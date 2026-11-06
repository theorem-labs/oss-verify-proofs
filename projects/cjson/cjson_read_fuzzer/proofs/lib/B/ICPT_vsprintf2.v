(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloatProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_mlib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_pop_arg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_vsnprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_str3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcleaf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_vfprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_sn_write.
Module ICPT_vsnprintf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_musl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloatProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_printf_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_printf_core.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_str3.ICPT_str OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_vfprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_printf_snsink OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_sn_write OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_vfprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.Printf_sn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope. Open Scope Z_scope. Open Scope mspec_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AVSNPRINTF_T : Z := 0x4253c.
Definition AVSNPRINTF_ICPT : Z := 0x46c34.
Definition A_REAL_VSNPRINTF : Z := 0x9a0e4.
Definition AVSNI_STACK : Z := 8064.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition vsni_cells (m : word -> option byte) : Prop :=
  vfi_cells m /\ ro_cells bsegs m 0xa3480 [C8 (Z_to_bv 64 0x9a0e4)].

Lemma vsni_cells_munch : forall W m m', vsni_cells m -> munch W m m' ->
  Forall (fun iv => disjoint_from W (fst iv) (snd iv - fst iv)) icpt_cell_ivs ->
  disjoint_from W 0x13b53c 1 -> disjoint_from W 0xa3478 16 -> vsni_cells m'.
Proof.
  intros W m m' [VC RL] MU D1 D2 D3. split; [eapply vfi_cells_munch; eauto; eapply disjoint_from_sub; [exact D3| lia| lia]|].
  eapply ro_cells_transport; [exact RL| exact MU|]. eapply disjoint_from_sub; [exact D3| cbn; lia| cbn; lia].
Qed.

Definition vsnprintf_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (D : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells bsegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)].

(* [comment removed for export] *)
Definition vsnprintf_icpt_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (D n A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells bsegs m D [CB dn junkd] ->
    bytes_at bsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> Forall no_s args -> args_ok 0 0 0 m lo q 0 slots args ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts y fl p t) (fp_calls (length fmt) fmt args) ->
    (length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
    stk bsegs m lo q -> (lo <= q - AVSNI_STACK) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    MRT m -> vsni_cells m -> lowsh_at m -> pcommon_stmt A ->
    (alloc_ceiling <= lo) -> (q + 64 <= 2^47 - 1) ->
    (0 < zlength fmt) -> shadow_ok m A (zlength fmt) -> app_range A (zlength fmt) ->
    app_range D (Z.of_nat dn) -> mrt_iv_ok (D, D + Z.of_nat dn) -> shadow_ok m D (Z.of_nat dn) ->
    (0 <= r) -> (r + 1 <= Z.of_nat dn) -> (Z.of_nat dn < 2^31) ->
    evt bsegs (vsnprintf_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AVSNPRINTF_ICPT) fc None m (seg_rom bsegs)).

Section VsnprintfIcpt.
  Variables (rae sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (D n lo : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (canary : word).
  Let K := Z.min n (r + 1).
  Hypothesis HN : 1 <= n < 2^63.
  Hypothesis HR : 0 <= r /\ r + 1 <= Z.of_nat dn /\ Z.of_nat dn < 2^31.
  Hypothesis ARD : app_range D (Z.of_nat dn).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + AVSNI_STACK <= bv_unsigned sp.
  Hypothesis SEP : D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D.

  Lemma HK : 0 < K <= Z.of_nat dn. Proof. unfold K. lia. Qed.
  Lemma RB : 0 <= D /\ D + Z.of_nat dn < 2^47. Proof. exact (app_range_lt47 _ _ ARD). Qed.
  Lemma ARK : app_range D K. Proof. pose proof HK. eapply app_range_sub; [exact ARD| lia| lia| lia]. Qed.
  Lemma CEILv : alloc_ceiling = alloc_ceiling. Proof. reflexivity. Qed.
  Lemma STKv : AVSNI_STACK = 8064. Proof. reflexivity. Qed.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (vsnprintf_icpt_post rae sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8 s9 s10 s11 F D dn junkd r o lo canary m).
  (* [comment removed for export] *)
  Variables (Ft : bvmap 5 word) (fc' : bv 32).
  #[warnings="-notation-for-abbreviation"]
  Notation ST_ pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9
            x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 n) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        Ft (Z_to_bv 64 pc) fc' None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition vsi_frame (mm : word -> option byte) : Prop :=
    mem_inv bsegs mm /\ MRT mm /\ stk bsegs mm lo (bv_unsigned sp + -2160)
    /\ rw_cells bsegs mm (bv_unsigned sp + -72) [C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae]
    /\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m mm /\ wmono bsegs m mm
    /\ stk bsegs mm (bv_unsigned sp + -2160) (bv_unsigned sp + -72)
    /\ shadow_ok mm D K
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ ssp_cells mm canary
    /\ rw_cells bsegs mm D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)].

  Ltac lit_cond Kc := revert Kc; rewrite ?unsigned_lit by lia; intros Kc; try rewrite !Z.mod_small in Kc by lia.
  Ltac vsi_intro AF := destruct AF as (MI' & MR' & ST' & FR' & MU' & WM' & ST2 & SO & FRM' & FOK' & SSP' & DST').
  Ltac vsi_pack := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))); assumption.

  Lemma vsi_after_callee : forall mm mm' k,
    MRT mm -> shadow_ok mm D K -> ssp_cells mm canary ->
    0 <= k <= 80 -> munch [(bv_unsigned sp - 2160 - k, bv_unsigned sp - 2160)] mm mm' -> wmono bsegs mm mm' ->
    MRT mm' /\ shadow_ok mm' D K /\ ssp_cells mm' canary.
  Proof.
    intros mm mm' k MR SOk SSP Hk MUr WMr. pose proof RB. pose proof HK. pose proof CEILv. pose proof STKv.
    split; [|split].
    - eapply MRT_munch; [exact MR| exact MUr|]. apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil].
    - eapply shadow_ok_munch_app; [exact SOk| exact MUr| lia| exact ARK|]. apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil].
    - destruct SSP as [S1 S2]. unfold ssp_cells, got_ssp, ssp_guard in *.
      split; (eapply rw_cells_transport; [eassumption| exact MUr| exact WMr| cbn; lia]).
  Qed.

  (* [comment removed for export] *)
  Lemma vsi_ret : forall mm x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31,
    vsi_frame mm ->
    evt bsegs POST (ST_ 0x46d30 mm x1 x5 x6 x7 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. vsi_intro AF.
    pose proof RB as RB'. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    do 12 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with ST1 : stk bsegs mm2 lo _ |- _ =>
      lazymatch goal with ST3 : stk bsegs mm2 (bv_unsigned sp + -2160) _ |- _ =>
      lazymatch goal with FR3 : rw_cells bsegs mm2 (bv_unsigned sp + -72) _ |- _ =>
        pose proof (stk_merge bsegs mm2 _ _ _ ST1 ST3 ltac:(lia)) as STm;
        release_frame FR3 STm (bv_unsigned sp)
      end end end end.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma vsi_region : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    vsi_frame mm ->
    evt bsegs POST (ST_ 0x46e68 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. vsi_intro AF.
    pose proof RB as RB'. pose proof HK as HK'. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof MR' as MR2. pose proof SO as SO2. pose proof SSP' as SSP2.
    pose proof (munch_refl [(bv_unsigned sp - 2160 - 80, bv_unsigned sp - 2160)] mm) as MU1.
    pose proof (wmono_refl bsegs mm) as WM1.
    do 4 zstep.
    callsp region_is_poisoned_ok;
      [ exact (MRT_icpt _ MR') | exact MI' | exact ST' | exact CEIL | lia | reflexivity | reflexivity | lia
      | exact ARK | exact SO | ].
    zstep. zstep. zstep. fold_lits. sh_if_true.
    apply vsi_ret.
    lazymatch goal with |- vsi_frame ?mm2 =>
      lazymatch goal with MUc : munch _ mm mm2, WMc : wmono bsegs mm mm2 |- _ =>
        destruct (vsi_after_callee mm mm2 80 MR2 SO2 SSP2 ltac:(lia) MUc WMc) as (MR3 & SO3 & SSP3)
      end end.
    vsi_pack.
  Qed.

  (* [comment removed for export] *)
  Lemma vsi_cc8 : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    vsi_frame mm ->
    evt bsegs POST (ST_ 0x46e60 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB as RB'.
    zstep. zstep. if_cases Kc.
    - apply vsi_ret. exact AF.
    - apply vsi_region. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma vsi_loop : forall mm (k : nat) (i : Z) x1 x5 x6 x7 (acc : word) x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    vsi_frame mm ->
    Z.to_nat (SH (D + K - 1) - SH D - i) = k -> 0 <= i -> SH D + i < SH (D + K - 1) ->
    evt bsegs POST (ST_ 0x46e50 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 r) (Z_to_bv 64 (2147450880 + D / 8 + i)) (Z_to_bv 64 (2147450880 + (D + K - 1) / 8))
                        acc x14 x15 x16 x17 (Z_to_bv 64 D) x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros mm k. induction k as [|k IH]; intros i x1 x5 x6 x7 acc x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 AF Hk Hi Hlt;
      pose proof RB as RB'; pose proof HK as HK'; pose proof (SH_bounds D ltac:(lia)) as B1; pose proof (SH_bounds (D + K - 1) ltac:(lia)) as B2;
      unfold SH, SHADOW_OFFSET in *; [lia|].
    pose proof AF as AF'. vsi_intro AF'.
    assert (V : exists b, mm (wa (2147450880 + D / 8 + i)) = Some b).
    { destruct (mm (wa (2147450880 + D / 8 + i))) as [b|] eqn:E; [exists b; reflexivity| exfalso].
      apply (proj2 SO (2147450880 + D / 8 + i)); [| exact E]. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    destruct V as [b RDb]. pose proof (vis_read1 mm _ b RDb) as RD. unfold wa in RD.
    zstep. zstep. zstep. zstep.
    if_cases Kc; zify_cond Kc.
    - replace (2147450880 + D / 8 + i + 1) with (2147450880 + D / 8 + (i + 1)) by lia.
      apply (IH (i + 1)); try assumption; lia.
    - replace (2147450880 + D / 8 + i + 1) with (2147450880 + (D + K - 1) / 8) by lia.
      apply vsi_cc8. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma vsi_slow : forall mm x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    vsi_frame mm ->
    evt bsegs POST (ST_ 0x46e34 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 r) (Z_to_bv 64 (2147450880 + D / 8)) (Z_to_bv 64 (2147450880 + (D + K - 1) / 8))
                        (Z_to_bv 64 (D + K - 1)) x14 x15 x16 x17 (Z_to_bv 64 D) x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB as RB'. pose proof HK as HK'.
    pose proof (SH_bounds D ltac:(lia)) as B1. pose proof (SH_bounds (D + K - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. vsi_intro AF'.
    destruct (shadow_ok_shb mm D K (K - 1) SO ltac:(lia)) as (ve & SHE & Ce).
    pose proof (shb_load_div' mm (D + (K - 1)) ve (D + K - 1) SHE ltac:(lia) ltac:(lia)) as RD.
    zstep. clear RD.
    rewrite (sxb_zb_small ve) by lia.
    do 5 zstep.
    zstep. if_cases Kc; zify_cond Kc.
    - apply vsi_cc8. exact AF.
    - replace (2147450880 + D / 8) with (2147450880 + D / 8 + 0) by lia.
      eapply (vsi_loop mm (Z.to_nat (SH (D + K - 1) - SH D - 0)) 0); try exact AF; unfold SH, SHADOW_OFFSET; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vsi_quick : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    vsi_frame mm -> K <= 64 ->
    evt bsegs POST (ST_ 0x46cf4 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF HKr. pose proof RB as RB'. pose proof HK as HK'.
    pose proof (SH_bounds D ltac:(lia)) as B1. pose proof (SH_bounds (D + K - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. vsi_intro AF'.
    pose proof (MRT_icpt _ MR') as IC'. icpt_split IC'.
    do 9 zstep.
    rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
    replace (D + K + -1) with (D + K - 1) by lia.
    zstep. zstep. rewrite !land_m8 by lia.
    destruct (vis_read8 mm ((2147450880 + D / 8) / 8 * 8)) as (w1 & L1 & W1).
    { intros j Hj. apply (proj2 SO). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    destruct (vis_read8 mm ((2147450880 + (D + K - 1) / 8) / 8 * 8)) as (w2 & L2 & W2).
    { intros j Hj. apply (proj2 SO). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    unfold wa in W1, W2.
    step. step. clear W1 W2.
    zstep. step. if_cases Kc.
    - apply vsi_slow. exact AF.
    - apply vsi_ret. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma vsi_c94 : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    vsi_frame mm ->
    evt bsegs POST (ST_ 0x46e2c mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB as RB'.
    zstep. if_cases Kc; zify_cond Kc; lit_cond Kc.
    - apply vsi_region. exact AF.
    - exfalso. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vsi_b50 : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    vsi_frame mm ->
    evt bsegs POST (ST_ 0x46ce8 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB as RB'. pose proof HK as HK'.
    zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
    - apply vsi_c94. exact AF.
    - apply vsi_quick; [exact AF|].
      revert Kc. rewrite ?unsigned_lit by lia. intros Kc.
      destruct (Z.lt_ge_cases K 65) as [Hl|Hg]; [lia| exfalso].
      first [ rewrite Z.mod_small in Kc by lia
            | change 18446744073709551615 with (Z.ones 64) in Kc; rewrite Z.land_ones in Kc by lia;
              rewrite Z.mod_small in Kc by lia ]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vsi_b30 : forall mm x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    vsi_frame mm ->
    evt bsegs POST (ST_ 0x46cc8 mm x1 x5 x6 x7 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB as RB'. pose proof HK as HK'. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0 HR. lia. }
    zstep. rewrite ?Z_to_bv_swrap32, ?(swrap32_small (r + 1)), ?(SoftFloatProps.sext32_small (r + 1)) by lia.
    zstep. zstep. if_cases Kc; zify_cond Kc; lit_cond Kc.
    - (* [comment removed for export] *)
      zstep. zstep. fold_lits. rewrite (zb_lxor_ones D) by lia. zstep. zstep.
      zstep. if_cases Kc2; zify_cond Kc2; lit_cond Kc2.
      + replace (r + 1) with K by (unfold K; lia). apply vsi_b50. exact AF.
      + exfalso. lia.
    - (* [comment removed for export] *)
      zstep. fold_lits. rewrite (zb_lxor_ones D) by lia. zstep. zstep.
      zstep. if_cases Kc2; zify_cond Kc2; lit_cond Kc2.
      + exfalso. lia.
      + pose proof (vsi_b50 mm) as NX. replace K with n in NX by (unfold K; lia). apply NX. exact AF.
  Qed.
End VsnprintfIcpt.


End CeilWrap.
End ICPT_vsnprintf.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module ICPT_vsnprintf2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_musl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloatProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_printf_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_printf_core.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_str3.ICPT_str OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_vfprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_printf_snsink OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_sn_write OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_vfprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.Printf_sn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf ICPT_vsnprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope. Open Scope Z_scope. Open Scope mspec_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac gs1 := zstep; try fold_lits.

Lemma vsnprintf_icpt_ok : vsnprintf_icpt_stmt.
Proof.
  unfold vsnprintf_icpt_stmt. intros until o. cbv zeta.
  intros -> -> -> -> DST BY HF P1 VAA NOS AOK MODEL FPF ROOM Hn Hn1 ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI DD1 DVA GD.
  intros MR VSC LOW PC CEIL Q47 FNZ FSO FAR ARD MID SOD R0 R1 DN31.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold AVSNI_STACK in LO.
  unfold GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (app_range_lt47 _ _ ARD) as RB. pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (WAPP : Forall app_iv [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]).
  { apply Forall_cons; [apply app_iv_stack; lia|]. apply Forall_cons; [apply app_iv_of_range; exact ARD| apply Forall_nil]. }
  assert (WMRT : Forall mrt_iv_ok [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]).
  { apply Forall_cons; [apply mrt_iv_ok_stack; lia|]. apply Forall_cons; [exact MID| apply Forall_nil]. }
  pose proof VSC as [[IC [CF RLV]] RL]. pose proof IC as IC'. icpt_split IC'.
  unfold AVSNPRINTF_ICPT.
  (* [comment removed for export] *)
  carve_frame 96%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 17 gs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    destruct (stk_split bsegs m0 lo (bv_unsigned sp + -2160) (bv_unsigned sp + -96) ST ltac:(lia)) as [ST1 ST2] end.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 2160 - 16, bv_unsigned sp - 2160)] mm) as MU1 end.
  gs. callsp try_init_ok.
  1:{ lazymatch goal with |- icpt_cells ?mm => eapply icpt_cells_munch; [exact IC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil] end. }
  1:{ assumption. } 1:{ exact ST1. } 1:{ exact CEIL. } 1:{ lia. }
  clear MU1.
  gsto 0x46ca8%Z.
  (* [comment removed for export] *)
  gs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SB1 : shbase_cells mm) by (eapply shbase_cells_munch; [exact (proj1 IC)| exact MU| cbn; lia| cbn; lia]);
    assert (LOW1 : lowsh_at mm) by (eapply lowsh_at_munch; [exact LOW| exact MU| exact WM|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_HI; lia|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI; destruct ARD as [ARD'|ARD']; unfold lowmem_range, highmem_range, KHIGHMEM_BEG, KLOWSHADOW_BEG in ARD'; lia| apply Forall_nil]);
    pose proof (munch_refl [(bv_unsigned sp - 2160 - 2272, bv_unsigned sp - 2160)] mm) as MU2;
    lazymatch goal with STc : stk bsegs mm lo _ |- _ =>
      callsp PC; [ assumption | exact SB1 | exact LOW1 | exact STc | exact CEIL | unfold APC_STACK; lia | reflexivity | ] end end.
  clear MU2 SB1 LOW1.
  gsto 0x46cc4%Z.
  (* [comment removed for export] *)
  gs.
  name_spq (bv_unsigned sp + -2160)%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MR2 : MRT mm) by (eapply MRT_munch; [exact MR| exact MU| exact WMRT]);
    assert (VSC2 : vsni_cells mm) by (eapply vsni_cells_munch; [exact VSC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil| cbn; lia| cbn; lia]);
    assert (LOW2 : lowsh_at mm) by (eapply lowsh_at_munch; [exact LOW| exact MU| exact WM|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_HI; lia|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI; destruct ARD as [ARD'|ARD']; unfold lowmem_range, highmem_range, KHIGHMEM_BEG, KLOWSHADOW_BEG in ARD'; lia| apply Forall_nil]);
    assert (FSO2 : shadow_ok mm A (Z.of_nat (length fmt))) by (eapply shadow_ok_munch_app; [exact FSO| exact MU| lia| exact FAR| exact WAPP]);
    assert (SOD2 : shadow_ok mm D (Z.of_nat dn)) by (eapply shadow_ok_munch_app; [exact SOD| exact MU| lia| exact ARD| exact WAPP]);
    assert (SSP2 : ssp_cells mm canary) by (destruct SSP as [SS1 SS2]; split; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; unfold got_ssp, ssp_guard; lia]));
    assert (VAA2 : va_area mm VA slots) by (unfold va_area in VAA |- *; eapply bytes_at_transport; [exact VAA| exact MU|]; rewrite (u64s_length slots); cbn; lia)
  end.
  lazymatch goal with STc : stk bsegs _ lo (bv_unsigned sp + -2160) |- _ => rename STc into ST1 end.
  pose proof vsnprintf_proof as VS. unfold vsnprintf_stmt in VS.
  eapply evt_cut.
  { eapply VS with (D := D) (n := n) (A := A) (VA := VA) (dn := dn) (junkd := junkd) (fmt := fmt) (slots := slots) (args := args) (lo := lo) (canary := canary) (r := r) (o := o);
      clear VS; rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength.
    all: try reflexivity.
    all: try lia.
    all: first [ exact DST | exact BY | exact HF | exact P1 | exact VAA2 | exact NOS | eapply args_ok_nos; [exact NOS | exact AOK]
               | exact MODEL | exact FPF | rewrite Hsp; exact ST1 | exact SSP2 | assumption | exact FRM | exact MR2 | exact (proj1 VSC2) | exact LOW2 | exact PC | exact CEIL | exact FSO2 | exact FAR | exact ARD | exact MID | exact SOD2
               | match goal with |- ?G => idtac "VS-REMAINING" G end ]. }
  cbv beta. intros ms' P. clear VS.
  unfold vsnprintf_post in P. rewrite ?Hsp in P.
  (nelim P 26%nat; intros y5 y6 y7 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 Ft fc' m3 -> MUc WMc MI3 FRM' FOK ST3 SSP3 DST3).
  assert (MR3 : MRT m3) by (eapply MRT_munch; [exact MR2| exact MUc|]; apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_cons; [exact MID| apply Forall_nil]]).
  assert (SOD3 : shadow_ok m3 D (Z.of_nat dn)).
  { eapply shadow_ok_munch_app; [exact SOD2| exact MUc| lia| exact ARD|]. apply Forall_cons; [apply app_iv_stack; lia| apply Forall_cons; [apply app_iv_of_range; exact ARD| apply Forall_nil]]. }
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m3 MUc WMc; clear MUc WMc end.
  replace (ret_pc (Z_to_bv 64 289992)) with (Z_to_bv 64 289992 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  subst sp0. clear Hsp MR2 VSC2 LOW2 FSO2 SOD2 SSP2 VAA2.
  (* [comment removed for export] *)
  lazymatch goal with FRc : rw_cells bsegs m3 (bv_unsigned sp + -96) [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11] |- _ =>
    apply (proj1 (rw_cells_app bsegs _ _ [c0; c1; c2] _)) in FRc; destruct FRc as [FRlo FRhi]; cbn [cells_size csize Nat.add app] in FRhi;
    replace (bv_unsigned sp + -96 + Z.of_nat 24) with (bv_unsigned sp + -72) in FRhi by lia;
    lazymatch goal with STf : stk bsegs m3 (bv_unsigned sp + -2160) (bv_unsigned sp + -96) |- _ =>
      release_frame FRlo STf (bv_unsigned sp + -72); rename STf into STF end
  end.
  eapply (vsi_b30 _ sp gp tp _ _ _ _ _ _ _ _ s8 s9 s10 s11 F m D n lo dn junkd r o canary); try eassumption; try (unfold AVSNI_STACK; lia).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))));
    try eassumption.
  eapply shadow_ok_sub; [exact SOD3| lia| lia| lia].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac gs1 := zstep; try fold_lits.
End ICPT_vsnprintf2.

(* [comment removed for export] *)
Module ICPT_vsprintf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_musl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloatProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_printf_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_printf_core.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_str3.ICPT_str OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_vfprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_printf_snsink OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_sn_write OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_vfprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.Printf_sn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf ICPT_vsnprintf ICPT_vsnprintf2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope. Open Scope Z_scope. Open Scope mspec_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AVSPRINTF_T : Z := 0x61b90.
Definition AVSPRINTF_ICPT : Z := 0x46f4c.
Definition A_REAL_VSPRINTF : Z := 0x9a28c.
Definition AVSPI_STACK : Z := 10224.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition vspi_cells (m : word -> option byte) : Prop :=
  vsni_cells m /\ ro_cells bsegs m 0xa3488 [C8 (Z_to_bv 64 0x9a28c)].

Lemma vspi_cells_munch : forall W m m', vspi_cells m -> munch W m m' ->
  Forall (fun iv => disjoint_from W (fst iv) (snd iv - fst iv)) icpt_cell_ivs ->
  disjoint_from W 0x13b53c 1 -> disjoint_from W 0xa3478 24 -> vspi_cells m'.
Proof.
  intros W m m' [VC RL] MU D1 D2 D3. split; [eapply vsni_cells_munch; eauto; eapply disjoint_from_sub; [exact D3| lia| lia]|].
  eapply ro_cells_transport; [exact RL| exact MU|]. eapply disjoint_from_sub; [exact D3| cbn; lia| cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition real_vsprintf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (D A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells bsegs m D [CB dn junkd] ->
    bytes_at bsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> Forall no_s args -> args_ok 0 0 0 m lo q 0 slots args ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts y fl p t) (fp_calls (length fmt) fmt args) ->
    (length o < dn)%nat ->
    stk bsegs m lo q -> (lo <= q - AVSNI_STACK) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    MRT m -> vsni_cells m -> lowsh_at m -> pcommon_stmt A ->
    (alloc_ceiling <= lo) -> (q + 64 <= 2^47 - 1) ->
    (0 < zlength fmt) -> shadow_ok m A (zlength fmt) -> app_range A (zlength fmt) ->
    app_range D (Z.of_nat dn) -> mrt_iv_ok (D, D + Z.of_nat dn) -> shadow_ok m D (Z.of_nat dn) ->
    (0 <= r) -> (r + 1 <= Z.of_nat dn) -> (Z.of_nat dn < 2^31) ->
    evt bsegs (vsnprintf_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 A_REAL_VSPRINTF) fc None m (seg_rom bsegs)).

Lemma real_vsprintf_ok : real_vsprintf_stmt.
Proof.
  unfold real_vsprintf_stmt. intros until o. cbv zeta.
  intros -> -> -> DST BY HF P1 VAA NOS AOK MODEL FPF ROOM ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI DD1 DVA GD.
  intros MR VSC LOW PC CEIL Q47 FNZ FSO FAR ARD MID SOD R0 R1 DN31.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  unfold A_REAL_VSPRINTF.
  do 5 zstep. fold_lits.
  zstep. (* [comment removed for export] *)
  pose proof vsnprintf_icpt_ok as VS. unfold vsnprintf_icpt_stmt, AVSNPRINTF_ICPT in VS. cbv zeta in VS.
  eapply VS; clear VS; first [reflexivity | eassumption | unfold zlength in *; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vsprintf_icpt_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (D A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells bsegs m D [CB dn junkd] ->
    bytes_at bsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> Forall no_s args -> args_ok 0 0 0 m lo q 0 slots args ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts y fl p t) (fp_calls (length fmt) fmt args) ->
    (length o < dn)%nat ->
    stk bsegs m lo q -> (lo <= q - AVSPI_STACK) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    MRT m -> vspi_cells m -> lowsh_at m -> pcommon_stmt A ->
    (alloc_ceiling <= lo) -> (q + 64 <= 2^47 - 1) ->
    (0 < zlength fmt) -> shadow_ok m A (zlength fmt) -> app_range A (zlength fmt) ->
    app_range D (Z.of_nat dn) -> mrt_iv_ok (D, D + Z.of_nat dn) -> shadow_ok m D (Z.of_nat dn) ->
    (0 <= r) -> (r + 1 <= Z.of_nat dn) -> (Z.of_nat dn < 2^31) ->
    evt bsegs (vsnprintf_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AVSPRINTF_ICPT) fc None m (seg_rom bsegs)).

Section VsprintfIcpt.
  Variables (rae sp gp tp s0e s1e s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (D lo : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (canary : word).
  Let K := r + 1.
  Hypothesis HR : 0 <= r /\ r + 1 <= Z.of_nat dn /\ Z.of_nat dn < 2^31.
  Hypothesis ARD : app_range D (Z.of_nat dn).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + AVSPI_STACK <= bv_unsigned sp.
  Hypothesis SEP : D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D.

  Lemma HK' : 0 < K <= Z.of_nat dn. Proof. unfold K. lia. Qed.
  Lemma RB' : 0 <= D /\ D + Z.of_nat dn < 2^47. Proof. exact (app_range_lt47 _ _ ARD). Qed.
  Lemma ARK' : app_range D K. Proof. pose proof HK'. eapply app_range_sub; [exact ARD| lia| lia| lia]. Qed.
  Lemma CEILv' : alloc_ceiling = alloc_ceiling. Proof. reflexivity. Qed.
  Lemma STKv' : AVSPI_STACK = 10224. Proof. reflexivity. Qed.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (vsnprintf_icpt_post rae sp gp tp s0e s1e s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 F D dn junkd r o lo canary m).
  (* [comment removed for export] *)
  Variables (Ft : bvmap 5 word) (fc' : bv 32).
  #[warnings="-notation-for-abbreviation"]
  Notation ST_ pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9
            x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        Ft (Z_to_bv 64 pc) fc' None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition vpi_frame (mm : word -> option byte) : Prop :=
    mem_inv bsegs mm /\ MRT mm /\ stk bsegs mm lo (bv_unsigned sp + -2160)
    /\ rw_cells bsegs mm (bv_unsigned sp + -64) [C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae]
    /\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m mm /\ wmono bsegs m mm
    /\ stk bsegs mm (bv_unsigned sp + -2160) (bv_unsigned sp + -64)
    /\ shadow_ok mm D K
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ ssp_cells mm canary
    /\ rw_cells bsegs mm D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)].

  Ltac lit_cond Kc := revert Kc; rewrite ?unsigned_lit by lia; intros Kc; try rewrite !Z.mod_small in Kc by lia.
  Ltac vpi_intro AF := destruct AF as (MI' & MR' & ST' & FR' & MU' & WM' & ST2 & SO & FRM' & FOK' & SSP' & DST').
  Ltac vpi_pack := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))); assumption.

  Lemma vpi_after_callee : forall mm mm' k,
    MRT mm -> shadow_ok mm D K -> ssp_cells mm canary ->
    0 <= k <= 80 -> munch [(bv_unsigned sp - 2160 - k, bv_unsigned sp - 2160)] mm mm' -> wmono bsegs mm mm' ->
    MRT mm' /\ shadow_ok mm' D K /\ ssp_cells mm' canary.
  Proof.
    intros mm mm' k MR SOk SSP Hk MUr WMr. pose proof RB'. pose proof HK'. pose proof CEILv'. pose proof STKv'.
    split; [|split].
    - eapply MRT_munch; [exact MR| exact MUr|]. apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil].
    - eapply shadow_ok_munch_app; [exact SOk| exact MUr| lia| exact ARK'|]. apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil].
    - destruct SSP as [S1 S2]. unfold ssp_cells, got_ssp, ssp_guard in *.
      split; (eapply rw_cells_transport; [eassumption| exact MUr| exact WMr| cbn; lia]).
  Qed.

  (* [comment removed for export] *)
  Lemma vpi_ret : forall mm x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    vpi_frame mm ->
    evt bsegs POST (ST_ 0x47034 mm x1 x5 x6 x7 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. vpi_intro AF.
    pose proof RB' as RB. pose proof CEILv' as CE. pose proof STKv' as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    do 11 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with ST1 : stk bsegs mm2 lo _ |- _ =>
      lazymatch goal with ST3 : stk bsegs mm2 (bv_unsigned sp + -2160) _ |- _ =>
      lazymatch goal with FR3 : rw_cells bsegs mm2 (bv_unsigned sp + -64) _ |- _ =>
        pose proof (stk_merge bsegs mm2 _ _ _ ST1 ST3 ltac:(lia)) as STm;
        release_frame FR3 STm (bv_unsigned sp)
      end end end end.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma vpi_region : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
    vpi_frame mm ->
    evt bsegs POST (ST_ 0x47110 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. vpi_intro AF.
    pose proof RB' as RB. pose proof HK' as HK. pose proof CEILv' as CE. pose proof STKv' as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof MR' as MR2. pose proof SO as SO2. pose proof SSP' as SSP2.
    pose proof (munch_refl [(bv_unsigned sp - 2160 - 80, bv_unsigned sp - 2160)] mm) as MU1.
    pose proof (wmono_refl bsegs mm) as WM1.
    do 4 zstep.
    callsp region_is_poisoned_ok;
      [ exact (MRT_icpt _ MR') | exact MI' | exact ST' | exact CEIL | lia | reflexivity | reflexivity | lia
      | exact ARK' | exact SO | ].
    zstep. zstep. zstep. fold_lits. sh_if_true.
    apply vpi_ret.
    lazymatch goal with |- vpi_frame ?mm2 =>
      lazymatch goal with MUc : munch _ mm mm2, WMc : wmono bsegs mm mm2 |- _ =>
        destruct (vpi_after_callee mm mm2 80 MR2 SO2 SSP2 ltac:(lia) MUc WMc) as (MR3 & SO3 & SSP3)
      end end.
    vpi_pack.
  Qed.

  (* [comment removed for export] *)
  Lemma vpi_048 : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
    vpi_frame mm ->
    evt bsegs POST (ST_ 0x471e0 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB' as RB.
    zstep. zstep. if_cases Kc.
    - apply vpi_ret. exact AF.
    - zstep. apply vpi_region. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma vpi_loop : forall mm (k : nat) (i : Z) x1 x5 x6 x7 (acc : word) x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
    vpi_frame mm ->
    Z.to_nat (SH (D + K - 1) - SH D - i) = k -> 0 <= i -> SH D + i < SH (D + K - 1) ->
    evt bsegs POST (ST_ 0x471d0 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 r) (Z_to_bv 64 (2147450880 + D / 8 + i)) (Z_to_bv 64 (2147450880 + (D + K - 1) / 8))
                        acc x14 x15 x16 x17 (Z_to_bv 64 D) x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros mm k. induction k as [|k IH]; intros i x1 x5 x6 x7 acc x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31 AF Hk Hi Hlt;
      pose proof RB' as RB; pose proof HK' as HK; pose proof (SH_bounds D ltac:(lia)) as B1; pose proof (SH_bounds (D + K - 1) ltac:(lia)) as B2;
      unfold SH, SHADOW_OFFSET in *; [lia|].
    pose proof AF as AF'. vpi_intro AF'.
    assert (V : exists b, mm (wa (2147450880 + D / 8 + i)) = Some b).
    { destruct (mm (wa (2147450880 + D / 8 + i))) as [b|] eqn:E; [exists b; reflexivity| exfalso].
      apply (proj2 SO (2147450880 + D / 8 + i)); [| exact E]. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    destruct V as [b RDb]. pose proof (vis_read1 mm _ b RDb) as RD. unfold wa in RD.
    zstep. zstep. zstep. zstep.
    if_cases Kc; zify_cond Kc.
    - replace (2147450880 + D / 8 + i + 1) with (2147450880 + D / 8 + (i + 1)) by lia.
      apply (IH (i + 1)); try assumption; lia.
    - replace (2147450880 + D / 8 + i + 1) with (2147450880 + (D + K - 1) / 8) by lia.
      apply vpi_048. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma vpi_slow : forall mm x1 x5 x6 x7 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
    vpi_frame mm ->
    evt bsegs POST (ST_ 0x471b4 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 r) (Z_to_bv 64 (2147450880 + D / 8)) (Z_to_bv 64 (2147450880 + (D + K - 1) / 8))
                        (Z_to_bv 64 (D + K - 1)) x14 x15 x16 x17 (Z_to_bv 64 D) x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB' as RB. pose proof HK' as HK.
    pose proof (SH_bounds D ltac:(lia)) as B1. pose proof (SH_bounds (D + K - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. vpi_intro AF'.
    destruct (shadow_ok_shb mm D K (K - 1) SO ltac:(lia)) as (ve & SHE & Ce).
    pose proof (shb_load_div' mm (D + (K - 1)) ve (D + K - 1) SHE ltac:(lia) ltac:(lia)) as RD.
    zstep. clear RD.
    rewrite (sxb_zb_small ve) by lia.
    do 5 zstep.
    zstep. if_cases Kc; zify_cond Kc.
    - apply vpi_048. exact AF.
    - replace (2147450880 + D / 8) with (2147450880 + D / 8 + 0) by lia.
      eapply (vpi_loop mm (Z.to_nat (SH (D + K - 1) - SH D - 0)) 0); try exact AF; unfold SH, SHADOW_OFFSET; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vpi_quick : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
    vpi_frame mm -> K <= 64 ->
    evt bsegs POST (ST_ 0x46ff8 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF HKr. pose proof RB' as RB. pose proof HK' as HK.
    pose proof (SH_bounds D ltac:(lia)) as B1. pose proof (SH_bounds (D + K - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. vpi_intro AF'.
    pose proof (MRT_icpt _ MR') as IC'. icpt_split IC'.
    do 9 zstep.
    rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
    replace (D + K + -1) with (D + K - 1) by lia.
    zstep. zstep. rewrite !land_m8 by lia.
    destruct (vis_read8 mm ((2147450880 + D / 8) / 8 * 8)) as (w1 & L1 & W1).
    { intros j Hj. apply (proj2 SO). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    destruct (vis_read8 mm ((2147450880 + (D + K - 1) / 8) / 8 * 8)) as (w2 & L2 & W2).
    { intros j Hj. apply (proj2 SO). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    unfold wa in W1, W2.
    step. step. clear W1 W2.
    zstep. step. if_cases Kc.
    - apply vpi_slow. exact AF.
    - apply vpi_ret. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma vpi_e54 : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
    vpi_frame mm ->
    evt bsegs POST (ST_ 0x46fec mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB' as RB. pose proof HK' as HK.
    zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
    - apply vpi_region. exact AF.
    - apply vpi_quick; [exact AF|].
      revert Kc. rewrite ?unsigned_lit by lia. intros Kc.
      destruct (Z.lt_ge_cases K 65) as [Hl|Hg]; [lia| exfalso].
      first [ rewrite Z.mod_small in Kc by lia
            | change 18446744073709551615 with (Z.ones 64) in Kc; rewrite Z.land_ones in Kc by lia;
              rewrite Z.mod_small in Kc by lia ]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vpi_e3c : forall mm x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
    vpi_frame mm ->
    evt bsegs POST (ST_ 0x46fd4 mm x1 x5 x6 x7 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB' as RB. pose proof HK' as HK. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0 HR. lia. }
    zstep. rewrite ?Z_to_bv_swrap32, ?(swrap32_small (r + 1)), ?(SoftFloatProps.sext32_small (r + 1)) by lia.
    zstep. fold_lits. rewrite (zb_lxor_ones D) by lia. zstep. zstep.
    zstep. if_cases Kc; zify_cond Kc; lit_cond Kc.
    - exfalso. unfold K in *. lia.
    - apply vpi_e54. exact AF.
  Qed.
End VsprintfIcpt.


End CeilWrap.
End ICPT_vsprintf.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_defs RT_data CJ_iface AShadow ICPT_iface RT_poison RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat SoftFloatProps FmtFp Stdio StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas Printf_model Printf_mlib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_memset F_memcpy F_fwritex F_pad F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_printf_iface.F_fmt_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_pop_arg Exit F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_vsnprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_printf_core.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg ICPT_mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_str3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_str3.ICPT_str.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_pcleaf ICPT_pcdefs ICPT_vfprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_vsnprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_printf_snsink.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_sn_write.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_vsnprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_vfprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_vsnprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.Printf_sn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_vsnprintf.
Import ICPT_vsnprintf.
Import ICPT_vsnprintf2.
Import ICPT_vsprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope. Open Scope Z_scope. Open Scope mspec_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Lemma vsprintf_icpt_ok : vsprintf_icpt_stmt.
Proof.
  unfold vsprintf_icpt_stmt. intros until o. cbv zeta.
  intros -> -> -> DST BY HF P1 VAA NOS AOK MODEL FPF ROOM ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI DD1 DVA GD.
  intros MR VSC LOW PC CEIL Q47 FNZ FSO FAR ARD MID SOD R0 R1 DN31.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold AVSPI_STACK in LO.
  unfold GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (app_range_lt47 _ _ ARD) as RB. pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (WAPP : Forall app_iv [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]).
  { apply Forall_cons; [apply app_iv_stack; lia|]. apply Forall_cons; [apply app_iv_of_range; exact ARD| apply Forall_nil]. }
  assert (WMRT : Forall mrt_iv_ok [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]).
  { apply Forall_cons; [apply mrt_iv_ok_stack; lia|]. apply Forall_cons; [exact MID| apply Forall_nil]. }
  pose proof VSC as [[[IC [CF RLV]] RLN] RL]. pose proof IC as IC'. icpt_split IC'.
  unfold AVSPRINTF_ICPT.
  (* [comment removed for export] *)
  carve_frame 88%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 15 gs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    destruct (stk_split bsegs m0 lo (bv_unsigned sp + -2160) (bv_unsigned sp + -88) ST ltac:(lia)) as [ST1 ST2] end.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 2160 - 16, bv_unsigned sp - 2160)] mm) as MU1 end.
  gs. callsp try_init_ok.
  1:{ lazymatch goal with |- icpt_cells ?mm => eapply icpt_cells_munch; [exact IC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil] end. }
  1:{ assumption. } 1:{ exact ST1. } 1:{ exact CEIL. } 1:{ lia. }
  clear MU1.
  gsto 0x46fb8%Z.
  (* [comment removed for export] *)
  gs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SB1 : shbase_cells mm) by (eapply shbase_cells_munch; [exact (proj1 IC)| exact MU| cbn; lia| cbn; lia]);
    assert (LOW1 : lowsh_at mm) by (eapply lowsh_at_munch; [exact LOW| exact MU| exact WM|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_HI; lia|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI; destruct ARD as [ARD'|ARD']; unfold lowmem_range, highmem_range, KHIGHMEM_BEG, KLOWSHADOW_BEG in ARD'; lia| apply Forall_nil]);
    pose proof (munch_refl [(bv_unsigned sp - 2160 - 2272, bv_unsigned sp - 2160)] mm) as MU2;
    lazymatch goal with STc : stk bsegs mm lo _ |- _ =>
      callsp PC; [ assumption | exact SB1 | exact LOW1 | exact STc | exact CEIL | unfold APC_STACK; lia | reflexivity | ] end end.
  clear MU2 SB1 LOW1.
  gsto 0x46fd0%Z.
  (* [comment removed for export] *)
  gs.
  name_spq (bv_unsigned sp + -2160)%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MR2 : MRT mm) by (eapply MRT_munch; [exact MR| exact MU| exact WMRT]);
    assert (VSC2 : vspi_cells mm) by (eapply vspi_cells_munch; [exact VSC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil| cbn; lia| cbn; lia]);
    assert (LOW2 : lowsh_at mm) by (eapply lowsh_at_munch; [exact LOW| exact MU| exact WM|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_HI; lia|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI; destruct ARD as [ARD'|ARD']; unfold lowmem_range, highmem_range, KHIGHMEM_BEG, KLOWSHADOW_BEG in ARD'; lia| apply Forall_nil]);
    assert (FSO2 : shadow_ok mm A (Z.of_nat (length fmt))) by (eapply shadow_ok_munch_app; [exact FSO| exact MU| lia| exact FAR| exact WAPP]);
    assert (SOD2 : shadow_ok mm D (Z.of_nat dn)) by (eapply shadow_ok_munch_app; [exact SOD| exact MU| lia| exact ARD| exact WAPP]);
    assert (SSP2 : ssp_cells mm canary) by (destruct SSP as [SS1 SS2]; split; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; unfold got_ssp, ssp_guard; lia]));
    assert (VAA2 : va_area mm VA slots) by (unfold va_area in VAA |- *; eapply bytes_at_transport; [exact VAA| exact MU|]; rewrite (u64s_length slots); cbn; lia)
  end.
  lazymatch goal with STc : stk bsegs _ lo (bv_unsigned sp + -2160) |- _ => rename STc into ST1 end.
  pose proof real_vsprintf_ok as VS. unfold real_vsprintf_stmt in VS.
  eapply evt_cut.
  { eapply VS with (D := D) (A := A) (VA := VA) (dn := dn) (junkd := junkd) (fmt := fmt) (slots := slots) (args := args) (lo := lo) (canary := canary) (r := r) (o := o);
      clear VS; rewrite ?unsigned_lit by lia; unfold AVSNI_STACK, GLOBALS_TOP, STATIC_SPLIT, zlength.
    all: try reflexivity.
    all: try lia.
    all: first [ exact DST | exact BY | exact HF | exact P1 | exact VAA2 | exact NOS | eapply args_ok_nos; [exact NOS | exact AOK]
               | exact MODEL | exact FPF | rewrite Hsp; exact ST1 | exact SSP2 | assumption | exact FRM | exact MR2 | exact (proj1 VSC2) | exact LOW2 | exact PC | exact CEIL | exact FSO2 | exact FAR | exact ARD | exact MID | exact SOD2
               | match goal with |- ?G => idtac "VS-REMAINING" G end ]. }
  cbv beta. intros ms' P. clear VS.
  unfold vsnprintf_icpt_post in P. rewrite ?Hsp in P.
  (nelim P 26%nat; intros y5 y6 y7 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 Ft fc' m3 -> MUc WMc MI3 FRM' FOK ST3 SSP3 DST3).
  assert (MR3 : MRT m3) by (eapply MRT_munch; [exact MR2| exact MUc|]; apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_cons; [exact MID| apply Forall_nil]]).
  assert (SOD3 : shadow_ok m3 D (Z.of_nat dn)).
  { eapply shadow_ok_munch_app; [exact SOD2| exact MUc| lia| exact ARD|]. apply Forall_cons; [apply app_iv_stack; lia| apply Forall_cons; [apply app_iv_of_range; exact ARD| apply Forall_nil]]. }
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m3 MUc WMc; clear MUc WMc end.
  replace (ret_pc (Z_to_bv 64 290772)) with (Z_to_bv 64 290772 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  subst sp0. clear Hsp MR2 VSC2 LOW2 FSO2 SOD2 SSP2 VAA2.
  (* [comment removed for export] *)
  lazymatch goal with FRc : rw_cells bsegs m3 (bv_unsigned sp + -88) [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10] |- _ =>
    apply (proj1 (rw_cells_app bsegs _ _ [c0; c1; c2] _)) in FRc; destruct FRc as [FRlo FRhi]; cbn [cells_size csize Nat.add app] in FRhi;
    replace (bv_unsigned sp + -88 + Z.of_nat 24) with (bv_unsigned sp + -64) in FRhi by lia;
    lazymatch goal with STf : stk bsegs m3 (bv_unsigned sp + -2160) (bv_unsigned sp + -88) |- _ =>
      release_frame FRlo STf (bv_unsigned sp + -64); rename STf into STF end
  end.
  eapply (vpi_e3c _ sp gp tp _ _ _ _ _ _ _ s7 s8 s9 s10 s11 F m D lo dn junkd r o canary); try eassumption; try (unfold AVSPI_STACK; lia).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))));
    try eassumption.
  eapply shadow_ok_sub; [exact SOD3| lia| lia| lia].
Qed.


End CeilWrap.
