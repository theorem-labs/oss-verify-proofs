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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require SO_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Stdio_iface.
Module Drv_munch.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CeilWrap.
Context {ACEIL : Ceil}.

Lemma disjoint_from_Forall_fw : forall (Q : Z * Z -> Prop) W a n,
  Forall Q W -> (forall lo hi, Q (lo, hi) -> a + n <= lo \/ hi <= a) -> disjoint_from W a n.
Proof. intros Q W a n FW HQ. induction FW as [|[lo hi] W Hx FW IH]; cbn; [exact I|]. split; [apply (HQ _ _ Hx)| exact IH]. Qed.

Lemma stderr_wfile0_munch : forall m m' W,
  stderr_wfile0 m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => snd iv <= RSTDERR \/ RSTDERR + 232 <= fst iv) W -> stderr_wfile0 m'.
Proof.
  intros m m' W (flags & mode & e & wend & tail & FC & H) MU WM FW.
  exists flags, mode, e, wend, tail. split; [| exact H].
  eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
  eapply disjoint_from_Forall_fw; [exact FW|]. cbn. intros lo hi HH. lia.
Qed.

Lemma ssp_cells_munch : forall m m' W canary,
  ssp_cells m canary -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => (snd iv <= got_ssp \/ got_ssp + 8 <= fst iv) /\ (snd iv <= ssp_guard \/ ssp_guard + 8 <= fst iv)) W ->
  ssp_cells m' canary.
Proof.
  intros m m' W canary [G1 G2] MU WM FW. split.
  - eapply rw_cells_transport; [exact G1 | exact MU | exact WM |]. eapply disjoint_from_Forall_fw; [exact FW|]. cbn. intros lo hi [HH _]. lia.
  - eapply rw_cells_transport; [exact G2 | exact MU | exact WM |]. eapply disjoint_from_Forall_fw; [exact FW|]. cbn. intros lo hi [_ HH]. lia.
Qed.
End CeilWrap.
End Drv_munch.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes ITree Nodes Decode SysStep SFModel MonadX.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow ICPT_iface RT_poison RT_poison2 ICPT_mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_str3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_str3.ICPT_str.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_pad F_fmt_fp_lib Exit F_printf_iface Stdio_iface SO_base SO_fwrite.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Export Drv_icpt_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_model.    (* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import SO_piface.
Import Drv_munch.   (* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)

Section Fw.
  Context {St : Type}.

  Definition fwrite_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - AFWRITE_STACK, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary
      /\ st' = st.

  (* [comment removed for export] *)
  Definition fwrite_icpt_spec : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
      towrite_stmt ->
      icpt_cells m -> fwrite_icpt_cells m -> mem_inv asegs m ->
      stderr_wfile0 m ->
      bytes_at asegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^31 ->
      a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
      stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AFWRITE_STACK <= bv_unsigned sp ->
      (bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
      app_range (bv_unsigned a0) (zlength s) -> shadow_ok m (bv_unsigned a0) (zlength s) ->
      ssp_cells m canary ->
      implM asegs (stderr_fwrite s : M St unit) st
            (fwrite_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x424f4) fc None m (seg_rom asegs)).
End Fw.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac fw_ivs := unfold got_ssp, ssp_guard; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section FwriteCheck.
  Variables (rae sp gp tp s0e s1e s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (P n lo : Z).
  Variable Pc : mem -> Prop.
  Hypothesis HA : app_range P n.
  Hypothesis Hn : 0 < n < 2^31.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + AFWRITE_STACK <= bv_unsigned sp.
  Hypothesis PcT : forall mm mm', Pc mm -> munch [(bv_unsigned sp - 2128 - 80, bv_unsigned sp - 2128)] mm mm' -> wmono asegs mm mm' -> Pc mm'.

  Lemma RBv : 0 <= P /\ P + n + 8 <= 2^47.
  Proof. destruct HA as [(H1 & H2 & H3)|(H1 & H2 & H3)]; unfold KLOWSHADOW_BEG, KHIGHMEM_BEG, KHIGHMEM_END in *; lia. Qed.
  Lemma CEILv : alloc_ceiling = alloc_ceiling. Proof. reflexivity. Qed.
  Lemma STKv : AFWRITE_STACK = 2368. Proof. reflexivity. Qed.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR rae sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rae) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - AFWRITE_STACK, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ Pc m').
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"]
  Notation ST_ pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp (Z_to_bv 64 n)
            x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition afw_frame (mm : mem) : Prop :=
    mem_inv asegs mm /\ icpt_cells mm /\ stk asegs mm lo (bv_unsigned sp + -2128)
    /\ rw_cells asegs mm (bv_unsigned sp + -56) [C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae]
    /\ Pc mm
    /\ munch [(bv_unsigned sp - AFWRITE_STACK, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m mm /\ wmono asegs m mm
    /\ stk asegs mm (bv_unsigned sp + -2128) (bv_unsigned sp + -56)
    /\ shadow_ok mm P n.

  Ltac afw_intro AF := (nelim AF 9%nat; intros MI' IC' ST' FR' PC' MU' WM' ST2 SO).
  Ltac afw_pack := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); assumption.

  (* [comment removed for export] *)
  Lemma afw_after_callee : forall mm mm' k,
    icpt_cells mm -> Pc mm -> shadow_ok mm P n -> 0 <= k <= 80 ->
    munch [(bv_unsigned sp - 2128 - k, bv_unsigned sp - 2128)] mm mm' -> wmono asegs mm mm' ->
    icpt_cells mm' /\ Pc mm' /\ shadow_ok mm' P n.
  Proof.
    intros mm mm' k IC PCm SOm Hk MUr WMr. pose proof RBv as [R1 R2]. pose proof CEILv. pose proof STKv.
    split; [| split].
    - eapply icpt_cells_munch; [exact IC| exact MUr|]. unfold icpt_cell_ivs. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
    - eapply PcT; [exact PCm| | exact WMr]. eapply munch_weaken; [| exact MUr]. intros x Hx. cbn in Hx |- *. split; [lia| exact I].
    - eapply shadow_ok_munch_app; [exact SOm| exact MUr| lia| exact HA|].
      apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma afw_ret : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31,
    afw_frame mm ->
    evt asegs POST (ST_ 0x44a50 mm x1 x5 x6 x7 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. afw_intro AF.
    pose proof RBv as [R1 R2]. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    do 10 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with ST1 : stk asegs mm2 lo _ |- _ =>
      lazymatch goal with ST3 : stk asegs mm2 (bv_unsigned sp + -2128) _ |- _ =>
      lazymatch goal with FR3 : rw_cells asegs mm2 (bv_unsigned sp + -56) _ |- _ =>
        pose proof (stk_merge asegs mm2 _ _ _ ST1 ST3 ltac:(lia)) as STm;
        release_frame FR3 STm (bv_unsigned sp)
      end end end end.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma afw_region : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31,
    afw_frame mm ->
    evt asegs POST (ST_ 0x44b2c mm x1 x5 x6 x7 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. afw_intro AF.
    pose proof RBv as [R1 R2].
    pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof IC' as IC2. pose proof PC' as PC2. pose proof SO as SO2.
    pose proof (munch_refl [(bv_unsigned sp - 2128 - 80, bv_unsigned sp - 2128)] mm) as MU1. pose proof (wmono_refl asegs mm) as WM1.
    do 4 zstep.
    callsp region_is_poisoned_ok;
      [ exact IC' | exact MI' | exact ST' | exact CEIL | lia | reflexivity | reflexivity | lia
      | exact HA | exact SO | ].
    zstep. fold_lits. sh_if_true.
    zstep. zstep.
    apply afw_ret.
    lazymatch goal with |- afw_frame ?mm2 =>
      lazymatch goal with MUc : munch _ mm mm2 |- _ =>
      lazymatch goal with WMc : wmono asegs mm mm2 |- _ =>
        (nelim (afw_after_callee mm mm2 80 IC2 PC2 SO2 ltac:(lia) MUc WMc) 3%nat; intros IC3 PC3 SO3)
      end end end.
    afw_pack.
  Qed.

  (* [comment removed for export] *)
  Lemma afw_691fc : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31,
    afw_frame mm ->
    evt asegs POST (ST_ 0x44b24 mm x1 x5 x6 x7 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RBv as [R1 R2].
    zstep. zstep. if_cases Kc.
    - apply afw_ret. exact AF.
    - apply afw_region. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma afw_loop : forall mm (k : nat) (i : Z) x1 x5 x6 x7 (acc : word) x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31,
    afw_frame mm ->
    Z.to_nat (SH (P + n - 1) - SH P - i) = k -> 0 <= i -> SH P + i < SH (P + n - 1) ->
    evt asegs POST (ST_ 0x44b14 mm x1 x5 x6 x7 (Z_to_bv 64 1) (Z_to_bv 64 (2147450880 + P / 8 + i)) (Z_to_bv 64 (2147450880 + (P + n - 1) / 8))
                        acc x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm k. induction k as [|k IH]; intros i x1 x5 x6 x7 acc x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31 AF Hk Hi Hlt;
      pose proof RBv as [R1 R2];
      pose proof (SH_bounds P ltac:(lia)) as B1; pose proof (SH_bounds (P + n - 1) ltac:(lia)) as B2;
      unfold SH, SHADOW_OFFSET in *; [lia|].
    pose proof AF as AF'. afw_intro AF'.
    assert (V : exists b, mm (wa (2147450880 + P / 8 + i)) = Some b).
    { destruct (mm (wa (2147450880 + P / 8 + i))) as [b|] eqn:E; [exists b; reflexivity| exfalso].
      apply (proj2 SO (2147450880 + P / 8 + i)); [| exact E]. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    destruct V as [b RDb]. pose proof (vis_read1 mm _ b RDb) as RD. unfold wa in RD.
    zstep. zstep. zstep. zstep.
    if_cases Kc; zify_cond Kc.
    - replace (2147450880 + P / 8 + i + 1) with (2147450880 + P / 8 + (i + 1)) by lia.
      apply (IH (i + 1)); try assumption; lia.
    - replace (2147450880 + P / 8 + i + 1) with (2147450880 + (P + n - 1) / 8) by lia.
      apply afw_691fc. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma afw_slow : forall mm x1 x5 x6 x7 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31,
    afw_frame mm ->
    evt asegs POST (ST_ 0x44af8 mm x1 x5 x6 x7 (Z_to_bv 64 1) (Z_to_bv 64 (2147450880 + P / 8)) (Z_to_bv 64 (2147450880 + (P + n - 1) / 8))
                        (Z_to_bv 64 (P + n - 1)) x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RBv as [R1 R2].
    pose proof (SH_bounds P ltac:(lia)) as B1. pose proof (SH_bounds (P + n - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. afw_intro AF'.
    (nelim (shadow_ok_shb mm P n (n - 1) SO ltac:(lia)) 3%nat; intros ve SHE Ce).
    pose proof (shb_load_div' mm (P + (n - 1)) ve (P + n - 1) SHE ltac:(lia) ltac:(lia)) as RD.
    zstep. clear RD.
    rewrite (sxb_zb_small ve) by lia.
    do 5 zstep.
    zstep. if_cases Kc; zify_cond Kc.
    - apply afw_691fc. exact AF.
    - replace (2147450880 + P / 8) with (2147450880 + P / 8 + 0) by lia.
      eapply (afw_loop mm (Z.to_nat (SH (P + n - 1) - SH P - 0)) 0); try exact AF; unfold SH, SHADOW_OFFSET; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma afw_quick : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31,
    afw_frame mm -> n <= 64 ->
    evt asegs POST (ST_ 0x44a14 mm x1 x5 x6 x7 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF H64.
    pose proof RBv as [R1 R2].
    pose proof (SH_bounds P ltac:(lia)) as B1. pose proof (SH_bounds (P + n - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. afw_intro AF'.
    pose proof IC' as IC2. icpt_split IC2.
    do 9 zstep.
    rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
    replace (P + n + -1) with (P + n - 1) by lia.
    zstep. zstep. rewrite !land_m8 by lia.
    destruct (vis_read8 mm ((2147450880 + P / 8) / 8 * 8)) as (w1 & L1 & W1). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 SO). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    destruct (vis_read8 mm ((2147450880 + (P + n - 1) / 8) / 8 * 8)) as (w2 & L2 & W2). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 SO). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    unfold wa in W1, W2.
    step. step. clear W1 W2.
    zstep. step. if_cases Kc.
    - apply afw_slow. exact AF.
    - apply afw_ret. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma afw_check : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31,
    afw_frame mm ->
    evt asegs (fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
        ms' = MS (mkR rae sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc rae) fc None m' (seg_rom asegs)
        /\ munch [(bv_unsigned sp - AFWRITE_STACK, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m m'
        /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ Pc m')
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp (Z_to_bv 64 n)
              (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x449f0) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros AF. pose proof RBv as [R1 R2].
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    zstep. fold_lits. sh_if_false.             (* [comment removed for export] *)
    zstep. fold_lits. rewrite ?Z.mul_1_l, ?Z.mul_1_r.   (* [comment removed for export] *)
    zstep. fold_lits. rewrite (zb_lxor_ones P) by lia. zstep. zstep.
    zstep. if_cases Kc2; zify_cond Kc2; revert Kc2; rewrite ?unsigned_lit by lia; intros Kc2; try rewrite !Z.mod_small in Kc2 by lia.
    + exfalso. lia.
    + zstep. zstep. zstep. if_cases Kc3; zify_cond Kc3;
        change 18446744073709551615 with (Z.ones 64) in Kc3; rewrite Z.land_ones in Kc3 by lia.
      * (* [comment removed for export] *)
        zstep. if_cases Kc4; zify_cond Kc4; [apply afw_region; exact AF | exfalso; revert Kc4; rewrite ?unsigned_lit by lia; intros Kc4; lia].
      * apply afw_quick; [exact AF|].
        destruct (Z.lt_ge_cases n 65) as [Hl|Hg]; [lia| exfalso].
        rewrite Z.mod_small in Kc3 by lia. lia.
  Qed.
End FwriteCheck.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fwrite_icpt_ok {St : Type} : @fwrite_icpt_spec St.
Proof.
  unfold fwrite_icpt_spec. intros until s. intros TW IC RC MI SEF BYT HF LS -> -> -> ST CEIL SPB SEP1 SEP2 HA SOK SSP.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64) in RSP.
  assert (SE : AFWRITE_STACK = 2368) by reflexivity. pose proof CEIL as CE. try rewrite alloc_ceiling_lit in CE.
  pose proof (app_range_lt47 _ _ HA) as R47.
  pose proof (munch_refl [(bv_unsigned sp - AFWRITE_STACK, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m) as MUp.
  set (P := bv_unsigned a0) in *.
  assert (EA0 : a0 = Z_to_bv 64 P) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (conj IC (conj RC (conj SOK (conj SEF (conj BYT SSP))))) as PK.
  eapply (implM_evt asegs). 2:{ intros ms' H; exact H. } cbv beta.
  zstep.                                   (* [comment removed for export] *)
  carve_frame 56%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 14 zstep.
  (nelim PK 6%nat; intros IC0 RC0 SOK0 SEF0 BYT0 SSP0). try clear IC; try clear RC; try clear SOK; try clear SEF; try clear BYT; try clear SSP.
  zstep.                                   (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    assert (IC1 : icpt_cells m0)
      by (eapply icpt_cells_munch; [exact IC0| exact MU|]; unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil);
    destruct (stk_split asegs m0 lo (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ST ltac:(lia)) as [ST1 ST2]
  end.
  callsp try_init_ok; [exact IC1| assumption| exact ST1| exact CEIL| lia|].
  clear IC1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    assert (IC1 : icpt_cells m0)
      by (eapply icpt_cells_munch; [exact IC0| exact MU|]; unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil);
    assert (RC1 : ro_cells asegs m0 AREAL_FWRITE_SLOT [C8 (Z_to_bv 64 AMUSL_FWRITE)])
      by (eapply ro_cells_transport; [exact RC0| exact MU|]; unfold AREAL_FWRITE_SLOT; cbn; lia)
  end.
  unfold AREAL_FWRITE_SLOT, AMUSL_FWRITE in RC1.
  do 2 zstep.                              (* [comment removed for export] *)
  do 6 zstep.                              (* [comment removed for export] *)
  apply evt_done.
  (* [comment removed for export] *)
  lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (SEF1 : stderr_wfile0 m1)
      by (eapply stderr_wfile0_munch; [exact SEF0| exact MUp| exact WM| fw_ivs]);
    assert (HF1 : bytes_at asegs m1 P (zb s))
      by (eapply bytes_at_transport; [exact BYT0| exact MUp|]; cbn; rewrite ?zb_length'; unfold zlength in *; lia);
    assert (SSP1 : ssp_cells m1 canary)
      by (eapply ssp_cells_munch; [exact SSP0| exact MUp| exact WM| fw_ivs]);
    assert (SOK1 : shadow_ok m1 P (zlength s))
      by (eapply shadow_ok_munch_app; [exact SOK0| exact MUp| lia| exact HA|]; apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil]);
    (* [comment removed for export] *)
    lazymatch goal with STl : stk asegs m1 lo (bv_unsigned sp + -2128) |- _ =>
      destruct (stk_split asegs m1 lo (bv_unsigned sp - 2368) (bv_unsigned sp + -2128) STl ltac:(lia)) as [STlo SThi];
      assert (STc : stk asegs m1 (bv_unsigned sp - 2368) (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2128)))) by (rewrite unsigned_lit by lia; exact SThi)
    end
  end.
  pose proof (@fwrite_diag_proof St) as FWD. unfold fwrite_diag_stmt in FWD.
  eapply implM_post_evt''.
  { rewrite EA0. eapply FWD with (lo := bv_unsigned sp - 2368) (canary := canary);
      [ exact TW | exact SEF1 | rewrite unsigned_lit by lia; exact HF1 | exact HF | exact LS
      | reflexivity | reflexivity | reflexivity
      | exact STc | rewrite unsigned_lit by lia; unfold FWRITE_DEPTH; lia | unfold GLOBALS_TOP; lia
      | rewrite !unsigned_lit by lia; lia | rewrite unsigned_lit by lia; exact SEP2
      | exact SSP1 | assumption ]. }
  (* [comment removed for export] *)
  cbv beta. intros [] st2 ms' PO.
  (nelim PO 23%nat; intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 -> MUr WMr MI2 ST3 SEF2 SSP2 ->).
  rewrite unsigned_lit in MUr, ST3 by lia.
  replace (ret_pc (Z_to_bv 64 0x449ec)) with (Z_to_bv 64 0x449ec : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  lazymatch goal with FRx : rw_cells asegs ?mx (bv_unsigned sp + -56) _ |- _ =>
    lazymatch goal with STlo : stk asegs mx lo (bv_unsigned sp - 2368) |- _ =>
      assert (STlo2 : stk asegs m2 lo (bv_unsigned sp - 2368))
        by (eapply stk_transport_disjoint; [exact STlo| exact MUr| exact WMr| cbn; lia]);
      pose proof (stk_merge asegs m2 _ _ _ STlo2 ST3 ltac:(lia)) as ST3' end;
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact FRx| exact MUr| exact WMr| cbn; lia]);
    lazymatch goal with ST2x : stk asegs mx (bv_unsigned sp + -2128) (bv_unsigned sp + -56) |- _ =>
      assert (ST4 : stk asegs m2 (bv_unsigned sp + -2128) (bv_unsigned sp + -56))
        by (eapply stk_transport_disjoint; [exact ST2x| exact MUr| exact WMr| cbn; lia]) end;
    assert (MU2 : munch [(bv_unsigned sp - AFWRITE_STACK, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m m2)
      by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUr]; intros y Hy; cbn in Hy |- *; lia);
    assert (WM2 : wmono asegs m m2) by (eapply wmono_trans; [exact WM| exact WMr]);
    lazymatch goal with ICx : icpt_cells mx |- _ =>
      assert (IC2 : icpt_cells m2)
        by (eapply icpt_cells_munch; [exact ICx| exact MUr|]; unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil) end;
    lazymatch goal with SOx : shadow_ok mx P _ |- _ =>
      assert (SO2 : shadow_ok m2 P (zlength s))
        by (eapply shadow_ok_munch_app; [exact SOx| exact MUr| lia| exact HA|];
            apply Forall_cons; [apply app_iv_stack; lia| apply Forall_cons; [apply app_iv_img; unfold AIMG_HI; cbn; lia| apply Forall_nil]]) end
  end.
  zstep. fold_lits. sh_if_false.           (* [comment removed for export] *)
  eapply evt_mono.
  { apply (afw_check ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m P (zlength s) lo
             (fun mm => stderr_wfile0 mm /\ ssp_cells mm canary));
      [ exact HA | exact LS | exact CEIL | exact SPB
      | intros mm mm' [X1 X2] MUx WMx; split;
          [ eapply stderr_wfile0_munch; [exact X1| exact MUx| exact WMx| fw_ivs]
          | eapply ssp_cells_munch; [exact X2| exact MUx| exact WMx| fw_ivs] ]
      | ].
    split; [exact MI2|]. split; [exact IC2|]. split; [exact ST3'|]. split; [exact FR2|]. split; [split; [exact SEF2| exact SSP2]|].
    split; [exact MU2|]. split; [exact WM2|]. split; [exact ST4| exact SO2]. }
  cbv beta. intros ms2 nelH_; (nelim nelH_ 21%nat; intros w0 w1 w2 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 m3 -> MU3 WM3 MI3 ST5 [SEF3 SSP3]).
  unfold fwrite_icpt_post. exists w0, w1, w2, y1, y2, y3, y4, y5, y6, y7, w3, w4, w5, w6, m3.
  split; [reflexivity|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact ST5|].
  split; [exact SEF3|]. split; [exact SSP3| reflexivity].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Notation mem := (word -> option byte).
Ltac fw_ivs := unfold got_ssp, ssp_guard; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.
