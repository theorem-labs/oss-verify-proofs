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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RT_poison_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition poison_cells (m : word -> option byte) : Prop :=
  ro_cells asegs m 0xa9adc [C1 (Z_to_bv 8 1)]                  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1fa0 [C8 (Z_to_bv 64 0xa3e08)]       (* [comment removed for export] *)
  /\ ro_cells asegs m 0x13be20 [C8 (Z_to_bv 64 0xffffffffffffffff)]        (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1f60 [C8 (Z_to_bv 64 0x139d20)]       (* [comment removed for export] *)
  /\ ro_cells asegs m 0x139d20 [C8 (Z_to_bv 64 4096)]           (* [comment removed for export] *)
  /\ ro_cells asegs m 0x13be38 [C8 (Z_to_bv 64 0)]              (* [comment removed for export] *)
  /\ ro_cells asegs m 0x13be9c [C1 (Z_to_bv 8 1)]               (* [comment removed for export] *)
  /\ ro_cells asegs m 0x13be83 [C1 (Z_to_bv 8 1)]               (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1fc0 [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x13bd9c)]
                                                                (* [comment removed for export] *)
  /\ ro_cells asegs m 0x13bd9c [C4 (Z_to_bv 64 0)]             (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5fd510 [C8 (Z_to_bv 64 4096)]           (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa2c08 [C8 (Z_to_bv 64 0x5fd290)]       (* [comment removed for export] *)
  /\ (exists canary : word, ro_cells asegs m 0x5fd290 [C8 canary]).

Definition poison_cell_ivs : list (Z * Z) :=
  [(0xa1f60, 0xa1f68); (0xa1fa0, 0xa1fa8); (0xa1fc0, 0xa1fd0); (0xa2c08, 0xa2c10); (0xa9adc, 0xa9add);
   (0x139d20, 0x139d28); (0x13bd9c, 0x13bda0); (0x13be20, 0x13bea0); (0x5fd290, 0x5fd298); (0x5fd510, 0x5fd518)].

(* [comment removed for export] *)
Definition APOISON_STACK : Z := 1024.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition poison_shadow_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a sz v lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(SH a, SH a + sz / 8); (bv_unsigned sp - APOISON_STACK, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (SH a) [CB (Z.to_nat (sz / 8)) (repeat (Z_to_bv 8 v) (Z.to_nat (sz / 8)))]
    /\ stk asegs m' lo (bv_unsigned sp).

Definition poison_shadow_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a sz v lo : Z) (junk : list byte),
  icpt_cells m -> poison_cells m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + APOISON_STACK <= bv_unsigned sp ->
  a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 sz -> a2 = Z_to_bv 64 v ->
  a mod 8 = 0 -> sz mod 8 = 0 -> 8 <= sz -> app_range a sz -> 0 <= v < 256 ->
  (v = 0 -> sz / 8 < 0xffffffffffffffff) ->
  rw_cells asegs m (SH a) [CB (Z.to_nat (sz / 8)) junk] ->
  evt asegs (poison_shadow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a sz v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 APOISON_SHADOW) fc None m (seg_rom asegs)).

(* [comment removed for export] *)


End CeilWrap.
End RT_poison_iface.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module RT_poison3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison2 RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_mem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac poison_split PC :=
  let ca := fresh "canary" in
  (nelim PC 13%nat; intros CANP G50 CF120 G10 PSZ CF144 CF244 CF219 G70 DYING LPGSZ GSSP [ca SSP]).

Lemma poison_cells_munch : forall W m m',
  poison_cells m -> munch W m m' ->
  Forall (fun iv => disjoint_from W (fst iv) (snd iv - fst iv)) poison_cell_ivs ->
  poison_cells m'.
Proof.
  intros W m m' PC MU D. unfold poison_cell_ivs in D.
  pose proof (proj1 (Forall_forall _ _) D) as DF. cbn [fst snd] in DF.
  assert (D10 : disjoint_from W 0xa1f60 8) by (apply (DF (0xa1f60, 0xa1f68)); cbn; tauto).
  assert (D50 : disjoint_from W 0xa1fa0 8) by (apply (DF (0xa1fa0, 0xa1fa8)); cbn; tauto).
  assert (D70 : disjoint_from W 0xa1fc0 16) by (apply (DF (0xa1fc0, 0xa1fd0)); cbn; tauto).
  assert (D48 : disjoint_from W 0xa2c08 8) by (apply (DF (0xa2c08, 0xa2c10)); cbn; tauto).
  assert (DE4 : disjoint_from W 0xa9adc 1) by (apply (DF (0xa9adc, 0xa9add)); cbn; tauto).
  assert (D20 : disjoint_from W 0x139d20 8) by (apply (DF (0x139d20, 0x139d28)); cbn; tauto).
  assert (D9C : disjoint_from W 0x13bd9c 4) by (apply (DF (0x13bd9c, 0x13bda0)); cbn; tauto).
  assert (DCF : disjoint_from W 0x13be20 0x80) by (apply (DF (0x13be20, 0x13bea0)); cbn; tauto).
  assert (DC70 : disjoint_from W 0x5fd290 8) by (apply (DF (0x5fd290, 0x5fd298)); cbn; tauto).
  assert (DEF0 : disjoint_from W 0x5fd510 8) by (apply (DF (0x5fd510, 0x5fd518)); cbn; tauto).
  poison_split PC.
  unfold poison_cells.
  Ltac tr H D := eapply ro_cells_transport; [exact H| eassumption| eapply disjoint_from_sub; [exact D| cbn; lia| cbn; lia]].
  split; [tr CANP DE4|]. split; [tr G50 D50|]. split; [tr CF120 DCF|]. split; [tr G10 D10|]. split; [tr PSZ D20|].
  split; [tr CF144 DCF|]. split; [tr CF244 DCF|]. split; [tr CF219 DCF|]. split; [tr G70 D70|].
  split; [tr DYING D9C|]. split; [tr LPGSZ DEF0|]. split; [tr GSSP D48|]. exists canary. tr SSP DC70.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma psh_CEILv : alloc_ceiling = alloc_ceiling. Proof. reflexivity. Qed.
Lemma psh_STKv : APOISON_STACK = 1024. Proof. reflexivity. Qed.
Lemma psh_SHB : forall a sz, app_range a sz -> 2147450880 <= SH a /\ SH a + sz / 8 <= 0x10007fff8000.
Proof. intros a sz AR. pose proof (app_range_lt47 a sz AR). rewrite SH_def. unfold SHADOW_OFFSET. Z.div_mod_to_equations. lia. Qed.
Lemma psh_SHR1 : forall a, 0 <= a -> Z.shiftr a 3 = a / 8.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma psh_SHR2 : forall a sz, 0 <= a -> 8 <= sz -> a mod 8 = 0 -> sz mod 8 = 0 -> Z.shiftr (a + sz + -8) 3 = a / 8 + sz / 8 - 1.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. Qed.
Lemma psh_BEG_eq : forall a, 2147450880 + Z.shiftr a 3 = SH a.
Proof. intros. rewrite <- SH_shiftr. lia. Qed.

Section PoisonShadowPrefix.
  Variables (rae sp gp tp s0e s1e s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m m1 : word -> option byte) (a sz v lo : Z) (junk : list byte).
  Hypothesis A8 : a mod 8 = 0.
  Hypothesis SZ8 : sz mod 8 = 0.
  Hypothesis SZ : 8 <= sz.
  Hypothesis AR : app_range a sz.
  Hypothesis HV : 0 <= v < 256.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + APOISON_STACK <= bv_unsigned sp.

  Variable POST : machine_state -> Prop.
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"]
  Notation ST_ pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9
            x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition psh_frame (mm : word -> option byte) : Prop :=
    mem_inv asegs mm /\ icpt_cells mm /\ poison_cells mm /\ stk asegs mm lo (bv_unsigned sp + -56)
    /\ rw_cells asegs mm (bv_unsigned sp + -56) [C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae]
    /\ rw_cells asegs mm (SH a) [CB (Z.to_nat (sz / 8)) junk]
    /\ munch [(SH a, SH a + sz / 8); (bv_unsigned sp - APOISON_STACK, bv_unsigned sp)] m mm /\ wmono asegs m mm.

  Ltac psh_intro AF := destruct AF as (MI' & IC' & PC' & ST' & FR' & SHA' & MU' & WM'). (* [comment removed for export] *)
  Ltac psh_prep :=
    pose proof (app_range_lt47 a sz AR) as RB; pose proof psh_CEILv as CE; pose proof psh_STKv as SE;
    pose proof (psh_SHB a sz AR) as SB8; pose proof (bv_unsigned_in_range 64 sp) as RSP.

  Hypothesis AF1 : psh_frame m1.
  (* [comment removed for export] *)
  Hypothesis K28 : forall x1 x5 x6 x7 x8 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x55900 m1 x1 x5 x6 x7 x8 (Z_to_bv 64 2147450880) (Z_to_bv 64 a) (Z_to_bv 64 (a + sz + -8)) (Z_to_bv 64 v)
                        x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma psh_F : forall x1 x5 x6 x7 x8 x13 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x558ac m1 x1 x5 x6 x7 x8 (Z_to_bv 64 2147450880) (Z_to_bv 64 a) (Z_to_bv 64 sz) (Z_to_bv 64 v)
                        x13 (Z_to_bv 64 2147450879) x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros. psh_prep. psh_intro AF1. pose proof IC' as IC2. icpt_split IC'. poison_split PC'.
    zstep. zstep. fold_lits. sh_if_false.
    do 3 zstep. fold_lits.
    destruct AR as [LOW|HI].
    - unfold lowmem_range, KLOWSHADOW_BEG in LOW. sh_if_true. apply K28.
    - unfold highmem_range, KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END in HI. sh_if_false.
      do 8 zstep. fold_lits. sh_if_true.
      do 6 zstep. fold_lits. sh_if_false.
      zstep. fold_lits. sh_if_false.
      apply K28.
  Qed.

  (* [comment removed for export] *)
  Lemma psh_A : forall x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x556b0 m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 a) (Z_to_bv 64 sz) (Z_to_bv 64 v)
                        x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros. psh_prep. psh_intro AF1. pose proof IC' as IC2. icpt_split IC'. poison_split PC'.
    zstep. zstep. sh_if_false.
    do 8 zstep. fold_lits.
    destruct AR as [LOW|HI].
    - unfold lowmem_range, KLOWSHADOW_BEG in LOW. sh_if_true. apply psh_F.
    - unfold highmem_range, KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END in HI. sh_if_false.
      do 8 zstep. fold_lits. sh_if_true.
      do 6 zstep. fold_lits. sh_if_false.
      zstep. fold_lits. sh_if_true.
      do 4 zstep. fold_lits. sh_if_false.
      zstep. fold_lits. sh_if_true.
      apply psh_F.
  Qed.

  (* [comment removed for export] *)
  Lemma psh_body : forall x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x5569c m1 rae x5 x6 x7 s0e s1e (Z_to_bv 64 a) (Z_to_bv 64 sz) (Z_to_bv 64 v) x13 x14 x15 x16 x17
                        s2e s3e s4e s5e x28 x29 x30 x31).
  Proof.
    intros. psh_prep. pose proof AF1 as AF. psh_intro AF. pose proof IC' as IC2. icpt_split IC'. poison_split PC'.
    zstep. if_cases K; zify_cond K.
    - apply psh_A.
    - do 3 zstep. fold_lits. zstep. sh_if_false. apply psh_A.
  Qed.
End PoisonShadowPrefix.

(* [comment removed for export] *)
Lemma psh_prologue :
  forall (rae sp gp tp t0 t1 t2 s0e s1e a0 a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a sz lo : Z) (junk : list byte)
         (POST : machine_state -> Prop),
  icpt_cells m -> poison_cells m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + APOISON_STACK <= bv_unsigned sp ->
  0 <= a /\ a + sz < 2^47 -> 0 <= sz ->
  rw_cells asegs m (SH a) [CB (Z.to_nat (sz / 8)) junk] ->
  (forall m1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
     psh_frame rae sp s0e s1e s2e s3e s4e s5e m a sz lo junk m1 ->
     evt asegs POST (MS (mkR rae (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 s0e s1e a0 a1 a2 x13 x14 x15 x16 x17
                             s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x5569c) fc None m1 (seg_rom asegs))) ->
  evt asegs POST (MS (mkR rae sp gp tp t0 t1 t2 s0e s1e a0 a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 APOISON_SHADOW) fc None m (seg_rom asegs)).
Proof.
  intros until POST. intros IC PC MI ST CEIL SPB RB HSZ SHA K.
  pose proof (bv_unsigned_in_range 64 sp) as RSP.
  pose proof psh_STKv as SE.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  assert (SB8 : 2147450880 <= SH a /\ SH a + sz / 8 <= 0x10007fff8000)
    by (rewrite SH_def; unfold SHADOW_OFFSET; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(SH a, SH a + sz / 8); (bv_unsigned sp - APOISON_STACK, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (conj IC PC) as PK.
  unfold APOISON_SHADOW.
  carve_frame 56%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 8 zstep.
  destruct PK as [IC0 PC0]. clear IC PC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (IC1 : icpt_cells mm)
      by (eapply icpt_cells_munch; [exact IC0| exact MU|];
          unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil);
    assert (PC1 : poison_cells mm)
      by (eapply poison_cells_munch; [exact PC0| exact MU|];
          unfold poison_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil)
  end.
  eapply K.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PoisonShadowMemset.
  Variables (rae sp gp tp s0e s1e s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m m1 : word -> option byte) (a sz v lo : Z) (junk : list byte).
  Hypothesis A8 : a mod 8 = 0.
  Hypothesis SZ8 : sz mod 8 = 0.
  Hypothesis SZ : 8 <= sz.
  Hypothesis AR : app_range a sz.
  Hypothesis HV : 0 <= v < 256.
  Hypothesis THR : v = 0 -> sz / 8 < 0xffffffffffffffff.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + APOISON_STACK <= bv_unsigned sp.
  Hypothesis AF1 : psh_frame rae sp s0e s1e s2e s3e s4e s5e m a sz lo junk m1.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (poison_shadow_post rae sp gp tp s0e s1e s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 F fc a sz v lo m).
  #[warnings="-notation-for-abbreviation"]
  Notation ST_ pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9
            x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Ltac psh_prep :=
    pose proof (app_range_lt47 a sz AR) as RB; pose proof psh_CEILv as CE; pose proof psh_STKv as SE;
    pose proof (psh_SHB a sz AR) as SB8; pose proof (bv_unsigned_in_range 64 sp) as RSP.
  Ltac psh_intro AF := destruct AF as (MI' & IC' & PC' & ST' & FR' & SHA' & MU' & WM'). (* [comment removed for export] *)

  Lemma LEN_eq : Z.shiftr (a + sz + -8) 3 + 1 - Z.shiftr a 3 = sz / 8.
  Proof. pose proof (app_range_lt47 a sz AR). rewrite psh_SHR2, psh_SHR1 by lia. lia. Qed.

  (* [comment removed for export] *)
  Lemma psh_tail : forall x1 x5 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x559f4 m1 x1 x5 (Z_to_bv 64 0x9b5f4) x7 (Z_to_bv 64 (sz / 8)) x9
                        (Z_to_bv 64 (SH a)) (Z_to_bv 64 v) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof using A8 AF1 AR CEIL HV SPB SZ SZ8 THR. (* [comment removed for export] *)
    intros. psh_prep. psh_intro AF1. pose proof IC' as IC2. icpt_split IC'.
    assert (RN : 0 <= sz / 8 < 2^44) by (Z.div_mod_to_equations; lia).
    do 10 zstep.
    release_frame FR' ST' (bv_unsigned sp).
    call memset_callv; [exact SHA'| lia| lia| lia| exact MI'|].
    rewrite (Z.mod_small v 256) in * by lia.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma psh_I : forall x1 x5 x6 x7 x8 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x55900 m1 x1 x5 x6 x7 x8 (Z_to_bv 64 2147450880) (Z_to_bv 64 a) (Z_to_bv 64 (a + sz + -8)) (Z_to_bv 64 v)
                        x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros. psh_prep. psh_intro AF1. pose proof IC' as IC2. icpt_split IC'. poison_split PC'.
    pose proof (psh_SHR1 a ltac:(lia)) as E1. pose proof (psh_SHR2 a sz ltac:(lia) SZ A8 SZ8) as E2.
    assert (B1 : 0 <= Z.shiftr a 3 < 2^44) by (rewrite E1; Z.div_mod_to_equations; lia).
    assert (B2 : 0 <= Z.shiftr (a + sz + -8) 3 < 2^44) by (rewrite E2; Z.div_mod_to_equations; lia).
    do 4 zstep. fold_lits. sh_if_false.
    do 5 zstep.
    rewrite psh_BEG_eq, LEN_eq.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) zstep. zstep. apply psh_tail.
    - (* [comment removed for export] *)
      assert (TH : sz / 8 < 0xffffffffffffffff) by (apply THR; lia).
      do 4 zstep. fold_lits. sh_if_true.
      zstep. zstep. replace (Z_to_bv 64 0) with (Z_to_bv 64 v) by (f_equal; lia). apply psh_tail.
  Qed.
End PoisonShadowMemset.

Lemma poison_shadow_ok : poison_shadow_spec.
Proof.
  unfold poison_shadow_spec.
  intros until junk. intros IC PC MI ST CEIL SPB -> -> -> A8 SZ8 SZ AR HV THR SHA.
  pose proof (app_range_lt47 a sz AR) as RB.
  eapply psh_prologue; try eassumption; try lia.
  intros m1. intros. eapply psh_body; try eassumption.
  intros. eapply psh_I; eassumption.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac poison_split PC :=
  let ca := fresh "canary" in
  (nelim PC 13%nat; intros CANP G50 CF120 G10 PSZ CF144 CF244 CF219 G70 DYING LPGSZ GSSP [ca SSP]).
End RT_poison3.

(* [comment removed for export] *)
Module RT_poison4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison2 RT_poison_iface RT_poison3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AGETMMAPGRAN : Z := 0x676f0.

Lemma getmmapgran_ok :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  poison_cells m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 544 <= bv_unsigned sp ->
  evt asegs (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
               ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4096) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom asegs)
               /\ munch [(bv_unsigned sp - 544, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
               /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AGETMMAPGRAN) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros PC MI ST CEIL SPB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  poison_split PC. unfold AGETMMAPGRAN.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 3 zstep.
  (* [comment removed for export] *)
  do 4 zstep.
  do 7 zstep. fold_lits. sh_if_false.
  do 6 zstep. fold_lits. sh_if_false.
  do 2 zstep. fold_lits. sh_if_false.
  do 3 zstep. fold_lits. sh_if_false.
  do 2 zstep. fold_lits. sh_if_true.
  do 4 zstep. fold_lits. sh_if_false.
  do 9 zstep. fold_lits.
  do 3 zstep.
  do 3 zstep. rewrite bv_eqb_refl. cbn [negb].
  do 5 zstep.
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dec_total_mmap_ok :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  icpt_cells m -> poison_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m (seg_rom asegs)
                        /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x61f3c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros IC PC MI. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  icpt_split IC. poison_split PC.
  do 3 zstep. fold_lits. zstep. sh_if_true. zstep.
  apply evt_done. split; [reflexivity| auto].
Qed.

Lemma inc_total_mmap_ok :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  icpt_cells m -> poison_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m (seg_rom asegs)
                        /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x61ef8) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros IC PC MI. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  icpt_split IC. poison_split PC.
  do 3 zstep. fold_lits. zstep. sh_if_true. zstep.
  apply evt_done. split; [reflexivity| auto].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma getnamedfd_null_ok :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 272 <= bv_unsigned sp ->
  evt asegs (fun ms' => exists (m' : word -> option byte),
               ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom asegs)
               /\ munch [(bv_unsigned sp - 272, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
               /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x683dc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST CEIL SPB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 56%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 10 zstep. fold_lits. zstep. sh_if_true.
  do 10 zstep.
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.


End CeilWrap.
End RT_poison4.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow ICPT_iface RT_poison RT_poison2.
Import RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_memset ICPT_mem.
Import RT_poison3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac poison_split PC :=
  let ca := fresh "canary" in
  destruct PC as (CANP & G50 & CF120 & G10 & PSZ & CF144 & CF244 & CF219 & G70 & DYING & LPGSZ & GSSP & [ca SSP]).

Lemma rw_cells_CB_nil : forall segs mm A, 0 <= A -> A <= 2^64 -> rw_cells segs mm A [CB 0%nat []].
Proof.
  intros segs mm A H1 H2. split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [cells_size Cells.csize Nat.add]. split; [lia|]. split; [cbn; lia|]. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
Definition pz_range (a : Z) : Prop :=
  (8 <= a /\ a <= KLOWSHADOW_BEG) \/ (KHIGHMEM_BEG + 8 <= a /\ a + 8 <= KHIGHMEM_END).

Definition poison_shadow_zero_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - APOISON_STACK, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition poison_shadow_zero_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a v lo : Z),
  icpt_cells m -> poison_cells m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + APOISON_STACK <= bv_unsigned sp ->
  a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 v ->
  a mod 8 = 0 -> pz_range a -> 0 < v < 256 ->
  evt asegs (poison_shadow_zero_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 APOISON_SHADOW) fc None m (seg_rom asegs)).

Section PoisonShadowZero.
  Variables (rae sp gp tp s0e s1e s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m m1 : word -> option byte) (a v lo : Z).
  Hypothesis A8 : a mod 8 = 0.
  Hypothesis HRG : pz_range a.
  Hypothesis HV : 0 < v < 256.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + APOISON_STACK <= bv_unsigned sp.
  Hypothesis AF1 : psh_frame rae sp s0e s1e s2e s3e s4e s5e m a 0 lo [] m1.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (poison_shadow_zero_post rae sp gp tp s0e s1e s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 F fc lo m).
  #[warnings="-notation-for-abbreviation"]
  Notation ST_ pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9
            x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Ltac psh_prep :=
    pose proof psh_CEILv as CE; pose proof psh_STKv as SE; pose proof (bv_unsigned_in_range 64 sp) as RSP;
    pose proof HRG as HRGl; unfold pz_range, KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END in HRGl.
  Ltac psh_intro AF := destruct AF as (MI' & IC' & PC' & ST' & FR' & SHA' & MU' & WM').

  (* [comment removed for export] *)
  Lemma pz_tail : forall x1 x5 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x559f4 m1 x1 x5 (Z_to_bv 64 0x9b5f4) x7 (Z_to_bv 64 0) x9
                        (Z_to_bv 64 (SH a)) (Z_to_bv 64 v) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros. psh_prep. psh_intro AF1. pose proof IC' as IC2. icpt_split IC'.
    pose proof SHA' as SHA2. change (Z.to_nat (0 / 8)) with 0%nat in SHA2.
    assert (SB : 2147450880 <= SH a /\ SH a + 8 <= 17594333528064) by (rewrite SH_def; unfold SHADOW_OFFSET; Z.div_mod_to_equations; lia).
    do 10 zstep.
    release_frame FR' ST' (bv_unsigned sp).
    call memset_callv; [exact SHA2| lia| lia| lia| exact MI'|].
    apply evt_done. unfold poison_shadow_zero_post. do 16 eexists. split; [reflexivity|].
    split. { eapply munch_weaken; [| eassumption]. unfold sub_fp; cbn; intros; lia. }
    split; [assumption|]. split; [assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  Lemma pz_I : forall x1 x5 x6 x7 x8 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x55900 m1 x1 x5 x6 x7 x8 (Z_to_bv 64 2147450880) (Z_to_bv 64 a) (Z_to_bv 64 (a + -8)) (Z_to_bv 64 v)
                        x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros. psh_prep. psh_intro AF1. pose proof IC' as IC2. icpt_split IC'. poison_split PC'.
    pose proof (psh_SHR1 a ltac:(lia)) as E1.
    assert (E2 : Z.shiftr (a + -8) 3 = a / 8 - 1) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (B1 : 0 <= Z.shiftr a 3 < 2^44) by (rewrite E1; Z.div_mod_to_equations; lia).
    assert (B2 : 0 <= Z.shiftr (a + -8) 3 < 2^44) by (rewrite E2; Z.div_mod_to_equations; lia).
    do 4 zstep. fold_lits. sh_if_false.
    do 5 zstep.
    rewrite psh_BEG_eq. replace (Z.shiftr (a + -8) 3 + 1 - Z.shiftr a 3) with 0 by lia.
    zstep. if_cases K; zify_cond K; [| exfalso; lia].
    zstep. zstep. apply pz_tail.
  Qed.

  (* [comment removed for export] *)
  Lemma pz_F : forall x1 x5 x6 x7 x8 x13 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x558ac m1 x1 x5 x6 x7 x8 (Z_to_bv 64 2147450880) (Z_to_bv 64 a) (Z_to_bv 64 0) (Z_to_bv 64 v)
                        x13 (Z_to_bv 64 2147450879) x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros. psh_prep. psh_intro AF1. pose proof IC' as IC2. icpt_split IC'. poison_split PC'.
    zstep. zstep. fold_lits. sh_if_false.
    do 3 zstep. fold_lits.
    destruct HRGl as [LOW|HI].
    - sh_if_true. apply pz_I.
    - sh_if_false.
      do 8 zstep. fold_lits. sh_if_true.
      do 6 zstep. fold_lits. sh_if_false.
      zstep. fold_lits. sh_if_false.
      apply pz_I.
  Qed.

  (* [comment removed for export] *)
  Lemma pz_A : forall x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x556b0 m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 a) (Z_to_bv 64 0) (Z_to_bv 64 v)
                        x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros. psh_prep. psh_intro AF1. pose proof IC' as IC2. icpt_split IC'. poison_split PC'.
    zstep. zstep. sh_if_false.
    do 8 zstep. fold_lits.
    destruct HRGl as [LOW|HI].
    - sh_if_true. apply pz_F.
    - sh_if_false.
      do 8 zstep. fold_lits. sh_if_true.
      do 6 zstep. fold_lits. sh_if_false.
      zstep. fold_lits. sh_if_true.
      do 4 zstep. fold_lits. sh_if_false.
      zstep. fold_lits. sh_if_true.
      apply pz_F.
  Qed.

  (* [comment removed for export] *)
  Lemma pz_body : forall x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x5569c m1 rae x5 x6 x7 s0e s1e (Z_to_bv 64 a) (Z_to_bv 64 0) (Z_to_bv 64 v) x13 x14 x15 x16 x17
                        s2e s3e s4e s5e x28 x29 x30 x31).
  Proof.
    intros. psh_prep. pose proof AF1 as AF. psh_intro AF. pose proof IC' as IC2. icpt_split IC'. poison_split PC'.
    zstep. if_cases K; zify_cond K; [exfalso; lia|].
    do 3 zstep. fold_lits. zstep. sh_if_false. apply pz_A.
  Qed.
End PoisonShadowZero.

Lemma poison_shadow_zero_ok : poison_shadow_zero_spec.
Proof.
  unfold poison_shadow_zero_spec.
  intros until lo. intros IC PC MI ST CEIL SPB -> -> -> A8 HA HV.
  pose proof HA as HAl. unfold pz_range, KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END in HAl.
  assert (SHA : rw_cells asegs m (SH a) [CB (Z.to_nat (0 / 8)) []]).
  { change (Z.to_nat (0 / 8)) with 0%nat. apply rw_cells_CB_nil; rewrite SH_def; unfold SHADOW_OFFSET; Z.div_mod_to_equations; lia. }
  eapply psh_prologue; try eassumption; try lia.
  intros m1. intros. eapply pz_body; try eassumption.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac poison_split PC :=
  let ca := fresh "canary" in
  destruct PC as (CANP & G50 & CF120 & G10 & PSZ & CF144 & CF244 & CF219 & G70 & DYING & LPGSZ & GSSP & [ca SSP]).
