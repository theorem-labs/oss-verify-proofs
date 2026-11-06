(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow ICPT_iface RT_poison RT_poison2 ICPT_mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_str3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_str3.ICPT_str.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_musl F_syscalls.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AREAD_T : Z := 0x4251c.          (* [comment removed for export] *)
Definition AREAD_ICPT : Z := 0x4474c.
Definition AREAD_STACK : Z := 2208.        (* [comment removed for export] *)
Definition AREAL_READ_SLOT : Z := 0xa3440. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition read_icpt_cells (m : word -> option byte) : Prop :=
  ro_cells bsegs m AREAL_READ_SLOT [C8 (Z_to_bv 64 read_entry)].

Definition read_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - AREAD_STACK, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells bsegs m' B [CB n junk]
                    /\ rw_cells bsegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells bsegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells bsegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

(* [comment removed for export] *)
Definition RS_LO : Z := 0x5cc010.
Definition RS_HI : Z := 0x5dc010.
Definition stage_range (a n : Z) : Prop := RS_LO <= a /\ 0 <= n /\ a + n <= RS_HI.
Definition read_icpt_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         (fd count : Z) (junk : list byte) (errv : word) (lo : Z),
  icpt_cells m -> read_icpt_cells m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AREAD_STACK <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells bsegs m (errno_addr tp) [C4 errv] ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count -> tp = Z_to_bv 64 ATP ->
  (3 <= fd < 2^32)%Z -> (0 < count < 2^40)%Z ->
  stage_range (bv_unsigned a1) count -> shadow_ok m (bv_unsigned a1) count ->
  bv_unsigned a1 + count <= lo ->
  impl bsegs (at_node bsegs) (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
       (epost (read_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 AREAD_T) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Section ReadIcpt.
  Variables (rae sp gp tp s0e s1e s2e s3e s4e s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (B cnt lo : Z).
  (* [comment removed for export] *)
  Variable Pc : (word -> option byte) -> Prop.
  Variable res : Z.     (* [comment removed for export] *)
  Hypothesis HB : stage_range B cnt.
  Hypothesis Hcnt : 0 < cnt < 2^40.
  Hypothesis Hres : -1 <= res <= cnt.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + AREAD_STACK <= bv_unsigned sp.
  Hypothesis PcT : forall mm mm', Pc mm -> munch [(bv_unsigned sp - 2128 - 80, bv_unsigned sp - 2128)] mm mm' -> wmono bsegs mm mm' -> Pc mm'.

  Lemma RBv : RS_LO <= B /\ B + cnt <= RS_HI. Proof. destruct HB as (H1 & _ & H2). split; assumption. Qed.
  Lemma CEILv : alloc_ceiling = alloc_ceiling. Proof. reflexivity. Qed.
  Lemma STKv : AREAD_STACK = 2208. Proof. reflexivity. Qed.
  Lemma ARres : 0 < res -> app_range B res.
  Proof. intros H. left. destruct HB as (H1 & H2 & H3). unfold lowmem_range, KLOWSHADOW_BEG, RS_LO, RS_HI in *. lia. Qed.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR rae sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rae) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - AREAD_STACK, bv_unsigned sp); (B, B + cnt); (bv_unsigned tp + -164, bv_unsigned tp + -160)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp) /\ Pc m').
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"]
  Notation ST_ pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9
            x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Definition ard_frame (mm : word -> option byte) : Prop :=
    mem_inv bsegs mm /\ icpt_cells mm /\ stk bsegs mm lo (bv_unsigned sp + -2128)
    /\ rw_cells bsegs mm (bv_unsigned sp + -48) [C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae]
    /\ Pc mm
    /\ munch [(bv_unsigned sp - AREAD_STACK, bv_unsigned sp); (B, B + cnt); (bv_unsigned tp + -164, bv_unsigned tp + -160)]%Z m mm /\ wmono bsegs m mm
    /\ stk bsegs mm (bv_unsigned sp + -2128) (bv_unsigned sp + -48)
    /\ (0 < res -> shadow_ok mm B res).

  Ltac lit_cond Kc := revert Kc; rewrite ?unsigned_lit by lia; intros Kc; try rewrite !Z.mod_small in Kc by lia.
  Ltac ard_intro AF := destruct AF as (MI' & IC' & ST' & FR' & PC' & MU' & WM' & ST2 & SO).
  Ltac ard_pack := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); assumption.

  (* [comment removed for export] *)
  Lemma ard_after_callee : forall mm mm' k,
    icpt_cells mm -> Pc mm -> (0 < res -> shadow_ok mm B res) -> 0 <= k <= 80 ->
    munch [(bv_unsigned sp - 2128 - k, bv_unsigned sp - 2128)] mm mm' -> wmono bsegs mm mm' ->
    icpt_cells mm' /\ Pc mm' /\ (0 < res -> shadow_ok mm' B res).
  Proof.
    intros mm mm' k IC PCm SOm Hk MUr WMr. pose proof RBv as [R1 R2]. pose proof CEILv. pose proof STKv.
    unfold RS_LO, RS_HI in R1, R2.
    split; [| split].
    - eapply icpt_cells_munch; [exact IC| exact MUr|]. unfold icpt_cell_ivs. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
    - eapply PcT; [exact PCm| | exact WMr]. eapply munch_weaken; [| exact MUr]. intros x Hx. cbn in Hx |- *. split; [lia| exact I].
    - intros HR. eapply shadow_ok_munch_app; [exact (SOm HR)| exact MUr| exact HR| exact (ARres HR)|].
      apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma ard_ret : forall mm x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    ard_frame mm ->
    evt bsegs POST (ST_ 0x447fc mm x1 x5 x6 x7 x9 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. ard_intro AF.
    pose proof RBv as [R1 R2]. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    do 9 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with ST1 : stk bsegs mm2 lo _ |- _ =>
      lazymatch goal with ST3 : stk bsegs mm2 (bv_unsigned sp + -2128) _ |- _ =>
      lazymatch goal with FR3 : rw_cells bsegs mm2 (bv_unsigned sp + -48) _ |- _ =>
        pose proof (stk_merge bsegs mm2 _ _ _ ST1 ST3 ltac:(lia)) as STm;
        release_frame FR3 STm (bv_unsigned sp)
      end end end end.
    finish.
  Qed.
  (* [comment removed for export] *)
  Lemma ard_region : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    ard_frame mm -> 0 < res ->
    evt bsegs POST (ST_ 0x44898 mm x1 x5 x6 x7 (Z_to_bv 64 B) (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF HR. ard_intro AF.
    pose proof RBv as [R1 R2]. unfold RS_LO, RS_HI in R1, R2.
    pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof IC' as IC2. pose proof PC' as PC2. pose proof SO as SO2.
    pose proof (munch_refl [(bv_unsigned sp - 2128 - 80, bv_unsigned sp - 2128)] mm) as MU1. pose proof (wmono_refl bsegs mm) as WM1.
    do 4 zstep.
    callsp region_is_poisoned_ok;
      [ exact IC' | exact MI' | exact ST' | exact CEIL | lia | reflexivity | reflexivity | lia
      | exact (ARres HR) | exact (SO HR) | ].
    zstep. zstep. zstep. fold_lits. sh_if_true.
    apply ard_ret.
    lazymatch goal with |- ard_frame ?mm2 =>
      lazymatch goal with MUc : munch _ mm mm2 |- _ =>
      lazymatch goal with WMc : wmono bsegs mm mm2 |- _ =>
        destruct (ard_after_callee mm mm2 80 IC2 PC2 SO2 ltac:(lia) MUc WMc) as (IC3 & PC3 & SO3)
      end end end.
    ard_pack.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_683d8 : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    ard_frame mm -> 0 < res ->
    evt bsegs POST (ST_ 0x44970 mm x1 x5 x6 x7 (Z_to_bv 64 B) (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF HR. pose proof RBv as [R1 R2].
    zstep. zstep. if_cases Kc.
    - apply ard_ret. exact AF.
    - zstep. apply ard_region; [exact AF| exact HR].
  Qed.

  (* [comment removed for export] *)
  Lemma ard_loop : forall mm (k : nat) (i : Z) x1 x5 x6 x7 (acc : word) x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    ard_frame mm -> 0 < res ->
    Z.to_nat (SH (B + res - 1) - SH B - i) = k -> 0 <= i -> SH B + i < SH (B + res - 1) ->
    evt bsegs POST (ST_ 0x44960 mm x1 x5 x6 x7 (Z_to_bv 64 B) (Z_to_bv 64 res) (Z_to_bv 64 (2147450880 + B / 8 + i)) (Z_to_bv 64 (2147450880 + (B + res - 1) / 8))
                        acc x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros mm k. induction k as [|k IH]; intros i x1 x5 x6 x7 acc x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 AF HR Hk Hi Hlt;
      pose proof RBv as [R1 R2]; unfold RS_LO, RS_HI in R1, R2;
      pose proof (SH_bounds B ltac:(lia)) as B1; pose proof (SH_bounds (B + res - 1) ltac:(lia)) as B2;
      unfold SH, SHADOW_OFFSET in *; [lia|].
    pose proof AF as AF'. ard_intro AF'.
    assert (V : exists b, mm (wa (2147450880 + B / 8 + i)) = Some b).
    { destruct (mm (wa (2147450880 + B / 8 + i))) as [b|] eqn:E; [exists b; reflexivity| exfalso].
      apply (proj2 (SO HR) (2147450880 + B / 8 + i)); [| exact E]. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    destruct V as [b RDb]. pose proof (vis_read1 mm _ b RDb) as RD. unfold wa in RD.
    zstep. zstep. zstep. zstep.
    if_cases Kc; zify_cond Kc.
    - replace (2147450880 + B / 8 + i + 1) with (2147450880 + B / 8 + (i + 1)) by lia.
      apply (IH (i + 1)); try assumption; lia.
    - replace (2147450880 + B / 8 + i + 1) with (2147450880 + (B + res - 1) / 8) by lia.
      apply ard_683d8; [exact AF| exact HR].
  Qed.

  (* [comment removed for export] *)
  Lemma ard_slow : forall mm x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    ard_frame mm -> 0 < res ->
    evt bsegs POST (ST_ 0x44944 mm x1 x5 x6 x7 (Z_to_bv 64 B) (Z_to_bv 64 res) (Z_to_bv 64 (2147450880 + B / 8)) (Z_to_bv 64 (2147450880 + (B + res - 1) / 8))
                        (Z_to_bv 64 (B + res - 1)) x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF HR. pose proof RBv as [R1 R2]. unfold RS_LO, RS_HI in R1, R2.
    pose proof (SH_bounds B ltac:(lia)) as B1. pose proof (SH_bounds (B + res - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. ard_intro AF'.
    destruct (shadow_ok_shb mm B res (res - 1) (SO HR) ltac:(lia)) as (ve & SHE & Ce).
    pose proof (shb_load_div' mm (B + (res - 1)) ve (B + res - 1) SHE ltac:(lia) ltac:(lia)) as RD.
    zstep. clear RD.
    rewrite (sxb_zb_small ve) by lia.
    do 5 zstep.
    zstep. if_cases Kc; zify_cond Kc.
    - apply ard_683d8; [exact AF| exact HR].
    - replace (2147450880 + B / 8) with (2147450880 + B / 8 + 0) by lia.
      eapply (ard_loop mm (Z.to_nat (SH (B + res - 1) - SH B - 0)) 0); try exact AF; try exact HR; unfold SH, SHADOW_OFFSET; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_quick : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    ard_frame mm -> 0 < res <= 64 ->
    evt bsegs POST (ST_ 0x447c0 mm x1 x5 x6 x7 (Z_to_bv 64 B) (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF HRr. assert (HR : 0 < res) by lia.
    pose proof RBv as [R1 R2]. unfold RS_LO, RS_HI in R1, R2.
    pose proof (SH_bounds B ltac:(lia)) as B1. pose proof (SH_bounds (B + res - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. ard_intro AF'.
    pose proof IC' as IC2. icpt_split IC2.
    do 9 zstep.
    rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
    replace (B + res + -1) with (B + res - 1) by lia.
    zstep. zstep. rewrite !land_m8 by lia.
    destruct (vis_read8 mm ((2147450880 + B / 8) / 8 * 8)) as (w1 & L1 & W1).
    { intros j Hj. apply (proj2 (SO HR)). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    destruct (vis_read8 mm ((2147450880 + (B + res - 1) / 8) / 8 * 8)) as (w2 & L2 & W2).
    { intros j Hj. apply (proj2 (SO HR)). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    unfold wa in W1, W2.
    step. step. clear W1 W2.
    zstep. step. if_cases Kc.
    - apply ard_slow; [exact AF| exact HR].
    - apply ard_ret. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_check : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    ard_frame mm ->
    evt bsegs POST (ST_ 0x447a0 mm x1 x5 x6 x7 (Z_to_bv 64 B) (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RBv as [R1 R2]. unfold RS_LO, RS_HI in R1, R2.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    zstep. if_cases Kc; zify_cond Kc.
    - (* [comment removed for export] *) apply ard_ret. exact AF.
    - assert (HR : 0 < res).
      { destruct (Z.eq_dec res (-1)) as [E|NE].
        + exfalso. rewrite E in Kc1. revert Kc1. clear. intros Kc1.
          replace ((-1) mod 18446744073709551616) with 18446744073709551615 in Kc1 by reflexivity. lia.
        + rewrite Z.mod_small in Kc0 by lia. lia. }
      clear Kc0 Kc1.
      zstep. fold_lits. rewrite (zb_lxor_ones B) by lia. zstep. zstep.
      zstep. if_cases Kc2; zify_cond Kc2; revert Kc2; rewrite ?unsigned_lit by lia; intros Kc2; try rewrite !Z.mod_small in Kc2 by lia.
      + exfalso. lia.
      + zstep. zstep. zstep. if_cases Kc3; zify_cond Kc3.
        * apply ard_region; [exact AF| exact HR].
        * apply ard_quick; [exact AF|].
          revert Kc3. rewrite ?unsigned_lit by lia. intros Kc3.
          destruct (Z.lt_ge_cases res 65) as [Hl|Hg]; [lia| exfalso].
          rewrite Z.mod_small in Kc3 by lia. lia.
  Qed.
End ReadIcpt.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma impl_post_evt_e : forall {A} (t : itree node (exc A)) (Q Q' : A -> machine_state -> Prop) ms,
  impl bsegs (at_node bsegs) t (epost Q) ms -> (forall a ms', Q a ms' -> evt bsegs (Q' a) ms') ->
  impl bsegs (at_node bsegs) t (epost Q') ms.
Proof.
  intros A t. induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. destruct r as [|a]; cbn in *; [exact (evt_done _ _ _ H')| apply HQ; exact H'].
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Definition read_resZ (a : read_ans) : Z := match a with RdErr _ => -1 | RdData bs => Z.of_nat (length bs) end.
Lemma read_ret_resZ : forall a, read_ret a = Z_to_bv 64 (read_resZ a).
Proof. intros [e|bs]; reflexivity. Qed.

Lemma read_icpt_ok : read_icpt_spec.
Proof.
  unfold read_icpt_spec. intros until lo. intros IC RC MI ST CEIL SPB BUF ERR -> -> TP FD CNT HM SOK BLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64) in RSP. pose proof HM as (R1 & R2 & R3). unfold RS_LO, RS_HI in R1, R3.
  assert (SE : AREAD_STACK = 2208) by reflexivity. pose proof CEIL as CE. try rewrite alloc_ceiling_lit in CE.
  assert (TPV : bv_unsigned tp = ATP) by (rewrite TP; apply unsigned_lit; unfold ATP; lia). unfold ATP in TPV.
  change (errno_addr tp) with (bv_unsigned tp + -164)%Z in ERR |- *.
  pose proof (munch_refl [(bv_unsigned sp - AREAD_STACK, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + count); (bv_unsigned tp + -164, bv_unsigned tp + -160)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m) as MUp.
  set (B := bv_unsigned a1) in *.
  assert (EA1 : a1 = Z_to_bv 64 B) by (symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  set (Pc := fun (a : read_ans) (mm : word -> option byte) =>
         match a with
         | RdErr e => rw_cells bsegs mm B [CB (Z.to_nat count) junk] /\ rw_cells bsegs mm (bv_unsigned tp + -164) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
         | RdData bs => rw_cells bsegs mm B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)]
                        /\ rw_cells bsegs mm (bv_unsigned tp + -164) [C4 errv] /\ (length bs <= Z.to_nat count)%nat
         end).
  assert (PcT : forall a mm mm', Pc a mm -> munch [(bv_unsigned sp - 2128 - 80, bv_unsigned sp - 2128)] mm mm' -> wmono bsegs mm mm' -> Pc a mm').
  { intros [e|bs] mm mm'; cbn beta; intros PCm MUr WMr.
    - destruct PCm as (P1 & P2 & P3). split; [| split; [| exact P3]].
      + eapply rw_cells_transport; [exact P1| exact MUr| exact WMr| cbn; rewrite ?Z2Nat.id by lia; lia].
      + eapply rw_cells_transport; [exact P2| exact MUr| exact WMr| cbn; lia].
    - destruct PCm as (P1 & P2 & P3). split; [| split; [| exact P3]].
      + eapply rw_cells_transport; [exact P1| exact MUr| exact WMr| cbn; rewrite ?length_skipn; lia].
      + eapply rw_cells_transport; [exact P2| exact MUr| exact WMr| cbn; lia]. }
  pose proof (conj IC (conj RC (conj SOK (conj BUF ERR)))) as PK.
  unfold AREAD_T. apply impl_from_evt.
  zstep.                                   (* [comment removed for export] *)
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 12 zstep.
  destruct PK as (IC0 & RC0 & SOK0 & BUF0 & ERR0). try clear IC; try clear RC; try clear SOK; try clear BUF; try clear ERR.
  zstep.                                   (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    assert (IC1 : icpt_cells m0)
      by (eapply icpt_cells_munch; [exact IC0| exact MU|]; unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil);
    assert (RC1 : read_icpt_cells m0)
      by (eapply ro_cells_transport; [exact RC0| exact MU|]; unfold AREAL_READ_SLOT; cbn; lia);
    destruct (stk_split bsegs m0 lo (bv_unsigned sp + -2128) (bv_unsigned sp + -48) ST ltac:(lia)) as [ST1 ST2]
  end.
  callsp try_init_ok; [exact IC1| assumption| exact ST1| exact CEIL| lia|].
  clear IC1 RC1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    assert (IC1 : icpt_cells m0)
      by (eapply icpt_cells_munch; [exact IC0| exact MU|]; unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil);
    assert (RC1 : ro_cells bsegs m0 AREAL_READ_SLOT [C8 (Z_to_bv 64 read_entry)])
      by (eapply ro_cells_transport; [exact RC0| exact MU|]; unfold AREAL_READ_SLOT; cbn; lia)
  end.
  unfold AREAL_READ_SLOT, read_entry in RC1.
  do 2 zstep.                              (* [comment removed for export] *)
  do 5 zstep.                              (* [comment removed for export] *)
  apply evt_done.
  (* [comment removed for export] *)
  lazymatch goal with |- ITree.impl _ _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (BUF1 : rw_cells bsegs m1 B [CB (Z.to_nat count) junk])
      by (eapply rw_cells_transport; [exact BUF0| exact MUp| exact WM| cbn; rewrite ?Z2Nat.id by lia; lia]);
    assert (ERR1 : rw_cells bsegs m1 (bv_unsigned tp + -164) [C4 errv])
      by (eapply rw_cells_transport; [exact ERR0| exact MUp| exact WM| cbn; lia]);
    lazymatch goal with STl : stk bsegs m1 lo (bv_unsigned sp + -2128) |- _ =>
      assert (STc : stk bsegs m1 lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2128)))) by (rewrite unsigned_lit by lia; exact STl)
    end
  end.
  eapply impl_post_evt_e.
  { eapply read_spec; [ exact STc | exact BUF1 | exact ERR1 | assumption | reflexivity | reflexivity | exact FD | lia | | | | | lia];
      rewrite ?unsigned_lit by lia; lia. }
  (* [comment removed for export] *)
  intros a ms' RP.
  destruct RP as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MUr & WMr & MI2 & ST3 & CELLS).
  rewrite unsigned_lit in MUr, ST3 by lia. change (errno_addr tp) with (bv_unsigned tp + -164)%Z in MUr, CELLS.
  replace (ret_pc (Z_to_bv 64 0x4479c)) with (Z_to_bv 64 0x4479c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite read_ret_resZ.
  (* [comment removed for export] *)
  lazymatch goal with FRx : rw_cells bsegs ?mx (bv_unsigned sp + -48) _ |- _ =>
    assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact FRx| exact MUr| exact WMr| cbn; lia]);
    lazymatch goal with ST2x : stk bsegs mx (bv_unsigned sp + -2128) (bv_unsigned sp + -48) |- _ =>
      assert (ST4 : stk bsegs m2 (bv_unsigned sp + -2128) (bv_unsigned sp + -48))
        by (eapply stk_transport_disjoint; [exact ST2x| exact MUr| exact WMr| cbn; lia]) end;
    assert (MU2 : munch [(bv_unsigned sp - AREAD_STACK, bv_unsigned sp); (B, B + count); (bv_unsigned tp + -164, bv_unsigned tp + -160)]%Z m m2)
      by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUr]; intros y Hy; cbn in Hy |- *; lia);
    assert (WM2 : wmono bsegs m m2) by (eapply wmono_trans; [exact WM| exact WMr]);
    lazymatch goal with ICx : icpt_cells mx |- _ =>
      assert (IC2 : icpt_cells m2)
        by (eapply icpt_cells_munch; [exact ICx| exact MUr|]; unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil) end
  end.
  assert (SO2 : 0 < read_resZ a -> shadow_ok m2 B (read_resZ a)).
  { intros HR. assert (LE : read_resZ a <= count) by (destruct a as [e|bs]; cbn in HR |- *; [lia| destruct CELLS as (_ & _ & L); lia]).
    eapply (shadow_ok_munch _ m m2); [eapply shadow_ok_sub; [exact SOK0| lia| lia| exact HR] | exact MU2 | exact HR | | |].
    - pose proof (SH_bounds B ltac:(lia)). lia.
    - pose proof (SH_bounds (B + read_resZ a - 1) ltac:(lia)). unfold KHIGHMEM_BEG in *. lia.
    - pose proof (SH_bounds B ltac:(lia)) as S1. pose proof (SH_bounds (B + read_resZ a - 1) ltac:(lia)) as S2.
      pose proof (SH_mono B (B + read_resZ a - 1) ltac:(lia)) as S3. unfold SH, SHADOW_OFFSET, KHIGHMEM_BEG in *.
      cbn. Z.div_mod_to_equations. lia. }
  zstep. fold_lits. sh_if_false.           (* [comment removed for export] *)
  rewrite EA1.
  eapply evt_mono.
  { apply (ard_check ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m B count lo (Pc a) (read_resZ a));
      [ exact HM | exact CNT | destruct a as [e|bs]; cbn; [lia| destruct CELLS as (_ & _ & L); lia] | exact CEIL | exact SPB
      | intros mm mm'; apply PcT | ].
    split; [exact MI2|]. split; [exact IC2|]. split; [exact ST3|]. split; [exact FR2|]. split; [exact CELLS|].
    split; [exact MU2|]. split; [exact WM2|]. split; [exact ST4| exact SO2]. }
  cbv beta. intros ms2 (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST5 & PC3).
  unfold read_icpt_post. exists w0, w1, w2, y1, y2, y3, y4, y5, y6, y7, w3, w4, w5, w6, m3.
  split; [rewrite read_ret_resZ; reflexivity|]. split; [rewrite Z2Nat.id by lia; change (errno_addr tp) with (bv_unsigned tp + -164)%Z; replace (bv_unsigned tp + -164 + 4) with (bv_unsigned tp + -160) by lia; exact MU3|].
  split; [exact WM3|]. split; [exact MI3|]. split; [exact ST5|].
  change (errno_addr tp) with (bv_unsigned tp + -164)%Z. destruct a as [e|bs]; exact PC3.
Qed.


End CeilWrap.
