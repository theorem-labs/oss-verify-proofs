(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree CJ_print_iface CJ_ensure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac shh H := let T := type of H in idtac H ":" T.
Ltac shmem :=
  lazymatch goal with |- evt _ _ (MS _ ?F ?pc _ _ ?m _) => idtac "PC" pc "MEM" m "F" F;
    repeat match goal with H : context [m] |- _ => shh H; revert H end end.
Ltac dlia := cbn; repeat match goal with |- _ /\ _ => split end; first [exact I | lia].

(* [comment removed for export] *)
Definition FAG18 (F Fc : bvmap 5 word) : Prop := forall k : bv 5, 18 <= bv_unsigned k <= 27 -> reg_get Fc k = reg_get F k.

Lemma FAG18_restore : forall F Fc, FAG18 F Fc ->
  forall k : bv 5, fp_callee_saved k -> reg_get (bvmap_set 8 (reg_get F (Z_to_bv 5 8)) (bvmap_set 9 (reg_get F (Z_to_bv 5 9)) Fc)) k = reg_get F k.
Proof.
  intros F Fc FA k Hk. unfold fp_callee_saved in Hk.
  destruct (Z.eq_dec (bv_unsigned k) 8) as [E8|N8].
  { rewrite freg_get_same by (rewrite E8; reflexivity). replace k with (Z_to_bv 5 8 : bv 5) by (apply bv_eq; rewrite E8; reflexivity). reflexivity. }
  rewrite freg_get_other by (unfold bv_eqb; apply Z.eqb_neq; replace (bv_unsigned (8%bv : bv 5)) with 8%Z by reflexivity; lia).
  destruct (Z.eq_dec (bv_unsigned k) 9) as [E9|N9].
  { rewrite freg_get_same by (rewrite E9; reflexivity). replace k with (Z_to_bv 5 9 : bv 5) by (apply bv_eq; rewrite E9; reflexivity). reflexivity. }
  rewrite freg_get_other by (unfold bv_eqb; apply Z.eqb_neq; replace (bv_unsigned (9%bv : bv 5)) with 9%Z by reflexivity; lia).
  apply FA. lia.
Qed.

(* [comment removed for export] *)
Lemma node_tyb_read : forall m p nx pv ch ty p1 vs vi p2 vd ky,
  rw_cells usegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky) -> 0 <= ty < 256 ->
  ov_read_bytes usegs m (Z_to_bv 64 (p + 24)) 1 = Some [Z_to_bv 8 ty].
Proof.
  intros until ky. intros [[WF BA] _] Hty.
  pose proof (bytes_at_read usegs m p _ 24 1 BA ltac:(lia) ltac:(cbn; lia)) as RD.
  change (wa (p + 24)) with (Z_to_bv 64 (p + 24)) in RD. rewrite RD. clear RD.
  replace (Z.to_nat 24) with 24%nat by reflexivity.
  cbn [cells_bytes cbytes node_cells le8 le4 word_to_le_bytes Z_to_le_bytes skipn firstn app].
  do 2 f_equal. apply bv_eq. unfold wz. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^64). change (bv_modulus 8) with 256. rewrite (Z.mod_small ty (2^64)) by lia. reflexivity.
Qed.

Section S.
  Variable HI : cj_heap_iface.

  Section Call.
    (* [comment removed for export] *)
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
              (m : word -> option byte)
              (SPB : Z) (LR B : list cblock) (n : nat) (p PB dep : Z) (fw : word) (lo : Z).
    Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - PV_STACK n.
    Hypothesis TP : tp = wz PTP.
    Hypothesis SPhi : bv_unsigned sp <= 2^64.
    Hypothesis N1 : (1 <= n)%nat.

    Notation POST := (pvalue_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m).
    Notation SPF := (bv_unsigned sp + -128).
    (* [comment removed for export] *)
    Notation PVFRAME mm loc := (rw_cells usegs mm (bv_unsigned sp + -128)
       [CB 40 loc; C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

    Lemma SPFeq : bv_unsigned (Z_to_bv 64 SPF) = SPF.
    Proof. apply unsigned_lit. pose proof CEIL as C. try rewrite alloc_ceiling_eq in C. unfold PV_STACK, PV_BASE in LO. lia. Qed.

    (* [comment removed for export] *)
    Lemma pv_epi : forall (mm : word -> option byte) (mo' : Model) (errv' : word) (loc : list byte) (Fc : bvmap 5 word) (fcc : bv 32)
                       (x1 x5 x6 x7 x8 x9 r x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
      PVFRAME mm loc -> stk usegs mm lo SPF -> mem_inv usegs mm -> rw_cells usegs mm PERRNO [C4 errv'] -> CJST mm ->
      frm0 fcc -> FAG18 F Fc ->
      pv_agree LR (bv_unsigned sp) PB m mm -> cj_chain CJ_PRINTABLE mm n p B ->
      print_outcome HI SPB LR PB dep fw r mm mo' ->
      SCPS usegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 r x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x14a38) fcc None mm (seg_rom usegs)) mo'.
    Proof.
      intros until x31. intros FR ST MI ERR CJ FRM FA PVA CH OUT.
      pose proof CEIL as CEIL'. unfold PV_STACK, PV_BASE in LO. try rewrite alloc_ceiling_eq in CEIL.
      destruct OUT as (LB' & buf' & len' & off' & HL' & OUT).
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL'|].
      do 13 step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. apply scps_done. unfold pvalue_post.
      do 19 eexists. split; [reflexivity|].
      split; [exact MI|]. split; [exact FRM|]. split.
      { apply (FAG18_restore F Fc FA). }
      split; [exact ST|]. split; [exact ERR|]. split; [exact CJ|]. split; [exact PVA|]. split; [exact CH|].
      exists LB', buf', len', off'. split; [exact HL'| exact OUT].
    Qed.

    (* [comment removed for export] *)
    Lemma pv_ret1 : forall (mm : word -> option byte) (mo' : Model) (errv' : word) (loc : list byte) (Fc : bvmap 5 word) (fcc : bv 32)
                       (LB' : list cblock) (buf' len' off' : Z) (bs' : list byte)
                       (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
      PVFRAME mm loc -> stk usegs mm lo SPF -> mem_inv usegs mm -> rw_cells usegs mm PERRNO [C4 errv'] -> CJST mm ->
      frm0 fcc -> FAG18 F Fc ->
      pv_agree LR (bv_unsigned sp) PB m mm -> cj_chain CJ_PRINTABLE mm n p B ->
      LHEAP HI SPB LB' mm mo' -> Permutation ((buf', len') :: LR) LB' ->
      pb_struct mm PB buf' len' off' dep fw -> pb_data mm buf' len' bs' -> pb_nums len' off' dep -> pb_nul bs' len' off' ->
      SCPS usegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x14a34) fcc None mm (seg_rom usegs)) mo'.
    Proof.
      intros until x31. intros FR ST MI ERR CJ FRM FA PVA CH HL' HP' PS' PD' PN' NUL.
      pose proof CEIL as CEIL'. unfold PV_STACK, PV_BASE in LO. try rewrite alloc_ceiling_eq in CEIL.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL'|].
      step. apply evt_done. cbv beta.
      eapply pv_epi; [exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CH|].
      exists LB', buf', len', off'. split; [exact HL'|]. right. split; [reflexivity|]. exists bs'. auto 10.
    Qed.

    (* [comment removed for export] *)
    Lemma pv_ret0 : forall (mm : word -> option byte) (mo' : Model) (errv' : word) (loc : list byte) (Fc : bvmap 5 word) (fcc : bv 32)
                       (LB' : list cblock) (buf' len' off' dep' : Z)
                       (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
      PVFRAME mm loc -> stk usegs mm lo SPF -> mem_inv usegs mm -> rw_cells usegs mm PERRNO [C4 errv'] -> CJST mm ->
      frm0 fcc -> FAG18 F Fc ->
      pv_agree LR (bv_unsigned sp) PB m mm -> cj_chain CJ_PRINTABLE mm n p B ->
      LHEAP HI SPB LB' mm mo' -> pb_struct mm PB buf' len' off' dep' fw ->
      ((buf' = 0 /\ Permutation LR LB') \/ (buf' <> 0 /\ Permutation ((buf', len') :: LR) LB')) ->
      SCPS usegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x1493c) fcc None mm (seg_rom usegs)) mo'.
    Proof.
      intros until x31. intros FR ST MI ERR CJ FRM FA PVA CH HL' PS' HB.
      pose proof CEIL as CEIL'. unfold PV_STACK, PV_BASE in LO. try rewrite alloc_ceiling_eq in CEIL.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL'|].
      step. step. apply evt_done. cbv beta.
      eapply pv_epi; [exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CH|].
      exists LB', buf', len', off'. split; [exact HL'|]. left. split; [reflexivity|]. exists dep'. split; [exact PS'| exact HB].
    Qed.

  End Call.
End S.


End CeilWrap.
(* [comment removed for export] *)
Ltac shh H := let T := type of H in idtac H ":" T.
Ltac shmem :=
  lazymatch goal with |- evt _ _ (MS _ ?F ?pc _ _ ?m _) => idtac "PC" pc "MEM" m "F" F;
    repeat match goal with H : context [m] |- _ => shh H; revert H end end.
Ltac dlia := cbn; repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
