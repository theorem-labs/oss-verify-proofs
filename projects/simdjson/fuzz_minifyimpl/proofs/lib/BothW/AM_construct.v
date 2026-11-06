(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Mem ITree Nodes Decode Arr Bytes ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow SysStepF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase ABytes ARep AModelFacts F_memset F_apoison F_m2s F_annot F_annot_sg APoisonR_iface F_annot_grow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AU_parts_iface AU_kit AU_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AKit AKit2 FsKit ShadowTac AU_steptac AU_h_kit AAnnot_iface AM_kitB AM_kitC AM_annotw AM_strctor BM_ctx.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UM_guards.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_prune_relevant; OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.
Definition bxc (P : Prop) : Prop := P.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxc P) in H end.


Section CANSEC1. Context {rc : runConstT}.
Definition ACONSTRUCT : Z := 0xb3290.
Definition AUCOPY : Z := 0xb34b4.          (* [comment removed for export] *)
Definition AUCOPY_LOOP : Z := 0xb3504.     (* [comment removed for export] *)
Definition AUCOPY_RET : Z := 0xb3318.      (* [comment removed for export] *)
Definition ALOOP_RET : Z := 0xb34c8.       (* [comment removed for export] *)
Definition ACONSTRUCT_STACK : Z := 64 + ANNOTW_STACK.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ckb_b35b8 : forall ra sp gp tp t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF bsegs RNG (fun ms' => exists y_t1, ms' = (MS (mkR ra sp gp tp (Z_to_bv 64 (sval b)) y_t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 P) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb3544) fc None mm (seg_rom bsegs)))
         (MS (mkR ra sp gp tp (Z_to_bv 64 (sval b)) t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 P) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb3540) fc None mm (seg_rom bsegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep. if_cases K2; zify_lts K2. { exfalso. Z.div_mod_to_equations. lia. }
    zstep. apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b35cc : forall ra sp gp tp t0 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF bsegs RNG (fun ms' => exists y_t2, ms' = (MS (mkR ra sp gp tp t0 (Z_to_bv 64 (sval b)) y_t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb3558) fc None mm (seg_rom bsegs)))
         (MS (mkR ra sp gp tp t0 (Z_to_bv 64 (sval b)) t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb3554) fc None mm (seg_rom bsegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep. if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma errmsg_range : forall k, (k < 54)%nat -> 0 <= nth k ERRMSG 0 < 256.
Proof.
  intros k Hk.
  assert (F : forallb (fun z => (0 <=? z) && (z <? 256))%bool ERRMSG = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F.
  assert (IN : In (nth k ERRMSG 0) ERRMSG) by (apply nth_In; change (length ERRMSG) with 54%nat; exact Hk).
  specialize (F _ IN). cbn beta in F. apply andb_prop in F as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2. lia.
Qed.

Lemma errmsg_nth : forall k, (k < 54)%nat -> nth_error errmsg k = Some (Z_to_bv 8 (nth k ERRMSG 0)).
Proof.
  intros k Hk. unfold errmsg. rewrite nth_error_map.
  rewrite (nth_error_nth' ERRMSG 0) by (change (length ERRMSG) with 54%nat; exact Hk). reflexivity.
Qed.

Lemma firstn1_skipn_nth : forall {X} (l : list X) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof. induction l as [|x l IH]; intros [|k] d H; cbn in *; try lia; [reflexivity| apply IH; lia]. Qed.

Lemma errmsg_firstn_S : forall k, (k < 54)%nat -> firstn (S k) errmsg = firstn k errmsg ++ [Z_to_bv 8 (nth k ERRMSG 0)].
Proof.
  intros k Hk. rewrite <- (firstn_skipn k errmsg) at 1. rewrite firstn_app, firstn_firstn, Nat.min_r, firstn_length, errmsg_len, Nat.min_l by lia.
  replace (S k - k)%nat with 1%nat by lia. f_equal.
  destruct (skipn k errmsg) as [|x l] eqn:E.
  - exfalso. apply (f_equal (@length byte)) in E. rewrite length_skipn, errmsg_len in E. cbn in E. lia.
  - cbn. f_equal. pose proof (errmsg_nth k Hk) as N. rewrite <- (firstn_skipn k errmsg), nth_error_app2 in N by (rewrite firstn_length, errmsg_len; lia).
    rewrite firstn_length, errmsg_len, Nat.min_l, Nat.sub_diag, E in N by lia. cbn in N. congruence.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section CE.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : amem) (V A P lo ULO UHI : Z).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - 2800.
  Hypothesis SPH : SP + 16 <= 2^47.
  Hypothesis SP16 : SP mod 16 = 0.                 (* [comment removed for export] *)
  Hypothesis V8 : V mod 8 = 0.
  Hypothesis VBLK : ablk V (V + 24).
  Hypothesis BR : ablock_range A 54.
  Hypothesis PBR : ablock_range P 56.
  Hypothesis DJV : V + 24 <= A \/ A + 56 <= V.
  Hypothesis DJPV : V + 24 <= P \/ P + 56 <= V.
  Hypothesis DJP : A + 56 <= P \/ P + 56 <= A.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RV : rng RNG V 24.
  Hypothesis RVS : rng RNG (shad V) 3.
  Hypothesis RBA : rng RNG A 54.
  Hypothesis RSA : rng RNG (shad A) 7.
  Hypothesis RBP : rng RNG P 54.
  Hypothesis RSP : rng RNG (shad P) 7.
  (* [comment removed for export] *)
  Hypothesis USH0 : unpoisoned m ULO UHI.
  Hypothesis U1 : ATOP <= ULO.
  Hypothesis U2 : ULO <= lo.
  Hypothesis U3 : SP <= UHI.
  Hypothesis U4 : UHI <= 2^47.
  Hypothesis RUSH : rng RNG (shad ULO) (shad UHI - shad ULO).

  Notation W4 := [(lo, SP); (V + 8, V + 16); (shad A, shad A + 7); (A, A + 54)].
  (* [comment removed for export] *)
  Hypothesis PCm : poison_cells m.
  Hypothesis ACm : annot_cells m.
  (* [comment removed for export] *)
  Definition FRAME (m1 : amem) : Prop :=
    (exists j1, rw_cells bsegs m1 (SP + -96) [CB 8 j1; C8 (Z_to_bv 64 0xb34c8)])
    /\ rw_cells bsegs m1 (SP + -80) [C8 (Z_to_bv 64 (P + 54)); C8 (Z_to_bv 64 0xb3318)]
    /\ (exists j0, rw_cells bsegs m1 (SP + -64) [CB 8 j0; C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 54)); C8 s2; C8 s1; C8 s0; C8 ra]).
  Definition VEC (m1 : amem) : Prop := rw_cells bsegs m1 V [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 54))].
  Definition VSH (m1 : amem) : Prop := rw_cells bsegs m1 (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Definition FULL (m1 : amem) : Prop := rw_cells bsegs m1 (shad A) [CB 7 (block_shadow_bytes 54)].
  Definition INV (m1 : amem) : Prop :=
    FRAME m1 /\ stk bsegs m1 lo (SP + -96) /\ VEC m1 /\ VSH m1 /\ FULL m1
    /\ bytes_at bsegs m1 P errmsg /\ unpoisoned m1 P (P + 54) /\ unpoisoned m1 A (A + 54) /\ wr_at bsegs m1 A 54
    /\ munch W4 m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1.

  (* [comment removed for export] *)
  Definition ce_post : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch W4 m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo SP
      /\ rw_cells bsegs m' V [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 54)); C8 (Z_to_bv 64 (A + 54))]
      /\ VSH m' /\ FULL m'
      /\ rw_cells bsegs m' A [CB 54 errmsg]
      /\ bytes_at bsegs m' P errmsg.

  (* [comment removed for export] *)
  Lemma ce_facts : 0 <= lo /\ SP < 2^47 /\ 0x6d4000 <= V /\ V + 24 <= ATOP /\ (V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V)
    /\ 0x6d4000 <= A /\ A + 54 <= ATOP /\ A mod 16 = 0 /\ (A + 56 <= 0x7fff7000 \/ 0x10007fff8000 <= A)
    /\ 0x6d4000 <= P /\ P + 56 <= ATOP /\ P mod 16 = 0 /\ (P + 56 <= 0x7fff7000 \/ 0x10007fff8000 <= P)
    /\ 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000 /\ 0x7fff8000 <= shad A /\ shad A + 7 <= 0x10007fff8000 /\ 0x7fff8000 <= shad P /\ shad P + 7 <= 0x10007fff8000
    /\ shad V = Z.shiftr V 3 + 2147450880 /\ Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1
    /\ 0x7fff7f800000 <= ATOP /\ ATOP <= 0x7fffff800000 /\ (shad V + 3 <= shad A \/ shad A + 7 <= shad V).
  Proof.
    pose proof atop_range as ATR. pose proof (bv_unsigned_in_range 64 sp) as RSP0.
    pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
    destruct BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & _ & BL3 & _). unfold AIMG_HI in BL1.
    destruct PBR as (PR1 & PR2 & PR3 & PR4). pose proof (ablk_lin _ _ PR1) as (PL1 & _ & PL3 & _). unfold AIMG_HI in PL1.
    assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
    assert (ANS : A + 56 <= 0x7fff7000 \/ 0x10007fff8000 <= A) by (unfold ablk, AIMG_HI, KLS in BR1; clear - BR1 BR4; Z.div_mod_to_equations; lia).
    assert (PNS : P + 56 <= 0x7fff7000 \/ 0x10007fff8000 <= P) by (unfold ablk, AIMG_HI, KLS in PR1; clear - PR1; lia).
    repeat split; try (unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; clear - ATR RSP0 VLO VHI BL1 BL3 BR4 PL1 PL3 PR4 VNS ANS PNS LOA LOS SPH V8 DJV; Z.div_mod_to_equations; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma ush_of_munch : forall m1, munch W4 m m1 -> unpoisoned m1 ULO UHI.
  Proof.
    intros m1 MU1. pose proof ce_facts as (LO0 & SP47 & VLO & VHI & VNS & AL1 & AH1 & A16 & ANS & PL1 & PH1 & P16 & PNS & SV1 & SV2 & SA1 & SA2 & SP1 & SP2 & _ & _ & ATR & ATR2 & SHDJ).
    pose proof ATOP_al16 as ATAL.
    eapply unpoisoned_munch; [exact USH0| exact MU1|]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF.
    clear - U1 U2 U3 U4 LOA LOS VLO VHI VNS AL1 AH1 A16 ANS ATR ATR2 ATAL. Z.div_mod_to_equations. lia.
  Qed.

  Ltac ckrd UNP LOx HIx Ad b RDb CKb :=
    destruct (unpoisoned_check_rd bsegs _ LOx HIx Ad 1 UNP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RDb & CKb);
    unfold shad, ASHOFF in RDb; replace (2147450880 + Z.shiftr Ad 3) with (Z.shiftr Ad 3 + 2147450880) in RDb by lia.
  Ltac ckcut L Ad bb CKb :=
    eapply evtF_cut;
    [ eapply L with (b := bb);
      [ lia
      | first [ exact CKb | lazymatch goal with |- _ \/ (_ /\ ?Px mod 8 + _ - _ < _) => replace Px with Ad by lia end; exact CKb ] ]
    | cbv beta; let ms' := fresh "ms'" in let PO := fresh "PO" in intros ms' PO; destruct_exs PO; subst ms' ].

  (* [comment removed for export] *)
  Notation LST pc mm va vp x5 x6 x7 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 0xb34c8) (Z_to_bv 64 (SP + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 V)
             (Z_to_bv 64 va) (Z_to_bv 64 vp) (Z_to_bv 64 (P + 54)) (Z_to_bv 64 va) (Z_to_bv 64 vp)
             (Z_to_bv 64 2147450880) (Z_to_bv 64 (-1)) (Z_to_bv 64 2) (Z_to_bv 64 P)
             s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma INV_store : forall m1 i, INV m1 -> 0 <= i < 54 -> bytes_at bsegs m1 A (firstn (Z.to_nat i) errmsg) ->
    INV (write_to_mem m1 (wa (A + i)) [Z_to_bv 8 (nth (Z.to_nat i) ERRMSG 0)])
    /\ bytes_at bsegs (write_to_mem m1 (wa (A + i)) [Z_to_bv 8 (nth (Z.to_nat i) ERRMSG 0)]) A (firstn (Z.to_nat (i + 1)) errmsg).
  Proof.
    intros m1 i (((j1 & FRL1) & FRW1 & (j0 & FR1)) & ST1 & VEC1 & VSH1 & FULL1 & SRC1 & UNPs1 & UNPd1 & WT1 & MU1 & WM1 & MI1) Hi PRE.
    pose proof ce_facts as (LO0 & SP47 & VLO & VHI & VNS & AL1 & AH1 & A16 & ANS & PL1 & PH1 & P16 & PNS & SV1 & SV2 & SA1 & SA2 & SP1 & SP2 & _ & _ & ATR & ATR2 & SHDJ).
    pose proof (bv_unsigned_in_range 64 sp) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0.
    assert (SOK : store_ok bsegs m1 (wa (A + i)) 1 = true) by (eapply wr_at_store_ok; [exact WT1| lia| lia]).
    set (m2 := write_to_mem m1 (wa (A + i)) _).
    assert (MU2 : munch [(A + i, A + i + 1)] m1 m2).
    { apply munch_write; [apply munch_refl| lia| cbn; lia|]. cbn [inside length]. left. cbn. lia. }
    assert (WM2 : wmono bsegs m1 m2) by (apply wmono_write; apply wmono_refl).
    assert (XC : forall B cs, (B + Z.of_nat (cells_size cs) <= A + i \/ A + i + 1 <= B) -> rw_cells bsegs m1 B cs -> rw_cells bsegs m2 B cs).
    { intros B cs D H. eapply rw_cells_transport; [exact H| exact MU2| exact WM2|]. cbn [disjoint_from]. split; [exact D| exact I]. }
    split.
    - split. { split; [| split].
               - exists j1. apply XC; [cbn [cells_size csize Nat.add]; clear - LOA LOS AH1 ATR Hi; lia| exact FRL1].
               - apply XC; [cbn [cells_size csize Nat.add]; clear - LOA LOS AH1 ATR Hi; lia| exact FRW1].
               - exists j0. apply XC; [cbn [cells_size csize Nat.add]; clear - LOA LOS AH1 ATR Hi; lia| exact FR1]. }
      split. { apply stk_write; [exact ST1| lia| cbn; lia]. }
      split. { apply XC; [cbn [cells_size csize Nat.add]; clear - DJV Hi; lia| exact VEC1]. }
      split. { apply XC; [cbn [cells_size csize Nat.add]; clear - SV1 SV2 ANS Hi; lia| exact VSH1]. }
      split. { apply XC; [cbn [cells_size csize Nat.add]; clear - SA1 SA2 ANS Hi; lia| exact FULL1]. }
      split. { eapply bytes_at_write_other; [exact SRC1| lia| cbn; lia| rewrite errmsg_len; cbn [length]; clear - DJP Hi; lia]. }
      split. { eapply unpoisoned_munch; [exact UNPs1| exact MU2|]. cbn [disjoint_from]. split; [| exact I]. rewrite !shad_div. unfold ASHOFF. clear - PNS ANS PL1 PH1 AL1 ATR2 Hi; Z.div_mod_to_equations; lia. }
      split. { eapply unpoisoned_munch; [exact UNPd1| exact MU2|]. cbn [disjoint_from]. split; [| exact I]. rewrite !shad_div. unfold ASHOFF. clear - ANS AL1 AH1 ATR2 Hi; Z.div_mod_to_equations; lia. }
      split. { apply wr_at_write. exact WT1. }
      split. { apply munch_write; [exact MU1| lia| cbn; lia|]. cbn [inside length]. right. right. right. left. cbn. lia. }
      split. { apply wmono_write. exact WM1. }
      apply mem_inv_store; [exact MI1| exact SOK].
    - replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite errmsg_firstn_S by lia.
      apply bytes_at_app_join.
      + eapply bytes_at_write_other; [exact PRE| lia| cbn; lia| rewrite firstn_length, errmsg_len; left; lia].
      + rewrite firstn_length, errmsg_len, Nat.min_l by lia. replace (A + Z.of_nat (Z.to_nat i)) with (A + i) by lia.
        replace (Z.to_nat i) with (Z.to_nat i) by reflexivity. apply bytes_at_write_same; [lia| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ce_exit_at : forall m1 va vp (x5 x6 x7 x28 x29 x30 x31 : word),
    INV m1 -> bytes_at bsegs m1 A errmsg -> va = A + 54 ->
    evtF bsegs RNG ce_post (LST 0xb3594 m1 va vp x5 x6 x7 x28 x29 x30 x31).
  Proof.
    intros m1 va vp x5 x6 x7 x28 x29 x30 x31 (((j1 & FRL1) & FRW1 & (j0 & FR1)) & ST1 & VEC1 & VSH1 & FULL1 & SRC1 & UNPs1 & UNPd1 & WT1 & MU1 & WM1 & MI1) ALL ->.
    pose proof ce_facts as (LO0 & SP47 & VLO & VHI & VNS & AL1 & AH1 & A16 & ANS & PL1 & PH1 & P16 & PNS & SV1 & SV2 & SA1 & SA2 & SP1 & SP2 & SHV & SHV8 & ATR & ATR2 & SHDJ).
    pose proof (bv_unsigned_in_range 64 sp) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0.
    unfold VEC, VSH, FULL in *.
    (* [comment removed for export] *)
    assert (BLK1 : rw_cells bsegs m1 A [CB 54 errmsg]).
    { split; [split|]; [cbn [cells_wf cell_wf]; rewrite errmsg_len; split; [reflexivity| exact I]
                         | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact ALL
                         | cbn [cells_size csize Nat.add]; exact WT1]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, SP); (V + 8, V + 16)] m1) as MUX. box SRC1. clear ALL UNPs1 UNPd1 WT1.
    zstep.                                  (* [comment removed for export] *)
    zstep. zstep.                           (* [comment removed for export] *)
    lazymatch goal with H : stk bsegs _ lo _ |- _ => release_frame FRL1 H (SP + -80) end.
    zstep.                                  (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 0xb34c8)) with (Z_to_bv 64 0xb34c8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. zstep.                           (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K AL1 AH1 ATR; ubguard K; lia| clear K]).   (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    try replace (A + 54 - A) with 54 by lia.
    zstep. zstep. zstep. zstep.             (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K AL1 AH1 ATR; ubguard K; lia| clear K]).   (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    lazymatch goal with H : stk bsegs _ lo _ |- _ => release_frame FRW1 H (SP + -64) end.
    zstep.                                  (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 0xb3318)) with (Z_to_bv 64 0xb3318 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with FRx : rw_cells bsegs mm (SP + -64) _, MUx : munch W4 m mm, WMx : wmono bsegs m mm |- _ =>
      assert (HWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W4) by (repeat constructor; cbn; unfold AIMG_HI; clear - SA1 LOA LOS ATR VLO AL1; lia);
      pose proof (poison_cells_frame _ _ _ PCm MUx WMx HWI) as PCq; pose proof (annot_cells_frame _ _ _ ACm MUx WMx HWI) as ACq;
      pose proof PCq as (GOTq & _ & _ & SHBq & _);
      pose proof (ush_of_munch mm MUx) as USHq;
      rw_split FRx 1%nat FRA FRT; rw_split FRT 3%nat TX1 FRB
      end end.
    name_sp sp (-64)%Z.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evtF_cut; [ eapply (ctx_dtor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -56) V (A + 54) lo ULO UHI)
                       | cbv beta; unfold ctx_dtor_post; rewrite ?Hsp; rewrite ?unsigned_lit by (clear - LOS LOA LO0 SP47 ATR; lia); clear PCq ACq; post_call bsegs mm ]
    end;
      rewrite ?Hsp; rewrite ?unsigned_lit by (clear - LOS LOA LO0 SP47 ATR; lia);
      first [ exact PCq | exact ACq | exact GOTq | exact SHBq | exact TX1 | exact USHq | exact V8 | exact VBLK | exact RI | exact RV | exact RVS | exact U4
            | reflexivity | eassumption
            | (clear - LOA ATR; lia) | (clear - LOS; lia) | (clear - SPH; lia) | (clear - SP16; Z.div_mod_to_equations; lia)
            | (clear - U2 LOS; lia) | (clear - U3; lia)
            | (clear - AH1 AL1 ATR; lia)
            | (f_equal; clear; lia)
            | (eapply rng_sub'; [exact RSTK| clear - LOS LO0; lia])
            | (eapply rng_sub'; [exact RUSH| rewrite !shad_div; unfold ASHOFF; clear - U2 U3 LOS LO0; Z.div_mod_to_equations; lia])
            | idtac ].
    all: try unname_sp.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.             (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    match goal with FRAx : rw_cells bsegs ?mm (SP + -64) [_], TXx : rw_cells bsegs ?mm' (SP + -56) [_; _; _], FRBx : rw_cells bsegs ?mm'' (SP + -32) _ |- _ =>
      rw_join FRAx TXx FRAT; rw_join FRAT FRBx FRJ end.
    lazymatch goal with H : stk bsegs _ lo _ |- _ => release_frame FRJ H (bv_unsigned sp) end.
    zstep.                                  (* [comment removed for export] *)
    apply evtF_done. unfold ce_post. unfold bxc in SRC1.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
      lazymatch goal with MUx : munch W4 m mm, WMx : wmono bsegs m mm, MIx : mem_inv bsegs mm, STx : stk bsegs mm lo _,
                          VECx : rw_cells bsegs mm V _, VSHx : rw_cells bsegs mm (shad V) _, FULLx : rw_cells bsegs mm (shad A) _, BLKx : rw_cells bsegs mm A _, MUXx : munch _ m1 mm |- _ =>
      do 15 eexists; exists mm; split; [reflexivity|];
      split; [exact MUx|]; split; [exact WMx|]; split; [exact MIx|]; split; [exact STx|]; split; [exact VECx|]; split; [exact VSHx|]; split; [exact FULLx|];
      split; [exact BLKx|];
      eapply bytes_at_transport; [exact SRC1| exact MUXx| cbn [disjoint_from]; rewrite errmsg_len; clear - DJPV LOA LOS ATR PL1 PH1; lia]
      end end.
  Qed.

  (* [comment removed for export] *)
  Lemma ce_loop : forall fuel i m1 (x5 x6 x7 x28 x29 x30 x31 : word),
    Z.of_nat fuel > 54 - i -> 0 <= i < 54 -> INV m1 -> bytes_at bsegs m1 A (firstn (Z.to_nat i) errmsg) ->
    evtF bsegs RNG ce_post (LST 0xb352c m1 (A + i) (P + i) x5 x6 x7 x28 x29 x30 x31).
  Proof.
    induction fuel as [|fuel IH]; intros i m1 x5 x6 x7 x28 x29 x30 x31 FUEL Hi INV1 PRE; [lia|].
    pose proof INV1 as (((j1 & FRL1) & FRW1 & (j0 & FR1)) & ST1 & VEC1 & VSH1 & FULL1 & SRC1 & UNPs1 & UNPd1 & WT1 & MU1 & WM1 & MI1).
    pose proof ce_facts as (LO0 & SP47 & VLO & VHI & VNS & AL1 & AH1 & A16 & ANS & PL1 & PH1 & P16 & PNS & SV1 & SV2 & SA1 & SA2 & SP1 & SP2 & _ & _ & ATR & ATR2 & SHDJ).
    pose proof (bv_unsigned_in_range 64 sp) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0.
    set (c := nth (Z.to_nat i) ERRMSG 0). pose proof (errmsg_range (Z.to_nat i) ltac:(lia)) as CR. fold c in CR.
    assert (RDc : ov_read_bytes bsegs m1 (wa (P + i)) 1 = Some [Z_to_bv 8 c]).
    { pose proof (bytes_at_read bsegs m1 P errmsg i 1 SRC1 ltac:(lia) ltac:(rewrite errmsg_len; lia)) as R. rewrite R.
      rewrite (firstn1_skipn_nth errmsg (Z.to_nat i) (Z_to_bv 8 0)) by (rewrite errmsg_len; lia). unfold errmsg. rewrite map_nth. reflexivity. }
    assert (SOK : store_ok bsegs m1 (wa (A + i)) 1 = true) by (eapply wr_at_store_ok; [exact WT1| lia| lia]).
    assert (ACCs : rng RNG (Z.shiftr (P + i) 3 + 2147450880) 1)
      by (eapply rng_sub'; [exact RSP| rewrite Z.shiftr_div_pow2, shad_div by lia; unfold ASHOFF; clear - Hi P16 PL1; Z.div_mod_to_equations; lia]).
    assert (ACCd : rng RNG (Z.shiftr (A + i) 3 + 2147450880) 1)
      by (eapply rng_sub'; [exact RSA| rewrite Z.shiftr_div_pow2, shad_div by lia; unfold ASHOFF; clear - Hi A16 AL1; Z.div_mod_to_equations; lia]).
    (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K PL1 Hi; lia| clear K]).   (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K AL1 Hi; lia| clear K]).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. ckrd UNPs1 P (P + 54) (P + i) b0 RDb0 CKb0. zstep. rewrite sxb_sval.
    ckcut ckb_b35b8 (P + i) b0 CKb0. clear RDb0 CKb0.
    (* [comment removed for export] *)
    zstep. zstep. ckrd UNPd1 A (A + 54) (A + i) b1 RDb1 CKb1. zstep. rewrite sxb_sval.
    zstep.                                  (* [comment removed for export] *)
    ckcut ckb_b35cc (A + i) b1 CKb1. clear RDb1 CKb1.
    (* [comment removed for export] *)
    zstep. change (le1 (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 c)))) with (le1 (zxb (Z_to_bv 8 c))). rewrite le1_zxb.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => set (m2 := mx) in * end.
    assert (IP : INV m2 /\ bytes_at bsegs m2 A (firstn (Z.to_nat (i + 1)) errmsg)) by (exact (INV_store m1 i INV1 Hi PRE)).
    destruct IP as [INV2 PRE2]. clearbody m2. clear RDc SOK FRL1 FRW1 FR1 ST1 VEC1 VSH1 FULL1 SRC1 UNPs1 UNPd1 WT1 MU1 WM1 MI1 INV1 PRE.
    pose proof INV2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI2).
    (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K PH1 ATR Hi; lia| clear K]).   (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K AL1 AH1 ATR Hi; lia| clear K]).   (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep. if_cases Kn; zify_cond Kn.
    - (* [comment removed for export] *)
      assert (NEXT : forall va vp (y5 y6 y7 y28 y29 y30 y31 : word), va = A + (i + 1) -> vp = P + (i + 1) ->
                evtF bsegs RNG ce_post (LST 0xb352c m2 va vp y5 y6 y7 y28 y29 y30 y31)).
      { intros va vp y5 y6 y7 y28 y29 y30 y31 -> ->. apply IH; [lia| rewrite ?unsigned_lit in Kn by lia; lia| exact INV2| exact PRE2]. }
      apply NEXT; lia.
    - (* [comment removed for export] *)
      zstep.                                (* [comment removed for export] *)
      assert (E54 : i + 1 = 54) by (rewrite ?unsigned_lit in Kn by lia; lia).
      replace (Z.to_nat (i + 1)) with 54%nat in PRE2 by lia. rewrite <- errmsg_len, firstn_all in PRE2.
      assert (EXIT : forall va vp (y5 y6 y7 y28 y29 y30 y31 : word), va = A + 54 -> evtF bsegs RNG ce_post (LST 0xb3594 m2 va vp y5 y6 y7 y28 y29 y30 y31))
        by (intros va vp y5 y6 y7 y28 y29 y30 y31 E; apply ce_exit_at; [exact INV2| exact PRE2| exact E]).
      apply EXIT; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ce_spec : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (st : astate) (p : AsanCtrl.aptr) (ch : achunk),
    mem_inv bsegs m -> stk bsegs m lo SP ->
    poison_cells m -> annot_cells m -> artcells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
    rt_got m -> rt_shbase m ->
    rw_cells bsegs m V [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 54))] -> VSH m ->
    rw_cells bsegs m (shad A) [CB 7 (repeat (Z_to_bv 8 252) 7)] ->
    bytes_at bsegs m P errmsg -> unpoisoned m P (P + 54) -> wr_at bsegs m A 54 ->
    (a_live st) !! p = Some ch -> chunk_size ch = 54 -> (is_primary 54 = false -> A = chunk_user_beg ch) -> achunk_kind_ok ch 54 ->
    (exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + 54 + 64 <= RHI
         /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at bsegs m (shad RLO) (shlen (RHI - RLO))) ->
    evtF bsegs RNG ce_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 P) (Z_to_bv 64 (P + 54)) (Z_to_bv 64 54) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ACONSTRUCT) fc None m (seg_rom bsegs)).
  Proof.
    intros until ch. intros MI ST PC AC ART PRM RR GOT SHB VEC0 VSH0 FULL0 SRC0 UNPs0 WT0 LIVE CSZ UBEG KIND ARENA.
    pose proof ce_facts as (LO0 & SP47 & VLO & VHI & VNS & AL1 & AH1 & A16 & ANS & PL1 & PH1 & P16 & PNS & SV1 & SV2 & SA1 & SA2 & SP1 & SP2 & SHV & SHV8 & ATR & ATR2 & SHDJ).
    pose proof (bv_unsigned_in_range 64 sp) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0.
    unfold VSH in VSH0. unfold ACONSTRUCT.
    assert (ACC1 : rng RNG (Z.shiftr (V + 8) 3 + 2147450880) 1) by (rewrite SHV8; eapply rng_sub'; [exact RVS| lia]).
    (* [comment removed for export] *)
    box SRC0. box UNPs0.
    pose proof (munch_refl W4 m) as MU. pose proof (wmono_refl bsegs m) as WM.
    carve_frame 64%nat ST.
    zstep. zstep. zstep. zstep. zstep.      (* [comment removed for export] *)
    zstep. zstep.                           (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with VSHx : rw_cells bsegs mm (shad V) _ |- _ =>
      pose proof (sh3_read mm (shad V) 1 ltac:(lia) VSHx) as HR1; rewrite <- SHV8 in HR1 end end.
    astep. astep.                           (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    try replace (54 + A) with (A + 54) by lia.
    zstep.                                  (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K AL1 AH1 ATR; lia| clear K]).              (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K AL1 AH1 ATR; ubguard K; lia| clear K]).   (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep. zstep.                           (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with VECx : rw_cells bsegs mm V _, FULLx : rw_cells bsegs mm (shad A) [CB 7 (repeat _ _)] |- _ =>
      assert (HWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W4) by (repeat constructor; cbn; unfold AIMG_HI; clear - SA1 LOA ATR VLO AL1; lia);
      pose proof (poison_cells_frame _ _ _ PC MU WM HWI) as PCq;
      pose proof (annot_cells_frame _ _ _ AC MU WM HWI) as ACq;
      pose proof (artcells_frame _ _ _ ART MU WM HWI) as ARTq;
      pose proof (premap_cells_frameA _ _ _ PRM MU WM HWI) as PRMq;
      pose proof (arelro_munchA _ _ _ RR MU HWI) as RRq;
      assert (ARENAq : exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + 54 + 64 <= RHI
                 /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at bsegs mm (shad RLO) (shlen (RHI - RLO)))
        by (destruct ARENA as (RLO & RHI & X1 & X2 & X3 & X4 & X5 & X6); exists RLO, RHI; repeat (split; [assumption|]); eapply wr_at_transport; [exact X6| exact WM]);
      name_sp sp (-64)%Z;
      eapply evtF_cut;
      [ eapply (annotw_increase_grow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V A 54 lo st p ch);
        first [ exact PCq | exact ACq | exact ARTq | exact PRMq | exact RRq | exact VECx | exact V8 | exact VBLK | exact BR | exact LIVE | exact CSZ | exact UBEG | exact KIND
              | exact ARENAq | exact RI | exact RV | exact RVS | exact FULLx | exact RSA | reflexivity
              | (rewrite Hsp; eassumption) | eassumption
              | (rewrite Hsp; unfold ANNOTW_STACK; clear - LOS; lia) | (rewrite Hsp; clear - RSP0 LOS LOA ATR SPH; lia)
              | (change (rup8 54) with 56; exact DJV)
              | (unfold AREQMAX; clear; lia)
              | (rewrite Hsp; eapply rng_sub'; [exact RSTK| clear - LOS LOA LO0; lia])
              | lia ]
      | cbv beta; unfold annotw_grow_post, ANNOTW_STACK; change (shlen (rup8 54)) with 7; change (54 / 8) with 6; clear PCq ACq ARTq PRMq RRq ARENAq HWI; post_call bsegs mm ]
      end end.
    unname_sp.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with BODY : rw_cells bsegs mm (shad A) [CB _ (repeat _ _)], LAST : (54 mod 8 <> 0 -> rw_cells bsegs mm _ [C1 _]) |- _ =>
      pose proof (bsb_cells_join mm (shad A) 54 ltac:(lia) BODY LAST) as FULL2; change (Z.to_nat (granules 54)) with 7%nat in FULL2; clear BODY LAST
      end end.
    zstep.                                  (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    lazymatch goal with STx : stk bsegs _ lo _ |- _ => carve_frame 16%nat STx end.
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    lazymatch goal with STx : stk bsegs _ lo _ |- _ => carve_frame 16%nat STx end.
    zstep. zstep.                           (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K; lia| clear K]).   (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep. zstep.                           (* [comment removed for export] *)
    zstep. zstep.                           (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with FRLx : rw_cells bsegs mm (SP + -96) _, FRWx : rw_cells bsegs mm (SP + -80) _, FRx : rw_cells bsegs mm (SP + -64) _,
                          STx : stk bsegs mm lo _, VECx : rw_cells bsegs mm V _, VSHx : rw_cells bsegs mm (shad V) _, FULLx : rw_cells bsegs mm (shad A) [CB 7 (block_shadow_bytes 54)],
                          WTx : wr_at bsegs mm A 54, MUx : munch W4 m mm, WMx : wmono bsegs m mm, MIx : mem_inv bsegs mm |- _ =>
      assert (UNPd : unpoisoned mm A (A + 54))
        by (apply ablock_unpoisoned; [apply (ablock_shadow_of_cells mm A 54 ltac:(lia) ltac:(lia)); exact FULLx| clear - A16; Z.div_mod_to_equations; lia| lia| lia| lia]);
      unfold bxc in SRC0, UNPs0;
      assert (SRC2 : bytes_at bsegs mm P errmsg)
        by (eapply bytes_at_transport; [exact SRC0| exact MUx| cbn [disjoint_from]; rewrite errmsg_len; rewrite !shad_div; unfold ASHOFF; clear - LOA ATR PL1 PH1 PNS DJPV DJP AL1 AH1 ANS A16 P16; Z.div_mod_to_equations; lia]);
      assert (UNPs : unpoisoned mm P (P + 54))
        by (eapply unpoisoned_munch; [exact UNPs0| exact MUx|]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; clear - LOA ATR PL1 PH1 PNS VNS VLO DJP AL1 AH1 ANS A16 P16 ATR2; Z.div_mod_to_equations; lia);
      assert (INV0 : INV mm)
        by (split; [split; [eexists; exact FRLx| split; [exact FRWx| eexists; exact FRx]]|]; split; [exact STx|]; split; [exact VECx|]; split; [exact VSHx|]; split; [exact FULLx|];
            split; [exact SRC2|]; split; [exact UNPs|]; split; [exact UNPd|]; split; [exact WTx|]; split; [exact MUx|]; split; [exact WMx| exact MIx]);
      clear SRC0 UNPs0;
      assert (START : forall va vp (y5 y6 y7 y28 y29 y30 y31 : word), va = A + 0 -> vp = P + 0 ->
                evtF bsegs RNG ce_post (LST 0xb352c mm va vp y5 y6 y7 y28 y29 y30 y31))
        by (intros va vp y5 y6 y7 y28 y29 y30 y31 -> ->; apply (ce_loop 55%nat 0); [lia| lia| exact INV0|];
            change (Z.to_nat 0) with 0%nat; cbn [firstn]; split; [lia|]; split; [cbn; lia|]; intros k Hk; cbn in Hk; lia)
      end end.
    apply START; lia.
  Qed.
End CE.
End CANSEC1.
