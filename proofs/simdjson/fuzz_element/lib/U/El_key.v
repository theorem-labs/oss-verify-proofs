(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit F_memcmp Atp_defs Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Atp_objl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_defs El_acc_3da20 El_acc_3dce0 El_acc_3dd90.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition cmp_post (ra : word) (sp : Z) (gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (r a1' a2' a3' a4' : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 sp) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 r a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(sp - 48, sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo sp.

Definition cmp_stmt (centry : Z) : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (sp lo p q : Z) (bp bq : list byte),
    length bq = length bp -> 0 <= p -> 0 <= q -> p + Z.of_nat (length bp) < 2 ^ 63 -> q + Z.of_nat (length bp) < 2 ^ 63 ->
    (length bp = 0%nat \/ (p + Z.of_nat (length bp) <= sp - 48 /\ q + Z.of_nat (length bp) <= sp - 48)) ->
    bytes_at usegs m p bp -> bytes_at usegs m q bq -> mem_inv usegs m -> stk usegs m lo sp -> lo + 48 <= sp -> sp < 2 ^ 63 -> sp mod 16 = 0 ->
    evt usegs (cmp_post ra sp gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra (Z_to_bv 64 sp) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (length bp))) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 centry) fc None m (seg_rom usegs)).

Lemma bcmp_cmp : cmp_stmt bcmp_entry.
Proof.
  unfold cmp_stmt. intros until bq. intros LEN P0 Q0 PH QH _ BP BQ MI ST _ _ _.
  eapply evt_cut; [eapply (bcmp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m p q bp bq); try reflexivity; assumption|].
  cbv beta. intros ms' (r & a1' & a2' & a3' & a4' & -> & _).
  apply evt_done. exists r, a1', a2', a3', a4', m. split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI| exact ST].
Qed.

Definition key_row (base centry : Z) : Prop :=
  (base = EL_ATKEY /\ centry = bcmp_entry) \/ (base = EL_ATKEY2 /\ centry = bcmp_entry) \/ (base = EL_ATKEYCI /\ centry = EL_STRNCASECMP).

Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Section Key.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variables base centry : Z.
  Hypothesis ROW : key_row base centry.
  Hypothesis CMP : cmp_stmt centry.

  Notation L := (zlength (ae_p1 E)).

  Definition key_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (OUT lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch [(q - 240, q); (OUT, OUT + 24)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q /\ frm0 fc'
      /\ exists (w0 w1 : word) (code : Z) (od : list byte), rw_cells usegs m' OUT [C8 w0; C8 w1; C4 (Z_to_bv 64 code); CB 4 od]
           /\ (code = 0 \/ code = 17 \/ code = 20).

  Ltac key_fin PO :=
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & m' & -> & MU & WM & MI' & ST' & FRM' & RES);
    apply evt_done; unfold key_post; do 18 eexists; split; [reflexivity|];
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros x Hx; lia|];
    split; [exact WM|]; split; [exact MI'|]; split; [exact ST'|]; split; [exact FRM'| exact RES].

  Lemma key_spec : forall (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node OUT lo : Z) (jo : list byte),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> mem_inv usegs m -> frm0 fc ->
    rw_cells usegs m OUT [CB 24 jo] -> q <= OUT -> OUT + 24 <= ae_B E -> q <= node -> node + 16 <= ae_B E -> q <= ae_DOC E ->
    stk usegs m lo q -> ae_lo E <= lo -> lo + 240 <= q -> (0 < L -> 0 < ae_PTR E) -> ae_PTR E + L <= ae_lo E ->
    evt usegs (key_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT lo m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 OUT) (Z_to_bv 64 node) (Z_to_bv 64 (ae_PTR E)) (Z_to_bv 64 L)
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 base) fc None m (seg_rom usegs)).
  Proof using OK ROW CMP.
    intros until jo. intros AI ROOT HEAP MI FRM OUTC QO O1 QN N1 QDOC ST LOLO LOQ P0 PL.
    destruct ROW as [[HB _]|[[HB _]|[HB _]]]; rewrite HB; unfold EL_ATKEY, EL_ATKEY2, EL_ATKEYCI.
    - eapply evt_cut;
        [eapply (acc_3da20_spec E OK ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s q node OUT lo jo);
         try eassumption; lia|].
      intros ms' PO. unfold acc_3da20_post in PO. key_fin PO.
    - eapply evt_cut;
        [eapply (acc_3dce0_spec E OK ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s q node OUT lo jo);
         try eassumption; lia|].
      intros ms' PO. unfold acc_3dce0_post in PO. key_fin PO.
    - eapply evt_cut;
        [eapply (acc_3dd90_spec E OK ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s q node OUT lo jo);
         try eassumption; lia|].
      intros ms' PO. unfold acc_3dd90_post in PO. key_fin PO.
  Qed.
End Key.
End WithCeiling0.
