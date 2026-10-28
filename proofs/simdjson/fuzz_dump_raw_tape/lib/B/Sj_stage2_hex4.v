(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Layout Sj_tables Sj_stage2_hooks Sj_stage2_strkit Sj_stage2_auto.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_shadow_dig | s2_load_buf | s2_load_dig | s2_load_dig2 | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Definition a_cc (E : s2env) : Prop :=
  forall m', munch (s2_W E) (e_m0 E) m' -> wmono bsegs (e_m0 E) m' ->
    ro_cells bsegs m' g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)]
    /\ ro_cells bsegs m' g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)].

Section Hex4.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Hypothesis CC : a_cc E.
  Notation bs := (e_bs E).

  Definition hex4v (q : Z) : Z :=
    or4 (dig (420 + B bs (q + 1))) (dig (630 + B bs q)) (dig (210 + B bs (q + 2))) (dig (0 + B bs (q + 3))).

  Local Ltac hguard :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if ?c then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
        lazymatch a with
        | 0xe7a54%Z => idtac
        | 0xe7a58%Z => idtac | 0xe7a64%Z => idtac | 0xe7a78%Z => idtac | 0xe7a88%Z => idtac
        | 0xe7a9c%Z => idtac | 0xe7aac%Z => idtac | 0xe7ac0%Z => idtac | 0xe7acc%Z => idtac
        end;
        let K := fresh "KG" in destruct c eqn:K; [ first [ g_solve K | fail 3 "hex4: ASan check not discharged" ] | clear K ]
    end.

  Lemma hex4_call : forall (Q : machine_state -> Prop) (R q : Z) nxt sl sc
      x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    (0 <= R < 2 ^ 64)%Z -> (R mod 2 = 0)%Z ->
    (e_lo E + 16 <= e_spa E)%Z ->
    MEMI E nxt sl sc fc m1 ->
    (0 <= q /\ q + 3 < e_len E + 56)%Z ->
    (forall y5 y10 y11 y12 y13 y14 y15 y16 y17 m1', y10 = Z_to_bv 64 (hex4v q) -> MEMI E nxt sl sc fc m1' ->
       evt bsegs Q (S2R E R (Z_to_bv 64 R) y5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                        x28 x29 x30 x31 F fc m1')) ->
    evt bsegs Q (S2R E 0xe7918 (Z_to_bv 64 R) x5 x6 x7 x8 x9 (Z_to_bv 64 (e_BUF E + q)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                     x28 x29 x30 x31 F fc m1).
  Proof using OK SHZ CC.
    intros Q R q nxt sl sc x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m1 HR0 HR1 HROOM HM HQ K.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (B_range bs q BOK) as HB0. pose proof (B_range bs (q + 1) BOK) as HB1.
    pose proof (B_range bs (q + 2) BOK) as HB2. pose proof (B_range bs (q + 3) BOK) as HB3.
    s2_env OK.
    pose proof HM as HMo. s2_open_mem HMo.
    destruct (CC m1 MU WM) as [G1 G2]. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1, G2.
    zstep.
    carve_frame 16%nat ST.
    apply (rw_cells_split_CB bsegs m1 _ [] 16 junk [] [8;8]%nat) in FR0; [|reflexivity].
    cbn [mk_CB_cells app] in FR0.
    repeat match type of FR0 with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR0; clearbody j end.
    repeat first [ hguard | gstep ].
    rewrite (ret_pc_even R HR0 HR1).
    release_frame FR0 ST (e_spa E).
    eapply K; [unfold hex4v, or4, sxu; rewrite Z.lor_assoc; reflexivity|].
    exact (conj FRM (conj FR (conj SAV (conj GAP (conj FFW (conj IMPL (conj DOCC (conj IDXA (conj BUFRO (conj TAPEW (conj SBUFW
             (conj (ex_intro _ ocs (conj OCA (conj OCL OCR))) (conj (ex_intro _ ias (conj IAA (conj IAL IAR))) (conj MI (conj MU (conj WM (conj ST TIMG))))))))))))))))).
  Qed.
End Hex4.
