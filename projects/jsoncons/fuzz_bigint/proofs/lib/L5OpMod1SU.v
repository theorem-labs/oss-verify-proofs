(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface BigLinkGlue L5Defs L5Core L5CoreSpecsU L5DivSpecsU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigFactsBase.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5OM1SU.
Import L5CSU. Import L5DSU.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition GEN : Z := 0x22798.       (* [comment removed for export] *)
Definition DIV_RET : Z := 0x22494.   (* [comment removed for export] *)
Definition OPF_BACK : Z := 0x20d10.  (* [comment removed for export] *)
Definition COPY_BACK : Z := 0x20d20. (* [comment removed for export] *)
Definition OPF_RETI : Z := 0x20d2c.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition o1_saves (M : word -> option byte) (S : Z) (R0 : bvmap 5 word) : Prop :=
     L5.u64_at RSEGS M (S - 72) DIV_RET /\ L5.u64_at RSEGS M (S - 80) (S + 64) /\ L5.u64_at RSEGS M (S - 88) (U R0 9)
  /\ L5.u64_at RSEGS M (S - 96) (U R0 18) /\ L5.u64_at RSEGS M (S - 104) (U R0 19) /\ L5.u64_at RSEGS M (S - 112) (U R0 20)
  /\ L5.u64_at RSEGS M (S - 120) (U R0 21) /\ L5.u64_at RSEGS M (S - 128) (U R0 22) /\ L5.u64_at RSEGS M (S - 136) (U R0 23)
  /\ L5.u64_at RSEGS M (S - 144) (U R0 24) /\ L5.u64_at RSEGS M (S - 152) (U R0 25) /\ L5.u64_at RSEGS M (S - 160) (U R0 26)
  /\ L5.u64_at RSEGS M (S - 168) (U R0 27).
(* [comment removed for export] *)
Definition top_frame (M : word -> option byte) (S : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (S - 8) (U R0 1) /\ L5.u64_at RSEGS M (S - 16) (U R0 8)
  /\ L5.u64_at RSEGS M (S - 24) OPF_BACK /\ L5.u64_at RSEGS M (S - 32) (S + 96).
(* [comment removed for export] *)
Definition blocks_ofst (st : L5.bstore) : list (Z * Z) := match st with L5.BInl _ _ => [] | L5.BDyn c p => [(p, 8 * c)] end.

(* [comment removed for export] *)
Definition div_entry_regs (S : Z) (R0 Rd : bvmap 5 word) : Prop :=
  getr Rd (reg 1) = Z_to_bv 64 DIV_RET /\ getr Rd (reg 8) = Z_to_bv 64 (S + 64)
  /\ (forall i, In i [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr Rd (reg i) = getr R0 (reg i)).

(* [comment removed for export] *)
Local Ltac regeqs D1 D8 DS :=
  pose proof (D1 : getr _ (Z_to_bv 5 1) = _) as E1; pose proof (D8 : getr _ (Z_to_bv 5 8) = _) as E8;
  pose proof (DS 9%nat ltac:(cbn; tauto) : getr _ (Z_to_bv 5 9) = _) as E9;
  pose proof (DS 18%nat ltac:(cbn; tauto) : getr _ (Z_to_bv 5 18) = _) as E18;
  pose proof (DS 19%nat ltac:(cbn; tauto) : getr _ (Z_to_bv 5 19) = _) as E19;
  pose proof (DS 20%nat ltac:(cbn; tauto) : getr _ (Z_to_bv 5 20) = _) as E20;
  pose proof (DS 21%nat ltac:(cbn; tauto) : getr _ (Z_to_bv 5 21) = _) as E21;
  pose proof (DS 22%nat ltac:(cbn; tauto) : getr _ (Z_to_bv 5 22) = _) as E22;
  pose proof (DS 23%nat ltac:(cbn; tauto) : getr _ (Z_to_bv 5 23) = _) as E23;
  pose proof (DS 24%nat ltac:(cbn; tauto) : getr _ (Z_to_bv 5 24) = _) as E24;
  pose proof (DS 25%nat ltac:(cbn; tauto) : getr _ (Z_to_bv 5 25) = _) as E25;
  pose proof (DS 26%nat ltac:(cbn; tauto) : getr _ (Z_to_bv 5 26) = _) as E26;
  pose proof (DS 27%nat ltac:(cbn; tauto) : getr _ (Z_to_bv 5 27) = _) as E27.
Local Ltac cellA H := lazymatch goal with |- L5.u64_at _ _ ?a ?v => lazymatch type of H with L5.u64_at _ _ ?b ?w =>
  replace a with b by lia; replace v with w; [exact H|] end end.
Lemma o1_saves_div_saves M S R0 Rd : 0 <= S + 64 < 2 ^ 64 -> div_entry_regs S R0 Rd -> o1_saves M S R0 -> div_saves M (S - 64) Rd.
Proof.
  intros HS (D1 & D8 & DS) (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13). regeqs D1 D8 DS. unfold div_saves, U in *.
  rewrite E1, E8, E9, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
  split. { cellA A1. unfold DIV_RET. rewrite BG.unsigned_lit by lia. reflexivity. }
  split. { cellA A2. rewrite BG.unsigned_lit by lia. reflexivity. }
  split. { cellA A3. reflexivity. } split. { cellA A4. reflexivity. } split. { cellA A5. reflexivity. } split. { cellA A6. reflexivity. }
  split. { cellA A7. reflexivity. } split. { cellA A8. reflexivity. } split. { cellA A9. reflexivity. } split. { cellA A10. reflexivity. }
  split. { cellA A11. reflexivity. } split. { cellA A12. reflexivity. } cellA A13. reflexivity.
Qed.
Lemma div_saves_o1_saves M S R0 Rd : 0 <= S + 64 < 2 ^ 64 -> div_entry_regs S R0 Rd -> div_saves M (S - 64) Rd -> o1_saves M S R0.
Proof.
  intros HS (D1 & D8 & DS) (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13). regeqs D1 D8 DS. unfold o1_saves, div_saves, U in *.
  rewrite E1, E8, E9, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27 in *.
  split. { cellA A1. unfold DIV_RET. rewrite BG.unsigned_lit by lia. reflexivity. }
  split. { cellA A2. rewrite BG.unsigned_lit by lia. reflexivity. }
  split. { cellA A3. reflexivity. } split. { cellA A4. reflexivity. } split. { cellA A5. reflexivity. } split. { cellA A6. reflexivity. }
  split. { cellA A7. reflexivity. } split. { cellA A8. reflexivity. } split. { cellA A9. reflexivity. } split. { cellA A10. reflexivity. }
  split. { cellA A11. reflexivity. } split. { cellA A12. reflexivity. } cellA A13. reflexivity.
Qed.

(* [comment removed for export] *)
Definition o1_gen_entry (L : heap_layout) (HI : heap_iface) (LB : list (Z * Z)) (cr : credit) (S : Z) (R0 : bvmap 5 word)
           (M0 : word -> option byte) (model0 : Model) (fbx bo : Z) (bb : L5.bigobj) (wb : list Z)
           (R : bvmap 5 word) (M : word -> option byte) (model : Model) (fnum fden b0 b1 : Z) : Prop :=
  let X := S + 64 in let Q := S - 64 in let spd := S - 416 in let nb := L5.bo_len bb in let qneg := Z.b2z (Z.testbit (L5.bo_fb bb) 1) in
  (* [comment removed for export] *)
     getr R (reg 2) = Z_to_bv 64 spd /\ getr R (reg 3) = Z_to_bv 64 GP /\ getr R (reg 4) = Z_to_bv 64 TP
  /\ getr R (reg 8) = Z_to_bv 64 X /\ getr R (reg 9) = Z_to_bv 64 Q /\ getr R (reg 18) = Z_to_bv 64 X
  /\ getr R (reg 22) = Z_to_bv 64 (Q - 120) /\ getr R (reg 23) = Z_to_bv 64 1
  /\ getr R (reg 25) = Z_to_bv 64 0 /\ getr R (reg 26) = Z_to_bv 64 qneg
  (* [comment removed for export] *)
  /\ hi_heap HI LB cr M (m_vmmaps model) /\ model_but_vm model0 model
  /\ L5.defined M (S - SCR_OPMOD) SCR_OPMOD /\ L5C.hpres L LB S SCR_OPMOD [] M0 M /\ L5.img_clear M 0x10000 0x20000
  (* [comment removed for export] *)
  /\ top_frame M S R0 /\ o1_saves M S R0
  /\ zero_obj M Q /\ x_is_a M X fbx /\ L5.defined M X 32
  (* [comment removed for export] *)
  /\ L5.big_at RSEGS M (Q - 184) (L5.BO fnum 2 (L5.BInl A0 A1)) /\ Z.testbit fnum 1 = false
  /\ L5.bo_st bb = L5.BInl b0 b1 /\ (nb = 1%nat \/ nb = 2%nat)
  /\ L5.big_at RSEGS M (Q - 136) (L5.BO fden nb (L5.BInl b0 b1)) /\ Z.testbit fden 1 = false
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (Q - 152) (Q - 120) /\ L5.u64_at RSEGS M (Q - 144) (Z.of_nat nb)
  /\ L5.u64_at RSEGS M (Q - 232) (Q + 16) /\ L5.u64_at RSEGS M (Q - 224) 0
  /\ L5.u64_at RSEGS M (Q - 248) (X + 16) /\ L5.u64_at RSEGS M (Q - 240) 2
  (* [comment removed for export] *)
  /\ L5.big_at RSEGS M bo bb /\ L5C.obj_limbs RSEGS M bb wb
  (* [comment removed for export] *)
  /\ (nb = 1%nat -> 2 ^ 32 <= b0) /\ (nb = 2%nat -> BigFactsBase.val wb <= BigFactsBase.val [A0; A1]).

End SCFG_1.
End L5OM1SU.
