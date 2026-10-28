(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge Frame Cells Step Mem Arr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_pieces Printf_piecesx Printf_apfmt Printf_ctfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Printf_lib F_pop_arg F_printf_iface F_vsnprintf Printf_sn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import W_bio_printf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_C12 : Z := 0x23fd5.     (* [comment removed for export] *)
Definition A_C13 : Z := 0x2938d.     (* [comment removed for export] *)
Definition A_C14 : Z := 0x2a387.     (* [comment removed for export] *)
Definition A_C15 : Z := 0x2c010.     (* [comment removed for export] *)
Definition A_C1 : Z := 0x2c314.
Definition A_C2 : Z := 0x36db1.
Definition A_C3 : Z := 0x13553.
Definition A_C4 : Z := 0x34357.
Definition A_C5 : Z := 0x302b0.
Definition A_C6 : Z := 0x2ecfd.
Definition A_C7 : Z := 0x2ac5a.
Definition A_C8 : Z := 0x2c0c0.
Definition A_C9 : Z := 0x14aeb.
Definition A_C10 : Z := 0x211f3.    (* [comment removed for export] *)
Definition A_C11 : Z := 0x20650.
Definition A_EMPTY : Z := 0x195be.   (* [comment removed for export] *)
Definition SLK_EMPTY : list Z := [79; 83; 83; 76; 95; 68; 69].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ro_cells_bytes : forall m A n bs, ro_cells ctusegs m A [CB n bs] -> bytes_at ctusegs m A bs.
Proof. intros m A n bs [_ H]. cbn [cells_bytes cbytes app] in H. rewrite app_nil_r in H. exact H. Qed.

Local Ltac rom_lit A :=
  intros m MI;
  lazymatch goal with |- bytes_at _ _ _ ?bs =>
    let bs' := eval cbv in bs in
    change bs with bs';
    apply (ro_cells_bytes m A (length bs') bs');
    apply (ro_cells_image ctusegs m A bs' MI); [vm_compute; reflexivity| unfold A; lia| unfold A; cbn; lia]
  end.

Lemma fmt_C12_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C12 (zb FMT_C12). Proof. rom_lit A_C12. Qed.
Lemma fmt_C13_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C13 (zb FMT_C13). Proof. rom_lit A_C13. Qed.
Lemma fmt_C14_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C14 (zb FMT_C14). Proof. rom_lit A_C14. Qed.
Lemma fmt_C15_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C15 (zb FMT_C15). Proof. rom_lit A_C15. Qed.
Lemma fmt_C1_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C1 (zb FMT_C1). Proof. rom_lit A_C1. Qed.
Lemma fmt_C2_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C2 (zb FMT_C2). Proof. rom_lit A_C2. Qed.
Lemma fmt_C3_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C3 (zb FMT_C3). Proof. rom_lit A_C3. Qed.
Lemma fmt_C4_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C4 (zb FMT_C4). Proof. rom_lit A_C4. Qed.
Lemma fmt_C5_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C5 (zb FMT_C5). Proof. rom_lit A_C5. Qed.
Lemma fmt_C6_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C6 (zb FMT_C6). Proof. rom_lit A_C6. Qed.
Lemma fmt_C7_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C7 (zb FMT_C7). Proof. rom_lit A_C7. Qed.
Lemma fmt_C8_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C8 (zb FMT_C8). Proof. rom_lit A_C8. Qed.
Lemma fmt_C9_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C9 (zb FMT_C9). Proof. rom_lit A_C9. Qed.
Lemma fmt_C10_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C10 (zb FMT_C10). Proof. rom_lit A_C10. Qed.
Lemma fmt_C11_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C11 (zb FMT_C11). Proof. rom_lit A_C11. Qed.
Lemma lit_EMPTY : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_EMPTY (zb [] ++ Z_to_bv 8 0 :: zb SLK_EMPTY). Proof. rom_lit A_EMPTY. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeiling0. Context {CE__ : Ceiling.Ceiling} {RN__ : Rnd.RunRnd}.

(* [comment removed for export] *)
Lemma pcok_C12 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C12 FMT_C12 [Z_to_bv 64 20; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 20; PA_s []] (zrepeat 32 20).
Proof.
  intros m lo q a4 a5 a6 a7 MI SL. pose proof printf_piecesx_C12 as P. pose proof (lit_EMPTY m MI) as HC.
  split; [apply fmt_C12_at; exact MI|]. split; [exact fmt_bytes_C12|]. split; [exact pass1x_ok_C12|].
  split; [unfold A_C12, STATIC_SPLIT; change (zlength FMT_C12) with 4; lia|].
  split.
  { intros m' MU'. cbn [args_ok arg_ok]. rewrite !unsigned_lit by (unfold A_EMPTY; lia).
    split. { split; [lia| reflexivity]. }
    split; [| exact I].
    exists (zb SLK_EMPTY).
    split.
    { eapply bytes_at_transport; [exact HC| exact MU'|]. cbn [disjoint_from zb SLK_EMPTY map Datatypes.length app Z.of_nat Pos.of_succ_nat Pos.succ]. unfold A_EMPTY, STATIC_SPLIT in *.
      repeat split; try exact I; lia. }
    split; [constructor|]. unfold A_EMPTY, STATIC_SPLIT in *.
    cbn [zlength zb SLK_EMPTY map Datatypes.length Z.of_nat Pos.of_succ_nat Pos.succ]. unfold zlength. cbn [Datatypes.length Z.of_nat Pos.of_succ_nat Pos.succ].
    split; [| lia]. change (- (103870 + 0 + 1) mod 8) with 7. lia. }
  split; [change (zlength (zrepeat 32 20)) with 20; replace (zrepeat 32 20) with (concat [[]; zrepeat 32 20; []; []]) by (cbn [concat app]; rewrite app_nil_r; reflexivity);
         apply (printf_modelx_sn _ _ _ _ P); unfold SN_CAP; cbn [concat app]; rewrite app_nil_r, zlength_zrepeat by lia; lia|].
  split; [apply fp_callsx_is0| change (length (zrepeat 32 20)) with 20%nat; lia].
Qed.

(* [comment removed for export] *)
Lemma pcok_C13 : forall m lo q b (a2 a3 a4 a5 a6 a7 : word), mem_inv ctusegs m -> 0 <= b < 256 -> bv_unsigned a2 mod 2^32 = b ->
  printf_call_ok m lo q A_C13 FMT_C13 [a2; a3; a4; a5; a6; a7] [PA_u b] (hex2 b ++ [58]).
Proof.
  intros m lo q b a2 a3 a4 a5 a6 a7 MI Hb Ha2.
  destruct (printf_piecesx_C13 b Hb) as (ps & P & CC). pose proof (printf_piecesx_count _ _ _ _ P) as L.
  split; [apply fmt_C13_at; exact MI|]. split; [exact fmt_bytes_C13|]. split; [exact pass1x_ok_C13|].
  split; [unfold A_C13, STATIC_SPLIT; change (zlength FMT_C13) with 6; lia|].
  split. { intros m' MU'. cbn [args_ok arg_ok]. split; [| exact I]. split; [lia| exact Ha2]. }
  rewrite <- CC. split; [rewrite L; apply (printf_modelx_sn _ _ _ _ P); rewrite L; unfold SN_CAP; lia|].
  split; [apply fp_callsx_u| unfold zlength in L; lia].
Qed.

(* [comment removed for export] *)
Lemma pcok_C14 : forall m lo q (a2 a3 a4 a5 a6 a7 : word), mem_inv ctusegs m ->
  printf_call_ok m lo q A_C14 FMT_C14 [a2; a3; a4; a5; a6; a7] [] [10].
Proof.
  intros m lo q a2 a3 a4 a5 a6 a7 MI. pose proof printf_piecesx_C14 as P.
  split; [apply fmt_C14_at; exact MI|]. split; [exact fmt_bytes_C14|]. split; [exact pass1x_ok_C14|].
  split; [unfold A_C14, STATIC_SPLIT; change (zlength FMT_C14) with 2; lia|].
  split. { intros m' MU'. exact I. }
  split; [change [10] with (concat [[10]]); change (zlength (concat [[10]])) with 1; apply (printf_modelx_sn _ _ _ _ P); unfold SN_CAP; change (zlength (concat [[10]])) with 1; lia|].
  split; [apply fp_callsx_nil| cbn [length]; lia].
Qed.

(* [comment removed for export] *)
Lemma pcok_C15 : forall m lo q b (a2 a3 a4 a5 a6 a7 : word), mem_inv ctusegs m -> 0 <= b < 256 -> bv_unsigned a2 mod 2^32 = b ->
  printf_call_ok m lo q A_C15 FMT_C15 [a2; a3; a4; a5; a6; a7] [PA_u b] (hex2 b).
Proof.
  intros m lo q b a2 a3 a4 a5 a6 a7 MI Hb Ha2.
  destruct (printf_piecesx_C15 b Hb) as (ps & P & CC). pose proof (printf_piecesx_count _ _ _ _ P) as L.
  split; [apply fmt_C15_at; exact MI|]. split; [exact fmt_bytes_C15|]. split; [exact pass1x_ok_C15|].
  split; [unfold A_C15, STATIC_SPLIT; change (zlength FMT_C15) with 5; lia|].
  split. { intros m' MU'. cbn [args_ok arg_ok]. split; [| exact I]. split; [lia| exact Ha2]. }
  rewrite <- CC. split; [rewrite L; apply (printf_modelx_sn _ _ _ _ P); rewrite L; unfold SN_CAP; lia|].
  split; [apply fp_callsx_u| unfold zlength in L; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pcok_wstar : forall m lo q A fmt w ps r (a4 a5 a6 a7 : word),
  mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  bytes_at ctusegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1x_ok fmt = true -> 65536 <= A -> A + zlength fmt <= STATIC_SPLIT ->
  0 <= w < 2^31 ->
  printf_piecesx fmt [PA_i w; PA_s []] = Some (ps, r) -> r <= 80 ->
  printf_call_ok m lo q A fmt [Z_to_bv 64 w; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i w; PA_s []] (concat ps).
Proof.
  intros until a7. intros MI SL BY FB P1 A0 A1 Hw P Hr. pose proof (lit_EMPTY m MI) as HC. pose proof (printf_piecesx_count _ _ _ _ P) as L.
  split; [exact BY|]. split; [exact FB|]. split; [exact P1|]. split; [lia|].
  split.
  { intros m' MU'. cbn [args_ok arg_ok]. rewrite !unsigned_lit by (unfold A_EMPTY; lia).
    split. { split; [lia| rewrite (Z.mod_small w) by lia; reflexivity]. }
    split; [| exact I].
    exists (zb SLK_EMPTY).
    split.
    { eapply bytes_at_transport; [exact HC| exact MU'|]. cbn [disjoint_from zb SLK_EMPTY map Datatypes.length app Z.of_nat Pos.of_succ_nat Pos.succ]. unfold A_EMPTY, STATIC_SPLIT in *.
      repeat split; try exact I; lia. }
    split; [constructor|]. unfold A_EMPTY, STATIC_SPLIT in *.
    cbn [zlength zb SLK_EMPTY map Datatypes.length Z.of_nat Pos.of_succ_nat Pos.succ]. unfold zlength. cbn [Datatypes.length Z.of_nat Pos.of_succ_nat Pos.succ].
    split; [| lia]. change (- (103870 + 0 + 1) mod 8) with 7. lia. }
  split; [rewrite L; apply (printf_modelx_sn _ _ _ _ P); unfold SN_CAP; rewrite L; exact Hr|].
  split; [apply fp_callsx_is0| unfold zlength in L; lia].
Qed.

Definition O_C1 : list Z := [32; 32; 32; 32; 83; 105; 103; 110; 101; 100; 32; 67; 101; 114; 116; 105; 102; 105; 99; 97; 116; 101; 32; 84; 105; 109; 101; 115; 116; 97; 109; 112; 58].
Lemma pcok_C1 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C1 FMT_C1 [Z_to_bv 64 4; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 4; PA_s []] O_C1.
Proof.
  intros m lo q a4 a5 a6 a7 MI SL.
  replace O_C1 with (concat (fst ((fun x => match x with Some p => p | None => ([], 0) end) (printf_piecesx FMT_C1 [PA_i 4; PA_s []])))) by (vm_compute; reflexivity).
  rewrite printf_piecesx_C1. cbn [fst].
  eapply pcok_wstar; [exact MI| exact SL| apply fmt_C1_at; exact MI| exact fmt_bytes_C1| exact pass1x_ok_C1| unfold A_C1; lia
    | unfold A_C1, STATIC_SPLIT; change (zlength FMT_C1) with 33; lia| lia| exact printf_piecesx_C1| lia].
Qed.
Lemma zlength_O_C1 : zlength O_C1 = 33. Proof. reflexivity. Qed.

Definition O_C2 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 86; 101; 114; 115; 105; 111; 110; 32; 32; 32; 58; 32].
Lemma pcok_C2 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C2 FMT_C2 [Z_to_bv 64 8; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 8; PA_s []] O_C2.
Proof.
  intros m lo q a4 a5 a6 a7 MI SL.
  replace O_C2 with (concat (fst ((fun x => match x with Some p => p | None => ([], 0) end) (printf_piecesx FMT_C2 [PA_i 8; PA_s []])))) by (vm_compute; reflexivity).
  rewrite printf_piecesx_C2. cbn [fst].
  eapply pcok_wstar; [exact MI| exact SL| apply fmt_C2_at; exact MI| exact fmt_bytes_C2| exact pass1x_ok_C2| unfold A_C2; lia
    | unfold A_C2, STATIC_SPLIT; change (zlength FMT_C2) with 17; lia| lia| exact printf_piecesx_C2| lia].
Qed.
Lemma zlength_O_C2 : zlength O_C2 = 21. Proof. reflexivity. Qed.

Definition O_C3 : list Z := [117; 110; 107; 110; 111; 119; 110; 10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32].
Lemma pcok_C3 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C3 FMT_C3 [Z_to_bv 64 20; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 20; PA_s []] O_C3.
Proof.
  intros m lo q a4 a5 a6 a7 MI SL.
  replace O_C3 with (concat (fst ((fun x => match x with Some p => p | None => ([], 0) end) (printf_piecesx FMT_C3 [PA_i 20; PA_s []])))) by (vm_compute; reflexivity).
  rewrite printf_piecesx_C3. cbn [fst].
  eapply pcok_wstar; [exact MI| exact SL| apply fmt_C3_at; exact MI| exact fmt_bytes_C3| exact pass1x_ok_C3| unfold A_C3; lia
    | unfold A_C3, STATIC_SPLIT; change (zlength FMT_C3) with 12; lia| lia| exact printf_piecesx_C3| lia].
Qed.
Lemma zlength_O_C3 : zlength O_C3 = 28. Proof. reflexivity. Qed.

Definition O_C5 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 76; 111; 103; 32; 73; 68; 32; 32; 32; 32; 58; 32].
Lemma pcok_C5 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C5 FMT_C5 [Z_to_bv 64 8; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 8; PA_s []] O_C5.
Proof.
  intros m lo q a4 a5 a6 a7 MI SL.
  replace O_C5 with (concat (fst ((fun x => match x with Some p => p | None => ([], 0) end) (printf_piecesx FMT_C5 [PA_i 8; PA_s []])))) by (vm_compute; reflexivity).
  rewrite printf_piecesx_C5. cbn [fst].
  eapply pcok_wstar; [exact MI| exact SL| apply fmt_C5_at; exact MI| exact fmt_bytes_C5| exact pass1x_ok_C5| unfold A_C5; lia
    | unfold A_C5, STATIC_SPLIT; change (zlength FMT_C5) with 17; lia| lia| exact printf_piecesx_C5| lia].
Qed.
Lemma zlength_O_C5 : zlength O_C5 = 21. Proof. reflexivity. Qed.

Definition O_C6 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 84; 105; 109; 101; 115; 116; 97; 109; 112; 32; 58; 32].
Lemma pcok_C6 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C6 FMT_C6 [Z_to_bv 64 8; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 8; PA_s []] O_C6.
Proof.
  intros m lo q a4 a5 a6 a7 MI SL.
  replace O_C6 with (concat (fst ((fun x => match x with Some p => p | None => ([], 0) end) (printf_piecesx FMT_C6 [PA_i 8; PA_s []])))) by (vm_compute; reflexivity).
  rewrite printf_piecesx_C6. cbn [fst].
  eapply pcok_wstar; [exact MI| exact SL| apply fmt_C6_at; exact MI| exact fmt_bytes_C6| exact pass1x_ok_C6| unfold A_C6; lia
    | unfold A_C6, STATIC_SPLIT; change (zlength FMT_C6) with 17; lia| lia| exact printf_piecesx_C6| lia].
Qed.
Lemma zlength_O_C6 : zlength O_C6 = 21. Proof. reflexivity. Qed.

Definition O_C7 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 69; 120; 116; 101; 110; 115; 105; 111; 110; 115; 58; 32].
Lemma pcok_C7 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C7 FMT_C7 [Z_to_bv 64 8; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 8; PA_s []] O_C7.
Proof.
  intros m lo q a4 a5 a6 a7 MI SL.
  replace O_C7 with (concat (fst ((fun x => match x with Some p => p | None => ([], 0) end) (printf_piecesx FMT_C7 [PA_i 8; PA_s []])))) by (vm_compute; reflexivity).
  rewrite printf_piecesx_C7. cbn [fst].
  eapply pcok_wstar; [exact MI| exact SL| apply fmt_C7_at; exact MI| exact fmt_bytes_C7| exact pass1x_ok_C7| unfold A_C7; lia
    | unfold A_C7, STATIC_SPLIT; change (zlength FMT_C7) with 17; lia| lia| exact printf_piecesx_C7| lia].
Qed.
Lemma zlength_O_C7 : zlength O_C7 = 21. Proof. reflexivity. Qed.

Definition O_C9 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 83; 105; 103; 110; 97; 116; 117; 114; 101; 32; 58; 32].
Lemma pcok_C9 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C9 FMT_C9 [Z_to_bv 64 8; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 8; PA_s []] O_C9.
Proof.
  intros m lo q a4 a5 a6 a7 MI SL.
  replace O_C9 with (concat (fst ((fun x => match x with Some p => p | None => ([], 0) end) (printf_piecesx FMT_C9 [PA_i 8; PA_s []])))) by (vm_compute; reflexivity).
  rewrite printf_piecesx_C9. cbn [fst].
  eapply pcok_wstar; [exact MI| exact SL| apply fmt_C9_at; exact MI| exact fmt_bytes_C9| exact pass1x_ok_C9| unfold A_C9; lia
    | unfold A_C9, STATIC_SPLIT; change (zlength FMT_C9) with 17; lia| lia| exact printf_piecesx_C9| lia].
Qed.
Lemma zlength_O_C9 : zlength O_C9 = 21. Proof. reflexivity. Qed.

Definition O_C11 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32].
Lemma pcok_C11 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C11 FMT_C11 [Z_to_bv 64 8; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 8; PA_s []] O_C11.
Proof.
  intros m lo q a4 a5 a6 a7 MI SL.
  replace O_C11 with (concat (fst ((fun x => match x with Some p => p | None => ([], 0) end) (printf_piecesx FMT_C11 [PA_i 8; PA_s []])))) by (vm_compute; reflexivity).
  rewrite printf_piecesx_C11. cbn [fst].
  eapply pcok_wstar; [exact MI| exact SL| apply fmt_C11_at; exact MI| exact fmt_bytes_C11| exact pass1x_ok_C11| unfold A_C11; lia
    | unfold A_C11, STATIC_SPLIT; change (zlength FMT_C11) with 17; lia| lia| exact printf_piecesx_C11| lia].
Qed.
Lemma zlength_O_C11 : zlength O_C11 = 21. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition O_C4 : list Z := [118; 49; 32; 40; 48; 120; 48; 41].
Lemma pcok_C4 : forall m lo q (a2 a3 a4 a5 a6 a7 : word), mem_inv ctusegs m ->
  printf_call_ok m lo q A_C4 FMT_C4 [a2; a3; a4; a5; a6; a7] [] O_C4.
Proof.
  intros m lo q a2 a3 a4 a5 a6 a7 MI. pose proof printf_piecesx_C4 as P.
  split; [apply fmt_C4_at; exact MI|]. split; [exact fmt_bytes_C4|]. split; [exact pass1x_ok_C4|].
  split; [unfold A_C4, STATIC_SPLIT; change (zlength FMT_C4) with 9; lia|].
  split. { intros m' MU'. exact I. }
  split; [change O_C4 with (concat [[118; 49; 32; 40; 48; 120; 48; 41]]); change (zlength (concat [[118; 49; 32; 40; 48; 120; 48; 41]])) with 8;
         apply (printf_modelx_sn _ _ _ _ P); unfold SN_CAP; change (zlength (concat [[118; 49; 32; 40; 48; 120; 48; 41]])) with 8; lia|].
  split; [apply fp_callsx_nil| cbn [length O_C4]; lia].
Qed.
Definition O_C8 : list Z := [110; 111; 110; 101].
Lemma pcok_C8 : forall m lo q (a2 a3 a4 a5 a6 a7 : word), mem_inv ctusegs m ->
  printf_call_ok m lo q A_C8 FMT_C8 [a2; a3; a4; a5; a6; a7] [] O_C8.
Proof.
  intros m lo q a2 a3 a4 a5 a6 a7 MI. pose proof printf_piecesx_C8 as P.
  split; [apply fmt_C8_at; exact MI|]. split; [exact fmt_bytes_C8|]. split; [exact pass1x_ok_C8|].
  split; [unfold A_C8, STATIC_SPLIT; change (zlength FMT_C8) with 5; lia|].
  split. { intros m' MU'. exact I. }
  split; [change O_C8 with (concat [[110; 111; 110; 101]]); change (zlength (concat [[110; 111; 110; 101]])) with 4;
         apply (printf_modelx_sn _ _ _ _ P); unfold SN_CAP; change (zlength (concat [[110; 111; 110; 101]])) with 4; lia|].
  split; [apply fp_callsx_nil| cbn [length O_C8]; lia].
Qed.

(* [comment removed for export] *)
Lemma pcok_C10 : forall m lo q A (LN : Z) (s : list Z) (slack : list byte) (a3 a4 a5 a6 a7 : word),
  mem_inv ctusegs m -> STATIC_SPLIT <= lo -> bytes_at ctusegs m A (zb FMT_C10) -> 65536 <= A -> A + 3 <= STATIC_SPLIT ->
  bytes_at ctusegs m LN (zb s ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256) s -> length slack = 7%nat ->
  65536 <= LN -> LN + zlength s + 8 <= STATIC_SPLIT -> zlength s <= 80 ->
  printf_call_ok m lo q A FMT_C10 [Z_to_bv 64 LN; a3; a4; a5; a6; a7] [PA_s s] s.
Proof.
  intros until a7. intros MI SL BY A0 A1 HS RNG SLK L0 L1 LS.
  pose proof (zlength_nonneg'' s) as S0.
  destruct (printf_piecesx_C10 s ltac:(lia)) as (ps & P & CC). pose proof (printf_piecesx_count _ _ _ _ P) as L.
  split; [exact BY|]. split; [exact fmt_bytes_C10|]. split; [exact pass1x_ok_C10|].
  split; [change (zlength FMT_C10) with 3; lia|].
  split.
  { intros m' MU'. cbn [args_ok arg_ok]. rewrite !unsigned_lit by (unfold STATIC_SPLIT in *; lia). split; [| exact I].
    exists slack. split.
    { eapply bytes_at_transport; [exact HS| exact MU'|]. cbn [disjoint_from]. unfold zb. rewrite length_app, length_map. cbn [length]. rewrite SLK.
      unfold STATIC_SPLIT, zlength in *. repeat split; try exact I; lia. }
    split; [exact RNG|]. unfold zlength in *. rewrite SLK. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unfold STATIC_SPLIT in *.
    change (Z.of_nat 7) with 7.
    split; [pose proof (Z.mod_pos_bound (- (LN + Z.of_nat (length s) + 1)) 8 ltac:(lia)); lia| lia]. }
  assert (MD : printf_modelx OUT_sn OUTFP_sn FMT_C10 [PA_s s] [] = ITree.Ret (ITree.Exc.Ok (zlength s, s))).
  { rewrite <- CC at 3. apply (printf_modelx_sn _ _ _ _ P). rewrite CC. unfold SN_CAP. lia. }
  split; [exact MD|].
  split; [apply fp_callsx_nog; repeat constructor| unfold zlength in LS; lia].
Qed.

Lemma zlength_hex2 : forall b, zlength (hex2 b) = 2. Proof. intros. reflexivity. Qed.
Lemma zlength_hex2c : forall b, zlength (hex2 b ++ [58]) = 3. Proof. intros. reflexivity. Qed.

End WithCeiling0.
