(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
Proof.
  intros m A n bs Cells.
  exact (bytes_at_ext ctusegs m A _ bs (proj2 Cells) (app_nil_r bs)).
Qed.

Local Ltac rom_lit addr :=
  let mm := fresh "mm" in
  let Inv := fresh "Inv" in
  intros mm Inv;
  refine (ro_bytes_at ctusegs mm addr _ Inv _ _ (ro_bytes_b_sound ctusegs _ addr _));
  [ apply Z.leb_le | apply Z.leb_le | ];
  vm_compute; reflexivity.

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
Lemma lit_EMPTY : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_EMPTY (zb [] ++ Z_to_bv 8 0 :: zb SLK_EMPTY).
Proof. rom_lit A_EMPTY. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeiling0. Context {CE__ : Ceiling.Ceiling} {RN__ : Rnd.RunRnd}.

(* [comment removed for export] *)
Lemma pcok_C12 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C12 FMT_C12 [Z_to_bv 64 20; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 20; PA_s []] (zrepeat 32 20).
Proof.
  intros m lo q a4 a5 a6 a7 Rom Above.
  pose proof (printf_modelx_sn _ _ _ _ printf_piecesx_C12 ltac:(apply Z.leb_le; vm_compute; reflexivity)) as Model.
  assert (Gap : disjoint_from [(lo, q)] A_EMPTY (Z.of_nat (length (zb [] ++ Z_to_bv 8 0 :: zb SLK_EMPTY)))).
  { split; [left| exact I].
    apply (Z.le_trans _ STATIC_SPLIT _); [apply Z.leb_le; vm_compute; reflexivity| exact Above]. }
  unfold printf_call_ok.
  refine (conj (fmt_C12_at m Rom) (conj fmt_bytes_C12 (conj pass1x_ok_C12
            (conj _ (conj _ (conj Model (conj (fp_callsx_is0 _ _ _) _))))))).
  - split; apply Z.leb_le; vm_compute; reflexivity.
  - intros m' Munched. cbn [args_ok arg_ok].
    change (bv_unsigned (Z_to_bv 64 A_EMPTY)) with A_EMPTY.
    pose proof (bytes_at_transport ctusegs [(lo, q)] m m' A_EMPTY _ (lit_EMPTY m Rom) Munched Gap) as Moved.
    refine (conj (conj _ eq_refl) (conj _ I)); [lia|].
    exists (zb SLK_EMPTY). refine (conj Moved (conj (Forall_nil _) _)).
    change (zlength (zb SLK_EMPTY)) with 7. change (zlength (@nil Z)) with 0.
    unfold A_EMPTY. unfold STATIC_SPLIT in Above. lia.
  - apply Nat.ltb_lt. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pcok_C13 : forall m lo q b (a2 a3 a4 a5 a6 a7 : word), mem_inv ctusegs m -> 0 <= b < 256 -> bv_unsigned a2 mod 2^32 = b ->
  printf_call_ok m lo q A_C13 FMT_C13 [a2; a3; a4; a5; a6; a7] [PA_u b] (hex2 b ++ [58]).
Proof.
  intros m lo q b a2 a3 a4 a5 a6 a7 Rom ByteB SlotB.
  destruct (printf_piecesx_C13 b ByteB) as (ps & Pcs & Cat).
  pose proof (printf_modelx_sn _ _ _ _ Pcs) as Model. rewrite Cat in Model.
  unfold printf_call_ok.
  refine (conj (fmt_C13_at m Rom) (conj fmt_bytes_C13 (conj pass1x_ok_C13
            (conj _ (conj _ (conj (Model _) (conj (fp_callsx_u _ _ _) _))))))).
  - split; apply Z.leb_le; vm_compute; reflexivity.
  - intros m' _. cbn [args_ok arg_ok]. refine (conj (conj _ SlotB) I). lia.
  - apply Z.leb_le. vm_compute. reflexivity.
  - apply Nat.ltb_lt. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pcok_C14 : forall m lo q (a2 a3 a4 a5 a6 a7 : word), mem_inv ctusegs m ->
  printf_call_ok m lo q A_C14 FMT_C14 [a2; a3; a4; a5; a6; a7] [] [10].
Proof.
  intros m lo q a2 a3 a4 a5 a6 a7 Rom.
  pose proof (printf_modelx_sn _ _ _ _ printf_piecesx_C14 ltac:(apply Z.leb_le; vm_compute; reflexivity)) as Model.
  unfold printf_call_ok.
  refine (conj (fmt_C14_at m Rom) (conj fmt_bytes_C14 (conj pass1x_ok_C14
            (conj _ (conj (fun m' _ => I) (conj Model (conj (fp_callsx_nil _ _) _))))))).
  - split; apply Z.leb_le; vm_compute; reflexivity.
  - apply Nat.ltb_lt. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pcok_C15 : forall m lo q b (a2 a3 a4 a5 a6 a7 : word), mem_inv ctusegs m -> 0 <= b < 256 -> bv_unsigned a2 mod 2^32 = b ->
  printf_call_ok m lo q A_C15 FMT_C15 [a2; a3; a4; a5; a6; a7] [PA_u b] (hex2 b).
Proof.
  intros m lo q b a2 a3 a4 a5 a6 a7 Rom ByteB SlotB.
  destruct (printf_piecesx_C15 b ByteB) as (ps & Pcs & Cat).
  pose proof (printf_modelx_sn _ _ _ _ Pcs) as Model. rewrite Cat in Model.
  unfold printf_call_ok.
  refine (conj (fmt_C15_at m Rom) (conj fmt_bytes_C15 (conj pass1x_ok_C15
            (conj _ (conj _ (conj (Model _) (conj (fp_callsx_u _ _ _) _))))))).
  - split; apply Z.leb_le; vm_compute; reflexivity.
  - intros m' _. cbn [args_ok arg_ok]. refine (conj (conj _ SlotB) I). lia.
  - apply Z.leb_le. vm_compute. reflexivity.
  - apply Nat.ltb_lt. vm_compute. reflexivity.
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
  intros m lo q A fmt w ps r a4 a5 a6 a7 Rom Above FmtAt FmtByt FmtP1 Lo64k HiSplit WRng Pcs Cap.
  pose proof (printf_piecesx_count _ _ _ _ Pcs) as Cnt.
  pose proof (printf_modelx_sn _ _ _ _ Pcs ltac:(unfold SN_CAP; lia)) as Model.
  rewrite <- Cnt in Model.
  assert (Gap : disjoint_from [(lo, q)] A_EMPTY (Z.of_nat (length (zb [] ++ Z_to_bv 8 0 :: zb SLK_EMPTY)))).
  { split; [left| exact I].
    apply (Z.le_trans _ STATIC_SPLIT _); [apply Z.leb_le; vm_compute; reflexivity| exact Above]. }
  assert (Short : (length (concat ps) < 512)%nat) by (unfold zlength in Cnt; lia).
  unfold printf_call_ok.
  refine (conj FmtAt (conj FmtByt (conj FmtP1
            (conj (conj Lo64k HiSplit) (conj _ (conj Model (conj (fp_callsx_is0 _ _ _) Short))))))).
  intros m' Munched. cbn [args_ok arg_ok].
  rewrite (unsigned_lit w) by lia.
  change (bv_unsigned (Z_to_bv 64 A_EMPTY)) with A_EMPTY.
  pose proof (bytes_at_transport ctusegs [(lo, q)] m m' A_EMPTY _ (lit_EMPTY m Rom) Munched Gap) as Moved.
  refine (conj (conj _ eq_refl) (conj _ I)); [lia|].
  exists (zb SLK_EMPTY). refine (conj Moved (conj (Forall_nil _) _)).
  change (zlength (zb SLK_EMPTY)) with 7. change (zlength (@nil Z)) with 0.
  unfold A_EMPTY. unfold STATIC_SPLIT in Above. lia.
Qed.

Definition O_C1 : list Z := [32; 32; 32; 32; 83; 105; 103; 110; 101; 100; 32; 67; 101; 114; 116; 105; 102; 105; 99; 97; 116; 101; 32; 84; 105; 109; 101; 115; 116; 97; 109; 112; 58].
Lemma pcok_C1 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C1 FMT_C1 [Z_to_bv 64 4; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 4; PA_s []] O_C1.
Proof.
  intros m lo q a4 a5 a6 a7 Rom Above.
  refine (pcok_wstar m lo q A_C1 FMT_C1 4 _ _ a4 a5 a6 a7 Rom Above (fmt_C1_at m Rom) fmt_bytes_C1 pass1x_ok_C1
            _ _ _ printf_piecesx_C1 _);
    first [lia| apply Z.leb_le; vm_compute; reflexivity].
Qed.
Lemma zlength_O_C1 : zlength O_C1 = 33. Proof. reflexivity. Qed.

Definition O_C2 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 86; 101; 114; 115; 105; 111; 110; 32; 32; 32; 58; 32].
Lemma pcok_C2 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C2 FMT_C2 [Z_to_bv 64 8; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 8; PA_s []] O_C2.
Proof.
  intros m lo q a4 a5 a6 a7 Rom Above.
  refine (pcok_wstar m lo q A_C2 FMT_C2 8 _ _ a4 a5 a6 a7 Rom Above (fmt_C2_at m Rom) fmt_bytes_C2 pass1x_ok_C2
            _ _ _ printf_piecesx_C2 _);
    first [lia| apply Z.leb_le; vm_compute; reflexivity].
Qed.
Lemma zlength_O_C2 : zlength O_C2 = 21. Proof. reflexivity. Qed.

Definition O_C3 : list Z := [117; 110; 107; 110; 111; 119; 110; 10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32].
Lemma pcok_C3 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C3 FMT_C3 [Z_to_bv 64 20; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 20; PA_s []] O_C3.
Proof.
  intros m lo q a4 a5 a6 a7 Rom Above.
  refine (pcok_wstar m lo q A_C3 FMT_C3 20 _ _ a4 a5 a6 a7 Rom Above (fmt_C3_at m Rom) fmt_bytes_C3 pass1x_ok_C3
            _ _ _ printf_piecesx_C3 _);
    first [lia| apply Z.leb_le; vm_compute; reflexivity].
Qed.
Lemma zlength_O_C3 : zlength O_C3 = 28. Proof. reflexivity. Qed.

Definition O_C5 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 76; 111; 103; 32; 73; 68; 32; 32; 32; 32; 58; 32].
Lemma pcok_C5 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C5 FMT_C5 [Z_to_bv 64 8; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 8; PA_s []] O_C5.
Proof.
  intros m lo q a4 a5 a6 a7 Rom Above.
  refine (pcok_wstar m lo q A_C5 FMT_C5 8 _ _ a4 a5 a6 a7 Rom Above (fmt_C5_at m Rom) fmt_bytes_C5 pass1x_ok_C5
            _ _ _ printf_piecesx_C5 _);
    first [lia| apply Z.leb_le; vm_compute; reflexivity].
Qed.
Lemma zlength_O_C5 : zlength O_C5 = 21. Proof. reflexivity. Qed.

Definition O_C6 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 84; 105; 109; 101; 115; 116; 97; 109; 112; 32; 58; 32].
Lemma pcok_C6 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C6 FMT_C6 [Z_to_bv 64 8; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 8; PA_s []] O_C6.
Proof.
  intros m lo q a4 a5 a6 a7 Rom Above.
  refine (pcok_wstar m lo q A_C6 FMT_C6 8 _ _ a4 a5 a6 a7 Rom Above (fmt_C6_at m Rom) fmt_bytes_C6 pass1x_ok_C6
            _ _ _ printf_piecesx_C6 _);
    first [lia| apply Z.leb_le; vm_compute; reflexivity].
Qed.
Lemma zlength_O_C6 : zlength O_C6 = 21. Proof. reflexivity. Qed.

Definition O_C7 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 69; 120; 116; 101; 110; 115; 105; 111; 110; 115; 58; 32].
Lemma pcok_C7 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C7 FMT_C7 [Z_to_bv 64 8; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 8; PA_s []] O_C7.
Proof.
  intros m lo q a4 a5 a6 a7 Rom Above.
  refine (pcok_wstar m lo q A_C7 FMT_C7 8 _ _ a4 a5 a6 a7 Rom Above (fmt_C7_at m Rom) fmt_bytes_C7 pass1x_ok_C7
            _ _ _ printf_piecesx_C7 _);
    first [lia| apply Z.leb_le; vm_compute; reflexivity].
Qed.
Lemma zlength_O_C7 : zlength O_C7 = 21. Proof. reflexivity. Qed.

Definition O_C9 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 83; 105; 103; 110; 97; 116; 117; 114; 101; 32; 58; 32].
Lemma pcok_C9 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C9 FMT_C9 [Z_to_bv 64 8; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 8; PA_s []] O_C9.
Proof.
  intros m lo q a4 a5 a6 a7 Rom Above.
  refine (pcok_wstar m lo q A_C9 FMT_C9 8 _ _ a4 a5 a6 a7 Rom Above (fmt_C9_at m Rom) fmt_bytes_C9 pass1x_ok_C9
            _ _ _ printf_piecesx_C9 _);
    first [lia| apply Z.leb_le; vm_compute; reflexivity].
Qed.
Lemma zlength_O_C9 : zlength O_C9 = 21. Proof. reflexivity. Qed.

Definition O_C11 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32].
Lemma pcok_C11 : forall m lo q (a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C11 FMT_C11 [Z_to_bv 64 8; Z_to_bv 64 A_EMPTY; a4; a5; a6; a7] [PA_i 8; PA_s []] O_C11.
Proof.
  intros m lo q a4 a5 a6 a7 Rom Above.
  refine (pcok_wstar m lo q A_C11 FMT_C11 8 _ _ a4 a5 a6 a7 Rom Above (fmt_C11_at m Rom) fmt_bytes_C11 pass1x_ok_C11
            _ _ _ printf_piecesx_C11 _);
    first [lia| apply Z.leb_le; vm_compute; reflexivity].
Qed.
Lemma zlength_O_C11 : zlength O_C11 = 21. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition O_C4 : list Z := [118; 49; 32; 40; 48; 120; 48; 41].
Lemma pcok_C4 : forall m lo q (a2 a3 a4 a5 a6 a7 : word), mem_inv ctusegs m ->
  printf_call_ok m lo q A_C4 FMT_C4 [a2; a3; a4; a5; a6; a7] [] O_C4.
Proof.
  intros m lo q a2 a3 a4 a5 a6 a7 Rom.
  pose proof (printf_modelx_sn _ _ _ _ printf_piecesx_C4 ltac:(apply Z.leb_le; vm_compute; reflexivity)) as Model.
  unfold printf_call_ok.
  refine (conj (fmt_C4_at m Rom) (conj fmt_bytes_C4 (conj pass1x_ok_C4
            (conj _ (conj (fun m' _ => I) (conj Model (conj (fp_callsx_nil _ _) _))))))).
  - split; apply Z.leb_le; vm_compute; reflexivity.
  - apply Nat.ltb_lt. vm_compute. reflexivity.
Qed.
Definition O_C8 : list Z := [110; 111; 110; 101].
Lemma pcok_C8 : forall m lo q (a2 a3 a4 a5 a6 a7 : word), mem_inv ctusegs m ->
  printf_call_ok m lo q A_C8 FMT_C8 [a2; a3; a4; a5; a6; a7] [] O_C8.
Proof.
  intros m lo q a2 a3 a4 a5 a6 a7 Rom.
  pose proof (printf_modelx_sn _ _ _ _ printf_piecesx_C8 ltac:(apply Z.leb_le; vm_compute; reflexivity)) as Model.
  unfold printf_call_ok.
  refine (conj (fmt_C8_at m Rom) (conj fmt_bytes_C8 (conj pass1x_ok_C8
            (conj _ (conj (fun m' _ => I) (conj Model (conj (fp_callsx_nil _ _) _))))))).
  - split; apply Z.leb_le; vm_compute; reflexivity.
  - apply Nat.ltb_lt. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pcok_C10 : forall m lo q A (LN : Z) (s : list Z) (slack : list byte) (a3 a4 a5 a6 a7 : word),
  mem_inv ctusegs m -> STATIC_SPLIT <= lo -> bytes_at ctusegs m A (zb FMT_C10) -> 65536 <= A -> A + 3 <= STATIC_SPLIT ->
  bytes_at ctusegs m LN (zb s ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256) s -> length slack = 7%nat ->
  65536 <= LN -> LN + zlength s + 8 <= STATIC_SPLIT -> zlength s <= 80 ->
  printf_call_ok m lo q A FMT_C10 [Z_to_bv 64 LN; a3; a4; a5; a6; a7] [PA_s s] s.
Proof.
  intros m lo q A LN s slack a3 a4 a5 a6 a7 Rom Above FmtAt ALo AHi StrAt StrByt SlkLen LNLo LNHi SLen.
  destruct (printf_piecesx_C10 s ltac:(lia)) as (ps & Pcs & Cat).
  pose proof (printf_modelx_sn _ _ _ _ Pcs ltac:(rewrite Cat; unfold SN_CAP; lia)) as Model.
  rewrite Cat in Model.
  assert (SlkZ : zlength slack = 7) by (unfold zlength; rewrite SlkLen; reflexivity).
  assert (Span : Z.of_nat (length (zb s ++ Z_to_bv 8 0 :: slack)) = zlength s + 8).
  { unfold zb, zlength in *. rewrite length_app, length_map. cbn [length]. lia. }
  assert (SlotLN : bv_unsigned (Z_to_bv 64 LN) = LN).
  { apply unsigned_lit. unfold STATIC_SPLIT, zlength in LNHi. lia. }
  unfold printf_call_ok.
  refine (conj FmtAt (conj fmt_bytes_C10 (conj pass1x_ok_C10
            (conj (conj ALo AHi) (conj _ (conj Model (conj (fp_callsx_s _ _ _) _))))))).
  - intros m' Munched. cbn [args_ok arg_ok]. rewrite SlotLN.
    assert (Moved : bytes_at ctusegs m' LN (zb s ++ Z_to_bv 8 0 :: slack)).
    { apply (bytes_at_transport ctusegs [(lo, q)] m m' LN _ StrAt Munched).
      rewrite Span. split; [left; lia| exact I]. }
    refine (conj (ex_intro _ slack (conj Moved (conj StrByt _))) I).
    rewrite SlkZ. lia.
  - unfold zlength in SLen. lia.
Qed.

Lemma zlength_hex2 : forall b, zlength (hex2 b) = 2. Proof. intros. reflexivity. Qed.
Lemma zlength_hex2c : forall b, zlength (hex2 b ++ [58]) = 3. Proof. intros. reflexivity. Qed.

End WithCeiling0.
