(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0OddB.v at 97ea9c9eafa; image B of
   fuzz_headamp's table (0x9c560) and strings (0x21180 .. 0x21340, lib/AU/HPgImgB.v headamp_B_cells / headamp_B_strs /
   headamp_B_globs), o_tail_img dropped (HPgBase.hd_cstr carries the NUL word's tail), the strings' range and the
   division constant's read-only bytes added. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the image data the ODD block
   of ent_build's case 0 reads (pod.h:247-248, `const char *o = odd_ch[c % 14]; memcpy(ch, o, strlen(o) + 1);`,
   0x82318 .. 0x82388, lib/AU/HPgE0Def.v e0_odd_stmt). Proves no function (kind: segment lemma).
   - o_ptr m: the pointer ent_headamp_key.odd_ch[m] (the cell 0x9c560 + 8 m of .data.rel.ro, HPgImgB headamp_B_cells);
     o_str m: the model's text of that string (Pod/Tables.v odd_ch).
   - o_cell / o_strin: the cell and the string as headamp_B_cells and headamp_B_strs list them; o_glob: the table is
     the registered global (0x9c560, 112); o_tbl_img: the table's 112 bytes lie in a loaded segment; o_str_img: the
     bytes [0x21180, 0x21380), which hold the fourteen strings and the tails of their NUL words, lie in a loaded
     segment.
   - o_ptr_lo / o_len_le / o_nz: each text has at most 21 bytes, lies with its NUL word in [0x21180, 0x21380) and
     has no zero byte.
   - o_k14_rom: the `/ 14` multiplier 0x124924924924924a the block loads at .rodata 0x10318 (0x82318 `auipc`,
     0x8231c `ld a1`) is 8 read-only image bytes. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgE0Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition O_TBL : Z := 0x9c560.          (* ent_headamp_key.odd_ch, 14 pointers *)
Definition o_ptrs : list Z :=
[0x21180; 0x211a0; 0x211c0; 0x211e0; 0x21200; 0x21240; 0x21260; 0x21280; 0x212a0; 0x212c0; 0x212e0; 0x21300;
 0x21320; 0x21340].
Definition o_ptr (m : Z) : Z := nth (Z.to_nat m) o_ptrs 0.
Definition o_str (m : Z) : list byte := nth (Z.to_nat m) odd_ch [].
Definition o_len (m : Z) : Z := Z.of_nat (length (o_str m)).
(* the strings and the tails of their NUL words lie in [O_SLO, O_SHI) *)
Definition O_SLO : Z := 0x21180.
Definition O_SHI : Z := 0x21380.

Lemma o_cases : forall m, 0 <= m < 14 ->
m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8 \/ m = 9 \/ m = 10 \/ m = 11 \/
m = 12 \/ m = 13.
Proof. intros m Hm. lia. Qed.

Ltac o_in := repeat (first [left; vm_compute; reflexivity | right]).

Lemma o_cell : forall m, 0 <= m < 14 -> In (O_TBL + 8 * m, o_ptr m) headamp_B_cells.
Proof.
intros m Hm. pose proof (o_cases _ Hm) as E. unfold headamp_B_cells; cbn [In].
repeat (destruct E as [E|E]; [subst m; o_in|]). subst m. o_in.
Qed.
Lemma o_strin : forall m, 0 <= m < 14 -> In (o_ptr m, map (fun b : byte => bv_unsigned b) (o_str m)) headamp_B_strs.
Proof.
intros m Hm. pose proof (o_cases _ Hm) as E. unfold headamp_B_strs; cbn [In].
repeat (destruct E as [E|E]; [subst m; o_in|]). subst m. o_in.
Qed.
Lemma o_glob : In (O_TBL, 112) headamp_B_globs.
Proof. unfold headamp_B_globs; cbn [In]. o_in. Qed.

(* the per-string bounds, checked once *)
Definition o_bounds_b (m : nat) : bool :=
(O_SLO <=? o_ptr (Z.of_nat m)) && (o_ptr (Z.of_nat m) + o_len (Z.of_nat m) + 8 <=? O_SHI) &&
(Nat.leb (length (o_str (Z.of_nat m))) 21) && no_nul (o_str (Z.of_nat m)).
Lemma o_bounds_chk : forallb o_bounds_b (seq 0 14) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma o_bounds : forall m, 0 <= m < 14 -> o_bounds_b (Z.to_nat m) = true.
Proof.
intros m Hm. apply (proj1 (forallb_forall _ _) o_bounds_chk). apply in_seq. lia.
Qed.
Lemma o_ptr_lo : forall m, 0 <= m < 14 -> O_SLO <= o_ptr m /\ o_ptr m + o_len m + 8 <= O_SHI.
Proof.
intros m Hm. pose proof (o_bounds m Hm) as H. unfold o_bounds_b in H. rewrite Z2Nat.id in H by lia.
repeat (apply andb_prop in H as [H ?]). lia.
Qed.
Lemma o_len_le : forall m, 0 <= m < 14 -> (length (o_str m) <= 21)%nat.
Proof.
intros m Hm. pose proof (o_bounds m Hm) as H. unfold o_bounds_b in H. rewrite Z2Nat.id in H by lia.
repeat (apply andb_prop in H as [H ?]). apply Nat.leb_le. assumption.
Qed.
Lemma o_nz : forall m, 0 <= m < 14 -> Forall (fun b : byte => bv_unsigned b <> 0) (o_str m).
Proof.
intros m Hm. pose proof (o_bounds m Hm) as H. unfold o_bounds_b in H. rewrite Z2Nat.id in H by lia.
repeat (apply andb_prop in H as [H ?]). apply e0_no_nul_Forall. assumption.
Qed.

(* the table's 112 bytes lie in a loaded segment (the RW PT_LOAD that holds .data.rel.ro) *)
Lemma o_tbl_seg_chk :
existsb (fun s => (Z.of_N (seg_base s) <=? O_TBL) && (O_TBL + 112 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma o_tbl_img : forall a, O_TBL <= a < O_TBL + 112 -> in_img rsegs a.
Proof.
intros a Ha. pose proof o_tbl_seg_chk as H. apply existsb_exists in H as (s & Hs & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.
(* the strings' bytes [O_SLO, O_SHI) lie in a loaded segment (the read-only PT_LOAD that holds .rodata) *)
Lemma o_str_seg_chk :
existsb (fun s => (Z.of_N (seg_base s) <=? O_SLO) && (O_SHI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma o_str_img : forall a, O_SLO <= a < O_SHI -> in_img rsegs a.
Proof.
intros a Ha. pose proof o_str_seg_chk as H. apply existsb_exists in H as (s & Hs & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.

(* the constant 0x124924924924924a at .rodata 0x10318 (the `/ 14` multiplier, headamp_B_cells) is 8 image bytes *)
Lemma o_k14_rom : rom_run_b 0x10318 8 = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions o_cell.
Print Assumptions o_strin.
Print Assumptions o_glob.
Print Assumptions o_ptr_lo.
Print Assumptions o_len_le.
Print Assumptions o_nz.
Print Assumptions o_tbl_img.
Print Assumptions o_str_img.
Print Assumptions o_k14_rom.
