(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0OddB.v at 111d25b4415f for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the table ent_headamp_key.odd_ch is rate's (0x9bb40 and its 14 string pointers) against lib/A/RtPgImgA.v rate_A_cells / rate_A_strs / rate_A_globs; the strings' range is rate's [0x21220, 0x21400); the read-only PT_LOAD is rate's [0x10000, 0x2f9d4) and the RW one holding the table starts at 0x9b690; the string helpers are lib/A/RtPgW7bCall.v's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0OddB.v at 21da95a5fcd3; image B (images.AsanUbsan): the table ent_headamp_key.odd_ch is at 0x9be40 (A's at +0x300, the same 14 string pointers) against lib/AU/RtPgImgB.v rate_B_cells / rate_B_strs / rate_B_globs; the read-only PT_LOAD is [0x10000, 0x2fa0c) and the RW one holding the table is [0x9b998, 0x9d000); the string helpers are lib/AU/RtPgW7bCallB.v's; ob_img_chk adds a check of the 14 cells, the 14 strings and the .rodata constant 0x10318 against image B's own loaded bytes; names o_ -> ob_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the image data the ODD block
   of ent_build's case 0 reads (pod.h:247-248, `const char *o = odd_ch[c % 14]; memcpy(ch, o, strlen(o) + 1);`,
   0x81de0 .. 0x81e50, lib/AU/RtPgEnt0DefB.v rt7b_odd_stmt). Proves no function (kind: segment lemma).
   - ob_ptr m: the pointer ent_headamp_key.odd_ch[m] (the cell 0x9be40 + 8 m of .data.rel.ro, RtPgImgB rate_B_cells);
     ob_str m: the model's text of that string (Pod/Tables.v odd_ch).
   - ob_cell / ob_strin: the cell and the string as RtPgImgB's rate_B_cells and rate_B_strs list them; ob_glob: the
     table is the registered global (0x9be40, 112); ob_tbl_img: the table's 112 bytes lie in a loaded segment.
   - ob_img_chk: the same 14 cells and 14 strings (with their NULs), and the 8 bytes of the `c / 14` multiplier
     0x124924924924924a at .rodata 0x10318 (the `ld` 0x81de4), are image B's own loaded bytes.
   - ob_tail_img: the bytes from each string's NUL to the end of the NUL's 8-byte word are image bytes of the
     read-only PT_LOAD [0x10000, 0x2fa0c), so every reader sees them whatever the memory (the strlen wrapper's word
     loop reads them).
   - ob_len_le / ob_ptr_lo / ob_nz: each text has at most 21 bytes, lies in [0x21220, 0x21400) and has no zero byte. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgW7bCallB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Definition OB_TBL : Z := 0x9be40.          (* ent_headamp_key.odd_ch, 14 pointers *)
Definition ob_ptrs : list Z :=
[0x21220; 0x21240; 0x21260; 0x21280; 0x212a0; 0x212e0; 0x21300; 0x21320; 0x21340; 0x21360; 0x21380; 0x213a0;
 0x213c0; 0x213e0].
Definition ob_ptr (m : Z) : Z := nth (Z.to_nat m) ob_ptrs 0.
Definition ob_str (m : Z) : list byte := nth (Z.to_nat m) odd_ch [].
Definition ob_len (m : Z) : Z := Z.of_nat (length (ob_str m)).

Lemma ob_cases : forall m, 0 <= m < 14 ->
m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8 \/ m = 9 \/ m = 10 \/ m = 11 \/
m = 12 \/ m = 13.
Proof. intros m Hm. lia. Qed.

Ltac ob_in := repeat (first [left; vm_compute; reflexivity | right]).

Lemma ob_cell : forall m, 0 <= m < 14 -> In (OB_TBL + 8 * m, ob_ptr m) rate_B_cells.
Proof.
intros m Hm. pose proof (ob_cases _ Hm) as E. unfold rate_B_cells; cbn [In].
repeat (destruct E as [E|E]; [subst m; ob_in|]). subst m. ob_in.
Qed.
Lemma ob_strin : forall m, 0 <= m < 14 -> In (ob_ptr m, map (fun b : byte => bv_unsigned b) (ob_str m)) rate_B_strs.
Proof.
intros m Hm. pose proof (ob_cases _ Hm) as E. unfold rate_B_strs; cbn [In].
repeat (destruct E as [E|E]; [subst m; ob_in|]). subst m. ob_in.
Qed.
Lemma ob_glob : In (OB_TBL, 112) rate_B_globs.
Proof. unfold rate_B_globs; cbn [In]. ob_in. Qed.

(* the same cells, strings and the `c / 14` multiplier against image B's own loaded bytes *)
Definition ob_imgb (a v : Z) : bool :=
match seg_rom rsegs (Z_to_bv 64 a) with Some b => bv_unsigned b =? v | None => false end.
Definition ob_img_m (m : nat) : bool :=
forallb (fun i => ob_imgb (OB_TBL + 8 * Z.of_nat m + Z.of_nat i) (Z.shiftr (ob_ptr (Z.of_nat m)) (8 * Z.of_nat i) mod 256))
  (seq 0 8) &&
forallb (fun j => ob_imgb (ob_ptr (Z.of_nat m) + Z.of_nat j)
  (nth j (map (fun b : byte => bv_unsigned b) (ob_str (Z.of_nat m) ++ [Cursor.NUL])) 0))
  (seq 0 (S (length (ob_str (Z.of_nat m))))).
Definition OB_K14 : Z := 0x124924924924924a.
Lemma ob_img_chk : forallb ob_img_m (seq 0 14) = true /\
forallb (fun i => ob_imgb (0x10318 + Z.of_nat i) (Z.shiftr OB_K14 (8 * Z.of_nat i) mod 256)) (seq 0 8) = true.
Proof. split; vm_compute; reflexivity. Qed.

(* the per-string bounds, checked once *)
Definition ob_bounds_b (m : nat) : bool :=
(0x21220 <=? ob_ptr (Z.of_nat m)) && (ob_ptr (Z.of_nat m) + ob_len (Z.of_nat m) + 8 <=? 0x21400) &&
(Nat.leb (length (ob_str (Z.of_nat m))) 21) && no_nul (ob_str (Z.of_nat m)) &&
forallb w7b_rom_some (w7b_tail_addrs (ob_ptr (Z.of_nat m)) (ob_len (Z.of_nat m))).
Lemma ob_bounds_chk : forallb ob_bounds_b (seq 0 14) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ob_bounds : forall m, 0 <= m < 14 -> ob_bounds_b (Z.to_nat m) = true.
Proof.
intros m Hm. apply (proj1 (forallb_forall _ _) ob_bounds_chk). apply in_seq. lia.
Qed.
Lemma ob_ptr_lo : forall m, 0 <= m < 14 -> 0x21220 <= ob_ptr m /\ ob_ptr m + ob_len m + 8 <= 0x21400.
Proof.
intros m Hm. pose proof (ob_bounds m Hm) as H. unfold ob_bounds_b in H. rewrite Z2Nat.id in H by lia.
repeat (apply andb_prop in H as [H ?]). lia.
Qed.
Lemma ob_len_le : forall m, 0 <= m < 14 -> (length (ob_str m) <= 21)%nat.
Proof.
intros m Hm. pose proof (ob_bounds m Hm) as H. unfold ob_bounds_b in H. rewrite Z2Nat.id in H by lia.
repeat (apply andb_prop in H as [H ?]). apply Nat.leb_le. assumption.
Qed.
Lemma ob_nz : forall m, 0 <= m < 14 -> Forall (fun b : byte => bv_unsigned b <> 0) (ob_str m).
Proof.
intros m Hm. pose proof (ob_bounds m Hm) as H. unfold ob_bounds_b in H. rewrite Z2Nat.id in H by lia.
repeat (apply andb_prop in H as [H ?]). apply w7b_no_nul_Forall. assumption.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ob_tail_img : forall m, 0 <= m < 14 ->
forall a, ob_ptr m + ob_len m < a < ob_ptr m + ob_len m - (ob_ptr m + ob_len m) mod 8 + 8 ->
forall (H : word -> bool) mem, aview rsegs H mem a <> None.
Proof.
intros m Hm a Ha H mem. pose proof (ob_bounds m Hm) as Hb. unfold ob_bounds_b in Hb. rewrite Z2Nat.id in Hb by lia.
apply andb_prop in Hb as [_ Hq].
assert (Hmod : 0 <= (ob_ptr m + ob_len m) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Ha' : In a (w7b_tail_addrs (ob_ptr m) (ob_len m))).
{ unfold w7b_tail_addrs. apply in_map_iff. exists (Z.to_nat (a - (ob_ptr m + ob_len m + 1))). split.
  - rewrite Z2Nat.id by lia. lia.
  - apply in_seq. revert Ha Hmod. generalize ((ob_ptr m + ob_len m) mod 8). intros k Ha Hk. lia. }
pose proof (proj1 (forallb_forall _ _) Hq a Ha') as Hr. unfold w7b_rom_some in Hr.
unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)); [discriminate|].
destruct (seg_rom rsegs (Z_to_bv 64 a)); [discriminate | discriminate Hr].
Qed.
End b.

(* the table's 112 bytes lie in a loaded segment (the RW PT_LOAD at 0x9b998) *)
Lemma ob_tbl_seg_chk :
existsb (fun s => (Z.of_N (seg_base s) <=? OB_TBL) && (OB_TBL + 112 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ob_tbl_img : forall a, OB_TBL <= a < OB_TBL + 112 -> in_img rsegs a.
Proof.
intros a Ha. pose proof ob_tbl_seg_chk as H. apply existsb_exists in H as (s & Hs & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.

Print Assumptions ob_cell.
Print Assumptions ob_strin.
Print Assumptions ob_img_chk.
Print Assumptions ob_ptr_lo.
Print Assumptions ob_len_le.
Print Assumptions ob_nz.
Print Assumptions ob_tail_img.
Print Assumptions ob_tbl_img.
