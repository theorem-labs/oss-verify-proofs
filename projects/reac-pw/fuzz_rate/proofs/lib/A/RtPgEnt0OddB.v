(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0OddB.v at 111d25b4415f for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the table ent_headamp_key.odd_ch is rate's (0x9bb40 and its 14 string pointers) against lib/A/RtPgImgA.v rate_A_cells / rate_A_strs / rate_A_globs; the strings' range is rate's [0x21220, 0x21400); the read-only PT_LOAD is rate's [0x10000, 0x2f9d4) and the RW one holding the table starts at 0x9b690; the string helpers are lib/A/RtPgW7bCall.v's. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the image data the ODD block
   of ent_build's case 0 reads (pod.h:247-248, `const char *o = odd_ch[c % 14]; memcpy(ch, o, strlen(o) + 1);`,
   0x81b6c .. 0x81bc8, lib/A/RtPgEnt0Def.v rt7_odd_stmt). Proves no function (kind: segment lemma).
   - o_ptr m: the pointer ent_headamp_key.odd_ch[m] (the cell 0x9bb40 + 8 m of .data.rel.ro, RtPgImgA rate_A_cells);
     o_str m: the model's text of that string (Pod/Tables.v odd_ch).
   - o_cell / o_strin: the cell and the string as RtPgImgA's rate_A_cells and rate_A_strs list them; o_glob: the
     table is the registered global (0x9bb40, 112); o_tbl_img: the table's 112 bytes lie in a loaded segment.
   - o_tail_img: the bytes from each string's NUL to the end of the NUL's 8-byte word are image bytes of the
     read-only PT_LOAD [0x10000, 0x2f9d4), so every reader sees them whatever the memory (the strlen wrapper's word
     loop reads them).
   - o_len_le / o_ptr_lo / o_nz: each text has at most 21 bytes, lies in [0x21220, 0x21400) and has no zero byte. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgImgA RtPgW7bCall.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

Definition O_TBL : Z := 0x9bb40.          (* ent_headamp_key.odd_ch, 14 pointers *)
Definition o_ptrs : list Z :=
[0x21220; 0x21240; 0x21260; 0x21280; 0x212a0; 0x212e0; 0x21300; 0x21320; 0x21340; 0x21360; 0x21380; 0x213a0;
 0x213c0; 0x213e0].
Definition o_ptr (m : Z) : Z := nth (Z.to_nat m) o_ptrs 0.
Definition o_str (m : Z) : list byte := nth (Z.to_nat m) odd_ch [].
Definition o_len (m : Z) : Z := Z.of_nat (length (o_str m)).

Lemma o_cases : forall m, 0 <= m < 14 ->
m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8 \/ m = 9 \/ m = 10 \/ m = 11 \/
m = 12 \/ m = 13.
Proof. intros m Hm. lia. Qed.

Ltac o_in := repeat (first [left; vm_compute; reflexivity | right]).

Lemma o_cell : forall m, 0 <= m < 14 -> In (O_TBL + 8 * m, o_ptr m) rate_A_cells.
Proof.
intros m Hm. pose proof (o_cases _ Hm) as E. unfold rate_A_cells; cbn [In].
repeat (destruct E as [E|E]; [subst m; o_in|]). subst m. o_in.
Qed.
Lemma o_strin : forall m, 0 <= m < 14 -> In (o_ptr m, map (fun b : byte => bv_unsigned b) (o_str m)) rate_A_strs.
Proof.
intros m Hm. pose proof (o_cases _ Hm) as E. unfold rate_A_strs; cbn [In].
repeat (destruct E as [E|E]; [subst m; o_in|]). subst m. o_in.
Qed.
Lemma o_glob : In (O_TBL, 112) rate_A_globs.
Proof. unfold rate_A_globs; cbn [In]. o_in. Qed.

(* the per-string bounds, checked once *)
Definition o_bounds_b (m : nat) : bool :=
(0x21220 <=? o_ptr (Z.of_nat m)) && (o_ptr (Z.of_nat m) + o_len (Z.of_nat m) + 8 <=? 0x21400) &&
(Nat.leb (length (o_str (Z.of_nat m))) 21) && no_nul (o_str (Z.of_nat m)) &&
forallb w7_rom_some (w7_tail_addrs (o_ptr (Z.of_nat m)) (o_len (Z.of_nat m))).
Lemma o_bounds_chk : forallb o_bounds_b (seq 0 14) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma o_bounds : forall m, 0 <= m < 14 -> o_bounds_b (Z.to_nat m) = true.
Proof.
intros m Hm. apply (proj1 (forallb_forall _ _) o_bounds_chk). apply in_seq. lia.
Qed.
Lemma o_ptr_lo : forall m, 0 <= m < 14 -> 0x21220 <= o_ptr m /\ o_ptr m + o_len m + 8 <= 0x21400.
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
repeat (apply andb_prop in H as [H ?]). apply w7_no_nul_Forall. assumption.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma o_tail_img : forall m, 0 <= m < 14 ->
forall a, o_ptr m + o_len m < a < o_ptr m + o_len m - (o_ptr m + o_len m) mod 8 + 8 ->
forall (H : word -> bool) mem, aview rsegs H mem a <> None.
Proof.
intros m Hm a Ha H mem. pose proof (o_bounds m Hm) as Hb. unfold o_bounds_b in Hb. rewrite Z2Nat.id in Hb by lia.
apply andb_prop in Hb as [_ Hq].
assert (Hmod : 0 <= (o_ptr m + o_len m) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Ha' : In a (w7_tail_addrs (o_ptr m) (o_len m))).
{ unfold w7_tail_addrs. apply in_map_iff. exists (Z.to_nat (a - (o_ptr m + o_len m + 1))). split.
  - rewrite Z2Nat.id by lia. lia.
  - apply in_seq. revert Ha Hmod. generalize ((o_ptr m + o_len m) mod 8). intros k Ha Hk. lia. }
pose proof (proj1 (forallb_forall _ _) Hq a Ha') as Hr. unfold w7_rom_some in Hr.
unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)); [discriminate|].
destruct (seg_rom rsegs (Z_to_bv 64 a)); [discriminate | discriminate Hr].
Qed.
End b.

(* the table's 112 bytes lie in a loaded segment (the RW PT_LOAD at 0x9b690) *)
Lemma o_tbl_seg_chk :
existsb (fun s => (Z.of_N (seg_base s) <=? O_TBL) && (O_TBL + 112 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma o_tbl_img : forall a, O_TBL <= a < O_TBL + 112 -> in_img rsegs a.
Proof.
intros a Ha. pose proof o_tbl_seg_chk as H. apply existsb_exists in H as (s & Hs & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.

Print Assumptions o_cell.
Print Assumptions o_strin.
Print Assumptions o_ptr_lo.
Print Assumptions o_len_le.
Print Assumptions o_nz.
Print Assumptions o_tail_img.
Print Assumptions o_tbl_img.
