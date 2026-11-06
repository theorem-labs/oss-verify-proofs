(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import STRW_tac FseWalkKit.
Import ListNotations.
Open Scope Z_scope.
Lemma map_upd_nat : forall {X} (f : Z -> X) n v l, map f (upd_nat n v l) = upd (map f l) n (f v).
Proof. intros X f n v l. revert n. induction l as [|a l IH]; intros [|n]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma nth_error_map_Znth : forall {X} (f : Z -> X) (l : list Z) i, 0 <= i < Z.of_nat (length l) ->
nth_error (map f l) (Z.to_nat i) = Some (f (Znth i l)).
Proof.
intros X f l i Hi. unfold Znth. rewrite nth_error_map.
Local Ltac2 Set LiaHints.tbl := fun () => "0010=52803074047.5000004S2Hi".
rewrite (nth_error_nth' l 0) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma Forall_Znth : forall (P : Z -> Prop) (l : list Z) i, Forall P l -> 0 <= i < Z.of_nat (length l) -> P (Znth i l).
Proof. intros P l i H Hi. unfold Znth. apply (proj1 (Forall_forall _ _) H). apply nth_In. Local Ltac2 Set LiaHints.tbl := fun () => "0010=52803074047.5000004S2Hi".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section Mem.
Variable segs : list Segment.
#[using="Type"] Lemma u8arr_sb : forall m A (buf : list Z) i x v,
u8arr segs m A (map (Z_to_bv 8) buf) -> 0 <= i < Z.of_nat (length buf) -> x mod 256 = v mod 256 ->
u8arr segs (write_to_mem m (wa (A + i)) (le1 (Z_to_bv 64 x))) A (map (Z_to_bv 8) (Zupd i v buf)).
Proof.
intros m A buf i x v ARR Hi E. rewrite le1_lit.
unfold Zupd. rewrite map_upd_nat.
replace (Z_to_bv 8 v) with (Z_to_bv 8 x) by (apply Z_to_bv8_mod; exact E).
apply u8arr_write; [exact ARR| rewrite length_map; exact Hi].
Qed.
#[using="Type"] Lemma u16_znth : forall m A (nc : list Z) i a,
bytes_at segs m A (u16s (map (Z_to_bv 64) nc)) -> 0 <= i < Z.of_nat (length nc) -> a = wa (A + 2 * i) ->
ov_read_bytes segs m a 2 = Some (le2 (Z_to_bv 64 (Znth i nc))).
Proof.
intros m A nc i a NCB Hi ->. Local Ltac2 Set LiaHints.tbl := fun () => "0010=10351595562.7000004S2Hi".
eapply (u16ro_read segs m A _ i); [exact NCB| | lia | reflexivity].
apply nth_error_map_Znth. exact Hi.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Mem.
Lemma sx16_short : forall c, - 32768 <= c < 32768 -> sx16 (Z_to_bv 64 c) = Z_to_bv 64 c.
Proof.
intros c Hc. unfold sx16. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
rewrite swrap16_eq. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>20432958294.1600000<S2Hc1H2H02H4".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma zx16_short : forall c, - 32768 <= c < 32768 -> zx16 (Z_to_bv 64 c) = Z_to_bv 64 (c mod 65536).
Proof.
intros c Hc. unfold zx16. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
change (2^16) with 65536. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>11447729963.2300000?S1H2H02H42H52H9".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac u8_sok ARR i :=
lazymatch type of ARR with u8arr ?segs ?mx ?A ?bs =>
let a := cur_mem_addr in
pose proof (u8arr_store_ok segs mx A bs i a ARR ltac:(rewrite ?length_map, ?Zupd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK
end.
Ltac u8_store ARR i v :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx ?a (le1 (Z_to_bv 64 ?x))) _) =>
lazymatch type of ARR with u8arr ?segs mx ?A (map (Z_to_bv 8) ?buf) =>
let E := addr_expr a in
let ARR' := fresh "ARR" in
assert (ARR' : u8arr segs (write_to_mem mx (wa E) (le1 (Z_to_bv 64 x))) A (map (Z_to_bv 8) (Zupd i v buf)));
[ replace (wa E) with (wa (A + i)) by (unfold wa; f_equal; lia);
apply (u8arr_sb segs mx A buf i x v ARR); [ rewrite ?Zupd_length; lia | ]
| clear ARR; store_done; rename ARR' into ARR ]
end
end.
