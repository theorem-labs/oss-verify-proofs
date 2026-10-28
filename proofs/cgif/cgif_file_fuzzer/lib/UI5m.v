(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r
UI1w UI4l UI21 UI5o UI5l YI6b UN3c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac jafter_stretch_keep HS k regs2 mem2 clob newpc idxs HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
pose proof (st_ok_after_stretch segs k E ss ms regs2 mem2 rs newpc clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob newpc) in
change (ss_after_stretch ss rs k clob newpc) with ss2 in HS2
end.
Ltac add_region HS r :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_region segs E1 ss1 ms1 r) in HS;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| vm_compute; reflexivity | | ]
end.
Ltac ew_havocA :=
repeat match goal with
| |- context [ew (havoc ?E0 ?k ?ws) ?n] => rewrite (ew_havoc_old E0 k ws n) by nat_lt_lit
end.
Ltac ew_havocA_in H :=
repeat match type of H with
| context [ew (havoc ?E0 ?k ?ws) ?n] => rewrite (ew_havoc_old E0 k ws n) in H by nat_lt_lit
end.
Ltac mem_back1 bases slv :=
match goal with
| HF : frame_of ?E ?rs ?m ?m' |- mbyte _ ?m' ?a = _ =>
mb_frame_with HF slv ltac:(ew_havocA; bases; slv)
| Hout : (forall x : word, bv_unsigned x < ?d \/ ?d + ?n <= bv_unsigned x -> ?m' x = ?m x) |- mbyte ?sg ?m' ?a = _ =>
unfold mbyte at 1; rewrite (Hout (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by slv; slv); fold (mbyte sg m a)
| Hhi : (forall x : Z, alloc_ceiling <= x < 2 ^ 64 -> ~ _ -> mbyte _ ?m' x = mbyte _ ?m x /\ _) |- mbyte _ ?m' ?a = _ =>
rewrite (proj1 (Hhi a ltac:(slv) ltac:(slv)))
end.
Ltac mem_back bases slv := cbn [ms_mem mkst] in *; repeat (reflexivity || mem_back1 bases slv).
Ltac frame_wordI HS idx HU2 HE n rr :=
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv + (- dd)) by lia;
eapply (st_chunk_word _ _ _ idx _ 2%nat (- dd) (SOff n 0) spv (bv_unsigned w) HS);
[ reflexivity | reflexivity | cbv; auto 20
| ew_havocA; exact HU2
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE n rr eq_refl), Z_to_bv_bv_unsigned; reflexivity
| let Rw := fresh "Rw" in pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; clear - Rw; lia ]
end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma denot_mul3 : forall E n x,
ew E n = Z_to_bv 64 x -> 0 <= x < 65536 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 1)) (SOff n 0)) = Z_to_bv 64 (3 * x).
Proof using.
intros E n x Hn Hx. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n x Hn), U_SLit by lia. change (Z.land (zcanon 1) 63) with 1.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (x * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma denot_mul3' : forall E n x,
ew E n = Z_to_bv 64 x -> 0 <= x < 65536 ->
sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = Z_to_bv 64 (3 * x).
Proof using.
intros E n x Hn Hx. rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n x Hn), U_SLit by lia.
change (zcanon 3) with 3. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma land4_mod32 : forall x, Z.land x 4 = Z.land (x mod 2 ^ 32) 4.
Proof using. intros x. rewrite <- (Z.land_ones x 32) by lia. rewrite <- Z.land_assoc. reflexivity. Qed.
End b.
