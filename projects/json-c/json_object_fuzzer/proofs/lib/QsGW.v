(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig.
Import ListNotations.
Open Scope Z_scope.

Ltac small_offset k :=
let b := eval vm_compute in (andb (Z.leb (-4096) k) (Z.ltb k 4096))%Z in
lazymatch b with true => idtac end. Ltac mkr__small_offset_0 k := let b := eval vm_compute in (andb (Z.leb (-4096) k) (Z.ltb k 4096))%Z in
lazymatch b with true => idtac end.

Ltac solve_load_safe :=
match goal with
| |- context [ov_read_bytes ?segs ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
small_offset k;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
small_offset k;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.

Ltac solve_store_safe :=
match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
small_offset k;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.

Ltac solve_load ::= first [ solve_load_safe | solve_load_image ]. Ltac mkr__solve_load_1 := first [ solve_load_safe | solve_load_image ].
Ltac solve_store ::= solve_store_safe. Ltac mkr__solve_store_2 := solve_store_safe.

Lemma amo_aligned_intro4 : forall a : Z, (0 <= a < 2^64)%Z -> (a mod 4 = 0)%Z -> amo_aligned AW (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
Lemma amo_aligned_intro8 : forall a : Z, (0 <= a < 2^64)%Z -> (a mod 8 = 0)%Z -> amo_aligned AD (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.

Ltac amo_align AMO :=
try (rewrite AMO; cbv beta iota delta [negb]);
try (rewrite Z.eqb_refl; cbv iota).

Ltac amo_step AMO :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_cbv; simp_is_x0; simp_regs; amo_align AMO; exec_cbv; simp_is_x0; simp_regs; amo_align AMO; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end end
end. Ltac mkr__amo_step_3 AMO := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_cbv; simp_is_x0; simp_regs; amo_align AMO; exec_cbv; simp_is_x0; simp_regs; amo_align AMO; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end end
end.

Ltac if_lit := first [ if_true | if_false ]. Ltac mkr__if_lit_4 := first [ if_true | if_false ].

Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).
