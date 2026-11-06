(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1cr X1cs X1dg X1df X1ck X1co X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05l X081.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Export X09e.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X0ys.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys.
Export OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X09e.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Definition A_lsp_unquant_lbr : Z := 0xb4818.
Definition A_lsp_unquant_nb : Z := 0xb3c2c.
Definition A_lsp_unquant_high : Z := 0xb51dc.
Definition A_lsp_interpolate : Z := 0xaed80.
Definition lsp_entryA (k : lsp_kind) : Z :=
match k with LspUnquantLbr => A_lsp_unquant_lbr | LspUnquantNb => A_lsp_unquant_nb | LspUnquantHigh => A_lsp_unquant_high end.
Definition lsp_order (k : lsp_kind) : Z := match k with LspUnquantHigh => 8 | _ => 10 end.

Definition LSPQ_DEPTH : Z := 128.

Definition LSPI_DEPTH : Z := 64.

Definition A_cdbk_nb : Z := 0x24880.
Definition A_cdbk_nb_low1 : Z := 0x24ba0.
Definition A_cdbk_nb_low2 : Z := 0x24d20.
Definition A_cdbk_nb_high1 : Z := 0x24ea0.
Definition A_cdbk_nb_high2 : Z := 0x25020.
Definition A_high_lsp_cdbk : Z := 0x251c0.
Definition A_high_lsp_cdbk2 : Z := 0x25440.
Definition lsp_tabs (m : mem) : Prop :=
aobj bsegs m A_cdbk_nb 640 /\ aobj bsegs m A_cdbk_nb_low1 320 /\ aobj bsegs m A_cdbk_nb_low2 320
/\ aobj bsegs m A_cdbk_nb_high1 320 /\ aobj bsegs m A_cdbk_nb_high2 320
/\ aobj bsegs m A_high_lsp_cdbk 512 /\ aobj bsegs m A_high_lsp_cdbk2 512.

Section Pure.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.
Definition ub b (n : Z) : bits_st ptr := snd (speex_bits_unpack_unsigned b n).
Definition uv b (n : Z) : Z := fst (speex_bits_unpack_unsigned b n).
Definition lsp_bits (k : lsp_kind) b : bits_st ptr :=
match k with
| LspUnquantLbr => ub (ub (ub b 6) 6) 6
| LspUnquantNb => ub (ub (ub (ub (ub b 6) 6) 6) 6) 6
| LspUnquantHigh => ub (ub b 6) 6
end.

Lemma ub_ok : forall b n, bits_ok b -> 0 <= n -> bits_ok (ub b n) /\ sb_buf_size (ub b n) = sb_buf_size b /\ 0 <= uv b n < 2 ^ n.
Proof.
intros b n OK Hn. unfold ub, uv. destruct (speex_bits_unpack_unsigned b n) as [v b'] eqn:E. cbn [fst snd].
pose proof (speex_bits_unpack_unsigned_ok b n v b' OK Hn E) as (OK1 & V & _ & _ & SZ & _). auto.
Qed.
End Pure.

Section Kinds.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition lsp_unquant_postA (k : lsp_kind) (A D IQ usp lo : Z) b
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (ws : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(A, A + BITS_SIZEOF); (IQ, IQ + 4 * lsp_order k); (usp + -LSPQ_DEPTH, usp)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ frm0 fc'
/\ rw_cells bsegs m' IQ (f32 ws) /\ length ws = Z.to_nat (lsp_order k)
/\ bits_rep bsegs m' A D (lsp_bits k b) /\ bits_ok (lsp_bits k b).

Definition lsp_unquant_stmtA (k : lsp_kind) : Prop :=
forall (A D IQ usp lo : Z) b (old : list word)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep bsegs m A D b -> bits_ok b ->
aobj bsegs m A BITS_SIZEOF -> aobj bsegs m D (sb_buf_size b) -> aobj bsegs m IQ (4 * lsp_order k) ->
lsp_tabs m -> lib_consts m -> client_constsB m ->
rw_cells bsegs m IQ (f32 old) -> length old = Z.to_nat (lsp_order k) -> IQ mod 4 = 0 ->
hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) -> hidp (IQ + 4 * lsp_order k <= SH_LO \/ SH_HI <= IQ) ->
IMG_TOP_B <= A -> IMG_TOP_B <= IQ ->
A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo -> hidp (IQ + 4 * lsp_order k <= lo \/ usp <= IQ) ->
hidp (IQ + 4 * lsp_order k <= A \/ A + BITS_SIZEOF <= IQ) -> hidp (IQ + 4 * lsp_order k <= D \/ D + sb_buf_size b <= IQ) ->
stk bsegs m lo usp -> lo <= usp - LSPQ_DEPTH -> SH_HI <= lo -> usp < 2^63 ->
mem_inv bsegs m -> frm0 fc ->
evt bsegs (lsp_unquant_postA k A D IQ usp lo b ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IQ) (Z_to_bv 64 (lsp_order k)) (Z_to_bv 64 A) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (lsp_entryA k)) fc None m (seg_rom bsegs)).
End Kinds.

Definition lsp_interpolate_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(usp lo IQ : Z) (n : nat) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (qs' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(IQ, IQ + 4 * Z.of_nat n); (usp + -LSPI_DEPTH, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ frm0 fc'
/\ rw_cells bsegs m' IQ (f32 qs') /\ length qs' = n.

Definition lsp_interpolate_stmtA : Prop :=
forall (OLD NEW IQ usp lo sub : Z) (n : nat) (os ns qs : list word)
(ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
3 <= Z.of_nat n < 2^31 ->
aobj bsegs m OLD (4 * Z.of_nat n) -> aobj bsegs m NEW (4 * Z.of_nat n) -> aobj bsegs m IQ (4 * Z.of_nat n) ->
OLD mod 4 = 0 -> NEW mod 4 = 0 -> IQ mod 4 = 0 -> 0 < OLD -> 0 < NEW ->
rw_cells bsegs m OLD (f32 os) -> length os = n -> rw_cells bsegs m NEW (f32 ns) -> length ns = n ->
rw_cells bsegs m IQ (f32 qs) -> length qs = n ->
hidp (IQ + 4 * Z.of_nat n <= SH_LO \/ SH_HI <= IQ) -> IMG_TOP_B <= IQ ->
hidp (IQ + 4 * Z.of_nat n <= lo \/ usp <= IQ) -> hidp (OLD + 4 * Z.of_nat n <= lo \/ usp <= OLD) -> hidp (NEW + 4 * Z.of_nat n <= lo \/ usp <= NEW) ->
hidp (IQ + 4 * Z.of_nat n <= OLD \/ OLD + 4 * Z.of_nat n <= IQ) -> hidp (IQ + 4 * Z.of_nat n <= NEW \/ NEW + 4 * Z.of_nat n <= IQ) ->
client_constsB m -> stk bsegs m lo usp -> lo <= usp - LSPI_DEPTH -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (lsp_interpolate_postA ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo IQ n m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OLD) (Z_to_bv 64 NEW) (Z_to_bv 64 IQ) (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 sub) (Z_to_bv 64 4) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_interpolate) fc None m (seg_rom bsegs)).

Definition cdbk_bytes (base : Z) (n : nat) : list byte :=
match image_bytes bsegs base n with Some bs => bs | None => [] end.

Lemma cdbk_ro : forall m base n, mem_inv bsegs m ->
ro_bytes_b bsegs base (cdbk_bytes base n) = true -> 0 <= base -> base + Z.of_nat (length (cdbk_bytes base n)) <= 2^64 ->
u8ro bsegs m base (cdbk_bytes base n).
Proof.
intros m base n MI RB H0 HL. unfold u8ro.
pose proof (ro_cells_bytes_at bsegs m base _ (ro_cells_image bsegs m base _ MI RB H0 HL)) as BY.
cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY.
Qed.

Ltac cdbk_ro_tac base n :=
exists (cdbk_bytes base n);
assert (L : length (cdbk_bytes base n) = n) by (vm_compute; reflexivity);
split; [exact L|]; intros m MI; apply cdbk_ro; [exact MI| vm_compute; reflexivity| lia| rewrite L; lia].

Definition cdbk_at (base : Z) (n : nat) : Prop :=
exists CD : list byte, length CD = n /\ forall m, mem_inv bsegs m -> u8ro bsegs m base CD.

Lemma cdbk_nb_at : cdbk_at A_cdbk_nb 640.              Proof. unfold A_cdbk_nb. cdbk_ro_tac 0x24880 640%nat. Qed.
Lemma cdbk_nb_low1_at : cdbk_at A_cdbk_nb_low1 320.    Proof. unfold A_cdbk_nb_low1. cdbk_ro_tac 0x24ba0 320%nat. Qed.
Lemma cdbk_nb_low2_at : cdbk_at A_cdbk_nb_low2 320.    Proof. unfold A_cdbk_nb_low2. cdbk_ro_tac 0x24d20 320%nat. Qed.
Lemma cdbk_nb_high1_at : cdbk_at A_cdbk_nb_high1 320.  Proof. unfold A_cdbk_nb_high1. cdbk_ro_tac 0x24ea0 320%nat. Qed.
Lemma cdbk_nb_high2_at : cdbk_at A_cdbk_nb_high2 320.  Proof. unfold A_cdbk_nb_high2. cdbk_ro_tac 0x25020 320%nat. Qed.
Lemma high_lsp_cdbk_at : cdbk_at A_high_lsp_cdbk 512.  Proof. unfold A_high_lsp_cdbk. cdbk_ro_tac 0x251c0 512%nat. Qed.
Lemma high_lsp_cdbk2_at : cdbk_at A_high_lsp_cdbk2 512. Proof. unfold A_high_lsp_cdbk2. cdbk_ro_tac 0x25440 512%nat. Qed.

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Ltac lsp_rd segs RO CDB CD r :=
lazymatch goal with MI : mem_inv segs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
let U := fresh "U" in let N := fresh "N" in let RD := fresh "RD" in
pose proof (RO mc MI) as U;
assert (N : nth_error CD (Z.to_nat r) = Some (nth (Z.to_nat r) CD (Z_to_bv 8 0))) by (apply nth_error_nth'; lia);
pose proof (u8ro_read segs mc CDB CD r _ _ U N ltac:(lia) eq_refl) as RD; clear U N
end.

Ltac norm_cb CDB r :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let rr := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
unify R rr;
lazymatch rr with mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?E) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
replace (Z_to_bv 64 E) with (Z_to_bv 64 (CDB + r))
by (f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; change (2 ^ 2) with 4; rewrite ?Z.mod_small by lia; rewrite ?swrap32_small by lia; lia)
end
end.

Ltac rebase_bits A D b rj bs :=
lazymatch goal with
| OBA : aobj bsegs ?m0 A 48, OBD : aobj bsegs ?m0 D _, MU : munch ?W ?m0 ?mc, OF : offsh ?W, OBJ : rw_cells bsegs ?mc A _, DAT : u8arr bsegs ?mc D bs,
G1 : ro_cells bsegs ?mc 1032472 _, G2 : ro_cells bsegs ?mc 1071800 _, G3 : ro_cells bsegs ?mc 1032560 _, G4 : ro_cells bsegs ?mc 1071808 _
|- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (REP1 : bits_rep bsegs mc A D b)
by (split; [exists rj; split; [assumption| exact OBJ]| split; [exists bs; split; [exact DAT| assumption]| assumption]]);
pose proof (aobj_munch bsegs _ m0 mc A 48 OBA MU (shfree_of_aobj bsegs _ m0 A 48 OF OBA)) as OBA1;
pose proof (aobj_munch bsegs _ m0 mc D _ OBD MU (shfree_of_aobj bsegs _ m0 D _ OF OBD)) as OBD1;
assert (CC1 : client_constsB mc)
by (unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))));
clear OBJ DAT
end.

Ltac vloop_facts OBQ MU OF IQ Q NZ :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of MU with munch ?W ?m0 mc =>
let OBs := fresh "OBs" in
assert (OBs : aobj bsegs m0 Q NZ) by (eapply (aobj_sub bsegs m0 IQ _ Q NZ OBQ); lia);
pose proof (aobj_munch bsegs W m0 mc Q NZ OBs MU (shfree_of_aobj bsegs W m0 Q NZ OF OBs)) as OBQc;
clear OBs;
pose proof (munch_refl [(Q, Q + NZ)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (D0 : rw_cells bsegs mc Q (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia)
end end.

Ltac vloop_cb OBC MU OF CDB CN :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of MU with munch ?W ?m0 mc =>
pose proof (aobj_munch bsegs W m0 mc CDB CN OBC MU (shfree_of_aobj bsegs W m0 CDB CN OF OBC)) as OBCc
end end.

Ltac vloop_names Q X LX FRM :=
match goal with H : rw_cells bsegs _ Q (f32 ?l), L : length ?l = _, F : frm0 _ |- _ => rename H into X; rename L into LX; rename F into FRM end.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Definition A_lsp_unquant_lbr : Z := 0xae630.
Definition A_lsp_unquant_nb : Z := 0xadbec.
Definition A_lsp_unquant_high : Z := 0xaee84.
Definition A_lsp_interpolate : Z := 0xa9bc0.
Definition lsp_entryA (k : lsp_kind) : Z :=
match k with LspUnquantLbr => A_lsp_unquant_lbr | LspUnquantNb => A_lsp_unquant_nb | LspUnquantHigh => A_lsp_unquant_high end.
Definition lsp_order (k : lsp_kind) : Z := match k with LspUnquantHigh => 8 | _ => 10 end.

Definition LSPQ_DEPTH : Z := 128.

Definition LSPI_DEPTH : Z := 64.

Definition A_cdbk_nb : Z := 0x24880.
Definition A_cdbk_nb_low1 : Z := 0x24ba0.
Definition A_cdbk_nb_low2 : Z := 0x24d20.
Definition A_cdbk_nb_high1 : Z := 0x24ea0.
Definition A_cdbk_nb_high2 : Z := 0x25020.
Definition A_high_lsp_cdbk : Z := 0x251c0.
Definition A_high_lsp_cdbk2 : Z := 0x25440.
Definition lsp_tabs (m : mem) : Prop :=
aobj asegs m A_cdbk_nb 640 /\ aobj asegs m A_cdbk_nb_low1 320 /\ aobj asegs m A_cdbk_nb_low2 320
/\ aobj asegs m A_cdbk_nb_high1 320 /\ aobj asegs m A_cdbk_nb_high2 320
/\ aobj asegs m A_high_lsp_cdbk 512 /\ aobj asegs m A_high_lsp_cdbk2 512.

Section Pure.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.
Definition ub b (n : Z) : bits_st ptr := snd (speex_bits_unpack_unsigned b n).
Definition uv b (n : Z) : Z := fst (speex_bits_unpack_unsigned b n).
Definition lsp_bits (k : lsp_kind) b : bits_st ptr :=
match k with
| LspUnquantLbr => ub (ub (ub b 6) 6) 6
| LspUnquantNb => ub (ub (ub (ub (ub b 6) 6) 6) 6) 6
| LspUnquantHigh => ub (ub b 6) 6
end.

Lemma ub_ok : forall b n, bits_ok b -> 0 <= n -> bits_ok (ub b n) /\ sb_buf_size (ub b n) = sb_buf_size b /\ 0 <= uv b n < 2 ^ n.
Proof.
intros b n OK Hn. unfold ub, uv. destruct (speex_bits_unpack_unsigned b n) as [v b'] eqn:E. cbn [fst snd].
pose proof (speex_bits_unpack_unsigned_ok b n v b' OK Hn E) as (OK1 & V & _ & _ & SZ & _). auto.
Qed.
End Pure.

Section Kinds.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition lsp_unquant_postA (k : lsp_kind) (A D IQ usp lo : Z) b
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (ws : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(A, A + BITS_SIZEOF); (IQ, IQ + 4 * lsp_order k); (usp + -LSPQ_DEPTH, usp)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc'
/\ rw_cells asegs m' IQ (f32 ws) /\ length ws = Z.to_nat (lsp_order k)
/\ bits_rep asegs m' A D (lsp_bits k b) /\ bits_ok (lsp_bits k b).

Definition lsp_unquant_stmtA (k : lsp_kind) : Prop :=
forall (A D IQ usp lo : Z) b (old : list word)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep asegs m A D b -> bits_ok b ->
aobj asegs m A BITS_SIZEOF -> aobj asegs m D (sb_buf_size b) -> aobj asegs m IQ (4 * lsp_order k) ->
lsp_tabs m -> lib_consts m -> client_consts m ->
rw_cells asegs m IQ (f32 old) -> length old = Z.to_nat (lsp_order k) -> IQ mod 4 = 0 ->
hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) -> hidp (IQ + 4 * lsp_order k <= SH_LO \/ SH_HI <= IQ) ->
IMG_TOP <= A -> IMG_TOP <= IQ ->
A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo -> hidp (IQ + 4 * lsp_order k <= lo \/ usp <= IQ) ->
hidp (IQ + 4 * lsp_order k <= A \/ A + BITS_SIZEOF <= IQ) -> hidp (IQ + 4 * lsp_order k <= D \/ D + sb_buf_size b <= IQ) ->
stk asegs m lo usp -> lo <= usp - LSPQ_DEPTH -> SH_HI <= lo -> usp < 2^63 ->
mem_inv asegs m -> frm0 fc ->
evt asegs (lsp_unquant_postA k A D IQ usp lo b ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IQ) (Z_to_bv 64 (lsp_order k)) (Z_to_bv 64 A) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (lsp_entryA k)) fc None m (seg_rom asegs)).
End Kinds.

Definition lsp_interpolate_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(usp lo IQ : Z) (n : nat) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (qs' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(IQ, IQ + 4 * Z.of_nat n); (usp + -LSPI_DEPTH, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc'
/\ rw_cells asegs m' IQ (f32 qs') /\ length qs' = n.

Definition lsp_interpolate_stmtA : Prop :=
forall (OLD NEW IQ usp lo sub : Z) (n : nat) (os ns qs : list word)
(ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
3 <= Z.of_nat n < 2^31 ->
aobj asegs m OLD (4 * Z.of_nat n) -> aobj asegs m NEW (4 * Z.of_nat n) -> aobj asegs m IQ (4 * Z.of_nat n) ->
OLD mod 4 = 0 -> NEW mod 4 = 0 -> IQ mod 4 = 0 -> 0 < OLD -> 0 < NEW ->
rw_cells asegs m OLD (f32 os) -> length os = n -> rw_cells asegs m NEW (f32 ns) -> length ns = n ->
rw_cells asegs m IQ (f32 qs) -> length qs = n ->
hidp (IQ + 4 * Z.of_nat n <= SH_LO \/ SH_HI <= IQ) -> IMG_TOP <= IQ ->
hidp (IQ + 4 * Z.of_nat n <= lo \/ usp <= IQ) -> hidp (OLD + 4 * Z.of_nat n <= lo \/ usp <= OLD) -> hidp (NEW + 4 * Z.of_nat n <= lo \/ usp <= NEW) ->
hidp (IQ + 4 * Z.of_nat n <= OLD \/ OLD + 4 * Z.of_nat n <= IQ) -> hidp (IQ + 4 * Z.of_nat n <= NEW \/ NEW + 4 * Z.of_nat n <= IQ) ->
client_consts m -> stk asegs m lo usp -> lo <= usp - LSPI_DEPTH -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> frm0 fc ->
evt asegs (lsp_interpolate_postA ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo IQ n m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OLD) (Z_to_bv 64 NEW) (Z_to_bv 64 IQ) (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 sub) (Z_to_bv 64 4) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_interpolate) fc None m (seg_rom asegs)).

Definition cdbk_bytes (base : Z) (n : nat) : list byte :=
match image_bytes asegs base n with Some bs => bs | None => [] end.

Lemma cdbk_ro : forall m base n, mem_inv asegs m ->
ro_bytes_b asegs base (cdbk_bytes base n) = true -> 0 <= base -> base + Z.of_nat (length (cdbk_bytes base n)) <= 2^64 ->
u8ro asegs m base (cdbk_bytes base n).
Proof.
intros m base n MI RB H0 HL. unfold u8ro.
pose proof (ro_cells_bytes_at asegs m base _ (ro_cells_image asegs m base _ MI RB H0 HL)) as BY.
cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY.
Qed.

Ltac cdbk_ro_tac base n :=
exists (cdbk_bytes base n);
assert (L : length (cdbk_bytes base n) = n) by (vm_compute; reflexivity);
split; [exact L|]; intros m MI; apply cdbk_ro; [exact MI| vm_compute; reflexivity| lia| rewrite L; lia].

Definition cdbk_at (base : Z) (n : nat) : Prop :=
exists CD : list byte, length CD = n /\ forall m, mem_inv asegs m -> u8ro asegs m base CD.

Lemma cdbk_nb_at : cdbk_at A_cdbk_nb 640.              Proof. unfold A_cdbk_nb. cdbk_ro_tac 0x24880 640%nat. Qed.
Lemma cdbk_nb_low1_at : cdbk_at A_cdbk_nb_low1 320.    Proof. unfold A_cdbk_nb_low1. cdbk_ro_tac 0x24ba0 320%nat. Qed.
Lemma cdbk_nb_low2_at : cdbk_at A_cdbk_nb_low2 320.    Proof. unfold A_cdbk_nb_low2. cdbk_ro_tac 0x24d20 320%nat. Qed.
Lemma cdbk_nb_high1_at : cdbk_at A_cdbk_nb_high1 320.  Proof. unfold A_cdbk_nb_high1. cdbk_ro_tac 0x24ea0 320%nat. Qed.
Lemma cdbk_nb_high2_at : cdbk_at A_cdbk_nb_high2 320.  Proof. unfold A_cdbk_nb_high2. cdbk_ro_tac 0x25020 320%nat. Qed.
Lemma high_lsp_cdbk_at : cdbk_at A_high_lsp_cdbk 512.  Proof. unfold A_high_lsp_cdbk. cdbk_ro_tac 0x251c0 512%nat. Qed.
Lemma high_lsp_cdbk2_at : cdbk_at A_high_lsp_cdbk2 512. Proof. unfold A_high_lsp_cdbk2. cdbk_ro_tac 0x25440 512%nat. Qed.

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Ltac lsp_rd segs RO CDB CD r :=
lazymatch goal with MI : mem_inv segs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
let U := fresh "U" in let N := fresh "N" in let RD := fresh "RD" in
pose proof (RO mc MI) as U;
assert (N : nth_error CD (Z.to_nat r) = Some (nth (Z.to_nat r) CD (Z_to_bv 8 0))) by (apply nth_error_nth'; lia);
pose proof (u8ro_read segs mc CDB CD r _ _ U N ltac:(lia) eq_refl) as RD; clear U N
end.

Ltac norm_cb CDB r :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let rr := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
unify R rr;
lazymatch rr with mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?E) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
replace (Z_to_bv 64 E) with (Z_to_bv 64 (CDB + r))
by (f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; change (2 ^ 2) with 4; rewrite ?Z.mod_small by lia; rewrite ?swrap32_small by lia; lia)
end
end.

Ltac rebase_bits A D b rj bs :=
lazymatch goal with
| OBA : aobj asegs ?m0 A 48, OBD : aobj asegs ?m0 D _, MU : munch ?W ?m0 ?mc, OF : offsh ?W, OBJ : rw_cells asegs ?mc A _, DAT : u8arr asegs ?mc D bs,
G1 : ro_cells asegs ?mc 997528 _, G2 : ro_cells asegs ?mc 1036920 _, G3 : ro_cells asegs ?mc 997616 _, G4 : ro_cells asegs ?mc 1036928 _
|- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (REP1 : bits_rep asegs mc A D b)
by (split; [exists rj; split; [assumption| exact OBJ]| split; [exists bs; split; [exact DAT| assumption]| assumption]]);
pose proof (aobj_munch asegs _ m0 mc A 48 OBA MU (shfree_of_aobj asegs _ m0 A 48 OF OBA)) as OBA1;
pose proof (aobj_munch asegs _ m0 mc D _ OBD MU (shfree_of_aobj asegs _ m0 D _ OF OBD)) as OBD1;
assert (CC1 : client_consts mc)
by (unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))));
clear OBJ DAT
end.

Ltac vloop_facts OBQ MU OF IQ Q NZ :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of MU with munch ?W ?m0 mc =>
let OBs := fresh "OBs" in
assert (OBs : aobj asegs m0 Q NZ) by (eapply (aobj_sub asegs m0 IQ _ Q NZ OBQ); lia);
pose proof (aobj_munch asegs W m0 mc Q NZ OBs MU (shfree_of_aobj asegs W m0 Q NZ OF OBs)) as OBQc;
clear OBs;
pose proof (munch_refl [(Q, Q + NZ)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (D0 : rw_cells asegs mc Q (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia)
end end.

Ltac vloop_cb OBC MU OF CDB CN :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of MU with munch ?W ?m0 mc =>
pose proof (aobj_munch asegs W m0 mc CDB CN OBC MU (shfree_of_aobj asegs W m0 CDB CN OF OBC)) as OBCc
end end.

Ltac vloop_names Q X LX FRM :=
match goal with H : rw_cells asegs _ Q (f32 ?l), L : length ?l = _, F : frm0 _ |- _ => rename H into X; rename L into LX; rename F into FRM end.
