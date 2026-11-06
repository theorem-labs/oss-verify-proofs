(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1cs X1dg X1df X1ck X1co X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l X05k X081 X082.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= (try unfold BITS_SIZEOF in * ); tlia_one.
Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); first [ exact I | lia | split; [lia|exact I] ].
Local Notation mem := (word -> option byte).

Definition lbr_l0_post (zra zsp zgp ztp zt0 zt1 zt2 zs0 zs1 za6 za7 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 : word) (Q NZ : Z) (n : nat) (mI : mem) : machine_state -> Prop :=
fun ms' => exists a0' a1' a2' a3' a4' a5' F' fc' m' (ws : list word),
ms' = MS (mkR zra zsp zgp ztp zt0 zt1 zt2 zs0 zs1 a0' a1' a2' a3' a4' a5' za6 za7 (Z_to_bv 64 SHB) zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F' (Z_to_bv 64 0xae6bc) fc' None m' (seg_rom asegs)
/\ munch [(Q, Q + NZ)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ frm0 fc' /\ rw_cells asegs m' Q (f32 ws) /\ length ws = n.

Lemma lbr_l0 : forall (Q NZ : Z) (n : nat) (mI : mem) (zra zsp zgp ztp zt0 zt1 zt2 zs0 zs1 za6 za7 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 : word), NZ = 4 * Z.of_nat n -> forall
(rest done : list word) (x : word) (off kz i : Z) (ya4 ya5 : word) (F1 : bvmap 5 word) fc mc,
Q mod 4 = 0 -> aobj asegs mI Q NZ -> offsh [(Q, Q + NZ)] ->
off = 4 * Z.of_nat (length done) -> kz = Z.of_nat (S (length rest)) -> (length done + 1 + length rest = n)%nat -> i = Z.of_nat (length done) ->
frm0 fc -> mem_inv asegs mc -> munch [(Q, Q + NZ)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc Q (f32 done) -> rw_cells asegs mc (Q + off) (f32 (x :: rest)) ->
evt asegs (lbr_l0_post zra zsp zgp ztp zt0 zt1 zt2 zs0 zs1 za6 za7 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 Q NZ n mI)
(MS (mkR zra zsp zgp ztp zt0 zt1 zt2 zs0 zs1 (Z_to_bv 64 (Q + off)) (Z_to_bv 64 kz) (Z_to_bv 64 i) (Z_to_bv 64 (Q + off)) ya4 ya5 za6 za7 (Z_to_bv 64 SHB) zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F1 (Z_to_bv 64 0xae674) fc None mc (seg_rom asegs)).
Proof.
intros Q NZ n mI zra zsp zgp ztp zt0 zt1 zt2 zs0 zs1 za6 za7 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 ENZ rest.
induction rest as [|x' rest IH]; intros done x off kz i ya4 ya5 F1 fc mc Q4 OBQ OF Hoff Hkz HN Hi FRM MI MU WM DONE X;
pose proof OBQ as (OQ0 & OQ1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
subst kz i.
- cbn [length] in HN. rewrite f32_cons, f32_nil in X.
ato 0xae680. astep. chk_merge OBQ 4.
ato 0xae6a4. astep. cbn [length].
try sh_if.
ato 0xae6bc.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
unfold lbr_l0_post. finish; [ exact DONE | ].
rewrite length_app. cbn [length]. lia.
- cbn [length] in HN, BX.
rewrite f32_cons in X. chunk_uncons X as X1.
ato 0xae680. astep. chk_merge OBQ 4.
ato 0xae6a4. astep. cbn [length].
sh_if.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (Z.of_nat (S (S (length rest))) + -1) with (Z.of_nat (S (length rest))) by lia.
replace (Q + off + 4) with (Q + (off + 4)) in * by lia.
eapply (IH (done ++ [_]) x' (off + 4) _ (Z.of_nat (length done) + 1)); try eassumption; try reflexivity.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.

Definition lbr_l1_post (zra zsp zgp ztp zt1 zt2 zs0 zs1 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 : word) (Q NZ : Z) (n : nat) (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' a0' a1' a2' a3' a4' a5' a6' a7' F' fc' m' (ws : list word),
ms' = MS (mkR zra zsp zgp ztp t0' zt1 zt2 zs0 zs1 a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 SHB) zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F' (Z_to_bv 64 0xae77c) fc' None m' (seg_rom asegs)
/\ munch [(Q, Q + NZ)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ frm0 fc' /\ rw_cells asegs m' Q (f32 ws) /\ length ws = n.

Lemma lbr_l1 : forall (Q NZ : Z) (n : nat) (CDB CN : Z) (CD : list byte) (mI : mem) (zra zsp zgp ztp zt1 zt2 zs0 zs1 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 : word), NZ = 4 * Z.of_nat n -> forall
(rest done : list word) (x : word) (off kz r : Z) (yt0 ya5 ya6 ya7 : word) (F1 : bvmap 5 word) fc mc,
Q mod 4 = 0 -> aobj asegs mI Q NZ -> offsh [(Q, Q + NZ)] ->
aobj asegs mI CDB CN -> Z.of_nat (length CD) = CN -> (forall m', mem_inv asegs m' -> u8ro asegs m' CDB CD) ->
0 <= r -> r + Z.of_nat (S (length rest)) <= CN ->
off = 4 * Z.of_nat (length done) -> kz = Z.of_nat (S (length rest)) -> (length done + 1 + length rest = n)%nat ->
frm0 fc -> mem_inv asegs mc -> munch [(Q, Q + NZ)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc Q (f32 done) -> rw_cells asegs mc (Q + off) (f32 (x :: rest)) ->
evt asegs (lbr_l1_post zra zsp zgp ztp zt1 zt2 zs0 zs1 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 Q NZ n mI)
(MS (mkR zra zsp zgp ztp yt0 zt1 zt2 zs0 zs1 (Z_to_bv 64 (Q + off)) (Z_to_bv 64 (CDB + r)) (Z_to_bv 64 kz) (Z_to_bv 64 (CDB + r)) (Z_to_bv 64 (Q + off)) ya5 ya6 ya7 (Z_to_bv 64 SHB) zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F1 (Z_to_bv 64 0xae6f0) fc None mc (seg_rom asegs)).
Proof.
intros Q NZ n CDB CN CD mI zra zsp zgp ztp zt1 zt2 zs0 zs1 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 ENZ rest.
induction rest as [|x' rest IH]; intros done x off kz r yt0 ya5 ya6 ya7 F1 fc mc Q4 OBQ OF OBC LCD RO R0 R1 Hoff Hkz HN FRM MI MU WM DONE X;
pose proof OBQ as (OQ0 & OQ1 & _); pose proof OBC as (OC0 & OC1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
subst kz.
- cbn [length] in HN, R1. rewrite f32_cons, f32_nil in X.
lsp_rd asegs RO CDB CD r.
ato 0xae6fc. astep. chk_merge OBC 1.
ato 0xae710. astep. chk_merge OBQ 4.
ato 0xae71c. astep. chk_merge OBQ 4.
ato 0xae748. astep. cbn [length].
try sh_if.
ato 0xae77c.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
unfold lbr_l1_post. finish; [ exact DONE | ].
rewrite length_app. cbn [length]. lia.
- cbn [length] in HN, BX, R1.
rewrite f32_cons in X. chunk_uncons X as X1.
lsp_rd asegs RO CDB CD r.
ato 0xae6fc. astep. chk_merge OBC 1.
ato 0xae710. astep. chk_merge OBQ 4.
ato 0xae71c. astep. chk_merge OBQ 4.
ato 0xae748. astep. cbn [length].
sh_if.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (Z.of_nat (S (S (length rest))) + -1) with (Z.of_nat (S (length rest))) by lia.
replace (Q + off + 4) with (Q + (off + 4)) in * by lia.
replace (CDB + r + 1) with (CDB + (r + 1)) by lia.
eapply (IH (done ++ [_]) x' (off + 4) _ (r + 1)); try eassumption; try reflexivity.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.

Definition lbr_l2_post (zra zsp zgp ztp zt1 zt2 zs0 zs1 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 : word) (Q NZ : Z) (n : nat) (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' a0' a1' a2' a3' a4' a5' a6' a7' F' fc' m' (ws : list word),
ms' = MS (mkR zra zsp zgp ztp t0' zt1 zt2 zs0 zs1 a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 SHB) zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F' (Z_to_bv 64 0xae840) fc' None m' (seg_rom asegs)
/\ munch [(Q, Q + NZ)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ frm0 fc' /\ rw_cells asegs m' Q (f32 ws) /\ length ws = n.

Lemma lbr_l2 : forall (Q NZ : Z) (n : nat) (CDB CN : Z) (CD : list byte) (mI : mem) (zra zsp zgp ztp zt1 zt2 zs0 zs1 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 : word), NZ = 4 * Z.of_nat n -> forall
(rest done : list word) (x : word) (off kz r : Z) (yt0 ya5 ya6 ya7 : word) (F1 : bvmap 5 word) fc mc,
Q mod 4 = 0 -> aobj asegs mI Q NZ -> offsh [(Q, Q + NZ)] ->
aobj asegs mI CDB CN -> Z.of_nat (length CD) = CN -> (forall m', mem_inv asegs m' -> u8ro asegs m' CDB CD) ->
0 <= r -> r + Z.of_nat (S (length rest)) <= CN ->
off = 4 * Z.of_nat (length done) -> kz = Z.of_nat (S (length rest)) -> (length done + 1 + length rest = n)%nat ->
frm0 fc -> mem_inv asegs mc -> munch [(Q, Q + NZ)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc Q (f32 done) -> rw_cells asegs mc (Q + off) (f32 (x :: rest)) ->
evt asegs (lbr_l2_post zra zsp zgp ztp zt1 zt2 zs0 zs1 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 Q NZ n mI)
(MS (mkR zra zsp zgp ztp yt0 zt1 zt2 zs0 zs1 (Z_to_bv 64 (Q + off)) (Z_to_bv 64 (CDB + r)) (Z_to_bv 64 (CDB + r)) (Z_to_bv 64 kz) (Z_to_bv 64 (Q + off)) ya5 ya6 ya7 (Z_to_bv 64 SHB) zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F1 (Z_to_bv 64 0xae7b4) fc None mc (seg_rom asegs)).
Proof.
intros Q NZ n CDB CN CD mI zra zsp zgp ztp zt1 zt2 zs0 zs1 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 ENZ rest.
induction rest as [|x' rest IH]; intros done x off kz r yt0 ya5 ya6 ya7 F1 fc mc Q4 OBQ OF OBC LCD RO R0 R1 Hoff Hkz HN FRM MI MU WM DONE X;
pose proof OBQ as (OQ0 & OQ1 & _); pose proof OBC as (OC0 & OC1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
subst kz.
- cbn [length] in HN, R1. rewrite f32_cons, f32_nil in X.
lsp_rd asegs RO CDB CD r.
ato 0xae7c0. astep. chk_merge OBC 1.
ato 0xae7d4. astep. chk_merge OBQ 4.
ato 0xae7e0. astep. chk_merge OBQ 4.
ato 0xae80c. astep. cbn [length].
try sh_if.
ato 0xae840.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
unfold lbr_l2_post. finish; [ exact DONE | ].
rewrite length_app. cbn [length]. lia.
- cbn [length] in HN, BX, R1.
rewrite f32_cons in X. chunk_uncons X as X1.
lsp_rd asegs RO CDB CD r.
ato 0xae7c0. astep. chk_merge OBC 1.
ato 0xae7d4. astep. chk_merge OBQ 4.
ato 0xae7e0. astep. chk_merge OBQ 4.
ato 0xae80c. astep. cbn [length].
sh_if.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (Z.of_nat (S (S (length rest))) + -1) with (Z.of_nat (S (length rest))) by lia.
replace (Q + off + 4) with (Q + (off + 4)) in * by lia.
replace (CDB + r + 1) with (CDB + (r + 1)) by lia.
eapply (IH (done ++ [_]) x' (off + 4) _ (r + 1)); try eassumption; try reflexivity.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.

Definition lbr_l3_post (zra zsp zgp ztp zt0 zt1 zt2 zs1 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 : word) (Q NZ : Z) (n : nat) (mI : mem) : machine_state -> Prop :=
fun ms' => exists s0' a0' a1' a2' a3' a4' a5' a6' a7' F' fc' m' (ws : list word),
ms' = MS (mkR zra zsp zgp ztp zt0 zt1 zt2 s0' zs1 a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 SHB) zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F' (Z_to_bv 64 0xae8fc) fc' None m' (seg_rom asegs)
/\ munch [(Q, Q + NZ)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ frm0 fc' /\ rw_cells asegs m' Q (f32 ws) /\ length ws = n.

Lemma lbr_l3 : forall (Q NZ : Z) (n : nat) (CDB CN : Z) (CD : list byte) (mI : mem) (zra zsp zgp ztp zt0 zt1 zt2 zs1 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 : word), NZ = 4 * Z.of_nat n -> forall
(rest done : list word) (x : word) (off kz r : Z) (ya4 ya5 ya6 ya7 : word) (F1 : bvmap 5 word) fc mc,
Q mod 4 = 0 -> aobj asegs mI Q NZ -> offsh [(Q, Q + NZ)] ->
aobj asegs mI CDB CN -> Z.of_nat (length CD) = CN -> (forall m', mem_inv asegs m' -> u8ro asegs m' CDB CD) ->
0 <= r -> r + Z.of_nat (S (length rest)) <= CN ->
off = 4 * Z.of_nat (length done) -> kz = Z.of_nat (S (length rest)) -> (length done + 1 + length rest = n)%nat ->
frm0 fc -> mem_inv asegs mc -> munch [(Q, Q + NZ)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc Q (f32 done) -> rw_cells asegs mc (Q + off) (f32 (x :: rest)) ->
evt asegs (lbr_l3_post zra zsp zgp ztp zt0 zt1 zt2 zs1 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 Q NZ n mI)
(MS (mkR zra zsp zgp ztp zt0 zt1 zt2 (Z_to_bv 64 (Q + off)) zs1 (Z_to_bv 64 (Q + off)) (Z_to_bv 64 (CDB + r)) (Z_to_bv 64 (CDB + r)) (Z_to_bv 64 kz) ya4 ya5 ya6 ya7 (Z_to_bv 64 SHB) zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F1 (Z_to_bv 64 0xae870) fc None mc (seg_rom asegs)).
Proof.
intros Q NZ n CDB CN CD mI zra zsp zgp ztp zt0 zt1 zt2 zs1 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 ENZ rest.
induction rest as [|x' rest IH]; intros done x off kz r ya4 ya5 ya6 ya7 F1 fc mc Q4 OBQ OF OBC LCD RO R0 R1 Hoff Hkz HN FRM MI MU WM DONE X;
pose proof OBQ as (OQ0 & OQ1 & _); pose proof OBC as (OC0 & OC1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
subst kz.
- cbn [length] in HN, R1. rewrite f32_cons, f32_nil in X.
lsp_rd asegs RO CDB CD r.
ato 0xae87c. astep. chk_merge OBC 1.
ato 0xae890. astep. chk_merge OBQ 4.
ato 0xae89c. astep. chk_merge OBQ 4.
ato 0xae8c8. astep. cbn [length].
try sh_if.
ato 0xae8fc.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
unfold lbr_l3_post. finish; [ exact DONE | ].
rewrite length_app. cbn [length]. lia.
- cbn [length] in HN, BX, R1.
rewrite f32_cons in X. chunk_uncons X as X1.
lsp_rd asegs RO CDB CD r.
ato 0xae87c. astep. chk_merge OBC 1.
ato 0xae890. astep. chk_merge OBQ 4.
ato 0xae89c. astep. chk_merge OBQ 4.
ato 0xae8c8. astep. cbn [length].
sh_if.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (Z.of_nat (S (S (length rest))) + -1) with (Z.of_nat (S (length rest))) by lia.
replace (Q + off + 4) with (Q + (off + 4)) in * by lia.
replace (CDB + r + 1) with (CDB + (r + 1)) by lia.
eapply (IH (done ++ [_]) x' (off + 4) _ (r + 1)); try eassumption; try reflexivity.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.

Section W.
Context {ptr : Type}.
Variables (A D IQ usp lo : Z) (b : bits_st ptr).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Hypothesis REP : bits_rep asegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis OBA : aobj asegs m A BITS_SIZEOF.
Hypothesis OBD : aobj asegs m D (sb_buf_size b).
Hypothesis OBQ : aobj asegs m IQ 40.
Hypothesis TABS : lsp_tabs m.
Hypothesis Q4 : IQ mod 4 = 0.
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis QSH : hidp (IQ + 40 <= SH_LO \/ SH_HI <= IQ).
Hypothesis ATOP : IMG_TOP <= A.
Hypothesis QTOP : IMG_TOP <= IQ.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis DLO : D + sb_buf_size b <= lo.
Hypothesis QAP : hidp (IQ + 40 <= lo \/ usp <= IQ).
Hypothesis SEPQA : hidp (IQ + 40 <= A \/ A + BITS_SIZEOF <= IQ).
Hypothesis SEPQD : hidp (IQ + 40 <= D \/ D + sb_buf_size b <= IQ).
Hypothesis LO : lo <= usp - 128.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Local Notation W := [(A, A + 48); (IQ, IQ + 40); (usp + -128, usp)].

Lemma lsp_unquant_lbr_walk : forall (old : list word) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
rw_cells asegs m IQ (f32 old) -> length old = 10%nat ->
lib_consts m -> client_consts m -> stk asegs m lo usp -> mem_inv asegs m -> frm0 fc ->
evt asegs (lsp_unquant_postA LspUnquantLbr A D IQ usp lo b ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IQ) (Z_to_bv 64 10) (Z_to_bv 64 A) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_unquant_lbr) fc None m (seg_rom asegs)).
Proof.
intros old t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc X LX LC CC ST MI FRM.
pose proof TABS as (OBC0 & OBC1 & OBC2 & OBC3 & OBC4 & OBC5 & OBC6).
unfold A_cdbk_nb, A_cdbk_nb_low1, A_cdbk_nb_low2, A_cdbk_nb_high1, A_cdbk_nb_high2, A_high_lsp_cdbk, A_high_lsp_cdbk2 in *.
destruct cdbk_nb_at as (CD0 & LCD0 & RO0).
destruct cdbk_nb_low1_at as (CD1 & LCD1 & RO1).
destruct cdbk_nb_high1_at as (CD2 & LCD2 & RO2).
unfold A_cdbk_nb, A_cdbk_nb_low1, A_cdbk_nb_low2, A_cdbk_nb_high1, A_cdbk_nb_high2, A_high_lsp_cdbk, A_high_lsp_cdbk2 in *.
pose proof (lib_const m _ _ LC (ltac:(lc_in) : In (GOT_f41c8, LC_GOT_f41c8) LIB_TABLES)) as GC0.
pose proof (lib_const m _ _ LC (ltac:(lc_in) : In (GOT_f41d0, LC_GOT_f41d0) LIB_TABLES)) as GC1.
pose proof (lib_const m _ _ LC (ltac:(lc_in) : In (GOT_f41e0, LC_GOT_f41e0) LIB_TABLES)) as GC2.
unfold GOT_f41c8, LC_GOT_f41c8, GOT_f41d0, LC_GOT_f41d0, GOT_f41e0, LC_GOT_f41e0 in *. clear LC.
pose proof CC as (G1 & G2 & G3 & G4).
unfold A_lsp_unquant_lbr, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof REP as ((rj0 & Lrj0 & OBJ) & (bs0 & DAT & Hbs0) & SIDE0). unfold bits_cells in OBJ.
assert (Lbs0 : Z.of_nat (length bs0) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs0, zlength_map_unsigned in OK'. lia. }
pose proof OBA as (OA0 & OA1 & _). pose proof OBD as (OD0 & OD1 & _). pose proof OBQ as (OQ0 & OQ1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP in ATOP, QTOP.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W).
{ pose proof (ASH : _ \/ _) as Y1. pose proof (QSH : _ \/ _) as Y2. clear - Y1 Y2 LOS LO. cbn. unfold SH_LO, SH_HI in *. lia. }
assert (OFQ : IQ + 40 <= SH_LO \/ SH_HI <= IQ) by (destruct OF as (_ & O2 & _); exact O2).
pose proof (QAP : _ \/ _) as QAP'. pose proof (SEPQA : _ \/ _) as SEPQA'. pose proof (SEPQD : _ \/ _) as SEPQD'. hide_disj.
destruct old as [|q0 qrest]; [cbn [length] in LX; lia|]. cbn [length] in LX.
carve_frame 48%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xae65c. astep. try sh_if.
ato 0xae674.
replace (Z_to_bv 64 IQ) with (Z_to_bv 64 (IQ + 0)) by (rewrite Z.add_0_r; reflexivity).
replace IQ with (IQ + 0) in X at 1 by lia.
vloop_facts OBQ MU OF IQ IQ 40.
assert (OFW : offsh [(IQ, IQ + 40)]) by (unfold hid in OFQ; clear - OFQ; cbn; lia).
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [ eapply (lbr_l0 IQ 40 10%nat mc) with (rest := qrest) (done := []) (x := q0) (off := 0)
| clear MU0 WM0 OBQc D0 OFW X LX FRM; post_call segs mc ]
end.
1: reflexivity. 1: exact Q4. 1: exact OBQc. 1: exact OFW. 1: reflexivity. 1: (cbn [length]; lia). 1: (cbn [length]; lia). 1: reflexivity.
1: eassumption. 1: eassumption. 1: exact MU0. 1: exact WM0. 1: exact D0. 1: exact X.
vloop_names IQ X LX FRM.

ato 0xae6c4. rebase_bits A D b rj0 bs0.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -48) lo b 6 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO DLO).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
change (snd (speex_bits_unpack_unsigned b 6)) with (ub b 6) in *. change (fst (speex_bits_unpack_unsigned b 6)) with (uv b 6) in *.
pose proof (ub_ok b 6 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 6) with 64 in V1R.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep asegs _ A D (ub b 6) |- _ => destruct H as ((rj1 & Lrj1 & OBJ) & (bs1 & DAT & Hbs1) & SIDE1); unfold bits_cells in OBJ end.
assert (Lbs1 : Z.of_nat (length bs1) = sb_buf_size b).
{ pose proof OK1 as OK'. unfold bits_ok in OK'. rewrite Hbs1, zlength_map_unsigned in OK'. lia. }
ato 0xae6f0.
norm_cb 149632 (uv b 6 * 10).
lazymatch type of X with rw_cells _ _ _ (f32 ?l) => rename l into ws0 end.
destruct ws0 as [|w0 wr0]; [cbn [length] in LX; lia|]. cbn [length] in LX.
replace (Z_to_bv 64 IQ) with (Z_to_bv 64 (IQ + 0)) by (rewrite Z.add_0_r; reflexivity).
replace IQ with (IQ + 0) in X at 1 by lia.
vloop_facts OBQ MU OF IQ IQ 40. vloop_cb OBC0 MU OF 149632 640.
assert (OFW : offsh [(IQ, IQ + 40)]) by (unfold hid in OFQ; clear - OFQ; cbn; lia).
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [ eapply (lbr_l1 IQ 40 10%nat 149632 640 CD0 mc) with (rest := wr0) (done := []) (x := w0) (off := 0) (r := uv b 6 * 10)
| clear MU0 WM0 OBQc OBCc D0 OFW X LX FRM; post_call segs mc ]
end.
1: reflexivity. 1: exact Q4. 1: exact OBQc. 1: exact OFW. 1: exact OBCc. 1: (rewrite LCD0; reflexivity). 1: exact RO0. 1: lia. 1: (cbn [length]; lia).
1: reflexivity. 1: (cbn [length]; lia). 1: (cbn [length]; lia).
1: eassumption. 1: eassumption. 1: exact MU0. 1: exact WM0. 1: exact D0. 1: exact X.
vloop_names IQ X LX FRM.

ato 0xae784. rebase_bits A D (ub b 6) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -48) lo (ub b 6) 6 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK1 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ1; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
change (snd (speex_bits_unpack_unsigned (ub b 6) 6)) with (ub (ub b 6) 6) in *. change (fst (speex_bits_unpack_unsigned (ub b 6) 6)) with (uv (ub b 6) 6) in *.
pose proof (ub_ok (ub b 6) 6 OK1 ltac:(lia)) as (OK2 & SZ2 & V2R). change (2 ^ 6) with 64 in V2R. rewrite SZ1 in SZ2.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep asegs _ A D (ub (ub b 6) 6) |- _ => destruct H as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2); unfold bits_cells in OBJ end.
assert (Lbs2 : Z.of_nat (length bs2) = sb_buf_size b).
{ pose proof OK2 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }
ato 0xae7b4.
norm_cb 150432 (uv (ub b 6) 6 * 4 + uv (ub b 6) 6).
lazymatch type of X with rw_cells _ _ _ (f32 ?l) => rename l into ws1 end.
destruct ws1 as [|u1_0 [|u1_1 [|u1_2 [|u1_3 [|u1_4 [|u1_5 [|u1_6 [|u1_7 [|u1_8 [|u1_9 [|? ?]]]]]]]]]]]; try (cbn [length] in LX; lia). clear LX.
chunk_split_f32 X at 5%nat as XL. rename X into XH.
replace (Z_to_bv 64 IQ) with (Z_to_bv 64 (IQ + 0)) by (rewrite Z.add_0_r; reflexivity).
replace IQ with (IQ + 0) in XL at 1 by lia.
vloop_facts OBQ MU OF IQ IQ 20. vloop_cb OBC1 MU OF 150432 320.
assert (OFW : offsh [(IQ, IQ + 20)]) by (unfold hid in OFQ; clear - OFQ; cbn; lia).
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [ eapply (lbr_l2 IQ 20 5%nat 150432 320 CD1 mc) with (rest := [u1_1; u1_2; u1_3; u1_4]) (done := []) (x := u1_0) (off := 0) (r := uv (ub b 6) 6 * 4 + uv (ub b 6) 6)
| clear MU0 WM0 OBQc OBCc D0 OFW XL  FRM; post_call segs mc ]
end.
1: reflexivity. 1: exact Q4. 1: exact OBQc. 1: exact OFW. 1: exact OBCc. 1: (rewrite LCD1; reflexivity). 1: exact RO1. 1: lia. 1: (cbn [length]; lia).
1: reflexivity. 1: (cbn [length]; lia). 1: (cbn [length]; lia).
1: eassumption. 1: eassumption. 1: exact MU0. 1: exact WM0. 1: exact D0. 1: exact XL.
vloop_names IQ XL LXL FRM.

ato 0xae848. rebase_bits A D (ub (ub b 6) 6) rj2 bs2. rewrite <- SZ2 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -48) lo (ub (ub b 6) 6) 6 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK2 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ2; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
change (snd (speex_bits_unpack_unsigned (ub (ub b 6) 6) 6)) with (ub (ub (ub b 6) 6) 6) in *. change (fst (speex_bits_unpack_unsigned (ub (ub b 6) 6) 6)) with (uv (ub (ub b 6) 6) 6) in *.
pose proof (ub_ok (ub (ub b 6) 6) 6 OK2 ltac:(lia)) as (OK3 & SZ3 & V3R). change (2 ^ 6) with 64 in V3R. rewrite SZ2 in SZ3.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep asegs _ A D (ub (ub (ub b 6) 6) 6) |- _ => destruct H as ((rj3 & Lrj3 & OBJ) & (bs3 & DAT & Hbs3) & SIDE3); unfold bits_cells in OBJ end.
assert (Lbs3 : Z.of_nat (length bs3) = sb_buf_size b).
{ pose proof OK3 as OK'. unfold bits_ok in OK'. rewrite Hbs3, zlength_map_unsigned in OK'. lia. }
ato 0xae870.
norm_cb 151200 (uv (ub (ub b 6) 6) 6 * 4 + uv (ub (ub b 6) 6) 6).
replace (Z_to_bv 64 (IQ + 20)) with (Z_to_bv 64 (IQ + 20 + 0)) by (rewrite Z.add_0_r; reflexivity).
replace (IQ + 20) with (IQ + 20 + 0) in XH at 1 by lia.
vloop_facts OBQ MU OF IQ (IQ + 20) 20. vloop_cb OBC3 MU OF 151200 320.
assert (OFW : offsh [(IQ + 20, IQ + 20 + 20)]) by (unfold hid in OFQ; clear - OFQ; cbn; lia).
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [ eapply (lbr_l3 (IQ + 20) 20 5%nat 151200 320 CD2 mc) with (rest := [u1_6; u1_7; u1_8; u1_9]) (done := []) (x := u1_5) (off := 0) (r := uv (ub (ub b 6) 6) 6 * 4 + uv (ub (ub b 6) 6) 6)
| clear MU0 WM0 OBQc OBCc D0 OFW XH  FRM; post_call segs mc ]
end.
1: reflexivity. 1: (clear - Q4; rewrite Z.add_mod, Q4 by lia; reflexivity). 1: exact OBQc. 1: exact OFW. 1: exact OBCc. 1: (rewrite LCD2; reflexivity). 1: exact RO2. 1: lia. 1: (cbn [length]; lia).
1: reflexivity. 1: (cbn [length]; lia). 1: (cbn [length]; lia).
1: eassumption. 1: eassumption. 1: exact MU0. 1: exact WM0. 1: exact D0. 1: exact XH.
vloop_names (IQ + 20) XH LXH FRM.

ato 0xae910. release_frame FR ST usp. astep. astep.
lazymatch type of XL with rw_cells _ _ _ (f32 ?l) => rename l into wXL end.
destruct wXL as [|l0 [|l1 [|l2 [|l3 [|l4 [|? ?]]]]]]; try (cbn [length] in LXL; lia).
lazymatch type of XH with rw_cells _ _ _ (f32 ?l) => rename l into wXH end.
destruct wXH as [|h0 [|h1 [|h2 [|h3 [|h4 [|? ?]]]]]]; try (cbn [length] in LXH; lia).
chunk_cat XL XH. rewrite <- f32_app in XL. cbn [app] in XL. rename XL into X.
unfold lsp_unquant_postA, LSPQ_DEPTH, BITS_SIZEOF, lsp_order, lsp_bits. change (4 * 10) with 40. change (Z.to_nat 10) with 10%nat.
finish; first [ exact X | exact LX | reflexivity | exact OK3 | idtac ].
split; [exists rj3; split; [exact Lrj3| exact OBJ]| split; [exists bs3; split; [exact DAT| exact Hbs3]| exact SIDE3]].
Qed.
End W.

Lemma lsp_unquant_lbr_stmt : forall ptr, @lsp_unquant_stmtA ptr LspUnquantLbr.
Proof.
intros ptr A D IQ usp lo b old ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
REP OK OBA OBD OBQ TABS LC CC X LX Q4 ASH QSH ATOP QTOP ALO DLO QAP SEPQA SEPQD ST LO LOS SPH MI FRM.
cbn [lsp_order lsp_entryA] in *. change (4 * 10) with 40 in *. change (Z.to_nat 10) with 10%nat in *. unfold LSPQ_DEPTH in LO.
eapply lsp_unquant_lbr_walk; eassumption.
Qed.
