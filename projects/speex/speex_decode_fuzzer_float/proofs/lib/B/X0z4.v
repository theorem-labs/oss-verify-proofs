(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1dk X1cs X1dg X1df X1ck X1co X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0ys X0wh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yt X0z5.
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

Definition nb_l0_post (zra zsp zgp ztp zt0 zt1 zt2 zs1 za7 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6  : word) (IQ qoff NZ : Z) (n : nat) (mI : mem) : machine_state -> Prop :=
fun ms' => exists a0' a1' a2' a4' a5' a6' F' fc' m' (ws : list word),
ms' = MS (mkR zra zsp zgp ztp zt0 zt1 zt2 (Z_to_bv 64 IQ) zs1 a0' a1' a2' (Z_to_bv 64 1) a4' a5' a6' za7 (Z_to_bv 64 SHB) (Z_to_bv 64 1) zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F' (Z_to_bv 64 0xb3ce8) fc' None m' (seg_rom bsegs)
/\ munch [(IQ + qoff, IQ + qoff + NZ)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc' /\ rw_cells bsegs m' (IQ + qoff) (f32 ws) /\ length ws = n.

Lemma nb_l0 : forall (IQ ON qoff NZ : Z) (n : nat) (mI : mem) (zra zsp zgp ztp zt0 zt1 zt2 zs1 za7 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6  : word),
NZ = 4 * Z.of_nat n -> 0 <= qoff -> qoff + NZ <= ON -> 0 < IQ -> IQ mod 4 = 0 -> qoff mod 4 = 0 -> aobj bsegs mI IQ ON -> offsh [(IQ + qoff, IQ + qoff + NZ)] ->
forall (rest done : list word) (x : word) (boff kz i : Z) (wa0 wa1 wa2 wa4 ya5 ya6 : word) (F1 : bvmap 5 word) fc mc,
wa0 = (Z_to_bv 64 (IQ + boff)) ->
wa1 = (Z_to_bv 64 kz) ->
wa2 = (Z_to_bv 64 i) ->
wa4 = (Z_to_bv 64 (IQ + boff)) ->
boff = qoff + 4 * Z.of_nat (length done) -> kz = Z.of_nat (S (length rest)) -> (length done + 1 + length rest = n)%nat -> i = Z.of_nat (length done) ->
frm0 fc -> mem_inv bsegs mc -> munch [(IQ + qoff, IQ + qoff + NZ)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (IQ + qoff) (f32 done) -> rw_cells bsegs mc (IQ + boff) (f32 (x :: rest)) ->
evt bsegs (nb_l0_post zra zsp zgp ztp zt0 zt1 zt2 zs1 za7 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6  IQ qoff NZ n mI)
(MS (mkR zra zsp zgp ztp zt0 zt1 zt2 (Z_to_bv 64 IQ) zs1 wa0 wa1 wa2 (Z_to_bv 64 1) wa4 ya5 ya6 za7 (Z_to_bv 64 SHB) (Z_to_bv 64 1) zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F1 (Z_to_bv 64 0xb3c8c) fc None mc (seg_rom bsegs)).
Proof.
intros IQ ON qoff NZ n mI zra zsp zgp ztp zt0 zt1 zt2 zs1 za7 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6  ENZ Q0 QN IQ0 Q4 QO4 OBQ OF rest.
induction rest as [|x' rest IH]; intros done x boff kz i wa0 wa1 wa2 wa4 ya5 ya6 F1 fc mc EWa0 EWa1 EWa2 EWa4 Hoff Hkz HN Hi FRM MI MU WM DONE X;
subst wa0 wa1 wa2 wa4;
pose proof OBQ as (OQ0 & OQ1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
subst kz i.
- cbn [length] in HN. rewrite f32_cons, f32_nil in X.
bato 0xb3cac. astep. chk_merge OBQ 4.
bato 0xb3cd0. bnorm. astep. cbn [length].
try sh_if.
bato 0xb3ce8.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
unfold nb_l0_post. finish; [ exact DONE | ].
rewrite length_app. cbn [length]. lia.
- cbn [length] in HN, BX.
rewrite f32_cons in X. chunk_uncons X as X1.
bato 0xb3cac. astep. chk_merge OBQ 4.
bato 0xb3cd0. bnorm. astep. cbn [length].
sh_if.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (Z.of_nat (S (S (length rest))) + -1) with (Z.of_nat (S (length rest))) by lia.
replace (IQ + boff + 4) with (IQ + (boff + 4)) in * by lia.
eapply (IH (done ++ [_]) x' (boff + 4) (Z.of_nat (S (length rest))) (Z.of_nat (length done) + 1)); try eassumption; try reflexivity.
all: try (f_equal; lia).
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.

Definition nb_l1_post (zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt4 zt5 zt6 wa7 : word) (IQ qoff NZ CDB : Z) (n : nat) (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' t1' t2' a0' a1' a2' a3' t3' F' fc' m' (ws : list word),
ms' = MS (mkR zra zsp zgp ztp t0' t1' t2' (Z_to_bv 64 IQ) zs1 a0' a1' a2' a3' (Z_to_bv 64 CDB) (Z_to_bv 64 0) (Z_to_bv 64 1) wa7 (Z_to_bv 64 SHB) (Z_to_bv 64 1) zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 t3' zt4 zt5 zt6)
F' (Z_to_bv 64 0xb3e08) fc' None m' (seg_rom bsegs)
/\ munch [(IQ + qoff, IQ + qoff + NZ)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc' /\ rw_cells bsegs m' (IQ + qoff) (f32 ws) /\ length ws = n.

Lemma nb_l1 : forall (IQ ON qoff NZ row : Z) (n : nat) (CDB CN : Z) (CD : list byte) (mI : mem) (zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt4 zt5 zt6 wa7 : word),
NZ = 4 * Z.of_nat n -> 0 <= qoff -> qoff + NZ <= ON -> 0 < IQ -> IQ mod 4 = 0 -> qoff mod 4 = 0 -> aobj bsegs mI IQ ON -> offsh [(IQ + qoff, IQ + qoff + NZ)] ->
wa7 = (Z_to_bv 64 row) ->
aobj bsegs mI CDB CN -> Z.of_nat (length CD) = CN -> (forall m', mem_inv bsegs m' -> u8ro bsegs m' CDB CD) -> 0 < CDB -> CN < 2^31 ->
0 <= row -> row + Z.of_nat n <= CN ->
forall (rest done : list word) (x : word) (boff kz i : Z) (wt0 wa0 wa2 wa3 yt1 yt2 ya1 yt3 : word) (F1 : bvmap 5 word) fc mc,
wt0 = (Z_to_bv 64 (IQ + boff)) ->
wa0 = (Z_to_bv 64 (IQ + boff)) ->
wa2 = (Z_to_bv 64 i) ->
wa3 = (Z_to_bv 64 kz) ->
boff = qoff + 4 * Z.of_nat (length done) -> kz = Z.of_nat (S (length rest)) -> (length done + 1 + length rest = n)%nat -> i = Z.of_nat (length done) ->
frm0 fc -> mem_inv bsegs mc -> munch [(IQ + qoff, IQ + qoff + NZ)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (IQ + qoff) (f32 done) -> rw_cells bsegs mc (IQ + boff) (f32 (x :: rest)) ->
evt bsegs (nb_l1_post zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt4 zt5 zt6 wa7 IQ qoff NZ CDB n mI)
(MS (mkR zra zsp zgp ztp wt0 yt1 yt2 (Z_to_bv 64 IQ) zs1 wa0 ya1 wa2 wa3 (Z_to_bv 64 CDB) (Z_to_bv 64 0) (Z_to_bv 64 1) wa7 (Z_to_bv 64 SHB) (Z_to_bv 64 1) zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 yt3 zt4 zt5 zt6)
F1 (Z_to_bv 64 0xb3d3c) fc None mc (seg_rom bsegs)).
Proof.
intros IQ ON qoff NZ row n CDB CN CD mI zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt4 zt5 zt6 wa7 ENZ Q0 QN IQ0 Q4 QO4 OBQ OF EWa7 OBC LCD RO C0 CNB R0 R1 rest.
induction rest as [|x' rest IH]; intros done x boff kz i wt0 wa0 wa2 wa3 yt1 yt2 ya1 yt3 F1 fc mc EWt0 EWa0 EWa2 EWa3 Hoff Hkz HN Hi FRM MI MU WM DONE X;
subst wt0 wa0 wa2 wa3 wa7;
pose proof OBQ as (OQ0 & OQ1 & _); pose proof OBC as (OC0 & OC1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
subst kz i.
- cbn [length] in HN. rewrite f32_cons, f32_nil in X.
lsp_rdB RO CDB CD row (Z.of_nat (length done)).
bato 0xb3d5c. astep. chk_merge OBQ 4.
bato 0xb3d98. bnorm. chk_hint OBC. astep. bato 0xb3da0. astep. chk_merge OBC 1. match goal with H : sh_cur _ |- _ => clear H end.
bato 0xb3dac. astep. chk_merge OBQ 4.
bato 0xb3dd4. bnorm. astep. cbn [length].
try sh_if.
bato 0xb3e08.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
unfold nb_l1_post. finish; [ exact DONE | ].
rewrite length_app. cbn [length]. lia.
- cbn [length] in HN, BX.
rewrite f32_cons in X. chunk_uncons X as X1.
lsp_rdB RO CDB CD row (Z.of_nat (length done)).
bato 0xb3d5c. astep. chk_merge OBQ 4.
bato 0xb3d98. bnorm. chk_hint OBC. astep. bato 0xb3da0. astep. chk_merge OBC 1. match goal with H : sh_cur _ |- _ => clear H end.
bato 0xb3dac. astep. chk_merge OBQ 4.
bato 0xb3dd4. bnorm. astep. cbn [length].
sh_if.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (Z.of_nat (S (S (length rest))) + -1) with (Z.of_nat (S (length rest))) by lia.
replace (IQ + boff + 4) with (IQ + (boff + 4)) in * by lia.
eapply (IH (done ++ [_]) x' (boff + 4) (Z.of_nat (S (length rest))) (Z.of_nat (length done) + 1)); try eassumption; try reflexivity.
all: try (f_equal; lia).
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.

Definition nb_l2_post (zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 : word) (IQ qoff NZ CDB : Z) (n : nat) (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' t1' t2' a0' a1' a2' a3' F' fc' m' (ws : list word),
ms' = MS (mkR zra zsp zgp ztp t0' t1' t2' (Z_to_bv 64 IQ) zs1 a0' a1' a2' a3' (Z_to_bv 64 CDB) (Z_to_bv 64 0) wa6 wa7 (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - IQ)) zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F' (Z_to_bv 64 0xb3f04) fc' None m' (seg_rom bsegs)
/\ munch [(IQ + qoff, IQ + qoff + NZ)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc' /\ rw_cells bsegs m' (IQ + qoff) (f32 ws) /\ length ws = n.

Lemma nb_l2 : forall (IQ ON qoff NZ lim row : Z) (n : nat) (CDB CN : Z) (CD : list byte) (mI : mem) (zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 : word),
NZ = 4 * Z.of_nat n -> 0 <= qoff -> qoff + NZ <= ON -> 0 < IQ -> IQ mod 4 = 0 -> qoff mod 4 = 0 -> aobj bsegs mI IQ ON -> offsh [(IQ + qoff, IQ + qoff + NZ)] ->
lim = qoff + NZ ->
wa6 = (Z_to_bv 64 row) ->
wa7 = (Z_to_bv 64 lim) ->
aobj bsegs mI CDB CN -> Z.of_nat (length CD) = CN -> (forall m', mem_inv bsegs m' -> u8ro bsegs m' CDB CD) -> 0 < CDB -> CN < 2^31 ->
0 <= row -> row + Z.of_nat n <= CN ->
forall (rest done : list word) (x : word) (boff kz i : Z) (wa2 wa3 yt0 yt1 yt2 ya0 ya1 : word) (F1 : bvmap 5 word) fc mc,
wa2 = (Z_to_bv 64 boff) ->
wa3 = (Z_to_bv 64 i) ->
boff = qoff + 4 * Z.of_nat (length done) -> kz = Z.of_nat (S (length rest)) -> (length done + 1 + length rest = n)%nat -> i = Z.of_nat (length done) ->
frm0 fc -> mem_inv bsegs mc -> munch [(IQ + qoff, IQ + qoff + NZ)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (IQ + qoff) (f32 done) -> rw_cells bsegs mc (IQ + boff) (f32 (x :: rest)) ->
evt bsegs (nb_l2_post zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 IQ qoff NZ CDB n mI)
(MS (mkR zra zsp zgp ztp yt0 yt1 yt2 (Z_to_bv 64 IQ) zs1 ya0 ya1 wa2 wa3 (Z_to_bv 64 CDB) (Z_to_bv 64 0) wa6 wa7 (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - IQ)) zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F1 (Z_to_bv 64 0xb3e4c) fc None mc (seg_rom bsegs)).
Proof.
intros IQ ON qoff NZ lim row n CDB CN CD mI zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 ENZ Q0 QN IQ0 Q4 QO4 OBQ OF ELIM EWa6 EWa7 OBC LCD RO C0 CNB R0 R1 rest.
induction rest as [|x' rest IH]; intros done x boff kz i wa2 wa3 yt0 yt1 yt2 ya0 ya1 F1 fc mc EWa2 EWa3 Hoff Hkz HN Hi FRM MI MU WM DONE X;
subst wa2 wa3 wa6 wa7;
pose proof OBQ as (OQ0 & OQ1 & _); pose proof OBC as (OC0 & OC1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
subst kz i.
- cbn [length] in HN. rewrite f32_cons, f32_nil in X.
lsp_rdB RO CDB CD row (Z.of_nat (length done)).
bato 0xb3e60. astep. chk_merge OBQ 4.
bato 0xb3e9c. bnorm. chk_hint OBC. astep. bato 0xb3ea4. astep. chk_merge OBC 1. match goal with H : sh_cur _ |- _ => clear H end.
bato 0xb3eb0. astep. chk_merge OBQ 4.
bato 0xb3ed0. bnorm. astep. cbn [length].
try sh_if.
bato 0xb3f04.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
unfold nb_l2_post. finish; [ exact DONE | ].
rewrite length_app. cbn [length]. lia.
- cbn [length] in HN, BX.
rewrite f32_cons in X. chunk_uncons X as X1.
lsp_rdB RO CDB CD row (Z.of_nat (length done)).
bato 0xb3e60. astep. chk_merge OBQ 4.
bato 0xb3e9c. bnorm. chk_hint OBC. astep. bato 0xb3ea4. astep. chk_merge OBC 1. match goal with H : sh_cur _ |- _ => clear H end.
bato 0xb3eb0. astep. chk_merge OBQ 4.
bato 0xb3ed0. bnorm. astep. cbn [length].
sh_if.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (Z.of_nat (S (S (length rest))) + -1) with (Z.of_nat (S (length rest))) by lia.
replace (IQ + boff + 4) with (IQ + (boff + 4)) in * by lia.
eapply (IH (done ++ [_]) x' (boff + 4) (Z.of_nat (S (length rest))) (Z.of_nat (length done) + 1)); try eassumption; try reflexivity.
all: try (f_equal; lia).
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.

Definition nb_l3_post (zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 : word) (IQ qoff NZ CDB : Z) (n : nat) (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' t1' t2' a0' a1' a2' a3' F' fc' m' (ws : list word),
ms' = MS (mkR zra zsp zgp ztp t0' t1' t2' (Z_to_bv 64 IQ) zs1 a0' a1' a2' a3' (Z_to_bv 64 CDB) (Z_to_bv 64 0) wa6 wa7 (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - IQ)) zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F' (Z_to_bv 64 0xb3ffc) fc' None m' (seg_rom bsegs)
/\ munch [(IQ + qoff, IQ + qoff + NZ)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc' /\ rw_cells bsegs m' (IQ + qoff) (f32 ws) /\ length ws = n.

Lemma nb_l3 : forall (IQ ON qoff NZ lim row : Z) (n : nat) (CDB CN : Z) (CD : list byte) (mI : mem) (zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 : word),
NZ = 4 * Z.of_nat n -> 0 <= qoff -> qoff + NZ <= ON -> 0 < IQ -> IQ mod 4 = 0 -> qoff mod 4 = 0 -> aobj bsegs mI IQ ON -> offsh [(IQ + qoff, IQ + qoff + NZ)] ->
lim = qoff + NZ ->
wa6 = (Z_to_bv 64 row) ->
wa7 = (Z_to_bv 64 lim) ->
aobj bsegs mI CDB CN -> Z.of_nat (length CD) = CN -> (forall m', mem_inv bsegs m' -> u8ro bsegs m' CDB CD) -> 0 < CDB -> CN < 2^31 ->
0 <= row -> row + Z.of_nat n <= CN ->
forall (rest done : list word) (x : word) (boff kz i : Z) (wa2 wa3 yt0 yt1 yt2 ya0 ya1 : word) (F1 : bvmap 5 word) fc mc,
wa2 = (Z_to_bv 64 boff) ->
wa3 = (Z_to_bv 64 i) ->
boff = qoff + 4 * Z.of_nat (length done) -> kz = Z.of_nat (S (length rest)) -> (length done + 1 + length rest = n)%nat -> i = Z.of_nat (length done) ->
frm0 fc -> mem_inv bsegs mc -> munch [(IQ + qoff, IQ + qoff + NZ)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (IQ + qoff) (f32 done) -> rw_cells bsegs mc (IQ + boff) (f32 (x :: rest)) ->
evt bsegs (nb_l3_post zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 IQ qoff NZ CDB n mI)
(MS (mkR zra zsp zgp ztp yt0 yt1 yt2 (Z_to_bv 64 IQ) zs1 ya0 ya1 wa2 wa3 (Z_to_bv 64 CDB) (Z_to_bv 64 0) wa6 wa7 (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - IQ)) zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F1 (Z_to_bv 64 0xb3f44) fc None mc (seg_rom bsegs)).
Proof.
intros IQ ON qoff NZ lim row n CDB CN CD mI zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 ENZ Q0 QN IQ0 Q4 QO4 OBQ OF ELIM EWa6 EWa7 OBC LCD RO C0 CNB R0 R1 rest.
induction rest as [|x' rest IH]; intros done x boff kz i wa2 wa3 yt0 yt1 yt2 ya0 ya1 F1 fc mc EWa2 EWa3 Hoff Hkz HN Hi FRM MI MU WM DONE X;
subst wa2 wa3 wa6 wa7;
pose proof OBQ as (OQ0 & OQ1 & _); pose proof OBC as (OC0 & OC1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
subst kz i.
- cbn [length] in HN. rewrite f32_cons, f32_nil in X.
lsp_rdB RO CDB CD row (Z.of_nat (length done)).
bato 0xb3f58. astep. chk_merge OBQ 4.
bato 0xb3f94. bnorm. chk_hint OBC. astep. bato 0xb3f9c. astep. chk_merge OBC 1. match goal with H : sh_cur _ |- _ => clear H end.
bato 0xb3fa8. astep. chk_merge OBQ 4.
bato 0xb3fc8. bnorm. astep. cbn [length].
try sh_if.
bato 0xb3ffc.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
unfold nb_l3_post. finish; [ exact DONE | ].
rewrite length_app. cbn [length]. lia.
- cbn [length] in HN, BX.
rewrite f32_cons in X. chunk_uncons X as X1.
lsp_rdB RO CDB CD row (Z.of_nat (length done)).
bato 0xb3f58. astep. chk_merge OBQ 4.
bato 0xb3f94. bnorm. chk_hint OBC. astep. bato 0xb3f9c. astep. chk_merge OBC 1. match goal with H : sh_cur _ |- _ => clear H end.
bato 0xb3fa8. astep. chk_merge OBQ 4.
bato 0xb3fc8. bnorm. astep. cbn [length].
sh_if.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (Z.of_nat (S (S (length rest))) + -1) with (Z.of_nat (S (length rest))) by lia.
replace (IQ + boff + 4) with (IQ + (boff + 4)) in * by lia.
eapply (IH (done ++ [_]) x' (boff + 4) (Z.of_nat (S (length rest))) (Z.of_nat (length done) + 1)); try eassumption; try reflexivity.
all: try (f_equal; lia).
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.

Definition nb_l4_post (zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 : word) (IQ qoff NZ CDB : Z) (n : nat) (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' t1' t2' a0' a1' a2' a3' F' fc' m' (ws : list word),
ms' = MS (mkR zra zsp zgp ztp t0' t1' t2' (Z_to_bv 64 IQ) zs1 a0' a1' a2' a3' (Z_to_bv 64 CDB) (Z_to_bv 64 0) wa6 wa7 (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - IQ)) zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F' (Z_to_bv 64 0xb40ec) fc' None m' (seg_rom bsegs)
/\ munch [(IQ + qoff, IQ + qoff + NZ)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc' /\ rw_cells bsegs m' (IQ + qoff) (f32 ws) /\ length ws = n.

Lemma nb_l4 : forall (IQ ON qoff NZ lim row : Z) (n : nat) (CDB CN : Z) (CD : list byte) (mI : mem) (zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 : word),
NZ = 4 * Z.of_nat n -> 0 <= qoff -> qoff + NZ <= ON -> 0 < IQ -> IQ mod 4 = 0 -> qoff mod 4 = 0 -> aobj bsegs mI IQ ON -> offsh [(IQ + qoff, IQ + qoff + NZ)] ->
lim = qoff + NZ ->
wa6 = (Z_to_bv 64 row) ->
wa7 = (Z_to_bv 64 lim) ->
aobj bsegs mI CDB CN -> Z.of_nat (length CD) = CN -> (forall m', mem_inv bsegs m' -> u8ro bsegs m' CDB CD) -> 0 < CDB -> CN < 2^31 ->
0 <= row -> row + Z.of_nat n <= CN ->
forall (rest done : list word) (x : word) (boff kz i : Z) (wa2 wa3 yt0 yt1 yt2 ya0 ya1 : word) (F1 : bvmap 5 word) fc mc,
wa2 = (Z_to_bv 64 i) ->
wa3 = (Z_to_bv 64 boff) ->
boff = qoff + 4 * Z.of_nat (length done) -> kz = Z.of_nat (S (length rest)) -> (length done + 1 + length rest = n)%nat -> i = Z.of_nat (length done) ->
frm0 fc -> mem_inv bsegs mc -> munch [(IQ + qoff, IQ + qoff + NZ)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (IQ + qoff) (f32 done) -> rw_cells bsegs mc (IQ + boff) (f32 (x :: rest)) ->
evt bsegs (nb_l4_post zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 IQ qoff NZ CDB n mI)
(MS (mkR zra zsp zgp ztp yt0 yt1 yt2 (Z_to_bv 64 IQ) zs1 ya0 ya1 wa2 wa3 (Z_to_bv 64 CDB) (Z_to_bv 64 0) wa6 wa7 (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - IQ)) zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F1 (Z_to_bv 64 0xb4034) fc None mc (seg_rom bsegs)).
Proof.
intros IQ ON qoff NZ lim row n CDB CN CD mI zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 ENZ Q0 QN IQ0 Q4 QO4 OBQ OF ELIM EWa6 EWa7 OBC LCD RO C0 CNB R0 R1 rest.
induction rest as [|x' rest IH]; intros done x boff kz i wa2 wa3 yt0 yt1 yt2 ya0 ya1 F1 fc mc EWa2 EWa3 Hoff Hkz HN Hi FRM MI MU WM DONE X;
subst wa2 wa3 wa6 wa7;
pose proof OBQ as (OQ0 & OQ1 & _); pose proof OBC as (OC0 & OC1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
subst kz i.
- cbn [length] in HN. rewrite f32_cons, f32_nil in X.
lsp_rdB RO CDB CD row (Z.of_nat (length done)).
bato 0xb4048. astep. chk_merge OBQ 4.
bato 0xb4084. bnorm. chk_hint OBC. astep. bato 0xb408c. astep. chk_merge OBC 1. match goal with H : sh_cur _ |- _ => clear H end.
bato 0xb4098. astep. chk_merge OBQ 4.
bato 0xb40b8. bnorm. astep. cbn [length].
try sh_if.
bato 0xb40ec.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
unfold nb_l4_post. finish; [ exact DONE | ].
rewrite length_app. cbn [length]. lia.
- cbn [length] in HN, BX.
rewrite f32_cons in X. chunk_uncons X as X1.
lsp_rdB RO CDB CD row (Z.of_nat (length done)).
bato 0xb4048. astep. chk_merge OBQ 4.
bato 0xb4084. bnorm. chk_hint OBC. astep. bato 0xb408c. astep. chk_merge OBC 1. match goal with H : sh_cur _ |- _ => clear H end.
bato 0xb4098. astep. chk_merge OBQ 4.
bato 0xb40b8. bnorm. astep. cbn [length].
sh_if.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (Z.of_nat (S (S (length rest))) + -1) with (Z.of_nat (S (length rest))) by lia.
replace (IQ + boff + 4) with (IQ + (boff + 4)) in * by lia.
eapply (IH (done ++ [_]) x' (boff + 4) (Z.of_nat (S (length rest))) (Z.of_nat (length done) + 1)); try eassumption; try reflexivity.
all: try (f_equal; lia).
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.

Definition nb_l5_post (zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 : word) (IQ qoff NZ CDB : Z) (n : nat) (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' t1' t2' a0' a1' a2' a3' F' fc' m' (ws : list word),
ms' = MS (mkR zra zsp zgp ztp t0' t1' t2' (Z_to_bv 64 IQ) zs1 a0' a1' a2' a3' (Z_to_bv 64 CDB) (Z_to_bv 64 0) wa6 wa7 (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - IQ)) zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F' (Z_to_bv 64 0xb41dc) fc' None m' (seg_rom bsegs)
/\ munch [(IQ + qoff, IQ + qoff + NZ)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc' /\ rw_cells bsegs m' (IQ + qoff) (f32 ws) /\ length ws = n.

Lemma nb_l5 : forall (IQ ON qoff NZ lim row : Z) (n : nat) (CDB CN : Z) (CD : list byte) (mI : mem) (zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 : word),
NZ = 4 * Z.of_nat n -> 0 <= qoff -> qoff + NZ <= ON -> 0 < IQ -> IQ mod 4 = 0 -> qoff mod 4 = 0 -> aobj bsegs mI IQ ON -> offsh [(IQ + qoff, IQ + qoff + NZ)] ->
lim = qoff + NZ ->
wa6 = (Z_to_bv 64 row) ->
wa7 = (Z_to_bv 64 lim) ->
aobj bsegs mI CDB CN -> Z.of_nat (length CD) = CN -> (forall m', mem_inv bsegs m' -> u8ro bsegs m' CDB CD) -> 0 < CDB -> CN < 2^31 ->
0 <= row -> row + Z.of_nat n <= CN ->
forall (rest done : list word) (x : word) (boff kz i : Z) (wa2 wa3 yt0 yt1 yt2 ya0 ya1 : word) (F1 : bvmap 5 word) fc mc,
wa2 = (Z_to_bv 64 i) ->
wa3 = (Z_to_bv 64 boff) ->
boff = qoff + 4 * Z.of_nat (length done) -> kz = Z.of_nat (S (length rest)) -> (length done + 1 + length rest = n)%nat -> i = Z.of_nat (length done) ->
frm0 fc -> mem_inv bsegs mc -> munch [(IQ + qoff, IQ + qoff + NZ)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (IQ + qoff) (f32 done) -> rw_cells bsegs mc (IQ + boff) (f32 (x :: rest)) ->
evt bsegs (nb_l5_post zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 IQ qoff NZ CDB n mI)
(MS (mkR zra zsp zgp ztp yt0 yt1 yt2 (Z_to_bv 64 IQ) zs1 ya0 ya1 wa2 wa3 (Z_to_bv 64 CDB) (Z_to_bv 64 0) wa6 wa7 (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - IQ)) zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
F1 (Z_to_bv 64 0xb4124) fc None mc (seg_rom bsegs)).
Proof.
intros IQ ON qoff NZ lim row n CDB CN CD mI zra zsp zgp ztp zs1 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6 wa6 wa7 ENZ Q0 QN IQ0 Q4 QO4 OBQ OF ELIM EWa6 EWa7 OBC LCD RO C0 CNB R0 R1 rest.
induction rest as [|x' rest IH]; intros done x boff kz i wa2 wa3 yt0 yt1 yt2 ya0 ya1 F1 fc mc EWa2 EWa3 Hoff Hkz HN Hi FRM MI MU WM DONE X;
subst wa2 wa3 wa6 wa7;
pose proof OBQ as (OQ0 & OQ1 & _); pose proof OBC as (OC0 & OC1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
subst kz i.
- cbn [length] in HN. rewrite f32_cons, f32_nil in X.
lsp_rdB RO CDB CD row (Z.of_nat (length done)).
bato 0xb4138. astep. chk_merge OBQ 4.
bato 0xb4174. bnorm. chk_hint OBC. astep. bato 0xb417c. astep. chk_merge OBC 1. match goal with H : sh_cur _ |- _ => clear H end.
bato 0xb4188. astep. chk_merge OBQ 4.
bato 0xb41a8. bnorm. astep. cbn [length].
try sh_if.
bato 0xb41dc.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
unfold nb_l5_post. finish; [ exact DONE | ].
rewrite length_app. cbn [length]. lia.
- cbn [length] in HN, BX.
rewrite f32_cons in X. chunk_uncons X as X1.
lsp_rdB RO CDB CD row (Z.of_nat (length done)).
bato 0xb4138. astep. chk_merge OBQ 4.
bato 0xb4174. bnorm. chk_hint OBC. astep. bato 0xb417c. astep. chk_merge OBC 1. match goal with H : sh_cur _ |- _ => clear H end.
bato 0xb4188. astep. chk_merge OBQ 4.
bato 0xb41a8. bnorm. astep. cbn [length].
sh_if.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (Z.of_nat (S (S (length rest))) + -1) with (Z.of_nat (S (length rest))) by lia.
replace (IQ + boff + 4) with (IQ + (boff + 4)) in * by lia.
eapply (IH (done ++ [_]) x' (boff + 4) (Z.of_nat (S (length rest))) (Z.of_nat (length done) + 1)); try eassumption; try reflexivity.
all: try (f_equal; lia).
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.

Section W.
Context {ptr : Type}.
Variables (A D IQ usp lo : Z) (b : bits_st ptr).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Hypothesis REP : bits_rep bsegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis OBA : aobj bsegs m A BITS_SIZEOF.
Hypothesis OBD : aobj bsegs m D (sb_buf_size b).
Hypothesis OBQ : aobj bsegs m IQ 40.
Hypothesis TABS : lsp_tabs m.
Hypothesis Q4 : IQ mod 4 = 0.
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis QSH : hidp (IQ + 40 <= SH_LO \/ SH_HI <= IQ).
Hypothesis ATOP : IMG_TOP_B <= A.
Hypothesis QTOP : IMG_TOP_B <= IQ.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis DLO : D + sb_buf_size b <= lo.
Hypothesis QAP : hidp (IQ + 40 <= lo \/ usp <= IQ).
Hypothesis SEPQA : hidp (IQ + 40 <= A \/ A + BITS_SIZEOF <= IQ).
Hypothesis SEPQD : hidp (IQ + 40 <= D \/ D + sb_buf_size b <= IQ).
Hypothesis LO : lo <= usp - 128.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Local Notation W := [(A, A + 48); (IQ, IQ + 40); (usp + -128, usp)].

Lemma lsp_unquant_nb_walk : forall (old : list word) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
rw_cells bsegs m IQ (f32 old) -> length old = 10%nat ->
lib_consts m -> client_constsB m -> stk bsegs m lo usp -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (lsp_unquant_postA LspUnquantNb A D IQ usp lo b ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IQ) (Z_to_bv 64 10) (Z_to_bv 64 A) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_unquant_nb) fc None m (seg_rom bsegs)).
Proof.
intros old t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc X LX LC CC ST MI FRM.
pose proof TABS as (OBC0 & OBC1 & OBC2 & OBC3 & OBC4 & OBC5 & OBC6).
unfold A_cdbk_nb, A_cdbk_nb_low1, A_cdbk_nb_low2, A_cdbk_nb_high1, A_cdbk_nb_high2, A_high_lsp_cdbk, A_high_lsp_cdbk2 in *.
destruct cdbk_nb_at as (CD0 & LCD0 & RO0).
destruct cdbk_nb_low1_at as (CD1 & LCD1 & RO1).
destruct cdbk_nb_low2_at as (CD2 & LCD2 & RO2).
destruct cdbk_nb_high1_at as (CD3 & LCD3 & RO3).
destruct cdbk_nb_high2_at as (CD4 & LCD4 & RO4).
unfold A_cdbk_nb, A_cdbk_nb_low1, A_cdbk_nb_low2, A_cdbk_nb_high1, A_cdbk_nb_high2, A_high_lsp_cdbk, A_high_lsp_cdbk2 in *.
pose proof (lib_const m _ _ LC (ltac:(lc_in) : In (GOT_f41c8, LC_GOT_f41c8) LIB_TABLES)) as GC0.
pose proof (lib_const m _ _ LC (ltac:(lc_in) : In (GOT_f41d0, LC_GOT_f41d0) LIB_TABLES)) as GC1.
pose proof (lib_const m _ _ LC (ltac:(lc_in) : In (GOT_f41d8, LC_GOT_f41d8) LIB_TABLES)) as GC2.
pose proof (lib_const m _ _ LC (ltac:(lc_in) : In (GOT_f41e0, LC_GOT_f41e0) LIB_TABLES)) as GC3.
pose proof (lib_const m _ _ LC (ltac:(lc_in) : In (GOT_f41e8, LC_GOT_f41e8) LIB_TABLES)) as GC4.
unfold GOT_f41c8, LC_GOT_f41c8, GOT_f41d0, LC_GOT_f41d0, GOT_f41d8, LC_GOT_f41d8, GOT_f41e0, LC_GOT_f41e0, GOT_f41e8, LC_GOT_f41e8 in *. clear LC.
pose proof CC as (G1 & G2 & G3 & G4).
unfold A_lsp_unquant_nb, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof REP as ((rj0 & Lrj0 & OBJ) & (bs0 & DAT & Hbs0) & SIDE0). unfold bits_cells in OBJ.
assert (Lbs0 : Z.of_nat (length bs0) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs0, zlength_map_unsigned in OK'. lia. }
pose proof OBA as (OA0 & OA1 & _). pose proof OBD as (OD0 & OD1 & _). pose proof OBQ as (OQ0 & OQ1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP_B in ATOP, QTOP.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W).
{ pose proof (ASH : _ \/ _) as Y1. pose proof (QSH : _ \/ _) as Y2. clear - Y1 Y2 LOS LO. cbn. unfold SH_LO, SH_HI in *. lia. }
assert (OFQ : IQ + 40 <= SH_LO \/ SH_HI <= IQ) by (destruct OF as (_ & O2 & _); exact O2).
pose proof (QAP : _ \/ _) as QAP'. pose proof (SEPQA : _ \/ _) as SEPQA'. pose proof (SEPQD : _ \/ _) as SEPQD'. hide_disj.
destruct old as [|q0 qrest]; [cbn [length] in LX; lia|]. cbn [length] in LX.
carve_frame 64%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
bato 0xb3c8c. rewrite (land3_al IQ Q4). bdec.
replace IQ with (IQ + 0) in X at 1 by lia.
vloop_factsB OBQ MU OF IQ 40 0 40.
assert (OFW : offsh [(IQ + 0, IQ + 0 + 40)]) by (unfold hid in OFQ; clear - OFQ; cbn; lia).
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [ eapply (nb_l0 IQ 40 0 40 10%nat mc) with (rest := qrest) (done := []) (x := q0) (boff := 0) (kz := 10) (i := 0)
| clear MU0 WM0 OBQc D0 OFW X LX FRM; post_call segs mc ]
end.
1: reflexivity.
1: lia.
1: lia.
1: lia.
1: exact Q4.
1: reflexivity.
1: exact OBQc.
1: exact OFW.
1: (f_equal; lia).
1: (f_equal; lia).
1: (f_equal; lia).
1: (f_equal; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: eassumption.
1: eassumption.
1: exact MU0.
1: exact WM0.
1: exact D0.
1: exact X.
rewrite ?Z.add_0_r in *. vloop_names IQ X LX FRM.

bato 0xb3d00. rebase_bits A D b rj0 bs0.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -64) lo b 6 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO DLO).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk bsegs _ lo _ |- _ => rename H into ST end.
change (snd (speex_bits_unpack_unsigned b 6)) with (ub b 6) in *. change (fst (speex_bits_unpack_unsigned b 6)) with (uv b 6) in *.
pose proof (ub_ok b 6 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 6) with 64 in V1R.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep bsegs _ A D (ub b 6) |- _ => destruct H as ((rj1 & Lrj1 & OBJ) & (bs1 & DAT & Hbs1) & SIDE1); unfold bits_cells in OBJ end.
assert (Lbs1 : Z.of_nat (length bs1) = sb_buf_size b).
{ pose proof OK1 as OK'. unfold bits_ok in OK'. rewrite Hbs1, zlength_map_unsigned in OK'. lia. }
bato 0xb3d3c. bnorm. bdec.
lazymatch type of X with rw_cells _ _ _ (f32 ?l) => rename l into ws0 end.
destruct ws0 as [|w0 wr0]; [cbn [length] in LX; lia|]. cbn [length] in LX.
replace IQ with (IQ + 0) in X at 1 by lia.
vloop_factsB OBQ MU OF IQ 40 0 40. vloop_cb OBC0 MU OF 149632 640.
assert (OFW : offsh [(IQ + 0, IQ + 0 + 40)]) by (unfold hid in OFQ; clear - OFQ; cbn; lia).
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [ eapply (nb_l1 IQ 40 0 40 (uv b 6 * 10) 10%nat 149632 640 CD0 mc) with (rest := wr0) (done := []) (x := w0) (boff := 0) (kz := 10) (i := 0)
| clear MU0 WM0 OBQc OBCc D0 OFW X LX FRM; post_call segs mc ]
end.
1: reflexivity.
1: lia.
1: lia.
1: lia.
1: exact Q4.
1: reflexivity.
1: exact OBQc.
1: exact OFW.
1: (f_equal; lia).
1: exact OBCc.
1: (rewrite LCD0; reflexivity).
1: exact RO0.
1: lia.
1: lia.
1: lia.
1: lia.
1: (f_equal; lia).
1: (f_equal; lia).
1: (f_equal; lia).
1: (f_equal; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: eassumption.
1: eassumption.
1: exact MU0.
1: exact WM0.
1: exact D0.
1: exact X.
rewrite ?Z.add_0_r in *. vloop_names IQ X LX FRM.

bato 0xb3e10. rebase_bits A D (ub b 6) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -64) lo (ub b 6) 6 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK1 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ1; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk bsegs _ lo _ |- _ => rename H into ST end.
change (snd (speex_bits_unpack_unsigned (ub b 6) 6)) with (ub (ub b 6) 6) in *. change (fst (speex_bits_unpack_unsigned (ub b 6) 6)) with (uv (ub b 6) 6) in *.
pose proof (ub_ok (ub b 6) 6 OK1 ltac:(lia)) as (OK2 & SZ2 & V2R). change (2 ^ 6) with 64 in V2R. rewrite SZ1 in SZ2.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep bsegs _ A D (ub (ub b 6) 6) |- _ => destruct H as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2); unfold bits_cells in OBJ end.
assert (Lbs2 : Z.of_nat (length bs2) = sb_buf_size b).
{ pose proof OK2 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }
bato 0xb3e4c. bnorm. bdec.
lazymatch type of X with rw_cells _ _ _ (f32 ?l) => rename l into ws1 end.
destruct ws1 as [|u1_0 [|u1_1 [|u1_2 [|u1_3 [|u1_4 [|u1_5 [|u1_6 [|u1_7 [|u1_8 [|u1_9 [|? ?]]]]]]]]]]]; try (cbn [length] in LX; lia). clear LX.
chunk_split_f32 X at 5%nat as XL. rename X into XH.
replace IQ with (IQ + 0) in XL at 1 by lia.
vloop_factsB OBQ MU OF IQ 40 0 20. vloop_cb OBC1 MU OF 150432 320.
assert (OFW : offsh [(IQ + 0, IQ + 0 + 20)]) by (unfold hid in OFQ; clear - OFQ; cbn; lia).
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [ eapply (nb_l2 IQ 40 0 20 20 (uv (ub b 6) 6 * 4 + uv (ub b 6) 6) 5%nat 150432 320 CD1 mc) with (rest := [u1_1; u1_2; u1_3; u1_4]) (done := []) (x := u1_0) (boff := 0) (kz := 5) (i := 0)
| clear MU0 WM0 OBQc OBCc D0 OFW XL  FRM; post_call segs mc ]
end.
1: reflexivity.
1: lia.
1: lia.
1: lia.
1: exact Q4.
1: reflexivity.
1: exact OBQc.
1: exact OFW.
1: reflexivity.
1: (f_equal; lia).
1: (f_equal; lia).
1: exact OBCc.
1: (rewrite LCD1; reflexivity).
1: exact RO1.
1: lia.
1: lia.
1: lia.
1: lia.
1: (f_equal; lia).
1: (f_equal; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: eassumption.
1: eassumption.
1: exact MU0.
1: exact WM0.
1: exact D0.
1: exact XL.
rewrite ?Z.add_0_r in *.
vloop_names IQ XL LXL FRM.

bato 0xb3f0c. rebase_bits A D (ub (ub b 6) 6) rj2 bs2. rewrite <- SZ2 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -64) lo (ub (ub b 6) 6) 6 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK2 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ2; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk bsegs _ lo _ |- _ => rename H into ST end.
change (snd (speex_bits_unpack_unsigned (ub (ub b 6) 6) 6)) with (ub (ub (ub b 6) 6) 6) in *. change (fst (speex_bits_unpack_unsigned (ub (ub b 6) 6) 6)) with (uv (ub (ub b 6) 6) 6) in *.
pose proof (ub_ok (ub (ub b 6) 6) 6 OK2 ltac:(lia)) as (OK3 & SZ3 & V3R). change (2 ^ 6) with 64 in V3R. rewrite SZ2 in SZ3.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep bsegs _ A D (ub (ub (ub b 6) 6) 6) |- _ => destruct H as ((rj3 & Lrj3 & OBJ) & (bs3 & DAT & Hbs3) & SIDE3); unfold bits_cells in OBJ end.
assert (Lbs3 : Z.of_nat (length bs3) = sb_buf_size b).
{ pose proof OK3 as OK'. unfold bits_ok in OK'. rewrite Hbs3, zlength_map_unsigned in OK'. lia. }
bato 0xb3f44. bnorm. bdec.
lazymatch type of XL with rw_cells _ _ _ (f32 ?l) => rename l into ws2 end.
destruct ws2 as [|u2_0 [|u2_1 [|u2_2 [|u2_3 [|u2_4 [|? ?]]]]]]; try (cbn [length] in LXL; lia). clear LXL.
replace IQ with (IQ + 0) in XL at 1 by lia.
vloop_factsB OBQ MU OF IQ 40 0 20. vloop_cb OBC2 MU OF 150816 320.
assert (OFW : offsh [(IQ + 0, IQ + 0 + 20)]) by (unfold hid in OFQ; clear - OFQ; cbn; lia).
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [ eapply (nb_l3 IQ 40 0 20 20 (uv (ub (ub b 6) 6) 6 * 4 + uv (ub (ub b 6) 6) 6) 5%nat 150816 320 CD2 mc) with (rest := [u2_1; u2_2; u2_3; u2_4]) (done := []) (x := u2_0) (boff := 0) (kz := 5) (i := 0)
| clear MU0 WM0 OBQc OBCc D0 OFW XL  FRM; post_call segs mc ]
end.
1: reflexivity.
1: lia.
1: lia.
1: lia.
1: exact Q4.
1: reflexivity.
1: exact OBQc.
1: exact OFW.
1: reflexivity.
1: (f_equal; lia).
1: (f_equal; lia).
1: exact OBCc.
1: (rewrite LCD2; reflexivity).
1: exact RO2.
1: lia.
1: lia.
1: lia.
1: lia.
1: (f_equal; lia).
1: (f_equal; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: eassumption.
1: eassumption.
1: exact MU0.
1: exact WM0.
1: exact D0.
1: exact XL.
rewrite ?Z.add_0_r in *.
vloop_names IQ XL LXL FRM.

bato 0xb4004. rebase_bits A D (ub (ub (ub b 6) 6) 6) rj3 bs3. rewrite <- SZ3 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -64) lo (ub (ub (ub b 6) 6) 6) 6 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK3 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ3; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk bsegs _ lo _ |- _ => rename H into ST end.
change (snd (speex_bits_unpack_unsigned (ub (ub (ub b 6) 6) 6) 6)) with (ub (ub (ub (ub b 6) 6) 6) 6) in *. change (fst (speex_bits_unpack_unsigned (ub (ub (ub b 6) 6) 6) 6)) with (uv (ub (ub (ub b 6) 6) 6) 6) in *.
pose proof (ub_ok (ub (ub (ub b 6) 6) 6) 6 OK3 ltac:(lia)) as (OK4 & SZ4 & V4R). change (2 ^ 6) with 64 in V4R. rewrite SZ3 in SZ4.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep bsegs _ A D (ub (ub (ub (ub b 6) 6) 6) 6) |- _ => destruct H as ((rj4 & Lrj4 & OBJ) & (bs4 & DAT & Hbs4) & SIDE4); unfold bits_cells in OBJ end.
assert (Lbs4 : Z.of_nat (length bs4) = sb_buf_size b).
{ pose proof OK4 as OK'. unfold bits_ok in OK'. rewrite Hbs4, zlength_map_unsigned in OK'. lia. }
bato 0xb4034. bnorm. bdec.
vloop_factsB OBQ MU OF IQ 40 20 20. vloop_cb OBC3 MU OF 151200 320.
assert (OFW : offsh [(IQ + 20, IQ + 20 + 20)]) by (unfold hid in OFQ; clear - OFQ; cbn; lia).
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [ eapply (nb_l4 IQ 40 20 20 40 (uv (ub (ub (ub b 6) 6) 6) 6 * 4 + uv (ub (ub (ub b 6) 6) 6) 6) 5%nat 151200 320 CD3 mc) with (rest := [u1_6; u1_7; u1_8; u1_9]) (done := []) (x := u1_5) (boff := 20) (kz := 5) (i := 0)
| clear MU0 WM0 OBQc OBCc D0 OFW XH  FRM; post_call segs mc ]
end.
1: reflexivity.
1: lia.
1: lia.
1: lia.
1: exact Q4.
1: reflexivity.
1: exact OBQc.
1: exact OFW.
1: reflexivity.
1: (f_equal; lia).
1: (f_equal; lia).
1: exact OBCc.
1: (rewrite LCD3; reflexivity).
1: exact RO3.
1: lia.
1: lia.
1: lia.
1: lia.
1: (f_equal; lia).
1: (f_equal; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: eassumption.
1: eassumption.
1: exact MU0.
1: exact WM0.
1: exact D0.
1: exact XH.
vloop_names (IQ + 20) XH LXH FRM.

bato 0xb40f4. rebase_bits A D (ub (ub (ub (ub b 6) 6) 6) 6) rj4 bs4. rewrite <- SZ4 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -64) lo (ub (ub (ub (ub b 6) 6) 6) 6) 6 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK4 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ4; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk bsegs _ lo _ |- _ => rename H into ST end.
change (snd (speex_bits_unpack_unsigned (ub (ub (ub (ub b 6) 6) 6) 6) 6)) with (ub (ub (ub (ub (ub b 6) 6) 6) 6) 6) in *. change (fst (speex_bits_unpack_unsigned (ub (ub (ub (ub b 6) 6) 6) 6) 6)) with (uv (ub (ub (ub (ub b 6) 6) 6) 6) 6) in *.
pose proof (ub_ok (ub (ub (ub (ub b 6) 6) 6) 6) 6 OK4 ltac:(lia)) as (OK5 & SZ5 & V5R). change (2 ^ 6) with 64 in V5R. rewrite SZ4 in SZ5.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep bsegs _ A D (ub (ub (ub (ub (ub b 6) 6) 6) 6) 6) |- _ => destruct H as ((rj5 & Lrj5 & OBJ) & (bs5 & DAT & Hbs5) & SIDE5); unfold bits_cells in OBJ end.
assert (Lbs5 : Z.of_nat (length bs5) = sb_buf_size b).
{ pose proof OK5 as OK'. unfold bits_ok in OK'. rewrite Hbs5, zlength_map_unsigned in OK'. lia. }
bato 0xb4124. bnorm. bdec.
lazymatch type of XH with rw_cells _ _ _ (f32 ?l) => rename l into ws4 end.
destruct ws4 as [|u4_0 [|u4_1 [|u4_2 [|u4_3 [|u4_4 [|? ?]]]]]]; try (cbn [length] in LXH; lia). clear LXH.
vloop_factsB OBQ MU OF IQ 40 20 20. vloop_cb OBC4 MU OF 151584 320.
assert (OFW : offsh [(IQ + 20, IQ + 20 + 20)]) by (unfold hid in OFQ; clear - OFQ; cbn; lia).
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [ eapply (nb_l5 IQ 40 20 20 40 (uv (ub (ub (ub (ub b 6) 6) 6) 6) 6 * 4 + uv (ub (ub (ub (ub b 6) 6) 6) 6) 6) 5%nat 151584 320 CD4 mc) with (rest := [u4_1; u4_2; u4_3; u4_4]) (done := []) (x := u4_0) (boff := 20) (kz := 5) (i := 0)
| clear MU0 WM0 OBQc OBCc D0 OFW XH  FRM; post_call segs mc ]
end.
1: reflexivity.
1: lia.
1: lia.
1: lia.
1: exact Q4.
1: reflexivity.
1: exact OBQc.
1: exact OFW.
1: reflexivity.
1: (f_equal; lia).
1: (f_equal; lia).
1: exact OBCc.
1: (rewrite LCD4; reflexivity).
1: exact RO4.
1: lia.
1: lia.
1: lia.
1: lia.
1: (f_equal; lia).
1: (f_equal; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: (cbn [length]; lia).
1: eassumption.
1: eassumption.
1: exact MU0.
1: exact WM0.
1: exact D0.
1: exact XH.
vloop_names (IQ + 20) XH LXH FRM.

bato 0xb41fc. release_frame FR ST usp. astep. astep.
lazymatch type of XL with rw_cells _ _ _ (f32 ?l) => rename l into wXL end.
destruct wXL as [|l0 [|l1 [|l2 [|l3 [|l4 [|? ?]]]]]]; try (cbn [length] in LXL; lia).
lazymatch type of XH with rw_cells _ _ _ (f32 ?l) => rename l into wXH end.
destruct wXH as [|h0 [|h1 [|h2 [|h3 [|h4 [|? ?]]]]]]; try (cbn [length] in LXH; lia).
chunk_cat XL XH. rewrite <- f32_app in XL. cbn [app] in XL. rename XL into X.
unfold lsp_unquant_postA, LSPQ_DEPTH, BITS_SIZEOF, lsp_order, lsp_bits. change (4 * 10) with 40. change (Z.to_nat 10) with 10%nat.
finish; first [ exact X | exact LX | reflexivity | exact OK5 | idtac ].
split; [exists rj5; split; [exact Lrj5| exact OBJ]| split; [exists bs5; split; [exact DAT| exact Hbs5]| exact SIDE5]].
Qed.
End W.

Lemma lsp_unquant_nb_stmt : forall ptr, @lsp_unquant_stmtA ptr LspUnquantNb.
Proof.
intros ptr A D IQ usp lo b old ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
REP OK OBA OBD OBQ TABS LC CC X LX Q4 ASH QSH ATOP QTOP ALO DLO QAP SEPQA SEPQD ST LO LOS SPH MI FRM.
cbn [lsp_order lsp_entryA] in *. change (4 * 10) with 40 in *. change (Z.to_nat 10) with 10%nat in *. unfold LSPQ_DEPTH in LO.
eapply lsp_unquant_nb_walk; eassumption.
Qed.
