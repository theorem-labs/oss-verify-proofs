From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Qfw3 Q5Rg Qc3B QCcH Qsw7 QJjn QRUw QBGG QmtA QoBT Q7T7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM Uh14 UmtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes Qfw3.Mq2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg Qc3B.
Import UEQM.
Import QCcH Qsw7 QJjn QRUw.
Import QBGG.
Import Uh14 UmtA QoBT Q7T7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Ltac runc := do 40 (try (lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => ub_closed c; ub_if_lit
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?k) _ _ _ _) => ub_closed k; bstep end)).

Lemma w_of_u : forall (a : word) v, bv_unsigned a = v -> a = Z_to_bv 64 v.
Proof.
intros a v H. apply bv_eq. rewrite Z_to_bv_unsigned, <- H. unfold bv_wrap.
rewrite Z.mod_small; [reflexivity | apply bv_unsigned_in_range].
Qed.

Ltac vmax_ok := lazymatch goal with |- bv_unsigned ?x <= _ =>
let R := fresh "R" in pose proof (bv_unsigned_in_range 64 x) as R; unfold bv_modulus in R;
change (2 ^ Z.of_N 64) with (2 ^ 64) in R; generalize dependent (bv_unsigned x); intros; lia end.

Lemma cii_u8_U_spec : cii_stmt rsegs QmtA.CII_U8_U 1 0 255.
Proof.
unfold cii_stmt, QmtA.CII_U8_U, fdp_pre. intros until data. intros (A0 & FDP & SRC & LEN & Hptr & ST & LO & HP & HD & MI) A1 A2. subst a0.
apply w_of_u in A1. apply w_of_u in A2. subst a1 a2.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (munch_refl (fdp_W (bv_unsigned sp) P) m) as MU. unfold fdp_W in MU.
pose proof (wmono_refl rsegs m) as WM.
runc.
destruct (Z.eq_dec rem 0) as [R0 | R1].
- rewrite R0 in *. if_truex. runc.
finish.
all: try lia. all: try vmax_ok.
all: rewrite Z.max_r by lia; assumption.
- if_falsex. bstep. step. if_falsex.
destruct (nth_error data (Z.to_nat (rem - 1))) as [b1|] eqn:Hb1; [| exfalso; apply nth_error_None in Hb1; lia].
pose proof (bv_unsigned_in_range 8 b1) as BR1. unfold bv_modulus in BR1. cbn in BR1.
lazymatch goal with H : bytes_at rsegs ?mx ptr data |- _ => pose proof (u8ro_read rsegs mx ptr data (rem - 1) b1 _ H Hb1 ltac:(lia) eq_refl) as RD1 end.
replace (ptr + (rem - 1)) with (ptr + (rem + -1)) in RD1 by lia.
bstep. step. runc.
finish.
all: try lia. all: try vmax_ok.
all: rewrite Z.max_l by lia; replace (rem - 1) with (rem + -1) by lia; assumption.
Qed.

Ltac fdp_rd ptr rem data k :=
let b := fresh "b" in let Hb := fresh "Hb" in let BR := fresh "BR" in let RD := fresh "RD" in
destruct (nth_error data (Z.to_nat (rem - 1 - k))) as [b|] eqn:Hb; [| exfalso; apply nth_error_None in Hb; lia];
pose proof (bv_unsigned_in_range 8 b) as BR; unfold bv_modulus in BR; cbn in BR;
lazymatch goal with H : bytes_at rsegs ?mx ptr data |- _ => pose proof (u8ro_read rsegs mx ptr data (rem - 1 - k) b _ H Hb ltac:(lia) eq_refl) as RD end;
let e := eval cbv in (- (k + 1)) in replace (ptr + (rem - 1 - k)) with (ptr + (rem + e)) in RD by lia.

Ltac fdp_close sp P :=
lazymatch goal with H : rw_cells rsegs ?mx (bv_unsigned sp + -16) _, H' : stk rsegs ?mx _ _ |- _ => release_frame H H' (bv_unsigned sp) end;
finish; try lia; try vmax_ok;
try (lazymatch goal with H : rw_cells rsegs ?mm P [C8 ?p; C8 (Z_to_bv 64 ?y)] |- rw_cells rsegs ?mm P [C8 ?p; C8 (Z_to_bv 64 ?y')] =>
replace y' with y by lia; exact H end).

Ltac u64_it sp P ptr rem data k :=
let R := fresh "R" in
destruct (Z.eq_dec rem k) as [R|R];
[ solve [rewrite R in *; runc; fdp_close sp P]
| if_falsex; bstep; step; if_falsex; fdp_rd ptr rem data k; runc ].

Ltac int_it sp P ptr rem data k :=
let R := fresh "R" in
destruct (Z.eq_dec rem k) as [R|R];
[ solve [rewrite R in *; runc; fdp_close sp P]
| if_falsex; runc; step; if_falsex; fdp_rd ptr rem data k; runc ].

Lemma cii_int_U_spec : cii_stmt rsegs QmtA.CII_INT_U 4 (2^64 - 2^31) (2^31 - 1).
Proof.
unfold cii_stmt, QmtA.CII_INT_U, fdp_pre. intros until data. intros (A0 & FDP & SRC & LEN & Hptr & ST & LO & HP & HD & MI) A1 A2. subst a0.
apply w_of_u in A1. apply w_of_u in A2. subst a1 a2.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (munch_refl (fdp_W (bv_unsigned sp) P) m) as MU. unfold fdp_W in MU.
pose proof (wmono_refl rsegs m) as WM.
carve_frame 16%nat ST.
runc.
int_it sp P ptr rem data 0. int_it sp P ptr rem data 1. int_it sp P ptr rem data 2. int_it sp P ptr rem data 3.
fdp_close sp P.
Qed.

Lemma cii_u64_U_spec : cii_stmt rsegs QmtA.CII_U64_U 8 0 (2^64 - 1).
Proof.
unfold cii_stmt, QmtA.CII_U64_U, fdp_pre. intros until data. intros (A0 & FDP & SRC & LEN & Hptr & ST & LO & HP & HD & MI) A1 A2. subst a0.
apply w_of_u in A1. apply w_of_u in A2. subst a1 a2.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (munch_refl (fdp_W (bv_unsigned sp) P) m) as MU. unfold fdp_W in MU.
pose proof (wmono_refl rsegs m) as WM.
carve_frame 16%nat ST.
runc.
u64_it sp P ptr rem data 0. u64_it sp P ptr rem data 1. u64_it sp P ptr rem data 2. u64_it sp P ptr rem data 3.
u64_it sp P ptr rem data 4. u64_it sp P ptr rem data 5. u64_it sp P ptr rem data 6. u64_it sp P ptr rem data 7.
fdp_close sp P.
Qed.

Lemma cii_i64_U_spec : cii_stmt rsegs QmtA.CII_I64_U 8 (2^63) (2^63 - 1).
Proof.
unfold cii_stmt, QmtA.CII_I64_U, fdp_pre. intros until data. intros (A0 & FDP & SRC & LEN & Hptr & ST & LO & HP & HD & MI) A1 A2. subst a0.
apply w_of_u in A1. apply w_of_u in A2. subst a1 a2.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (munch_refl (fdp_W (bv_unsigned sp) P) m) as MU. unfold fdp_W in MU.
pose proof (wmono_refl rsegs m) as WM.
carve_frame 16%nat ST.
runc.
u64_it sp P ptr rem data 0. u64_it sp P ptr rem data 1. u64_it sp P ptr rem data 2. u64_it sp P ptr rem data 3.
u64_it sp P ptr rem data 4. u64_it sp P ptr rem data 5. u64_it sp P ptr rem data 6. u64_it sp P ptr rem data 7.
fdp_close sp P.
Qed.
