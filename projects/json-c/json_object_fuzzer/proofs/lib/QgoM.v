(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Qfw3_c1 Q5Rg Lib.SepCache QRjH QHnV QCcH QfLs Qsw7 QJjn QgoP Q7UD Qhd4 Qwm6 QlKV QsKa Qw5U QpNt Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes Qfw3_c1.Mq2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QRjH.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import QgoP.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq8.

Import QlKV.Mq0 Qw5U.Mq1.

Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Section Cells.
Variable segs : list Segment.

#[using="Type"] Lemma rw_cells_pair : forall m A x y,
rw_cells segs m A [C1 x] -> rw_cells segs m (A + 1) [C1 y] -> rw_cells segs m A [C1 x; C1 y].
Proof. intros m A x y H1 H2. apply (proj2 (rw_cells_app segs m A [C1 x] [C1 y])). split; [exact H1 | exact H2]. Qed.

#[using="Type"] Lemma rw_cells_unpair : forall m A x y,
rw_cells segs m A [C1 x; C1 y] -> rw_cells segs m A [C1 x] /\ rw_cells segs m (A + 1) [C1 y].
Proof. intros m A x y H. apply (proj1 (rw_cells_app segs m A [C1 x] [C1 y])) in H. exact H. Qed.

#[using="Type"] Lemma rw_cells_CB_snoc : forall m A n s b,
rw_cells segs m A [CB n s] -> rw_cells segs m (A + Z.of_nat n) [C1 b] -> rw_cells segs m A [CB (S n) (s ++ [b])].
Proof.
intros m A n s b H1 H2.
assert (L : length s = n) by (destruct H1 as [[[Hwf _] _] _]; exact Hwf).
assert (H : rw_cells segs m A ([CB n s] ++ [C1 b])).
{ apply (proj2 (rw_cells_app segs m A [CB n s] [C1 b])). cbn [cells_size csize]. rewrite Nat.add_0_r. split; [exact H1 | exact H2]. }
eapply rw_cells_recast; [exact H | cbn; rewrite length_app; cbn; lia | cbn; rewrite app_nil_r; reflexivity | cbn; lia].
Qed.

#[using="Type"] Lemma rw_cells_CB_head : forall m A n b bs,
rw_cells segs m A [CB (S n) (b :: bs)] -> rw_cells segs m A [C1 b] /\ rw_cells segs m (A + 1) [CB n bs].
Proof.
intros m A n b bs H.
destruct (rw_cells_CB_cut segs m A (S n) (b :: bs) 1 H ltac:(lia)) as [H1 H2].
cbn [firstn skipn] in H1, H2. change (Z.of_nat 1) with 1 in H2. replace (S n - 1)%nat with n in H2 by lia.
split; [| exact H2].
eapply rw_cells_recast; [exact H1 | cbn; split; exact I | reflexivity | reflexivity].
Qed.

#[using="Type"] Lemma obj_join : forall m S n (szb j : byte) s rest,
0 <= n <= 21 -> bv_unsigned szb = 2 * n ->
rw_cells segs m S [C1 szb] ->
rw_cells segs m (S + 1) [CB (Z.to_nat n) s] ->
rw_cells segs m (S + n + 1) [C1 b0; C1 j] ->
rw_cells segs m (S + n + 3) [CB (Z.to_nat (21 - n)) rest] ->
rw_cells segs m S [C1 (Z_to_bv 8 (2 * n)); CB 23 (s ++ b0 :: j :: rest)].
Proof.
intros m S n szb j s rest Hn Hsz SZ DATA WIN REST.
assert (Ls : length s = Z.to_nat n) by (destruct DATA as [[[Hwf _] _] _]; exact Hwf).
assert (Lr : length rest = Z.to_nat (21 - n)) by (destruct REST as [[[Hwf _] _] _]; exact Hwf).
pose proof (rw_cells_bound segs _ _ _ REST) as B. cbn [cells_size csize Nat.add] in B.
assert (H : rw_cells segs m S ([C1 szb] ++ ([CB (Z.to_nat n) s] ++ ([C1 b0; C1 j] ++ [CB (Z.to_nat (21 - n)) rest])))).
{ apply (proj2 (rw_cells_app segs m S _ _)). split; [exact SZ|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
apply (proj2 (rw_cells_app segs m _ _ _)). split; [exact DATA|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. replace (S + 1 + n) with (S + n + 1) by lia.
apply (proj2 (rw_cells_app segs m _ _ _)). split; [exact WIN|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 2) with 2.
replace (S + n + 1 + 2) with (S + n + 3) by lia. exact REST. }
eapply rw_cells_recast; [exact H | | |].
- cbn [cells_wf cell_wf csize length]. rewrite length_app. cbn [length].
repeat split; try exact I; try reflexivity. lia.
- cbn. rewrite <- app_assoc. cbn. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 (2 * n)) with ((2 * n) mod 2 ^ 8).
pose proof (bv_unsigned_in_range 8 szb) as R. unfold bv_modulus in R. cbn in R. rewrite Z.mod_small; lia.
- cbn. lia.
Qed.
End Cells.

Lemma first_nul_split : forall (pre post : list byte),
exists str rest, pre ++ b0 :: post = str ++ b0 :: rest /\ ~ In b0 str /\ (length str <= length pre)%nat.
Proof.
induction pre as [|b pre IH]; intros post.
- exists [], post. split; [reflexivity|]. split; [intros H; exact H | cbn; lia].
- destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE].
+ exists [], (pre ++ b0 :: post). split; [| split; [intros H; exact H | cbn; lia]].
change (b :: (pre ++ b0 :: post) = b0 :: (pre ++ b0 :: post)). f_equal. apply bv_eq. rewrite E. reflexivity.
+ destruct (IH post) as (str & rest & E2 & Hn & Hl). exists (b :: str), rest.
split; [change (b :: (pre ++ b0 :: post) = b :: (str ++ b0 :: rest)); rewrite E2; reflexivity|].
split; [| cbn; lia]. intros [H|H]; [| exact (Hn H)]. apply NE. rewrite H. reflexivity.
Qed.

Lemma lor7_eq23 : forall n, 16 <= n <= 23 -> Z.lor n 7 = 23.
Proof.
intros n Hn.
assert (H : forallb (fun k => Z.lor (16 + Z.of_nat k) 7 =? 23) (seq 0 8) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H (Z.to_nat (n - 16)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
apply Z.eqb_eq in H. replace (16 + (n - 16)) with n in H by lia. exact H.
Qed.
Lemma lor7_bound : forall n, 0 <= n <= 15 -> 7 <= Z.lor n 7 <= 15.
Proof.
intros n Hn.
assert (H : forallb (fun k => andb (7 <=? Z.lor (Z.of_nat k) 7) (Z.lor (Z.of_nat k) 7 <=? 15)) (seq 0 16) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H (Z.to_nat n) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
apply andb_true_iff in H as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.

Tactic Notation "call_pushb" constr(Sv) constr(nv) constr(lov) constr(szbv) constr(xv) constr(yv) :=
lazymatch goal with
| |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) => name_sp sp k
| |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => name_sp sp k
end;
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [eapply pushb_spec with (S := Sv) (n := nv) (lo := lov) (szb := szbv) (x := xv) (y := yv)
| unfold pushb_post, pushb_W; post_call segs mm] end;
unname_sp.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section ACrls.
Hypothesis OBL_AMEMSET_U : amemset_spec_U.

Lemma crls_doneA :
forall (sp ra s0 s1 s2 s3 s4 s5 s6 s7 : word)
(x1 gp tp t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
(S P ptr rem lo maxlen n k : Z) (szb j : byte) (s rest data fj : list byte),
rw_cells asegs m (bv_unsigned sp + -80) [CB 8 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs m lo (bv_unsigned sp + -80) -> lo <= bv_unsigned sp - 80 ->
bv_unsigned szb = 2 * n -> 0 <= n <= maxlen -> maxlen <= 20 ->
rw_cells asegs m S [C1 szb] ->
rw_cells asegs m (S + 1) [CB (Z.to_nat n) s] ->
rw_cells asegs m (S + n + 1) [C1 b0; C1 j] ->
rw_cells asegs m (S + n + 3) [CB (Z.to_nat (21 - n)) rest] ->
0 <= k <= rem ->
rw_cells asegs m P [C8 (Z_to_bv 64 (ptr + k)); C8 (Z_to_bv 64 (rem - k))] ->
bytes_at asegs m ptr data ->
munch (crls_WA (bv_unsigned sp) S P lo) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
ro_cells asegs m (S / 8 + 2147450880) [C1 (Z_to_bv 8 0)] -> 0 <= S < 2^47 ->
evt asegs (crls_postA maxlen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S P ptr rem lo data m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 S) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 2147450880) x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x92408) fc None m (seg_rom asegs)).
Proof.
intros until fj. intros FR ST LO Hsz Hn Hmax SZ DATA WIN REST Hk FDP SRC MU WM MI SH0 SR47.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bv_unsigned_in_range 8 szb) as SR. unfold bv_modulus in SR. cbn in SR.
unfold crls_WA in MU.
asan_chk0.
step. change (zxb szb) with (Z_to_bv 64 (bv_unsigned szb)). rewrite Hsz.
step. rewrite (unsigned_lit (2 * n)) by lia. rewrite land1_even.
step. if_false.
step. rewrite (unsigned_lit (2 * n)) by lia. rewrite shiftr1_double by lia.
step. rewrite (unsigned_lit n) by lia.
step.
assert (TAIL : forall (xa1 : word),
evt asegs (crls_postA maxlen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S P ptr rem lo data m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 S) x9 (Z_to_bv 64 (2 * n)) xa1 (Z_to_bv 64 23) a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 2147450880) x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x92438) fc None m (seg_rom asegs))).
{ intros xa1.
step. step. step. if_falsex.
step. step. if_false.
step.
do 11 step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -80) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk asegs ?mx lo _ |- _ => rename H into ST2 end.
release_frame FR2 ST2 (bv_unsigned sp).
pose proof (obj_join asegs m S n szb j s rest ltac:(lia) Hsz SZ DATA WIN REST) as OBJ.
assert (Ls : length s = Z.to_nat n) by (destruct DATA as [[[Hwf _] _] _]; exact Hwf).
destruct (first_nul_split s (j :: rest)) as (str & rest' & E & NONUL & Hlen).
rewrite E in OBJ.
finish.
all: try exact OBJ.
all: try exact FDP.
all: try lia.
exact NONUL. }
destruct (Z_lt_dec n 16) as [Hn16 | Hn16].
- pose proof (lor7_bound n ltac:(lia)) as L7.
step. if_truex. apply TAIL.
- pose proof (lor7_eq23 n ltac:(lia)) as L7.
step. rewrite L7. if_falsex. step. apply TAIL.
Qed.

Definition crls_ev (m0 : word -> option byte) (sp : word) (S P ptr rem lo : Z) : Prop :=
forall mc, munch (crls_WA (bv_unsigned sp) S P lo) m0 mc ->
ro_cells asegs mc (P / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\ ro_cells asegs mc ((P + 8) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\
ro_cells asegs mc (S / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\ (0 < rem -> unpoisoned asegs mc A_SB ptr rem).

Lemma crls_loopA :
forall (fuel : nat) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 : word)
(x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
(S P ptr rem lo maxlen n k cnt : Z) (szb j : byte) (s rest data fj : list byte),
cnt <= Z.of_nat fuel ->
rw_cells asegs m (bv_unsigned sp + -80) [CB 8 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs m lo (bv_unsigned sp + -80) -> lo <= bv_unsigned sp - (80 + 4096) ->
bv_unsigned szb = 2 * n -> 0 <= n <= maxlen - cnt -> 1 <= cnt <= maxlen -> maxlen <= 20 ->
rw_cells asegs m S [C1 szb] ->
rw_cells asegs m (S + 1) [CB (Z.to_nat n) s] ->
rw_cells asegs m (S + n + 1) [C1 b0; C1 j] ->
rw_cells asegs m (S + n + 3) [CB (Z.to_nat (21 - n)) rest] ->
0 <= k <= rem ->
rw_cells asegs m P [C8 (Z_to_bv 64 (ptr + k)); C8 (Z_to_bv 64 (rem - k))] ->
bytes_at asegs m ptr data -> Z.of_nat (length data) = rem ->
munch (crls_WA (bv_unsigned sp) S P lo) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
crls_ev m0 sp S P ptr rem lo ->
6574080 <= S -> S + 24 <= lo -> 0 < ptr -> ptr + rem <= lo -> (S + 24 <= ptr \/ ptr + rem <= S) -> bv_unsigned sp <= P -> P + 16 <= 2^47 -> P mod 8 = 0 ->
alloc_ceiling <= lo ->
evt asegs (crls_postA maxlen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S P ptr rem lo data m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 cnt) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) (Z_to_bv 64 (P / 8 + 2147450880)) (Z_to_bv 64 92)
s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x92350) fc None m (seg_rom asegs)).
Proof.
induction fuel as [|fuel IH]; intros until fj; intros Hfuel FR ST LOS Hsz Hn Hcnt Hmax SZ DATA WIN REST Hk FDP SRC LEN MU WM MI EV S0 SLO PTR0 DLO SDS SPP P47 PAL LO.
{ exfalso. lia. }
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bv_unsigned_in_range 8 szb) as SR. unfold bv_modulus in SR. cbn in SR.
pose proof alloc_ceiling_range as ACR.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
assert (Ls : length s = Z.to_nat n) by (destruct DATA as [[[Hwf _] _] _]; exact Hwf).
assert (Lr : length rest = Z.to_nat (21 - n)) by (destruct REST as [[[Hwf _] _] _]; exact Hwf).
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.

assert (PUSHK : forall (k' : Z) (mc : word -> option byte) (c : byte) (xa0 xa2 xa3 xa4 xa5 : word),
k < k' <= rem ->
rw_cells asegs mc (bv_unsigned sp + -80) [CB 8 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs mc lo (bv_unsigned sp + -80) ->
rw_cells asegs mc S [C1 szb] -> rw_cells asegs mc (S + 1) [CB (Z.to_nat n) s] ->
rw_cells asegs mc (S + n + 1) [C1 b0; C1 j] -> rw_cells asegs mc (S + n + 3) [CB (Z.to_nat (21 - n)) rest] ->
rw_cells asegs mc P [C8 (Z_to_bv 64 (ptr + k')); C8 (Z_to_bv 64 (rem - k'))] ->
bytes_at asegs mc ptr data ->
munch (crls_WA (bv_unsigned sp) S P lo) m0 mc -> wmono asegs m0 mc -> mem_inv asegs mc ->
evt asegs (crls_postA maxlen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S P ptr rem lo data m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 P) xa0 (Z_to_bv 64 (bv_unsigned c)) xa2 xa3 xa4 xa5 a6 a7
(Z_to_bv 64 cnt) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) (Z_to_bv 64 (P / 8 + 2147450880)) (Z_to_bv 64 92)
s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x923d8) fc None mc (seg_rom asegs))).
{ intros k' mc c xa0 xa2 xa3 xa4 xa5 Hk' FRc STc SZc DATAc WINc RESTc FDPc SRCc MUc WMc MIc.
clear FR ST SZ DATA WIN REST FDP SRC MU WM MI.
pose proof (bv_unsigned_in_range 8 c) as CR. unfold bv_modulus in CR. cbn in CR.
unfold crls_WA in MUc.
step. step.
call_pushb S n lo szb b0 j.
all: lazymatch goal with
| |- evt _ _ _ => idtac
| |- Z_to_bv _ _ = Z_to_bv _ _ => reflexivity
| |- bv_unsigned _ = 2 * _ => assumption
| |- rw_cells _ _ _ [C1 _] => assumption
| |- rw_cells _ _ _ [C1 _; C1 _] => assumption
| |- stk _ _ _ _ => assumption
| |- mem_inv _ _ => assumption
| |- _ => lia
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
lazymatch goal with H : rw_cells asegs m2 S [C1 ?sz] |- _ => rename H into SZ2 end.
lazymatch goal with H : rw_cells asegs m2 (S + n + 1) _ |- _ => rename H into WIN2 end.
lazymatch goal with H : rw_cells asegs m2 (S + 1) _ |- _ => rename H into DATA2 end.
lazymatch goal with H : rw_cells asegs m2 (S + n + 3) _ |- _ => rename H into REST2 end.
lazymatch goal with H : rw_cells asegs m2 P _ |- _ => rename H into FDP2 end.
lazymatch goal with H : rw_cells asegs m2 (bv_unsigned sp + -80) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk asegs m2 lo _ |- _ => rename H into ST2 end.
lazymatch goal with H : bytes_at asegs m2 ptr data |- _ => rename H into SRC2 end.
lazymatch goal with H : munch _ m0 m2 |- _ => rename H into MU2 end.
lazymatch goal with H : wmono asegs m0 m2 |- _ => rename H into WM2 end.
lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
lazymatch goal with H : bv_unsigned ?szb' = 2 * (n + 1) |- _ => rename H into Hsz2 end.
destruct (rw_cells_unpair _ _ _ _ _ WIN2) as [Hcb Hnul]. clear WIN2.
replace (S + n + 1) with (S + 1 + Z.of_nat (Z.to_nat n)) in Hcb by lia.
pose proof (rw_cells_CB_snoc _ _ _ _ _ _ DATA2 Hcb) as DATA3. clear DATA2 Hcb.
replace (Datatypes.S (Z.to_nat n)) with (Z.to_nat (n + 1)) in DATA3 by lia.
destruct rest as [|j' rest']; [cbn in Lr; exfalso; lia|].
replace (Z.to_nat (21 - n)) with (Datatypes.S (Z.to_nat (21 - (n + 1)))) in REST2 by lia.
destruct (rw_cells_CB_head _ _ _ _ _ _ REST2) as [Hj' REST3]. clear REST2.
replace (S + n + 1 + 1) with (S + (n + 1) + 1) in Hnul by lia.
replace (S + n + 3) with (S + (n + 1) + 1 + 1) in Hj' by lia.
pose proof (rw_cells_pair _ _ _ _ _ Hnul Hj') as WIN3. clear Hnul Hj'.
replace (S + n + 3 + 1) with (S + (n + 1) + 3) in REST3 by lia.
fold (crls_WA (bv_unsigned sp) S P lo) in MU2.
destruct (EV _ MU2) as (_ & _ & SHS2 & _).

step. step.
destruct (Z.eq_dec (cnt + -1) 0) as [C0 | CN].
- rewrite C0. if_false. step.
eapply crls_doneA with (k := k'); [exact FR2 | exact ST2 | lia | exact Hsz2 | lia | exact Hmax | exact SZ2 | exact DATA3 | exact WIN3 | exact REST3 | lia | exact FDP2 | exact SRC2 | exact MU2 | exact WM2 | exact MI2 | exact SHS2 | lia].
- if_truex. clear SHS2.
eapply (IH sp ra s0 s1 s2 s3 s4 s5 s6 s7) with (k := k') (n := n + 1) (cnt := cnt + -1);
[ lia | exact FR2 | exact ST2 | exact LOS | exact Hsz2 | lia | lia | exact Hmax | exact SZ2 | exact DATA3 | exact WIN3 | exact REST3 | lia | exact FDP2 | exact SRC2 | exact LEN | exact MU2 | exact WM2 | exact MI2 | exact EV
| exact S0 | exact SLO | exact PTR0 | exact DLO | exact SDS | exact SPP | exact P47 | exact PAL | exact LO ]. }

destruct (EV _ MU) as (SHP & SHP8 & SHS & UNDc).
step. rewrite ?zxb_zero. step. if_false.
step. step.
destruct (Z.eq_dec (rem - k) 0) as [RK0 | RKN].
{ if_truex.
eapply crls_doneA with (k := k); [exact FR | exact ST | lia | exact Hsz | lia | exact Hmax | exact SZ | exact DATA | exact WIN | exact REST | lia | exact FDP | exact SRC | exact MU | exact WM | exact MI | exact SHS | lia]. }
if_falsex.

step. rewrite ?zxb_zero. step. if_false.
step.
destruct (unpoisoned_byte_ro m ptr rem (ptr + k) (UNDc ltac:(lia)) ltac:(lia)) as (v1 & SHK & Hv1).
destruct (nth_error data (Z.to_nat k)) as [b1|] eqn:Hb1; [| exfalso; apply nth_error_None in Hb1; lia].
pose proof (bv_unsigned_in_range 8 b1) as B1R. unfold bv_modulus in B1R. cbn in B1R.
step. step. sh_norm. step. step.
assert (B88 : forall (xa1 xa2 : word),
evt asegs (crls_postA maxlen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S P ptr rem lo data m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 P) (Z_to_bv 64 (ptr + k)) xa1 xa2 (Z_to_bv 64 (rem - k)) a4 a5 a6 a7
(Z_to_bv 64 cnt) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) (Z_to_bv 64 (P / 8 + 2147450880)) (Z_to_bv 64 92)
s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9237c) fc None m (seg_rom asegs))).
2:{ destruct Hv1 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply B88.
- rewrite (QsKa.Mq1.sxb_small v1) by lia. if_truex. step. step.
rewrite (unsigned_lit (ptr + k)) by lia. rewrite QsKa.Mq1.land7_mod8 by lia. if_falsex. step. apply B88. }
intros xa1 xa2. clear SHK v1 Hv1.
unfold crls_WA in MU.
pose proof (u8ro_read asegs m ptr data k b1 _ SRC Hb1 ltac:(lia) eq_refl) as RD1.
step. clear RD1. change (zxb b1) with (Z_to_bv 64 (bv_unsigned b1)).
step.
clear SHP SHP8 SHS.
step.

lazymatch goal with MUc : munch _ m0 ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (EV _ MUc) as (_ & SHP8b & _ & _) end.
step. rewrite ?zxb_zero. step. if_false. clear SHP8b.
step. step.
step.
destruct (Z.eq_dec (bv_unsigned b1) 92) as [E92 | N92].
2:{
if_truex. fold (crls_WA (bv_unsigned sp) S P lo) in MU.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
eapply (PUSHK (k + 1) mx b1); [lia | exact FR | exact ST | exact SZ | exact DATA | exact WIN | exact REST | | exact SRC | exact MU | exact WM | exact MI] end.
replace (rem - (k + 1)) with (rem - k + -1) by lia. replace (ptr + (k + 1)) with (ptr + k + 1) by lia. exact FDP. }
if_falsex.
step.
destruct (Z.eq_dec (rem - k - 1) 0) as [R0 | R1].
{
if_truex. fold (crls_WA (bv_unsigned sp) S P lo) in MU.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
eapply (PUSHK (k + 1) mx b1); [lia | exact FR | exact ST | exact SZ | exact DATA | exact WIN | exact REST | | exact SRC | exact MU | exact WM | exact MI] end.
replace (rem - (k + 1)) with (rem - k + -1) by lia. replace (ptr + (k + 1)) with (ptr + k + 1) by lia. exact FDP. }
if_falsex.

destruct (nth_error data (Z.to_nat (k + 1))) as [b2|] eqn:Hb2; [| exfalso; apply nth_error_None in Hb2; lia].
pose proof (bv_unsigned_in_range 8 b2) as B2R. unfold bv_modulus in B2R. cbn in B2R.
lazymatch goal with MUc : munch _ m0 ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (EV _ MUc) as (SHPc & _ & _ & UNDd);
destruct (unpoisoned_byte_ro mc ptr rem (ptr + k + 1) (UNDd ltac:(lia)) ltac:(lia)) as (v2 & SHK2 & Hv2) end.
step. step. sh_norm. step. step.
assert (BBC : forall (xa4 xa5 : word),
evt asegs (crls_postA maxlen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S P ptr rem lo data m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 P) (Z_to_bv 64 (ptr + k)) (Z_to_bv 64 (bv_unsigned b1)) (Z_to_bv 64 (ptr + k + 1))
(Z_to_bv 64 (rem - k)) xa4 xa5 a6 a7
(Z_to_bv 64 cnt) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) (Z_to_bv 64 (P / 8 + 2147450880)) (Z_to_bv 64 92)
s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x923b0) fc None m2 (seg_rom asegs))).
2:{ destruct Hv2 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply BBC.
- rewrite (QsKa.Mq1.sxb_small v2) by lia. if_truex. step. step.
rewrite (unsigned_lit (ptr + k + 1)) by lia. rewrite QsKa.Mq1.land7_mod8 by lia. if_truex. apply BBC. }
intros xa4 xa5. clear SHK2 v2 Hv2.

step. rewrite ?zxb_zero. step. if_false.
pose proof (u8ro_read asegs _ ptr data (k + 1) b2 _ SRC Hb2 ltac:(lia) eq_refl) as RD2.
replace (ptr + (k + 1)) with (ptr + k + 1) in RD2 by lia.
step. clear RD2. change (zxb b2) with (Z_to_bv 64 (bv_unsigned b2)).
step.
clear SHPc UNDd.
step.
lazymatch goal with MUc : munch _ m0 ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (EV _ MUc) as (_ & SHP8c & _ & _) end.
step. rewrite ?zxb_zero. step. if_false. clear SHP8c.
step. step.
step.
destruct (Z.eq_dec (bv_unsigned b2) 92) as [F92 | M92].
-
if_falsex. fold (crls_WA (bv_unsigned sp) S P lo) in MU.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
eapply (PUSHK (k + 2) mx b1); [lia | exact FR | exact ST | exact SZ | exact DATA | exact WIN | exact REST | | exact SRC | exact MU | exact WM | exact MI] end.
replace (rem - (k + 2)) with (rem - k + -2) by lia. replace (ptr + (k + 2)) with (ptr + k + 2) by lia. exact FDP.
-
if_truex. fold (crls_WA (bv_unsigned sp) S P lo) in MU.
destruct (EV _ MU) as (_ & _ & SHSd & _).
eapply crls_doneA with (k := k + 2);
[exact FR | exact ST | lia | exact Hsz | lia | exact Hmax | exact SZ | exact DATA | exact WIN | exact REST | lia
| replace (ptr + (k + 2)) with (ptr + k + 2) by lia; replace (rem - (k + 2)) with (rem - k + -2) by lia; exact FDP
| exact SRC | exact MU | exact WM | exact MI | exact SHSd | lia ].
Qed.

Lemma crls_spec_A : crls_A_stmt 0x922cc.
Proof.
unfold crls_A_stmt. intros until data. intros A0 A1 A2 Hmax RT OBJ UNS SAL S0 SAPP FDP UNP PAL SRC LEN PTR0 UND ST LO LOS SPA SLO DLO SDS SPP P47 MI.
subst a0 a1 a2. unfold CRLS_STK_A in LOS.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof alloc_ceiling_range as ACR.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (rw_cells_bound _ _ _ _ OBJ) as OB. cbn [cells_size csize Nat.add] in OB.
pose proof (munch_refl (crls_WA (bv_unsigned sp) S P lo) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold crls_WA in MU.

pose proof RT as RTC. unfold asan_rt_ok, a4_rt_cells in RTC. apply Forall_app in RTC as [_ RTC].
apply Forall_cons_iff in RTC as [GOT RTC]. apply Forall_cons_iff in RTC as [CELL _]. cbn [fst snd] in GOT, CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
apply ro_C8_of_bytes_at in GOT. apply ro_C8_of_bytes_at in CELL.
carve_frame 80%nat ST.
do 10 step.
step. step. step. step. step.
step. step. step. step.
assert (WAPP : Forall (fun iv : Z * Z => snd iv <= A_SB \/ A_HMB <= fst iv) [(lo, bv_unsigned sp); (S, S + 24); (P, P + 16)]).
{ unfold app_range in SAPP. unfold A_SB, A_HMB in *. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (UNSc : unpoisoned asegs mc A_SB S 24) by (eapply unpoisoned_keep; [exact UNS | exact MU | lia | lia | exact WAPP]);
assert (RTc : asan_rt_ok mc) by (eapply asan_rt_ok_transport; [exact RT | exact MU | intros cc Hcc; pose proof (a4_rt_cells_in_img cc Hcc) as X; cbn [disjoint_from]; repeat split; lia]) end.
stash SRC.
eapply OBL_AMEMSET_U with (d := S) (c := 0) (n := 24) (lo := lo) (old := junk).
1: intros _; exact UNSc.
1: exact RTc.
all: rewrite ?unsigned_lit by lia.
1: lia.
1: lia.
1: left; lia.
1: reflexivity.
1: reflexivity.
1: reflexivity.
1: lia.
1: lia.
1: left; lia.
1: exact OBJ.
1: exact ST.
1: exact LO.
1: lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: exact MI.
1: reflexivity.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m1 MU1 WM1 MI1 OBJ1 ST1.
unstash SRC.
assert (SRC1 : rem <> 0 -> bytes_at asegs m1 ptr data).
{ intros RN. eapply bytes_at_transport; [exact SRC | exact MU1 |]. cbn [disjoint_from]. rewrite LEN. destruct SDS as [?|[?|?]]; lia. }
clear SRC.
transport_after_call asegs m0 m1 MU1 WM1. clear MU1 WM1 UNSc RTc.
replace (ret_pc (Z_to_bv 64 598808)) with (Z_to_bv 64 598808) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
change (Z.to_nat 24) with 24%nat in OBJ1.

assert (EV : forall mc, munch [(lo, bv_unsigned sp); (S, S + 24); (P, P + 16)] m mc ->
ro_cells asegs mc (P / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\ ro_cells asegs mc ((P + 8) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\
unpoisoned asegs mc A_SB S 24 /\ (0 < rem -> unpoisoned asegs mc A_SB ptr rem)).
{ intros mc MUc.
assert (UP : unpoisoned asegs mc A_SB P 16) by (eapply unpoisoned_keep; [exact UNP | exact MUc | lia | lia | exact WAPP]).
split; [apply (unpoisoned_al8_ro mc P 16 P UP); lia|]. split; [apply (unpoisoned_al8_ro mc P 16 (P + 8) UP); [lia | lia | clear - PAL; Z.div_mod_to_equations; lia]|].
split; [eapply unpoisoned_keep; [exact UNS | exact MUc | lia | lia | exact WAPP]|].
intros Hr. eapply unpoisoned_keep; [exact (UND Hr) | exact MUc | lia | lia | exact WAPP]. }
destruct (EV _ MU) as (SHP & SHP8 & _ & _).
step. step. step. sh_norm.
step. rewrite ?zxb_zero. step. if_false. clear SHP SHP8.
step.

assert (OBJz : rw_cells asegs m1 S ([C1 b0] ++ ([CB 0 []] ++ ([C1 b0; C1 b0] ++ [CB 21 (repeat b0 21)])))).
{ eapply rw_cells_recast; [exact OBJ1 | cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity]. }
clear OBJ1.
apply (proj1 (rw_cells_app asegs m1 S _ _)) in OBJz as [SZ0 OBJz]. cbn [cells_size csize Nat.add] in OBJz. change (Z.of_nat 1) with 1 in OBJz.
apply (proj1 (rw_cells_app asegs m1 _ _ _)) in OBJz as [DATA0 OBJz]. cbn [cells_size csize Nat.add] in OBJz. rewrite Z.add_0_r in OBJz.
apply (proj1 (rw_cells_app asegs m1 _ _ _)) in OBJz as [WIN0 REST0]. cbn [cells_size csize Nat.add] in REST0. change (Z.of_nat 2) with 2 in REST0.
replace (S + 1) with (S + 0 + 1) in WIN0 by lia. replace (S + 1 + 2) with (S + 0 + 3) in REST0 by lia.

assert (J : forall r : Z, 0 <= r <= maxlen ->
evt asegs (crls_postA maxlen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S P ptr rem lo data m)
(MS (mkR (Z_to_bv 64 598808) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 P)
(Z_to_bv 64 0) (Z_to_bv 64 r) v2 v3 v4 v5 v6 v7 (Z_to_bv 64 maxlen) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880))
s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
F (Z_to_bv 64 0x92338) fc None m1 (seg_rom asegs))).
2:{ step.
destruct (Z_lt_dec rem maxlen) as [LT | GE].
- if_truex. apply J. lia.
- if_falsex. step. apply J. lia. }
intros r Hr.
step. step.
lazymatch goal with |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?spv + ?kk))) _)) _ _ _ _ _ _) => name_sp spv kk end.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [eapply reserve_spec with (S := S) (n := 0) (r := r) (szb := b0) (rest := @nil cell) | unfold reserve_post; post_call segs mm] end.
all: unname_sp.
all: lazymatch goal with
| |- evt _ _ _ => idtac
| |- Z_to_bv _ _ = Z_to_bv _ _ => reflexivity
| |- bv_unsigned _ = 2 * _ => reflexivity
| |- rw_cells _ _ _ (C1 _ :: _) => exact SZ0
| |- mem_inv _ _ => assumption
| |- _ => lia
end.
step. if_falsex.
step. step. sh_norm. step.
assert (EVL : crls_ev m sp S P ptr rem lo).
{ intros mc MUc. unfold crls_WA in MUc. destruct (EV mc MUc) as (E1 & E2 & E3 & E4).
split; [exact E1|]. split; [exact E2|]. split; [| exact E4]. apply (unpoisoned_al8_ro mc S 24 S E3); lia. }
replace (Z_to_bv 64 ptr) with (Z_to_bv 64 (ptr + 0)) in FDP by (rewrite Z.add_0_r; reflexivity).
replace (Z_to_bv 64 rem) with (Z_to_bv 64 (rem - 0)) in FDP by (rewrite Z.sub_0_r; reflexivity).
fold (crls_WA (bv_unsigned sp) S P lo) in MU.
destruct (Z.eq_dec rem 0) as [R0 | RN0].
{
assert (data = []) as -> by (destruct data; [reflexivity | cbn in LEN; lia]).
assert (SRCz : forall mz : word -> option byte, bytes_at asegs mz ptr []) by (intros mz; apply bytes_at_nil; lia).
destruct (EVL _ MU) as (_ & SHP8z & SHSz & _).
step. rewrite ?zxb_zero. step. if_false.
step. step. rewrite R0. if_truex.
eapply crls_doneA with (k := 0) (n := 0) (szb := b0) (j := b0) (s := @nil byte) (rest := repeat b0 21);
[ exact FR | exact ST1 | lia | reflexivity | lia | lia | exact SZ0 | exact DATA0 | exact WIN0 | exact REST0 | lia | rewrite R0 in FDP; exact FDP | apply SRCz | exact MU | exact WM | exact MI1 | exact SHSz | lia ]. }
assert (SDS' : S + 24 <= ptr \/ ptr + rem <= S) by (destruct SDS as [? | ?]; [lia | assumption]).
eapply (crls_loopA (Z.to_nat maxlen) sp ra s0 s1 s2 s3 s4 s5 s6 s7) with (k := 0) (n := 0) (cnt := maxlen) (szb := b0) (j := b0) (s := @nil byte) (rest := repeat b0 21);
[ lia | exact FR | exact ST1 | lia | reflexivity | lia | lia | lia | exact SZ0 | exact DATA0 | exact WIN0 | exact REST0 | lia | exact FDP | exact (SRC1 RN0) | exact LEN | exact MU | exact WM | exact MI1 | exact EVL
| exact S0 | exact SLO | exact PTR0 | exact DLO | exact SDS' | exact SPP | exact P47 | exact PAL | exact LO ].
Qed.
End ACrls.

Theorem crls_A : crls_A_stmt 0x922cc.
Proof. exact (crls_spec_A QpNt.Mq4.amemset_U). Qed.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 Qw5U.Mq4 QpNt.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma upd_at_prefix : forall {X} (pre : list X) (x : X) (post : list X) (y : X) i,
length pre = i -> upd (pre ++ x :: post) i y = pre ++ y :: post.
Proof. induction pre as [|p pre IH]; intros x post y i <-; cbn; [reflexivity | now rewrite (IH x post y (length pre) eq_refl)]. Qed.

Lemma skipn_cons_nth : forall {X} (l : list X) i d, (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof.
induction l as [|x l IH]; intros [|i] d Hi; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.

Lemma firstn_snoc_nth : forall {X} (l : list X) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
induction l as [|x l IH]; intros [|i] d Hi; cbn in *; try lia; [reflexivity|]. f_equal. apply IH. lia.
Qed.

Lemma nth_error_nth' : forall {X} (l : list X) i d, (i < length l)%nat -> nth_error l i = Some (nth i l d).
Proof. induction l as [|x l IH]; intros [|i] d Hi; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma internal_memmove_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D B n : Z) (src old : list byte) (Q : machine_state -> Prop),
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 n ->
0 <= D -> D + n <= 2^63 -> 0 <= B -> B + n <= 2^63 -> 0 <= n < 2^40 ->
(B + n <= D \/ D + n <= B) ->
bytes_at asegs m B src -> length src = Z.to_nat n -> rw_cells asegs m D [CB (Z.to_nat n) old] ->
mem_inv asegs m ->
(forall (a1' a2' a3' a4' a5' a6' : word) m',
munch [(D, D + n)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' D [CB (Z.to_nat n) src] -> bytes_at asegs m' B src ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x74f18) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros -> -> -> HD HDn HS HSn Hn SEP SRC SRCL DST MI K.
pose proof (munch_refl [(D, D + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (LOLD : length old = Z.to_nat n) by (destruct DST as [[[Hwf _] _] _]; exact Hwf).
step.
destruct (Z.lt_ge_cases D B) as [HDS | HSD].
-
if_falsex.
step.
destruct (Z.eq_dec n 0) as [Hn0 | Hnz].
+ if_truex. step.
assert (Esrc : src = []) by (destruct src; [reflexivity | cbn in SRCL; lia]).
assert (Eold : old = []) by (destruct old; [reflexivity | cbn in LOLD; lia]).
subst src old. eapply K; [exact MU | exact WM | exact MI | exact DST | exact SRC].
+ if_falsex.
step. step.
try replace (n + D) with (D + n) by lia.

assert (FWD : forall (Kn : nat) (i di bi : Z) (x4 : word) mi,
Z.to_nat (n - i) = Kn -> 0 <= i < n -> di = D + i -> bi = B + i ->
munch [(D, D + n)] m mi -> wmono asegs m mi -> mem_inv asegs mi -> bytes_at asegs mi B src ->
rw_cells asegs mi D [CB (Z.to_nat n) (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) old)] ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 bi) (Z_to_bv 64 (D + n)) (Z_to_bv 64 di) x4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x74f28) fc None mi (seg_rom asegs))).
{ clear MU WM MI SRC DST.
induction Kn as [|Kn IH]; intros i di bi x4 mi HK Hi -> -> MUi WMi MIi SRCi DSTi; [lia|].
assert (LCUR : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) old) = Z.to_nat n)
by (rewrite length_app, length_firstn, length_skipn; lia).
pose proof (nth_error_nth' src (Z.to_nat i) (Z_to_bv 8 0) ltac:(lia)) as NTH.
pose proof (u8ro_read asegs mi B src i _ (wa (B + i)) SRCi NTH ltac:(lia) eq_refl) as HR.
step. clear HR.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DSTi) as DA. clear DSTi.
pose proof (u8arr_store_ok asegs _ _ _ i (wa (D + i)) DA ltac:(rewrite LCUR; lia) eq_refl) as SOK.
step.
rewrite QZDE.le1_zxb.
pose proof (u8arr_write asegs _ _ _ i (nth (Z.to_nat i) src (Z_to_bv 8 0)) DA ltac:(rewrite LCUR; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DSTn. clear DA2. rewrite upd_length, LCUR in DSTn.

rewrite (skipn_cons_nth old (Z.to_nat i) (Z_to_bv 8 0)) in DSTn by lia.
rewrite (upd_at_prefix _ _ _ _ (Z.to_nat i)) in DSTn by (rewrite length_firstn; lia).
step. step.
step.
destruct (Z.eq_dec (i + 1) n) as [Hlast | Hmore].
* if_falsex. step. step.
eapply K; [exact MUi | exact WMi | exact MIi | | exact SRCi].
replace src with (firstn (Z.to_nat i) src ++ nth (Z.to_nat i) src (Z_to_bv 8 0) :: skipn (S (Z.to_nat i)) old) at 1; [exact DSTn|].
rewrite skipn_all2 by lia. rewrite <- (firstn_snoc_nth src (Z.to_nat i) (Z_to_bv 8 0)) by lia.
rewrite firstn_all2 by lia. reflexivity.
* if_truex.
eapply (IH (i + 1)); [lia | lia | lia | lia | exact MUi | exact WMi | exact MIi | exact SRCi |].
replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
rewrite (firstn_snoc_nth src (Z.to_nat i) (Z_to_bv 8 0)) by lia. rewrite <- app_assoc. cbn [app]. exact DSTn. }
eapply (FWD (Z.to_nat (n - 0)) 0); [lia | lia | lia | lia | exact MU | exact WM | exact MI | exact SRC | cbn [Z.to_nat firstn skipn app]; exact DST].
-
if_truex.
step.
destruct (Z.eq_dec B D) as [Heq | Hne].
+ if_truex. step.
assert (Hn0 : n = 0) by lia.
assert (Esrc : src = []) by (destruct src; [reflexivity | cbn in SRCL; lia]).
assert (Eold : old = []) by (destruct old; [reflexivity | cbn in LOLD; lia]).
subst src old. eapply K; [exact MU | exact WM | exact MI | exact DST | exact SRC].
+ if_falsex.
step.
destruct (Z.eq_dec n 0) as [Hn0 | Hnz].
* if_truex. step.
assert (Esrc : src = []) by (destruct src; [reflexivity | cbn in SRCL; lia]).
assert (Eold : old = []) by (destruct old; [reflexivity | cbn in LOLD; lia]).
subst src old. eapply K; [exact MU | exact WM | exact MI | exact DST | exact SRC].
* if_falsex.
step. step.
replace (n + -1) with (n - 1) by lia.

assert (BWD : forall (Kn : nat) (j : Z) (x4 x5 x6 : word) mi,
Z.to_nat j = Kn -> 0 <= j < n ->
munch [(D, D + n)] m mi -> wmono asegs m mi -> mem_inv asegs mi -> bytes_at asegs mi B src ->
rw_cells asegs mi D [CB (Z.to_nat n) (firstn (S (Z.to_nat j)) old ++ skipn (S (Z.to_nat j)) src)] ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 B) (Z_to_bv 64 1) (Z_to_bv 64 j) x4 x5 x6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x74f50) fc None mi (seg_rom asegs))).
{ clear MU WM MI SRC DST.
induction Kn as [Kn IH] using lt_wf_ind; intros j x4 x5 x6 mi HK Hj MUi WMi MIi SRCi DSTi.
assert (LCUR : length (firstn (S (Z.to_nat j)) old ++ skipn (S (Z.to_nat j)) src) = Z.to_nat n)
by (rewrite length_app, length_firstn, length_skipn; lia).
pose proof (nth_error_nth' src (Z.to_nat j) (Z_to_bv 8 0) ltac:(lia)) as NTH.
pose proof (u8ro_read asegs mi B src j _ (wa (B + j)) SRCi NTH ltac:(lia) eq_refl) as HR.
step.
try replace (j + B) with (B + j) by lia.
step. clear HR.
step.
try replace (j + D) with (D + j) by lia.
step. step.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DSTi) as DA. clear DSTi.
pose proof (u8arr_store_ok asegs _ _ _ j (wa (D + j)) DA ltac:(rewrite LCUR; lia) eq_refl) as SOK.
step.
rewrite QZDE.le1_zxb.
pose proof (u8arr_write asegs _ _ _ j (nth (Z.to_nat j) src (Z_to_bv 8 0)) DA ltac:(rewrite LCUR; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DSTn. clear DA2. rewrite upd_length, LCUR in DSTn.

rewrite (firstn_snoc_nth old (Z.to_nat j) (Z_to_bv 8 0)) in DSTn by lia. rewrite <- app_assoc in DSTn. cbn [app] in DSTn.
rewrite (upd_at_prefix _ _ _ _ (Z.to_nat j)) in DSTn by (rewrite length_firstn; lia).
rewrite <- (skipn_cons_nth src (Z.to_nat j) (Z_to_bv 8 0)) in DSTn by lia.
step.
destruct (Z.eq_dec j 0) as [Hlast | Hmore].
-- if_falsex. step.
eapply K; [exact MUi | exact WMi | exact MIi | | exact SRCi].
subst j. cbn [Z.to_nat firstn skipn app] in DSTn. exact DSTn.
-- if_truex.
replace (j + -1) with (j - 1) by lia.
eapply (IH (Z.to_nat (j - 1)) ltac:(lia) (j - 1)); [lia | lia | exact MUi | exact WMi | exact MIi | exact SRCi |].
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. exact DSTn. }
eapply (BWD (Z.to_nat (n - 1)) (n - 1)); [lia | lia | exact MU | exact WM | exact MI | exact SRC |].
replace (S (Z.to_nat (n - 1))) with (Z.to_nat n) by lia.
rewrite firstn_all2 by lia. rewrite skipn_all2 by lia. rewrite app_nil_r. exact DST.
Qed.

Definition A_MEMMOVE_U : Z := 0x61e20.

Definition amemmove_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d s n lo : Z) (old src : list byte)
(Q : machine_state -> Prop),
(0 < n -> unpoisoned asegs m A_SB d n) -> (0 < n -> unpoisoned asegs m A_SB s n) -> asan_rt_ok m ->
0 <= d -> d + n <= 2^47 -> 0 <= s -> s + n <= 2^47 ->
(d + n <= lo \/ bv_unsigned sp <= d) -> (s + n <= lo \/ bv_unsigned sp <= s) ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n -> 0 <= n < 2^40 -> (n <= 64 \/ (app_mem d n /\ app_mem s n)) ->
(s + n <= d \/ d + n <= s) ->
rw_cells asegs m d [CB (Z.to_nat n) old] -> bytes_at asegs m s src -> length src = Z.to_nat n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) src] -> bytes_at asegs m' s src ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMMOVE_U) fc None m (seg_rom asegs)).

Section MuslAMemmove.

Lemma amemmove_sound_U : amemmove_spec_U.
Proof.
unfold amemmove_spec_U.
intros until Q. intros UPd0 UPs0 RT Hd0 Hd47 Hs0 Hs47 Hdlo Hslo Ha0 Ha1 Ha2 Hn Hsz Hdisj DST SRC SRCL ST LO LOS SPA MI RA K.
subst a0 a1 a2. unfold_consts. word_range sp SPR.
pose proof RT as RTC. unfold asan_rt_ok, a4_rt_cells, a4_rt_consts in RTC. cbn [app] in RTC.
apply Forall_cons_iff in RTC as [GOTF RTC]. apply Forall_cons_iff in RTC as [FLAG RTC].
cbn [fst snd] in GOTF, FLAG.
do 59 (apply Forall_cons_iff in RTC as [_ RTC]).
apply Forall_cons_iff in RTC as [GOT RTC]. apply Forall_cons_iff in RTC as [CELL _]. cbn [fst snd] in GOT, CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
apply ro_C8_of_bytes_at in GOTF. apply ro_C8_of_bytes_at in GOT. apply ro_C8_of_bytes_at in CELL.
assert (FLAGc : ro_cells asegs m 0xf07d9 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact FLAG]). clear FLAG.
stash SRC.
pose proof (munch_refl [(d, d + n); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
unfold A_MEMMOVE_U. carve_frame 64%nat ST.
do 11 step.
unstash SRC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SRC1 : bytes_at asegs mc s src)
by (eapply bytes_at_transport; [exact SRC | exact MU | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia])
end.
clear SRC.
do 4 step. if_false.
step. step. step. step.
rewrite (unsigned_lit s) by lia. rewrite (lxor_ones64 s) by lia. if_falsex.
step. step. step.

assert (TAIL2G : forall (xra x0 x1 x2 x3 x4 x5 x6 x7 w1 w2 w3 w5 w6 z3 z4 z5 z6 : word) (oldz : list byte) mz,
munch [(d, d + n); (lo, bv_unsigned sp)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
stk asegs mz lo (bv_unsigned sp + -64) ->
rw_cells asegs mz (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mz d [CB (Z.to_nat n) oldz] -> bytes_at asegs mz s src ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x0 x1 x2 sp w1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
x3 x4 x5 x6 x7 w2 w3 (Z_to_bv 64 (bv_unsigned sp + -2136)) w5 w6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
F (Z_to_bv 64 0x61f00) fc None mz (seg_rom asegs))).
{ intros xra x0 x1 x2 x3 x4 x5 x6 x7 w1 w2 w3 w5 w6 z3 z4 z5 z6 oldz mz MUz WMz MIz STz FRz DSTz SRCz.
clear GOTF GOT CELL FLAGc MU WM MU0 ST FR DST SRC1 MI.
step.
eapply internal_memmove_spec with (D := d) (B := s) (n := n);
[ reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | lia | exact Hdisj | exact SRCz | exact SRCL | exact DSTz | exact MIz | ].
intros y1 y2 y3 y4 y5 y6 m5 MU5 WM5 MI5 DST5 SRC5.
lazymatch type of MU5 with munch _ ?mc _ =>
transport_after_call asegs mc m5 MU5 WM5; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU5 WM5 end.
replace (ret_pc (Z_to_bv 64 0x61f04)) with (Z_to_bv 64 0x61f04) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 11 step.
eapply K;
[ exact MUz | exact WMz | exact MI5 | exact DST5 | exact SRC5
| release_frame FRz STz (bv_unsigned sp); exact STz ]. }
destruct (Z.eq_dec n 0) as [Hn0 | Hnz].
{
clear UPd0 UPs0.
subst n. change (0 + -65) with (-65). if_true.
step. if_false. step.
step. step. rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. if_true.
step. if_false. step.
eapply TAIL2G; [exact MU | exact WM | exact MI | exact ST | exact FR | exact DST | exact SRC1]. }
destruct (Z.lt_ge_cases 64 n) as [Hbig | Hsmall].
{
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UPs1 : unpoisoned asegs mc A_SB s n)
by (eapply unpoisoned_transport; [exact (UPs0 ltac:(lia)) | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB s n); try eassumption; unfold A_SB; lia]);
assert (RT1 : asan_rt_ok mc)
by (eapply asan_rt_ok_transport; [exact RT | exact MU0 | intros cc Hcc2; pose proof (a4_rt_cells_in_img cc Hcc2); cbn; split; [left; lia | exact I]])
end.
destruct Hsz as [Hsz | [AMd AMs]]; [lia|].
if_truex.
step. if_truex.
do 5 step.
step.
stash SRC1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2144) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply region_is_poisoned_sound_U with (s := s) (n := n) (lo := lo);
[ exact UPs1 | exact RT1 | exact AMs | lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MI
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 MU2 WM2 MI2 ST1' UPs2 RT2.
assert (SRC2 : bytes_at asegs m2 s src)
by (unstash SRC1; eapply bytes_at_transport; [exact SRC1 | exact MU2 | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia]).
clear SRC1.
assert (UPd2 : unpoisoned asegs m2 A_SB d n).
{ eapply unpoisoned_transport; [exact (UPd0 ltac:(lia)) | | intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia].
eapply munch_trans; [exact MU0 | eapply munch_weaken; [| exact MU2]]. unfold sub_fp; cbn [outside]; intros; lia. }
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x62098)) with (Z_to_bv 64 0x62098) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 4 step.
step. if_true.
step. step. rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. if_truex.
step. if_truex.
do 4 step.
step.
stash SRC2.
eapply region_is_poisoned_sound_U with (s := d) (n := n) (lo := lo);
[ exact UPd2 | exact RT2 | exact AMd | lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1'
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MI2
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0' u1' u2' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' m3 MU3 WM3 MI3 ST1'' UPd3 RT3.
assert (SRC3 : bytes_at asegs m3 s src)
by (unstash SRC2; eapply bytes_at_transport; [exact SRC2 | exact MU3 | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia]).
clear SRC2.
lazymatch type of MU3 with munch _ ?mc _ =>
transport_after_call asegs mc m3 MU3 WM3; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU3 WM3 end.
replace (ret_pc (Z_to_bv 64 0x62138)) with (Z_to_bv 64 0x62138) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 4 step.
step. if_true.
eapply TAIL2G; [exact MU | exact WM | exact MI3 | eapply stk_merge; [exact ST1'' | exact ST2 | lia] | exact FR | exact DST | exact SRC3]. }

rewrite (size_test_n n) by lia. cbv iota.
assert (Hg : d / 8 <= (d + n - 1) / 8 <= d / 8 + 8) by (Z.div_mod_to_equations; lia).
assert (Hh : s / 8 <= (s + n - 1) / 8 <= s / 8 + 8) by (clear Hg; Z.div_mod_to_equations; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UPd1 : unpoisoned asegs mc A_SB d n)
by (eapply unpoisoned_transport; [exact (UPd0 ltac:(lia)) | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia]);
assert (UPs1 : unpoisoned asegs mc A_SB s n)
by (eapply unpoisoned_transport; [exact (UPs0 ltac:(lia)) | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB s n); try eassumption; unfold A_SB; lia])
end.
clear MU0.
destruct (unpoisoned_word asegs _ _ _ _ (d / 8 + A_SB) UPd1 ltac:(unfold A_SB; clear Hh; Z.div_mod_to_equations; lia)) as (w1 & Lw1 & W1c).
destruct (unpoisoned_word asegs _ _ _ _ ((d + n - 1) / 8 + A_SB) UPd1 ltac:(unfold A_SB; clear Hh; Z.div_mod_to_equations; lia)) as (w2 & Lw2 & W2c).
destruct (unpoisoned_word asegs _ _ _ _ (s / 8 + A_SB) UPs1 ltac:(unfold A_SB; clear Hg; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((s + n - 1) / 8 + A_SB) UPs1 ltac:(unfold A_SB; clear Hg; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in W1c, W2c, V1c, V2c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (GR0 : forall j, 0 <= j -> d / 8 + j < (d + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (d / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]);
[ intros j Hj Hjl; apply ov_read1_of_ro;
replace (d / 8 + 2147450880 + j) with ((d / 8 + j) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPd1); lia |];
assert (GS0 : forall j, 0 <= j -> s / 8 + j < (s + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (s / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]);
[ intros j Hj Hjl; apply ov_read1_of_ro;
replace (s / 8 + 2147450880 + j) with ((s / 8 + j) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPs1); lia |];
assert (HRLd : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (d + n - 1) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPd1) as (v & Hro & Hv); exists v; split; [| exact Hv]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro);
assert (HRLs : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((s + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (s + n - 1) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPs1) as (v & Hro & Hv); exists v; split; [| exact Hv]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro)
end.
clear UPd1 UPs1.
step. step. step.
try replace (n + s) with (s + n) by lia.
step. step. step.
replace (s + n + -1) with (s + n - 1) by lia.
step. step. step. step. step.
sh_norm.
replace (2147450880 + s / 8) with (s / 8 + 2147450880) by lia.
replace (2147450880 + (s + n - 1) / 8) with ((s + n - 1) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (s / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((s + n - 1) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TAIL2 : forall x3 x4 x5 x6 x7 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) x3 x4 x5 x6 x7
s2 (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (bv_unsigned sp + -2136)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61f00) fc None mc (seg_rom asegs)))
by (intros x3 x4 x5 x6 x7; eapply TAIL2G; [exact MU | exact WM | exact MI | exact ST | exact FR | exact DST | exact SRC1])
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP2 : forall (Kn : nat) (i : Z) (x6 x7 : word),
Z.to_nat ((d + n - 1) / 8 - d / 8 - i) = Kn -> 0 <= i -> d / 8 + i < (d + n - 1) / 8 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 (d / 8 + 2147450880 + i)) (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) (Z_to_bv 64 0) x6 x7
s2 (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (bv_unsigned sp + -2136)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6210c) fc None mc (seg_rom asegs)))
end.
{ clear GS0 GOTF FLAGc GOT CELL Hh HRLd HRLs;
induction Kn as [|Kn IH]; intros i x6 x7 HK Hi Hig; [lia|];
pose proof (GR0 i Hi Hig) as HR;
step; rewrite ?zxb_zero; clear HR;
step; step; rewrite ?(unsigned_lit 0) by lia; change (Z.lor 0 0) with 0;
step;
destruct (Z.eq_dec (d / 8 + i + 1) ((d + n - 1) / 8)) as [Heq|Hne];
[ if_falsex; step; step; if_true; apply TAIL2
| if_truex; replace (d / 8 + 2147450880 + i + 1) with (d / 8 + 2147450880 + (i + 1)) by lia; apply (IH (i + 1)); lia ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (MID : forall x3 x4 x5 x6 x7 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) x3 x4 x5 x6 x7
s2 (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (bv_unsigned sp + -2136)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61eb4) fc None mc (seg_rom asegs)))
end.
{ intros x3 x4 x5 x6 x7;
clear V1c V2c GS0 GOTF FLAGc Hh HRLs;
step; step; rewrite (unsigned_lit d) by lia; rewrite (lxor_ones64 d) by lia; if_falsex;
step; step; rewrite (size_test_n n) by lia; cbv iota;
step; step; step;
try replace (n + d) with (d + n) by lia;
step; step; step;
replace (d + n + -1) with (d + n - 1) by lia;
step; step; step; step; step;
sh_norm;
replace (2147450880 + d / 8) with (d / 8 + 2147450880) by lia;
replace (2147450880 + (d + n - 1) / 8) with ((d + n - 1) / 8 + 2147450880) by lia;
rewrite (unsigned_lit (d / 8 + 2147450880)) by lia; rewrite (unsigned_lit ((d + n - 1) / 8 + 2147450880)) by lia;
rewrite !land_m8_64 by lia;
do 2 step; step; step;
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end;
[
destruct HRLd as (v & HR & Hv);
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia);
step; rewrite (sxb_small v) by lia; clear HR;
step; rewrite (unsigned_lit (d + n - 1)) by lia; rewrite land7_mod8 by lia;
step; step; step; step;
destruct Hv as [-> | (Hk & Hlast)];
[ rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia);
rewrite (unsigned_lit 0) by lia; rewrite Z.land_0_l
| rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 v)) by (rewrite !unsigned_lit by lia; lia);
rewrite (v_slt_1 (Z_to_bv 64 ((d + n - 1) mod 8)) (Z_to_bv 64 v)) by (rewrite !signed_lit by lia; try clear Hg; try clear Hh; Z.div_mod_to_equations; lia);
rewrite !(unsigned_lit 1) by lia; change (Z.lxor 1 1) with 0; rewrite Z.land_0_r ];
(step;
destruct (Z.eq_dec (d / 8) ((d + n - 1) / 8)) as [Heq1|Hne1];
[ if_truex; step; step; if_true; apply TAIL2
| if_falsex; replace (d / 8 + 2147450880) with (d / 8 + 2147450880 + 0) by lia;
apply (LOOP2 (Z.to_nat ((d + n - 1) / 8 - d / 8 - 0)) 0); lia ])
|  apply TAIL2 ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP1 : forall (Kn : nat) (i : Z) (x6 x7 : word),
Z.to_nat ((s + n - 1) / 8 - s / 8 - i) = Kn -> 0 <= i -> s / 8 + i < (s + n - 1) / 8 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 (s / 8 + 2147450880 + i)) (Z_to_bv 64 ((s + n - 1) / 8 + 2147450880)) (Z_to_bv 64 0) x6 x7
s2 (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (bv_unsigned sp + -2136)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x62068) fc None mc (seg_rom asegs)))
end.
{ clear W1c W2c V1c V2c GR0 GOTF FLAGc GOT CELL Hg TAIL2 LOOP2 HRLd HRLs;
induction Kn as [|Kn IH]; intros i x6 x7 HK Hi Hig; [lia|];
pose proof (GS0 i Hi Hig) as HR;
step; rewrite ?zxb_zero; clear HR;
step; step; rewrite ?(unsigned_lit 0) by lia; change (Z.lor 0 0) with 0;
step;
destruct (Z.eq_dec (s / 8 + i + 1) ((s + n - 1) / 8)) as [Heq|Hne];
[ if_falsex; step; step; if_true; apply MID
| if_truex; replace (s / 8 + 2147450880 + i + 1) with (s / 8 + 2147450880 + (i + 1)) by lia; apply (IH (i + 1)); lia ]. }

clear W1c W2c GR0 GOTF FLAGc Hg TAIL2 LOOP2 HRLd.
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
-
destruct HRLs as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
step. rewrite (sxb_small v) by lia. clear HR.
step. rewrite (unsigned_lit (s + n - 1)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
+ rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (s / 8) ((s + n - 1) / 8)) as [Heq1|Hne1].
* if_truex. step. step. if_true. apply MID.
* if_falsex. replace (s / 8 + 2147450880) with (s / 8 + 2147450880 + 0) by lia.
apply (LOOP1 (Z.to_nat ((s + n - 1) / 8 - s / 8 - 0)) 0); lia.
+ rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 v)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((s + n - 1) mod 8)) (Z_to_bv 64 v)) by (rewrite !signed_lit by lia; try clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (s / 8) ((s + n - 1) / 8)) as [Heq1|Hne1].
* if_truex. step. step. if_true. apply MID.
* if_falsex. replace (s / 8 + 2147450880) with (s / 8 + 2147450880 + 0) by lia.
apply (LOOP1 (Z.to_nat ((s + n - 1) / 8 - s / 8 - 0)) 0); lia.
-  apply MID.
Qed.
End MuslAMemmove.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition amemmove_any_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (ab nb d sb nsb s n lo : Z) (old src : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (ab, nb) LB -> ab <= d -> d + n <= ab + nb ->
In (sb, nsb) LB -> sb <= s -> s + n <= sb + nsb ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n -> 0 <= n < 2^40 -> (s + n <= d \/ d + n <= s) ->
rw_cells asegs m d [CB (Z.to_nat n) old] -> bytes_at asegs m s src -> length src = Z.to_nat n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) src] -> bytes_at asegs m' s src ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMMOVE_U) fc None m (seg_rom asegs)).

End WithIface.
End RC__1.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpNt.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma upd_at_prefix : forall {X} (pre : list X) (x : X) (post : list X) (y : X) i,
length pre = i -> upd (pre ++ x :: post) i y = pre ++ y :: post.
Proof. induction pre as [|p pre IH]; intros x post y i <-; cbn; [reflexivity | now rewrite (IH x post y (length pre) eq_refl)]. Qed.

Lemma skipn_cons_nth : forall {X} (l : list X) i d, (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof.
induction l as [|x l IH]; intros [|i] d Hi; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.

Lemma firstn_snoc_nth : forall {X} (l : list X) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
induction l as [|x l IH]; intros [|i] d Hi; cbn in *; try lia; [reflexivity|]. f_equal. apply IH. lia.
Qed.

Lemma nth_error_nth' : forall {X} (l : list X) i d, (i < length l)%nat -> nth_error l i = Some (nth i l d).
Proof. induction l as [|x l IH]; intros [|i] d Hi; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma internal_memmove_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D B n : Z) (src old : list byte) (Q : machine_state -> Prop),
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 n ->
0 <= D -> D + n <= 2^63 -> 0 <= B -> B + n <= 2^63 -> 0 <= n < 2^40 ->
(B + n <= D \/ D + n <= B) ->
bytes_at asegs m B src -> length src = Z.to_nat n -> rw_cells asegs m D [CB (Z.to_nat n) old] ->
mem_inv asegs m ->
(forall (a1' a2' a3' a4' a5' a6' : word) m',
munch [(D, D + n)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' D [CB (Z.to_nat n) src] -> bytes_at asegs m' B src ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x752f0) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros -> -> -> HD HDn HS HSn Hn SEP SRC SRCL DST MI K.
pose proof (munch_refl [(D, D + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (LOLD : length old = Z.to_nat n) by (destruct DST as [[[Hwf _] _] _]; exact Hwf).
step.
destruct (Z.lt_ge_cases D B) as [HDS | HSD].
-
if_falsex.
step.
destruct (Z.eq_dec n 0) as [Hn0 | Hnz].
+ if_truex. step.
assert (Esrc : src = []) by (destruct src; [reflexivity | cbn in SRCL; lia]).
assert (Eold : old = []) by (destruct old; [reflexivity | cbn in LOLD; lia]).
subst src old. eapply K; [exact MU | exact WM | exact MI | exact DST | exact SRC].
+ if_falsex.
step. step.
try replace (n + D) with (D + n) by lia.

assert (FWD : forall (Kn : nat) (i di bi : Z) (x4 : word) mi,
Z.to_nat (n - i) = Kn -> 0 <= i < n -> di = D + i -> bi = B + i ->
munch [(D, D + n)] m mi -> wmono asegs m mi -> mem_inv asegs mi -> bytes_at asegs mi B src ->
rw_cells asegs mi D [CB (Z.to_nat n) (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) old)] ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 bi) (Z_to_bv 64 (D + n)) (Z_to_bv 64 di) x4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x75300) fc None mi (seg_rom asegs))).
{ clear MU WM MI SRC DST.
induction Kn as [|Kn IH]; intros i di bi x4 mi HK Hi -> -> MUi WMi MIi SRCi DSTi; [lia|].
assert (LCUR : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) old) = Z.to_nat n)
by (rewrite length_app, length_firstn, length_skipn; lia).
pose proof (nth_error_nth' src (Z.to_nat i) (Z_to_bv 8 0) ltac:(lia)) as NTH.
pose proof (u8ro_read asegs mi B src i _ (wa (B + i)) SRCi NTH ltac:(lia) eq_refl) as HR.
step. clear HR.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DSTi) as DA. clear DSTi.
pose proof (u8arr_store_ok asegs _ _ _ i (wa (D + i)) DA ltac:(rewrite LCUR; lia) eq_refl) as SOK.
step.
rewrite QZDE.le1_zxb.
pose proof (u8arr_write asegs _ _ _ i (nth (Z.to_nat i) src (Z_to_bv 8 0)) DA ltac:(rewrite LCUR; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DSTn. clear DA2. rewrite upd_length, LCUR in DSTn.

rewrite (skipn_cons_nth old (Z.to_nat i) (Z_to_bv 8 0)) in DSTn by lia.
rewrite (upd_at_prefix _ _ _ _ (Z.to_nat i)) in DSTn by (rewrite length_firstn; lia).
step. step.
step.
destruct (Z.eq_dec (i + 1) n) as [Hlast | Hmore].
* if_falsex. step. step.
eapply K; [exact MUi | exact WMi | exact MIi | | exact SRCi].
replace src with (firstn (Z.to_nat i) src ++ nth (Z.to_nat i) src (Z_to_bv 8 0) :: skipn (S (Z.to_nat i)) old) at 1; [exact DSTn|].
rewrite skipn_all2 by lia. rewrite <- (firstn_snoc_nth src (Z.to_nat i) (Z_to_bv 8 0)) by lia.
rewrite firstn_all2 by lia. reflexivity.
* if_truex.
eapply (IH (i + 1)); [lia | lia | lia | lia | exact MUi | exact WMi | exact MIi | exact SRCi |].
replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
rewrite (firstn_snoc_nth src (Z.to_nat i) (Z_to_bv 8 0)) by lia. rewrite <- app_assoc. cbn [app]. exact DSTn. }
eapply (FWD (Z.to_nat (n - 0)) 0); [lia | lia | lia | lia | exact MU | exact WM | exact MI | exact SRC | cbn [Z.to_nat firstn skipn app]; exact DST].
-
if_truex.
step.
destruct (Z.eq_dec B D) as [Heq | Hne].
+ if_truex. step.
assert (Hn0 : n = 0) by lia.
assert (Esrc : src = []) by (destruct src; [reflexivity | cbn in SRCL; lia]).
assert (Eold : old = []) by (destruct old; [reflexivity | cbn in LOLD; lia]).
subst src old. eapply K; [exact MU | exact WM | exact MI | exact DST | exact SRC].
+ if_falsex.
step.
destruct (Z.eq_dec n 0) as [Hn0 | Hnz].
* if_truex. step.
assert (Esrc : src = []) by (destruct src; [reflexivity | cbn in SRCL; lia]).
assert (Eold : old = []) by (destruct old; [reflexivity | cbn in LOLD; lia]).
subst src old. eapply K; [exact MU | exact WM | exact MI | exact DST | exact SRC].
* if_falsex.
step. step.
replace (n + -1) with (n - 1) by lia.

assert (BWD : forall (Kn : nat) (j : Z) (x4 x5 x6 : word) mi,
Z.to_nat j = Kn -> 0 <= j < n ->
munch [(D, D + n)] m mi -> wmono asegs m mi -> mem_inv asegs mi -> bytes_at asegs mi B src ->
rw_cells asegs mi D [CB (Z.to_nat n) (firstn (S (Z.to_nat j)) old ++ skipn (S (Z.to_nat j)) src)] ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 B) (Z_to_bv 64 1) (Z_to_bv 64 j) x4 x5 x6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x75328) fc None mi (seg_rom asegs))).
{ clear MU WM MI SRC DST.
induction Kn as [Kn IH] using lt_wf_ind; intros j x4 x5 x6 mi HK Hj MUi WMi MIi SRCi DSTi.
assert (LCUR : length (firstn (S (Z.to_nat j)) old ++ skipn (S (Z.to_nat j)) src) = Z.to_nat n)
by (rewrite length_app, length_firstn, length_skipn; lia).
pose proof (nth_error_nth' src (Z.to_nat j) (Z_to_bv 8 0) ltac:(lia)) as NTH.
pose proof (u8ro_read asegs mi B src j _ (wa (B + j)) SRCi NTH ltac:(lia) eq_refl) as HR.
step.
try replace (j + B) with (B + j) by lia.
step. clear HR.
step.
try replace (j + D) with (D + j) by lia.
step. step.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DSTi) as DA. clear DSTi.
pose proof (u8arr_store_ok asegs _ _ _ j (wa (D + j)) DA ltac:(rewrite LCUR; lia) eq_refl) as SOK.
step.
rewrite QZDE.le1_zxb.
pose proof (u8arr_write asegs _ _ _ j (nth (Z.to_nat j) src (Z_to_bv 8 0)) DA ltac:(rewrite LCUR; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DSTn. clear DA2. rewrite upd_length, LCUR in DSTn.

rewrite (firstn_snoc_nth old (Z.to_nat j) (Z_to_bv 8 0)) in DSTn by lia. rewrite <- app_assoc in DSTn. cbn [app] in DSTn.
rewrite (upd_at_prefix _ _ _ _ (Z.to_nat j)) in DSTn by (rewrite length_firstn; lia).
rewrite <- (skipn_cons_nth src (Z.to_nat j) (Z_to_bv 8 0)) in DSTn by lia.
step.
destruct (Z.eq_dec j 0) as [Hlast | Hmore].
-- if_falsex. step.
eapply K; [exact MUi | exact WMi | exact MIi | | exact SRCi].
subst j. cbn [Z.to_nat firstn skipn app] in DSTn. exact DSTn.
-- if_truex.
replace (j + -1) with (j - 1) by lia.
eapply (IH (Z.to_nat (j - 1)) ltac:(lia) (j - 1)); [lia | lia | exact MUi | exact WMi | exact MIi | exact SRCi |].
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. exact DSTn. }
eapply (BWD (Z.to_nat (n - 1)) (n - 1)); [lia | lia | exact MU | exact WM | exact MI | exact SRC |].
replace (S (Z.to_nat (n - 1))) with (Z.to_nat n) by lia.
rewrite firstn_all2 by lia. rewrite skipn_all2 by lia. rewrite app_nil_r. exact DST.
Qed.

Definition A_MEMMOVE_U : Z := 0x621f8.

Definition amemmove_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d s n lo : Z) (old src : list byte)
(Q : machine_state -> Prop),
(0 < n -> unpoisoned asegs m A_SB d n) -> (0 < n -> unpoisoned asegs m A_SB s n) -> asan_rt_ok m ->
0 <= d -> d + n <= 2^47 -> 0 <= s -> s + n <= 2^47 ->
(d + n <= lo \/ bv_unsigned sp <= d) -> (s + n <= lo \/ bv_unsigned sp <= s) ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n -> 0 <= n < 2^40 -> (n <= 64 \/ (app_mem d n /\ app_mem s n)) ->
(s + n <= d \/ d + n <= s) ->
rw_cells asegs m d [CB (Z.to_nat n) old] -> bytes_at asegs m s src -> length src = Z.to_nat n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) src] -> bytes_at asegs m' s src ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMMOVE_U) fc None m (seg_rom asegs)).

Section MuslAMemmove.

Lemma amemmove_sound_U : amemmove_spec_U.
Proof.
unfold amemmove_spec_U.
intros until Q. intros UPd0 UPs0 RT Hd0 Hd47 Hs0 Hs47 Hdlo Hslo Ha0 Ha1 Ha2 Hn Hsz Hdisj DST SRC SRCL ST LO LOS SPA MI RA K.
subst a0 a1 a2. unfold_consts. word_range sp SPR.
pose proof RT as RTC. unfold asan_rt_ok, a4_rt_cells, a4_rt_consts in RTC. cbn [app] in RTC.
apply Forall_cons_iff in RTC as [GOTF RTC]. apply Forall_cons_iff in RTC as [FLAG RTC].
cbn [fst snd] in GOTF, FLAG.
do 62 (apply Forall_cons_iff in RTC as [_ RTC]).
apply Forall_cons_iff in RTC as [GOT RTC]. apply Forall_cons_iff in RTC as [CELL _]. cbn [fst snd] in GOT, CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
apply ro_C8_of_bytes_at in GOTF. apply ro_C8_of_bytes_at in GOT. apply ro_C8_of_bytes_at in CELL.
assert (FLAGc : ro_cells asegs m 0xf2e99 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact FLAG]). clear FLAG.
stash SRC.
pose proof (munch_refl [(d, d + n); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
unfold A_MEMMOVE_U. carve_frame 64%nat ST.
do 11 step.
unstash SRC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SRC1 : bytes_at asegs mc s src)
by (eapply bytes_at_transport; [exact SRC | exact MU | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia])
end.
clear SRC.
do 4 step. if_false.
step. step. step. step.
rewrite (unsigned_lit s) by lia. rewrite (lxor_ones64 s) by lia. if_falsex.
step. step. step.

assert (TAIL2G : forall (xra x0 x1 x2 x3 x4 x5 x6 x7 w1 w2 w3 w5 w6 z3 z4 z5 z6 : word) (oldz : list byte) mz,
munch [(d, d + n); (lo, bv_unsigned sp)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
stk asegs mz lo (bv_unsigned sp + -64) ->
rw_cells asegs mz (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mz d [CB (Z.to_nat n) oldz] -> bytes_at asegs mz s src ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x0 x1 x2 sp w1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
x3 x4 x5 x6 x7 w2 w3 (Z_to_bv 64 (bv_unsigned sp + -2136)) w5 w6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
F (Z_to_bv 64 0x622d8) fc None mz (seg_rom asegs))).
{ intros xra x0 x1 x2 x3 x4 x5 x6 x7 w1 w2 w3 w5 w6 z3 z4 z5 z6 oldz mz MUz WMz MIz STz FRz DSTz SRCz.
clear GOTF GOT CELL FLAGc MU WM MU0 ST FR DST SRC1 MI.
step.
eapply internal_memmove_spec with (D := d) (B := s) (n := n);
[ reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | lia | exact Hdisj | exact SRCz | exact SRCL | exact DSTz | exact MIz | ].
intros y1 y2 y3 y4 y5 y6 m5 MU5 WM5 MI5 DST5 SRC5.
lazymatch type of MU5 with munch _ ?mc _ =>
transport_after_call asegs mc m5 MU5 WM5; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU5 WM5 end.
replace (ret_pc (Z_to_bv 64 0x622dc)) with (Z_to_bv 64 0x622dc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 11 step.
eapply K;
[ exact MUz | exact WMz | exact MI5 | exact DST5 | exact SRC5
| release_frame FRz STz (bv_unsigned sp); exact STz ]. }
destruct (Z.eq_dec n 0) as [Hn0 | Hnz].
{
clear UPd0 UPs0.
subst n. change (0 + -65) with (-65). if_true.
step. if_false. step.
step. step. rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. if_true.
step. if_false. step.
eapply TAIL2G; [exact MU | exact WM | exact MI | exact ST | exact FR | exact DST | exact SRC1]. }
destruct (Z.lt_ge_cases 64 n) as [Hbig | Hsmall].
{
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UPs1 : unpoisoned asegs mc A_SB s n)
by (eapply unpoisoned_transport; [exact (UPs0 ltac:(lia)) | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB s n); try eassumption; unfold A_SB; lia]);
assert (RT1 : asan_rt_ok mc)
by (eapply asan_rt_ok_transport; [exact RT | exact MU0 | intros cc Hcc2; pose proof (a4_rt_cells_in_img cc Hcc2); cbn; split; [left; lia | exact I]])
end.
destruct Hsz as [Hsz | [AMd AMs]]; [lia|].
if_truex.
step. if_truex.
do 5 step.
step.
stash SRC1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2144) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply region_is_poisoned_sound_U with (s := s) (n := n) (lo := lo);
[ exact UPs1 | exact RT1 | exact AMs | lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MI
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 MU2 WM2 MI2 ST1' UPs2 RT2.
assert (SRC2 : bytes_at asegs m2 s src)
by (unstash SRC1; eapply bytes_at_transport; [exact SRC1 | exact MU2 | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia]).
clear SRC1.
assert (UPd2 : unpoisoned asegs m2 A_SB d n).
{ eapply unpoisoned_transport; [exact (UPd0 ltac:(lia)) | | intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia].
eapply munch_trans; [exact MU0 | eapply munch_weaken; [| exact MU2]]. unfold sub_fp; cbn [outside]; intros; lia. }
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x62470)) with (Z_to_bv 64 0x62470) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 4 step.
step. if_true.
step. step. rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. if_truex.
step. if_truex.
do 4 step.
step.
stash SRC2.
eapply region_is_poisoned_sound_U with (s := d) (n := n) (lo := lo);
[ exact UPd2 | exact RT2 | exact AMd | lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1'
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MI2
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0' u1' u2' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' m3 MU3 WM3 MI3 ST1'' UPd3 RT3.
assert (SRC3 : bytes_at asegs m3 s src)
by (unstash SRC2; eapply bytes_at_transport; [exact SRC2 | exact MU3 | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia]).
clear SRC2.
lazymatch type of MU3 with munch _ ?mc _ =>
transport_after_call asegs mc m3 MU3 WM3; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU3 WM3 end.
replace (ret_pc (Z_to_bv 64 0x62510)) with (Z_to_bv 64 0x62510) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 4 step.
step. if_true.
eapply TAIL2G; [exact MU | exact WM | exact MI3 | eapply stk_merge; [exact ST1'' | exact ST2 | lia] | exact FR | exact DST | exact SRC3]. }

rewrite (size_test_n n) by lia. cbv iota.
assert (Hg : d / 8 <= (d + n - 1) / 8 <= d / 8 + 8) by (Z.div_mod_to_equations; lia).
assert (Hh : s / 8 <= (s + n - 1) / 8 <= s / 8 + 8) by (clear Hg; Z.div_mod_to_equations; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UPd1 : unpoisoned asegs mc A_SB d n)
by (eapply unpoisoned_transport; [exact (UPd0 ltac:(lia)) | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia]);
assert (UPs1 : unpoisoned asegs mc A_SB s n)
by (eapply unpoisoned_transport; [exact (UPs0 ltac:(lia)) | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB s n); try eassumption; unfold A_SB; lia])
end.
clear MU0.
destruct (unpoisoned_word asegs _ _ _ _ (d / 8 + A_SB) UPd1 ltac:(unfold A_SB; clear Hh; Z.div_mod_to_equations; lia)) as (w1 & Lw1 & W1c).
destruct (unpoisoned_word asegs _ _ _ _ ((d + n - 1) / 8 + A_SB) UPd1 ltac:(unfold A_SB; clear Hh; Z.div_mod_to_equations; lia)) as (w2 & Lw2 & W2c).
destruct (unpoisoned_word asegs _ _ _ _ (s / 8 + A_SB) UPs1 ltac:(unfold A_SB; clear Hg; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((s + n - 1) / 8 + A_SB) UPs1 ltac:(unfold A_SB; clear Hg; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in W1c, W2c, V1c, V2c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (GR0 : forall j, 0 <= j -> d / 8 + j < (d + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (d / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]);
[ intros j Hj Hjl; apply ov_read1_of_ro;
replace (d / 8 + 2147450880 + j) with ((d / 8 + j) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPd1); lia |];
assert (GS0 : forall j, 0 <= j -> s / 8 + j < (s + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (s / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]);
[ intros j Hj Hjl; apply ov_read1_of_ro;
replace (s / 8 + 2147450880 + j) with ((s / 8 + j) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPs1); lia |];
assert (HRLd : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (d + n - 1) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPd1) as (v & Hro & Hv); exists v; split; [| exact Hv]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro);
assert (HRLs : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((s + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (s + n - 1) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPs1) as (v & Hro & Hv); exists v; split; [| exact Hv]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro)
end.
clear UPd1 UPs1.
step. step. step.
try replace (n + s) with (s + n) by lia.
step. step. step.
replace (s + n + -1) with (s + n - 1) by lia.
step. step. step. step. step.
sh_norm.
replace (2147450880 + s / 8) with (s / 8 + 2147450880) by lia.
replace (2147450880 + (s + n - 1) / 8) with ((s + n - 1) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (s / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((s + n - 1) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TAIL2 : forall x3 x4 x5 x6 x7 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) x3 x4 x5 x6 x7
s2 (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (bv_unsigned sp + -2136)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x622d8) fc None mc (seg_rom asegs)))
by (intros x3 x4 x5 x6 x7; eapply TAIL2G; [exact MU | exact WM | exact MI | exact ST | exact FR | exact DST | exact SRC1])
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP2 : forall (Kn : nat) (i : Z) (x6 x7 : word),
Z.to_nat ((d + n - 1) / 8 - d / 8 - i) = Kn -> 0 <= i -> d / 8 + i < (d + n - 1) / 8 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 (d / 8 + 2147450880 + i)) (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) (Z_to_bv 64 0) x6 x7
s2 (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (bv_unsigned sp + -2136)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x624e4) fc None mc (seg_rom asegs)))
end.
{ clear GS0 GOTF FLAGc GOT CELL Hh HRLd HRLs;
induction Kn as [|Kn IH]; intros i x6 x7 HK Hi Hig; [lia|];
pose proof (GR0 i Hi Hig) as HR;
step; rewrite ?zxb_zero; clear HR;
step; step; rewrite ?(unsigned_lit 0) by lia; change (Z.lor 0 0) with 0;
step;
destruct (Z.eq_dec (d / 8 + i + 1) ((d + n - 1) / 8)) as [Heq|Hne];
[ if_falsex; step; step; if_true; apply TAIL2
| if_truex; replace (d / 8 + 2147450880 + i + 1) with (d / 8 + 2147450880 + (i + 1)) by lia; apply (IH (i + 1)); lia ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (MID : forall x3 x4 x5 x6 x7 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) x3 x4 x5 x6 x7
s2 (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (bv_unsigned sp + -2136)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6228c) fc None mc (seg_rom asegs)))
end.
{ intros x3 x4 x5 x6 x7;
clear V1c V2c GS0 GOTF FLAGc Hh HRLs;
step; step; rewrite (unsigned_lit d) by lia; rewrite (lxor_ones64 d) by lia; if_falsex;
step; step; rewrite (size_test_n n) by lia; cbv iota;
step; step; step;
try replace (n + d) with (d + n) by lia;
step; step; step;
replace (d + n + -1) with (d + n - 1) by lia;
step; step; step; step; step;
sh_norm;
replace (2147450880 + d / 8) with (d / 8 + 2147450880) by lia;
replace (2147450880 + (d + n - 1) / 8) with ((d + n - 1) / 8 + 2147450880) by lia;
rewrite (unsigned_lit (d / 8 + 2147450880)) by lia; rewrite (unsigned_lit ((d + n - 1) / 8 + 2147450880)) by lia;
rewrite !land_m8_64 by lia;
do 2 step; step; step;
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end;
[
destruct HRLd as (v & HR & Hv);
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia);
step; rewrite (sxb_small v) by lia; clear HR;
step; rewrite (unsigned_lit (d + n - 1)) by lia; rewrite land7_mod8 by lia;
step; step; step; step;
destruct Hv as [-> | (Hk & Hlast)];
[ rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia);
rewrite (unsigned_lit 0) by lia; rewrite Z.land_0_l
| rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 v)) by (rewrite !unsigned_lit by lia; lia);
rewrite (v_slt_1 (Z_to_bv 64 ((d + n - 1) mod 8)) (Z_to_bv 64 v)) by (rewrite !signed_lit by lia; try clear Hg; try clear Hh; Z.div_mod_to_equations; lia);
rewrite !(unsigned_lit 1) by lia; change (Z.lxor 1 1) with 0; rewrite Z.land_0_r ];
(step;
destruct (Z.eq_dec (d / 8) ((d + n - 1) / 8)) as [Heq1|Hne1];
[ if_truex; step; step; if_true; apply TAIL2
| if_falsex; replace (d / 8 + 2147450880) with (d / 8 + 2147450880 + 0) by lia;
apply (LOOP2 (Z.to_nat ((d + n - 1) / 8 - d / 8 - 0)) 0); lia ])
|  apply TAIL2 ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP1 : forall (Kn : nat) (i : Z) (x6 x7 : word),
Z.to_nat ((s + n - 1) / 8 - s / 8 - i) = Kn -> 0 <= i -> s / 8 + i < (s + n - 1) / 8 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 (s / 8 + 2147450880 + i)) (Z_to_bv 64 ((s + n - 1) / 8 + 2147450880)) (Z_to_bv 64 0) x6 x7
s2 (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (bv_unsigned sp + -2136)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x62440) fc None mc (seg_rom asegs)))
end.
{ clear W1c W2c V1c V2c GR0 GOTF FLAGc GOT CELL Hg TAIL2 LOOP2 HRLd HRLs;
induction Kn as [|Kn IH]; intros i x6 x7 HK Hi Hig; [lia|];
pose proof (GS0 i Hi Hig) as HR;
step; rewrite ?zxb_zero; clear HR;
step; step; rewrite ?(unsigned_lit 0) by lia; change (Z.lor 0 0) with 0;
step;
destruct (Z.eq_dec (s / 8 + i + 1) ((s + n - 1) / 8)) as [Heq|Hne];
[ if_falsex; step; step; if_true; apply MID
| if_truex; replace (s / 8 + 2147450880 + i + 1) with (s / 8 + 2147450880 + (i + 1)) by lia; apply (IH (i + 1)); lia ]. }

clear W1c W2c GR0 GOTF FLAGc Hg TAIL2 LOOP2 HRLd.
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
-
destruct HRLs as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
step. rewrite (sxb_small v) by lia. clear HR.
step. rewrite (unsigned_lit (s + n - 1)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
+ rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (s / 8) ((s + n - 1) / 8)) as [Heq1|Hne1].
* if_truex. step. step. if_true. apply MID.
* if_falsex. replace (s / 8 + 2147450880) with (s / 8 + 2147450880 + 0) by lia.
apply (LOOP1 (Z.to_nat ((s + n - 1) / 8 - s / 8 - 0)) 0); lia.
+ rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 v)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((s + n - 1) mod 8)) (Z_to_bv 64 v)) by (rewrite !signed_lit by lia; try clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (s / 8) ((s + n - 1) / 8)) as [Heq1|Hne1].
* if_truex. step. step. if_true. apply MID.
* if_falsex. replace (s / 8 + 2147450880) with (s / 8 + 2147450880 + 0) by lia.
apply (LOOP1 (Z.to_nat ((s + n - 1) / 8 - s / 8 - 0)) 0); lia.
-  apply MID.
Qed.
End MuslAMemmove.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition amemmove_any_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (ab nb d sb nsb s n lo : Z) (old src : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (ab, nb) LB -> ab <= d -> d + n <= ab + nb ->
In (sb, nsb) LB -> sb <= s -> s + n <= sb + nsb ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n -> 0 <= n < 2^40 -> (s + n <= d \/ d + n <= s) ->
rw_cells asegs m d [CB (Z.to_nat n) old] -> bytes_at asegs m s src -> length src = Z.to_nat n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) src] -> bytes_at asegs m' s src ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMMOVE_U) fc None m (seg_rom asegs)).

End WithIface.
End RC__1.
