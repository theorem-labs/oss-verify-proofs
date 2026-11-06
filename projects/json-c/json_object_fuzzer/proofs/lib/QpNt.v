(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Qfw3_c1 Q5Rg Qc3B QCcH Qsw7 QJjn QRUw QBGG QoBT Q7T7 Q7UD Qwm6 QlKV QsKa Qw5U Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes Qfw3_c1.Mq2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg Qc3B.
Import QCcH Qsw7 QJjn QRUw.
Import QBGG.
Import QoBT Q7T7.
Import Q7UD Qwm6.
Import Qwm6.Mq0 QlKV.Mqa.

Import Qw5U.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
Ltac litn := fold_closed_in_goal.
Ltac freg H :=
lazymatch type of H with Sem.reg_get ?F ?k = ?v =>
match goal with |- context [Sem.reg_get F ?k'] =>
replace (Sem.reg_get F k') with v by (symmetry; exact H) end
end.
Ltac solve_fsaved :=
let k := fresh "k" in let Hk := fresh "Hk" in
intros k Hk; cbn [FSAVED In] in Hk;
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk];
repeat (first [ rewrite freg_get_other by (vm_compute; reflexivity)
| rewrite freg_get_same by (vm_compute; reflexivity) ]);
reflexivity.

Lemma neq_wz : forall x y, 0 <= x < 2^64 -> -2^64 <= y < 2^64 -> x <> y -> x <> y + 2^64 ->
bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
intros x y Hx Hy N1 N2. unfold bv_eqb. apply Z.eqb_neq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2^64). rewrite (Z.mod_small x) by lia.
destruct (Z.lt_ge_cases y 0).
- replace y with ((y + 2^64) + (-1) * 2^64) at 1 by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia.
Qed.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section ACfp.
Definition cfp_pb1 := Eval vm_compute in match image_bytes asegs 0x10328 8 with Some bs => bs | None => [] end.
Definition cfp_pb2 := Eval vm_compute in match image_bytes asegs 0x103b8 8 with Some bs => bs | None => [] end.
Definition cfp_pb3 := Eval vm_compute in match image_bytes asegs 0x10330 8 with Some bs => bs | None => [] end.
Lemma cfp_ro_A : forall m, mem_inv asegs m ->
ro_cells asegs m 0x10328 [CB 8 cfp_pb1] /\ ro_cells asegs m 0x103b8 [CB 8 cfp_pb2] /\ ro_cells asegs m 0x10330 [CB 8 cfp_pb3].
Proof.
intros m MI. split; [|split].
- change 8%nat with (length cfp_pb1). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length cfp_pb1)) with 8%Z. lia.
- change 8%nat with (length cfp_pb2). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length cfp_pb2)) with 8%Z. lia.
- change 8%nat with (length cfp_pb3). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length cfp_pb3)) with 8%Z. lia.
Qed.
Lemma cfp_A : cfp_A_stmt 0x928d4.
Proof.
unfold cfp_A_stmt. intros until data. intros A0 RT FDP UNP PAL SRC LEN PTR0 UND ST LO LOS SPP P47 DLO MI F10 F11 FRM. subst a0.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR.
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (munch_refl (fdp_WSA 16 (bv_unsigned sp) P) m) as MU. unfold fdp_WSA in MU.
pose proof (wmono_refl asegs m) as WM.
destruct (cfp_ro_A m MI) as (RO1 & RO2 & RO3).
pose proof RT as RTC. unfold asan_rt_ok, a4_rt_cells in RTC. apply Forall_app in RTC as [_ RTC].
apply Forall_cons_iff in RTC as [GOT RTC]. apply Forall_cons_iff in RTC as [CELL _]. cbn [fst snd] in GOT, CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
apply QsKa.Mq1.ro_C8_of_bytes_at in GOT. apply QsKa.Mq1.ro_C8_of_bytes_at in CELL.
assert (WAPP : Forall (fun iv : Z * Z => snd iv <= A_SB \/ A_HMB <= fst iv) [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)]).
{ unfold A_SB, A_HMB. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
assert (EV : forall mc, munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)] m mc ->
ro_cells asegs mc (P / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\ ro_cells asegs mc ((P + 8) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\
(0 < rem -> unpoisoned asegs mc A_SB ptr rem)).
{ intros mc MUc.
assert (UP : unpoisoned asegs mc A_SB P 16) by (eapply unpoisoned_keep; [exact UNP | exact MUc | lia | lia | exact WAPP]).
split; [apply (unpoisoned_al8_ro mc P 16 P UP); lia|]. split; [apply (unpoisoned_al8_ro mc P 16 (P + 8) UP); [lia | lia | clear - PAL; Z.div_mod_to_equations; lia]|].
intros Hr. eapply unpoisoned_keep; [exact (UND Hr) | exact MUc | lia | lia | exact WAPP]. }
carve_frame 16%nat ST.
step. step.
step. freg F10. freg F11. litn. step. if_lit.
step. step. step. step. step.
step. freg F10. step. freg F11. step. step. step. if_lit.
step. step. freg F10. step. if_lit. step. freg F11. step. if_lit.
destruct (EV _ MU) as (SHP & SHP8 & UNDc).
step. step. sh_norm. step. rewrite ?zxb_zero. step. if_false.
step. step. step. step. freg F11. step. freg F10. step.
step.
assert (TAIL : forall (mc : word -> option byte) (F' : bvmap 5 word) (fcX : bv 32) (xt0 xt1 xt2 xa2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (rem1 : Z),
Qc3B.frm0 fcX -> fsaved F F' ->
rw_cells asegs mc (bv_unsigned sp + -16) [CB 8 (firstn 8 junk); C8 ra] ->
stk asegs mc lo (bv_unsigned sp + -16) ->
rw_cells asegs mc P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem1)] ->
bytes_at asegs mc ptr data -> rem1 = Z.max (rem - 1) 0 ->
munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
ro_cells asegs mc 66352 [CB 8 cfp_pb3] ->
evt asegs (fdp_postFA 16 9 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp xt0 xt1 xt2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) xa2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (P / 8)) xa5 xa6 xa7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F' (Z_to_bv 64 0x929a4) fcX None mc (seg_rom asegs))).
{ intros mc F' fcX xt0 xt1 xt2 xa2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 rem1 FRMX FS FRc STc FDPc SRCc Hrem1 MUc WMc MIc RO3c.
clear FR ST FDP SRC MU WM MI RO1 RO2 RO3 SHP SHP8 UNDc GOT CELL.
assert (EXITF : forall (mc2 : word -> option byte) (acc ya0 ya2 ya7 yt0 yt1 yt2 yt3 yt4 : word) (ya4 ya6 : word) (c : Z),
rw_cells asegs mc2 (bv_unsigned sp + -16) [CB 8 (firstn 8 junk); C8 ra] ->
stk asegs mc2 lo (bv_unsigned sp + -16) ->
rw_cells asegs mc2 P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 c)] ->
bytes_at asegs mc2 ptr data -> c = Z.max (rem - 9) 0 ->
munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)] m mc2 -> wmono asegs m mc2 -> mem_inv asegs mc2 ->
ro_cells asegs mc2 66352 [CB 8 cfp_pb3] ->
evt asegs (fdp_postFA 16 9 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp yt0 yt1 yt2 s0 s1 ya0 (Z_to_bv 64 (P + 8)) ya2 (Z_to_bv 64 2147450880) ya4 acc ya6 ya7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 xt5 xt6)
F' (Z_to_bv 64 0x92a2c) fcX None mc2 (seg_rom asegs))).
{ intros mc2 acc ya0 ya2 ya7 yt0 yt1 yt2 yt3 yt4 ya4 ya6 c FR2 ST2 FDP2 SRC2 Hc MU2 WM2 MI2 RO32.
clear FRc STc FDPc SRCc MUc WMc MIc RO3c.
step. step. step. step. step. step. step. step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame H ST2 (bv_unsigned sp) end.
finish.
- intros k Hk. pose proof (FS k Hk) as E. cbn [FSAVED In] in Hk.
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk];
repeat (first [ rewrite freg_get_other by (vm_compute; reflexivity) | rewrite freg_get_same by (vm_compute; reflexivity) ]); exact E.
- rewrite <- Hc. exact FDP2. }
pose proof (bytes_at_bound _ _ _ _ SRCc) as DBc.
assert (R1 : 0 <= rem1 <= rem) by lia.
destruct (EV _ MUc) as (_ & SHP8t & _).
step. step. sh_norm. step. rewrite ?zxb_zero. step. if_false. clear SHP8t.
step. step. step. step. step. step. step.
assert (LOOPI : forall (fuel : nat) (i : Z) (mc2 : word -> option byte) (acc ya2 yt3 yt4 : word),
8 - i <= Z.of_nat fuel -> 0 <= i <= 7 -> i <= rem1 ->
rw_cells asegs mc2 (bv_unsigned sp + -16) [CB 8 (firstn 8 junk); C8 ra] ->
stk asegs mc2 lo (bv_unsigned sp + -16) ->
rw_cells asegs mc2 P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (rem1 - i))] ->
bytes_at asegs mc2 ptr data ->
munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)] m mc2 -> wmono asegs m mc2 -> mem_inv asegs mc2 ->
ro_cells asegs mc2 66352 [CB 8 cfp_pb3] ->
evt asegs (fdp_postFA 16 9 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (-1)) (Z_to_bv 64 (rem1 - i + -1)) (Z_to_bv 64 56) s0 s1
(Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) ya2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (P / 8 + 2147450880)) acc (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) (Z_to_bv 64 (8 * i + -8))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 xt5 xt6)
F' (Z_to_bv 64 0x929d0) fcX None mc2 (seg_rom asegs))).
{ induction fuel as [|fuel IH]; intros i mc2 acc ya2 yt3 yt4 Hfuel Hi Hir FR2 ST2 FDP2 SRC2 MU2 WM2 MI2 RO32; [exfalso; lia|].
clear FRc STc FDPc SRCc MUc WMc MIc RO3c.
step.
destruct (Z.eq_dec (rem1 - i) 0) as [E0 | N0].
{ replace (rem1 - i + -1) with (-1) by lia. if_true.
eapply EXITF with (c := rem1 - i); [exact FR2 | exact ST2 | exact FDP2 | exact SRC2 | lia | exact MU2 | exact WM2 | exact MI2 | exact RO32]. }
lazymatch goal with |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (neq_wz x y) by lia end. cbv beta iota.
destruct (EV _ MU2) as (_ & SHP8i & _).
step. rewrite ?zxb_zero. step. if_false. clear SHP8i.
step.
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (EV _ MUc) as (SHPj & _ & UNDj);
destruct (unpoisoned_byte_ro mc ptr rem (ptr + (rem1 - i + -1)) (UNDj ltac:(lia)) ltac:(lia)) as (v1 & SHK & Hv1) end.
step. rewrite ?zxb_zero. step. if_false.
step. step.
destruct (nth_error data (Z.to_nat (rem1 - i - 1))) as [b1|] eqn:Hb1; [| exfalso; apply nth_error_None in Hb1; lia].
pose proof (bv_unsigned_in_range 8 b1) as BR1. unfold bv_modulus in BR1. cbn in BR1.
step. step. sh_norm. step. step.
assert (B70C : forall (zt3 zt4 : word),
evt asegs (fdp_postFA 16 9 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (-1)) (Z_to_bv 64 (rem1 - i + -1)) (Z_to_bv 64 56) s0 s1
(Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 (ptr + (rem1 - i + -1))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (P / 8 + 2147450880)) acc (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) (Z_to_bv 64 (8 * i + -8))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 zt3 zt4 xt5 xt6)
F' (Z_to_bv 64 0x92a00) fcX None m1 (seg_rom asegs))).
2:{ destruct Hv1 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply B70C.
- rewrite (QsKa.Mq1.sxb_small v1) by lia. if_truex. step. step.
rewrite (unsigned_lit (ptr + (rem1 - i + -1))) by lia. rewrite QsKa.Mq1.land7_mod8 by lia. if_truex. apply B70C. }
intros zt3 zt4. clear SHK v1 Hv1 SHPj UNDj.
lazymatch goal with H : bytes_at asegs ?mx ptr data |- _ => pose proof (u8ro_read asegs mx ptr data (rem1 - i - 1) b1 _ H Hb1 ltac:(lia) eq_refl) as RD1 end.
replace (ptr + (rem1 - i - 1)) with (ptr + (rem1 - i + -1)) in RD1 by lia.
step. clear RD1.
step. step. step. step.
step.
lazymatch goal with H : rw_cells asegs ?mx P _ |- _ => rename H into FDP3 end.
destruct (Z.eq_dec i 7) as [I7 | IN7].
- subst i. if_falsex. step.
eapply EXITF with (c := rem1 - 7 + -1); [eassumption | eassumption | exact FDP3 | eassumption | lia | eassumption | eassumption | eassumption | eassumption].
- if_truex.
replace (rem1 - i + -2) with (rem1 - (i + 1) + -1) by lia.
replace (8 * i) with (8 * (i + 1) + -8) by lia.
replace (rem1 - i + -1) with (rem1 - (i + 1)) in FDP3 by lia.
eapply (IH (i + 1)); [lia | lia | lia | eassumption | eassumption | exact FDP3 | eassumption | eassumption | eassumption | eassumption | eassumption]. }
replace (rem1 + -1) with (rem1 - 0 + -1) by lia.
replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 (8 * 0 + -8)) by reflexivity.
replace (Z_to_bv 64 rem1) with (Z_to_bv 64 (rem1 - 0)) in FDPc by (rewrite Z.sub_0_r; reflexivity).
eapply (LOOPI 8%nat 0); [lia | lia | lia | exact FRc | exact STc | exact FDPc | exact SRCc | exact MUc | exact WMc | exact MIc | exact RO3c]. }
destruct (Z.eq_dec rem 0) as [Rz | Rnz].
-
rewrite Rz in *. if_truex. fold_mkR.
eapply TAIL with (rem1 := 0); try eassumption; [solve_fsaved | reflexivity].
- if_falsex.
step. rewrite ?zxb_zero. step. if_false. clear SHP SHP8 UNDc.
step. step.
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (EV _ MUc) as (SHPj & _ & UNDj);
destruct (unpoisoned_byte_ro mc ptr rem (ptr + (rem + -1)) (UNDj ltac:(lia)) ltac:(lia)) as (v1 & SHK & Hv1) end.
step. step. rewrite ?zxb_zero. step. if_false.
step. step.
destruct (nth_error data (Z.to_nat (rem - 1))) as [bb|] eqn:Hbb; [| exfalso; apply nth_error_None in Hbb; lia].
pose proof (bv_unsigned_in_range 8 bb) as BRb. unfold bv_modulus in BRb. cbn in BRb.
step. step. sh_norm. step. step.
lazymatch goal with |- evt _ ?Q (MS _ ?FF _ ?fcc _ ?mm _) =>
assert (B68C : forall (za5 za6 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 (ptr + (rem + -1)))
(Z_to_bv 64 2147450880) (Z_to_bv 64 (P / 8)) za5 za6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FF (Z_to_bv 64 0x92980) fcc None mm (seg_rom asegs))) end.
2:{ destruct Hv1 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply B68C.
- rewrite (QsKa.Mq1.sxb_small v1) by lia. if_truex. step. step.
rewrite (unsigned_lit (ptr + (rem + -1))) by lia. rewrite QsKa.Mq1.land7_mod8 by lia. if_truex. apply B68C. }
intros za5 za6. clear SHK v1 Hv1 SHPj UNDj.
lazymatch goal with H : bytes_at asegs ?mx ptr data |- _ => pose proof (u8ro_read asegs mx ptr data (rem - 1) bb _ H Hbb ltac:(lia) eq_refl) as RD0 end.
replace (ptr + (rem - 1)) with (ptr + (rem + -1)) in RD0 by lia.
step. clear RD0. step. step.
match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
+ step. step. fold_mkR.
eapply TAIL with (rem1 := rem + -1); try eassumption; [solve_fsaved | lia].
+ step. step. step. fold_mkR.
eapply TAIL with (rem1 := rem + -1); try eassumption; [solve_fsaved | lia].
Qed.
End ACfp.
End RC__1.
End Mq0.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH QHnV QfLs Q0Ek QjDH Qhd4 Q9O6 QnPO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn.
Import Q7UD Qhd4.
Import Qwm6.Mq0 QlKV.Mq2 QsKa Q9O6 Q9O6.Mq2 QnPO.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section WithSegs.
Variable segs : list Segment.

Lemma agree_of_munchX : forall BS W m m',
munch W m m' -> wmono segs m m' -> (forall a k x, In (a, k) BS -> a <= x < a + k -> outside W x) -> agree_on segs BS m m'.
Proof.
intros BS W m m' MU WM HO x Hx (b & Hb & Hr). destruct b as [a k]. cbn in Hr. split.
- apply MU. rewrite wa_unsigned by lia. exact (HO a k x Hb Hr).
- apply WM.
Qed.

Lemma hdr_set_pb : forall m m' p (c1 c2 c3 c5 c6 : cell) (pb0 pb : Z) cs,
csize c1 = 4%nat -> csize c2 = 4%nat -> csize c3 = 8%nat ->
rw_cells segs m p ([c1; c2; c3; C8 (wz pb0); c5; c6] ++ cs) ->
munch [(p + 16, p + 24)] m m' -> wmono segs m m' -> rw_cells segs m' (p + 16) [C8 (wz pb)] ->
rw_cells segs m' p ([c1; c2; c3; C8 (wz pb); c5; c6] ++ cs).
Proof.
intros m m' p c1 c2 c3 c5 c6 pb0 pb cs S1 S2 S3 H MU WM H16.
apply (proj1 (rw_cells_app segs m p [c1; c2; c3] _)) in H as [HA H]. cbn [cells_size Nat.add] in H. rewrite S1, S2, S3 in H. cbn in H.
apply (proj1 (rw_cells_app segs m (p + Z.of_nat 16) [C8 (wz pb0)] _)) in H as [_ HB]. cbn [cells_size csize Nat.add] in HB.
apply (proj2 (rw_cells_app segs m' p [c1; c2; c3] _)). split.
- eapply rw_cells_transport; [exact HA | exact MU | exact WM | cbn [cells_size Nat.add disjoint_from]; rewrite S1, S2, S3; cbn; lia].
- cbn [cells_size Nat.add]. rewrite S1, S2, S3. change (4 + (4 + (8 + 0)))%nat with 16%nat.
apply (proj2 (rw_cells_app segs m' (p + Z.of_nat 16) [C8 (wz pb)] _)). split.
+ replace (p + Z.of_nat 16) with (p + 16) by lia. exact H16.
+ cbn [cells_size csize Nat.add]. eapply rw_cells_transport; [exact HB | exact MU | exact WM | cbn [disjoint_from]; lia].
Qed.

Section Node.
Variable fn : fnaddrs.
Lemma jnode_agree : forall s m m' BS REST p rc pb0,
jnode segs fn s m REST p rc pb0 -> agree_on segs BS m m' -> incl REST BS -> jnode segs fn s m' REST p rc pb0.
Proof.
intros s m m' BS REST p rc pb0 J AG Hi. destruct s as [|[|]| |[|]|kids|kids]; cbn in J |- *.
- destruct J as (b & junk & ER & H). exists b, junk. split; [exact ER|].
eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
- destruct J as (bits & ud & udn & uds & ER & HU & H & HC). exists bits, ud, udn, uds. split; [exact ER|]. split; [exact HU|]. split.
+ eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
+ eapply cstr_agree; [exact HC | exact AG | apply Hi; rewrite ER; right; left; reflexivity | destruct HC as (HC1 & _); lia].
- destruct J as (bits & ER & HS & H). exists bits. split; [exact ER|]. split; [exact HS|].
eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
- destruct J as (cty & v & junk & ER & HC & H). exists cty, v, junk. split; [exact ER|]. split; [exact HC|].
eapply rw_cells_agree; [exact H | exact AG | exists p, 56; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
- destruct J as (len & pd & pdn & str & junk2 & ER & HL & HS & HP & H & HD).
exists len, pd, pdn, str, junk2. split; [exact ER|]. split; [exact HL|]. split; [exact HS|]. split; [exact HP|]. split.
+ eapply rw_cells_agree; [exact H | exact AG | exists p, 56; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
+ eapply rw_cells_agree; [exact HD | exact AG | exists pd, pdn; split; [apply Hi; rewrite ER; right; left; reflexivity |]].
destruct HD as [[Hwf _] _]. cbn in Hwf. cbn [cells_size csize]. lia.
- destruct J as (len & str & junk & ER & HL & HS & H). exists len, str, junk. split; [exact ER|]. split; [exact HL|]. split; [exact HS|].
eapply rw_cells_agree; [exact H | exact AG | exists p, (str_objsize len); split; [apply Hi; rewrite ER; left; reflexivity |]].
cbn [cells_size csize]. unfold str_objsize. lia.
- destruct J as (t & TBS & kvs & KBS & ER & H & HT & L1 & L2 & KIDS). exists t, TBS, kvs, KBS.
split; [exact ER|]. split; [|split; [|split; [exact L1 | split; [exact L2|]]]].
+ eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
+ eapply lhtab2_agree; [exact HT | exact AG | intros b Hb; apply Hi; rewrite ER; right; apply in_or_app; left; exact Hb].
+ eapply (kids_okv_agree segs fn); [exact KIDS | exact AG | intros b Hb; apply Hi; rewrite ER; right; apply in_or_app; right; exact Hb].
- destruct J as (a & ABS & ps & KBS & ER & H & HA & L1 & L2 & KIDS). exists a, ABS, ps, KBS.
split; [exact ER|]. split; [|split; [|split; [exact L1 | split; [exact L2|]]]].
+ eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
+ eapply alist_agree; [exact HA | exact AG | intros b Hb; apply Hi; rewrite ER; right; apply in_or_app; left; exact Hb].
+ eapply (kids_okp_agree segs fn); [exact KIDS | exact AG | intros b Hb; apply Hi; rewrite ER; right; apply in_or_app; right; exact Hb].
Qed.

Lemma jnode_set_pb : forall s m m' REST p rc pb0 pb,
jnode segs fn s m REST p rc pb0 ->
munch [(p + 16, p + 24)] m m' -> wmono segs m m' -> rw_cells segs m' (p + 16) [C8 (wz pb)] ->
(forall a k, In (a, k) (tl REST) -> a + k <= p + 16 \/ p + 24 <= a) ->
jnode segs fn s m' REST p rc pb.
Proof.
intros s m m' REST p rc pb0 pb J MU WM H16 DISJ.
assert (AGx : forall rest, (forall a k, In (a, k) rest -> a + k <= p + 16 \/ p + 24 <= a) -> agree_on segs rest m m').
{ intros rest D. eapply agree_of_munchX; [exact MU | exact WM |]. intros a k x Hin Hx. cbn. pose proof (D a k Hin). lia. }
destruct s as [|[|]| |[|]|kids|kids]; cbn in J |- *; unfold jhdr_cells in *.
- destruct J as (b & junk & ER & H). exists b, junk. split; [exact ER|]. cbn [app] in H |- *.
eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_; _]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
- destruct J as (bits & ud & udn & uds & ER & HU & H & HC). exists bits, ud, udn, uds. split; [exact ER|]. split; [exact HU|]. rewrite ER in DISJ. cbn [tl] in DISJ. split.
+ eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
+ eapply cstr_agree; [exact HC | apply (AGx _ DISJ) | left; reflexivity | destruct HC as (HC1 & _); lia].
- destruct J as (bits & ER & HS & H). exists bits. split; [exact ER|]. split; [exact HS|].
eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
- destruct J as (cty & v & junk & ER & HC & H). exists cty, v, junk. split; [exact ER|]. split; [exact HC|].
eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_; _; _]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
- destruct J as (len & pd & pdn & str & junk2 & ER & HL & HS & HP & H & HD). rewrite ER in DISJ. cbn [tl] in DISJ.
exists len, pd, pdn, str, junk2. split; [exact ER|]. split; [exact HL|]. split; [exact HS|]. split; [exact HP|]. split.
+ eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_; _]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
+ eapply rw_cells_agree; [exact HD | apply (AGx _ DISJ) | exists pd, pdn; split; [left; reflexivity|]].
destruct HD as [[Hwf _] _]. cbn in Hwf. cbn [cells_size csize]. lia.
- destruct J as (len & str & junk & ER & HL & HS & H). exists len, str, junk. split; [exact ER|]. split; [exact HL|]. split; [exact HS|].
eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_; _]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
- destruct J as (t & TBS & kvs & KBS & ER & H & HT & L1 & L2 & KIDS). exists t, TBS, kvs, KBS. rewrite ER in DISJ. cbn [tl] in DISJ.
split; [exact ER|]. split; [|split; [|split; [exact L1 | split; [exact L2|]]]].
+ eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
+ eapply lhtab2_agree; [exact HT | apply (AGx _ DISJ) | intros b Hb; apply in_or_app; left; exact Hb].
+ eapply (kids_okv_agree segs fn); [exact KIDS | apply (AGx _ DISJ) | intros b Hb; apply in_or_app; right; exact Hb].
- destruct J as (a & ABS & ps & KBS & ER & H & HA & L1 & L2 & KIDS). exists a, ABS, ps, KBS. rewrite ER in DISJ. cbn [tl] in DISJ.
split; [exact ER|]. split; [|split; [|split; [exact L1 | split; [exact L2|]]]].
+ eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
+ eapply alist_agree; [exact HA | apply (AGx _ DISJ) | intros b Hb; apply in_or_app; left; exact Hb].
+ eapply (kids_okp_agree segs fn); [exact KIDS | apply (AGx _ DISJ) | intros b Hb; apply in_or_app; right; exact Hb].
Qed.
End Node.

Definition jty (s : jshape) : Z :=
match s with Sbool => JT_BOOLEAN | Sdouble _ => JT_DOUBLE | Sint => JT_INT | Sstr _ => JT_STRING | Sobj _ => JT_OBJECT | Sarr _ => JT_ARRAY end.

Lemma jty_range : forall s, 0 <= jty s <= 6.
Proof. destruct s; cbn; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY; lia. Qed.

Lemma jnode_hdrT : forall fn s m REST p rc pb0, jnode segs fn s m REST p rc pb0 ->
exists n udel ud cs rest, REST = (p, n) :: rest /\ 48 <= n /\
rw_cells segs m p ([C4 (wz (jty s)); C4 (wz rc); C8 (wz (fn_ofF fn s)); C8 (wz pb0); C8 (wz udel); C8 (wz ud)] ++ cs).
Proof.
intros fn s m REST p rc pb0 J. destruct s as [|[|]| |[|]|kids|kids]; cbn in J.
- destruct J as (b & junk & -> & H). exists 48, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (bits & ud & udn & uds & -> & _ & H & _). exists 48, (fn_free_userdata fn), ud. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (bits & -> & _ & H). exists 48, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (cty & v & junk & -> & _ & H). exists 56, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (len & pd & pdn & str & junk2 & -> & _ & _ & _ & H & _). exists 56, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (len & str & junk & -> & Hl & _ & H). exists (str_objsize len), 0, 0. eexists. exists []. split; [reflexivity|]. split; [unfold str_objsize; lia|]. exact H.
- destruct J as (t & TBS & kvs & KBS & -> & H & _). exists 48, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (a & ABS & ps & KBS & -> & H & _). exists 48, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
Qed.

Lemma jnode_length_ge : forall fn s m REST p rc pb0, jnode segs fn s m REST p rc pb0 -> nblk0 s <= Z.of_nat (length REST).
Proof.
intros fn s m REST p rc pb0 J. destruct s as [|[|]| |[|]|kids|kids]; cbn [jnode] in J.
- destruct J as (b & junk & -> & _). cbn [length nblk0]. lia.
- destruct J as (bits & ud & udn & uds & -> & _). cbn [length nblk0]. lia.
- destruct J as (bits & -> & _). cbn [length nblk0]. lia.
- destruct J as (cty & v & junk & -> & _). cbn [length nblk0]. lia.
- destruct J as (len & pd & pdn & str & junk2 & -> & _). cbn [length nblk0]. lia.
- destruct J as (len & str & junk & -> & _). cbn [length nblk0]. lia.
- destruct J as (t & TBS & kvs & KBS & -> & _ & (tbl & size & es & svs & Ekvs & -> & _) & L1 & L2 & OK).
assert (LK : nblk0k kids <= Z.of_nat (length (concat KBS))).
{ eapply (kids_okv_length_ge segs fn m kids); [| exact OK]. intros s Hs bs0 p0 rc0 JV0. destruct (jval_length_ge segs fn s m bs0 p0 rc0 JV0) as (pb1 & PBS1 & REST1 & -> & _ & H). rewrite length_app. lia. }
assert (LKe : length es = length kids) by (rewrite Ekvs, length_map in L1; exact L1).
unfold lh_blocks. rewrite nblk0_obj. cbn [length app]. rewrite length_app, length_map. lia.
- destruct J as (a & ABS & ps & KBS & -> & _ & (arr & size & junk & -> & _) & L1 & L2 & OK).
assert (LK : nblk0k kids <= Z.of_nat (length (concat KBS))).
{ eapply (kids_okp_length_ge segs fn m kids); [| exact OK]. intros s Hs bs0 p0 rc0 JV0. destruct (jval_length_ge segs fn s m bs0 p0 rc0 JV0) as (pb1 & PBS1 & REST1 & -> & _ & H). rewrite length_app. lia. }
rewrite nblk0_arr. cbn [length app]. lia.
Qed.
Lemma jval_fresh_node : forall fn s m BS p rc w, jval segs fn s m BS p rc -> jtx s BS = Some (w, []) -> jnode segs fn s m BS p rc 0.
Proof.
intros fn s m BS p rc w JV H.
destruct (proj1 (jval_split segs fn _ _ _ _ _) JV) as (pb1 & PBS & REST1 & -> & OP1 & JN).
pose proof (jnode_length_ge _ _ _ _ _ _ _ JN) as LE.
pose proof (jtx_length _ _ _ _ H) as L. rewrite length_app in L. cbn [length] in L.
assert (PBS = []) by (destruct PBS; [reflexivity | cbn [length] in L; lia]). subst PBS. rewrite app_nil_r.
destruct OP1 as [[-> _] | [_ (buf & bpos & size & content & E & _)]]; [exact JN | discriminate E].
Qed.
End WithSegs.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1 Lib.SepCache QJZd QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QJZd.Mq0 Q9O6.Mq2 Qwm6.Mq1.
Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Top0.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Theorem get_string_null_A : jo_get_string_null_A_stmt HIx AGET_STRING 48.
Proof.
unfold jo_get_string_null_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP' & RA) K.
subst tp.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold AGET_STRING in *. word_range sp SPR. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 48%nat ST.
do 6 step. step. if_lit.
do 5 step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
evt_done5.
assert (HP1 : HEAPAx A LB LM FRS B m1 md) by (heap_nowA A4L HIx HP MU WM MI1).
release_frame FR ST (bv_unsigned sp).
eapply (K _ md m1 (Z_to_bv 64 0)); [ | exact ERR | exact HP1].
split; [apply ret_statew_intro; [apply fsaved_refl | intros X; exact X]|].
split; [apply model_vm_only_refl|]. split; [exact ST|].
split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; exact Hbb | lia | solve_clientWA A4L HIx HP].
Qed.
End Top0.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QgoP.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 Qw5U.Mq4 QJZd.Mq8 QsKa.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Ltac rt_cell RT c H :=
pose proof (proj1 (Forall_forall _ _) RT c
ltac:(unfold a4_rt_cells, a4_rt_consts; cbn [app]; repeat (first [left; reflexivity | right]))) as H;
cbn [fst snd] in H.

Lemma ro_C1_of_bytes_at : forall segs m a x, bytes_at segs m a [x] -> ro_cells segs m a [C1 x].
Proof. intros segs m a x H. split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact H]. Qed.

Lemma byte_rng : forall x : byte, 0 <= bv_unsigned x < 256.
Proof. intros x. pose proof (bv_unsigned_in_range 8 x) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma zxb_eqb0 : forall x : byte, bv_eqb (zxb x) (Z_to_bv 64 0) = (bv_unsigned x =? 0).
Proof. intros x. pose proof (byte_rng x). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma zxb_eqb : forall x y : byte, bv_eqb (zxb x) (zxb y) = (bv_unsigned x =? bv_unsigned y).
Proof. intros x y. pose proof (byte_rng x). pose proof (byte_rng y). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma sltu_sign : forall x y : byte,
Z_to_bv 64 (bv_unsigned (v_sltu (zxb y) (zxb x)) - bv_unsigned (v_sltu (zxb x) (zxb y))) = Z_to_bv 64 (cmp_sign x y).
Proof.
intros x y. pose proof (byte_rng x). pose proof (byte_rng y). unfold cmp_sign.
destruct (Z.lt_trichotomy (bv_unsigned x) (bv_unsigned y)) as [L | [E | G]].
- rewrite (v_sltu_0' (zxb y) (zxb x)) by (unfold zxb; rewrite !unsigned_lit by lia; lia).
rewrite (v_sltu_1' (zxb x) (zxb y)) by (unfold zxb; rewrite !unsigned_lit by lia; lia).
rewrite !unsigned_lit by lia. replace (Z.sgn (bv_unsigned x - bv_unsigned y)) with (-1) by lia. reflexivity.
- rewrite (v_sltu_0' (zxb y) (zxb x)) by (unfold zxb; rewrite !unsigned_lit by lia; lia).
rewrite (v_sltu_0' (zxb x) (zxb y)) by (unfold zxb; rewrite !unsigned_lit by lia; lia).
rewrite !unsigned_lit by lia. replace (Z.sgn (bv_unsigned x - bv_unsigned y)) with 0 by lia. reflexivity.
- rewrite (v_sltu_1' (zxb y) (zxb x)) by (unfold zxb; rewrite !unsigned_lit by lia; lia).
rewrite (v_sltu_0' (zxb x) (zxb y)) by (unfold zxb; rewrite !unsigned_lit by lia; lia).
rewrite !unsigned_lit by lia. replace (Z.sgn (bv_unsigned x - bv_unsigned y)) with 1 by lia. reflexivity.
Qed.

Lemma istrcmp_sound_U : istrcmp_spec_U.
Proof.
unfold istrcmp_spec_U.
intros until Q. intros MODEL UPA UPB RT Ha Ha47 Hl40 Hb Hb47 HAM HaLo HbLo Ea0 Ea1 NL NR STRA STRB ST LO LOS SPA MI RA K.
subst a0 a1. unfold_consts. word_range sp SPR.
rt_cell RT (0xf07d8, [Z_to_bv 8 1]) INITED. apply ro_C1_of_bytes_at in INITED.
rt_cell RT (0xe5da8, le8 (Z_to_bv 64 0x181628)) GOTFL. apply ro_C8_of_bytes_at in GOTFL.
rt_cell RT (0x18171d, [Z_to_bv 8 0]) STRICT. apply ro_C1_of_bytes_at in STRICT.
rt_cell RT (0x181722, [Z_to_bv 8 1]) ICMP. apply ro_C1_of_bytes_at in ICMP.
rt_cell RT (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL)) GOT. apply ro_C8_of_bytes_at in GOT.
rt_cell RT (A_SB_CELL, le8 (Z_to_bv 64 A_SB)) CELL. apply ro_C8_of_bytes_at in CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
stash STRA. stash STRB.
unfold A_ISTRCMP. carve_frame 104%nat ST.
step.
do 14 step.
do 5 step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2192) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply try_asan_init_spec; [exact MI | assumption | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a1x m2 MU2 WM2 MI2 ST1'.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x4ff88)) with (Z_to_bv 64 0x4ff88) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_false.
do 3 step.

unfold istrcmp_model in MODEL.
destruct (icmp_walk_nread _ _ _ _ _ _ _ MODEL) as (Kf & Kl & Kr).
pose proof (icmp_walk_pos _ _ _ _ _ _ _ MODEL ltac:(lia)) as Kpos.
destruct (icmp_walk_last _ _ _ _ _ _ _ MODEL Kpos) as (xa & xb & NA & NB & LAST).
assert (LASTs : cmp_stop xa xb = true /\ v = cmp_sign xa xb).
{ destruct LAST as [L1 | (Hs & Hk & Hv)]; [exact L1|]. exfalso.
assert (E0 : bv_unsigned xa = 0) by (apply (cstr_nth_zero ls (k - 1) xa NL NA); lia).
unfold cmp_stop in Hs. rewrite E0 in Hs. rewrite Z.eqb_refl, orb_true_r in Hs. discriminate. }
clear LAST. destruct LASTs as (STOP & Ev).
rewrite length_app in Kl, Kr. cbn [length] in Kl, Kr.
unstash STRA. unstash STRB.
assert (STRA2 : bytes_at asegs m2 a (ls ++ [b0]))
by (eapply bytes_at_transport; [exact STRA | eassumption | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
assert (STRB2 : bytes_at asegs m2 b (rs ++ [b0]))
by (eapply bytes_at_transport; [exact STRB | eassumption | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
assert (POST : forall x10 : word,
evt asegs Q (MS (mkR (Z_to_bv 64 0x4ff88) (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0 t1 t2 sp (Z_to_bv 64 b) x10 a1x a2 a3 a4 a5 a6 a7
(Z_to_bv 64 a) ra (Z_to_bv 64 (Z.of_nat k)) s5 s6 s7 s8 (zxb xa) (zxb xb) (Z_to_bv 64 (bv_unsigned sp + -2176)) t3 t4 t5 t6)
F (Z_to_bv 64 0x4ffb4) fc None m2 (seg_rom asegs))).
2: {
assert (LOOP : forall (Kn : nat) (i : Z) (x10 x25 x26 : word),
Z.to_nat (Z.of_nat k - i) = Kn -> 0 <= i < Z.of_nat k ->
evt asegs Q (MS (mkR (Z_to_bv 64 0x4ff88) (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0 t1 t2 sp (Z_to_bv 64 b) x10 a1x a2 a3 a4 a5 a6 a7
(Z_to_bv 64 a) ra (Z_to_bv 64 i) s5 s6 s7 s8 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -2176)) t3 t4 t5 t6)
F (Z_to_bv 64 0x4ff98) fc None m2 (seg_rom asegs))).
{ induction Kn as [|Kn IH]; intros i x10 x25 x26 HK Hi; [lia|].
assert (RDS : exists ya yb, nth_error (ls ++ [b0]) (Z.to_nat i) = Some ya /\ nth_error (rs ++ [b0]) (Z.to_nat i) = Some yb /\
((i + 1 < Z.of_nat k /\ cmp_stop ya yb = false) \/ (i + 1 = Z.of_nat k /\ ya = xa /\ yb = xb))).
{ destruct (Z.eq_dec (i + 1) (Z.of_nat k)) as [E|NE].
- exists xa, xb. replace (Z.to_nat i) with (k - 1)%nat by lia. split; [exact NA|]. split; [exact NB|]. right. auto.
- destruct (icmp_walk_before _ _ _ _ _ _ _ (Z.to_nat i) MODEL ltac:(lia)) as (ya & yb & H1 & H2 & H3).
exists ya, yb. split; [exact H1|]. split; [exact H2|]. left. split; [lia | exact H3]. }
destruct RDS as (ya & yb & NYA & NYB & CASE).
pose proof (u8ro_read asegs m2 a (ls ++ [b0]) i ya _ STRA2 NYA ltac:(lia) eq_refl) as RD1.
pose proof (u8ro_read asegs m2 b (rs ++ [b0]) i yb _ STRB2 NYB ltac:(lia) eq_refl) as RD2.
step. step. step. step. step.
step. rewrite zxb_eqb0.
destruct CASE as [(Hlt & NS) | (Hlast & -> & ->)].
- unfold cmp_stop in NS. apply orb_false_iff in NS. destruct NS as (NS1 & NS2). apply negb_false_iff in NS1.
rewrite NS2. cbv iota.
step. rewrite zxb_eqb, NS1. cbv iota.
apply (IH (i + 1)); lia.
- replace (i + 1) with (Z.of_nat k) by lia.
destruct (bv_unsigned xa =? 0) eqn:E0; cbv iota; [apply POST|].
step. rewrite zxb_eqb.
unfold cmp_stop in STOP. rewrite E0, orb_false_r in STOP. apply negb_true_iff in STOP. rewrite STOP. cbv iota.
apply POST. }
apply (LOOP k 0); lia. }
intros x10.

assert (TAILG : forall (xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 w5 w6 w7 w8 w11 q3 q4 q5 q6 : word) mz,
munch [(lo, bv_unsigned sp)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
bytes_at asegs mz a (ls ++ [b0]) -> bytes_at asegs mz b (rs ++ [b0]) ->
stk asegs mz lo (bv_unsigned sp + -104) ->
rw_cells asegs mz (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7
w2 w3 w4 w5 w6 w7 w8 (zxb xa) (zxb xb) w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x50070) fc None mz (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 w5 w6 w7 w8 w11 q3 q4 q5 q6 mz MUz WMz MIz STRAz STRBz STz FRz.
repeat match goal with H : ro_cells asegs ?mc _ _ |- _ => clear H | H : stk asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
repeat match goal with H : rw_cells asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
step. step. step. rewrite sltu_sign, <- Ev.
do 4 step.
step. step.
step. step.
do 13 step.
step. step.
eapply K; [exact MUz | exact WMz | exact MIz | exact STRAz | exact STRBz | release_frame FRz STz (bv_unsigned sp); exact STz]. }
remember (Z.of_nat k - 1) as len eqn:Elen.
assert (Ek : Z.of_nat k = len + 1) by lia.
rewrite Ek in *.

assert (CHK2G : forall (xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w6 w7 w11 q3 q4 q5 q6 : word) mz,
munch [(lo, bv_unsigned sp)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
bytes_at asegs mz a (ls ++ [b0]) -> bytes_at asegs mz b (rs ++ [b0]) ->
asan_rt_ok mz -> unpoisoned asegs mz A_SB b (len + 1) ->
stk asegs mz lo (bv_unsigned sp + -104) ->
rw_cells asegs mz (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp q0 q1 q2 w0 (Z_to_bv 64 b) y0 y1 y2 y3 y4 y5 y6 y7
w2 w3 (Z_to_bv 64 (len + 1)) (Z_to_bv 64 len) w6 w7 (Z_to_bv 64 0x181628) (zxb xa) (zxb xb) w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x50020) fc None mz (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w6 w7 w11 q3 q4 q5 q6 mz MUz WMz MIz STRAz STRBz RTz UPz STz FRz.
repeat match goal with H : ro_cells asegs ?mc _ _ |- _ => clear H | H : stk asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
repeat match goal with H : rw_cells asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
rt_cell RTz (0x18171d, [Z_to_bv 8 0]) STRICT. apply ro_C1_of_bytes_at in STRICT.
rt_cell RTz (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL)) GOT. apply ro_C8_of_bytes_at in GOT.
rt_cell RTz (A_SB_CELL, le8 (Z_to_bv 64 A_SB)) CELL. apply ro_C8_of_bytes_at in CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
step. rewrite ?zxb_zero.
step. if_false.
step. step. rewrite (unsigned_lit b) by lia. rewrite (lxor_ones64 b) by lia. if_falsex.
step. step.
destruct (Z.le_gt_cases 64 len) as [Hbig | Hsmall].
{
if_truex.
step. if_truex.
step. step. step.
stash STRAz. stash STRBz.
destruct (stk_split asegs mz lo (bv_unsigned sp - 2192) _ STz ltac:(lia)) as [ST1z ST2z]. clear STz.
eapply region_is_poisoned_sound_U with (s := b) (n := len + 1) (lo := lo);
[ exact UPz | exact RTz | exact (proj2 (HAM ltac:(lia))) | lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1z
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MIz
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m3 MU3 WM3 MI3 ST1'' UP3 RT3.
unstash STRAz. unstash STRBz.
assert (STRA3 : bytes_at asegs m3 a (ls ++ [b0]))
by (eapply bytes_at_transport; [exact STRAz | exact MU3 | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
assert (STRB3 : bytes_at asegs m3 b (rs ++ [b0]))
by (eapply bytes_at_transport; [exact STRBz | exact MU3 | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
clear STRAz STRBz.
transport_after_call asegs mz m3 MU3 WM3; clear MIz; clear MU3 WM3.
replace (ret_pc (Z_to_bv 64 0x50360)) with (Z_to_bv 64 0x50360) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_true.
eapply TAILG; [exact MUz | exact WMz | exact MI3 | exact STRA3 | exact STRB3
| eapply stk_merge; [exact ST1'' | exact ST2z | lia] | exact FRz]. }

if_falsex.
assert (Hh : b / 8 <= (b + len) / 8 <= b / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (b / 8 + A_SB) UPz ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((b + len) / 8 + A_SB) UPz ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
assert (GS0 : forall j, 0 <= j -> b / 8 + j < (b + len) / 8 ->
ov_read_bytes asegs mz (Z_to_bv 64 (b / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]).
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (b / 8 + 2147450880 + j) with ((b / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPz). replace (b + (len + 1) - 1) with (b + len) by lia. lia. }
assert (HRL : exists v, ov_read_bytes asegs mz (Z_to_bv 64 ((b + len) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (b + len) mod 8 < v))).
{ destruct (unpoisoned_last asegs _ _ _ _ UPz) as (v0 & Hro & Hv). replace (b + (len + 1) - 1) with (b + len) in Hro, Hv by lia.
exists v0. split; [| exact Hv]. apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
clear UPz.
do 3 step.
step. replace (len + b) with (b + len) by lia.
do 2 step; do 2 step; do 2 step.
sh_norm.
replace (2147450880 + b / 8) with (b / 8 + 2147450880) by lia.
replace (2147450880 + (b + len) / 8) with ((b + len) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (b / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((b + len) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.
assert (TAIL2 : forall (xra' q0' q1' q2' w0' w1' y0' y1' y2' y3' y4' y5' y6' y7' w2' w3' w4' w5' w6' w7' w8' w11' q3' q4' q5' q6' : word),
evt asegs Q (MS (mkR xra' (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp q0' q1' q2' w0' w1' y0' y1' y2' y3' y4' y5' y6' y7'
w2' w3' w4' w5' w6' w7' w8' (zxb xa) (zxb xb) w11' q3' q4' q5' q6')
F (Z_to_bv 64 0x50070) fc None mz (seg_rom asegs)))
by (intros; eapply TAILG; eassumption).

assert (LOOP2 : forall (Kn : nat) (i : Z) (y3' y4' : word),
Z.to_nat ((b + len) / 8 - b / 8 - i) = Kn -> 0 <= i -> b / 8 + i < (b + len) / 8 ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp q0 q1 q2 w0 (Z_to_bv 64 b)
(Z_to_bv 64 (b / 8 + 2147450880 + i)) (Z_to_bv 64 ((b + len) / 8 + 2147450880)) (Z_to_bv 64 0) y3' y4' y5 y6 y7
w2 w3 (Z_to_bv 64 (len + 1)) (Z_to_bv 64 (b + len)) w6 w7 (Z_to_bv 64 0x181628) (zxb xa) (zxb xb) w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x5033c) fc None mz (seg_rom asegs))).
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i y3' y4' HK Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (b / 8 + i + 1) ((b + len) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. apply TAIL2.
- if_truex. replace (b / 8 + 2147450880 + i + 1) with (b / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply TAIL2. }

destruct HRL as (vv & HR & Hv).
assert (Hv8 : 0 <= vv < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step. rewrite (sxb_small vv) by lia. clear HR.
step. rewrite (unsigned_lit (b + len)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (b / 8) ((b + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL2.
+ if_falsex. replace (b / 8 + 2147450880) with (b / 8 + 2147450880 + 0) by lia.
apply (LOOP2 (Z.to_nat ((b + len) / 8 - b / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 vv)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((b + len) mod 8)) (Z_to_bv 64 vv)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (b / 8) ((b + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL2.
+ if_falsex. replace (b / 8 + 2147450880) with (b / 8 + 2147450880 + 0) by lia.
apply (LOOP2 (Z.to_nat ((b + len) / 8 - b / 8 - 0)) 0); lia. }

assert (RT2 : asan_rt_ok m2)
by (eapply asan_rt_ok_transport; [exact RT | exact MU | intros cc Hcc2; pose proof (a4_rt_cells_in_img cc Hcc2); cbn; split; [left; lia | exact I]]).
assert (UPA2 : unpoisoned asegs m2 A_SB a (len + 1))
by (eapply unpoisoned_transport; [exact UPA | exact MU | intros a' k' Ha' Hk'; eapply (shadow_outside_stack A_SB a (len + 1)); try eassumption; unfold A_SB; lia]).
assert (UPB2 : unpoisoned asegs m2 A_SB b (len + 1))
by (eapply unpoisoned_transport; [exact UPB | exact MU | intros a' k' Ha' Hk'; eapply (shadow_outside_stack A_SB b (len + 1)); try eassumption; unfold A_SB; lia]).
clear UPA UPB.
do 2 step.
step. step. if_false.
step. rewrite ?zxb_zero.
step. replace (len + 1 + -1) with len by lia.
step. step.
step. if_false.
step. step. rewrite (unsigned_lit a) by lia. rewrite (lxor_ones64 a) by lia. if_falsex.
step. step.
destruct (Z.le_gt_cases 64 len) as [Hbig | Hsmall].
{
if_truex.
step. if_truex.
step. step. step.
clear STRA STRB. stash STRA2. stash STRB2.
eapply region_is_poisoned_sound_U with (s := a) (n := len + 1) (lo := lo);
[ exact UPA2 | exact RT2 | exact (proj1 (HAM ltac:(lia))) | lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1'
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MI2
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m3 MU3 WM3 MI3 ST1'' UP3 RT3.
unstash STRA2. unstash STRB2.
assert (STRA3 : bytes_at asegs m3 a (ls ++ [b0]))
by (eapply bytes_at_transport; [exact STRA2 | exact MU3 | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
assert (STRB3 : bytes_at asegs m3 b (rs ++ [b0]))
by (eapply bytes_at_transport; [exact STRB2 | exact MU3 | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
assert (UPB3 : unpoisoned asegs m3 A_SB b (len + 1))
by (eapply unpoisoned_transport; [exact UPB2 | exact MU3 | intros a' k' Ha' Hk'; eapply (shadow_outside_stack A_SB b (len + 1)); try eassumption; unfold A_SB; lia]).
clear STRA2 STRB2 UPB2 UPA2 RT2.
transport_after_call asegs m2 m3 MU3 WM3; clear MI2; clear MU3 WM3.
replace (ret_pc (Z_to_bv 64 0x50280)) with (Z_to_bv 64 0x50280) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_true.
eapply CHK2G; [exact MU | exact WM | exact MI3 | exact STRA3 | exact STRB3 | exact RT3 | exact UPB3
| eapply stk_merge; [exact ST1'' | exact ST2 | lia] | exact FR]. }

if_falsex.
assert (CHK2 : forall (xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w6 w7 w11 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp q0 q1 q2 w0 (Z_to_bv 64 b) y0 y1 y2 y3 y4 y5 y6 y7
w2 w3 (Z_to_bv 64 (len + 1)) (Z_to_bv 64 len) w6 w7 (Z_to_bv 64 0x181628) (zxb xa) (zxb xb) w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x50020) fc None m2 (seg_rom asegs)))
by (intros; eapply CHK2G; [exact MU | exact WM | exact MI2 | exact STRA2 | exact STRB2 | exact RT2 | exact UPB2
| eapply stk_merge; [exact ST1' | exact ST2 | lia] | exact FR]).
assert (Hh : a / 8 <= (a + len) / 8 <= a / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (a / 8 + A_SB) UPA2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((a + len) / 8 + A_SB) UPA2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
assert (GS0 : forall j, 0 <= j -> a / 8 + j < (a + len) / 8 ->
ov_read_bytes asegs m2 (Z_to_bv 64 (a / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]).
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (a / 8 + 2147450880 + j) with ((a / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPA2). replace (a + (len + 1) - 1) with (a + len) by lia. lia. }
assert (HRL : exists v, ov_read_bytes asegs m2 (Z_to_bv 64 ((a + len) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (a + len) mod 8 < v))).
{ destruct (unpoisoned_last asegs _ _ _ _ UPA2) as (v0 & Hro & Hv). replace (a + (len + 1) - 1) with (a + len) in Hro, Hv by lia.
exists v0. split; [| exact Hv]. apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
clear UPA2 UPB2 RT2 CHK2G TAILG.
do 3 step.
step. replace (len + a) with (a + len) by lia.
do 2 step; do 2 step; do 2 step.
sh_norm.
replace (2147450880 + a / 8) with (a / 8 + 2147450880) by lia.
replace (2147450880 + (a + len) / 8) with ((a + len) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (a / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((a + len) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

assert (LOOP1 : forall (Kn : nat) (i : Z) (y3' y4' : word),
Z.to_nat ((a + len) / 8 - a / 8 - i) = Kn -> 0 <= i -> a / 8 + i < (a + len) / 8 ->
evt asegs Q (MS (mkR (Z_to_bv 64 0x4ff88) (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0 t1 t2 sp (Z_to_bv 64 b)
(Z_to_bv 64 (a / 8 + 2147450880 + i)) (Z_to_bv 64 ((a + len) / 8 + 2147450880)) (Z_to_bv 64 0) y3' y4' a5 a6 a7
(Z_to_bv 64 a) ra (Z_to_bv 64 (len + 1)) (Z_to_bv 64 len) (Z_to_bv 64 (len + 1)) s7 (Z_to_bv 64 0x181628) (zxb xa) (zxb xb)
(Z_to_bv 64 (bv_unsigned sp + -2176)) t3 t4 t5 t6)
F (Z_to_bv 64 0x5025c) fc None m2 (seg_rom asegs))).
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i y3' y4' HK Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (a / 8 + i + 1) ((a + len) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. apply CHK2.
- if_truex. replace (a / 8 + 2147450880 + i + 1) with (a / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply CHK2. }

destruct HRL as (vv & HR & Hv).
assert (Hv8 : 0 <= vv < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step. rewrite (sxb_small vv) by lia. clear HR.
step. rewrite (unsigned_lit (a + len)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (a / 8) ((a + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply CHK2.
+ if_falsex. replace (a / 8 + 2147450880) with (a / 8 + 2147450880 + 0) by lia.
apply (LOOP1 (Z.to_nat ((a + len) / 8 - a / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 vv)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((a + len) mod 8)) (Z_to_bv 64 vv)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (a / 8) ((a + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply CHK2.
+ if_falsex. replace (a / 8 + 2147450880) with (a / 8 + 2147450880 + 0) by lia.
apply (LOOP1 (Z.to_nat ((a + len) / 8 - a / 8 - 0)) 0); lia.
Qed.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import Q7UD Qhd4 Qwm6.
Import Qhd4.Mq0.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 Qw5U.Mq4 QnPO.Mq3 QJZd.Mq7 QJZd.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma real_memcpy_Z : real_memcpy_specZ_stmt.
Proof.
unfold real_memcpy_specZ_stmt. intros until junk. intros SRC SRCL DST DISJ MI.
eapply evt_mono; [eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk);
[exact SRC | exact SRCL | exact DST | exact DISJ | exact MI] |].
intros ms' P. exact P.
Qed.

Theorem amemset_U : amemset_spec_U.
Proof. exact amemset_sound_U. Qed.

Theorem amemcpy_U : amemcpy_spec_U.
Proof. exact (amemcpy_sound_U real_memcpy_Z). Qed.

Theorem astrlen_U : astrlen_spec_U.
Proof. exact astrlen_sound_U. Qed.

Section C.
Variable HIx : heap_iface_A A4L.

Lemma blk_app_bounds : forall A LB LM FRS B m md ab nb x k,
HEAPA A4L HIx A LB LM FRS B m md -> In (ab, nb) LB -> ab <= x -> x + k <= ab + nb ->
0 <= x /\ x + k <= 2^47 /\ x + k <= alloc_ceiling.
Proof.
intros A LB LM FRS B m md ab nb x k HP Hblk Hx Hk.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ab nb HP ltac:(apply in_or_app; left; exact Hblk)) as (Hnb0 & _ & Hpos & Hhi & _).
rc_pose_range RC__. unfold alloc_ceiling in *. lia.
Qed.

Lemma blk_app_mem : forall A LB LM FRS B m md ab nb x k,
HEAPA A4L HIx A LB LM FRS B m md -> In (ab, nb) LB -> ab <= x -> x + k <= ab + nb -> app_mem x k.
Proof.
intros A LB LM FRS B m md ab nb x k HP Hblk Hx Hk.
destruct (blk_app_bounds _ _ _ _ _ _ _ ab nb x k HP Hblk Hx Hk) as (B1 & B2 & B3).
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ ab nb HP ltac:(apply in_or_app; left; exact Hblk)) as AM.
cbn [hl_sb A4L] in AM. unfold app_mem, A_SB, A_HMB in *. rc_pose_range RC__. unfold alloc_ceiling in *. lia.
Qed.

Theorem amemset_A : amemset_spec_A HIx.
Proof.
unfold amemset_spec_A. intros until Q. intros HP Hblk Hab Hdn Ha0 Ha1 Ha2 Hc Hn DST ST LO LOS SPA HT MI RA K.
destruct (blk_app_bounds _ _ _ _ _ _ _ ab nb d n HP Hblk Hab Hdn) as (B1 & B2 & B3).
eapply (amemset_U ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d c n lo old Q);
try eassumption; try lia.
- intros _. eapply unpoisoned_of_blk; [exact HP | exact Hblk | lia | lia | lia].
- eapply asan_rt_ok_of_HEAPA; exact HP.
Qed.

Theorem amemcpy_any_A : amemcpy_any_spec_A HIx.
Proof.
unfold amemcpy_any_spec_A. intros until Q. intros HP Hblk Hab Hdn Hsblk Hsb Hsn Ha0 Ha1 Ha2 Hn Hdisj DST SRC SRCL ST LO LOS SPA HT MI RA K.
destruct (blk_app_bounds _ _ _ _ _ _ _ ab nb d n HP Hblk Hab Hdn) as (B1 & B2 & B3).
destruct (blk_app_bounds _ _ _ _ _ _ _ sb nsb s n HP Hsblk Hsb Hsn) as (C1 & C2 & C3).
eapply (amemcpy_U ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s n lo old src Q);
try eassumption; try lia.
- intros Hpos. eapply unpoisoned_of_blk; [exact HP | exact Hblk | lia | lia | lia].
- intros Hpos. eapply unpoisoned_of_blk; [exact HP | exact Hsblk | lia | lia | lia].
- eapply asan_rt_ok_of_HEAPA; exact HP.
- right. split; [eapply blk_app_mem; [exact HP | exact Hblk | lia | lia] | eapply blk_app_mem; [exact HP | exact Hsblk | lia | lia]].
Qed.

Theorem astrlen_any_A : astrlen_any_spec_A HIx.
Proof.
unfold astrlen_any_spec_A. intros until Q. intros HP Hsblk Hsb Hsn Ha0 NONUL Hlen STR PAD SLK ST LO LOS SPA HT MI RA K.
destruct (blk_app_bounds _ _ _ _ _ _ _ sb nsb s (Z.of_nat (length str) + 1) HP Hsblk Hsb ltac:(lia)) as (C1 & C2 & C3).
eapply (astrlen_U ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s lo str slack Q);
try eassumption; try lia.
- eapply unpoisoned_of_blk; [exact HP | exact Hsblk | lia | lia | lia].
- eapply asan_rt_ok_of_HEAPA; exact HP.
- right. eapply blk_app_mem; [exact HP | exact Hsblk | lia | lia].
Qed.
End C.
End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl Quj7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes Qfw3_c1.Mq2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg Qc3B.
Import QCcH Qsw7 QJjn QRUw.
Import QBGG.
Import QoBT Q7T7.
Import QbFI. Import QRBl. Import Qwm6.
Import Qwm6.Mq4 QlKV.Mqj.

Import Qw5U.Mq6.
Import Quj7.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
Ltac litn := fold_closed_in_goal.
Ltac freg H :=
lazymatch type of H with Sem.reg_get ?F ?k = ?v =>
match goal with |- context [Sem.reg_get F ?k'] =>
replace (Sem.reg_get F k') with v by (symmetry; exact H) end
end.
Ltac solve_fsaved :=
let k := fresh "k" in let Hk := fresh "Hk" in
intros k Hk; cbn [FSAVED In] in Hk;
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk];
repeat (first [ rewrite freg_get_other by (vm_compute; reflexivity)
| rewrite freg_get_same by (vm_compute; reflexivity) ]);
reflexivity.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section ACfp.
Definition cfp_pb1 := Eval vm_compute in match image_bytes asegs 0x10330 8 with Some bs => bs | None => [] end.
Definition cfp_pb2 := Eval vm_compute in match image_bytes asegs 0x103c8 8 with Some bs => bs | None => [] end.
Definition cfp_pb3 := Eval vm_compute in match image_bytes asegs 0x10338 8 with Some bs => bs | None => [] end.
Lemma cfp_ro_A : forall m, mem_inv asegs m ->
ro_cells asegs m 0x10330 [CB 8 cfp_pb1] /\ ro_cells asegs m 0x103c8 [CB 8 cfp_pb2] /\ ro_cells asegs m 0x10338 [CB 8 cfp_pb3].
Proof.
intros m MI. split; [|split].
- change 8%nat with (length cfp_pb1). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length cfp_pb1)) with 8%Z. lia.
- change 8%nat with (length cfp_pb2). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length cfp_pb2)) with 8%Z. lia.
- change 8%nat with (length cfp_pb3). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length cfp_pb3)) with 8%Z. lia.
Qed.

Definition cfp_B_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P ptr rem lo : Z) (data : list byte),
a0 = Z_to_bv 64 P ->
asan_rt_ok m ->
rw_cells asegs m P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] -> unpoisoned asegs m A_SB P 16 -> P mod 8 = 0 ->
bytes_at asegs m ptr data -> Z.of_nat (length data) = rem -> 0 < ptr -> (0 < rem -> unpoisoned asegs m A_SB ptr rem) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
0x647000 <= P -> P + 16 <= alloc_ceiling -> (P + 24 <= A_SB \/ A_HMB <= P) -> ptr + rem <= alloc_ceiling ->
(rem = 0 \/ P + 16 <= ptr \/ ptr + rem <= P) ->
mem_inv asegs m ->
Sem.reg_get F (Z_to_bv 5 10) = Z_to_bv 64 0xFFEFFFFFFFFFFFFF ->
Sem.reg_get F (Z_to_bv 5 11) = Z_to_bv 64 0x7FEFFFFFFFFFFFFF ->
frm0 fc ->
evt asegs (fdp_postFA 64 9 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Ltac cfp_tail_B sp EVc SRC1 LEN1 rem rem1 :=
step; step; step; step; fold_mkR;
lazymatch goal with MUq : munch _ _ ?mq |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
destruct (EVc _ MUq) as (RTq & UNPq & UNDq);
eapply evt_cut; [ eapply Quj7.cii_u64_B with (lo := _); try eassumption |];
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
[ reflexivity
| rewrite unsigned_lit by lia; reflexivity
| vm_compute; reflexivity
| intros Hr1; eapply (QsKa.Mqa.unpoisoned_sub_any asegs _ A_SB _ rem _ rem1); [apply UNDq; lia | lia | lia | lia]
| eassumption
| lia | lia | lia
| cbv beta delta [cii_postA cii_WSA]; rewrite !(unsigned_lit (bv_unsigned sp + -48)) by lia; post_call asegs mq ]
end.

Lemma cfp_A : cfp_B_stmt 0x931a4.
Proof.
unfold cfp_B_stmt. intros until data. intros A0 RT FDP UNP PAL SRC LEN PTR0 UND ST LO LOS PIM PAC PAPP DLO PDS MI F10 F11 FRM. subst a0. unfold A_SB, A_HMB in PAPP.

destruct (Z.eq_dec rem 0) as [RZ | RNZ].
{ assert (DZ : data = []) by (destruct data; [reflexivity | cbn in LEN; lia]).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR.
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (munch_refl (fdp_WSA 64 (bv_unsigned sp) P) m) as MU. unfold fdp_WSA in MU.
pose proof (wmono_refl asegs m) as WM.
destruct (cfp_ro_A m MI) as (RO1 & RO2 & RO3).
assert (WAPP : Forall (fun iv : Z * Z => snd iv <= A_SB \/ A_HMB <= fst iv) [(bv_unsigned sp - 64, bv_unsigned sp); (P + 8, P + 16)]).
{ unfold A_SB, A_HMB in *. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }

assert (EVc : forall mc, munch [(bv_unsigned sp - 64, bv_unsigned sp); (P + 8, P + 16)] m mc ->
asan_rt_ok mc /\ unpoisoned asegs mc A_SB P 16 /\ (0 < rem -> unpoisoned asegs mc A_SB ptr rem)).
{ intros mc MUc. split; [|split].
- eapply asan_rt_ok_transport; [exact RT | exact MUc | intros cc Hcc; pose proof (a4_rt_cells_in_img cc Hcc) as X; cbn [disjoint_from]; repeat split; lia].
- eapply unpoisoned_keep; [exact UNP | exact MUc | lia | lia | exact WAPP].
- intros Hr. pose proof (UND Hr) as U. pose proof U as (_ & _). eapply unpoisoned_keep; [exact U | exact MUc | lia | | exact WAPP].
unfold unpoisoned, shadow_span_hi, A_SB in U. lia. }
carve_frame 48%nat ST.
step. step. step. step. step. step.
step. freg F10. freg F11. litn.
step. if_lit.
step. freg F10. step. step. step.
step. freg F10.
step. freg F11.
step. if_lit.
step. step. step. if_lit. step. freg F11. step. if_lit.
step. step. step. freg F11. step. step.
step. step. step. step.

fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m1 end.
destruct (EVc _ MU) as (RT1 & UNP1 & UND1).
eapply evt_cut; [ eapply Quj7.cii_u8_B with (ptr := ptr) (lo := lo); try eassumption |].
all: rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia.
1: reflexivity. 1-2: rewrite unsigned_lit by lia; reflexivity. 1: eassumption. 1: lia.
cbv beta delta [cii_postA cii_WSA]. rewrite !(unsigned_lit (bv_unsigned sp + -48)) by lia.
post_call asegs m1. rename PC0 into FDP. clear PC. try clear SRC. rename PC1 into SRC. rename POST into ST.
step. step.

set (rem1 := Z.max (rem - 1) 0) in FDP.
assert (LEN1 : Z.of_nat (length (firstn (Z.to_nat rem1) data)) = rem1) by (rewrite length_firstn; lia).
lazymatch goal with H : bytes_at asegs ?mq ptr data |- _ =>
pose proof H as SRC1; rewrite <- (firstn_skipn (Z.to_nat rem1) data) in SRC1; apply bytes_at_app in SRC1 as [SRC1 _] end.
assert (HD1 : ptr + rem1 <= bv_unsigned sp - 64) by lia.

match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
- step. step. cfp_tail_B sp EVc SRC1 LEN1 rem rem1.
rename PC0 into FDP2. rename POST into ST2.
step. step. step. step. step.
step. step. step. step. step. step. step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -48) _ |- _ => release_frame H ST2 (bv_unsigned sp) end.
finish; first [ solve_fsaved | replace (Z.max (rem - 9) 0) with (Z.max (rem1 - 8) 0) by lia; assumption | rewrite DZ; apply bytes_at_nil; clear - DB; lia ].
- step. step. step. cfp_tail_B sp EVc SRC1 LEN1 rem rem1.
rename PC0 into FDP2. rename POST into ST2.
step. step. step. step. step.
step. step. step. step. step. step. step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -48) _ |- _ => release_frame H ST2 (bv_unsigned sp) end.
finish; first [ solve_fsaved | replace (Z.max (rem - 9) 0) with (Z.max (rem1 - 8) 0) by lia; assumption | rewrite DZ; apply bytes_at_nil; clear - DB; lia ]. }
{
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR.
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (munch_refl (fdp_WSA 64 (bv_unsigned sp) P) m) as MU. unfold fdp_WSA in MU.
pose proof (wmono_refl asegs m) as WM.
destruct (cfp_ro_A m MI) as (RO1 & RO2 & RO3).
assert (WAPP : Forall (fun iv : Z * Z => snd iv <= A_SB \/ A_HMB <= fst iv) [(bv_unsigned sp - 64, bv_unsigned sp); (P + 8, P + 16)]).
{ unfold A_SB, A_HMB in *. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }

assert (EVc : forall mc, munch [(bv_unsigned sp - 64, bv_unsigned sp); (P + 8, P + 16)] m mc ->
asan_rt_ok mc /\ unpoisoned asegs mc A_SB P 16 /\ (0 < rem -> unpoisoned asegs mc A_SB ptr rem)).
{ intros mc MUc. split; [|split].
- eapply asan_rt_ok_transport; [exact RT | exact MUc | intros cc Hcc; pose proof (a4_rt_cells_in_img cc Hcc) as X; cbn [disjoint_from]; repeat split; lia].
- eapply unpoisoned_keep; [exact UNP | exact MUc | lia | lia | exact WAPP].
- intros Hr. pose proof (UND Hr) as U. pose proof U as (_ & _). eapply unpoisoned_keep; [exact U | exact MUc | lia | | exact WAPP].
unfold unpoisoned, shadow_span_hi, A_SB in U. lia. }
carve_frame 48%nat ST.
step. step. step. step. step. step.
step. freg F10. freg F11. litn.
step. if_lit.
step. freg F10. step. step. step.
step. freg F10.
step. freg F11.
step. if_lit.
step. step. step. if_lit. step. freg F11. step. if_lit.
step. step. step. freg F11. step. step.
step. step. step. step.

fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m1 end.
destruct (EVc _ MU) as (RT1 & UNP1 & UND1).
eapply evt_cut; [ eapply Quj7.cii_u8_B with (ptr := ptr) (lo := lo); try eassumption |].
all: rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia.
1: reflexivity. 1-2: rewrite unsigned_lit by lia; reflexivity. 1: eassumption. 1: lia.
cbv beta delta [cii_postA cii_WSA]. rewrite !(unsigned_lit (bv_unsigned sp + -48)) by lia.
post_call asegs m1. rename PC0 into FDP. clear PC. try clear SRC. rename PC1 into SRC. rename POST into ST.
step. step.

set (rem1 := Z.max (rem - 1) 0) in FDP.
assert (LEN1 : Z.of_nat (length (firstn (Z.to_nat rem1) data)) = rem1) by (rewrite length_firstn; lia).
lazymatch goal with H : bytes_at asegs ?mq ptr data |- _ =>
pose proof H as SRC1; rewrite <- (firstn_skipn (Z.to_nat rem1) data) in SRC1; apply bytes_at_app in SRC1 as [SRC1 _] end.
assert (HD1 : ptr + rem1 <= bv_unsigned sp - 64) by lia.

match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
- step. step. cfp_tail_B sp EVc SRC1 LEN1 rem rem1.
rename PC0 into FDP2. rename POST into ST2.
step. step. step. step. step.
step. step. step. step. step. step. step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -48) _ |- _ => release_frame H ST2 (bv_unsigned sp) end.
finish; first [ solve_fsaved | replace (Z.max (rem - 9) 0) with (Z.max (rem1 - 8) 0) by lia; assumption | rewrite DZ; apply bytes_at_nil; clear - DB; lia ].
- step. step. step. cfp_tail_B sp EVc SRC1 LEN1 rem rem1.
rename PC0 into FDP2. rename POST into ST2.
step. step. step. step. step.
step. step. step. step. step. step. step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -48) _ |- _ => release_frame H ST2 (bv_unsigned sp) end.
finish; first [ solve_fsaved | replace (Z.max (rem - 9) 0) with (Z.max (rem1 - 8) 0) by lia; assumption | rewrite DZ; apply bytes_at_nil; clear - DB; lia ]. }
Qed.
End ACfp.
End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd QJZd.Mq9 Q9O6.Mq5. Import Qwm6.Mq1.
Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Top0.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Theorem get_string_null_A : jo_get_string_null_A_stmt HIx AGET_STRING 48.
Proof.
unfold jo_get_string_null_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP' & RA) K.
subst tp.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold AGET_STRING in *. word_range sp SPR. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 48%nat ST.
do 6 bstep. bstep. if_lit.
do 5 bstep. bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
evt_done5.
assert (HP1 : HEAPAx A LB LM FRS B m1 md) by (heap_nowA A4L HIx HP MU WM MI1).
release_frame FR ST (bv_unsigned sp).
eapply (K _ md m1 (Z_to_bv 64 0)); [ | exact ERR | exact HP1].
split; [apply ret_statew_intro; [apply fsaved_refl | intros X; exact X]|].
split; [apply model_vm_only_refl|]. split; [exact ST|].
split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; exact Hbb | lia | solve_clientWA A4L HIx HP].
Qed.
End Top0.
End RC__1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QgoP.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg Qw5U QJZd.Mqg QsKa.Mq9.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Ltac rt_cell RT c H :=
pose proof (proj1 (Forall_forall _ _) RT c
ltac:(unfold a4_rt_cells, a4_rt_consts; cbn [app]; repeat (first [left; reflexivity | right]))) as H;
cbn [fst snd] in H.

Lemma ro_C1_of_bytes_at : forall segs m a x, bytes_at segs m a [x] -> ro_cells segs m a [C1 x].
Proof. intros segs m a x H. split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact H]. Qed.

Lemma byte_rng : forall x : byte, 0 <= bv_unsigned x < 256.
Proof. intros x. pose proof (bv_unsigned_in_range 8 x) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma zxb_eqb0 : forall x : byte, bv_eqb (zxb x) (Z_to_bv 64 0) = (bv_unsigned x =? 0).
Proof. intros x. pose proof (byte_rng x). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma zxb_eqb : forall x y : byte, bv_eqb (zxb x) (zxb y) = (bv_unsigned x =? bv_unsigned y).
Proof. intros x y. pose proof (byte_rng x). pose proof (byte_rng y). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma sltu_sign : forall x y : byte,
Z_to_bv 64 (bv_unsigned (v_sltu (zxb y) (zxb x)) - bv_unsigned (v_sltu (zxb x) (zxb y))) = Z_to_bv 64 (cmp_sign x y).
Proof.
intros x y. pose proof (byte_rng x). pose proof (byte_rng y). unfold cmp_sign.
destruct (Z.lt_trichotomy (bv_unsigned x) (bv_unsigned y)) as [L | [E | G]].
- rewrite (v_sltu_0' (zxb y) (zxb x)) by (unfold zxb; rewrite !unsigned_lit by lia; lia).
rewrite (v_sltu_1' (zxb x) (zxb y)) by (unfold zxb; rewrite !unsigned_lit by lia; lia).
rewrite !unsigned_lit by lia. replace (Z.sgn (bv_unsigned x - bv_unsigned y)) with (-1) by lia. reflexivity.
- rewrite (v_sltu_0' (zxb y) (zxb x)) by (unfold zxb; rewrite !unsigned_lit by lia; lia).
rewrite (v_sltu_0' (zxb x) (zxb y)) by (unfold zxb; rewrite !unsigned_lit by lia; lia).
rewrite !unsigned_lit by lia. replace (Z.sgn (bv_unsigned x - bv_unsigned y)) with 0 by lia. reflexivity.
- rewrite (v_sltu_1' (zxb y) (zxb x)) by (unfold zxb; rewrite !unsigned_lit by lia; lia).
rewrite (v_sltu_0' (zxb x) (zxb y)) by (unfold zxb; rewrite !unsigned_lit by lia; lia).
rewrite !unsigned_lit by lia. replace (Z.sgn (bv_unsigned x - bv_unsigned y)) with 1 by lia. reflexivity.
Qed.

Lemma istrcmp_sound_U : istrcmp_spec_U.
Proof.
unfold istrcmp_spec_U.
intros until Q. intros MODEL UPA UPB RT Ha Ha47 Hl40 Hb Hb47 HAM HaLo HbLo Ea0 Ea1 NL NR STRA STRB ST LO LOS SPA MI RA K.
subst a0 a1. unfold_consts. word_range sp SPR.
rt_cell RT (0xf2e98, [Z_to_bv 8 1]) INITED. apply ro_C1_of_bytes_at in INITED.
rt_cell RT (0xe81a8, le8 (Z_to_bv 64 0x183ce8)) GOTFL. apply ro_C8_of_bytes_at in GOTFL.
rt_cell RT (0x183ddd, [Z_to_bv 8 0]) STRICT. apply ro_C1_of_bytes_at in STRICT.
rt_cell RT (0x183de2, [Z_to_bv 8 1]) ICMP. apply ro_C1_of_bytes_at in ICMP.
rt_cell RT (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL)) GOT. apply ro_C8_of_bytes_at in GOT.
rt_cell RT (A_SB_CELL, le8 (Z_to_bv 64 A_SB)) CELL. apply ro_C8_of_bytes_at in CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
stash STRA. stash STRB.
unfold A_ISTRCMP. carve_frame 104%nat ST.
step.
do 14 step.
do 5 step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2192) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply try_asan_init_spec; [exact MI | assumption | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a1x m2 MU2 WM2 MI2 ST1'.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x50360)) with (Z_to_bv 64 0x50360) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_false.
do 3 step.

unfold istrcmp_model in MODEL.
destruct (icmp_walk_nread _ _ _ _ _ _ _ MODEL) as (Kf & Kl & Kr).
pose proof (icmp_walk_pos _ _ _ _ _ _ _ MODEL ltac:(lia)) as Kpos.
destruct (icmp_walk_last _ _ _ _ _ _ _ MODEL Kpos) as (xa & xb & NA & NB & LAST).
assert (LASTs : cmp_stop xa xb = true /\ v = cmp_sign xa xb).
{ destruct LAST as [L1 | (Hs & Hk & Hv)]; [exact L1|]. exfalso.
assert (E0 : bv_unsigned xa = 0) by (apply (cstr_nth_zero ls (k - 1) xa NL NA); lia).
unfold cmp_stop in Hs. rewrite E0 in Hs. rewrite Z.eqb_refl, orb_true_r in Hs. discriminate. }
clear LAST. destruct LASTs as (STOP & Ev).
rewrite length_app in Kl, Kr. cbn [length] in Kl, Kr.
unstash STRA. unstash STRB.
assert (STRA2 : bytes_at asegs m2 a (ls ++ [b0]))
by (eapply bytes_at_transport; [exact STRA | eassumption | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
assert (STRB2 : bytes_at asegs m2 b (rs ++ [b0]))
by (eapply bytes_at_transport; [exact STRB | eassumption | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
assert (POST : forall x10 : word,
evt asegs Q (MS (mkR (Z_to_bv 64 0x50360) (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0 t1 t2 sp (Z_to_bv 64 b) x10 a1x a2 a3 a4 a5 a6 a7
(Z_to_bv 64 a) ra (Z_to_bv 64 (Z.of_nat k)) s5 s6 s7 s8 (zxb xa) (zxb xb) (Z_to_bv 64 (bv_unsigned sp + -2176)) t3 t4 t5 t6)
F (Z_to_bv 64 0x5038c) fc None m2 (seg_rom asegs))).
2: {
assert (LOOP : forall (Kn : nat) (i : Z) (x10 x25 x26 : word),
Z.to_nat (Z.of_nat k - i) = Kn -> 0 <= i < Z.of_nat k ->
evt asegs Q (MS (mkR (Z_to_bv 64 0x50360) (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0 t1 t2 sp (Z_to_bv 64 b) x10 a1x a2 a3 a4 a5 a6 a7
(Z_to_bv 64 a) ra (Z_to_bv 64 i) s5 s6 s7 s8 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -2176)) t3 t4 t5 t6)
F (Z_to_bv 64 0x50370) fc None m2 (seg_rom asegs))).
{ induction Kn as [|Kn IH]; intros i x10 x25 x26 HK Hi; [lia|].
assert (RDS : exists ya yb, nth_error (ls ++ [b0]) (Z.to_nat i) = Some ya /\ nth_error (rs ++ [b0]) (Z.to_nat i) = Some yb /\
((i + 1 < Z.of_nat k /\ cmp_stop ya yb = false) \/ (i + 1 = Z.of_nat k /\ ya = xa /\ yb = xb))).
{ destruct (Z.eq_dec (i + 1) (Z.of_nat k)) as [E|NE].
- exists xa, xb. replace (Z.to_nat i) with (k - 1)%nat by lia. split; [exact NA|]. split; [exact NB|]. right. auto.
- destruct (icmp_walk_before _ _ _ _ _ _ _ (Z.to_nat i) MODEL ltac:(lia)) as (ya & yb & H1 & H2 & H3).
exists ya, yb. split; [exact H1|]. split; [exact H2|]. left. split; [lia | exact H3]. }
destruct RDS as (ya & yb & NYA & NYB & CASE).
pose proof (u8ro_read asegs m2 a (ls ++ [b0]) i ya _ STRA2 NYA ltac:(lia) eq_refl) as RD1.
pose proof (u8ro_read asegs m2 b (rs ++ [b0]) i yb _ STRB2 NYB ltac:(lia) eq_refl) as RD2.
step. step. step. step. step.
step. rewrite zxb_eqb0.
destruct CASE as [(Hlt & NS) | (Hlast & -> & ->)].
- unfold cmp_stop in NS. apply orb_false_iff in NS. destruct NS as (NS1 & NS2). apply negb_false_iff in NS1.
rewrite NS2. cbv iota.
step. rewrite zxb_eqb, NS1. cbv iota.
apply (IH (i + 1)); lia.
- replace (i + 1) with (Z.of_nat k) by lia.
destruct (bv_unsigned xa =? 0) eqn:E0; cbv iota; [apply POST|].
step. rewrite zxb_eqb.
unfold cmp_stop in STOP. rewrite E0, orb_false_r in STOP. apply negb_true_iff in STOP. rewrite STOP. cbv iota.
apply POST. }
apply (LOOP k 0); lia. }
intros x10.

assert (TAILG : forall (xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 w5 w6 w7 w8 w11 q3 q4 q5 q6 : word) mz,
munch [(lo, bv_unsigned sp)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
bytes_at asegs mz a (ls ++ [b0]) -> bytes_at asegs mz b (rs ++ [b0]) ->
stk asegs mz lo (bv_unsigned sp + -104) ->
rw_cells asegs mz (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7
w2 w3 w4 w5 w6 w7 w8 (zxb xa) (zxb xb) w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x50448) fc None mz (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 w5 w6 w7 w8 w11 q3 q4 q5 q6 mz MUz WMz MIz STRAz STRBz STz FRz.
repeat match goal with H : ro_cells asegs ?mc _ _ |- _ => clear H | H : stk asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
repeat match goal with H : rw_cells asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
step. step. step. rewrite sltu_sign, <- Ev.
do 4 step.
step. step.
step. step.
do 13 step.
step. step.
eapply K; [exact MUz | exact WMz | exact MIz | exact STRAz | exact STRBz | release_frame FRz STz (bv_unsigned sp); exact STz]. }
remember (Z.of_nat k - 1) as len eqn:Elen.
assert (Ek : Z.of_nat k = len + 1) by lia.
rewrite Ek in *.

assert (CHK2G : forall (xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w6 w7 w11 q3 q4 q5 q6 : word) mz,
munch [(lo, bv_unsigned sp)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
bytes_at asegs mz a (ls ++ [b0]) -> bytes_at asegs mz b (rs ++ [b0]) ->
asan_rt_ok mz -> unpoisoned asegs mz A_SB b (len + 1) ->
stk asegs mz lo (bv_unsigned sp + -104) ->
rw_cells asegs mz (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp q0 q1 q2 w0 (Z_to_bv 64 b) y0 y1 y2 y3 y4 y5 y6 y7
w2 w3 (Z_to_bv 64 (len + 1)) (Z_to_bv 64 len) w6 w7 (Z_to_bv 64 0x183ce8) (zxb xa) (zxb xb) w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x503f8) fc None mz (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w6 w7 w11 q3 q4 q5 q6 mz MUz WMz MIz STRAz STRBz RTz UPz STz FRz.
repeat match goal with H : ro_cells asegs ?mc _ _ |- _ => clear H | H : stk asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
repeat match goal with H : rw_cells asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
rt_cell RTz (0x183ddd, [Z_to_bv 8 0]) STRICT. apply ro_C1_of_bytes_at in STRICT.
rt_cell RTz (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL)) GOT. apply ro_C8_of_bytes_at in GOT.
rt_cell RTz (A_SB_CELL, le8 (Z_to_bv 64 A_SB)) CELL. apply ro_C8_of_bytes_at in CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
step. rewrite ?zxb_zero.
step. if_false.
step. step. rewrite (unsigned_lit b) by lia. rewrite (lxor_ones64 b) by lia. if_falsex.
step. step.
destruct (Z.le_gt_cases 64 len) as [Hbig | Hsmall].
{
if_truex.
step. if_truex.
step. step. step.
stash STRAz. stash STRBz.
destruct (stk_split asegs mz lo (bv_unsigned sp - 2192) _ STz ltac:(lia)) as [ST1z ST2z]. clear STz.
eapply region_is_poisoned_sound_U with (s := b) (n := len + 1) (lo := lo);
[ exact UPz | exact RTz | exact (proj2 (HAM ltac:(lia))) | lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1z
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MIz
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m3 MU3 WM3 MI3 ST1'' UP3 RT3.
unstash STRAz. unstash STRBz.
assert (STRA3 : bytes_at asegs m3 a (ls ++ [b0]))
by (eapply bytes_at_transport; [exact STRAz | exact MU3 | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
assert (STRB3 : bytes_at asegs m3 b (rs ++ [b0]))
by (eapply bytes_at_transport; [exact STRBz | exact MU3 | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
clear STRAz STRBz.
transport_after_call asegs mz m3 MU3 WM3; clear MIz; clear MU3 WM3.
replace (ret_pc (Z_to_bv 64 0x50738)) with (Z_to_bv 64 0x50738) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_true.
eapply TAILG; [exact MUz | exact WMz | exact MI3 | exact STRA3 | exact STRB3
| eapply stk_merge; [exact ST1'' | exact ST2z | lia] | exact FRz]. }

if_falsex.
assert (Hh : b / 8 <= (b + len) / 8 <= b / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (b / 8 + A_SB) UPz ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((b + len) / 8 + A_SB) UPz ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
assert (GS0 : forall j, 0 <= j -> b / 8 + j < (b + len) / 8 ->
ov_read_bytes asegs mz (Z_to_bv 64 (b / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]).
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (b / 8 + 2147450880 + j) with ((b / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPz). replace (b + (len + 1) - 1) with (b + len) by lia. lia. }
assert (HRL : exists v, ov_read_bytes asegs mz (Z_to_bv 64 ((b + len) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (b + len) mod 8 < v))).
{ destruct (unpoisoned_last asegs _ _ _ _ UPz) as (v0 & Hro & Hv). replace (b + (len + 1) - 1) with (b + len) in Hro, Hv by lia.
exists v0. split; [| exact Hv]. apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
clear UPz.
do 3 step.
step. replace (len + b) with (b + len) by lia.
do 2 step; do 2 step; do 2 step.
sh_norm.
replace (2147450880 + b / 8) with (b / 8 + 2147450880) by lia.
replace (2147450880 + (b + len) / 8) with ((b + len) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (b / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((b + len) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.
assert (TAIL2 : forall (xra' q0' q1' q2' w0' w1' y0' y1' y2' y3' y4' y5' y6' y7' w2' w3' w4' w5' w6' w7' w8' w11' q3' q4' q5' q6' : word),
evt asegs Q (MS (mkR xra' (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp q0' q1' q2' w0' w1' y0' y1' y2' y3' y4' y5' y6' y7'
w2' w3' w4' w5' w6' w7' w8' (zxb xa) (zxb xb) w11' q3' q4' q5' q6')
F (Z_to_bv 64 0x50448) fc None mz (seg_rom asegs)))
by (intros; eapply TAILG; eassumption).

assert (LOOP2 : forall (Kn : nat) (i : Z) (y3' y4' : word),
Z.to_nat ((b + len) / 8 - b / 8 - i) = Kn -> 0 <= i -> b / 8 + i < (b + len) / 8 ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp q0 q1 q2 w0 (Z_to_bv 64 b)
(Z_to_bv 64 (b / 8 + 2147450880 + i)) (Z_to_bv 64 ((b + len) / 8 + 2147450880)) (Z_to_bv 64 0) y3' y4' y5 y6 y7
w2 w3 (Z_to_bv 64 (len + 1)) (Z_to_bv 64 (b + len)) w6 w7 (Z_to_bv 64 0x183ce8) (zxb xa) (zxb xb) w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x50714) fc None mz (seg_rom asegs))).
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i y3' y4' HK Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (b / 8 + i + 1) ((b + len) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. apply TAIL2.
- if_truex. replace (b / 8 + 2147450880 + i + 1) with (b / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply TAIL2. }

destruct HRL as (vv & HR & Hv).
assert (Hv8 : 0 <= vv < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step. rewrite (sxb_small vv) by lia. clear HR.
step. rewrite (unsigned_lit (b + len)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (b / 8) ((b + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL2.
+ if_falsex. replace (b / 8 + 2147450880) with (b / 8 + 2147450880 + 0) by lia.
apply (LOOP2 (Z.to_nat ((b + len) / 8 - b / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 vv)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((b + len) mod 8)) (Z_to_bv 64 vv)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (b / 8) ((b + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL2.
+ if_falsex. replace (b / 8 + 2147450880) with (b / 8 + 2147450880 + 0) by lia.
apply (LOOP2 (Z.to_nat ((b + len) / 8 - b / 8 - 0)) 0); lia. }

assert (RT2 : asan_rt_ok m2)
by (eapply asan_rt_ok_transport; [exact RT | exact MU | intros cc Hcc2; pose proof (a4_rt_cells_in_img cc Hcc2); cbn; split; [left; lia | exact I]]).
assert (UPA2 : unpoisoned asegs m2 A_SB a (len + 1))
by (eapply unpoisoned_transport; [exact UPA | exact MU | intros a' k' Ha' Hk'; eapply (shadow_outside_stack A_SB a (len + 1)); try eassumption; unfold A_SB; lia]).
assert (UPB2 : unpoisoned asegs m2 A_SB b (len + 1))
by (eapply unpoisoned_transport; [exact UPB | exact MU | intros a' k' Ha' Hk'; eapply (shadow_outside_stack A_SB b (len + 1)); try eassumption; unfold A_SB; lia]).
clear UPA UPB.
do 2 step.
step. step. if_false.
step. rewrite ?zxb_zero.
step. replace (len + 1 + -1) with len by lia.
step. step.
step. if_false.
step. step. rewrite (unsigned_lit a) by lia. rewrite (lxor_ones64 a) by lia. if_falsex.
step. step.
destruct (Z.le_gt_cases 64 len) as [Hbig | Hsmall].
{
if_truex.
step. if_truex.
step. step. step.
clear STRA STRB. stash STRA2. stash STRB2.
eapply region_is_poisoned_sound_U with (s := a) (n := len + 1) (lo := lo);
[ exact UPA2 | exact RT2 | exact (proj1 (HAM ltac:(lia))) | lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1'
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MI2
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m3 MU3 WM3 MI3 ST1'' UP3 RT3.
unstash STRA2. unstash STRB2.
assert (STRA3 : bytes_at asegs m3 a (ls ++ [b0]))
by (eapply bytes_at_transport; [exact STRA2 | exact MU3 | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
assert (STRB3 : bytes_at asegs m3 b (rs ++ [b0]))
by (eapply bytes_at_transport; [exact STRB2 | exact MU3 | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
assert (UPB3 : unpoisoned asegs m3 A_SB b (len + 1))
by (eapply unpoisoned_transport; [exact UPB2 | exact MU3 | intros a' k' Ha' Hk'; eapply (shadow_outside_stack A_SB b (len + 1)); try eassumption; unfold A_SB; lia]).
clear STRA2 STRB2 UPB2 UPA2 RT2.
transport_after_call asegs m2 m3 MU3 WM3; clear MI2; clear MU3 WM3.
replace (ret_pc (Z_to_bv 64 0x50658)) with (Z_to_bv 64 0x50658) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_true.
eapply CHK2G; [exact MU | exact WM | exact MI3 | exact STRA3 | exact STRB3 | exact RT3 | exact UPB3
| eapply stk_merge; [exact ST1'' | exact ST2 | lia] | exact FR]. }

if_falsex.
assert (CHK2 : forall (xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w6 w7 w11 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp q0 q1 q2 w0 (Z_to_bv 64 b) y0 y1 y2 y3 y4 y5 y6 y7
w2 w3 (Z_to_bv 64 (len + 1)) (Z_to_bv 64 len) w6 w7 (Z_to_bv 64 0x183ce8) (zxb xa) (zxb xb) w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x503f8) fc None m2 (seg_rom asegs)))
by (intros; eapply CHK2G; [exact MU | exact WM | exact MI2 | exact STRA2 | exact STRB2 | exact RT2 | exact UPB2
| eapply stk_merge; [exact ST1' | exact ST2 | lia] | exact FR]).
assert (Hh : a / 8 <= (a + len) / 8 <= a / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (a / 8 + A_SB) UPA2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((a + len) / 8 + A_SB) UPA2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
assert (GS0 : forall j, 0 <= j -> a / 8 + j < (a + len) / 8 ->
ov_read_bytes asegs m2 (Z_to_bv 64 (a / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]).
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (a / 8 + 2147450880 + j) with ((a / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPA2). replace (a + (len + 1) - 1) with (a + len) by lia. lia. }
assert (HRL : exists v, ov_read_bytes asegs m2 (Z_to_bv 64 ((a + len) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (a + len) mod 8 < v))).
{ destruct (unpoisoned_last asegs _ _ _ _ UPA2) as (v0 & Hro & Hv). replace (a + (len + 1) - 1) with (a + len) in Hro, Hv by lia.
exists v0. split; [| exact Hv]. apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
clear UPA2 UPB2 RT2 CHK2G TAILG.
do 3 step.
step. replace (len + a) with (a + len) by lia.
do 2 step; do 2 step; do 2 step.
sh_norm.
replace (2147450880 + a / 8) with (a / 8 + 2147450880) by lia.
replace (2147450880 + (a + len) / 8) with ((a + len) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (a / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((a + len) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

assert (LOOP1 : forall (Kn : nat) (i : Z) (y3' y4' : word),
Z.to_nat ((a + len) / 8 - a / 8 - i) = Kn -> 0 <= i -> a / 8 + i < (a + len) / 8 ->
evt asegs Q (MS (mkR (Z_to_bv 64 0x50360) (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0 t1 t2 sp (Z_to_bv 64 b)
(Z_to_bv 64 (a / 8 + 2147450880 + i)) (Z_to_bv 64 ((a + len) / 8 + 2147450880)) (Z_to_bv 64 0) y3' y4' a5 a6 a7
(Z_to_bv 64 a) ra (Z_to_bv 64 (len + 1)) (Z_to_bv 64 len) (Z_to_bv 64 (len + 1)) s7 (Z_to_bv 64 0x183ce8) (zxb xa) (zxb xb)
(Z_to_bv 64 (bv_unsigned sp + -2176)) t3 t4 t5 t6)
F (Z_to_bv 64 0x50634) fc None m2 (seg_rom asegs))).
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i y3' y4' HK Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (a / 8 + i + 1) ((a + len) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. apply CHK2.
- if_truex. replace (a / 8 + 2147450880 + i + 1) with (a / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply CHK2. }

destruct HRL as (vv & HR & Hv).
assert (Hv8 : 0 <= vv < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step. rewrite (sxb_small vv) by lia. clear HR.
step. rewrite (unsigned_lit (a + len)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (a / 8) ((a + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply CHK2.
+ if_falsex. replace (a / 8 + 2147450880) with (a / 8 + 2147450880 + 0) by lia.
apply (LOOP1 (Z.to_nat ((a + len) / 8 - a / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 vv)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((a + len) mod 8)) (Z_to_bv 64 vv)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (a / 8) ((a + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply CHK2.
+ if_falsex. replace (a / 8 + 2147450880) with (a / 8 + 2147450880 + 0) by lia.
apply (LOOP1 (Z.to_nat ((a + len) / 8 - a / 8 - 0)) 0); lia.
Qed.
End RC__1.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QbFI. Import Qhd4 Qwm6.
Import Qhd4.Mq2.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg Qw5U QnPO.Mq5 QJZd QJZd.Mqg.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma real_memcpy_Z : real_memcpy_specZ_stmt.
Proof.
unfold real_memcpy_specZ_stmt. intros until junk. intros SRC SRCL DST DISJ MI.
eapply evt_mono; [eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk);
[exact SRC | exact SRCL | exact DST | exact DISJ | exact MI] |].
intros ms' P. exact P.
Qed.

Theorem amemset_U : amemset_spec_U.
Proof. exact amemset_sound_U. Qed.

Theorem amemcpy_U : amemcpy_spec_U.
Proof. exact (amemcpy_sound_U real_memcpy_Z). Qed.

Theorem astrlen_U : astrlen_spec_U.
Proof. exact astrlen_sound_U. Qed.

Section C.
Variable HIx : heap_iface_A A4L.

Lemma blk_app_bounds : forall A LB LM FRS B m md ab nb x k,
HEAPA A4L HIx A LB LM FRS B m md -> In (ab, nb) LB -> ab <= x -> x + k <= ab + nb ->
0 <= x /\ x + k <= 2^47 /\ x + k <= alloc_ceiling.
Proof.
intros A LB LM FRS B m md ab nb x k HP Hblk Hx Hk.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ab nb HP ltac:(apply in_or_app; left; exact Hblk)) as (Hnb0 & _ & Hpos & Hhi & _).
rc_pose_range RC__. unfold alloc_ceiling in *. lia.
Qed.

Lemma blk_app_mem : forall A LB LM FRS B m md ab nb x k,
HEAPA A4L HIx A LB LM FRS B m md -> In (ab, nb) LB -> ab <= x -> x + k <= ab + nb -> app_mem x k.
Proof.
intros A LB LM FRS B m md ab nb x k HP Hblk Hx Hk.
destruct (blk_app_bounds _ _ _ _ _ _ _ ab nb x k HP Hblk Hx Hk) as (B1 & B2 & B3).
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ ab nb HP ltac:(apply in_or_app; left; exact Hblk)) as AM.
cbn [hl_sb A4L] in AM. unfold app_mem, A_SB, A_HMB in *. rc_pose_range RC__. unfold alloc_ceiling in *. lia.
Qed.

Theorem amemset_A : amemset_spec_A HIx.
Proof.
unfold amemset_spec_A. intros until Q. intros HP Hblk Hab Hdn Ha0 Ha1 Ha2 Hc Hn DST ST LO LOS SPA HT MI RA K.
destruct (blk_app_bounds _ _ _ _ _ _ _ ab nb d n HP Hblk Hab Hdn) as (B1 & B2 & B3).
eapply (amemset_U ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d c n lo old Q);
try eassumption; try lia.
- intros _. eapply unpoisoned_of_blk; [exact HP | exact Hblk | lia | lia | lia].
- eapply asan_rt_ok_of_HEAPA; exact HP.
Qed.

Theorem amemcpy_any_A : amemcpy_any_spec_A HIx.
Proof.
unfold amemcpy_any_spec_A. intros until Q. intros HP Hblk Hab Hdn Hsblk Hsb Hsn Ha0 Ha1 Ha2 Hn Hdisj DST SRC SRCL ST LO LOS SPA HT MI RA K.
destruct (blk_app_bounds _ _ _ _ _ _ _ ab nb d n HP Hblk Hab Hdn) as (B1 & B2 & B3).
destruct (blk_app_bounds _ _ _ _ _ _ _ sb nsb s n HP Hsblk Hsb Hsn) as (C1 & C2 & C3).
eapply (amemcpy_U ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s n lo old src Q);
try eassumption; try lia.
- intros Hpos. eapply unpoisoned_of_blk; [exact HP | exact Hblk | lia | lia | lia].
- intros Hpos. eapply unpoisoned_of_blk; [exact HP | exact Hsblk | lia | lia | lia].
- eapply asan_rt_ok_of_HEAPA; exact HP.
- right. split; [eapply blk_app_mem; [exact HP | exact Hblk | lia | lia] | eapply blk_app_mem; [exact HP | exact Hsblk | lia | lia]].
Qed.

Theorem astrlen_any_A : astrlen_any_spec_A HIx.
Proof.
unfold astrlen_any_spec_A. intros until Q. intros HP Hsblk Hsb Hsn Ha0 NONUL Hlen STR PAD SLK ST LO LOS SPA HT MI RA K.
destruct (blk_app_bounds _ _ _ _ _ _ _ sb nsb s (Z.of_nat (length str) + 1) HP Hsblk Hsb ltac:(lia)) as (C1 & C2 & C3).
eapply (astrlen_U ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s lo str slack Q);
try eassumption; try lia.
- eapply unpoisoned_of_blk; [exact HP | exact Hsblk | lia | lia | lia].
- eapply asan_rt_ok_of_HEAPA; exact HP.
- right. eapply blk_app_mem; [exact HP | exact Hsblk | lia | lia].
Qed.
End C.
End RC__1.
End Mq8.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnPO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnPO.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section WithSegs.
Variable segs : list Segment.

Lemma agree_of_munchX : forall BS W m m',
munch W m m' -> wmono segs m m' -> (forall a k x, In (a, k) BS -> a <= x < a + k -> outside W x) -> agree_on segs BS m m'.
Proof.
intros BS W m m' MU WM HO x Hx (b & Hb & Hr). destruct b as [a k]. cbn in Hr. split.
- apply MU. rewrite wa_unsigned by lia. exact (HO a k x Hb Hr).
- apply WM.
Qed.

Lemma hdr_set_pb : forall m m' p (c1 c2 c3 c5 c6 : cell) (pb0 pb : Z) cs,
csize c1 = 4%nat -> csize c2 = 4%nat -> csize c3 = 8%nat ->
rw_cells segs m p ([c1; c2; c3; C8 (wz pb0); c5; c6] ++ cs) ->
munch [(p + 16, p + 24)] m m' -> wmono segs m m' -> rw_cells segs m' (p + 16) [C8 (wz pb)] ->
rw_cells segs m' p ([c1; c2; c3; C8 (wz pb); c5; c6] ++ cs).
Proof.
intros m m' p c1 c2 c3 c5 c6 pb0 pb cs S1 S2 S3 H MU WM H16.
apply (proj1 (rw_cells_app segs m p [c1; c2; c3] _)) in H as [HA H]. cbn [cells_size Nat.add] in H. rewrite S1, S2, S3 in H. cbn in H.
apply (proj1 (rw_cells_app segs m (p + Z.of_nat 16) [C8 (wz pb0)] _)) in H as [_ HB]. cbn [cells_size csize Nat.add] in HB.
apply (proj2 (rw_cells_app segs m' p [c1; c2; c3] _)). split.
- eapply rw_cells_transport; [exact HA | exact MU | exact WM | cbn [cells_size Nat.add disjoint_from]; rewrite S1, S2, S3; cbn; lia].
- cbn [cells_size Nat.add]. rewrite S1, S2, S3. change (4 + (4 + (8 + 0)))%nat with 16%nat.
apply (proj2 (rw_cells_app segs m' (p + Z.of_nat 16) [C8 (wz pb)] _)). split.
+ replace (p + Z.of_nat 16) with (p + 16) by lia. exact H16.
+ cbn [cells_size csize Nat.add]. eapply rw_cells_transport; [exact HB | exact MU | exact WM | cbn [disjoint_from]; lia].
Qed.

Section Node.
Variable fn : fnaddrs.
Lemma jnode_agree : forall s m m' BS REST p rc pb0,
jnode segs fn s m REST p rc pb0 -> agree_on segs BS m m' -> incl REST BS -> jnode segs fn s m' REST p rc pb0.
Proof.
intros s m m' BS REST p rc pb0 J AG Hi. destruct s as [|[|]| |[|]|kids|kids]; cbn in J |- *.
- destruct J as (b & junk & ER & H). exists b, junk. split; [exact ER|].
eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
- destruct J as (bits & ud & udn & uds & ER & HU & H & HC). exists bits, ud, udn, uds. split; [exact ER|]. split; [exact HU|]. split.
+ eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
+ eapply cstr_agree; [exact HC | exact AG | apply Hi; rewrite ER; right; left; reflexivity | destruct HC as (HC1 & _); lia].
- destruct J as (bits & ER & HS & H). exists bits. split; [exact ER|]. split; [exact HS|].
eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
- destruct J as (cty & v & junk & ER & HC & H). exists cty, v, junk. split; [exact ER|]. split; [exact HC|].
eapply rw_cells_agree; [exact H | exact AG | exists p, 56; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
- destruct J as (len & pd & pdn & str & junk2 & ER & HL & HS & HP & H & HD).
exists len, pd, pdn, str, junk2. split; [exact ER|]. split; [exact HL|]. split; [exact HS|]. split; [exact HP|]. split.
+ eapply rw_cells_agree; [exact H | exact AG | exists p, 56; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
+ eapply rw_cells_agree; [exact HD | exact AG | exists pd, pdn; split; [apply Hi; rewrite ER; right; left; reflexivity |]].
destruct HD as [[Hwf _] _]. cbn in Hwf. cbn [cells_size csize]. lia.
- destruct J as (len & str & junk & ER & HL & HS & H). exists len, str, junk. split; [exact ER|]. split; [exact HL|]. split; [exact HS|].
eapply rw_cells_agree; [exact H | exact AG | exists p, (str_objsize len); split; [apply Hi; rewrite ER; left; reflexivity |]].
cbn [cells_size csize]. unfold str_objsize. lia.
- destruct J as (t & TBS & kvs & KBS & ER & H & HT & L1 & L2 & KIDS). exists t, TBS, kvs, KBS.
split; [exact ER|]. split; [|split; [|split; [exact L1 | split; [exact L2|]]]].
+ eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
+ eapply lhtab2_agree; [exact HT | exact AG | intros b Hb; apply Hi; rewrite ER; right; apply in_or_app; left; exact Hb].
+ eapply (kids_okv_agree segs fn); [exact KIDS | exact AG | intros b Hb; apply Hi; rewrite ER; right; apply in_or_app; right; exact Hb].
- destruct J as (a & ABS & ps & KBS & ER & H & HA & L1 & L2 & KIDS). exists a, ABS, ps, KBS.
split; [exact ER|]. split; [|split; [|split; [exact L1 | split; [exact L2|]]]].
+ eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
+ eapply alist_agree; [exact HA | exact AG | intros b Hb; apply Hi; rewrite ER; right; apply in_or_app; left; exact Hb].
+ eapply (kids_okp_agree segs fn); [exact KIDS | exact AG | intros b Hb; apply Hi; rewrite ER; right; apply in_or_app; right; exact Hb].
Qed.

Lemma jnode_set_pb : forall s m m' REST p rc pb0 pb,
jnode segs fn s m REST p rc pb0 ->
munch [(p + 16, p + 24)] m m' -> wmono segs m m' -> rw_cells segs m' (p + 16) [C8 (wz pb)] ->
(forall a k, In (a, k) (tl REST) -> a + k <= p + 16 \/ p + 24 <= a) ->
jnode segs fn s m' REST p rc pb.
Proof.
intros s m m' REST p rc pb0 pb J MU WM H16 DISJ.
assert (AGx : forall rest, (forall a k, In (a, k) rest -> a + k <= p + 16 \/ p + 24 <= a) -> agree_on segs rest m m').
{ intros rest D. eapply agree_of_munchX; [exact MU | exact WM |]. intros a k x Hin Hx. cbn. pose proof (D a k Hin). lia. }
destruct s as [|[|]| |[|]|kids|kids]; cbn in J |- *; unfold jhdr_cells in *.
- destruct J as (b & junk & ER & H). exists b, junk. split; [exact ER|]. cbn [app] in H |- *.
eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_; _]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
- destruct J as (bits & ud & udn & uds & ER & HU & H & HC). exists bits, ud, udn, uds. split; [exact ER|]. split; [exact HU|]. rewrite ER in DISJ. cbn [tl] in DISJ. split.
+ eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
+ eapply cstr_agree; [exact HC | apply (AGx _ DISJ) | left; reflexivity | destruct HC as (HC1 & _); lia].
- destruct J as (bits & ER & HS & H). exists bits. split; [exact ER|]. split; [exact HS|].
eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
- destruct J as (cty & v & junk & ER & HC & H). exists cty, v, junk. split; [exact ER|]. split; [exact HC|].
eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_; _; _]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
- destruct J as (len & pd & pdn & str & junk2 & ER & HL & HS & HP & H & HD). rewrite ER in DISJ. cbn [tl] in DISJ.
exists len, pd, pdn, str, junk2. split; [exact ER|]. split; [exact HL|]. split; [exact HS|]. split; [exact HP|]. split.
+ eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_; _]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
+ eapply rw_cells_agree; [exact HD | apply (AGx _ DISJ) | exists pd, pdn; split; [left; reflexivity|]].
destruct HD as [[Hwf _] _]. cbn in Hwf. cbn [cells_size csize]. lia.
- destruct J as (len & str & junk & ER & HL & HS & H). exists len, str, junk. split; [exact ER|]. split; [exact HL|]. split; [exact HS|].
eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_; _]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
- destruct J as (t & TBS & kvs & KBS & ER & H & HT & L1 & L2 & KIDS). exists t, TBS, kvs, KBS. rewrite ER in DISJ. cbn [tl] in DISJ.
split; [exact ER|]. split; [|split; [|split; [exact L1 | split; [exact L2|]]]].
+ eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
+ eapply lhtab2_agree; [exact HT | apply (AGx _ DISJ) | intros b Hb; apply in_or_app; left; exact Hb].
+ eapply (kids_okv_agree segs fn); [exact KIDS | apply (AGx _ DISJ) | intros b Hb; apply in_or_app; right; exact Hb].
- destruct J as (a & ABS & ps & KBS & ER & H & HA & L1 & L2 & KIDS). exists a, ABS, ps, KBS. rewrite ER in DISJ. cbn [tl] in DISJ.
split; [exact ER|]. split; [|split; [|split; [exact L1 | split; [exact L2|]]]].
+ eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
+ eapply alist_agree; [exact HA | apply (AGx _ DISJ) | intros b Hb; apply in_or_app; left; exact Hb].
+ eapply (kids_okp_agree segs fn); [exact KIDS | apply (AGx _ DISJ) | intros b Hb; apply in_or_app; right; exact Hb].
Qed.
End Node.

Definition jty (s : jshape) : Z :=
match s with Sbool => JT_BOOLEAN | Sdouble _ => JT_DOUBLE | Sint => JT_INT | Sstr _ => JT_STRING | Sobj _ => JT_OBJECT | Sarr _ => JT_ARRAY end.

Lemma jty_range : forall s, 0 <= jty s <= 6.
Proof. destruct s; cbn; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY; lia. Qed.

Lemma jnode_hdrT : forall fn s m REST p rc pb0, jnode segs fn s m REST p rc pb0 ->
exists n udel ud cs rest, REST = (p, n) :: rest /\ 48 <= n /\
rw_cells segs m p ([C4 (wz (jty s)); C4 (wz rc); C8 (wz (fn_ofF fn s)); C8 (wz pb0); C8 (wz udel); C8 (wz ud)] ++ cs).
Proof.
intros fn s m REST p rc pb0 J. destruct s as [|[|]| |[|]|kids|kids]; cbn in J.
- destruct J as (b & junk & -> & H). exists 48, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (bits & ud & udn & uds & -> & _ & H & _). exists 48, (fn_free_userdata fn), ud. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (bits & -> & _ & H). exists 48, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (cty & v & junk & -> & _ & H). exists 56, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (len & pd & pdn & str & junk2 & -> & _ & _ & _ & H & _). exists 56, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (len & str & junk & -> & Hl & _ & H). exists (str_objsize len), 0, 0. eexists. exists []. split; [reflexivity|]. split; [unfold str_objsize; lia|]. exact H.
- destruct J as (t & TBS & kvs & KBS & -> & H & _). exists 48, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (a & ABS & ps & KBS & -> & H & _). exists 48, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
Qed.

Lemma jnode_length_ge : forall fn s m REST p rc pb0, jnode segs fn s m REST p rc pb0 -> nblk0 s <= Z.of_nat (length REST).
Proof.
intros fn s m REST p rc pb0 J. destruct s as [|[|]| |[|]|kids|kids]; cbn [jnode] in J.
- destruct J as (b & junk & -> & _). cbn [length nblk0]. lia.
- destruct J as (bits & ud & udn & uds & -> & _). cbn [length nblk0]. lia.
- destruct J as (bits & -> & _). cbn [length nblk0]. lia.
- destruct J as (cty & v & junk & -> & _). cbn [length nblk0]. lia.
- destruct J as (len & pd & pdn & str & junk2 & -> & _). cbn [length nblk0]. lia.
- destruct J as (len & str & junk & -> & _). cbn [length nblk0]. lia.
- destruct J as (t & TBS & kvs & KBS & -> & _ & (tbl & size & es & svs & Ekvs & -> & _) & L1 & L2 & OK).
assert (LK : nblk0k kids <= Z.of_nat (length (concat KBS))).
{ eapply (kids_okv_length_ge segs fn m kids); [| exact OK]. intros s Hs bs0 p0 rc0 JV0. destruct (jval_length_ge segs fn s m bs0 p0 rc0 JV0) as (pb1 & PBS1 & REST1 & -> & _ & H). rewrite length_app. lia. }
assert (LKe : length es = length kids) by (rewrite Ekvs, length_map in L1; exact L1).
unfold lh_blocks. rewrite nblk0_obj. cbn [length app]. rewrite length_app, length_map. lia.
- destruct J as (a & ABS & ps & KBS & -> & _ & (arr & size & junk & -> & _) & L1 & L2 & OK).
assert (LK : nblk0k kids <= Z.of_nat (length (concat KBS))).
{ eapply (kids_okp_length_ge segs fn m kids); [| exact OK]. intros s Hs bs0 p0 rc0 JV0. destruct (jval_length_ge segs fn s m bs0 p0 rc0 JV0) as (pb1 & PBS1 & REST1 & -> & _ & H). rewrite length_app. lia. }
rewrite nblk0_arr. cbn [length app]. lia.
Qed.
Lemma jval_fresh_node : forall fn s m BS p rc w, jval segs fn s m BS p rc -> jtx s BS = Some (w, []) -> jnode segs fn s m BS p rc 0.
Proof.
intros fn s m BS p rc w JV H.
destruct (proj1 (jval_split segs fn _ _ _ _ _) JV) as (pb1 & PBS & REST1 & -> & OP1 & JN).
pose proof (jnode_length_ge _ _ _ _ _ _ _ JN) as LE.
pose proof (jtx_length _ _ _ _ H) as L. rewrite length_app in L. cbn [length] in L.
assert (PBS = []) by (destruct PBS; [reflexivity | cbn [length] in L; lia]). subst PBS. rewrite app_nil_r.
destruct OP1 as [[-> _] | [_ (buf & bpos & size & content & E & _)]]; [exact JN | discriminate E].
Qed.
End WithSegs.
End RC__1.
