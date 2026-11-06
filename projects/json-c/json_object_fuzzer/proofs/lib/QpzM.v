(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Qc6I QJFf QVsB QDM6 QCiC Qpj5 QdZp QTVW QnRU QteI Qu3b QQNJ QHig QwAs Q0Do Q6sh QKTr QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 Q9Ho QYyZ QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Qc6I QJFf QVsB QDM6.
Import QCiC.Mq1 Qpj5.Mq1 QdZp.
Import QTVW.Mq4 QnRU.Mq4 QteI.Mq1 Qu3b.Mq0 QQNJ.Mq1 QQNJ.Mq2 QQNJ.Mq0.

Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QYyZ.Mq2.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.

Theorem fwritex_stderr_proof {BAND : Band} : fwritex_stderr_stmt.
Proof.
unfold fwritex_stderr_stmt, out_stmt. intros St B. intros until canary.
intros SINK SRC BYT BSL SZ -> -> ST LO GLO SPHI TOP SSP MI SEPF SEPB SEPS1 SEPS2 SEPS3 TSA.
destruct st as [buf st].
destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO & B47 & ISHm). cbn [fst] in FC, BUF, LEN.
unfold OUT_DEPTH, GLOBALS_TOP, INTERNAL_BUFSIZ, TOPOK_none in *.
destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS.
assert (LSB : length (zb bs) = length bs) by apply zb_length.
pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0.
assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
assert (LS : 0 <= zlength bs) by (unfold zlength; lia).
unfold zlength in *.
set (S := bv_unsigned a0) in *.
assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).

pose proof BUF as BUF0.
apply (rw_cells_split_CB asegs _ _ [] 80 (zb buf ++ rest) [] [length buf; 80 - length buf]%nat) in BUF; [| cbn; unfold zlength in *; lia].
cbn [mk_CB_cells app] in BUF.
rewrite firstn_app, zb_length, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in BUF by (rewrite zb_length; lia).
rewrite skipn_app, zb_length, Nat.sub_diag, skipn_O, skipn_all2 in BUF by (rewrite zb_length; lia). cbn [app] in BUF.
apply (proj1 (QnRU.Mq3.rw_cells_app asegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite ?firstn_all2 in BUFb by lia.
unfold implM, OUT_stderr. cbv beta iota zeta.
destruct (OUT_MAX <? zlength bs) eqn:OGUARD.
{
cbv beta iota zeta. apply impl_ret_unr. }
cbv beta iota zeta.
assert (OG : zlength bs <= OUT_MAX) by (apply Z.ltb_ge; exact OGUARD). unfold OUT_MAX, zlength in OG.
destruct (80 - zlength buf <? zlength bs) eqn:CMP.
-
pose proof (proj1 (Z.ltb_lt _ _) CMP) as CMP'. unfold zlength in CMP'.
eapply impl_evt.
{ eapply fwx_nofit with (lo := lo); [exact FC | exact EA0 | reflexivity | reflexivity | lia | lia | unfold zlength in *; lia | lia | lia | reflexivity | exact ST | lia | lia | exact MI | lia]. }
cbv beta. intros ms1 PO.
destruct PO as (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
unfold file_cells in FC.
transport_after_call asegs m m1 MU1 WM1.
unfold INTERNAL_BUFSIZ. cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with true by (symmetry; exact CMP) end. cbv beta iota zeta.
eapply impl_ebind.
{ eapply (stdio_write_spec (St:=St)) with (B := B) (fd := 2) (Fp := 960096) (buf := buf) (s := bs) (S := S) (lo := lo) (canary := canary)
(wend := B + 80) (bufsize := 80) (mode := mode) (lbf := 0xffffffff) (tail := tail) (flags := flags) (wfn := F_STDIO_WRITE);
try reflexivity.
- exact FC.
- apply (bytes_at_ext _ _ _ _ _ (rw_cells_bytes_at _ _ _ _ BUFa)). cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
- exact SRC.
- lia.
- exact ST1.
- unfold STDIO_WRITE_DEPTH. lia.
- lia.
- split; [exact GOT | exact GUARD].
- exact MI1.
- lia. - lia.
- unfold got_ssp. lia.
- unfold ssp_guard. lia.
- lia. - lia.
- unfold zlength. lia.
- lia.
- unfold zlength. lia.
- lia.
- unfold zlength. lia.
- right. unfold zlength. lia.
- unfold zlength. lia.
- first [lia | rewrite unsigned_lit by lia; lia]. }
cbv beta. intros [[] st'] ms' PO. cbn [fst snd] in PO.
destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
unfold STDIO_WRITE_DEPTH in MU2.
apply impl_ret_ok. cbn [fst snd]. apply evt_done.

pose proof (rw_cells_transport asegs _ m1 m2 _ _ BUF0 MU2 WM2 ltac:(cbn; lia)) as BUF2.
pose proof (bytes_at_transport asegs _ m1 m2 _ _ SRC MU2 ltac:(cbn; rewrite LSB; lia)) as SRC2.
unfold out_post, SR. do 16 eexists. split; [reflexivity|].
split. { apply (munch_trans _ m m1 m2).
- eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; Q0z1.lia3.
- eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; Q0z1.lia3. }
split; [eapply wmono_trans; [exact WM1 | exact WM2] |]. split; [exact MI2|]. split; [exact ST2|].
split.
{
exists flags, mode, tail, (zb buf ++ rest). cbn [fst].
split; [rewrite Z.add_0_r; exact FC2|]. split; [exact FL32|]. split; [exact FL8|].
split; [exact BUF2|]. split; [| split; [exact BHI| split; [exact BGLO| split; [exact B47|]]]].
2:{ eapply (ISH_munch_zone m m2 [(lo, bv_unsigned sp); (960096, 960096 + 232); (B, B + 80)]); [exact ISHm| | eapply wmono_trans; [exact WM1| exact WM2]| zforalls].
apply (munch_trans _ m m1 m2); [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros; Q0z1.lia3. }
unfold zlength. cbn [length]. rewrite length_app, zb_length. lia. }
split; [exact SSP2 | exact SRC2].
-
pose proof (proj1 (Z.ltb_ge _ _) CMP) as CMP'. unfold zlength in CMP'.
cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with false by (symmetry; exact CMP) end. cbv beta iota zeta.
apply impl_ret_ok. cbn [fst snd].
unfold file_cells in FC.
eapply evt_mono.
{ eapply (fwx_fit_plain ra sp gp tp t0 t1 t2 s0 s1 a0) with (lo := lo) (cap := (80 - length buf)%nat) (src := zb bs) (S := S)
(Fp := 960096) (wend := B + 80) (wpos := B + Z.of_nat (length buf)) (junk := rest);
[ exact FC | exact BUFb | lia | exact SRC | rewrite LSB; reflexivity | exact EA0 | reflexivity | reflexivity | try lia .. ];
[exact ST | exact MI |  unfold QnRU.Mq3.FWRITEX_STACK, MEMCPY_ICPT_STACK; lia
| exact (proj2 (proj2 ISHm)) | exact (proj1 (proj2 ISHm))
| apply (rng_ok_of_ash _ _ _ (proj1 ISHm)); [first [exact SZ| match goal with |- szone _ (Z.of_nat (length ?x)) => replace (length x) with (length bs) by (symmetry; exact LSB) end; exact SZ]| lia]
| apply (rng_ok_of_ash _ _ _ (proj1 ISHm)); [unfold szone; right; idtac; lia| lia] ].
}
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2).
unfold out_post, SR. do 16 eexists.
split. { reflexivity. }
split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; Q0z1.lia3. }
split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
assert (GOT2 : rw_cells asegs m2 945024 [C8 (Z_to_bv 64 6565536)]).
{ eapply (rw_cells_transport asegs _ m m2); [exact GOT | exact MU2 | exact WM2 | cbn; lia]. }
assert (GUARD2 : rw_cells asegs m2 6565536 [C8 canary]).
{ eapply (rw_cells_transport asegs _ m m2); [exact GUARD | exact MU2 | exact WM2 | cbn; lia]. }
assert (BUFa2 : rw_cells asegs m2 B [CB (length buf) (zb buf)]).
{ eapply (rw_cells_transport asegs _ m m2); [exact BUFa | exact MU2 | exact WM2 | cbn; lia]. }
split.
{
exists flags, mode, tail, (skipn (length (zb bs)) rest). cbn [fst].
split. { unfold zlength. rewrite length_app, Nat2Z.inj_add, Z.add_assoc. exact FC2. }
split; [exact FL32|]. split; [exact FL8|].
split.
{
assert (J : rw_cells asegs m2 B ([] ++ [CB (length buf) (zb buf); CB (length (zb bs)) (zb bs); CB (80 - length buf - length (zb bs))%nat (skipn (length (zb bs)) rest)] ++ [])).
{ cbn [app]. apply (proj2 (QnRU.Mq3.rw_cells_app asegs _ _ [_] _)); split; [exact BUFa2|].
cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
rewrite zb_app, <- app_assoc. rewrite LSB in J |- *.
replace (length buf + (length bs + (80 - length buf - length bs + 0)))%nat with 80%nat in J by lia. exact J. }
split; [| split; [exact BHI| split; [exact BGLO| split; [exact B47|]]]].
2:{ eapply (ISH_munch_zone m m2); [exact ISHm| exact MU2| exact WM2| zforalls]. }
unfold zlength. rewrite length_app, length_skipn, LSB. lia. }
split; [split; [exact GOT2 | exact GUARD2] | exact SRC2].
Qed.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u Qcrs QCNF QoNr QvDJ QoBx Qs9x QC9y QcfN QFd5 Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Q13u QDM6 QJFf.Mq0 QwAs.Mq1 Qc6I QJFf QVsB.

Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp QvDJ.Mq3.
Import Qu3b.Mq3.
Import QTVW.Mq1 Qu3b.Mq1 QTVW.Mq2 QnRU.Mq5 QnRU.Mq3 QnRU.Mq4 QteI.Mq1.
Import QCNF.Mq0.
Import QoBx Qu3b.Mq0.
Import Qs9x QC9y QcfN.Mq0.
Import QQNJ.Mq1.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QFd5.Mq0 QYyZ.Mq1 QteI.Mq2.
Import QlES.

Import Q0z1. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.

Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.

Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac show_goal := match goal with |- ?G => idtac "GOAL:" G end.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac plia := unfold zlength, got_ssp, ssp_guard, PC_DEPTH, OUT_DEPTH, GLOBALS_TOP, FMT_FP_DEPTH, INT_MAX in *; lia.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.

Tactic Notation "callw" tactic3(tac) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | post_call segs m ]
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac br K := brf K; try (exfalso; lia).

Ltac fixr := try (rewrite !swrap32_small by lia); try (rewrite !Z.add_0_r).

Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end.

Definition hide (P : Prop) := P.
Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac glo_lia :=
unfold zlength, zrepeat; rewrite ?repeat_length, ?length_firstn, ?length_app, ?length_map; cbn [length]; try rewrite Z2Nat.id by lia;
first [ lia | unfold GLOBALS_TOP, PC_DEPTH; lia | unfold GLOBALS_TOP, PC_DEPTH, zlength in *; lia ].

Ltac ienter := lazymatch goal with |- Qpj5.Mq1.implM _ _ _ _ _ => unfold Qpj5.Mq1.implM; apply impl_from_evt | |- Qc6I.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
lazymatch goal with |- Qc6I.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Qpj5.Mq1.implM asegs c s Q ms) | _ => idtac end.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma nth_error_zb : forall l i c, nth_error l i = Some c -> nth_error (zb l) i = Some (Z_to_bv 8 c).
Proof. intros l i c H. unfold zb. rewrite nth_error_map, H. reflexivity. Qed.
Lemma znth_nth_error : forall l i, (0 <= i < zlength l)%Z -> nth_error l (Z.to_nat i) = Some (znth l i).
Proof.
intros l i Hi. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
destruct (nth_error l (Z.to_nat i)) as [c|] eqn:E.
- rewrite (nth_error_nth _ _ _ E). reflexivity.
- apply nth_error_None in E. unfold zlength in Hi. lia.
Qed.
Lemma zbytes_read : forall m A l i a,
bytes_at asegs m A (zb l) -> (0 <= i < zlength l)%Z -> a = wa (A + i) ->
ov_read_bytes asegs m a 1 = Some [Z_to_bv 8 (znth l i)].
Proof.
intros m A l i a HB Hi ->.
eapply (u8ro_read asegs m A (zb l) i); [exact HB | | lia | reflexivity].
apply nth_error_zb. apply znth_nth_error. exact Hi.
Qed.
Lemma Forall_znth : forall (P : Z -> Prop) l i, Forall P l -> (0 <= i < zlength l)%Z -> P (znth l i).
Proof.
intros P l i HF Hi. apply (proj1 (Forall_forall P l) HF). unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
apply nth_In. unfold zlength in Hi. lia.
Qed.

Lemma land_lxor_distr : forall a b m, Z.land (Z.lxor a b) m = Z.lxor (Z.land a m) (Z.land b m).
Proof. intros. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.lxor_spec, !Z.land_spec. destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity. Qed.

Section Sfx.
Variable fmt : list Z.
Definition sfx (k : Z) : list Z := skipn (Z.to_nat k) fmt.
Lemma sfx_cons : forall k, (0 <= k < zlength fmt)%Z -> sfx k = znth fmt k :: sfx (k + 1).
Proof.
intros k Hk. unfold sfx. rewrite Z2Nat.inj_add, Nat.add_1_r by lia.
pose proof (znth_nth_error fmt k Hk) as E.
destruct (nth_error_split fmt (Z.to_nat k) _ E) as (pre & post & Efmt & Hlen).
rewrite Efmt at 1 2. rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. cbn [skipn app].
rewrite <- Efmt. f_equal. rewrite Efmt at 1. change (pre ++ znth fmt k :: post) with (pre ++ ([znth fmt k] ++ post)).
rewrite app_assoc, skipn_app, skipn_all2 by (rewrite length_app; cbn; lia). rewrite length_app. cbn [length].
replace (S (Z.to_nat k) - (length pre + 1))%nat with 0%nat by lia. reflexivity.
Qed.
Lemma sfx_nil : forall k, (zlength fmt <= k)%Z -> sfx k = [].
Proof. intros k Hk. unfold sfx. apply skipn_all2. unfold zlength in Hk. lia. Qed.
Lemma sfx_skipn : forall n k, (0 <= k)%Z -> skipn n (sfx k) = sfx (k + Z.of_nat n).
Proof. intros n k Hk. unfold sfx. rewrite skipn_skipn. f_equal. lia. Qed.
Lemma sfx_length : forall k, (0 <= k <= zlength fmt)%Z -> zlength (sfx k) = (zlength fmt - k)%Z.
Proof. intros k Hk. unfold sfx, zlength in *. rewrite length_skipn. lia. Qed.
Lemma sfx_cons_inv : forall k c s, (0 <= k)%Z -> sfx k = c :: s -> (k < zlength fmt)%Z /\ c = znth fmt k /\ s = sfx (k + 1).
Proof.
intros k c s Hk E. destruct (Z.lt_ge_cases k (zlength fmt)) as [Hlt|Hge].
- rewrite sfx_cons in E by lia. injection E as <- <-. split; [exact Hlt| split; reflexivity].
- rewrite sfx_nil in E by lia. discriminate.
Qed.

Lemma lit_run_firstn : forall s, lit_run s = firstn (length (lit_run s)) s.
Proof. induction s as [|c s IH]; cbn; [reflexivity|]. destruct ((c =? 0) || (c =? 37))%Z; cbn; [reflexivity|]. f_equal. exact IH. Qed.
Lemma lit_run_length : forall s, (length (lit_run s) <= length s)%nat.
Proof. induction s as [|c s IH]; cbn; [lia|]. destruct ((c =? 0) || (c =? 37))%Z; cbn; lia. Qed.
Lemma lit_run_in : forall s j c, nth_error (lit_run s) j = Some c -> c <> 0%Z /\ c <> 37%Z.
Proof.
induction s as [|c s IH]; intros j c' H; cbn in H. { destruct j; discriminate. }
destruct (Z.eqb_spec c 0); [destruct j; discriminate|]. destruct (Z.eqb_spec c 37); [destruct j; discriminate|]. cbn in H.
destruct j as [|j]; cbn in H. { injection H as <-. lia. } eapply IH. exact H.
Qed.
Lemma lit_run_stop : forall s c s', skipn (length (lit_run s)) s = c :: s' -> c = 0%Z \/ c = 37%Z.
Proof.
induction s as [|c s IH]; intros c' s' H; cbn in H; [discriminate|].
destruct (Z.eqb_spec c 0); [cbn in H; injection H as <- _; lia|]. destruct (Z.eqb_spec c 37); [cbn in H; injection H as <- _; lia|].
cbn in H. eapply IH. exact H.
Qed.

Lemma lit_run_sfx : forall i, (0 <= i)%Z -> let n := zlength (lit_run (sfx i)) in
(i + n <= Z.max i (zlength fmt))%Z /\ skipn (length (lit_run (sfx i))) (sfx i) = sfx (i + n)
/\ (forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z
/\ lit_run (sfx i) = firstn (Z.to_nat n) (sfx i).
Proof.
intros i Hi. cbv zeta. pose proof (lit_run_length (sfx i)) as L. unfold zlength.
split. { unfold sfx in L |- *. rewrite length_skipn in L. lia. }
split. { rewrite sfx_skipn by lia. reflexivity. }
split.
- intros j Hj.
assert (E : nth_error (lit_run (sfx i)) (Z.to_nat j) = Some (znth fmt (i + j))).
{ rewrite lit_run_firstn. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 (Z.to_nat j) (length (lit_run (sfx i)))); [|lia].
unfold sfx. rewrite nth_error_skipn. replace (Z.to_nat i + Z.to_nat j)%nat with (Z.to_nat (i + j)) by lia.
apply znth_nth_error. unfold sfx in *. rewrite length_skipn in L. unfold zlength. lia. }
exact (lit_run_in _ _ _ E).
- rewrite Nat2Z.id. apply lit_run_firstn.
Qed.
End Sfx.

Lemma land_M64_id : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma landM64_zero : forall p, (-2^63 <= p < 2^63)%Z -> (Z.land p 18446744073709551615 = 0 <-> p = 0)%Z.
Proof.
intros p Hp. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
split; intros H; [|subst p; reflexivity]. Z.div_mod_to_equations. nia.
Qed.
Lemma if_false_Z : forall a b : Z, (if false then a else b) = b. Proof. reflexivity. Qed.
Lemma if_true_Z : forall a b : Z, (if true then a else b) = a. Proof. reflexivity. Qed.

Lemma div10_magic : forall x, (0 <= x < 2^64)%Z ->
Z.shiftr (Z.shiftr (x * 14757395258967641293) 64) 3 = (x / 10)%Z.
Proof.
intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia. change (2^64 * 2^3)%Z with (2^67)%Z.
pose proof (Z.div_mod x 10 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as R.
pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)) as Q0. pose proof (Z.div_lt_upper_bound x 10 (2^64) ltac:(lia) ltac:(lia)) as Q1.
set (q := (x / 10)%Z) in *. set (s := (x mod 10)%Z) in *. clearbody q s. subst x.
symmetry. apply (Z.div_unique_pos _ _ _ (2 * q + s * 14757395258967641293)%Z).
- change (2^67)%Z with 147573952589676412928%Z. change (2^64)%Z with 18446744073709551616%Z in Q1. lia.
- change (2^67)%Z with 147573952589676412928%Z. lia.
Qed.
Lemma lor48_digit : forall d, (0 <= d < 10)%Z -> Z.lor d 48 = (48 + d)%Z.
Proof.
intros d Hd.
assert (H : (d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9)%Z) by lia.
destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity.
Qed.
Lemma le1_small : forall v, (0 <= v < 256)%Z -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v Hv. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma digits_aux_S : forall f b d y acc,
digits_aux (S f) b d y acc = if y =? 0 then acc else digits_aux f b d (y / b) (d (y mod b) :: acc).
Proof. reflexivity. Qed.
Lemma digits_aux_acc : forall f b d y acc, digits_aux f b d y acc = digits_aux f b d y [] ++ acc.
Proof.
induction f as [|f IH]; intros b d y acc; [reflexivity|]. rewrite !digits_aux_S.
destruct (y =? 0)%Z; [reflexivity|]. rewrite (IH _ _ _ (d (y mod b)%Z :: acc)), (IH _ _ _ [d (y mod b)%Z]). rewrite <- app_assoc. reflexivity.
Qed.
Lemma digits_aux_fuel : forall b f d y acc, (1 < b)%Z -> (0 <= y < b ^ Z.of_nat f)%Z ->
digits_aux f b d y acc = digits_aux (S f) b d y acc.
Proof.
intros b. induction f as [|f IH]; intros d y acc Hb Hy.
- rewrite digits_aux_S. rewrite Z.pow_0_r in Hy. replace y with 0%Z by lia. reflexivity.
- rewrite !digits_aux_S. destruct (Z.eqb_spec y 0); [reflexivity|].
apply IH; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hy by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite Z.mul_comm. lia.
Qed.
Lemma dec_digits_0 : dec_digits 0 = [].
Proof. reflexivity. Qed.
Lemma dec_digits_small : forall x, (1 <= x <= 9)%Z -> dec_digits x = [48 + x]%Z.
Proof.
intros x Hx. unfold dec_digits. change 20%nat with (S (S 18)). rewrite !digits_aux_S.
destruct (Z.eqb_spec x 0); [lia|]. rewrite Z.div_small by lia. cbn [Z.eqb]. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma dec_digits_step : forall x, (10 <= x < 2^64)%Z -> dec_digits x = dec_digits (x / 10) ++ [48 + x mod 10]%Z.
Proof.
intros x Hx. unfold dec_digits at 1. change 20%nat with (S 19). rewrite digits_aux_S.
destruct (Z.eqb_spec x 0); [lia|]. rewrite digits_aux_acc. apply (f_equal2 (@app Z)); [|reflexivity]. unfold dec_digits. apply digits_aux_fuel; [lia|].
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
apply Z.lt_trans with (2^64)%Z; [lia|]. vm_compute. reflexivity.
Qed.
Lemma digits_aux_length : forall f b d y acc, (length (digits_aux f b d y acc) <= f + length acc)%nat.
Proof.
induction f as [|f IH]; intros b d y acc; [cbn; lia|]. rewrite digits_aux_S.
destruct (y =? 0)%Z; [cbn; lia|]. specialize (IH b d (y / b)%Z (d (y mod b)%Z :: acc)). cbn [length] in IH. lia.
Qed.
Lemma dec_digits_length : forall x, (length (dec_digits x) <= 20)%nat.
Proof. intros x. unfold dec_digits. pose proof (digits_aux_length 20 10 (fun v => 48 + v)%Z x []) as L. cbn [length Nat.add] in L. exact L. Qed.
Lemma dec_digits_range : forall x, Forall (fun c => 48 <= c < 58)%Z (dec_digits x).
Proof.
intros x. unfold dec_digits.
assert (G : forall f y acc, Forall (fun c => 48 <= c < 58)%Z acc -> Forall (fun c => 48 <= c < 58)%Z (digits_aux f 10 (fun v => 48 + v)%Z y acc)).
{ induction f as [|f IH]; intros y acc Ha; [exact Ha|]. rewrite digits_aux_S.
destruct (Z.eqb_spec y 0); [exact Ha|]. apply IH. constructor; [|exact Ha]. pose proof (Z.mod_pos_bound y 10 ltac:(lia)). lia. }
apply G. constructor.
Qed.

Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells asegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.
Lemma upd_firstn_part : forall {X} (l : list X) i x n, (n <= i < length l)%nat -> firstn n (upd l i x) = firstn n l.
Proof.
intros X l i x n H. rewrite upd_firstn_skipn by lia. rewrite firstn_app, firstn_firstn, length_firstn.
replace (Nat.min n i) with n by lia. replace (n - Nat.min i (length l))%nat with 0%nat by lia. cbn. apply app_nil_r.
Qed.
Lemma upd_skipn_at : forall {X} (l : list X) i x, (i < length l)%nat -> skipn i (upd l i x) = x :: skipn (S i) l.
Proof.
intros X l i x H. rewrite upd_firstn_skipn by lia. rewrite skipn_app, length_firstn.
replace (Nat.min i (length l)) with i by lia. rewrite Nat.sub_diag, skipn_all2 by (rewrite length_firstn; lia). reflexivity.
Qed.

Lemma hex_digits_0 : forall l, hex_digits l 0 = [].
Proof. reflexivity. Qed.
Lemma hex_digits_step : forall l x, (0 < x < 2^64)%Z ->
hex_digits l x = hex_digits l (x / 16) ++ [Z.lor (znth XDIGITS (x mod 16)) l].
Proof.
intros l x Hx. unfold hex_digits at 1. change 16%nat with (S 15). rewrite digits_aux_S.
destruct (Z.eqb_spec x 0); [lia|]. rewrite digits_aux_acc. apply (f_equal2 (@app Z)); [|reflexivity]. unfold hex_digits. apply digits_aux_fuel; [lia|].
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
change (16 * 16 ^ Z.of_nat 15)%Z with (2^64)%Z. lia.
Qed.
Lemma hex_digits_length : forall l x, (length (hex_digits l x) <= 16)%nat.
Proof. intros l x. unfold hex_digits. pose proof (digits_aux_length 16 16 (fun v => Z.lor (znth XDIGITS v) l) x []) as L. cbn [length Nat.add] in L. exact L. Qed.
Lemma hexchar_ok0 : forall n, (0 <= n < 0 + Z.of_nat 16)%Z -> ((48 <=? Z.lor (znth XDIGITS n) 0) && (Z.lor (znth XDIGITS n) 0 <? 103))%Z = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma hexchar_ok32 : forall n, (0 <= n < 0 + Z.of_nat 16)%Z -> ((48 <=? Z.lor (znth XDIGITS n) 32) && (Z.lor (znth XDIGITS n) 32 <? 103))%Z = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma hexchar_range : forall l v, (l = 0 \/ l = 32)%Z -> (0 <= v < 16)%Z -> (48 <= Z.lor (znth XDIGITS v) l < 103)%Z.
Proof.
intros l v [-> | ->] Hv.
- pose proof (hexchar_ok0 v ltac:(cbn; lia)) as E. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
- pose proof (hexchar_ok32 v ltac:(cbn; lia)) as E. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.
Lemma hex_digits_range : forall l x, (l = 0 \/ l = 32)%Z -> Forall (fun c => 48 <= c < 103)%Z (hex_digits l x).
Proof.
intros l x Hl. unfold hex_digits.
assert (G : forall f y acc, Forall (fun c => 48 <= c < 103)%Z acc -> Forall (fun c => 48 <= c < 103)%Z (digits_aux f 16 (fun v => Z.lor (znth XDIGITS v) l) y acc)).
{ induction f as [|f IH]; intros y acc Ha; [exact Ha|]. rewrite digits_aux_S.
destruct (Z.eqb_spec y 0); [exact Ha|]. apply IH. constructor; [|exact Ha]. apply hexchar_range; [exact Hl|]. pose proof (Z.mod_pos_bound y 16 ltac:(lia)). lia. }
apply G. constructor.
Qed.

Lemma ift : forall (X : Type) (a b : X), (if true then a else b) = a. Proof. reflexivity. Qed.
Lemma iff : forall (X : Type) (a b : X), (if false then a else b) = b. Proof. reflexivity. Qed.

Lemma lo64_range : forall y, (0 <= lo64 y < 2^64)%Z.
Proof. intros y. unfold lo64. rewrite wrap64_mod. apply Z.mod_pos_bound. lia. Qed.
Lemma hi64_range : forall y, (0 <= hi64 y < 2^64)%Z.
Proof. intros y. unfold hi64. rewrite wrap64_mod. apply Z.mod_pos_bound. lia. Qed.
Lemma lo64_hi64 : forall y, (0 <= y < 2^128)%Z -> (lo64 y + 2^64 * hi64 y)%Z = y.
Proof.
intros y Hy. unfold lo64, hi64. rewrite !wrap64_mod. rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small (y / 2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; change (2^64 * 2^64)%Z with (2^128)%Z; lia]).
pose proof (Z.div_mod y (2^64) ltac:(lia)). lia.
Qed.

Section Ranges128.
Local Open Scope Z_scope.
Lemma mk128_range : forall hi lo, 0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= mk128 hi lo < 2^128.
Proof.
intros hi lo Hh Hl. unfold mk128. apply QwAs.lor_lt_pow2; [|lia].
rewrite Z.shiftl_mul_pow2 by lia. change (2^128) with (2^64 * 2^64). nia.
Qed.
Lemma shr64_range64 : forall a k, 0 <= a < 2^64 -> 0 <= k -> 0 <= Z.shiftr a k < 2^64.
Proof. intros. apply Qcrs.Z_shiftr_range; lia. Qed.
Lemma sra63_range : forall x, 0 <= sra63 x < 2^64.
Proof. intros x. unfold sra63, ONES64. destruct (is_neg64 x); cbn; lia. Qed.

End Ranges128.

Lemma sx32_int : forall (slot : word) i, (-2^31 <= i < 2^31)%Z -> (bv_unsigned slot mod 2^32 = i mod 2^32)%Z ->
sx32 slot = Z_to_bv 64 (i mod 2^64).
Proof.
intros slot i Hi E. unfold sx32. rewrite Z_to_bv_mod64. apply Z_to_bv_eqm. f_equal.
change (2^32)%Z with 4294967296%Z in E.
rewrite swrap32_eq. rewrite <- Zplus_mod_idemp_l, E, Zplus_mod_idemp_l.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma zx32_uint : forall (slot : word) u, (bv_unsigned slot mod 2^32 = u)%Z -> zx32 slot = Z_to_bv 64 u.
Proof. intros slot u E. unfold zx32. rewrite E. reflexivity. Qed.

Lemma land_land_same : forall a m, Z.land (Z.land a m) m = Z.land a m.
Proof. intros. rewrite <- Z.land_assoc, Z.land_diag. reflexivity. Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
Lemma cb8_c8_in : forall m A pre post bs, rw_cells asegs m A (pre ++ CB 8 bs :: post) -> rw_cells asegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
intros m A pre post bs [[Hwf Hb] Hw].
apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
split; [split|].
- apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
- rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite le8_of_bytes by exact H2. exact Hb.
- rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.
Ltac c8ify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let rec go pre l := lazymatch l with
| CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
| ?c :: ?l' => go constr:(pre ++ [c]) l'
| [] => idtac end in
go constr:(@nil cell) cs end.

Lemma printf_loop_S : forall {St : Type} (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z) fuel s args cnt,
printf_loop OUT OUTFP (S fuel) s args cnt =
match s with
| [] => munr
| c :: _ =>
if (c =? 0)%Z then mret cnt else
let lit := lit_run s in
let l := zlength lit in
let s1 := skipn (Datatypes.length lit) s in
match s1 with
| [] => munr
| c1 :: s2 =>
if ((c1 =? 37) && match s2 with [] => true | c2 :: _ => (c2 =? 37) end)%Z
then munr
else if (0 <? l)%Z then
(if (INT_MAX - cnt <? l)%Z then munr
else OUT lit ;;; printf_loop OUT OUTFP fuel s1 args (cnt + l))
else
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
OUT [] ;;;
cnt' <- conv OUT OUTFP cnt d a ;;
printf_loop OUT OUTFP fuel s3 args' cnt'
| _, _ => munr
end
end
end.
Proof. reflexivity. Qed.
Lemma fp_calls_S : forall fuel s args,
fp_calls (S fuel) s args =
match s with
| [] => []
| c :: _ =>
if (c =? 0)%Z then [] else
let lit := lit_run s in
let s1 := skipn (Datatypes.length lit) s in
if (0 <? zlength lit)%Z then fp_calls fuel s1 args
else match s1 with
| _ :: s2 =>
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
match a with
| PA_g dd =>
let fl := (if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD))%Z in
(dd, d_w d, d_p d, fl, d_t d) :: fp_calls fuel s3 args'
| _ => fp_calls fuel s3 args'
end
| _, _ => []
end
| _ => []
end
end.
Proof. reflexivity. Qed.

Lemma In_firstn_w : forall {A} (x : A) n l, In x (firstn n l) -> In x l.
Proof. intros A x n l. revert n. induction l as [|y l IH]; intros [|n] H; cbn in H; try contradiction. destruct H as [->|H]; [left; reflexivity | right; eapply IH; exact H]. Qed.
Lemma In_skipn_w : forall {A} (x : A) n l, In x (skipn n l) -> In x l.
Proof. intros A x n l. revert n. induction l as [|y l IH]; intros [|n] H; cbn in H; try contradiction; [exact H|]. right. eapply IH. exact H. Qed.
Lemma Forall_sub : forall {A} (P : A -> Prop) (l : list A) n k, Forall P l -> Forall P (firstn n (skipn k l)).
Proof.
intros A P l n k H. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall P l) H).
eapply In_skipn_w. eapply In_firstn_w. exact Hx.
Qed.
Lemma zb_firstn : forall n l, zb (firstn n l) = firstn n (zb l).
Proof. intros. unfold zb. rewrite firstn_map. reflexivity. Qed.
Lemma zb_skipn : forall n l, zb (skipn n l) = skipn n (zb l).
Proof. intros. unfold zb. rewrite skipn_map. reflexivity. Qed.
Lemma bytes_at_sub : forall m A (l : list byte) k n,
bytes_at asegs m A l -> (k <= length l)%nat ->
bytes_at asegs m (A + Z.of_nat k) (firstn n (skipn k l)).
Proof.
intros m A l k n H Hk.
rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H]. rewrite length_firstn, Nat.min_l in H by lia.
rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma parse_dir_conv_type : forall s d rest, parse_dir s = Some (d, rest) -> conv_type (d_t d) = Some (d_ty d).
Proof.
intros s d rest PD. destruct (parse_dir_shape _ _ _ PD) as (_ & SH). destruct (parse_flags s 0) as [fl0 s1'].
destruct SH as (_ & c1 & s1b & _ & _ & s2 & _ & c2 & s2b & _ & PX).
destruct PX as [(_ & _ & _ & Ht & _ & CT) | (_ & _ & c3 & s3b & _ & _ & s3 & _ & _ & CT)]; [rewrite Ht|]; exact CT.
Qed.

Lemma parse_dir_xp : forall s d rest, parse_dir s = Some (d, rest) ->
((d_xp d = false /\ d_p d = -1) \/ (d_xp d = true /\ 0 <= d_p d <= INT_MAX))%Z.
Proof.
intros s d rest PD. destruct (parse_dir_shape _ _ _ PD) as (_ & SH). destruct (parse_flags s 0) as [fl0 s1'].
destruct SH as (_ & c1 & s1b & _ & _ & s2 & _ & c2 & s2b & _ & PX).
destruct PX as [(_ & Hp & Hx & _) | (_ & Hx & c3 & s3b & _ & _ & s3 & G & _)].
- left. split; [exact Hx | exact Hp].
- right. split; [exact Hx|]. eapply getint_some_range; [|exact G]. unfold INT_MAX. lia.
Qed.

Lemma c8_read4 : forall m A pre (w : word) post a,
rw_cells asegs m A (pre ++ C8 w :: post) -> a = wa (A + Z.of_nat (cells_size pre)) ->
ov_read_bytes asegs m a 4 = Some (le4 w).
Proof.
intros m A pre w post a H ->.
apply (proj1 (rw_cells_app asegs m A pre (C8 w :: post))) in H. destruct H as [_ H].
pose proof (rw_cells_bytes_at' _ _ _ _ H) as Hb. cbn [cells_bytes cbytes] in Hb.
pose proof (bytes_at_ov_read asegs m _ _ 0 4 Hb) as R. rewrite Z.add_0_r in R.
rewrite R. 2:{ cbn [skipn]. rewrite length_app, length_le8. lia. }
change (skipn 0 (le8 w ++ cells_bytes post)) with (le8 w ++ cells_bytes post).
rewrite firstn_app, length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r, firstn4_le8. reflexivity.
Qed.

Lemma bytes_at_nil : forall m a, (0 <= a)%Z -> (a <= 2^64)%Z -> bytes_at asegs m a [].
Proof. intros m a H0 H1. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

Section PrintfCore.
Context {BAND : Band}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q + 16 <= 140737488355328)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 143488)%Z /\ szone A (Z.of_nat (length fmt)).

Hypothesis SEP_F : ((945072 <= Fp /\ Fp + 232 <= 6565536) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((6566104 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Notation sfx := (sfx fmt).
Definition ctx_all : unit :=
let _ := (ra, q, gp, tp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, F, fc0, m0,
lo, canary, A, fmt, AP, VA, slots, nla, nlt) in tt.

Definition W : list (Z * Z) := [(lo, q); (AP, AP + 8); (Fp, Fp + 232); (B, B + BS)]%Z.
Notation SPv := (Z_to_bv 64 (q + -544)).
Notation FPv := (Z_to_bv 64 Fp).

Definition Fokd (F1 F2 : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k.
Definition Fok (Ft : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k.
Lemma Fok_refl : Fok F. Proof using F.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0. intros k _. reflexivity. Qed.
Lemma Fok_trans : forall F1 F2, Fok F1 -> (forall k : reg, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k) -> Fok F2.
Proof using F.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0. intros F1 F2 H1 H2 k Hk. rewrite (H2 k Hk). apply H1. exact Hk. Qed.

Definition POST : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (apv : word) (m' : word -> option byte),
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch W m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
/\ frm0 fc' /\ Fok Ft
/\ stk asegs m' lo q
/\ SINK m' st'
/\ ssp_cells m' canary
/\ rw_cells asegs m' AP [C8 apv]
/\ (0 <= r <= INT_MAX)%Z.

Definition hi_cells : list cell :=
[C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

Definition lo_cells (pfx s2s za pl plp l10n alo ahi : word) (j128 : list byte) : list cell :=
[C8 pfx; C8 s2s; C8 za; C8 pl; C8 plp; C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
C8 nla; C8 nlt; C8 (Z_to_bv 64 AP); C8 (Z_to_bv 64 75913); C8 l10n; C8 (Z_to_bv 64 ssp_guard); C8 (Z_to_bv 64 214748364);
C8 alo; C8 ahi; CB 24 j128].

Definition finv (m : word -> option byte) : Prop :=
mem_inv asegs m /\ munch W m0 m /\ wmono asegs m0 m
/\ rw_cells asegs m (q + -112) hi_cells
/\ stk asegs m lo (q + -544)
/\ bytes_at asegs m A (zb fmt)
/\ va_area m VA slots
/\ rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary].

Ltac hush := idtac.

Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & BY & VAA & SSP1 & SSP2); unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.

Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).

Lemma u8_lit : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. Qed.
Lemma fmt_rng : forall i, (0 <= i < zlength fmt)%Z -> (0 <= znth fmt i < 256)%Z.
Proof using fmt HF.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0. intros i Hi. exact (Forall_znth _ fmt i HF Hi). Qed.

Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).

Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.

Lemma states0_bytes : forall m, mem_inv asegs m -> bytes_at asegs m 0x27260 (zb STATES0).
Proof.
clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma states0_read : forall m t ty, mem_inv asegs m -> conv_type t = Some ty ->
ov_read_bytes asegs m (wa (t + 160352 + -65)) 1 = Some [Z_to_bv 8 ty].
Proof.
clear. intros m t ty MI CT. pose proof (conv_type_range t ty CT) as R.
rewrite <- (states0_conv t ty CT).
eapply (zbytes_read m 0x27260 STATES0 (t - 65)); [apply states0_bytes; exact MI | change (zlength STATES0) with 58%Z; lia | f_equal; lia].
Qed.

Definition PFXSTR : list Z := [45; 43; 32; 32; 32; 48; 88; 48; 120]%Z.
Lemma pfx_bytes : forall m, mem_inv asegs m -> bytes_at asegs m 68991 (zb PFXSTR).
Proof.
clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma pfx_sub : forall m k n, mem_inv asegs m -> (k + n <= 9)%nat ->
bytes_at asegs m (68991 + Z.of_nat k) (zb (firstn n (skipn k PFXSTR))).
Proof.
clear. intros m k n MI Hk. rewrite zb_firstn, zb_skipn. apply bytes_at_sub; [apply pfx_bytes; exact MI|]. cbn. lia.
Qed.
Lemma xdigits_bytes : forall m, mem_inv asegs m -> bytes_at asegs m 142360 (zb XDIGITS).
Proof.
clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma xdigits_read : forall m v, mem_inv asegs m -> (0 <= v < 16)%Z ->
ov_read_bytes asegs m (wa (142360 + v)) 1 = Some [Z_to_bv 8 (znth XDIGITS v)].
Proof.
clear. intros m v MI Hv. eapply (zbytes_read m 142360 XDIGITS v); [apply xdigits_bytes; exact MI | change (zlength XDIGITS) with 16%Z; lia | reflexivity].
Qed.

Definition JT1 : list Z := [60; 206; 10; 0; 188; 206; 10; 0; 220; 207; 10; 0; 188; 206; 10; 0; 60; 206; 10; 0; 60; 206; 10; 0; 60; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 160; 208; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 60; 208; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 60; 206; 10; 0; 188; 206; 10; 0; 252; 207; 10; 0; 140; 206; 10; 0; 60; 206; 10; 0; 60; 206; 10; 0; 60; 206; 10; 0; 188; 206; 10; 0; 140; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 232; 206; 10; 0; 136; 207; 10; 0; 52; 207; 10; 0; 40; 208; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 212; 206; 10; 0; 188; 206; 10; 0; 196; 207; 10; 0; 188; 206; 10; 0; 188; 206; 10; 0; 60; 208; 10; 0]%Z.
Lemma jt1_bytes : forall m, mem_inv asegs m -> bytes_at asegs m 160024 (zb JT1).
Proof.
clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma jt1_read_lit : forall m (t : Z) bs, mem_inv asegs m -> (65 <= t <= 120)%Z ->
firstn 4 (skipn (Z.to_nat (4 * (t - 65))) (zb JT1)) = bs ->
ov_read_bytes asegs m (wa (160024 + 4 * (t - 65))) 4 = Some bs.
Proof.
clear. intros m t bs MI Ht <-.
pose proof (bytes_at_ov_read asegs m 160024 (zb JT1) (Z.to_nat (4 * (t - 65))) 4 (jt1_bytes m MI)) as R.
rewrite Z2Nat.id in R by lia. apply R.
rewrite zb_length. cbn [length JT1]. lia.
Qed.
Lemma jt1_read_s : forall m t, mem_inv asegs m -> t = 115%Z -> ov_read_bytes asegs m (wa (160024 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 212; Z_to_bv 8 206; Z_to_bv 8 10; Z_to_bv 8 0].
Proof. clear. intros m t MI ->. apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]. Qed.
Lemma jt1_read_d : forall m t, mem_inv asegs m -> (t = 100 \/ t = 105)%Z -> ov_read_bytes asegs m (wa (160024 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 140; Z_to_bv 8 206; Z_to_bv 8 10; Z_to_bv 8 0].
Proof. clear. intros m t MI [-> | ->]; (apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]). Qed.
Lemma jt1_read_u : forall m t, mem_inv asegs m -> t = 117%Z -> ov_read_bytes asegs m (wa (160024 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 196; Z_to_bv 8 207; Z_to_bv 8 10; Z_to_bv 8 0].
Proof. clear. intros m t MI ->. apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]. Qed.
Lemma jt1_read_x : forall m t, mem_inv asegs m -> (t = 120 \/ t = 88)%Z -> ov_read_bytes asegs m (wa (160024 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 60; Z_to_bv 8 208; Z_to_bv 8 10; Z_to_bv 8 0].
Proof. clear. intros m t MI [-> | ->]; (apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]). Qed.
Lemma jt1_read_fp : forall m t, mem_inv asegs m -> conv_type t = Some T_DBL -> ov_read_bytes asegs m (wa (160024 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 8; Z_to_bv 8 45; Z_to_bv 8 8; Z_to_bv 8 0].
Proof.
clear. intros m t MI CT. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL in CT.

repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [try discriminate CT|] end; try discriminate CT.
Qed.

Lemma conv_type_cases : forall t ty, conv_type t = Some ty ->
(ty = T_PTR /\ t = 115%Z) \/ (ty = T_INT /\ (t = 100 \/ t = 105)%Z) \/ (ty = T_UINT /\ (t = 117 \/ t = 120 \/ t = 88)%Z) \/ (ty = T_DBL).
Proof.
clear. intros t ty CT. unfold conv_type in CT.
repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [injection CT as <-|] end; try discriminate CT;
repeat match goal with E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] | E : (_ =? _) = true |- _ => apply Z.eqb_eq in E end;
subst; auto 10.
Qed.

Lemma fl_shl50 : forall fl, (0 <= fl < 131072)%Z ->
(Z.land (Z.shiftl fl 50) 18446744073709551615 < 9223372036854775808 <-> Z.land fl 8192 = 0)%Z.
Proof.
clear. intros fl Hfl. rewrite Z.shiftl_mul_pow2 by lia.
change 8192%Z with (2^13)%Z. rewrite zb_land_pow2 by lia.
change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
split; intros H; Z.div_mod_to_equations; nia.
Qed.
Lemma nzmask_bits' : forall n, (0 <= n < 0 + Z.of_nat 64)%Z -> Bool.eqb (Z.testbit 18446744073709486079 n) (negb (Z.testbit 65536 n)) = true.
Proof. clear. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma nzmask_eq : forall fl, (0 <= fl < 131072)%Z -> Z.land fl 18446744073709486079 = Z.land fl (Z.lnot 65536).
Proof.
clear. intros fl Hfl. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases n 64).
- pose proof (nzmask_bits' n ltac:(cbn; lia)) as E. destruct (Z.testbit 18446744073709486079 n), (Z.testbit 65536 n); cbn in E; try discriminate; reflexivity.
- replace (Z.testbit fl n) with false; [reflexivity|]. symmetry.
destruct (Z.eq_dec fl 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
apply Z.lt_le_trans with 17%Z; [apply Z.log2_lt_pow2; cbn in *; lia|lia].
Qed.
Lemma land_bound' : forall a m, (0 <= a)%Z -> (0 <= m)%Z -> (0 <= Z.land a m <= a)%Z.
Proof.
clear. intros a m Ha Hm. split; [apply Z.land_nonneg; left; exact Ha|].
pose proof (Z.sub_land_same_l a m) as E.
assert (0 <= Z.land a (Z.lnot m))%Z by (apply Z.land_nonneg; left; exact Ha). lia.
Qed.

Lemma sextw_small : forall p, (-2147483648 <= p < 2147483648)%Z -> bv_swrap 32 (Z.land p 18446744073709551615 + 0) = p.
Proof.
clear. intros p Hp. rewrite Z.add_0_r. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
rewrite swrap32_eq.
replace (p mod 2 ^ 64)%Z with (p + 2^64 * (- (p / 2^64)))%Z by (Z.div_mod_to_equations; lia).
change (2^64)%Z with (4294967296 * 4294967296)%Z.
set (kq := (- (p / (4294967296 * 4294967296)))%Z). clearbody kq. Z.div_mod_to_equations. nia.
Qed.

Lemma pad_test_xor : forall fl b, Z.land b 73728 = b ->
(Z.land (Z.lxor fl b) 73728 =? 0)%Z = (Z.land fl 73728 =? b)%Z.
Proof.
clear. intros fl b Hb. rewrite land_lxor_distr, Hb.
destruct (Z.eqb_spec (Z.lxor (Z.land fl 73728) b) 0) as [E|E]; destruct (Z.eqb_spec (Z.land fl 73728) b) as [E2|E2]; try reflexivity; exfalso.
- apply E2. apply Z.lxor_eq. exact E.
- apply E. rewrite E2. apply Z.lxor_nilpotent.
Qed.

Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.

Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].

Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Lemma implM_eq_ms : forall {X} (c : M St X) s Q ms ms', ms = ms' -> implM asegs c s Q ms' -> implM asegs c s Q ms.
Proof using.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0. intros X c s Q ms ms' -> H. exact H. Qed.
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Lemma sink_store : forall m st a (bs : list byte),
SINK m st -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
(a + Z.of_nat (length bs) <= Fp \/ Fp + 232 <= a)%Z -> (a + Z.of_nat (length bs) <= B \/ B + BS <= a)%Z ->
(GLOBALS_TOP <= a)%Z ->
SINK (write_to_mem m (wa a) bs) st.
Proof using Fp B BS SINK SFR.    try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0.
intros m st a bs HS Ha Hb D1 D2 D3.
apply (SFR [(a, a + Z.of_nat (length bs))]%Z m _ st HS).
- apply munch_write; [apply munch_refl | lia | lia | cbn; lia].
- apply wmono_write. apply wmono_refl.
- constructor; [cbn; lia | constructor].
- constructor; [cbn; lia | constructor].
- constructor; [cbn; lia | constructor].
Qed.
Lemma sink_call : forall Wc m m' st,
SINK m st -> munch Wc m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= Fp \/ Fp + 232 <= fst iv)%Z Wc ->
Forall (fun iv => snd iv <= B \/ B + BS <= fst iv)%Z Wc ->
Forall (fun iv => GLOBALS_TOP <= fst iv)%Z Wc ->
SINK m' st.
Proof using Fp B BS SINK SFR.    try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0. intros Wc m m' st HS MU WM D1 D2 D3. exact (SFR Wc m m' st HS MU WM D1 D2 D3). Qed.

Lemma arg_ok_W : forall m m' w a, arg_ok Fp B BS m lo q AP w a -> munch W m m' -> arg_ok Fp B BS m' lo q AP w a.
Proof using Fp B BS q lo fmt AP slots.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0.
intros m m' w a H MU. destruct a as [s|i|u|d]; cbn in H |- *; try exact H.
destruct H as (slack & BYs & Hs & PAD & NZ & SZs & D1 & D2 & D3 & D4). exists slack.
split; [|repeat (split; [assumption|]); assumption].
eapply bytes_at_transport; [exact BYs | exact MU |].
unfold W. cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
Lemma args_ok_W : forall m m' ws args, args_ok Fp B BS m lo q AP ws args -> munch W m m' -> args_ok Fp B BS m' lo q AP ws args.
Proof using Fp B BS q lo fmt AP slots.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0.
intros m m' ws args. revert ws. induction args as [|a args IH]; intros ws H MU; [destruct ws; exact I|].
cbn [args_ok] in H |- *.
destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2]. split; [eapply arg_ok_W; eauto | apply IH; assumption].
Qed.

Definition lo_cells14 (pfx s2s za pl plp l10n : word) : list cell :=
[C8 pfx; C8 s2s; C8 za; C8 pl; C8 plp; C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
C8 nla; C8 nlt; C8 (Z_to_bv 64 AP); C8 (Z_to_bv 64 75913); C8 l10n; C8 (Z_to_bv 64 ssp_guard); C8 (Z_to_bv 64 214748364)].
Lemma lo_split : forall m pfx s2s za pl plp l10n alo ahi j128,
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells asegs m (q + -544) (lo_cells14 pfx s2s za pl plp l10n) /\
rw_cells asegs m (q + -544 + 112) [C8 alo; C8 ahi] /\ rw_cells asegs m (q + -544 + 128) [CB 24 j128].
Proof using q AP nla nlt.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0.
clear. intros. unfold lo_cells in H.
apply (proj1 (rw_cells_app asegs m _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in H. destruct H as [H1 H2]. cbn [cells_size csize Nat.add app] in H2.
change (Z.of_nat 112) with 112%Z in H2.
apply (proj1 (rw_cells_app asegs m _ [_;_] _)) in H2. destruct H2 as [H2 H3]. cbn [cells_size csize Nat.add app] in H3.
change (Z.of_nat 16) with 16%Z in H3.
split; [exact H1|]. split; [exact H2|]. replace (q + -544 + 128)%Z with (q + -544 + 112 + 16)%Z by lia. exact H3.
Qed.
Lemma lo_join : forall m pfx s2s za pl plp l10n alo ahi j128,
rw_cells asegs m (q + -544) (lo_cells14 pfx s2s za pl plp l10n) ->
rw_cells asegs m (q + -544 + 112) [C8 alo; C8 ahi] -> rw_cells asegs m (q + -544 + 128) [CB 24 j128] ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128).
Proof using q AP nla nlt.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0.
clear. intros. unfold lo_cells.
apply (proj2 (rw_cells_app asegs m _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)). split; [exact H|]. cbn [cells_size csize Nat.add app].
change (Z.of_nat 112) with 112%Z.
apply (proj2 (rw_cells_app asegs m _ [_;_] _)). cbn [cells_size csize Nat.add app]. change (Z.of_nat 16) with 16%Z. split; [exact H0|].
replace (q + -544 + 112 + 16)%Z with (q + -544 + 128)%Z by lia. exact H1.
Qed.

Ltac transport_chunks segs m a bs ::=
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_frame segs m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_frame segs m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia | simpl_sizes; slia | glo_lia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Ltac transport_after_call segs m m' MU WM ::=
let W := lazymatch type of MU with munch ?W _ _ => W end in
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; slia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; slia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; glo_lia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : stk segs m ?loq ?hiq |- _ =>
first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
| clear H ]
| H : munch ?Wq ?mq m |- _ =>
first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
| fail 100 "callee footprint not inside caller footprint" ]
| H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
end.

Lemma pop_arg_callq : forall ra' t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (a0v k ty : Z) (slot x y : word),
a0v = (q + -544 + 112)%Z ->
rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] ->
va_area m VA slots -> nth_error slots (Z.to_nat k) = Some slot -> (0 <= k)%Z ->
rw_cells asegs m (q + -544 + 112) [C8 x; C8 y] ->
stk asegs m lo (q + -544) ->
mem_inv asegs m ->
(ty = T_PTR \/ ty = T_INT \/ ty = T_UINT)%Z ->
evt asegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft' m',
ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
Ft' (ret_pc ra') fc None m' (seg_rom asegs)
/\ munch [(q + -544 - 16, q + -544); (AP, AP + 8); (q + -544 + 112, q + -544 + 112 + 16)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (q + -544)
/\ rw_cells asegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (k + 1)))]
/\ rw_cells asegs m' (q + -544 + 112) [C8 (QoBx.pop_arg_lo ty slot); C8 (QoBx.pop_arg_hi ty slot y)]
/\ Fokd Ft Ft')
(MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 ty) (Z_to_bv 64 AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 0xd483c) fc None m (seg_rom asegs)).
Proof using q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear A0. try clear VAHI. try clear BS0.

intros until y. intros -> APC VAA NTH Hk ARGC ST MI TY. unfold PC_DEPTH, GLOBALS_TOP in *.
pose proof (va_area_bound _ _ _ VAA) as VB. unfold zlength in *.
destruct (stk_split _ _ _ (q + -544 - 16) _ ST ltac:(lia)) as [ST1 ST2].
assert (Eq : bv_unsigned SPv = (q + -544)%Z) by (apply unsigned_lit; lia).
assert (Ea : bv_unsigned (Z_to_bv 64 (q + -544 + 112)) = (q + -544 + 112)%Z) by (apply unsigned_lit; lia).
assert (Ep : bv_unsigned (Z_to_bv 64 AP) = AP) by (apply unsigned_lit; lia).
assert (IL : (Z.to_nat k < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
eapply evt_mono.
{ eapply (pop_arg_spec ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + -544 + 112)) (Z_to_bv 64 ty) (Z_to_bv 64 AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Ft fc m VA slots k ty slot x y);
rewrite ?Eq, ?Ea, ?Ep.
all: first [exact ST2 | exact APC | exact VAA | exact NTH | exact ARGC | exact MI | exact TY | reflexivity | lia]. }
cbv beta. intros ms' P. unfold pop_arg_post in P. rewrite !Eq, !Ea, !Ep in P.
destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft' & m' & -> & MU & WM & MI' & ST' & APC' & ARGC' & VAA' & HF).
repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
split.
{ eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ]. }
split; [exact APC'|]. split; [exact ARGC'|]. exact HF.
Qed.

Lemma strnlen_callq : forall ra' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (P n : Z) (buf : list byte),
stk asegs m lo (q + -544) ->
bytes_at asegs m P buf ->
memchr_ok P 0 n buf ->
mem_inv asegs m ->
(P + Z.of_nat (length buf) <= lo \/ q <= P)%Z -> (0 < P < 2^64)%Z -> (0 <= n < 2^64)%Z ->
ISH m -> szone P (memchr_len 0 n buf) ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
Ft (ret_pc ra') fc None m' (seg_rom asegs)
/\ munch [(lo, q + -544)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (q + -544)
/\ bytes_at asegs m' P buf)
(MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 0x4f954) fc None m (seg_rom asegs)).
Proof using q gp tp lo LO GLO QHI.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0.

intros until buf. intros ST BUF OK MI SEP P0 Hn ISHm SZ. unfold PC_DEPTH, GLOBALS_TOP in *.
pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
pose proof (memchr_len_bound 0 n buf ltac:(lia)) as [LB _].
destruct ISHm as (ASH & RC & SB).
assert (Eq : bv_unsigned SPv = (q + -544)%Z) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (strnlen_icpt_spec P n lo buf ra' SPv gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Ft fc m);
rewrite ?Eq.
all: first [exact ST | exact BUF | exact OK | exact MI | exact SB | exact RC | apply (rng_ok_of_ash _ _ _ ASH SZ ltac:(lia))
| idtac; lia | unfold STRNLEN_ICPT_STACK, STRNLEN_STACK, MEMCHR_ICPT_STACK; lia | lia]. }
cbv beta. intros ms' PS. unfold strnlen_post in PS. rewrite !Eq in PS.
destruct PS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & BUF').
repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. exact BUF'.
Qed.

Lemma memchr_len_cstr : forall n (str slack : list byte), ~ In (Z_to_bv 8 0) str -> (Z.of_nat (length str) < n)%Z ->
memchr_len 0 n (str ++ Z_to_bv 8 0 :: slack) = (Z.of_nat (length str) + 1)%Z.
Proof. clear. intros n str slack NN Hn. unfold memchr_len. rewrite (find_byte_cstr 0 n str slack NN Hn). reflexivity. Qed.
Lemma memchr_len_cstr_le : forall n (str slack : list byte), ~ In (Z_to_bv 8 0) str -> (0 <= n)%Z ->
(0 <= memchr_len 0 n (str ++ Z_to_bv 8 0 :: slack) <= Z.of_nat (length str) + 1)%Z.
Proof.
clear. intros n str slack NN Hn. unfold memchr_len. destruct (Z.lt_ge_cases (Z.of_nat (length str)) n) as [H|H].
- rewrite (find_byte_cstr 0 n str slack NN H). lia.
- rewrite (find_byte_cstr_short 0 n str slack NN H). lia.
Qed.
Lemma zb_nonul : forall s, Forall (fun c => 0 < c < 256)%Z s -> ~ In (Z_to_bv 8 0) (zb s).
Proof.
clear. intros s HF IN. unfold zb in IN. apply in_map_iff in IN. destruct IN as (c & E & Hc).
apply (proj1 (Forall_forall _ s) HF) in Hc.
assert (E' : bv_unsigned (Z_to_bv 8 c) = bv_unsigned (Z_to_bv 8 0)) by (rewrite E; reflexivity).
rewrite u8_lit in E' by lia. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z in E'. lia.
Qed.

Definition out_postq (ra' : word) (Ft : bvmap 5 word) (fc : bv 32) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(S : Z) (bs : list Z) (m : word -> option byte) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
ms' = MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra') fc None m' (seg_rom asegs)
/\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (q + -544)
/\ SINK m' st'
/\ ssp_cells m' canary
/\ bytes_at asegs m' S (zb bs).
Lemma out_callq : forall ra' t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (st : St) (S L : Z) (bs : list Z),
SINK m st -> bytes_at asegs m S (zb bs) -> Forall (fun c => 0 <= c < 256)%Z bs -> L = zlength bs ->
stk asegs m lo (q + -544) -> ssp_cells m canary -> mem_inv asegs m ->
(0 <= S)%Z -> (S < 2^64)%Z ->
(S + zlength bs <= lo \/ q + -544 <= S)%Z -> (S + zlength bs <= Fp \/ Fp + 232 <= S)%Z -> (S + zlength bs <= B \/ B + BS <= S)%Z ->
(zlength bs < 2^31)%Z ->
szone S (zlength bs) ->
(S + zlength bs <= 2^47)%Z ->
implM asegs (OUT bs) st (out_postq ra' Ft fc s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 S bs m)
(MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) FPv a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 0xd33c8) fc None m (seg_rom asegs)).
Proof using Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0.    try clear SFR. try clear SFL. try clear HF. try clear FRM0. try clear HA. try clear HVA. try clear A0. try clear VAHI.

intros until bs. intros HS SRC RNG -> ST SSP MI HS0 HS1 D1 D2 D3 LB SZ HT. unfold PC_DEPTH, GLOBALS_TOP in *.
pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite zb_length in SB. unfold zlength in *.
assert (Eq : bv_unsigned SPv = (q + -544)%Z) by (apply unsigned_lit; lia).
assert (Es : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
pose proof HOUT as HO. unfold out_stmt in HO.
specialize (HO ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length bs))) FPv a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Ft fc m st bs lo canary).
rewrite !Eq, !Es in HO.
eapply implM_mono.
{ apply HO; try assumption; try reflexivity; unfold OUT_DEPTH, zlength; try lia.
eapply TOK; [|exact TQ]. lia. }
cbv beta. intros [] st' ms' P. unfold out_post, SR in P. rewrite !Eq in P. exact P.
Qed.

Definition fp_postq (ra' : word) (Ft : bvmap 5 word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(m : word -> option byte) : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
ms' = MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft' (ret_pc ra') fc' None m' (seg_rom asegs)
/\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc' /\ Fokd Ft Ft'
/\ stk asegs m' lo (q + -544)
/\ SINK m' st'
/\ ssp_cells m' canary.
Lemma fp_callq : forall ra' t0 t1 t2 s0 s1 (a1 a2 a7 : word) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (st : St) (y w p fl t : Z),
fpcall_stmt Fp B BS SINK TOPOK OUTFP (y, w, p, fl, t) ->
SINK m st -> y = (bv_unsigned a1 + 2^64 * bv_unsigned a2)%Z -> bv_unsigned a7 <> 5%Z ->
(-2^31 <= w <= 1)%Z -> (-2^31 <= p < 2^20)%Z -> (0 <= fl < 2^32)%Z -> (0 <= t < 256)%Z -> Z.lor t 32 <> 97%Z ->
stk asegs m lo (q + -544) -> ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
implM asegs (OUTFP y w p fl t) st (fp_postq ra' Ft s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 FPv a1 a2 (Z_to_bv 64 w) (Z_to_bv 64 p) (Z_to_bv 64 fl) (Z_to_bv 64 t) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 0xd4a44) fc None m (seg_rom asegs)).
Proof using Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP.    try clear SFR. try clear SFL. try clear HOUT. try clear HF. try clear FRM0. try clear HA. try clear HVA. try clear A0. try clear VAHI. try clear BS0.

intros until t. intros FPC HS Hy H7 Hw Hp Hfl Ht Hta ST SSP MI FRM. unfold PC_DEPTH, GLOBALS_TOP in *.
assert (Eq : bv_unsigned SPv = (q + -544)%Z) by (apply unsigned_lit; lia).
cbn [fpcall_stmt] in FPC.
specialize (FPC ra' SPv gp tp t0 t1 t2 s0 s1 FPv a1 a2 (Z_to_bv 64 w) (Z_to_bv 64 p) (Z_to_bv 64 fl) (Z_to_bv 64 t) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Ft fc m st lo canary).
rewrite !Eq in FPC.
eapply implM_mono.
{ apply FPC; try assumption; try reflexivity; unfold FMT_FP_DEPTH; try lia.
eapply TOK; [|exact TQ]. lia. }
cbv beta. intros r st' ms' P. unfold fpcall_post, SR in P. rewrite !Eq in P. exact P.
Qed.

Lemma conv_type_dbl : forall t, conv_type t = Some T_DBL -> (69 <= t <= 103)%Z /\ Z.lor t 32 <> 97%Z.
Proof.
clear. intros t CT. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL in CT.
repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [try discriminate CT|] end; try discriminate CT.
Qed.

Ltac solve_szone :=
lazymatch goal with |- szone ?p ?n =>
first [ match goal with H : szone p _ |- _ => eapply szone_sub; [exact H| lia| glo_lia| glo_lia] end
| match goal with H : _ /\ szone p _ |- _ => eapply szone_sub; [exact (proj2 H)| lia| glo_lia| glo_lia] end
| lazymatch p with
| (q + _)%Z => unfold szone; right; idtac; glo_lia
| q => unfold szone; right; idtac; glo_lia
| _ => first [ match goal with H : _ /\ szone ?a _ |- _ => eapply szone_sub; [exact (proj2 H)| glo_lia| glo_lia| glo_lia] end
| unfold szone; left; glo_lia
| unfold szone; right; idtac; glo_lia ]
end
| match goal with |- ?g => idtac "solve_szone FAILED on" g; fail end ]
end.

Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 945024 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 6565536 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | |
| solve_szone
|  try (solve [unfold zlength, zrepeat in *; rewrite ?repeat_length, ?Z2Nat.id by lia; lia]) ]
| cbv beta ].

Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call asegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := idtac.

Definition S_EXIT : Prop :=
forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
(pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 apv] ->
frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
evt asegs (POST r st)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd47e8) fc None m (seg_rom asegs)).

Definition S_SCAN : Prop :=
forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i n cnt' : Z) (Q : machine_state -> Prop),
let _ := ctx_all in
finv m ->
(0 <= i)%Z -> (0 <= n)%Z -> (i + n < zlength fmt)%Z ->
(forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z ->
(znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z ->
(0 < n \/ znth fmt i = 37)%Z ->
(0 <= cnt' <= INT_MAX)%Z -> (n <= INT_MAX - cnt')%Z ->
(forall a1 a2 : word,
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - cnt')) (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) (Z_to_bv 64 n) (Z_to_bv 64 (A + i)) x24 x25 (Z_to_bv 64 n) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3b34) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt i)) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 cnt') x20 x21 x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3ad8) fc None m (seg_rom asegs)).

Definition S_FLAGS : Prop :=
forall (x1 x6 x7 x10 x11 x12 x15 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(p k fl b : Z) (w3 : word) (FL : Z) (s1 : list Z),
let _ := ctx_all in
finv m -> (0 <= p)%Z -> (1 <= k)%Z -> (p + k <= zlength fmt)%Z ->
bv_unsigned w3 = b -> (0 <= fl < 131072)%Z -> (0 <= b < 131072)%Z ->
parse_flags (sfx (p + k)) (Z.lor fl b) = (FL, s1) -> s1 <> [] ->
(forall (k' c' : Z) (a3 a4 a5 : word),
(p + k <= k' < zlength fmt)%Z -> s1 = sfx k' -> c' = znth fmt k' -> flag_bit c' = None -> (0 <= FL < 131072)%Z ->
evt asegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 c') (Z_to_bv 64 (A + k')) a3 a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 32)
x18 x19 x20 x21 x22 x23 (Z_to_bv 64 FL) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3bec) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 w3 (Z_to_bv 64 (A + p + k)) x15 (Z_to_bv 64 1) (Z_to_bv 64 32)
x18 x19 x20 x21 x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3bc8) fc None m (seg_rom asegs)).

Definition S_WLOOP : Prop :=
forall (x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(pos acc w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (w, s2) -> s2 <> [] ->
(forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
(pos < k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
evt asegs Q
(MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3d1c) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) x12 (Z_to_bv 64 (A + pos)) x14 x15 x16 x17
x18 x19 x20 x21 (Z_to_bv 64 acc) x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3c80) fc None m (seg_rom asegs)).

Definition S_WIDTH : Prop :=
forall (x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(k1 w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= k1 < zlength fmt)%Z ->
getint (sfx k1) 0 = Some (w, s2) -> s2 <> [] ->
(forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
(k1 <= k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
evt asegs Q
(MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3d1c) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3c34) fc None m (seg_rom asegs)).

Definition S_PLOOP : Prop :=
forall (x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(pos acc p : Z) (s3 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (p, s3) -> s3 <> [] ->
(forall (k3 : Z) (a1 a3 a4 : word),
(pos < k3 < zlength fmt)%Z -> s3 = sfx k3 -> is_digit (znth fmt k3) = false -> (0 <= p <= INT_MAX)%Z ->
evt asegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3e54) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) (Z_to_bv 64 (A + pos)) x13 x14 x15 (Z_to_bv 64 10) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 acc) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3de0) fc None m (seg_rom asegs)).

Definition S_PREC : Prop :=
forall (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(k2 k3 p : Z) (xp : bool) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= k2 < zlength fmt)%Z ->
( (znth fmt k2 <> 46 /\ p = -1 /\ xp = false /\ k3 = k2)
\/ (znth fmt k2 = 46 /\ xp = true /\ k2 + 1 < zlength fmt /\ znth fmt (k2 + 1) <> 42
/\ getint (sfx (k2 + 1)) 0 = Some (p, sfx k3) /\ k2 + 1 <= k3 < zlength fmt) )%Z ->
(forall (a1 a3 a4 : word),
(-1 <= p <= INT_MAX)%Z ->
evt asegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3e54) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 (Z_to_bv 64 (A + k2)) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3d1c) fc None m (seg_rom asegs)).

Definition S_STATE : Prop :=
forall (x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(k3 ty : Z),
let _ := ctx_all in
finv m -> (0 <= k3 < zlength fmt)%Z -> conv_type (znth fmt k3) = Some ty ->
(forall (a2 a3 : word),
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 ty) a2 a3 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 (Z_to_bv 64 (A + k3 + 1)) x22 x23 x24 x25 x26 (Z_to_bv 64 0) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3ed4) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 (A + k3)) x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3e54) fc None m (seg_rom asegs)).

Definition S_DIR : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(i : Z) (d : dir) (rest : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= i)%Z -> (i + 1 <= zlength fmt)%Z ->
parse_dir (sfx (i + 1)) = Some (d, rest) ->
(forall (k4 : Z) (a2 a3 a4 t1 : word),
(i + 1 < k4 <= zlength fmt)%Z -> rest = sfx k4 -> znth fmt (k4 - 1) = d_t d ->
(0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
evt asegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) a2 a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 (Z_to_bv 64 (A + k4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3ed4) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3b58) fc None m (seg_rom asegs)).

Definition S_END : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
(pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 apv] ->
frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
evt asegs (POST r st)
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) FPv x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd4690) fc None m (seg_rom asegs)).

Definition S_HEAD (fuel : nat) : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i cnt l k : Z) (args : list parg)
(pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i) args) ->
frm0 fc -> Fok Ft ->
(0 <= i)%Z -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l <= INT_MAX)%Z ->
implM asegs (printf_loop OUT OUTFP fuel (sfx i) args (cnt + l)) st POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 cnt) FPv (Z_to_bv 64 (A + i)) x22 x23 x24 x25 (Z_to_bv 64 l) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3abc) fc None m (seg_rom asegs)).

Definition S_CONV : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (d : dir) (a : parg) (args : list parg)
(pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) (a :: args) ->
match a with PA_g dd =>
fpcall_stmt Fp B BS SINK TOPOK OUTFP
(dd, d_w d, d_p d, (if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD))%Z, d_t d)
| _ => True end ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(1 <= i4 <= zlength fmt)%Z -> znth fmt (i4 - 1) = d_t d -> conv_type (d_t d) = Some (d_ty d) ->
(0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
((d_xp d = false /\ d_p d = -1) \/ (d_xp d = true /\ 0 <= d_p d <= INT_MAX))%Z ->
(0 <= c <= INT_MAX)%Z ->
implM asegs (cnt' <- conv OUT OUTFP c d a ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) x12 x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3ed4) fc None m (seg_rom asegs)).

Definition body_loc (BA n : Z) : Prop :=
(((q + -392 <= BA /\ BA + n <= q + -368)
\/ ((BA + n <= lo \/ q <= BA) /\ (BA + n <= Fp \/ Fp + 232 <= BA) /\ (BA + n <= B \/ B + BS <= BA)))
/\ szone BA n)%Z.

Definition S_TAIL : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (prefix body : list Z) (BA PFXA : Z)
(s2s za plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
bytes_at asegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> body_loc BA (zlength body) -> (BA + zlength body <= 2^47)%Z -> (zlength body <= INT_MAX)%Z ->
(forall m', mem_inv asegs m' -> bytes_at asegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(65536 <= PFXA)%Z -> (PFXA + zlength prefix <= 143488)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
implM asegs (cnt' <- conv_tail OUT c fl w p prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 (Z_to_bv 64 (BA + zlength body)) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd4358) fc None m (seg_rom asegs)).

Definition tregs (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 t3 t4 t5 t6 : word) (i4 c w BA wq pq : Z) : bvmap 5 word :=
mkR xra SPv gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) s8 s9 (Z_to_bv 64 wq) (Z_to_bv 64 pq) t3 t4 t5 t6.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
Definition tinv (m : word -> option byte) (st : St) (k i4 : Z) (args : list parg) (fuel : nat)
(PFXA fl n pl pq BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte) : Prop :=
finv m
/\ rw_cells asegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) (Z_to_bv 64 (Z.land fl 73728)) (Z_to_bv 64 n) (Z_to_bv 64 pl) (Z_to_bv 64 (pl + pq)) (Z_to_bv 64 0) alo ahi j128)
/\ rw_cells asegs m (q + -392) [CB 24 digs]
/\ rw_cells asegs m (q + -368) [CB 256 pad]
/\ SINK m st /\ rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] /\ (0 <= k)%Z
/\ args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args
/\ Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args)
/\ bytes_at asegs m BA (zb body) /\ Forall (fun c => 0 <= c < 256)%Z body /\ body_loc BA n /\ (BA + n <= 2^47)%Z /\ n = zlength body
/\ (forall m', mem_inv asegs m' -> bytes_at asegs m' PFXA (zb prefix)) /\ Forall (fun c => 0 <= c < 256)%Z prefix
/\ (65536 <= PFXA)%Z /\ (PFXA + pl <= 143488)%Z /\ pl = zlength prefix /\ (pl <= 2)%Z
/\ (0 <= i4 <= zlength fmt)%Z /\ (0 <= fl < 131072)%Z /\ (0 <= n <= INT_MAX)%Z /\ (n <= pq)%Z /\ (pl + pq <= INT_MAX)%Z.

Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp);
pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.

Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.

Definition S_T6 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM asegs (mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0xd4574) fc None m (seg_rom asegs)).

Definition S_T5 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM asegs (OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0xd4558) fc None m (seg_rom asegs)).

Definition S_T4 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM asegs (mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0xd44d4) fc None m (seg_rom asegs)).

Definition S_T3 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM asegs (mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0xd444c) fc None m (seg_rom asegs)).

Definition S_T2 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM asegs (OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0xd4430) fc None m (seg_rom asegs)).

Definition S_T1 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
Z.land fl 73728 = 0%Z ->
implM asegs (mpad OUT 32 wq (pl + pq) fl ;;; OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0xd43b0) fc None m (seg_rom asegs)).

Definition S_INTC2 : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p argi : Z) (prefix body : list Z) (BA PFXA : Z)
(s2s za plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
bytes_at asegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
(forall m', mem_inv asegs m' -> bytes_at asegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(65536 <= PFXA)%Z -> (PFXA + zlength prefix <= 143488)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
(0 <= argi < 2^64)%Z ->
implM asegs (cnt' <- (if ((argi =? 0) && (p =? 0))%Z then conv_tail OUT c fl w p prefix []
else conv_tail OUT c fl w (Z.max p (zlength body + (if (argi =? 0)%Z then 1 else 0))) prefix body) ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd4320) fc None m (seg_rom asegs)).

Definition S_INTC : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) (BA PFXA : Z)
(s2s za plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
bytes_at asegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
(forall m', mem_inv asegs m' -> bytes_at asegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(65536 <= PFXA)%Z -> (PFXA + zlength prefix <= 143488)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= argi < 2^64)%Z ->
implM asegs (cnt' <- conv_int OUT c fl w p xp argi prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd4308) fc None m (seg_rom asegs)).

Definition dloop_post (x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (a2 a3 : word) (xq : Z) (W : list Z) (m' : word -> option byte),
ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xq) (Z_to_bv 64 (q + -392 + (j - zlength W))) a2 a3
(Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength W))) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd42f0) fc None m' (seg_rom asegs)
/\ munch [(q + -392, q + -368)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength W)) ds ++ zb W ++ skipn (Z.to_nat j) ds)]
/\ (1 <= xq <= 9)%Z /\ dec_digits x = (48 + xq)%Z :: W /\ (zlength W + 1 <= j)%Z.
Definition S_DLOOP : Prop :=
forall (x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x j : Z) (ds : list byte),
let _ := ctx_all in
mem_inv asegs m -> rw_cells asegs m (q + -392) [CB 24 ds] ->
(10 <= x < 2^64)%Z -> (zlength (dec_digits x) <= j <= 24)%Z -> x11 = Z_to_bv 64 (q + -392 + j) ->
evt asegs (dloop_post x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc x j ds m)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) x11 x12 x13
(Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd42b8) fc None m (seg_rom asegs)).

Definition S_FMTU2 : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (x d jj : Z) (W prefix : list Z) (PFXA : Z)
(pfx s2s za plp ahi : word) (j128 pre pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 (pre ++ zb W)] -> zlength pre = jj -> (1 <= jj)%Z ->
((d = 0 /\ W = [] /\ dec_digits x = []) \/ (1 <= d <= 9 /\ dec_digits x = (48 + d) :: W))%Z ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(forall m', mem_inv asegs m' -> bytes_at asegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(65536 <= PFXA)%Z -> (PFXA + zlength prefix <= 143488)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= x < 2^64)%Z ->
implM asegs (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 d) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 PFXA)
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 (q + -392 + jj)) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd42f0) fc None m (seg_rom asegs)).

Definition S_FMTU : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (x : Z) (prefix : list Z) (PFXA : Z)
(pfx s2s za plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(forall m', mem_inv asegs m' -> bytes_at asegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(65536 <= PFXA)%Z -> (PFXA + zlength prefix <= 143488)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= x < 2^64)%Z ->
implM asegs (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 x) x11 x12 x13 (Z_to_bv 64 10) x15 x16 (Z_to_bv 64 PFXA)
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd42a8) fc None m (seg_rom asegs)).

Definition S_CV_D : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (i : Z)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (i mod 2^64)) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(-2^31 <= i < 2^31)%Z ->
implM asegs (cnt' <- (let '(argi, prefix) :=
(if INTMAX_MAX <? i mod 2^64 then ((- (i mod 2^64)) mod 2^64, [45])
else if negb (Z.land fl MARK_POS =? 0) then (i mod 2^64, [43])
else if negb (Z.land fl PAD_POS =? 0) then (i mod 2^64, [32])
else (i mod 2^64, []))%Z in
conv_int OUT c fl w p xp argi prefix (dec_digits argi)) ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3fa4) fc None m (seg_rom asegs)).

Definition S_CV_U : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (u : Z)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= u < 2^32)%Z ->
implM asegs (cnt' <- conv_int OUT c fl w p xp u [] (dec_digits u) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd40dc) fc None m (seg_rom asegs)).

Definition xloop_post (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (l x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (a2 a3 : word) (m' : word -> option byte),
let H := hex_digits l x in
ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 l) a2 a3 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength H))) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd4194) fc None m' (seg_rom asegs)
/\ munch [(q + -392, q + -368)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength H)) ds ++ zb H ++ skipn (Z.to_nat j) ds)]
/\ (zlength H <= j)%Z.
Definition S_XLOOP : Prop :=
forall (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (l x j : Z) (ds : list byte),
let _ := ctx_all in
mem_inv asegs m -> rw_cells asegs m (q + -392) [CB 24 ds] ->
(0 < x < 2^64)%Z -> (l = 0 \/ l = 32)%Z -> (zlength (hex_digits l x) <= j <= 24)%Z -> x23 = Z_to_bv 64 (q + -392 + j) ->
evt asegs (xloop_post x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc l x j ds m)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) (Z_to_bv 64 l) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd416c) fc None m (seg_rom asegs)).

Definition S_CV_X : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (u t : Z)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= u < 2^32)%Z -> (t = 120 \/ t = 88)%Z ->
implM asegs (cnt' <- conv_int OUT c fl w p xp u
(if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0) then (if t =? 120 then [48; 120] else [48; 88]) else [])%Z
(hex_digits (Z.land t 32) u) ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd4154) fc None m (seg_rom asegs)).

Definition S_CV_S : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p fl10 : Z) (xp : bool) (P : Z) (s : list Z) (slack : list byte)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 P) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
bytes_at asegs m P (zb s ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256)%Z s ->
((- (P + zlength s + 1)) mod 8 <= zlength slack)%Z -> (0 < P)%Z ->
szone P (zlength s + 1) ->
(P + zlength s + 1 + zlength slack <= lo \/ q <= P)%Z ->
(P + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= P)%Z ->
(P + zlength s + 1 + zlength slack <= B \/ B + BS <= P)%Z ->
(P + zlength s + 1 + zlength slack <= 2^47)%Z ->
(fl10 = Z.land fl (Z.lnot 65536))%Z ->
implM asegs (cnt' <- (if (p <? 0) && (INT_MAX <=? zlength s) then munr
else conv_tail OUT c (Z.land fl (Z.lnot ZERO_PAD)) w (if p <? 0 then zlength s else Z.min (zlength s) p) []
(firstn (Z.to_nat (if p <? 0 then zlength s else Z.min (zlength s) p)) s))%Z ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) (Z_to_bv 64 fl10) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3fec) fc None m (seg_rom asegs)).

Definition S_CV_FP : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (y t : Z)
(pfx s2s za pl plp : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 (hi64 y)) j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
fpcall_stmt Fp B BS SINK TOPOK OUTFP (y, w, p, fl, t) ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= y < 2^128)%Z -> conv_type t = Some T_DBL ->
implM asegs (cnt' <- (if xp && (p <? 0) then munr
else if (1 <? w) || (2^20 <=? p) then munr
else r <- OUTFP y w p fl t ;; if (r <? 0) || (INT_MAX - c <? r) then munr else mret (c + r))%Z ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3f54) fc None m (seg_rom asegs)).

Definition POST1 : Z -> machine_state -> Prop :=
fun r ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F (ret_pc ra) fc0 None m' (seg_rom asegs)
/\ munch [(lo, q)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
/\ stk asegs m' lo q
/\ ssp_cells m' canary.

Definition S_EXIT1 : Prop :=
forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(m : word -> option byte) (r : Z)
(pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m -> munch [(lo, q)] m0 m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
(0 <= r < 2^64)%Z ->
evt asegs (POST1 r)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd47e8) fc0 None m (seg_rom asegs)).

Definition S_P1 : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
(m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m -> munch [(lo, q)] m0 m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
pass1_ok fmt = true ->
evt asegs (POST1 0)
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 A) x22 x23 x24 x25 (Z_to_bv 64 0) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd3abc) fc0 None m (seg_rom asegs)).

Definition S_PRO : Prop :=
forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (f : Z) (Q : machine_state -> Prop),
let _ := ctx_all in
stk asegs m0 lo q -> mem_inv asegs m0 -> bytes_at asegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
(0 <= f < 2^64)%Z ->
(forall (m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte) (a0 a1 a2 a3 : word),
finv m -> munch [(q + -544, q)]%Z m0 m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
evt asegs Q
(MS (mkR ra SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 nlt x15 x16 x17
s2e (Z_to_bv 64 0) (Z_to_bv 64 f) (Z_to_bv 64 A) s6e s7e s8e s9e (Z_to_bv 64 0) s11e x28 x29 x30 x31)
F (Z_to_bv 64 0xd3abc) fc0 None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 f) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
F (Z_to_bv 64 0xd3a0c) fc0 None m0 (seg_rom asegs)).

Unset Keyed Unification.
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia | glo_lia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; glo_lia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Hypothesis HS_CV_D : S_CV_D.
Hypothesis HS_CV_U : S_CV_U.
Hypothesis HS_CV_X : S_CV_X.
Hypothesis HS_CV_S : S_CV_S.
Hypothesis HS_CV_FP : S_CV_FP.

Lemma L_CONV : S_CONV.
Proof using BS0 GLO HA HAP HF HS_CV_D HS_CV_FP HS_CV_S HS_CV_U HS_CV_X HVA LO QHI SEP_B SEP_F SFL SFR VAHI BAND.
intros fuel HH x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c d a args pfx s2s za pl plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Ht CT Hfl Hw Hp XP Hc.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.

cbn [args_ok] in AOK. destruct (skipn (Z.to_nat k) slots) as [|slot slots'] eqn:ESK; [destruct AOK|]. destruct AOK as [AOK1 AOK].
assert (NTH : nth_error slots (Z.to_nat k) = Some slot).
{ rewrite <- (Nat.add_0_r (Z.to_nat k)), <- nth_error_skipn, ESK. reflexivity. }
assert (ESK' : skipn (Z.to_nat (k + 1)) slots = slots').
{ replace (Z.to_nat (k + 1)) with (1 + Z.to_nat k)%nat by lia. rewrite <- skipn_skipn, ESK. reflexivity. }
rewrite <- ESK' in AOK.
destruct (lo_split _ _ _ _ _ _ _ _ _ _ LOW) as (LOW14 & ARGC & J128). unfold lo_cells14, ssp_guard in LOW14. clear LOW.
pose proof (conv_type_cases _ _ CT) as CASES. pose proof (conv_type_range _ _ CT) as TR.
pose proof (land_bound' (d_fl d) 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq (d_fl d)) in FLB by lia.
unfold conv. cbv zeta. unfold LEFT_ADJ, ZERO_PAD.

destruct (Z.eq_dec (d_ty d) T_DBL) as [EDBL|NDBL].
{ destruct a as [sv | iv | uv | dd];
[ destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [exfalso; unfold T_PTR, T_DBL in *; lia | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [exfalso; unfold T_INT, T_DBL in *; lia | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [exfalso; unfold T_UINT, T_DBL in *; lia | cbn [negb]; apply implM_unr_l]
| cbv zeta; apply implM_unr_l ]. }

ienter; zs; br K; zs; zs; zs; zs.
callx (eapply pop_arg_callq; [lia | exact APC | exact VAA | exact NTH | lia | exact ARGC | exact ST | exact MI | unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, NDBL |- *; (first [ clear - K NDBL CASES LU LZB d HAP SEP_F GLO LO slots VA AP fmt lo q Fp BAND; lia | lia ])]).
match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rename H into ARGC' end.
match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
zs.
match goal with H : SINK ?mm _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (SFL _ _ H) as (fb & FLC & FB & ISHm) end; zs; zs; zs; br K1; clear FLC.
rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht.
zsto 0xd3f10%Z; change (Z.b2z (0 <? 0)) with 0%Z; rewrite Z.land_0_l; zs; br K2a; zsto 0xd3f24%Z; rewrite (nzmask_eq (d_fl d)) by lia; zs; brf K2;
[ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
| assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; lia);
rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ].
all: zsto 0xd3f34%Z; zs; br K3; zsto 0xd3f48%Z.
all: replace (Z.shiftl (d_t d + -65) 2 + 160024)%Z with (160024 + 4 * (d_t d - 65))%Z by (rewrite Z.shiftl_mul_pow2; lia).

all: apply evt_done.
all: destruct a as [sv | iv | uv | dd];
[ destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
|  cbv zeta; apply implM_unr_l ].
all: try (match goal with ETY : d_ty ?dd = T_PTR |- _ => assert (T115 : d_t dd = 115%Z) by (clear - CASES ETY; unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia) end).
all: try (match goal with ETY : d_ty ?dd = T_INT |- _ => assert (TDI : (d_t dd = 100 \/ d_t dd = 105)%Z) by (clear - CASES ETY; unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia) end).
all: try (match goal with ETY : d_ty ?dd = T_UINT |- _ =>
assert (TUX : (d_t dd = 117 \/ (d_t dd = 120 \/ d_t dd = 88))%Z) by (clear - CASES ETY; unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia);
destruct TUX as [T117 | TX];
[ rewrite (proj2 (Z.eqb_eq _ _) T117) | replace (d_t dd =? 117)%Z with false by (symmetry; apply Z.eqb_neq; (first [ clear - TX K NDBL LU LZB d HAP SEP_F GLO LO slots VA AP fmt lo q Fp BAND; lia | lia ])) ] end).
all: match goal with H : rw_cells _ _ (q + -544 + 112)%Z _, ETY : d_ty ?dd = _ |- _ => rewrite ETY in H; cbn [pop_arg_lo pop_arg_hi QoBx.T_PTR QoBx.T_INT QoBx.T_UINT QoBx.T_DBL T_PTR T_INT T_UINT T_DBL Z.eqb Pos.eqb] in H end.
all: ienter.
all: first [ the_mi ltac:(fun M => pose proof (jt1_read_s _ _ M T115) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_d _ _ M TDI) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_x _ _ M TX) as RD1) ].
all: zs; zs; zs.

all: let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end.
all: assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; (first [ clear - LU LZB Hfl d slots fmt BAND FLB; lia | lia ])).
all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mm _) =>
lazymatch pc with
| 868332%Z =>
rewrite <- (Z_to_bv_bv_unsigned slot) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
match goal with MUc : munch _ m0 mm |- _ =>
destruct (arg_ok_W _ _ _ _ AOK1 MUc) as (slack & STR & SRNG & SPAD & P0 & SZS & SD1 & SD2 & SD3 & SD4 & SD5) end;
stmt (HS_CV_S fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
(xp := d_xp d) (P := bv_unsigned slot) (s := sv) (slack := slack));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | exact P0 | exact SZS | exact SD1 | exact SD2 | exact SD3 | exact SD5
| subst fl'; rewrite ?land_land_same; reflexivity ]
| 868260%Z =>
destruct AOK1 as [Hiv Emod];
rewrite (sx32_int slot iv Hiv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_D fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (i := iv));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Hiv ]
| 868572%Z =>
destruct AOK1 as [Huv Emod];
rewrite (zx32_uint slot uv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_U fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Huv ]
| 868692%Z =>
destruct AOK1 as [Huv Emod];
rewrite (zx32_uint slot uv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_X fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv) (t := d_t d));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Huv | exact TX ]

end end.
Qed.

Set Keyed Unification.
Hypothesis HS_FMTU : S_FMTU.

Lemma fl_shl52 : forall fl, (0 <= fl < 131072)%Z ->
(Z.land (Z.shiftl fl 52) 18446744073709551615 < 9223372036854775808 <-> Z.land fl 2048 = 0)%Z.
Proof using .
clear. intros fl Hfl. rewrite Z.shiftl_mul_pow2 by lia.
change 2048%Z with (2^11)%Z. rewrite zb_land_pow2 by lia.
change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
split; intros H; Z.div_mod_to_equations; nia.
Qed.

Lemma L_CV_D : S_CV_D.
Proof using BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR BAND.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp i pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hi.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
stmt (HS_FMTU fuel HH) as NX.
pose proof (Z.mod_pos_bound i (2^64) ltac:(lia)) as RA.
set (argi := (i mod 2^64)%Z) in *.
unfold INTMAX_MAX, MARK_POS, PAD_POS.
ienter.
zs. zs. brf K1.
-
zs. zs. zs. zs. zs. zs. zs. zs.
replace (Z_to_bv 64 (0 - argi)) with (Z_to_bv 64 ((- argi) mod 2 ^ 64)) in * by (apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; f_equal; lia).
replace (9223372036854775807 <? argi)%Z with true by (symmetry; apply Z.ltb_lt; lia).
pose proof (Z.mod_pos_bound (- argi) (2^64) ltac:(lia)) as RB.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := ((- argi) mod 2 ^ 64)%Z) (prefix := [45%Z]) (PFXA := 68991%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; exact (pfx_sub mq 0 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
- replace (9223372036854775807 <? argi)%Z with false by (symmetry; apply Z.ltb_ge; lia).
zs. zs. zs. zs. zs. brf K2.
+
assert (HM : Z.land fl 2048 <> 0%Z) by (intros E; apply (proj2 (fl_shl52 fl Hfl)) in E; lia).
replace (Z.land fl 2048 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact HM). cbn [negb].
zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [43%Z]) (PFXA := 68992%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; exact (pfx_sub mq 1 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
+ assert (HM : Z.land fl 2048 = 0%Z) by (apply (proj1 (fl_shl52 fl Hfl)); lia).
replace (Z.land fl 2048 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact HM). cbn [negb].
zs. zs. zs. zs. zs.
pose proof (land_bound' fl 1 ltac:(lia) ltac:(lia)) as B1.
assert (C1 : (Z.land fl 1 = 0 \/ Z.land fl 1 = 1)%Z).
{ pose proof (Z.land_ones fl 1 ltac:(lia)) as E. change (Z.ones 1) with 1%Z in E. change (2^1)%Z with 2%Z in E. rewrite E.
pose proof (Z.mod_pos_bound fl 2 ltac:(lia)). lia. }
destruct C1 as [E1 | E1]; rewrite E1 in *.
*
cbn [Z.eqb negb Z.mul Z.add].
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := []) (PFXA := 68991%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
*
cbn [Z.eqb negb Z.mul Z.add].
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [32%Z]) (PFXA := 68993%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; exact (pfx_sub mq 2 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
Qed.

Set Keyed Unification.

Lemma L_CV_FP : S_CV_FP.
Proof using GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ BAND BS0.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp y t pfx s2s za pl plp j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Hfl Hw Hc XP Hy CT.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (conv_type_dbl t CT) as [Ht Hta].
pose proof (lo64_range y) as RL. pose proof (hi64_range y) as RH.
ienter.

assert (XF : (xp && (p <? 0))%bool = false).
{ destruct XP as [[-> ->] | [-> Hp]]; [reflexivity|]. cbn [andb]. apply Z.ltb_ge. lia. }
rewrite XF.
destruct XP as [[-> ->] | [-> Hp]]; cbn [Z.b2z];
[ zs; zs; rewrite Z.land_0_l; zs; if_lit
| zs; zs;
replace (Z.lxor p 9223372036854775808 <? 9223372036854775808)%Z with false
by (symmetry; apply Z.ltb_ge; change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; lia);
cbn [Z.b2z Z.land]; zs; if_lit ].

all: destruct (Z.ltb_spec0 1 w) as [W1|W1]; [cbn [orb]; ileave; apply implM_unr_l|].
all: match goal with |- context [if (?a || ?b)%bool then munr else _] =>
destruct b eqn:P20; [ileave; apply implM_unr_l | cbn [orb]] end.
all: match goal with P20 : (?a <=? ?pp)%Z = false |- _ => apply Z.leb_gt in P20 end.
all: zs; zs; zs; zs; zs; zs; zs; zs.
all: ileave; massoc; eapply implM_bind;
[ eapply fp_callq;
[ exact FPC1 | exact HS | rewrite !unsigned_lit by lia; symmetry; apply lo64_hi64; lia | rewrite unsigned_lit by lia; lia | lia | lia | lia | lia | exact Hta
| exact ST | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | exact MI | exact FRM ]
| cbv beta ].
all: intros r st'; lazymatch goal with |- context [fp_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => post_call asegs mm end.
all: try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end).
all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
all: unfold INT_MAX in *.

all: destruct (Z.lt_ge_cases r 0) as [RN|RP];
[ replace ((r <? 0) || (2147483647 - c <? r))%bool with true by (symmetry; apply orb_true_iff; left; apply Z.ltb_lt; exact RN); apply implM_unr_l | ].
all: destruct (Z.lt_ge_cases 2147483647 r) as [RB|RS];
[ replace ((r <? 0) || (2147483647 - c <? r))%bool with true by (symmetry; apply orb_true_iff; right; apply Z.ltb_lt; lia); apply implM_unr_l | ].
all: replace (r <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia); cbn [orb].
all: destruct (Z.ltb_spec0 (2147483647 - c) r) as [OV|OV]; [apply implM_unr_l|].
all: apply implM_ret_l.
all: ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
all: zs; zs; brf KR; [ | exfalso; try rewrite unsigned_lit in KR by lia; try rewrite land_M64_id in KR by lia; lia ].
all: stmt HH as NXH.
all: jumpM (eapply NXH with (i := i4) (cnt := c) (l := r) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; hyp | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC
| assumption | exact FOK2 | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Unset Keyed Unification.
Hypothesis HS_TAIL : S_TAIL.

Lemma L_CV_S : S_CV_S.
Proof using BS0 GLO HA HAP HS_TAIL HVA LO QHI SEP_B SEP_F SFL SFR VAHI BAND.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p fl10 xp P s slack pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP STR SRNG SPAD P0 SZS SD1 SD2 SD3 SD4 E10.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app, zb_length in SB. cbn [length] in SB.
assert (LSB : Z.of_nat (length (zb s ++ Z_to_bv 8 0 :: slack)) = (Z.of_nat (length s) + 1 + Z.of_nat (length slack))%Z)
by (rewrite length_app, zb_length; cbn [length]; lia).
pose proof (zb_nonul s SRNG) as NONUL. pose proof (zb_length s) as LZS.
pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq fl) in FLB by lia.
assert (BRNG : forall n, Forall (fun c0 => 0 <= c0 < 256)%Z (firstn n s)).
{ intros n. rewrite <- (skipn_O s). apply Forall_sub. eapply Forall_impl; [|exact SRNG]. cbv beta. intros. lia. }
stmt (HS_TAIL fuel HH) as NX.
set (len := Z.of_nat (length s)) in *.
unfold ZERO_PAD.
ienter.
zs. zs. brf K0; [|exfalso; lia].
destruct XP as [[-> ->] | [-> Hp]].
-
cbn [Z.b2z]. change ((-1) <? 0)%Z with true. cbn [andb].
destruct (Z.leb_spec0 2147483647 len) as [BIG|SMALL]; [ileave; apply implM_unr_l|].
rewrite ?ift, ?iff.
zs. zs. if_lit. zs. zs. zs.
callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack) (n := 2147483647%Z);
[ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
| rewrite length_app, zb_length; cbn [length]; unfold zlength in *; (first [ clear - K0 LZS SB LU LZB SD3 SD2 SD1 P0 SPAD len slack s P BS0 HAP SEP_B SEP_F GLO LO slots VA AP fmt lo q BS B Fp BAND; lia | lia ]) | lia | lia
| match goal with H : SINK ?mm _ |- ISH ?mm => destruct (SFL _ _ H) as (fbq & FLCq & FBq & ISHq); exact ISHq | |- ?g => idtac "ISHslotFAILED" g; fail end
| match goal with |- szone _ (memchr_len 0 ?nn _) => pose proof (memchr_len_cstr_le nn (zb s) slack NONUL ltac:(lia)) as MLB end;
rewrite zb_length in MLB; eapply szone_sub; [exact SZS| (first [ clear - LZS SB LU LZB len slack s P slots fmt BAND; lia | lia ])| unfold zlength in *; lia| lia] ]).
rewrite (strnlen_res_cstr 0) by exact NONUL. rewrite zb_length. fold len. replace (Z.min len 2147483647) with len by lia.
match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR1 end.
zs. zs. if_lit.
assert (NTH : nth_error (zb s ++ Z_to_bv 8 0 :: slack) (Z.to_nat len) = Some (Z_to_bv 8 0)).
{ rewrite nth_error_app2 by (rewrite zb_length; lia). rewrite zb_length. replace (Z.to_nat len - length s)%nat with 0%nat by lia. reflexivity. }
pose proof (u8ro_read asegs _ P (zb s ++ Z_to_bv 8 0 :: slack) len (Z_to_bv 8 0) _ STR1 NTH ltac:(lia) eq_refl) as RD.
zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. zs. if_lit. zs. zs. zs. zs. zs. zs. zs.
match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at asegs mm P (zb s)) end.
{ pose proof STR2 as STR3. apply bytes_at_app in STR3. exact (proj1 STR3). }
rewrite (@firstn_all2 Z (Z.to_nat len) s) by (unfold len; lia).
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := len) (prefix := []) (body := s) (BA := P) (PFXA := 68991%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact SUB | eapply Forall_impl; [|exact SRNG]; cbv beta; intros; lia
| unfold body_loc; split; [zl| solve_szone] | zl | unfold INT_MAX; zl
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
-
replace (p <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb Z.b2z]. rewrite ?ift, ?iff.
zs. zs.

lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if _ then Z_to_bv 64 ?pcj else _) ?fc ?rv ?m ?ro) =>
let pk := eval vm_compute in (bv_key (Z_to_bv 5 11)) in
let R' := eval cbv beta iota delta [tset] in (tset pk (Z_to_bv 64 p) R) in
apply (evt_cut segs (fun ms' : machine_state => ms' = MS R' F (Z_to_bv 64 pcj) fc rv m ro) Q)
end.
{ brf K1; [ apply evt_done; reflexivity
| zs; apply evt_done; assert (Ep : p = 2147483647%Z) by lia; rewrite Ep; reflexivity ]. }
intros ms' ->.

all: zs; zs.
all: callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack);
[ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
| rewrite length_app, zb_length; cbn [length]; unfold zlength in *; (first [ clear - K0 LZS SB LU LZB SD3 SD2 SD1 P0 SPAD len slack s P BS0 HAP SEP_B SEP_F GLO LO slots VA AP fmt lo q BS B Fp BAND; lia | lia ]) | lia | lia
| match goal with H : SINK ?mm _ |- ISH ?mm => destruct (SFL _ _ H) as (fbq & FLCq & FBq & ISHq); exact ISHq | |- ?g => idtac "ISHslotFAILED" g; fail end
| match goal with |- szone _ (memchr_len 0 ?nn _) => pose proof (memchr_len_cstr_le nn (zb s) slack NONUL ltac:(lia)) as MLB end;
rewrite zb_length in MLB; eapply szone_sub; [exact SZS| lia| unfold zlength in *; lia| lia] ]).
all: rewrite (strnlen_res_cstr 0) by exact NONUL; rewrite zb_length; fold len.
all: zs; zs; br K2; zs; zs; zs; zs; zs; zs; zs.
all: match goal with H : bytes_at _ ?mm ?PP (zb _ ++ _) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
all: lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at asegs mm P (zb (firstn (Z.to_nat (Z.min len p)) s)))
by (pose proof STR2 as STR3; rewrite <- (firstn_skipn (Z.to_nat (Z.min len p)) s) in STR3; rewrite zb_app, <- app_assoc in STR3; apply bytes_at_app in STR3; exact (proj1 STR3)) end.
all: assert (LF : zlength (firstn (Z.to_nat (Z.min len p)) s) = Z.min len p) by (unfold zlength; rewrite length_firstn; lia).
all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := Z.min len p) (prefix := []) (body := firstn (Z.to_nat (Z.min len p)) s) (BA := P) (PFXA := 68991%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact SUB | apply BRNG
| unfold body_loc; split; [rewrite LF; (first [ clear - K0 LZS LSB SB LU LZB SD3 SD2 SD1 P0 SPAD len Hp slack s P p BS0 HAP SEP_B SEP_F GLO LO slots VA AP fmt lo q BS B Fp BAND; lia | lia ])| rewrite LF; eapply szone_sub; [exact SZS| lia| unfold zlength in *; lia| lia]] | rewrite LF; lia | rewrite LF; unfold INT_MAX; lia
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
all: match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
Qed.

Set Keyed Unification.

Lemma L_CV_U : S_CV_U.
Proof using GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR BAND.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
stmt (HS_FMTU fuel HH) as NX.
ienter.
zs. zs. zs. zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := u) (prefix := []) (PFXA := 68991%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros m' MI'; exact (pfx_sub m' 0 0 MI' ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
Qed.

Set Keyed Unification.
Hypothesis HS_INTC : S_INTC.
Hypothesis HS_XLOOP : S_XLOOP.

Lemma L_CV_X : S_CV_X.
Proof using BS0 GLO HA HAP HS_INTC HS_XLOOP HVA LO QHI SEP_B SEP_F SFR BAND.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u t pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu Ht.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
stmt (HS_INTC fuel HH) as NX.
unfold ALT_FORM.
assert (Hl : (Z.land t 32 = 0 \/ Z.land t 32 = 32)%Z) by (destruct Ht as [-> | ->]; [right | left]; reflexivity).
pose proof (hex_digits_length (Z.land t 32) u) as LH.
assert (HRNG : Forall (fun c0 => 0 <= c0 < 256)%Z (hex_digits (Z.land t 32) u)).
{ eapply Forall_impl; [|apply hex_digits_range; exact Hl]. cbv beta. intros. lia. }
ienter.
zs. zs. zs. zs. brf K0.
-
replace (u =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K0). cbn [negb andb].
zs. zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := []) (BA := (q + -368)%Z) (PFXA := 68991%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| rewrite K0, hex_digits_0; apply bytes_at_nil; lia | exact HRNG | rewrite K0, hex_digits_0; zl | zl
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
- replace (u =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K0). cbn [negb andb].
zs. zs.
replace (Z.land t 32) with (Z.land t 32) by reflexivity.
stmt HS_XLOOP as NL.
callx (eapply NL with (l := Z.land t 32) (x := u) (j := 24%Z) (ds := digs);
[ exact MI | exact DIG | lia | exact Hl | unfold zlength; lia | f_equal; lia ]).
destruct_ands POST. cbv zeta in *.
match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ =>
rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
pose proof (rw_cells_bytes_at' _ _ _ _ DIG') as BODY. cbn [cells_bytes cbytes app] in BODY. rewrite app_nil_r in BODY.
apply bytes_at_app in BODY. destruct BODY as [_ BODY]. rewrite length_firstn, LDS in BODY.
replace (Z.of_nat (Nat.min (Z.to_nat (24 - zlength (hex_digits (Z.land t 32) u))) 24)) with (24 - zlength (hex_digits (Z.land t 32) u))%Z in BODY by (unfold zlength in *; lia).
zs. zs. brf K1.
+
replace (Z.land fl 8 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K1). cbn [negb andb].
zs. zs. zs. zs. zs. zs. zs. zs.
destruct Ht as [-> | ->]; cbn [Z.eqb Pos.eqb].
* jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 120]%Z)
(BA := (q + -392 + (24 - zlength (hex_digits (Z.land 120 32) u)))%Z) (PFXA := 68998%Z));
[ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact BODY | exact HRNG | unfold zlength in *; lia | zl
| intros mq MIq; exact (pfx_sub mq 7 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
* jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 88]%Z)
(BA := (q + -392 + (24 - zlength (hex_digits (Z.land 88 32) u)))%Z) (PFXA := 68996%Z));
[ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact BODY | exact HRNG | unfold zlength in *; lia | zl
| intros mq MIq; exact (pfx_sub mq 5 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
+
replace (Z.land fl 8 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K1). cbn [negb andb].
zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [])
(BA := (q + -392 + (24 - zlength (hex_digits (Z.land t 32) u)))%Z) (PFXA := 68991%Z));
[ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact BODY | exact HRNG | unfold zlength in *; lia | zl
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
Qed.

Set Keyed Unification.
Hypothesis HS_FLAGS : S_FLAGS.
Hypothesis HS_WIDTH : S_WIDTH.
Hypothesis HS_PREC : S_PREC.
Hypothesis HS_STATE : S_STATE.

Lemma L_DIR : S_DIR.
Proof using HF HS_FLAGS HS_PREC HS_STATE HS_WIDTH BAND.
intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q i d rest pfx s2s za pl plp alo ahi j128 _
FI LOW Hi Hi1 PD HK.
pose proof FI as FI'. dest_finv FI. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
pose proof (parse_dir_shape _ _ _ PD) as (POSN & SH).
destruct (parse_flags (sfx (i + 1)) 0) as [fl s1] eqn:PF.
destruct SH as (Efl & c1' & s1b & Es1 & N42 & s2 & G & c2 & s2b & Es2 & PX).

destruct (parse_flags_suffix _ _ _ _ PF) as (n1 & Hs1 & Hn1). rewrite sfx_skipn in Hs1 by lia. set (k1 := (i + 1 + Z.of_nat n1)%Z) in Hs1.
rewrite Hs1 in Es1. destruct (sfx_cons_inv fmt k1 c1' s1b ltac:(lia) Es1) as (Hk1 & Ec1' & Es1b).
destruct (getint_suffix _ _ _ _ G) as (n2 & Hs2 & Hn2). rewrite Hs1, sfx_skipn in Hs2 by lia. set (k2 := (k1 + Z.of_nat n2)%Z) in Hs2.
rewrite Hs2 in Es2. destruct (sfx_cons_inv fmt k2 c2 s2b ltac:(lia) Es2) as (Hk2 & Ec2 & Es2b).
assert (Hi1' : (i + 1 < zlength fmt)%Z) by zl.
rewrite (sfx_cons fmt (i + 1)) in POSN, PF by zl.

assert (POSTFLAGS : forall (t0 t1 a3 a4 a5 a6 a7 : word),
evt asegs Q
(MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) a3 a4 a5 a6 a7
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3c34) fc None m (seg_rom asegs))).
{ intros t0 t1 a3 a4 a5 a6 a7.
pose proof (parse_flags_range (sfx (i + 1)) 0 ltac:(lia)) as FLR. rewrite (sfx_cons fmt (i + 1)), PF in FLR by zl. cbn [fst] in FLR.
stmt HS_WIDTH as NXW. jump (eapply NXW with (k1 := k1) (w := d_w d) (s2 := s2); [exact FI' | exact LOW' | lia | rewrite <- Hs1; exact G | rewrite Hs2, Es2; discriminate | ]).
intros k2' t0' t1' a1' a3' a4' a5' a6' a7' Hk2' Hs2' Hnd Hw.
assert (k2' = k2).
{ pose proof (sfx_length fmt k2 ltac:(zl)) as L1. pose proof (sfx_length fmt k2' ltac:(zl)) as L2. rewrite <- Hs2', Hs2 in L2. lia. }
subst k2'.
stmt HS_PREC as NXP. jump (eapply NXP with (k2 := k2) (p := d_p d) (xp := d_xp d) (k3 := (if d_xp d then k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 else k2)%Z);
[exact FI' | exact LOW' | lia | | ]).
{ destruct PX as [(N46 & Hp & Hxp & Ht & Hrest & CT) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & Es3 & CT)].
- left. rewrite <- Ec2, Hxp. repeat split; try assumption; reflexivity.
- right. rewrite Hxp. rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
rewrite Hs3 in Es3.
assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
destruct (sfx_cons_inv fmt (k2 + 1 + Z.of_nat n3) (d_t d) rest Hk30 Es3) as (Hk3 & Et & Erest).
assert (EK : (k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 = k2 + 1 + Z.of_nat n3)%Z).
{ rewrite Es2b, Erest. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)). pose proof (sfx_length fmt (k2 + 1 + Z.of_nat n3 + 1) ltac:(zl)). unfold zlength in *. lia. }
rewrite EK. split; [congruence|]. split; [reflexivity|]. split; [zl|]. split; [rewrite <- Ec3; exact N42q|].
split; [rewrite <- Es2b, <- Hs3; exact G2 | zl]. }
intros a1q a3q a4q Hp.
destruct PX as [(N46 & Hpq & Hxp & Ht & Hrest & CT) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & Es3 & CT)].
- rewrite Hxp. cbn [Z.b2z].
stmt HS_STATE as NXS. jump (eapply NXS with (k3 := k2) (ty := d_ty d); [exact FI' | zl | rewrite <- Ec2; exact CT | ]).
intros a2q a3q2. rewrite Hxp in HK. cbn [Z.b2z] in HK.
jump (apply (HK (k2 + 1)%Z); [zl | rewrite Hrest, Es2b; reflexivity | replace (k2 + 1 - 1)%Z with k2 by lia; rewrite <- Ec2, Ht; reflexivity | lia | lia | lia]).
- rewrite Hxp. cbn [Z.b2z]. rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
rewrite Hs3 in Es3.
assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
destruct (sfx_cons_inv fmt (k2 + 1 + Z.of_nat n3) (d_t d) rest Hk30 Es3) as (Hk3 & Et & Erest).
assert (EK : (k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 = k2 + 1 + Z.of_nat n3)%Z).
{ rewrite Es2b, Erest. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)). pose proof (sfx_length fmt (k2 + 1 + Z.of_nat n3 + 1) ltac:(zl)). unfold zlength in *. lia. }
rewrite EK.
stmt HS_STATE as NXS. jump (eapply NXS with (k3 := (k2 + 1 + Z.of_nat n3)%Z) (ty := d_ty d); [exact FI' | zl | rewrite <- Et; exact CT | ]).
intros a2q a3q2. rewrite Hxp in HK. cbn [Z.b2z] in HK.
jump (apply (HK (k2 + 1 + Z.of_nat n3 + 1)%Z); [zl | exact Erest | replace (k2 + 1 + Z.of_nat n3 + 1 - 1)%Z with (k2 + 1 + Z.of_nat n3)%Z by lia; symmetry; exact Et | lia | lia | lia]). }

assert (FL34 : forall (a3 a4 a5 : word), evt asegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt (i + 1))) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 (Z_to_bv 64 1) x17
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3ba4) fc None m (seg_rom asegs))).
{ intros a3q a4q a5q. pose proof (fmt_rng (i + 1) ltac:(zl)) as RG.

assert (NOFLAG : flag_bit (znth fmt (i + 1)) = None -> fl = 0%Z /\ k1 = (i + 1)%Z).
{ intros NF. rewrite (parse_flags_cons_none _ _ _ NF) in PF. injection PF as Efl0 Es1q. split; [congruence|].
pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt (i + 1) ltac:(zl)) as L2.
rewrite (sfx_cons fmt (i + 1)) in L2 by zl. rewrite Es1q, Hs1 in L2. lia. }
zs. zs. zs. brf K2.
-
assert (NF : flag_bit (znth fmt (i + 1)) = None).
{ destruct (flag_bit (znth fmt (i + 1))) eqn:E; [|reflexivity]. exfalso.
pose proof (flag_bit_range (znth fmt (i + 1)) ltac:(congruence)) as R. rewrite land_M64_id in K2 by lia. lia. }
destruct (NOFLAG NF) as [Efl0 Ek1].
zs. zs. zs. brf K3. { exfalso. apply N42. rewrite Ec1', Ek1. exact K3. }
jump (apply POSTFLAGS).
- assert (Hc : (32 <= znth fmt (i + 1) < 64)%Z) by (apply (proj1 (sp_test _ RG)); lia).
rewrite (land_M64_id (znth fmt (i + 1) + -32)) in * by lia.
zs. zs. zs. zs. zs. brf K3.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
assert (NF : flag_bit (znth fmt (i + 1)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
destruct (NOFLAG NF) as [Efl0 Ek1].
zs. zs. brf K4; [ jump (apply POSTFLAGS) | exfalso; apply N42; rewrite Ec1', Ek1; exact K4 ].
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
destruct (flag_bit (znth fmt (i + 1))) as [b|] eqn:E.
2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
pose proof (flag_some _ _ Hc E) as [Hfw Hb].
rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
zs.
stmt HS_FLAGS as NXF. jump (eapply NXF with (p := (i + 1)%Z) (k := 1%Z) (fl := 0%Z) (b := b) (FL := fl) (s1 := s1);
[exact FI' | lia | lia | zl | rewrite unsigned_lit_land; exact Hfw | lia | lia | rewrite Z.lor_0_l; exact PF | rewrite Hs1, Es1; discriminate | ]).
intros k' c' a3' a4' a5' Hk' Hs1' Hc' HN HFL.
assert (Ek1 : k' = k1).
{ pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt k' ltac:(zl)) as L2. rewrite <- Hs1', Hs1 in L2. lia. }
subst k'. subst c'. pose proof (fmt_rng k1 ltac:(zl)) as RGk.
zs. zs. brf K4; [ | exfalso; apply N42; rewrite Ec1'; exact K4 ].
jump (apply POSTFLAGS). }

rd_fmt (i + 1)%Z. zs. fix_u8 (i + 1)%Z. zs. zs. zs. zs. zs. brf K.
-  zs. zs. apply FL34.
- assert (DG : is_digit (znth fmt (i + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
assert (Hi2 : (i + 2 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (i + 2) (zlength fmt)); [assumption|]. exfalso.
rewrite (sfx_nil fmt (i + 1 + 1)) in POSN by lia. rewrite DG in POSN. discriminate. }
replace (i + 1 + 1)%Z with (i + 2)%Z in POSN by lia.
rewrite (sfx_cons fmt (i + 2)) in POSN by zl. rewrite DG in POSN. cbn [andb] in POSN. apply Z.eqb_neq in POSN.
rd_fmt (i + 2)%Z. zs. fix_u8 (i + 2)%Z. zs. zs. zs. zs. br K1. apply FL34.
Qed.

Set Keyed Unification.

Lemma L_DLOOP : S_DLOOP.
Proof using GLO LO QHI BAND.
intros x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m x.
remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x11 x12 x13 x23 m.
induction nx as [nx IH] using lt_wf_ind.
intros x Enx x11 x12 x13 x23 m j ds _ MI DIG Hx Hj ->.
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (dec_digits_step x ltac:(lia)) as DS.
pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)) as Q0.
pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as R0.
assert (Q1 : (x / 10 < 1844674407370955162)%Z) by (apply Z.div_lt_upper_bound; lia).
assert (LD : (2 <= zlength (dec_digits x))%Z).
{ rewrite DS. unfold zlength. rewrite length_app. cbn [length].
destruct (Z.lt_ge_cases (x / 10) 10).
- rewrite dec_digits_small by lia. cbn. lia.
- rewrite (dec_digits_step (x / 10)) by lia. rewrite length_app. cbn [length]. lia. }
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
zs. zs. zs. zs. zs.
rewrite (land_W64_small (Z.shiftr (x * 14757395258967641293) 64)) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite div10_magic by lia. zs. zs. zs.
replace (bv_swrap 32 (x - x / 10 * 10)) with (x mod 10)%Z by (rewrite swrap32_small by lia; lia).
rewrite (land_W64_small (x mod 10)) by lia. rewrite lor48_digit by lia.
set (c := (48 + x mod 10)%Z) in *.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA.
pose proof (u8arr_store_ok asegs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
zs. zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
pose proof (u8arr_write asegs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
zs. zs. brf K.
-
eapply evt_mono.
{ eapply (IH (Z.to_nat (x / 10)) ltac:(lia) (x / 10)%Z eq_refl); [ exact MI | exact DIG1 | lia | | reflexivity ].
rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
cbv beta. intros ms' P. destruct P as (a2' & a3' & xq & W' & m' & -> & MU' & WM' & MI' & DIG' & Hxq & HD & HW).
unfold dloop_post. exists a2', a3', xq, (W' ++ [c]), m'.
assert (EL : zlength (W' ++ [c]) = (zlength W' + 1)%Z) by (unfold zlength; rewrite length_app; cbn [length]; lia).
rewrite EL.
split; [ mseq | ].
split; [ eapply munch_trans; [exact MU | exact MU'] | ].
split; [ eapply wmono_trans; [exact WM | exact WM'] | ].
split; [ exact MI' | ].
split.
{ replace (firstn (Z.to_nat (j - (zlength W' + 1))) ds ++ zb (W' ++ [c]) ++ skipn (Z.to_nat j) ds)
with (firstn (Z.to_nat (j - 1 - zlength W')) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)) ++ zb W' ++ skipn (Z.to_nat (j - 1)) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c))); [exact DIG'|].
rewrite upd_firstn_part by (rewrite LDS; unfold zlength in *; lia). rewrite upd_skipn_at by (rewrite LDS; lia).
replace (Z.to_nat (j - 1 - zlength W')) with (Z.to_nat (j - (zlength W' + 1))) by lia.
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia.
rewrite zb_app, <- !app_assoc. reflexivity. }
split; [ exact Hxq | ]. split; [ rewrite DS, HD; reflexivity | ]. unfold zlength in *. lia.
-
zs. apply evt_done.
unfold dloop_post. eexists (Z_to_bv 64 x), (Z_to_bv 64 c), (x / 10)%Z, [c], _.
split; [ mseq | ].
split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact MI | ].
split.
{ replace (firstn (Z.to_nat (j - zlength [c])) ds ++ zb [c] ++ skipn (Z.to_nat j) ds) with (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)); [exact DIG1|].
rewrite upd_firstn_skipn by (rewrite LDS; lia). cbn [zb map app zlength length Z.of_nat Pos.of_succ_nat].
replace (Z.to_nat (j - 1)) with (Z.to_nat (j - 1)) by reflexivity.
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. reflexivity. }
split; [ lia | ]. split; [ rewrite DS, dec_digits_small by lia; reflexivity | ]. zl.
Qed.

Set Keyed Unification.
Hypothesis HS_EXIT : S_EXIT.

Lemma L_END : S_END.
Proof using GLO HAP HS_EXIT LO SEP_F VAHI BAND.
intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m st r pfx s2s za pl plp l10n alo ahi j128 digs pad apv _
FI LOW DIG PAD HS APC FRM FOK Hr.
pose proof FI as FI'. dest_finv FI.
zs. br K.
stmt HS_EXIT as NX. jump (eapply NX; [exact FI' | exact LOW | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | exact Hr]).
Qed.

Set Keyed Unification.

Lemma L_EXIT : S_EXIT.
Proof using LO BAND.
intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
Ft fc m st r pfx s2s za pl plp l10n alo ahi j128 digs pad apv _ FI LOW DIG PAD HS APC FRM FOK Hr.
dest_finv FI. unfold lo_cells, ssp_guard in LOW.
zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 14 zstep.
zstep. zstep.

release_frame LOW ST (q + -392)%Z.
release_frame DIG ST (q + -368)%Z.
release_frame PAD ST (q + -112)%Z.
release_frame FRhi ST q.
apply evt_done. unfold POST.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact FOK|].
split; [exact ST|]. split; [exact HS|]. split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2]|]. split; [exact APC|]. exact Hr.
Qed.

Set Keyed Unification.

Lemma L_EXIT1 : S_EXIT1.
Proof using LO BAND.
intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
m r pfx s2s za pl plp l10n alo ahi j128 digs pad _ FI MU1 LOW DIG PAD Hr.
dest_finv FI. unfold lo_cells, ssp_guard in LOW.
zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 14 zstep.
zstep. zstep.
release_frame LOW ST (q + -392)%Z.
release_frame DIG ST (q + -368)%Z.
release_frame PAD ST (q + -112)%Z.
release_frame FRhi ST q.
apply evt_done. unfold POST1.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU1|]. split; [exact WM|]. split; [exact MI|].
split; [exact ST|]. unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2].
Qed.

Set Keyed Unification.

Lemma L_FLAGS : S_FLAGS.
Proof using HF BAND.
intros x1 x6 x7 x10 x11 x12 x15 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q p k fl b w3 FL s1 _
FI Hp Hk Hpk Hw3 Hfl Hb PF NE HK.
remember (Z.to_nat (zlength fmt - (p + k))) as kk eqn:Hkk.
revert k fl b w3 x11 x12 x15 Hk Hpk Hw3 Hfl Hb PF HK Hkk.
induction kk as [|kk IH]; intros.
{  rewrite sfx_nil in PF by (unfold zlength in *; lia). cbn in PF. injection PF as _ <-. exfalso. apply NE. reflexivity. }
assert (Hlt : (p + k < zlength fmt)%Z) by (unfold zlength in *; lia).
pose proof FI as FI'. dest_finv FI.
zs. rd_fmt (p + k)%Z. zs. fix_u8 (p + k)%Z. zs. zs. rewrite Hw3. zs. brf K.
-
assert (NF : flag_bit (znth fmt (p + k)) = None).
{ destruct (flag_bit (znth fmt (p + k))) eqn:E; [|reflexivity]. exfalso.
pose proof (flag_bit_range (znth fmt (p + k)) ltac:(congruence)) as R.
pose proof (proj2 (sp_test (znth fmt (p + k)) RG) R). lia. }
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
injection PF as EFL Es1.
rewrite Z.lor_comm, EFL.
jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
{ rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
rewrite <- EFL. apply lor_bound17; lia.
- assert (Hc : (32 <= znth fmt (p + k) < 64)%Z) by (apply (proj1 (sp_test _ RG)); exact K).
rewrite (land_M64_id (znth fmt (p + k) + -32)) in * by lia.
zs. zs. zs. zs. brf K2.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
destruct (flag_bit (znth fmt (p + k))) as [b'|] eqn:E.
2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
pose proof (flag_some _ _ Hc E) as [Hfw Hb'].
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
replace (A + p + k + 1)%Z with (A + p + (k + 1))%Z by lia.
rewrite Z.lor_comm.
eapply (IH (k + 1)%Z (Z.lor fl b) b'); try lia.
{ rewrite unsigned_lit_land. exact Hfw. }
{ apply lor_bound17; lia. }
{ replace (p + (k + 1))%Z with (p + k + 1)%Z by lia. exact PF. }
{ intros k' c' a3 a4 a5 Hk' Hs1 Hc' HN HFL. eapply HK; try eassumption; lia. }
all: unfold zlength in *; lia.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
assert (NF : flag_bit (znth fmt (p + k)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
injection PF as EFL Es1.
rewrite Z.lor_comm, EFL.
jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
{ rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
rewrite <- EFL. apply lor_bound17; lia.
Qed.

Set Keyed Unification.
Hypothesis HS_FMTU2 : S_FMTU2.
Hypothesis HS_DLOOP : S_DLOOP.

Lemma L_FMTU : S_FMTU.
Proof using BS0 GLO HA HAP HS_DLOOP HS_FMTU2 HVA LO SEP_B SEP_F SFR BAND.
intros fuel HH x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x prefix PFXA pfx s2s za plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hx.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
pose proof (dec_digits_length x) as LDX.
stmt (HS_FMTU2 fuel HH) as NX.
ienter.
zs. zs. zs. brf K.
-
zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := x) (d := x) (jj := 24%Z) (W := []) (prefix := prefix) (PFXA := PFXA) (pre := digs));
[ mk_finv | exact LOW | rewrite app_nil_r; exact DIG | zl | lia
| destruct (Z.eq_dec x 0) as [-> | NZ]; [left; split; [reflexivity|]; split; [reflexivity|]; apply dec_digits_0 | right; split; [lia|]; apply dec_digits_small; lia]
| exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
-
zs.
stmt HS_DLOOP as NL.
callx (eapply NL with (j := 24%Z) (ds := digs); [ exact MI | exact DIG | lia | unfold zlength; lia | f_equal; lia ]).
destruct_ands POST.
match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ => rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := x) (prefix := prefix) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG' | unfold zlength in *; rewrite length_firstn, LDS; lia | unfold zlength in *; lia
| right; split; [assumption | assumption]
| exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
Qed.

Set Keyed Unification.

Lemma L_FMTU2 : S_FMTU2.
Proof using BS0 GLO HA HAP HS_INTC HVA LO QHI SEP_B SEP_F SFR BAND.
intros fuel HH x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x d jj W prefix PFXA pfx s2s za plp ahi j128 pre pad _
FI LOW DIG Hjj Hjj1 HD PAD HS APC Hk AOK FPC FRM FOK HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hx.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (rw_CB_length _ _ _ _ DIG) as LDS. rewrite length_app, zb_length in LDS.
pose proof (dec_digits_length x) as LDX.
stmt (HS_INTC fuel HH) as NX.
ienter.
zs. zs. brf K1.
-
destruct HD as [(Hd0 & -> & DX) | (Hd & DX)]; [|exfalso; lia].
rewrite app_nil_r in DIG.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := x) (prefix := prefix) (body := dec_digits x) (BA := (q + -368)%Z) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| rewrite DX; apply bytes_at_nil; lia | eapply Forall_impl; [|apply dec_digits_range]; cbv beta; intros; lia | rewrite DX; zl | rewrite DX; zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
-
destruct HD as [(Hd0 & -> & DX) | (Hd & DX)]; [exfalso; lia|].
assert (LW : (Z.of_nat (length W) + 1 <= 20)%Z) by (rewrite DX in LDX; cbn [length] in LDX; lia).
zs. rewrite lor48_digit by lia. zs.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA. clear DIG.
pose proof (u8arr_store_ok asegs _ _ _ (jj - 1)%Z (wa (q + -392 + jj + -1)) DA ltac:(rewrite length_app, zb_length; unfold zlength in *; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_small by lia. replace (q + -392 + jj + -1)%Z with (q + -392 + (jj - 1))%Z by lia.
pose proof (u8arr_write asegs _ _ _ (jj - 1)%Z (Z_to_bv 8 (48 + d)) DA ltac:(rewrite length_app, zb_length; unfold zlength in *; lia)) as DA2. clear DA. store_done.
assert (EU : upd (pre ++ zb W) (Z.to_nat (jj - 1)) (Z_to_bv 8 (48 + d)) = firstn (Z.to_nat (jj - 1)) pre ++ zb ((48 + d)%Z :: W)).
{ rewrite upd_firstn_skipn by (rewrite length_app, zb_length; unfold zlength in *; lia).
rewrite firstn_app. replace (Z.to_nat (jj - 1) - length pre)%nat with 0%nat by (unfold zlength in *; lia). cbn [firstn]. rewrite app_nil_r.
replace (S (Z.to_nat (jj - 1))) with (length pre) by (unfold zlength in *; lia). rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
rewrite EU in DA2.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG.
replace (length (firstn (Z.to_nat (jj - 1)) pre ++ zb ((48 + d)%Z :: W))) with 24%nat in DIG
by (rewrite length_app, length_firstn, zb_length; cbn [length]; unfold zlength in *; lia).
pose proof (proj1 DA2) as BODY. apply bytes_at_app in BODY. destruct BODY as [_ BODY].
rewrite length_firstn in BODY. replace (Z.of_nat (Nat.min (Z.to_nat (jj - 1)) (length pre))) with (jj - 1)%Z in BODY by (unfold zlength in *; lia).
zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := x) (prefix := prefix) (body := dec_digits x) (BA := (q + -392 + (jj - 1))%Z) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| rewrite DX; exact BODY | eapply Forall_impl; [|apply dec_digits_range]; cbv beta; intros; lia | rewrite DX; zl | rewrite DX; zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
Qed.

Unset Keyed Unification.
Hypothesis HS_SCAN : S_SCAN.
Hypothesis HS_DIR : S_DIR.
Hypothesis HS_CONV : S_CONV.
Hypothesis HS_END : S_END.

Lemma L_HEAD : forall fuel, S_HEAD fuel.
Proof using A0 BS0 GLO HA HAP HF HOUT HS_CONV HS_DIR HS_END HS_SCAN HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI BAND.
induction fuel as [|fuel IH]; intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 Ft fc m st i cnt l k args pfx s2s za pl plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi Hcnt Hl Hcl.
{ cbn [printf_loop]. apply implM_unr. }
rewrite printf_loop_S. rewrite fp_calls_S in FPC.
destruct (sfx i) as [|c s'] eqn:Es. { apply implM_unr. }
destruct (sfx_cons_inv fmt i c s' Hi Es) as (Hilt & Ec & Es').
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
pose proof (fmt_rng i ltac:(zl)) as RGi.
destruct (Z.eqb_spec c 0) as [C0|C0].
{
apply implM_ret.
zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. rewrite <- Ec, C0. zs. fixr. zs. if_lit.
stmt HS_END as NX. jump (eapply NX; [exact FI' | exact LOW' | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | unfold INT_MAX; lia]). }
rewrite <- Es in *. cbv zeta. cbv zeta in FPC.
pose proof (lit_run_sfx fmt i Hi) as (Hn & Hs1 & LIT & Hlit). cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
set (lit := lit_run (sfx i)) in *. set (n := Z.of_nat (length lit)) in *.
rewrite Hs1. rewrite Hs1 in FPC.
assert (Hn0 : (0 <= n)%Z) by (unfold n; lia).
destruct (sfx (i + n)) as [|c1 s2] eqn:Es1. { apply implM_unr. }
destruct (sfx_cons_inv fmt (i + n) c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
match goal with |- context [if ?b then munr else _] => destruct b eqn:PCT; [apply implM_unr|] end.

assert (TERM : (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z).
{ pose proof (lit_run_stop (sfx i) c1 s2 Hs1) as ST12. rewrite <- Ec1.
destruct ST12 as [E0|E37]; [left; exact E0 | right]. split; [exact E37|].
rewrite E37, Z.eqb_refl in PCT. cbn [andb] in PCT. destruct s2 as [|c2 s2q]; [discriminate|].
destruct (sfx_cons_inv fmt (i + n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
split; [exact Hin1|]. rewrite <- Ec2. apply Z.eqb_neq. exact PCT. }
stmt HS_SCAN as NXS.
destruct (0 <? n) eqn:En; try rewrite En in FPC; [apply Z.ltb_lt in En; rename En into Npos | apply Z.ltb_ge in En; rename En into Nz].
-
destruct (Z.ltb_spec0 (2147483647 - (cnt + l)) n) as [|Hncl]; [apply implM_unr|].
ienter.
zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
jump (eapply NXS with (i := i) (n := n) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | exact LIT | exact TERM | left; exact Npos | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1 a2.

zs. br K1.
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. br K2. clear FLC.
zs. zs. zs. zs.
ileave. eapply implM_bind.
{ eapply out_callq; try exact HS; try exact ST; try exact MI.
- rewrite Hlit, zb_firstn. unfold sfx. rewrite zb_skipn. replace (A + i)%Z with (A + Z.of_nat (Z.to_nat i))%Z by lia. apply bytes_at_sub; [exact BY | zl].
- rewrite Hlit. unfold sfx. apply Forall_sub. exact HF.
- unfold n, zlength. reflexivity.
- unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
- lia. - zl. - zl. - zl. - zl. - unfold INT_MAX in *; zl. - solve_szone.
-  first [zl | unfold zlength in *; lia]. }
cbv beta. intros [] st'. post_call asegs m. rename MI0 into MI.
ienter. replace (ret_pc (Z_to_bv 64 867156)) with (Z_to_bv 64 867156) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
zs. zs. br K3.

rewrite <- Es1. rewrite <- Es1 in FPC.
stmt IH as NXH.
jumpM (eapply NXH with (i := (i + n)%Z) (cnt := (cnt + l)%Z) (l := n) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
-
assert (En0 : n = 0%Z) by lia. rewrite En0 in *.
assert (C37 : znth fmt i = 37%Z).
{ destruct TERM as [E0 | [E37 _]]; rewrite Z.add_0_r in *; [|exact E37]. exfalso. apply C0. rewrite Ec. exact E0. }
replace (i + 0 + 1)%Z with (i + 1)%Z in Es2 by lia.
destruct (parse_dir s2) as [[d s3]|] eqn:PD; [|apply implM_unr].
destruct args as [|a args']; [apply implM_unr|].
ienter.
zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
jump (eapply NXS with (i := i) (n := 0%Z) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | intros j Hj; lia | rewrite !Z.add_0_r in TERM |- *; exact TERM | right; exact C37 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1 a2.

zs. br K1.
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. br K2. clear FLC.
zs. zs. zs. zs.
ileave. eapply implM_bind.
{ eapply out_callq; try exact HS; try exact ST; try exact MI.
- apply bytes_at_nil; zl.
- constructor.
- reflexivity.
- unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
- lia. - zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; lia. - solve_szone.
-  change (zlength (@nil Z)) with 0%Z; first [zl | lia]. }
cbv beta. intros [] st'. post_call asegs m. rename MI0 into MI.
ienter. replace (ret_pc (Z_to_bv 64 867156)) with (Z_to_bv 64 867156) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
zs. zs. br K3.

stmt HS_DIR as NXD.
jump (eapply NXD with (i := i) (d := d) (rest := s3)); [mk_finv | unfold lo_cells, ssp_guard; exact LOW | lia | zl | rewrite <- Es2; exact PD | ].
intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp. subst s3.

stmt (HS_CONV fuel IH) as NXC.
jumpM (eapply NXC with (i4 := k4) (k := k) (c := (cnt + l)%Z) (d := d) (a := a) (args := args'));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK
| | | exact FRM | exact FOK | lia | exact Ht | | lia | exact Hw | exact Hp | exact (parse_dir_xp _ _ _ PD) | unfold INT_MAX; lia ].
+ destruct a; try exact I. exact (Forall_inv FPC).
+ destruct a; try exact FPC. exact (Forall_inv_tail FPC).
+ exact (parse_dir_conv_type _ _ _ PD).
Qed.

Set Keyed Unification.
Hypothesis HS_INTC2 : S_INTC2.

Lemma L_INTC : S_INTC.
Proof using HS_INTC2 BAND.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp argi prefix body BA PFXA s2s za plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BEND BLEN HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hargi.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
stmt (HS_INTC2 fuel HH) as NX.
unfold conv_int.
ienter.
destruct XP as [[-> ->] | [-> Hp]]; cbn [Z.b2z].
-
replace (false && (-1 <? 0))%bool with false by reflexivity.
zs. zs. rewrite Z.land_0_l. zs. if_lit. zs. if_lit.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := (-1)%Z) (argi := argi) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG | zl | zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia | lia ].
-
replace (true && (p <? 0))%bool with false by (cbn; symmetry; apply Z.ltb_ge; lia).
zs. zs.
replace (Z.lxor p 9223372036854775808 <? 9223372036854775808)%Z with false
by (symmetry; apply Z.ltb_ge; change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; lia).
cbn [Z.b2z Z.land]. zs. if_lit. zs. if_lit. zs. zs.
pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB.
rewrite (nzmask_eq fl) in FLB |- * by lia.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := p) (argi := argi) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG | zl | zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia | lia ].
Qed.

Set Keyed Unification.

Lemma L_INTC2 : S_INTC2.
Proof using GLO HAP HS_TAIL LO QHI SEP_B SEP_F BAND.
intros fuel HH x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p argi prefix body BA PFXA s2s za plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BEND BLEN HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hp Hc Hargi.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (zb_length body) as LB.
set (n := Z.of_nat (length body)) in *.
stmt (HS_TAIL fuel HH) as NX.
ienter.
zs. zs. brf K1.
-
replace (argi =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. rewrite ?if_false_Z, ?Z.add_0_r.
zs. zs. zs. zs. replace (argi <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite ?Z.add_0_r.
zs. brf K2; [ | zs ]; zs; zs.
all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := Z.max p n) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG
| unfold body_loc; split; [zl| solve_szone] | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
-
replace (argi =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb]. rewrite ?if_true_Z.
zs. brf K3.
+
assert (Hp0 : p <> 0%Z) by (intros E; apply K3; apply (proj2 (landM64_zero p ltac:(lia))); exact E).
replace (p =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact Hp0).
zs. zs. zs. zs. replace (argi <? 1)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
zs. brf K2; [ | zs ]; zs; zs.
all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := Z.max p (n + 1)) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG
| unfold body_loc; split; [zl| solve_szone] | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
+
assert (Hp0 : p = 0%Z) by (apply (proj1 (landM64_zero p ltac:(lia))); exact K3).
replace (p =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact Hp0).
zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (prefix := prefix) (body := []) (BA := (q + -368)%Z) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| apply bytes_at_nil; lia | apply Forall_nil
| unfold body_loc; split; [zl| solve_szone] | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
Qed.

Set Keyed Unification.
Hypothesis HS_EXIT1 : S_EXIT1.

Lemma L_P1 : S_P1.
Proof using HF HS_DIR HS_EXIT1 HS_SCAN BAND.
intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 m pfx s2s za pl plp alo ahi j128 digs pad _
FI MU1 LOW DIG PAD P1.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
stmt HS_EXIT1 as NXE. stmt HS_SCAN as NXS. stmt HS_DIR as NXD.
unfold pass1_ok in P1. apply andb_true_iff in P1. destruct P1 as [LITB P1]. apply Z.leb_le in LITB. unfold INT_MAX in LITB.
pose proof (lit_run_sfx fmt 0 ltac:(lia)) as (Hn & Hs1 & LIT & Hlit). change (sfx 0) with fmt in Hn, Hs1, LIT, Hlit.
cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
set (n := Z.of_nat (length (lit_run fmt))) in *.
rewrite Hs1 in P1. rewrite !Z.add_0_l in *.
destruct (sfx n) as [|c1 s2] eqn:Es1; [discriminate|].
destruct (sfx_cons_inv fmt n c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
pose proof (lit_run_stop fmt c1 s2 Hs1) as C1.
assert (TERM : (znth fmt n = 0 \/ (znth fmt n = 37 /\ n + 1 < Z.of_nat (length fmt) /\ znth fmt (n + 1) <> 37))%Z
/\ (znth fmt n <> 0%Z -> exists d rest, parse_dir (sfx (n + 1)) = Some (d, rest))).
{ rewrite <- Ec1. destruct (Z.eqb_spec c1 0) as [E0|E0]; [split; [left; exact E0 | intros X; exfalso; exact (X E0)]|].
destruct s2 as [|c2 s2q]; [discriminate|].
destruct (sfx_cons_inv fmt (n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
apply andb_true_iff in P1. destruct P1 as [P37 PD]. destruct (Z.eqb_spec c2 37) as [|N37]; [discriminate|].
split. { right. split; [lia|]. split; [unfold zlength in Hin1; exact Hin1|]. rewrite <- Ec2. exact N37. }
intros _. rewrite <- Es2. destruct (parse_dir (c2 :: s2q)) as [[d rest]|]; [|discriminate]. exists d, rest. reflexivity. }
destruct TERM as [TERM PDX].

zs. zs. zs. br K. zs. rd_fmt 0%Z. rewrite Z.add_0_r in RD. zs. fix_u8 0%Z. zs. fixr. zs. brf K0.
-
assert (n = 0)%Z as N0. { destruct (Z.eq_dec n 0); [assumption|]. exfalso. destruct (LIT 0%Z ltac:(lia)) as [X _]. apply X. exact K0. }
zs. if_lit. zs. zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
-
jump (eapply NXS with (i := 0%Z) (n := n) (cnt' := 0%Z);
[ exact FI' | lia | lia | zl | intros j Hj; rewrite Z.add_0_l; apply LIT; exact Hj | rewrite Z.add_0_l; exact TERM
| destruct (Z.lt_ge_cases 0 n); [left; assumption | right; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); destruct C1 as [C1|C1]; [exfalso; apply K0; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); exact C1 | exact C1]]
| unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1 a2. rewrite !Z.add_0_r.
zs. if_lit. zs. brf K1.
+
assert (N0 : n = 0%Z) by lia.
destruct C1 as [C1|C1]; [exfalso; apply K0; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); exact C1|].
destruct (PDX ltac:(rewrite <- Ec1, C1; lia)) as (d & rest & PD).
rewrite N0 in PD.
jump (eapply NXD with (i := 0%Z) (d := d) (rest := rest); [exact FI' | exact LOW' | lia | zl | exact PD | ]).
intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp.
zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
+
zs. zs. zs. br K2. zs. rd_fmt n. zs. fix_u8 n. zs. fixr. zs. brf K3.
*
zs. if_lit. zs. zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
*
destruct C1 as [C1|C1]; [exfalso; apply K3; rewrite <- Ec1, C1; reflexivity|].
destruct (PDX K3) as (d & rest & PD).
jump (eapply NXS with (i := n) (n := 0%Z) (cnt' := n);
[ exact FI' | lia | lia | zl | intros j Hj; exfalso; lia | rewrite Z.add_0_r; exact TERM
| right; rewrite <- Ec1; exact C1 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1' a2''. rewrite !Z.add_0_r.
zs. if_lit. zs. if_lit.
jump (eapply NXD with (i := n) (d := d) (rest := rest); [exact FI' | exact LOW' | lia | zl | exact PD | ]).
intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp.
zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
Qed.

Set Keyed Unification.

Lemma L_PLOOP : S_PLOOP.
Proof using HF BAND.
intros x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 Ft fc m Q pos acc p s3 pfx s2s za pl plp alo ahi j128 _
FI LOW Hpos Hacc DG G NE HK.
remember (Z.to_nat (zlength fmt - pos)) as kk eqn:Hkk.
revert pos acc x13 x14 x15 Hpos Hacc DG G HK Hkk.
induction kk as [|kk IH]; intros; [unfold zlength in *; exfalso; lia|].
pose proof FI as FI'. dest_finv FI. unfold lo_cells, ssp_guard in LOW.
pose proof (proj1 (digit_range _) DG) as DGR.
rewrite (sfx_cons fmt pos) in G by zl. rewrite (getint_cons_digit _ _ _ DG) in G.
destruct (214748364 <? acc) eqn:OV1; [discriminate|]. destruct (INT_MAX - 10 * acc <? znth fmt pos - 48) eqn:OV2; [discriminate|]. cbn [orb] in G.
apply Z.ltb_ge in OV1. apply Z.ltb_ge in OV2. unfold INT_MAX in OV2.
assert (Hnx : (pos + 1 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (pos + 1) (zlength fmt)) as [|Hge]; [assumption|]. exfalso.
rewrite sfx_nil in G by lia. cbn in G. injection G as _ <-. apply NE. reflexivity. }
zs. zs. br K.
zs. try rewrite (swrap32_small (acc * 10)) by lia.
zs. rewrite Z.add_0_r, (swrap32_small (znth fmt pos + -48)) by lia.
zs. try rewrite (lxor_imax (acc * 10)) by lia.
zs. try rewrite (proj2 (Z.ltb_ge (2147483647 - acc * 10) (znth fmt pos + -48))) by lia. cbn [Z.b2z].
zs. try rewrite (swrap32_small (acc * 10 + (znth fmt pos + -48))) by lia.
zs. try change (bv_swrap 32 (0 - 0)) with 0%Z.
zs. try rewrite Z.lor_0_l.
rd_fmt (pos + 1)%Z. zs. fix_u8 (pos + 1)%Z. zs. zs. zs. zs. brf K2.
-
assert (ND : is_digit (znth fmt (pos + 1)) = false).
{ destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
rewrite (sfx_cons fmt (pos + 1)) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G.
injection G as Ew Es2.
zs. zs. zs. zs.
jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
- assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
intros k3 a1' a3' a4' Hk3 Hs3 Hnd Hp. apply HK; try assumption. zl.
Qed.

Lemma L_PREC : S_PLOOP -> S_PREC.
Proof using HF BAND.
intros HPL x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k2 k3 p xp pfx s2s za pl plp alo ahi j128 _
FI LOW Hk2 PX HK.
pose proof FI as FI'. dest_finv FI.
rd_fmt k2. zs. fix_u8 k2. zs. zs.
destruct PX as [(N46 & Hp & Hxp & Hk3) | (E46 & Hxp & Hk21 & N42 & G & Hk3)].
- br K. subst p xp k3. do 6 zs. jump (apply HK; unfold INT_MAX; lia).
- br K. rd_fmt (k2 + 1)%Z. zs. fix_u8 (k2 + 1)%Z. zs. zs. br K1.
subst xp. zsto 0xd3da4%Z.
pose proof (fmt_rng (k2 + 1) ltac:(zl)) as RG3.
zs. brf K3.
+
assert (ND : is_digit (znth fmt (k2 + 1)) = false).
{ destruct (is_digit (znth fmt (k2 + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG3)) in E. lia. }
rewrite (sfx_cons fmt (k2 + 1)) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G.
injection G as Ep Es. subst p.
assert (k3 = k2 + 1)%Z.
{ pose proof (sfx_length fmt k3 ltac:(zl)) as L1. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)) as L2.
rewrite (sfx_cons fmt (k2 + 1)) in L2 by zl. rewrite Es in L2. lia. }
subst k3. zs. zs. zs. jump (apply HK; unfold INT_MAX; lia).
+ assert (D3 : is_digit (znth fmt (k2 + 1)) = true) by (apply (proj1 (digit_test _ RG3)); lia).
zs. zs.
stmt HPL as NXL. jump (eapply NXL with (pos := (k2 + 1)%Z) (acc := 0%Z); [exact FI' | exact LOW | zl | lia | exact D3 | exact G | | ]).
{ intros E. pose proof (sfx_length fmt k3 ltac:(zl)) as L. rewrite E in L. change (zlength (@nil Z)) with 0%Z in L. zl. }
intros k3' a1' a3' a4' Hk3' Hs3 Hnd Hp.
assert (k3' = k3)%Z.
{ pose proof (sfx_length fmt k3 ltac:(zl)) as L1. pose proof (sfx_length fmt k3' ltac:(zl)) as L2. rewrite <- Hs3 in L2. lia. }
subst k3'. apply HK. lia.
Qed.

Unset Keyed Unification.

Lemma L_PRO : S_PRO.
Proof using BS0 GLO HA HAP HVA LO QHI SEP_F BAND.
intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f Q _ ST0 MI0 BY0 VAA0 SSP0 Hf CONT.
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO. unfold zlength in *.
destruct SSP0 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. fix_rsegs.
pose proof (zb_length fmt) as LZB. pose proof (u64s_length slots) as LU. unfold va_area in VAA0.
pose proof (munch_refl [(q + -544, q)]%Z m0) as MU. pose proof (wmono_refl asegs m0) as WM.
pose proof ST0 as ST.
carve_frame 544%nat ST.

apply (rw_cells_split_CB asegs _ _ [] 544 _ [] [40;8;8;8;8;8;8;8;8;8;320;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
do 43 zs.

lazymatch type of FR with rw_cells _ _ _ (CB 40 ?ja :: _) => set (jA := ja) in FR; clearbody jA end.
lazymatch type of FR with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: CB 320 ?jb :: _) => set (jB := jb) in FR; clearbody jB end.
apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [LOWa FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
replace (q + -544 + Z.of_nat 432)%Z with (q + -112)%Z in FRhi by lia.
apply (rw_cells_split_CB asegs _ _ [_;_;_;_;_;_;_;_;_;_] 320 _ [] [16; 24; 24; 256]%nat) in LOWa; [ | cbn; lia ].
cbn [mk_CB_cells app] in LOWa.
apply (rw_cells_split_CB asegs _ _ [] 40 _ _ [8; 8; 8; 8; 8]%nat) in LOWa; [ | cbn; lia ].
cbn [mk_CB_cells app] in LOWa.
apply (rw_cells_split_CB asegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] 16 _ _ [8; 8]%nat) in LOWa; [ | cbn; lia ].
cbn [mk_CB_cells app] in LOWa.
do 7 c8ify LOWa.
apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in LOWa. destruct LOWa as [LOW DP]. cbn [cells_size csize Nat.add app] in DP.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DP. destruct DP as [DIG PAD]. cbn [cells_size csize Nat.add app] in PAD.
replace (q + -544 + Z.of_nat 152)%Z with (q + -392)%Z in DIG by lia.
replace (q + -544 + Z.of_nat 152 + Z.of_nat 24)%Z with (q + -368)%Z in PAD by lia.
eapply CONT; [ | exact MU | exact LOW | exact DIG | exact PAD ].
unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area.
split; [assumption|]. split; [eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|].
split; [exact FRhi|]. split; [exact ST|]. split; [exact BY0|]. split; [exact VAA0|]. split; [exact SSP1|exact SSP2].
Qed.

Set Keyed Unification.

Lemma L_LOOP1 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i n : Z) (Q : machine_state -> Prop) (k : nat) (j : Z),
finv m ->
k = Z.to_nat (n - j) -> (0 <= j)%Z -> (j < n \/ (j = n /\ znth fmt (i + n) = 37))%Z ->
(0 <= i)%Z -> (i + n < zlength fmt)%Z ->
(forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z ->
(znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z ->

(forall a0, evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (if (znth fmt (i + n) =? 0)%Z then 0xd3af0 else 0xd3af8)) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt (i + j))) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (A + i + j)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3ae0) fc None m (seg_rom asegs)).
Proof using HF BAND.
intros until k. induction k as [|k IH]; intros j FI Hk Hj Hjn Hi Hin LIT TERM HK.
-
assert (j = n) by lia. subst j. destruct Hjn as [|[_ T37]]; [lia|].
dest_finv FI. unfold INT_MAX in *.
zs. rewrite T37. if_lit. specialize (HK (Z_to_bv 64 37)). rewrite T37, (proj2 (Z.eqb_neq 37 0)) in HK by lia. exact HK.
- destruct Hjn as [Hjn|[Hjn _]]; [|exfalso; lia].
pose proof (LIT j ltac:(lia)) as [NZ N37].
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
pose proof (fmt_rng (i + j) ltac:(unfold zlength in *; lia)) as RG0.
zs. br K.
rd_fmt (i + j + 1)%Z. zs. fix_u8 (i + j + 1)%Z. zs. zs.
destruct (Z.lt_ge_cases (j + 1) n) as [Hlt|Hge].
+
pose proof (LIT (j + 1)%Z ltac:(lia)) as [NZ1 _]. replace (i + j + 1)%Z with (i + (j + 1))%Z in * by lia.
br K1. replace (A + i + j + 1)%Z with (A + i + (j + 1))%Z by lia.
eapply (IH (j + 1)%Z FI'); try lia; try assumption.
+ assert (j + 1 = n)%Z by lia. replace (i + j + 1)%Z with (i + n)%Z in * by lia.
replace (A + i + j + 1)%Z with (A + i + n)%Z by lia.
destruct TERM as [T0 | (T37 & Hn1 & T1)].
* rewrite T0. if_lit. specialize (HK (Z_to_bv 64 0)). rewrite T0, Z.eqb_refl in HK. exact HK.
* br K1. eapply (IH n FI'); try lia; try assumption.
Qed.

Lemma L_SCAN : S_SCAN.
Proof using A0 HA HF BAND.
intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m i n cnt' Q _
FI Hi Hn Hin LIT TERM Hnz Hc Hnc HK.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
assert (NZ0 : znth fmt i <> 0%Z).
{ destruct Hnz as [Hp|H37]; [|rewrite H37; lia]. pose proof (LIT 0%Z ltac:(lia)) as [X _]. rewrite Z.add_0_r in X. exact X. }
pose proof (fmt_rng i ltac:(unfold zlength in *; lia)) as RGi.
zs. zs. br K.
eapply evt_eq; [ | eapply L_LOOP1 with (i := i) (n := n) (k := Z.to_nat (n - 0)) (j := 0%Z); try exact FI'; try lia; try assumption ].
{ cbv delta [mkR]. rewrite !Z.add_0_r. reflexivity. }
{ destruct Hnz as [Hp|H37]; [left; lia|]. destruct (Z.lt_ge_cases 0 n); [left; lia|]. right. split; [lia|]. replace (i + n)%Z with i by lia. exact H37. }
intros a0.

assert (TL : forall a1 a2, evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd3b24) fc None m (seg_rom asegs))).
{ intros a1 a2. zs. first [progress replace (A + i + n + - (A + i))%Z with n by lia | progress replace (A + i + n - (A + i))%Z with n by lia]. zs. fixr. zs. br K1. zs. fixr. apply HK. }
destruct TERM as [T0 | (T37 & Hn1 & T1)].
- rewrite T0, Z.eqb_refl. zs. zs. apply TL.
- rewrite T37. cbn [Z.eqb Pos.eqb]. zs. zs. rd_fmt (i + n + 1)%Z. zs. fix_u8 (i + n + 1)%Z. zs. br K1. zs. apply TL.
Qed.

Set Keyed Unification.

Lemma L_STATE : S_STATE.
Proof using HF BAND.
intros x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k3 ty _ FI Hk3 CT HK.
pose proof FI as FI'. dest_finv FI.
pose proof (conv_type_range _ _ CT) as TR. pose proof (conv_type_ty _ _ CT) as TY.
zs. zs. rd_fmt k3. zs. fix_u8 k3. zs. zs. brf K.
{ exfalso. rewrite land_M64_neg in K by lia. lia. }
clear K. zs. zs. zs. zs. zs. zs.
pose proof (states0_read m _ _ MI CT) as RD2. zs. cbv beta. rewrite (u8_lit ty) by lia.
zs. zs. zs. brf K2. { exfalso. try rewrite land_M64_id in K2 by lia. lia. }
clear K2. zs. zs. brf K3. { exfalso. try rewrite land_M64_id in K3 by lia. lia. }
clear K3. zs. brf K4. { exfalso. try rewrite land_M64_id in K4 by lia. lia. }
clear K4. zs. br K5.
jump (apply HK).
Qed.

Unset Keyed Unification.
Hypothesis HS_T2 : S_T2.

Lemma L_T1 : S_T1.
Proof using BS0 GLO HA HAP HOUT HS_T2 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ BAND.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw Hfl0.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad at 1. unfold LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
replace (Z.land fl 73728 =? 0)%Z with true by (rewrite Hfl0; reflexivity). cbn [negb orb].
ienter. zs. zs. brf K2.
-
rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt (HS_T2 fuel HH) as NX2.
jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (wq - (pl + pq))%Z) in *.
zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
zs. zs.
apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. destruct (SFL _ _ HS) as (fb0 & FLC0 & FB0 & ISH0). clear FLC0 FB0.
callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia
| match goal with H : stk _ _ lo _ |- _ => exact H end
| idtac; glo_lia | unfold MEMSET_ICPT_STACK; glo_lia | glo_lia
| exact (proj2 (proj2 ISH0)) | exact (proj1 (proj2 ISH0))
| apply (rng_ok_of_ash _ _ _ (proj1 ISH0)); [unfold szone; right; idtac; glo_lia| lia] ]).
clear fb0 ISH0.
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 32 256) in PADa by lia.
zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
out_call.
1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
1:{ lia. } 1:{ lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells asegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
end.
stmt (HS_T2 fuel HH) as NX2.
jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Set Keyed Unification.
Hypothesis HS_T3 : S_T3.

Lemma L_T2 : S_T2.
Proof using BS0 GLO HA HAP HOUT HS_T3 HVA LO QHI SEP_B SEP_F SFL TOK TQ BAND.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
ienter.
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
out_call.
1:{ apply HPFX. exact MI. }
1:{ exact PRNG. }
1:{ rewrite Hpl. reflexivity. }
1:{ lia. } 1:{ lia. } 1:{ zl. } 1:{ zl. } 1:{ zl. } 1:{ zl. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
stmt (HS_T3 fuel HH) as NX3.
jumpM (eapply NX3 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Set Keyed Unification.
Hypothesis HS_T4 : S_T4.

Lemma L_T3 : S_T3.
Proof using BS0 GLO HA HAP HOUT HS_T4 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ BAND.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad at 1. unfold LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z. rewrite (pad_test_xor fl 65536) by reflexivity.
ienter. zs. zs. brf K1.
-
rewrite (proj2 (Z.eqb_neq _ _) K1). cbn [negb orb].
stmt (HS_T4 fuel HH) as NX4.
jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite K1, Z.eqb_refl. cbn [negb orb].
zs. zs. brf K2.
+ rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt (HS_T4 fuel HH) as NX4.
jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
+ rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (wq - (pl + pq))%Z) in *.
zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
zs. zs.
apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. destruct (SFL _ _ HS) as (fb0 & FLC0 & FB0 & ISH0). clear FLC0 FB0.
callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia
| match goal with H : stk _ _ lo _ |- _ => exact H end
| idtac; glo_lia | unfold MEMSET_ICPT_STACK; glo_lia | glo_lia
| exact (proj2 (proj2 ISH0)) | exact (proj1 (proj2 ISH0))
| apply (rng_ok_of_ash _ _ _ (proj1 ISH0)); [unfold szone; right; idtac; glo_lia| lia] ]).
clear fb0 ISH0.
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 48 256) in PADa by lia.
zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
out_call.
1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
1:{ lia. } 1:{ lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells asegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
end.
stmt (HS_T4 fuel HH) as NX4.
jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Unset Keyed Unification.
Hypothesis HS_T5 : S_T5.

Lemma L_T4 : S_T4.
Proof using BS0 GLO HA HAP HOUT HS_T5 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ BAND.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad at 1. change (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z with true. cbn [negb orb].
ienter.
pose proof (c8_read4 _ _ [C8 (Z_to_bv 64 PFXA); C8 (Z_to_bv 64 (Z.land fl 73728))] (Z_to_bv 64 n) _ _ LOW eq_refl) as RD4. cbn [cells_size csize Nat.add] in RD4.
zs. rewrite (sx32_lit n) by (first [ clear - LP LB LU LZB HnI body prefix pl n pq w slots fmt BAND; lia | lia ]). zs. brf K2.
-
rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt (HS_T5 fuel HH) as NX5.
jumpM (eapply NX5 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (pq - n)) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (pq - n)%Z) in *.
zs. zs. zs. try rewrite (swrap32_small (pq - n)) by (first [ clear - LP LB LU LZB Hcw Hwq Hc Hplp Hnp Hpl Hn body prefix pl n pq wq w c slots fmt BAND; lia | lia ]). fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; (first [ clear - K3 N256 n4 LP LB LU LZB body prefix pl n pq w slots fmt BAND; lia | lia ])].
zs. zs.
apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; (first [ clear - K3 n4 LP LB LU LZB body prefix pl n pq w slots fmt BAND; lia | lia ]) ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. destruct (SFL _ _ HS) as (fb0 & FLC0 & FB0 & ISH0). clear FLC0 FB0.
callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia
| match goal with H : stk _ _ lo _ |- _ => exact H end
| idtac; glo_lia | unfold MEMSET_ICPT_STACK; glo_lia | glo_lia
| exact (proj2 (proj2 ISH0)) | exact (proj1 (proj2 ISH0))
| apply (rng_ok_of_ash _ _ _ (proj1 ISH0)); [unfold szone; right; idtac; glo_lia| lia] ]).
clear fb0 ISH0.
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 48 256) in PADa by lia.
zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
out_call.
1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
1:{ lia. } 1:{ lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. (first [ clear - K4 LP LB LU LZB Hn n4 body prefix pl n pq w BS0 HAP SEP_B SEP_F GLO LO slots VA AP fmt lo q BS B Fp BAND; lia | lia ]). }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. (first [ clear - K4 LP LB LU LZB Hn n4 body prefix pl n pq w BS0 HAP SEP_B SEP_F GLO LO slots VA AP fmt lo q BS B Fp BAND; lia | lia ]). }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.

match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells asegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by (first [ clear - K4 LP LB LU LZB n4 body prefix pl n pq w slots fmt BAND; lia | lia ]); clear Ha Hb ]
end.
stmt (HS_T5 fuel HH) as NX5.
jumpM (eapply NX5 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Set Keyed Unification.
Hypothesis HS_T6 : S_T6.

Lemma L_T5 : S_T5.
Proof using BS0 GLO HA HAP HOUT HS_T6 HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI BAND.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
ienter.
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
out_call.
1:{ exact BODY. }
1:{ exact BRNG. }
1:{ rewrite Hn. reflexivity. }
1:{ lia. } 1:{ lia. } 1:{ zl. } 1:{ zl. } 1:{ zl. } 1:{ zl. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
stmt (HS_T6 fuel HH) as NX6.
jumpM (eapply NX6 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Set Keyed Unification.

Lemma L_T6 : S_T6.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ BAND.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z. rewrite (pad_test_xor fl 8192) by reflexivity.
ienter. zs. zs. brf K1.
-
rewrite (proj2 (Z.eqb_neq _ _) K1). cbn [negb orb].
stmt HH as NXH.
jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite K1, Z.eqb_refl. cbn [negb orb].
zs. zs. brf K2.
+
rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt HH as NXH.
jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
+ rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (wq - (pl + pq))%Z) in *.
zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
zs. zs.

apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. destruct (SFL _ _ HS) as (fb0 & FLC0 & FB0 & ISH0). clear FLC0 FB0.
callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia
| match goal with H : stk _ _ lo _ |- _ => exact H end
| idtac; glo_lia | unfold MEMSET_ICPT_STACK; glo_lia | glo_lia
| exact (proj2 (proj2 ISH0)) | exact (proj1 (proj2 ISH0))
| apply (rng_ok_of_ash _ _ _ (proj1 ISH0)); [unfold szone; right; idtac; glo_lia| lia] ]).
clear fb0 ISH0.
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 32 256) in PADa by lia.
zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
out_call.
1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
1:{ lia. } 1:{ lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
lazymatch goal with |- forall _ _ _, _ -> _ => idtac end.
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
zs.

match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells asegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
end.
stmt HH as NXH.
jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
match goal with H : SINK _ _ |- _ => exact H end.
Qed.

Unset Keyed Unification.
Hypothesis HS_T1 : S_T1.

Lemma conv_tail_k : forall (a1 a2 a3 a4 a5 a6 : M St unit) (v : Z) (k : Z -> M St Z) s Q ms,
implM asegs (a1 ;;; a2 ;;; a3 ;;; a4 ;;; a5 ;;; a6 ;;; k v) s Q ms ->
implM asegs (x <- (a1 ;;; a2 ;;; a3 ;;; a4 ;;; a5 ;;; a6 ;;; mret v) ;; k x) s Q ms.
Proof using .
clear. intros a1 a2 a3 a4 a5 a6 v k s Q ms H.
Ltac kstep H := apply implM_assoc; eapply implM_bind_ext; [ | exact H ]; cbv beta;
let x := fresh "x" in let s' := fresh "s'" in let ms' := fresh "ms'" in let H' := fresh "H" in
intros x s' ms' H'.
kstep H. kstep H0. kstep H1. kstep H2. kstep H3. kstep H4. apply implM_ret_l. exact H5.
Qed.

Lemma L_TAIL : S_TAIL.
Proof using BS0 GLO HA HAP HS_T1 HS_T2 HVA LO QHI SEP_B SEP_F SFR VAHI BAND.
intros fuel HH x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p prefix body BA PFXA s2s za plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BLOC BHI BIM HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hp Hc.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW. unfold body_loc in BLOC.
pose proof (bytes_at_bound _ _ _ _ BODY) as BB. pose proof (zb_length body) as LB. rewrite LB in BB.
set (n := Z.of_nat (length body)) in *. set (pl := Z.of_nat (length prefix)) in *.
unfold conv_tail. unfold zlength. fold n. fold pl. cbv zeta.
ienter.
zs. rewrite (sextw_small p) by lia. zs. replace (BA + n - BA)%Z with n by lia. zs. zs. zs.

lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if _ then Z_to_bv 64 ?pcj else _) ?fc ?rv ?m ?ro) =>
let pk := eval vm_compute in (bv_key (Z_to_bv 5 11)) in
let R' := eval cbv beta iota delta [tset] in (tset pk (Z_to_bv 64 (Z.max p n)) R) in
apply (evt_cut segs (fun ms' : machine_state => ms' = MS R' F (Z_to_bv 64 pcj) fc rv m ro) Q)
end.
{ brf K1; [ apply evt_done; first [ rewrite (Z.max_r p n) by lia | rewrite (Z.max_l p n) by lia ]; reflexivity
| zs; apply evt_done; first [ rewrite (Z.max_l p n) by (first [ clear - K1 LB LU LZB n body prefix p slots fmt BAND; lia | lia ]) | rewrite (Z.max_r p n) by lia ]; reflexivity ]. }
intros ms' ->.

all: zs; try rewrite (sextw_small p) by lia; fixr; zs; zs; fixr; zs; brf K2;
[ replace (INT_MAX - pl <? Z.max p n)%Z with true by (symmetry; apply Z.ltb_lt; unfold INT_MAX; lia); ileave; apply implM_unr_l
| replace (INT_MAX - pl <? Z.max p n)%Z with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia) ].

all: zs; zs; zs; fixr; zs; zs; zs.

lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if _ then Z_to_bv 64 ?pcj else _) ?fc ?rv ?m ?ro) =>
let pk := eval vm_compute in (bv_key (Z_to_bv 5 26)) in
let R' := eval cbv beta iota delta [tset] in (tset pk (Z_to_bv 64 (Z.max w (pl + Z.max p n))) R) in
apply (evt_cut segs (fun ms' : machine_state => ms' = MS R' F (Z_to_bv 64 pcj) fc rv m ro) Q)
end.
{ brf K3; [ apply evt_done; first [ rewrite (Z.max_r w (pl + Z.max p n)) by lia | rewrite (Z.max_l w (pl + Z.max p n)) by lia ]; reflexivity
| zs; apply evt_done; first [ rewrite (Z.max_l w (pl + Z.max p n)) by lia | rewrite (Z.max_r w (pl + Z.max p n)) by lia ]; reflexivity ]. }
intros ms' ->.

all: zs; brf K4;
[ replace (INT_MAX - c <? Z.max w (pl + Z.max p n))%Z with true by (symmetry; apply Z.ltb_lt; unfold INT_MAX; lia); ileave; apply implM_unr_l
| replace (INT_MAX - c <? Z.max w (pl + Z.max p n))%Z with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia) ].

all: zs; zs; zs; zs; brf K5.
all: ileave; apply conv_tail_k.
all: match goal with
| K : Z.land ?flv 73728 <> 0%Z |- _ =>
unfold mpad at 1; change (Z.lor LEFT_ADJ ZERO_PAD) with 73728%Z; rewrite (proj2 (Z.eqb_neq _ 0) K); cbn [negb orb]; apply implM_ret_l;
stmt (HS_T2 fuel HH) as NX2;
jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := Z.max w (pl + Z.max p n)) (pq := Z.max p n) (args := args)
(PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ]
| K : Z.land ?flv 73728 = 0%Z |- _ =>
stmt (HS_T1 fuel HH) as NX1;
jumpM (eapply NX1 with (k := k) (i4 := i4) (c := c) (w := w) (wq := Z.max w (pl + Z.max p n)) (pq := Z.max p n) (args := args)
(PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | (first [ clear - LB LU LZB Hw pl n body prefix p w slots fmt BAND; lia | lia ]) | lia | unfold INT_MAX; lia | exact K ]
end.
Qed.

Set Keyed Unification.

Lemma L_WLOOP : S_WLOOP.
Proof using HF BAND.
intros x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q pos acc w s2 pfx s2s za pl plp alo ahi j128 _
FI LOW Hpos Hacc DG G NE HK.
remember (Z.to_nat (zlength fmt - pos)) as kk eqn:Hkk.
revert pos acc x5 x6 x12 x14 x15 x16 x17 Hpos Hacc DG G HK Hkk.
induction kk as [|kk IH]; intros; [unfold zlength in *; exfalso; lia|].
pose proof FI as FI'. dest_finv FI. unfold lo_cells, ssp_guard in LOW.
pose proof (proj1 (digit_range _) DG) as DGR.
rewrite (sfx_cons fmt pos) in G by (unfold zlength in *; lia). rewrite (getint_cons_digit _ _ _ DG) in G.
destruct (214748364 <? acc) eqn:OV1; [discriminate|]. destruct (INT_MAX - 10 * acc <? znth fmt pos - 48) eqn:OV2; [discriminate|]. cbn [orb] in G.
apply Z.ltb_ge in OV1. apply Z.ltb_ge in OV2. unfold INT_MAX in OV2.

assert (Hnx : (pos + 1 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (pos + 1) (zlength fmt)) as [|Hge]; [assumption|]. exfalso.
rewrite sfx_nil in G by lia. cbn in G. injection G as _ <-. apply NE. reflexivity. }
zs. zs. br K.
zs. zs. try rewrite (swrap32_small (acc * 10)) by lia.
zs. rewrite Z.add_0_r, (swrap32_small (znth fmt pos + -48)) by lia.
rd_fmt (pos + 1)%Z. zs. fix_u8 (pos + 1)%Z.
zs. try rewrite (lxor_imax (acc * 10)) by lia.
zs. try rewrite (swrap32_small (acc * 10 + (znth fmt pos + -48))) by lia.
zs. try rewrite (proj2 (Z.ltb_ge (2147483647 - acc * 10) (znth fmt pos + -48))) by lia. cbn [Z.b2z].
zs. try change (bv_swrap 32 (0 - 0)) with 0%Z.
zs. zs. zs. try rewrite Z.lor_0_l. zs. zs. brf K2.
-
assert (ND : is_digit (znth fmt (pos + 1)) = false).
{ destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
rewrite (sfx_cons fmt (pos + 1)) in G by (unfold zlength in *; lia). rewrite (getint_cons_nondigit _ _ _ ND) in G.
injection G as Ew Es2.
zs. br K3.
jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
-
assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
Qed.

Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
Proof using HF BAND.
intros HWL x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k1 w s2 pfx s2s za pl plp alo ahi j128 _
FI LOW Hk1 G NE HK.
pose proof FI as FI'. dest_finv FI.
pose proof (fmt_rng k1 ltac:(zl)) as RG1.
zs. zs. zs. zs. brf K.
-
assert (ND : is_digit (znth fmt k1) = false).
{ destruct (is_digit (znth fmt k1)) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG1)) in E. lia. }
rewrite (sfx_cons fmt k1) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G. injection G as Ew Es2.
subst w. jump (apply (HK k1); [zl | | exact ND | unfold INT_MAX; lia]).
rewrite (sfx_cons fmt k1) by zl. symmetry. exact Es2.
- assert (DG : is_digit (znth fmt k1) = true) by (apply (proj1 (digit_test _ RG1)); lia).
zs. zs.
stmt HWL as NXL. jump (eapply NXL with (pos := k1) (acc := 0%Z); [exact FI' | exact LOW | zl | lia | exact DG | exact G | exact NE | ]).
intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
Qed.

Set Keyed Unification.

Lemma L_XLOOP : S_XLOOP.
Proof using GLO LO QHI BAND.
intros x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m l x.
remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x12 x13 x23 m.
induction nx as [nx IH] using lt_wf_ind.
intros x Enx x12 x13 x23 m j ds _ MI DIG Hx Hl Hj ->.
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (hex_digits_step l x ltac:(lia)) as DS.
pose proof (Z.div_pos x 16 ltac:(lia) ltac:(lia)) as Q0.
pose proof (Z.mod_pos_bound x 16 ltac:(lia)) as R0.
assert (Q1 : (x / 16 < 1152921504606846976)%Z) by (apply Z.div_lt_upper_bound; lia).
assert (LD : (1 <= zlength (hex_digits l x))%Z) by (rewrite DS; unfold zlength; rewrite length_app; cbn [length]; lia).
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
pose proof (hexchar_range 0 (x mod 16)%Z ltac:(lia) ltac:(lia)) as XR. rewrite Z.lor_0_r in XR.
pose proof (hexchar_range l (x mod 16)%Z Hl ltac:(lia)) as HR.
zs. zs. zs. zs.
replace (Z.land x 15) with (x mod 16)%Z in * by (change 15%Z with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity).
pose proof (xdigits_read _ (x mod 16)%Z MI ltac:(lia)) as RD.
zs. cbv beta. rewrite (u8_lit (znth XDIGITS (x mod 16))) by lia.
zs. replace (Z.shiftr x 4) with (x / 16)%Z by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
zs. try rewrite (land_W64_small (znth XDIGITS (x mod 16))) by lia.
set (c := Z.lor (znth XDIGITS (x mod 16)) l) in *.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA.
pose proof (u8arr_store_ok asegs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
pose proof (u8arr_write asegs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
zs. zs. brf K.
-
eapply evt_mono.
{ eapply (IH (Z.to_nat (x / 16)) ltac:(lia) (x / 16)%Z eq_refl) with (j := (j - 1)%Z); [ exact MI | exact DIG1 | lia | exact Hl | | f_equal; lia ].
rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
cbv beta. intros ms' P. destruct P as (a2' & a3' & m' & -> & MU' & WM' & MI' & DIG' & HW).
unfold xloop_post. exists a2', a3', m'. cbv zeta.
assert (EL : zlength (hex_digits l x) = (zlength (hex_digits l (x / 16)) + 1)%Z) by (rewrite DS; unfold zlength; rewrite length_app; cbn [length]; lia).
rewrite EL.
split; [ mseq | ].
split; [ eapply munch_trans; [exact MU | exact MU'] | ].
split; [ eapply wmono_trans; [exact WM | exact WM'] | ].
split; [ exact MI' | ].
split.
{ replace (firstn (Z.to_nat (j - (zlength (hex_digits l (x / 16)) + 1))) ds ++ zb (hex_digits l x) ++ skipn (Z.to_nat j) ds)
with (firstn (Z.to_nat (j - 1 - zlength (hex_digits l (x / 16)))) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)) ++ zb (hex_digits l (x / 16)) ++ skipn (Z.to_nat (j - 1)) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c))); [exact DIG'|].
rewrite upd_firstn_part by (rewrite LDS; unfold zlength in *; lia). rewrite upd_skipn_at by (rewrite LDS; lia).
replace (Z.to_nat (j - 1 - zlength (hex_digits l (x / 16)))) with (Z.to_nat (j - (zlength (hex_digits l (x / 16)) + 1))) by lia.
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia.
rewrite DS, zb_app, <- !app_assoc. reflexivity. }
unfold zlength in *. lia.
-
apply evt_done. unfold xloop_post. eexists _, _, _. cbv zeta.
assert (E0 : hex_digits l (x / 16) = []) by (replace (x / 16)%Z with 0%Z by lia; apply hex_digits_0).
assert (EL : zlength (hex_digits l x) = 1%Z) by (rewrite DS, E0; reflexivity).
rewrite EL.
split; [ mseq | ].
split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact MI | ].
split.
{ replace (firstn (Z.to_nat (j - 1)) ds ++ zb (hex_digits l x) ++ skipn (Z.to_nat j) ds) with (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)); [exact DIG1|].
rewrite upd_firstn_skipn by (rewrite LDS; lia). rewrite DS, E0. cbn [zb map app].
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. reflexivity. }
lia.
Qed.

End PrintfCore.

End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Qc6I QJFf QVsB QDM6.
Import QCiC.Mq1 Qpj5.Mq1 QdZp.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QTVW.Mq4 QnRU.Mq4 QteI.Mq1 Qu3b.Mq0 QQNJ.Mq1 QQNJ.Mq2.
Import QvG1.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Theorem stdio_write_flush_proof {BAND : Band} : stdio_write_flush_stmt.
Proof.
unfold stdio_write_flush_stmt. intros until canary. intros SINK -> -> ST LO GLO SPHI SEPB SSP MI A1B.
destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO & B47 & ISHm). cbn [fst] in FC, BUF, LEN.
unfold OUT_DEPTH, GLOBALS_TOP in *.
pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
apply bytes_at_app in BY as [BY _].
rewrite <- (Z_to_bv_bv_unsigned a1).
pose proof (bv_unsigned_in_range 64 a1) as RA1. unfold bv_modulus in RA1.
eapply implM_mono.
{ eapply (stdio_write_spec (St:=St)) with (B := B) (fd := 2) (Fp := 960096) (buf := buf) (s := []) (S := bv_unsigned a1) (lo := lo) (canary := canary)
(wend := B + 80) (bufsize := 80) (mode := mode) (lbf := 0xffffffff) (tail := tail) (flags := flags) (wfn := F_STDIO_WRITE);
try reflexivity; try lia.
- exact FC.
- exact BY.
- apply bytes_at_nil. unfold zlength; cbn [length]. lia.
- exact ST.
- unfold STDIO_WRITE_DEPTH. lia.
- exact SSP.
- exact MI.
- unfold got_ssp. lia.
- unfold ssp_guard. lia.
- unfold zlength in *; cbn [length]. lia.
- unfold zlength; cbn [length]. lia.
- left. reflexivity. }
cbv beta. intros [] st' ms' PO.
destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & FC' & SSP' & ->).
unfold STDIO_WRITE_DEPTH in MU.
unfold stdio_write_flush_post. do 16 eexists. split; [reflexivity|].
split. { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. unfold STDIO_WRITE_DEPTH in *. intros; lia. }
split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [| exact SSP'].

exists flags, mode, tail, (zb buf ++ rest). cbn [fst].
split. { rewrite Z.add_0_r. exact FC'. }
split; [exact FL32|]. split; [exact FL8|].
split.
{
eapply (rw_cells_transport _ _ m m'); [exact BUF | exact MU | exact WM |].
cbn. unfold zlength in *. lia. }
split; [| split; [exact BHI| split; [exact BGLO| split; [exact B47|]]]].
2:{ eapply ISH_munch_zone; [exact ISHm| exact MU| exact WM|]. unfold STDIO_WRITE_DEPTH. zforalls. }
unfold zlength in *. cbn [length]. rewrite length_app. unfold zb. rewrite length_map. lia.
Qed.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiqM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Qc6I QJFf QVsB QDM6 QiqM.
Import QCiC.Mq1 Qpj5.Mq1 QdZp.
Import QTVW.Mq4 QnRU.Mq4 QteI.Mq1 Qu3b.Mq0 QQNJ.Mq2.
Import QvG1.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Definition wfn_of (so : stdout_st) : Z := if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE.
Definition lbf_of (so : stdout_st) : Z := if so_lbf_nl so then 10 else 0xffffffff.
Definition stdout_cells (so : stdout_st) (flags mode : word) (tail : list byte) : list cell :=
file_cells flags (RSTDOUT_BUF + 1024) (RSTDOUT_BUF + zlength (so_buf so)) RSTDOUT_BUF (wfn_of so) RSTDOUT_BUF 1024 1 mode (lbf_of so) tail.

Definition STDOUT_WRITE_DEPTH : Z := 144.

Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).
Ltac exact_frm := lazymatch goal with |- frm0 ?f => first [is_evar f; fail 1 "exact_frm: evar" | assumption] end.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma rw_cells_recast : forall m A cs cs',
rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
rw_cells asegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma C4_low32 : forall (a b : word) , bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> cbytes (C4 a) = cbytes (C4 b).
Proof.
intros a b E. cbn [cbytes]. unfold le4.
rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia).
rewrite E. reflexivity.
Qed.
Lemma rw_cells_C4_eq : forall m A pre (a b : word) post,
bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 ->
rw_cells asegs m A (pre ++ C4 a :: post) -> rw_cells asegs m A (pre ++ C4 b :: post).
Proof.
intros m A pre a b post E H. eapply rw_cells_recast; [exact H| | |].
- destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [H1 H2]. split; [exact H1|]. exact H2.
- rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (C4_low32 a b E). reflexivity.
- rewrite !cells_size_app. reflexivity.
Qed.

Ltac fix_lbf FC :=
lazymatch type of FC with rw_cells ?sg ?m' ?A ?cs =>
lazymatch cs with ?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: C4 (Z_to_bv 64 (-1)) :: ?rest =>
apply (rw_cells_C4_eq m' A [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20]
(Z_to_bv 64 (-1)) (Z_to_bv 64 4294967295) rest ltac:(vm_compute; reflexivity)) in FC
end
end.

Lemma rw_cells_C4_CB4 : forall m A (v : word) cs,
rw_cells asegs m A (C4 v :: cs) -> rw_cells asegs m A (CB 4 (le4 v) :: cs).
Proof.
intros m A v cs [[W B] R]. split; [split|].
- cbn [cells_wf cell_wf] in *. split; [apply length_le4| exact (proj2 W)].
- exact B.
- exact R.
Qed.
Lemma firstn1_le4 : forall v : word, firstn 1 (skipn 0 (le4 v)) = le1 v.
Proof. intros v. reflexivity. Qed.

Lemma flags_byte_and64 : forall flags : word,
Z.land (bv_unsigned flags) 64 = 0 -> Z.land (bv_unsigned flags mod 256) 64 = 0.
Proof.
intros flags H. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
rewrite (Z.land_comm _ (Z.ones 8)), <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_ones by lia.
rewrite H. reflexivity.
Qed.

Lemma rw_cells_CB4_C4 : forall m A (v : word) cs,
rw_cells asegs m A (CB 4 (le4 v) :: cs) -> rw_cells asegs m A (C4 v :: cs).
Proof.
intros m A v cs [[W B] R]. split; [split|].
- cbn [cells_wf cell_wf] in *. split; [exact I| exact (proj2 W)].
- exact B.
- exact R.
Qed.

Section StdoutWrite.
Context {BAND : Band}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis get_set : forall s so, get_so (set_so so s) = so.
Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.

Definition so_after (so : stdout_st) : stdout_st :=
mkStdout true [] (if so_first so then false else so_lbf_nl so) false.

Definition stdout_writefn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(flags mode : word) (tail : list byte) (l : Z) (lo : Z) (canary : word) (m : mem) (st : St)
: unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - STDOUT_WRITE_DEPTH, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' RSTDOUT (stdout_cells (so_after (get_so st)) flags mode tail)
/\ ssp_cells m' canary
/\ st' = set_so (so_after (get_so st)) st.

Lemma stdout_writefn_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(flags mode : word) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
let so := get_so st in
so_active so = true ->
rw_cells asegs m RSTDOUT (stdout_cells so flags mode tail) ->
Z.land (bv_unsigned flags) 64 = 0 ->
bytes_at asegs m RSTDOUT_BUF (to_bytes (so_buf so)) -> (zlength (so_buf so) <= 1024) ->
bytes_at asegs m S (to_bytes s) ->
a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDOUT_WRITE_DEPTH) -> (band_lo <= lo) ->
ssp_cells m canary -> mem_inv asegs m ->
(zlength s <= 2^25) -> (0 <= S < 2^64) -> (S + zlength s <= 2^47) ->
(s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= RSTDOUT \/ RSTDOUT + 232 <= S))) ->
bv_unsigned sp <= 2^47 ->
implM asegs (stdout_writefn get_so set_so s) st
(stdout_writefn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags mode tail (zlength s) lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (wfn_of so)) fc None m (seg_rom asegs)).
Proof.
intros until canary. cbv zeta. intros ACT FC FL64 BUFB BUFL SRC -> -> -> ST LO GLO SSP MI LENS S0 Shi SEPS SPT.
pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, STDOUT_WRITE_DEPTH in *.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. unfold to_bytes in BS. rewrite length_map in BS.
assert (LSB : length (to_bytes s) = length s) by (unfold to_bytes; apply length_map).
unfold stdout_writefn. apply implM_rdso.
unfold stdout_cells, wfn_of, lbf_of in *.
destruct (so_first (get_so st)) eqn:FIRST.
-
apply implM_bind_assoc. apply implM_updso. apply implM_bind_assoc.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
apply implM_sysk.
change (bytes_at asegs m S (to_bytes s)) with (boxed (bytes_at asegs m S (to_bytes s))) in SRC.
change (bytes_at asegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st)))) with (boxed (bytes_at asegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st))))) in BUFB.
assert (LBB : length (to_bytes (so_buf (get_so st))) = length (so_buf (get_so st))) by (unfold to_bytes; apply length_map).
unfold file_cells in FC. apply rw_cells_C4_CB4 in FC.
carve_frame 32%nat ST.
do 9 step. rewrite ?firstn1_le4, ?zext_extract_le1. unfold zx8.
step. step. step. fix_lit_store. step.
if_cases Hsvb; zify_cond Hsvb. 1:{ exfalso. exact (Hsvb (flags_byte_and64 flags FL64)). }
do 10 step. step_ecall.
replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (symmetry; apply sx32_lit; lia).
split. { at_node_red; split_spine; try reflexivity; try lia. }
intros rsp ans Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec.
destruct ans as [e|v]. 2:{ exfalso. destruct Hdec as (_ & Hok & _). discriminate Hok. }
destruct Hdec as [-> He]. unfold efferr, eff0. cbv iota.
apply implM_updso.

unfold implM. apply impl_from_evt. sys_nret.
do 5 step.
if_cases He0; zify_cond He0. 1:{ exfalso. rewrite unsigned_errno_ret in He0 by lia. lia. }
step. step.
fix_lbf FC.
step. apply evt_done.
rewrite !get_set, !set_set. cbn [so_active so_buf so_first].
unfold stdout_stdio_write. apply (implM_rdso asegs get_so). rewrite get_set. cbn [so_buf].
apply rw_cells_CB4_C4 in FC.
eapply implM_bind.
{ eapply (stdio_write_spec (St:=St)) with (B := RSTDOUT_BUF) (fd := 1) (Fp := RSTDOUT) (buf := so_buf (get_so st)) (s := s) (S := S)
(lo := lo) (canary := canary) (wend := RSTDOUT_BUF + 1024) (bufsize := 1024) (mode := mode) (lbf := 0xffffffff) (tail := tail)
(flags := flags) (wfn := F_STDIO_WRITE); try reflexivity; rewrite ?unsigned_lit by lia.
all: first [ exact FC | exact ST | exact MI | exact BUFL | split; [exact GOT | exact GUARD]
| lia | unfold STDIO_WRITE_DEPTH; lia | unfold got_ssp; lia | unfold ssp_guard; lia
| unfold boxed in BUFB; apply (bytes_at_transport _ _ _ _ _ _ BUFB MU); cbn [disjoint_from]; rewrite LBB; unfold zlength in BUFL; lia
| destruct SEPS as [-> | [S1 S2]]; [left; reflexivity | right; split; lia]
| src_now SRC SEPS MU LSB ]. }
cbv beta. intros [] st' ms' PO.
destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
rewrite !unsigned_lit in MU2, ST2 by lia.
apply implM_upd. rewrite !get_set, !set_set. cbn [so_lbf_nl so_first].

replace (ret_pc (Z_to_bv 64 0xd373c)) with (Z_to_bv 64 0xd373c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
destruct SSP2 as [GOT2 GUARD2]. unfold got_ssp, ssp_guard in GOT2, GUARD2.
assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 canary; C8 s0; C8 ra]).
{ eapply (rw_cells_transport asegs _ _ m2); [exact FR | exact MU2 | exact WM2 | cbn; unfold STDIO_WRITE_DEPTH in *; lia]. }
step. step. step. if_false. step. step. step. step.
release_frame FR2 ST2 (bv_unsigned sp).
unfold stdout_writefn_post, so_after, stdout_cells, wfn_of, lbf_of, file_cells. rewrite FIRST. cbn [so_first so_buf so_lbf_nl].
sys_finish.
+ apply (munch_trans _ m m0 m2).
* eapply munch_weaken; [| exact MU]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
* eapply munch_weaken; [| exact MU2]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
+ eapply wmono_trans; [exact WM | exact WM2].
+ split; [exact GOT2 | exact GUARD2].
+ rewrite ?set_set. reflexivity.
-
apply (implM_retb asegs). unfold stdout_stdio_write. apply (implM_rdso asegs get_so).
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
assert (LBB : length (to_bytes (so_buf (get_so st))) = length (so_buf (get_so st))) by (unfold to_bytes; apply length_map).
eapply implM_bind.
{ eapply (stdio_write_spec (St:=St)) with (B := RSTDOUT_BUF) (fd := 1) (Fp := RSTDOUT) (buf := so_buf (get_so st)) (s := s) (S := S)
(lo := lo) (canary := canary) (wend := RSTDOUT_BUF + 1024) (bufsize := 1024) (mode := mode) (lbf := if so_lbf_nl (get_so st) then 10 else 4294967295) (tail := tail)
(flags := flags) (wfn := F_STDIO_WRITE); try reflexivity; rewrite ?unsigned_lit by lia.
all: try first [ exact FC | exact ST | exact MI | exact BUFL | exact BUFB | exact SRC | split; [exact GOT | exact GUARD]
| lia | unfold STDIO_WRITE_DEPTH in *; lia | unfold got_ssp; lia | unfold ssp_guard; lia ].
destruct SEPS as [-> | [S1 S2]]; [left; reflexivity | right; split; lia]. }
cbv beta. intros [] st' ms' PO.
destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
apply implM_upd. apply evt_done. rewrite ?get_set.
unfold stdout_writefn_post, so_after, stdout_cells, wfn_of, lbf_of, file_cells. rewrite FIRST. cbn [so_first so_buf so_lbf_nl].
sys_finish.
+ eapply munch_weaken; [| exact MU2]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
+ rewrite ?set_set. reflexivity.
Qed.
End StdoutWrite.
End Mq3.
From stdpp Require gmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QteI.Mq1 QQNJ.Mq3.
Import Q0z1.
Import QlES.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo AP S : Z) (str : list Z) (slack : list byte).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Hypothesis APC : rw_cells asegs m AP [C8 (wz S)].
Hypothesis APLO : bv_unsigned sp <= AP.

Hypothesis STR : bytes_at asegs m S (zb str ++ b8 0 :: slack).
Hypothesis BYT : Forall (fun c => 0 < c < 256) str.
Hypothesis SZ : szone S (zlength str + 1).
Hypothesis SLEN : zlength str + 1 <= 2^40.
Hypothesis SEP : S + zlength str + 1 + zlength slack <= lo \/ bv_unsigned sp <= S.

Definition MID (ms' : machine_state) : Prop :=
exists (m2 : word -> option byte) (junk1 junk2 : list byte) (x3 x4 : word),
ms' = MS (mkR (wz 0x536f0) (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp
(wz 0x1edef) (wz 0x146d9) x3 (wz 115) x4 (wz 0) a5 a6 a7
(wz 10) (wz 0x1edf1) (wz 0x15b57) (wz AP) (wz 0x1edf0)
(wz 9) (wz (bv_unsigned sp + -2184)) (wz 12297829382473034410)
(wz (-1)) (wz 37) t3 t4 t5 t6)
F (wz 0x536f0) fc None m2 (seg_rom asegs)
/\ rw_cells asegs m2 (bv_unsigned sp + -2240) [CB 8 junk1; C8 (wz (bv_unsigned sp + -120)); C8 a0]
/\ rw_cells asegs m2 (bv_unsigned sp + -2176)
[CB 2072 junk2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m2 (bv_unsigned sp + -2216)
[CB 8 (le8 (wz 0)); CB 8 (le8 (wz 18446744073709551615)); C8 (wz 0x1edef); C8 (wz 0x1edf1); C1 (b8 (bv_unsigned (wz 0)));
CB 3 (take 3 (drop 1 (le8 (wz 0)))); C1 (b8 (bv_unsigned (wz 115))); CB 3 (drop 4 (drop 1 (le8 (wz 0))))]
/\ mem_inv asegs m2
/\ rw_cells asegs m2 AP [C8 (wz S)]
/\ ro_cells asegs m2 0x1edde [C1 (b8 99); C1 (b8 108); C1 (b8 105); C1 (b8 58); C1 (b8 32); C1 (b8 99); C1 (b8 97); C1 (b8 110); C1 (b8 110); C1 (b8 111); C1 (b8 116); C1 (b8 32); C1 (b8 111); C1 (b8 112); C1 (b8 101); C1 (b8 110); C1 (b8 32); C1 (b8 37); C1 (b8 115); C1 (b8 10); C1 (b8 0)]
/\ stk asegs m2 lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m2
/\ wmono asegs m m2.

Lemma printf_common_cannot_open_head :
evt asegs MID
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x1edde)  (wz AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. idtac. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
pose proof (rw_cells_bound _ _ _ _ APC) as BAP. cbn in BAP.
assert (SNZ : 0 < S /\ S + (zlength str + 1) + 8 <= 2^47) by (unfold szone in SZ; idtac; lia).

set (BAh := bytes_at) in STR. change (boxed (szone S (zlength str + 1))) in SZ.
change (boxed (S + zlength str + 1 + zlength slack <= lo \/ bv_unsigned sp <= S)) in SEP.

pose_str FMT 0x1edde [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 37; 115; 10; 0] MI.
unfold pcommon_entry, zlength in *.

eapply evt_cut; [ eapply pc_setup with (c := 99) (l := [108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 37; 115; 10]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | cbn; lia | lia | cbn; lia] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

scan_pct 17%nat 0%nat [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 37; 115; 10; 0] 0x1edde.
run. call_strchr 0x15b57 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.

run. call_strchr 0x1c640 [106; 122; 116; 76; 113].

run. call_strchr 0x146d7 [99; 67; 115; 83].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => apply evt_done; unfold MID; exists mc, junk1, junk2 end.
eexists _, _. split; [reflexivity|]. split; [exact FRa|]. split; [exact FRb|]. split; [dir_back DIR|].
split; [assumption|]. split; [assumption|]. split; [exact FMT|]. split; [exact ST|]. split; [exact MU| exact WM].
Qed.
End S.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QteI.Mq1 QQNJ.Mq3.
Import Q0z1.
Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Definition MID (ms' : machine_state) : Prop :=
exists (m2 : word -> option byte) (junk1 junk2 : list byte) (x3 x4 : word),
ms' = MS (mkR (wz 0x536f0) (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp
(wz 85509) (wz 0) x3 (wz 100) x4 (wz 0) a5 a6 a7
(wz 10) (wz 85511) (wz 0x15b57) a2 (wz 85510)
(wz 9) (wz (bv_unsigned sp + -2184)) (wz 12297829382473034410)
(wz (-1)) (wz 37) t3 t4 t5 t6)
F (wz 0x536f0) fc None m2 (seg_rom asegs)
/\ rw_cells asegs m2 (bv_unsigned sp + -2240) [CB 8 junk1; C8 (wz (bv_unsigned sp + -120)); C8 a0]
/\ rw_cells asegs m2 (bv_unsigned sp + -2176)
[CB 2072 junk2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m2 (bv_unsigned sp + -2216)
[CB 8 (le8 (wz 0)); CB 8 (le8 (wz 18446744073709551615)); C8 (wz 85509); C8 (wz 85511); C1 (b8 (bv_unsigned (wz 0)));
CB 3 (take 3 (drop 1 (le8 (wz 0)))); C1 (b8 (bv_unsigned (wz 100))); CB 3 (drop 4 (drop 1 (le8 (wz 0))))]
/\ mem_inv asegs m2
/\ ro_cells asegs m2 85509 [C1 (b8 37); C1 (b8 100); C1 (b8 10); C1 (b8 0)]
/\ stk asegs m2 lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m2
/\ wmono asegs m m2.

Lemma printf_common_emit_d_head :
evt asegs MID
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x14e05)  a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. idtac. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.

pose_str FMT 0x14e05 [37; 100; 10; 0] MI.
unfold pcommon_entry in *.

eapply evt_cut; [ eapply pc_setup with (c := 37) (l := [100; 10]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | cbn; lia | lia | cbn; lia] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

run. call_strchr 0x15b57 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.

run. call_strchr 0x1c640 [106; 122; 116; 76; 113].

run. call_strchr 0x146d7 [99; 67; 115; 83].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => apply evt_done; unfold MID; exists mc, junk1, junk2 end.
eexists _, _. split; [reflexivity|]. split; [exact FRa|]. split; [exact FRb|]. split; [dir_back DIR|].
split; [assumption|]. split; [exact FMT|]. split; [exact ST|]. split; [exact MU| exact WM].
Qed.
End S.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QteI.Mq1 QQNJ.Mq3.
Import Q0z1.
Import QlES.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo AP S : Z) (str : list Z) (slack : list byte).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Hypothesis APC : rw_cells asegs m AP [C8 (wz S)].
Hypothesis APLO : bv_unsigned sp <= AP.

Hypothesis STR : bytes_at asegs m S (zb str ++ b8 0 :: slack).
Hypothesis BYT : Forall (fun c => 0 < c < 256) str.
Hypothesis SZ : szone S (zlength str + 1).
Hypothesis SLEN : zlength str + 1 <= 2^40.
Hypothesis SEP : S + zlength str + 1 + zlength slack <= lo \/ bv_unsigned sp <= S.

Definition MID (ms' : machine_state) : Prop :=
exists (m2 : word -> option byte) (junk1 junk2 : list byte) (x3 x4 : word),
ms' = MS (mkR (wz 0x536f0) (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp
(wz 0x1ee06) (wz 0x146d9) x3 (wz 115) x4 (wz 0) a5 a6 a7
(wz 10) (wz 0x1ee08) (wz 0x15b57) (wz AP) (wz 0x1ee07)
(wz 9) (wz (bv_unsigned sp + -2184)) (wz 12297829382473034410)
(wz (-1)) (wz 37) t3 t4 t5 t6)
F (wz 0x536f0) fc None m2 (seg_rom asegs)
/\ rw_cells asegs m2 (bv_unsigned sp + -2240) [CB 8 junk1; C8 (wz (bv_unsigned sp + -120)); C8 a0]
/\ rw_cells asegs m2 (bv_unsigned sp + -2176)
[CB 2072 junk2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m2 (bv_unsigned sp + -2216)
[CB 8 (le8 (wz 0)); CB 8 (le8 (wz 18446744073709551615)); C8 (wz 0x1ee06); C8 (wz 0x1ee08); C1 (b8 (bv_unsigned (wz 0)));
CB 3 (take 3 (drop 1 (le8 (wz 0)))); C1 (b8 (bv_unsigned (wz 115))); CB 3 (drop 4 (drop 1 (le8 (wz 0))))]
/\ mem_inv asegs m2
/\ rw_cells asegs m2 AP [C8 (wz S)]
/\ ro_cells asegs m2 0x1edf3 [C1 (b8 99); C1 (b8 108); C1 (b8 105); C1 (b8 58); C1 (b8 32); C1 (b8 114); C1 (b8 101); C1 (b8 97); C1 (b8 100); C1 (b8 32); C1 (b8 101); C1 (b8 114); C1 (b8 114); C1 (b8 111); C1 (b8 114); C1 (b8 32); C1 (b8 111); C1 (b8 110); C1 (b8 32); C1 (b8 37); C1 (b8 115); C1 (b8 10); C1 (b8 0)]
/\ stk asegs m2 lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m2
/\ wmono asegs m m2.

Lemma printf_common_read_error_head :
evt asegs MID
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x1edf3)  (wz AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. idtac. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
pose proof (rw_cells_bound _ _ _ _ APC) as BAP. cbn in BAP.
assert (SNZ : 0 < S /\ S + (zlength str + 1) + 8 <= 2^47) by (unfold szone in SZ; idtac; lia).

set (BAh := bytes_at) in STR. change (boxed (szone S (zlength str + 1))) in SZ.
change (boxed (S + zlength str + 1 + zlength slack <= lo \/ bv_unsigned sp <= S)) in SEP.

pose_str FMT 0x1edf3 [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 37; 115; 10; 0] MI.
unfold pcommon_entry, zlength in *.

eapply evt_cut; [ eapply pc_setup with (c := 99) (l := [108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 37; 115; 10]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | cbn; lia | lia | cbn; lia] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

scan_pct 19%nat 0%nat [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 37; 115; 10; 0] 0x1edf3.
run. call_strchr 0x15b57 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.

run. call_strchr 0x1c640 [106; 122; 116; 76; 113].

run. call_strchr 0x146d7 [99; 67; 115; 83].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => apply evt_done; unfold MID; exists mc, junk1, junk2 end.
eexists _, _. split; [reflexivity|]. split; [exact FRa|]. split; [exact FRb|]. split; [dir_back DIR|].
split; [assumption|]. split; [assumption|]. split; [exact FMT|]. split; [exact ST|]. split; [exact MU| exact WM].
Qed.
End S.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QteI.Mq1 QQNJ.Mq3.
Import Q0z1.
Import QlES.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Definition MID (ms' : machine_state) : Prop :=
exists (m2 : word -> option byte) (junk1 junk2 : list byte) (x3 x4 : word),
ms' = MS (mkR (wz 0x536f0) (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp
(wz 108523) (wz 0) x3 (wz 117) x4 (wz 0) a5 a6 a7
(wz 10) (wz 108525) (wz 0x15b57) a2 (wz 108524)
(wz 9) (wz (bv_unsigned sp + -2184)) (wz 12297829382473034410)
(wz (-1)) (wz 37) t3 t4 t5 t6)
F (wz 0x536f0) fc None m2 (seg_rom asegs)
/\ rw_cells asegs m2 (bv_unsigned sp + -2240) [CB 8 junk1; C8 (wz (bv_unsigned sp + -120)); C8 a0]
/\ rw_cells asegs m2 (bv_unsigned sp + -2176)
[CB 2072 junk2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m2 (bv_unsigned sp + -2216)
[CB 8 (le8 (wz 0)); CB 8 (le8 (wz 18446744073709551615)); C8 (wz 108523); C8 (wz 108525); C1 (b8 (bv_unsigned (wz 0)));
CB 3 (take 3 (drop 1 (le8 (wz 0)))); C1 (b8 (bv_unsigned (wz 117))); CB 3 (drop 4 (drop 1 (le8 (wz 0))))]
/\ mem_inv asegs m2
/\ ro_cells asegs m2 108509 [C1 (b8 99); C1 (b8 108); C1 (b8 105); C1 (b8 58); C1 (b8 32); C1 (b8 105); C1 (b8 110); C1 (b8 112); C1 (b8 117); C1 (b8 116); C1 (b8 32); C1 (b8 62); C1 (b8 61); C1 (b8 32); C1 (b8 37); C1 (b8 117); C1 (b8 32); C1 (b8 98); C1 (b8 121); C1 (b8 116); C1 (b8 101); C1 (b8 115); C1 (b8 44); C1 (b8 32); C1 (b8 114); C1 (b8 101); C1 (b8 102); C1 (b8 117); C1 (b8 115); C1 (b8 101); C1 (b8 100); C1 (b8 10); C1 (b8 0)]
/\ stk asegs m2 lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m2
/\ wmono asegs m m2.

Lemma printf_common_too_big_head :
evt asegs MID
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x1a7dd)  a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. idtac. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.

pose_str FMT 0x1a7dd [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 37; 117; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10; 0] MI.
unfold pcommon_entry in *.

eapply evt_cut; [ eapply pc_setup with (c := 99) (l := [108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 37; 117; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | cbn; lia | lia | cbn; lia] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

scan_pct 14%nat 0%nat [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 37; 117; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10; 0] 0x1a7dd.
run. call_strchr 0x15b57 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.

run. call_strchr 0x1c640 [106; 122; 116; 76; 113].

run. call_strchr 0x146d7 [99; 67; 115; 83].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => apply evt_done; unfold MID; exists mc, junk1, junk2 end.
eexists _, _. split; [reflexivity|]. split; [exact FRa|]. split; [exact FRb|]. split; [dir_back DIR|].
split; [assumption|]. split; [exact FMT|]. split; [exact ST|]. split; [exact MU| exact WM].
Qed.
End S.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QteI.Mq1 QQNJ.Mq3.
Import Q0z1.
Import QlES.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo AP S : Z) (str : list Z) (slack : list byte).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Hypothesis APC : rw_cells asegs m AP [C8 (wz S)].
Hypothesis APLO : bv_unsigned sp <= AP.

Hypothesis STR : bytes_at asegs m S (zb str ++ b8 0 :: slack).
Hypothesis BYT : Forall (fun c => 0 < c < 256) str.
Hypothesis SZ : szone S (zlength str + 1).
Hypothesis SLEN : zlength str + 1 <= 2^40.
Hypothesis SEP : S + zlength str + 1 + zlength slack <= lo \/ bv_unsigned sp <= S.

Definition MID (ms' : machine_state) : Prop :=
exists (m2 : word -> option byte) (junk1 junk2 : list byte) (x3 x4 : word),
ms' = MS (mkR (wz 0x536f0) (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp
(wz 0x16111) (wz 0x146d9) x3 (wz 115) x4 (wz 0) a5 a6 a7
(wz 10) (wz 0x16113) (wz 0x15b57) (wz AP) (wz 0x16112)
(wz 9) (wz (bv_unsigned sp + -2184)) (wz 12297829382473034410)
(wz (-1)) (wz 37) t3 t4 t5 t6)
F (wz 0x536f0) fc None m2 (seg_rom asegs)
/\ rw_cells asegs m2 (bv_unsigned sp + -2240) [CB 8 junk1; C8 (wz (bv_unsigned sp + -120)); C8 a0]
/\ rw_cells asegs m2 (bv_unsigned sp + -2176)
[CB 2072 junk2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m2 (bv_unsigned sp + -2216)
[CB 8 (le8 (wz 0)); CB 8 (le8 (wz 18446744073709551615)); C8 (wz 0x16111); C8 (wz 0x16113); C1 (b8 (bv_unsigned (wz 0)));
CB 3 (take 3 (drop 1 (le8 (wz 0)))); C1 (b8 (bv_unsigned (wz 115))); CB 3 (drop 4 (drop 1 (le8 (wz 0))))]
/\ mem_inv asegs m2
/\ rw_cells asegs m2 AP [C8 (wz S)]
/\ ro_cells asegs m2 0x1610a [C1 (b8 117); C1 (b8 115); C1 (b8 97); C1 (b8 103); C1 (b8 101); C1 (b8 58); C1 (b8 32); C1 (b8 37); C1 (b8 115); C1 (b8 32); C1 (b8 73); C1 (b8 78); C1 (b8 80); C1 (b8 85); C1 (b8 84); C1 (b8 10); C1 (b8 0)]
/\ stk asegs m2 lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m2
/\ wmono asegs m m2.

Lemma printf_common_usage_head :
evt asegs MID
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x1610a)  (wz AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. idtac. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
pose proof (rw_cells_bound _ _ _ _ APC) as BAP. cbn in BAP.
assert (SNZ : 0 < S /\ S + (zlength str + 1) + 8 <= 2^47) by (unfold szone in SZ; idtac; lia).

set (BAh := bytes_at) in STR. change (boxed (szone S (zlength str + 1))) in SZ.
change (boxed (S + zlength str + 1 + zlength slack <= lo \/ bv_unsigned sp <= S)) in SEP.

pose_str FMT 0x1610a [117; 115; 97; 103; 101; 58; 32; 37; 115; 32; 73; 78; 80; 85; 84; 10; 0] MI.
unfold pcommon_entry, zlength in *.

eapply evt_cut; [ eapply pc_setup with (c := 117) (l := [115; 97; 103; 101; 58; 32; 37; 115; 32; 73; 78; 80; 85; 84; 10]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | cbn; lia | lia | cbn; lia] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

scan_pct 7%nat 0%nat [117; 115; 97; 103; 101; 58; 32; 37; 115; 32; 73; 78; 80; 85; 84; 10; 0] 0x1610a.
run. call_strchr 0x15b57 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.

run. call_strchr 0x1c640 [106; 122; 116; 76; 113].

run. call_strchr 0x146d7 [99; 67; 115; 83].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => apply evt_done; unfold MID; exists mc, junk1, junk2 end.
eexists _, _. split; [reflexivity|]. split; [exact FRa|]. split; [exact FRb|]. split; [dir_back DIR|].
split; [assumption|]. split; [assumption|]. split; [exact FMT|]. split; [exact ST|]. split; [exact MU| exact WM].
Qed.
End S.
End Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf QVsB.
Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp.
Import Qs9x QC9y.
Import QQNJ.Mq1.
Import QcfN. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section ITreeFacts.
Variable segs : list Segment.
Context {node : Type}.
Variable atn : node -> machine_state -> Prop.
Local Notation impl := (Qc6I.impl segs atn).
Local Notation bind := (Qc6I.bind node).

Fixpoint tforall {A} (P : A -> Prop) (t : itree node A) : Prop :=
match t with
| Qc6I.Ret r => P r
| Vis n k => forall x, tforall P (k x)
end.

Lemma tforall_bind : forall {A B} (P : A -> Prop) (P' : B -> Prop) (t : itree node A) (f : A -> itree node B),
tforall P t -> (forall a, P a -> tforall P' (f a)) -> tforall P' (bind t f).
Proof.
induction t as [r|n k IH]; intros f H Hf; cbn in *; [apply Hf; exact H|].
intros x. apply IH; [apply H | exact Hf].
Qed.

Lemma impl_bind_ext2 : forall {A B C} (P : A -> Prop) (t : itree node A) (f : A -> itree node B) (g : A -> itree node C) Q1 Q2 ms,
tforall P t ->
(forall r ms', P r -> impl (f r) Q1 ms' -> impl (g r) Q2 ms') ->
impl (bind t f) Q1 ms -> impl (bind t g) Q2 ms.
Proof.
induction t as [r|n k IH]; intros f g Q1 Q2 ms HP Hfg H; cbn [Qc6I.bind] in *.
- apply Hfg; [exact HP | exact H].
- cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. eapply IH; [apply HP | exact Hfg | apply Hk].
Qed.

Lemma impl_bind_elim : forall {A B} (P : A -> Prop) (t : itree node A) (h : A -> itree node B) Q1 Q2 ms,
tforall P t ->
(forall r ms', P r -> impl (h r) Q1 ms' -> evt segs (Q2 r) ms') ->
impl (bind t h) Q1 ms -> impl t Q2 ms.
Proof.
induction t as [r|n k IH]; intros h Q1 Q2 ms HP Hh H; cbn [Qc6I.bind] in *.
- cbn. apply (Hh r); [exact HP | exact H].
- cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. eapply IH; [apply HP | exact Hh | apply Hk].
Qed.

Lemma impl_tforall : forall {A} (P : A -> Prop) (t : itree node A) Q ms,
tforall P t -> impl t Q ms -> impl t (fun r ms' => Q r ms' /\ P r) ms.
Proof.
induction t as [r|n k IH]; intros Q ms HP H; cbn in *.
- eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ | exact HP].
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; [apply HP | apply Hk].
Qed.
End ITreeFacts.

Section StderrBridge.
Variable segs : list Segment.
Context {St : Type}.
Local Notation impl := (Qc6I.impl segs (at_node segs)).

Definition FLUSH_stderr : M (list Z * St) unit :=
fun bs => let '(buf, st) := bs in
ebind (stdio_writev 2 buf [] st) (fun r => Qc6I.Ret (Ok (tt, (@nil Z, snd r)))).

Lemma wv_loop_leaves : forall fuel fd x (st : St),
tforall (fun r => match r with Ok q => snd q = st | Unr => True end) (mloop fuel (wv_body fd) x st).
Proof.
induction fuel as [|fuel IH]; intros fd x st; cbn [mloop]; [cbn; exact I|].
unfold mbind at 1. unfold ebind.
eapply tforall_bind with (P := fun r => match r with Ok q => snd q = st | Unr => True end).
- unfold wv_body, mbind, msys, enode, ebind. cbn [Qc6I.bind].
intros rsp. destruct (dec_writev (snd x) rsp) as [cnt|]; cbn [Qc6I.bind]; [| cbn; exact I].
cbn [fst snd]. destruct (cnt =? snd x); cbn; reflexivity.
- intros [|[[x'|r] st']] H; cbn in H |- *; [exact I | | exact H]. subst st'. apply IH.
Qed.
Lemma stdio_writev_leaves : forall fd buf s (st : St),
tforall (fun r => match r with Ok q => snd q = st | Unr => True end) (stdio_writev fd buf s st).
Proof. intros fd buf s st. unfold stdio_writev. apply wv_loop_leaves. Qed.

Lemma OUT_stderr_leaves : forall p buf (st : St),
tforall (fun r => match r with Ok q => snd (snd q) = st | Unr => True end) (OUT_stderr p (buf, st)).
Proof.
intros p buf st. unfold OUT_stderr.
destruct (OUT_MAX <? zlength p); [cbn; exact I|].
destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p); [|cbn; reflexivity].
unfold ebind. eapply tforall_bind; [apply stdio_writev_leaves|]. intros [|[a s']] H; cbn; [exact I | exact H].
Qed.

Lemma outsk_flush_leaves : forall ps buf (st : St),
tforall (fun r => match r with Ok q => snd (snd q) = st | Unr => True end) (outsk OUT_stderr ps FLUSH_stderr (buf, st)).
Proof.
induction ps as [|p ps IH]; intros buf st; cbn [outsk].
- unfold FLUSH_stderr, ebind. eapply tforall_bind; [apply stdio_writev_leaves|]. intros [|[a s']] H; cbn; [exact I | exact H].
- unfold mbind at 1. unfold ebind. eapply tforall_bind; [apply OUT_stderr_leaves|].
intros [|[[] [buf' st']]] H; cbn in H |- *; [exact I|]. subst st'. apply IH.
Qed.

Lemma stderr_bridge : forall ps buf (st : St) (Q : St -> machine_state -> Prop) ms,
Forall (fun p => zlength p <= OUT_MAX) ps ->
impl (outsk OUT_stderr ps FLUSH_stderr (buf, st)) (epost (fun p ms' => Q (snd (snd p)) ms')) ms ->
impl (mbind (stderr_pieces buf ps) (fun b => stdio_writev 2 b []) st) (epost (fun p ms' => Q (snd p) ms')) ms.
Proof.
induction ps as [|p ps IH]; intros buf st Q ms SH H; cbn [outsk stderr_pieces] in H |- *.
2: apply Forall_cons_iff in SH; destruct SH as [Hp SH];
unfold mbind at 1 in H; unfold OUT_stderr in H;
replace (OUT_MAX <? zlength p) with false in H by (symmetry; apply Z.ltb_ge; lia);
fold (@OUT_stderr St) in H.
-
rewrite mbind_mret. unfold FLUSH_stderr, ebind in H.
eapply (impl_bind_elim segs (at_node segs) _ _ _ _ _ _ (stdio_writev_leaves 2 buf [] st)); [|exact H].
intros [|[[] st']] ms' Hr Hi; cbn in Hi |- *; [apply evt_done; exact I|].
cbn in Hi. exact Hi.
- destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p) eqn:T.
+
rewrite ?T in H. unfold ebind in H.
apply impl_bind_assoc_rev in H.
unfold mbind at 1. change ((stdio_writev 2 buf p ;;; stderr_pieces [] ps) st) with (ebind (stdio_writev 2 buf p st) (fun q => stderr_pieces [] ps (snd q))).
unfold ebind. apply impl_bind_assoc.
eapply (impl_bind_ext2 segs (at_node segs) _ _ _ _ _ _ _ (stdio_writev_leaves 2 buf p st)); [|exact H].
intros [|[[] st']] ms' Hr Hi; cbn [Qc6I.bind] in Hi |- *.
* exact Hi.
* cbn in Hr. subst st'. apply IH; [exact SH | exact Hi].
+
rewrite ?T in H. cbn [ebind Qc6I.bind fst snd] in H.
apply IH; [exact SH | exact H].
Qed.
End StderrBridge.

Lemma outsk_OUT_stdout : forall {St B} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) ps (k : M St B),
Forall (fun p => zlength p <= OUT_MAX) ps ->
outsk (OUT_stdout get_so set_so) ps k = outsk (stdout_fwritex get_so set_so) ps k.
Proof.
intros St B get_so set_so ps k SH. induction SH as [|p ps Hp SH IH]; cbn [outsk]; [reflexivity|].
unfold OUT_stdout at 1. replace (OUT_MAX <? zlength p) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite IH. reflexivity.
Qed.
End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp Qsn5 QQwg QUxU QOJv QqLk QMSY QkfD QpME QkJ4 QRfV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QTVW.Mq3 QOJv.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk QnRU.Mqa QMSY QkfD.
Import QpME.Mq1 QkJ4.
Import QRfV.Mq0.
Import QlES.
Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n mb : Z) (gp : word).
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let ssz := sec_size n.
Let msz := sec_map_size n.
Let AB := mb + 4096.
Let A := AB + rz.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n <= 2^26.
Hypothesis HP : from_primary n = false.
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Set Default Proof Using "RL Hn HP MBP MBK MBC AVO AVP".

Lemma sgeomS : rz = 2048 /\ n' = n /\ 64513 <= n <= 2^26 /\ nd mod 8 = 0 /\ n + 2048 <= nd /\ nd < n + 2056 /\ ssz = nd + 2048
/\ msz mod 4096 = 0 /\ ssz + 4096 <= msz /\ msz < ssz + 8192 /\ nd = 2048 + round_up n 8
/\ A mod 16 = 0 /\ appr_lia mb msz /\ mb + msz <= band_lo
/\ (mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb) /\ 0x10007fff8000 <= prim_lo RE /\ prim_lo RE + 2^37 + 0x1000 <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (mb + msz <= rl_T X \/ rl_T X + 4096 <= mb)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (mb + msz <= rl_ctx X \/ rl_ctx X + 65536 <= mb)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (mb + msz <= rl_dn X \/ rl_dn X + 0x100000 <= mb)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (mb + msz <= rl_ssb X \/ rl_ssb X + 0x800000 <= mb).
Proof. exact (sgeom RE X n mb RL Hn HP MBP MBK MBC AVO AVP). Qed.

Lemma alloc_hdr_sec : forall ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s7r : word) (sp : word) (F : bvmap 5 word) fc m lo
(fj : list byte) (canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav : word) (b0 b1 : byte) (h w d : word) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m (bv_unsigned sp + -128) (alloc_frame fj canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
rw_cells asegs m (A + -16) [C1 b0; C1 b1; C2 h; C4 w; C8 d] ->
(forall m1 (u0 u1 u2 u3 u5 u6 u7 : word),
munch [(A + -16, A)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) ->
rw_cells asegs m1 (bv_unsigned sp + -128) (alloc_frame fj canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
rw_cells asegs m1 (A + -16) [C1 b0; C1 (b8 (hb1 b1)); C2 (wz 0); C4 (wz n'); C8 d] ->
RTconst RE X m1 ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 0) (wz n') u0 u1 u2 u3 (wz (AB + ssz)) u5 u6 u7
(wz AB) (wz ssz) (wz A) (wz (A + -16)) (wz A_INSTANCE) s7r (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f408) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 0) (wz n') (wz AB) a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz ssz) (wz rz) (wz n) (wz A_INSTANCE) s7r (wz (-8)) (wz 7) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f310) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI ST CEIL LO FR HDR CONT.
pose proof sgeomS as (Grz & Gn' & GN & Gnd8 & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & GP & PK & PC & TK & TB & TA & TD & CK & CC & CD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (RT_T _ _ _ RT) as TT. pose proof (RT_ctx_tid _ _ _ RT) as CT. cbv beta delta [rt_T_cells] in TT.
pose proof (munch_refl [(A + -16, A)] m) as MU. pose proof (wmono_refl asegs m) as WM.
subst A. unfold alloc_frame in FR.
step.
step.
rewrite (unsigned_lit (AB + rz)), land_7 by lia.
replace ((AB + rz) mod 8) with 0 by (clear - GA16; Z.div_mod_to_equations; lia).
step.
step. if_lit.
step.
step. ifz.
step.
stp.
step.
step.
step.
rewrite (unsigned_lit n'), Z.shiftr_div_pow2, (Z.div_small n') by (first [ clear - TK PK GM1 Gssz Gnd1 GN Gn' Grz MBK AB msz ssz nd n' rz mb n X RE BAND; lia | lia ]).
step.
rewrite (unsigned_lit n), Z.shiftr_div_pow2, (Z.div_small n) by lia.
step.
step.
step.
step. if_lit.
step.
step.
step.
step.
step.
rewrite hb1_norm in HDR.
step. ifz.
step.
stp.
stp.
step.
replace (ssz + AB) with (AB + ssz) by lia.
eapply CONT; [exact MU| exact WM| assumption| exact ST| exact FR| exact HDR| ].
eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [apply (rt_avoid_sec RE X n mb RL Hn HP MBP MBK MBC AVO AVP); try unfold A in *; unfold AB, msz, ssz, nd, rz in *; lia| constructor].
Qed.

Definition depot_W (sp : Z) : list (Z * Z) :=
[(sp - 352, sp - 128); (SS_BASE, DP_END); (rl_dn X, rl_dn X + 0x100000); (rl_ssb X, rl_ssb X + 0x800000)].

Lemma alloc_depot_sec : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sp : word) (F : bvmap 5 word) fc m lo
(obj tsz dn : Z) (q : list word) (b0 : byte) (b1v : Z) (d : word) (Q : machine_state -> Prop),
RTconst RE X m -> RDepot RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz tsz)] ->
u64arr asegs m (obj + 16) q -> Z.of_nat (length q) = 30 -> 1 <= tsz <= 30 ->
depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= obj -> obj + 256 < 2^64 ->
rw_cells asegs m (A + -16) [C1 b0; C1 (b8 b1v); C2 (wz 0); C4 (wz n'); C8 d] ->
(forall m1 (u0 u1 u2 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 : word) (id : Z),
munch ((A + -8, A) :: depot_W (bv_unsigned sp)) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) ->
RTconst RE X m1 -> RDepot RE X m1 ->
rw_cells asegs m1 obj [C8 (wz (obj + 16)); C8 (wz tsz)] -> u64arr asegs m1 (obj + 16) q ->
1 <= id < 2^16 -> (exists dn', depot_n asegs m1 dn' /\ dn <= dn' <= dn + 1) ->
rw_cells asegs m1 (A + -16) [C1 b0; C1 (b8 b1v); C2 (wz 0); C4 (wz n'); C8 (wz id)] ->
evt asegs Q (MS (mkR (wz 0x3f414) (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 (wz 0) (wz n') (wz id) u5 u6 u7 u10 u11 u12 u13
(wz AB) (wz ssz) (wz A) (wz (A + -16)) (wz A_INSTANCE) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f424) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 0) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz ssz) (wz A) (wz (A + -16)) (wz A_INSTANCE) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f408) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RD MI ST CEIL LO OBJ TRQ LQ SZR DNH DCAP OB1 OB2 HDR CONT.
pose proof sgeomS as (Grz & Gn' & GN & Gnd8 & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & GP & PK & PC & TK' & TB & TA & TD & CK & CC & CD & NK & NC & ND & BK & BC & BD).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (munch_refl ((A + -8, A) :: depot_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold depot_W, SS_BASE, DP_END in MU. subst A.
step.
step.
step.
call_sp_ch (depot_put_spec RE X) ltac:(fun PO => unfold depot_stack, SS_BASE, DP_END in PO);
[exact RL| exact RD| assumption| exact ST| exact CEIL'| unfold depot_stack; lia| exact TRQ| exact LQ| exact SZR| exact DNH| exact DCAP| lia| lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST end.
match goal with H : (exists id, _) |- _ => destruct H as (id & -> & ID & RD1 & TRQ1 & (dn1 & [DNC DNP] & DNR)) end. unfold DP_N in DNC.
step.
step.
rewrite (unsigned_lit id), (zext32_small id) by lia.
step.
rewrite (unsigned_lit id), Z.lor_0_l by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(AB + rz + -8, AB + rz)] mm) as MUh; pose proof (wmono_refl asegs mm) as WMh end.
step.
eapply CONT; [exact MU| exact WM| assumption| exact ST| | | exact OBJ| exact TRQ| exact ID| exists dn1; split; [split; [unfold DP_N; exact DNC| exact DNP]| exact DNR]| exact HDR].
- eapply RTconst_munch; [exact RT| exact MU| exact WM|]. unfold depot_W.
constructor; [apply (rt_avoid_sec RE X n mb RL Hn HP MBP MBK MBC AVO AVP); try unfold A in *; unfold AB, msz, ssz, nd, rz in *; (first [ clear - TK' PK GM1 Gssz Gnd1 GN Grz ks q MBK mb n X RE BAND; lia | lia ])|].
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_depot_img; exact RL|].
constructor; [apply rt_avoid_dn; exact RL|].
constructor; [apply rt_avoid_ssb; exact RL| constructor].
- eapply RDepot_frame; [exact RD1| exact WMh|].
eapply agree_on_of_munch; [exact MUh| exact WMh|]. intros z Fz _. cbn [outside]. split; [| exact I].
destruct Fz as [Fz|[Fz|[Fz|Fz]]]; [destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; lia
| destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; (first [ clear - F2 F1 z BK ND NK CK TK' PK GP GM1 Gssz Gnd1 Gnd8 GN Grz ks q AVP MBK MBP AB msz ssz nd rz mb n X RE BAND; lia | lia ]) | destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; (first [ clear - F2 F1 z BD BK NK CK TK' PK GP GM1 Gssz Gnd1 Gnd8 GN Grz ks q AVP MBK MBP AB msz ssz nd rz mb n X RE BAND; lia | lia ]) | (first [ clear - Fz z TA TK' PK GK GM1 Gssz Gnd1 Gnd8 GN Grz ks q MBK MBP AB msz ssz nd rz mb n X RE BAND; lia | lia ])].
Qed.

End S.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QTVW.Mq3 QOJv.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk QnRU.Mqa QMSY QkfD.
Import QpME.Mq1 QkJ4.
Import QRfV.Mq0.
Import QpME.Mq1 QkJ4.
Import QlES.
Import QpME.Mq4. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.

Local Ltac lia ::= lia_fast. Local Ltac mkr__lia_0 := lia_fast.
Local Ltac Q0z1.transport_lia ::= tslia_fast. Local Ltac mkr__transport_lia_1 := tslia_fast.
Local Ltac QsGW.if_lit ::= if_lit_fast. Local Ltac mkr__if_lit_2 := if_lit_fast.
Local Ltac Qu1d.sfp_cheap ::= sfp_fast. Local Ltac mkr__sfp_cheap_3 := sfp_fast.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n mb : Z) (gp : word).
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let ssz := sec_size n.
Let msz := sec_map_size n.
Let AB := mb + 4096.
Let A := AB + rz.
Let sz := msz - 4096.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n <= 2^26.
Hypothesis HP : from_primary n = false.
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Set Default Proof Using "RL Hn HP MBP MBK MBC AVO AVP".

Lemma sgeomS : rz = 2048 /\ n' = n /\ 64513 <= n <= 2^26 /\ nd mod 8 = 0 /\ n + 2048 <= nd /\ nd < n + 2056 /\ ssz = nd + 2048
/\ msz mod 4096 = 0 /\ ssz + 4096 <= msz /\ msz < ssz + 8192 /\ nd = 2048 + round_up n 8
/\ A mod 16 = 0 /\ appr_lia mb msz /\ mb + msz <= band_lo
/\ (mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb) /\ 0x10007fff8000 <= prim_lo RE /\ prim_lo RE + 2^37 + 0x1000 <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (mb + msz <= rl_T X \/ rl_T X + 4096 <= mb)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (mb + msz <= rl_ctx X \/ rl_ctx X + 65536 <= mb)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (mb + msz <= rl_dn X \/ rl_dn X + 0x100000 <= mb)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (mb + msz <= rl_ssb X \/ rl_ssb X + 0x800000 <= mb).
Proof. exact (sgeom RE X n mb RL Hn HP MBP MBK MBC AVO AVP). Qed.

Lemma alloc_partial_sec : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s0v s3v s9v : word) (sp : word) (F : bvmap 5 word) fc m
(obj : Z) (pb : byte) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m ->
(n' mod 8 <> 0 -> rw_cells asegs m (SH A + n' / 8) [C1 pb]) ->
(forall m1 (u u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 u22 : word),
munch [(SH A + n' / 8, SH A + ngran n')] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> RTconst RE X m1 ->
(n' mod 8 <> 0 -> rw_cells asegs m1 (SH A + n' / 8) [C1 (b8 (n' mod 8))]) ->
evt asegs Q (MS (mkR u (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 s0v (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) s3v (wz A) (wz (A + -16)) u22 (wz obj) (wz 0) s9v (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f5b4) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 s0v (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) s3v (wz A) (wz (A + -16)) (wz (8 * (n' / 8))) (wz obj) (wz 0) s9v (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f520) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI P3 CONT.
pose proof sgeomS as (Grz & Gn' & GN & Gnd8 & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & _).
assert (AL16 : AB mod 16 = 0) by (subst AB; clear - MBP; Z.div_mod_to_equations; lia).
assert (Grz16 : rz mod 16 = 0) by (rewrite Grz; reflexivity).
assert (Gn1 : 1 <= n') by lia.
assert (SHa : SH AB = AB / 8 + 0x7fff8000) by reflexivity.
assert (SHA : SH (AB + rz) = SH AB + rz / 8) by (rewrite <- SH_plus8; f_equal; clear - Grz16; Z.div_mod_to_equations; lia).
assert (N8 : 0 <= n' / 8 /\ 0 <= n' mod 8 < 8 /\ n' = 8 * (n' / 8) + n' mod 8) by (clear - Gn1; Z.div_mod_to_equations; lia).
pose proof (ngran_eq n' ltac:((first [ clear - Gn1 AB msz nd n' rz mb n BAND; lia | lia ]))) as (NG1 & NG2 & NG3). pose proof (round_up_8 n' ltac:((first [ clear - Gn1 AB msz nd n' rz mb n BAND; lia | lia ]))) as [RU8 _].
subst A.
step.
destruct (Z.eq_dec (n' mod 8) 0) as [Z0|NZ].
- ifz.
eapply CONT; [| apply wmono_refl| exact MI| exact RT| intros NE; exfalso; exact (NE Z0)].
replace (ngran n') with (n' / 8) by (rewrite NG1; unfold round_up; clear -Z0 N8; Z.div_mod_to_equations; lia). apply munch_refl.
- ifz. specialize (P3 NZ).
remember (SH (AB + rz) + n' / 8) as SP8 eqn:ESP8.
pose proof (munch_refl [(SP8, SH (AB + rz) + ngran n')] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 19%nat K19. rtc RT 5%nat K5. rtc RT 1%nat K1. rtc RT 14%nat K14.
step. call0 (can_poison_spec RE X); [exact RT| exact MI|]. subst_words.
step. if_lit.
step. step. step.
step.
stp. stp. stp. stp.
step. destruct (Z.leb_spec (AB + rz + 8 * (n' / 8)) 0x7fff7fff) as [LOWM|HIGHM].
{
ifz.
step. step.
step.
lits.
step.
rewrite (unsigned_lit (AB + rz + 8 * (n' / 8))), Z.shiftr_div_pow2 by (first [ clear - LOWM NZ N8 Gn1 GM1 Gssz Gnd1 GN Gn' Grz MBK AB msz ssz nd n' rz mb n BAND; lia | lia ]). change (2 ^ 3) with 8.
step.
replace (2147450880 + (AB + rz + 8 * (n' / 8)) / 8) with SP8 by (rewrite ESP8, SHA, SHa; clear - AL16 Grz16 N8; Z.div_mod_to_equations; (first [ clear - H24 q4 H19 q3 H15 H14 r2 q2 H5 H4 r0 q0 H0 H r q q1 Grz16 r3 AL16 r4 AB rz mb n; lia | lia ])).
stp.
step.
rewrite (unsigned_lit n'), (Z.land_comm n' 18446744073709551615), land_ones64 by (first [ clear - NZ N8 Gn1 Gnd1 GN Gn' MBK AB msz nd n' rz mb n BAND; lia | lia ]).
step.
rewrite (unsigned_lit n'), land_7 by (first [ clear - NZ N8 Gn1 Gnd1 GN Gn' MBK AB msz nd n' rz mb n BAND; lia | lia ]).
step.
rewrite (unsigned_lit (n' mod 8)) in P3 by lia.
eapply CONT; [exact MU| exact WM| assumption| | intros _; exact P3].
eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [| constructor]. rewrite ESP8, SHA, SHa. subst AB. apply rt_avoid_gap; [exact RL| clear - GK N8 Grz; Z.div_mod_to_equations; (first [ clear - H5 H4 r0 q0 H0 H r q N8 r1 q1 GK Grz msz n' rz mb n; lia | lia ])| rewrite ?KHI_eq, NG1; unfold round_up; clear - GC GM1 Gssz Gnd1 Gn' N8 NZ Grz; Z.div_mod_to_equations; (first [ clear - H15 H14 r2 H10 H9 q2 r1 q1 H5 H4 r0 q0 H0 H r q NZ N8 r3 q3 GC GM1 Gssz Gnd1 Gn' Grz msz ssz nd n' rz mb n BAND; lia | lia ])]. }
unfold_cond; cond_unsig; if_false.
step. step. step. step.
step. step.
stp.
step. ifz.
step. step. step.
stp. stp.
step. unfold_cond; cond_unsig; if_false.
step. unfold_cond; cond_unsig; if_false.
step. step.
step.
lits.
step.
rewrite (unsigned_lit (AB + rz + 8 * (n' / 8))), Z.shiftr_div_pow2 by (first [ clear - HIGHM NZ N8 Gn1 GC GM1 Gssz Gnd1 GN Gn' Grz MBK AB msz ssz nd n' rz mb n BAND; lia | lia ]). change (2 ^ 3) with 8.
step.
replace (2147450880 + (AB + rz + 8 * (n' / 8)) / 8) with SP8 by (rewrite ESP8, SHA, SHa; clear - AL16 Grz16 N8; Z.div_mod_to_equations; (first [ clear - H24 q4 H19 q3 H15 H14 r2 q2 H5 H4 r0 q0 H0 H r q q1 Grz16 r3 AL16 r4 AB rz mb n; lia | lia ])).
stp.
step.
rewrite (unsigned_lit n'), (Z.land_comm n' 18446744073709551615), land_ones64 by (first [ clear - NZ N8 Gn1 Gnd1 GN Gn' MBK AB msz nd n' rz mb n BAND; lia | lia ]).
step.
rewrite (unsigned_lit n'), land_7 by (first [ clear - NZ N8 Gn1 Gnd1 GN Gn' MBK AB msz nd n' rz mb n BAND; lia | lia ]).
step.
rewrite (unsigned_lit (n' mod 8)) in P3 by lia.
eapply CONT; [exact MU| exact WM| assumption| | intros _; exact P3].
eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [| constructor]. rewrite ESP8, SHA, SHa. subst AB. apply rt_avoid_gap; [exact RL| clear - GK N8 Grz; Z.div_mod_to_equations; (first [ clear - H5 H4 r0 q0 H0 H r q N8 r1 q1 GK Grz msz n' rz mb n; lia | lia ])| rewrite ?KHI_eq, NG1; unfold round_up; clear - GC GM1 Gssz Gnd1 Gn' N8 NZ Grz; Z.div_mod_to_equations; (first [ clear - H15 H14 r2 H10 H9 q2 r1 q1 H5 H4 r0 q0 H0 H r q NZ N8 r3 q3 GC GM1 Gssz Gnd1 Gn' Grz msz ssz nd n' rz mb n BAND; lia | lia ])].
Qed.

End S.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Q13u Qc6I QJFf QVsB.
Import QCiC.Mq1 Qpj5.Mq1 QdZp.
Import QTVW.Mq1 Qu3b.Mq1 QnRU.Mq3 QnRU.Mq4 QteI.Mq1 Qu3b.Mq0 QQNJ.Mq1.
Import QvG1.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition stderr_wfile0 (m : mem) : Prop :=
exists (flags mode : word) (e wend : Z) (tail : list byte),
rw_cells asegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x6435e0 0 2 mode 0xffffffff tail)
/\ Z.land (bv_unsigned flags) 40 = 0
/\ (wend = 0 \/ (wend = 0x6435e0 /\ e = 0x6435e0))
/\ 0 <= e < 2^63.

Lemma stderr_wfile0_wfile : forall m, stderr_wfile0 m -> stderr_wfile m.
Proof. intros m (flags & mode & e & wend & tail & H & FL & _ & _). exists flags, mode, e, wend, tail. split; [exact H| exact FL]. Qed.

Definition FWRITE_DEPTH : Z := 240.

Section Fwrite.
Context {BAND : Band}.
Context {St : Type}.

Definition fwrite_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ stderr_wfile0 m'
/\ ssp_cells m' canary
/\ st' = st.

Definition fwrite_diag_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
towrite_stmt ->
stderr_wfile0 m ->
bytes_at asegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s <= OUT_MAX ->
a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
ssp_cells m canary -> mem_inv asegs m ->
(bv_unsigned sp <= 2^47) -> (bv_unsigned a0 + zlength s <= 2^47) ->
implM asegs (stderr_fwrite s : M St unit) st
(fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd3500) fc None m (seg_rom asegs)).
End Fwrite.
End Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Qc6I QJFf QVsB QDM6.
Import QCiC.Mq1 Qpj5.Mq1 QdZp.
Import QTVW.Mqb QnRU QteI.Mqb Qu3b.Mq4 QQNJ.Mq8 QQNJ QQNJ.Mq7.

Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QYyZ.Mq9.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.

Theorem fwritex_stderr_proof {BAND : Band} : fwritex_stderr_stmt.
Proof.
unfold fwritex_stderr_stmt, out_stmt. intros St B. intros until canary.
intros SINK SRC BYT BSL SZ -> -> ST LO GLO SPHI TOP SSP MI SEPF SEPB SEPS1 SEPS2 SEPS3 TSA.
destruct st as [buf st].
destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO & B47 & ISHm). cbn [fst] in FC, BUF, LEN.
unfold OUT_DEPTH, GLOBALS_TOP, INTERNAL_BUFSIZ, TOPOK_none in *.
destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS.
assert (LSB : length (zb bs) = length bs) by apply zb_length.
pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0.
assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
assert (LS : 0 <= zlength bs) by (unfold zlength; lia).
unfold zlength in *.
set (S := bv_unsigned a0) in *.
assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).

pose proof BUF as BUF0.
apply (rw_cells_split_CB asegs _ _ [] 80 (zb buf ++ rest) [] [length buf; 80 - length buf]%nat) in BUF; [| cbn; unfold zlength in *; lia].
cbn [mk_CB_cells app] in BUF.
rewrite firstn_app, zb_length, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in BUF by (rewrite zb_length; lia).
rewrite skipn_app, zb_length, Nat.sub_diag, skipn_O, skipn_all2 in BUF by (rewrite zb_length; lia). cbn [app] in BUF.
apply (proj1 (QnRU.Mqf.rw_cells_app asegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite ?firstn_all2 in BUFb by lia.
unfold implM, OUT_stderr. cbv beta iota zeta.
destruct (OUT_MAX <? zlength bs) eqn:OGUARD.
{
cbv beta iota zeta. apply impl_ret_unr. }
cbv beta iota zeta.
assert (OG : zlength bs <= OUT_MAX) by (apply Z.ltb_ge; exact OGUARD). unfold OUT_MAX, zlength in OG.
destruct (80 - zlength buf <? zlength bs) eqn:CMP.
-
pose proof (proj1 (Z.ltb_lt _ _) CMP) as CMP'. unfold zlength in CMP'.
eapply impl_evt.
{ eapply fwx_nofit with (lo := lo); [exact FC | exact EA0 | reflexivity | reflexivity | lia | lia | unfold zlength in *; lia | lia | lia | reflexivity | exact ST | lia | lia | exact MI | lia]. }
cbv beta. intros ms1 PO.
destruct PO as (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
unfold file_cells in FC.
transport_after_call asegs m m1 MU1 WM1.
unfold INTERNAL_BUFSIZ. cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with true by (symmetry; exact CMP) end. cbv beta iota zeta.
eapply impl_ebind.
{ eapply (stdio_write_spec (St:=St)) with (B := B) (fd := 2) (Fp := 970048) (buf := buf) (s := bs) (S := S) (lo := lo) (canary := canary)
(wend := B + 80) (bufsize := 80) (mode := mode) (lbf := 0xffffffff) (tail := tail) (flags := flags) (wfn := F_STDIO_WRITE);
try reflexivity.
- exact FC.
- apply (bytes_at_ext _ _ _ _ _ (rw_cells_bytes_at _ _ _ _ BUFa)). cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
- exact SRC.
- lia.
- exact ST1.
- unfold STDIO_WRITE_DEPTH. lia.
- lia.
- split; [exact GOT | exact GUARD].
- exact MI1.
- lia. - lia.
- unfold got_ssp. lia.
- unfold ssp_guard. lia.
- lia. - lia.
- unfold zlength. lia.
- lia.
- unfold zlength. lia.
- lia.
- unfold zlength. lia.
- right. unfold zlength. lia.
- unfold zlength. lia.
- first [lia | rewrite unsigned_lit by lia; lia]. }
cbv beta. intros [[] st'] ms' PO. cbn [fst snd] in PO.
destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
unfold STDIO_WRITE_DEPTH in MU2.
apply impl_ret_ok. cbn [fst snd]. apply evt_done.

pose proof (rw_cells_transport asegs _ m1 m2 _ _ BUF0 MU2 WM2 ltac:(cbn; lia)) as BUF2.
pose proof (bytes_at_transport asegs _ m1 m2 _ _ SRC MU2 ltac:(cbn; rewrite LSB; lia)) as SRC2.
unfold out_post, SR. do 16 eexists. split; [reflexivity|].
split. { apply (munch_trans _ m m1 m2).
- eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; Q0z1.lia3.
- eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; Q0z1.lia3. }
split; [eapply wmono_trans; [exact WM1 | exact WM2] |]. split; [exact MI2|]. split; [exact ST2|].
split.
{
exists flags, mode, tail, (zb buf ++ rest). cbn [fst].
split; [rewrite Z.add_0_r; exact FC2|]. split; [exact FL32|]. split; [exact FL8|].
split; [exact BUF2|]. split; [| split; [exact BHI| split; [exact BGLO| split; [exact B47|]]]].
2:{ eapply (ISH_munch_zone m m2 [(lo, bv_unsigned sp); (970048, 970048 + 232); (B, B + 80)]); [exact ISHm| | eapply wmono_trans; [exact WM1| exact WM2]| zforalls].
apply (munch_trans _ m m1 m2); [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros; Q0z1.lia3. }
unfold zlength. cbn [length]. rewrite length_app, zb_length. lia. }
split; [exact SSP2 | exact SRC2].
-
pose proof (proj1 (Z.ltb_ge _ _) CMP) as CMP'. unfold zlength in CMP'.
cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with false by (symmetry; exact CMP) end. cbv beta iota zeta.
apply impl_ret_ok. cbn [fst snd].
unfold file_cells in FC.
eapply evt_mono.
{ eapply (fwx_fit_plain ra sp gp tp t0 t1 t2 s0 s1 a0) with (lo := lo) (cap := (80 - length buf)%nat) (src := zb bs) (S := S)
(Fp := 970048) (wend := B + 80) (wpos := B + Z.of_nat (length buf)) (junk := rest);
[ exact FC | exact BUFb | lia | exact SRC | rewrite LSB; reflexivity | exact EA0 | reflexivity | reflexivity | try lia .. ];
[exact ST | exact MI |  unfold QnRU.Mqf.FWRITEX_STACK, MEMCPY_ICPT_STACK; lia
| exact (proj2 (proj2 ISHm)) | exact (proj1 (proj2 ISHm))
| apply (rng_ok_of_ash _ _ _ (proj1 ISHm)); [first [exact SZ| match goal with |- szone _ (Z.of_nat (length ?x)) => replace (length x) with (length bs) by (symmetry; exact LSB) end; exact SZ]| lia]
| apply (rng_ok_of_ash _ _ _ (proj1 ISHm)); [unfold szone; right; idtac; lia| lia] ].
}
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2).
unfold out_post, SR. do 16 eexists.
split. { reflexivity. }
split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; Q0z1.lia3. }
split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
assert (GOT2 : rw_cells asegs m2 954256 [C8 (Z_to_bv 64 6575456)]).
{ eapply (rw_cells_transport asegs _ m m2); [exact GOT | exact MU2 | exact WM2 | cbn; lia]. }
assert (GUARD2 : rw_cells asegs m2 6575456 [C8 canary]).
{ eapply (rw_cells_transport asegs _ m m2); [exact GUARD | exact MU2 | exact WM2 | cbn; lia]. }
assert (BUFa2 : rw_cells asegs m2 B [CB (length buf) (zb buf)]).
{ eapply (rw_cells_transport asegs _ m m2); [exact BUFa | exact MU2 | exact WM2 | cbn; lia]. }
split.
{
exists flags, mode, tail, (skipn (length (zb bs)) rest). cbn [fst].
split. { unfold zlength. rewrite length_app, Nat2Z.inj_add, Z.add_assoc. exact FC2. }
split; [exact FL32|]. split; [exact FL8|].
split.
{
assert (J : rw_cells asegs m2 B ([] ++ [CB (length buf) (zb buf); CB (length (zb bs)) (zb bs); CB (80 - length buf - length (zb bs))%nat (skipn (length (zb bs)) rest)] ++ [])).
{ cbn [app]. apply (proj2 (QnRU.Mqf.rw_cells_app asegs _ _ [_] _)); split; [exact BUFa2|].
cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
rewrite zb_app, <- app_assoc. rewrite LSB in J |- *.
replace (length buf + (length bs + (80 - length buf - length bs + 0)))%nat with 80%nat in J by lia. exact J. }
split; [| split; [exact BHI| split; [exact BGLO| split; [exact B47|]]]].
2:{ eapply (ISH_munch_zone m m2); [exact ISHm| exact MU2| exact WM2| zforalls]. }
unfold zlength. rewrite length_app, length_skipn, LSB. lia. }
split; [split; [exact GOT2 | exact GUARD2] | exact SRC2].
Qed.
End Mqd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWHo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mqc.
Import Q13u QDM6 QJFf.Mq0 QwAs.Mq1 Qc6I QJFf QVsB.

Import QCiC.Mq1 Qpj5.Mq1. Import QCNF QoNr.Mq0. Import QdZp QvDJ.Mq3.
Import Qu3b.Mq6.
Import QTVW.Mq8 Qu3b.Mq5 QTVW.Mq9 QnRU.Mqg QnRU.Mqf QnRU QteI.Mqb.
Import QCNF.Mq2.
Import QoBx.Mq0 Qu3b.Mq4.
Import QWHo QC9y.Mq0 QcfN.Mq3.
Import QQNJ.Mq8.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QFd5 QYyZ QteI.
Import QlES.

Import Q0z1. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.

Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.

Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac show_goal := match goal with |- ?G => idtac "GOAL:" G end.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac plia := unfold zlength, got_ssp, ssp_guard, PC_DEPTH, OUT_DEPTH, GLOBALS_TOP, FMT_FP_DEPTH, INT_MAX in *; lia.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.

Tactic Notation "callw" tactic3(tac) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | post_call segs m ]
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac br K := brf K; try (exfalso; lia).

Ltac fixr := try (rewrite !swrap32_small by lia); try (rewrite !Z.add_0_r).

Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end.

Definition hide (P : Prop) := P.
Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac glo_lia :=
unfold zlength, zrepeat; rewrite ?repeat_length, ?length_firstn, ?length_app, ?length_map; cbn [length]; try rewrite Z2Nat.id by lia;
first [ lia | unfold GLOBALS_TOP, PC_DEPTH; lia | unfold GLOBALS_TOP, PC_DEPTH, zlength in *; lia ].

Ltac ienter := lazymatch goal with |- Qpj5.Mq1.implM _ _ _ _ _ => unfold Qpj5.Mq1.implM; apply impl_from_evt | |- Qc6I.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
lazymatch goal with |- Qc6I.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Qpj5.Mq1.implM asegs c s Q ms) | _ => idtac end.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma nth_error_zb : forall l i c, nth_error l i = Some c -> nth_error (zb l) i = Some (Z_to_bv 8 c).
Proof. intros l i c H. unfold zb. rewrite nth_error_map, H. reflexivity. Qed.
Lemma znth_nth_error : forall l i, (0 <= i < zlength l)%Z -> nth_error l (Z.to_nat i) = Some (znth l i).
Proof.
intros l i Hi. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
destruct (nth_error l (Z.to_nat i)) as [c|] eqn:E.
- rewrite (nth_error_nth _ _ _ E). reflexivity.
- apply nth_error_None in E. unfold zlength in Hi. lia.
Qed.
Lemma zbytes_read : forall m A l i a,
bytes_at asegs m A (zb l) -> (0 <= i < zlength l)%Z -> a = wa (A + i) ->
ov_read_bytes asegs m a 1 = Some [Z_to_bv 8 (znth l i)].
Proof.
intros m A l i a HB Hi ->.
eapply (u8ro_read asegs m A (zb l) i); [exact HB | | lia | reflexivity].
apply nth_error_zb. apply znth_nth_error. exact Hi.
Qed.
Lemma Forall_znth : forall (P : Z -> Prop) l i, Forall P l -> (0 <= i < zlength l)%Z -> P (znth l i).
Proof.
intros P l i HF Hi. apply (proj1 (Forall_forall P l) HF). unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
apply nth_In. unfold zlength in Hi. lia.
Qed.

Lemma land_lxor_distr : forall a b m, Z.land (Z.lxor a b) m = Z.lxor (Z.land a m) (Z.land b m).
Proof. intros. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.lxor_spec, !Z.land_spec. destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity. Qed.

Section Sfx.
Variable fmt : list Z.
Definition sfx (k : Z) : list Z := skipn (Z.to_nat k) fmt.
Lemma sfx_cons : forall k, (0 <= k < zlength fmt)%Z -> sfx k = znth fmt k :: sfx (k + 1).
Proof.
intros k Hk. unfold sfx. rewrite Z2Nat.inj_add, Nat.add_1_r by lia.
pose proof (znth_nth_error fmt k Hk) as E.
destruct (nth_error_split fmt (Z.to_nat k) _ E) as (pre & post & Efmt & Hlen).
rewrite Efmt at 1 2. rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. cbn [skipn app].
rewrite <- Efmt. f_equal. rewrite Efmt at 1. change (pre ++ znth fmt k :: post) with (pre ++ ([znth fmt k] ++ post)).
rewrite app_assoc, skipn_app, skipn_all2 by (rewrite length_app; cbn; lia). rewrite length_app. cbn [length].
replace (S (Z.to_nat k) - (length pre + 1))%nat with 0%nat by lia. reflexivity.
Qed.
Lemma sfx_nil : forall k, (zlength fmt <= k)%Z -> sfx k = [].
Proof. intros k Hk. unfold sfx. apply skipn_all2. unfold zlength in Hk. lia. Qed.
Lemma sfx_skipn : forall n k, (0 <= k)%Z -> skipn n (sfx k) = sfx (k + Z.of_nat n).
Proof. intros n k Hk. unfold sfx. rewrite skipn_skipn. f_equal. lia. Qed.
Lemma sfx_length : forall k, (0 <= k <= zlength fmt)%Z -> zlength (sfx k) = (zlength fmt - k)%Z.
Proof. intros k Hk. unfold sfx, zlength in *. rewrite length_skipn. lia. Qed.
Lemma sfx_cons_inv : forall k c s, (0 <= k)%Z -> sfx k = c :: s -> (k < zlength fmt)%Z /\ c = znth fmt k /\ s = sfx (k + 1).
Proof.
intros k c s Hk E. destruct (Z.lt_ge_cases k (zlength fmt)) as [Hlt|Hge].
- rewrite sfx_cons in E by lia. injection E as <- <-. split; [exact Hlt| split; reflexivity].
- rewrite sfx_nil in E by lia. discriminate.
Qed.

Lemma lit_run_firstn : forall s, lit_run s = firstn (length (lit_run s)) s.
Proof. induction s as [|c s IH]; cbn; [reflexivity|]. destruct ((c =? 0) || (c =? 37))%Z; cbn; [reflexivity|]. f_equal. exact IH. Qed.
Lemma lit_run_length : forall s, (length (lit_run s) <= length s)%nat.
Proof. induction s as [|c s IH]; cbn; [lia|]. destruct ((c =? 0) || (c =? 37))%Z; cbn; lia. Qed.
Lemma lit_run_in : forall s j c, nth_error (lit_run s) j = Some c -> c <> 0%Z /\ c <> 37%Z.
Proof.
induction s as [|c s IH]; intros j c' H; cbn in H. { destruct j; discriminate. }
destruct (Z.eqb_spec c 0); [destruct j; discriminate|]. destruct (Z.eqb_spec c 37); [destruct j; discriminate|]. cbn in H.
destruct j as [|j]; cbn in H. { injection H as <-. lia. } eapply IH. exact H.
Qed.
Lemma lit_run_stop : forall s c s', skipn (length (lit_run s)) s = c :: s' -> c = 0%Z \/ c = 37%Z.
Proof.
induction s as [|c s IH]; intros c' s' H; cbn in H; [discriminate|].
destruct (Z.eqb_spec c 0); [cbn in H; injection H as <- _; lia|]. destruct (Z.eqb_spec c 37); [cbn in H; injection H as <- _; lia|].
cbn in H. eapply IH. exact H.
Qed.

Lemma lit_run_sfx : forall i, (0 <= i)%Z -> let n := zlength (lit_run (sfx i)) in
(i + n <= Z.max i (zlength fmt))%Z /\ skipn (length (lit_run (sfx i))) (sfx i) = sfx (i + n)
/\ (forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z
/\ lit_run (sfx i) = firstn (Z.to_nat n) (sfx i).
Proof.
intros i Hi. cbv zeta. pose proof (lit_run_length (sfx i)) as L. unfold zlength.
split. { unfold sfx in L |- *. rewrite length_skipn in L. lia. }
split. { rewrite sfx_skipn by lia. reflexivity. }
split.
- intros j Hj.
assert (E : nth_error (lit_run (sfx i)) (Z.to_nat j) = Some (znth fmt (i + j))).
{ rewrite lit_run_firstn. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 (Z.to_nat j) (length (lit_run (sfx i)))); [|lia].
unfold sfx. rewrite nth_error_skipn. replace (Z.to_nat i + Z.to_nat j)%nat with (Z.to_nat (i + j)) by lia.
apply znth_nth_error. unfold sfx in *. rewrite length_skipn in L. unfold zlength. lia. }
exact (lit_run_in _ _ _ E).
- rewrite Nat2Z.id. apply lit_run_firstn.
Qed.
End Sfx.

Lemma land_M64_id : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma landM64_zero : forall p, (-2^63 <= p < 2^63)%Z -> (Z.land p 18446744073709551615 = 0 <-> p = 0)%Z.
Proof.
intros p Hp. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
split; intros H; [|subst p; reflexivity]. Z.div_mod_to_equations. nia.
Qed.
Lemma if_false_Z : forall a b : Z, (if false then a else b) = b. Proof. reflexivity. Qed.
Lemma if_true_Z : forall a b : Z, (if true then a else b) = a. Proof. reflexivity. Qed.

Lemma div10_magic : forall x, (0 <= x < 2^64)%Z ->
Z.shiftr (Z.shiftr (x * 14757395258967641293) 64) 3 = (x / 10)%Z.
Proof.
intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia. change (2^64 * 2^3)%Z with (2^67)%Z.
pose proof (Z.div_mod x 10 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as R.
pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)) as Q0. pose proof (Z.div_lt_upper_bound x 10 (2^64) ltac:(lia) ltac:(lia)) as Q1.
set (q := (x / 10)%Z) in *. set (s := (x mod 10)%Z) in *. clearbody q s. subst x.
symmetry. apply (Z.div_unique_pos _ _ _ (2 * q + s * 14757395258967641293)%Z).
- change (2^67)%Z with 147573952589676412928%Z. change (2^64)%Z with 18446744073709551616%Z in Q1. lia.
- change (2^67)%Z with 147573952589676412928%Z. lia.
Qed.
Lemma lor48_digit : forall d, (0 <= d < 10)%Z -> Z.lor d 48 = (48 + d)%Z.
Proof.
intros d Hd.
assert (H : (d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9)%Z) by lia.
destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity.
Qed.
Lemma le1_small : forall v, (0 <= v < 256)%Z -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v Hv. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma digits_aux_S : forall f b d y acc,
digits_aux (S f) b d y acc = if y =? 0 then acc else digits_aux f b d (y / b) (d (y mod b) :: acc).
Proof. reflexivity. Qed.
Lemma digits_aux_acc : forall f b d y acc, digits_aux f b d y acc = digits_aux f b d y [] ++ acc.
Proof.
induction f as [|f IH]; intros b d y acc; [reflexivity|]. rewrite !digits_aux_S.
destruct (y =? 0)%Z; [reflexivity|]. rewrite (IH _ _ _ (d (y mod b)%Z :: acc)), (IH _ _ _ [d (y mod b)%Z]). rewrite <- app_assoc. reflexivity.
Qed.
Lemma digits_aux_fuel : forall b f d y acc, (1 < b)%Z -> (0 <= y < b ^ Z.of_nat f)%Z ->
digits_aux f b d y acc = digits_aux (S f) b d y acc.
Proof.
intros b. induction f as [|f IH]; intros d y acc Hb Hy.
- rewrite digits_aux_S. rewrite Z.pow_0_r in Hy. replace y with 0%Z by lia. reflexivity.
- rewrite !digits_aux_S. destruct (Z.eqb_spec y 0); [reflexivity|].
apply IH; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hy by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite Z.mul_comm. lia.
Qed.
Lemma dec_digits_0 : dec_digits 0 = [].
Proof. reflexivity. Qed.
Lemma dec_digits_small : forall x, (1 <= x <= 9)%Z -> dec_digits x = [48 + x]%Z.
Proof.
intros x Hx. unfold dec_digits. change 20%nat with (S (S 18)). rewrite !digits_aux_S.
destruct (Z.eqb_spec x 0); [lia|]. rewrite Z.div_small by lia. cbn [Z.eqb]. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma dec_digits_step : forall x, (10 <= x < 2^64)%Z -> dec_digits x = dec_digits (x / 10) ++ [48 + x mod 10]%Z.
Proof.
intros x Hx. unfold dec_digits at 1. change 20%nat with (S 19). rewrite digits_aux_S.
destruct (Z.eqb_spec x 0); [lia|]. rewrite digits_aux_acc. apply (f_equal2 (@app Z)); [|reflexivity]. unfold dec_digits. apply digits_aux_fuel; [lia|].
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
apply Z.lt_trans with (2^64)%Z; [lia|]. vm_compute. reflexivity.
Qed.
Lemma digits_aux_length : forall f b d y acc, (length (digits_aux f b d y acc) <= f + length acc)%nat.
Proof.
induction f as [|f IH]; intros b d y acc; [cbn; lia|]. rewrite digits_aux_S.
destruct (y =? 0)%Z; [cbn; lia|]. specialize (IH b d (y / b)%Z (d (y mod b)%Z :: acc)). cbn [length] in IH. lia.
Qed.
Lemma dec_digits_length : forall x, (length (dec_digits x) <= 20)%nat.
Proof. intros x. unfold dec_digits. pose proof (digits_aux_length 20 10 (fun v => 48 + v)%Z x []) as L. cbn [length Nat.add] in L. exact L. Qed.
Lemma dec_digits_range : forall x, Forall (fun c => 48 <= c < 58)%Z (dec_digits x).
Proof.
intros x. unfold dec_digits.
assert (G : forall f y acc, Forall (fun c => 48 <= c < 58)%Z acc -> Forall (fun c => 48 <= c < 58)%Z (digits_aux f 10 (fun v => 48 + v)%Z y acc)).
{ induction f as [|f IH]; intros y acc Ha; [exact Ha|]. rewrite digits_aux_S.
destruct (Z.eqb_spec y 0); [exact Ha|]. apply IH. constructor; [|exact Ha]. pose proof (Z.mod_pos_bound y 10 ltac:(lia)). lia. }
apply G. constructor.
Qed.

Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells asegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.
Lemma upd_firstn_part : forall {X} (l : list X) i x n, (n <= i < length l)%nat -> firstn n (upd l i x) = firstn n l.
Proof.
intros X l i x n H. rewrite upd_firstn_skipn by lia. rewrite firstn_app, firstn_firstn, length_firstn.
replace (Nat.min n i) with n by lia. replace (n - Nat.min i (length l))%nat with 0%nat by lia. cbn. apply app_nil_r.
Qed.
Lemma upd_skipn_at : forall {X} (l : list X) i x, (i < length l)%nat -> skipn i (upd l i x) = x :: skipn (S i) l.
Proof.
intros X l i x H. rewrite upd_firstn_skipn by lia. rewrite skipn_app, length_firstn.
replace (Nat.min i (length l)) with i by lia. rewrite Nat.sub_diag, skipn_all2 by (rewrite length_firstn; lia). reflexivity.
Qed.

Lemma hex_digits_0 : forall l, hex_digits l 0 = [].
Proof. reflexivity. Qed.
Lemma hex_digits_step : forall l x, (0 < x < 2^64)%Z ->
hex_digits l x = hex_digits l (x / 16) ++ [Z.lor (znth XDIGITS (x mod 16)) l].
Proof.
intros l x Hx. unfold hex_digits at 1. change 16%nat with (S 15). rewrite digits_aux_S.
destruct (Z.eqb_spec x 0); [lia|]. rewrite digits_aux_acc. apply (f_equal2 (@app Z)); [|reflexivity]. unfold hex_digits. apply digits_aux_fuel; [lia|].
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
change (16 * 16 ^ Z.of_nat 15)%Z with (2^64)%Z. lia.
Qed.
Lemma hex_digits_length : forall l x, (length (hex_digits l x) <= 16)%nat.
Proof. intros l x. unfold hex_digits. pose proof (digits_aux_length 16 16 (fun v => Z.lor (znth XDIGITS v) l) x []) as L. cbn [length Nat.add] in L. exact L. Qed.
Lemma hexchar_ok0 : forall n, (0 <= n < 0 + Z.of_nat 16)%Z -> ((48 <=? Z.lor (znth XDIGITS n) 0) && (Z.lor (znth XDIGITS n) 0 <? 103))%Z = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma hexchar_ok32 : forall n, (0 <= n < 0 + Z.of_nat 16)%Z -> ((48 <=? Z.lor (znth XDIGITS n) 32) && (Z.lor (znth XDIGITS n) 32 <? 103))%Z = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma hexchar_range : forall l v, (l = 0 \/ l = 32)%Z -> (0 <= v < 16)%Z -> (48 <= Z.lor (znth XDIGITS v) l < 103)%Z.
Proof.
intros l v [-> | ->] Hv.
- pose proof (hexchar_ok0 v ltac:(cbn; lia)) as E. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
- pose proof (hexchar_ok32 v ltac:(cbn; lia)) as E. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.
Lemma hex_digits_range : forall l x, (l = 0 \/ l = 32)%Z -> Forall (fun c => 48 <= c < 103)%Z (hex_digits l x).
Proof.
intros l x Hl. unfold hex_digits.
assert (G : forall f y acc, Forall (fun c => 48 <= c < 103)%Z acc -> Forall (fun c => 48 <= c < 103)%Z (digits_aux f 16 (fun v => Z.lor (znth XDIGITS v) l) y acc)).
{ induction f as [|f IH]; intros y acc Ha; [exact Ha|]. rewrite digits_aux_S.
destruct (Z.eqb_spec y 0); [exact Ha|]. apply IH. constructor; [|exact Ha]. apply hexchar_range; [exact Hl|]. pose proof (Z.mod_pos_bound y 16 ltac:(lia)). lia. }
apply G. constructor.
Qed.

Lemma ift : forall (X : Type) (a b : X), (if true then a else b) = a. Proof. reflexivity. Qed.
Lemma iff : forall (X : Type) (a b : X), (if false then a else b) = b. Proof. reflexivity. Qed.

Lemma lo64_range : forall y, (0 <= lo64 y < 2^64)%Z.
Proof. intros y. unfold lo64. rewrite wrap64_mod. apply Z.mod_pos_bound. lia. Qed.
Lemma hi64_range : forall y, (0 <= hi64 y < 2^64)%Z.
Proof. intros y. unfold hi64. rewrite wrap64_mod. apply Z.mod_pos_bound. lia. Qed.
Lemma lo64_hi64 : forall y, (0 <= y < 2^128)%Z -> (lo64 y + 2^64 * hi64 y)%Z = y.
Proof.
intros y Hy. unfold lo64, hi64. rewrite !wrap64_mod. rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small (y / 2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; change (2^64 * 2^64)%Z with (2^128)%Z; lia]).
pose proof (Z.div_mod y (2^64) ltac:(lia)). lia.
Qed.

Section Ranges128.
Local Open Scope Z_scope.
Lemma mk128_range : forall hi lo, 0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= mk128 hi lo < 2^128.
Proof.
intros hi lo Hh Hl. unfold mk128. apply QwAs.lor_lt_pow2; [|lia].
rewrite Z.shiftl_mul_pow2 by lia. change (2^128) with (2^64 * 2^64). nia.
Qed.
Lemma shr64_range64 : forall a k, 0 <= a < 2^64 -> 0 <= k -> 0 <= Z.shiftr a k < 2^64.
Proof. intros. apply Qcrs.Z_shiftr_range; lia. Qed.
Lemma sra63_range : forall x, 0 <= sra63 x < 2^64.
Proof. intros x. unfold sra63, ONES64. destruct (is_neg64 x); cbn; lia. Qed.

End Ranges128.

Lemma sx32_int : forall (slot : word) i, (-2^31 <= i < 2^31)%Z -> (bv_unsigned slot mod 2^32 = i mod 2^32)%Z ->
sx32 slot = Z_to_bv 64 (i mod 2^64).
Proof.
intros slot i Hi E. unfold sx32. rewrite Z_to_bv_mod64. apply Z_to_bv_eqm. f_equal.
change (2^32)%Z with 4294967296%Z in E.
rewrite swrap32_eq. rewrite <- Zplus_mod_idemp_l, E, Zplus_mod_idemp_l.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma zx32_uint : forall (slot : word) u, (bv_unsigned slot mod 2^32 = u)%Z -> zx32 slot = Z_to_bv 64 u.
Proof. intros slot u E. unfold zx32. rewrite E. reflexivity. Qed.

Lemma land_land_same : forall a m, Z.land (Z.land a m) m = Z.land a m.
Proof. intros. rewrite <- Z.land_assoc, Z.land_diag. reflexivity. Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
Lemma cb8_c8_in : forall m A pre post bs, rw_cells asegs m A (pre ++ CB 8 bs :: post) -> rw_cells asegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
intros m A pre post bs [[Hwf Hb] Hw].
apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
split; [split|].
- apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
- rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite le8_of_bytes by exact H2. exact Hb.
- rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.
Ltac c8ify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let rec go pre l := lazymatch l with
| CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
| ?c :: ?l' => go constr:(pre ++ [c]) l'
| [] => idtac end in
go constr:(@nil cell) cs end.

Lemma printf_loop_S : forall {St : Type} (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z) fuel s args cnt,
printf_loop OUT OUTFP (S fuel) s args cnt =
match s with
| [] => munr
| c :: _ =>
if (c =? 0)%Z then mret cnt else
let lit := lit_run s in
let l := zlength lit in
let s1 := skipn (Datatypes.length lit) s in
match s1 with
| [] => munr
| c1 :: s2 =>
if ((c1 =? 37) && match s2 with [] => true | c2 :: _ => (c2 =? 37) end)%Z
then munr
else if (0 <? l)%Z then
(if (INT_MAX - cnt <? l)%Z then munr
else OUT lit ;;; printf_loop OUT OUTFP fuel s1 args (cnt + l))
else
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
OUT [] ;;;
cnt' <- conv OUT OUTFP cnt d a ;;
printf_loop OUT OUTFP fuel s3 args' cnt'
| _, _ => munr
end
end
end.
Proof. reflexivity. Qed.
Lemma fp_calls_S : forall fuel s args,
fp_calls (S fuel) s args =
match s with
| [] => []
| c :: _ =>
if (c =? 0)%Z then [] else
let lit := lit_run s in
let s1 := skipn (Datatypes.length lit) s in
if (0 <? zlength lit)%Z then fp_calls fuel s1 args
else match s1 with
| _ :: s2 =>
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
match a with
| PA_g dd =>
let fl := (if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD))%Z in
(dd, d_w d, d_p d, fl, d_t d) :: fp_calls fuel s3 args'
| _ => fp_calls fuel s3 args'
end
| _, _ => []
end
| _ => []
end
end.
Proof. reflexivity. Qed.

Lemma In_firstn_w : forall {A} (x : A) n l, In x (firstn n l) -> In x l.
Proof. intros A x n l. revert n. induction l as [|y l IH]; intros [|n] H; cbn in H; try contradiction. destruct H as [->|H]; [left; reflexivity | right; eapply IH; exact H]. Qed.
Lemma In_skipn_w : forall {A} (x : A) n l, In x (skipn n l) -> In x l.
Proof. intros A x n l. revert n. induction l as [|y l IH]; intros [|n] H; cbn in H; try contradiction; [exact H|]. right. eapply IH. exact H. Qed.
Lemma Forall_sub : forall {A} (P : A -> Prop) (l : list A) n k, Forall P l -> Forall P (firstn n (skipn k l)).
Proof.
intros A P l n k H. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall P l) H).
eapply In_skipn_w. eapply In_firstn_w. exact Hx.
Qed.
Lemma zb_firstn : forall n l, zb (firstn n l) = firstn n (zb l).
Proof. intros. unfold zb. rewrite firstn_map. reflexivity. Qed.
Lemma zb_skipn : forall n l, zb (skipn n l) = skipn n (zb l).
Proof. intros. unfold zb. rewrite skipn_map. reflexivity. Qed.
Lemma bytes_at_sub : forall m A (l : list byte) k n,
bytes_at asegs m A l -> (k <= length l)%nat ->
bytes_at asegs m (A + Z.of_nat k) (firstn n (skipn k l)).
Proof.
intros m A l k n H Hk.
rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H]. rewrite length_firstn, Nat.min_l in H by lia.
rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma parse_dir_conv_type : forall s d rest, parse_dir s = Some (d, rest) -> conv_type (d_t d) = Some (d_ty d).
Proof.
intros s d rest PD. destruct (parse_dir_shape _ _ _ PD) as (_ & SH). destruct (parse_flags s 0) as [fl0 s1'].
destruct SH as (_ & c1 & s1b & _ & _ & s2 & _ & c2 & s2b & _ & PX).
destruct PX as [(_ & _ & _ & Ht & _ & CT) | (_ & _ & c3 & s3b & _ & _ & s3 & _ & _ & CT)]; [rewrite Ht|]; exact CT.
Qed.

Lemma parse_dir_xp : forall s d rest, parse_dir s = Some (d, rest) ->
((d_xp d = false /\ d_p d = -1) \/ (d_xp d = true /\ 0 <= d_p d <= INT_MAX))%Z.
Proof.
intros s d rest PD. destruct (parse_dir_shape _ _ _ PD) as (_ & SH). destruct (parse_flags s 0) as [fl0 s1'].
destruct SH as (_ & c1 & s1b & _ & _ & s2 & _ & c2 & s2b & _ & PX).
destruct PX as [(_ & Hp & Hx & _) | (_ & Hx & c3 & s3b & _ & _ & s3 & G & _)].
- left. split; [exact Hx | exact Hp].
- right. split; [exact Hx|]. eapply getint_some_range; [|exact G]. unfold INT_MAX. lia.
Qed.

Lemma c8_read4 : forall m A pre (w : word) post a,
rw_cells asegs m A (pre ++ C8 w :: post) -> a = wa (A + Z.of_nat (cells_size pre)) ->
ov_read_bytes asegs m a 4 = Some (le4 w).
Proof.
intros m A pre w post a H ->.
apply (proj1 (rw_cells_app asegs m A pre (C8 w :: post))) in H. destruct H as [_ H].
pose proof (rw_cells_bytes_at' _ _ _ _ H) as Hb. cbn [cells_bytes cbytes] in Hb.
pose proof (bytes_at_ov_read asegs m _ _ 0 4 Hb) as R. rewrite Z.add_0_r in R.
rewrite R. 2:{ cbn [skipn]. rewrite length_app, length_le8. lia. }
change (skipn 0 (le8 w ++ cells_bytes post)) with (le8 w ++ cells_bytes post).
rewrite firstn_app, length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r, firstn4_le8. reflexivity.
Qed.

Lemma bytes_at_nil : forall m a, (0 <= a)%Z -> (a <= 2^64)%Z -> bytes_at asegs m a [].
Proof. intros m a H0 H1. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

Section PrintfCore.
Context {BAND : Band}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q + 16 <= 140737488355328)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 143552)%Z /\ szone A (Z.of_nat (length fmt)).

Hypothesis SEP_F : ((954304 <= Fp /\ Fp + 232 <= 6575456) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((6576024 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Notation sfx := (sfx fmt).
Definition ctx_all : unit :=
let _ := (ra, q, gp, tp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, F, fc0, m0,
lo, canary, A, fmt, AP, VA, slots, nla, nlt) in tt.

Definition W : list (Z * Z) := [(lo, q); (AP, AP + 8); (Fp, Fp + 232); (B, B + BS)]%Z.
Notation SPv := (Z_to_bv 64 (q + -544)).
Notation FPv := (Z_to_bv 64 Fp).

Definition Fokd (F1 F2 : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k.
Definition Fok (Ft : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k.
Lemma Fok_refl : Fok F. Proof using F.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0. intros k _. reflexivity. Qed.
Lemma Fok_trans : forall F1 F2, Fok F1 -> (forall k : reg, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k) -> Fok F2.
Proof using F.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0. intros F1 F2 H1 H2 k Hk. rewrite (H2 k Hk). apply H1. exact Hk. Qed.

Definition POST : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (apv : word) (m' : word -> option byte),
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch W m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
/\ frm0 fc' /\ Fok Ft
/\ stk asegs m' lo q
/\ SINK m' st'
/\ ssp_cells m' canary
/\ rw_cells asegs m' AP [C8 apv]
/\ (0 <= r <= INT_MAX)%Z.

Definition hi_cells : list cell :=
[C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

Definition lo_cells (pfx s2s za pl plp l10n alo ahi : word) (j128 : list byte) : list cell :=
[C8 pfx; C8 s2s; C8 za; C8 pl; C8 plp; C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
C8 nla; C8 nlt; C8 (Z_to_bv 64 AP); C8 (Z_to_bv 64 75913); C8 l10n; C8 (Z_to_bv 64 ssp_guard); C8 (Z_to_bv 64 214748364);
C8 alo; C8 ahi; CB 24 j128].

Definition finv (m : word -> option byte) : Prop :=
mem_inv asegs m /\ munch W m0 m /\ wmono asegs m0 m
/\ rw_cells asegs m (q + -112) hi_cells
/\ stk asegs m lo (q + -544)
/\ bytes_at asegs m A (zb fmt)
/\ va_area m VA slots
/\ rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary].

Ltac hush := idtac.

Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & BY & VAA & SSP1 & SSP2); unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.

Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).

Lemma u8_lit : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. Qed.
Lemma fmt_rng : forall i, (0 <= i < zlength fmt)%Z -> (0 <= znth fmt i < 256)%Z.
Proof using fmt HF.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0. intros i Hi. exact (Forall_znth _ fmt i HF Hi). Qed.

Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).

Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.

Lemma states0_bytes : forall m, mem_inv asegs m -> bytes_at asegs m 0x272c0 (zb STATES0).
Proof.
clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma states0_read : forall m t ty, mem_inv asegs m -> conv_type t = Some ty ->
ov_read_bytes asegs m (wa (t + 160448 + -65)) 1 = Some [Z_to_bv 8 ty].
Proof.
clear. intros m t ty MI CT. pose proof (conv_type_range t ty CT) as R.
rewrite <- (states0_conv t ty CT).
eapply (zbytes_read m 0x272c0 STATES0 (t - 65)); [apply states0_bytes; exact MI | change (zlength STATES0) with 58%Z; lia | f_equal; lia].
Qed.

Definition PFXSTR : list Z := [45; 43; 32; 32; 32; 48; 88; 48; 120]%Z.
Lemma pfx_bytes : forall m, mem_inv asegs m -> bytes_at asegs m 69023 (zb PFXSTR).
Proof.
clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma pfx_sub : forall m k n, mem_inv asegs m -> (k + n <= 9)%nat ->
bytes_at asegs m (69023 + Z.of_nat k) (zb (firstn n (skipn k PFXSTR))).
Proof.
clear. intros m k n MI Hk. rewrite zb_firstn, zb_skipn. apply bytes_at_sub; [apply pfx_bytes; exact MI|]. cbn. lia.
Qed.
Lemma xdigits_bytes : forall m, mem_inv asegs m -> bytes_at asegs m 142472 (zb XDIGITS).
Proof.
clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma xdigits_read : forall m v, mem_inv asegs m -> (0 <= v < 16)%Z ->
ov_read_bytes asegs m (wa (142472 + v)) 1 = Some [Z_to_bv 8 (znth XDIGITS v)].
Proof.
clear. intros m v MI Hv. eapply (zbytes_read m 142472 XDIGITS v); [apply xdigits_bytes; exact MI | change (zlength XDIGITS) with 16%Z; lia | reflexivity].
Qed.

Definition JT1 : list Z := [160; 244; 10; 0; 32; 245; 10; 0; 64; 246; 10; 0; 32; 245; 10; 0; 160; 244; 10; 0; 160; 244; 10; 0; 160; 244; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 4; 247; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 160; 246; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 160; 244; 10; 0; 32; 245; 10; 0; 96; 246; 10; 0; 240; 244; 10; 0; 160; 244; 10; 0; 160; 244; 10; 0; 160; 244; 10; 0; 32; 245; 10; 0; 240; 244; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 76; 245; 10; 0; 236; 245; 10; 0; 152; 245; 10; 0; 140; 246; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 56; 245; 10; 0; 32; 245; 10; 0; 40; 246; 10; 0; 32; 245; 10; 0; 32; 245; 10; 0; 160; 246; 10; 0]%Z.
Lemma jt1_bytes : forall m, mem_inv asegs m -> bytes_at asegs m 160120 (zb JT1).
Proof.
clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma jt1_read_lit : forall m (t : Z) bs, mem_inv asegs m -> (65 <= t <= 120)%Z ->
firstn 4 (skipn (Z.to_nat (4 * (t - 65))) (zb JT1)) = bs ->
ov_read_bytes asegs m (wa (160120 + 4 * (t - 65))) 4 = Some bs.
Proof.
clear. intros m t bs MI Ht <-.
pose proof (bytes_at_ov_read asegs m 160120 (zb JT1) (Z.to_nat (4 * (t - 65))) 4 (jt1_bytes m MI)) as R.
rewrite Z2Nat.id in R by lia. apply R.
rewrite zb_length. cbn [length JT1]. lia.
Qed.
Lemma jt1_read_s : forall m t, mem_inv asegs m -> t = 115%Z -> ov_read_bytes asegs m (wa (160120 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 56; Z_to_bv 8 245; Z_to_bv 8 10; Z_to_bv 8 0].
Proof. clear. intros m t MI ->. apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]. Qed.
Lemma jt1_read_d : forall m t, mem_inv asegs m -> (t = 100 \/ t = 105)%Z -> ov_read_bytes asegs m (wa (160120 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 240; Z_to_bv 8 244; Z_to_bv 8 10; Z_to_bv 8 0].
Proof. clear. intros m t MI [-> | ->]; (apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]). Qed.
Lemma jt1_read_u : forall m t, mem_inv asegs m -> t = 117%Z -> ov_read_bytes asegs m (wa (160120 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 40; Z_to_bv 8 246; Z_to_bv 8 10; Z_to_bv 8 0].
Proof. clear. intros m t MI ->. apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]. Qed.
Lemma jt1_read_x : forall m t, mem_inv asegs m -> (t = 120 \/ t = 88)%Z -> ov_read_bytes asegs m (wa (160120 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 160; Z_to_bv 8 246; Z_to_bv 8 10; Z_to_bv 8 0].
Proof. clear. intros m t MI [-> | ->]; (apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]). Qed.
Lemma jt1_read_fp : forall m t, mem_inv asegs m -> conv_type t = Some T_DBL -> ov_read_bytes asegs m (wa (160120 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 8; Z_to_bv 8 45; Z_to_bv 8 8; Z_to_bv 8 0].
Proof.
clear. intros m t MI CT. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL in CT.

repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [try discriminate CT|] end; try discriminate CT.
Qed.

Lemma conv_type_cases : forall t ty, conv_type t = Some ty ->
(ty = T_PTR /\ t = 115%Z) \/ (ty = T_INT /\ (t = 100 \/ t = 105)%Z) \/ (ty = T_UINT /\ (t = 117 \/ t = 120 \/ t = 88)%Z) \/ (ty = T_DBL).
Proof.
clear. intros t ty CT. unfold conv_type in CT.
repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [injection CT as <-|] end; try discriminate CT;
repeat match goal with E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] | E : (_ =? _) = true |- _ => apply Z.eqb_eq in E end;
subst; auto 10.
Qed.

Lemma fl_shl50 : forall fl, (0 <= fl < 131072)%Z ->
(Z.land (Z.shiftl fl 50) 18446744073709551615 < 9223372036854775808 <-> Z.land fl 8192 = 0)%Z.
Proof.
clear. intros fl Hfl. rewrite Z.shiftl_mul_pow2 by lia.
change 8192%Z with (2^13)%Z. rewrite zb_land_pow2 by lia.
change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
split; intros H; Z.div_mod_to_equations; nia.
Qed.
Lemma nzmask_bits' : forall n, (0 <= n < 0 + Z.of_nat 64)%Z -> Bool.eqb (Z.testbit 18446744073709486079 n) (negb (Z.testbit 65536 n)) = true.
Proof. clear. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma nzmask_eq : forall fl, (0 <= fl < 131072)%Z -> Z.land fl 18446744073709486079 = Z.land fl (Z.lnot 65536).
Proof.
clear. intros fl Hfl. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases n 64).
- pose proof (nzmask_bits' n ltac:(cbn; lia)) as E. destruct (Z.testbit 18446744073709486079 n), (Z.testbit 65536 n); cbn in E; try discriminate; reflexivity.
- replace (Z.testbit fl n) with false; [reflexivity|]. symmetry.
destruct (Z.eq_dec fl 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
apply Z.lt_le_trans with 17%Z; [apply Z.log2_lt_pow2; cbn in *; lia|lia].
Qed.
Lemma land_bound' : forall a m, (0 <= a)%Z -> (0 <= m)%Z -> (0 <= Z.land a m <= a)%Z.
Proof.
clear. intros a m Ha Hm. split; [apply Z.land_nonneg; left; exact Ha|].
pose proof (Z.sub_land_same_l a m) as E.
assert (0 <= Z.land a (Z.lnot m))%Z by (apply Z.land_nonneg; left; exact Ha). lia.
Qed.

Lemma sextw_small : forall p, (-2147483648 <= p < 2147483648)%Z -> bv_swrap 32 (Z.land p 18446744073709551615 + 0) = p.
Proof.
clear. intros p Hp. rewrite Z.add_0_r. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
rewrite swrap32_eq.
replace (p mod 2 ^ 64)%Z with (p + 2^64 * (- (p / 2^64)))%Z by (Z.div_mod_to_equations; lia).
change (2^64)%Z with (4294967296 * 4294967296)%Z.
set (kq := (- (p / (4294967296 * 4294967296)))%Z). clearbody kq. Z.div_mod_to_equations. nia.
Qed.

Lemma pad_test_xor : forall fl b, Z.land b 73728 = b ->
(Z.land (Z.lxor fl b) 73728 =? 0)%Z = (Z.land fl 73728 =? b)%Z.
Proof.
clear. intros fl b Hb. rewrite land_lxor_distr, Hb.
destruct (Z.eqb_spec (Z.lxor (Z.land fl 73728) b) 0) as [E|E]; destruct (Z.eqb_spec (Z.land fl 73728) b) as [E2|E2]; try reflexivity; exfalso.
- apply E2. apply Z.lxor_eq. exact E.
- apply E. rewrite E2. apply Z.lxor_nilpotent.
Qed.

Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.

Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].

Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Lemma implM_eq_ms : forall {X} (c : M St X) s Q ms ms', ms = ms' -> implM asegs c s Q ms' -> implM asegs c s Q ms.
Proof using.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0. intros X c s Q ms ms' -> H. exact H. Qed.
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Lemma sink_store : forall m st a (bs : list byte),
SINK m st -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
(a + Z.of_nat (length bs) <= Fp \/ Fp + 232 <= a)%Z -> (a + Z.of_nat (length bs) <= B \/ B + BS <= a)%Z ->
(GLOBALS_TOP <= a)%Z ->
SINK (write_to_mem m (wa a) bs) st.
Proof using Fp B BS SINK SFR.    try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0.
intros m st a bs HS Ha Hb D1 D2 D3.
apply (SFR [(a, a + Z.of_nat (length bs))]%Z m _ st HS).
- apply munch_write; [apply munch_refl | lia | lia | cbn; lia].
- apply wmono_write. apply wmono_refl.
- constructor; [cbn; lia | constructor].
- constructor; [cbn; lia | constructor].
- constructor; [cbn; lia | constructor].
Qed.
Lemma sink_call : forall Wc m m' st,
SINK m st -> munch Wc m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= Fp \/ Fp + 232 <= fst iv)%Z Wc ->
Forall (fun iv => snd iv <= B \/ B + BS <= fst iv)%Z Wc ->
Forall (fun iv => GLOBALS_TOP <= fst iv)%Z Wc ->
SINK m' st.
Proof using Fp B BS SINK SFR.    try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0. intros Wc m m' st HS MU WM D1 D2 D3. exact (SFR Wc m m' st HS MU WM D1 D2 D3). Qed.

Lemma arg_ok_W : forall m m' w a, arg_ok Fp B BS m lo q AP w a -> munch W m m' -> arg_ok Fp B BS m' lo q AP w a.
Proof using Fp B BS q lo fmt AP slots.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0.
intros m m' w a H MU. destruct a as [s|i|u|d]; cbn in H |- *; try exact H.
destruct H as (slack & BYs & Hs & PAD & NZ & SZs & D1 & D2 & D3 & D4). exists slack.
split; [|repeat (split; [assumption|]); assumption].
eapply bytes_at_transport; [exact BYs | exact MU |].
unfold W. cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
Lemma args_ok_W : forall m m' ws args, args_ok Fp B BS m lo q AP ws args -> munch W m m' -> args_ok Fp B BS m' lo q AP ws args.
Proof using Fp B BS q lo fmt AP slots.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0.
intros m m' ws args. revert ws. induction args as [|a args IH]; intros ws H MU; [destruct ws; exact I|].
cbn [args_ok] in H |- *.
destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2]. split; [eapply arg_ok_W; eauto | apply IH; assumption].
Qed.

Definition lo_cells14 (pfx s2s za pl plp l10n : word) : list cell :=
[C8 pfx; C8 s2s; C8 za; C8 pl; C8 plp; C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
C8 nla; C8 nlt; C8 (Z_to_bv 64 AP); C8 (Z_to_bv 64 75913); C8 l10n; C8 (Z_to_bv 64 ssp_guard); C8 (Z_to_bv 64 214748364)].
Lemma lo_split : forall m pfx s2s za pl plp l10n alo ahi j128,
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells asegs m (q + -544) (lo_cells14 pfx s2s za pl plp l10n) /\
rw_cells asegs m (q + -544 + 112) [C8 alo; C8 ahi] /\ rw_cells asegs m (q + -544 + 128) [CB 24 j128].
Proof using q AP nla nlt.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0.
clear. intros. unfold lo_cells in H.
apply (proj1 (rw_cells_app asegs m _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in H. destruct H as [H1 H2]. cbn [cells_size csize Nat.add app] in H2.
change (Z.of_nat 112) with 112%Z in H2.
apply (proj1 (rw_cells_app asegs m _ [_;_] _)) in H2. destruct H2 as [H2 H3]. cbn [cells_size csize Nat.add app] in H3.
change (Z.of_nat 16) with 16%Z in H3.
split; [exact H1|]. split; [exact H2|]. replace (q + -544 + 128)%Z with (q + -544 + 112 + 16)%Z by lia. exact H3.
Qed.
Lemma lo_join : forall m pfx s2s za pl plp l10n alo ahi j128,
rw_cells asegs m (q + -544) (lo_cells14 pfx s2s za pl plp l10n) ->
rw_cells asegs m (q + -544 + 112) [C8 alo; C8 ahi] -> rw_cells asegs m (q + -544 + 128) [CB 24 j128] ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128).
Proof using q AP nla nlt.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear LO. try clear GLO. try clear QHI. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0.
clear. intros. unfold lo_cells.
apply (proj2 (rw_cells_app asegs m _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)). split; [exact H|]. cbn [cells_size csize Nat.add app].
change (Z.of_nat 112) with 112%Z.
apply (proj2 (rw_cells_app asegs m _ [_;_] _)). cbn [cells_size csize Nat.add app]. change (Z.of_nat 16) with 16%Z. split; [exact H0|].
replace (q + -544 + 112 + 16)%Z with (q + -544 + 128)%Z by lia. exact H1.
Qed.

Ltac transport_chunks segs m a bs ::=
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_frame segs m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_frame segs m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia | simpl_sizes; slia | glo_lia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Ltac transport_after_call segs m m' MU WM ::=
let W := lazymatch type of MU with munch ?W _ _ => W end in
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; slia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; slia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; glo_lia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : stk segs m ?loq ?hiq |- _ =>
first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
| clear H ]
| H : munch ?Wq ?mq m |- _ =>
first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
| fail 100 "callee footprint not inside caller footprint" ]
| H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
end.

Lemma pop_arg_callq : forall ra' t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (a0v k ty : Z) (slot x y : word),
a0v = (q + -544 + 112)%Z ->
rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] ->
va_area m VA slots -> nth_error slots (Z.to_nat k) = Some slot -> (0 <= k)%Z ->
rw_cells asegs m (q + -544 + 112) [C8 x; C8 y] ->
stk asegs m lo (q + -544) ->
mem_inv asegs m ->
(ty = T_PTR \/ ty = T_INT \/ ty = T_UINT)%Z ->
evt asegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft' m',
ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
Ft' (ret_pc ra') fc None m' (seg_rom asegs)
/\ munch [(q + -544 - 16, q + -544); (AP, AP + 8); (q + -544 + 112, q + -544 + 112 + 16)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (q + -544)
/\ rw_cells asegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (k + 1)))]
/\ rw_cells asegs m' (q + -544 + 112) [C8 (QoBx.Mq0.pop_arg_lo ty slot); C8 (QoBx.Mq0.pop_arg_hi ty slot y)]
/\ Fokd Ft Ft')
(MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 ty) (Z_to_bv 64 AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 0xd6f00) fc None m (seg_rom asegs)).
Proof using q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear A0. try clear VAHI. try clear BS0.

intros until y. intros -> APC VAA NTH Hk ARGC ST MI TY. unfold PC_DEPTH, GLOBALS_TOP in *.
pose proof (va_area_bound _ _ _ VAA) as VB. unfold zlength in *.
destruct (stk_split _ _ _ (q + -544 - 16) _ ST ltac:(lia)) as [ST1 ST2].
assert (Eq : bv_unsigned SPv = (q + -544)%Z) by (apply unsigned_lit; lia).
assert (Ea : bv_unsigned (Z_to_bv 64 (q + -544 + 112)) = (q + -544 + 112)%Z) by (apply unsigned_lit; lia).
assert (Ep : bv_unsigned (Z_to_bv 64 AP) = AP) by (apply unsigned_lit; lia).
assert (IL : (Z.to_nat k < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
eapply evt_mono.
{ eapply (pop_arg_spec ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + -544 + 112)) (Z_to_bv 64 ty) (Z_to_bv 64 AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Ft fc m VA slots k ty slot x y);
rewrite ?Eq, ?Ea, ?Ep.
all: first [exact ST2 | exact APC | exact VAA | exact NTH | exact ARGC | exact MI | exact TY | reflexivity | lia]. }
cbv beta. intros ms' P. unfold pop_arg_post in P. rewrite !Eq, !Ea, !Ep in P.
destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft' & m' & -> & MU & WM & MI' & ST' & APC' & ARGC' & VAA' & HF).
repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
split.
{ eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ]. }
split; [exact APC'|]. split; [exact ARGC'|]. exact HF.
Qed.

Lemma strnlen_callq : forall ra' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (P n : Z) (buf : list byte),
stk asegs m lo (q + -544) ->
bytes_at asegs m P buf ->
memchr_ok P 0 n buf ->
mem_inv asegs m ->
(P + Z.of_nat (length buf) <= lo \/ q <= P)%Z -> (0 < P < 2^64)%Z -> (0 <= n < 2^64)%Z ->
ISH m -> szone P (memchr_len 0 n buf) ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
Ft (ret_pc ra') fc None m' (seg_rom asegs)
/\ munch [(lo, q + -544)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (q + -544)
/\ bytes_at asegs m' P buf)
(MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 0x4fd2c) fc None m (seg_rom asegs)).
Proof using q gp tp lo LO GLO QHI.    try clear SFR. try clear SFL. try clear TOK. try clear HOUT. try clear HF. try clear TQ. try clear FRM0. try clear HA. try clear SEP_F. try clear SEP_B. try clear HAP. try clear HVA. try clear A0. try clear VAHI. try clear BS0.

intros until buf. intros ST BUF OK MI SEP P0 Hn ISHm SZ. unfold PC_DEPTH, GLOBALS_TOP in *.
pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
pose proof (memchr_len_bound 0 n buf ltac:(lia)) as [LB _].
destruct ISHm as (ASH & RC & SB).
assert (Eq : bv_unsigned SPv = (q + -544)%Z) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (strnlen_icpt_spec P n lo buf ra' SPv gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Ft fc m);
rewrite ?Eq.
all: first [exact ST | exact BUF | exact OK | exact MI | exact SB | exact RC | apply (rng_ok_of_ash _ _ _ ASH SZ ltac:(lia))
| idtac; lia | unfold STRNLEN_ICPT_STACK, STRNLEN_STACK, MEMCHR_ICPT_STACK; lia | lia]. }
cbv beta. intros ms' PS. unfold strnlen_post in PS. rewrite !Eq in PS.
destruct PS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & BUF').
repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. exact BUF'.
Qed.

Lemma memchr_len_cstr : forall n (str slack : list byte), ~ In (Z_to_bv 8 0) str -> (Z.of_nat (length str) < n)%Z ->
memchr_len 0 n (str ++ Z_to_bv 8 0 :: slack) = (Z.of_nat (length str) + 1)%Z.
Proof. clear. intros n str slack NN Hn. unfold memchr_len. rewrite (find_byte_cstr 0 n str slack NN Hn). reflexivity. Qed.
Lemma memchr_len_cstr_le : forall n (str slack : list byte), ~ In (Z_to_bv 8 0) str -> (0 <= n)%Z ->
(0 <= memchr_len 0 n (str ++ Z_to_bv 8 0 :: slack) <= Z.of_nat (length str) + 1)%Z.
Proof.
clear. intros n str slack NN Hn. unfold memchr_len. destruct (Z.lt_ge_cases (Z.of_nat (length str)) n) as [H|H].
- rewrite (find_byte_cstr 0 n str slack NN H). lia.
- rewrite (find_byte_cstr_short 0 n str slack NN H). lia.
Qed.
Lemma zb_nonul : forall s, Forall (fun c => 0 < c < 256)%Z s -> ~ In (Z_to_bv 8 0) (zb s).
Proof.
clear. intros s HF IN. unfold zb in IN. apply in_map_iff in IN. destruct IN as (c & E & Hc).
apply (proj1 (Forall_forall _ s) HF) in Hc.
assert (E' : bv_unsigned (Z_to_bv 8 c) = bv_unsigned (Z_to_bv 8 0)) by (rewrite E; reflexivity).
rewrite u8_lit in E' by lia. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z in E'. lia.
Qed.

Definition out_postq (ra' : word) (Ft : bvmap 5 word) (fc : bv 32) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(S : Z) (bs : list Z) (m : word -> option byte) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
ms' = MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra') fc None m' (seg_rom asegs)
/\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (q + -544)
/\ SINK m' st'
/\ ssp_cells m' canary
/\ bytes_at asegs m' S (zb bs).
Lemma out_callq : forall ra' t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (st : St) (S L : Z) (bs : list Z),
SINK m st -> bytes_at asegs m S (zb bs) -> Forall (fun c => 0 <= c < 256)%Z bs -> L = zlength bs ->
stk asegs m lo (q + -544) -> ssp_cells m canary -> mem_inv asegs m ->
(0 <= S)%Z -> (S < 2^64)%Z ->
(S + zlength bs <= lo \/ q + -544 <= S)%Z -> (S + zlength bs <= Fp \/ Fp + 232 <= S)%Z -> (S + zlength bs <= B \/ B + BS <= S)%Z ->
(zlength bs < 2^31)%Z ->
szone S (zlength bs) ->
(S + zlength bs <= 2^47)%Z ->
implM asegs (OUT bs) st (out_postq ra' Ft fc s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 S bs m)
(MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) FPv a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 0xd5a8c) fc None m (seg_rom asegs)).
Proof using Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0.    try clear SFR. try clear SFL. try clear HF. try clear FRM0. try clear HA. try clear HVA. try clear A0. try clear VAHI.

intros until bs. intros HS SRC RNG -> ST SSP MI HS0 HS1 D1 D2 D3 LB SZ HT. unfold PC_DEPTH, GLOBALS_TOP in *.
pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite zb_length in SB. unfold zlength in *.
assert (Eq : bv_unsigned SPv = (q + -544)%Z) by (apply unsigned_lit; lia).
assert (Es : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
pose proof HOUT as HO. unfold out_stmt in HO.
specialize (HO ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length bs))) FPv a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Ft fc m st bs lo canary).
rewrite !Eq, !Es in HO.
eapply implM_mono.
{ apply HO; try assumption; try reflexivity; unfold OUT_DEPTH, zlength; try lia.
eapply TOK; [|exact TQ]. lia. }
cbv beta. intros [] st' ms' P. unfold out_post, SR in P. rewrite !Eq in P. exact P.
Qed.

Definition fp_postq (ra' : word) (Ft : bvmap 5 word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(m : word -> option byte) : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
ms' = MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft' (ret_pc ra') fc' None m' (seg_rom asegs)
/\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc' /\ Fokd Ft Ft'
/\ stk asegs m' lo (q + -544)
/\ SINK m' st'
/\ ssp_cells m' canary.
Lemma fp_callq : forall ra' t0 t1 t2 s0 s1 (a1 a2 a7 : word) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (st : St) (y w p fl t : Z),
fpcall_stmt Fp B BS SINK TOPOK OUTFP (y, w, p, fl, t) ->
SINK m st -> y = (bv_unsigned a1 + 2^64 * bv_unsigned a2)%Z -> bv_unsigned a7 <> 5%Z ->
(-2^31 <= w <= 1)%Z -> (-2^31 <= p < 2^20)%Z -> (0 <= fl < 2^32)%Z -> (0 <= t < 256)%Z -> Z.lor t 32 <> 97%Z ->
stk asegs m lo (q + -544) -> ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
implM asegs (OUTFP y w p fl t) st (fp_postq ra' Ft s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 FPv a1 a2 (Z_to_bv 64 w) (Z_to_bv 64 p) (Z_to_bv 64 fl) (Z_to_bv 64 t) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 0xd7108) fc None m (seg_rom asegs)).
Proof using Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP.    try clear SFR. try clear SFL. try clear HOUT. try clear HF. try clear FRM0. try clear HA. try clear HVA. try clear A0. try clear VAHI. try clear BS0.

intros until t. intros FPC HS Hy H7 Hw Hp Hfl Ht Hta ST SSP MI FRM. unfold PC_DEPTH, GLOBALS_TOP in *.
assert (Eq : bv_unsigned SPv = (q + -544)%Z) by (apply unsigned_lit; lia).
cbn [fpcall_stmt] in FPC.
specialize (FPC ra' SPv gp tp t0 t1 t2 s0 s1 FPv a1 a2 (Z_to_bv 64 w) (Z_to_bv 64 p) (Z_to_bv 64 fl) (Z_to_bv 64 t) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Ft fc m st lo canary).
rewrite !Eq in FPC.
eapply implM_mono.
{ apply FPC; try assumption; try reflexivity; unfold FMT_FP_DEPTH; try lia.
eapply TOK; [|exact TQ]. lia. }
cbv beta. intros r st' ms' P. unfold fpcall_post, SR in P. rewrite !Eq in P. exact P.
Qed.

Lemma conv_type_dbl : forall t, conv_type t = Some T_DBL -> (69 <= t <= 103)%Z /\ Z.lor t 32 <> 97%Z.
Proof.
clear. intros t CT. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL in CT.
repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [try discriminate CT|] end; try discriminate CT.
Qed.

Ltac solve_szone :=
lazymatch goal with |- szone ?p ?n =>
first [ match goal with H : szone p _ |- _ => eapply szone_sub; [exact H| lia| glo_lia| glo_lia] end
| match goal with H : _ /\ szone p _ |- _ => eapply szone_sub; [exact (proj2 H)| lia| glo_lia| glo_lia] end
| lazymatch p with
| (q + _)%Z => unfold szone; right; idtac; glo_lia
| q => unfold szone; right; idtac; glo_lia
| _ => first [ match goal with H : _ /\ szone ?a _ |- _ => eapply szone_sub; [exact (proj2 H)| glo_lia| glo_lia| glo_lia] end
| unfold szone; left; glo_lia
| unfold szone; right; idtac; glo_lia ]
end
| match goal with |- ?g => idtac "solve_szone FAILED on" g; fail end ]
end.

Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 954256 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 6575456 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | |
| solve_szone
|  try (solve [unfold zlength, zrepeat in *; rewrite ?repeat_length, ?Z2Nat.id by lia; lia]) ]
| cbv beta ].

Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call asegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := idtac.

Definition S_EXIT : Prop :=
forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
(pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 apv] ->
frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
evt asegs (POST r st)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6eac) fc None m (seg_rom asegs)).

Definition S_SCAN : Prop :=
forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i n cnt' : Z) (Q : machine_state -> Prop),
let _ := ctx_all in
finv m ->
(0 <= i)%Z -> (0 <= n)%Z -> (i + n < zlength fmt)%Z ->
(forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z ->
(znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z ->
(0 < n \/ znth fmt i = 37)%Z ->
(0 <= cnt' <= INT_MAX)%Z -> (n <= INT_MAX - cnt')%Z ->
(forall a1 a2 : word,
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - cnt')) (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) (Z_to_bv 64 n) (Z_to_bv 64 (A + i)) x24 x25 (Z_to_bv 64 n) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd61f8) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt i)) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 cnt') x20 x21 x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd619c) fc None m (seg_rom asegs)).

Definition S_FLAGS : Prop :=
forall (x1 x6 x7 x10 x11 x12 x15 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(p k fl b : Z) (w3 : word) (FL : Z) (s1 : list Z),
let _ := ctx_all in
finv m -> (0 <= p)%Z -> (1 <= k)%Z -> (p + k <= zlength fmt)%Z ->
bv_unsigned w3 = b -> (0 <= fl < 131072)%Z -> (0 <= b < 131072)%Z ->
parse_flags (sfx (p + k)) (Z.lor fl b) = (FL, s1) -> s1 <> [] ->
(forall (k' c' : Z) (a3 a4 a5 : word),
(p + k <= k' < zlength fmt)%Z -> s1 = sfx k' -> c' = znth fmt k' -> flag_bit c' = None -> (0 <= FL < 131072)%Z ->
evt asegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 c') (Z_to_bv 64 (A + k')) a3 a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 32)
x18 x19 x20 x21 x22 x23 (Z_to_bv 64 FL) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd62b0) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 w3 (Z_to_bv 64 (A + p + k)) x15 (Z_to_bv 64 1) (Z_to_bv 64 32)
x18 x19 x20 x21 x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd628c) fc None m (seg_rom asegs)).

Definition S_WLOOP : Prop :=
forall (x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(pos acc w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (w, s2) -> s2 <> [] ->
(forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
(pos < k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
evt asegs Q
(MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd63e0) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) x12 (Z_to_bv 64 (A + pos)) x14 x15 x16 x17
x18 x19 x20 x21 (Z_to_bv 64 acc) x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6344) fc None m (seg_rom asegs)).

Definition S_WIDTH : Prop :=
forall (x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(k1 w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= k1 < zlength fmt)%Z ->
getint (sfx k1) 0 = Some (w, s2) -> s2 <> [] ->
(forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
(k1 <= k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
evt asegs Q
(MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd63e0) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd62f8) fc None m (seg_rom asegs)).

Definition S_PLOOP : Prop :=
forall (x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(pos acc p : Z) (s3 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (p, s3) -> s3 <> [] ->
(forall (k3 : Z) (a1 a3 a4 : word),
(pos < k3 < zlength fmt)%Z -> s3 = sfx k3 -> is_digit (znth fmt k3) = false -> (0 <= p <= INT_MAX)%Z ->
evt asegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6518) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) (Z_to_bv 64 (A + pos)) x13 x14 x15 (Z_to_bv 64 10) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 acc) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd64a4) fc None m (seg_rom asegs)).

Definition S_PREC : Prop :=
forall (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(k2 k3 p : Z) (xp : bool) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= k2 < zlength fmt)%Z ->
( (znth fmt k2 <> 46 /\ p = -1 /\ xp = false /\ k3 = k2)
\/ (znth fmt k2 = 46 /\ xp = true /\ k2 + 1 < zlength fmt /\ znth fmt (k2 + 1) <> 42
/\ getint (sfx (k2 + 1)) 0 = Some (p, sfx k3) /\ k2 + 1 <= k3 < zlength fmt) )%Z ->
(forall (a1 a3 a4 : word),
(-1 <= p <= INT_MAX)%Z ->
evt asegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6518) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 (Z_to_bv 64 (A + k2)) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd63e0) fc None m (seg_rom asegs)).

Definition S_STATE : Prop :=
forall (x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(k3 ty : Z),
let _ := ctx_all in
finv m -> (0 <= k3 < zlength fmt)%Z -> conv_type (znth fmt k3) = Some ty ->
(forall (a2 a3 : word),
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 ty) a2 a3 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 (Z_to_bv 64 (A + k3 + 1)) x22 x23 x24 x25 x26 (Z_to_bv 64 0) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6598) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 (A + k3)) x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6518) fc None m (seg_rom asegs)).

Definition S_DIR : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(i : Z) (d : dir) (rest : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= i)%Z -> (i + 1 <= zlength fmt)%Z ->
parse_dir (sfx (i + 1)) = Some (d, rest) ->
(forall (k4 : Z) (a2 a3 a4 t1 : word),
(i + 1 < k4 <= zlength fmt)%Z -> rest = sfx k4 -> znth fmt (k4 - 1) = d_t d ->
(0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
evt asegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) a2 a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 (Z_to_bv 64 (A + k4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6598) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd621c) fc None m (seg_rom asegs)).

Definition S_END : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
(pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 apv] ->
frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
evt asegs (POST r st)
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) FPv x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6d54) fc None m (seg_rom asegs)).

Definition S_HEAD (fuel : nat) : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i cnt l k : Z) (args : list parg)
(pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i) args) ->
frm0 fc -> Fok Ft ->
(0 <= i)%Z -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l <= INT_MAX)%Z ->
implM asegs (printf_loop OUT OUTFP fuel (sfx i) args (cnt + l)) st POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 cnt) FPv (Z_to_bv 64 (A + i)) x22 x23 x24 x25 (Z_to_bv 64 l) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6180) fc None m (seg_rom asegs)).

Definition S_CONV : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (d : dir) (a : parg) (args : list parg)
(pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) (a :: args) ->
match a with PA_g dd =>
fpcall_stmt Fp B BS SINK TOPOK OUTFP
(dd, d_w d, d_p d, (if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD))%Z, d_t d)
| _ => True end ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(1 <= i4 <= zlength fmt)%Z -> znth fmt (i4 - 1) = d_t d -> conv_type (d_t d) = Some (d_ty d) ->
(0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
((d_xp d = false /\ d_p d = -1) \/ (d_xp d = true /\ 0 <= d_p d <= INT_MAX))%Z ->
(0 <= c <= INT_MAX)%Z ->
implM asegs (cnt' <- conv OUT OUTFP c d a ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) x12 x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6598) fc None m (seg_rom asegs)).

Definition body_loc (BA n : Z) : Prop :=
(((q + -392 <= BA /\ BA + n <= q + -368)
\/ ((BA + n <= lo \/ q <= BA) /\ (BA + n <= Fp \/ Fp + 232 <= BA) /\ (BA + n <= B \/ B + BS <= BA)))
/\ szone BA n)%Z.

Definition S_TAIL : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (prefix body : list Z) (BA PFXA : Z)
(s2s za plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
bytes_at asegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> body_loc BA (zlength body) -> (BA + zlength body <= 2^47)%Z -> (zlength body <= INT_MAX)%Z ->
(forall m', mem_inv asegs m' -> bytes_at asegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(65536 <= PFXA)%Z -> (PFXA + zlength prefix <= 143552)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
implM asegs (cnt' <- conv_tail OUT c fl w p prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 (Z_to_bv 64 (BA + zlength body)) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6a1c) fc None m (seg_rom asegs)).

Definition tregs (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 t3 t4 t5 t6 : word) (i4 c w BA wq pq : Z) : bvmap 5 word :=
mkR xra SPv gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) s8 s9 (Z_to_bv 64 wq) (Z_to_bv 64 pq) t3 t4 t5 t6.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
Definition tinv (m : word -> option byte) (st : St) (k i4 : Z) (args : list parg) (fuel : nat)
(PFXA fl n pl pq BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte) : Prop :=
finv m
/\ rw_cells asegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) (Z_to_bv 64 (Z.land fl 73728)) (Z_to_bv 64 n) (Z_to_bv 64 pl) (Z_to_bv 64 (pl + pq)) (Z_to_bv 64 0) alo ahi j128)
/\ rw_cells asegs m (q + -392) [CB 24 digs]
/\ rw_cells asegs m (q + -368) [CB 256 pad]
/\ SINK m st /\ rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] /\ (0 <= k)%Z
/\ args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args
/\ Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args)
/\ bytes_at asegs m BA (zb body) /\ Forall (fun c => 0 <= c < 256)%Z body /\ body_loc BA n /\ (BA + n <= 2^47)%Z /\ n = zlength body
/\ (forall m', mem_inv asegs m' -> bytes_at asegs m' PFXA (zb prefix)) /\ Forall (fun c => 0 <= c < 256)%Z prefix
/\ (65536 <= PFXA)%Z /\ (PFXA + pl <= 143552)%Z /\ pl = zlength prefix /\ (pl <= 2)%Z
/\ (0 <= i4 <= zlength fmt)%Z /\ (0 <= fl < 131072)%Z /\ (0 <= n <= INT_MAX)%Z /\ (n <= pq)%Z /\ (pl + pq <= INT_MAX)%Z.

Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp);
pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.

Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.

Definition S_T6 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM asegs (mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0xd6c38) fc None m (seg_rom asegs)).

Definition S_T5 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM asegs (OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0xd6c1c) fc None m (seg_rom asegs)).

Definition S_T4 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM asegs (mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0xd6b98) fc None m (seg_rom asegs)).

Definition S_T3 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM asegs (mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0xd6b10) fc None m (seg_rom asegs)).

Definition S_T2 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM asegs (OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0xd6af4) fc None m (seg_rom asegs)).

Definition S_T1 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
Z.land fl 73728 = 0%Z ->
implM asegs (mpad OUT 32 wq (pl + pq) fl ;;; OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0xd6a74) fc None m (seg_rom asegs)).

Definition S_INTC2 : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p argi : Z) (prefix body : list Z) (BA PFXA : Z)
(s2s za plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
bytes_at asegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
(forall m', mem_inv asegs m' -> bytes_at asegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(65536 <= PFXA)%Z -> (PFXA + zlength prefix <= 143552)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
(0 <= argi < 2^64)%Z ->
implM asegs (cnt' <- (if ((argi =? 0) && (p =? 0))%Z then conv_tail OUT c fl w p prefix []
else conv_tail OUT c fl w (Z.max p (zlength body + (if (argi =? 0)%Z then 1 else 0))) prefix body) ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd69e4) fc None m (seg_rom asegs)).

Definition S_INTC : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) (BA PFXA : Z)
(s2s za plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
bytes_at asegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
(forall m', mem_inv asegs m' -> bytes_at asegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(65536 <= PFXA)%Z -> (PFXA + zlength prefix <= 143552)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= argi < 2^64)%Z ->
implM asegs (cnt' <- conv_int OUT c fl w p xp argi prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd69cc) fc None m (seg_rom asegs)).

Definition dloop_post (x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (a2 a3 : word) (xq : Z) (W : list Z) (m' : word -> option byte),
ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xq) (Z_to_bv 64 (q + -392 + (j - zlength W))) a2 a3
(Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength W))) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd69b4) fc None m' (seg_rom asegs)
/\ munch [(q + -392, q + -368)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength W)) ds ++ zb W ++ skipn (Z.to_nat j) ds)]
/\ (1 <= xq <= 9)%Z /\ dec_digits x = (48 + xq)%Z :: W /\ (zlength W + 1 <= j)%Z.
Definition S_DLOOP : Prop :=
forall (x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x j : Z) (ds : list byte),
let _ := ctx_all in
mem_inv asegs m -> rw_cells asegs m (q + -392) [CB 24 ds] ->
(10 <= x < 2^64)%Z -> (zlength (dec_digits x) <= j <= 24)%Z -> x11 = Z_to_bv 64 (q + -392 + j) ->
evt asegs (dloop_post x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc x j ds m)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) x11 x12 x13
(Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd697c) fc None m (seg_rom asegs)).

Definition S_FMTU2 : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (x d jj : Z) (W prefix : list Z) (PFXA : Z)
(pfx s2s za plp ahi : word) (j128 pre pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 (pre ++ zb W)] -> zlength pre = jj -> (1 <= jj)%Z ->
((d = 0 /\ W = [] /\ dec_digits x = []) \/ (1 <= d <= 9 /\ dec_digits x = (48 + d) :: W))%Z ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(forall m', mem_inv asegs m' -> bytes_at asegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(65536 <= PFXA)%Z -> (PFXA + zlength prefix <= 143552)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= x < 2^64)%Z ->
implM asegs (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 d) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 PFXA)
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 (q + -392 + jj)) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd69b4) fc None m (seg_rom asegs)).

Definition S_FMTU : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (x : Z) (prefix : list Z) (PFXA : Z)
(pfx s2s za plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(forall m', mem_inv asegs m' -> bytes_at asegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(65536 <= PFXA)%Z -> (PFXA + zlength prefix <= 143552)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= x < 2^64)%Z ->
implM asegs (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 x) x11 x12 x13 (Z_to_bv 64 10) x15 x16 (Z_to_bv 64 PFXA)
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd696c) fc None m (seg_rom asegs)).

Definition S_CV_D : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (i : Z)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (i mod 2^64)) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(-2^31 <= i < 2^31)%Z ->
implM asegs (cnt' <- (let '(argi, prefix) :=
(if INTMAX_MAX <? i mod 2^64 then ((- (i mod 2^64)) mod 2^64, [45])
else if negb (Z.land fl MARK_POS =? 0) then (i mod 2^64, [43])
else if negb (Z.land fl PAD_POS =? 0) then (i mod 2^64, [32])
else (i mod 2^64, []))%Z in
conv_int OUT c fl w p xp argi prefix (dec_digits argi)) ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6668) fc None m (seg_rom asegs)).

Definition S_CV_U : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (u : Z)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= u < 2^32)%Z ->
implM asegs (cnt' <- conv_int OUT c fl w p xp u [] (dec_digits u) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd67a0) fc None m (seg_rom asegs)).

Definition xloop_post (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (l x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (a2 a3 : word) (m' : word -> option byte),
let H := hex_digits l x in
ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 l) a2 a3 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength H))) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6858) fc None m' (seg_rom asegs)
/\ munch [(q + -392, q + -368)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength H)) ds ++ zb H ++ skipn (Z.to_nat j) ds)]
/\ (zlength H <= j)%Z.
Definition S_XLOOP : Prop :=
forall (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (l x j : Z) (ds : list byte),
let _ := ctx_all in
mem_inv asegs m -> rw_cells asegs m (q + -392) [CB 24 ds] ->
(0 < x < 2^64)%Z -> (l = 0 \/ l = 32)%Z -> (zlength (hex_digits l x) <= j <= 24)%Z -> x23 = Z_to_bv 64 (q + -392 + j) ->
evt asegs (xloop_post x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc l x j ds m)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) (Z_to_bv 64 l) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6830) fc None m (seg_rom asegs)).

Definition S_CV_X : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (u t : Z)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= u < 2^32)%Z -> (t = 120 \/ t = 88)%Z ->
implM asegs (cnt' <- conv_int OUT c fl w p xp u
(if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0) then (if t =? 120 then [48; 120] else [48; 88]) else [])%Z
(hex_digits (Z.land t 32) u) ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6818) fc None m (seg_rom asegs)).

Definition S_CV_S : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p fl10 : Z) (xp : bool) (P : Z) (s : list Z) (slack : list byte)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 P) ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
bytes_at asegs m P (zb s ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256)%Z s ->
((- (P + zlength s + 1)) mod 8 <= zlength slack)%Z -> (0 < P)%Z ->
szone P (zlength s + 1) ->
(P + zlength s + 1 + zlength slack <= lo \/ q <= P)%Z ->
(P + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= P)%Z ->
(P + zlength s + 1 + zlength slack <= B \/ B + BS <= P)%Z ->
(P + zlength s + 1 + zlength slack <= 2^47)%Z ->
(fl10 = Z.land fl (Z.lnot 65536))%Z ->
implM asegs (cnt' <- (if (p <? 0) && (INT_MAX <=? zlength s) then munr
else conv_tail OUT c (Z.land fl (Z.lnot ZERO_PAD)) w (if p <? 0 then zlength s else Z.min (zlength s) p) []
(firstn (Z.to_nat (if p <? 0 then zlength s else Z.min (zlength s) p)) s))%Z ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) (Z_to_bv 64 fl10) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd66b0) fc None m (seg_rom asegs)).

Definition S_CV_FP : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (y t : Z)
(pfx s2s za pl plp : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 (hi64 y)) j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
fpcall_stmt Fp B BS SINK TOPOK OUTFP (y, w, p, fl, t) ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= y < 2^128)%Z -> conv_type t = Some T_DBL ->
implM asegs (cnt' <- (if xp && (p <? 0) then munr
else if (1 <? w) || (2^20 <=? p) then munr
else r <- OUTFP y w p fl t ;; if (r <? 0) || (INT_MAX - c <? r) then munr else mret (c + r))%Z ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6618) fc None m (seg_rom asegs)).

Definition POST1 : Z -> machine_state -> Prop :=
fun r ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F (ret_pc ra) fc0 None m' (seg_rom asegs)
/\ munch [(lo, q)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
/\ stk asegs m' lo q
/\ ssp_cells m' canary.

Definition S_EXIT1 : Prop :=
forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(m : word -> option byte) (r : Z)
(pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m -> munch [(lo, q)] m0 m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
(0 <= r < 2^64)%Z ->
evt asegs (POST1 r)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6eac) fc0 None m (seg_rom asegs)).

Definition S_P1 : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
(m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m -> munch [(lo, q)] m0 m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
pass1_ok fmt = true ->
evt asegs (POST1 0)
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 A) x22 x23 x24 x25 (Z_to_bv 64 0) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6180) fc0 None m (seg_rom asegs)).

Definition S_PRO : Prop :=
forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (f : Z) (Q : machine_state -> Prop),
let _ := ctx_all in
stk asegs m0 lo q -> mem_inv asegs m0 -> bytes_at asegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
(0 <= f < 2^64)%Z ->
(forall (m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte) (a0 a1 a2 a3 : word),
finv m -> munch [(q + -544, q)]%Z m0 m ->
rw_cells asegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells asegs m (q + -392) [CB 24 digs] ->
rw_cells asegs m (q + -368) [CB 256 pad] ->
evt asegs Q
(MS (mkR ra SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 nlt x15 x16 x17
s2e (Z_to_bv 64 0) (Z_to_bv 64 f) (Z_to_bv 64 A) s6e s7e s8e s9e (Z_to_bv 64 0) s11e x28 x29 x30 x31)
F (Z_to_bv 64 0xd6180) fc0 None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 f) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
F (Z_to_bv 64 0xd60d0) fc0 None m0 (seg_rom asegs)).

Unset Keyed Unification.
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia | glo_lia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; glo_lia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Hypothesis HS_CV_D : S_CV_D.
Hypothesis HS_CV_U : S_CV_U.
Hypothesis HS_CV_X : S_CV_X.
Hypothesis HS_CV_S : S_CV_S.
Hypothesis HS_CV_FP : S_CV_FP.

Lemma L_CONV : S_CONV.
Proof using BS0 GLO HA HAP HF HS_CV_D HS_CV_FP HS_CV_S HS_CV_U HS_CV_X HVA LO QHI SEP_B SEP_F SFL SFR VAHI BAND.
intros fuel HH x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c d a args pfx s2s za pl plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Ht CT Hfl Hw Hp XP Hc.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.

cbn [args_ok] in AOK. destruct (skipn (Z.to_nat k) slots) as [|slot slots'] eqn:ESK; [destruct AOK|]. destruct AOK as [AOK1 AOK].
assert (NTH : nth_error slots (Z.to_nat k) = Some slot).
{ rewrite <- (Nat.add_0_r (Z.to_nat k)), <- nth_error_skipn, ESK. reflexivity. }
assert (ESK' : skipn (Z.to_nat (k + 1)) slots = slots').
{ replace (Z.to_nat (k + 1)) with (1 + Z.to_nat k)%nat by lia. rewrite <- skipn_skipn, ESK. reflexivity. }
rewrite <- ESK' in AOK.
destruct (lo_split _ _ _ _ _ _ _ _ _ _ LOW) as (LOW14 & ARGC & J128). unfold lo_cells14, ssp_guard in LOW14. clear LOW.
pose proof (conv_type_cases _ _ CT) as CASES. pose proof (conv_type_range _ _ CT) as TR.
pose proof (land_bound' (d_fl d) 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq (d_fl d)) in FLB by lia.
unfold conv. cbv zeta. unfold LEFT_ADJ, ZERO_PAD.

destruct (Z.eq_dec (d_ty d) T_DBL) as [EDBL|NDBL].
{ destruct a as [sv | iv | uv | dd];
[ destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [exfalso; unfold T_PTR, T_DBL in *; lia | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [exfalso; unfold T_INT, T_DBL in *; lia | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [exfalso; unfold T_UINT, T_DBL in *; lia | cbn [negb]; apply implM_unr_l]
| cbv zeta; apply implM_unr_l ]. }

ienter; zs; br K; zs; zs; zs; zs.
callx (eapply pop_arg_callq; [lia | exact APC | exact VAA | exact NTH | lia | exact ARGC | exact ST | exact MI | unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, NDBL |- *; (first [ clear - K NDBL CASES LU LZB d HAP SEP_F GLO LO slots VA AP fmt lo q Fp BAND; lia | lia ])]).
match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rename H into ARGC' end.
match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
zs.
match goal with H : SINK ?mm _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (SFL _ _ H) as (fb & FLC & FB & ISHm) end; zs; zs; zs; br K1; clear FLC.
rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht.
zsto 0xd65d4%Z; change (Z.b2z (0 <? 0)) with 0%Z; rewrite Z.land_0_l; zs; br K2a; zsto 0xd65e8%Z; rewrite (nzmask_eq (d_fl d)) by lia; zs; brf K2;
[ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
| assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; lia);
rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ].
all: zsto 0xd65f8%Z; zs; br K3; zsto 0xd660c%Z.
all: replace (Z.shiftl (d_t d + -65) 2 + 160120)%Z with (160120 + 4 * (d_t d - 65))%Z by (rewrite Z.shiftl_mul_pow2; lia).

all: apply evt_done.
all: destruct a as [sv | iv | uv | dd];
[ destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
|  cbv zeta; apply implM_unr_l ].
all: try (match goal with ETY : d_ty ?dd = T_PTR |- _ => assert (T115 : d_t dd = 115%Z) by (clear - CASES ETY; unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia) end).
all: try (match goal with ETY : d_ty ?dd = T_INT |- _ => assert (TDI : (d_t dd = 100 \/ d_t dd = 105)%Z) by (clear - CASES ETY; unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia) end).
all: try (match goal with ETY : d_ty ?dd = T_UINT |- _ =>
assert (TUX : (d_t dd = 117 \/ (d_t dd = 120 \/ d_t dd = 88))%Z) by (clear - CASES ETY; unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia);
destruct TUX as [T117 | TX];
[ rewrite (proj2 (Z.eqb_eq _ _) T117) | replace (d_t dd =? 117)%Z with false by (symmetry; apply Z.eqb_neq; (first [ clear - TX K NDBL LU LZB d HAP SEP_F GLO LO slots VA AP fmt lo q Fp BAND; lia | lia ])) ] end).
all: match goal with H : rw_cells _ _ (q + -544 + 112)%Z _, ETY : d_ty ?dd = _ |- _ => rewrite ETY in H; cbn [pop_arg_lo pop_arg_hi QoBx.Mq0.T_PTR QoBx.Mq0.T_INT QoBx.Mq0.T_UINT QoBx.Mq0.T_DBL T_PTR T_INT T_UINT T_DBL Z.eqb Pos.eqb] in H end.
all: ienter.
all: first [ the_mi ltac:(fun M => pose proof (jt1_read_s _ _ M T115) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_d _ _ M TDI) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_x _ _ M TX) as RD1) ].
all: zs; zs; zs.

all: let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end.
all: assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; (first [ clear - LU LZB Hfl d slots fmt BAND FLB; lia | lia ])).
all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mm _) =>
lazymatch pc with
| 878256%Z =>
rewrite <- (Z_to_bv_bv_unsigned slot) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
match goal with MUc : munch _ m0 mm |- _ =>
destruct (arg_ok_W _ _ _ _ AOK1 MUc) as (slack & STR & SRNG & SPAD & P0 & SZS & SD1 & SD2 & SD3 & SD4 & SD5) end;
stmt (HS_CV_S fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
(xp := d_xp d) (P := bv_unsigned slot) (s := sv) (slack := slack));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | exact P0 | exact SZS | exact SD1 | exact SD2 | exact SD3 | exact SD5
| subst fl'; rewrite ?land_land_same; reflexivity ]
| 878184%Z =>
destruct AOK1 as [Hiv Emod];
rewrite (sx32_int slot iv Hiv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_D fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (i := iv));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Hiv ]
| 878496%Z =>
destruct AOK1 as [Huv Emod];
rewrite (zx32_uint slot uv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_U fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Huv ]
| 878616%Z =>
destruct AOK1 as [Huv Emod];
rewrite (zx32_uint slot uv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_X fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv) (t := d_t d));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Huv | exact TX ]

end end.
Qed.

Set Keyed Unification.
Hypothesis HS_FMTU : S_FMTU.

Lemma fl_shl52 : forall fl, (0 <= fl < 131072)%Z ->
(Z.land (Z.shiftl fl 52) 18446744073709551615 < 9223372036854775808 <-> Z.land fl 2048 = 0)%Z.
Proof using .
clear. intros fl Hfl. rewrite Z.shiftl_mul_pow2 by lia.
change 2048%Z with (2^11)%Z. rewrite zb_land_pow2 by lia.
change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
split; intros H; Z.div_mod_to_equations; nia.
Qed.

Lemma L_CV_D : S_CV_D.
Proof using BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR BAND.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp i pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hi.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
stmt (HS_FMTU fuel HH) as NX.
pose proof (Z.mod_pos_bound i (2^64) ltac:(lia)) as RA.
set (argi := (i mod 2^64)%Z) in *.
unfold INTMAX_MAX, MARK_POS, PAD_POS.
ienter.
zs. zs. brf K1.
-
zs. zs. zs. zs. zs. zs. zs. zs.
replace (Z_to_bv 64 (0 - argi)) with (Z_to_bv 64 ((- argi) mod 2 ^ 64)) in * by (apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; f_equal; lia).
replace (9223372036854775807 <? argi)%Z with true by (symmetry; apply Z.ltb_lt; lia).
pose proof (Z.mod_pos_bound (- argi) (2^64) ltac:(lia)) as RB.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := ((- argi) mod 2 ^ 64)%Z) (prefix := [45%Z]) (PFXA := 69023%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; exact (pfx_sub mq 0 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
- replace (9223372036854775807 <? argi)%Z with false by (symmetry; apply Z.ltb_ge; lia).
zs. zs. zs. zs. zs. brf K2.
+
assert (HM : Z.land fl 2048 <> 0%Z) by (intros E; apply (proj2 (fl_shl52 fl Hfl)) in E; lia).
replace (Z.land fl 2048 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact HM). cbn [negb].
zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [43%Z]) (PFXA := 69024%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; exact (pfx_sub mq 1 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
+ assert (HM : Z.land fl 2048 = 0%Z) by (apply (proj1 (fl_shl52 fl Hfl)); lia).
replace (Z.land fl 2048 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact HM). cbn [negb].
zs. zs. zs. zs. zs.
pose proof (land_bound' fl 1 ltac:(lia) ltac:(lia)) as B1.
assert (C1 : (Z.land fl 1 = 0 \/ Z.land fl 1 = 1)%Z).
{ pose proof (Z.land_ones fl 1 ltac:(lia)) as E. change (Z.ones 1) with 1%Z in E. change (2^1)%Z with 2%Z in E. rewrite E.
pose proof (Z.mod_pos_bound fl 2 ltac:(lia)). lia. }
destruct C1 as [E1 | E1]; rewrite E1 in *.
*
cbn [Z.eqb negb Z.mul Z.add].
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := []) (PFXA := 69023%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
*
cbn [Z.eqb negb Z.mul Z.add].
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [32%Z]) (PFXA := 69025%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; exact (pfx_sub mq 2 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
Qed.

Set Keyed Unification.

Lemma L_CV_FP : S_CV_FP.
Proof using GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ BAND BS0.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp y t pfx s2s za pl plp j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Hfl Hw Hc XP Hy CT.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (conv_type_dbl t CT) as [Ht Hta].
pose proof (lo64_range y) as RL. pose proof (hi64_range y) as RH.
ienter.

assert (XF : (xp && (p <? 0))%bool = false).
{ destruct XP as [[-> ->] | [-> Hp]]; [reflexivity|]. cbn [andb]. apply Z.ltb_ge. lia. }
rewrite XF.
destruct XP as [[-> ->] | [-> Hp]]; cbn [Z.b2z];
[ zs; zs; rewrite Z.land_0_l; zs; if_lit
| zs; zs;
replace (Z.lxor p 9223372036854775808 <? 9223372036854775808)%Z with false
by (symmetry; apply Z.ltb_ge; change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; lia);
cbn [Z.b2z Z.land]; zs; if_lit ].

all: destruct (Z.ltb_spec0 1 w) as [W1|W1]; [cbn [orb]; ileave; apply implM_unr_l|].
all: match goal with |- context [if (?a || ?b)%bool then munr else _] =>
destruct b eqn:P20; [ileave; apply implM_unr_l | cbn [orb]] end.
all: match goal with P20 : (?a <=? ?pp)%Z = false |- _ => apply Z.leb_gt in P20 end.
all: zs; zs; zs; zs; zs; zs; zs; zs.
all: ileave; massoc; eapply implM_bind;
[ eapply fp_callq;
[ exact FPC1 | exact HS | rewrite !unsigned_lit by lia; symmetry; apply lo64_hi64; lia | rewrite unsigned_lit by lia; lia | lia | lia | lia | lia | exact Hta
| exact ST | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | exact MI | exact FRM ]
| cbv beta ].
all: intros r st'; lazymatch goal with |- context [fp_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => post_call asegs mm end.
all: try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end).
all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
all: unfold INT_MAX in *.

all: destruct (Z.lt_ge_cases r 0) as [RN|RP];
[ replace ((r <? 0) || (2147483647 - c <? r))%bool with true by (symmetry; apply orb_true_iff; left; apply Z.ltb_lt; exact RN); apply implM_unr_l | ].
all: destruct (Z.lt_ge_cases 2147483647 r) as [RB|RS];
[ replace ((r <? 0) || (2147483647 - c <? r))%bool with true by (symmetry; apply orb_true_iff; right; apply Z.ltb_lt; lia); apply implM_unr_l | ].
all: replace (r <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia); cbn [orb].
all: destruct (Z.ltb_spec0 (2147483647 - c) r) as [OV|OV]; [apply implM_unr_l|].
all: apply implM_ret_l.
all: ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
all: zs; zs; brf KR; [ | exfalso; try rewrite unsigned_lit in KR by lia; try rewrite land_M64_id in KR by lia; lia ].
all: stmt HH as NXH.
all: jumpM (eapply NXH with (i := i4) (cnt := c) (l := r) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; hyp | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC
| assumption | exact FOK2 | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Unset Keyed Unification.
Hypothesis HS_TAIL : S_TAIL.

Lemma L_CV_S : S_CV_S.
Proof using BS0 GLO HA HAP HS_TAIL HVA LO QHI SEP_B SEP_F SFL SFR VAHI BAND.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p fl10 xp P s slack pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP STR SRNG SPAD P0 SZS SD1 SD2 SD3 SD4 E10.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app, zb_length in SB. cbn [length] in SB.
assert (LSB : Z.of_nat (length (zb s ++ Z_to_bv 8 0 :: slack)) = (Z.of_nat (length s) + 1 + Z.of_nat (length slack))%Z)
by (rewrite length_app, zb_length; cbn [length]; lia).
pose proof (zb_nonul s SRNG) as NONUL. pose proof (zb_length s) as LZS.
pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq fl) in FLB by lia.
assert (BRNG : forall n, Forall (fun c0 => 0 <= c0 < 256)%Z (firstn n s)).
{ intros n. rewrite <- (skipn_O s). apply Forall_sub. eapply Forall_impl; [|exact SRNG]. cbv beta. intros. lia. }
stmt (HS_TAIL fuel HH) as NX.
set (len := Z.of_nat (length s)) in *.
unfold ZERO_PAD.
ienter.
zs. zs. brf K0; [|exfalso; lia].
destruct XP as [[-> ->] | [-> Hp]].
-
cbn [Z.b2z]. change ((-1) <? 0)%Z with true. cbn [andb].
destruct (Z.leb_spec0 2147483647 len) as [BIG|SMALL]; [ileave; apply implM_unr_l|].
rewrite ?ift, ?iff.
zs. zs. if_lit. zs. zs. zs.
callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack) (n := 2147483647%Z);
[ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
| rewrite length_app, zb_length; cbn [length]; unfold zlength in *; (first [ clear - K0 LZS SB LU LZB SD3 SD2 SD1 P0 SPAD len slack s P BS0 HAP SEP_B SEP_F GLO LO slots VA AP fmt lo q BS B Fp BAND; lia | lia ]) | lia | lia
| match goal with H : SINK ?mm _ |- ISH ?mm => destruct (SFL _ _ H) as (fbq & FLCq & FBq & ISHq); exact ISHq | |- ?g => idtac "ISHslotFAILED" g; fail end
| match goal with |- szone _ (memchr_len 0 ?nn _) => pose proof (memchr_len_cstr_le nn (zb s) slack NONUL ltac:(lia)) as MLB end;
rewrite zb_length in MLB; eapply szone_sub; [exact SZS| (first [ clear - LZS SB LU LZB len slack s P slots fmt BAND; lia | lia ])| unfold zlength in *; lia| lia] ]).
rewrite (strnlen_res_cstr 0) by exact NONUL. rewrite zb_length. fold len. replace (Z.min len 2147483647) with len by lia.
match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR1 end.
zs. zs. if_lit.
assert (NTH : nth_error (zb s ++ Z_to_bv 8 0 :: slack) (Z.to_nat len) = Some (Z_to_bv 8 0)).
{ rewrite nth_error_app2 by (rewrite zb_length; lia). rewrite zb_length. replace (Z.to_nat len - length s)%nat with 0%nat by lia. reflexivity. }
pose proof (u8ro_read asegs _ P (zb s ++ Z_to_bv 8 0 :: slack) len (Z_to_bv 8 0) _ STR1 NTH ltac:(lia) eq_refl) as RD.
zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. zs. if_lit. zs. zs. zs. zs. zs. zs. zs.
match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at asegs mm P (zb s)) end.
{ pose proof STR2 as STR3. apply bytes_at_app in STR3. exact (proj1 STR3). }
rewrite (@firstn_all2 Z (Z.to_nat len) s) by (unfold len; lia).
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := len) (prefix := []) (body := s) (BA := P) (PFXA := 69023%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact SUB | eapply Forall_impl; [|exact SRNG]; cbv beta; intros; lia
| unfold body_loc; split; [zl| solve_szone] | zl | unfold INT_MAX; zl
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
-
replace (p <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb Z.b2z]. rewrite ?ift, ?iff.
zs. zs.

lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if _ then Z_to_bv 64 ?pcj else _) ?fc ?rv ?m ?ro) =>
let pk := eval vm_compute in (bv_key (Z_to_bv 5 11)) in
let R' := eval cbv beta iota delta [tset] in (tset pk (Z_to_bv 64 p) R) in
apply (evt_cut segs (fun ms' : machine_state => ms' = MS R' F (Z_to_bv 64 pcj) fc rv m ro) Q)
end.
{ brf K1; [ apply evt_done; reflexivity
| zs; apply evt_done; assert (Ep : p = 2147483647%Z) by lia; rewrite Ep; reflexivity ]. }
intros ms' ->.

all: zs; zs.
all: callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack);
[ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
| rewrite length_app, zb_length; cbn [length]; unfold zlength in *; (first [ clear - K0 LZS SB LU LZB SD3 SD2 SD1 P0 SPAD len slack s P BS0 HAP SEP_B SEP_F GLO LO slots VA AP fmt lo q BS B Fp BAND; lia | lia ]) | lia | lia
| match goal with H : SINK ?mm _ |- ISH ?mm => destruct (SFL _ _ H) as (fbq & FLCq & FBq & ISHq); exact ISHq | |- ?g => idtac "ISHslotFAILED" g; fail end
| match goal with |- szone _ (memchr_len 0 ?nn _) => pose proof (memchr_len_cstr_le nn (zb s) slack NONUL ltac:(lia)) as MLB end;
rewrite zb_length in MLB; eapply szone_sub; [exact SZS| lia| unfold zlength in *; lia| lia] ]).
all: rewrite (strnlen_res_cstr 0) by exact NONUL; rewrite zb_length; fold len.
all: zs; zs; br K2; zs; zs; zs; zs; zs; zs; zs.
all: match goal with H : bytes_at _ ?mm ?PP (zb _ ++ _) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
all: lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at asegs mm P (zb (firstn (Z.to_nat (Z.min len p)) s)))
by (pose proof STR2 as STR3; rewrite <- (firstn_skipn (Z.to_nat (Z.min len p)) s) in STR3; rewrite zb_app, <- app_assoc in STR3; apply bytes_at_app in STR3; exact (proj1 STR3)) end.
all: assert (LF : zlength (firstn (Z.to_nat (Z.min len p)) s) = Z.min len p) by (unfold zlength; rewrite length_firstn; lia).
all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := Z.min len p) (prefix := []) (body := firstn (Z.to_nat (Z.min len p)) s) (BA := P) (PFXA := 69023%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact SUB | apply BRNG
| unfold body_loc; split; [rewrite LF; (first [ clear - K0 LZS LSB SB LU LZB SD3 SD2 SD1 P0 SPAD len Hp slack s P p BS0 HAP SEP_B SEP_F GLO LO slots VA AP fmt lo q BS B Fp BAND; lia | lia ])| rewrite LF; eapply szone_sub; [exact SZS| lia| unfold zlength in *; lia| lia]] | rewrite LF; lia | rewrite LF; unfold INT_MAX; lia
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
all: match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
Qed.

Set Keyed Unification.

Lemma L_CV_U : S_CV_U.
Proof using GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR BAND.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
stmt (HS_FMTU fuel HH) as NX.
ienter.
zs. zs. zs. zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := u) (prefix := []) (PFXA := 69023%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros m' MI'; exact (pfx_sub m' 0 0 MI' ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
Qed.

Set Keyed Unification.
Hypothesis HS_INTC : S_INTC.
Hypothesis HS_XLOOP : S_XLOOP.

Lemma L_CV_X : S_CV_X.
Proof using BS0 GLO HA HAP HS_INTC HS_XLOOP HVA LO QHI SEP_B SEP_F SFR BAND.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u t pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu Ht.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
stmt (HS_INTC fuel HH) as NX.
unfold ALT_FORM.
assert (Hl : (Z.land t 32 = 0 \/ Z.land t 32 = 32)%Z) by (destruct Ht as [-> | ->]; [right | left]; reflexivity).
pose proof (hex_digits_length (Z.land t 32) u) as LH.
assert (HRNG : Forall (fun c0 => 0 <= c0 < 256)%Z (hex_digits (Z.land t 32) u)).
{ eapply Forall_impl; [|apply hex_digits_range; exact Hl]. cbv beta. intros. lia. }
ienter.
zs. zs. zs. zs. brf K0.
-
replace (u =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K0). cbn [negb andb].
zs. zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := []) (BA := (q + -368)%Z) (PFXA := 69023%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| rewrite K0, hex_digits_0; apply bytes_at_nil; lia | exact HRNG | rewrite K0, hex_digits_0; zl | zl
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
- replace (u =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K0). cbn [negb andb].
zs. zs.
replace (Z.land t 32) with (Z.land t 32) by reflexivity.
stmt HS_XLOOP as NL.
callx (eapply NL with (l := Z.land t 32) (x := u) (j := 24%Z) (ds := digs);
[ exact MI | exact DIG | lia | exact Hl | unfold zlength; lia | f_equal; lia ]).
destruct_ands POST. cbv zeta in *.
match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ =>
rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
pose proof (rw_cells_bytes_at' _ _ _ _ DIG') as BODY. cbn [cells_bytes cbytes app] in BODY. rewrite app_nil_r in BODY.
apply bytes_at_app in BODY. destruct BODY as [_ BODY]. rewrite length_firstn, LDS in BODY.
replace (Z.of_nat (Nat.min (Z.to_nat (24 - zlength (hex_digits (Z.land t 32) u))) 24)) with (24 - zlength (hex_digits (Z.land t 32) u))%Z in BODY by (unfold zlength in *; lia).
zs. zs. brf K1.
+
replace (Z.land fl 8 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K1). cbn [negb andb].
zs. zs. zs. zs. zs. zs. zs. zs.
destruct Ht as [-> | ->]; cbn [Z.eqb Pos.eqb].
* jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 120]%Z)
(BA := (q + -392 + (24 - zlength (hex_digits (Z.land 120 32) u)))%Z) (PFXA := 69030%Z));
[ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact BODY | exact HRNG | unfold zlength in *; lia | zl
| intros mq MIq; exact (pfx_sub mq 7 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
* jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 88]%Z)
(BA := (q + -392 + (24 - zlength (hex_digits (Z.land 88 32) u)))%Z) (PFXA := 69028%Z));
[ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact BODY | exact HRNG | unfold zlength in *; lia | zl
| intros mq MIq; exact (pfx_sub mq 5 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
+
replace (Z.land fl 8 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K1). cbn [negb andb].
zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [])
(BA := (q + -392 + (24 - zlength (hex_digits (Z.land t 32) u)))%Z) (PFXA := 69023%Z));
[ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact BODY | exact HRNG | unfold zlength in *; lia | zl
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
Qed.

Set Keyed Unification.
Hypothesis HS_FLAGS : S_FLAGS.
Hypothesis HS_WIDTH : S_WIDTH.
Hypothesis HS_PREC : S_PREC.
Hypothesis HS_STATE : S_STATE.

Lemma L_DIR : S_DIR.
Proof using HF HS_FLAGS HS_PREC HS_STATE HS_WIDTH BAND.
intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q i d rest pfx s2s za pl plp alo ahi j128 _
FI LOW Hi Hi1 PD HK.
pose proof FI as FI'. dest_finv FI. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
pose proof (parse_dir_shape _ _ _ PD) as (POSN & SH).
destruct (parse_flags (sfx (i + 1)) 0) as [fl s1] eqn:PF.
destruct SH as (Efl & c1' & s1b & Es1 & N42 & s2 & G & c2 & s2b & Es2 & PX).

destruct (parse_flags_suffix _ _ _ _ PF) as (n1 & Hs1 & Hn1). rewrite sfx_skipn in Hs1 by lia. set (k1 := (i + 1 + Z.of_nat n1)%Z) in Hs1.
rewrite Hs1 in Es1. destruct (sfx_cons_inv fmt k1 c1' s1b ltac:(lia) Es1) as (Hk1 & Ec1' & Es1b).
destruct (getint_suffix _ _ _ _ G) as (n2 & Hs2 & Hn2). rewrite Hs1, sfx_skipn in Hs2 by lia. set (k2 := (k1 + Z.of_nat n2)%Z) in Hs2.
rewrite Hs2 in Es2. destruct (sfx_cons_inv fmt k2 c2 s2b ltac:(lia) Es2) as (Hk2 & Ec2 & Es2b).
assert (Hi1' : (i + 1 < zlength fmt)%Z) by zl.
rewrite (sfx_cons fmt (i + 1)) in POSN, PF by zl.

assert (POSTFLAGS : forall (t0 t1 a3 a4 a5 a6 a7 : word),
evt asegs Q
(MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) a3 a4 a5 a6 a7
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd62f8) fc None m (seg_rom asegs))).
{ intros t0 t1 a3 a4 a5 a6 a7.
pose proof (parse_flags_range (sfx (i + 1)) 0 ltac:(lia)) as FLR. rewrite (sfx_cons fmt (i + 1)), PF in FLR by zl. cbn [fst] in FLR.
stmt HS_WIDTH as NXW. jump (eapply NXW with (k1 := k1) (w := d_w d) (s2 := s2); [exact FI' | exact LOW' | lia | rewrite <- Hs1; exact G | rewrite Hs2, Es2; discriminate | ]).
intros k2' t0' t1' a1' a3' a4' a5' a6' a7' Hk2' Hs2' Hnd Hw.
assert (k2' = k2).
{ pose proof (sfx_length fmt k2 ltac:(zl)) as L1. pose proof (sfx_length fmt k2' ltac:(zl)) as L2. rewrite <- Hs2', Hs2 in L2. lia. }
subst k2'.
stmt HS_PREC as NXP. jump (eapply NXP with (k2 := k2) (p := d_p d) (xp := d_xp d) (k3 := (if d_xp d then k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 else k2)%Z);
[exact FI' | exact LOW' | lia | | ]).
{ destruct PX as [(N46 & Hp & Hxp & Ht & Hrest & CT) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & Es3 & CT)].
- left. rewrite <- Ec2, Hxp. repeat split; try assumption; reflexivity.
- right. rewrite Hxp. rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
rewrite Hs3 in Es3.
assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
destruct (sfx_cons_inv fmt (k2 + 1 + Z.of_nat n3) (d_t d) rest Hk30 Es3) as (Hk3 & Et & Erest).
assert (EK : (k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 = k2 + 1 + Z.of_nat n3)%Z).
{ rewrite Es2b, Erest. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)). pose proof (sfx_length fmt (k2 + 1 + Z.of_nat n3 + 1) ltac:(zl)). unfold zlength in *. lia. }
rewrite EK. split; [congruence|]. split; [reflexivity|]. split; [zl|]. split; [rewrite <- Ec3; exact N42q|].
split; [rewrite <- Es2b, <- Hs3; exact G2 | zl]. }
intros a1q a3q a4q Hp.
destruct PX as [(N46 & Hpq & Hxp & Ht & Hrest & CT) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & Es3 & CT)].
- rewrite Hxp. cbn [Z.b2z].
stmt HS_STATE as NXS. jump (eapply NXS with (k3 := k2) (ty := d_ty d); [exact FI' | zl | rewrite <- Ec2; exact CT | ]).
intros a2q a3q2. rewrite Hxp in HK. cbn [Z.b2z] in HK.
jump (apply (HK (k2 + 1)%Z); [zl | rewrite Hrest, Es2b; reflexivity | replace (k2 + 1 - 1)%Z with k2 by lia; rewrite <- Ec2, Ht; reflexivity | lia | lia | lia]).
- rewrite Hxp. cbn [Z.b2z]. rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
rewrite Hs3 in Es3.
assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
destruct (sfx_cons_inv fmt (k2 + 1 + Z.of_nat n3) (d_t d) rest Hk30 Es3) as (Hk3 & Et & Erest).
assert (EK : (k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 = k2 + 1 + Z.of_nat n3)%Z).
{ rewrite Es2b, Erest. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)). pose proof (sfx_length fmt (k2 + 1 + Z.of_nat n3 + 1) ltac:(zl)). unfold zlength in *. lia. }
rewrite EK.
stmt HS_STATE as NXS. jump (eapply NXS with (k3 := (k2 + 1 + Z.of_nat n3)%Z) (ty := d_ty d); [exact FI' | zl | rewrite <- Et; exact CT | ]).
intros a2q a3q2. rewrite Hxp in HK. cbn [Z.b2z] in HK.
jump (apply (HK (k2 + 1 + Z.of_nat n3 + 1)%Z); [zl | exact Erest | replace (k2 + 1 + Z.of_nat n3 + 1 - 1)%Z with (k2 + 1 + Z.of_nat n3)%Z by lia; symmetry; exact Et | lia | lia | lia]). }

assert (FL34 : forall (a3 a4 a5 : word), evt asegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt (i + 1))) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 (Z_to_bv 64 1) x17
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6268) fc None m (seg_rom asegs))).
{ intros a3q a4q a5q. pose proof (fmt_rng (i + 1) ltac:(zl)) as RG.

assert (NOFLAG : flag_bit (znth fmt (i + 1)) = None -> fl = 0%Z /\ k1 = (i + 1)%Z).
{ intros NF. rewrite (parse_flags_cons_none _ _ _ NF) in PF. injection PF as Efl0 Es1q. split; [congruence|].
pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt (i + 1) ltac:(zl)) as L2.
rewrite (sfx_cons fmt (i + 1)) in L2 by zl. rewrite Es1q, Hs1 in L2. lia. }
zs. zs. zs. brf K2.
-
assert (NF : flag_bit (znth fmt (i + 1)) = None).
{ destruct (flag_bit (znth fmt (i + 1))) eqn:E; [|reflexivity]. exfalso.
pose proof (flag_bit_range (znth fmt (i + 1)) ltac:(congruence)) as R. rewrite land_M64_id in K2 by lia. lia. }
destruct (NOFLAG NF) as [Efl0 Ek1].
zs. zs. zs. brf K3. { exfalso. apply N42. rewrite Ec1', Ek1. exact K3. }
jump (apply POSTFLAGS).
- assert (Hc : (32 <= znth fmt (i + 1) < 64)%Z) by (apply (proj1 (sp_test _ RG)); lia).
rewrite (land_M64_id (znth fmt (i + 1) + -32)) in * by lia.
zs. zs. zs. zs. zs. brf K3.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
assert (NF : flag_bit (znth fmt (i + 1)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
destruct (NOFLAG NF) as [Efl0 Ek1].
zs. zs. brf K4; [ jump (apply POSTFLAGS) | exfalso; apply N42; rewrite Ec1', Ek1; exact K4 ].
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
destruct (flag_bit (znth fmt (i + 1))) as [b|] eqn:E.
2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
pose proof (flag_some _ _ Hc E) as [Hfw Hb].
rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
zs.
stmt HS_FLAGS as NXF. jump (eapply NXF with (p := (i + 1)%Z) (k := 1%Z) (fl := 0%Z) (b := b) (FL := fl) (s1 := s1);
[exact FI' | lia | lia | zl | rewrite unsigned_lit_land; exact Hfw | lia | lia | rewrite Z.lor_0_l; exact PF | rewrite Hs1, Es1; discriminate | ]).
intros k' c' a3' a4' a5' Hk' Hs1' Hc' HN HFL.
assert (Ek1 : k' = k1).
{ pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt k' ltac:(zl)) as L2. rewrite <- Hs1', Hs1 in L2. lia. }
subst k'. subst c'. pose proof (fmt_rng k1 ltac:(zl)) as RGk.
zs. zs. brf K4; [ | exfalso; apply N42; rewrite Ec1'; exact K4 ].
jump (apply POSTFLAGS). }

rd_fmt (i + 1)%Z. zs. fix_u8 (i + 1)%Z. zs. zs. zs. zs. zs. brf K.
-  zs. zs. apply FL34.
- assert (DG : is_digit (znth fmt (i + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
assert (Hi2 : (i + 2 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (i + 2) (zlength fmt)); [assumption|]. exfalso.
rewrite (sfx_nil fmt (i + 1 + 1)) in POSN by lia. rewrite DG in POSN. discriminate. }
replace (i + 1 + 1)%Z with (i + 2)%Z in POSN by lia.
rewrite (sfx_cons fmt (i + 2)) in POSN by zl. rewrite DG in POSN. cbn [andb] in POSN. apply Z.eqb_neq in POSN.
rd_fmt (i + 2)%Z. zs. fix_u8 (i + 2)%Z. zs. zs. zs. zs. br K1. apply FL34.
Qed.

Set Keyed Unification.

Lemma L_DLOOP : S_DLOOP.
Proof using GLO LO QHI BAND.
intros x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m x.
remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x11 x12 x13 x23 m.
induction nx as [nx IH] using lt_wf_ind.
intros x Enx x11 x12 x13 x23 m j ds _ MI DIG Hx Hj ->.
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (dec_digits_step x ltac:(lia)) as DS.
pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)) as Q0.
pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as R0.
assert (Q1 : (x / 10 < 1844674407370955162)%Z) by (apply Z.div_lt_upper_bound; lia).
assert (LD : (2 <= zlength (dec_digits x))%Z).
{ rewrite DS. unfold zlength. rewrite length_app. cbn [length].
destruct (Z.lt_ge_cases (x / 10) 10).
- rewrite dec_digits_small by lia. cbn. lia.
- rewrite (dec_digits_step (x / 10)) by lia. rewrite length_app. cbn [length]. lia. }
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
zs. zs. zs. zs. zs.
rewrite (land_W64_small (Z.shiftr (x * 14757395258967641293) 64)) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite div10_magic by lia. zs. zs. zs.
replace (bv_swrap 32 (x - x / 10 * 10)) with (x mod 10)%Z by (rewrite swrap32_small by lia; lia).
rewrite (land_W64_small (x mod 10)) by lia. rewrite lor48_digit by lia.
set (c := (48 + x mod 10)%Z) in *.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA.
pose proof (u8arr_store_ok asegs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
zs. zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
pose proof (u8arr_write asegs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
zs. zs. brf K.
-
eapply evt_mono.
{ eapply (IH (Z.to_nat (x / 10)) ltac:(lia) (x / 10)%Z eq_refl); [ exact MI | exact DIG1 | lia | | reflexivity ].
rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
cbv beta. intros ms' P. destruct P as (a2' & a3' & xq & W' & m' & -> & MU' & WM' & MI' & DIG' & Hxq & HD & HW).
unfold dloop_post. exists a2', a3', xq, (W' ++ [c]), m'.
assert (EL : zlength (W' ++ [c]) = (zlength W' + 1)%Z) by (unfold zlength; rewrite length_app; cbn [length]; lia).
rewrite EL.
split; [ mseq | ].
split; [ eapply munch_trans; [exact MU | exact MU'] | ].
split; [ eapply wmono_trans; [exact WM | exact WM'] | ].
split; [ exact MI' | ].
split.
{ replace (firstn (Z.to_nat (j - (zlength W' + 1))) ds ++ zb (W' ++ [c]) ++ skipn (Z.to_nat j) ds)
with (firstn (Z.to_nat (j - 1 - zlength W')) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)) ++ zb W' ++ skipn (Z.to_nat (j - 1)) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c))); [exact DIG'|].
rewrite upd_firstn_part by (rewrite LDS; unfold zlength in *; lia). rewrite upd_skipn_at by (rewrite LDS; lia).
replace (Z.to_nat (j - 1 - zlength W')) with (Z.to_nat (j - (zlength W' + 1))) by lia.
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia.
rewrite zb_app, <- !app_assoc. reflexivity. }
split; [ exact Hxq | ]. split; [ rewrite DS, HD; reflexivity | ]. unfold zlength in *. lia.
-
zs. apply evt_done.
unfold dloop_post. eexists (Z_to_bv 64 x), (Z_to_bv 64 c), (x / 10)%Z, [c], _.
split; [ mseq | ].
split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact MI | ].
split.
{ replace (firstn (Z.to_nat (j - zlength [c])) ds ++ zb [c] ++ skipn (Z.to_nat j) ds) with (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)); [exact DIG1|].
rewrite upd_firstn_skipn by (rewrite LDS; lia). cbn [zb map app zlength length Z.of_nat Pos.of_succ_nat].
replace (Z.to_nat (j - 1)) with (Z.to_nat (j - 1)) by reflexivity.
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. reflexivity. }
split; [ lia | ]. split; [ rewrite DS, dec_digits_small by lia; reflexivity | ]. zl.
Qed.

Set Keyed Unification.
Hypothesis HS_EXIT : S_EXIT.

Lemma L_END : S_END.
Proof using GLO HAP HS_EXIT LO SEP_F VAHI BAND.
intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m st r pfx s2s za pl plp l10n alo ahi j128 digs pad apv _
FI LOW DIG PAD HS APC FRM FOK Hr.
pose proof FI as FI'. dest_finv FI.
zs. br K.
stmt HS_EXIT as NX. jump (eapply NX; [exact FI' | exact LOW | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | exact Hr]).
Qed.

Set Keyed Unification.

Lemma L_EXIT : S_EXIT.
Proof using LO BAND.
intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
Ft fc m st r pfx s2s za pl plp l10n alo ahi j128 digs pad apv _ FI LOW DIG PAD HS APC FRM FOK Hr.
dest_finv FI. unfold lo_cells, ssp_guard in LOW.
zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 14 zstep.
zstep. zstep.

release_frame LOW ST (q + -392)%Z.
release_frame DIG ST (q + -368)%Z.
release_frame PAD ST (q + -112)%Z.
release_frame FRhi ST q.
apply evt_done. unfold POST.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact FOK|].
split; [exact ST|]. split; [exact HS|]. split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2]|]. split; [exact APC|]. exact Hr.
Qed.

Set Keyed Unification.

Lemma L_EXIT1 : S_EXIT1.
Proof using LO BAND.
intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
m r pfx s2s za pl plp l10n alo ahi j128 digs pad _ FI MU1 LOW DIG PAD Hr.
dest_finv FI. unfold lo_cells, ssp_guard in LOW.
zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 14 zstep.
zstep. zstep.
release_frame LOW ST (q + -392)%Z.
release_frame DIG ST (q + -368)%Z.
release_frame PAD ST (q + -112)%Z.
release_frame FRhi ST q.
apply evt_done. unfold POST1.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU1|]. split; [exact WM|]. split; [exact MI|].
split; [exact ST|]. unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2].
Qed.

Set Keyed Unification.

Lemma L_FLAGS : S_FLAGS.
Proof using HF BAND.
intros x1 x6 x7 x10 x11 x12 x15 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q p k fl b w3 FL s1 _
FI Hp Hk Hpk Hw3 Hfl Hb PF NE HK.
remember (Z.to_nat (zlength fmt - (p + k))) as kk eqn:Hkk.
revert k fl b w3 x11 x12 x15 Hk Hpk Hw3 Hfl Hb PF HK Hkk.
induction kk as [|kk IH]; intros.
{  rewrite sfx_nil in PF by (unfold zlength in *; lia). cbn in PF. injection PF as _ <-. exfalso. apply NE. reflexivity. }
assert (Hlt : (p + k < zlength fmt)%Z) by (unfold zlength in *; lia).
pose proof FI as FI'. dest_finv FI.
zs. rd_fmt (p + k)%Z. zs. fix_u8 (p + k)%Z. zs. zs. rewrite Hw3. zs. brf K.
-
assert (NF : flag_bit (znth fmt (p + k)) = None).
{ destruct (flag_bit (znth fmt (p + k))) eqn:E; [|reflexivity]. exfalso.
pose proof (flag_bit_range (znth fmt (p + k)) ltac:(congruence)) as R.
pose proof (proj2 (sp_test (znth fmt (p + k)) RG) R). lia. }
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
injection PF as EFL Es1.
rewrite Z.lor_comm, EFL.
jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
{ rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
rewrite <- EFL. apply lor_bound17; lia.
- assert (Hc : (32 <= znth fmt (p + k) < 64)%Z) by (apply (proj1 (sp_test _ RG)); exact K).
rewrite (land_M64_id (znth fmt (p + k) + -32)) in * by lia.
zs. zs. zs. zs. brf K2.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
destruct (flag_bit (znth fmt (p + k))) as [b'|] eqn:E.
2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
pose proof (flag_some _ _ Hc E) as [Hfw Hb'].
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
replace (A + p + k + 1)%Z with (A + p + (k + 1))%Z by lia.
rewrite Z.lor_comm.
eapply (IH (k + 1)%Z (Z.lor fl b) b'); try lia.
{ rewrite unsigned_lit_land. exact Hfw. }
{ apply lor_bound17; lia. }
{ replace (p + (k + 1))%Z with (p + k + 1)%Z by lia. exact PF. }
{ intros k' c' a3 a4 a5 Hk' Hs1 Hc' HN HFL. eapply HK; try eassumption; lia. }
all: unfold zlength in *; lia.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
assert (NF : flag_bit (znth fmt (p + k)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
injection PF as EFL Es1.
rewrite Z.lor_comm, EFL.
jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
{ rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
rewrite <- EFL. apply lor_bound17; lia.
Qed.

Set Keyed Unification.
Hypothesis HS_FMTU2 : S_FMTU2.
Hypothesis HS_DLOOP : S_DLOOP.

Lemma L_FMTU : S_FMTU.
Proof using BS0 GLO HA HAP HS_DLOOP HS_FMTU2 HVA LO SEP_B SEP_F SFR BAND.
intros fuel HH x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x prefix PFXA pfx s2s za plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hx.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
pose proof (dec_digits_length x) as LDX.
stmt (HS_FMTU2 fuel HH) as NX.
ienter.
zs. zs. zs. brf K.
-
zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := x) (d := x) (jj := 24%Z) (W := []) (prefix := prefix) (PFXA := PFXA) (pre := digs));
[ mk_finv | exact LOW | rewrite app_nil_r; exact DIG | zl | lia
| destruct (Z.eq_dec x 0) as [-> | NZ]; [left; split; [reflexivity|]; split; [reflexivity|]; apply dec_digits_0 | right; split; [lia|]; apply dec_digits_small; lia]
| exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
-
zs.
stmt HS_DLOOP as NL.
callx (eapply NL with (j := 24%Z) (ds := digs); [ exact MI | exact DIG | lia | unfold zlength; lia | f_equal; lia ]).
destruct_ands POST.
match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ => rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := x) (prefix := prefix) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG' | unfold zlength in *; rewrite length_firstn, LDS; lia | unfold zlength in *; lia
| right; split; [assumption | assumption]
| exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
Qed.

Set Keyed Unification.

Lemma L_FMTU2 : S_FMTU2.
Proof using BS0 GLO HA HAP HS_INTC HVA LO QHI SEP_B SEP_F SFR BAND.
intros fuel HH x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x d jj W prefix PFXA pfx s2s za plp ahi j128 pre pad _
FI LOW DIG Hjj Hjj1 HD PAD HS APC Hk AOK FPC FRM FOK HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hx.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (rw_CB_length _ _ _ _ DIG) as LDS. rewrite length_app, zb_length in LDS.
pose proof (dec_digits_length x) as LDX.
stmt (HS_INTC fuel HH) as NX.
ienter.
zs. zs. brf K1.
-
destruct HD as [(Hd0 & -> & DX) | (Hd & DX)]; [|exfalso; lia].
rewrite app_nil_r in DIG.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := x) (prefix := prefix) (body := dec_digits x) (BA := (q + -368)%Z) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| rewrite DX; apply bytes_at_nil; lia | eapply Forall_impl; [|apply dec_digits_range]; cbv beta; intros; lia | rewrite DX; zl | rewrite DX; zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
-
destruct HD as [(Hd0 & -> & DX) | (Hd & DX)]; [exfalso; lia|].
assert (LW : (Z.of_nat (length W) + 1 <= 20)%Z) by (rewrite DX in LDX; cbn [length] in LDX; lia).
zs. rewrite lor48_digit by lia. zs.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA. clear DIG.
pose proof (u8arr_store_ok asegs _ _ _ (jj - 1)%Z (wa (q + -392 + jj + -1)) DA ltac:(rewrite length_app, zb_length; unfold zlength in *; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_small by lia. replace (q + -392 + jj + -1)%Z with (q + -392 + (jj - 1))%Z by lia.
pose proof (u8arr_write asegs _ _ _ (jj - 1)%Z (Z_to_bv 8 (48 + d)) DA ltac:(rewrite length_app, zb_length; unfold zlength in *; lia)) as DA2. clear DA. store_done.
assert (EU : upd (pre ++ zb W) (Z.to_nat (jj - 1)) (Z_to_bv 8 (48 + d)) = firstn (Z.to_nat (jj - 1)) pre ++ zb ((48 + d)%Z :: W)).
{ rewrite upd_firstn_skipn by (rewrite length_app, zb_length; unfold zlength in *; lia).
rewrite firstn_app. replace (Z.to_nat (jj - 1) - length pre)%nat with 0%nat by (unfold zlength in *; lia). cbn [firstn]. rewrite app_nil_r.
replace (S (Z.to_nat (jj - 1))) with (length pre) by (unfold zlength in *; lia). rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
rewrite EU in DA2.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG.
replace (length (firstn (Z.to_nat (jj - 1)) pre ++ zb ((48 + d)%Z :: W))) with 24%nat in DIG
by (rewrite length_app, length_firstn, zb_length; cbn [length]; unfold zlength in *; lia).
pose proof (proj1 DA2) as BODY. apply bytes_at_app in BODY. destruct BODY as [_ BODY].
rewrite length_firstn in BODY. replace (Z.of_nat (Nat.min (Z.to_nat (jj - 1)) (length pre))) with (jj - 1)%Z in BODY by (unfold zlength in *; lia).
zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := x) (prefix := prefix) (body := dec_digits x) (BA := (q + -392 + (jj - 1))%Z) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| rewrite DX; exact BODY | eapply Forall_impl; [|apply dec_digits_range]; cbv beta; intros; lia | rewrite DX; zl | rewrite DX; zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
Qed.

Unset Keyed Unification.
Hypothesis HS_SCAN : S_SCAN.
Hypothesis HS_DIR : S_DIR.
Hypothesis HS_CONV : S_CONV.
Hypothesis HS_END : S_END.

Lemma L_HEAD : forall fuel, S_HEAD fuel.
Proof using A0 BS0 GLO HA HAP HF HOUT HS_CONV HS_DIR HS_END HS_SCAN HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI BAND.
induction fuel as [|fuel IH]; intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 Ft fc m st i cnt l k args pfx s2s za pl plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi Hcnt Hl Hcl.
{ cbn [printf_loop]. apply implM_unr. }
rewrite printf_loop_S. rewrite fp_calls_S in FPC.
destruct (sfx i) as [|c s'] eqn:Es. { apply implM_unr. }
destruct (sfx_cons_inv fmt i c s' Hi Es) as (Hilt & Ec & Es').
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
pose proof (fmt_rng i ltac:(zl)) as RGi.
destruct (Z.eqb_spec c 0) as [C0|C0].
{
apply implM_ret.
zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. rewrite <- Ec, C0. zs. fixr. zs. if_lit.
stmt HS_END as NX. jump (eapply NX; [exact FI' | exact LOW' | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | unfold INT_MAX; lia]). }
rewrite <- Es in *. cbv zeta. cbv zeta in FPC.
pose proof (lit_run_sfx fmt i Hi) as (Hn & Hs1 & LIT & Hlit). cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
set (lit := lit_run (sfx i)) in *. set (n := Z.of_nat (length lit)) in *.
rewrite Hs1. rewrite Hs1 in FPC.
assert (Hn0 : (0 <= n)%Z) by (unfold n; lia).
destruct (sfx (i + n)) as [|c1 s2] eqn:Es1. { apply implM_unr. }
destruct (sfx_cons_inv fmt (i + n) c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
match goal with |- context [if ?b then munr else _] => destruct b eqn:PCT; [apply implM_unr|] end.

assert (TERM : (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z).
{ pose proof (lit_run_stop (sfx i) c1 s2 Hs1) as ST12. rewrite <- Ec1.
destruct ST12 as [E0|E37]; [left; exact E0 | right]. split; [exact E37|].
rewrite E37, Z.eqb_refl in PCT. cbn [andb] in PCT. destruct s2 as [|c2 s2q]; [discriminate|].
destruct (sfx_cons_inv fmt (i + n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
split; [exact Hin1|]. rewrite <- Ec2. apply Z.eqb_neq. exact PCT. }
stmt HS_SCAN as NXS.
destruct (0 <? n) eqn:En; try rewrite En in FPC; [apply Z.ltb_lt in En; rename En into Npos | apply Z.ltb_ge in En; rename En into Nz].
-
destruct (Z.ltb_spec0 (2147483647 - (cnt + l)) n) as [|Hncl]; [apply implM_unr|].
ienter.
zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
jump (eapply NXS with (i := i) (n := n) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | exact LIT | exact TERM | left; exact Npos | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1 a2.

zs. br K1.
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. br K2. clear FLC.
zs. zs. zs. zs.
ileave. eapply implM_bind.
{ eapply out_callq; try exact HS; try exact ST; try exact MI.
- rewrite Hlit, zb_firstn. unfold sfx. rewrite zb_skipn. replace (A + i)%Z with (A + Z.of_nat (Z.to_nat i))%Z by lia. apply bytes_at_sub; [exact BY | zl].
- rewrite Hlit. unfold sfx. apply Forall_sub. exact HF.
- unfold n, zlength. reflexivity.
- unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
- lia. - zl. - zl. - zl. - zl. - unfold INT_MAX in *; zl. - solve_szone.
-  first [zl | unfold zlength in *; lia]. }
cbv beta. intros [] st'. post_call asegs m. rename MI0 into MI.
ienter. replace (ret_pc (Z_to_bv 64 877080)) with (Z_to_bv 64 877080) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
zs. zs. br K3.

rewrite <- Es1. rewrite <- Es1 in FPC.
stmt IH as NXH.
jumpM (eapply NXH with (i := (i + n)%Z) (cnt := (cnt + l)%Z) (l := n) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
-
assert (En0 : n = 0%Z) by lia. rewrite En0 in *.
assert (C37 : znth fmt i = 37%Z).
{ destruct TERM as [E0 | [E37 _]]; rewrite Z.add_0_r in *; [|exact E37]. exfalso. apply C0. rewrite Ec. exact E0. }
replace (i + 0 + 1)%Z with (i + 1)%Z in Es2 by lia.
destruct (parse_dir s2) as [[d s3]|] eqn:PD; [|apply implM_unr].
destruct args as [|a args']; [apply implM_unr|].
ienter.
zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
jump (eapply NXS with (i := i) (n := 0%Z) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | intros j Hj; lia | rewrite !Z.add_0_r in TERM |- *; exact TERM | right; exact C37 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1 a2.

zs. br K1.
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. br K2. clear FLC.
zs. zs. zs. zs.
ileave. eapply implM_bind.
{ eapply out_callq; try exact HS; try exact ST; try exact MI.
- apply bytes_at_nil; zl.
- constructor.
- reflexivity.
- unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
- lia. - zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; lia. - solve_szone.
-  change (zlength (@nil Z)) with 0%Z; first [zl | lia]. }
cbv beta. intros [] st'. post_call asegs m. rename MI0 into MI.
ienter. replace (ret_pc (Z_to_bv 64 877080)) with (Z_to_bv 64 877080) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
zs. zs. br K3.

stmt HS_DIR as NXD.
jump (eapply NXD with (i := i) (d := d) (rest := s3)); [mk_finv | unfold lo_cells, ssp_guard; exact LOW | lia | zl | rewrite <- Es2; exact PD | ].
intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp. subst s3.

stmt (HS_CONV fuel IH) as NXC.
jumpM (eapply NXC with (i4 := k4) (k := k) (c := (cnt + l)%Z) (d := d) (a := a) (args := args'));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK
| | | exact FRM | exact FOK | lia | exact Ht | | lia | exact Hw | exact Hp | exact (parse_dir_xp _ _ _ PD) | unfold INT_MAX; lia ].
+ destruct a; try exact I. exact (Forall_inv FPC).
+ destruct a; try exact FPC. exact (Forall_inv_tail FPC).
+ exact (parse_dir_conv_type _ _ _ PD).
Qed.

Set Keyed Unification.
Hypothesis HS_INTC2 : S_INTC2.

Lemma L_INTC : S_INTC.
Proof using HS_INTC2 BAND.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp argi prefix body BA PFXA s2s za plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BEND BLEN HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hargi.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
stmt (HS_INTC2 fuel HH) as NX.
unfold conv_int.
ienter.
destruct XP as [[-> ->] | [-> Hp]]; cbn [Z.b2z].
-
replace (false && (-1 <? 0))%bool with false by reflexivity.
zs. zs. rewrite Z.land_0_l. zs. if_lit. zs. if_lit.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := (-1)%Z) (argi := argi) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG | zl | zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia | lia ].
-
replace (true && (p <? 0))%bool with false by (cbn; symmetry; apply Z.ltb_ge; lia).
zs. zs.
replace (Z.lxor p 9223372036854775808 <? 9223372036854775808)%Z with false
by (symmetry; apply Z.ltb_ge; change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; lia).
cbn [Z.b2z Z.land]. zs. if_lit. zs. if_lit. zs. zs.
pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB.
rewrite (nzmask_eq fl) in FLB |- * by lia.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := p) (argi := argi) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG | zl | zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia | lia ].
Qed.

Set Keyed Unification.

Lemma L_INTC2 : S_INTC2.
Proof using GLO HAP HS_TAIL LO QHI SEP_B SEP_F BAND.
intros fuel HH x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p argi prefix body BA PFXA s2s za plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BEND BLEN HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hp Hc Hargi.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (zb_length body) as LB.
set (n := Z.of_nat (length body)) in *.
stmt (HS_TAIL fuel HH) as NX.
ienter.
zs. zs. brf K1.
-
replace (argi =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. rewrite ?if_false_Z, ?Z.add_0_r.
zs. zs. zs. zs. replace (argi <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite ?Z.add_0_r.
zs. brf K2; [ | zs ]; zs; zs.
all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := Z.max p n) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG
| unfold body_loc; split; [zl| solve_szone] | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
-
replace (argi =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb]. rewrite ?if_true_Z.
zs. brf K3.
+
assert (Hp0 : p <> 0%Z) by (intros E; apply K3; apply (proj2 (landM64_zero p ltac:(lia))); exact E).
replace (p =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact Hp0).
zs. zs. zs. zs. replace (argi <? 1)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
zs. brf K2; [ | zs ]; zs; zs.
all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := Z.max p (n + 1)) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG
| unfold body_loc; split; [zl| solve_szone] | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
+
assert (Hp0 : p = 0%Z) by (apply (proj1 (landM64_zero p ltac:(lia))); exact K3).
replace (p =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact Hp0).
zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (prefix := prefix) (body := []) (BA := (q + -368)%Z) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| apply bytes_at_nil; lia | apply Forall_nil
| unfold body_loc; split; [zl| solve_szone] | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
Qed.

Set Keyed Unification.
Hypothesis HS_EXIT1 : S_EXIT1.

Lemma L_P1 : S_P1.
Proof using HF HS_DIR HS_EXIT1 HS_SCAN BAND.
intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 m pfx s2s za pl plp alo ahi j128 digs pad _
FI MU1 LOW DIG PAD P1.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
stmt HS_EXIT1 as NXE. stmt HS_SCAN as NXS. stmt HS_DIR as NXD.
unfold pass1_ok in P1. apply andb_true_iff in P1. destruct P1 as [LITB P1]. apply Z.leb_le in LITB. unfold INT_MAX in LITB.
pose proof (lit_run_sfx fmt 0 ltac:(lia)) as (Hn & Hs1 & LIT & Hlit). change (sfx 0) with fmt in Hn, Hs1, LIT, Hlit.
cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
set (n := Z.of_nat (length (lit_run fmt))) in *.
rewrite Hs1 in P1. rewrite !Z.add_0_l in *.
destruct (sfx n) as [|c1 s2] eqn:Es1; [discriminate|].
destruct (sfx_cons_inv fmt n c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
pose proof (lit_run_stop fmt c1 s2 Hs1) as C1.
assert (TERM : (znth fmt n = 0 \/ (znth fmt n = 37 /\ n + 1 < Z.of_nat (length fmt) /\ znth fmt (n + 1) <> 37))%Z
/\ (znth fmt n <> 0%Z -> exists d rest, parse_dir (sfx (n + 1)) = Some (d, rest))).
{ rewrite <- Ec1. destruct (Z.eqb_spec c1 0) as [E0|E0]; [split; [left; exact E0 | intros X; exfalso; exact (X E0)]|].
destruct s2 as [|c2 s2q]; [discriminate|].
destruct (sfx_cons_inv fmt (n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
apply andb_true_iff in P1. destruct P1 as [P37 PD]. destruct (Z.eqb_spec c2 37) as [|N37]; [discriminate|].
split. { right. split; [lia|]. split; [unfold zlength in Hin1; exact Hin1|]. rewrite <- Ec2. exact N37. }
intros _. rewrite <- Es2. destruct (parse_dir (c2 :: s2q)) as [[d rest]|]; [|discriminate]. exists d, rest. reflexivity. }
destruct TERM as [TERM PDX].

zs. zs. zs. br K. zs. rd_fmt 0%Z. rewrite Z.add_0_r in RD. zs. fix_u8 0%Z. zs. fixr. zs. brf K0.
-
assert (n = 0)%Z as N0. { destruct (Z.eq_dec n 0); [assumption|]. exfalso. destruct (LIT 0%Z ltac:(lia)) as [X _]. apply X. exact K0. }
zs. if_lit. zs. zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
-
jump (eapply NXS with (i := 0%Z) (n := n) (cnt' := 0%Z);
[ exact FI' | lia | lia | zl | intros j Hj; rewrite Z.add_0_l; apply LIT; exact Hj | rewrite Z.add_0_l; exact TERM
| destruct (Z.lt_ge_cases 0 n); [left; assumption | right; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); destruct C1 as [C1|C1]; [exfalso; apply K0; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); exact C1 | exact C1]]
| unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1 a2. rewrite !Z.add_0_r.
zs. if_lit. zs. brf K1.
+
assert (N0 : n = 0%Z) by lia.
destruct C1 as [C1|C1]; [exfalso; apply K0; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); exact C1|].
destruct (PDX ltac:(rewrite <- Ec1, C1; lia)) as (d & rest & PD).
rewrite N0 in PD.
jump (eapply NXD with (i := 0%Z) (d := d) (rest := rest); [exact FI' | exact LOW' | lia | zl | exact PD | ]).
intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp.
zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
+
zs. zs. zs. br K2. zs. rd_fmt n. zs. fix_u8 n. zs. fixr. zs. brf K3.
*
zs. if_lit. zs. zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
*
destruct C1 as [C1|C1]; [exfalso; apply K3; rewrite <- Ec1, C1; reflexivity|].
destruct (PDX K3) as (d & rest & PD).
jump (eapply NXS with (i := n) (n := 0%Z) (cnt' := n);
[ exact FI' | lia | lia | zl | intros j Hj; exfalso; lia | rewrite Z.add_0_r; exact TERM
| right; rewrite <- Ec1; exact C1 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1' a2''. rewrite !Z.add_0_r.
zs. if_lit. zs. if_lit.
jump (eapply NXD with (i := n) (d := d) (rest := rest); [exact FI' | exact LOW' | lia | zl | exact PD | ]).
intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp.
zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
Qed.

Set Keyed Unification.

Lemma L_PLOOP : S_PLOOP.
Proof using HF BAND.
intros x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 Ft fc m Q pos acc p s3 pfx s2s za pl plp alo ahi j128 _
FI LOW Hpos Hacc DG G NE HK.
remember (Z.to_nat (zlength fmt - pos)) as kk eqn:Hkk.
revert pos acc x13 x14 x15 Hpos Hacc DG G HK Hkk.
induction kk as [|kk IH]; intros; [unfold zlength in *; exfalso; lia|].
pose proof FI as FI'. dest_finv FI. unfold lo_cells, ssp_guard in LOW.
pose proof (proj1 (digit_range _) DG) as DGR.
rewrite (sfx_cons fmt pos) in G by zl. rewrite (getint_cons_digit _ _ _ DG) in G.
destruct (214748364 <? acc) eqn:OV1; [discriminate|]. destruct (INT_MAX - 10 * acc <? znth fmt pos - 48) eqn:OV2; [discriminate|]. cbn [orb] in G.
apply Z.ltb_ge in OV1. apply Z.ltb_ge in OV2. unfold INT_MAX in OV2.
assert (Hnx : (pos + 1 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (pos + 1) (zlength fmt)) as [|Hge]; [assumption|]. exfalso.
rewrite sfx_nil in G by lia. cbn in G. injection G as _ <-. apply NE. reflexivity. }
zs. zs. br K.
zs. try rewrite (swrap32_small (acc * 10)) by lia.
zs. rewrite Z.add_0_r, (swrap32_small (znth fmt pos + -48)) by lia.
zs. try rewrite (lxor_imax (acc * 10)) by lia.
zs. try rewrite (proj2 (Z.ltb_ge (2147483647 - acc * 10) (znth fmt pos + -48))) by lia. cbn [Z.b2z].
zs. try rewrite (swrap32_small (acc * 10 + (znth fmt pos + -48))) by lia.
zs. try change (bv_swrap 32 (0 - 0)) with 0%Z.
zs. try rewrite Z.lor_0_l.
rd_fmt (pos + 1)%Z. zs. fix_u8 (pos + 1)%Z. zs. zs. zs. zs. brf K2.
-
assert (ND : is_digit (znth fmt (pos + 1)) = false).
{ destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
rewrite (sfx_cons fmt (pos + 1)) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G.
injection G as Ew Es2.
zs. zs. zs. zs.
jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
- assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
intros k3 a1' a3' a4' Hk3 Hs3 Hnd Hp. apply HK; try assumption. zl.
Qed.

Lemma L_PREC : S_PLOOP -> S_PREC.
Proof using HF BAND.
intros HPL x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k2 k3 p xp pfx s2s za pl plp alo ahi j128 _
FI LOW Hk2 PX HK.
pose proof FI as FI'. dest_finv FI.
rd_fmt k2. zs. fix_u8 k2. zs. zs.
destruct PX as [(N46 & Hp & Hxp & Hk3) | (E46 & Hxp & Hk21 & N42 & G & Hk3)].
- br K. subst p xp k3. do 6 zs. jump (apply HK; unfold INT_MAX; lia).
- br K. rd_fmt (k2 + 1)%Z. zs. fix_u8 (k2 + 1)%Z. zs. zs. br K1.
subst xp. zsto 0xd6468%Z.
pose proof (fmt_rng (k2 + 1) ltac:(zl)) as RG3.
zs. brf K3.
+
assert (ND : is_digit (znth fmt (k2 + 1)) = false).
{ destruct (is_digit (znth fmt (k2 + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG3)) in E. lia. }
rewrite (sfx_cons fmt (k2 + 1)) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G.
injection G as Ep Es. subst p.
assert (k3 = k2 + 1)%Z.
{ pose proof (sfx_length fmt k3 ltac:(zl)) as L1. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)) as L2.
rewrite (sfx_cons fmt (k2 + 1)) in L2 by zl. rewrite Es in L2. lia. }
subst k3. zs. zs. zs. jump (apply HK; unfold INT_MAX; lia).
+ assert (D3 : is_digit (znth fmt (k2 + 1)) = true) by (apply (proj1 (digit_test _ RG3)); lia).
zs. zs.
stmt HPL as NXL. jump (eapply NXL with (pos := (k2 + 1)%Z) (acc := 0%Z); [exact FI' | exact LOW | zl | lia | exact D3 | exact G | | ]).
{ intros E. pose proof (sfx_length fmt k3 ltac:(zl)) as L. rewrite E in L. change (zlength (@nil Z)) with 0%Z in L. zl. }
intros k3' a1' a3' a4' Hk3' Hs3 Hnd Hp.
assert (k3' = k3)%Z.
{ pose proof (sfx_length fmt k3 ltac:(zl)) as L1. pose proof (sfx_length fmt k3' ltac:(zl)) as L2. rewrite <- Hs3 in L2. lia. }
subst k3'. apply HK. lia.
Qed.

Unset Keyed Unification.

Lemma L_PRO : S_PRO.
Proof using BS0 GLO HA HAP HVA LO QHI SEP_F BAND.
intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f Q _ ST0 MI0 BY0 VAA0 SSP0 Hf CONT.
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO. unfold zlength in *.
destruct SSP0 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. fix_rsegs.
pose proof (zb_length fmt) as LZB. pose proof (u64s_length slots) as LU. unfold va_area in VAA0.
pose proof (munch_refl [(q + -544, q)]%Z m0) as MU. pose proof (wmono_refl asegs m0) as WM.
pose proof ST0 as ST.
carve_frame 544%nat ST.

apply (rw_cells_split_CB asegs _ _ [] 544 _ [] [40;8;8;8;8;8;8;8;8;8;320;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
do 43 zs.

lazymatch type of FR with rw_cells _ _ _ (CB 40 ?ja :: _) => set (jA := ja) in FR; clearbody jA end.
lazymatch type of FR with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: CB 320 ?jb :: _) => set (jB := jb) in FR; clearbody jB end.
apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [LOWa FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
replace (q + -544 + Z.of_nat 432)%Z with (q + -112)%Z in FRhi by lia.
apply (rw_cells_split_CB asegs _ _ [_;_;_;_;_;_;_;_;_;_] 320 _ [] [16; 24; 24; 256]%nat) in LOWa; [ | cbn; lia ].
cbn [mk_CB_cells app] in LOWa.
apply (rw_cells_split_CB asegs _ _ [] 40 _ _ [8; 8; 8; 8; 8]%nat) in LOWa; [ | cbn; lia ].
cbn [mk_CB_cells app] in LOWa.
apply (rw_cells_split_CB asegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] 16 _ _ [8; 8]%nat) in LOWa; [ | cbn; lia ].
cbn [mk_CB_cells app] in LOWa.
do 7 c8ify LOWa.
apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in LOWa. destruct LOWa as [LOW DP]. cbn [cells_size csize Nat.add app] in DP.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DP. destruct DP as [DIG PAD]. cbn [cells_size csize Nat.add app] in PAD.
replace (q + -544 + Z.of_nat 152)%Z with (q + -392)%Z in DIG by lia.
replace (q + -544 + Z.of_nat 152 + Z.of_nat 24)%Z with (q + -368)%Z in PAD by lia.
eapply CONT; [ | exact MU | exact LOW | exact DIG | exact PAD ].
unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area.
split; [assumption|]. split; [eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|].
split; [exact FRhi|]. split; [exact ST|]. split; [exact BY0|]. split; [exact VAA0|]. split; [exact SSP1|exact SSP2].
Qed.

Set Keyed Unification.

Lemma L_LOOP1 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i n : Z) (Q : machine_state -> Prop) (k : nat) (j : Z),
finv m ->
k = Z.to_nat (n - j) -> (0 <= j)%Z -> (j < n \/ (j = n /\ znth fmt (i + n) = 37))%Z ->
(0 <= i)%Z -> (i + n < zlength fmt)%Z ->
(forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z ->
(znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z ->

(forall a0, evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (if (znth fmt (i + n) =? 0)%Z then 0xd61b4 else 0xd61bc)) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt (i + j))) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (A + i + j)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd61a4) fc None m (seg_rom asegs)).
Proof using HF BAND.
intros until k. induction k as [|k IH]; intros j FI Hk Hj Hjn Hi Hin LIT TERM HK.
-
assert (j = n) by lia. subst j. destruct Hjn as [|[_ T37]]; [lia|].
dest_finv FI. unfold INT_MAX in *.
zs. rewrite T37. if_lit. specialize (HK (Z_to_bv 64 37)). rewrite T37, (proj2 (Z.eqb_neq 37 0)) in HK by lia. exact HK.
- destruct Hjn as [Hjn|[Hjn _]]; [|exfalso; lia].
pose proof (LIT j ltac:(lia)) as [NZ N37].
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
pose proof (fmt_rng (i + j) ltac:(unfold zlength in *; lia)) as RG0.
zs. br K.
rd_fmt (i + j + 1)%Z. zs. fix_u8 (i + j + 1)%Z. zs. zs.
destruct (Z.lt_ge_cases (j + 1) n) as [Hlt|Hge].
+
pose proof (LIT (j + 1)%Z ltac:(lia)) as [NZ1 _]. replace (i + j + 1)%Z with (i + (j + 1))%Z in * by lia.
br K1. replace (A + i + j + 1)%Z with (A + i + (j + 1))%Z by lia.
eapply (IH (j + 1)%Z FI'); try lia; try assumption.
+ assert (j + 1 = n)%Z by lia. replace (i + j + 1)%Z with (i + n)%Z in * by lia.
replace (A + i + j + 1)%Z with (A + i + n)%Z by lia.
destruct TERM as [T0 | (T37 & Hn1 & T1)].
* rewrite T0. if_lit. specialize (HK (Z_to_bv 64 0)). rewrite T0, Z.eqb_refl in HK. exact HK.
* br K1. eapply (IH n FI'); try lia; try assumption.
Qed.

Lemma L_SCAN : S_SCAN.
Proof using A0 HA HF BAND.
intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m i n cnt' Q _
FI Hi Hn Hin LIT TERM Hnz Hc Hnc HK.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
assert (NZ0 : znth fmt i <> 0%Z).
{ destruct Hnz as [Hp|H37]; [|rewrite H37; lia]. pose proof (LIT 0%Z ltac:(lia)) as [X _]. rewrite Z.add_0_r in X. exact X. }
pose proof (fmt_rng i ltac:(unfold zlength in *; lia)) as RGi.
zs. zs. br K.
eapply evt_eq; [ | eapply L_LOOP1 with (i := i) (n := n) (k := Z.to_nat (n - 0)) (j := 0%Z); try exact FI'; try lia; try assumption ].
{ cbv delta [mkR]. rewrite !Z.add_0_r. reflexivity. }
{ destruct Hnz as [Hp|H37]; [left; lia|]. destruct (Z.lt_ge_cases 0 n); [left; lia|]. right. split; [lia|]. replace (i + n)%Z with i by lia. exact H37. }
intros a0.

assert (TL : forall a1 a2, evt asegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd61e8) fc None m (seg_rom asegs))).
{ intros a1 a2. zs. first [progress replace (A + i + n + - (A + i))%Z with n by lia | progress replace (A + i + n - (A + i))%Z with n by lia]. zs. fixr. zs. br K1. zs. fixr. apply HK. }
destruct TERM as [T0 | (T37 & Hn1 & T1)].
- rewrite T0, Z.eqb_refl. zs. zs. apply TL.
- rewrite T37. cbn [Z.eqb Pos.eqb]. zs. zs. rd_fmt (i + n + 1)%Z. zs. fix_u8 (i + n + 1)%Z. zs. br K1. zs. apply TL.
Qed.

Set Keyed Unification.

Lemma L_STATE : S_STATE.
Proof using HF BAND.
intros x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k3 ty _ FI Hk3 CT HK.
pose proof FI as FI'. dest_finv FI.
pose proof (conv_type_range _ _ CT) as TR. pose proof (conv_type_ty _ _ CT) as TY.
zs. zs. rd_fmt k3. zs. fix_u8 k3. zs. zs. brf K.
{ exfalso. rewrite land_M64_neg in K by lia. lia. }
clear K. zs. zs. zs. zs. zs. zs.
pose proof (states0_read m _ _ MI CT) as RD2. zs. cbv beta. rewrite (u8_lit ty) by lia.
zs. zs. zs. brf K2. { exfalso. try rewrite land_M64_id in K2 by lia. lia. }
clear K2. zs. zs. brf K3. { exfalso. try rewrite land_M64_id in K3 by lia. lia. }
clear K3. zs. brf K4. { exfalso. try rewrite land_M64_id in K4 by lia. lia. }
clear K4. zs. br K5.
jump (apply HK).
Qed.

Unset Keyed Unification.
Hypothesis HS_T2 : S_T2.

Lemma L_T1 : S_T1.
Proof using BS0 GLO HA HAP HOUT HS_T2 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ BAND.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw Hfl0.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad at 1. unfold LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
replace (Z.land fl 73728 =? 0)%Z with true by (rewrite Hfl0; reflexivity). cbn [negb orb].
ienter. zs. zs. brf K2.
-
rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt (HS_T2 fuel HH) as NX2.
jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (wq - (pl + pq))%Z) in *.
zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
zs. zs.
apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. destruct (SFL _ _ HS) as (fb0 & FLC0 & FB0 & ISH0). clear FLC0 FB0.
callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia
| match goal with H : stk _ _ lo _ |- _ => exact H end
| idtac; glo_lia | unfold MEMSET_ICPT_STACK; glo_lia | glo_lia
| exact (proj2 (proj2 ISH0)) | exact (proj1 (proj2 ISH0))
| apply (rng_ok_of_ash _ _ _ (proj1 ISH0)); [unfold szone; right; idtac; glo_lia| lia] ]).
clear fb0 ISH0.
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 32 256) in PADa by lia.
zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
out_call.
1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
1:{ lia. } 1:{ lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells asegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
end.
stmt (HS_T2 fuel HH) as NX2.
jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Set Keyed Unification.
Hypothesis HS_T3 : S_T3.

Lemma L_T2 : S_T2.
Proof using BS0 GLO HA HAP HOUT HS_T3 HVA LO QHI SEP_B SEP_F SFL TOK TQ BAND.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
ienter.
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
out_call.
1:{ apply HPFX. exact MI. }
1:{ exact PRNG. }
1:{ rewrite Hpl. reflexivity. }
1:{ lia. } 1:{ lia. } 1:{ zl. } 1:{ zl. } 1:{ zl. } 1:{ zl. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
stmt (HS_T3 fuel HH) as NX3.
jumpM (eapply NX3 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Set Keyed Unification.
Hypothesis HS_T4 : S_T4.

Lemma L_T3 : S_T3.
Proof using BS0 GLO HA HAP HOUT HS_T4 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ BAND.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad at 1. unfold LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z. rewrite (pad_test_xor fl 65536) by reflexivity.
ienter. zs. zs. brf K1.
-
rewrite (proj2 (Z.eqb_neq _ _) K1). cbn [negb orb].
stmt (HS_T4 fuel HH) as NX4.
jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite K1, Z.eqb_refl. cbn [negb orb].
zs. zs. brf K2.
+ rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt (HS_T4 fuel HH) as NX4.
jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
+ rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (wq - (pl + pq))%Z) in *.
zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
zs. zs.
apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. destruct (SFL _ _ HS) as (fb0 & FLC0 & FB0 & ISH0). clear FLC0 FB0.
callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia
| match goal with H : stk _ _ lo _ |- _ => exact H end
| idtac; glo_lia | unfold MEMSET_ICPT_STACK; glo_lia | glo_lia
| exact (proj2 (proj2 ISH0)) | exact (proj1 (proj2 ISH0))
| apply (rng_ok_of_ash _ _ _ (proj1 ISH0)); [unfold szone; right; idtac; glo_lia| lia] ]).
clear fb0 ISH0.
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 48 256) in PADa by lia.
zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
out_call.
1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
1:{ lia. } 1:{ lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells asegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
end.
stmt (HS_T4 fuel HH) as NX4.
jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Unset Keyed Unification.
Hypothesis HS_T5 : S_T5.

Lemma L_T4 : S_T4.
Proof using BS0 GLO HA HAP HOUT HS_T5 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ BAND.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad at 1. change (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z with true. cbn [negb orb].
ienter.
pose proof (c8_read4 _ _ [C8 (Z_to_bv 64 PFXA); C8 (Z_to_bv 64 (Z.land fl 73728))] (Z_to_bv 64 n) _ _ LOW eq_refl) as RD4. cbn [cells_size csize Nat.add] in RD4.
zs. rewrite (sx32_lit n) by (first [ clear - LP LB LU LZB HnI body prefix pl n pq w slots fmt BAND; lia | lia ]). zs. brf K2.
-
rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt (HS_T5 fuel HH) as NX5.
jumpM (eapply NX5 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (pq - n)) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (pq - n)%Z) in *.
zs. zs. zs. try rewrite (swrap32_small (pq - n)) by (first [ clear - LP LB LU LZB Hcw Hwq Hc Hplp Hnp Hpl Hn body prefix pl n pq wq w c slots fmt BAND; lia | lia ]). fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; (first [ clear - K3 N256 n4 LP LB LU LZB body prefix pl n pq w slots fmt BAND; lia | lia ])].
zs. zs.
apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; (first [ clear - K3 n4 LP LB LU LZB body prefix pl n pq w slots fmt BAND; lia | lia ]) ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. destruct (SFL _ _ HS) as (fb0 & FLC0 & FB0 & ISH0). clear FLC0 FB0.
callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia
| match goal with H : stk _ _ lo _ |- _ => exact H end
| idtac; glo_lia | unfold MEMSET_ICPT_STACK; glo_lia | glo_lia
| exact (proj2 (proj2 ISH0)) | exact (proj1 (proj2 ISH0))
| apply (rng_ok_of_ash _ _ _ (proj1 ISH0)); [unfold szone; right; idtac; glo_lia| lia] ]).
clear fb0 ISH0.
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 48 256) in PADa by lia.
zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
out_call.
1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
1:{ lia. } 1:{ lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. (first [ clear - K4 LP LB LU LZB Hn n4 body prefix pl n pq w BS0 HAP SEP_B SEP_F GLO LO slots VA AP fmt lo q BS B Fp BAND; lia | lia ]). }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. (first [ clear - K4 LP LB LU LZB Hn n4 body prefix pl n pq w BS0 HAP SEP_B SEP_F GLO LO slots VA AP fmt lo q BS B Fp BAND; lia | lia ]). }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.

match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells asegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by (first [ clear - K4 LP LB LU LZB n4 body prefix pl n pq w slots fmt BAND; lia | lia ]); clear Ha Hb ]
end.
stmt (HS_T5 fuel HH) as NX5.
jumpM (eapply NX5 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Set Keyed Unification.
Hypothesis HS_T6 : S_T6.

Lemma L_T5 : S_T5.
Proof using BS0 GLO HA HAP HOUT HS_T6 HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI BAND.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
ienter.
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
out_call.
1:{ exact BODY. }
1:{ exact BRNG. }
1:{ rewrite Hn. reflexivity. }
1:{ lia. } 1:{ lia. } 1:{ zl. } 1:{ zl. } 1:{ zl. } 1:{ zl. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
stmt (HS_T6 fuel HH) as NX6.
jumpM (eapply NX6 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Set Keyed Unification.

Lemma L_T6 : S_T6.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ BAND.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z. rewrite (pad_test_xor fl 8192) by reflexivity.
ienter. zs. zs. brf K1.
-
rewrite (proj2 (Z.eqb_neq _ _) K1). cbn [negb orb].
stmt HH as NXH.
jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite K1, Z.eqb_refl. cbn [negb orb].
zs. zs. brf K2.
+
rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt HH as NXH.
jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
+ rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (wq - (pl + pq))%Z) in *.
zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
zs. zs.

apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. destruct (SFL _ _ HS) as (fb0 & FLC0 & FB0 & ISH0). clear FLC0 FB0.
callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia
| match goal with H : stk _ _ lo _ |- _ => exact H end
| idtac; glo_lia | unfold MEMSET_ICPT_STACK; glo_lia | glo_lia
| exact (proj2 (proj2 ISH0)) | exact (proj1 (proj2 ISH0))
| apply (rng_ok_of_ash _ _ _ (proj1 ISH0)); [unfold szone; right; idtac; glo_lia| lia] ]).
clear fb0 ISH0.
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 32 256) in PADa by lia.
zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
destruct (SFL _ _ HS) as (fb & FLC & FB & ISHm). zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
out_call.
1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
1:{ lia. } 1:{ lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
lazymatch goal with |- forall _ _ _, _ -> _ => idtac end.
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
zs.

match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells asegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
end.
stmt HH as NXH.
jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
match goal with H : SINK _ _ |- _ => exact H end.
Qed.

Unset Keyed Unification.
Hypothesis HS_T1 : S_T1.

Lemma conv_tail_k : forall (a1 a2 a3 a4 a5 a6 : M St unit) (v : Z) (k : Z -> M St Z) s Q ms,
implM asegs (a1 ;;; a2 ;;; a3 ;;; a4 ;;; a5 ;;; a6 ;;; k v) s Q ms ->
implM asegs (x <- (a1 ;;; a2 ;;; a3 ;;; a4 ;;; a5 ;;; a6 ;;; mret v) ;; k x) s Q ms.
Proof using .
clear. intros a1 a2 a3 a4 a5 a6 v k s Q ms H.
Ltac kstep H := apply implM_assoc; eapply implM_bind_ext; [ | exact H ]; cbv beta;
let x := fresh "x" in let s' := fresh "s'" in let ms' := fresh "ms'" in let H' := fresh "H" in
intros x s' ms' H'.
kstep H. kstep H0. kstep H1. kstep H2. kstep H3. kstep H4. apply implM_ret_l. exact H5.
Qed.

Lemma L_TAIL : S_TAIL.
Proof using BS0 GLO HA HAP HS_T1 HS_T2 HVA LO QHI SEP_B SEP_F SFR VAHI BAND.
intros fuel HH x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p prefix body BA PFXA s2s za plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BLOC BHI BIM HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hp Hc.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW. unfold body_loc in BLOC.
pose proof (bytes_at_bound _ _ _ _ BODY) as BB. pose proof (zb_length body) as LB. rewrite LB in BB.
set (n := Z.of_nat (length body)) in *. set (pl := Z.of_nat (length prefix)) in *.
unfold conv_tail. unfold zlength. fold n. fold pl. cbv zeta.
ienter.
zs. rewrite (sextw_small p) by lia. zs. replace (BA + n - BA)%Z with n by lia. zs. zs. zs.

lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if _ then Z_to_bv 64 ?pcj else _) ?fc ?rv ?m ?ro) =>
let pk := eval vm_compute in (bv_key (Z_to_bv 5 11)) in
let R' := eval cbv beta iota delta [tset] in (tset pk (Z_to_bv 64 (Z.max p n)) R) in
apply (evt_cut segs (fun ms' : machine_state => ms' = MS R' F (Z_to_bv 64 pcj) fc rv m ro) Q)
end.
{ brf K1; [ apply evt_done; first [ rewrite (Z.max_r p n) by lia | rewrite (Z.max_l p n) by lia ]; reflexivity
| zs; apply evt_done; first [ rewrite (Z.max_l p n) by (first [ clear - K1 LB LU LZB n body prefix p slots fmt BAND; lia | lia ]) | rewrite (Z.max_r p n) by lia ]; reflexivity ]. }
intros ms' ->.

all: zs; try rewrite (sextw_small p) by lia; fixr; zs; zs; fixr; zs; brf K2;
[ replace (INT_MAX - pl <? Z.max p n)%Z with true by (symmetry; apply Z.ltb_lt; unfold INT_MAX; lia); ileave; apply implM_unr_l
| replace (INT_MAX - pl <? Z.max p n)%Z with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia) ].

all: zs; zs; zs; fixr; zs; zs; zs.

lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if _ then Z_to_bv 64 ?pcj else _) ?fc ?rv ?m ?ro) =>
let pk := eval vm_compute in (bv_key (Z_to_bv 5 26)) in
let R' := eval cbv beta iota delta [tset] in (tset pk (Z_to_bv 64 (Z.max w (pl + Z.max p n))) R) in
apply (evt_cut segs (fun ms' : machine_state => ms' = MS R' F (Z_to_bv 64 pcj) fc rv m ro) Q)
end.
{ brf K3; [ apply evt_done; first [ rewrite (Z.max_r w (pl + Z.max p n)) by lia | rewrite (Z.max_l w (pl + Z.max p n)) by lia ]; reflexivity
| zs; apply evt_done; first [ rewrite (Z.max_l w (pl + Z.max p n)) by lia | rewrite (Z.max_r w (pl + Z.max p n)) by lia ]; reflexivity ]. }
intros ms' ->.

all: zs; brf K4;
[ replace (INT_MAX - c <? Z.max w (pl + Z.max p n))%Z with true by (symmetry; apply Z.ltb_lt; unfold INT_MAX; lia); ileave; apply implM_unr_l
| replace (INT_MAX - c <? Z.max w (pl + Z.max p n))%Z with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia) ].

all: zs; zs; zs; zs; brf K5.
all: ileave; apply conv_tail_k.
all: match goal with
| K : Z.land ?flv 73728 <> 0%Z |- _ =>
unfold mpad at 1; change (Z.lor LEFT_ADJ ZERO_PAD) with 73728%Z; rewrite (proj2 (Z.eqb_neq _ 0) K); cbn [negb orb]; apply implM_ret_l;
stmt (HS_T2 fuel HH) as NX2;
jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := Z.max w (pl + Z.max p n)) (pq := Z.max p n) (args := args)
(PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ]
| K : Z.land ?flv 73728 = 0%Z |- _ =>
stmt (HS_T1 fuel HH) as NX1;
jumpM (eapply NX1 with (k := k) (i4 := i4) (c := c) (w := w) (wq := Z.max w (pl + Z.max p n)) (pq := Z.max p n) (args := args)
(PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | (first [ clear - LB LU LZB Hw pl n body prefix p w slots fmt BAND; lia | lia ]) | lia | unfold INT_MAX; lia | exact K ]
end.
Qed.

Set Keyed Unification.

Lemma L_WLOOP : S_WLOOP.
Proof using HF BAND.
intros x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q pos acc w s2 pfx s2s za pl plp alo ahi j128 _
FI LOW Hpos Hacc DG G NE HK.
remember (Z.to_nat (zlength fmt - pos)) as kk eqn:Hkk.
revert pos acc x5 x6 x12 x14 x15 x16 x17 Hpos Hacc DG G HK Hkk.
induction kk as [|kk IH]; intros; [unfold zlength in *; exfalso; lia|].
pose proof FI as FI'. dest_finv FI. unfold lo_cells, ssp_guard in LOW.
pose proof (proj1 (digit_range _) DG) as DGR.
rewrite (sfx_cons fmt pos) in G by (unfold zlength in *; lia). rewrite (getint_cons_digit _ _ _ DG) in G.
destruct (214748364 <? acc) eqn:OV1; [discriminate|]. destruct (INT_MAX - 10 * acc <? znth fmt pos - 48) eqn:OV2; [discriminate|]. cbn [orb] in G.
apply Z.ltb_ge in OV1. apply Z.ltb_ge in OV2. unfold INT_MAX in OV2.

assert (Hnx : (pos + 1 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (pos + 1) (zlength fmt)) as [|Hge]; [assumption|]. exfalso.
rewrite sfx_nil in G by lia. cbn in G. injection G as _ <-. apply NE. reflexivity. }
zs. zs. br K.
zs. zs. try rewrite (swrap32_small (acc * 10)) by lia.
zs. rewrite Z.add_0_r, (swrap32_small (znth fmt pos + -48)) by lia.
rd_fmt (pos + 1)%Z. zs. fix_u8 (pos + 1)%Z.
zs. try rewrite (lxor_imax (acc * 10)) by lia.
zs. try rewrite (swrap32_small (acc * 10 + (znth fmt pos + -48))) by lia.
zs. try rewrite (proj2 (Z.ltb_ge (2147483647 - acc * 10) (znth fmt pos + -48))) by lia. cbn [Z.b2z].
zs. try change (bv_swrap 32 (0 - 0)) with 0%Z.
zs. zs. zs. try rewrite Z.lor_0_l. zs. zs. brf K2.
-
assert (ND : is_digit (znth fmt (pos + 1)) = false).
{ destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
rewrite (sfx_cons fmt (pos + 1)) in G by (unfold zlength in *; lia). rewrite (getint_cons_nondigit _ _ _ ND) in G.
injection G as Ew Es2.
zs. br K3.
jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
-
assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
Qed.

Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
Proof using HF BAND.
intros HWL x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k1 w s2 pfx s2s za pl plp alo ahi j128 _
FI LOW Hk1 G NE HK.
pose proof FI as FI'. dest_finv FI.
pose proof (fmt_rng k1 ltac:(zl)) as RG1.
zs. zs. zs. zs. brf K.
-
assert (ND : is_digit (znth fmt k1) = false).
{ destruct (is_digit (znth fmt k1)) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG1)) in E. lia. }
rewrite (sfx_cons fmt k1) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G. injection G as Ew Es2.
subst w. jump (apply (HK k1); [zl | | exact ND | unfold INT_MAX; lia]).
rewrite (sfx_cons fmt k1) by zl. symmetry. exact Es2.
- assert (DG : is_digit (znth fmt k1) = true) by (apply (proj1 (digit_test _ RG1)); lia).
zs. zs.
stmt HWL as NXL. jump (eapply NXL with (pos := k1) (acc := 0%Z); [exact FI' | exact LOW | zl | lia | exact DG | exact G | exact NE | ]).
intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
Qed.

Set Keyed Unification.

Lemma L_XLOOP : S_XLOOP.
Proof using GLO LO QHI BAND.
intros x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m l x.
remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x12 x13 x23 m.
induction nx as [nx IH] using lt_wf_ind.
intros x Enx x12 x13 x23 m j ds _ MI DIG Hx Hl Hj ->.
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (hex_digits_step l x ltac:(lia)) as DS.
pose proof (Z.div_pos x 16 ltac:(lia) ltac:(lia)) as Q0.
pose proof (Z.mod_pos_bound x 16 ltac:(lia)) as R0.
assert (Q1 : (x / 16 < 1152921504606846976)%Z) by (apply Z.div_lt_upper_bound; lia).
assert (LD : (1 <= zlength (hex_digits l x))%Z) by (rewrite DS; unfold zlength; rewrite length_app; cbn [length]; lia).
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
pose proof (hexchar_range 0 (x mod 16)%Z ltac:(lia) ltac:(lia)) as XR. rewrite Z.lor_0_r in XR.
pose proof (hexchar_range l (x mod 16)%Z Hl ltac:(lia)) as HR.
zs. zs. zs. zs.
replace (Z.land x 15) with (x mod 16)%Z in * by (change 15%Z with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity).
pose proof (xdigits_read _ (x mod 16)%Z MI ltac:(lia)) as RD.
zs. cbv beta. rewrite (u8_lit (znth XDIGITS (x mod 16))) by lia.
zs. replace (Z.shiftr x 4) with (x / 16)%Z by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
zs. try rewrite (land_W64_small (znth XDIGITS (x mod 16))) by lia.
set (c := Z.lor (znth XDIGITS (x mod 16)) l) in *.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA.
pose proof (u8arr_store_ok asegs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
pose proof (u8arr_write asegs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
zs. zs. brf K.
-
eapply evt_mono.
{ eapply (IH (Z.to_nat (x / 16)) ltac:(lia) (x / 16)%Z eq_refl) with (j := (j - 1)%Z); [ exact MI | exact DIG1 | lia | exact Hl | | f_equal; lia ].
rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
cbv beta. intros ms' P. destruct P as (a2' & a3' & m' & -> & MU' & WM' & MI' & DIG' & HW).
unfold xloop_post. exists a2', a3', m'. cbv zeta.
assert (EL : zlength (hex_digits l x) = (zlength (hex_digits l (x / 16)) + 1)%Z) by (rewrite DS; unfold zlength; rewrite length_app; cbn [length]; lia).
rewrite EL.
split; [ mseq | ].
split; [ eapply munch_trans; [exact MU | exact MU'] | ].
split; [ eapply wmono_trans; [exact WM | exact WM'] | ].
split; [ exact MI' | ].
split.
{ replace (firstn (Z.to_nat (j - (zlength (hex_digits l (x / 16)) + 1))) ds ++ zb (hex_digits l x) ++ skipn (Z.to_nat j) ds)
with (firstn (Z.to_nat (j - 1 - zlength (hex_digits l (x / 16)))) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)) ++ zb (hex_digits l (x / 16)) ++ skipn (Z.to_nat (j - 1)) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c))); [exact DIG'|].
rewrite upd_firstn_part by (rewrite LDS; unfold zlength in *; lia). rewrite upd_skipn_at by (rewrite LDS; lia).
replace (Z.to_nat (j - 1 - zlength (hex_digits l (x / 16)))) with (Z.to_nat (j - (zlength (hex_digits l (x / 16)) + 1))) by lia.
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia.
rewrite DS, zb_app, <- !app_assoc. reflexivity. }
unfold zlength in *. lia.
-
apply evt_done. unfold xloop_post. eexists _, _, _. cbv zeta.
assert (E0 : hex_digits l (x / 16) = []) by (replace (x / 16)%Z with 0%Z by lia; apply hex_digits_0).
assert (EL : zlength (hex_digits l x) = 1%Z) by (rewrite DS, E0; reflexivity).
rewrite EL.
split; [ mseq | ].
split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact MI | ].
split.
{ replace (firstn (Z.to_nat (j - 1)) ds ++ zb (hex_digits l x) ++ skipn (Z.to_nat j) ds) with (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)); [exact DIG1|].
rewrite upd_firstn_skipn by (rewrite LDS; lia). rewrite DS, E0. cbn [zb map app].
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. reflexivity. }
lia.
Qed.

End PrintfCore.

End Mqe.

Module Mqf.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Qc6I QJFf QVsB QDM6.
Import QCiC.Mq1 Qpj5.Mq1 QdZp.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QTVW.Mqb QnRU QteI.Mqb Qu3b.Mq4 QQNJ.Mq8 QQNJ.
Import QZzg.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Theorem stdio_write_flush_proof {BAND : Band} : stdio_write_flush_stmt.
Proof.
unfold stdio_write_flush_stmt. intros until canary. intros SINK -> -> ST LO GLO SPHI SEPB SSP MI A1B.
destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO & B47 & ISHm). cbn [fst] in FC, BUF, LEN.
unfold OUT_DEPTH, GLOBALS_TOP in *.
pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
apply bytes_at_app in BY as [BY _].
rewrite <- (Z_to_bv_bv_unsigned a1).
pose proof (bv_unsigned_in_range 64 a1) as RA1. unfold bv_modulus in RA1.
eapply implM_mono.
{ eapply (stdio_write_spec (St:=St)) with (B := B) (fd := 2) (Fp := 970048) (buf := buf) (s := []) (S := bv_unsigned a1) (lo := lo) (canary := canary)
(wend := B + 80) (bufsize := 80) (mode := mode) (lbf := 0xffffffff) (tail := tail) (flags := flags) (wfn := F_STDIO_WRITE);
try reflexivity; try lia.
- exact FC.
- exact BY.
- apply bytes_at_nil. unfold zlength; cbn [length]. lia.
- exact ST.
- unfold STDIO_WRITE_DEPTH. lia.
- exact SSP.
- exact MI.
- unfold got_ssp. lia.
- unfold ssp_guard. lia.
- unfold zlength in *; cbn [length]. lia.
- unfold zlength; cbn [length]. lia.
- left. reflexivity. }
cbv beta. intros [] st' ms' PO.
destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & FC' & SSP' & ->).
unfold STDIO_WRITE_DEPTH in MU.
unfold stdio_write_flush_post. do 16 eexists. split; [reflexivity|].
split. { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. unfold STDIO_WRITE_DEPTH in *. intros; lia. }
split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [| exact SSP'].

exists flags, mode, tail, (zb buf ++ rest). cbn [fst].
split. { rewrite Z.add_0_r. exact FC'. }
split; [exact FL32|]. split; [exact FL8|].
split.
{
eapply (rw_cells_transport _ _ m m'); [exact BUF | exact MU | exact WM |].
cbn. unfold zlength in *. lia. }
split; [| split; [exact BHI| split; [exact BGLO| split; [exact B47|]]]].
2:{ eapply ISH_munch_zone; [exact ISHm| exact MU| exact WM|]. unfold STDIO_WRITE_DEPTH. zforalls. }
unfold zlength in *. cbn [length]. rewrite length_app. unfold zb. rewrite length_map. lia.
Qed.
End Mqf.

Module Mqg.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QteI.Mqb QQNJ.Mq9.
Import Q0z1.
Import QlES.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo AP S : Z) (str : list Z) (slack : list byte).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Hypothesis APC : rw_cells asegs m AP [C8 (wz S)].
Hypothesis APLO : bv_unsigned sp <= AP.

Hypothesis STR : bytes_at asegs m S (zb str ++ b8 0 :: slack).
Hypothesis BYT : Forall (fun c => 0 < c < 256) str.
Hypothesis SZ : szone S (zlength str + 1).
Hypothesis SLEN : zlength str + 1 <= 2^40.
Hypothesis SEP : S + zlength str + 1 + zlength slack <= lo \/ bv_unsigned sp <= S.

Definition MID (ms' : machine_state) : Prop :=
exists (m2 : word -> option byte) (junk1 junk2 : list byte) (x3 x4 : word),
ms' = MS (mkR (wz 0x53ac8) (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp
(wz 0x1ef4d) (wz 0x14818) x3 (wz 115) x4 (wz 0) a5 a6 a7
(wz 10) (wz 0x1ef4f) (wz 0x15cb0) (wz AP) (wz 0x1ef4e)
(wz 9) (wz (bv_unsigned sp + -2184)) (wz 12297829382473034410)
(wz (-1)) (wz 37) t3 t4 t5 t6)
F (wz 0x53ac8) fc None m2 (seg_rom asegs)
/\ rw_cells asegs m2 (bv_unsigned sp + -2240) [CB 8 junk1; C8 (wz (bv_unsigned sp + -120)); C8 a0]
/\ rw_cells asegs m2 (bv_unsigned sp + -2176)
[CB 2072 junk2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m2 (bv_unsigned sp + -2216)
[CB 8 (le8 (wz 0)); CB 8 (le8 (wz 18446744073709551615)); C8 (wz 0x1ef4d); C8 (wz 0x1ef4f); C1 (b8 (bv_unsigned (wz 0)));
CB 3 (take 3 (drop 1 (le8 (wz 0)))); C1 (b8 (bv_unsigned (wz 115))); CB 3 (drop 4 (drop 1 (le8 (wz 0))))]
/\ mem_inv asegs m2
/\ rw_cells asegs m2 AP [C8 (wz S)]
/\ ro_cells asegs m2 0x1ef3c [C1 (b8 99); C1 (b8 108); C1 (b8 105); C1 (b8 58); C1 (b8 32); C1 (b8 99); C1 (b8 97); C1 (b8 110); C1 (b8 110); C1 (b8 111); C1 (b8 116); C1 (b8 32); C1 (b8 111); C1 (b8 112); C1 (b8 101); C1 (b8 110); C1 (b8 32); C1 (b8 37); C1 (b8 115); C1 (b8 10); C1 (b8 0)]
/\ stk asegs m2 lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m2
/\ wmono asegs m m2.

Lemma printf_common_cannot_open_head :
evt asegs MID
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x1ef3c)  (wz AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. idtac. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
pose proof (rw_cells_bound _ _ _ _ APC) as BAP. cbn in BAP.
assert (SNZ : 0 < S /\ S + (zlength str + 1) + 8 <= 2^47) by (unfold szone in SZ; idtac; lia).

set (BAh := bytes_at) in STR. change (boxed (szone S (zlength str + 1))) in SZ.
change (boxed (S + zlength str + 1 + zlength slack <= lo \/ bv_unsigned sp <= S)) in SEP.

pose_str FMT 0x1ef3c [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 37; 115; 10; 0] MI.
unfold pcommon_entry, zlength in *.

eapply evt_cut; [ eapply pc_setup with (c := 99) (l := [108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 37; 115; 10]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | cbn; lia | lia | cbn; lia] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

scan_pct 17%nat 0%nat [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 37; 115; 10; 0] 0x1ef3c.
run. call_strchr 0x15cb0 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.

run. call_strchr 0x1c77b [106; 122; 116; 76; 113].

run. call_strchr 0x14816 [99; 67; 115; 83].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => apply evt_done; unfold MID; exists mc, junk1, junk2 end.
eexists _, _. split; [reflexivity|]. split; [exact FRa|]. split; [exact FRb|]. split; [dir_back DIR|].
split; [assumption|]. split; [assumption|]. split; [exact FMT|]. split; [exact ST|]. split; [exact MU| exact WM].
Qed.
End S.
End Mqg.

Module Mqh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QteI.Mqb QQNJ.Mq9.
Import Q0z1.
Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Definition MID (ms' : machine_state) : Prop :=
exists (m2 : word -> option byte) (junk1 junk2 : list byte) (x3 x4 : word),
ms' = MS (mkR (wz 0x53ac8) (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp
(wz 85828) (wz 0) x3 (wz 100) x4 (wz 0) a5 a6 a7
(wz 10) (wz 85830) (wz 0x15cb0) a2 (wz 85829)
(wz 9) (wz (bv_unsigned sp + -2184)) (wz 12297829382473034410)
(wz (-1)) (wz 37) t3 t4 t5 t6)
F (wz 0x53ac8) fc None m2 (seg_rom asegs)
/\ rw_cells asegs m2 (bv_unsigned sp + -2240) [CB 8 junk1; C8 (wz (bv_unsigned sp + -120)); C8 a0]
/\ rw_cells asegs m2 (bv_unsigned sp + -2176)
[CB 2072 junk2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m2 (bv_unsigned sp + -2216)
[CB 8 (le8 (wz 0)); CB 8 (le8 (wz 18446744073709551615)); C8 (wz 85828); C8 (wz 85830); C1 (b8 (bv_unsigned (wz 0)));
CB 3 (take 3 (drop 1 (le8 (wz 0)))); C1 (b8 (bv_unsigned (wz 100))); CB 3 (drop 4 (drop 1 (le8 (wz 0))))]
/\ mem_inv asegs m2
/\ ro_cells asegs m2 85828 [C1 (b8 37); C1 (b8 100); C1 (b8 10); C1 (b8 0)]
/\ stk asegs m2 lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m2
/\ wmono asegs m m2.

Lemma printf_common_emit_d_head :
evt asegs MID
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x14f44)  a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. idtac. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.

pose_str FMT 0x14f44 [37; 100; 10; 0] MI.
unfold pcommon_entry in *.

eapply evt_cut; [ eapply pc_setup with (c := 37) (l := [100; 10]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | cbn; lia | lia | cbn; lia] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

run. call_strchr 0x15cb0 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.

run. call_strchr 0x1c77b [106; 122; 116; 76; 113].

run. call_strchr 0x14816 [99; 67; 115; 83].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => apply evt_done; unfold MID; exists mc, junk1, junk2 end.
eexists _, _. split; [reflexivity|]. split; [exact FRa|]. split; [exact FRb|]. split; [dir_back DIR|].
split; [assumption|]. split; [exact FMT|]. split; [exact ST|]. split; [exact MU| exact WM].
Qed.
End S.
End Mqh.

Module Mqi.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QteI.Mqb QQNJ.Mq9.
Import Q0z1.
Import QlES.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo AP S : Z) (str : list Z) (slack : list byte).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Hypothesis APC : rw_cells asegs m AP [C8 (wz S)].
Hypothesis APLO : bv_unsigned sp <= AP.

Hypothesis STR : bytes_at asegs m S (zb str ++ b8 0 :: slack).
Hypothesis BYT : Forall (fun c => 0 < c < 256) str.
Hypothesis SZ : szone S (zlength str + 1).
Hypothesis SLEN : zlength str + 1 <= 2^40.
Hypothesis SEP : S + zlength str + 1 + zlength slack <= lo \/ bv_unsigned sp <= S.

Definition MID (ms' : machine_state) : Prop :=
exists (m2 : word -> option byte) (junk1 junk2 : list byte) (x3 x4 : word),
ms' = MS (mkR (wz 0x53ac8) (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp
(wz 0x1ef64) (wz 0x14818) x3 (wz 115) x4 (wz 0) a5 a6 a7
(wz 10) (wz 0x1ef66) (wz 0x15cb0) (wz AP) (wz 0x1ef65)
(wz 9) (wz (bv_unsigned sp + -2184)) (wz 12297829382473034410)
(wz (-1)) (wz 37) t3 t4 t5 t6)
F (wz 0x53ac8) fc None m2 (seg_rom asegs)
/\ rw_cells asegs m2 (bv_unsigned sp + -2240) [CB 8 junk1; C8 (wz (bv_unsigned sp + -120)); C8 a0]
/\ rw_cells asegs m2 (bv_unsigned sp + -2176)
[CB 2072 junk2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m2 (bv_unsigned sp + -2216)
[CB 8 (le8 (wz 0)); CB 8 (le8 (wz 18446744073709551615)); C8 (wz 0x1ef64); C8 (wz 0x1ef66); C1 (b8 (bv_unsigned (wz 0)));
CB 3 (take 3 (drop 1 (le8 (wz 0)))); C1 (b8 (bv_unsigned (wz 115))); CB 3 (drop 4 (drop 1 (le8 (wz 0))))]
/\ mem_inv asegs m2
/\ rw_cells asegs m2 AP [C8 (wz S)]
/\ ro_cells asegs m2 0x1ef51 [C1 (b8 99); C1 (b8 108); C1 (b8 105); C1 (b8 58); C1 (b8 32); C1 (b8 114); C1 (b8 101); C1 (b8 97); C1 (b8 100); C1 (b8 32); C1 (b8 101); C1 (b8 114); C1 (b8 114); C1 (b8 111); C1 (b8 114); C1 (b8 32); C1 (b8 111); C1 (b8 110); C1 (b8 32); C1 (b8 37); C1 (b8 115); C1 (b8 10); C1 (b8 0)]
/\ stk asegs m2 lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m2
/\ wmono asegs m m2.

Lemma printf_common_read_error_head :
evt asegs MID
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x1ef51)  (wz AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. idtac. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
pose proof (rw_cells_bound _ _ _ _ APC) as BAP. cbn in BAP.
assert (SNZ : 0 < S /\ S + (zlength str + 1) + 8 <= 2^47) by (unfold szone in SZ; idtac; lia).

set (BAh := bytes_at) in STR. change (boxed (szone S (zlength str + 1))) in SZ.
change (boxed (S + zlength str + 1 + zlength slack <= lo \/ bv_unsigned sp <= S)) in SEP.

pose_str FMT 0x1ef51 [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 37; 115; 10; 0] MI.
unfold pcommon_entry, zlength in *.

eapply evt_cut; [ eapply pc_setup with (c := 99) (l := [108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 37; 115; 10]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | cbn; lia | lia | cbn; lia] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

scan_pct 19%nat 0%nat [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 37; 115; 10; 0] 0x1ef51.
run. call_strchr 0x15cb0 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.

run. call_strchr 0x1c77b [106; 122; 116; 76; 113].

run. call_strchr 0x14816 [99; 67; 115; 83].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => apply evt_done; unfold MID; exists mc, junk1, junk2 end.
eexists _, _. split; [reflexivity|]. split; [exact FRa|]. split; [exact FRb|]. split; [dir_back DIR|].
split; [assumption|]. split; [assumption|]. split; [exact FMT|]. split; [exact ST|]. split; [exact MU| exact WM].
Qed.
End S.
End Mqi.

Module Mqj.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QteI.Mqb QQNJ.Mq9.
Import Q0z1.
Import QlES.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Definition MID (ms' : machine_state) : Prop :=
exists (m2 : word -> option byte) (junk1 junk2 : list byte) (x3 x4 : word),
ms' = MS (mkR (wz 0x53ac8) (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp
(wz 108801) (wz 0) x3 (wz 117) x4 (wz 0) a5 a6 a7
(wz 10) (wz 108803) (wz 0x15cb0) a2 (wz 108802)
(wz 9) (wz (bv_unsigned sp + -2184)) (wz 12297829382473034410)
(wz (-1)) (wz 37) t3 t4 t5 t6)
F (wz 0x53ac8) fc None m2 (seg_rom asegs)
/\ rw_cells asegs m2 (bv_unsigned sp + -2240) [CB 8 junk1; C8 (wz (bv_unsigned sp + -120)); C8 a0]
/\ rw_cells asegs m2 (bv_unsigned sp + -2176)
[CB 2072 junk2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m2 (bv_unsigned sp + -2216)
[CB 8 (le8 (wz 0)); CB 8 (le8 (wz 18446744073709551615)); C8 (wz 108801); C8 (wz 108803); C1 (b8 (bv_unsigned (wz 0)));
CB 3 (take 3 (drop 1 (le8 (wz 0)))); C1 (b8 (bv_unsigned (wz 117))); CB 3 (drop 4 (drop 1 (le8 (wz 0))))]
/\ mem_inv asegs m2
/\ ro_cells asegs m2 108787 [C1 (b8 99); C1 (b8 108); C1 (b8 105); C1 (b8 58); C1 (b8 32); C1 (b8 105); C1 (b8 110); C1 (b8 112); C1 (b8 117); C1 (b8 116); C1 (b8 32); C1 (b8 62); C1 (b8 61); C1 (b8 32); C1 (b8 37); C1 (b8 117); C1 (b8 32); C1 (b8 98); C1 (b8 121); C1 (b8 116); C1 (b8 101); C1 (b8 115); C1 (b8 44); C1 (b8 32); C1 (b8 114); C1 (b8 101); C1 (b8 102); C1 (b8 117); C1 (b8 115); C1 (b8 101); C1 (b8 100); C1 (b8 10); C1 (b8 0)]
/\ stk asegs m2 lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m2
/\ wmono asegs m m2.

Lemma printf_common_too_big_head :
evt asegs MID
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x1a8f3)  a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. idtac. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.

pose_str FMT 0x1a8f3 [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 37; 117; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10; 0] MI.
unfold pcommon_entry in *.

eapply evt_cut; [ eapply pc_setup with (c := 99) (l := [108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 37; 117; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | cbn; lia | lia | cbn; lia] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

scan_pct 14%nat 0%nat [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 37; 117; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10; 0] 0x1a8f3.
run. call_strchr 0x15cb0 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.

run. call_strchr 0x1c77b [106; 122; 116; 76; 113].

run. call_strchr 0x14816 [99; 67; 115; 83].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => apply evt_done; unfold MID; exists mc, junk1, junk2 end.
eexists _, _. split; [reflexivity|]. split; [exact FRa|]. split; [exact FRb|]. split; [dir_back DIR|].
split; [assumption|]. split; [exact FMT|]. split; [exact ST|]. split; [exact MU| exact WM].
Qed.
End S.
End Mqj.

Module Mqk.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QteI.Mqb QQNJ.Mq9.
Import Q0z1.
Import QlES.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo AP S : Z) (str : list Z) (slack : list byte).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Hypothesis APC : rw_cells asegs m AP [C8 (wz S)].
Hypothesis APLO : bv_unsigned sp <= AP.

Hypothesis STR : bytes_at asegs m S (zb str ++ b8 0 :: slack).
Hypothesis BYT : Forall (fun c => 0 < c < 256) str.
Hypothesis SZ : szone S (zlength str + 1).
Hypothesis SLEN : zlength str + 1 <= 2^40.
Hypothesis SEP : S + zlength str + 1 + zlength slack <= lo \/ bv_unsigned sp <= S.

Definition MID (ms' : machine_state) : Prop :=
exists (m2 : word -> option byte) (junk1 junk2 : list byte) (x3 x4 : word),
ms' = MS (mkR (wz 0x53ac8) (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp
(wz 0x1626a) (wz 0x14818) x3 (wz 115) x4 (wz 0) a5 a6 a7
(wz 10) (wz 0x1626c) (wz 0x15cb0) (wz AP) (wz 0x1626b)
(wz 9) (wz (bv_unsigned sp + -2184)) (wz 12297829382473034410)
(wz (-1)) (wz 37) t3 t4 t5 t6)
F (wz 0x53ac8) fc None m2 (seg_rom asegs)
/\ rw_cells asegs m2 (bv_unsigned sp + -2240) [CB 8 junk1; C8 (wz (bv_unsigned sp + -120)); C8 a0]
/\ rw_cells asegs m2 (bv_unsigned sp + -2176)
[CB 2072 junk2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m2 (bv_unsigned sp + -2216)
[CB 8 (le8 (wz 0)); CB 8 (le8 (wz 18446744073709551615)); C8 (wz 0x1626a); C8 (wz 0x1626c); C1 (b8 (bv_unsigned (wz 0)));
CB 3 (take 3 (drop 1 (le8 (wz 0)))); C1 (b8 (bv_unsigned (wz 115))); CB 3 (drop 4 (drop 1 (le8 (wz 0))))]
/\ mem_inv asegs m2
/\ rw_cells asegs m2 AP [C8 (wz S)]
/\ ro_cells asegs m2 0x16263 [C1 (b8 117); C1 (b8 115); C1 (b8 97); C1 (b8 103); C1 (b8 101); C1 (b8 58); C1 (b8 32); C1 (b8 37); C1 (b8 115); C1 (b8 32); C1 (b8 73); C1 (b8 78); C1 (b8 80); C1 (b8 85); C1 (b8 84); C1 (b8 10); C1 (b8 0)]
/\ stk asegs m2 lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m2
/\ wmono asegs m m2.

Lemma printf_common_usage_head :
evt asegs MID
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x16263)  (wz AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. idtac. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
pose proof (rw_cells_bound _ _ _ _ APC) as BAP. cbn in BAP.
assert (SNZ : 0 < S /\ S + (zlength str + 1) + 8 <= 2^47) by (unfold szone in SZ; idtac; lia).

set (BAh := bytes_at) in STR. change (boxed (szone S (zlength str + 1))) in SZ.
change (boxed (S + zlength str + 1 + zlength slack <= lo \/ bv_unsigned sp <= S)) in SEP.

pose_str FMT 0x16263 [117; 115; 97; 103; 101; 58; 32; 37; 115; 32; 73; 78; 80; 85; 84; 10; 0] MI.
unfold pcommon_entry, zlength in *.

eapply evt_cut; [ eapply pc_setup with (c := 117) (l := [115; 97; 103; 101; 58; 32; 37; 115; 32; 73; 78; 80; 85; 84; 10]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | cbn; lia | lia | cbn; lia] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

scan_pct 7%nat 0%nat [117; 115; 97; 103; 101; 58; 32; 37; 115; 32; 73; 78; 80; 85; 84; 10; 0] 0x16263.
run. call_strchr 0x15cb0 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.

run. call_strchr 0x1c77b [106; 122; 116; 76; 113].

run. call_strchr 0x14816 [99; 67; 115; 83].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => apply evt_done; unfold MID; exists mc, junk1, junk2 end.
eexists _, _. split; [reflexivity|]. split; [exact FRa|]. split; [exact FRb|]. split; [dir_back DIR|].
split; [assumption|]. split; [assumption|]. split; [exact FMT|]. split; [exact ST|]. split; [exact MU| exact WM].
Qed.
End S.
End Mqk.

Module Mql.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf QVsB.
Import QCiC.Mq1 Qpj5.Mq1. Import QCNF QoNr.Mq0. Import QdZp.
Import QWHo QC9y.Mq0.
Import QQNJ.Mq8.
Import QcfN.Mq2. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section ITreeFacts.
Variable segs : list Segment.
Context {node : Type}.
Variable atn : node -> machine_state -> Prop.
Local Notation impl := (Qc6I.impl segs atn).
Local Notation bind := (Qc6I.bind node).

Fixpoint tforall {A} (P : A -> Prop) (t : itree node A) : Prop :=
match t with
| Qc6I.Ret r => P r
| Vis n k => forall x, tforall P (k x)
end.

Lemma tforall_bind : forall {A B} (P : A -> Prop) (P' : B -> Prop) (t : itree node A) (f : A -> itree node B),
tforall P t -> (forall a, P a -> tforall P' (f a)) -> tforall P' (bind t f).
Proof.
induction t as [r|n k IH]; intros f H Hf; cbn in *; [apply Hf; exact H|].
intros x. apply IH; [apply H | exact Hf].
Qed.

Lemma impl_bind_ext2 : forall {A B C} (P : A -> Prop) (t : itree node A) (f : A -> itree node B) (g : A -> itree node C) Q1 Q2 ms,
tforall P t ->
(forall r ms', P r -> impl (f r) Q1 ms' -> impl (g r) Q2 ms') ->
impl (bind t f) Q1 ms -> impl (bind t g) Q2 ms.
Proof.
induction t as [r|n k IH]; intros f g Q1 Q2 ms HP Hfg H; cbn [Qc6I.bind] in *.
- apply Hfg; [exact HP | exact H].
- cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. eapply IH; [apply HP | exact Hfg | apply Hk].
Qed.

Lemma impl_bind_elim : forall {A B} (P : A -> Prop) (t : itree node A) (h : A -> itree node B) Q1 Q2 ms,
tforall P t ->
(forall r ms', P r -> impl (h r) Q1 ms' -> evt segs (Q2 r) ms') ->
impl (bind t h) Q1 ms -> impl t Q2 ms.
Proof.
induction t as [r|n k IH]; intros h Q1 Q2 ms HP Hh H; cbn [Qc6I.bind] in *.
- cbn. apply (Hh r); [exact HP | exact H].
- cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. eapply IH; [apply HP | exact Hh | apply Hk].
Qed.

Lemma impl_tforall : forall {A} (P : A -> Prop) (t : itree node A) Q ms,
tforall P t -> impl t Q ms -> impl t (fun r ms' => Q r ms' /\ P r) ms.
Proof.
induction t as [r|n k IH]; intros Q ms HP H; cbn in *.
- eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ | exact HP].
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; [apply HP | apply Hk].
Qed.
End ITreeFacts.

Section StderrBridge.
Variable segs : list Segment.
Context {St : Type}.
Local Notation impl := (Qc6I.impl segs (at_node segs)).

Definition FLUSH_stderr : M (list Z * St) unit :=
fun bs => let '(buf, st) := bs in
ebind (stdio_writev 2 buf [] st) (fun r => Qc6I.Ret (Ok (tt, (@nil Z, snd r)))).

Lemma wv_loop_leaves : forall fuel fd x (st : St),
tforall (fun r => match r with Ok q => snd q = st | Unr => True end) (mloop fuel (wv_body fd) x st).
Proof.
induction fuel as [|fuel IH]; intros fd x st; cbn [mloop]; [cbn; exact I|].
unfold mbind at 1. unfold ebind.
eapply tforall_bind with (P := fun r => match r with Ok q => snd q = st | Unr => True end).
- unfold wv_body, mbind, msys, enode, ebind. cbn [Qc6I.bind].
intros rsp. destruct (dec_writev (snd x) rsp) as [cnt|]; cbn [Qc6I.bind]; [| cbn; exact I].
cbn [fst snd]. destruct (cnt =? snd x); cbn; reflexivity.
- intros [|[[x'|r] st']] H; cbn in H |- *; [exact I | | exact H]. subst st'. apply IH.
Qed.
Lemma stdio_writev_leaves : forall fd buf s (st : St),
tforall (fun r => match r with Ok q => snd q = st | Unr => True end) (stdio_writev fd buf s st).
Proof. intros fd buf s st. unfold stdio_writev. apply wv_loop_leaves. Qed.

Lemma OUT_stderr_leaves : forall p buf (st : St),
tforall (fun r => match r with Ok q => snd (snd q) = st | Unr => True end) (OUT_stderr p (buf, st)).
Proof.
intros p buf st. unfold OUT_stderr.
destruct (OUT_MAX <? zlength p); [cbn; exact I|].
destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p); [|cbn; reflexivity].
unfold ebind. eapply tforall_bind; [apply stdio_writev_leaves|]. intros [|[a s']] H; cbn; [exact I | exact H].
Qed.

Lemma outsk_flush_leaves : forall ps buf (st : St),
tforall (fun r => match r with Ok q => snd (snd q) = st | Unr => True end) (outsk OUT_stderr ps FLUSH_stderr (buf, st)).
Proof.
induction ps as [|p ps IH]; intros buf st; cbn [outsk].
- unfold FLUSH_stderr, ebind. eapply tforall_bind; [apply stdio_writev_leaves|]. intros [|[a s']] H; cbn; [exact I | exact H].
- unfold mbind at 1. unfold ebind. eapply tforall_bind; [apply OUT_stderr_leaves|].
intros [|[[] [buf' st']]] H; cbn in H |- *; [exact I|]. subst st'. apply IH.
Qed.

Lemma stderr_bridge : forall ps buf (st : St) (Q : St -> machine_state -> Prop) ms,
Forall (fun p => zlength p <= OUT_MAX) ps ->
impl (outsk OUT_stderr ps FLUSH_stderr (buf, st)) (epost (fun p ms' => Q (snd (snd p)) ms')) ms ->
impl (mbind (stderr_pieces buf ps) (fun b => stdio_writev 2 b []) st) (epost (fun p ms' => Q (snd p) ms')) ms.
Proof.
induction ps as [|p ps IH]; intros buf st Q ms SH H; cbn [outsk stderr_pieces] in H |- *.
2: apply Forall_cons_iff in SH; destruct SH as [Hp SH];
unfold mbind at 1 in H; unfold OUT_stderr in H;
replace (OUT_MAX <? zlength p) with false in H by (symmetry; apply Z.ltb_ge; lia);
fold (@OUT_stderr St) in H.
-
rewrite mbind_mret. unfold FLUSH_stderr, ebind in H.
eapply (impl_bind_elim segs (at_node segs) _ _ _ _ _ _ (stdio_writev_leaves 2 buf [] st)); [|exact H].
intros [|[[] st']] ms' Hr Hi; cbn in Hi |- *; [apply evt_done; exact I|].
cbn in Hi. exact Hi.
- destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p) eqn:T.
+
rewrite ?T in H. unfold ebind in H.
apply impl_bind_assoc_rev in H.
unfold mbind at 1. change ((stdio_writev 2 buf p ;;; stderr_pieces [] ps) st) with (ebind (stdio_writev 2 buf p st) (fun q => stderr_pieces [] ps (snd q))).
unfold ebind. apply impl_bind_assoc.
eapply (impl_bind_ext2 segs (at_node segs) _ _ _ _ _ _ _ (stdio_writev_leaves 2 buf p st)); [|exact H].
intros [|[[] st']] ms' Hr Hi; cbn [Qc6I.bind] in Hi |- *.
* exact Hi.
* cbn in Hr. subst st'. apply IH; [exact SH | exact Hi].
+
rewrite ?T in H. cbn [ebind Qc6I.bind fst snd] in H.
apply IH; [exact SH | exact H].
Qed.
End StderrBridge.

Lemma outsk_OUT_stdout : forall {St B} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) ps (k : M St B),
Forall (fun p => zlength p <= OUT_MAX) ps ->
outsk (OUT_stdout get_so set_so) ps k = outsk (stdout_fwritex get_so set_so) ps k.
Proof.
intros St B get_so set_so ps k SH. induction SH as [|p ps Hp SH IH]; cbn [outsk]; [reflexivity|].
unfold OUT_stdout at 1. replace (OUT_MAX <? zlength p) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite IH. reflexivity.
Qed.
End Mql.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4g QV3O QjgW QpF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqm.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QTVW.Mqa QOJv.Mqb QNQk Q9Ho.Mq4 QV3O QnRU.Mql QMSY.Mq0 QjgW.
Import QpME.Mq8 QpF1.
Import QRfV.Mq3.
Import QlES.
Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n mb : Z) (gp : word).
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let ssz := sec_size n.
Let msz := sec_map_size n.
Let AB := mb + 4096.
Let A := AB + rz.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n <= 2^26.
Hypothesis HP : from_primary n = false.
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Set Default Proof Using "RL Hn HP MBP MBK MBC AVO AVP".

Lemma sgeomS : rz = 2048 /\ n' = n /\ 64513 <= n <= 2^26 /\ nd mod 8 = 0 /\ n + 2048 <= nd /\ nd < n + 2056 /\ ssz = nd + 2048
/\ msz mod 4096 = 0 /\ ssz + 4096 <= msz /\ msz < ssz + 8192 /\ nd = 2048 + round_up n 8
/\ A mod 16 = 0 /\ appr_lia mb msz /\ mb + msz <= band_lo
/\ (mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb) /\ 0x10007fff8000 <= prim_lo RE /\ prim_lo RE + 2^37 + 0x1000 <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (mb + msz <= rl_T X \/ rl_T X + 4096 <= mb)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (mb + msz <= rl_ctx X \/ rl_ctx X + 65536 <= mb)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (mb + msz <= rl_dn X \/ rl_dn X + 0x100000 <= mb)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (mb + msz <= rl_ssb X \/ rl_ssb X + 0x800000 <= mb).
Proof. exact (sgeom RE X n mb RL Hn HP MBP MBK MBC AVO AVP). Qed.

Lemma alloc_hdr_sec : forall ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s7r : word) (sp : word) (F : bvmap 5 word) fc m lo
(fj : list byte) (canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav : word) (b0 b1 : byte) (h w d : word) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m (bv_unsigned sp + -128) (alloc_frame fj canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
rw_cells asegs m (A + -16) [C1 b0; C1 b1; C2 h; C4 w; C8 d] ->
(forall m1 (u0 u1 u2 u3 u5 u6 u7 : word),
munch [(A + -16, A)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) ->
rw_cells asegs m1 (bv_unsigned sp + -128) (alloc_frame fj canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
rw_cells asegs m1 (A + -16) [C1 b0; C1 (b8 (hb1 b1)); C2 (wz 0); C4 (wz n'); C8 d] ->
RTconst RE X m1 ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 0) (wz n') u0 u1 u2 u3 (wz (AB + ssz)) u5 u6 u7
(wz AB) (wz ssz) (wz A) (wz (A + -16)) (wz A_INSTANCE) s7r (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f634) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 0) (wz n') (wz AB) a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz ssz) (wz rz) (wz n) (wz A_INSTANCE) s7r (wz (-8)) (wz 7) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f53c) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI ST CEIL LO FR HDR CONT.
pose proof sgeomS as (Grz & Gn' & GN & Gnd8 & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & GP & PK & PC & TK & TB & TA & TD & CK & CC & CD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (RT_T _ _ _ RT) as TT. pose proof (RT_ctx_tid _ _ _ RT) as CT. cbv beta delta [rt_T_cells] in TT.
pose proof (munch_refl [(A + -16, A)] m) as MU. pose proof (wmono_refl asegs m) as WM.
subst A. unfold alloc_frame in FR.
step.
step.
rewrite (unsigned_lit (AB + rz)), land_7 by lia.
replace ((AB + rz) mod 8) with 0 by (clear - GA16; Z.div_mod_to_equations; lia).
step.
step. if_lit.
step.
step. ifz.
step.
stp.
step.
step.
step.
rewrite (unsigned_lit n'), Z.shiftr_div_pow2, (Z.div_small n') by (first [ clear - TK PK GM1 Gssz Gnd1 GN Gn' Grz MBK AB msz ssz nd n' rz mb n X RE BAND; lia | lia ]).
step.
rewrite (unsigned_lit n), Z.shiftr_div_pow2, (Z.div_small n) by lia.
step.
step.
step.
step. if_lit.
step.
step.
step.
step.
step.
rewrite hb1_norm in HDR.
step. ifz.
step.
stp.
stp.
step.
replace (ssz + AB) with (AB + ssz) by lia.
eapply CONT; [exact MU| exact WM| assumption| exact ST| exact FR| exact HDR| ].
eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [apply (rt_avoid_sec RE X n mb RL Hn HP MBP MBK MBC AVO AVP); try unfold A in *; unfold AB, msz, ssz, nd, rz in *; lia| constructor].
Qed.

Definition depot_W (sp : Z) : list (Z * Z) :=
[(sp - 352, sp - 128); (SS_BASE, DP_END); (rl_dn X, rl_dn X + 0x100000); (rl_ssb X, rl_ssb X + 0x800000)].

Lemma alloc_depot_sec : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sp : word) (F : bvmap 5 word) fc m lo
(obj tsz dn : Z) (q : list word) (b0 : byte) (b1v : Z) (d : word) (Q : machine_state -> Prop),
RTconst RE X m -> RDepot RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz tsz)] ->
u64arr asegs m (obj + 16) q -> Z.of_nat (length q) = 30 -> 1 <= tsz <= 30 ->
depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= obj -> obj + 256 < 2^64 ->
rw_cells asegs m (A + -16) [C1 b0; C1 (b8 b1v); C2 (wz 0); C4 (wz n'); C8 d] ->
(forall m1 (u0 u1 u2 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 : word) (id : Z),
munch ((A + -8, A) :: depot_W (bv_unsigned sp)) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) ->
RTconst RE X m1 -> RDepot RE X m1 ->
rw_cells asegs m1 obj [C8 (wz (obj + 16)); C8 (wz tsz)] -> u64arr asegs m1 (obj + 16) q ->
1 <= id < 2^16 -> (exists dn', depot_n asegs m1 dn' /\ dn <= dn' <= dn + 1) ->
rw_cells asegs m1 (A + -16) [C1 b0; C1 (b8 b1v); C2 (wz 0); C4 (wz n'); C8 (wz id)] ->
evt asegs Q (MS (mkR (wz 0x3f640) (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 (wz 0) (wz n') (wz id) u5 u6 u7 u10 u11 u12 u13
(wz AB) (wz ssz) (wz A) (wz (A + -16)) (wz A_INSTANCE) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f650) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 0) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz ssz) (wz A) (wz (A + -16)) (wz A_INSTANCE) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f634) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RD MI ST CEIL LO OBJ TRQ LQ SZR DNH DCAP OB1 OB2 HDR CONT.
pose proof sgeomS as (Grz & Gn' & GN & Gnd8 & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & GP & PK & PC & TK' & TB & TA & TD & CK & CC & CD & NK & NC & ND & BK & BC & BD).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (munch_refl ((A + -8, A) :: depot_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold depot_W, SS_BASE, DP_END in MU. subst A.
step.
step.
step.
call_sp_ch (depot_put_spec RE X) ltac:(fun PO => unfold depot_stack, SS_BASE, DP_END in PO);
[exact RL| exact RD| assumption| exact ST| exact CEIL'| unfold depot_stack; lia| exact TRQ| exact LQ| exact SZR| exact DNH| exact DCAP| lia| lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST end.
match goal with H : (exists id, _) |- _ => destruct H as (id & -> & ID & RD1 & TRQ1 & (dn1 & [DNC DNP] & DNR)) end. unfold DP_N in DNC.
step.
step.
rewrite (unsigned_lit id), (zext32_small id) by lia.
step.
rewrite (unsigned_lit id), Z.lor_0_l by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(AB + rz + -8, AB + rz)] mm) as MUh; pose proof (wmono_refl asegs mm) as WMh end.
step.
eapply CONT; [exact MU| exact WM| assumption| exact ST| | | exact OBJ| exact TRQ| exact ID| exists dn1; split; [split; [unfold DP_N; exact DNC| exact DNP]| exact DNR]| exact HDR].
- eapply RTconst_munch; [exact RT| exact MU| exact WM|]. unfold depot_W.
constructor; [apply (rt_avoid_sec RE X n mb RL Hn HP MBP MBK MBC AVO AVP); try unfold A in *; unfold AB, msz, ssz, nd, rz in *; (first [ clear - TK' PK GM1 Gssz Gnd1 GN Grz ks q MBK mb n X RE BAND; lia | lia ])|].
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_depot_img; exact RL|].
constructor; [apply rt_avoid_dn; exact RL|].
constructor; [apply rt_avoid_ssb; exact RL| constructor].
- eapply RDepot_frame; [exact RD1| exact WMh|].
eapply agree_on_of_munch; [exact MUh| exact WMh|]. intros z Fz _. cbn [outside]. split; [| exact I].
destruct Fz as [Fz|[Fz|[Fz|Fz]]]; [destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; lia
| destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; (first [ clear - F2 F1 z BK ND NK CK TK' PK GP GM1 Gssz Gnd1 Gnd8 GN Grz ks q AVP MBK MBP AB msz ssz nd rz mb n X RE BAND; lia | lia ]) | destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; (first [ clear - F2 F1 z BD BK NK CK TK' PK GP GM1 Gssz Gnd1 Gnd8 GN Grz ks q AVP MBK MBP AB msz ssz nd rz mb n X RE BAND; lia | lia ]) | (first [ clear - Fz z TA TK' PK GK GM1 Gssz Gnd1 Gnd8 GN Grz ks q MBK MBP AB msz ssz nd rz mb n X RE BAND; lia | lia ])].
Qed.

End S.
End Mqm.

Module Mqn.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QTVW.Mqa QOJv.Mqb QNQk Q9Ho.Mq4 QV3O QnRU.Mql QMSY.Mq0 QjgW.
Import QpME.Mq8 QpF1.
Import QRfV.Mq3.
Import QpME.Mq8 QpF1.
Import QlES.
Import QpME. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.

Local Ltac lia ::= lia_fast. Local Ltac mkr__lia_0 := lia_fast.
Local Ltac Q0z1.transport_lia ::= tslia_fast. Local Ltac mkr__transport_lia_1 := tslia_fast.
Local Ltac QbcP_c1.if_lit ::= if_lit_fast. Local Ltac mkr__if_lit_2 := if_lit_fast.
Local Ltac QN4c.sfp_cheap ::= sfp_fast. Local Ltac mkr__sfp_cheap_3 := sfp_fast.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n mb : Z) (gp : word).
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let ssz := sec_size n.
Let msz := sec_map_size n.
Let AB := mb + 4096.
Let A := AB + rz.
Let sz := msz - 4096.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n <= 2^26.
Hypothesis HP : from_primary n = false.
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Set Default Proof Using "RL Hn HP MBP MBK MBC AVO AVP".

Lemma sgeomS : rz = 2048 /\ n' = n /\ 64513 <= n <= 2^26 /\ nd mod 8 = 0 /\ n + 2048 <= nd /\ nd < n + 2056 /\ ssz = nd + 2048
/\ msz mod 4096 = 0 /\ ssz + 4096 <= msz /\ msz < ssz + 8192 /\ nd = 2048 + round_up n 8
/\ A mod 16 = 0 /\ appr_lia mb msz /\ mb + msz <= band_lo
/\ (mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb) /\ 0x10007fff8000 <= prim_lo RE /\ prim_lo RE + 2^37 + 0x1000 <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (mb + msz <= rl_T X \/ rl_T X + 4096 <= mb)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (mb + msz <= rl_ctx X \/ rl_ctx X + 65536 <= mb)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (mb + msz <= rl_dn X \/ rl_dn X + 0x100000 <= mb)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (mb + msz <= rl_ssb X \/ rl_ssb X + 0x800000 <= mb).
Proof. exact (sgeom RE X n mb RL Hn HP MBP MBK MBC AVO AVP). Qed.

Lemma alloc_partial_sec : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s0v s3v s9v : word) (sp : word) (F : bvmap 5 word) fc m
(obj : Z) (pb : byte) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m ->
(n' mod 8 <> 0 -> rw_cells asegs m (SH A + n' / 8) [C1 pb]) ->
(forall m1 (u u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 u22 : word),
munch [(SH A + n' / 8, SH A + ngran n')] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> RTconst RE X m1 ->
(n' mod 8 <> 0 -> rw_cells asegs m1 (SH A + n' / 8) [C1 (b8 (n' mod 8))]) ->
evt asegs Q (MS (mkR u (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 s0v (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) s3v (wz A) (wz (A + -16)) u22 (wz obj) (wz 0) s9v (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f7e0) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 s0v (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) s3v (wz A) (wz (A + -16)) (wz (8 * (n' / 8))) (wz obj) (wz 0) s9v (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f74c) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI P3 CONT.
pose proof sgeomS as (Grz & Gn' & GN & Gnd8 & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & _).
assert (AL16 : AB mod 16 = 0) by (subst AB; clear - MBP; Z.div_mod_to_equations; lia).
assert (Grz16 : rz mod 16 = 0) by (rewrite Grz; reflexivity).
assert (Gn1 : 1 <= n') by lia.
assert (SHa : SH AB = AB / 8 + 0x7fff8000) by reflexivity.
assert (SHA : SH (AB + rz) = SH AB + rz / 8) by (rewrite <- SH_plus8; f_equal; clear - Grz16; Z.div_mod_to_equations; lia).
assert (N8 : 0 <= n' / 8 /\ 0 <= n' mod 8 < 8 /\ n' = 8 * (n' / 8) + n' mod 8) by (clear - Gn1; Z.div_mod_to_equations; lia).
pose proof (ngran_eq n' ltac:((first [ clear - Gn1 AB msz nd n' rz mb n BAND; lia | lia ]))) as (NG1 & NG2 & NG3). pose proof (round_up_8 n' ltac:((first [ clear - Gn1 AB msz nd n' rz mb n BAND; lia | lia ]))) as [RU8 _].
subst A.
step.
destruct (Z.eq_dec (n' mod 8) 0) as [Z0|NZ].
- ifz.
eapply CONT; [| apply wmono_refl| exact MI| exact RT| intros NE; exfalso; exact (NE Z0)].
replace (ngran n') with (n' / 8) by (rewrite NG1; unfold round_up; clear -Z0 N8; Z.div_mod_to_equations; lia). apply munch_refl.
- ifz. specialize (P3 NZ).
remember (SH (AB + rz) + n' / 8) as SP8 eqn:ESP8.
pose proof (munch_refl [(SP8, SH (AB + rz) + ngran n')] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 19%nat K19. rtc RT 5%nat K5. rtc RT 1%nat K1. rtc RT 14%nat K14.
step. call0 (can_poison_spec RE X); [exact RT| exact MI|]. subst_words.
step. if_lit.
step. step. step.
step.
stp. stp. stp. stp.
step. destruct (Z.leb_spec (AB + rz + 8 * (n' / 8)) 0x7fff7fff) as [LOWM|HIGHM].
{
ifz.
step. step.
step.
lits.
step.
rewrite (unsigned_lit (AB + rz + 8 * (n' / 8))), Z.shiftr_div_pow2 by (first [ clear - LOWM NZ N8 Gn1 GM1 Gssz Gnd1 GN Gn' Grz MBK AB msz ssz nd n' rz mb n BAND; lia | lia ]). change (2 ^ 3) with 8.
step.
replace (2147450880 + (AB + rz + 8 * (n' / 8)) / 8) with SP8 by (rewrite ESP8, SHA, SHa; clear - AL16 Grz16 N8; Z.div_mod_to_equations; (first [ clear - H24 q4 H19 q3 H15 H14 r2 q2 H5 H4 r0 q0 H0 H r q q1 Grz16 r3 AL16 r4 AB rz mb n; lia | lia ])).
stp.
step.
rewrite (unsigned_lit n'), (Z.land_comm n' 18446744073709551615), land_ones64 by (first [ clear - NZ N8 Gn1 Gnd1 GN Gn' MBK AB msz nd n' rz mb n BAND; lia | lia ]).
step.
rewrite (unsigned_lit n'), land_7 by (first [ clear - NZ N8 Gn1 Gnd1 GN Gn' MBK AB msz nd n' rz mb n BAND; lia | lia ]).
step.
rewrite (unsigned_lit (n' mod 8)) in P3 by lia.
eapply CONT; [exact MU| exact WM| assumption| | intros _; exact P3].
eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [| constructor]. rewrite ESP8, SHA, SHa. subst AB. apply rt_avoid_gap; [exact RL| clear - GK N8 Grz; Z.div_mod_to_equations; (first [ clear - H5 H4 r0 q0 H0 H r q N8 r1 q1 GK Grz msz n' rz mb n; lia | lia ])| rewrite ?KHI_eq, NG1; unfold round_up; clear - GC GM1 Gssz Gnd1 Gn' N8 NZ Grz; Z.div_mod_to_equations; (first [ clear - H15 H14 r2 H10 H9 q2 r1 q1 H5 H4 r0 q0 H0 H r q NZ N8 r3 q3 GC GM1 Gssz Gnd1 Gn' Grz msz ssz nd n' rz mb n BAND; lia | lia ])]. }
unfold_cond; cond_unsig; if_false.
step. step. step. step.
step. step.
stp.
step. ifz.
step. step. step.
stp. stp.
step. unfold_cond; cond_unsig; if_false.
step. unfold_cond; cond_unsig; if_false.
step. step.
step.
lits.
step.
rewrite (unsigned_lit (AB + rz + 8 * (n' / 8))), Z.shiftr_div_pow2 by (first [ clear - HIGHM NZ N8 Gn1 GC GM1 Gssz Gnd1 GN Gn' Grz MBK AB msz ssz nd n' rz mb n BAND; lia | lia ]). change (2 ^ 3) with 8.
step.
replace (2147450880 + (AB + rz + 8 * (n' / 8)) / 8) with SP8 by (rewrite ESP8, SHA, SHa; clear - AL16 Grz16 N8; Z.div_mod_to_equations; (first [ clear - H24 q4 H19 q3 H15 H14 r2 q2 H5 H4 r0 q0 H0 H r q q1 Grz16 r3 AL16 r4 AB rz mb n; lia | lia ])).
stp.
step.
rewrite (unsigned_lit n'), (Z.land_comm n' 18446744073709551615), land_ones64 by (first [ clear - NZ N8 Gn1 Gnd1 GN Gn' MBK AB msz nd n' rz mb n BAND; lia | lia ]).
step.
rewrite (unsigned_lit n'), land_7 by (first [ clear - NZ N8 Gn1 Gnd1 GN Gn' MBK AB msz nd n' rz mb n BAND; lia | lia ]).
step.
rewrite (unsigned_lit (n' mod 8)) in P3 by lia.
eapply CONT; [exact MU| exact WM| assumption| | intros _; exact P3].
eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [| constructor]. rewrite ESP8, SHA, SHa. subst AB. apply rt_avoid_gap; [exact RL| clear - GK N8 Grz; Z.div_mod_to_equations; (first [ clear - H5 H4 r0 q0 H0 H r q N8 r1 q1 GK Grz msz n' rz mb n; lia | lia ])| rewrite ?KHI_eq, NG1; unfold round_up; clear - GC GM1 Gssz Gnd1 Gn' N8 NZ Grz; Z.div_mod_to_equations; (first [ clear - H15 H14 r2 H10 H9 q2 r1 q1 H5 H4 r0 q0 H0 H r q NZ N8 r3 q3 GC GM1 Gssz Gnd1 Gn' Grz msz ssz nd n' rz mb n BAND; lia | lia ])].
Qed.

End S.
End Mqn.

Module Mqo.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mqc.
Import Q13u Qc6I QJFf QVsB.
Import QCiC.Mq1 Qpj5.Mq1 QdZp.
Import QTVW.Mq8 Qu3b.Mq5 QnRU.Mqf QnRU QteI.Mqb Qu3b.Mq4 QQNJ.Mq8.
Import QZzg.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition stderr_wfile0 (m : mem) : Prop :=
exists (flags mode : word) (e wend : Z) (tail : list byte),
rw_cells asegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x645ca0 0 2 mode 0xffffffff tail)
/\ Z.land (bv_unsigned flags) 40 = 0
/\ (wend = 0 \/ (wend = 0x645ca0 /\ e = 0x645ca0))
/\ 0 <= e < 2^63.

Lemma stderr_wfile0_wfile : forall m, stderr_wfile0 m -> stderr_wfile m.
Proof. intros m (flags & mode & e & wend & tail & H & FL & _ & _). exists flags, mode, e, wend, tail. split; [exact H| exact FL]. Qed.

Definition FWRITE_DEPTH : Z := 240.

Section Fwrite.
Context {BAND : Band}.
Context {St : Type}.

Definition fwrite_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ stderr_wfile0 m'
/\ ssp_cells m' canary
/\ st' = st.

Definition fwrite_diag_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
towrite_stmt ->
stderr_wfile0 m ->
bytes_at asegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s <= OUT_MAX ->
a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
ssp_cells m canary -> mem_inv asegs m ->
(bv_unsigned sp <= 2^47) -> (bv_unsigned a0 + zlength s <= 2^47) ->
implM asegs (stderr_fwrite s : M St unit) st
(fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5bc4) fc None m (seg_rom asegs)).
End Fwrite.
End Mqo.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiqM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiqM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Definition wfn_of (so : stdout_st) : Z := if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE.
Definition lbf_of (so : stdout_st) : Z := if so_lbf_nl so then 10 else 0xffffffff.
Definition stdout_cells (so : stdout_st) (flags mode : word) (tail : list byte) : list cell :=
file_cells flags (RSTDOUT_BUF + 1024) (RSTDOUT_BUF + zlength (so_buf so)) RSTDOUT_BUF (wfn_of so) RSTDOUT_BUF 1024 1 mode (lbf_of so) tail.

Definition STDOUT_WRITE_DEPTH : Z := 144.

Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).
Ltac exact_frm := lazymatch goal with |- frm0 ?f => first [is_evar f; fail 1 "exact_frm: evar" | assumption] end.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma rw_cells_recast : forall m A cs cs',
rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
rw_cells asegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma C4_low32 : forall (a b : word) , bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> cbytes (C4 a) = cbytes (C4 b).
Proof.
intros a b E. cbn [cbytes]. unfold le4.
rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia).
rewrite E. reflexivity.
Qed.
Lemma rw_cells_C4_eq : forall m A pre (a b : word) post,
bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 ->
rw_cells asegs m A (pre ++ C4 a :: post) -> rw_cells asegs m A (pre ++ C4 b :: post).
Proof.
intros m A pre a b post E H. eapply rw_cells_recast; [exact H| | |].
- destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [H1 H2]. split; [exact H1|]. exact H2.
- rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (C4_low32 a b E). reflexivity.
- rewrite !cells_size_app. reflexivity.
Qed.

Ltac fix_lbf FC :=
lazymatch type of FC with rw_cells ?sg ?m' ?A ?cs =>
lazymatch cs with ?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: C4 (Z_to_bv 64 (-1)) :: ?rest =>
apply (rw_cells_C4_eq m' A [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20]
(Z_to_bv 64 (-1)) (Z_to_bv 64 4294967295) rest ltac:(vm_compute; reflexivity)) in FC
end
end.

Lemma rw_cells_C4_CB4 : forall m A (v : word) cs,
rw_cells asegs m A (C4 v :: cs) -> rw_cells asegs m A (CB 4 (le4 v) :: cs).
Proof.
intros m A v cs [[W B] R]. split; [split|].
- cbn [cells_wf cell_wf] in *. split; [apply length_le4| exact (proj2 W)].
- exact B.
- exact R.
Qed.
Lemma firstn1_le4 : forall v : word, firstn 1 (skipn 0 (le4 v)) = le1 v.
Proof. intros v. reflexivity. Qed.

Lemma flags_byte_and64 : forall flags : word,
Z.land (bv_unsigned flags) 64 = 0 -> Z.land (bv_unsigned flags mod 256) 64 = 0.
Proof.
intros flags H. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
rewrite (Z.land_comm _ (Z.ones 8)), <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_ones by lia.
rewrite H. reflexivity.
Qed.

Lemma rw_cells_CB4_C4 : forall m A (v : word) cs,
rw_cells asegs m A (CB 4 (le4 v) :: cs) -> rw_cells asegs m A (C4 v :: cs).
Proof.
intros m A v cs [[W B] R]. split; [split|].
- cbn [cells_wf cell_wf] in *. split; [exact I| exact (proj2 W)].
- exact B.
- exact R.
Qed.

Section StdoutWrite.
Context {BAND : Band}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis get_set : forall s so, get_so (set_so so s) = so.
Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.

Definition so_after (so : stdout_st) : stdout_st :=
mkStdout true [] (if so_first so then false else so_lbf_nl so) false.

Definition stdout_writefn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(flags mode : word) (tail : list byte) (l : Z) (lo : Z) (canary : word) (m : mem) (st : St)
: unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - STDOUT_WRITE_DEPTH, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' RSTDOUT (stdout_cells (so_after (get_so st)) flags mode tail)
/\ ssp_cells m' canary
/\ st' = set_so (so_after (get_so st)) st.

Lemma stdout_writefn_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(flags mode : word) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
let so := get_so st in
so_active so = true ->
rw_cells asegs m RSTDOUT (stdout_cells so flags mode tail) ->
Z.land (bv_unsigned flags) 64 = 0 ->
bytes_at asegs m RSTDOUT_BUF (to_bytes (so_buf so)) -> (zlength (so_buf so) <= 1024) ->
bytes_at asegs m S (to_bytes s) ->
a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDOUT_WRITE_DEPTH) -> (band_lo <= lo) ->
ssp_cells m canary -> mem_inv asegs m ->
(zlength s <= 2^25) -> (0 <= S < 2^64) -> (S + zlength s <= 2^47) ->
(s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= RSTDOUT \/ RSTDOUT + 232 <= S))) ->
bv_unsigned sp <= 2^47 ->
implM asegs (stdout_writefn get_so set_so s) st
(stdout_writefn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags mode tail (zlength s) lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (wfn_of so)) fc None m (seg_rom asegs)).
Proof.
intros until canary. cbv zeta. intros ACT FC FL64 BUFB BUFL SRC -> -> -> ST LO GLO SSP MI LENS S0 Shi SEPS SPT.
pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, STDOUT_WRITE_DEPTH in *.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. unfold to_bytes in BS. rewrite length_map in BS.
assert (LSB : length (to_bytes s) = length s) by (unfold to_bytes; apply length_map).
unfold stdout_writefn. apply implM_rdso.
unfold stdout_cells, wfn_of, lbf_of in *.
destruct (so_first (get_so st)) eqn:FIRST.
-
apply implM_bind_assoc. apply implM_updso. apply implM_bind_assoc.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
apply implM_sysk.
change (bytes_at asegs m S (to_bytes s)) with (boxed (bytes_at asegs m S (to_bytes s))) in SRC.
change (bytes_at asegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st)))) with (boxed (bytes_at asegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st))))) in BUFB.
assert (LBB : length (to_bytes (so_buf (get_so st))) = length (so_buf (get_so st))) by (unfold to_bytes; apply length_map).
unfold file_cells in FC. apply rw_cells_C4_CB4 in FC.
carve_frame 32%nat ST.
do 9 step. rewrite ?firstn1_le4, ?zext_extract_le1. unfold zx8.
step. step. step. fix_lit_store. step.
if_cases Hsvb; zify_cond Hsvb. 1:{ exfalso. exact (Hsvb (flags_byte_and64 flags FL64)). }
do 10 step. step_ecall.
replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (symmetry; apply sx32_lit; lia).
split. { at_node_red; split_spine; try reflexivity; try lia. }
intros rsp ans Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec.
destruct ans as [e|v]. 2:{ exfalso. destruct Hdec as (_ & Hok & _). discriminate Hok. }
destruct Hdec as [-> He]. unfold efferr, eff0. cbv iota.
apply implM_updso.

unfold implM. apply impl_from_evt. sys_nret.
do 5 step.
if_cases He0; zify_cond He0. 1:{ exfalso. rewrite unsigned_errno_ret in He0 by lia. lia. }
step. step.
fix_lbf FC.
step. apply evt_done.
rewrite !get_set, !set_set. cbn [so_active so_buf so_first].
unfold stdout_stdio_write. apply (implM_rdso asegs get_so). rewrite get_set. cbn [so_buf].
apply rw_cells_CB4_C4 in FC.
eapply implM_bind.
{ eapply (stdio_write_spec (St:=St)) with (B := RSTDOUT_BUF) (fd := 1) (Fp := RSTDOUT) (buf := so_buf (get_so st)) (s := s) (S := S)
(lo := lo) (canary := canary) (wend := RSTDOUT_BUF + 1024) (bufsize := 1024) (mode := mode) (lbf := 0xffffffff) (tail := tail)
(flags := flags) (wfn := F_STDIO_WRITE); try reflexivity; rewrite ?unsigned_lit by lia.
all: first [ exact FC | exact ST | exact MI | exact BUFL | split; [exact GOT | exact GUARD]
| lia | unfold STDIO_WRITE_DEPTH; lia | unfold got_ssp; lia | unfold ssp_guard; lia
| unfold boxed in BUFB; apply (bytes_at_transport _ _ _ _ _ _ BUFB MU); cbn [disjoint_from]; rewrite LBB; unfold zlength in BUFL; lia
| destruct SEPS as [-> | [S1 S2]]; [left; reflexivity | right; split; lia]
| src_now SRC SEPS MU LSB ]. }
cbv beta. intros [] st' ms' PO.
destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
rewrite !unsigned_lit in MU2, ST2 by lia.
apply implM_upd. rewrite !get_set, !set_set. cbn [so_lbf_nl so_first].

replace (ret_pc (Z_to_bv 64 0xd5e00)) with (Z_to_bv 64 0xd5e00 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
destruct SSP2 as [GOT2 GUARD2]. unfold got_ssp, ssp_guard in GOT2, GUARD2.
assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 canary; C8 s0; C8 ra]).
{ eapply (rw_cells_transport asegs _ _ m2); [exact FR | exact MU2 | exact WM2 | cbn; unfold STDIO_WRITE_DEPTH in *; lia]. }
step. step. step. if_false. step. step. step. step.
release_frame FR2 ST2 (bv_unsigned sp).
unfold stdout_writefn_post, so_after, stdout_cells, wfn_of, lbf_of, file_cells. rewrite FIRST. cbn [so_first so_buf so_lbf_nl].
sys_finish.
+ apply (munch_trans _ m m0 m2).
* eapply munch_weaken; [| exact MU]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
* eapply munch_weaken; [| exact MU2]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
+ eapply wmono_trans; [exact WM | exact WM2].
+ split; [exact GOT2 | exact GUARD2].
+ rewrite ?set_set. reflexivity.
-
apply (implM_retb asegs). unfold stdout_stdio_write. apply (implM_rdso asegs get_so).
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
assert (LBB : length (to_bytes (so_buf (get_so st))) = length (so_buf (get_so st))) by (unfold to_bytes; apply length_map).
eapply implM_bind.
{ eapply (stdio_write_spec (St:=St)) with (B := RSTDOUT_BUF) (fd := 1) (Fp := RSTDOUT) (buf := so_buf (get_so st)) (s := s) (S := S)
(lo := lo) (canary := canary) (wend := RSTDOUT_BUF + 1024) (bufsize := 1024) (mode := mode) (lbf := if so_lbf_nl (get_so st) then 10 else 4294967295) (tail := tail)
(flags := flags) (wfn := F_STDIO_WRITE); try reflexivity; rewrite ?unsigned_lit by lia.
all: try first [ exact FC | exact ST | exact MI | exact BUFL | exact BUFB | exact SRC | split; [exact GOT | exact GUARD]
| lia | unfold STDIO_WRITE_DEPTH in *; lia | unfold got_ssp; lia | unfold ssp_guard; lia ].
destruct SEPS as [-> | [S1 S2]]; [left; reflexivity | right; split; lia]. }
cbv beta. intros [] st' ms' PO.
destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
apply implM_upd. apply evt_done. rewrite ?get_set.
unfold stdout_writefn_post, so_after, stdout_cells, wfn_of, lbf_of, file_cells. rewrite FIRST. cbn [so_first so_buf so_lbf_nl].
sys_finish.
+ eapply munch_weaken; [| exact MU2]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
+ rewrite ?set_set. reflexivity.
Qed.
End StdoutWrite.
