(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC QgpE Q3bI QU0c QJ4Q Qo8J Q85Z QHup QG64 QBCP QiyH Qrlk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1 Q85Z.Mq2 QHup.Mq1 QG64.Mq3.
Import QBCP.Mq1.
Import QiyH.Mq0 Qrlk.Mq0.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

#[local] Ltac solve_incl :=
let x := fresh "x" in let H := fresh "H" in
intros x H; cbn [In] in H;
repeat (destruct H as [<-|H]; [cbn [In]; repeat first [left; reflexivity | right] |]);
destruct H.

Section Summary.
Variable mem0 : word -> option byte.
Variables d cv ret : word.
Variable n : Z.
Variable rom : word -> option byte.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
Hypothesis Hok : store_ok MSEGS mem0 d (Z.to_nat n) = true.
Hypothesis Hret : ret_ok ret.

#[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
#[local] Abbreviation PC o := (Z_to_bv 64 (ms_base + o)).

#[local] Ltac cover L' :=
apply (cfill_full_chain mem0 d n (cbyte cv) Hn Hnw _ L');
[ unfold L2, L6, L8, LB, LC, LD; solve_incl
| cbn [ms_chain]; lia ].

Theorem memset_summary : forall regs,
getr regs 10 = d -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
exists regs',
msteps MSEGS (mkst regs (Z_to_bv 64 ms_base) mem0 rom)
(mkst regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
/\ getr regs' 10 = d /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H1.
pose proof (u64_range d) as Hd.
rewrite <- (at_0 d) in H10.
replace (Z_to_bv 64 ms_base) with (PC 0) by (f_equal; lia).
replace (mkst regs (PC 0) mem0 rom) with (mkst regs (PC 0) (CF []) rom) by (rewrite cfill_nil; reflexivity).

assert (FIN : forall regs' (M : word -> option byte),
M = wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n)) ->
msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret M rom) ->
getr regs' 10 = at_ d 0 -> ms_agree regs regs' ->
exists regs'',
msteps MSEGS (mkst regs (PC 0) (CF []) rom)
(mkst regs'' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
/\ getr regs'' 10 = d /\ ms_agree regs regs'').
{ intros regs' M -> RUN P10 AG. exists regs'. rewrite at_0 in P10. auto. }
destruct (Z.lt_ge_cases n 9) as [Hsmall|Hn9].
{
destruct (Z.eq_dec n 0) as [Hz|Hnz].
{ destruct (A_exit0 mem0 d cv ret n rom Hn Hret regs H10 H11 H12 H1 Hz) as (r1 & RUN & P10 & AG).
eapply (FIN r1); try eassumption.
rewrite cfill_nil. rewrite Hz. reflexivity. }
destruct (Z.lt_ge_cases n 3) as [H3|H3].
{ destruct (A_exit2 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
eapply (FIN r1); try eassumption. cover ([(0,1); (n-1,1)]%Z). }
destruct (Z.lt_ge_cases n 7) as [H7|H7].
{ destruct (A_exit6 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
eapply (FIN r1); try eassumption. cover ([(0,1); (1,1); (2,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
destruct (A_exit8 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
eapply (FIN r1); try eassumption.
cover ([(0,1); (1,1); (2,1); (3,1); (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }

destruct (A_cont mem0 d cv ret n rom Hn Hnw Hok regs H10 H11 H12 H1 Hn9)
as (r1 & RUN1 & Q10 & Q11 & Q12 & Q13 & Q15 & Q1 & AG1).

set (k := ((- bv_unsigned d) mod 4)%Z).
pose proof (neg_mod4_range (bv_unsigned d)) as Hk. fold k in Hk.
pose proof (negw_and3 d) as Hkv. fold k in Hkv.
set (n1 := (n - k - (n - k) mod 4)%Z).
set (m1 := ((n - k) / 4)%Z).
pose proof (Z.div_mod (n - k) 4 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (n - k) 4 ltac:(lia)) as Hmb.
assert (Hm1 : (4 * m1 = n1)%Z) by (subst n1 m1; lia).
assert (Hn1 : (n - k - 3 <= n1 <= n - k)%Z) by (subst n1; lia).
pose proof (andi_m4 (n - k) ltac:(lia)) as Hn1v. fold n1 in Hn1v.
clearbody n1 m1. clear Hdm Hmb.
destruct (Z.lt_ge_cases n1 9) as [HB|HB].
{
destruct (B_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)
as (r2 & RUN2 & P10 & AG2).
eapply (FIN r2); [| eapply msteps_trans; [exact RUN1 | exact RUN2] | exact P10 | eapply ms_agree_trans; eassumption].
cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+n1-4,4); (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
destruct (B_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)
as (r2 & RUN2 & S10 & S11 & S12 & S13 & S14 & S1 & AG2).
destruct (Z.lt_ge_cases n1 25) as [HC|HC].
{ destruct (C_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 ltac:(lia) HC)
as (r3 & RUN3 & P10 & AG3).
eapply (FIN r3); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]]
| exact P10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
(n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
destruct (C_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 HC)
as (r3 & RUN3 & T10 & T11 & T12 & T13 & T14 & T1 & AG3).
destruct (andi_4_cases (at_ d k)) as (s4 & Hs4v & Hs4).
destruct (Z.lt_ge_cases (n1 - s4 - 24) 32) as [HD|HD].
{ destruct (D_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)
as (r4 & RUN4 & P10 & AG4).
eapply (FIN r4); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 |
eapply msteps_trans; [exact RUN3 | exact RUN4]]]
| exact P10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+12,4); (k+16,4); (k+20,4); (k+24,4);
(k+n1-28,4); (k+n1-24,4); (k+n1-20,4); (k+n1-16,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
(n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
destruct (D_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)
as (r4 & RUN4 & U10 & U11 & U12 & U14 & U15 & U1 & AG4).
destruct (E_run mem0 d cv ret n rom k n1 s4 Hs4 r4 (LD n k n1 s4) U10 U11 U12 U14 U15 U1 Hn9 ltac:(lia))
as (r5 & RUN5 & V10 & V11 & V12 & V13 & V14 & V1 & AG5).

set (r := (n1 - s4 - 24)%Z) in *.
set (q := Z.to_nat (r / 32 - 1)).
assert (Hq : (32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod r 32 ltac:(lia)). pose proof (Z.mod_pos_bound r 32 ltac:(lia)). lia. }
destruct (loop_run mem0 d cv ret n rom Hnw Hok q r5 (LD n k n1 s4) (k + s4 + 24)%Z r
V10 V11 V12 V13 V14 V1 ltac:(lia) ltac:(lia) Hq)
as (r6 & RUN6 & W10 & W1 & AG6).
destruct (ret_run ret rom Hret r6 (CF (((k + s4 + 24)%Z, (32 * (Z.of_nat q + 1))%Z) :: LD n k n1 s4)) W1)
as (r7 & RUN7 & ->).
eapply (FIN r6); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 |
eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 |
eapply msteps_trans; [exact RUN5 | eapply msteps_trans; [exact RUN6 | exact RUN7]]]]]]
| exact W10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+12,4); (k+16,4); (k+20,4); (k+24,4);
(k+s4+24, 32 * (Z.of_nat q + 1));
(k+n1-28,4); (k+n1-24,4); (k+n1-20,4); (k+n1-16,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
(n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z).
Qed.

End Summary.

Definition ms_entry : word := ltac:(let l := word_lit (Z_to_bv 64 ms_base) in exact l).

End Mq0.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWZn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1 Q85Z.Mq2 QHup.Mq1 QG64.Mq3.
Import QWZn.Mq0 Qrlk.Mq1 QiyH.Mq4.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MIS.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.

#[local] Notation MK := (memk mem0 dst bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.

Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
Ltac msb F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].

Ltac cond :=
rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
rewrite ?land_3 by lia; lia.
Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac sbp := apply sb_val_plain.

Lemma b4_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 4 <= n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xddda4 : word) (MK k) rom) (mkst regs' (0xdddd0 : word) (MK (k + 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
- mlbu F_dddf0 D_dddf0 k. mlbu F_dddf4 D_dddf4 (k+1)%Z. mlbu F_dddf8 D_dddf8 (k+2)%Z. mlbu F_dddfc D_dddfc (k+3)%Z.
stepn F_dde00 D_dde00.
stepn F_dde04 D_dde04.
msb F_dde08 D_dde08 k ltac:(sbp). msb F_dde0c D_dde0c (k+1)%Z ltac:(sbp).
msb F_dde10 D_dde10 (k+2)%Z ltac:(sbp). msb F_dde14 D_dde14 (k+3)%Z ltac:(sbp).
stepn F_dde18 D_dde18.
mk_eq. apply mst_refl.
- post.
Qed.

Lemma b8_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 8 <= n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xddd50 : word) (MK k) rom) (mkst regs' (0xddd9c : word) (MK (k + 8)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
- mlbu F_ddd9c D_ddd9c k. mlbu F_ddda0 D_ddda0 (k+1)%Z. mlbu F_ddda4 D_ddda4 (k+2)%Z. mlbu F_ddda8 D_ddda8 (k+3)%Z.
mlbu F_dddac D_dddac (k+4)%Z. mlbu F_dddb0 D_dddb0 (k+5)%Z. mlbu F_dddb4 D_dddb4 (k+6)%Z. mlbu F_dddb8 D_dddb8 (k+7)%Z.
stepn F_dddbc D_dddbc.
msb F_dddc0 D_dddc0 k ltac:(sbp). msb F_dddc4 D_dddc4 (k+1)%Z ltac:(sbp).
msb F_dddc8 D_dddc8 (k+2)%Z ltac:(sbp). msb F_dddcc D_dddcc (k+3)%Z ltac:(sbp).
stepn F_dddd0 D_dddd0.
msb F_dddd4 D_dddd4 (k+4)%Z ltac:(sbp). msb F_dddd8 D_dddd8 (k+5)%Z ltac:(sbp).
msb F_ddddc D_ddddc (k+6)%Z ltac:(sbp). msb F_ddde0 D_ddde0 (k+7)%Z ltac:(sbp).
stepn F_ddde4 D_ddde4.
mk_eq. apply mst_refl.
- post.
Qed.

Lemma b16_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 16 <= n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xddcbc : word) (MK k) rom) (mkst regs' (0xddd48 : word) (MK (k + 16)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
- mlbu F_ddd08 D_ddd08 k. mlbu F_ddd0c D_ddd0c (k+1)%Z. mlbu F_ddd10 D_ddd10 (k+2)%Z. mlbu F_ddd14 D_ddd14 (k+3)%Z.
mlbu F_ddd18 D_ddd18 (k+4)%Z. mlbu F_ddd1c D_ddd1c (k+5)%Z. mlbu F_ddd20 D_ddd20 (k+6)%Z. mlbu F_ddd24 D_ddd24 (k+7)%Z.
msb F_ddd28 D_ddd28 k ltac:(sbp). msb F_ddd2c D_ddd2c (k+1)%Z ltac:(sbp).
msb F_ddd30 D_ddd30 (k+2)%Z ltac:(sbp). msb F_ddd34 D_ddd34 (k+3)%Z ltac:(sbp).
mlbu F_ddd38 D_ddd38 (k+8)%Z. mlbu F_ddd3c D_ddd3c (k+9)%Z. mlbu F_ddd40 D_ddd40 (k+10)%Z. mlbu F_ddd44 D_ddd44 (k+11)%Z.
msb F_ddd48 D_ddd48 (k+4)%Z ltac:(sbp). msb F_ddd4c D_ddd4c (k+5)%Z ltac:(sbp).
msb F_ddd50 D_ddd50 (k+6)%Z ltac:(sbp). msb F_ddd54 D_ddd54 (k+7)%Z ltac:(sbp).
mlbu F_ddd58 D_ddd58 (k+12)%Z. mlbu F_ddd5c D_ddd5c (k+13)%Z. mlbu F_ddd60 D_ddd60 (k+14)%Z. mlbu F_ddd64 D_ddd64 (k+15)%Z.
stepn F_ddd68 D_ddd68.
msb F_ddd6c D_ddd6c (k+8)%Z ltac:(sbp). msb F_ddd70 D_ddd70 (k+9)%Z ltac:(sbp).
msb F_ddd74 D_ddd74 (k+10)%Z ltac:(sbp). msb F_ddd78 D_ddd78 (k+11)%Z ltac:(sbp).
stepn F_ddd7c D_ddd7c.
msb F_ddd80 D_ddd80 (k+12)%Z ltac:(sbp). msb F_ddd84 D_ddd84 (k+13)%Z ltac:(sbp).
msb F_ddd88 D_ddd88 (k+14)%Z ltac:(sbp). msb F_ddd8c D_ddd8c (k+15)%Z ltac:(sbp).
stepn F_ddd90 D_ddd90.
mk_eq. apply mst_refl.
- post.
Qed.

Lemma t4_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xdda78 : word) (MK k) rom) (mkst regs' (0xdddd0 : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
- eexists. split.
+ stepn F_ddac4 D_ddac4.
stepb_ft F_ddac8 D_ddac8 ltac:(cond).
stepn F_ddacc D_ddacc.
mk_eq. apply mst_refl.
+ post.
- eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddda4 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_ddac4 D_ddac4.
stepb_tk F_ddac8 D_ddac8 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Lemma b8_tail : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xddd9c : word) (MK k) rom) (mkst regs' (0xdddd0 : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
- eexists. split.
+ stepn F_ddde8 D_ddde8.
stepb_tk F_dddec D_dddec ltac:(cond).
mk_eq. apply mst_refl.
+ post.
- eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddda4 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_ddde8 D_ddde8.
stepb_ft F_dddec D_dddec ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Lemma t8_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
(k + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xdda70 : word) (MK k) rom)
(mkst regs' (0xdddd0 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
destruct HL8 as [HL8|HL8].
-
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda78 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_ddabc D_ddabc.
stepb_ft F_ddac0 D_ddac0 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddd50 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_ddabc D_ddabc.
stepb_tk F_ddac0 D_ddac0 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddd9c : word) (MK (k + 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL8. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Lemma b16_tail : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
(k + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xddd48 : word) (MK k) rom)
(mkst regs' (0xdddd0 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
destruct HL8 as [HL8|HL8].
- eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda78 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_ddd94 D_ddd94.
stepb_tk F_ddd98 D_ddd98 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddd50 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_ddd94 D_ddd94.
stepb_ft F_ddd98 D_ddd98 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddd9c : word) (MK (k + 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Lemma t16_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 32)%Z -> (0 <= k)%Z ->
(k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xdda68 : word) (MK k) rom)
(mkst regs' (0xdddd0 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
-
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda70 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_ddab4 D_ddab4.
stepb_ft F_ddab8 D_ddab8 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddcbc : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_ddab4 D_ddab4.
stepb_tk F_ddab8 D_ddab8 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddd48 : word) (MK (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1 Q85Z.Mq2 QHup.Mq1 QG64.Mq3.
Import QBCP.Mq1.
Import QiyH.Mq3 Qrlk.Mq2.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

#[local] Ltac solve_incl :=
let x := fresh "x" in let H := fresh "H" in
intros x H; cbn [In] in H;
repeat (destruct H as [<-|H]; [cbn [In]; repeat first [left; reflexivity | right] |]);
destruct H.

Section Summary.
Variable mem0 : word -> option byte.
Variables d cv ret : word.
Variable n : Z.
Variable rom : word -> option byte.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
Hypothesis Hok : store_ok MSEGS mem0 d (Z.to_nat n) = true.
Hypothesis Hret : ret_ok ret.

#[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
#[local] Abbreviation PC o := (Z_to_bv 64 (ms_base + o)).

#[local] Ltac cover L' :=
apply (cfill_full_chain mem0 d n (cbyte cv) Hn Hnw _ L');
[ unfold L2, L6, L8, LB, LC, LD; solve_incl
| cbn [ms_chain]; lia ].

Theorem memset_summary : forall regs,
getr regs 10 = d -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
exists regs',
msteps MSEGS (mkst regs (Z_to_bv 64 ms_base) mem0 rom)
(mkst regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
/\ getr regs' 10 = d /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H1.
pose proof (u64_range d) as Hd.
rewrite <- (at_0 d) in H10.
replace (Z_to_bv 64 ms_base) with (PC 0) by (f_equal; lia).
replace (mkst regs (PC 0) mem0 rom) with (mkst regs (PC 0) (CF []) rom) by (rewrite cfill_nil; reflexivity).

assert (FIN : forall regs' (M : word -> option byte),
M = wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n)) ->
msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret M rom) ->
getr regs' 10 = at_ d 0 -> ms_agree regs regs' ->
exists regs'',
msteps MSEGS (mkst regs (PC 0) (CF []) rom)
(mkst regs'' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
/\ getr regs'' 10 = d /\ ms_agree regs regs'').
{ intros regs' M -> RUN P10 AG. exists regs'. rewrite at_0 in P10. auto. }
destruct (Z.lt_ge_cases n 9) as [Hsmall|Hn9].
{
destruct (Z.eq_dec n 0) as [Hz|Hnz].
{ destruct (A_exit0 mem0 d cv ret n rom Hn Hret regs H10 H11 H12 H1 Hz) as (r1 & RUN & P10 & AG).
eapply (FIN r1); try eassumption.
rewrite cfill_nil. rewrite Hz. reflexivity. }
destruct (Z.lt_ge_cases n 3) as [H3|H3].
{ destruct (A_exit2 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
eapply (FIN r1); try eassumption. cover ([(0,1); (n-1,1)]%Z). }
destruct (Z.lt_ge_cases n 7) as [H7|H7].
{ destruct (A_exit6 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
eapply (FIN r1); try eassumption. cover ([(0,1); (1,1); (2,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
destruct (A_exit8 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
eapply (FIN r1); try eassumption.
cover ([(0,1); (1,1); (2,1); (3,1); (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }

destruct (A_cont mem0 d cv ret n rom Hn Hnw Hok regs H10 H11 H12 H1 Hn9)
as (r1 & RUN1 & Q10 & Q11 & Q12 & Q13 & Q15 & Q1 & AG1).

set (k := ((- bv_unsigned d) mod 4)%Z).
pose proof (neg_mod4_range (bv_unsigned d)) as Hk. fold k in Hk.
pose proof (negw_and3 d) as Hkv. fold k in Hkv.
set (n1 := (n - k - (n - k) mod 4)%Z).
set (m1 := ((n - k) / 4)%Z).
pose proof (Z.div_mod (n - k) 4 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (n - k) 4 ltac:(lia)) as Hmb.
assert (Hm1 : (4 * m1 = n1)%Z) by (subst n1 m1; lia).
assert (Hn1 : (n - k - 3 <= n1 <= n - k)%Z) by (subst n1; lia).
pose proof (andi_m4 (n - k) ltac:(lia)) as Hn1v. fold n1 in Hn1v.
clearbody n1 m1. clear Hdm Hmb.
destruct (Z.lt_ge_cases n1 9) as [HB|HB].
{
destruct (B_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)
as (r2 & RUN2 & P10 & AG2).
eapply (FIN r2); [| eapply msteps_trans; [exact RUN1 | exact RUN2] | exact P10 | eapply ms_agree_trans; eassumption].
cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+n1-4,4); (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
destruct (B_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)
as (r2 & RUN2 & S10 & S11 & S12 & S13 & S14 & S1 & AG2).
destruct (Z.lt_ge_cases n1 25) as [HC|HC].
{ destruct (C_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 ltac:(lia) HC)
as (r3 & RUN3 & P10 & AG3).
eapply (FIN r3); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]]
| exact P10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
(n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
destruct (C_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 HC)
as (r3 & RUN3 & T10 & T11 & T12 & T13 & T14 & T1 & AG3).
destruct (andi_4_cases (at_ d k)) as (s4 & Hs4v & Hs4).
destruct (Z.lt_ge_cases (n1 - s4 - 24) 32) as [HD|HD].
{ destruct (D_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)
as (r4 & RUN4 & P10 & AG4).
eapply (FIN r4); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 |
eapply msteps_trans; [exact RUN3 | exact RUN4]]]
| exact P10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+12,4); (k+16,4); (k+20,4); (k+24,4);
(k+n1-28,4); (k+n1-24,4); (k+n1-20,4); (k+n1-16,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
(n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
destruct (D_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)
as (r4 & RUN4 & U10 & U11 & U12 & U14 & U15 & U1 & AG4).
destruct (E_run mem0 d cv ret n rom k n1 s4 Hs4 r4 (LD n k n1 s4) U10 U11 U12 U14 U15 U1 Hn9 ltac:(lia))
as (r5 & RUN5 & V10 & V11 & V12 & V13 & V14 & V1 & AG5).

set (r := (n1 - s4 - 24)%Z) in *.
set (q := Z.to_nat (r / 32 - 1)).
assert (Hq : (32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod r 32 ltac:(lia)). pose proof (Z.mod_pos_bound r 32 ltac:(lia)). lia. }
destruct (loop_run mem0 d cv ret n rom Hnw Hok q r5 (LD n k n1 s4) (k + s4 + 24)%Z r
V10 V11 V12 V13 V14 V1 ltac:(lia) ltac:(lia) Hq)
as (r6 & RUN6 & W10 & W1 & AG6).
destruct (ret_run ret rom Hret r6 (CF (((k + s4 + 24)%Z, (32 * (Z.of_nat q + 1))%Z) :: LD n k n1 s4)) W1)
as (r7 & RUN7 & ->).
eapply (FIN r6); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 |
eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 |
eapply msteps_trans; [exact RUN5 | eapply msteps_trans; [exact RUN6 | exact RUN7]]]]]]
| exact W10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+12,4); (k+16,4); (k+20,4); (k+24,4);
(k+s4+24, 32 * (Z.of_nat q + 1));
(k+n1-28,4); (k+n1-24,4); (k+n1-20,4); (k+n1-16,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
(n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z).
Qed.

End Summary.

Definition ms_entry : word := ltac:(let l := word_lit (Z_to_bv 64 ms_base) in exact l).

End Mq2.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU0c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU0c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJ4Q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJ4Q.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo8J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo8J.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHup.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG64.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWZn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWZn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qrlk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrlk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiyH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiyH.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MIS.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.

#[local] Notation MK := (memk mem0 dst bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.

Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
Ltac msb F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].

Ltac cond :=
rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
rewrite ?land_3 by lia; lia.
Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac sbp := apply sb_val_plain.

Lemma b4_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 4 <= n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb6e0 : word) (MK k) rom) (mkst regs' (0xdb70c : word) (MK (k + 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
- mlbu F_db704 D_db704 k. mlbu F_db708 D_db708 (k+1)%Z. mlbu F_db70c D_db70c (k+2)%Z. mlbu F_db710 D_db710 (k+3)%Z.
stepn F_db714 D_db714.
stepn F_db718 D_db718.
msb F_db71c D_db71c k ltac:(sbp). msb F_db720 D_db720 (k+1)%Z ltac:(sbp).
msb F_db724 D_db724 (k+2)%Z ltac:(sbp). msb F_db728 D_db728 (k+3)%Z ltac:(sbp).
stepn F_db72c D_db72c.
mk_eq. apply mst_refl.
- post.
Qed.

Lemma b8_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 8 <= n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb68c : word) (MK k) rom) (mkst regs' (0xdb6d8 : word) (MK (k + 8)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
- mlbu F_db6b0 D_db6b0 k. mlbu F_db6b4 D_db6b4 (k+1)%Z. mlbu F_db6b8 D_db6b8 (k+2)%Z. mlbu F_db6bc D_db6bc (k+3)%Z.
mlbu F_db6c0 D_db6c0 (k+4)%Z. mlbu F_db6c4 D_db6c4 (k+5)%Z. mlbu F_db6c8 D_db6c8 (k+6)%Z. mlbu F_db6cc D_db6cc (k+7)%Z.
stepn F_db6d0 D_db6d0.
msb F_db6d4 D_db6d4 k ltac:(sbp). msb F_db6d8 D_db6d8 (k+1)%Z ltac:(sbp).
msb F_db6dc D_db6dc (k+2)%Z ltac:(sbp). msb F_db6e0 D_db6e0 (k+3)%Z ltac:(sbp).
stepn F_db6e4 D_db6e4.
msb F_db6e8 D_db6e8 (k+4)%Z ltac:(sbp). msb F_db6ec D_db6ec (k+5)%Z ltac:(sbp).
msb F_db6f0 D_db6f0 (k+6)%Z ltac:(sbp). msb F_db6f4 D_db6f4 (k+7)%Z ltac:(sbp).
stepn F_db6f8 D_db6f8.
mk_eq. apply mst_refl.
- post.
Qed.

Lemma b16_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 16 <= n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb5f8 : word) (MK k) rom) (mkst regs' (0xdb684 : word) (MK (k + 16)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
- mlbu F_db61c D_db61c k. mlbu F_db620 D_db620 (k+1)%Z. mlbu F_db624 D_db624 (k+2)%Z. mlbu F_db628 D_db628 (k+3)%Z.
mlbu F_db62c D_db62c (k+4)%Z. mlbu F_db630 D_db630 (k+5)%Z. mlbu F_db634 D_db634 (k+6)%Z. mlbu F_db638 D_db638 (k+7)%Z.
msb F_db63c D_db63c k ltac:(sbp). msb F_db640 D_db640 (k+1)%Z ltac:(sbp).
msb F_db644 D_db644 (k+2)%Z ltac:(sbp). msb F_db648 D_db648 (k+3)%Z ltac:(sbp).
mlbu F_db64c D_db64c (k+8)%Z. mlbu F_db650 D_db650 (k+9)%Z. mlbu F_db654 D_db654 (k+10)%Z. mlbu F_db658 D_db658 (k+11)%Z.
msb F_db65c D_db65c (k+4)%Z ltac:(sbp). msb F_db660 D_db660 (k+5)%Z ltac:(sbp).
msb F_db664 D_db664 (k+6)%Z ltac:(sbp). msb F_db668 D_db668 (k+7)%Z ltac:(sbp).
mlbu F_db66c D_db66c (k+12)%Z. mlbu F_db670 D_db670 (k+13)%Z. mlbu F_db674 D_db674 (k+14)%Z. mlbu F_db678 D_db678 (k+15)%Z.
stepn F_db67c D_db67c.
msb F_db680 D_db680 (k+8)%Z ltac:(sbp). msb F_db684 D_db684 (k+9)%Z ltac:(sbp).
msb F_db688 D_db688 (k+10)%Z ltac:(sbp). msb F_db68c D_db68c (k+11)%Z ltac:(sbp).
stepn F_db690 D_db690.
msb F_db694 D_db694 (k+12)%Z ltac:(sbp). msb F_db698 D_db698 (k+13)%Z ltac:(sbp).
msb F_db69c D_db69c (k+14)%Z ltac:(sbp). msb F_db6a0 D_db6a0 (k+15)%Z ltac:(sbp).
stepn F_db6a4 D_db6a4.
mk_eq. apply mst_refl.
- post.
Qed.

Lemma t4_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb3b4 : word) (MK k) rom) (mkst regs' (0xdb70c : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
- eexists. split.
+ stepn F_db3d8 D_db3d8.
stepb_ft F_db3dc D_db3dc ltac:(cond).
stepn F_db3e0 D_db3e0.
mk_eq. apply mst_refl.
+ post.
- eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb6e0 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_db3d8 D_db3d8.
stepb_tk F_db3dc D_db3dc ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Lemma b8_tail : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb6d8 : word) (MK k) rom) (mkst regs' (0xdb70c : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
- eexists. split.
+ stepn F_db6fc D_db6fc.
stepb_tk F_db700 D_db700 ltac:(cond).
mk_eq. apply mst_refl.
+ post.
- eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb6e0 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_db6fc D_db6fc.
stepb_ft F_db700 D_db700 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Lemma t8_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
(k + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb3ac : word) (MK k) rom)
(mkst regs' (0xdb70c : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
destruct HL8 as [HL8|HL8].
-
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb3b4 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_db3d0 D_db3d0.
stepb_ft F_db3d4 D_db3d4 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb68c : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_db3d0 D_db3d0.
stepb_tk F_db3d4 D_db3d4 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb6d8 : word) (MK (k + 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL8. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Lemma b16_tail : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
(k + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb684 : word) (MK k) rom)
(mkst regs' (0xdb70c : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
destruct HL8 as [HL8|HL8].
- eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb3b4 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_db6a8 D_db6a8.
stepb_tk F_db6ac D_db6ac ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb68c : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_db6a8 D_db6a8.
stepb_ft F_db6ac D_db6ac ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb6d8 : word) (MK (k + 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Lemma t16_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 32)%Z -> (0 <= k)%Z ->
(k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb3a4 : word) (MK k) rom)
(mkst regs' (0xdb70c : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
-
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb3ac : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_db3c8 D_db3c8.
stepb_ft F_db3cc D_db3cc ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb5f8 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_db3c8 D_db3c8.
stepb_tk F_db3cc D_db3cc ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb684 : word) (MK (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
