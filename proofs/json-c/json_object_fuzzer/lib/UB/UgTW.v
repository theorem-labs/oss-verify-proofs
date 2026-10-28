(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3 QWxq Qc3B QlEo Lib.GwApply QsjA QZAi Ql2m QqdR QYTG QnDM UjdK U4l4 UxrO Um2h UDgQ Q8Ie UzOj QSCw Qbz7 UTru U3Uw UrBC UeSv UwP2 U0Ae UTa4 UM4C UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3.Mq2 QWxq.Mq0 Qc3B QlEo.Mq0 QWxq.Mq1 Q5Rg.Mq0.

Import QZAi.Mq1 Ql2m.Mq3 QZAi QqdR QYTG.Mq2.
Import QnDM.
Import UjdK U4l4 UxrO Um2h UDgQ.
Import Q8Ie.
Import UzOj.
Import QSCw Qbz7.
Import UTru U3Uw.Mq0.
Import UrBC UeSv UwP2 U0Ae UTa4 UM4C.
Import UEQM.
Import ListNotations.
Import QlEo.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition FMT_ld : list Z := [37; 108; 100; 0].
Definition FMT_lu : list Z := [37; 108; 117; 0].
Definition FMT_u00cc : list Z := [92; 117; 48; 48; 37; 99; 37; 99; 0].
Definition A_FMT_ld : Z := 0x12b29.
Definition A_FMT_lu : Z := 0x10822.
Definition A_FMT_u00cc : Z := 0x113f0.

Lemma fmt_ld_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m A_FMT_ld (zb FMT_ld).
Proof. intros m MI. apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_ld; lia | unfold A_FMT_ld, zlength; cbn; lia]. Qed.
Lemma fmt_lu_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m A_FMT_lu (zb FMT_lu).
Proof. intros m MI. apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_lu; lia | unfold A_FMT_lu, zlength; cbn; lia]. Qed.
Lemma fmt_u00cc_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m A_FMT_u00cc (zb FMT_u00cc).
Proof. intros m MI. apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_u00cc; lia | unfold A_FMT_u00cc, zlength; cbn; lia]. Qed.

Definition dec_text (i : Z) : list Z :=
if i <? 0 then 45 :: dec_digits (- i) else if i =? 0 then [48] else dec_digits i.

Lemma dec_text_length : forall i, -2^63 <= i < 2^64 -> 1 <= zlength (dec_text i) <= 20.
Proof.
intros i Hi. unfold dec_text.
destruct (Z.ltb_spec0 i 0).
- pose proof (dec_digits_pos_length (- i) ltac:(lia)).
pose proof (dec_digits_len_bound 19 (- i) ltac:(cbn; lia) ltac:(lia)). unfold zlength. cbn [length]. lia.
- destruct (Z.eqb_spec i 0); [unfold zlength; cbn; lia|].
pose proof (dec_digits_pos_length i ltac:(lia)). pose proof (dec_digits_length i). unfold zlength. lia.
Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zb1 :=
match goal with
| |- context [?a <=? ?b] => first [replace (a <=? b) with true by (symmetry; apply Z.leb_le; lia) | replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia)]
| |- context [?a <? ?b] => first [replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia)]
| |- context [?a =? ?b] => first [replace (a =? b) with true by (symmetry; apply Z.eqb_eq; lia) | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; lia)]
end; cbn [andb orb negb]; cbv beta iota.
Ltac fl0 := rewrite ?FL1, ?FL2, ?FL3, ?FL4, ?FL5; cbn [negb orb andb].
Ltac lhs_cbv1 := match goal with |- ?l = _ => let l' := eval cbv -[conv_pieces dec_digits] in l in change l with l' end.
Ltac lhs_cbv2 := match goal with |- ?l = _ => let l' := eval cbv -[int_pieces Z.modulo Z.pow Z.ltb INTMAX_MAX Z.opp dec_digits] in l in change l with l' end.

Lemma printf_pieces_ld_pos : forall x, 1 <= x < 2^63 ->
printf_pieces FMT_ld [PA_li x] = Some ([[]; []; dec_digits x], zlength (dec_digits x)).
Proof.
intros x Hx. unfold printf_pieces. lhs_cbv1. unfold conv_pieces. lhs_cbv2.
rewrite Z.mod_small by lia. unfold INTMAX_MAX. zb1.
unfold int_pieces. cbv beta iota zeta delta [andb Z.ltb].
pose proof (dec_digits_pos_length x ltac:(lia)). pose proof (dec_digits_length x).
zb1. rewrite tail_pieces_d by (unfold zlength; cbn [length]; lia). reflexivity.
Qed.

Lemma printf_pieces_ld_neg : forall x, -2^63 <= x < 0 ->
printf_pieces FMT_ld [PA_li x] = Some ([[]; [45]; dec_digits (- x)], 1 + zlength (dec_digits (- x))).
Proof.
intros x Hx. unfold printf_pieces. lhs_cbv1. unfold conv_pieces. lhs_cbv2.
replace (x mod 2 ^ 64) with (x + 2^64) by (apply Z.mod_unique with (q := -1); lia).
unfold INTMAX_MAX. zb1.
replace ((- (x + 2 ^ 64)) mod 2 ^ 64) with (- x) by (apply Z.mod_unique with (q := -1); lia).
unfold int_pieces. cbv beta iota zeta delta [andb Z.ltb].
pose proof (dec_digits_pos_length (- x) ltac:(lia)). pose proof (dec_digits_len_bound 19 (- x) ltac:(cbn; lia) ltac:(lia)).
pose proof (dec_digits_length (- x)).
zb1. rewrite tail_pieces_d by (unfold zlength; cbn [length]; lia). reflexivity.
Qed.

Lemma printf_pieces_lu_pos : forall x, 1 <= x < 2^64 ->
printf_pieces FMT_lu [PA_lu x] = Some ([[]; []; dec_digits x], zlength (dec_digits x)).
Proof.
intros x Hx. unfold printf_pieces. lhs_cbv1. unfold conv_pieces. lhs_cbv2.
unfold int_pieces. cbv beta iota zeta delta [andb Z.ltb].
pose proof (dec_digits_pos_length x ltac:(lia)). pose proof (dec_digits_length x).
zb1. rewrite tail_pieces_d by (unfold zlength; cbn [length]; lia). reflexivity.
Qed.

Theorem printf_sn_ld : forall i, -2^63 <= i < 2^63 ->
printf_model OUT_sn OUTFP_sn FMT_ld [PA_li i] [] = QlEo.Mq0.Ret (Ok (zlength (dec_text i), dec_text i)).
Proof.
intros i Hi. unfold dec_text.
destruct (Z.eq_dec i 0) as [->|NZ].
{ vm_compute. reflexivity. }
destruct (Z.ltb_spec0 i 0).
- pose proof (dec_digits_len_bound 19 (- i) ltac:(cbn; lia) ltac:(lia)) as L.
rewrite (printf_model_sn _ _ _ _ (printf_pieces_ld_neg i ltac:(lia))); cbn [concat app]; rewrite ?app_nil_r.
+ unfold zlength. cbn [length]. repeat f_equal. lia.
+ unfold zlength, SN_CAP in *. cbn [length]. lia.
- zb1. pose proof (dec_digits_length i) as L.
rewrite (printf_model_sn _ _ _ _ (printf_pieces_ld_pos i ltac:(lia))); cbn [concat app]; rewrite ?app_nil_r; [reflexivity|].
unfold zlength, SN_CAP in *. lia.
Qed.

Theorem printf_sn_lu : forall u, 0 <= u < 2^64 ->
printf_model OUT_sn OUTFP_sn FMT_lu [PA_lu u] [] = QlEo.Mq0.Ret (Ok (zlength (dec_text u), dec_text u)).
Proof.
intros u Hu. unfold dec_text. zb1.
destruct (Z.eq_dec u 0) as [->|NZ].
{ vm_compute. reflexivity. }
zb1. pose proof (dec_digits_length u) as L.
rewrite (printf_model_sn _ _ _ _ (printf_pieces_lu_pos u ltac:(lia))); cbn [concat app]; rewrite ?app_nil_r; [reflexivity|].
unfold zlength, SN_CAP in *. lia.
Qed.

Ltac lhs_cbvc := match goal with |- ?l = _ => let l' := eval cbv -[Z.modulo] in l in change l with l' end.
Theorem printf_sn_u00cc : forall c1 c2,
printf_model OUT_sn OUTFP_sn FMT_u00cc [PA_i c1; PA_i c2] [] = QlEo.Mq0.Ret (Ok (6, [92; 117; 48; 48; c1 mod 256; c2 mod 256])).
Proof.
intros c1 c2.
assert (P : printf_pieces FMT_u00cc [PA_i c1; PA_i c2] = Some ([[92; 117; 48; 48]; []; []; [c1 mod 256]; []; []; [c2 mod 256]], 6)).
{ lhs_cbvc. reflexivity. }
rewrite (printf_model_sn _ _ _ _ P); [reflexivity|]. unfold zlength, SN_CAP. cbn. lia.
Qed.

Lemma pass1_ok_ld : pass1_ok FMT_ld = true. Proof. reflexivity. Qed.
Lemma pass1_ok_lu : pass1_ok FMT_lu = true. Proof. reflexivity. Qed.
Lemma pass1_ok_u00cc : pass1_ok FMT_u00cc = true. Proof. reflexivity. Qed.
Lemma fp_calls_ld : forall i, fp_calls (length FMT_ld) FMT_ld [PA_li i] = []. Proof. reflexivity. Qed.
Lemma fp_calls_lu : forall u, fp_calls (length FMT_lu) FMT_lu [PA_lu u] = []. Proof. reflexivity. Qed.
Lemma fp_calls_u00cc : forall c1 c2, fp_calls (length FMT_u00cc) FMT_u00cc [PA_i c1; PA_i c2] = []. Proof. reflexivity. Qed.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.

Definition snprintf_ld_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (n i : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word),
let q := bv_unsigned sp in let D := bv_unsigned a0 in
a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_ld ->
-2^63 <= i < 2^63 -> bv_unsigned a3 = i mod 2^64 ->
rw_cells rsegs m D [CB dn junkd] -> (21 <= dn)%nat -> (21 <= n < 2^63) ->
stk rsegs m lo q -> (lo <= q - SNPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
evt rsegs (snprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn (dec_text i) (zlength (dec_text i)) junkd lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 snprintf_entry) fc None m (seg_rom rsegs)).

Theorem snprintf_ld_proof : snprintf_ld_stmt.
Proof.
unfold snprintf_ld_stmt. intros until canary. cbv zeta. intros Ha1 Ha2 Hi Ha3 DST Hdn Hn ST LO GLO QHI SSP MI FRM DD1 GD.
pose proof (dec_text_length i ltac:(lia)) as L.
eapply snprintf_gen_proof with (fmt := FMT_ld) (args := [PA_li i]);
[ exact Ha1 | exact Ha2 | exact DST | apply fmt_ld_bytes; exact MI | unfold FMT_ld; forall_range | apply pass1_ok_ld
| repeat constructor | cbn; split; [split; [exact Hi | exact Ha3] | exact I] | apply printf_sn_ld; exact Hi
| rewrite fp_calls_ld; apply Forall_nil
| unfold zlength in L; lia | lia | lia | exact ST | exact LO | exact GLO | exact QHI | exact SSP | exact MI | exact FRM
| unfold A_FMT_ld; lia | unfold A_FMT_ld, STATIC_SPLIT, zlength; cbn; lia | exact DD1 | exact GD ].
Qed.

Definition snprintf_lu_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (n u : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word),
let q := bv_unsigned sp in let D := bv_unsigned a0 in
a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_lu ->
bv_unsigned a3 = u ->
rw_cells rsegs m D [CB dn junkd] -> (21 <= dn)%nat -> (21 <= n < 2^63) ->
stk rsegs m lo q -> (lo <= q - SNPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
evt rsegs (snprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn (dec_text u) (zlength (dec_text u)) junkd lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 snprintf_entry) fc None m (seg_rom rsegs)).

Theorem snprintf_lu_proof : snprintf_lu_stmt.
Proof.
unfold snprintf_lu_stmt. intros until canary. cbv zeta. intros Ha1 Ha2 Ha3 DST Hdn Hn ST LO GLO QHI SSP MI FRM DD1 GD.
pose proof (bv_unsigned_in_range 64 a3) as Ru. unfold bv_modulus in Ru. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ru. rewrite Ha3 in Ru.
pose proof (dec_text_length u ltac:(lia)) as L.
eapply snprintf_gen_proof with (fmt := FMT_lu) (args := [PA_lu u]);
[ exact Ha1 | exact Ha2 | exact DST | apply fmt_lu_bytes; exact MI | unfold FMT_lu; forall_range | apply pass1_ok_lu
| repeat constructor | cbn; split; [split; [lia | exact Ha3] | exact I] | apply printf_sn_lu; lia
| rewrite fp_calls_lu; apply Forall_nil
| unfold zlength in L; lia | lia | lia | exact ST | exact LO | exact GLO | exact QHI | exact SSP | exact MI | exact FRM
| unfold A_FMT_lu; lia | unfold A_FMT_lu, STATIC_SPLIT, zlength; cbn; lia | exact DD1 | exact GD ].
Qed.

Definition snprintf_u00cc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (n c1 c2 : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word),
let q := bv_unsigned sp in let D := bv_unsigned a0 in
a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_u00cc ->
-2^31 <= c1 < 2^31 -> bv_unsigned a3 mod 2^32 = c1 mod 2^32 ->
-2^31 <= c2 < 2^31 -> bv_unsigned a4 mod 2^32 = c2 mod 2^32 ->
rw_cells rsegs m D [CB dn junkd] -> (7 <= dn)%nat -> (7 <= n < 2^63) ->
stk rsegs m lo q -> (lo <= q - SNPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
evt rsegs (snprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn [92; 117; 48; 48; c1 mod 256; c2 mod 256] 6 junkd lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 snprintf_entry) fc None m (seg_rom rsegs)).

Theorem snprintf_u00cc_proof : snprintf_u00cc_stmt.
Proof.
unfold snprintf_u00cc_stmt. intros until canary. cbv zeta. intros Ha1 Ha2 Hc1 Ha3 Hc2 Ha4 DST Hdn Hn ST LO GLO QHI SSP MI FRM DD1 GD.
eapply snprintf_gen_proof with (fmt := FMT_u00cc) (args := [PA_i c1; PA_i c2]).
all: first [ exact Ha1 | exact Ha2 | exact DST | apply fmt_u00cc_bytes; exact MI | (unfold FMT_u00cc; forall_range) | apply pass1_ok_u00cc
| apply printf_sn_u00cc | (rewrite fp_calls_u00cc; apply Forall_nil)
| (cbn; split; [split; [exact Hc1 | exact Ha3] | split; [split; [exact Hc2 | exact Ha4] | exact I]])
| exact ST | exact LO | exact GLO | exact QHI | exact SSP | exact MI | exact FRM | exact DD1 | exact GD
| solve [repeat constructor]
| (unfold A_FMT_u00cc, STATIC_SPLIT, zlength; cbn; lia)
| match goal with |- ?g => idtac "LEFT" g end ].
Qed.

Lemma wview_static : forall m a, wview rsegs (fun _ => None) a <> None -> wview rsegs m a <> None.
Proof. intros m a H. unfold wview in *. destruct (m a); [discriminate | exact H]. Qed.

Lemma wr_at_static8 : forall m A, (0 <= A)%Z -> (A + 8 <= 2^64)%Z ->
(forall i, (0 <= i < 8)%Z -> wview rsegs (fun _ => None) (wa (A + i)) <> None) -> wr_at rsegs m A 8.
Proof. intros m A H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros i Hi. apply wview_static. apply H. exact Hi. Qed.

Ltac static8 :=
intros i Hi;
assert (Hc : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%Z) by lia;
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; discriminate.

Lemma ssp_cells_of_bytes_at : forall m g,
bytes_at rsegs m got_ssp (le8 (Z_to_bv 64 ssp_guard)) -> bytes_at rsegs m ssp_guard (le8 g) -> ssp_cells m g.
Proof.
intros m g H1 H2. unfold ssp_cells. unfold got_ssp, ssp_guard in *.
split; (split; [split; [cbn; repeat split | cbn [cells_bytes cbytes app]; rewrite app_nil_r; assumption] | apply wr_at_static8; [lia | lia | static8]]).
Qed.
End Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QdBa QfYR QfcC Lib.SepCache QDUx Q9Ay Qy5Y QPUx UeMs Q7wb UzHs U6hf UuJ9 UxDK Uoo0 UnKY UqYW U3qs QCqH QaBw UscZ U55E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3.Mq2 QWxq.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM.
Import QDUx Q9Ay.
Import Qy5Y QPUx.
Import UeMs.Mq0.
Import Q7wb.
Import U4l4 UzHs UDgQ U6hf UuJ9 UxDK Uoo0 UnKY UqYW U3qs.
Import QCqH QaBw.
Import UscZ.

Import UEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac hush := idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac br K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); try (exfalso; lia).
Tactic Notation "callx" tactic3(tac) := callw tac; try (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end).

Lemma strtod_file_raw : forall T p txt (fl : word) p0 (c24 c32 c40 c48 c56 c64 c72 c80 c96 c104 c112 fd pp c128 md lk lbf : word) p1 (c152 c160 c168 c176 c184 c192 c200 c208 c216 c224 : word),
let J := mkJ fl p0 c24 c32 c40 c48 c56 c64 c72 c80 c96 c104 c112 fd pp c128 md lk lbf p1 c152 c160 c168 c176 c208 c216 c224 in
let f := mkSh txt 0 0 0 false false in
rf_cells_raw T p true f J c184 c192 c200 =
[C4 fl; CB 4 p0; C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 18446744073709551615); C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72; C8 c80;
C8 (Z_to_bv 64 T); C8 c96; C8 c104; C8 c112; C4 fd; C4 pp; C8 c128; C4 md; C4 lk; C4 lbf; CB 4 p1;
C8 c152; C8 c160; C8 c168; C8 c176; C8 c184; C8 c192; C8 c200; C8 c208; C8 c216; C8 c224].
Proof. intros. unfold rf_cells_raw, rf_rend. cbn. rewrite Z.add_0_r. reflexivity. Qed.

Theorem rstrtod_proof : rstrtod_stmt.
Proof.
unfold rstrtod_stmt. intros until ev. intros BY BYT Htxt Hpre Hlen Hlt PEC HS ST LO GT SPH Tpos HT T1 HPE HPE2 SEPE [SSP1 SSP2] ERR MI FRM Htp Ha0 Ha1.
cbv delta [rsegs] in *. fold rsegs in *.
unfold RSTRTOD_DEPTH, RGLOBALS_TOP, RIMG_LO, RATP in *. unfold UeMs.Mq0.RERRNO in *. unfold got_ssp, ssp_guard in SSP1, SSP2.
subst tp a0 a1.
pose_word_ranges.
assert (LT : length (map (Z_to_bv 8) txt) = length txt) by apply length_map.
assert (Hp : (0 <= zlength pre < zlength txt)%Z) by (subst txt; unfold zlength; rewrite length_app; cbn; lia).
unfold zlength in Hlt, SEPE, HT. unfold RGLOBALS_TOP in HT.
pose proof (munch_refl [(lo, bv_unsigned sp); (PE, PE + 8); (490332, 490332 + 4)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.

set (f0 := mkSh txt 0 0 0 false false).
pose proof HS as HS'. unfold scan_strtod in HS'. change (mkSh txt 0 0 0 false false) with f0 in HS'.
destruct (floatscan (fuel_of txt) f0 1 1) as [[fR yR]|] eqn:HM; [|discriminate HS'].
injection HS' as Ebits Eused.
assert (Hnul : znth txt (zlength pre) = 0%Z) by (subst txt; apply znth_app_mid).
assert (Hnum : forall i, (0 <= i < zlength pre)%Z -> is_numch (znth txt i) = true).
{ intros i Hi. subst txt. rewrite znth_app_pre by exact Hi. exact (proj1 (Forall_forall _ _) Hpre _ (znth_In' pre i Hi)). }
assert (OK0 : sh_ok T txt f0).
{ unfold sh_ok, f0. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio]. unfold zlength in *. repeat split; try reflexivity; try lia; try (intros X; discriminate X). }
unfold RSTRTOD.

zs.
carve_frame 40%nat ST. rename FR into FRT.
carve_frame 232%nat ST. rename FR into FILE.
destruct (file_cells_of_junk _ _ _ _ FILE) as (fl & p0 & w8 & w16 & c24 & c32 & c40 & c48 & c56 & c64 & c72 & c80 & w88 & c96 & c104 & c112 & fd & pp & c128 & md & lk & lbf & p1 & c152 & c160 & c168 & c176 & c184 & c192 & c200 & c208 & c216 & c224 & FC & L0 & L1).
clear FILE. match goal with H : list byte |- _ => try clear H end.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
zs. zs. zs. zs.

set (J := mkJ fl p0 c24 c32 c40 c48 c56 c64 c72 c80 c96 c104 c112 fd pp c128 md lk lbf p1 c152 c160 c168 c176 c208 c216 c224).
rewrite <- (strtod_file_raw T (zlength pre) txt fl p0 c24 c32 c40 c48 c56 c64 c72 c80 c96 c104 c112 fd pp c128 md lk lbf p1 c152 c160 c168 c176 c184 c192 c200 c208 c216 c224) in FC.
fold J f0 in FC.
assert (RJ0 : RFJ T txt (zlength pre) true J 0 1 f0).
{ unfold RFJ, f0. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. split; [exact OK0|].
repeat split; try lia; intros X; try discriminate X; try lia. }
pose proof shlim_spec as SL. unfold shlim_stmt in SL.
zs. zs. zs. callx (eapply SL with (Fp := (bv_unsigned sp + -272)%Z) (T := T) (p := zlength pre) (w := true) (txt := txt) (f := f0) (J := J);
[exact FC | exact OK0 | exact L0 | exact L1 | lia | lia | unfold zlength in *; lia | assumption]).
clear SL.
match goal with H : rw_cells _ _ _ (rf_cells _ _ _ (sh_lim0 f0) _) |- _ => rename H into FC1 end. change (sh_lim0 f0) with f0 in FC1.
match goal with H : stk _ _ lo _ |- _ => rename H into STK end.

zs. zs. zs. zs.
destruct (stk_split _ _ _ (bv_unsigned sp + -272 - 8656)%Z _ STK ltac:(lia)) as [STlo SThi].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (U55E.Mq0.L_ENTRY (Z_to_bv 64 0x5b554) (bv_unsigned sp + -272)%Z gp (Z_to_bv 64 PE) (Z_to_bv 64 T) (Z_to_bv 64 622192) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mm
(bv_unsigned sp + -272)%Z T (zlength pre) J txt pre post canary 1%Z (fuel_of txt) f0 0%Z 1%Z fR yR) as LE end.
specialize (LE HM ltac:(right; reflexivity) ltac:(intros X; exfalso; discriminate X) BYT Hp Hnul Hnum ltac:(unfold zlength in *; lia) ltac:(lia) T1
ltac:(unfold zlength in *; lia) ltac:(unfold UmCU.RERRNO, zlength in *; lia) ltac:(unfold UmCU.FS_DEPTH; lia) ltac:(lia) ltac:(lia)
ltac:(unfold UmCU.FS_DEPTH, zlength in *; lia) ltac:(unfold UmCU.FS_DEPTH, ssp_guard; lia) ltac:(unfold got_ssp, zlength in *; lia) ltac:(unfold ssp_guard, zlength in *; lia) ltac:(lia) FRM).
cbv zeta in LE. unfold UmCU.FS_DEPTH, UmCU.RERRNO, UmCU.FLOATSCAN, UmCU.RATP in LE.
unfold UmCU.fs_post, UmCU.Wfs, UmCU.FS_DEPTH, UmCU.RERRNO, UmCU.FokR in LE.
callx (eapply LE; [ exact SThi | exact MI0 | exact FC1 | exact RJ0 | lia | lia | reflexivity | exact BY | split; [exact SSP1 | exact SSP2] | exact ERR ]).
clear LE.
match goal with H : rw_cells _ _ _ (rf_cells _ _ _ fR _) |- _ => rename H into FC2 end.
match goal with H : RFJ _ _ _ _ _ _ _ fR |- _ => rename H into RJ2 end.
match goal with H : ssp_cells _ canary |- _ => destruct H as [SSP3 SSP4]; unfold got_ssp, ssp_guard in SSP3, SSP4 end.
match goal with H : stk _ ?m' (bv_unsigned sp + -272 - 8656)%Z _ |- _ => pose proof (stk_merge _ _ _ _ _ STlo H ltac:(lia)) as STK2; clear H STlo end.
match goal with H : bytes_at _ _ T (zbytes txt) |- _ => rename H into BY2; unfold zbytes in BY2 end.
match goal with H : frm0 ?x |- evt _ _ (MS _ _ _ ?x _ _ _) => rename H into FRM2 end.
match goal with H : forall k : reg, _ -> _ -> _ -> reg_get _ k = reg_get F k |- _ => rename H into FOK end.
pose proof RJ2 as RJ3. destruct RJ3 as (OK2 & Rc2 & CC2 & KM2 & NS2 & SS2). destruct OK2 as (Hbuf2 & Rl2 & Rr2 & Rc02 & Rn2 & Rst2).
assert (JRR : JR (zlength pre) fR).
{ unfold fuel_of in HM. eapply (floatscan_JR txt (zlength pre) BYT Hp Hnul Hnum _ _ _ _ _ HM).
unfold JF, f0. cbn. repeat split; try reflexivity; try lia; intros X; try discriminate X; lia. }
unfold JR in JRR.
pose proof FC2 as FC3. unfold rf_cells in FC3.
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale J] in FC3.
assert (RR : (0 <= rf_rend T (zlength pre) true fR <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio fR); unfold zlength in *; lia). unfold M64 in RR.

zs. (if_cases K0; zify_cond K0; try (rewrite ?signed_of_Z in K0 by lia); [ exfalso; lia | ]).
zs. zs. zs. zs. zs. zs. zs.
match goal with H : rw_cells _ _ PE [C8 (Z_to_bv 64 ?v)] |- _ => replace v with (T + used)%Z in H by (rewrite <- Eused; unfold sh_cnt; lia) end.

zs. callx (eapply trunctfdf2_spec; [eassumption]).
cbv delta [rsegs] in *. fold rsegs in *.
rewrite !ulit_lo64, !ulit_hi64.
change (lo64 yR + 2 ^ 64 * hi64 yR)%Z with (canon yR). rewrite Q9Ay.f128_to_d_canon. rewrite Ebits.

zs. zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]).
zs. zs. zs. zs. zs. zs.
match goal with H : stk _ ?m' lo _, H2 : mem_inv _ ?m' |- evt _ _ (MS _ _ _ _ _ ?m' _) => rename H into ST9; rename H2 into MI9 end.
release_frame FC3 ST9 (bv_unsigned sp + -40)%Z.
release_frame FRT ST9 (bv_unsigned sp).
apply evt_done. unfold rstrtod_post.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [unfold UmCU.RATP; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI9|]. split; [exact FRM2|].
split. { intros k H10 H14 H15. rewrite reg_get_set_other by (intros E; apply H10; rewrite <- E; reflexivity). exact (FOK k H10 H14 H15). }
split; [rewrite freg_get_same by (vm_compute; reflexivity); reflexivity|].
split; [exact ST9|]. split; [hyp|]. split; [exact BY2|]. split; [split; [exact SSP3 | exact SSP4]|]. split; [match goal with H : rw_cells _ _ 490332 _ |- _ => exact H end|].
rewrite <- Eused. unfold sh_cnt. lia.
Qed.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QULt.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UOpO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UOpO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Unip.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Unip. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UZr4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UZr4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Upt0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Upt0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UjdK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UjdK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlMT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlMT. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDnE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDnE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uh29.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uh29.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma img_byte_296e8 k : 0 <= k < 4 -> exists b, memory_read rsegs (wa (0x98320 + k)) 1 = Some [b].
Proof.
intros Hk.
assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) as [->|[->|[->| ->]]] by lia; eexists; vm_compute; reflexivity.
Qed.

#[using="Type"] Lemma read_malloc_replaced : forall m, exists w : word, ov_read_bytes rsegs m (wa 0x98320) 4 = Some (le4 w).
Proof.
intros m.
assert (G : forall a, (exists b, memory_read rsegs a 1 = Some [b]) -> exists b,
match m a with Some b => Some b | None => match memory_read rsegs a 1 with Some (b :: _) => Some b | _ => None end end = Some b).
{ intros a [b Hb]. destruct (m a) as [b'|]; [exists b'; reflexivity|]. rewrite Hb. exists b; reflexivity. }
cbn [ov_read_bytes].
destruct (G (wa 0x98320) ltac:(replace (wa 0x98320) with (wa (0x98320 + 0)) by reflexivity; apply img_byte_296e8; lia)) as [b0 ->].
rewrite !wa_succ.
destruct (G (wa (0x98320 + 1)) ltac:(apply img_byte_296e8; lia)) as [b1 ->].
replace (0x98320 + 1 + 1) with (0x98320 + 2) by lia.
destruct (G (wa (0x98320 + 2)) ltac:(apply img_byte_296e8; lia)) as [b2 ->].
replace (0x98320 + 2 + 1) with (0x98320 + 3) by lia.
destruct (G (wa (0x98320 + 3)) ltac:(apply img_byte_296e8; lia)) as [b3 ->].
exists (le_bytes_to_word [b0; b1; b2; b3]).
f_equal. symmetry. apply le4_of_mod32; [reflexivity|].
unfold le_bytes_to_word. rewrite bytes_le_to_Z_le_val.
pose proof (le_val_range (map bv_unsigned [b0; b1; b2; b3]) (bytes_ok_map _)) as R.
change (256 ^ Z.of_nat (length (map bv_unsigned [b0; b1; b2; b3]))) with (2^32) in R.
rewrite unsigned_lit by lia. apply Z.mod_small. lia.
Qed.

#[using="Type"] Lemma calloc_overflows_spec cnt sz : 0 <= cnt < 2^64 -> 0 <= sz < 2^64 ->
calloc_overflows cnt sz = true <-> 2^64 <= cnt * sz.
Proof.
intros HC HS. unfold calloc_overflows. rewrite andb_true_iff, negb_true_iff, Z.eqb_neq, Z.ltb_lt.
split.
- intros [NZ LT]. Z.div_mod_to_equations. nia.
- intros GE. assert (NZ : sz <> 0) by (intros ->; lia). split; [exact NZ|]. Z.div_mod_to_equations. nia.
Qed.

Section TOP.
Hypothesis RMI : rmalloc_impl_stmt.

#[using="RMI"] Theorem rcalloc_spec_proof : rcalloc_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB cnt sz lo B errv.
intros HP AV SB ST CLO LO ERR MI TP A0 A1 CNT SZ.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof CLO as CLOv. unfold alloc_ceiling in CLOv. unfold RCALLOC_STACK, RMALLOC_STACK in LO.
assert (ETP : bv_unsigned tp + -164 = 490332) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
pose proof HP as HP0.

unfold raw_calloc.
eapply (implM_bind rsegs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
{ apply implM_get. apply evt_done. repeat split; reflexivity. }
intros s0' s1' ms1 (-> & -> & ->). cbv beta.

match goal with |- implM _ ?t _ ?Q ?ms =>
assert (PRO : evt rsegs (fun ms' => exists m1,
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51f8c) fc None m1 (seg_rom rsegs)
/\ (exists fr0, rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 fr0; C8 s1; C8 s0; C8 ra])
/\ stk rsegs m1 lo (bv_unsigned sp + -32)
/\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1) ms) end.
{ pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl rsegs m) as WM.
unfold RCALLOC_SYM. carve_frame 32%nat ST.
step. step. step. step.
apply evt_done. eexists. split; [reflexivity|].
split; [eexists; exact FR|]. split; [exact ST|]. split; [exact MUs|]. split; [exact WM| exact MI]. }
eapply implM_evt; [exact PRO|]. clear PRO. cbv beta. intros ms1 (m1 & -> & [fr0 FR] & ST1 & MU1 & WM1 & MI1).
assert (DJ1 : forall a k, a + k <= lo -> disjoint_from [(bv_unsigned sp + -32, bv_unsigned sp)] a k) by (intros a9 k9 Hk9; cbn; lia).
assert (ERR1 : rw_cells rsegs m1 (errno_addr tp) [C4 errv]).
{ eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. apply DJ1. rewrite ETP. cbn. lia. }
assert (AV1 : rauxv_ok m1 B).
{ eapply rauxv_ok_frame; [exact AV| exact MU1| exact WM1|]. constructor; [|constructor]. cbn. unfold RAUXV_CELL. lia. }
assert (HP1 : RHEAP s LB m1).
{ eapply RHEAP_frame_proof; [exact HP0| exact MU1| exact WM1|]. constructor; [|constructor]. left. cbn. lia. }
assert (PRES1 : rheap_pres LB (bv_unsigned sp) m m1).
{ eapply rheap_pres_of_munch; [exact MU1| exact WM1|]. intros a Ha HC. cbn. split; [|exact I].
destruct HC as [HC|[HC|(b & Hb & HC)]]; [lia| lia|].
pose proof (RHEAP_block_range_proof _ _ _ _ HP0 Hb) as (_ & _ & _ & BC & _). unfold alloc_ceiling in BC. lia. }
subst a0 a1.

assert (PR : 0 <= sz * cnt <= (2^64 - 1) * (2^64 - 1)) by nia.
assert (HQ : 0 <= Z.shiftr (sz * cnt) 64 < 2^64).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
assert (HQ0 : Z.shiftr (sz * cnt) 64 = 0 <-> cnt * sz < 2^64).
{ rewrite Z.shiftr_div_pow2, (Z.mul_comm sz cnt) by lia. split; [| intros; apply Z.div_small; lia].
intros E0. Z.div_mod_to_equations. lia. }
destruct (calloc_overflows cnt sz) eqn:OV.
-
apply (proj1 (calloc_overflows_spec cnt sz CNT SZ)) in OV.
unfold ccalloc. rewrite (proj2 (calloc_overflows_spec cnt sz CNT SZ) OV). cbn [membed].
eapply (implM_bind rsegs _ _ _ (fun x sa msa => x = (ps_m s, None) /\ sa = s /\ msa = _)).
{ apply implM_ret. apply evt_done. repeat split; reflexivity. }
intros x sq msq (-> & -> & ->). cbv beta.
eapply (implM_bind rsegs _ _ _ (fun _ sx msx => sx = set_m (ps_m s) s /\ msx = _)).
{ apply implM_upd. apply evt_done. split; reflexivity. }
intros [] sx msx [-> ->]. apply implM_ret.
step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia. { exfalso. subst sz. lia. }
step. step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
{ exfalso. change 18446744073709551615 with (Z.ones 64) in K1. rewrite Z.land_ones, Z.mod_small in K1 by lia. apply HQ0 in K1. lia. }
try (change 18446744073709551615 with (Z.ones 64) in K1; rewrite Z.land_ones, Z.mod_small in K1 by lia).

step. step. step. step.

clear MU1 WM1. pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m1) as MU2.
pose proof (wmono_refl rsegs m1) as WM2.
step. step. step. step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m2 end.
release_frame FR ST1 (bv_unsigned sp).
apply evt_done. unfold rcalloc_post. do 15 eexists. exists m2, (Z_to_bv 64 12).
split; [reflexivity|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|].
split. { eapply rauxv_ok_frame; [exact AV1| exact MU2| exact WM2|]. unfold RAUXV_CELL.
constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
split. { eapply rheap_pres_trans; [exact PRES1|]. eapply rheap_pres_of_munch; [exact MU2| exact WM2|].
intros a Ha HC. cbn. unfold rclient_addr, ralloc_static, RLIBC, RMLOCK, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in HC.
destruct HC as [HC|[HC|(b & Hb & HC)]]; [lia| lia|].
pose proof (RHEAP_block_range_proof _ _ _ _ HP0 Hb) as (_ & _ & _ & BC & BI). unfold alloc_ceiling in BC. lia. }
split; [destruct (ps_fa s), (ps_fa (set_m (ps_m s) s)); reflexivity|]. split; [destruct (ps_so s), (ps_so (set_m (ps_m s) s)); reflexivity|].
split; [reflexivity|]. split; [reflexivity|].
apply (RHEAP_ext s); [| reflexivity| reflexivity].
eapply RHEAP_frame_proof; [exact HP1| exact MU2| exact WM2|].
constructor; [left; cbn; lia|]. constructor; [|constructor]. right; left. cbn. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
-
assert (NOVF : cnt * sz < 2^64).
{ destruct (Z.lt_ge_cases (cnt * sz) (2^64)) as [Hl|Hl]; [exact Hl|]. apply (proj2 (calloc_overflows_spec cnt sz CNT SZ)) in Hl. congruence. }
pose proof NOVF as NOV. set (N := cnt * sz) in *.
assert (N0 : 0 <= N) by (subst N; nia).
unfold ccalloc. rewrite OV. fold N.

eapply (implM_bind rsegs _ _ _ (fun x s' ms' => evt rsegs (rmalloc_post (Z_to_bv 64 0x51fcc) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp s0 (Z_to_bv 64 N) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB N lo B m1
(cm_conv (fst x) N (snd x)) (set_m (fst x) s')) ms')).
{ assert (J : forall a2v, implM rsegs (membed (cmalloc (ps_m s) N)) s
(fun x s' ms' => evt rsegs (rmalloc_post (Z_to_bv 64 0x51fcc) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp s0 (Z_to_bv 64 N) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB N lo B m1
(cm_conv (fst x) N (snd x)) (set_m (fst x) s')) ms')
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cnt) (Z_to_bv 64 sz) a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51fc0) fc None m1 (seg_rom rsegs))).
{ intros a2v.
eapply (implM_evt rsegs _ _ _ (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x51fcc) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 N) (Z_to_bv 64 N) (Z_to_bv 64 sz) a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m1 (seg_rom rsegs))).
{
step. rewrite !(unsigned_lit sz), !(unsigned_lit cnt) by lia. replace (sz * cnt) with N by (subst N; lia).
step. step. step. apply evt_done. reflexivity. }
intros ms' ->.
eapply (rmalloc_membed RMI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s LB N lo B errv);
try eassumption; try reflexivity; rewrite ?unsigned_lit by lia; unfold RMALLOC_STACK; try lia; try eassumption. }

eapply (implM_evt rsegs _ _ _ (fun ms' => exists a2v, ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cnt) (Z_to_bv 64 sz) a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51fc0) fc None m1 (seg_rom rsegs))).
{ step. if_cases K0; zify_cond K0; [apply evt_done; eexists; reflexivity|].
step. step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
2:{ exfalso. apply K1. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones, Z.mod_small by lia. apply HQ0. exact NOVF. }
apply evt_done; eexists; reflexivity. }
intros ms' [a2v ->]. apply J. }
intros [cs' op] s' ms' PM. cbv beta in PM. cbn [fst snd] in PM.
eapply implM_evt; [exact PM|]. clear PM. cbv beta. intros ms2 PM.
destruct PM as (u0 & u1 & u2 & ra0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AV2 & PRES2 & PSF & PSO & RES).
rewrite ?unsigned_lit in ST2, PRES2 by lia.
eapply (implM_bind rsegs _ _ _ (fun _ sx msx => sx = set_m cs' s' /\ msx = _)). { apply implM_upd. apply evt_done. split; reflexivity. }
intros [] sx msx [-> ->]. apply implM_ret.
replace (ret_pc (Z_to_bv 64 0x51fcc)) with (Z_to_bv 64 0x51fcc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32) [CB 8 fr0; C8 s1; C8 s0; C8 ra]).
{ eapply rheap_pres_rw_cells; [exact PRES2| exact FR|]. left. lia. }
assert (PRES02 : rheap_pres LB (bv_unsigned sp) m m2).
{ eapply rheap_pres_trans; [exact PRES1|]. eapply rheap_pres_weaken; [exact PRES2| lia| intros b Hb; exact Hb]. }
destruct op as [slot|]; cbn [cm_conv] in RES |- *.
2:{
destruct RES as (-> & E12 & HP2).

step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
step. step. step. step. step. step.
release_frame FR2 ST2 (bv_unsigned sp).
apply evt_done. unfold rcalloc_post. do 15 eexists. exists m2, errv2.
split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact AV2|].
split; [exact PRES02|]. split; [exact PSF|]. split; [exact PSO|]. split; [reflexivity|]. split; [exact E12| exact HP2]. }

destruct RES as (A & junk & -> & BR & HP2 & BLK & _ & ZJ).
pose proof BR as (A0p & A16 & _ & AC & AIMG). unfold alloc_ceiling in AC.
set (bnew := ((slot, fresh_off cs' slot N), A, N) : block) in *.
pose proof (RHEAP_blocks_nodup_proof _ _ _ HP2) as ND. cbn [map blk_id fst] in ND.
assert (DJA : forall a k, (a + k <= A \/ A + N <= a) -> disjoint_from [(A, A + N)] a k) by (intros a9 k9 Hk9; cbn; lia).

assert (FIN : forall (m4 : mem) (x0 x1 x2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x3 x4 x5 x6 : word),
munch [(A, A + N)] m2 m4 -> wmono rsegs m2 m4 -> mem_inv rsegs m4 ->
rw_cells rsegs m4 A [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))] ->
rcalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB N lo B m (Some (slot, fresh_off cs' slot N)) (set_m cs' s')
(MS (mkR ra sp gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 A) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6)
F (ret_pc ra) fc None m4 (seg_rom rsegs))).
{ intros m4 x0 x1 x2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x3 x4 x5 x6 MU4 WM4 MI4 ZER.
assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -32) [CB 8 fr0; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_transport; [exact FR2| exact MU4| exact WM4|]. apply DJA. cbn. lia. }
assert (ST4 : stk rsegs m4 lo (bv_unsigned sp + -32)).
{ eapply stk_transport_disjoint; [exact ST2| exact MU4| exact WM4|]. apply DJA. lia. }
release_frame FR4 ST4 (bv_unsigned sp).
unfold rcalloc_post. do 15 eexists. exists m4, errv2.
split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|].
split. { eapply rw_cells_transport; [exact ERR2| exact MU4| exact WM4|]. apply DJA. rewrite ETP. cbn. lia. }
split. { eapply rauxv_ok_frame; [exact AV2| exact MU4| exact WM4|]. constructor; [|constructor]. cbn. unfold RAUXV_CELL. lia. }
split. { eapply rheap_pres_trans; [exact PRES02|]. eapply rheap_pres_of_munch; [exact MU4| exact WM4|]. intros a Ha HC. cbn. split; [|exact I].
destruct HC as [HC|[HC|(b & Hb & HC)]]; [lia| lia|].
assert (NE2 : blk_id bnew <> blk_id b).
{ intros E. apply NoDup_cons_iff in ND as [NI _]. apply NI. cbn [bnew blk_id fst] in E |- *. rewrite E. apply in_map_iff. exists b. auto. }
pose proof (RHEAP_blocks_disjoint_proof _ _ _ bnew b HP2 ltac:(left; reflexivity) ltac:(right; exact Hb) NE2) as D.
cbn [bnew blk_addr blk_size fst snd] in D. lia. }
split; [exact PSF|]. split; [exact PSO|].
exists A. split; [reflexivity|]. split; [exact BR|]. split; [| exact ZER].
eapply RHEAP_frame_proof; [exact HP2| exact MU4| exact WM4|]. constructor; [|constructor].
right; right. exists bnew. split; [left; reflexivity|]. cbn. lia. }

assert (CLEAR : forall (xra xa0 xa1 xa2 xa3 xa4 xa5 xa6 : word),
evt rsegs (rcalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB N lo B m (Some (slot, fresh_off cs' slot N)) (set_m cs' s'))
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0 u1 u2 (Z_to_bv 64 A) (Z_to_bv 64 N) xa0 xa1 xa2 xa3 xa4 xa5 xa6 ua7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
F (Z_to_bv 64 0x51fe0) fc None m2 (seg_rom rsegs))).
{ intros.
eapply evt_cut. { eapply (zt_clear) with (p := A) (n := N); [exact BLK| lia| lia| lia| exact MI2]. }
cbv beta. intros ms3 (k & rax & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m3 & -> & HK & MU3 & WM3 & MI3 & ZT3).
assert (FR3 : rw_cells rsegs m3 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32))) [CB 8 fr0; C8 s1; C8 s0; C8 ra]).
{ rewrite unsigned_lit by lia. eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. apply DJA. cbn. lia. }
eapply evt_mono. { eapply (zt_tail) with (p := A) (n := N) (k := k); [exact ZT3| lia| lia| lia| exact MI3| exact FR3| rewrite unsigned_lit by lia; lia]. }
cbv beta. intros ms4 (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & m4 & -> & MU4 & WM4 & MI4 & ZER).
rewrite unsigned_lit by lia. replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
apply FIN; [eapply munch_trans; [exact MU3| exact MU4]| eapply wmono_trans; [exact WM3| exact WM4]| exact MI4| exact ZER]. }

step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia. { exfalso. lia. }
step. step. destruct (read_malloc_replaced m2) as [wrep RD]. change (wa 0x98320) with (Z_to_bv 64 623392) in RD.
step. step. if_cases K1.
2:{  apply CLEAR. }

step. step.
eapply evt_cut. { eapply (raz_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (set_m cs' s') (bnew :: LB) slot (fresh_off cs' slot N) A N HP2 ltac:(left; reflexivity) MI2 eq_refl). }
cbv beta. intros ms3 (v0 & v1 & v2 & v3 & v4 & v5 & v6 & -> & RZ).
replace (ret_pc (Z_to_bv 64 336044)) with (Z_to_bv 64 0x520ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

step. if_cases K2; zify_cond K2.
2:{  step. apply CLEAR. }
destruct (RZ K2) as (g & idx & SL & AZ). specialize (ZJ g idx SL AZ). subst junk.

step. step. step. step. step. step.
apply evt_done.
apply FIN; [apply munch_refl| apply wmono_refl| exact MI2| exact BLK].
Qed.
End TOP.

End RC__1.
