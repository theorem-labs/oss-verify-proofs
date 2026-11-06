(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW Qc27 Q13u QDM6 QJFf QwAs Qc6I QVsB Qcrs QCiC Qpj5 QCNF QoNr QdZp QHig Q0Do Q6sh QKTr QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 Q9Ho Qu3b QnRU QteI QQNJ QMPy QIG5 QC9y Qr5k QbPx_c1 QCqp Qi1S QHRw Qvzz Q8Kb QlES QXE1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Qc27 Q13u QDM6 QJFf.Mq0 QwAs.Mq1 Qc6I QJFf QVsB.

Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import Qu3b.Mq3.
Import QTVW.Mq1 Qu3b.Mq1 QnRU.Mq3 QnRU.Mq4 QteI.Mq1.
Import QCNF.Mq0 QQNJ.Mq3.
Import QMPy.
Import QIG5. Import QC9y.
Import Qr5k.Mq0 QbPx_c1.Mq0 QCqp.Mq0 Qi1S.Mq1 QCqp.Mq1 QHRw.Mq0 Qvzz.Mq0 Q8Kb.Mq0.
Import QlES.
Import QXE1.Mq0.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition FMT_ld : list Z := [37; 108; 100; 0].
Definition FMT_lu : list Z := [37; 108; 117; 0].
Definition FMT_u00cc : list Z := [92; 117; 48; 48; 37; 99; 37; 99; 0].
Definition A_FMT_ld : Z := 0x23700.
Definition A_FMT_lu : Z := 0x23720.
Definition A_FMT_u00cc : Z := 0x236a0.

Lemma fmt_ld_bytes : forall m, mem_inv asegs m -> bytes_at asegs m A_FMT_ld (zb FMT_ld).
Proof. intros m MI. apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_ld; lia | unfold A_FMT_ld, zlength; cbn; lia]. Qed.
Lemma fmt_lu_bytes : forall m, mem_inv asegs m -> bytes_at asegs m A_FMT_lu (zb FMT_lu).
Proof. intros m MI. apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_lu; lia | unfold A_FMT_lu, zlength; cbn; lia]. Qed.
Lemma fmt_u00cc_bytes : forall m, mem_inv asegs m -> bytes_at asegs m A_FMT_u00cc (zb FMT_u00cc).
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
printf_model OUT_sn OUTFP_sn FMT_ld [PA_li i] [] = Qc6I.Ret (Ok (zlength (dec_text i), dec_text i)).
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
printf_model OUT_sn OUTFP_sn FMT_lu [PA_lu u] [] = Qc6I.Ret (Ok (zlength (dec_text u), dec_text u)).
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
printf_model OUT_sn OUTFP_sn FMT_u00cc [PA_i c1; PA_i c2] [] = Qc6I.Ret (Ok (6, [92; 117; 48; 48; c1 mod 256; c2 mod 256])).
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

Lemma szone_fmt {BAND : Band} : forall A n, gzone A n -> szone A n.
Proof. intros A n G. unfold szone. right. right. right. exact G. Qed.

Section Jsonc.
Context {BAND : Band}.

Hypothesis PC_LD : pcommon_stmt A_FMT_ld.
Hypothesis PC_LU : pcommon_stmt A_FMT_lu.
Hypothesis PC_U00CC : pcommon_stmt A_FMT_u00cc.

Definition vsnprintf_ld_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (D n VA i : Z) (dn : nat) (junkd : list byte) (slot : word) (slots : list word)
(lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_ld -> a3 = Z_to_bv 64 VA ->
rw_cells asegs m D [CB dn junkd] -> ISH m ->
va_area m VA (slot :: slots) -> -2^63 <= i < 2^63 -> bv_unsigned slot = i mod 2^64 ->
(21 <= dn)%nat -> (21 <= n < 2^63) ->
stk asegs m lo q -> (lo <= q - VSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(q <= VA) -> (VA + 8 * zlength (slot :: slots) <= 2^47) ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength (slot :: slots) <= D) ->
dapp D (Z.of_nat dn) -> (forall k, 0 < k <= 20 -> rng_ok m D k) ->
evt asegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd (zlength (dec_text i)) (dec_text i) lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 vsnprintf_entry) fc None m (seg_rom asegs)).

Definition vsnprintf_lu_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (D n VA : Z) (dn : nat) (junkd : list byte) (slot : word) (slots : list word)
(lo : Z) (canary : word),
let q := bv_unsigned sp in let u := bv_unsigned slot in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_lu -> a3 = Z_to_bv 64 VA ->
rw_cells asegs m D [CB dn junkd] -> ISH m ->
va_area m VA (slot :: slots) ->
(21 <= dn)%nat -> (21 <= n < 2^63) ->
stk asegs m lo q -> (lo <= q - VSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(q <= VA) -> (VA + 8 * zlength (slot :: slots) <= 2^47) ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength (slot :: slots) <= D) ->
dapp D (Z.of_nat dn) -> (forall k, 0 < k <= 20 -> rng_ok m D k) ->
evt asegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd (zlength (dec_text u)) (dec_text u) lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 vsnprintf_entry) fc None m (seg_rom asegs)).

Definition vsnprintf_u00cc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (D n VA c1 c2 : Z) (dn : nat) (junkd : list byte) (slot1 slot2 : word) (slots : list word)
(lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_u00cc -> a3 = Z_to_bv 64 VA ->
rw_cells asegs m D [CB dn junkd] -> ISH m ->
va_area m VA (slot1 :: slot2 :: slots) ->
-2^31 <= c1 < 2^31 -> bv_unsigned slot1 mod 2^32 = c1 mod 2^32 ->
-2^31 <= c2 < 2^31 -> bv_unsigned slot2 mod 2^32 = c2 mod 2^32 ->
(7 <= dn)%nat -> (7 <= n < 2^63) ->
stk asegs m lo q -> (lo <= q - VSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(q <= VA) -> (VA + 8 * zlength (slot1 :: slot2 :: slots) <= 2^47) ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength (slot1 :: slot2 :: slots) <= D) ->
dapp D (Z.of_nat dn) -> rng_ok m D 6 ->
evt asegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd 6 [92; 117; 48; 48; c1 mod 256; c2 mod 256] lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 vsnprintf_entry) fc None m (seg_rom asegs)).

End Jsonc.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ QFd5 Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Qc27 Q13u QDM6 QJFf.Mq0 QwAs.Mq1 Qc6I QJFf QVsB.

Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import Qu3b.Mq3.
Import QTVW.Mq1 Qu3b.Mq1 QYyZ.Mq2 QFd5.Mq0 QnRU.Mq3 QnRU.Mq4 QteI.Mq1.
Import QCNF.Mq0 QQNJ.Mq3.
Import QMPy.
Import QIG5. Import QC9y.
Import Qr5k.Mq0 QbPx_c1.Mq0 QCqp.Mq0 Qr5k.Mq1 Qi1S.Mq1 QHRw.Mq0 Qvzz.Mq0.
Import Q0z1.
Import QlES.
Import Q8Kb.Mq4.
Import QXE1.Mq0.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_4 := lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation wz := (Z_to_bv 64).

Lemma rt_vsn {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0e7c88 [C8 (wz 0x0d9004)].
Proof. intros m RC; unfold rt_consts_at in RC; decompose [and] RC; assumption. Qed.

Lemma ssp_cells_munch : forall m m' W canary, ssp_cells m canary -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (snd iv <= got_ssp \/ got_ssp + 8 <= fst iv) /\ (snd iv <= ssp_guard \/ ssp_guard + 8 <= fst iv)) W -> ssp_cells m' canary.
Proof.
intros m m' W canary [G1 G2] MU WM HW. split.
- eapply rw_cells_apart; [exact G1| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [H _]. cbn in *. lia.
- eapply rw_cells_apart; [exact G2| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [_ H]. cbn in *. lia.
Qed.

Definition snprintf_stub : Z := 0x4f99c.
Definition snprintf_icpt_entry : Z := 0x54338.
Definition vsnprintf_icpt_entry : Z := 0x53f48.

Definition SNP_DEPTH : Z := 96 + 2160 + VSN_DEPTH.

Section S.
Context {BAND : Band}.
Variables (AFMT : Z) (fmt : list Z).
Hypothesis PCOMMON : pcommon_stmt AFMT.
Hypothesis REALV : vsnprintf_stmt AFMT fmt.

Definition snprintf_icpt_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(D n : Z) (dn : nat) (junkd : list byte) (args : list parg)
(lo : Z) (canary : word) (r : Z) (o : list Z),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 AFMT ->
rw_cells asegs m D [CB dn junkd] ->
ISH m ->
bytes_at asegs m AFMT (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
sargs_ok [a3; a4; a5; a6; a7] args ->
printf_model OUT_sn OUTFP_sn fmt args [] = Qc6I.Ret (Ok (r, o)) ->
fp_calls (length fmt) fmt args = [] ->
(length o < dn)%nat -> (zlength o < n < 2^63) ->
(0 <= r < 2^31 - 1) -> (Z.min n (r + 1) <= 64) -> rng_ok m D (Z.min n (r + 1)) ->
stk asegs m lo q -> (lo <= q - SNP_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(65536 <= AFMT) -> (AFMT + zlength fmt <= STATIC_SPLIT) -> szone AFMT (zlength fmt) ->
(D + Z.of_nat dn <= lo \/ q <= D) ->
dapp D (Z.of_nat dn) -> (0 < zlength o -> rng_ok m D (zlength o)) ->
evt asegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 snprintf_stub) fc None m (seg_rom asegs)).

Theorem snprintf_icpt_proof : snprintf_icpt_stmt.
Proof.
unfold snprintf_icpt_stmt. intros until o. cbv zeta.
intros -> -> -> DST ISH0 BY HF P1 SAOK MODEL FPC ROOM Hn Hr H64 RNG ST LO GLO QHI SSP MI FRM HA0 HA SZ DD DAPP RNGO.
unfold SNP_DEPTH, VSN_DEPTH, VF_DEPTH, GLOBALS_TOP in *.
assert (CEIL : band_lo <= lo) by (idtac; exact GLO).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m) as MU.
pose proof ISH0 as (ASH & RC & SB).
change (boxed (bytes_at asegs m AFMT (zb fmt))) in BY.
unfold snprintf_stub.

step. carve_frame 96%nat ST. rename FR into FRw.
do 15 istep.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof (rt_161720 _ RCc) as K18. pose proof (rt_157bb0 _ RCc) as K7. pose proof (rt_1f25bc _ RCc) as K22. pose proof (rt_vsn _ RCc) as KV.
step. call_u tryinit_spec7; [exact K18| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. if_lit. istep. istep. istep. istep. step.

istep. carve_frame 2032%nat ST. rename FR into FRi.
do 10 istep.
istep. carve_frame 128%nat ST. rename FR into FRj.
do 5 istep.
step. call_u tryinit_spec7; [exact K18| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. if_lit.
istep. istep. istep. istep. istep.
step. if_lit.
istep. istep. istep. istep. step.
pose proof PCOMMON as PCD. unfold pcommon_stmt, PCOMMON_STACK, pcommon_entry in PCD.
call_u PCD;
[ eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls]
| assumption | unsigned_lits; exact ST | exact CEIL | unsigned_lits; lia |].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.

istep. istep. istep. istep. istep. istep.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
assert (ISHA : ISH mA) by (eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls]).
assert (SSPA : ssp_cells mA canary) by (eapply ssp_cells_munch; [exact SSP| exact MUs| exact WM| unfold got_ssp, ssp_guard; apply Forall_cons; [cbn; lia| apply Forall_nil]]).
assert (BYA : bytes_at asegs mA AFMT (zb fmt)).
{ unfold boxed in BY. eapply bytes_at_transport; [exact BY| exact MUs|]. pose proof (zb_length fmt) as LZ. unfold STATIC_SPLIT, zlength in *. cbn [disjoint_from]. rewrite LZ. split; [lia| exact I]. }
assert (RNGOA : 0 < zlength o -> rng_ok mA D (zlength o)).
{ intros K0. eapply rng_ok_munch; [exact (RNGO K0) | exact MUs | exact WM |].
pose proof (proj1 (proj2 (RNGO K0))) as D47. unfold zlength in *.
repeat (apply Forall_cons; [cbn [fst snd]; rewrite !SH_eq; Z.div_mod_to_equations; lia|]). apply Forall_nil. }
assert (RNGA : rng_ok mA D (Z.min n (r + 1))).
{ eapply rng_ok_munch; [exact RNG | exact MUs | exact WM |].
pose proof (proj1 (proj2 RNG)) as D47.
repeat (apply Forall_cons; [cbn [fst snd]; rewrite !SH_eq; Z.div_mod_to_equations; lia|]). apply Forall_nil. }

pose proof FRw as VAC. apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_] _)) in VAC. destruct VAC as [_ VAC]. cbn [cells_size csize Nat.add app] in VAC.
replace (bv_unsigned sp + -96 + Z.of_nat 56) with (bv_unsigned sp + -40) in VAC by lia.
pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA. clear VAC.
change (le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a3; a4; a5; a6; a7]) in VAA.
clear MUs SSP K18 K7 K22 KV RCc PCD.
eapply evt_cut.
{ eapply REALV with (D := D) (n := n) (VA := bv_unsigned sp + -40) (dn := dn) (junkd := junkd) (slots := [a3; a4; a5; a6; a7]) (args := args)
(lo := lo) (canary := canary) (r := r) (o := o);
rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, VF_DEPTH, GLOBALS_TOP, zlength in *; cbn [length].
all: try reflexivity. all: try lia.
all: first [ exact DST | exact ISHA | exact BYA | exact HF | exact P1 | exact VAA | exact SAOK | exact MODEL | exact FPC
| exact ST | exact SSPA | exact FRM | exact SZ | exact DAPP | exact RNGOA | assumption
| destruct DD as [DD | DD]; [left | right]; lia ]. }
cbv beta. intros ms' P.
unfold vsnprintf_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SSP3 & DST3).
assert (RNG3 : rng_ok m3 D (Z.min n (r + 1))).
{ eapply rng_ok_munch; [exact RNGA | exact MUc | exact WMc |].
pose proof (proj1 (proj2 RNGA)) as D47. unfold dapp in DAPP.
repeat (apply Forall_cons; [cbn [fst snd]; rewrite !SH_eq; Z.div_mod_to_equations; lia|]). apply Forall_nil. }
assert (ISH3 : ISH m3).
{ eapply ISH_munch_app; [exact ISHA | exact MUc | exact WMc |]. unfold dapp in DAPP.
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
transport_after_call asegs mA m3 MUc WMc. clear MUc WMc.
fixret.
set (w := Z.min n (r + 1)) in *.
assert (W1 : 1 <= w <= 64) by (unfold w; unfold zlength in Hn; lia).
step. unfold_cond. rewrite (signed_small r) by lia. if_false.
destruct ISH3 as (_ & _ & SB3).
eapply (vsn_icpt_tail (bv_unsigned sp) gp tp _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ s7 s6 s5 s4 s3 (wz D) (wz n) (wz AFMT) (wz 344976) _ _
Ft fc' m3 D n r AFMT _ _ _ RNG3 W1 Hr ltac:(unfold zlength in Hn; lia) SB3 FRi).
intros u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6.
fixret.
release_frame FRj ST3 (bv_unsigned sp + -2128). release_frame FRi ST3 (bv_unsigned sp + -96).

do 5 istep. step. release_frame FRw ST3 (bv_unsigned sp).
apply evt_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [assumption|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|]. split; [exact SSP3| exact DST3].
Qed.
End S.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QFy3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mqc.
Import Qc27 Q13u QDM6 QJFf.Mq0 QwAs.Mq1 Qc6I QJFf QVsB.

Import QCiC.Mq1 Qpj5.Mq1. Import QCNF QoNr.Mq0. Import QdZp.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import Qu3b.Mq6.
Import QTVW.Mq8 Qu3b.Mq5 QYyZ.Mq9 QFd5 QnRU.Mqf QnRU QteI.Mqb.
Import QCNF.Mq2 QQNJ.Mq9.
Import QMPy.Mq0.
Import QFy3. Import QC9y.Mq0.
Import Qr5k.Mq3 QbPx_c1 QCqp Qr5k Qi1S.Mq3 QHRw Qvzz.
Import Q0z1.
Import QlES.
Import Q8Kb.Mq8.
Import QXE1.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_4 := lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation wz := (Z_to_bv 64).

Lemma rt_vsn {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0ea0a8 [C8 (wz 0x0db6c8)].
Proof. intros m RC; unfold rt_consts_at in RC; decompose [and] RC; assumption. Qed.

Lemma ssp_cells_munch : forall m m' W canary, ssp_cells m canary -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (snd iv <= got_ssp \/ got_ssp + 8 <= fst iv) /\ (snd iv <= ssp_guard \/ ssp_guard + 8 <= fst iv)) W -> ssp_cells m' canary.
Proof.
intros m m' W canary [G1 G2] MU WM HW. split.
- eapply rw_cells_apart; [exact G1| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [H _]. cbn in *. lia.
- eapply rw_cells_apart; [exact G2| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [_ H]. cbn in *. lia.
Qed.

Definition snprintf_stub : Z := 0x4fd74.
Definition snprintf_icpt_entry : Z := 0x54710.
Definition vsnprintf_icpt_entry : Z := 0x54320.

Definition SNP_DEPTH : Z := 96 + 2160 + VSN_DEPTH.

Section S.
Context {BAND : Band}.
Variables (AFMT : Z) (fmt : list Z).
Hypothesis PCOMMON : pcommon_stmt AFMT.
Hypothesis REALV : vsnprintf_stmt AFMT fmt.

Definition snprintf_icpt_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(D n : Z) (dn : nat) (junkd : list byte) (args : list parg)
(lo : Z) (canary : word) (r : Z) (o : list Z),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 AFMT ->
rw_cells asegs m D [CB dn junkd] ->
ISH m ->
bytes_at asegs m AFMT (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
sargs_ok [a3; a4; a5; a6; a7] args ->
printf_model OUT_sn OUTFP_sn fmt args [] = Qc6I.Ret (Ok (r, o)) ->
fp_calls (length fmt) fmt args = [] ->
(length o < dn)%nat -> (zlength o < n < 2^63) ->
(0 <= r < 2^31 - 1) -> (Z.min n (r + 1) <= 64) -> rng_ok m D (Z.min n (r + 1)) ->
stk asegs m lo q -> (lo <= q - SNP_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(65536 <= AFMT) -> (AFMT + zlength fmt <= STATIC_SPLIT) -> szone AFMT (zlength fmt) ->
(D + Z.of_nat dn <= lo \/ q <= D) ->
dapp D (Z.of_nat dn) -> (0 < zlength o -> rng_ok m D (zlength o)) ->
evt asegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 snprintf_stub) fc None m (seg_rom asegs)).

Theorem snprintf_icpt_proof : snprintf_icpt_stmt.
Proof.
unfold snprintf_icpt_stmt. intros until o. cbv zeta.
intros -> -> -> DST ISH0 BY HF P1 SAOK MODEL FPC ROOM Hn Hr H64 RNG ST LO GLO QHI SSP MI FRM HA0 HA SZ DD DAPP RNGO.
unfold SNP_DEPTH, VSN_DEPTH, VF_DEPTH, GLOBALS_TOP in *.
assert (CEIL : band_lo <= lo) by (idtac; exact GLO).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m) as MU.
pose proof ISH0 as (ASH & RC & SB).
change (boxed (bytes_at asegs m AFMT (zb fmt))) in BY.
unfold snprintf_stub.

step. carve_frame 96%nat ST. rename FR into FRw.
do 15 istep.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof (rt_161720 _ RCc) as K18. pose proof (rt_157bb0 _ RCc) as K7. pose proof (rt_1f25bc _ RCc) as K22. pose proof (rt_vsn _ RCc) as KV.
step. call_u tryinit_spec7; [exact K18| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. if_lit. istep. istep. istep. istep. step.

istep. carve_frame 2032%nat ST. rename FR into FRi.
do 10 istep.
istep. carve_frame 128%nat ST. rename FR into FRj.
do 5 istep.
step. call_u tryinit_spec7; [exact K18| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. if_lit.
istep. istep. istep. istep. istep.
step. if_lit.
istep. istep. istep. istep. step.
pose proof PCOMMON as PCD. unfold pcommon_stmt, PCOMMON_STACK, pcommon_entry in PCD.
call_u PCD;
[ eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls]
| assumption | unsigned_lits; exact ST | exact CEIL | unsigned_lits; lia |].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.

istep. istep. istep. istep. istep. istep.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
assert (ISHA : ISH mA) by (eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls]).
assert (SSPA : ssp_cells mA canary) by (eapply ssp_cells_munch; [exact SSP| exact MUs| exact WM| unfold got_ssp, ssp_guard; apply Forall_cons; [cbn; lia| apply Forall_nil]]).
assert (BYA : bytes_at asegs mA AFMT (zb fmt)).
{ unfold boxed in BY. eapply bytes_at_transport; [exact BY| exact MUs|]. pose proof (zb_length fmt) as LZ. unfold STATIC_SPLIT, zlength in *. cbn [disjoint_from]. rewrite LZ. split; [lia| exact I]. }
assert (RNGOA : 0 < zlength o -> rng_ok mA D (zlength o)).
{ intros K0. eapply rng_ok_munch; [exact (RNGO K0) | exact MUs | exact WM |].
pose proof (proj1 (proj2 (RNGO K0))) as D47. unfold zlength in *.
repeat (apply Forall_cons; [cbn [fst snd]; rewrite !SH_eq; Z.div_mod_to_equations; lia|]). apply Forall_nil. }
assert (RNGA : rng_ok mA D (Z.min n (r + 1))).
{ eapply rng_ok_munch; [exact RNG | exact MUs | exact WM |].
pose proof (proj1 (proj2 RNG)) as D47.
repeat (apply Forall_cons; [cbn [fst snd]; rewrite !SH_eq; Z.div_mod_to_equations; lia|]). apply Forall_nil. }

pose proof FRw as VAC. apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_] _)) in VAC. destruct VAC as [_ VAC]. cbn [cells_size csize Nat.add app] in VAC.
replace (bv_unsigned sp + -96 + Z.of_nat 56) with (bv_unsigned sp + -40) in VAC by lia.
pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA. clear VAC.
change (le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a3; a4; a5; a6; a7]) in VAA.
clear MUs SSP K18 K7 K22 KV RCc PCD.
eapply evt_cut.
{ eapply REALV with (D := D) (n := n) (VA := bv_unsigned sp + -40) (dn := dn) (junkd := junkd) (slots := [a3; a4; a5; a6; a7]) (args := args)
(lo := lo) (canary := canary) (r := r) (o := o);
rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, VF_DEPTH, GLOBALS_TOP, zlength in *; cbn [length].
all: try reflexivity. all: try lia.
all: first [ exact DST | exact ISHA | exact BYA | exact HF | exact P1 | exact VAA | exact SAOK | exact MODEL | exact FPC
| exact ST | exact SSPA | exact FRM | exact SZ | exact DAPP | exact RNGOA | assumption
| destruct DD as [DD | DD]; [left | right]; lia ]. }
cbv beta. intros ms' P.
unfold vsnprintf_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SSP3 & DST3).
assert (RNG3 : rng_ok m3 D (Z.min n (r + 1))).
{ eapply rng_ok_munch; [exact RNGA | exact MUc | exact WMc |].
pose proof (proj1 (proj2 RNGA)) as D47. unfold dapp in DAPP.
repeat (apply Forall_cons; [cbn [fst snd]; rewrite !SH_eq; Z.div_mod_to_equations; lia|]). apply Forall_nil. }
assert (ISH3 : ISH m3).
{ eapply ISH_munch_app; [exact ISHA | exact MUc | exact WMc |]. unfold dapp in DAPP.
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
transport_after_call asegs mA m3 MUc WMc. clear MUc WMc.
fixret.
set (w := Z.min n (r + 1)) in *.
assert (W1 : 1 <= w <= 64) by (unfold w; unfold zlength in Hn; lia).
step. unfold_cond. rewrite (signed_small r) by lia. if_false.
destruct ISH3 as (_ & _ & SB3).
eapply (vsn_icpt_tail (bv_unsigned sp) gp tp _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ s7 s6 s5 s4 s3 (wz D) (wz n) (wz AFMT) (wz 345960) _ _
Ft fc' m3 D n r AFMT _ _ _ RNG3 W1 Hr ltac:(unfold zlength in Hn; lia) SB3 FRi).
intros u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6.
fixret.
release_frame FRj ST3 (bv_unsigned sp + -2128). release_frame FRi ST3 (bv_unsigned sp + -96).

do 5 istep. step. release_frame FRw ST3 (bv_unsigned sp).
apply evt_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [assumption|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|]. split; [exact SSP3| exact DST3].
Qed.
End S.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoNr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoNr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMPy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMPy.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFy3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFy3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC9y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC9y.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qr5k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qr5k.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbPx_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbPx_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCqp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCqp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi1S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qi1S.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCqp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCqp.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHRw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHRw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvzz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvzz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8Kb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8Kb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXE1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXE1.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition FMT_ld : list Z := [37; 108; 100; 0].
Definition FMT_lu : list Z := [37; 108; 117; 0].
Definition FMT_u00cc : list Z := [92; 117; 48; 48; 37; 99; 37; 99; 0].
Definition A_FMT_ld : Z := 0x23760.
Definition A_FMT_lu : Z := 0x23780.
Definition A_FMT_u00cc : Z := 0x23700.

Lemma fmt_ld_bytes : forall m, mem_inv asegs m -> bytes_at asegs m A_FMT_ld (zb FMT_ld).
Proof. intros m MI. apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_ld; lia | unfold A_FMT_ld, zlength; cbn; lia]. Qed.
Lemma fmt_lu_bytes : forall m, mem_inv asegs m -> bytes_at asegs m A_FMT_lu (zb FMT_lu).
Proof. intros m MI. apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_lu; lia | unfold A_FMT_lu, zlength; cbn; lia]. Qed.
Lemma fmt_u00cc_bytes : forall m, mem_inv asegs m -> bytes_at asegs m A_FMT_u00cc (zb FMT_u00cc).
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
printf_model OUT_sn OUTFP_sn FMT_ld [PA_li i] [] = Qc6I.Ret (Ok (zlength (dec_text i), dec_text i)).
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
printf_model OUT_sn OUTFP_sn FMT_lu [PA_lu u] [] = Qc6I.Ret (Ok (zlength (dec_text u), dec_text u)).
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
printf_model OUT_sn OUTFP_sn FMT_u00cc [PA_i c1; PA_i c2] [] = Qc6I.Ret (Ok (6, [92; 117; 48; 48; c1 mod 256; c2 mod 256])).
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

Lemma szone_fmt {BAND : Band} : forall A n, gzone A n -> szone A n.
Proof. intros A n G. unfold szone. right. right. right. exact G. Qed.

Section Jsonc.
Context {BAND : Band}.

Hypothesis PC_LD : pcommon_stmt A_FMT_ld.
Hypothesis PC_LU : pcommon_stmt A_FMT_lu.
Hypothesis PC_U00CC : pcommon_stmt A_FMT_u00cc.

Definition vsnprintf_ld_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (D n VA i : Z) (dn : nat) (junkd : list byte) (slot : word) (slots : list word)
(lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_ld -> a3 = Z_to_bv 64 VA ->
rw_cells asegs m D [CB dn junkd] -> ISH m ->
va_area m VA (slot :: slots) -> -2^63 <= i < 2^63 -> bv_unsigned slot = i mod 2^64 ->
(21 <= dn)%nat -> (21 <= n < 2^63) ->
stk asegs m lo q -> (lo <= q - VSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(q <= VA) -> (VA + 8 * zlength (slot :: slots) <= 2^47) ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength (slot :: slots) <= D) ->
dapp D (Z.of_nat dn) -> (forall k, 0 < k <= 20 -> rng_ok m D k) ->
evt asegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd (zlength (dec_text i)) (dec_text i) lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 vsnprintf_entry) fc None m (seg_rom asegs)).

Definition vsnprintf_lu_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (D n VA : Z) (dn : nat) (junkd : list byte) (slot : word) (slots : list word)
(lo : Z) (canary : word),
let q := bv_unsigned sp in let u := bv_unsigned slot in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_lu -> a3 = Z_to_bv 64 VA ->
rw_cells asegs m D [CB dn junkd] -> ISH m ->
va_area m VA (slot :: slots) ->
(21 <= dn)%nat -> (21 <= n < 2^63) ->
stk asegs m lo q -> (lo <= q - VSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(q <= VA) -> (VA + 8 * zlength (slot :: slots) <= 2^47) ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength (slot :: slots) <= D) ->
dapp D (Z.of_nat dn) -> (forall k, 0 < k <= 20 -> rng_ok m D k) ->
evt asegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd (zlength (dec_text u)) (dec_text u) lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 vsnprintf_entry) fc None m (seg_rom asegs)).

Definition vsnprintf_u00cc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (D n VA c1 c2 : Z) (dn : nat) (junkd : list byte) (slot1 slot2 : word) (slots : list word)
(lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_u00cc -> a3 = Z_to_bv 64 VA ->
rw_cells asegs m D [CB dn junkd] -> ISH m ->
va_area m VA (slot1 :: slot2 :: slots) ->
-2^31 <= c1 < 2^31 -> bv_unsigned slot1 mod 2^32 = c1 mod 2^32 ->
-2^31 <= c2 < 2^31 -> bv_unsigned slot2 mod 2^32 = c2 mod 2^32 ->
(7 <= dn)%nat -> (7 <= n < 2^63) ->
stk asegs m lo q -> (lo <= q - VSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(q <= VA) -> (VA + 8 * zlength (slot1 :: slot2 :: slots) <= 2^47) ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength (slot1 :: slot2 :: slots) <= D) ->
dapp D (Z.of_nat dn) -> rng_ok m D 6 ->
evt asegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd 6 [92; 117; 48; 48; c1 mod 256; c2 mod 256] lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 vsnprintf_entry) fc None m (seg_rom asegs)).

End Jsonc.
