(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig QwAs Q0Do Qc6I QJFf QVsB QCiC Qpj5 QoNr QdZp Qk8e Q6sh QKTr QTVW Qs9x QcfN QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 Q9Ho Qu3b QnRU QteI QoBx QQNJ QpzM QnaW QQ8H QEp5 Q6b1 QK8Y QJp5 Q0z1 QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1. Import QoNr. Import QdZp Qk8e.Mq0 Q6sh QKTr.
Import QTVW.Mq5 Qs9x QcfN. Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QTVW.Mq1 Qu3b.Mq1 QnRU.Mq3 QnRU.Mq4 QteI.Mq1 QoBx Qu3b.Mq0 QQNJ.Mq1 QpzM.Mqc QnaW.Mq0 QQ8H.Mq0 QpzM.Mq9 QQNJ.Mq3 QEp5 Q6b1 QK8Y QJp5.
Import Q0z1.
Import QlES.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition fprintf_stub : Z := 0x4f998.
Definition fprintf_icpt_entry : Z := 0x54260.

Lemma ssp_cells_munch' : forall m m' W canary, ssp_cells m canary -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (snd iv <= got_ssp \/ got_ssp + 8 <= fst iv) /\ (snd iv <= ssp_guard \/ ssp_guard + 8 <= fst iv)) W -> ssp_cells m' canary.
Proof.
intros m m' W canary [G1 G2] MU WM HW. split.
- eapply rw_cells_apart; [exact G1| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [H _]. cbn in *. lia.
- eapply rw_cells_apart; [exact G2| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [_ H]. cbn in *. lia.
Qed.

Lemma forall_range_b : forall l, forallb (fun c => (0 <=? c) && (c <? 256))%bool l = true -> Forall (fun c => 0 <= c < 256) l.
Proof.
intros l H. rewrite forallb_forall in H. apply Forall_forall. intros c Hc. specialize (H c Hc).
apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma vf_to_diag_post : forall St ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (st st' : St) ms,
vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st' ms -> st' = st ->
fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt st' ms.
Proof.
intros until ms. intros (x5 & x6 & x7 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & E & MU & WM & MI & FRM & FOK & ST & SF & SSP) Est.
exists x5, x6, x7, a0, a1, a2, a3, a4, a5, a6, a7, x28, x29, x30, x31, Ft, fc', m'.
repeat (split; [assumption|]). exact Est.
Qed.

Section FprintfIcpt.
Context {BAND : Band}.
Context {St : Type}.
Hypothesis FWE : fwritex_stderr_stmt.
Hypothesis FLS : stdio_write_flush_stmt.

Definition pc_hyp (A : Z) (m : mem) (lo usp : Z) (a2 a3 a4 a5 a6 a7 : word) : Prop :=
forall (ra' gp' tp' t0 t1 t2 s0 s1 a0 a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m' : mem),
ISH m' -> mem_inv asegs m' -> stk asegs m' lo (usp + -112) ->
rw_cells asegs m' (usp + -48) [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
munch [(lo, usp)] m m' -> wmono asegs m m' ->
evt asegs (rpost ra' (wz (usp + -112)) gp' tp' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(bv_unsigned (wz (usp + -112)) - PCOMMON_STACK, bv_unsigned (wz (usp + -112)))] lo m' (fun _ _ => True))
(MS (mkR ra' (wz (usp + -112)) gp' tp' t0 t1 t2 s0 s1 a0 (wz A) (wz (usp + -48)) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m' (seg_rom asegs)).

Lemma fprintf_icpt_gen :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z) (lo : Z) (canary : word),
let q := bv_unsigned sp in
pc_hyp A m lo q a2 a3 a4 a5 a6 a7 ->
a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A ->
stderr_wfile m -> ISH m ->
bytes_at asegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
args_ok RSTDERR (q - 112 - 352) 80 m lo q (q - 112 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
stk asegs m lo q -> (lo <= q - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
Qpj5.Mq1.implM asegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
(fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz fprintf_stub) fc None m (seg_rom asegs)).
Proof using FLS FWE BAND.
intros until canary. cbv zeta.
intros PC -> -> SF ISH0 BY HF P1 AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA.
unfold FPRINTF_DEPTH, VF_FRAME, GLOBALS_TOP, STATIC_SPLIT in *. unfold pc_hyp, PCOMMON_STACK, pcommon_entry in PC.
assert (CEIL : band_lo <= lo) by (idtac; exact GLO).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs.
pose proof ISH0 as (ASH & RC & SB).
destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
set (BAh := bytes_at) in BY.
match goal with |- Qpj5.Mq1.implM _ _ _ ?Q _ => set (QQ := Q) end.
eapply (implM_evt asegs). 2:{ intros ms' H; exact H. } cbv beta.
unfold fprintf_stub. step.
carve_frame 112%nat ST.
do 15 istep.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof (rt_161720 _ RCc) as K18. pose proof (rt_157bb0 _ RCc) as K7. pose proof (rt_1f25bc _ RCc) as K22. pose proof (rt_159c68 _ RCc) as K17.
step. call_u tryinit_spec7; [exact K18| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. if_lit. istep. istep.
step. call_u tryinit_spec7; [exact K18| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. if_lit. istep. istep. istep. istep. istep. step. if_lit. istep. istep. istep. istep. step.

apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
replace (bv_unsigned sp + -112 + Z.of_nat 64) with (bv_unsigned sp + -48) in VAC by lia.
call_u PC; [ eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls] | assumption | exact ST | exact VAC | exact MUs | exact WM |].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
clear K18 K7 K22 RCc.

istep. istep. istep. step. istep. istep. step. step. clear K17.
apply evt_done.
lazymatch goal with |- Qpj5.Mq1.implM _ _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
assert (SSPA : ssp_cells mA canary) by (eapply ssp_cells_munch'; [exact SSP| exact MUs| exact WM| unfold got_ssp, ssp_guard; apply Forall_cons; [cbn; lia| apply Forall_nil]]).
assert (ISHA : ISH mA) by (eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls]).
assert (BYA : bytes_at asegs mA A (zb fmt)) by (subst BAh; eapply bytes_at_transport; [exact BY| exact MUs| cbn [disjoint_from]; rewrite LZB; lia]).
pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA.
clear SSP BY.
pose proof (vfprintf_stderr_proof (St:=St) FWE FLS) as VF. unfold vfprintf_stderr_stmt in VF. cbv zeta in VF.
eapply (implM_post_evt asegs).
{ eapply VF with (A := A) (VA := bv_unsigned sp + -48) (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := args) (lo := lo) (canary := canary);
clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
all: try reflexivity. all: try lia.
- exists flags, mode, e, wend, tail. split; [unfold file_cells; assumption | exact FL40].
- exact ISHA.
- exact BYA.
- exact HF.
- exact P1.
- exact VAA.
- clear MUs. eapply args_ok_vf; [| | exact MU]; [|lia].
replace (bv_unsigned sp + -112 - 352) with (bv_unsigned sp - 112 - 352) by lia.
replace (bv_unsigned sp + -112 - 368) with (bv_unsigned sp - 112 - 368) by lia. exact AOK.
- exact PP.
- exact FPC.
- exact ST.
- exact SSPA.
- assumption.
- exact FRM. }
cbv beta. intros [] [b4 st4] ms' P. clear VF MUs. cbn [snd] in P.
unfold vfprintf_stderr_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
transport_after_call asegs mA m3 MUc WMc. clear MUc WMc.
fixret.

do 5 istep. step.
lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -112) ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -48) ?rest |- _ =>
assert (FALL : rw_cells asegs mm (bv_unsigned sp + -112) (hd ++ rest));
[ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
| clear FR VAC ] end.
cbn [app] in FALL.
release_frame FALL ST3 (bv_unsigned sp).
apply evt_done. subst QQ. cbn [fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [assumption|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|]. split; [exact SF3|]. exact SSP3.
Qed.

Local Ltac pc_hyp_s LEM :=
intros until slack; intros BY HF SZ SLEN SEP CEIL LO UR; unfold pc_hyp; intros until m'; intros ISH' MI' ST' VA' MU' WM';
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in VA'; destruct VA' as [APC _];
lazymatch type of APC with rw_cells _ _ _ [C8 ?w] => rewrite <- (Z_to_bv_bv_unsigned w) in APC end;
eapply LEM;
[ exact ISH'| exact MI'| rewrite unsigned_lit by lia; exact ST'| exact CEIL| rewrite unsigned_lit by lia; unfold PCOMMON_STACK; lia| exact APC| rewrite unsigned_lit by lia; lia
| eapply bytes_at_transport; [exact BY| exact MU'| cbn [disjoint_from]; rewrite length_app, zb_length; cbn [length]; unfold zlength in SEP; lia]
| exact HF| exact SZ| exact SLEN| rewrite unsigned_lit by lia; lia ].
Lemma pc_hyp_usage : forall m lo usp (a2 a3 a4 a5 a6 a7 : word) (s : list Z) (slack : list byte),
bytes_at asegs m (bv_unsigned a2) (zb s ++ b8 0 :: slack) -> Forall (fun c => 0 < c < 256) s ->
szone (bv_unsigned a2) (zlength s + 1) -> zlength s + 1 <= 2^40 ->
(bv_unsigned a2 + zlength s + 1 + zlength slack <= lo \/ usp <= bv_unsigned a2) ->
band_lo <= lo -> lo <= usp - 112 - PCOMMON_STACK -> usp < 2^64 ->
pc_hyp AFMT_usage m lo usp a2 a3 a4 a5 a6 a7.
Proof.  unfold AFMT_usage, PCOMMON_STACK. pc_hyp_s printf_common_usage. Qed.
Lemma pc_hyp_cannot_open : forall m lo usp (a2 a3 a4 a5 a6 a7 : word) (s : list Z) (slack : list byte),
bytes_at asegs m (bv_unsigned a2) (zb s ++ b8 0 :: slack) -> Forall (fun c => 0 < c < 256) s ->
szone (bv_unsigned a2) (zlength s + 1) -> zlength s + 1 <= 2^40 ->
(bv_unsigned a2 + zlength s + 1 + zlength slack <= lo \/ usp <= bv_unsigned a2) ->
band_lo <= lo -> lo <= usp - 112 - PCOMMON_STACK -> usp < 2^64 ->
pc_hyp AFMT_cannot_open m lo usp a2 a3 a4 a5 a6 a7.
Proof.  unfold AFMT_cannot_open, PCOMMON_STACK. pc_hyp_s printf_common_cannot_open. Qed.
Lemma pc_hyp_read_error : forall m lo usp (a2 a3 a4 a5 a6 a7 : word) (s : list Z) (slack : list byte),
bytes_at asegs m (bv_unsigned a2) (zb s ++ b8 0 :: slack) -> Forall (fun c => 0 < c < 256) s ->
szone (bv_unsigned a2) (zlength s + 1) -> zlength s + 1 <= 2^40 ->
(bv_unsigned a2 + zlength s + 1 + zlength slack <= lo \/ usp <= bv_unsigned a2) ->
band_lo <= lo -> lo <= usp - 112 - PCOMMON_STACK -> usp < 2^64 ->
pc_hyp AFMT_read_error m lo usp a2 a3 a4 a5 a6 a7.
Proof.  unfold AFMT_read_error, PCOMMON_STACK. pc_hyp_s printf_common_read_error. Qed.
Lemma pc_hyp_too_big : forall m lo usp (a2 a3 a4 a5 a6 a7 : word),
band_lo <= lo -> lo <= usp - 112 - PCOMMON_STACK -> usp < 2^64 ->
pc_hyp AFMT_too_big m lo usp a2 a3 a4 a5 a6 a7.
Proof.
unfold AFMT_too_big, PCOMMON_STACK. intros until a7; intros CEIL LO UR.
unfold pc_hyp; intros until m'; intros ISH' MI' ST' VA' MU' WM'.
eapply printf_common_too_big; [exact ISH'| exact MI'| rewrite unsigned_lit by lia; exact ST'| exact CEIL| rewrite unsigned_lit by lia; unfold PCOMMON_STACK; lia].
Qed.

Local Ltac fg_sides0 PCH PIECES ARGS :=
lazymatch goal with
| |- pc_hyp _ _ _ _ _ _ _ _ _ _ => PCH
| |- stderr_wfile _ => assumption
| |- ISH _ => assumption
| |- bytes_at _ _ _ _ => apply fmt_bytes_at; [assumption | vm_compute; reflexivity | unfold AFMT_usage, AFMT_cannot_open, AFMT_read_error, AFMT_too_big; lia | vm_compute; discriminate]
| |- Forall _ _ => apply forall_range_b; vm_compute; reflexivity
| |- pass1_ok _ = true => vm_compute; reflexivity
| |- args_ok _ _ _ _ _ _ _ _ _ => ARGS
| |- printf_pieces _ _ = _ => PIECES
| |- fp_calls _ _ _ = [] => vm_compute; reflexivity
| |- stk _ _ _ _ => assumption
| |- ssp_cells _ _ => assumption
| |- mem_inv _ _ => assumption
| |- frm0 _ => assumption
| |- @eq (bv 64) _ _ => assumption
| |- ?a <= ?b => tryif has_var (a <= b) then lia else (vm_compute; discriminate)
end.
Local Ltac fg_sides PCH PIECES ARGS := lazymatch goal with |- ?G => first [ fg_sides0 PCH PIECES ARGS | idtac "FAILED:" G; fail ] end.

Theorem fprintf_diag_proof' : forall (d : diag_msg)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
stderr_wfile m -> ISH m ->
a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
implM asegs (s_diag (St:=St) d) st
(fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4f998) fc None m (seg_rom asegs)).
Proof using FLS FWE BAND.
intros d. intros until canary. intros SF ISH0 Ha0 DA ST LO GLO QHI SSP MI FRM.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
unfold FPRINTF_DEPTH, GLOBALS_TOP in *.
assert (CEIL : band_lo <= lo) by (idtac; exact GLO).

assert (BR : forall ps, Qpj5.Mq1.implM asegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
(fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x4f998) fc None m (seg_rom asegs)) ->
Forall (fun p => zlength p <= OUT_MAX) ps ->
Qpj5.Mq1.implM asegs (stderr_fprintf ps) st
(fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x4f998) fc None m (seg_rom asegs))).
{ intros ps H SH. unfold stderr_fprintf, Qpj5.Mq1.implM in *.
eapply impl_epost_mono.
- eapply (stderr_bridge asegs ps [] st (fun s' ms' => fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt s' ms') _ SH).
eapply impl_mono; [eapply (impl_tforall asegs (at_node asegs) _ _ _ _ (outsk_flush_leaves ps [] st)); exact H|].
intros [|[[] [b s']]] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I|]. eapply vf_to_diag_post; [exact H1 | exact H2].
- intros [[] s'] ms' H'. exact H'. }
pose proof fprintf_icpt_gen as FG. cbv zeta in FG. unfold VF_FRAME, FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, fprintf_stub in FG.
destruct d as [argv0 | path | path | | | |]; cbn [diag_args] in DA; try contradiction; unfold s_diag;
(apply BR; clear BR;
[| try (destruct DA as (_ & _ & _ & _ & _ & LEN & _)); unfold OUT_MAX in *;
unfold pieces_usage, pieces_cannot_open, pieces_read_error, pieces_too_big;
repeat (apply Forall_cons; [first [unfold zlength in *; lia | vm_compute; discriminate] |]); apply Forall_nil ]).
- destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA & G47). unfold GLOBALS_TOP in GA.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length argv0) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB.
assert (SZ : szone (bv_unsigned a2) (zlength argv0 + 1)) by (unfold szone; idtac; lia).
unfold OUT_MAX in LEN. unfold zlength in *.
eapply FG with (fmt := FMT_usage) (args := [PA_s argv0]) (A := AFMT_usage); clear FG.
all: fg_sides ltac:(eapply pc_hyp_usage; [exact BY| exact HF| exact SZ| unfold zlength; lia| unfold zlength; exact DJ| exact CEIL| unfold PCOMMON_STACK; lia| lia]) ltac:(apply printf_pieces_usage; unfold zlength, INT_MAX, OUT_MAX in *; lia) ltac:(cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; split; [exact BY|]; split; [exact HF|]; split; [exact SLK|]; split; [lia|]; split; [exact SZ|]; lia).
- destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA & G47). unfold GLOBALS_TOP in GA.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length path) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB.
assert (SZ : szone (bv_unsigned a2) (zlength path + 1)) by (unfold szone; idtac; lia).
unfold OUT_MAX in LEN. unfold zlength in *.
eapply FG with (fmt := FMT_cannot_open) (args := [PA_s path]) (A := AFMT_cannot_open); clear FG.
all: fg_sides ltac:(eapply pc_hyp_cannot_open; [exact BY| exact HF| exact SZ| unfold zlength; lia| unfold zlength; exact DJ| exact CEIL| unfold PCOMMON_STACK; lia| lia]) ltac:(apply printf_pieces_cannot_open; unfold zlength, INT_MAX, OUT_MAX in *; lia) ltac:(cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; split; [exact BY|]; split; [exact HF|]; split; [exact SLK|]; split; [lia|]; split; [exact SZ|]; lia).
- destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA & G47). unfold GLOBALS_TOP in GA.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length path) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB.
assert (SZ : szone (bv_unsigned a2) (zlength path + 1)) by (unfold szone; idtac; lia).
unfold OUT_MAX in LEN. unfold zlength in *.
eapply FG with (fmt := FMT_read_error) (args := [PA_s path]) (A := AFMT_read_error); clear FG.
all: fg_sides ltac:(eapply pc_hyp_read_error; [exact BY| exact HF| exact SZ| unfold zlength; lia| unfold zlength; exact DJ| exact CEIL| unfold PCOMMON_STACK; lia| lia]) ltac:(apply printf_pieces_read_error; unfold zlength, INT_MAX, OUT_MAX in *; lia) ltac:(cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; split; [exact BY|]; split; [exact HF|]; split; [exact SLK|]; split; [lia|]; split; [exact SZ|]; lia).
- destruct DA as [Ha1 Hu]. pose proof (bv_unsigned_in_range 64 a2) as R2.
eapply FG with (fmt := FMT_too_big) (args := [PA_u 67108864]) (A := AFMT_too_big); clear FG.
all: fg_sides ltac:(eapply pc_hyp_too_big; [exact CEIL| unfold PCOMMON_STACK; lia| lia]) ltac:(apply printf_pieces_too_big) ltac:(cbn [args_ok arg_ok]; split; [split; [lia | exact Hu] | exact I]).
Qed.
End FprintfIcpt.

Theorem fprintf_diag_proof {BAND : Band} : forall St : Type, @fprintf_diag_stmt _ St.
Proof.
intros St. unfold fprintf_diag_stmt. intros d. intros until canary. intros FWE FLS. intros.
eapply (fprintf_diag_proof' FWE FLS); eassumption.
Qed.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp QDM6 Qsn5 QQwg QvDJ QUxU QOJv QqLk QmP7 QYyZ QkfD QpME QkJ4 QsDw QcYs QmvA QVo2 QRfV QEYd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QTVW.Mq3 QOJv.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk QnRU.Mqa QmP7.Mq0 QpY2.Mq1 QYyZ.Mq0 Qu3b.Mq2 QYyZ.Mq5 QkfD QYyZ.Mq3 QpME.Mq1 QkJ4 QQ8H.Mq2 QsDw.Mq0 QcYs.Mq3 QmvA.Mq1 QpME.Mq6.
Import QVo2.Mq1.
Import QpY2.Mq2.
Import QRfV.Mq0 QnRU.Mq9 QEYd.
Import QcfN.Mq1.
Import QlES.
Import QVo2.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Let atn := at_nodeA L asegs.
Hypothesis large_alloc_spec : large_alloc_stmt RE X L.
Hypothesis poison_zero_spec : poison_zero_stmt_lh RE X L.

Definition calloc_W_sec (bp : Z) : list (Z * Z) :=
(bp - CALLOC_STACK, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W_sec RE X (bp - 2192)).

Definition calloc_post_sec (ra : word) (bp : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (LB : list ablock) (n lo : Z) (m : word -> option byte)
(r : option aptr * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
ms' = MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo bp
/\ RTconst RE X m' /\ RStats RE X m' /\ RDepot RE X m' /\ depot_step m m'
/\ match r with
| (None, a1) => a0 = wz 0 /\ a1 = a /\ munch (calloc_W_sec bp) m m' /\ RSec a LB RE X m'
| (Some p, a1) => exists mb, let msz := sec_map_size n in
p = ASec mb n
/\ as_reg a1 = as_reg a ++ [mkSec mb msz n]
/\ as_tq a1 = as_tq a /\ as_gq a1 = as_gq a /\ (forall c, cls a1 c = cls a c)
/\ as_cache_inited a1 = as_cache_inited a /\ as_next a1 = as_next a
/\ (as_nres a1 = as_nres a \/ as_nres a1 = as_nres a + kPtrArrBlock)
/\ as_spent a1 = as_spent a + sec_cost msz
/\ mb mod kPage = 0 /\ appr mb msz /\ mb + msz <= band_lo /\ zavoids mb msz (avoid_of (ae_L RE) a) = true
/\ a0 = wz (mb + kSecUserOff)
/\ munch (calloc_W_sec bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m m'
/\ RSec a1 LB RE X m'
/\ chunk_mem m' (mb + kPage) (mb + msz) (mb + kSecUserOff) n
/\ rw_cells asegs m' (mb + kSecUserOff) [CB (Z.to_nat n) (repeat (b8 0) (Z.to_nat n))]
end.

Lemma calloc_icpt_sec_spec : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PStateA) (a : AState) (G : ghost) (LB : list ablock) (FS : list fframe) (lo cnt sz dn : Z),
gcons a LB FS G RE X ->
RTconst RE X m -> RStats RE X m -> RSec a LB RE X m -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - CALLOC_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> cnt * sz <= 2^26 -> from_primary (cnt * sz) = false ->
aimplT atn (asan_malloc (ae_L RE) a (cnt * sz)) s
(calloc_post_sec ra bp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB (cnt * sz) lo m)
(MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz cnt) (wz sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x632cc) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros GC RT RS RSE RD MI ST CEIL LO BPR UNW DNH DCAP Hcnt Hsz Hmax HP.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof CEIL as CEIL'. idtac. unfold CALLOC_STACK, ALLOC_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & PC & _ & QK & QC & _). unfold prim_hi in PC. unfold ptrarr_hi in QC. idtac. rewrite ?KHI_eq in PK.
change (al_space_beg (ae_L RE)) with (prim_lo RE) in PC. change (al_ptrarr (ae_L RE)) with (ptrarr_lo RE) in QC.
apply appr_to_lia in QK; [| lia| lia].
set (n := cnt * sz) in *. assert (Hn : 0 <= n <= 2^26) by (subst n; nia).
pose proof (munch_refl (calloc_W_sec bp) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold calloc_W_sec, CALLOC_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE in MU. cbn [tl app] in MU.
assert (SEF : forall mm mm' W, munch W mm mm' -> wmono asegs mm mm' ->
(forall lo' hi' z, In (lo', hi') W -> lo' <= z < hi' -> fp_RStats RE X z \/ fp_RDepot RE X z \/ band_lo <= z) ->
RSec a LB RE X mm -> RSec a LB RE X mm').
{ intros mm mm' W MUw WMw HW RSEw. eapply RSec_frame; [exact RSEw| exact WMw|]. eapply agree_on_of_munch; [exact MUw| exact WMw|]. intros z Fz _. apply outside_intro.
intros lo' hi' Hin Hz. destruct (HW lo' hi' z Hin Hz) as [P|[P|P]].
- exact (fpS_excl _ _ _ _ _ _ GC z P ltac:(right; left; exact Fz)).
- exact (fpD_excl _ _ _ _ _ _ GC z P ltac:(right; left; exact Fz)).
- pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)). lia. }
apply aimplT_from_evt.
eapply calloc_icpt_pre; [exact RT| exact RL| exact (RDepot_unw RE X _ RD)| exact MI| exact ST| exact CEIL'| unfold CALLOC_STACK, ALLOC_STACK; lia| exact BPR| exact UNW| lia| lia|].
intros m1 u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u13 tsz q rest junk8 junk8b MU1 WM1 MI1 ST1 J8 OBJ LQ SZR FR RT1 TU1.
unfold cicpt_W in MU1.
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU1| exact WM1|]. constructor; [first [st_avoid_solve| eapply st_avoid_T; [eassumption| lia| lia]]|]. constructor; [st_avoid_solve| constructor]. }
assert (RSE1 : RSec a LB RE X m1).
{ eapply SEF; [exact MU1| exact WM1| | exact RSE]. intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
- do 2 right. idtac. lia.
- right; left. do 3 right. lia. }
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame_unw; [exact RL| exact RD| exact WM1| | exact TU1]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z [Fz NZ] _. cbn [outside].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). idtac. lia. }
phase_done MU m m1 MU1 WM1. clear RT RS RSE RD MI. try clear ST.
destruct (unw_obj_head _ _ _ _ _ _ OBJ LQ ltac:(lia)) as [OBJh (q30 & TRQ & LQ30)].

unfold asan_calloc_entry. carve_frame 48%nat ST1.
match goal with H : rw_cells asegs _ (bp + -2144 + -48) _ |- _ => replace (bp + -2144 + -48) with (bp + -2192) in H by lia end.
replace (bp + -2144 + -48) with (bp + -2192) in ST1 by lia.
pose proof (munch_refl [(bp - 2192, bp - 2144)] m1) as MUa. pose proof (wmono_refl asegs m1) as WMa.
step. stf. step. step. step. stf.
step.

lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists r' : word, ms1 = MS (@bvmap_set 5 word 12 r' R) FF (wz 0x3fa18) fcc rv mm ro)) end.
{ step. destruct (Z.eq_dec sz 0) as [Z0|NZ].
- ifz. apply evt_done. eexists. simp_regs. reflexivity.
- ifz. step.
rewrite !(unsigned_lit sz), !(unsigned_lit cnt) by lia. rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.div_small (sz * cnt) (2^64)) by nia.
step. if_lit. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms1 [r' ->]. simp_regs.
step.
rewrite !(unsigned_lit sz), !(unsigned_lit cnt) by lia. replace (sz * cnt) with n by lia.
step. stp. step. stp. stp.
step. step. step. stp.
step.
lazymatch type of MUa with munch _ _ ?mm =>
destruct (sz_frame RE X a LB FS G m1 mm _ GC MUa WMa ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; right; idtac; lia)) as (FT & _ & FD);
pose proof (FT RT1) as RT2; pose proof (FD RD1) as RD2;
assert (RSE2 : RSec a LB RE X mm) by (eapply SEF; [exact MUa| exact WMa| intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; do 2 right; idtac; lia| exact RSE1]);
assert (RS2 : RStats RE X mm) by (eapply RStats_munch; [exact RS1| exact MUa| exact WMa| constructor; [st_avoid_solve| constructor]]) end.
clear FT FD RT1 RSE1 RD1 RS1 MUa WMa.
apply evt_done. change (wz 967832) with (wz A_INSTANCE).
eapply aimplT_then.
{ eapply (allocate_sec_spec L RE X large_alloc_spec poison_zero_spec _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s a G LB FS n 0 lo (bp + -2136) tsz dn q30 GC RT2 RS2 RSE2 RD2);
[assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| exact Hn| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post_sec in PO. rewrite !(unsigned_lit (bp + -2192)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 260676)) with (wz 260676) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_INSTANCE in REST.
clear OBJh TRQ RT2 RSE2 RD2 RS2.

assert (FRALL : forall mx, rw_cells asegs mx (bp + -2144) [CB 8 junk8b] -> rw_cells asegs mx (bp + -2136) (unw_obj (bp + -2136) tsz q rest bp) ->
rw_cells asegs mx (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mx (bp + -2144) ([CB 8 junk8b] ++ unw_obj (bp + -2136) tsz q rest bp ++ [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ intros mx O0 O1 O2. apply (proj2 (rw_cells_app asegs mx _ [CB 8 junk8b] _)). split; [exact O0|]. cbn [cells_size csize Nat.add].
replace (bp + -2144 + Z.of_nat 8) with (bp + -2136) by lia.
apply (proj2 (rw_cells_app asegs mx _ _ _)). split; [exact O1|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia).
unfold unw_obj. cbn [cells_size csize Nat.add map app length]. replace (bp + -2136 + Z.of_nat 2064) with (bp + -72) by lia. exact O2. }
destruct r as [p|].
-
destruct REST as (mb & -> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & -> & MUk & RSEk & CM & UZ).
specialize (UZ eq_refl).
pose proof MBK as MBK'. apply appr_to_lia in MBK'; [| pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG0 _]; lia| lia]. pose proof MBC as MBC'. idtac.
set (msz := sec_map_size n) in *.
destruct (zavoid_facts RE X a mb msz (rlay_avoid RE X RL) ltac:(pose proof (sec_geom_facts n Hn HP); lia) ZA) as (_ & AVP & _ & _).
assert (MS8 : 8 * (msz / 8) = msz /\ 8192 <= msz) by (pose proof (sec_geom_facts n Hn HP) as (G1 & _ & _ & _ & G5 & G6 & G7 & G8 & _); fold msz in G7, G8; clear - G1 G5 G6 G7 G8; Z.div_mod_to_equations; lia).
assert (SHM : SH (mb + msz) = SH mb + msz / 8) by (rewrite <- SH_plus8; f_equal; lia).
assert (MBH : 0x645000 <= mb) by (pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG _]; fold msz in SMG; pose proof (sec_req_facts n ltac:(lia) HP) as [_ RQn]; clear - MBK' SMG RQn; lia).
assert (SHB : 0x80000000 <= SH mb /\ SH mb + msz / 8 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; clear - MBH MBC' MS8; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD.
rewrite SHM in MUk. remember (msz / 8) as q8 eqn:EQ8. clear EQ8.
apply (munch_weaken _ (((bp - (2192 + 1152), bp) :: (rl_T X + 3168, rl_T X + 3169) :: (6434236, 6434236 + 4) :: (1514848, 1514849) :: (rl_T X + 2800, rl_T X + 3168)
:: (967832 + 104, 967832 + 728) :: (ptrarr_lo RE, ptrarr_lo RE + 8388608) :: (1841608, 6363632) :: (rl_dn X, rl_dn X + 1048576) :: (rl_ssb X, rl_ssb X + 8388608) :: nil)
++ [(mb, mb + msz); (SH mb, SH mb + q8)])) in MU.
2:{ intros z Hz. cbn [outside app] in Hz |- *. clear - Hz. tauto. }
cbn [app] in MU. cbn [app] in MUk. lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
rewrite KU. hide AVP.
step. ifz.
rtc RT3 24%nat K24. change (al_space_beg (ae_L RE)) with (prim_lo RE) in K24.
unfold A_INSTANCE. step.
clear K24.

assert (EPI : forall (a1v s3v : word),
evt asegs (calloc_post_sec ra bp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB n lo m (Some (ASec mb n), a') s)
(MS (mkR (wz 260676) (wz (bp + -2192)) gp (wz A_TP) y0 y1 y2 (wz n) (wz (bp + -2136)) (wz (mb + 6144)) a1v z2 z3 z4 z5 z6 z7
(wz 967832) s3v (wz 1) (wz (bp + -2136)) (wz (bp + -89)) s7 s8 s9 s10 s11 y3 y4 y5 y6)
F (wz 0x3fa98) fc None m3 (seg_rom asegs))).
{ intros a1v s3v.
step. step. step. step. step. step.
release_frame FR0 ST3 (bp + -2144).
step.
replace (ret_pc (wz 407572)) with (wz 407572) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 8 step. step.
pose proof (FRALL _ J8 OBJ FR) as FRX. clear OBJ OBJ3 FR J8.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST3 bp.
step.
apply evt_done. unfold calloc_post_sec. do 15 eexists. exists m3.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST3|].
split; [exact RT3|]. split; [exact RS3|]. split; [exact RD3|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. exists mb. cbv zeta. fold msz.
split; [reflexivity|]. split; [exact REG|]. split; [exact TQ|]. split; [exact GQ|]. split; [exact CLS|]. split; [exact CI|]. split; [exact NX|].
split; [exact NR|]. split; [exact SPN|]. split; [exact MBP|]. split; [exact MBK|]. split; [exact MBC|]. split; [exact ZA|].
split; [rewrite KU; reflexivity|]. split; [| split; [exact RSEk| split; [exact CM| rewrite KU; exact UZ]]].
rewrite SHM. unfold calloc_W_sec, CALLOC_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU. }
unhide AVP. destruct AVP as [LOW|HIGH].
+ step. ifz.
apply EPI.
+ step. ifz.
stp. step.
step. ifz.
apply EPI.
-
destruct REST as (-> & -> & MUk & RSEk).
lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
step. if_lit.
pose proof (munch_refl [(bp - 2208, bp - 2192); (A_ERRNO, A_ERRNO + 4)] m3) as MUe. pose proof (wmono_refl asegs m3) as WMe. unfold A_ERRNO in MUe.
step. call_ch (set_errno_spec RE X) ltac:(fun PO => unfold A_ERRNO in PO; rewrite !(unsigned_lit (bp + -2192)) in PO by lia);
[exact RS3| assumption| rewrite unsigned_lit by lia; exact ST3| exact CEIL'| rewrite unsigned_lit by lia; lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST4 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS4 end.
lazymatch type of MUe with munch _ _ ?mm =>
destruct (sz_frame RE X a LB FS G m3 mm _ GC MUe WMe
ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia])) as (FT & _ & FD);
assert (RSE4 : RSec a LB RE X mm) by (eapply SEF; [exact MUe| exact WMe| intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[do 2 right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia]| exact RSEk]) end.
pose proof (FT RT3) as RT4. pose proof (FD RD3) as RD4. clear FT FD MUe WMe RT3 RSEk RD3 RS3.
stp.
step. step. step. step. step. step.
release_frame FR0 ST4 (bp + -2144).
step.
replace (ret_pc (wz 407572)) with (wz 407572) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 8 step. step.
pose proof (FRALL _ J8 OBJ FR) as FRX. clear OBJ OBJ3 FR J8.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST4 bp.
step.
apply evt_done. unfold calloc_post_sec. do 15 eexists. lazymatch type of ST4 with stk _ ?mm _ _ => exists mm end.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST4|].
split; [exact RT4|]. split; [exact RS4|]. split; [exact RD4|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [| exact RSE4].
unfold calloc_W_sec, CALLOC_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU.
Qed.
End S.
End Mq1.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEEn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq2 QqLk QmP7.Mq0 QpY2.Mq1 Q9Ho.Mq1 QYyZ.Mq0 QnRU.Mq0 QOJv.Mq5 Qu3b.Mq2 QnaW.Mq1 QYyZ.Mq5 QYyZ.Mq3 QEEn.Mq0 QQ8H.Mq2.
Import QteI.Mq0.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Lemma RChunks_cons {BAND : Band} : forall a LB G RE X m p A n,
RChunks a LB G RE X m -> chunk_rep a G RE m p A n ->
(forall p' A' n' z, In (p', A', n') LB -> (p, A, n) <> (p', A', n') ->
in_iv (fst (chunk_cont p A n), snd (chunk_cont p A n) - fst (chunk_cont p A n)) z ->
in_iv (fst (chunk_cont p' A' n'), snd (chunk_cont p' A' n') - fst (chunk_cont p' A' n')) z -> False) ->
RChunks a ((p, A, n) :: LB) G RE X m.
Proof.
intros a LB G RE X m p A n [H1 H2] CR DJ. split.
- intros q B k [E|Hin]; [inversion E; subst; exact CR| exact (H1 _ _ _ Hin)].
- intros q B k q' B' k' z [E|Hin] [E'|Hin'] NE Z1 Z2.
+ inversion E; inversion E'; subst. exact (NE eq_refl).
+ inversion E; subst. exact (DJ _ _ _ z Hin' NE Z1 Z2).
+ inversion E'; subst. exact (DJ _ _ _ z Hin ltac:(intros EE; exact (NE (eq_sym EE))) Z2 Z1).
+ exact (H2 _ _ _ _ _ _ z Hin Hin' NE Z1 Z2).
Qed.

Section Z.
Context {BAND : Band}.
Variables (a a1 : AState) (LB : list ablock) (FS : list fframe) (G G1 : ghost) (RE : aentry) (X : rlay) (c i : Z).
Hypothesis GC : gcons a LB FS G RE X.
Hypothesis GS : gstep RE X a a1 G G1.
Hypothesis TI : tag_at G1 c i = Some TCached.
Let GC1 : gcons a1 LB FS G1 RE X := proj2 (proj2 (proj2 GS)) LB FS GC.

Lemma slot_fpP : forall x,
in_iv (slot_beg RE c i, class_size c) x \/ in_sh (slot_beg RE c i, class_size c) x -> fp_RPrim G RE X x.
Proof.
intros x Hx. pose proof GS as (SQ & SL & OLD & _). pose proof kconsts as (_ & KO & _ & K32 & _).
pose proof (tag_slot _ _ _ _ _ _ GC1 c i TCached TI) as (C1 & I1 & N1 & R1 & R2 & B1 & B2 & S1 & S2 & AL). rewrite KO in B2.
assert (NP : forall c' i' t', tag_at G c' i' = Some t' -> negb (tag_prim t') = true ->
(in_iv (slot_beg RE c' i', class_size c') x -> in_iv (slot_beg RE c i, class_size c) x -> False)
/\ (in_sh (slot_beg RE c' i', class_size c') x -> in_sh (slot_beg RE c i, class_size c) x -> False)).
{ intros c' i' t' Ht' NPt.
assert (Ht1 : tag_at G1 c' i' = Some t').
{ destruct t' as [| |q|q|]; cbn in NPt; try discriminate;
[apply (proj1 (SL c' i' (TLive q) eq_refl)); exact Ht'| apply (proj1 (SQ c' i' (TQuar q) eq_refl)); exact Ht'| apply (proj1 (SQ c' i' TQOwn eq_refl)); exact Ht']. }
assert (NEQ : c' <> c \/ i' <> i).
{ destruct (Z.eq_dec c' c) as [->|NC]; [| left; exact NC]. destruct (Z.eq_dec i' i) as [->|NI]; [| right; exact NI].
rewrite TI in Ht1. inversion Ht1. subst t'. cbn in NPt. discriminate. }
pose proof (tag_slot _ _ _ _ _ _ GC1 c' i' t' Ht1) as (C1' & I1' & _ & R1' & R2' & _ & _ & S1' & S2' & AL').
pose proof (slots_disjoint _ _ _ _ _ _ GC1 c' i' t' c i TCached Ht1 TI NEQ) as D.
split.
- intros [X1 X2] [Y1 Y2]; cbn [fst snd] in X1, X2, Y1, Y2. lia.
- intros SX SY. eapply (in_sh_disjoint (slot_beg RE c' i') (class_size c') (slot_beg RE c i) (class_size c) x);
[clear - AL'; Z.div_mod_to_equations; lia| clear - AL; Z.div_mod_to_equations; lia| lia| lia| exact D| exact SX| exact SY]. }
destruct Hx as [Hx|Hx].
- do 4 right. left. split.
+ exists c. rewrite K32, KO. split; [lia|]. destruct Hx as [X1 X2]; cbn [fst snd] in X1, X2. lia.
+ intros (c' & i' & t' & Ht' & NPt & IN). exact (proj1 (NP c' i' t' Ht' NPt) IN Hx).
- do 5 right. split.
+ exists c. rewrite K32, KO. split; [lia|]. pose proof (reg_beg_align RE X c (gc_rlay _ _ _ _ _ _ GC)) as (A8 & _).
apply (in_sh_sub (reg_beg (ae_L RE) c) 3758096384 (slot_beg RE c i) (class_size c) x A8 ltac:(clear - AL; Z.div_mod_to_equations; lia) R1 ltac:(lia) Hx).
+ intros (c' & i' & t' & Ht' & NPt & IN). exact (proj2 (NP c' i' t' Ht' NPt) IN Hx).
Qed.
End Z.

Section Lift.
Context {BAND : Band}.
Variable C : arun_components.
Variable LV : lvp.
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRD : ac_RDepot C = RDepot.

Definition mz (G : ghost) (RE : aentry) (X : rlay) (SP x : Z) : Prop :=
fp_RPrim G RE X x \/ fp_RStats RE X x \/ fp_RDepot RE X x \/ band_lo <= x < SP.

Lemma malloc_W_mz0 : forall a LB FS G RE X c bp lo hi x,
gcons a LB FS G RE X -> 1 <= c <= 31 -> band_lo <= bp - MALLOC_STACK ->
In (lo, hi) (malloc_W RE X bp c (c_alloc_user (cls a c))) -> lo <= x < hi -> mz G RE X bp x.
Proof.
intros a LB FS G RE X c bp lo hi x GC Hc CSP Hin Hx. pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
pose proof (QSsj.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB.
pose proof (gc_bounds _ _ _ _ _ _ GC c ltac:(rewrite K32; lia)) as (AU1 & AU2 & _). rewrite KO in AU2.
assert (SHF : SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo) by (rewrite FB; unfold SH, A_SHADOW_OFS; clear - PAL PK PCH PH Hc; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD0.
assert (SHR : SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo) by (rewrite RB; unfold SH, A_SHADOW_OFS; clear - PAL PK PCH PH Hc; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD1.
idtac. rewrite ?KHI_eq in TK.
unfold malloc_W, alloc_W, MALLOC_STACK, ALLOC_STACK in Hin, CSP. cbn [tl app] in Hin.
assert (CB : forall lo' hi', In (lo', hi') (comb_W RE X (bp - 2144) c (c_alloc_user (cls a c))) -> hi' <= band_lo -> lo' <= x < hi' -> mz G RE X bp x).
{ intros lo' hi' Hin' B Hx'. destruct (comb_W_pz RE X a LB FS G (bp - 2144) c x lo' hi' GC Hc ltac:(idtac; unfold COMB_STACK; lia) Hin' Hx') as [P|[P|P]];
[left; exact P| right; left; exact P| idtac; lia]. }
unfold comb_W, COMB_STACK in CB.
destruct Hin as [E|[E|[E|[E|Hin]]]].
- injection E as <- <-. do 3 right. idtac. lia.
- injection E as <- <-. do 2 right; left. do 3 right. lia.
- injection E as <- <-. right; left. right; left. split; cbn [fst snd]; lia.
- injection E as <- <-. right; left. do 2 right. lia.
- cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; first
[ injection E as <- <-; right; left; do 2 right; lia
| injection E as <- <-; do 2 right; left; left; unfold SS_BASE, DP_END in *; split; cbn [fst snd]; lia
| injection E as <- <-; do 2 right; left; right; left; split; cbn [fst snd]; lia
| injection E as <- <-; do 2 right; left; do 2 right; left; split; cbn [fst snd]; lia
| injection E as <- <-; refine (CB _ _ _ _ Hx); [cbn [In]; tauto| first [lia | unfold ri_addr; lia | rewrite KS; lia | rewrite KS; change (536870912 / 8) with 67108864; lia | rewrite KO; lia | rewrite KO; change (3758096384 / 8) with 469762048; lia]] ].
Qed.

Lemma malloc_W_mz : forall a a1 LB FS G G1 RE X c i bp lo hi x,
gcons a LB FS G RE X -> gstep RE X a a1 G G1 -> tag_at G1 c i = Some TCached -> 1 <= c <= 31 ->
band_lo <= bp - MALLOC_STACK ->
In (lo, hi) (malloc_W RE X bp c (c_alloc_user (cls a c)) ++ slot_W RE c i) -> lo <= x < hi -> mz G RE X bp x.
Proof.
intros a a1 LB FS G G1 RE X c i bp lo hi x GC GS TI Hc CSP Hin Hx.
apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (malloc_W_mz0 a LB FS G RE X c bp lo hi x GC Hc CSP Hin Hx)|].
unfold slot_W in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; left;
apply (slot_fpP a a1 LB FS G G1 RE X c i GC GS TI); [left| right]; split; cbn [fst snd]; lia.
Qed.

Lemma mz_azone : forall a LB0 G RE X SP x, mz G RE X SP x -> azone a LB0 G RE X SP x.
Proof. intros a LB0 G RE X SP x [H|[H|[H|H]]]; unfold azone; tauto. Qed.

Lemma lift_some : forall s LB FS RE X G LB0 FS0 aa1 G1 c i n m m' SP W,
Permutation LB LB0 -> Permutation FS FS0 ->
gcons (ps_a s) LB0 FS0 G RE X -> RChunks (ps_a s) LB0 G RE X m -> ac_RSec C (ps_a s) LB0 RE X m ->
ac_RQuar C (ps_a s) LB0 G RE X m -> ac_RFake C FS0 RE X m ->
c = class_of n -> 0 <= n <= 2^26 -> from_primary n = true -> band_lo <= SP ->
qframe (ps_a s) aa1 -> gstep RE X (ps_a s) aa1 G G1 -> tag_at G1 c i = Some TCached -> 0 <= i ->
munch W m m' -> wmono asegs m m' -> (forall lo hi x, In (lo, hi) W -> lo <= x < hi -> mz G RE X SP x) ->
RTconst RE X m' -> RStats RE X m' -> RDepot RE X m' ->
(forall t, tag_prim t = false -> RPrim aa1 (set_tag c i t G1) RE X m') ->
chunk_mem m' (slot_beg RE c i) (slot_beg RE c i + class_size c) (slot_beg RE c i + rz_size n) n ->
aheap_presA asegs a_alayout LB FS SP m m'
/\ ablock_rangeA (slot_beg RE c i + rz_size n) n
/\ ARUN C (set_a (set_next (N.succ (as_next aa1)) aa1) s) ((APrim (as_next aa1) n, slot_beg RE c i + rz_size n, n) :: LB) FS RE m'
/\ blk_shadow asegs m' (slot_beg RE c i + rz_size n) n.
Proof.
intros s LB FS RE X G LB0 FS0 aa1 G1 c i n m m' SP W PB PF GC R4 R5 R6 R8 Ec Hn HP CSP QF GS TI I0 MU WM ZN RT' RS' RD' RPF CM.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof (class_of_facts n ltac:(lia) HP) as (Hc & Csz & _). cbv zeta in Hc, Csz. rewrite <- Ec in Hc, Csz.
pose proof (needed_facts n ltac:(lia)) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
pose proof GS as (SQ & SL & OLD & GCT). pose proof (GCT LB0 FS0 GC) as GC1.
destruct QF as (QF1 & QF2 & QF3 & QF4 & QF5 & QF6).
assert (QR : QR3 C (ps_a s) LB0 FS0 G RE X m) by (split; [exact R4| split; [exact R5| exact R8]]).
assert (ZA : forall lo' hi' x, In (lo', hi') W -> lo' <= x < hi' -> azone (ps_a s) LB0 G RE X SP x) by (intros lo' hi' x Hin Hx; apply mz_azone; exact (ZN lo' hi' x Hin Hx)).
split; [eapply aheap_presA_of_munch_a; [exact GC| exact PB| exact PF| exact CSP| exact MU| exact WM| exact ZA]|].
set (A := slot_beg RE c i + rz_size n) in *. set (p := APrim (as_next aa1) n) in *. set (G' := set_tag c i (TLive p) G1) in *.
pose proof (tag_slot _ _ _ _ _ _ GC1 c i TCached TI) as (C1 & _ & _ & SL1 & SL2 & SB1 & SB2 & CS1 & CS2 & AL). rewrite KO in SB2.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (N1 : n <= class_size c - rz_size n) by (unfold needed in Csz; pose proof (round_up_8 (Z.max n 8) ltac:(lia)); lia).

pose proof (gcons_alloc_prim aa1 LB0 FS0 G1 RE X c i n GC1 TI Ec Hn HP) as GC2. fold p in GC2. fold A in GC2. fold G' in GC2.
assert (QR' : QR3 C aa1 LB0 FS0 G1 RE X m').
{ eapply QR3_ext; [eapply (QR3_munch C); [exact GC| exact QR| exact MU| exact WM| exact ZA]| exact QF3| exact QF4| exact QF5| exact SL]. }
destruct QR' as (RC' & RSe' & RF').
assert (RC2 : RChunks (set_next (N.succ (as_next aa1)) aa1) ((p, A, n) :: LB0) G' RE X m').
{ apply RChunks_cons.
- eapply RChunks_sub; [exact RC'| intros b Hb; exact Hb| intros e He; exact He|].
intros q B k c' i' Hin Ht. subst G'. rewrite tag_at_set_tag_ne; [exact Ht| lia|].
destruct (Z.eq_dec c' c) as [->|NC]; [right| left; exact NC]. intros ->. rewrite TI in Ht. discriminate.
- cbn [chunk_rep]. split; [reflexivity|]. exists i. rewrite <- Ec. split; [subst G'; apply (tag_at_set_tag_eq _ _ _ _ _ TI)|]. split; [reflexivity| exact CM].
- intros q B k z Hin NE Z1 Z2. subst p. cbn [chunk_cont fst snd] in Z1.
replace (A - rz_size n) with (slot_beg RE c i) in Z1 by (subst A; lia).
replace (slot_beg RE c i + class_size (class_of n) - slot_beg RE c i) with (class_size c) in Z1 by (rewrite <- Ec; lia).
pose proof (RChunks_open _ _ _ _ _ _ _ _ _ RC' Hin) as CRq.
destruct q as [idq nq|mb nq]; cbn [chunk_rep chunk_cont fst snd] in CRq, Z2.
+ destruct CRq as (-> & i' & Hti' & HB & _).
replace (B - rz_size k + class_size (class_of k) - (B - rz_size k)) with (class_size (class_of k)) in Z2 by lia.
rewrite HB in Z2. replace (slot_beg RE (class_of k) i' + rz_size k - rz_size k) with (slot_beg RE (class_of k) i') in Z2 by lia.
assert (NEQ : class_of k <> c \/ i' <> i).
{ destruct (Z.eq_dec (class_of k) c) as [EC|NC]; [| left; exact NC]. destruct (Z.eq_dec i' i) as [->|NI]; [| right; exact NI].
rewrite EC, TI in Hti'. discriminate. }
pose proof (slots_disjoint _ _ _ _ _ _ GC1 _ _ _ c i TCached Hti' TI NEQ) as D.
destruct Z1 as [X1 X2], Z2 as [Y1 Y2]; cbn [fst snd] in X1, X2, Y1, Y2. lia.
+ destruct CRq as (-> & Hr & HB & _).
pose proof (sec_entry_facts (ps_a s) LB0 FS0 G RE X GC _ ltac:(rewrite <- QF3; exact Hr)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & _). cbn [se_beg se_size se_req] in *.
unfold iv_disjoint, prim_lo in E7. cbn [fst snd] in E7. rewrite KP in Z2.
destruct Z1 as [X1 X2], Z2 as [Y1 Y2]; cbn [fst snd] in X1, X2, Y1, Y2. unfold prim_lo in *. lia. }
split. { unfold ablock_rangeA. rewrite ?KHI_eq. unfold prim_lo, prim_hi in *. subst A. repeat split; first [lia| clear - AL RZ2; Z.div_mod_to_equations; lia]. }
split.
{ eapply (ARUN_close C _ _ _ _ _ X G' ((p, A, n) :: LB0) FS0); [apply perm_skip; exact PB| exact PF|]. cbn [ps_a set_a].
split; [exact GC2|]. rewrite HRT, HRS, HRP, HRC, HRD.
split; [exact RT'|]. split; [exact RS'|].
split. { eapply RPrim_ext; [exact (RPF (TLive p) eq_refl)| intros; reflexivity| reflexivity| apply same_len_refl| apply same_tags_refl]. }
split; [exact RC2|].
split. { eapply (ac_RSec_ext C); [exact RSe'| reflexivity| reflexivity| reflexivity]. }
split.
{ eapply (ac_RQuar_ext C).
- eapply (ac_RQuar_frame C); [exact R6| exact WM|]. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx _. apply outside_intro.
intros lo' hi' Hin Hx. pose proof (ZN lo' hi' x Hin Hx) as [P|[P|[P|P]]].
+ exact (fpQ_RPrim _ _ _ _ _ _ GC x Fx P).
+ exact (fpQ_RStats _ _ _ _ _ _ GC x Fx P).
+ exact (fpQ_RDepot _ _ _ _ _ _ GC x Fx P).
+ exfalso. apply (fp_RQuar_cz _ _ FS0 _ _ _ GC x Fx). left. lia.
- cbn. exact QF1.
- cbn. exact QF2.
- cbn. exact QF3.
- intros e He. unfold sec_live. cbn [In]. split; [intros (B & HB); exists B; right; exact HB| intros (B & [HB|HB]); [exfalso; subst p; discriminate| exists B; exact HB]].
- intros c' i' t Ht. split; intros H.
+ subst G'. rewrite tag_at_set_tag_ne; [apply (proj1 (SQ c' i' t Ht)); exact H| lia|].
destruct (Z.eq_dec c' c) as [->|NC]; [right| left; exact NC]. intros ->. apply (proj1 (SQ c i t Ht)) in H. rewrite TI in H. inversion H. subst t. discriminate.
+ subst G'. destruct (Z.eq_dec c' c) as [EC|NC]; [destruct (Z.eq_dec i' i) as [EI|NI]|].
* subst c' i'. rewrite (tag_at_set_tag_eq _ _ _ _ _ TI) in H. inversion H. subst t. discriminate.
* rewrite tag_at_set_tag_ne in H by (first [lia| right; lia]). apply (proj2 (SQ c' i' t Ht)). exact H.
* rewrite tag_at_set_tag_ne in H by (first [lia| left; lia]). apply (proj2 (SQ c' i' t Ht)). exact H. }
split; [exact RD'| exact RF']. }
exact (RChunks_shadow _ _ FS0 _ _ X _ p A n GC2 RC2 ltac:(left; reflexivity)).
Qed.

Lemma lift_none : forall s LB FS RE X G LB0 FS0 aa G1 c n m m' SP W,
Permutation LB LB0 -> Permutation FS FS0 ->
gcons (ps_a s) LB0 FS0 G RE X -> RChunks (ps_a s) LB0 G RE X m -> ac_RSec C (ps_a s) LB0 RE X m ->
ac_RQuar C (ps_a s) LB0 G RE X m -> ac_RFake C FS0 RE X m ->
c = class_of n -> band_lo <= SP ->
qframe (ps_a s) aa -> gstep RE X (ps_a s) aa G G1 ->
munch W m m' -> wmono asegs m m' -> (forall lo hi x, In (lo, hi) W -> lo <= x < hi -> mz G RE X SP x) ->
RTconst RE X m' -> RStats RE X m' -> RDepot RE X m' -> RPrim aa G1 RE X m' ->
aheap_presA asegs a_alayout LB FS SP m m' /\ ARUN C (set_a aa s) LB FS RE m'.
Proof.
intros s LB FS RE X G LB0 FS0 aa G1 c n m m' SP W PB PF GC R4 R5 R6 R8 Ec CSP QF GS MU WM ZN RT' RS' RD' RP'.
pose proof GS as (SQ & SL & OLD & GCT). pose proof (GCT LB0 FS0 GC) as GC1.
destruct QF as (QF1 & QF2 & QF3 & QF4 & QF5 & QF6).
assert (QR : QR3 C (ps_a s) LB0 FS0 G RE X m) by (split; [exact R4| split; [exact R5| exact R8]]).
assert (ZA : forall lo' hi' x, In (lo', hi') W -> lo' <= x < hi' -> azone (ps_a s) LB0 G RE X SP x) by (intros lo' hi' x Hin Hx; apply mz_azone; exact (ZN lo' hi' x Hin Hx)).
split; [eapply aheap_presA_of_munch_a; [exact GC| exact PB| exact PF| exact CSP| exact MU| exact WM| exact ZA]|].
assert (QR' : QR3 C aa LB0 FS0 G1 RE X m').
{ eapply QR3_ext; [eapply (QR3_munch C); [exact GC| exact QR| exact MU| exact WM| exact ZA]| exact QF3| exact QF4| exact QF5| exact SL]. }
destruct QR' as (RC' & RSe' & RF').
eapply (ARUN_close C _ _ _ _ _ X G1 LB0 FS0); [exact PB| exact PF|]. cbn [ps_a set_a].
split; [exact GC1|]. rewrite HRT, HRS, HRP, HRC, HRD.
split; [exact RT'|]. split; [exact RS'|]. split; [exact RP'|]. split; [exact RC'|]. split; [exact RSe'|].
split.
{ eapply (ac_RQuar_ext C).
- eapply (ac_RQuar_frame C); [exact R6| exact WM|]. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx _. apply outside_intro.
intros lo' hi' Hin Hx. pose proof (ZN lo' hi' x Hin Hx) as [P|[P|[P|P]]].
+ exact (fpQ_RPrim _ _ _ _ _ _ GC x Fx P).
+ exact (fpQ_RStats _ _ _ _ _ _ GC x Fx P).
+ exact (fpQ_RDepot _ _ _ _ _ _ GC x Fx P).
+ exfalso. apply (fp_RQuar_cz _ _ FS0 _ _ _ GC x Fx). left. lia.
- exact QF1.
- exact QF2.
- exact QF3.
- intros; tauto.
- exact SQ. }
split; [exact RD'| exact RF'].
Qed.

Lemma malloc_prim_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (n lo dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_malloc_stack a_alayout ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 n -> 0 <= n <= 2^26 ->
from_primary n = true ->
@implMG PStateA asegs (at_nodeA LV asegs) _ (raw_malloc_A L n) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some p => exists A junk,
a0' = Z_to_bv 64 A /\ ablock_rangeA A n /\ aptr_req p = n
/\ ARUN C s' ((p, A, n) :: LB) FS RE m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
/\ blk_shadow asegs m' A n
/\ (forall mb k, p = ASec mb k -> A = mb + kSecUserOff)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ala_malloc a_alayout)) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros EL AR ST CEIL LO MI -> -> UNW DNH DCAP -> Hn HP.
cbn [ala_malloc_stack ala_tp ala_gp ala_malloc a_alayout] in LO |- *.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRD in R7.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof (class_of_facts n ltac:(lia) HP) as (Hc & Csz & _). cbv zeta in Hc, Csz.
pose proof (needed_facts n ltac:(lia)) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
apply raw_malloc_A_intro. rewrite <- EL.
pose proof (malloc_icpt_spec LV RE X ra (bv_unsigned sp) (wz 67584) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s (ps_a s) G LB0 FS0 lo n dn GC R1 R2 R3 R7 MI ST CEIL' ltac:(unfold MALLOC_STACK; lia) ltac:(lia) UNW DNH DCAP ltac:(lia) HP) as M.
rewrite Z_to_bv_bv_unsigned in M.
eapply aimplT_mono; [exact M|]. clear M.
intros [r aa] s' ms' PO. cbn [fst snd]. unfold malloc_post in PO.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m' & G1 & -> & -> & WM & MI' & ST' & RT' & RS' & RD' & DS' & REST).
unfold std_postA. rewrite Z_to_bv_bv_unsigned. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
set (c := class_of n) in *.
destruct r as [p|].
- destruct REST as (aa1 & i & -> & -> & QF & GS & TI & I0 & -> & MU & RPF & CM & HJU).
destruct (lift_some s LB FS RE X G LB0 FS0 aa1 G1 c i n m m' (bv_unsigned sp) _ PB PF GC R4 R5 R6 R8 eq_refl Hn HP ltac:(idtac; lia) QF GS TI I0 MU WM
ltac:(intros lo' hi' x Hin Hx; eapply (malloc_W_mz (ps_a s) aa1 LB0 FS0 G G1 RE X c i); try eassumption; [lia| idtac; unfold MALLOC_STACK; lia])
RT' RS' RD' RPF CM) as (HP1 & HP2 & HP3 & HP4).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|].
pose proof (class_of_facts n ltac:(lia) HP) as (_ & Csz' & _). cbv zeta in Csz'. fold c in Csz'.
assert (N1 : n <= class_size c - rz_size n) by (unfold needed in Csz'; pose proof (round_up_8 (Z.max n 8) ltac:(lia)); lia).
destruct (hjunk_split _ _ (slot_beg RE c i + rz_size n + n) _ HJU ltac:(lia)) as [HJ1 _].
replace (slot_beg RE c i + rz_size n + n) with (slot_beg RE c i + rz_size n + Z.of_nat (Z.to_nat n)) in HJ1 by lia. destruct (hjunk_cells _ _ _ HJ1) as [junk UC].
split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|].
exists (slot_beg RE c i + rz_size n), junk. split; [reflexivity|]. split; [exact HP2|]. split; [reflexivity|]. split; [exact HP3|].
split; [exact UC|]. split; [exact HP4|]. intros mb k E. discriminate.
- destruct REST as (-> & MU & QF & GS & RP').
destruct (lift_none s LB FS RE X G LB0 FS0 aa G1 c n m m' (bv_unsigned sp) _ PB PF GC R4 R5 R6 R8 eq_refl ltac:(idtac; lia) QF GS MU WM
ltac:(intros lo' hi' x Hin Hx; eapply (malloc_W_mz0 (ps_a s) LB0 FS0 G RE X c); try eassumption; [lia| idtac; unfold MALLOC_STACK; lia])
RT' RS' RD' RP') as (HP1 & HP3).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|]. split; [reflexivity| exact HP3].
Qed.
End Lift.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QTVW.Mq3 QOJv.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk QnRU.Mqa QmP7.Mq0 QpY2.Mq1 QYyZ.Mq0 Qu3b.Mq2 QYyZ.Mq5 QkfD QYyZ.Mq3 QpME.Mq1 QkJ4 QQ8H.Mq2 QmvA.Mq1 QpME.Mq6.
Import QVo2.Mq1.
Import QpY2.Mq2.
Import QRfV.Mq0 QnRU.Mq9 QEYd.
Import QcfN.Mq1.
Import QlES.
Import QVo2.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Let atn := at_nodeA L asegs.
Hypothesis large_alloc_spec : large_alloc_stmt RE X L.
Hypothesis poison_zero_spec : poison_zero_stmt_lh RE X L.

Definition malloc_W_sec (bp : Z) : list (Z * Z) :=
(bp - MALLOC_STACK, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W_sec RE X (bp - 2144)).

Definition malloc_post_sec (ra : word) (bp : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (LB : list ablock) (n lo : Z) (m : word -> option byte)
(r : option aptr * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
ms' = MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo bp
/\ RTconst RE X m' /\ RStats RE X m' /\ RDepot RE X m' /\ depot_step m m'
/\ match r with
| (None, a1) => a0 = wz 0 /\ a1 = a /\ munch (malloc_W_sec bp) m m' /\ RSec a LB RE X m'
| (Some p, a1) => exists mb, let msz := sec_map_size n in
p = ASec mb n
/\ as_reg a1 = as_reg a ++ [mkSec mb msz n]
/\ as_tq a1 = as_tq a /\ as_gq a1 = as_gq a /\ (forall c, cls a1 c = cls a c)
/\ as_cache_inited a1 = as_cache_inited a /\ as_next a1 = as_next a
/\ (as_nres a1 = as_nres a \/ as_nres a1 = as_nres a + kPtrArrBlock)
/\ as_spent a1 = as_spent a + sec_cost msz
/\ mb mod kPage = 0 /\ appr mb msz /\ mb + msz <= band_lo /\ zavoids mb msz (avoid_of (ae_L RE) a) = true
/\ a0 = wz (mb + kSecUserOff)
/\ munch (malloc_W_sec bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m m'
/\ RSec a1 LB RE X m'
/\ chunk_mem m' (mb + kPage) (mb + msz) (mb + kSecUserOff) n
end.

Lemma malloc_icpt_sec_spec : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PStateA) (a : AState) (G : ghost) (LB : list ablock) (FS : list fframe) (lo n dn : Z),
gcons a LB FS G RE X ->
RTconst RE X m -> RStats RE X m -> RSec a LB RE X m -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - MALLOC_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
0 <= n <= 2^26 -> from_primary n = false ->
aimplT atn (asan_malloc (ae_L RE) a n) s
(malloc_post_sec ra bp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB n lo m)
(MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x632c8) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros GC RT RS RSE RD MI ST CEIL LO BPR UNW DNH DCAP Hn HP.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof CEIL as CEIL'. idtac. unfold MALLOC_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & PC & _ & QK & QC & _). unfold prim_hi in PC. unfold ptrarr_hi in QC. idtac. rewrite ?KHI_eq in PK.
change (al_space_beg (ae_L RE)) with (prim_lo RE) in PC. change (al_ptrarr (ae_L RE)) with (ptrarr_lo RE) in QC.
apply appr_to_lia in QK; [| lia| lia].
pose proof (munch_refl (malloc_W_sec bp) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold malloc_W_sec, MALLOC_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE in MU. cbn [tl app] in MU.

assert (SEF : forall mm mm' W, munch W mm mm' -> wmono asegs mm mm' ->
(forall lo' hi' z, In (lo', hi') W -> lo' <= z < hi' -> fp_RStats RE X z \/ fp_RDepot RE X z \/ band_lo <= z) ->
RSec a LB RE X mm -> RSec a LB RE X mm').
{ intros mm mm' W MUw WMw HW RSEw. eapply RSec_frame; [exact RSEw| exact WMw|]. eapply agree_on_of_munch; [exact MUw| exact WMw|]. intros z Fz _. apply outside_intro.
intros lo' hi' Hin Hz. destruct (HW lo' hi' z Hin Hz) as [P|[P|P]].
- exact (fpS_excl _ _ _ _ _ _ GC z P ltac:(right; left; exact Fz)).
- exact (fpD_excl _ _ _ _ _ _ GC z P ltac:(right; left; exact Fz)).
- pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)). lia. }
apply aimplT_from_evt.
eapply malloc_icpt_pre; [exact RT| exact RL| exact (RDepot_unw RE X _ RD)| exact MI| exact ST| exact CEIL'| unfold MALLOC_STACK; lia| exact BPR| exact UNW| lia|].
intros m1 u0 u1 u2 u3 u4 u5 u6 u7 u8 u10 u11 u12 u13 sz q rest junk8 MU1 WM1 MI1 ST1 OBJ LQ SZR FR RT1 TU1.
unfold micpt_W in MU1.
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU1| exact WM1|]. constructor; [first [st_avoid_solve| eapply st_avoid_T; [eassumption| lia| lia]]|]. constructor; [st_avoid_solve| constructor]. }
assert (RSE1 : RSec a LB RE X m1).
{ eapply SEF; [exact MU1| exact WM1| | exact RSE]. intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
- do 2 right. idtac. lia.
- right; left. do 3 right. lia. }
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame_unw; [exact RL| exact RD| exact WM1| | exact TU1]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z [Fz NZ] _. cbn [outside].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). idtac. lia. }
phase_done MU m m1 MU1 WM1. clear RT RS RSE RD MI. try clear ST.
destruct (unw_obj_head _ _ _ _ _ _ OBJ LQ ltac:(lia)) as [OBJh (q30 & TRQ & LQ30)].

unfold asan_malloc_entry. carve_frame 16%nat ST1.
match goal with H : rw_cells asegs _ (bp + -2128 + -16) _ |- _ => replace (bp + -2128 + -16) with (bp + -2144) in H by lia end.
replace (bp + -2128 + -16) with (bp + -2144) in ST1 by lia.
pose proof (munch_refl [(bp - 2144, bp - 2128)] m1) as MUa. pose proof (wmono_refl asegs m1) as WMa.
step. stf. step.
step. step. step. stp. stp. step. stp.
step.
lazymatch type of MUa with munch _ _ ?mm =>
destruct (sz_frame RE X a LB FS G m1 mm _ GC MUa WMa ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; right; idtac; lia)) as (FT & _ & FD);
pose proof (FT RT1) as RT2; pose proof (FD RD1) as RD2;
assert (RSE2 : RSec a LB RE X mm) by (eapply SEF; [exact MUa| exact WMa| intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; do 2 right; idtac; lia| exact RSE1]);
assert (RS2 : RStats RE X mm) by (eapply RStats_munch; [exact RS1| exact MUa| exact WMa| constructor; [st_avoid_solve| constructor]]) end.
clear FT FD RT1 RSE1 RD1 RS1 MUa WMa.
apply evt_done. change (wz 967832) with (wz A_INSTANCE).
eapply aimplT_then.
{ eapply (allocate_sec_spec L RE X large_alloc_spec poison_zero_spec _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s a G LB FS n 1 lo (bp + -2128) sz dn q30 GC RT2 RS2 RSE2 RD2);
[assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| exact Hn| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post_sec in PO. rewrite !(unsigned_lit (bp + -2144)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 258104)) with (wz 258104) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_INSTANCE in REST.
clear OBJh TRQ RT2 RSE2 RD2 RS2.

assert (FRALL : forall mx, rw_cells asegs mx (bp + -2128) (unw_obj (bp + -2128) sz q rest bp) ->
rw_cells asegs mx (bp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mx (bp + -2128) (unw_obj (bp + -2128) sz q rest bp ++ [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ intros mx O1 O2. apply (proj2 (rw_cells_app asegs mx _ _ _)). split; [exact O1|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia).
unfold unw_obj. cbn [cells_size csize Nat.add map app]. replace (bp + -2128 + Z.of_nat 2064) with (bp + -64) by lia. exact O2. }
destruct r as [p|].
-
destruct REST as (mb & -> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & -> & MUk & RSEk & CM & _).
pose proof MBK as MBK'. apply appr_to_lia in MBK'; [| pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG0 _]; lia| lia]. pose proof MBC as MBC'. idtac.
set (msz := sec_map_size n) in *.
assert (MS8 : 8 * (msz / 8) = msz /\ 4096 <= msz) by (pose proof (sec_geom_facts n Hn HP) as (G1 & _ & _ & _ & G5 & G6 & G7 & G8 & _); fold msz in G7, G8; clear - G1 G5 G6 G7 G8; Z.div_mod_to_equations; lia).
assert (SHM : SH (mb + msz) = SH mb + msz / 8) by (rewrite <- SH_plus8; f_equal; lia).
assert (MBH : 0x645000 <= mb) by (pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG _]; fold msz in SMG; pose proof (sec_req_facts n ltac:(lia) HP) as [_ RQn]; clear - MBK' SMG RQn; lia).
assert (SHB : 0x80000000 <= SH mb /\ SH mb + msz / 8 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; clear - MBH MBC' MS8; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD.
rewrite SHM in MUk. remember (msz / 8) as q8 eqn:EQ8. clear EQ8.
apply (munch_weaken _ (((bp - 3296, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (6434236, 6434236 + 4) :: (1514848, 1514849) :: (rl_T X + 2800, rl_T X + 3168)
:: (967832 + 104, 967832 + 728) :: (ptrarr_lo RE, ptrarr_lo RE + 8388608) :: (1841608, 6363632) :: (rl_dn X, rl_dn X + 1048576) :: (rl_ssb X, rl_ssb X + 8388608) :: nil)
++ [(mb, mb + msz); (SH mb, SH mb + q8)])) in MU.
2:{ intros z Hz. cbn [outside app] in Hz |- *. clear - Hz. tauto. }
cbn [app] in MU. cbn [app] in MUk. phase_done MU m2 m3 MUk WM3.
rewrite KU.
step. ifz.
step. step. step.
release_frame FR0 ST3 (bp + -2128).
step.
replace (ret_pc (wz 407004)) with (wz 407004) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 7 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST3 bp.
step.
apply evt_done. unfold malloc_post_sec. do 15 eexists. exists m3.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST3|].
split; [exact RT3|]. split; [exact RS3|]. split; [exact RD3|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. exists mb. cbv zeta. fold msz.
split; [reflexivity|]. split; [exact REG|]. split; [exact TQ|]. split; [exact GQ|]. split; [exact CLS|]. split; [exact CI|]. split; [exact NX|].
split; [exact NR|]. split; [exact SPN|]. split; [exact MBP|]. split; [exact MBK|]. split; [exact MBC|]. split; [exact ZA|].
split; [rewrite KU; reflexivity|]. split; [| split; [exact RSEk| exact CM]].
rewrite SHM. unfold malloc_W_sec, MALLOC_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU.
-
destruct REST as (-> & -> & MUk & RSEk).
phase_done MU m2 m3 MUk WM3.
step. if_lit.
step.
pose proof (munch_refl [(bp - 2160, bp - 2144); (A_ERRNO, A_ERRNO + 4)] m3) as MUe. pose proof (wmono_refl asegs m3) as WMe. unfold A_ERRNO in MUe.
step. call_ch (set_errno_spec RE X) ltac:(fun PO => unfold A_ERRNO in PO; rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RS3| assumption| rewrite unsigned_lit by lia; exact ST3| exact CEIL'| rewrite unsigned_lit by lia; lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST4 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS4 end.
lazymatch type of MUe with munch _ _ ?mm =>
destruct (sz_frame RE X a LB FS G m3 mm _ GC MUe WMe
ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia])) as (FT & _ & FD);
assert (RSE4 : RSec a LB RE X mm) by (eapply SEF; [exact MUe| exact WMe| intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[do 2 right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia]| exact RSEk]) end.
pose proof (FT RT3) as RT4. pose proof (FD RD3) as RD4. clear FT FD MUe WMe RT3 RSEk RD3 RS3.
step.
step. step. step.
release_frame FR0 ST4 (bp + -2128).
step.
replace (ret_pc (wz 407004)) with (wz 407004) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 7 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST4 bp.
step.
apply evt_done. unfold malloc_post_sec. do 15 eexists. lazymatch type of ST4 with stk _ ?mm _ _ => exists mm end.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST4|].
split; [exact RT4|]. split; [exact RS4|]. split; [exact RD4|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [| exact RSE4].
unfold malloc_W_sec, MALLOC_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU.
Qed.
End S.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUnM QkZz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QqLk QnRU.Mqa Q9Ho.Mq2 QmP7.Mq0 QYyZ.Mq0 Q9Ho.Mq1.
Import QpY2.Mq2.
Import QUnM QpME.Mq0.
Import QYyZ.Mq5.
Import Qu3b.Mq2 QnRU.Mq8 QmvA.Mq3 QkZz.Mq1 QteI.Mq9 QQ8H.Mq3.
Import QcfN.Mq1.
Import QlES.
Import QnRU.Mq6.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_3 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.

Import QpME.Mq4.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_4 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Ltac Q0z1.sf_hide_poison ::= sf_hide_poison_divlit. Local Ltac mkr__sf_hide_poison_5 := sf_hide_poison_divlit.

Local Notation wz := (Z_to_bv 64).

Definition qchunk_entry : Z := 0x43394.

Definition QCHUNK_STACK : Z := PUT_STACK.

Section S.
Context {BAND : Band}.
Variables (C : arun_components) (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).
Hypothesis recycle_spec : recycle_stmt C RE X L.

Hypothesis HRD : ac_RDepot C = RDepot.

Lemma qchunk_spec : forall ra sp gp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (p : aptr) (A lo : Z)
(obj sz bp dn : Z) (q0 q1 q2 q3 q4 : word) (rest : list byte),
QRUN C 0 QB QB [(p, A)] a LB0 FS0 G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - QCHUNK_STACK ->
0 <= aptr_req p <= 2^26 ->
qroom a p ->
rw_cells asegs m obj (unw_obj obj sz [q0; q1; q2; q3; q4] rest bp) ->
1 <= sz <= 30 -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= obj -> obj + 2080 < 2^64 ->
aimplT atn (tbind (enqueue (ae_L RE) a p) (fun s1 => if kQMaxCache <? q_bytes (as_tq s1) then drain (ae_L RE) s1 else tret s1)) s
(qret_post C RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 FS0 lo m free_step)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz (A - 16)) a2 (wz obj) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz qchunk_entry) fc None m (seg_rom asegs)).
Proof.
intros until rest; intros QR MI ST CEIL LO HN QRM OBJ SZB DNH DCAP OLO OHI.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof CEIL as CEIL'. idtac. unfold QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
change (2^64) with 18446744073709551616 in OHI.
pose proof kq_consts as (K24 & KBB & KBC & KMX & KMN & KMC). pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (rlay_obj_facts_lia RE X _ RL (ctx_obj RE X)) as (_ & CK & CB' & _). cbn [fst snd] in CK, CB'. idtac. rewrite ?KHI_eq in CK.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC, TD. rewrite ?KHI_eq in PK. idtac.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND). unfold QB in BND.
pose proof PQA as PQA0. apply Forall_cons_iff in PQA as [EQA _]. cbn [fst snd] in EQA.
assert (HU : 1 <= aptr_used p <= 2^26 + 1) by (unfold aptr_used, used_size; lia).
set (u := aptr_used p) in *. set (n := aptr_req p) in *.

pose proof (REP p ltac:(left; reflexivity)) as REPp.
pose proof (rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & NPd & _). cbn [fst snd] in NK, NC, NPd. unfold iv_disjoint, prim_lo in NPd; cbn [fst snd] in NPd.
idtac. rewrite ?KHI_eq in NK.
pose proof (rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & BPd & _). cbn [fst snd] in BK, BC, BPd. unfold iv_disjoint, prim_lo in BPd; cbn [fst snd] in BPd.
idtac. rewrite ?KHI_eq in BK.
assert (PC0 : exists lo_ hi_, qchunk_mem m lo_ hi_ A n /\ (forall x, lo_ <= x < hi_ -> fp_RQuar a LB0 G RE X x)
/\ (forall x, lo_ <= x < hi_ -> ~ (rl_T X <= x < rl_T X + 4096) /\ ~ (rl_dn X <= x < rl_dn X + 1048576) /\ ~ (rl_ssb X <= x < rl_ssb X + 8388608))).
{ destruct p as [id n0|mb n0]; cbn [qptr_rep] in REPp; subst n; cbn [aptr_req] in *.
- destruct REPp as (i & Ht & Hpr & HQA & QM). rewrite EQA in QM. eexists _, _. split; [exact QM|].
pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht) as (P1 & P2 & _). unfold prim_hi, prim_lo in P1, P2. split.
+ intros x Hx. do 5 right; left. exists (class_of n0), i, (TQuar (APrim id n0)). split; [exact Ht|]. split; [reflexivity|]. split; cbn [fst snd]; lia.
+ intros x Hx. (first [ clear - Hx x P2 P1 BPd NPd i PK TD TK ks n0 id X RE BAND; lia | lia ]).
- destruct REPp as (Hin & Hnl & Hpr & HQA & QM). rewrite EQA in QM. eexists _, _. split; [exact QM|]. split.
+ intros x Hx. do 7 right; left. exists (mkSec mb (sec_map_size n0) n0); cbn [se_beg se_size se_req]. auto.
+ intros x Hx. pose proof (sec_facts _ _ _ _ _ _ GC _ Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & D3). cbn [se_beg se_size] in D3.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (T_obj RE X)) as D. unfold iv_disjoint in D; cbn [fst snd] in D.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (dn_obj RE X)) as Dn. unfold iv_disjoint in Dn; cbn [fst snd] in Dn.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (ssb_obj RE X)) as Db. unfold iv_disjoint in Db; cbn [fst snd] in Db. pose proof KP. (first [ clear - H Db Dn D Hx x BPd BK NPd NK PK TD TK ks n0 mb X RE BAND; lia | lia ]). }
destruct PC0 as (plo & phi & QMp & PZ & PT3).
assert (PT : forall x, plo <= x < phi -> ~ (rl_T X <= x < rl_T X + 4096)) by (intros x Hx; exact (proj1 (PT3 x Hx))).
pose proof (qchunk_geom _ _ _ _ _ QMp) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & q' & g' & r' & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
assert (PDN1 : phi <= rl_dn X \/ rl_dn X + 1048576 <= plo).
{ destruct (Z.le_gt_cases phi (rl_dn X)) as [H1|H1]; [left; exact H1|].
destruct (Z.le_gt_cases (rl_dn X + 1048576) plo) as [H2|H2]; [right; exact H2|].
exfalso. apply (proj1 (proj2 (PT3 (Z.max plo (rl_dn X)) ltac:(lia)))). lia. }
assert (PDN2 : phi <= rl_ssb X \/ rl_ssb X + 8388608 <= plo).
{ destruct (Z.le_gt_cases phi (rl_ssb X)) as [H1|H1]; [left; exact H1|].
destruct (Z.le_gt_cases (rl_ssb X + 8388608) plo) as [H2|H2]; [right; exact H2|].
exfalso. apply (proj2 (proj2 (PT3 (Z.max plo (rl_ssb X)) ltac:(lia)))). lia. }
clear X1 X2 X3 X4 X5 X6 X7 X8 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 q' g' r'.
pose proof (qchunk_geom _ _ _ _ _ QMp) as (G1 & G2 & G3 & G4 & _). rewrite ?KHI_eq in G3. idtac.
destruct QMp as (_ & (b1 & idw & Hb1 & HDRp) & JUNKp & _). unfold qhdr_cells in HDRp.
pose proof (used_size_pos n ltac:(lia)) as [U1 U2]. assert (UN : used_size n = u) by (subst u n; reflexivity). rewrite UN in *.
pose proof (round_up_ge u 8 ltac:(lia)) as RU.
destruct (hjunk_split _ A (A + 8) phi JUNKp ltac:(lia)) as [J8 _]. destruct (hjunk_C8 _ A J8) as [w0 JC].
destruct (unw_obj_open m obj sz [q0; q1; q2; q3; q4] rest bp eq_refl OBJ) as (q30 & rest2 & LQ30 & _ & TRQ30 & _).

unfold unw_obj in OBJ. cbn [map app] in OBJ.
apply (proj1 (rw_cells_app asegs m obj [C8 (wz (obj + 16))] _)) in OBJ as [OB0 OBJ].
apply (proj1 (rw_cells_app asegs m _ [C4 (wz sz); C4 (wz 0)] _)) in OBJ as [OB1 OBJ].
apply (proj1 (rw_cells_app asegs m _ [C8 q0; C8 q1; C8 q2; C8 q3; C8 q4] _)) in OBJ as [OB2 OB3].
cbn [cells_size csize Nat.add] in OB1, OB2, OB3. change (Z.of_nat 8) with 8 in OB1, OB2, OB3. change (Z.of_nat 40) with 40 in OB3.
replace (obj + 8 + 8) with (obj + 16) in OB2, OB3 by lia. replace (obj + 16 + 40) with (obj + 56) in OB3 by lia.
recast OB1 [C8 (wz sz)].
rtc RT 26%nat K26.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned sp - 48 - depot_stack, bv_unsigned sp - 48); (A, A + 8)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
unfold qchunk_entry, depot_stack, SS_BASE, DP_END, QOBJ, TQ, GQ, QMUT, A_INSTANCE in *.
change (967832 + 888) with 968720 in *. change (967832 + 880) with 968712 in *. change (967832 + 728) with 968560 in *.
pose proof HM as HM0. hide HM0. hide JUNKp.
set (Wq := [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned sp - 48 - 224, bv_unsigned sp - 48); (A, A + 8);
(1841608, 6363632); (rl_dn X, rl_dn X + 1048576); (rl_ssb X, rl_ssb X + 8388608)]).
assert (WZ : forall lo' hi' x, In (lo', hi') Wq -> lo' <= x < hi' -> azone a LB0 G RE X (bv_unsigned sp) x).
{ intros lo' hi' x Hin Hx. subst Wq. cbn in Hin. unfold azone.
destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-.
- do 4 right. lia.
- do 4 right. lia.
- left. apply PZ. lia.
- do 3 right; left. left. split; cbn [fst snd]; lia.
- do 3 right; left. right; left. split; cbn [fst snd]; lia.
- do 3 right; left. right; right; left. split; cbn [fst snd]; lia. }
assert (RTW : Forall (rt_avoid RE X) Wq).
{ subst Wq. repeat apply Forall_cons; try apply Forall_nil; intros x Hx FT; cbn [fst snd] in Hx.
- exact (rt_avoid_stack RE X RL (bv_unsigned sp - 48) (bv_unsigned sp) ltac:(lia) x Hx FT).
- exact (rt_avoid_stack RE X RL (bv_unsigned sp - 48 - 224) (bv_unsigned sp - 48) ltac:(lia) x Hx FT).
- exact (fpQ_RTconst a LB0 FS0 G RE X GC x (PZ x ltac:(lia)) FT).
- refine (fpD_excl a LB0 FS0 G RE X GC x _ (or_intror (or_intror (or_intror FT)))). left. split; cbn [fst snd]; lia.
- refine (fpD_excl a LB0 FS0 G RE X GC x _ (or_intror (or_intror (or_intror FT)))). right; left. split; cbn [fst snd]; lia.
- refine (fpD_excl a LB0 FS0 G RE X GC x _ (or_intror (or_intror (or_intror FT)))). right; right; left. split; cbn [fst snd]; lia. }
assert (STW : Forall st_avoid Wq).
{ subst Wq. unfold A_ERRNO in *. repeat apply Forall_cons; try apply Forall_nil.
- st_avoid_solve.
- st_avoid_solve.
- apply st_avoid_offhull; cbn [fst snd]; (first [ clear - RU U1 G3 G2 G1 phi plo BK NK u ks A p X BAND; lia | lia ]).
- apply st_avoid_high; cbn [fst snd]; unfold A_ERRNO; lia.
- st_avoid_solve.
- st_avoid_solve. }
assert (RTW3 : Forall (rt_avoid RE X) (firstn 3 Wq)) by (pose proof RTW as RTW'; subst Wq; inversion RTW' as [|? ? R1 X1]; inversion X1 as [|? ? R2 X2]; inversion X2 as [|? ? R3 X3]; subst;
cbn [firstn]; constructor; [exact R1| constructor; [exact R2| constructor; [exact R3| constructor]]]).
subst Wq. cbn [firstn] in RTW3.
apply aimplT_from_evt.
carve_frame 48%nat ST.
do 7 step.
step.
step.
step. step. if_lit.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW3]) end.
call_sp_ch (get_current_thread_spec RE X) ltac:(fun PO => idtac); try eassumption; try lia.
subst. rename POST into RT2.
step. ifz.
pose proof (RT_T _ _ _ RT2) as KT. unfold rt_T_cells in KT.
step.
step. step.
pose proof (RT_ctx_tid _ _ _ RT2) as KC.
step.
step. step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RD1 : RDepot RE X mc);
[ eapply RDepot_frame; [exact RD| exact WM|]; eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Fx _; apply outside_intro; intros lo' hi' Hin Hy; cbn in Hin;
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-;
[ pose proof (fp_lt_ceil a LB0 FS0 G RE X GC z ltac:(do 5 right; left; exact Fx)); lia
| pose proof (fp_lt_ceil a LB0 FS0 G RE X GC z ltac:(do 5 right; left; exact Fx)); lia
| exact (fpQ_RDepot a LB0 FS0 G RE X GC z (PZ z ltac:(lia)) Fx) ]
| ] end.
change (sx32 (wz 0)) with (wz 0).
hide MU.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (DNHc : depot_n asegs mc dn) by (split; [unfold DP_N; exact DNC| exact DNP]) end.
eapply evt_cut.
{ eapply (depot_put_spec RE X) with (q := q30) (dn := dn); try eassumption; rewrite ?unsigned_lit by lia; try eassumption; try lia.
- unfold depot_stack. lia. }
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MUd & WMd & MId & STd & id & -> & IDB & RD3 & TRQ3 & (dn3 & [DNC3 DNP3] & DNR3)). unfold DP_N in DNC3. clear DNHc.
rewrite !(unsigned_lit (bv_unsigned sp + -48)) in MUd, STd by lia. unfold depot_stack, SS_BASE, DP_END in MUd.
clear KT KC K26.
unhide MU.
set (Wall := [(bv_unsigned sp + -48, bv_unsigned sp); (bv_unsigned sp + -48 - 224, bv_unsigned sp + -48); (QA p, QA p + 8);
(bv_unsigned sp + -48 - 224, bv_unsigned sp + -48); (1841608, 6363632); (rl_dn X, rl_dn X + 1048576); (rl_ssb X, rl_ssb X + 8388608)]).
lazymatch type of MUd with munch _ ?mx _ =>
assert (MUall : munch Wall m m3) by (subst Wall; eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUd]];
intros z Hz; cbn [outside app] in Hz |- *; clear - Hz; tauto);
pose proof (wmono_trans asegs _ _ _ WM WMd) as WMall;
clear MU; transport_after_call asegs mx m3 MUd WMd end.
clear MUd. pose proof (munch_refl [(QA p, QA p + 8)] m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
replace (ret_pc (wz 275436)) with (wz 275436) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

assert (WCASE : forall lo' hi' z, In (lo', hi') Wall -> lo' <= z < hi' ->
(band_lo <= z < bv_unsigned sp) \/ (QA p <= z < QA p + 8) \/ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hx. subst Wall. cbn in Hin.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; injection E as <- <-.
- left. lia. - left. lia. - right; left. lia. - left. lia.
- right; right. left. split; cbn [fst snd]; lia.
- right; right. right; left. split; cbn [fst snd]; lia.
- right; right. right; right; left. split; cbn [fst snd]; lia. }
assert (WZ' : forall lo' hi' z, In (lo', hi') Wall -> lo' <= z < hi' -> azone a LB0 G RE X (bv_unsigned sp) z).
{ intros lo' hi' z Hin Hx. unfold azone. destruct (WCASE lo' hi' z Hin Hx) as [Z|[Z|Z]]; [do 4 right; exact Z| left; apply PZ; lia| clear - Z; tauto]. }
assert (EZ' : forall lo' hi' z, In (lo', hi') Wall -> lo' <= z < hi' -> ezone a LB0 G RE X z).
{ intros lo' hi' z Hin Hx. unfold ezone. destruct (WCASE lo' hi' z Hin Hx) as [Z|[Z|Z]]; [do 5 right; lia| left; apply PZ; lia| do 4 right; left; exact Z]. }
assert (RTW' : Forall (rt_avoid RE X) Wall).
{ subst Wall. inversion RTW as [|? ? R1 X1]; inversion X1 as [|? ? R2 X2]; inversion X2 as [|? ? R3 X3]; inversion X3 as [|? ? R4 X4]; inversion X4 as [|? ? R5 X5]; inversion X5 as [|? ? R6 X6]; subst.
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) in * by lia.
constructor; [exact R1|]. constructor; [exact R2|]. constructor; [exact R3|]. constructor; [exact R2|]. constructor; [exact R4|]. constructor; [exact R5|]. constructor; [exact R6| constructor]. }
assert (STW' : Forall st_avoid Wall).
{ subst Wall. inversion STW as [|? ? R1 X1]; inversion X1 as [|? ? R2 X2]; inversion X2 as [|? ? R3 X3]; inversion X3 as [|? ? R4 X4]; inversion X4 as [|? ? R5 X5]; inversion X5 as [|? ? R6 X6]; subst.
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) in * by lia.
constructor; [exact R1|]. constructor; [exact R2|]. constructor; [exact R3|]. constructor; [exact R2|]. constructor; [exact R4|]. constructor; [exact R5|]. constructor; [exact R6| constructor]. }
clear RTW STW WZ RTW3. subst Wall.

replace (QA p - 16) with (QA p + -16) in HDRp |- * by lia.
do 4 step.
step.
step.
step. step.
change (zx16 (wz 0)) with (wz 0). rewrite (zx32_small u) by lia.
step. step.
step. step.
rewrite (unsigned_lit u) by lia. rewrite Z.lor_0_l.
step. step.
do 6 step.
step. step.
release_frame FR STd (bv_unsigned sp).
apply evt_done.
eapply aimplT_mono.
{ eapply (put_spec C L RE X); [| eassumption| exact STd| exact CEIL'| unfold PUT_STACK, DRAIN_STACK, RECYCLE_STACK; lia| subst n; lia| exact QRM].
split; [exact GC|]. split.
- apply QOTH_split. split; [eapply RTconst_munch; [exact RT| exact MUall| exact WMall| exact RTW']|].
split; [eapply RStats_munch; [exact RS| exact MUall| exact WMall| exact STW']|].
split.
+ eapply RPrim_frame; [exact RP| exact WMall|]. eapply agree_on_of_munch; [exact MUall| exact WMall|]. intros z Fx _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]].
* pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
* exact (fpQ_RPrim a LB0 FS0 G RE X GC z (PZ z ltac:(lia)) Fx).
* exact (fpP_RDepot a LB0 FS0 G RE X GC z Fx Z).
+ apply QREST_split. split.
* eapply QR3_munch; [exact GC| split; [exact RC| split; [exact RSE| exact RF]]| exact MUall| exact WMall| exact WZ'].
* rewrite HRD. eapply RDepot_frame; [exact RD3| exact WM3|]. eapply agree_on_of_munch; [exact MU3| exact WM3|]. intros z Fx _. apply outside_intro. intros lo' hi' Hin Hy.
cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. exact (fpQ_RDepot a LB0 FS0 G RE X GC z (PZ z ltac:(lia)) Fx).
- eapply (RQuarM_pend_agree 0 QB QB p (QA p) a LB0 FS0 G RE X m); [exact GC| exact (proj2 (proj2 QR))| exact WMall|].
eapply agree_on_of_munch; [exact MUall| exact WMall|]. intros z [Fx NH] _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]].
+ exact (fp_RQuar_cz a LB0 FS0 G RE X GC z Fx ltac:(left; lia)).
+ exact (NH Z).
+ exact (fpQ_RDepot a LB0 FS0 G RE X GC z Fx Z). }
cbv beta. intros r1 s'' ms'' PO. unfold qret_post in PO |- *.
destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m5 & G5 & -> & -> & MI5 & ST5 & AP5 & DK5 & QR5).
do 15 eexists. exists m5, G5. split; [reflexivity|]. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [| split; [| exact QR5]].
2:{
destruct DK5 as [DK5 EK5]. split.
- eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [apply DK5; split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]].
- eapply errno_keep_trans; [| exact EK5]. eapply (errno_keep_of_ezone a LB0 FS0 G RE X m _ _ GC MUall WMall). exact EZ'. }
eapply aheap_presA_trans; [| exact AP5].
eapply aheap_presA_of_munch_a; [exact GC| apply Permutation_refl| apply Permutation_refl| lia| exact MUall| exact WMall| exact WZ'].

rewrite (Z.shiftr_div_pow2 sz 8) by lia. rewrite (Z.div_small sz (2^8)) by lia. rewrite !Z.shiftr_0_l. reflexivity.
Qed.
End S.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QbcP_c1 Q61C QWRO Qu4g QFQR QKBN QN4c QV3O QjgW QpF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QTVW.Mqa QOJv.Mqb QNQk Q9Ho.Mq4 QV3O QnRU.Mql QmP7.Mq1 QpY2.Mqb QYyZ.Mq8 Qu3b QYyZ.Mqc QjgW QYyZ.Mqa QpME.Mq8 QpF1 QQ8H.Mq5 QsDw.Mq1 QcYs.Mq7 QmvA.Mq5 QpME.Mqc.
Import QVo2.Mq4.
Import QpY2.Mqc.
Import QRfV.Mq3 QnRU.Mqk QEYd.Mq0.
Import QcfN.Mq4.
Import QlES.
Import QVo2.Mq2.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Let atn := at_nodeA L asegs.
Hypothesis large_alloc_spec : large_alloc_stmt RE X L.
Hypothesis poison_zero_spec : poison_zero_stmt_lh RE X L.

Definition calloc_W_sec (bp : Z) : list (Z * Z) :=
(bp - CALLOC_STACK, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W_sec RE X (bp - 2192)).

Definition calloc_post_sec (ra : word) (bp : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (LB : list ablock) (n lo : Z) (m : word -> option byte)
(r : option aptr * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
ms' = MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo bp
/\ RTconst RE X m' /\ RStats RE X m' /\ RDepot RE X m' /\ depot_step m m'
/\ match r with
| (None, a1) => a0 = wz 0 /\ a1 = a /\ munch (calloc_W_sec bp) m m' /\ RSec a LB RE X m'
| (Some p, a1) => exists mb, let msz := sec_map_size n in
p = ASec mb n
/\ as_reg a1 = as_reg a ++ [mkSec mb msz n]
/\ as_tq a1 = as_tq a /\ as_gq a1 = as_gq a /\ (forall c, cls a1 c = cls a c)
/\ as_cache_inited a1 = as_cache_inited a /\ as_next a1 = as_next a
/\ (as_nres a1 = as_nres a \/ as_nres a1 = as_nres a + kPtrArrBlock)
/\ as_spent a1 = as_spent a + sec_cost msz
/\ mb mod kPage = 0 /\ appr mb msz /\ mb + msz <= band_lo /\ zavoids mb msz (avoid_of (ae_L RE) a) = true
/\ a0 = wz (mb + kSecUserOff)
/\ munch (calloc_W_sec bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m m'
/\ RSec a1 LB RE X m'
/\ chunk_mem m' (mb + kPage) (mb + msz) (mb + kSecUserOff) n
/\ rw_cells asegs m' (mb + kSecUserOff) [CB (Z.to_nat n) (repeat (b8 0) (Z.to_nat n))]
end.

Lemma calloc_icpt_sec_spec : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PStateA) (a : AState) (G : ghost) (LB : list ablock) (FS : list fframe) (lo cnt sz dn : Z),
gcons a LB FS G RE X ->
RTconst RE X m -> RStats RE X m -> RSec a LB RE X m -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - CALLOC_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> cnt * sz <= 2^26 -> from_primary (cnt * sz) = false ->
aimplT atn (asan_malloc (ae_L RE) a (cnt * sz)) s
(calloc_post_sec ra bp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB (cnt * sz) lo m)
(MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz cnt) (wz sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x636a4) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros GC RT RS RSE RD MI ST CEIL LO BPR UNW DNH DCAP Hcnt Hsz Hmax HP.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof CEIL as CEIL'. idtac. unfold CALLOC_STACK, ALLOC_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & PC & _ & QK & QC & _). unfold prim_hi in PC. unfold ptrarr_hi in QC. idtac. rewrite ?KHI_eq in PK.
change (al_space_beg (ae_L RE)) with (prim_lo RE) in PC. change (al_ptrarr (ae_L RE)) with (ptrarr_lo RE) in QC.
apply appr_to_lia in QK; [| lia| lia].
set (n := cnt * sz) in *. assert (Hn : 0 <= n <= 2^26) by (subst n; nia).
pose proof (munch_refl (calloc_W_sec bp) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold calloc_W_sec, CALLOC_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE in MU. cbn [tl app] in MU.
assert (SEF : forall mm mm' W, munch W mm mm' -> wmono asegs mm mm' ->
(forall lo' hi' z, In (lo', hi') W -> lo' <= z < hi' -> fp_RStats RE X z \/ fp_RDepot RE X z \/ band_lo <= z) ->
RSec a LB RE X mm -> RSec a LB RE X mm').
{ intros mm mm' W MUw WMw HW RSEw. eapply RSec_frame; [exact RSEw| exact WMw|]. eapply agree_on_of_munch; [exact MUw| exact WMw|]. intros z Fz _. apply outside_intro.
intros lo' hi' Hin Hz. destruct (HW lo' hi' z Hin Hz) as [P|[P|P]].
- exact (fpS_excl _ _ _ _ _ _ GC z P ltac:(right; left; exact Fz)).
- exact (fpD_excl _ _ _ _ _ _ GC z P ltac:(right; left; exact Fz)).
- pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)). lia. }
apply aimplT_from_evt.
eapply calloc_icpt_pre; [exact RT| exact RL| exact (RDepot_unw RE X _ RD)| exact MI| exact ST| exact CEIL'| unfold CALLOC_STACK, ALLOC_STACK; lia| exact BPR| exact UNW| lia| lia|].
intros m1 u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u13 tsz q rest junk8 junk8b MU1 WM1 MI1 ST1 J8 OBJ LQ SZR FR RT1 TU1.
unfold cicpt_W in MU1.
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU1| exact WM1|]. constructor; [first [st_avoid_solve| eapply st_avoid_T; [eassumption| lia| lia]]|]. constructor; [st_avoid_solve| constructor]. }
assert (RSE1 : RSec a LB RE X m1).
{ eapply SEF; [exact MU1| exact WM1| | exact RSE]. intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
- do 2 right. idtac. lia.
- right; left. do 3 right. lia. }
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame_unw; [exact RL| exact RD| exact WM1| | exact TU1]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z [Fz NZ] _. cbn [outside].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). idtac. lia. }
phase_done MU m m1 MU1 WM1. clear RT RS RSE RD MI. try clear ST.
destruct (unw_obj_head _ _ _ _ _ _ OBJ LQ ltac:(lia)) as [OBJh (q30 & TRQ & LQ30)].

unfold asan_calloc_entry. carve_frame 48%nat ST1.
match goal with H : rw_cells asegs _ (bp + -2144 + -48) _ |- _ => replace (bp + -2144 + -48) with (bp + -2192) in H by lia end.
replace (bp + -2144 + -48) with (bp + -2192) in ST1 by lia.
pose proof (munch_refl [(bp - 2192, bp - 2144)] m1) as MUa. pose proof (wmono_refl asegs m1) as WMa.
step. stf. step. step. step. stf.
step.

lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists r' : word, ms1 = MS (@bvmap_set 5 word 12 r' R) FF (wz 0x3fc44) fcc rv mm ro)) end.
{ step. destruct (Z.eq_dec sz 0) as [Z0|NZ].
- ifz. apply evt_done. eexists. simp_regs. reflexivity.
- ifz. step.
rewrite !(unsigned_lit sz), !(unsigned_lit cnt) by lia. rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.div_small (sz * cnt) (2^64)) by nia.
step. if_lit. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms1 [r' ->]. simp_regs.
step.
rewrite !(unsigned_lit sz), !(unsigned_lit cnt) by lia. replace (sz * cnt) with n by lia.
step. stp. step. stp. stp.
step. step. step. stp.
step.
lazymatch type of MUa with munch _ _ ?mm =>
destruct (sz_frame RE X a LB FS G m1 mm _ GC MUa WMa ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; right; idtac; lia)) as (FT & _ & FD);
pose proof (FT RT1) as RT2; pose proof (FD RD1) as RD2;
assert (RSE2 : RSec a LB RE X mm) by (eapply SEF; [exact MUa| exact WMa| intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; do 2 right; idtac; lia| exact RSE1]);
assert (RS2 : RStats RE X mm) by (eapply RStats_munch; [exact RS1| exact MUa| exact WMa| constructor; [st_avoid_solve| constructor]]) end.
clear FT FD RT1 RSE1 RD1 RS1 MUa WMa.
apply evt_done. change (wz 977752) with (wz A_INSTANCE).
eapply aimplT_then.
{ eapply (allocate_sec_spec L RE X large_alloc_spec poison_zero_spec _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s a G LB FS n 0 lo (bp + -2136) tsz dn q30 GC RT2 RS2 RSE2 RD2);
[assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| exact Hn| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post_sec in PO. rewrite !(unsigned_lit (bp + -2192)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 261232)) with (wz 261232) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_INSTANCE in REST.
clear OBJh TRQ RT2 RSE2 RD2 RS2.

assert (FRALL : forall mx, rw_cells asegs mx (bp + -2144) [CB 8 junk8b] -> rw_cells asegs mx (bp + -2136) (unw_obj (bp + -2136) tsz q rest bp) ->
rw_cells asegs mx (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mx (bp + -2144) ([CB 8 junk8b] ++ unw_obj (bp + -2136) tsz q rest bp ++ [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ intros mx O0 O1 O2. apply (proj2 (rw_cells_app asegs mx _ [CB 8 junk8b] _)). split; [exact O0|]. cbn [cells_size csize Nat.add].
replace (bp + -2144 + Z.of_nat 8) with (bp + -2136) by lia.
apply (proj2 (rw_cells_app asegs mx _ _ _)). split; [exact O1|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia).
unfold unw_obj. cbn [cells_size csize Nat.add map app length]. replace (bp + -2136 + Z.of_nat 2064) with (bp + -72) by lia. exact O2. }
destruct r as [p|].
-
destruct REST as (mb & -> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & -> & MUk & RSEk & CM & UZ).
specialize (UZ eq_refl).
pose proof MBK as MBK'. apply appr_to_lia in MBK'; [| pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG0 _]; lia| lia]. pose proof MBC as MBC'. idtac.
set (msz := sec_map_size n) in *.
destruct (zavoid_facts RE X a mb msz (rlay_avoid RE X RL) ltac:(pose proof (sec_geom_facts n Hn HP); lia) ZA) as (_ & AVP & _ & _).
assert (MS8 : 8 * (msz / 8) = msz /\ 8192 <= msz) by (pose proof (sec_geom_facts n Hn HP) as (G1 & _ & _ & _ & G5 & G6 & G7 & G8 & _); fold msz in G7, G8; clear - G1 G5 G6 G7 G8; Z.div_mod_to_equations; lia).
assert (SHM : SH (mb + msz) = SH mb + msz / 8) by (rewrite <- SH_plus8; f_equal; lia).
assert (MBH : 0x647000 <= mb) by (pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG _]; fold msz in SMG; pose proof (sec_req_facts n ltac:(lia) HP) as [_ RQn]; clear - MBK' SMG RQn; lia).
assert (SHB : 0x80000000 <= SH mb /\ SH mb + msz / 8 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; clear - MBH MBC' MS8; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD.
rewrite SHM in MUk. remember (msz / 8) as q8 eqn:EQ8. clear EQ8.
apply (munch_weaken _ (((bp - (2192 + 1152), bp) :: (rl_T X + 3168, rl_T X + 3169) :: (6444156, 6444156 + 4) :: (1524768, 1524769) :: (rl_T X + 2800, rl_T X + 3168)
:: (977752 + 104, 977752 + 728) :: (ptrarr_lo RE, ptrarr_lo RE + 8388608) :: (1851528, 6373552) :: (rl_dn X, rl_dn X + 1048576) :: (rl_ssb X, rl_ssb X + 8388608) :: nil)
++ [(mb, mb + msz); (SH mb, SH mb + q8)])) in MU.
2:{ intros z Hz. cbn [outside app] in Hz |- *. clear - Hz. tauto. }
cbn [app] in MU. cbn [app] in MUk. lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
rewrite KU. hide AVP.
step. ifz.
rtc RT3 24%nat K24. change (al_space_beg (ae_L RE)) with (prim_lo RE) in K24.
unfold A_INSTANCE. step.
clear K24.

assert (EPI : forall (a1v s3v : word),
evt asegs (calloc_post_sec ra bp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB n lo m (Some (ASec mb n), a') s)
(MS (mkR (wz 261232) (wz (bp + -2192)) gp (wz A_TP) y0 y1 y2 (wz n) (wz (bp + -2136)) (wz (mb + 6144)) a1v z2 z3 z4 z5 z6 z7
(wz 977752) s3v (wz 1) (wz (bp + -2136)) (wz (bp + -89)) s7 s8 s9 s10 s11 y3 y4 y5 y6)
F (wz 0x3fcc4) fc None m3 (seg_rom asegs))).
{ intros a1v s3v.
step. step. step. step. step. step.
release_frame FR0 ST3 (bp + -2144).
step.
replace (ret_pc (wz 408556)) with (wz 408556) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 8 step. step.
pose proof (FRALL _ J8 OBJ FR) as FRX. clear OBJ OBJ3 FR J8.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST3 bp.
step.
apply evt_done. unfold calloc_post_sec. do 15 eexists. exists m3.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST3|].
split; [exact RT3|]. split; [exact RS3|]. split; [exact RD3|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. exists mb. cbv zeta. fold msz.
split; [reflexivity|]. split; [exact REG|]. split; [exact TQ|]. split; [exact GQ|]. split; [exact CLS|]. split; [exact CI|]. split; [exact NX|].
split; [exact NR|]. split; [exact SPN|]. split; [exact MBP|]. split; [exact MBK|]. split; [exact MBC|]. split; [exact ZA|].
split; [rewrite KU; reflexivity|]. split; [| split; [exact RSEk| split; [exact CM| rewrite KU; exact UZ]]].
rewrite SHM. unfold calloc_W_sec, CALLOC_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU. }
unhide AVP. destruct AVP as [LOW|HIGH].
+ step. ifz.
apply EPI.
+ step. ifz.
stp. step.
step. ifz.
apply EPI.
-
destruct REST as (-> & -> & MUk & RSEk).
lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
step. if_lit.
pose proof (munch_refl [(bp - 2208, bp - 2192); (A_ERRNO, A_ERRNO + 4)] m3) as MUe. pose proof (wmono_refl asegs m3) as WMe. unfold A_ERRNO in MUe.
step. call_ch (set_errno_spec RE X) ltac:(fun PO => unfold A_ERRNO in PO; rewrite !(unsigned_lit (bp + -2192)) in PO by lia);
[exact RS3| assumption| rewrite unsigned_lit by lia; exact ST3| exact CEIL'| rewrite unsigned_lit by lia; lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST4 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS4 end.
lazymatch type of MUe with munch _ _ ?mm =>
destruct (sz_frame RE X a LB FS G m3 mm _ GC MUe WMe
ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia])) as (FT & _ & FD);
assert (RSE4 : RSec a LB RE X mm) by (eapply SEF; [exact MUe| exact WMe| intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[do 2 right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia]| exact RSEk]) end.
pose proof (FT RT3) as RT4. pose proof (FD RD3) as RD4. clear FT FD MUe WMe RT3 RSEk RD3 RS3.
stp.
step. step. step. step. step. step.
release_frame FR0 ST4 (bp + -2144).
step.
replace (ret_pc (wz 408556)) with (wz 408556) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 8 step. step.
pose proof (FRALL _ J8 OBJ FR) as FRX. clear OBJ OBJ3 FR J8.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST4 bp.
step.
apply evt_done. unfold calloc_post_sec. do 15 eexists. lazymatch type of ST4 with stk _ ?mm _ _ => exists mm end.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST4|].
split; [exact RT4|]. split; [exact RS4|]. split; [exact RD4|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [| exact RSE4].
unfold calloc_W_sec, CALLOC_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU.
Qed.
End S.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk QV3O QmP7.Mq1 QpY2.Mqb Q9Ho.Mq3 QYyZ.Mq8 QnRU.Mqc QOJv.Mqc Qu3b QnaW.Mq3 QYyZ.Mqc QYyZ.Mqa QEEn QQ8H.Mq5.
Import QteI.Mqa.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Lemma RChunks_cons {BAND : Band} : forall a LB G RE X m p A n,
RChunks a LB G RE X m -> chunk_rep a G RE m p A n ->
(forall p' A' n' z, In (p', A', n') LB -> (p, A, n) <> (p', A', n') ->
in_iv (fst (chunk_cont p A n), snd (chunk_cont p A n) - fst (chunk_cont p A n)) z ->
in_iv (fst (chunk_cont p' A' n'), snd (chunk_cont p' A' n') - fst (chunk_cont p' A' n')) z -> False) ->
RChunks a ((p, A, n) :: LB) G RE X m.
Proof.
intros a LB G RE X m p A n [H1 H2] CR DJ. split.
- intros q B k [E|Hin]; [inversion E; subst; exact CR| exact (H1 _ _ _ Hin)].
- intros q B k q' B' k' z [E|Hin] [E'|Hin'] NE Z1 Z2.
+ inversion E; inversion E'; subst. exact (NE eq_refl).
+ inversion E; subst. exact (DJ _ _ _ z Hin' NE Z1 Z2).
+ inversion E'; subst. exact (DJ _ _ _ z Hin ltac:(intros EE; exact (NE (eq_sym EE))) Z2 Z1).
+ exact (H2 _ _ _ _ _ _ z Hin Hin' NE Z1 Z2).
Qed.

Section Z.
Context {BAND : Band}.
Variables (a a1 : AState) (LB : list ablock) (FS : list fframe) (G G1 : ghost) (RE : aentry) (X : rlay) (c i : Z).
Hypothesis GC : gcons a LB FS G RE X.
Hypothesis GS : gstep RE X a a1 G G1.
Hypothesis TI : tag_at G1 c i = Some TCached.
Let GC1 : gcons a1 LB FS G1 RE X := proj2 (proj2 (proj2 GS)) LB FS GC.

Lemma slot_fpP : forall x,
in_iv (slot_beg RE c i, class_size c) x \/ in_sh (slot_beg RE c i, class_size c) x -> fp_RPrim G RE X x.
Proof.
intros x Hx. pose proof GS as (SQ & SL & OLD & _). pose proof kconsts as (_ & KO & _ & K32 & _).
pose proof (tag_slot _ _ _ _ _ _ GC1 c i TCached TI) as (C1 & I1 & N1 & R1 & R2 & B1 & B2 & S1 & S2 & AL). rewrite KO in B2.
assert (NP : forall c' i' t', tag_at G c' i' = Some t' -> negb (tag_prim t') = true ->
(in_iv (slot_beg RE c' i', class_size c') x -> in_iv (slot_beg RE c i, class_size c) x -> False)
/\ (in_sh (slot_beg RE c' i', class_size c') x -> in_sh (slot_beg RE c i, class_size c) x -> False)).
{ intros c' i' t' Ht' NPt.
assert (Ht1 : tag_at G1 c' i' = Some t').
{ destruct t' as [| |q|q|]; cbn in NPt; try discriminate;
[apply (proj1 (SL c' i' (TLive q) eq_refl)); exact Ht'| apply (proj1 (SQ c' i' (TQuar q) eq_refl)); exact Ht'| apply (proj1 (SQ c' i' TQOwn eq_refl)); exact Ht']. }
assert (NEQ : c' <> c \/ i' <> i).
{ destruct (Z.eq_dec c' c) as [->|NC]; [| left; exact NC]. destruct (Z.eq_dec i' i) as [->|NI]; [| right; exact NI].
rewrite TI in Ht1. inversion Ht1. subst t'. cbn in NPt. discriminate. }
pose proof (tag_slot _ _ _ _ _ _ GC1 c' i' t' Ht1) as (C1' & I1' & _ & R1' & R2' & _ & _ & S1' & S2' & AL').
pose proof (slots_disjoint _ _ _ _ _ _ GC1 c' i' t' c i TCached Ht1 TI NEQ) as D.
split.
- intros [X1 X2] [Y1 Y2]; cbn [fst snd] in X1, X2, Y1, Y2. lia.
- intros SX SY. eapply (in_sh_disjoint (slot_beg RE c' i') (class_size c') (slot_beg RE c i) (class_size c) x);
[clear - AL'; Z.div_mod_to_equations; lia| clear - AL; Z.div_mod_to_equations; lia| lia| lia| exact D| exact SX| exact SY]. }
destruct Hx as [Hx|Hx].
- do 4 right. left. split.
+ exists c. rewrite K32, KO. split; [lia|]. destruct Hx as [X1 X2]; cbn [fst snd] in X1, X2. lia.
+ intros (c' & i' & t' & Ht' & NPt & IN). exact (proj1 (NP c' i' t' Ht' NPt) IN Hx).
- do 5 right. split.
+ exists c. rewrite K32, KO. split; [lia|]. pose proof (reg_beg_align RE X c (gc_rlay _ _ _ _ _ _ GC)) as (A8 & _).
apply (in_sh_sub (reg_beg (ae_L RE) c) 3758096384 (slot_beg RE c i) (class_size c) x A8 ltac:(clear - AL; Z.div_mod_to_equations; lia) R1 ltac:(lia) Hx).
+ intros (c' & i' & t' & Ht' & NPt & IN). exact (proj2 (NP c' i' t' Ht' NPt) IN Hx).
Qed.
End Z.

Section Lift.
Context {BAND : Band}.
Variable C : arun_components.
Variable LV : lvp.
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRD : ac_RDepot C = RDepot.

Definition mz (G : ghost) (RE : aentry) (X : rlay) (SP x : Z) : Prop :=
fp_RPrim G RE X x \/ fp_RStats RE X x \/ fp_RDepot RE X x \/ band_lo <= x < SP.

Lemma malloc_W_mz0 : forall a LB FS G RE X c bp lo hi x,
gcons a LB FS G RE X -> 1 <= c <= 31 -> band_lo <= bp - MALLOC_STACK ->
In (lo, hi) (malloc_W RE X bp c (c_alloc_user (cls a c))) -> lo <= x < hi -> mz G RE X bp x.
Proof.
intros a LB FS G RE X c bp lo hi x GC Hc CSP Hin Hx. pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
pose proof (QKBN.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB.
pose proof (gc_bounds _ _ _ _ _ _ GC c ltac:(rewrite K32; lia)) as (AU1 & AU2 & _). rewrite KO in AU2.
assert (SHF : SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo) by (rewrite FB; unfold SH, A_SHADOW_OFS; clear - PAL PK PCH PH Hc; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD0.
assert (SHR : SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo) by (rewrite RB; unfold SH, A_SHADOW_OFS; clear - PAL PK PCH PH Hc; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD1.
idtac. rewrite ?KHI_eq in TK.
unfold malloc_W, alloc_W, MALLOC_STACK, ALLOC_STACK in Hin, CSP. cbn [tl app] in Hin.
assert (CB : forall lo' hi', In (lo', hi') (comb_W RE X (bp - 2144) c (c_alloc_user (cls a c))) -> hi' <= band_lo -> lo' <= x < hi' -> mz G RE X bp x).
{ intros lo' hi' Hin' B Hx'. destruct (comb_W_pz RE X a LB FS G (bp - 2144) c x lo' hi' GC Hc ltac:(idtac; unfold COMB_STACK; lia) Hin' Hx') as [P|[P|P]];
[left; exact P| right; left; exact P| idtac; lia]. }
unfold comb_W, COMB_STACK in CB.
destruct Hin as [E|[E|[E|[E|Hin]]]].
- injection E as <- <-. do 3 right. idtac. lia.
- injection E as <- <-. do 2 right; left. do 3 right. lia.
- injection E as <- <-. right; left. right; left. split; cbn [fst snd]; lia.
- injection E as <- <-. right; left. do 2 right. lia.
- cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; first
[ injection E as <- <-; right; left; do 2 right; lia
| injection E as <- <-; do 2 right; left; left; unfold SS_BASE, DP_END in *; split; cbn [fst snd]; lia
| injection E as <- <-; do 2 right; left; right; left; split; cbn [fst snd]; lia
| injection E as <- <-; do 2 right; left; do 2 right; left; split; cbn [fst snd]; lia
| injection E as <- <-; refine (CB _ _ _ _ Hx); [cbn [In]; tauto| first [lia | unfold ri_addr; lia | rewrite KS; lia | rewrite KS; change (536870912 / 8) with 67108864; lia | rewrite KO; lia | rewrite KO; change (3758096384 / 8) with 469762048; lia]] ].
Qed.

Lemma malloc_W_mz : forall a a1 LB FS G G1 RE X c i bp lo hi x,
gcons a LB FS G RE X -> gstep RE X a a1 G G1 -> tag_at G1 c i = Some TCached -> 1 <= c <= 31 ->
band_lo <= bp - MALLOC_STACK ->
In (lo, hi) (malloc_W RE X bp c (c_alloc_user (cls a c)) ++ slot_W RE c i) -> lo <= x < hi -> mz G RE X bp x.
Proof.
intros a a1 LB FS G G1 RE X c i bp lo hi x GC GS TI Hc CSP Hin Hx.
apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (malloc_W_mz0 a LB FS G RE X c bp lo hi x GC Hc CSP Hin Hx)|].
unfold slot_W in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; left;
apply (slot_fpP a a1 LB FS G G1 RE X c i GC GS TI); [left| right]; split; cbn [fst snd]; lia.
Qed.

Lemma mz_azone : forall a LB0 G RE X SP x, mz G RE X SP x -> azone a LB0 G RE X SP x.
Proof. intros a LB0 G RE X SP x [H|[H|[H|H]]]; unfold azone; tauto. Qed.

Lemma lift_some : forall s LB FS RE X G LB0 FS0 aa1 G1 c i n m m' SP W,
Permutation LB LB0 -> Permutation FS FS0 ->
gcons (ps_a s) LB0 FS0 G RE X -> RChunks (ps_a s) LB0 G RE X m -> ac_RSec C (ps_a s) LB0 RE X m ->
ac_RQuar C (ps_a s) LB0 G RE X m -> ac_RFake C FS0 RE X m ->
c = class_of n -> 0 <= n <= 2^26 -> from_primary n = true -> band_lo <= SP ->
qframe (ps_a s) aa1 -> gstep RE X (ps_a s) aa1 G G1 -> tag_at G1 c i = Some TCached -> 0 <= i ->
munch W m m' -> wmono asegs m m' -> (forall lo hi x, In (lo, hi) W -> lo <= x < hi -> mz G RE X SP x) ->
RTconst RE X m' -> RStats RE X m' -> RDepot RE X m' ->
(forall t, tag_prim t = false -> RPrim aa1 (set_tag c i t G1) RE X m') ->
chunk_mem m' (slot_beg RE c i) (slot_beg RE c i + class_size c) (slot_beg RE c i + rz_size n) n ->
aheap_presA asegs a_alayout LB FS SP m m'
/\ ablock_rangeA (slot_beg RE c i + rz_size n) n
/\ ARUN C (set_a (set_next (N.succ (as_next aa1)) aa1) s) ((APrim (as_next aa1) n, slot_beg RE c i + rz_size n, n) :: LB) FS RE m'
/\ blk_shadow asegs m' (slot_beg RE c i + rz_size n) n.
Proof.
intros s LB FS RE X G LB0 FS0 aa1 G1 c i n m m' SP W PB PF GC R4 R5 R6 R8 Ec Hn HP CSP QF GS TI I0 MU WM ZN RT' RS' RD' RPF CM.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof (class_of_facts n ltac:(lia) HP) as (Hc & Csz & _). cbv zeta in Hc, Csz. rewrite <- Ec in Hc, Csz.
pose proof (needed_facts n ltac:(lia)) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
pose proof GS as (SQ & SL & OLD & GCT). pose proof (GCT LB0 FS0 GC) as GC1.
destruct QF as (QF1 & QF2 & QF3 & QF4 & QF5 & QF6).
assert (QR : QR3 C (ps_a s) LB0 FS0 G RE X m) by (split; [exact R4| split; [exact R5| exact R8]]).
assert (ZA : forall lo' hi' x, In (lo', hi') W -> lo' <= x < hi' -> azone (ps_a s) LB0 G RE X SP x) by (intros lo' hi' x Hin Hx; apply mz_azone; exact (ZN lo' hi' x Hin Hx)).
split; [eapply aheap_presA_of_munch_a; [exact GC| exact PB| exact PF| exact CSP| exact MU| exact WM| exact ZA]|].
set (A := slot_beg RE c i + rz_size n) in *. set (p := APrim (as_next aa1) n) in *. set (G' := set_tag c i (TLive p) G1) in *.
pose proof (tag_slot _ _ _ _ _ _ GC1 c i TCached TI) as (C1 & _ & _ & SL1 & SL2 & SB1 & SB2 & CS1 & CS2 & AL). rewrite KO in SB2.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (N1 : n <= class_size c - rz_size n) by (unfold needed in Csz; pose proof (round_up_8 (Z.max n 8) ltac:(lia)); lia).

pose proof (gcons_alloc_prim aa1 LB0 FS0 G1 RE X c i n GC1 TI Ec Hn HP) as GC2. fold p in GC2. fold A in GC2. fold G' in GC2.
assert (QR' : QR3 C aa1 LB0 FS0 G1 RE X m').
{ eapply QR3_ext; [eapply (QR3_munch C); [exact GC| exact QR| exact MU| exact WM| exact ZA]| exact QF3| exact QF4| exact QF5| exact SL]. }
destruct QR' as (RC' & RSe' & RF').
assert (RC2 : RChunks (set_next (N.succ (as_next aa1)) aa1) ((p, A, n) :: LB0) G' RE X m').
{ apply RChunks_cons.
- eapply RChunks_sub; [exact RC'| intros b Hb; exact Hb| intros e He; exact He|].
intros q B k c' i' Hin Ht. subst G'. rewrite tag_at_set_tag_ne; [exact Ht| lia|].
destruct (Z.eq_dec c' c) as [->|NC]; [right| left; exact NC]. intros ->. rewrite TI in Ht. discriminate.
- cbn [chunk_rep]. split; [reflexivity|]. exists i. rewrite <- Ec. split; [subst G'; apply (tag_at_set_tag_eq _ _ _ _ _ TI)|]. split; [reflexivity| exact CM].
- intros q B k z Hin NE Z1 Z2. subst p. cbn [chunk_cont fst snd] in Z1.
replace (A - rz_size n) with (slot_beg RE c i) in Z1 by (subst A; lia).
replace (slot_beg RE c i + class_size (class_of n) - slot_beg RE c i) with (class_size c) in Z1 by (rewrite <- Ec; lia).
pose proof (RChunks_open _ _ _ _ _ _ _ _ _ RC' Hin) as CRq.
destruct q as [idq nq|mb nq]; cbn [chunk_rep chunk_cont fst snd] in CRq, Z2.
+ destruct CRq as (-> & i' & Hti' & HB & _).
replace (B - rz_size k + class_size (class_of k) - (B - rz_size k)) with (class_size (class_of k)) in Z2 by lia.
rewrite HB in Z2. replace (slot_beg RE (class_of k) i' + rz_size k - rz_size k) with (slot_beg RE (class_of k) i') in Z2 by lia.
assert (NEQ : class_of k <> c \/ i' <> i).
{ destruct (Z.eq_dec (class_of k) c) as [EC|NC]; [| left; exact NC]. destruct (Z.eq_dec i' i) as [->|NI]; [| right; exact NI].
rewrite EC, TI in Hti'. discriminate. }
pose proof (slots_disjoint _ _ _ _ _ _ GC1 _ _ _ c i TCached Hti' TI NEQ) as D.
destruct Z1 as [X1 X2], Z2 as [Y1 Y2]; cbn [fst snd] in X1, X2, Y1, Y2. lia.
+ destruct CRq as (-> & Hr & HB & _).
pose proof (sec_entry_facts (ps_a s) LB0 FS0 G RE X GC _ ltac:(rewrite <- QF3; exact Hr)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & _). cbn [se_beg se_size se_req] in *.
unfold iv_disjoint, prim_lo in E7. cbn [fst snd] in E7. rewrite KP in Z2.
destruct Z1 as [X1 X2], Z2 as [Y1 Y2]; cbn [fst snd] in X1, X2, Y1, Y2. unfold prim_lo in *. lia. }
split. { unfold ablock_rangeA. rewrite ?KHI_eq. unfold prim_lo, prim_hi in *. subst A. repeat split; first [lia| clear - AL RZ2; Z.div_mod_to_equations; lia]. }
split.
{ eapply (ARUN_close C _ _ _ _ _ X G' ((p, A, n) :: LB0) FS0); [apply perm_skip; exact PB| exact PF|]. cbn [ps_a set_a].
split; [exact GC2|]. rewrite HRT, HRS, HRP, HRC, HRD.
split; [exact RT'|]. split; [exact RS'|].
split. { eapply RPrim_ext; [exact (RPF (TLive p) eq_refl)| intros; reflexivity| reflexivity| apply same_len_refl| apply same_tags_refl]. }
split; [exact RC2|].
split. { eapply (ac_RSec_ext C); [exact RSe'| reflexivity| reflexivity| reflexivity]. }
split.
{ eapply (ac_RQuar_ext C).
- eapply (ac_RQuar_frame C); [exact R6| exact WM|]. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx _. apply outside_intro.
intros lo' hi' Hin Hx. pose proof (ZN lo' hi' x Hin Hx) as [P|[P|[P|P]]].
+ exact (fpQ_RPrim _ _ _ _ _ _ GC x Fx P).
+ exact (fpQ_RStats _ _ _ _ _ _ GC x Fx P).
+ exact (fpQ_RDepot _ _ _ _ _ _ GC x Fx P).
+ exfalso. apply (fp_RQuar_cz _ _ FS0 _ _ _ GC x Fx). left. lia.
- cbn. exact QF1.
- cbn. exact QF2.
- cbn. exact QF3.
- intros e He. unfold sec_live. cbn [In]. split; [intros (B & HB); exists B; right; exact HB| intros (B & [HB|HB]); [exfalso; subst p; discriminate| exists B; exact HB]].
- intros c' i' t Ht. split; intros H.
+ subst G'. rewrite tag_at_set_tag_ne; [apply (proj1 (SQ c' i' t Ht)); exact H| lia|].
destruct (Z.eq_dec c' c) as [->|NC]; [right| left; exact NC]. intros ->. apply (proj1 (SQ c i t Ht)) in H. rewrite TI in H. inversion H. subst t. discriminate.
+ subst G'. destruct (Z.eq_dec c' c) as [EC|NC]; [destruct (Z.eq_dec i' i) as [EI|NI]|].
* subst c' i'. rewrite (tag_at_set_tag_eq _ _ _ _ _ TI) in H. inversion H. subst t. discriminate.
* rewrite tag_at_set_tag_ne in H by (first [lia| right; lia]). apply (proj2 (SQ c' i' t Ht)). exact H.
* rewrite tag_at_set_tag_ne in H by (first [lia| left; lia]). apply (proj2 (SQ c' i' t Ht)). exact H. }
split; [exact RD'| exact RF']. }
exact (RChunks_shadow _ _ FS0 _ _ X _ p A n GC2 RC2 ltac:(left; reflexivity)).
Qed.

Lemma lift_none : forall s LB FS RE X G LB0 FS0 aa G1 c n m m' SP W,
Permutation LB LB0 -> Permutation FS FS0 ->
gcons (ps_a s) LB0 FS0 G RE X -> RChunks (ps_a s) LB0 G RE X m -> ac_RSec C (ps_a s) LB0 RE X m ->
ac_RQuar C (ps_a s) LB0 G RE X m -> ac_RFake C FS0 RE X m ->
c = class_of n -> band_lo <= SP ->
qframe (ps_a s) aa -> gstep RE X (ps_a s) aa G G1 ->
munch W m m' -> wmono asegs m m' -> (forall lo hi x, In (lo, hi) W -> lo <= x < hi -> mz G RE X SP x) ->
RTconst RE X m' -> RStats RE X m' -> RDepot RE X m' -> RPrim aa G1 RE X m' ->
aheap_presA asegs a_alayout LB FS SP m m' /\ ARUN C (set_a aa s) LB FS RE m'.
Proof.
intros s LB FS RE X G LB0 FS0 aa G1 c n m m' SP W PB PF GC R4 R5 R6 R8 Ec CSP QF GS MU WM ZN RT' RS' RD' RP'.
pose proof GS as (SQ & SL & OLD & GCT). pose proof (GCT LB0 FS0 GC) as GC1.
destruct QF as (QF1 & QF2 & QF3 & QF4 & QF5 & QF6).
assert (QR : QR3 C (ps_a s) LB0 FS0 G RE X m) by (split; [exact R4| split; [exact R5| exact R8]]).
assert (ZA : forall lo' hi' x, In (lo', hi') W -> lo' <= x < hi' -> azone (ps_a s) LB0 G RE X SP x) by (intros lo' hi' x Hin Hx; apply mz_azone; exact (ZN lo' hi' x Hin Hx)).
split; [eapply aheap_presA_of_munch_a; [exact GC| exact PB| exact PF| exact CSP| exact MU| exact WM| exact ZA]|].
assert (QR' : QR3 C aa LB0 FS0 G1 RE X m').
{ eapply QR3_ext; [eapply (QR3_munch C); [exact GC| exact QR| exact MU| exact WM| exact ZA]| exact QF3| exact QF4| exact QF5| exact SL]. }
destruct QR' as (RC' & RSe' & RF').
eapply (ARUN_close C _ _ _ _ _ X G1 LB0 FS0); [exact PB| exact PF|]. cbn [ps_a set_a].
split; [exact GC1|]. rewrite HRT, HRS, HRP, HRC, HRD.
split; [exact RT'|]. split; [exact RS'|]. split; [exact RP'|]. split; [exact RC'|]. split; [exact RSe'|].
split.
{ eapply (ac_RQuar_ext C).
- eapply (ac_RQuar_frame C); [exact R6| exact WM|]. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx _. apply outside_intro.
intros lo' hi' Hin Hx. pose proof (ZN lo' hi' x Hin Hx) as [P|[P|[P|P]]].
+ exact (fpQ_RPrim _ _ _ _ _ _ GC x Fx P).
+ exact (fpQ_RStats _ _ _ _ _ _ GC x Fx P).
+ exact (fpQ_RDepot _ _ _ _ _ _ GC x Fx P).
+ exfalso. apply (fp_RQuar_cz _ _ FS0 _ _ _ GC x Fx). left. lia.
- exact QF1.
- exact QF2.
- exact QF3.
- intros; tauto.
- exact SQ. }
split; [exact RD'| exact RF'].
Qed.

Lemma malloc_prim_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (n lo dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_malloc_stack a_alayout ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 n -> 0 <= n <= 2^26 ->
from_primary n = true ->
@implMG PStateA asegs (at_nodeA LV asegs) _ (raw_malloc_A L n) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some p => exists A junk,
a0' = Z_to_bv 64 A /\ ablock_rangeA A n /\ aptr_req p = n
/\ ARUN C s' ((p, A, n) :: LB) FS RE m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
/\ blk_shadow asegs m' A n
/\ (forall mb k, p = ASec mb k -> A = mb + kSecUserOff)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ala_malloc a_alayout)) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros EL AR ST CEIL LO MI -> -> UNW DNH DCAP -> Hn HP.
cbn [ala_malloc_stack ala_tp ala_gp ala_malloc a_alayout] in LO |- *.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRD in R7.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof (class_of_facts n ltac:(lia) HP) as (Hc & Csz & _). cbv zeta in Hc, Csz.
pose proof (needed_facts n ltac:(lia)) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
apply raw_malloc_A_intro. rewrite <- EL.
pose proof (malloc_icpt_spec LV RE X ra (bv_unsigned sp) (wz 67584) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s (ps_a s) G LB0 FS0 lo n dn GC R1 R2 R3 R7 MI ST CEIL' ltac:(unfold MALLOC_STACK; lia) ltac:(lia) UNW DNH DCAP ltac:(lia) HP) as M.
rewrite Z_to_bv_bv_unsigned in M.
eapply aimplT_mono; [exact M|]. clear M.
intros [r aa] s' ms' PO. cbn [fst snd]. unfold malloc_post in PO.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m' & G1 & -> & -> & WM & MI' & ST' & RT' & RS' & RD' & DS' & REST).
unfold std_postA. rewrite Z_to_bv_bv_unsigned. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
set (c := class_of n) in *.
destruct r as [p|].
- destruct REST as (aa1 & i & -> & -> & QF & GS & TI & I0 & -> & MU & RPF & CM & HJU).
destruct (lift_some s LB FS RE X G LB0 FS0 aa1 G1 c i n m m' (bv_unsigned sp) _ PB PF GC R4 R5 R6 R8 eq_refl Hn HP ltac:(idtac; lia) QF GS TI I0 MU WM
ltac:(intros lo' hi' x Hin Hx; eapply (malloc_W_mz (ps_a s) aa1 LB0 FS0 G G1 RE X c i); try eassumption; [lia| idtac; unfold MALLOC_STACK; lia])
RT' RS' RD' RPF CM) as (HP1 & HP2 & HP3 & HP4).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|].
pose proof (class_of_facts n ltac:(lia) HP) as (_ & Csz' & _). cbv zeta in Csz'. fold c in Csz'.
assert (N1 : n <= class_size c - rz_size n) by (unfold needed in Csz'; pose proof (round_up_8 (Z.max n 8) ltac:(lia)); lia).
destruct (hjunk_split _ _ (slot_beg RE c i + rz_size n + n) _ HJU ltac:(lia)) as [HJ1 _].
replace (slot_beg RE c i + rz_size n + n) with (slot_beg RE c i + rz_size n + Z.of_nat (Z.to_nat n)) in HJ1 by lia. destruct (hjunk_cells _ _ _ HJ1) as [junk UC].
split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|].
exists (slot_beg RE c i + rz_size n), junk. split; [reflexivity|]. split; [exact HP2|]. split; [reflexivity|]. split; [exact HP3|].
split; [exact UC|]. split; [exact HP4|]. intros mb k E. discriminate.
- destruct REST as (-> & MU & QF & GS & RP').
destruct (lift_none s LB FS RE X G LB0 FS0 aa G1 c n m m' (bv_unsigned sp) _ PB PF GC R4 R5 R6 R8 eq_refl ltac:(idtac; lia) QF GS MU WM
ltac:(intros lo' hi' x Hin Hx; eapply (malloc_W_mz0 (ps_a s) LB0 FS0 G RE X c); try eassumption; [lia| idtac; unfold MALLOC_STACK; lia])
RT' RS' RD' RP') as (HP1 & HP3).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|]. split; [reflexivity| exact HP3].
Qed.
End Lift.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QTVW.Mqa QOJv.Mqb QNQk Q9Ho.Mq4 QV3O QnRU.Mql QmP7.Mq1 QpY2.Mqb QYyZ.Mq8 Qu3b QYyZ.Mqc QjgW QYyZ.Mqa QpME.Mq8 QpF1 QQ8H.Mq5 QmvA.Mq5 QpME.Mqc.
Import QVo2.Mq4.
Import QpY2.Mqc.
Import QRfV.Mq3 QnRU.Mqk QEYd.Mq0.
Import QcfN.Mq4.
Import QlES.
Import QVo2.Mq2.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Let atn := at_nodeA L asegs.
Hypothesis large_alloc_spec : large_alloc_stmt RE X L.
Hypothesis poison_zero_spec : poison_zero_stmt_lh RE X L.

Definition malloc_W_sec (bp : Z) : list (Z * Z) :=
(bp - MALLOC_STACK, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W_sec RE X (bp - 2144)).

Definition malloc_post_sec (ra : word) (bp : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (LB : list ablock) (n lo : Z) (m : word -> option byte)
(r : option aptr * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
ms' = MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo bp
/\ RTconst RE X m' /\ RStats RE X m' /\ RDepot RE X m' /\ depot_step m m'
/\ match r with
| (None, a1) => a0 = wz 0 /\ a1 = a /\ munch (malloc_W_sec bp) m m' /\ RSec a LB RE X m'
| (Some p, a1) => exists mb, let msz := sec_map_size n in
p = ASec mb n
/\ as_reg a1 = as_reg a ++ [mkSec mb msz n]
/\ as_tq a1 = as_tq a /\ as_gq a1 = as_gq a /\ (forall c, cls a1 c = cls a c)
/\ as_cache_inited a1 = as_cache_inited a /\ as_next a1 = as_next a
/\ (as_nres a1 = as_nres a \/ as_nres a1 = as_nres a + kPtrArrBlock)
/\ as_spent a1 = as_spent a + sec_cost msz
/\ mb mod kPage = 0 /\ appr mb msz /\ mb + msz <= band_lo /\ zavoids mb msz (avoid_of (ae_L RE) a) = true
/\ a0 = wz (mb + kSecUserOff)
/\ munch (malloc_W_sec bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m m'
/\ RSec a1 LB RE X m'
/\ chunk_mem m' (mb + kPage) (mb + msz) (mb + kSecUserOff) n
end.

Lemma malloc_icpt_sec_spec : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PStateA) (a : AState) (G : ghost) (LB : list ablock) (FS : list fframe) (lo n dn : Z),
gcons a LB FS G RE X ->
RTconst RE X m -> RStats RE X m -> RSec a LB RE X m -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - MALLOC_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
0 <= n <= 2^26 -> from_primary n = false ->
aimplT atn (asan_malloc (ae_L RE) a n) s
(malloc_post_sec ra bp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB n lo m)
(MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x636a0) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros GC RT RS RSE RD MI ST CEIL LO BPR UNW DNH DCAP Hn HP.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof CEIL as CEIL'. idtac. unfold MALLOC_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & PC & _ & QK & QC & _). unfold prim_hi in PC. unfold ptrarr_hi in QC. idtac. rewrite ?KHI_eq in PK.
change (al_space_beg (ae_L RE)) with (prim_lo RE) in PC. change (al_ptrarr (ae_L RE)) with (ptrarr_lo RE) in QC.
apply appr_to_lia in QK; [| lia| lia].
pose proof (munch_refl (malloc_W_sec bp) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold malloc_W_sec, MALLOC_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE in MU. cbn [tl app] in MU.

assert (SEF : forall mm mm' W, munch W mm mm' -> wmono asegs mm mm' ->
(forall lo' hi' z, In (lo', hi') W -> lo' <= z < hi' -> fp_RStats RE X z \/ fp_RDepot RE X z \/ band_lo <= z) ->
RSec a LB RE X mm -> RSec a LB RE X mm').
{ intros mm mm' W MUw WMw HW RSEw. eapply RSec_frame; [exact RSEw| exact WMw|]. eapply agree_on_of_munch; [exact MUw| exact WMw|]. intros z Fz _. apply outside_intro.
intros lo' hi' Hin Hz. destruct (HW lo' hi' z Hin Hz) as [P|[P|P]].
- exact (fpS_excl _ _ _ _ _ _ GC z P ltac:(right; left; exact Fz)).
- exact (fpD_excl _ _ _ _ _ _ GC z P ltac:(right; left; exact Fz)).
- pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)). lia. }
apply aimplT_from_evt.
eapply malloc_icpt_pre; [exact RT| exact RL| exact (RDepot_unw RE X _ RD)| exact MI| exact ST| exact CEIL'| unfold MALLOC_STACK; lia| exact BPR| exact UNW| lia|].
intros m1 u0 u1 u2 u3 u4 u5 u6 u7 u8 u10 u11 u12 u13 sz q rest junk8 MU1 WM1 MI1 ST1 OBJ LQ SZR FR RT1 TU1.
unfold micpt_W in MU1.
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU1| exact WM1|]. constructor; [first [st_avoid_solve| eapply st_avoid_T; [eassumption| lia| lia]]|]. constructor; [st_avoid_solve| constructor]. }
assert (RSE1 : RSec a LB RE X m1).
{ eapply SEF; [exact MU1| exact WM1| | exact RSE]. intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
- do 2 right. idtac. lia.
- right; left. do 3 right. lia. }
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame_unw; [exact RL| exact RD| exact WM1| | exact TU1]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z [Fz NZ] _. cbn [outside].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). idtac. lia. }
phase_done MU m m1 MU1 WM1. clear RT RS RSE RD MI. try clear ST.
destruct (unw_obj_head _ _ _ _ _ _ OBJ LQ ltac:(lia)) as [OBJh (q30 & TRQ & LQ30)].

unfold asan_malloc_entry. carve_frame 16%nat ST1.
match goal with H : rw_cells asegs _ (bp + -2128 + -16) _ |- _ => replace (bp + -2128 + -16) with (bp + -2144) in H by lia end.
replace (bp + -2128 + -16) with (bp + -2144) in ST1 by lia.
pose proof (munch_refl [(bp - 2144, bp - 2128)] m1) as MUa. pose proof (wmono_refl asegs m1) as WMa.
step. stf. step.
step. step. step. stp. stp. step. stp.
step.
lazymatch type of MUa with munch _ _ ?mm =>
destruct (sz_frame RE X a LB FS G m1 mm _ GC MUa WMa ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; right; idtac; lia)) as (FT & _ & FD);
pose proof (FT RT1) as RT2; pose proof (FD RD1) as RD2;
assert (RSE2 : RSec a LB RE X mm) by (eapply SEF; [exact MUa| exact WMa| intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; do 2 right; idtac; lia| exact RSE1]);
assert (RS2 : RStats RE X mm) by (eapply RStats_munch; [exact RS1| exact MUa| exact WMa| constructor; [st_avoid_solve| constructor]]) end.
clear FT FD RT1 RSE1 RD1 RS1 MUa WMa.
apply evt_done. change (wz 977752) with (wz A_INSTANCE).
eapply aimplT_then.
{ eapply (allocate_sec_spec L RE X large_alloc_spec poison_zero_spec _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s a G LB FS n 1 lo (bp + -2128) sz dn q30 GC RT2 RS2 RSE2 RD2);
[assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| exact Hn| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post_sec in PO. rewrite !(unsigned_lit (bp + -2144)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 258660)) with (wz 258660) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_INSTANCE in REST.
clear OBJh TRQ RT2 RSE2 RD2 RS2.

assert (FRALL : forall mx, rw_cells asegs mx (bp + -2128) (unw_obj (bp + -2128) sz q rest bp) ->
rw_cells asegs mx (bp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mx (bp + -2128) (unw_obj (bp + -2128) sz q rest bp ++ [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ intros mx O1 O2. apply (proj2 (rw_cells_app asegs mx _ _ _)). split; [exact O1|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia).
unfold unw_obj. cbn [cells_size csize Nat.add map app]. replace (bp + -2128 + Z.of_nat 2064) with (bp + -64) by lia. exact O2. }
destruct r as [p|].
-
destruct REST as (mb & -> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & -> & MUk & RSEk & CM & _).
pose proof MBK as MBK'. apply appr_to_lia in MBK'; [| pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG0 _]; lia| lia]. pose proof MBC as MBC'. idtac.
set (msz := sec_map_size n) in *.
assert (MS8 : 8 * (msz / 8) = msz /\ 4096 <= msz) by (pose proof (sec_geom_facts n Hn HP) as (G1 & _ & _ & _ & G5 & G6 & G7 & G8 & _); fold msz in G7, G8; clear - G1 G5 G6 G7 G8; Z.div_mod_to_equations; lia).
assert (SHM : SH (mb + msz) = SH mb + msz / 8) by (rewrite <- SH_plus8; f_equal; lia).
assert (MBH : 0x647000 <= mb) by (pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG _]; fold msz in SMG; pose proof (sec_req_facts n ltac:(lia) HP) as [_ RQn]; clear - MBK' SMG RQn; lia).
assert (SHB : 0x80000000 <= SH mb /\ SH mb + msz / 8 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; clear - MBH MBC' MS8; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD.
rewrite SHM in MUk. remember (msz / 8) as q8 eqn:EQ8. clear EQ8.
apply (munch_weaken _ (((bp - 3296, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (6444156, 6444156 + 4) :: (1524768, 1524769) :: (rl_T X + 2800, rl_T X + 3168)
:: (977752 + 104, 977752 + 728) :: (ptrarr_lo RE, ptrarr_lo RE + 8388608) :: (1851528, 6373552) :: (rl_dn X, rl_dn X + 1048576) :: (rl_ssb X, rl_ssb X + 8388608) :: nil)
++ [(mb, mb + msz); (SH mb, SH mb + q8)])) in MU.
2:{ intros z Hz. cbn [outside app] in Hz |- *. clear - Hz. tauto. }
cbn [app] in MU. cbn [app] in MUk. phase_done MU m2 m3 MUk WM3.
rewrite KU.
step. ifz.
step. step. step.
release_frame FR0 ST3 (bp + -2128).
step.
replace (ret_pc (wz 407988)) with (wz 407988) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 7 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST3 bp.
step.
apply evt_done. unfold malloc_post_sec. do 15 eexists. exists m3.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST3|].
split; [exact RT3|]. split; [exact RS3|]. split; [exact RD3|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. exists mb. cbv zeta. fold msz.
split; [reflexivity|]. split; [exact REG|]. split; [exact TQ|]. split; [exact GQ|]. split; [exact CLS|]. split; [exact CI|]. split; [exact NX|].
split; [exact NR|]. split; [exact SPN|]. split; [exact MBP|]. split; [exact MBK|]. split; [exact MBC|]. split; [exact ZA|].
split; [rewrite KU; reflexivity|]. split; [| split; [exact RSEk| exact CM]].
rewrite SHM. unfold malloc_W_sec, MALLOC_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU.
-
destruct REST as (-> & -> & MUk & RSEk).
phase_done MU m2 m3 MUk WM3.
step. if_lit.
step.
pose proof (munch_refl [(bp - 2160, bp - 2144); (A_ERRNO, A_ERRNO + 4)] m3) as MUe. pose proof (wmono_refl asegs m3) as WMe. unfold A_ERRNO in MUe.
step. call_ch (set_errno_spec RE X) ltac:(fun PO => unfold A_ERRNO in PO; rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RS3| assumption| rewrite unsigned_lit by lia; exact ST3| exact CEIL'| rewrite unsigned_lit by lia; lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST4 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS4 end.
lazymatch type of MUe with munch _ _ ?mm =>
destruct (sz_frame RE X a LB FS G m3 mm _ GC MUe WMe
ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia])) as (FT & _ & FD);
assert (RSE4 : RSec a LB RE X mm) by (eapply SEF; [exact MUe| exact WMe| intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[do 2 right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia]| exact RSEk]) end.
pose proof (FT RT3) as RT4. pose proof (FD RD3) as RD4. clear FT FD MUe WMe RT3 RSEk RD3 RS3.
step.
step. step. step.
release_frame FR0 ST4 (bp + -2128).
step.
replace (ret_pc (wz 407988)) with (wz 407988) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 7 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST4 bp.
step.
apply evt_done. unfold malloc_post_sec. do 15 eexists. lazymatch type of ST4 with stk _ ?mm _ _ => exists mm end.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST4|].
split; [exact RT4|]. split; [exact RS4|]. split; [exact RD4|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [| exact RSE4].
unfold malloc_W_sec, MALLOC_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU.
Qed.
End S.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QV3O QnRU.Mql Q9Ho.Mq4 QmP7.Mq1 QYyZ.Mq8 Q9Ho.Mq3.
Import QpY2.Mqc.
Import QXcn QpME.Mq7.
Import QYyZ.Mqc.
Import Qu3b QnRU.Mqj QmvA QkZz.Mq2 QteI.Mqi QQ8H.Mq6.
Import QcfN.Mq4.
Import QlES.
Import QnRU.Mqh.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_3 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.

Import QpME.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_4 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Ltac Q0z1.sf_hide_poison ::= sf_hide_poison_divlit. Local Ltac mkr__sf_hide_poison_5 := sf_hide_poison_divlit.

Local Notation wz := (Z_to_bv 64).

Definition qchunk_entry : Z := 0x435c0.

Definition QCHUNK_STACK : Z := PUT_STACK.

Section S.
Context {BAND : Band}.
Variables (C : arun_components) (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).
Hypothesis recycle_spec : recycle_stmt C RE X L.

Hypothesis HRD : ac_RDepot C = RDepot.

Lemma qchunk_spec : forall ra sp gp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (p : aptr) (A lo : Z)
(obj sz bp dn : Z) (q0 q1 q2 q3 q4 : word) (rest : list byte),
QRUN C 0 QB QB [(p, A)] a LB0 FS0 G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - QCHUNK_STACK ->
0 <= aptr_req p <= 2^26 ->
qroom a p ->
rw_cells asegs m obj (unw_obj obj sz [q0; q1; q2; q3; q4] rest bp) ->
1 <= sz <= 30 -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= obj -> obj + 2080 < 2^64 ->
aimplT atn (tbind (enqueue (ae_L RE) a p) (fun s1 => if kQMaxCache <? q_bytes (as_tq s1) then drain (ae_L RE) s1 else tret s1)) s
(qret_post C RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 FS0 lo m free_step)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz (A - 16)) a2 (wz obj) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz qchunk_entry) fc None m (seg_rom asegs)).
Proof.
intros until rest; intros QR MI ST CEIL LO HN QRM OBJ SZB DNH DCAP OLO OHI.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof CEIL as CEIL'. idtac. unfold QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
change (2^64) with 18446744073709551616 in OHI.
pose proof kq_consts as (K24 & KBB & KBC & KMX & KMN & KMC). pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (rlay_obj_facts_lia RE X _ RL (ctx_obj RE X)) as (_ & CK & CB' & _). cbn [fst snd] in CK, CB'. idtac. rewrite ?KHI_eq in CK.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC, TD. rewrite ?KHI_eq in PK. idtac.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND). unfold QB in BND.
pose proof PQA as PQA0. apply Forall_cons_iff in PQA as [EQA _]. cbn [fst snd] in EQA.
assert (HU : 1 <= aptr_used p <= 2^26 + 1) by (unfold aptr_used, used_size; lia).
set (u := aptr_used p) in *. set (n := aptr_req p) in *.

pose proof (REP p ltac:(left; reflexivity)) as REPp.
pose proof (rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & NPd & _). cbn [fst snd] in NK, NC, NPd. unfold iv_disjoint, prim_lo in NPd; cbn [fst snd] in NPd.
idtac. rewrite ?KHI_eq in NK.
pose proof (rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & BPd & _). cbn [fst snd] in BK, BC, BPd. unfold iv_disjoint, prim_lo in BPd; cbn [fst snd] in BPd.
idtac. rewrite ?KHI_eq in BK.
assert (PC0 : exists lo_ hi_, qchunk_mem m lo_ hi_ A n /\ (forall x, lo_ <= x < hi_ -> fp_RQuar a LB0 G RE X x)
/\ (forall x, lo_ <= x < hi_ -> ~ (rl_T X <= x < rl_T X + 4096) /\ ~ (rl_dn X <= x < rl_dn X + 1048576) /\ ~ (rl_ssb X <= x < rl_ssb X + 8388608))).
{ destruct p as [id n0|mb n0]; cbn [qptr_rep] in REPp; subst n; cbn [aptr_req] in *.
- destruct REPp as (i & Ht & Hpr & HQA & QM). rewrite EQA in QM. eexists _, _. split; [exact QM|].
pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht) as (P1 & P2 & _). unfold prim_hi, prim_lo in P1, P2. split.
+ intros x Hx. do 5 right; left. exists (class_of n0), i, (TQuar (APrim id n0)). split; [exact Ht|]. split; [reflexivity|]. split; cbn [fst snd]; lia.
+ intros x Hx. (first [ clear - Hx x P2 P1 BPd NPd i PK TD TK ks n0 id X RE BAND; lia | lia ]).
- destruct REPp as (Hin & Hnl & Hpr & HQA & QM). rewrite EQA in QM. eexists _, _. split; [exact QM|]. split.
+ intros x Hx. do 7 right; left. exists (mkSec mb (sec_map_size n0) n0); cbn [se_beg se_size se_req]. auto.
+ intros x Hx. pose proof (sec_facts _ _ _ _ _ _ GC _ Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & D3). cbn [se_beg se_size] in D3.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (T_obj RE X)) as D. unfold iv_disjoint in D; cbn [fst snd] in D.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (dn_obj RE X)) as Dn. unfold iv_disjoint in Dn; cbn [fst snd] in Dn.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (ssb_obj RE X)) as Db. unfold iv_disjoint in Db; cbn [fst snd] in Db. pose proof KP. (first [ clear - H Db Dn D Hx x BPd BK NPd NK PK TD TK ks n0 mb X RE BAND; lia | lia ]). }
destruct PC0 as (plo & phi & QMp & PZ & PT3).
assert (PT : forall x, plo <= x < phi -> ~ (rl_T X <= x < rl_T X + 4096)) by (intros x Hx; exact (proj1 (PT3 x Hx))).
pose proof (qchunk_geom _ _ _ _ _ QMp) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & q' & g' & r' & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
assert (PDN1 : phi <= rl_dn X \/ rl_dn X + 1048576 <= plo).
{ destruct (Z.le_gt_cases phi (rl_dn X)) as [H1|H1]; [left; exact H1|].
destruct (Z.le_gt_cases (rl_dn X + 1048576) plo) as [H2|H2]; [right; exact H2|].
exfalso. apply (proj1 (proj2 (PT3 (Z.max plo (rl_dn X)) ltac:(lia)))). lia. }
assert (PDN2 : phi <= rl_ssb X \/ rl_ssb X + 8388608 <= plo).
{ destruct (Z.le_gt_cases phi (rl_ssb X)) as [H1|H1]; [left; exact H1|].
destruct (Z.le_gt_cases (rl_ssb X + 8388608) plo) as [H2|H2]; [right; exact H2|].
exfalso. apply (proj2 (proj2 (PT3 (Z.max plo (rl_ssb X)) ltac:(lia)))). lia. }
clear X1 X2 X3 X4 X5 X6 X7 X8 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 q' g' r'.
pose proof (qchunk_geom _ _ _ _ _ QMp) as (G1 & G2 & G3 & G4 & _). rewrite ?KHI_eq in G3. idtac.
destruct QMp as (_ & (b1 & idw & Hb1 & HDRp) & JUNKp & _). unfold qhdr_cells in HDRp.
pose proof (used_size_pos n ltac:(lia)) as [U1 U2]. assert (UN : used_size n = u) by (subst u n; reflexivity). rewrite UN in *.
pose proof (round_up_ge u 8 ltac:(lia)) as RU.
destruct (hjunk_split _ A (A + 8) phi JUNKp ltac:(lia)) as [J8 _]. destruct (hjunk_C8 _ A J8) as [w0 JC].
destruct (unw_obj_open m obj sz [q0; q1; q2; q3; q4] rest bp eq_refl OBJ) as (q30 & rest2 & LQ30 & _ & TRQ30 & _).

unfold unw_obj in OBJ. cbn [map app] in OBJ.
apply (proj1 (rw_cells_app asegs m obj [C8 (wz (obj + 16))] _)) in OBJ as [OB0 OBJ].
apply (proj1 (rw_cells_app asegs m _ [C4 (wz sz); C4 (wz 0)] _)) in OBJ as [OB1 OBJ].
apply (proj1 (rw_cells_app asegs m _ [C8 q0; C8 q1; C8 q2; C8 q3; C8 q4] _)) in OBJ as [OB2 OB3].
cbn [cells_size csize Nat.add] in OB1, OB2, OB3. change (Z.of_nat 8) with 8 in OB1, OB2, OB3. change (Z.of_nat 40) with 40 in OB3.
replace (obj + 8 + 8) with (obj + 16) in OB2, OB3 by lia. replace (obj + 16 + 40) with (obj + 56) in OB3 by lia.
recast OB1 [C8 (wz sz)].
rtc RT 26%nat K26.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned sp - 48 - depot_stack, bv_unsigned sp - 48); (A, A + 8)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
unfold qchunk_entry, depot_stack, SS_BASE, DP_END, QOBJ, TQ, GQ, QMUT, A_INSTANCE in *.
change (977752 + 888) with 978640 in *. change (977752 + 880) with 978632 in *. change (977752 + 728) with 978480 in *.
pose proof HM as HM0. hide HM0. hide JUNKp.
set (Wq := [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned sp - 48 - 224, bv_unsigned sp - 48); (A, A + 8);
(1851528, 6373552); (rl_dn X, rl_dn X + 1048576); (rl_ssb X, rl_ssb X + 8388608)]).
assert (WZ : forall lo' hi' x, In (lo', hi') Wq -> lo' <= x < hi' -> azone a LB0 G RE X (bv_unsigned sp) x).
{ intros lo' hi' x Hin Hx. subst Wq. cbn in Hin. unfold azone.
destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-.
- do 4 right. lia.
- do 4 right. lia.
- left. apply PZ. lia.
- do 3 right; left. left. split; cbn [fst snd]; lia.
- do 3 right; left. right; left. split; cbn [fst snd]; lia.
- do 3 right; left. right; right; left. split; cbn [fst snd]; lia. }
assert (RTW : Forall (rt_avoid RE X) Wq).
{ subst Wq. repeat apply Forall_cons; try apply Forall_nil; intros x Hx FT; cbn [fst snd] in Hx.
- exact (rt_avoid_stack RE X RL (bv_unsigned sp - 48) (bv_unsigned sp) ltac:(lia) x Hx FT).
- exact (rt_avoid_stack RE X RL (bv_unsigned sp - 48 - 224) (bv_unsigned sp - 48) ltac:(lia) x Hx FT).
- exact (fpQ_RTconst a LB0 FS0 G RE X GC x (PZ x ltac:(lia)) FT).
- refine (fpD_excl a LB0 FS0 G RE X GC x _ (or_intror (or_intror (or_intror FT)))). left. split; cbn [fst snd]; lia.
- refine (fpD_excl a LB0 FS0 G RE X GC x _ (or_intror (or_intror (or_intror FT)))). right; left. split; cbn [fst snd]; lia.
- refine (fpD_excl a LB0 FS0 G RE X GC x _ (or_intror (or_intror (or_intror FT)))). right; right; left. split; cbn [fst snd]; lia. }
assert (STW : Forall st_avoid Wq).
{ subst Wq. unfold A_ERRNO in *. repeat apply Forall_cons; try apply Forall_nil.
- st_avoid_solve.
- st_avoid_solve.
- apply st_avoid_offhull; cbn [fst snd]; (first [ clear - RU U1 G3 G2 G1 phi plo BK NK u ks A p X BAND; lia | lia ]).
- apply st_avoid_high; cbn [fst snd]; unfold A_ERRNO; lia.
- st_avoid_solve.
- st_avoid_solve. }
assert (RTW3 : Forall (rt_avoid RE X) (firstn 3 Wq)) by (pose proof RTW as RTW'; subst Wq; inversion RTW' as [|? ? R1 X1]; inversion X1 as [|? ? R2 X2]; inversion X2 as [|? ? R3 X3]; subst;
cbn [firstn]; constructor; [exact R1| constructor; [exact R2| constructor; [exact R3| constructor]]]).
subst Wq. cbn [firstn] in RTW3.
apply aimplT_from_evt.
carve_frame 48%nat ST.
do 7 step.
step.
step.
step. step. if_lit.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW3]) end.
call_sp_ch (get_current_thread_spec RE X) ltac:(fun PO => idtac); try eassumption; try lia.
subst. rename POST into RT2.
step. ifz.
pose proof (RT_T _ _ _ RT2) as KT. unfold rt_T_cells in KT.
step.
step. step.
pose proof (RT_ctx_tid _ _ _ RT2) as KC.
step.
step. step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RD1 : RDepot RE X mc);
[ eapply RDepot_frame; [exact RD| exact WM|]; eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Fx _; apply outside_intro; intros lo' hi' Hin Hy; cbn in Hin;
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-;
[ pose proof (fp_lt_ceil a LB0 FS0 G RE X GC z ltac:(do 5 right; left; exact Fx)); lia
| pose proof (fp_lt_ceil a LB0 FS0 G RE X GC z ltac:(do 5 right; left; exact Fx)); lia
| exact (fpQ_RDepot a LB0 FS0 G RE X GC z (PZ z ltac:(lia)) Fx) ]
| ] end.
change (sx32 (wz 0)) with (wz 0).
hide MU.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (DNHc : depot_n asegs mc dn) by (split; [unfold DP_N; exact DNC| exact DNP]) end.
eapply evt_cut.
{ eapply (depot_put_spec RE X) with (q := q30) (dn := dn); try eassumption; rewrite ?unsigned_lit by lia; try eassumption; try lia.
- unfold depot_stack. lia. }
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MUd & WMd & MId & STd & id & -> & IDB & RD3 & TRQ3 & (dn3 & [DNC3 DNP3] & DNR3)). unfold DP_N in DNC3. clear DNHc.
rewrite !(unsigned_lit (bv_unsigned sp + -48)) in MUd, STd by lia. unfold depot_stack, SS_BASE, DP_END in MUd.
clear KT KC K26.
unhide MU.
set (Wall := [(bv_unsigned sp + -48, bv_unsigned sp); (bv_unsigned sp + -48 - 224, bv_unsigned sp + -48); (QA p, QA p + 8);
(bv_unsigned sp + -48 - 224, bv_unsigned sp + -48); (1851528, 6373552); (rl_dn X, rl_dn X + 1048576); (rl_ssb X, rl_ssb X + 8388608)]).
lazymatch type of MUd with munch _ ?mx _ =>
assert (MUall : munch Wall m m3) by (subst Wall; eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUd]];
intros z Hz; cbn [outside app] in Hz |- *; clear - Hz; tauto);
pose proof (wmono_trans asegs _ _ _ WM WMd) as WMall;
clear MU; transport_after_call asegs mx m3 MUd WMd end.
clear MUd. pose proof (munch_refl [(QA p, QA p + 8)] m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
replace (ret_pc (wz 275992)) with (wz 275992) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

assert (WCASE : forall lo' hi' z, In (lo', hi') Wall -> lo' <= z < hi' ->
(band_lo <= z < bv_unsigned sp) \/ (QA p <= z < QA p + 8) \/ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hx. subst Wall. cbn in Hin.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; injection E as <- <-.
- left. lia. - left. lia. - right; left. lia. - left. lia.
- right; right. left. split; cbn [fst snd]; lia.
- right; right. right; left. split; cbn [fst snd]; lia.
- right; right. right; right; left. split; cbn [fst snd]; lia. }
assert (WZ' : forall lo' hi' z, In (lo', hi') Wall -> lo' <= z < hi' -> azone a LB0 G RE X (bv_unsigned sp) z).
{ intros lo' hi' z Hin Hx. unfold azone. destruct (WCASE lo' hi' z Hin Hx) as [Z|[Z|Z]]; [do 4 right; exact Z| left; apply PZ; lia| clear - Z; tauto]. }
assert (EZ' : forall lo' hi' z, In (lo', hi') Wall -> lo' <= z < hi' -> ezone a LB0 G RE X z).
{ intros lo' hi' z Hin Hx. unfold ezone. destruct (WCASE lo' hi' z Hin Hx) as [Z|[Z|Z]]; [do 5 right; lia| left; apply PZ; lia| do 4 right; left; exact Z]. }
assert (RTW' : Forall (rt_avoid RE X) Wall).
{ subst Wall. inversion RTW as [|? ? R1 X1]; inversion X1 as [|? ? R2 X2]; inversion X2 as [|? ? R3 X3]; inversion X3 as [|? ? R4 X4]; inversion X4 as [|? ? R5 X5]; inversion X5 as [|? ? R6 X6]; subst.
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) in * by lia.
constructor; [exact R1|]. constructor; [exact R2|]. constructor; [exact R3|]. constructor; [exact R2|]. constructor; [exact R4|]. constructor; [exact R5|]. constructor; [exact R6| constructor]. }
assert (STW' : Forall st_avoid Wall).
{ subst Wall. inversion STW as [|? ? R1 X1]; inversion X1 as [|? ? R2 X2]; inversion X2 as [|? ? R3 X3]; inversion X3 as [|? ? R4 X4]; inversion X4 as [|? ? R5 X5]; inversion X5 as [|? ? R6 X6]; subst.
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) in * by lia.
constructor; [exact R1|]. constructor; [exact R2|]. constructor; [exact R3|]. constructor; [exact R2|]. constructor; [exact R4|]. constructor; [exact R5|]. constructor; [exact R6| constructor]. }
clear RTW STW WZ RTW3. subst Wall.

replace (QA p - 16) with (QA p + -16) in HDRp |- * by lia.
do 4 step.
step.
step.
step. step.
change (zx16 (wz 0)) with (wz 0). rewrite (zx32_small u) by lia.
step. step.
step. step.
rewrite (unsigned_lit u) by lia. rewrite Z.lor_0_l.
step. step.
do 6 step.
step. step.
release_frame FR STd (bv_unsigned sp).
apply evt_done.
eapply aimplT_mono.
{ eapply (put_spec C L RE X); [| eassumption| exact STd| exact CEIL'| unfold PUT_STACK, DRAIN_STACK, RECYCLE_STACK; lia| subst n; lia| exact QRM].
split; [exact GC|]. split.
- apply QOTH_split. split; [eapply RTconst_munch; [exact RT| exact MUall| exact WMall| exact RTW']|].
split; [eapply RStats_munch; [exact RS| exact MUall| exact WMall| exact STW']|].
split.
+ eapply RPrim_frame; [exact RP| exact WMall|]. eapply agree_on_of_munch; [exact MUall| exact WMall|]. intros z Fx _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]].
* pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
* exact (fpQ_RPrim a LB0 FS0 G RE X GC z (PZ z ltac:(lia)) Fx).
* exact (fpP_RDepot a LB0 FS0 G RE X GC z Fx Z).
+ apply QREST_split. split.
* eapply QR3_munch; [exact GC| split; [exact RC| split; [exact RSE| exact RF]]| exact MUall| exact WMall| exact WZ'].
* rewrite HRD. eapply RDepot_frame; [exact RD3| exact WM3|]. eapply agree_on_of_munch; [exact MU3| exact WM3|]. intros z Fx _. apply outside_intro. intros lo' hi' Hin Hy.
cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. exact (fpQ_RDepot a LB0 FS0 G RE X GC z (PZ z ltac:(lia)) Fx).
- eapply (RQuarM_pend_agree 0 QB QB p (QA p) a LB0 FS0 G RE X m); [exact GC| exact (proj2 (proj2 QR))| exact WMall|].
eapply agree_on_of_munch; [exact MUall| exact WMall|]. intros z [Fx NH] _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]].
+ exact (fp_RQuar_cz a LB0 FS0 G RE X GC z Fx ltac:(left; lia)).
+ exact (NH Z).
+ exact (fpQ_RDepot a LB0 FS0 G RE X GC z Fx Z). }
cbv beta. intros r1 s'' ms'' PO. unfold qret_post in PO |- *.
destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m5 & G5 & -> & -> & MI5 & ST5 & AP5 & DK5 & QR5).
do 15 eexists. exists m5, G5. split; [reflexivity|]. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [| split; [| exact QR5]].
2:{
destruct DK5 as [DK5 EK5]. split.
- eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [apply DK5; split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]].
- eapply errno_keep_trans; [| exact EK5]. eapply (errno_keep_of_ezone a LB0 FS0 G RE X m _ _ GC MUall WMall). exact EZ'. }
eapply aheap_presA_trans; [| exact AP5].
eapply aheap_presA_of_munch_a; [exact GC| apply Permutation_refl| apply Permutation_refl| lia| exact MUall| exact WMall| exact WZ'].

rewrite (Z.shiftr_div_pow2 sz 8) by lia. rewrite (Z.div_small sz (2^8)) by lia. rewrite !Z.shiftr_0_l. reflexivity.
Qed.
End S.
End Mq8.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoNr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoNr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qk8e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qk8e.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWHo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWHo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcfN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcfN.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoBx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoBx.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpzM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpzM.Mqo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnaW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnaW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ8H.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ8H. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpzM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpzM.Mql. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QS6k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QS6k. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Xw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Xw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFwQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFwQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QE12.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QE12.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition fprintf_stub : Z := 0x4fd70.
Definition fprintf_icpt_entry : Z := 0x54638.

Lemma ssp_cells_munch' : forall m m' W canary, ssp_cells m canary -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (snd iv <= got_ssp \/ got_ssp + 8 <= fst iv) /\ (snd iv <= ssp_guard \/ ssp_guard + 8 <= fst iv)) W -> ssp_cells m' canary.
Proof.
intros m m' W canary [G1 G2] MU WM HW. split.
- eapply rw_cells_apart; [exact G1| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [H _]. cbn in *. lia.
- eapply rw_cells_apart; [exact G2| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [_ H]. cbn in *. lia.
Qed.

Lemma forall_range_b : forall l, forallb (fun c => (0 <=? c) && (c <? 256))%bool l = true -> Forall (fun c => 0 <= c < 256) l.
Proof.
intros l H. rewrite forallb_forall in H. apply Forall_forall. intros c Hc. specialize (H c Hc).
apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma vf_to_diag_post : forall St ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (st st' : St) ms,
vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st' ms -> st' = st ->
fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt st' ms.
Proof.
intros until ms. intros (x5 & x6 & x7 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & E & MU & WM & MI & FRM & FOK & ST & SF & SSP) Est.
exists x5, x6, x7, a0, a1, a2, a3, a4, a5, a6, a7, x28, x29, x30, x31, Ft, fc', m'.
repeat (split; [assumption|]). exact Est.
Qed.

Section FprintfIcpt.
Context {BAND : Band}.
Context {St : Type}.
Hypothesis FWE : fwritex_stderr_stmt.
Hypothesis FLS : stdio_write_flush_stmt.

Definition pc_hyp (A : Z) (m : mem) (lo usp : Z) (a2 a3 a4 a5 a6 a7 : word) : Prop :=
forall (ra' gp' tp' t0 t1 t2 s0 s1 a0 a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m' : mem),
ISH m' -> mem_inv asegs m' -> stk asegs m' lo (usp + -112) ->
rw_cells asegs m' (usp + -48) [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
munch [(lo, usp)] m m' -> wmono asegs m m' ->
evt asegs (rpost ra' (wz (usp + -112)) gp' tp' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(bv_unsigned (wz (usp + -112)) - PCOMMON_STACK, bv_unsigned (wz (usp + -112)))] lo m' (fun _ _ => True))
(MS (mkR ra' (wz (usp + -112)) gp' tp' t0 t1 t2 s0 s1 a0 (wz A) (wz (usp + -48)) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m' (seg_rom asegs)).

Lemma fprintf_icpt_gen :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z) (lo : Z) (canary : word),
let q := bv_unsigned sp in
pc_hyp A m lo q a2 a3 a4 a5 a6 a7 ->
a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A ->
stderr_wfile m -> ISH m ->
bytes_at asegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
args_ok RSTDERR (q - 112 - 352) 80 m lo q (q - 112 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
stk asegs m lo q -> (lo <= q - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
Qpj5.Mq1.implM asegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
(fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz fprintf_stub) fc None m (seg_rom asegs)).
Proof using FLS FWE BAND.
intros until canary. cbv zeta.
intros PC -> -> SF ISH0 BY HF P1 AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA.
unfold FPRINTF_DEPTH, VF_FRAME, GLOBALS_TOP, STATIC_SPLIT in *. unfold pc_hyp, PCOMMON_STACK, pcommon_entry in PC.
assert (CEIL : band_lo <= lo) by (idtac; exact GLO).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs.
pose proof ISH0 as (ASH & RC & SB).
destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
set (BAh := bytes_at) in BY.
match goal with |- Qpj5.Mq1.implM _ _ _ ?Q _ => set (QQ := Q) end.
eapply (implM_evt asegs). 2:{ intros ms' H; exact H. } cbv beta.
unfold fprintf_stub. step.
carve_frame 112%nat ST.
do 15 istep.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof (rt_161720 _ RCc) as K18. pose proof (rt_157bb0 _ RCc) as K7. pose proof (rt_1f25bc _ RCc) as K22. pose proof (rt_159c68 _ RCc) as K17.
step. call_u tryinit_spec7; [exact K18| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. if_lit. istep. istep.
step. call_u tryinit_spec7; [exact K18| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. if_lit. istep. istep. istep. istep. istep. step. if_lit. istep. istep. istep. istep. step.

apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
replace (bv_unsigned sp + -112 + Z.of_nat 64) with (bv_unsigned sp + -48) in VAC by lia.
call_u PC; [ eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls] | assumption | exact ST | exact VAC | exact MUs | exact WM |].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
clear K18 K7 K22 RCc.

istep. istep. istep. step. istep. istep. step. step. clear K17.
apply evt_done.
lazymatch goal with |- Qpj5.Mq1.implM _ _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
assert (SSPA : ssp_cells mA canary) by (eapply ssp_cells_munch'; [exact SSP| exact MUs| exact WM| unfold got_ssp, ssp_guard; apply Forall_cons; [cbn; lia| apply Forall_nil]]).
assert (ISHA : ISH mA) by (eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls]).
assert (BYA : bytes_at asegs mA A (zb fmt)) by (subst BAh; eapply bytes_at_transport; [exact BY| exact MUs| cbn [disjoint_from]; rewrite LZB; lia]).
pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA.
clear SSP BY.
pose proof (vfprintf_stderr_proof (St:=St) FWE FLS) as VF. unfold vfprintf_stderr_stmt in VF. cbv zeta in VF.
eapply (implM_post_evt asegs).
{ eapply VF with (A := A) (VA := bv_unsigned sp + -48) (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := args) (lo := lo) (canary := canary);
clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
all: try reflexivity. all: try lia.
- exists flags, mode, e, wend, tail. split; [unfold file_cells; assumption | exact FL40].
- exact ISHA.
- exact BYA.
- exact HF.
- exact P1.
- exact VAA.
- clear MUs. eapply args_ok_vf; [| | exact MU]; [|lia].
replace (bv_unsigned sp + -112 - 352) with (bv_unsigned sp - 112 - 352) by lia.
replace (bv_unsigned sp + -112 - 368) with (bv_unsigned sp - 112 - 368) by lia. exact AOK.
- exact PP.
- exact FPC.
- exact ST.
- exact SSPA.
- assumption.
- exact FRM. }
cbv beta. intros [] [b4 st4] ms' P. clear VF MUs. cbn [snd] in P.
unfold vfprintf_stderr_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
transport_after_call asegs mA m3 MUc WMc. clear MUc WMc.
fixret.

do 5 istep. step.
lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -112) ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -48) ?rest |- _ =>
assert (FALL : rw_cells asegs mm (bv_unsigned sp + -112) (hd ++ rest));
[ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
| clear FR VAC ] end.
cbn [app] in FALL.
release_frame FALL ST3 (bv_unsigned sp).
apply evt_done. subst QQ. cbn [fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [assumption|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|]. split; [exact SF3|]. exact SSP3.
Qed.

Local Ltac pc_hyp_s LEM :=
intros until slack; intros BY HF SZ SLEN SEP CEIL LO UR; unfold pc_hyp; intros until m'; intros ISH' MI' ST' VA' MU' WM';
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in VA'; destruct VA' as [APC _];
lazymatch type of APC with rw_cells _ _ _ [C8 ?w] => rewrite <- (Z_to_bv_bv_unsigned w) in APC end;
eapply LEM;
[ exact ISH'| exact MI'| rewrite unsigned_lit by lia; exact ST'| exact CEIL| rewrite unsigned_lit by lia; unfold PCOMMON_STACK; lia| exact APC| rewrite unsigned_lit by lia; lia
| eapply bytes_at_transport; [exact BY| exact MU'| cbn [disjoint_from]; rewrite length_app, zb_length; cbn [length]; unfold zlength in SEP; lia]
| exact HF| exact SZ| exact SLEN| rewrite unsigned_lit by lia; lia ].
Lemma pc_hyp_usage : forall m lo usp (a2 a3 a4 a5 a6 a7 : word) (s : list Z) (slack : list byte),
bytes_at asegs m (bv_unsigned a2) (zb s ++ b8 0 :: slack) -> Forall (fun c => 0 < c < 256) s ->
szone (bv_unsigned a2) (zlength s + 1) -> zlength s + 1 <= 2^40 ->
(bv_unsigned a2 + zlength s + 1 + zlength slack <= lo \/ usp <= bv_unsigned a2) ->
band_lo <= lo -> lo <= usp - 112 - PCOMMON_STACK -> usp < 2^64 ->
pc_hyp AFMT_usage m lo usp a2 a3 a4 a5 a6 a7.
Proof.  unfold AFMT_usage, PCOMMON_STACK. pc_hyp_s printf_common_usage. Qed.
Lemma pc_hyp_cannot_open : forall m lo usp (a2 a3 a4 a5 a6 a7 : word) (s : list Z) (slack : list byte),
bytes_at asegs m (bv_unsigned a2) (zb s ++ b8 0 :: slack) -> Forall (fun c => 0 < c < 256) s ->
szone (bv_unsigned a2) (zlength s + 1) -> zlength s + 1 <= 2^40 ->
(bv_unsigned a2 + zlength s + 1 + zlength slack <= lo \/ usp <= bv_unsigned a2) ->
band_lo <= lo -> lo <= usp - 112 - PCOMMON_STACK -> usp < 2^64 ->
pc_hyp AFMT_cannot_open m lo usp a2 a3 a4 a5 a6 a7.
Proof.  unfold AFMT_cannot_open, PCOMMON_STACK. pc_hyp_s printf_common_cannot_open. Qed.
Lemma pc_hyp_read_error : forall m lo usp (a2 a3 a4 a5 a6 a7 : word) (s : list Z) (slack : list byte),
bytes_at asegs m (bv_unsigned a2) (zb s ++ b8 0 :: slack) -> Forall (fun c => 0 < c < 256) s ->
szone (bv_unsigned a2) (zlength s + 1) -> zlength s + 1 <= 2^40 ->
(bv_unsigned a2 + zlength s + 1 + zlength slack <= lo \/ usp <= bv_unsigned a2) ->
band_lo <= lo -> lo <= usp - 112 - PCOMMON_STACK -> usp < 2^64 ->
pc_hyp AFMT_read_error m lo usp a2 a3 a4 a5 a6 a7.
Proof.  unfold AFMT_read_error, PCOMMON_STACK. pc_hyp_s printf_common_read_error. Qed.
Lemma pc_hyp_too_big : forall m lo usp (a2 a3 a4 a5 a6 a7 : word),
band_lo <= lo -> lo <= usp - 112 - PCOMMON_STACK -> usp < 2^64 ->
pc_hyp AFMT_too_big m lo usp a2 a3 a4 a5 a6 a7.
Proof.
unfold AFMT_too_big, PCOMMON_STACK. intros until a7; intros CEIL LO UR.
unfold pc_hyp; intros until m'; intros ISH' MI' ST' VA' MU' WM'.
eapply printf_common_too_big; [exact ISH'| exact MI'| rewrite unsigned_lit by lia; exact ST'| exact CEIL| rewrite unsigned_lit by lia; unfold PCOMMON_STACK; lia].
Qed.

Local Ltac fg_sides0 PCH PIECES ARGS :=
lazymatch goal with
| |- pc_hyp _ _ _ _ _ _ _ _ _ _ => PCH
| |- stderr_wfile _ => assumption
| |- ISH _ => assumption
| |- bytes_at _ _ _ _ => apply fmt_bytes_at; [assumption | vm_compute; reflexivity | unfold AFMT_usage, AFMT_cannot_open, AFMT_read_error, AFMT_too_big; lia | vm_compute; discriminate]
| |- Forall _ _ => apply forall_range_b; vm_compute; reflexivity
| |- pass1_ok _ = true => vm_compute; reflexivity
| |- args_ok _ _ _ _ _ _ _ _ _ => ARGS
| |- printf_pieces _ _ = _ => PIECES
| |- fp_calls _ _ _ = [] => vm_compute; reflexivity
| |- stk _ _ _ _ => assumption
| |- ssp_cells _ _ => assumption
| |- mem_inv _ _ => assumption
| |- frm0 _ => assumption
| |- @eq (bv 64) _ _ => assumption
| |- ?a <= ?b => tryif has_var (a <= b) then lia else (vm_compute; discriminate)
end.
Local Ltac fg_sides PCH PIECES ARGS := lazymatch goal with |- ?G => first [ fg_sides0 PCH PIECES ARGS | idtac "FAILED:" G; fail ] end.

Theorem fprintf_diag_proof' : forall (d : diag_msg)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
stderr_wfile m -> ISH m ->
a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
implM asegs (s_diag (St:=St) d) st
(fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4fd70) fc None m (seg_rom asegs)).
Proof using FLS FWE BAND.
intros d. intros until canary. intros SF ISH0 Ha0 DA ST LO GLO QHI SSP MI FRM.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
unfold FPRINTF_DEPTH, GLOBALS_TOP in *.
assert (CEIL : band_lo <= lo) by (idtac; exact GLO).

assert (BR : forall ps, Qpj5.Mq1.implM asegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
(fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x4fd70) fc None m (seg_rom asegs)) ->
Forall (fun p => zlength p <= OUT_MAX) ps ->
Qpj5.Mq1.implM asegs (stderr_fprintf ps) st
(fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x4fd70) fc None m (seg_rom asegs))).
{ intros ps H SH. unfold stderr_fprintf, Qpj5.Mq1.implM in *.
eapply impl_epost_mono.
- eapply (stderr_bridge asegs ps [] st (fun s' ms' => fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt s' ms') _ SH).
eapply impl_mono; [eapply (impl_tforall asegs (at_node asegs) _ _ _ _ (outsk_flush_leaves ps [] st)); exact H|].
intros [|[[] [b s']]] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I|]. eapply vf_to_diag_post; [exact H1 | exact H2].
- intros [[] s'] ms' H'. exact H'. }
pose proof fprintf_icpt_gen as FG. cbv zeta in FG. unfold VF_FRAME, FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, fprintf_stub in FG.
destruct d as [argv0 | path | path | | | |]; cbn [diag_args] in DA; try contradiction; unfold s_diag;
(apply BR; clear BR;
[| try (destruct DA as (_ & _ & _ & _ & _ & LEN & _)); unfold OUT_MAX in *;
unfold pieces_usage, pieces_cannot_open, pieces_read_error, pieces_too_big;
repeat (apply Forall_cons; [first [unfold zlength in *; lia | vm_compute; discriminate] |]); apply Forall_nil ]).
- destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA & G47). unfold GLOBALS_TOP in GA.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length argv0) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB.
assert (SZ : szone (bv_unsigned a2) (zlength argv0 + 1)) by (unfold szone; idtac; lia).
unfold OUT_MAX in LEN. unfold zlength in *.
eapply FG with (fmt := FMT_usage) (args := [PA_s argv0]) (A := AFMT_usage); clear FG.
all: fg_sides ltac:(eapply pc_hyp_usage; [exact BY| exact HF| exact SZ| unfold zlength; lia| unfold zlength; exact DJ| exact CEIL| unfold PCOMMON_STACK; lia| lia]) ltac:(apply printf_pieces_usage; unfold zlength, INT_MAX, OUT_MAX in *; lia) ltac:(cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; split; [exact BY|]; split; [exact HF|]; split; [exact SLK|]; split; [lia|]; split; [exact SZ|]; lia).
- destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA & G47). unfold GLOBALS_TOP in GA.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length path) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB.
assert (SZ : szone (bv_unsigned a2) (zlength path + 1)) by (unfold szone; idtac; lia).
unfold OUT_MAX in LEN. unfold zlength in *.
eapply FG with (fmt := FMT_cannot_open) (args := [PA_s path]) (A := AFMT_cannot_open); clear FG.
all: fg_sides ltac:(eapply pc_hyp_cannot_open; [exact BY| exact HF| exact SZ| unfold zlength; lia| unfold zlength; exact DJ| exact CEIL| unfold PCOMMON_STACK; lia| lia]) ltac:(apply printf_pieces_cannot_open; unfold zlength, INT_MAX, OUT_MAX in *; lia) ltac:(cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; split; [exact BY|]; split; [exact HF|]; split; [exact SLK|]; split; [lia|]; split; [exact SZ|]; lia).
- destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA & G47). unfold GLOBALS_TOP in GA.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length path) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB.
assert (SZ : szone (bv_unsigned a2) (zlength path + 1)) by (unfold szone; idtac; lia).
unfold OUT_MAX in LEN. unfold zlength in *.
eapply FG with (fmt := FMT_read_error) (args := [PA_s path]) (A := AFMT_read_error); clear FG.
all: fg_sides ltac:(eapply pc_hyp_read_error; [exact BY| exact HF| exact SZ| unfold zlength; lia| unfold zlength; exact DJ| exact CEIL| unfold PCOMMON_STACK; lia| lia]) ltac:(apply printf_pieces_read_error; unfold zlength, INT_MAX, OUT_MAX in *; lia) ltac:(cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; split; [exact BY|]; split; [exact HF|]; split; [exact SLK|]; split; [lia|]; split; [exact SZ|]; lia).
- destruct DA as [Ha1 Hu]. pose proof (bv_unsigned_in_range 64 a2) as R2.
eapply FG with (fmt := FMT_too_big) (args := [PA_u 67108864]) (A := AFMT_too_big); clear FG.
all: fg_sides ltac:(eapply pc_hyp_too_big; [exact CEIL| unfold PCOMMON_STACK; lia| lia]) ltac:(apply printf_pieces_too_big) ltac:(cbn [args_ok arg_ok]; split; [split; [lia | exact Hu] | exact I]).
Qed.
End FprintfIcpt.

Theorem fprintf_diag_proof {BAND : Band} : forall St : Type, @fprintf_diag_stmt _ St.
Proof.
intros St. unfold fprintf_diag_stmt. intros d. intros until canary. intros FWE FLS. intros.
eapply (fprintf_diag_proof' FWE FLS); eassumption.
Qed.
