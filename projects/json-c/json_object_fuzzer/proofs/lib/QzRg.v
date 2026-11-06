(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Qpj5 QvDJ Q6sh QQwg QKTr QJBH QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QNQk QSsj Qu1d QpY2 QTVW QqLk QnRU Q9Ho QmP7 QYyZ QmvA QUnM QpME Qu3b QkZz QteI QQ8H Qx6U QcA6 Qo6W QkJ4 QVo2 QsDw QcYs QcfN QlES QUYN Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QNQk.Mq2 QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QpY2.Mq3 QqLk QnRU.Mqa Q9Ho.Mq2 QmP7.Mq0 QYyZ.Mq0 Q9Ho.Mq1 QmvA.Mq0 QYyZ.Mq3.
Import QUnM QpME.Mq0.
Import QYyZ.Mq5.
Import Qu3b.Mq2 QnRU.Mq8 QmvA.Mq3 QkZz.Mq1 QteI.Mq9 QQ8H.Mq3 Qx6U.Mq4 QcA6.Mq1 Qo6W.Mq1.
Import QpME.Mq1 QkJ4 QVo2 QsDw.Mq0 QcYs.Mq3.
Import QcfN.Mq1 QpY2.Mq2.
Import QlES.
Import QUYN.Mq0.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_3 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_4 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Definition realloc_stub : Z := 0x632d0.
Definition asan_realloc_entry : Z := 0x3fad0.
Definition REALLOC_PC : Z := 0x63a44.

Definition rl_pre_W (bp T : Z) : list (Z * Z) :=
[(bp - 2144 - 144, bp); (IA_FLAG, IA_FLAG + 4); (IA, IA + 8); (IA_MAP1, IA_MAP1 + 262144); (0x0130d40, 0x171d30); (T + 3168, T + 3169)].

Definition realloc_pre_post {BAND : Band} (RE : aentry) (X : rlay) (ra : word) (bp : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo A0 n : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (sz : Z) (q : list word) (rest junk8 junk8b : list byte),
ms' = MS (mkR (wz 0x63ab4) (wz (bp + -2144)) gp (wz A_TP) t0 t1 t2 (wz bp) (wz n) (wz A0) (wz n) (wz (bp + -2136)) a3 a4 a5 a6 a7
(wz A0) (wz REALLOC_PC) (wz 1) (wz (bp + -2136)) (wz (bp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz asan_realloc_entry) fc None m' (seg_rom asegs)
/\ munch (rl_pre_W bp (rl_T X)) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bp + -2144)
/\ rw_cells asegs m' (bp - 2144) [CB 8 junk8b]
/\ rw_cells asegs m' (bp - 2136) (unw_obj (bp - 2136) sz q rest bp) /\ length q = 5%nat
/\ 1 <= sz <= 30
/\ rw_cells asegs m' (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ RTconst RE X m' /\ ia_inv m' /\ rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)].

Section Pre.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Lemma realloc_icpt_pre : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A0 n : Z),
RTconst RE X m -> rlay_ok RE X -> ia_inv m -> rw_cells asegs m (rl_T X + 3168) [C1 (b8 0)] -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - 2144 - 144 -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp ->
0 <= A0 < 2^47 -> 0 <= n < 2^64 ->
evt asegs (realloc_pre_post RE X ra bp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A0 n m)
(MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz A0) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz realloc_stub) fc None m (seg_rom asegs)).
Proof.
intros until n; intros RT RL IAI TU MI ST CEIL LO BPR UNW HA Hn.
pose proof CEIL as CEIL'. idtac. change (2^64) with 18446744073709551616 in BPR. change (2^47) with 140737488355328 in HA.
pose proof (QSsj.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD. idtac. rewrite ?KHI_eq in TK.

pose proof (munch_refl [(bp - 2144 - 144, bp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (RTW0 : Forall (rt_avoid RE X) [(bp - 2144 - 144, bp)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor]. }
assert (RTW : Forall (rt_avoid RE X) [(bp - 2144 - 144, bp); (1570184, 1570184 + 4); (986368, 986368 + 8); (986376, 986376 + 262144); (0x0130d40, 0x171d30); (rl_T X + 3168, rl_T X + 3169)]).
{ pose proof (@ia_W_rt BAND RE X (bp - 2144) ltac:(unfold INTALLOC_STACK; lia) RL) as FW. unfold ia_W, IA_FLAG, IA, IA_MAP1, INTALLOC_STACK in FW.
inversion FW as [|? ? R1 X1]; inversion X1 as [|? ? R2 X2]; inversion X2 as [|? ? R3 X3]; inversion X3 as [|? ? R4 X4]; inversion X4 as [|? ? R5 X5]; subst.
constructor; [exact (rt_avoid_stack RE X RL (bp - 2144 - 144) bp ltac:(lia))|].
constructor; [exact R2|]. constructor; [exact R3|]. constructor; [exact R4|]. constructor; [exact R5|].
constructor; [exact (rt_avoid_Thigh RE X (rl_T X + 3168) (rl_T X + 3169) RL ltac:(lia) ltac:(lia))| constructor]. }
unfold A_INSTANCE in *. unfold realloc_stub.
step.
carve_frame 2032%nat ST.
do 9 step.
step.
step.
carve_frame 112%nat ST.
step. step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW0]) end.
call_ch (try_asan_init_spec RE X) ltac:(fun PO => rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RT1| exact RL| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST1 end.
match goal with H : RTconst RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RT2 end. clear RT1.
step. if_lit.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (IA1 : ia_inv mc) by (eapply (ia_inv_agree (fun z => 0x10000 <= z < 0x645000)); [| exact IAI| intros z Hz; unfold IA, IA_FLAG in Hz; cbn beta; lia];
eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Hz _; cbn [outside]; lia)
end.

apply (munch_weaken _ [(bp - 2144 - 144, bp); (1570184, 1570184 + 4); (986368, 986368 + 8); (986376, 986376 + 262144); (0x0130d40, 0x171d30); (rl_T X + 3168, rl_T X + 3169)]) in MU.
2:{ intros z Hz. cbn [outside] in Hz |- *. clear - Hz. tauto. }
step.
call_ch (intalloc_spec RE X) ltac:(fun PO => unfold ia_W, INTALLOC_STACK, IA_FLAG, IA, IA_MAP1 in PO; rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
try eassumption; try (rewrite ?unsigned_lit by lia; first [eassumption| unfold INTALLOC_STACK; lia]).
subst.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with H : RTconst RE X mc |- _ => rename H into RT2b end;
lazymatch goal with H : ia_inv mc |- _ => rename H into IA2 end;
pose proof (munch_refl [(bp - 2144 - 144, bp); (rl_T X + 3168, rl_T X + 3169)] mc) as MU3;
pose proof (wmono_refl asegs mc) as WM3 end.

step.
rewrite (unsigned_lit A0) by lia. rewrite (Z.shiftr_div_pow2 A0 47) by lia. rewrite (Z.div_small A0 (2^47)) by (change (2^47) with 140737488355328; lia).
step. if_lit.
step.
rewrite (unsigned_lit A0) by lia. rewrite (Z.shiftr_div_pow2 A0 32) by lia. change (2^32) with 4294967296.
assert (QH : 0 <= A0 / 4294967296 < 32768) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
step.
rewrite (unsigned_lit (A0 / 4294967296)) by lia. rewrite (Z.shiftl_mul_pow2 (A0 / 4294967296) 3) by lia. change (2^3) with 8.
step.
pose proof IA2 as (b0 & FL & B01 & ZMAP & ZR). unfold IA_MAP1 in ZMAP.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HR : ov_read_bytes asegs mc (wa (986376 + (A0 / 4294967296 * 8))) 8 = Some (le8 (wz 0)))
by (eapply zbytes_load8; [exact ZMAP| lia| lia]) end.
step.
clear HR b0 FL B01 ZMAP ZR.
step.
step. if_lit.

step. step. step. step. step. step. step.
stf.
step.
stf.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT3 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
stp. step. if_lit.
step. call0 (get_current_pc_spec); []. subst_words.
rtc RT3 19%nat K19. rtc RT3 15%nat K15.
step. step.
stp.
step.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
step. stp. stp.
step.
rewrite (unsigned_lit bp), and_all_ones by lia.
stp.
step.
step. if_lit.
step. step. step. step. stp. step.

apply (proj1 (rw_cells_app asegs _ _ [CB 1952 _; C8 (wz bp)] _)) in FR as [FRa FRb].
lazymatch type of FRb with rw_cells _ _ ?a _ => replace a with (bp + -72) in FRb by (cbn; lia) end.
apply (proj1 (rw_cells_app asegs _ _ [CB 8 _] _)) in FR0 as [J8 FR0].
lazymatch type of FR0 with rw_cells _ _ ?a _ => replace a with (bp + -2136) in FR0 by (cbn; lia) end.
replace (bp + -2032) with (bp + -2136 + 104) in FRa by lia.
replace (bp + -2120) with (bp + -2136 + 16) in FR0 by lia.
destruct (bst_assemble88 _ _ _ _ _ FR0 FRa) as (q0 & q1 & q2 & q3 & q4 & rest & OBJ). rewrite (unsigned_lit bp) in OBJ by lia. clear FR0 FRa.
pose proof FRb as FRc. apply (proj1 (rw_cells_app asegs _ _ [CB 8 _; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _)) in FRc as [_ FRc].
lazymatch type of FRc with rw_cells _ _ ?a _ => replace a with (bp - 16) in FRc by (cbn; lia) end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT4 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end. clear RT3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (URD : unw_readable asegs RE mc (bp - 16)) end.
{ eapply (unw_readable_prologue RE _ m _ bp s0 ra); [exact MU| intros z Hz; cbn [outside]; lia| exact FRc| exact UNW]. }
clear FRc.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ST' : stk asegs mc lo (bv_unsigned (wz (bp + -2144)))) by (rewrite unsigned_lit by lia; exact ST1);
assert (LO' : lo <= bv_unsigned (wz (bp + -2144)) - unwind_stack) by (rewrite unsigned_lit by lia; unfold unwind_stack; lia);
assert (OLO' : bv_unsigned (wz (bp + -2144)) <= bp + -2136) by (rewrite unsigned_lit by lia; lia);
assert (MI' : mem_inv asegs mc) by assumption
end.
eapply evt_cut.
{ eapply (unwind_impl_spec RE X);
[exact RT4| exact RL| exact MI'| exact ST'| exact CEIL'| exact LO'| exact OBJ| exact TU| exact URD| unfold REALLOC_PC; lia
| exact OLO'| lia| lia]. }
clear ST' LO' OLO' MI'.
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MUd & WMd & MId & STd
& sz & q & rest' & OBJ3 & LQ & TU3 & SZB & RT5).
unfold unwind_stack in MUd. rewrite !(unsigned_lit (bp + -2144)) in MUd, STd by lia.
clear OBJ TU URD RT4.
lazymatch type of MUd with munch _ ?mx _ =>
apply (munch_chain' _ mx m3 _ m MUd) in MU; [| sub_fp_solve];
apply (munch_chain' _ mx m3 _ _ MUd) in MU3; [| sub_fp_solve];
transport_after_call asegs mx m3 MUd WMd; clear MUd WMd end.
replace (ret_pc (wz 408224)) with (wz 408224) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

step. step. step. step.
step.
apply evt_done. unfold realloc_pre_post.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
assert (IA3 : ia_inv mf)
by (eapply (ia_inv_agree (fun z => 0x10000 <= z < 0x645000)); [| exact IA2| intros y Hy; unfold IA, IA_FLAG in Hy; cbn beta; lia];
eapply agree_on_of_munch; [exact MU3| exact WM3|]; intros y Hy _; cbn [outside]; lia) end.
lazymatch type of FRb with rw_cells _ _ _ (CB 8 ?j8 :: _) => lazymatch type of J8 with rw_cells _ _ _ [CB 8 ?j8b] =>
do 12 eexists; exists m3, sz, q, rest', j8, j8b end end.
split; [reflexivity|]. split; [unfold rl_pre_W, IA_FLAG, IA, IA_MAP1; exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact STd|].
split; [replace (bp - 2144) with (bp + -2144) by lia; exact J8|].
split; [replace (bp - 2136) with (bp + -2136) by lia; exact OBJ3|]. split; [exact LQ|]. split; [exact SZB|].
split; [exact FRb|]. split; [exact RT5|]. split; [exact IA3| exact TU3].
Qed.
End Pre.

Definition rl_p2_W (sp T : Z) : list (Z * Z) := [(sp - 64 - 32, sp); (T + 2856, T + 2872)].

Section P2.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma RStats_realloc_words : forall m, RStats RE X m -> exists w1 w2 : word, rw_cells asegs m (rl_T X + 2856) [C8 w1; C8 w2].
Proof.
intros m (HJ & _). apply hjunk_C8x2.
destruct (hjunk_split m _ (rl_T X + 2856) _ HJ ltac:(lia)) as [_ H2].
destruct (hjunk_split m _ (rl_T X + 2856 + 16) _ H2 ltac:(lia)) as [H3 _]. exact H3.
Qed.

Lemma realloc_p2 : forall (ra : word) (sp : Z) (gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A0 n obj : Z) (Q : machine_state -> Prop),
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> mem_inv asegs m ->
stk asegs m lo sp -> band_lo <= lo -> lo <= sp - 64 - 32 -> 0 <= sp < 2^64 ->
0 < A0 < 2^64 -> 0 < n < 2^64 -> 0 <= obj < 2^64 ->
(forall m' (u0 u1 u2 u6 u7 u10 u11 u12 u13 : word) (j8 : list byte),
munch (rl_p2_W sp (rl_T X)) m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo (sp + -64) ->
rw_cells asegs m' (sp + -16) [CB 8 j8; C8 ra] ->
rw_cells asegs m' (sp + -64) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (wz 0x3fb6c)] ->
RTconst RE X m' -> RStats RE X m' ->
evt asegs Q (MS (mkR (wz 0x3fbe8) (wz (sp + -64)) gp (wz A_TP) u0 u1 u2 (wz obj) (wz A0) (wz A_INSTANCE) (wz n) (wz 8) (wz obj) (wz 1) (wz 1) u6 u7
(wz A_INSTANCE) (wz n) s4 s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13)
F (wz allocate_entry) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz sp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz A0) (wz n) (wz obj) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz asan_realloc_entry) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RL RS MI ST CEIL LO SPR HA Hn HO CONT.
pose proof CEIL as CEIL'. idtac. change (2^64) with 18446744073709551616 in *.
pose proof (QSsj.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
pose proof (munch_refl (rl_p2_W sp (rl_T X)) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold rl_p2_W in MU.
assert (RTW : Forall (rt_avoid RE X) [(sp - 64 - 32, sp); (rl_T X + 2856, rl_T X + 2872)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|]. constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor]. }
assert (STW : Forall st_avoid [(sp - 64 - 32, sp); (rl_T X + 2856, rl_T X + 2872)]).
{ constructor; [st_avoid_solve|]. constructor; [st_avoid_solve| constructor]. }
unfold asan_realloc_entry, A_INSTANCE in *.
carve_frame 16%nat ST.
step. stf.
step. step.
step. unfold_cond; cond_unsig; if_false.
step.
step. unfold_cond; cond_unsig; if_true.
step. stp. step. step.
step.
carve_frame 48%nat ST.
step. stf. do 5 step.
step. unfold_cond; cond_unsig; if_false.
step.
step. unfold_cond; cond_unsig; if_false.
step. step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_ch (get_thread_stats_spec RE X) ltac:(fun PO => rewrite !(unsigned_lit (sp + -64)) in PO by lia);
[exact RT1| exact RL| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST1 end.
match goal with H : RTconst RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RT2 end. clear RT1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RS1 : RStats RE X mc) by (eapply RStats_munch; [exact RS| exact MU| exact WM| exact STW]) end.
destruct (RStats_realloc_words _ RS1) as (w1 & w2 & STC).
step. step.
step. step.
step. step.
step. step. step. step. step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT3 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]);
assert (RS3 : RStats RE X mc) by (eapply RStats_munch; [exact RS| exact MU| exact WM| exact STW]) end.
eapply CONT; [exact MU| exact WM| assumption| exact ST1| exact FR| exact FR0| exact RT3| exact RS3].
Qed.
End P2.

Section P3.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Hypothesis OBL_RT_GOT_MEMCPY : forall m, RTconst RE X m -> ro_cells asegs m 0x0e5de0 [C8 (wz 0x0e7da8)].
Hypothesis OBL_MEMCPY : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv asegs m ->
evt asegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb34c) fc None m (seg_rom asegs)).

Lemma realloc_p3 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (A0 n0' A n obj b1 : Z) (id : word) (src ujunk : list byte) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m ->
rw_cells asegs m (A0 + -16) (hdr_cells b1 n0' id) ->
0 < n0' < 2^32 -> 0 < n < 2^32 -> 0 < A < 2^63 -> 16 <= A0 < 2^63 -> 0 <= obj < 2^64 ->
bytes_at asegs m A0 src -> length src = Z.to_nat (Z.min n n0') ->
rw_cells asegs m A [CB (Z.to_nat (Z.min n n0')) ujunk] ->
(A0 + Z.min n n0' <= A \/ A + Z.min n n0' <= A0) ->
(forall m' (u0 u1 u2 u6 u7 u10 u11 u12 u13 s3' : word),
munch [(A, A + Z.min n n0')] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' A [CB (Z.to_nat (Z.min n n0')) src] -> bytes_at asegs m' A0 src ->
evt asegs Q (MS (mkR (wz 0x3fc7c) sp gp tp u0 u1 u2 (wz obj) (wz A0) (wz A_INSTANCE) (wz A0) (wz 0) (wz 0) (wz obj) (wz 1) u6 u7
(wz A_INSTANCE) s3' (wz A) s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13)
F (wz 0x3ed54) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR (wz 0x3fbe8) sp gp tp t0 t1 t2 (wz obj) (wz A0) (wz A) a1 a2 a3 a4 a5 a6 a7
(wz A_INSTANCE) (wz n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3fbe8) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI HDR Hn0 Hn HA HA0 HO SRC LSRC UC SEP CONT.
change (2^64) with 18446744073709551616 in *. change (2^63) with 9223372036854775808 in *. change (2^32) with 4294967296 in *.
unfold hdr_cells in HDR. unfold A_INSTANCE in *.
step.
step. unfold_cond; cond_unsig; if_false.
step.
step.
step.
step. if_lit.
rtc RT 23%nat K23. pose proof (OBL_RT_GOT_MEMCPY _ RT) as KG.
step. step. step.
step. if_lit.
step. step.
change (zx16 (wz 0)) with (wz 0). rewrite (zx32_small n0') by lia.
step. step.
rewrite (unsigned_lit n0') by lia. rewrite ?(unsigned_lit 0) by lia. rewrite ?Z.shiftl_0_l. rewrite Z.lor_0_l.
step.
destruct (Z_lt_ge_dec n n0') as [LT|GE];
[ unfold_cond; cond_unsig; if_true; rewrite (Z.min_l n n0') in * by lia
| unfold_cond; cond_unsig; if_false; step; rewrite (Z.min_r n n0') in * by lia ].
all: step; step; step.
all: step.
all: (eapply evt_cut; [eapply (OBL_MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m src ujunk);
[rewrite !unsigned_lit by lia; exact SRC| rewrite !unsigned_lit by lia; exact LSRC
| rewrite !unsigned_lit by lia; exact UC| rewrite !unsigned_lit by lia; lia| assumption]|]).
all: intros ms'' PO; unfold memcpy_post in PO; rewrite !unsigned_lit in PO by lia.
all: destruct PO as (v0 & v1 & v2 & pw1 & pw2 & pw3 & pw4 & pw5 & pw6 & pw7 & v3 & v4 & v5 & v6 & m4 & -> & MU4 & WM4 & MI4 & UC4 & SRC4).
all: replace (ret_pc (wz 261216)) with (wz 261216) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
all: step; step; step; step; step; step.
all: step.
all: eapply CONT; [exact MU4| exact WM4| exact MI4| exact UC4| exact SRC4].
Qed.
End P3.

Section Epi.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma rl_frame_all : forall mx bp sz (q : list word) (rest junk8 junk8b : list byte) (ra s0 s1 s2 s3 s4 s5 s6 : word),
length q = 5%nat ->
rw_cells asegs mx (bp + -2144) [CB 8 junk8b] -> rw_cells asegs mx (bp + -2136) (unw_obj (bp + -2136) sz q rest bp) ->
rw_cells asegs mx (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mx (bp + -2144) ([CB 8 junk8b] ++ unw_obj (bp + -2136) sz q rest bp ++ [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Proof.
intros mx bp sz q rest junk8 junk8b ra s0 s1 s2 s3 s4 s5 s6 LQ O0 O1 O2.
apply (proj2 (rw_cells_app asegs mx _ [CB 8 junk8b] _)). split; [exact O0|]. cbn [cells_size csize Nat.add].
replace (bp + -2144 + Z.of_nat 8) with (bp + -2136) by lia.
apply (proj2 (rw_cells_app asegs mx _ _ _)). split; [exact O1|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try lia.
unfold unw_obj. cbn [cells_size csize Nat.add map app length]. replace (bp + -2136 + Z.of_nat 2064) with (bp + -72) by lia. exact O2.
Qed.

Lemma realloc_epi : forall (ra : word) (bp : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x0 x1 x2 x3 x5 x6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(y1 y2 y3 y4 y5 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo R sz : Z) (q : list word) (rest junk8 junk8b j8 : list byte),
mem_inv asegs m -> 0 <= bp < 2^64 -> stk asegs m lo (bp + -2208) -> lo <= bp - 2208 -> 0 < R < 2^64 ->
rw_cells asegs m (bp + -2208) [C8 y5; C8 y4; C8 y3; C8 y2; C8 y1; C8 (wz 0x3fb6c)] ->
rw_cells asegs m (bp + -2160) [CB 8 j8; C8 (wz 0x63ab4)] ->
rw_cells asegs m (bp + -2144) [CB 8 junk8b] -> rw_cells asegs m (bp + -2136) (unw_obj (bp + -2136) sz q rest bp) -> length q = 5%nat ->
rw_cells asegs m (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs (fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word),
ms' = MS (mkR ra (wz bp) gp tp t0 t1 t2 s0 s1 (wz R) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)
/\ stk asegs m lo bp)
(MS (mkR (wz 0x3fc7c) (wz (bp + -2208)) gp tp t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 (wz R) x5 x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3fc7c) fc None m (seg_rom asegs)).
Proof.
intros until j8; intros MI BPR ST LO HR FR48 FR16 J8 OBJ LQ FRS.
change (2^64) with 18446744073709551616 in *.
step.
do 6 step.
step.
release_frame FR48 ST (bp + -2160).
step.
replace (ret_pc (wz 260972)) with (wz 260972) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. unfold_cond; cond_unsig; if_false.
step. step.
release_frame FR16 ST (bp + -2144).
step.
replace (ret_pc (wz 408244)) with (wz 408244) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 8 step. step.
pose proof (rl_frame_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LQ J8 OBJ FRS) as FRX. clear OBJ FRS J8.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try lia. unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST bp.
step.
apply evt_done. do 7 eexists. split; [reflexivity| exact ST].
Qed.

Definition rl_null_W (bp : Z) : list (Z * Z) := [(bp - 2176, bp - 2160); (A_ERRNO, A_ERRNO + 4)].

Lemma realloc_epi_null : forall (ra : word) (bp : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 x6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(y1 y2 y3 y4 y5 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo sz : Z) (q : list word) (rest junk8 junk8b j8 : list byte),
RStats RE X m -> mem_inv asegs m -> 0 <= bp < 2^64 -> stk asegs m lo (bp + -2208) -> band_lo <= lo -> lo <= bp - 2208 ->
rw_cells asegs m (bp + -2208) [C8 y5; C8 y4; C8 y3; C8 y2; C8 y1; C8 (wz 0x3fb6c)] ->
rw_cells asegs m (bp + -2160) [CB 8 j8; C8 (wz 0x63ab4)] ->
rw_cells asegs m (bp + -2144) [CB 8 junk8b] -> rw_cells asegs m (bp + -2136) (unw_obj (bp + -2136) sz q rest bp) -> length q = 5%nat ->
rw_cells asegs m (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra (wz bp) gp (wz A_TP) t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (rl_null_W bp) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo bp /\ RStats RE X m')
(MS (mkR (wz 0x3fbe8) (wz (bp + -2208)) gp (wz A_TP) t0 t1 t2 x0 x1 (wz 0) a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3fbe8) fc None m (seg_rom asegs)).
Proof.
intros until j8; intros RS MI BPR ST CEIL LO FR48 FR16 J8 OBJ LQ FRS.
pose proof CEIL as CEIL'. idtac. change (2^64) with 18446744073709551616 in *.
pose proof (munch_refl (rl_null_W bp) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold rl_null_W, A_ERRNO in MU.
step.
step. if_lit.
step.
do 6 step.
step.
release_frame FR48 ST (bp + -2160).
step.
replace (ret_pc (wz 260972)) with (wz 260972) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_lit.
step.
call_ch (set_errno_spec RE X) ltac:(fun PO => unfold A_ERRNO in PO; rewrite !(unsigned_lit (bp + -2160)) in PO by lia);
[exact RS| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST4 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS4 end.
step.
step.
step. step.
release_frame FR16 ST4 (bp + -2144).
step.
replace (ret_pc (wz 408244)) with (wz 408244) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 8 step. step.
pose proof (rl_frame_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LQ J8 OBJ FRS) as FRX. clear OBJ FRS J8.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try lia. unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST4 bp.
step.
apply evt_done. do 14 eexists. lazymatch type of ST4 with stk _ ?mm _ _ => exists mm end.
split; [reflexivity|]. split; [unfold rl_null_W, A_ERRNO; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST4| exact RS4].
Qed.
End Epi.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4g.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4g. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV3O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV3O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mql. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmvA.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXcn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmvA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkZz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkZz.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ8H.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ8H.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx6U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx6U.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcA6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo6W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo6W.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpF1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVo2.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsDw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsDw.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcYs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcYs.Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcfN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcfN.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUYN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUYN.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_3 segs m a bs := transport_chunks_zb segs m a bs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_4 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Definition realloc_stub : Z := 0x636a8.
Definition asan_realloc_entry : Z := 0x3fcfc.
Definition REALLOC_PC : Z := 0x63e1c.

Definition rl_pre_W (bp T : Z) : list (Z * Z) :=
[(bp - 2144 - 144, bp); (IA_FLAG, IA_FLAG + 4); (IA, IA + 8); (IA_MAP1, IA_MAP1 + 262144); (0x0133400, 0x1743f0); (T + 3168, T + 3169)].

Definition realloc_pre_post {BAND : Band} (RE : aentry) (X : rlay) (ra : word) (bp : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo A0 n : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (sz : Z) (q : list word) (rest junk8 junk8b : list byte),
ms' = MS (mkR (wz 0x63e8c) (wz (bp + -2144)) gp (wz A_TP) t0 t1 t2 (wz bp) (wz n) (wz A0) (wz n) (wz (bp + -2136)) a3 a4 a5 a6 a7
(wz A0) (wz REALLOC_PC) (wz 1) (wz (bp + -2136)) (wz (bp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz asan_realloc_entry) fc None m' (seg_rom asegs)
/\ munch (rl_pre_W bp (rl_T X)) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bp + -2144)
/\ rw_cells asegs m' (bp - 2144) [CB 8 junk8b]
/\ rw_cells asegs m' (bp - 2136) (unw_obj (bp - 2136) sz q rest bp) /\ length q = 5%nat
/\ 1 <= sz <= 30
/\ rw_cells asegs m' (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ RTconst RE X m' /\ ia_inv m' /\ rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)].

Section Pre.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Lemma realloc_icpt_pre : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A0 n : Z),
RTconst RE X m -> rlay_ok RE X -> ia_inv m -> rw_cells asegs m (rl_T X + 3168) [C1 (b8 0)] -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - 2144 - 144 -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp ->
0 <= A0 < 2^47 -> 0 <= n < 2^64 ->
evt asegs (realloc_pre_post RE X ra bp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A0 n m)
(MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz A0) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz realloc_stub) fc None m (seg_rom asegs)).
Proof.
intros until n; intros RT RL IAI TU MI ST CEIL LO BPR UNW HA Hn.
pose proof CEIL as CEIL'. idtac. change (2^64) with 18446744073709551616 in BPR. change (2^47) with 140737488355328 in HA.
pose proof (QKBN.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD. idtac. rewrite ?KHI_eq in TK.

pose proof (munch_refl [(bp - 2144 - 144, bp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (RTW0 : Forall (rt_avoid RE X) [(bp - 2144 - 144, bp)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor]. }
assert (RTW : Forall (rt_avoid RE X) [(bp - 2144 - 144, bp); (1580104, 1580104 + 4); (996288, 996288 + 8); (996296, 996296 + 262144); (0x0133400, 0x1743f0); (rl_T X + 3168, rl_T X + 3169)]).
{ pose proof (@ia_W_rt BAND RE X (bp - 2144) ltac:(unfold INTALLOC_STACK; lia) RL) as FW. unfold ia_W, IA_FLAG, IA, IA_MAP1, INTALLOC_STACK in FW.
inversion FW as [|? ? R1 X1]; inversion X1 as [|? ? R2 X2]; inversion X2 as [|? ? R3 X3]; inversion X3 as [|? ? R4 X4]; inversion X4 as [|? ? R5 X5]; subst.
constructor; [exact (rt_avoid_stack RE X RL (bp - 2144 - 144) bp ltac:(lia))|].
constructor; [exact R2|]. constructor; [exact R3|]. constructor; [exact R4|]. constructor; [exact R5|].
constructor; [exact (rt_avoid_Thigh RE X (rl_T X + 3168) (rl_T X + 3169) RL ltac:(lia) ltac:(lia))| constructor]. }
unfold A_INSTANCE in *. unfold realloc_stub.
step.
carve_frame 2032%nat ST.
do 9 step.
step.
step.
carve_frame 112%nat ST.
step. step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW0]) end.
call_ch (try_asan_init_spec RE X) ltac:(fun PO => rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RT1| exact RL| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST1 end.
match goal with H : RTconst RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RT2 end. clear RT1.
step. if_lit.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (IA1 : ia_inv mc) by (eapply (ia_inv_agree (fun z => 0x10000 <= z < 0x647000)); [| exact IAI| intros z Hz; unfold IA, IA_FLAG in Hz; cbn beta; lia];
eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Hz _; cbn [outside]; lia)
end.

apply (munch_weaken _ [(bp - 2144 - 144, bp); (1580104, 1580104 + 4); (996288, 996288 + 8); (996296, 996296 + 262144); (0x0133400, 0x1743f0); (rl_T X + 3168, rl_T X + 3169)]) in MU.
2:{ intros z Hz. cbn [outside] in Hz |- *. clear - Hz. tauto. }
step.
call_ch (intalloc_spec RE X) ltac:(fun PO => unfold ia_W, INTALLOC_STACK, IA_FLAG, IA, IA_MAP1 in PO; rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
try eassumption; try (rewrite ?unsigned_lit by lia; first [eassumption| unfold INTALLOC_STACK; lia]).
subst.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with H : RTconst RE X mc |- _ => rename H into RT2b end;
lazymatch goal with H : ia_inv mc |- _ => rename H into IA2 end;
pose proof (munch_refl [(bp - 2144 - 144, bp); (rl_T X + 3168, rl_T X + 3169)] mc) as MU3;
pose proof (wmono_refl asegs mc) as WM3 end.

step.
rewrite (unsigned_lit A0) by lia. rewrite (Z.shiftr_div_pow2 A0 47) by lia. rewrite (Z.div_small A0 (2^47)) by (change (2^47) with 140737488355328; lia).
step. if_lit.
step.
rewrite (unsigned_lit A0) by lia. rewrite (Z.shiftr_div_pow2 A0 32) by lia. change (2^32) with 4294967296.
assert (QH : 0 <= A0 / 4294967296 < 32768) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
step.
rewrite (unsigned_lit (A0 / 4294967296)) by lia. rewrite (Z.shiftl_mul_pow2 (A0 / 4294967296) 3) by lia. change (2^3) with 8.
step.
pose proof IA2 as (b0 & FL & B01 & ZMAP & ZR). unfold IA_MAP1 in ZMAP.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HR : ov_read_bytes asegs mc (wa (996296 + (A0 / 4294967296 * 8))) 8 = Some (le8 (wz 0)))
by (eapply zbytes_load8; [exact ZMAP| lia| lia]) end.
step.
clear HR b0 FL B01 ZMAP ZR.
step.
step. if_lit.

step. step. step. step. step. step. step.
stf.
step.
stf.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT3 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
stp. step. if_lit.
step. call0 (get_current_pc_spec); []. subst_words.
rtc RT3 19%nat K19. rtc RT3 15%nat K15.
step. step.
stp.
step.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
step. stp. stp.
step.
rewrite (unsigned_lit bp), and_all_ones by lia.
stp.
step.
step. if_lit.
step. step. step. step. stp. step.

apply (proj1 (rw_cells_app asegs _ _ [CB 1952 _; C8 (wz bp)] _)) in FR as [FRa FRb].
lazymatch type of FRb with rw_cells _ _ ?a _ => replace a with (bp + -72) in FRb by (cbn; lia) end.
apply (proj1 (rw_cells_app asegs _ _ [CB 8 _] _)) in FR0 as [J8 FR0].
lazymatch type of FR0 with rw_cells _ _ ?a _ => replace a with (bp + -2136) in FR0 by (cbn; lia) end.
replace (bp + -2032) with (bp + -2136 + 104) in FRa by lia.
replace (bp + -2120) with (bp + -2136 + 16) in FR0 by lia.
destruct (bst_assemble88 _ _ _ _ _ FR0 FRa) as (q0 & q1 & q2 & q3 & q4 & rest & OBJ). rewrite (unsigned_lit bp) in OBJ by lia. clear FR0 FRa.
pose proof FRb as FRc. apply (proj1 (rw_cells_app asegs _ _ [CB 8 _; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _)) in FRc as [_ FRc].
lazymatch type of FRc with rw_cells _ _ ?a _ => replace a with (bp - 16) in FRc by (cbn; lia) end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT4 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end. clear RT3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (URD : unw_readable asegs RE mc (bp - 16)) end.
{ eapply (unw_readable_prologue RE _ m _ bp s0 ra); [exact MU| intros z Hz; cbn [outside]; lia| exact FRc| exact UNW]. }
clear FRc.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ST' : stk asegs mc lo (bv_unsigned (wz (bp + -2144)))) by (rewrite unsigned_lit by lia; exact ST1);
assert (LO' : lo <= bv_unsigned (wz (bp + -2144)) - unwind_stack) by (rewrite unsigned_lit by lia; unfold unwind_stack; lia);
assert (OLO' : bv_unsigned (wz (bp + -2144)) <= bp + -2136) by (rewrite unsigned_lit by lia; lia);
assert (MI' : mem_inv asegs mc) by assumption
end.
eapply evt_cut.
{ eapply (unwind_impl_spec RE X);
[exact RT4| exact RL| exact MI'| exact ST'| exact CEIL'| exact LO'| exact OBJ| exact TU| exact URD| unfold REALLOC_PC; lia
| exact OLO'| lia| lia]. }
clear ST' LO' OLO' MI'.
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MUd & WMd & MId & STd
& sz & q & rest' & OBJ3 & LQ & TU3 & SZB & RT5).
unfold unwind_stack in MUd. rewrite !(unsigned_lit (bp + -2144)) in MUd, STd by lia.
clear OBJ TU URD RT4.
lazymatch type of MUd with munch _ ?mx _ =>
apply (munch_chain' _ mx m3 _ m MUd) in MU; [| sub_fp_solve];
apply (munch_chain' _ mx m3 _ _ MUd) in MU3; [| sub_fp_solve];
transport_after_call asegs mx m3 MUd WMd; clear MUd WMd end.
replace (ret_pc (wz 409208)) with (wz 409208) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

step. step. step. step.
step.
apply evt_done. unfold realloc_pre_post.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
assert (IA3 : ia_inv mf)
by (eapply (ia_inv_agree (fun z => 0x10000 <= z < 0x647000)); [| exact IA2| intros y Hy; unfold IA, IA_FLAG in Hy; cbn beta; lia];
eapply agree_on_of_munch; [exact MU3| exact WM3|]; intros y Hy _; cbn [outside]; lia) end.
lazymatch type of FRb with rw_cells _ _ _ (CB 8 ?j8 :: _) => lazymatch type of J8 with rw_cells _ _ _ [CB 8 ?j8b] =>
do 12 eexists; exists m3, sz, q, rest', j8, j8b end end.
split; [reflexivity|]. split; [unfold rl_pre_W, IA_FLAG, IA, IA_MAP1; exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact STd|].
split; [replace (bp - 2144) with (bp + -2144) by lia; exact J8|].
split; [replace (bp - 2136) with (bp + -2136) by lia; exact OBJ3|]. split; [exact LQ|]. split; [exact SZB|].
split; [exact FRb|]. split; [exact RT5|]. split; [exact IA3| exact TU3].
Qed.
End Pre.

Definition rl_p2_W (sp T : Z) : list (Z * Z) := [(sp - 64 - 32, sp); (T + 2856, T + 2872)].

Section P2.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma RStats_realloc_words : forall m, RStats RE X m -> exists w1 w2 : word, rw_cells asegs m (rl_T X + 2856) [C8 w1; C8 w2].
Proof.
intros m (HJ & _). apply hjunk_C8x2.
destruct (hjunk_split m _ (rl_T X + 2856) _ HJ ltac:(lia)) as [_ H2].
destruct (hjunk_split m _ (rl_T X + 2856 + 16) _ H2 ltac:(lia)) as [H3 _]. exact H3.
Qed.

Lemma realloc_p2 : forall (ra : word) (sp : Z) (gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A0 n obj : Z) (Q : machine_state -> Prop),
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> mem_inv asegs m ->
stk asegs m lo sp -> band_lo <= lo -> lo <= sp - 64 - 32 -> 0 <= sp < 2^64 ->
0 < A0 < 2^64 -> 0 < n < 2^64 -> 0 <= obj < 2^64 ->
(forall m' (u0 u1 u2 u6 u7 u10 u11 u12 u13 : word) (j8 : list byte),
munch (rl_p2_W sp (rl_T X)) m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo (sp + -64) ->
rw_cells asegs m' (sp + -16) [CB 8 j8; C8 ra] ->
rw_cells asegs m' (sp + -64) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (wz 0x3fd98)] ->
RTconst RE X m' -> RStats RE X m' ->
evt asegs Q (MS (mkR (wz 0x3fe14) (wz (sp + -64)) gp (wz A_TP) u0 u1 u2 (wz obj) (wz A0) (wz A_INSTANCE) (wz n) (wz 8) (wz obj) (wz 1) (wz 1) u6 u7
(wz A_INSTANCE) (wz n) s4 s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13)
F (wz allocate_entry) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz sp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz A0) (wz n) (wz obj) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz asan_realloc_entry) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RL RS MI ST CEIL LO SPR HA Hn HO CONT.
pose proof CEIL as CEIL'. idtac. change (2^64) with 18446744073709551616 in *.
pose proof (QKBN.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
pose proof (munch_refl (rl_p2_W sp (rl_T X)) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold rl_p2_W in MU.
assert (RTW : Forall (rt_avoid RE X) [(sp - 64 - 32, sp); (rl_T X + 2856, rl_T X + 2872)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|]. constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor]. }
assert (STW : Forall st_avoid [(sp - 64 - 32, sp); (rl_T X + 2856, rl_T X + 2872)]).
{ constructor; [st_avoid_solve|]. constructor; [st_avoid_solve| constructor]. }
unfold asan_realloc_entry, A_INSTANCE in *.
carve_frame 16%nat ST.
step. stf.
step. step.
step. unfold_cond; cond_unsig; if_false.
step.
step. unfold_cond; cond_unsig; if_true.
step. stp. step. step.
step.
carve_frame 48%nat ST.
step. stf. do 5 step.
step. unfold_cond; cond_unsig; if_false.
step.
step. unfold_cond; cond_unsig; if_false.
step. step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_ch (get_thread_stats_spec RE X) ltac:(fun PO => rewrite !(unsigned_lit (sp + -64)) in PO by lia);
[exact RT1| exact RL| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST1 end.
match goal with H : RTconst RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RT2 end. clear RT1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RS1 : RStats RE X mc) by (eapply RStats_munch; [exact RS| exact MU| exact WM| exact STW]) end.
destruct (RStats_realloc_words _ RS1) as (w1 & w2 & STC).
step. step.
step. step.
step. step.
step. step. step. step. step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT3 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]);
assert (RS3 : RStats RE X mc) by (eapply RStats_munch; [exact RS| exact MU| exact WM| exact STW]) end.
eapply CONT; [exact MU| exact WM| assumption| exact ST1| exact FR| exact FR0| exact RT3| exact RS3].
Qed.
End P2.

Section P3.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Hypothesis OBL_RT_GOT_MEMCPY : forall m, RTconst RE X m -> ro_cells asegs m 0x0e81e0 [C8 (wz 0x0ea1c8)].
Hypothesis OBL_MEMCPY : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv asegs m ->
evt asegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdda10) fc None m (seg_rom asegs)).

Lemma realloc_p3 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (A0 n0' A n obj b1 : Z) (id : word) (src ujunk : list byte) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m ->
rw_cells asegs m (A0 + -16) (hdr_cells b1 n0' id) ->
0 < n0' < 2^32 -> 0 < n < 2^32 -> 0 < A < 2^63 -> 16 <= A0 < 2^63 -> 0 <= obj < 2^64 ->
bytes_at asegs m A0 src -> length src = Z.to_nat (Z.min n n0') ->
rw_cells asegs m A [CB (Z.to_nat (Z.min n n0')) ujunk] ->
(A0 + Z.min n n0' <= A \/ A + Z.min n n0' <= A0) ->
(forall m' (u0 u1 u2 u6 u7 u10 u11 u12 u13 s3' : word),
munch [(A, A + Z.min n n0')] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' A [CB (Z.to_nat (Z.min n n0')) src] -> bytes_at asegs m' A0 src ->
evt asegs Q (MS (mkR (wz 0x3fea8) sp gp tp u0 u1 u2 (wz obj) (wz A0) (wz A_INSTANCE) (wz A0) (wz 0) (wz 0) (wz obj) (wz 1) u6 u7
(wz A_INSTANCE) s3' (wz A) s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13)
F (wz 0x3ef80) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR (wz 0x3fe14) sp gp tp t0 t1 t2 (wz obj) (wz A0) (wz A) a1 a2 a3 a4 a5 a6 a7
(wz A_INSTANCE) (wz n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3fe14) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI HDR Hn0 Hn HA HA0 HO SRC LSRC UC SEP CONT.
change (2^64) with 18446744073709551616 in *. change (2^63) with 9223372036854775808 in *. change (2^32) with 4294967296 in *.
unfold hdr_cells in HDR. unfold A_INSTANCE in *.
step.
step. unfold_cond; cond_unsig; if_false.
step.
step.
step.
step. if_lit.
rtc RT 23%nat K23. pose proof (OBL_RT_GOT_MEMCPY _ RT) as KG.
step. step. step.
step. if_lit.
step. step.
change (zx16 (wz 0)) with (wz 0). rewrite (zx32_small n0') by lia.
step. step.
rewrite (unsigned_lit n0') by lia. rewrite ?(unsigned_lit 0) by lia. rewrite ?Z.shiftl_0_l. rewrite Z.lor_0_l.
step.
destruct (Z_lt_ge_dec n n0') as [LT|GE];
[ unfold_cond; cond_unsig; if_true; rewrite (Z.min_l n n0') in * by lia
| unfold_cond; cond_unsig; if_false; step; rewrite (Z.min_r n n0') in * by lia ].
all: step; step; step.
all: step.
all: (eapply evt_cut; [eapply (OBL_MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m src ujunk);
[rewrite !unsigned_lit by lia; exact SRC| rewrite !unsigned_lit by lia; exact LSRC
| rewrite !unsigned_lit by lia; exact UC| rewrite !unsigned_lit by lia; lia| assumption]|]).
all: intros ms'' PO; unfold memcpy_post in PO; rewrite !unsigned_lit in PO by lia.
all: destruct PO as (v0 & v1 & v2 & pw1 & pw2 & pw3 & pw4 & pw5 & pw6 & pw7 & v3 & v4 & v5 & v6 & m4 & -> & MU4 & WM4 & MI4 & UC4 & SRC4).
all: replace (ret_pc (wz 261772)) with (wz 261772) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
all: step; step; step; step; step; step.
all: step.
all: eapply CONT; [exact MU4| exact WM4| exact MI4| exact UC4| exact SRC4].
Qed.
End P3.

Section Epi.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma rl_frame_all : forall mx bp sz (q : list word) (rest junk8 junk8b : list byte) (ra s0 s1 s2 s3 s4 s5 s6 : word),
length q = 5%nat ->
rw_cells asegs mx (bp + -2144) [CB 8 junk8b] -> rw_cells asegs mx (bp + -2136) (unw_obj (bp + -2136) sz q rest bp) ->
rw_cells asegs mx (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mx (bp + -2144) ([CB 8 junk8b] ++ unw_obj (bp + -2136) sz q rest bp ++ [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Proof.
intros mx bp sz q rest junk8 junk8b ra s0 s1 s2 s3 s4 s5 s6 LQ O0 O1 O2.
apply (proj2 (rw_cells_app asegs mx _ [CB 8 junk8b] _)). split; [exact O0|]. cbn [cells_size csize Nat.add].
replace (bp + -2144 + Z.of_nat 8) with (bp + -2136) by lia.
apply (proj2 (rw_cells_app asegs mx _ _ _)). split; [exact O1|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try lia.
unfold unw_obj. cbn [cells_size csize Nat.add map app length]. replace (bp + -2136 + Z.of_nat 2064) with (bp + -72) by lia. exact O2.
Qed.

Lemma realloc_epi : forall (ra : word) (bp : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x0 x1 x2 x3 x5 x6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(y1 y2 y3 y4 y5 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo R sz : Z) (q : list word) (rest junk8 junk8b j8 : list byte),
mem_inv asegs m -> 0 <= bp < 2^64 -> stk asegs m lo (bp + -2208) -> lo <= bp - 2208 -> 0 < R < 2^64 ->
rw_cells asegs m (bp + -2208) [C8 y5; C8 y4; C8 y3; C8 y2; C8 y1; C8 (wz 0x3fd98)] ->
rw_cells asegs m (bp + -2160) [CB 8 j8; C8 (wz 0x63e8c)] ->
rw_cells asegs m (bp + -2144) [CB 8 junk8b] -> rw_cells asegs m (bp + -2136) (unw_obj (bp + -2136) sz q rest bp) -> length q = 5%nat ->
rw_cells asegs m (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs (fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word),
ms' = MS (mkR ra (wz bp) gp tp t0 t1 t2 s0 s1 (wz R) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)
/\ stk asegs m lo bp)
(MS (mkR (wz 0x3fea8) (wz (bp + -2208)) gp tp t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 (wz R) x5 x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3fea8) fc None m (seg_rom asegs)).
Proof.
intros until j8; intros MI BPR ST LO HR FR48 FR16 J8 OBJ LQ FRS.
change (2^64) with 18446744073709551616 in *.
step.
do 6 step.
step.
release_frame FR48 ST (bp + -2160).
step.
replace (ret_pc (wz 261528)) with (wz 261528) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. unfold_cond; cond_unsig; if_false.
step. step.
release_frame FR16 ST (bp + -2144).
step.
replace (ret_pc (wz 409228)) with (wz 409228) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 8 step. step.
pose proof (rl_frame_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LQ J8 OBJ FRS) as FRX. clear OBJ FRS J8.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try lia. unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST bp.
step.
apply evt_done. do 7 eexists. split; [reflexivity| exact ST].
Qed.

Definition rl_null_W (bp : Z) : list (Z * Z) := [(bp - 2176, bp - 2160); (A_ERRNO, A_ERRNO + 4)].

Lemma realloc_epi_null : forall (ra : word) (bp : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 x6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(y1 y2 y3 y4 y5 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo sz : Z) (q : list word) (rest junk8 junk8b j8 : list byte),
RStats RE X m -> mem_inv asegs m -> 0 <= bp < 2^64 -> stk asegs m lo (bp + -2208) -> band_lo <= lo -> lo <= bp - 2208 ->
rw_cells asegs m (bp + -2208) [C8 y5; C8 y4; C8 y3; C8 y2; C8 y1; C8 (wz 0x3fd98)] ->
rw_cells asegs m (bp + -2160) [CB 8 j8; C8 (wz 0x63e8c)] ->
rw_cells asegs m (bp + -2144) [CB 8 junk8b] -> rw_cells asegs m (bp + -2136) (unw_obj (bp + -2136) sz q rest bp) -> length q = 5%nat ->
rw_cells asegs m (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra (wz bp) gp (wz A_TP) t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (rl_null_W bp) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo bp /\ RStats RE X m')
(MS (mkR (wz 0x3fe14) (wz (bp + -2208)) gp (wz A_TP) t0 t1 t2 x0 x1 (wz 0) a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3fe14) fc None m (seg_rom asegs)).
Proof.
intros until j8; intros RS MI BPR ST CEIL LO FR48 FR16 J8 OBJ LQ FRS.
pose proof CEIL as CEIL'. idtac. change (2^64) with 18446744073709551616 in *.
pose proof (munch_refl (rl_null_W bp) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold rl_null_W, A_ERRNO in MU.
step.
step. if_lit.
step.
do 6 step.
step.
release_frame FR48 ST (bp + -2160).
step.
replace (ret_pc (wz 261528)) with (wz 261528) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_lit.
step.
call_ch (set_errno_spec RE X) ltac:(fun PO => unfold A_ERRNO in PO; rewrite !(unsigned_lit (bp + -2160)) in PO by lia);
[exact RS| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST4 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS4 end.
step.
step.
step. step.
release_frame FR16 ST4 (bp + -2144).
step.
replace (ret_pc (wz 409228)) with (wz 409228) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 8 step. step.
pose proof (rl_frame_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LQ J8 OBJ FRS) as FRX. clear OBJ FRS J8.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try lia. unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST4 bp.
step.
apply evt_done. do 14 eexists. lazymatch type of ST4 with stk _ ?mm _ _ => exists mm end.
split; [reflexivity|]. split; [unfold rl_null_W, A_ERRNO; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST4| exact RS4].
Qed.
End Epi.
