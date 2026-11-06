(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Q6sh QQwg QKTr QJBH QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk QpY2 QOJv Q9Ho QV3O QnRU QYyZ Qu3b QjgW QpME QpF1 QmvA QFd5 QsDw QRfV QcYs QteI QpzM QcfN QVo2 QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QTVW.Mqa QOJv.Mqb QNQk Q9Ho.Mq4 QV3O QnRU.Mql QmP7.Mq1 QpY2.Mqb QYyZ.Mq8 Qu3b QYyZ.Mqc QjgW QpME.Mq8 QpF1 QmvA.Mq5 QpME.Mqc.
Import QpY2.Mqc.
Import QFd5.Mq5 QsDw.Mq2 QRfV.Mq3 QcYs.Mq6 QnRU.Mqk QteI.Mqc QpzM.Mqm QpzM.Mqn QcYs.Mq4 QcYs.Mq5 QnRU.Mqd.
Import QcfN.Mq4 QVo2.Mq4.
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

Lemma too_big_sec : forall n, 0 <= n <= 2^26 -> from_primary n = false -> too_big n = false.
Proof.
intros n Hn HP. unfold too_big. rewrite HP. unfold kMaxAllowedMalloc.
pose proof (needed_facts n ltac:(lia)) as NF. pose proof (rz_size_range n) as [R1 _].
replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb]. apply Z.ltb_ge. lia.
Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Let atn := at_nodeA L asegs.
Hypothesis large_alloc_spec : large_alloc_stmt RE X L.
Hypothesis poison_zero_spec : poison_zero_stmt_lh RE X L.

Definition alloc_W_sec (sp : Z) : list (Z * Z) :=
[ (sp - ALLOC_STACK, sp); (0x174420, 0x174421); (rl_T X + 2800, rl_T X + 3168);
(A_INSTANCE + 104, A_INSTANCE + 728); (ptrarr_lo RE, ptrarr_lo RE + 0x800000);
(SS_BASE, DP_END); (rl_dn X, rl_dn X + 0x100000); (rl_ssb X, rl_ssb X + 0x800000) ].

Definition alloc_post_sec (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (LB : list ablock) (n cf lo : Z) (m : word -> option byte) (obj tsz : Z) (q : list word)
(r : option aptr * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ RDepot RE X m' /\ depot_step m m'
/\ rw_cells asegs m' obj [C8 (wz (obj + 16)); C8 (wz tsz)] /\ u64arr asegs m' (obj + 16) q
/\ match r with
| (None, a1) => a0 = wz 0 /\ a1 = a /\ munch (alloc_W_sec (bv_unsigned sp)) m m' /\ RSec a LB RE X m'
| (Some p, a1) => exists mb, let msz := sec_map_size n in
p = ASec mb n
/\ as_reg a1 = as_reg a ++ [mkSec mb msz n]
/\ as_tq a1 = as_tq a /\ as_gq a1 = as_gq a /\ (forall c, cls a1 c = cls a c)
/\ as_cache_inited a1 = as_cache_inited a /\ as_next a1 = as_next a
/\ (as_nres a1 = as_nres a \/ as_nres a1 = as_nres a + kPtrArrBlock)
/\ as_spent a1 = as_spent a + sec_cost msz
/\ mb mod kPage = 0 /\ appr mb msz /\ mb + msz <= band_lo /\ zavoids mb msz (avoid_of (ae_L RE) a) = true
/\ a0 = wz (mb + kSecUserOff)
/\ munch (alloc_W_sec (bv_unsigned sp) ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m m'
/\ RSec a1 LB RE X m'
/\ chunk_mem m' (mb + kPage) (mb + msz) (mb + kSecUserOff) n
/\ (cf = 0 -> rw_cells asegs m' (mb + kSecUserOff) [CB (Z.to_nat n) (repeat (b8 0) (Z.to_nat n))])
end.

Lemma allocate_sec_spec : forall ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (LB : list ablock) (FS : list fframe)
(n cf lo obj tsz dn : Z) (q : list word),
gcons a LB FS G RE X ->
RTconst RE X m -> RStats RE X m -> RSec a LB RE X m -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ALLOC_STACK ->
0 <= n <= 2^26 -> from_primary n = false -> 0 <= cf <= 1 ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz tsz)] -> u64arr asegs m (obj + 16) q -> Z.of_nat (length q) = 30 ->
1 <= tsz <= 30 -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= obj -> obj + 256 < 2^64 ->
aimplT atn (asan_malloc (ae_L RE) a n) s
(alloc_post_sec ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB n cf lo m obj tsz q)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz n) (wz 8) (wz obj) (wz 1) (wz cf) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz allocate_entry) fc None m (seg_rom asegs)).
Proof.
intros until q; intros GC RT RS RSE RD MI ST CEIL LO Hn HP CF OBJ TRQ LQ SZR DNH DCAP OB1 OB2.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof (rlay_avoid RE X RL) as AVC.
pose proof CEIL as CEIL'. idtac. unfold ALLOC_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & PC & _ & QK & QC & _). unfold prim_hi in PC. unfold ptrarr_hi in QC. idtac. rewrite ?KHI_eq in PK.
clear TA TD. change (al_space_beg (ae_L RE)) with (prim_lo RE) in PC. change (al_ptrarr (ae_L RE)) with (ptrarr_lo RE) in QC.
apply appr_to_lia in QK; [| lia| lia].
pose proof (sec_geom_facts n Hn HP) as (GN & Grz & Gn' & _ & Gnd1 & Gssz & _ & GM1 & GndE).
pose proof (munch_refl (alloc_W_sec (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_INSTANCE in MU.
apply aimplT_from_evt.

eapply alloc_pre1; [exact RT| exact RL| exact MI| exact ST| exact CEIL'| lia| lia| lia|].
intros m1 u0 u1 u2 u3 v1 v2 v3 v4 v5 v6 v7 u4 u5 u6 u7 fj MU1 WM1 MI1 ST1 FR1.
assert (RT1 : RTconst RE X m1) by (eapply RTconst_munch; [exact RT| exact MU1| exact WM1| apply Forall_cons; [apply rt_avoid_stack; [exact RL| lia]| apply Forall_nil]]).
assert (RS1 : RStats RE X m1) by (eapply RStats_munch; [exact RS| exact MU1| exact WM1| apply Forall_cons; [st_avoid_solve| apply Forall_nil]]).
assert (RSE1 : RSec a LB RE X m1).
{ eapply RSec_frame; [exact RSE| exact WM1|]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z Fz _. cbn [outside]. split; [| exact I].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)). lia. }
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame; [exact RD| exact WM1|]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z Fz _. cbn [outside]. split; [| exact I].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). lia. }
phase_done MU m m1 MU1 WM1. clear MI RT RS RSE RD.
eapply alloc_rzlog; [lia|]. intros a0'.
eapply alloc_pre3_sec; [exact RT1| exact RL| exact MI1| exact ST1| exact CEIL'| lia| exact Hn| exact HP|].
intros m2 w0 w1 w2 w3 x0 x1 x2 x3 x4 x5 x6 x7 w4 w5 w6 w7 MU2 WM2 MI2 ST2.
assert (RT2 : RTconst RE X m2) by (eapply RTconst_munch; [exact RT1| exact MU2| exact WM2| apply Forall_cons; [apply rt_avoid_stack; [exact RL| lia]| apply Forall_nil]]).
assert (RS2 : RStats RE X m2) by (eapply RStats_munch; [exact RS1| exact MU2| exact WM2| apply Forall_cons; [st_avoid_solve| apply Forall_nil]]).
assert (RSE2 : RSec a LB RE X m2).
{ eapply RSec_frame; [exact RSE1| exact WM2|]. eapply agree_on_of_munch; [exact MU2| exact WM2|]. intros z Fz _. cbn [outside]. split; [| exact I].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)). lia. }
assert (RD2 : RDepot RE X m2).
{ eapply RDepot_frame; [exact RD1| exact WM2|]. eapply agree_on_of_munch; [exact MU2| exact WM2|]. intros z Fz _. cbn [outside]. split; [| exact I].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). lia. }
phase_done MU m1 m2 MU2 WM2. clear MI1 RT1 RS1 RSE1 RD1. try clear ST1.

pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp - 128)] m2) as MUs. pose proof (wmono_refl asegs m2) as WMs.
step. call_sp_ch (get_current_thread_spec RE X) ltac:(fun _ => idtac); [exact RT2| exact RL| assumption| exact ST2| exact CEIL'| lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST3 end.
match goal with H : RTconst RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RT3; rename H2 into MI3 end.
lazymatch type of MUs with munch _ _ ?mm =>
assert (RS3 : RStats RE X mm) by (eapply RStats_munch; [exact RS2| exact MUs| exact WMs| apply Forall_cons; [st_avoid_solve| apply Forall_nil]]);
assert (RSE3 : RSec a LB RE X mm) by
(eapply RSec_frame; [exact RSE2| exact WMs|]; eapply agree_on_of_munch; [exact MUs| exact WMs|]; intros z Fz _; cbn [outside]; split; [| exact I];
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)); lia);
assert (RD3 : RDepot RE X mm) by
(eapply RDepot_frame; [exact RD2| exact WMs|]; eapply agree_on_of_munch; [exact MUs| exact WMs|]; intros z Fz _; cbn [outside]; split; [| exact I];
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)); lia)
end.
clear MUs WMs RT2 RS2 RSE2 RD2. try clear ST2. try clear MI2.
step.
step. ifz.
step. stp. step. step.
step.
apply evt_done.
unfold asan_malloc. rewrite (too_big_sec n Hn HP), HP.
replace (needed n + rz_size n) with (sec_size n) by reflexivity.
name_sp sp (-128). rewrite <- Hsp in ST3.
lazymatch goal with |- aimplT _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
eapply aimplT_bind;
[eapply (combined_sec_spec L RE X large_alloc_spec _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm s a LB FS G n lo);
[exact GC| exact AVC| exact RT3| exact RS3| exact RSE3| exact MI3| exact ST3| exact CEIL'| rewrite Hsp; unfold COMB_STACK; lia| exact Hn| exact HP] |] end.
intros [r a1] s' ms' PO. unfold combs_post in PO. rewrite Hsp in PO. unname_sp.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & -> & -> & MI4 & ST4 & WM3 & RT4 & RS4 & REST).
replace (ret_pc (wz 259380)) with (wz 259380) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_frame in FR1.

assert (RDK : forall mm W (P : Z -> Prop), (forall z, P z -> fp_RDepot RE X z -> False) -> munch W x22 mm -> wmono asegs x22 mm ->
(forall lo' hi' z, In (lo', hi') W -> lo' <= z < hi' -> fp_RStats RE X z \/ fp_RSec a RE X z \/ band_lo <= z \/ P z) -> RDepot RE X mm).
{ intros mm W P HP0 MUw WMw HW. eapply RDepot_frame; [exact RD3| exact WMw|]. eapply agree_on_of_munch; [exact MUw| exact WMw|]. intros z Fz _. apply outside_intro.
intros lo' hi' Hin Hz. destruct (HW lo' hi' z Hin Hz) as [P1|[P1|[P1|P1]]].
- exact (fpS_excl _ _ _ _ _ _ GC z P1 ltac:(do 2 right; left; exact Fz)).
- exact (fpD_excl _ _ _ _ _ _ GC z Fz ltac:(right; left; exact P1)).
- pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). lia.
- exact (HP0 z P1 Fz). }
assert (WLZ : forall (P : Z -> Prop) lo' hi' z, In (lo', hi') ((bv_unsigned sp + -128 - 48, bv_unsigned sp + -128) :: W_large (bv_unsigned sp + -128 - 48) RE X) -> lo' <= z < hi' ->
fp_RStats RE X z \/ fp_RSec a RE X z \/ band_lo <= z \/ P z).
{ intros P lo' hi' z Hin Hz. unfold W_large, LARGE_STACK in Hin. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-.
- do 2 right; left. idtac. lia.
- do 2 right; left. idtac. lia.
- right; left. left. split; cbn [fst snd]; lia.
- right; left. right; left. split; cbn [fst snd]; lia.
- left. left. split; cbn [fst snd]; lia. }
destruct r as [mb|].
2:{
destruct REST as (-> & -> & MU3 & RSE4). apply aimplT_ret.
pose proof (RDK m3 _ (fun _ => False) ltac:(intros z FF _; exact FF) MU3 WM3 (WLZ _)) as RD4.
unfold W_large, LARGE_STACK, A_INSTANCE in MU3.
lazymatch type of MU3 with munch _ ?mp _ => phase_done MU mp m3 MU3 WM3 end.
clear RD3 RT3 RS3 RSE3. try clear MI3. try clear ST3.
step.
step. if_lit.
pose proof (munch_refl [(0x174420, 0x174421); (bv_unsigned sp - 144, bv_unsigned sp - 128)] m3) as MUs. pose proof (wmono_refl asegs m3) as WMs.
step. call_sp_ch (set_oom_spec RE X) ltac:(fun _ => idtac); [exact RS4| assumption| exact ST4| exact CEIL'|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST5 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS5; rename H2 into MI5 end.
lazymatch type of MUs with munch _ _ ?mm =>
assert (RT5 : RTconst RE X mm) by
(eapply RTconst_frame; [exact RT4| exact WMs|]; eapply agree_on_of_munch; [exact MUs| exact WMs|]; intros z Fz _; cbn [outside]; split; [| split; [| exact I]];
[ destruct (Z.eq_dec z 0x174420) as [->|NE]; [exfalso; exact (fpS_excl _ _ _ _ _ _ GC 0x174420 ltac:(do 2 right; reflexivity) ltac:(do 4 right; exact Fz))| lia]
| pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(left; exact Fz)); lia ]);
assert (RSE5 : RSec a LB RE X mm) by
(eapply RSec_frame; [exact RSE4| exact WMs|]; eapply agree_on_of_munch; [exact MUs| exact WMs|]; intros z Fz _; cbn [outside]; split; [| split; [| exact I]];
[ destruct Fz as [Fz|[Fz|[Fz|Fz]]]; [destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; unfold A_INSTANCE in *; lia| destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; lia
| destruct Fz as (e & He & Hz); pose proof (sec_facts _ _ _ _ _ _ GC e He) as (_ & E2 & _ & E4 & E5 & E6 & _);
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [SG _]; unfold kPage in Hz; clear - E2 E4 SG Hz E6; lia
| destruct Fz as (e & He & Hz); pose proof (hdr_band _ _ _ _ _ _ GC e z He Hz); lia]
| pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)); lia ]);
assert (RD5 : RDepot RE X mm) by
(eapply RDepot_frame; [exact RD4| exact WMs|]; eapply agree_on_of_munch; [exact MUs| exact WMs|]; intros z Fz _; cbn [outside];
assert (B : 0x1c4088 <= z < 0x647000 \/ (0 < z < 0x10000) \/ (0x647000 <= z < band_lo)) by (destruct Fz as [[F1 F2]|[[F1 F2]|[[F1 F2]| ->]]]; cbn [fst snd] in *; lia); lia)
end.
clear MUs WMs RT4 RSE4 RD4 RS4.
step. call0 (may_return_null_spec RE X); [exact RT5| assumption|]. subst_words.
step. if_lit.
stp. step.
step. do 13 step. step.
release_frame FR1 ST5 (bv_unsigned sp).
step.
apply evt_done. unfold alloc_post_sec. do 16 eexists.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST5|].
split; [exact RT5|]. split; [exact RS5|]. split; [exact RD5|].
split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn; split; [split; [unfold DP_N; exact DNC| exact DNP]| lia]]|].
split; [exact OBJ|]. split; [exact TRQ|].
cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [| exact RSE5].
unfold alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_INSTANCE. exact MU. }

destruct REST as (-> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & MU3 & RSE4 & BODY & HJ & FAS).
rewrite KP in BODY, HJ, FAS, MBP. pose proof MBK as MBKr. apply appr_to_lia in MBK; [| pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG0 _]; lia| lia]. pose proof MBK as MBK'. pose proof MBC as MBC'. idtac.
set (msz := sec_map_size n) in *. set (ssz := sec_size n) in *.
destruct (zavoid_facts RE X a mb msz AVC ltac:(lia) ZA) as (AVO & AVP & AVQ & AVR).
assert (SOK : sec_ok RE X (mkSec mb msz n)).
{ unfold sec_ok. cbn [se_beg se_size se_req]. split; [rewrite <- KP in MBP; exact MBP|]. split; [exact MBKr|]. split; [exact MBC|]. split; [reflexivity|]. split; [exact HP|]. split; [lia|].
split; [unfold iv_disjoint; cbn [fst snd]; lia|]. split; [unfold iv_disjoint; cbn [fst snd]; lia|].
apply List.Forall_forall. intros o Ho. unfold iv_disjoint. cbn [fst snd]. destruct (AVO o Ho); lia. }
pose proof (gcons_reg_add a a1 LB FS G RE X mb msz n GC REG CLS NX SOK AVR ltac:(lia)) as GC1.
pose proof (nmap_RDepot a LB FS G RE X GC mb msz MBP MBK MBC ltac:(lia) AVO AVP AVQ AVR) as ZND.
assert (SHM : SH (mb + msz) = SH mb + msz / 8) by (rewrite <- SH_plus8; f_equal; pose proof (sec_geom_facts n Hn HP); clear - MBP H; Z.div_mod_to_equations; lia).
pose proof (RDK m3 _ (nmap mb msz) ZND MU3 WM3 ltac:(intros lo' hi' z Hin Hz; apply in_app_iff in Hin; destruct Hin as [Hin|Hin];
[exact (WLZ _ lo' hi' z Hin Hz)| cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-; do 3 right;
[left; exact Hz| right; split; cbn [fst snd]; lia]])) as RD4.
assert (MS8 : 8 * (msz / 8) = msz /\ 4096 + ssz <= msz) by (pose proof (sec_geom_facts n Hn HP) as (_ & _ & _ & _ & _ & _ & G7 & G8 & _); fold msz ssz in G7, G8; clear - G7 G8; Z.div_mod_to_equations; lia).
pose proof (sec_geom_facts n Hn HP) as (GN' & _ & _ & _ & Gnd1' & Gssz' & _ & _ & _). fold ssz in Gssz'.
assert (MBH : 0x647000 <= mb) by (clear - MBK MS8 GN' Gnd1' Gssz'; lia).
assert (SHB : 0x80000000 <= SH mb /\ SH mb + msz / 8 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; clear - MBH MBC' MS8; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD.
rewrite SHM in MU3. unfold W_large, LARGE_STACK, A_INSTANCE in MU3.

apply (munch_weaken _ (((bv_unsigned sp - 1152, bv_unsigned sp) :: (1524768, 1524769) :: (rl_T X + 2800, rl_T X + 3168) :: (977752 + 104, 977752 + 728)
:: (ptrarr_lo RE, ptrarr_lo RE + 8388608) :: (1851528, 6373552) :: (rl_dn X, rl_dn X + 1048576) :: (rl_ssb X, rl_ssb X + 8388608) :: nil)
++ [(mb, mb + msz); (SH mb, SH mb + msz / 8)])) in MU.
2:{ intros z Hz. cbn [outside app] in Hz |- *. clear - Hz. tauto. }
cbn [app] in MU.
cbn [app] in MU3.
lazymatch type of MU3 with munch _ ?mp _ => phase_done MU mp m3 MU3 WM3 end.
clear RD3 RT3 RS3 RSE3. try clear MI3. try clear ST3.
rewrite KP. apply aimplT_from_evt.
step.
step. unfold_cond; cond_unsig; if_false.

destruct (sec_pieces RE X n mb RL Hn HP MBP MBK MBC AVO AVP m3 BODY HJ FAS) as (j1 & j & j2 & pb & MG & HJm & HDR & UZ & HJU & SHD1 & PZ & P3 & SHD2).
clear BODY HJ FAS.
change (sec_map_size n) with msz in HJU, SHD2.
set (AB := mb + 4096) in *. set (A := AB + rz_size n) in *. set (n' := used_size n) in *.
set (up := A + 8 * ngran n') in *.
pose proof (ngran_eq n' ltac:(lia)) as (NG1 & NG2 & NG3). pose proof (round_up_8 n' ltac:(lia)) as [RU8 RUm].
assert (N8 : 0 <= n' / 8 /\ 0 <= n' mod 8 < 8 /\ n' = 8 * (n' / 8) + n' mod 8 /\ 8064 <= n' / 8) by (clear - GN Gn'; Z.div_mod_to_equations; lia).
assert (NGB : n' / 8 <= ngran n' <= n' / 8 + 1) by (rewrite NG1; unfold round_up; clear - N8; Z.div_mod_to_equations; lia).
assert (RUE : round_up n' 8 = round_up n 8) by (rewrite Gn'; reflexivity).
clear NG1 RU8.
remember (msz / 8) as q8 eqn:EQ8.
assert (SHa : SH AB = SH mb + 512) by (subst AB; rewrite <- (SH_plus8 mb 512); reflexivity).
assert (SHA : SH A = SH mb + 768) by (subst A AB; rewrite Grz, <- (SH_plus8 mb 768); f_equal; lia).
assert (SHU : SH up = SH mb + 768 + ngran n') by (subst up; rewrite <- SHA, <- SH_plus8; reflexivity).
set (k2 := (AB + (msz - 4096) - up) / 8) in *.
assert (K2 : 8 * k2 = mb + msz - up /\ up + 2048 <= mb + msz /\ 8 * q8 = msz)
by (subst k2 q8 up A AB; rewrite Grz, <- NG3; clear - MS8 Gssz GndE GM1 Gnd1 RUm RUE; Z.div_mod_to_equations; lia).
clear EQ8 MS8 RUm.

pose proof (AVO _ (T_obj RE X)) as TD. pose proof (AVO _ (dn_obj RE X)) as ND. pose proof (AVO _ (ssb_obj RE X)) as BD. cbn [fst snd] in TD, ND, BD.

hide TD. hide ND. hide BD. hide AVP. hide AVQ. hide NR.

pose proof (szone_frame a a1 LB FS G RE X mb msz n GC GC1 REG MBP MBK MBC ltac:(lia) AVO AVP AVQ AVR) as SZF.
pose proof (nbody_RStats a a1 LB FS G RE X mb msz n GC GC1 REG MBP MBK MBC ltac:(lia) AVO AVP AVQ AVR) as NBs.
pose proof (nbody_RDepot a a1 LB FS G RE X mb msz n GC GC1 REG MBP MBK MBC ltac:(lia) AVO AVP AVQ AVR) as NBd.
assert (NSt : forall z, band_lo <= z -> ~ fp_RStats RE X z) by (intros z Hz Fz; pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(right; left; exact Fz)); idtac; lia).
assert (NDt : forall z, band_lo <= z -> ~ fp_RDepot RE X z) by (intros z Hz Fz; pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)); idtac; lia).
assert (NSd : forall z, fp_RDepot RE X z -> ~ fp_RStats RE X z) by (intros z Hz Fz; exact (fpS_excl _ _ _ _ _ _ GC z Fz ltac:(do 2 right; left; exact Hz))).
assert (NBb : forall z, AB <= z < mb + msz -> nbody mb msz z) by (intros z Hz; left; subst AB; lia).
assert (NBh : forall z, SH AB <= z < SH mb + q8 -> nbody mb msz z).
{ intros z Hz. right. split; cbn [fst snd]; [subst AB; lia|]. replace ((msz - 4096) / 8) with (q8 - 512) by (clear - K2; Z.div_mod_to_equations; lia). fold AB. lia. }

eapply (alloc_hdr_sec RE X n mb gp RL Hn HP MBP MBK MBC AVO AVP); [exact RT4| exact MI4| exact ST4| exact CEIL'| lia| exact FR1| exact HDR|].
intros m4 h0 h1 h2 h3 h5 h6 h7 MU4 WM4 MI5 ST5 FR5 HDR5 RT5.
fold msz ssz AB A n' in MU4, HDR5 |- *.
destruct (SZF _ _ _ MU4 WM4 ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; left; apply NBb; lia)) as (FS' & FD & FSE).
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; intros Fz; exact (NBs z ltac:(apply NBb; lia) Fz)) RS4) as RS5.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; intros Fz; exact (NBd z ltac:(apply NBb; lia) Fz)) RD4) as RD5.
pose proof (FSE RSE4) as RSE5. clear FS' FD FSE.
ctr P3 MU4 WM4. pose proof (hjunk_wmono _ _ _ _ HJm WM4) as HJm5. pose proof (hjunk_wmono _ _ _ _ HJU WM4) as HJU5.
clear HDR FR1 RS4 RD4 RSE4 RT4 HJm HJU. try clear MI4. try clear ST4.
phase_done MU m3 m4 MU4 WM4.

eapply (alloc_depot_sec RE X n mb gp RL Hn HP MBP MBK MBC AVO AVP);
[exact RT5| exact RD5| exact MI5| exact ST5| exact CEIL'| lia| exact OBJ| exact TRQ| exact LQ| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| lia| lia| exact HDR5|].
intros m5 d0 d1 d2 d5 d6 d7 d10 d11 d12 d13 d14 d15 d16 d17 id MU5 WM5 MI6 ST6 RT6 RD6 OBJ6 TRQ6 ID (dn6 & [DNC6 DNP6] & DNR6) HDR6. unfold DP_N in DNC6.
fold msz ssz AB A n' in MU5, HDR6 |- *. unfold depot_W, SS_BASE, DP_END in MU5. clear OBJ TRQ.
destruct (SZF _ _ _ MU5 WM5 ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-;
[left; apply NBb; lia| do 3 right; idtac; lia| do 2 right; left; left; split; cbn [fst snd]; lia
| do 2 right; left; right; left; split; cbn [fst snd]; lia| do 2 right; left; do 2 right; left; split; cbn [fst snd]; lia])) as (FS' & FD & FSE).
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-;
[intros Fz; exact (NBs z ltac:(apply NBb; lia) Fz)| apply NSt; lia| apply NSd; left; split; cbn [fst snd]; lia
| apply NSd; right; left; split; cbn [fst snd]; lia| apply NSd; do 2 right; left; split; cbn [fst snd]; lia]) RS5) as RS6.
pose proof (FSE RSE5) as RSE6. clear FS' FD FSE.
ctr P3 MU5 WM5. pose proof (hjunk_wmono _ _ _ _ HJm5 WM5) as HJm6. pose proof (hjunk_wmono _ _ _ _ HJU5 WM5) as HJU6.
clear HDR5 RT5 RS5 RD5 RSE5 HJm5 HJU5. try clear MI5. try clear ST5.
unhide ND. unhide BD. phase_done MU m4 m5 MU5 WM5. hide ND. hide BD.

pose proof (RSec_hdr_last a a1 LB FS G RE X mb msz n GC GC1 REG MBP MBK MBC ltac:(lia) AVO AVP AVQ AVR LB m5 RSE6) as HDRS. fold ssz in HDRS.
eapply (alloc_shadow_sec RE X n mb gp RL Hn HP MBP MBK MBC AVO AVP); [exact RT6| exact MI6| exact ST6| exact CEIL'| lia| exact HDRS| exact SHD1| exact SHD2|].
intros m6 e0 e1 e2 e3 e4 e5 e6 e7 e10 e11 e12 e14 e15 e16 e17 MU6 WM6 MI7 ST7 RT7 FA1 FA2.
fold msz ssz AB A n' up k2 in MU6, FA1, FA2 |- *.
assert (ZS : forall lo' hi' z, In (lo', hi') [(bv_unsigned sp - 192, bv_unsigned sp - 128); (SH AB, SH AB + 256); (SH up, SH up + k2)] -> lo' <= z < hi' ->
szone RE X mb msz z /\ ~ fp_RStats RE X z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- split; [do 3 right; idtac; lia|]. split; [apply NSt| apply NDt]; lia.
- assert (NB : nbody mb msz z) by (apply NBh; lia). split; [left; exact NB|]. split; intros Fz; [exact (NBs z NB Fz)| exact (NBd z NB Fz)].
- assert (NB : nbody mb msz z) by (apply NBh; lia). split; [left; exact NB|]. split; intros Fz; [exact (NBs z NB Fz)| exact (NBd z NB Fz)]. }
destruct (SZF _ _ _ MU6 WM6 ltac:(intros lo' hi' z Hin Hz; exact (proj1 (ZS lo' hi' z Hin Hz)))) as (FS' & FD & FSE).
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; exact (proj1 (proj2 (ZS lo' hi' z Hin Hz)))) RS6) as RS7.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (proj2 (ZS lo' hi' z Hin Hz)))) RD6) as RD7.
pose proof (FSE RSE6) as RSE7. clear FS' FD FSE ZS.
ctr P3 MU6 WM6. pose proof (hjunk_wmono _ _ _ _ HJm6 WM6) as HJm7. pose proof (hjunk_wmono _ _ _ _ HJU6 WM6) as HJU7.
clear HDRS SHD1 SHD2 RT6 RS6 RD6 RSE6 HJm6 HJU6. try clear MI6. try clear ST6.
phase_done MU m5 m6 MU6 WM6.

stp. stp.
step.
rewrite (unsigned_lit n'), land_mask8_48 by lia. replace (n' - n' mod 8) with (8 * (n' / 8)) by lia.
step. unfold_cond; cond_unsig; if_false.
step. step. stp.
step.
apply evt_done.
replace (mb + kSecUserOff) with A by (subst A AB; rewrite KU, Grz; lia).
replace (round_down n' 8) with (8 * (n' / 8)) by (unfold round_down; lia).
name_sp sp (-128). rewrite <- Hsp in ST7.
lazymatch goal with |- aimplT _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
eapply aimplT_bind;
[eapply (poison_zero_spec _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm A (8 * (n' / 8)) lo s j);
[exact RT7| exact RL| exact MI7| exact ST7| exact CEIL'| rewrite Hsp; unfold PZ_STACK; lia
| subst A AB; clear - MBP Grz; Z.div_mod_to_equations; lia| rewrite Z.mul_comm; apply Z.mod_mul; lia| lia| rewrite ?KHI_eq; change (2^47) with 140737488355328; subst A AB;
assert (MS8 : 8 * (msz / 8) = msz /\ 4096 + ssz <= msz) by (pose proof (sec_geom_facts n Hn HP) as (_ & _ & _ & _ & _ & _ & G7 & G8 & _); fold msz ssz in G7, G8; clear - G7 G8; Z.div_mod_to_equations; lia);
clear - MBK MBH MBC MS8 Gssz' Gnd1' Grz GN Gn' N8; lia| exact PZ] |] end.
intros [] s'' ms'' PZP. unfold pz_post in PZP. rewrite Hsp in PZP. unname_sp.
destruct PZP as (f0 & f1 & f2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & f3 & f4 & f5 & f6 & m7 & -> & -> & MUz & WMz & MIz & STz & RTz & ZSH).
replace (ret_pc (wz 259916)) with (wz 259916) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold PZ_STACK in MUz.
assert (D8 : 8 * (n' / 8) / 8 = n' / 8) by (rewrite Z.mul_comm; apply Z.div_mul; lia). rewrite D8 in MUz, ZSH. clear PZ.
assert (ZS : forall lo' hi' z, In (lo', hi') [(bv_unsigned sp + -128 - 640, bv_unsigned sp + -128); (SH A, SH A + n' / 8)] -> lo' <= z < hi' ->
szone RE X mb msz z /\ ~ fp_RStats RE X z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
- split; [do 3 right; idtac; lia|]. split; [apply NSt| apply NDt]; lia.
- assert (NB : nbody mb msz z) by (apply NBh; lia). split; [left; exact NB|]. split; intros Fz; [exact (NBs z NB Fz)| exact (NBd z NB Fz)]. }
destruct (SZF _ _ _ MUz WMz ltac:(intros lo' hi' z Hin Hz; exact (proj1 (ZS lo' hi' z Hin Hz)))) as (FS' & FD & FSE).
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; exact (proj1 (proj2 (ZS lo' hi' z Hin Hz)))) RS7) as RSz.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (proj2 (ZS lo' hi' z Hin Hz)))) RD7) as RDz.
pose proof (FSE RSE7) as RSEz. clear FS' FD FSE ZS.
ctr P3 MUz WMz. pose proof (hjunk_wmono _ _ _ _ HJm7 WMz) as HJmz. pose proof (hjunk_wmono _ _ _ _ HJU7 WMz) as HJUz.
clear RT7 RS7 RD7 RSE7 HJm7 HJU7. try clear MI7. try clear ST7.
phase_done MU m6 m7 MUz WMz.
apply aimplT_ret.

eapply (alloc_partial_sec RE X n mb gp RL Hn HP MBP MBK MBC AVO AVP); [exact RTz| exact MIz| exact P3|].
intros m8 p0 p1 p2 p3 p4 p5 p6 p7 p8 p10 p11 p12 p14 p15 p16 p17 p22 MU8 WM8 MI9 RT9 P3'.
fold AB A n' in MU8, P3' |- *.
assert (ZS : forall lo' hi' z, In (lo', hi') [(SH A + n' / 8, SH A + ngran n')] -> lo' <= z < hi' ->
szone RE X mb msz z /\ ~ fp_RStats RE X z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[]]; injection E as <- <-.
assert (NB : nbody mb msz z) by (apply NBh; lia). split; [left; exact NB|]. split; intros Fz; [exact (NBs z NB Fz)| exact (NBd z NB Fz)]. }
destruct (SZF _ _ _ MU8 WM8 ltac:(intros lo' hi' z Hin Hz; exact (proj1 (ZS lo' hi' z Hin Hz)))) as (FS' & FD & FSE).
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; exact (proj1 (proj2 (ZS lo' hi' z Hin Hz)))) RSz) as RS9.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (proj2 (ZS lo' hi' z Hin Hz)))) RDz) as RD9.
pose proof (FSE RSEz) as RSE9. clear FS' FD FSE ZS.
pose proof (hjunk_wmono _ _ _ _ HJmz WM8) as HJm9. pose proof (hjunk_wmono _ _ _ _ HJUz WM8) as HJU9.
clear P3 RTz RSz RDz RSEz HJmz HJUz. try clear MIz.
phase_done MU m7 m8 MU8 WM8.
match goal with H : stk asegs m8 lo _ |- _ => rename H into ST9 end.

eapply (alloc_stats_sec RE X n mb gp RL Hn HP MBP MBK MBC AVO AVP); [exact RT9| exact RS9| exact MI9| exact ST9| exact CEIL'| lia|].
intros m9 f10 f11 f12 f13 f14 f15 f16 f17 f20 f21 f22 f24 f25 f26 f27 MU9 WM9 MI10 ST10 RT10 RS10.
fold AB A n' ssz in MU9 |- *.
assert (ZS : forall lo' hi' z, In (lo', hi') [(bv_unsigned sp - 160, bv_unsigned sp - 128); (rl_T X + 2800, rl_T X + 2824); (rl_T X + 2904, rl_T X + 2904 + 8)] -> lo' <= z < hi' ->
szone RE X mb msz z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- split; [do 3 right; idtac; lia| apply NDt; lia].
- assert (FSt : fp_RStats RE X z) by (left; split; cbn [fst snd]; lia). split; [right; left; exact FSt| intros Fz; exact (NSd z Fz FSt)].
- assert (FSt : fp_RStats RE X z) by (left; split; cbn [fst snd]; lia). split; [right; left; exact FSt| intros Fz; exact (NSd z Fz FSt)]. }
destruct (SZF _ _ _ MU9 WM9 ltac:(intros lo' hi' z Hin Hz; exact (proj1 (ZS lo' hi' z Hin Hz)))) as (FS' & FD & FSE).
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (ZS lo' hi' z Hin Hz))) RD9) as RD10.
pose proof (FSE RSE9) as RSE10. clear FS' FD FSE ZS.
ctr P3' MU9 WM9. pose proof (hjunk_wmono _ _ _ _ HJm9 WM9) as HJm10. pose proof (hjunk_wmono _ _ _ _ HJU9 WM9) as HJU10.
clear RT9 RS9 RD9 RSE9 HJm9 HJU9. try clear MI9. try clear ST9.
unhide TD. phase_done MU m8 m9 MU9 WM9. hide TD.

assert (HJA : hjunk m9 A (AB + (msz - 4096))).
{ eapply hjunk_merge; [| exact HJU10]. eapply zeros_hjunk; [exact UZ| lia| subst A AB; lia]. }
assert (UZc : cf = 0 -> rw_cells asegs m9 A [CB (Z.to_nat n) (repeat (b8 0) (Z.to_nat n))]) by (intros _; exact UZ). clear UZ.
eapply (alloc_fill_sec RE X n mb gp RL Hn HP MBP MBK MBC AVO AVP); [exact RT10| exact MI10| exact ST10| exact CEIL'| lia| exact FR5| exact CF| exact HJA|].
intros m10 i0 i1 i2 i3 i4 i5 i6 i7 i8 i10 i11 i12 i14 i15 i16 i17 MU10 WM10 MI11 ST11 RT11 FR11 HJU11 E0.
fold AB A n' in MU10, HJU11 |- *.
assert (ZS : forall lo' hi' z, In (lo', hi') [(A, A + Z.min n' 4096)] -> lo' <= z < hi' ->
szone RE X mb msz z /\ ~ fp_RStats RE X z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[]]; injection E as <- <-.
assert (NB : nbody mb msz z) by (apply NBb; lia). split; [left; exact NB|]. split; intros Fz; [exact (NBs z NB Fz)| exact (NBd z NB Fz)]. }
destruct (SZF _ _ _ MU10 WM10 ltac:(intros lo' hi' z Hin Hz; exact (proj1 (ZS lo' hi' z Hin Hz)))) as (FS' & FD & FSE).
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; exact (proj1 (proj2 (ZS lo' hi' z Hin Hz)))) RS10) as RS11.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (proj2 (ZS lo' hi' z Hin Hz)))) RD10) as RD11.
pose proof (FSE RSE10) as RSE11. clear FS' FD FSE ZS.
ctr P3' MU10 WM10. pose proof (hjunk_wmono _ _ _ _ HJm10 WM10) as HJm11.
assert (UZc' : cf = 0 -> rw_cells asegs m10 A [CB (Z.to_nat n) (repeat (b8 0) (Z.to_nat n))]) by (intros E; rewrite (E0 E); exact (UZc E)). clear UZc E0.
clear FR5 HJA RT10 RS10 RD10 RSE10 HJm10 HJU10. try clear MI10. try clear ST10.
phase_done MU m9 m10 MU10 WM10.

eapply (alloc_fin_sec RE X n mb gp RL Hn HP MBP MBK MBC AVO AVP); [exact RT11| exact MI11| exact ST11| exact CEIL'| lia| exact FR11| exact HDR6| intros _; exact MG|].
intros m11 k0 k1 k3 k4 k5 k6 k7 k10 k11 k12 k14 k15 k16 k17 MU11 WM11 MI12 ST12 RT12 HDR12 MG12.
fold AB A n' in MU11, HDR12, MG12 |- *.
assert (ZS : forall lo' hi' z, In (lo', hi') [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (A + -16, A)] -> lo' <= z < hi' ->
szone RE X mb msz z /\ ~ fp_RStats RE X z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- split; [do 3 right; idtac; lia|]. split; [apply NSt| apply NDt]; lia.
- assert (NB : nbody mb msz z) by (apply NBb; lia). split; [left; exact NB|]. split; intros Fz; [exact (NBs z NB Fz)| exact (NBd z NB Fz)].
- assert (NB : nbody mb msz z) by (apply NBb; lia). split; [left; exact NB|]. split; intros Fz; [exact (NBs z NB Fz)| exact (NBd z NB Fz)]. }
destruct (SZF _ _ _ MU11 WM11 ltac:(intros lo' hi' z Hin Hz; exact (proj1 (ZS lo' hi' z Hin Hz)))) as (FS' & FD & FSE).
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; exact (proj1 (proj2 (ZS lo' hi' z Hin Hz)))) RS11) as RS12.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (proj2 (ZS lo' hi' z Hin Hz)))) RD11) as RD12.
pose proof (FSE RSE11) as RSE12. clear FS' FD FSE ZS.
ctr P3' MU11 WM11. ctr UZc' MU11 WM11. pose proof (hjunk_wmono _ _ _ _ HJm11 WM11) as HJm12. pose proof (hjunk_wmono _ _ _ _ HJU11 WM11) as HJU12.
clear FR11 HDR6 MG RT11 RS11 RD11 RSE11 HJm11 HJU11. try clear MI11. try clear ST11.
phase_done MU m10 m11 MU11 WM11.

apply evt_done. unfold alloc_post_sec. do 15 eexists. exists m11.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [exact MI12|]. split; [exact ST12|].
split; [exact RT12|]. split; [exact RS12|]. split; [exact RD12|].
split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn6; split; [split; [unfold DP_N; exact DNC6| exact DNP6]| exact DNR6]]|].
split; [exact OBJ6|]. split; [exact TRQ6|].
exists mb. cbv zeta. fold msz.
split; [reflexivity|]. split; [exact REG|]. split; [exact TQ|]. split; [exact GQ|]. split; [exact CLS|]. split; [exact CI|]. split; [exact NX|].
split; [unhide NR; exact NR|]. split; [exact SPN|]. split; [rewrite KP; exact MBP|]. split; [exact MBKr|]. split; [exact MBC|]. split; [exact ZA|].
split; [subst A AB; rewrite KU, Grz; f_equal; lia|].
split. { rewrite SHM. unfold alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_INSTANCE. exact MU. }
split; [exact RSE12|].
change (sec_map_size n) with msz in HJU12.
assert (CM : chunk_mem m11 AB (AB + (msz - 4096)) A n).
{ destruct (fas_split m11 (SH AB) 256 1 FA1 ltac:(lia)) as [P1 Q1]. apply fas_one in P1.
pose proof (hb1_facts (b8 0)) as [_ HBF].
eapply (slot_chunk m11 AB (msz - 4096) n (hb1f (b8 0)) (wz id));
[lia| rewrite Grz; lia| rewrite Grz; reflexivity| subst AB; clear - MBP; Z.div_mod_to_equations; lia
| fold n'; rewrite NG3, Grz; subst up A AB; clear - K2 Grz; lia| clear - K2; Z.div_mod_to_equations; lia| subst AB; lia| lia| exact HBF
| intros _; exact (MG12 ltac:(rewrite Grz; lia))| exact HJm12| exact HDR12| exact HJU12| exact P1
| rewrite Grz; change (2048 / 8 - 1) with 255; exact Q1
| intros _; fold n' A; exact ZSH| exact P3'|].
fold n' A. replace (SH A + ngran n') with (SH up) by (rewrite SHU, SHA; lia).
replace ((msz - 4096 - rz_size n - round_up n' 8) / 8) with k2 by (subst k2 up; rewrite NG3; f_equal; subst A; lia). exact FA2. }
split.
- rewrite KP, KU. replace (mb + msz) with (AB + (msz - 4096)) by (subst AB; lia). replace (mb + 6144) with A by (subst A AB; rewrite Grz; lia). exact CM.
- intros E. rewrite KU. replace (mb + 6144) with A by (subst A AB; rewrite Grz; lia). exact (UZc' E).
Qed.
End S.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyW2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyW2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsGW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsGW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUxU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUxU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNwL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu1d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu1d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqLk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqLk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkfD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkfD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkJ4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkJ4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmvA.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFd5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFd5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsDw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsDw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRfV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRfV.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcYs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcYs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpzM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpzM.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpzM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpzM.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcYs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcYs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcYs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcYs.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcfN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcfN.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVo2.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVo2.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Lemma too_big_sec : forall n, 0 <= n <= 2^26 -> from_primary n = false -> too_big n = false.
Proof.
intros n Hn HP. unfold too_big. rewrite HP. unfold kMaxAllowedMalloc.
pose proof (needed_facts n ltac:(lia)) as NF. pose proof (rz_size_range n) as [R1 _].
replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb]. apply Z.ltb_ge. lia.
Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Let atn := at_nodeA L asegs.
Hypothesis large_alloc_spec : large_alloc_stmt RE X L.
Hypothesis poison_zero_spec : poison_zero_stmt_lh RE X L.

Definition alloc_W_sec (sp : Z) : list (Z * Z) :=
[ (sp - ALLOC_STACK, sp); (0x171d60, 0x171d61); (rl_T X + 2800, rl_T X + 3168);
(A_INSTANCE + 104, A_INSTANCE + 728); (ptrarr_lo RE, ptrarr_lo RE + 0x800000);
(SS_BASE, DP_END); (rl_dn X, rl_dn X + 0x100000); (rl_ssb X, rl_ssb X + 0x800000) ].

Definition alloc_post_sec (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (LB : list ablock) (n cf lo : Z) (m : word -> option byte) (obj tsz : Z) (q : list word)
(r : option aptr * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ RDepot RE X m' /\ depot_step m m'
/\ rw_cells asegs m' obj [C8 (wz (obj + 16)); C8 (wz tsz)] /\ u64arr asegs m' (obj + 16) q
/\ match r with
| (None, a1) => a0 = wz 0 /\ a1 = a /\ munch (alloc_W_sec (bv_unsigned sp)) m m' /\ RSec a LB RE X m'
| (Some p, a1) => exists mb, let msz := sec_map_size n in
p = ASec mb n
/\ as_reg a1 = as_reg a ++ [mkSec mb msz n]
/\ as_tq a1 = as_tq a /\ as_gq a1 = as_gq a /\ (forall c, cls a1 c = cls a c)
/\ as_cache_inited a1 = as_cache_inited a /\ as_next a1 = as_next a
/\ (as_nres a1 = as_nres a \/ as_nres a1 = as_nres a + kPtrArrBlock)
/\ as_spent a1 = as_spent a + sec_cost msz
/\ mb mod kPage = 0 /\ appr mb msz /\ mb + msz <= band_lo /\ zavoids mb msz (avoid_of (ae_L RE) a) = true
/\ a0 = wz (mb + kSecUserOff)
/\ munch (alloc_W_sec (bv_unsigned sp) ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m m'
/\ RSec a1 LB RE X m'
/\ chunk_mem m' (mb + kPage) (mb + msz) (mb + kSecUserOff) n
/\ (cf = 0 -> rw_cells asegs m' (mb + kSecUserOff) [CB (Z.to_nat n) (repeat (b8 0) (Z.to_nat n))])
end.

Lemma allocate_sec_spec : forall ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (LB : list ablock) (FS : list fframe)
(n cf lo obj tsz dn : Z) (q : list word),
gcons a LB FS G RE X ->
RTconst RE X m -> RStats RE X m -> RSec a LB RE X m -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ALLOC_STACK ->
0 <= n <= 2^26 -> from_primary n = false -> 0 <= cf <= 1 ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz tsz)] -> u64arr asegs m (obj + 16) q -> Z.of_nat (length q) = 30 ->
1 <= tsz <= 30 -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= obj -> obj + 256 < 2^64 ->
aimplT atn (asan_malloc (ae_L RE) a n) s
(alloc_post_sec ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB n cf lo m obj tsz q)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz n) (wz 8) (wz obj) (wz 1) (wz cf) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz allocate_entry) fc None m (seg_rom asegs)).
Proof.
intros until q; intros GC RT RS RSE RD MI ST CEIL LO Hn HP CF OBJ TRQ LQ SZR DNH DCAP OB1 OB2.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof (rlay_avoid RE X RL) as AVC.
pose proof CEIL as CEIL'. idtac. unfold ALLOC_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & PC & _ & QK & QC & _). unfold prim_hi in PC. unfold ptrarr_hi in QC. idtac. rewrite ?KHI_eq in PK.
clear TA TD. change (al_space_beg (ae_L RE)) with (prim_lo RE) in PC. change (al_ptrarr (ae_L RE)) with (ptrarr_lo RE) in QC.
apply appr_to_lia in QK; [| lia| lia].
pose proof (sec_geom_facts n Hn HP) as (GN & Grz & Gn' & _ & Gnd1 & Gssz & _ & GM1 & GndE).
pose proof (munch_refl (alloc_W_sec (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_INSTANCE in MU.
apply aimplT_from_evt.

eapply alloc_pre1; [exact RT| exact RL| exact MI| exact ST| exact CEIL'| lia| lia| lia|].
intros m1 u0 u1 u2 u3 v1 v2 v3 v4 v5 v6 v7 u4 u5 u6 u7 fj MU1 WM1 MI1 ST1 FR1.
assert (RT1 : RTconst RE X m1) by (eapply RTconst_munch; [exact RT| exact MU1| exact WM1| apply Forall_cons; [apply rt_avoid_stack; [exact RL| lia]| apply Forall_nil]]).
assert (RS1 : RStats RE X m1) by (eapply RStats_munch; [exact RS| exact MU1| exact WM1| apply Forall_cons; [st_avoid_solve| apply Forall_nil]]).
assert (RSE1 : RSec a LB RE X m1).
{ eapply RSec_frame; [exact RSE| exact WM1|]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z Fz _. cbn [outside]. split; [| exact I].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)). lia. }
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame; [exact RD| exact WM1|]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z Fz _. cbn [outside]. split; [| exact I].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). lia. }
phase_done MU m m1 MU1 WM1. clear MI RT RS RSE RD.
eapply alloc_rzlog; [lia|]. intros a0'.
eapply alloc_pre3_sec; [exact RT1| exact RL| exact MI1| exact ST1| exact CEIL'| lia| exact Hn| exact HP|].
intros m2 w0 w1 w2 w3 x0 x1 x2 x3 x4 x5 x6 x7 w4 w5 w6 w7 MU2 WM2 MI2 ST2.
assert (RT2 : RTconst RE X m2) by (eapply RTconst_munch; [exact RT1| exact MU2| exact WM2| apply Forall_cons; [apply rt_avoid_stack; [exact RL| lia]| apply Forall_nil]]).
assert (RS2 : RStats RE X m2) by (eapply RStats_munch; [exact RS1| exact MU2| exact WM2| apply Forall_cons; [st_avoid_solve| apply Forall_nil]]).
assert (RSE2 : RSec a LB RE X m2).
{ eapply RSec_frame; [exact RSE1| exact WM2|]. eapply agree_on_of_munch; [exact MU2| exact WM2|]. intros z Fz _. cbn [outside]. split; [| exact I].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)). lia. }
assert (RD2 : RDepot RE X m2).
{ eapply RDepot_frame; [exact RD1| exact WM2|]. eapply agree_on_of_munch; [exact MU2| exact WM2|]. intros z Fz _. cbn [outside]. split; [| exact I].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). lia. }
phase_done MU m1 m2 MU2 WM2. clear MI1 RT1 RS1 RSE1 RD1. try clear ST1.

pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp - 128)] m2) as MUs. pose proof (wmono_refl asegs m2) as WMs.
step. call_sp_ch (get_current_thread_spec RE X) ltac:(fun _ => idtac); [exact RT2| exact RL| assumption| exact ST2| exact CEIL'| lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST3 end.
match goal with H : RTconst RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RT3; rename H2 into MI3 end.
lazymatch type of MUs with munch _ _ ?mm =>
assert (RS3 : RStats RE X mm) by (eapply RStats_munch; [exact RS2| exact MUs| exact WMs| apply Forall_cons; [st_avoid_solve| apply Forall_nil]]);
assert (RSE3 : RSec a LB RE X mm) by
(eapply RSec_frame; [exact RSE2| exact WMs|]; eapply agree_on_of_munch; [exact MUs| exact WMs|]; intros z Fz _; cbn [outside]; split; [| exact I];
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)); lia);
assert (RD3 : RDepot RE X mm) by
(eapply RDepot_frame; [exact RD2| exact WMs|]; eapply agree_on_of_munch; [exact MUs| exact WMs|]; intros z Fz _; cbn [outside]; split; [| exact I];
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)); lia)
end.
clear MUs WMs RT2 RS2 RSE2 RD2. try clear ST2. try clear MI2.
step.
step. ifz.
step. stp. step. step.
step.
apply evt_done.
unfold asan_malloc. rewrite (too_big_sec n Hn HP), HP.
replace (needed n + rz_size n) with (sec_size n) by reflexivity.
name_sp sp (-128). rewrite <- Hsp in ST3.
lazymatch goal with |- aimplT _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
eapply aimplT_bind;
[eapply (combined_sec_spec L RE X large_alloc_spec _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm s a LB FS G n lo);
[exact GC| exact AVC| exact RT3| exact RS3| exact RSE3| exact MI3| exact ST3| exact CEIL'| rewrite Hsp; unfold COMB_STACK; lia| exact Hn| exact HP] |] end.
intros [r a1] s' ms' PO. unfold combs_post in PO. rewrite Hsp in PO. unname_sp.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & -> & -> & MI4 & ST4 & WM3 & RT4 & RS4 & REST).
replace (ret_pc (wz 258824)) with (wz 258824) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_frame in FR1.

assert (RDK : forall mm W (P : Z -> Prop), (forall z, P z -> fp_RDepot RE X z -> False) -> munch W x22 mm -> wmono asegs x22 mm ->
(forall lo' hi' z, In (lo', hi') W -> lo' <= z < hi' -> fp_RStats RE X z \/ fp_RSec a RE X z \/ band_lo <= z \/ P z) -> RDepot RE X mm).
{ intros mm W P HP0 MUw WMw HW. eapply RDepot_frame; [exact RD3| exact WMw|]. eapply agree_on_of_munch; [exact MUw| exact WMw|]. intros z Fz _. apply outside_intro.
intros lo' hi' Hin Hz. destruct (HW lo' hi' z Hin Hz) as [P1|[P1|[P1|P1]]].
- exact (fpS_excl _ _ _ _ _ _ GC z P1 ltac:(do 2 right; left; exact Fz)).
- exact (fpD_excl _ _ _ _ _ _ GC z Fz ltac:(right; left; exact P1)).
- pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). lia.
- exact (HP0 z P1 Fz). }
assert (WLZ : forall (P : Z -> Prop) lo' hi' z, In (lo', hi') ((bv_unsigned sp + -128 - 48, bv_unsigned sp + -128) :: W_large (bv_unsigned sp + -128 - 48) RE X) -> lo' <= z < hi' ->
fp_RStats RE X z \/ fp_RSec a RE X z \/ band_lo <= z \/ P z).
{ intros P lo' hi' z Hin Hz. unfold W_large, LARGE_STACK in Hin. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-.
- do 2 right; left. idtac. lia.
- do 2 right; left. idtac. lia.
- right; left. left. split; cbn [fst snd]; lia.
- right; left. right; left. split; cbn [fst snd]; lia.
- left. left. split; cbn [fst snd]; lia. }
destruct r as [mb|].
2:{
destruct REST as (-> & -> & MU3 & RSE4). apply aimplT_ret.
pose proof (RDK m3 _ (fun _ => False) ltac:(intros z FF _; exact FF) MU3 WM3 (WLZ _)) as RD4.
unfold W_large, LARGE_STACK, A_INSTANCE in MU3.
lazymatch type of MU3 with munch _ ?mp _ => phase_done MU mp m3 MU3 WM3 end.
clear RD3 RT3 RS3 RSE3. try clear MI3. try clear ST3.
step.
step. if_lit.
pose proof (munch_refl [(0x171d60, 0x171d61); (bv_unsigned sp - 144, bv_unsigned sp - 128)] m3) as MUs. pose proof (wmono_refl asegs m3) as WMs.
step. call_sp_ch (set_oom_spec RE X) ltac:(fun _ => idtac); [exact RS4| assumption| exact ST4| exact CEIL'|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST5 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS5; rename H2 into MI5 end.
lazymatch type of MUs with munch _ _ ?mm =>
assert (RT5 : RTconst RE X mm) by
(eapply RTconst_frame; [exact RT4| exact WMs|]; eapply agree_on_of_munch; [exact MUs| exact WMs|]; intros z Fz _; cbn [outside]; split; [| split; [| exact I]];
[ destruct (Z.eq_dec z 0x171d60) as [->|NE]; [exfalso; exact (fpS_excl _ _ _ _ _ _ GC 0x171d60 ltac:(do 2 right; reflexivity) ltac:(do 4 right; exact Fz))| lia]
| pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(left; exact Fz)); lia ]);
assert (RSE5 : RSec a LB RE X mm) by
(eapply RSec_frame; [exact RSE4| exact WMs|]; eapply agree_on_of_munch; [exact MUs| exact WMs|]; intros z Fz _; cbn [outside]; split; [| split; [| exact I]];
[ destruct Fz as [Fz|[Fz|[Fz|Fz]]]; [destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; unfold A_INSTANCE in *; lia| destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; lia
| destruct Fz as (e & He & Hz); pose proof (sec_facts _ _ _ _ _ _ GC e He) as (_ & E2 & _ & E4 & E5 & E6 & _);
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [SG _]; unfold kPage in Hz; clear - E2 E4 SG Hz E6; lia
| destruct Fz as (e & He & Hz); pose proof (hdr_band _ _ _ _ _ _ GC e z He Hz); lia]
| pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)); lia ]);
assert (RD5 : RDepot RE X mm) by
(eapply RDepot_frame; [exact RD4| exact WMs|]; eapply agree_on_of_munch; [exact MUs| exact WMs|]; intros z Fz _; cbn [outside];
assert (B : 0x1c19c8 <= z < 0x645000 \/ (0 < z < 0x10000) \/ (0x645000 <= z < band_lo)) by (destruct Fz as [[F1 F2]|[[F1 F2]|[[F1 F2]| ->]]]; cbn [fst snd] in *; lia); lia)
end.
clear MUs WMs RT4 RSE4 RD4 RS4.
step. call0 (may_return_null_spec RE X); [exact RT5| assumption|]. subst_words.
step. if_lit.
stp. step.
step. do 13 step. step.
release_frame FR1 ST5 (bv_unsigned sp).
step.
apply evt_done. unfold alloc_post_sec. do 16 eexists.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST5|].
split; [exact RT5|]. split; [exact RS5|]. split; [exact RD5|].
split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn; split; [split; [unfold DP_N; exact DNC| exact DNP]| lia]]|].
split; [exact OBJ|]. split; [exact TRQ|].
cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [| exact RSE5].
unfold alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_INSTANCE. exact MU. }

destruct REST as (-> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & MU3 & RSE4 & BODY & HJ & FAS).
rewrite KP in BODY, HJ, FAS, MBP. pose proof MBK as MBKr. apply appr_to_lia in MBK; [| pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG0 _]; lia| lia]. pose proof MBK as MBK'. pose proof MBC as MBC'. idtac.
set (msz := sec_map_size n) in *. set (ssz := sec_size n) in *.
destruct (zavoid_facts RE X a mb msz AVC ltac:(lia) ZA) as (AVO & AVP & AVQ & AVR).
assert (SOK : sec_ok RE X (mkSec mb msz n)).
{ unfold sec_ok. cbn [se_beg se_size se_req]. split; [rewrite <- KP in MBP; exact MBP|]. split; [exact MBKr|]. split; [exact MBC|]. split; [reflexivity|]. split; [exact HP|]. split; [lia|].
split; [unfold iv_disjoint; cbn [fst snd]; lia|]. split; [unfold iv_disjoint; cbn [fst snd]; lia|].
apply List.Forall_forall. intros o Ho. unfold iv_disjoint. cbn [fst snd]. destruct (AVO o Ho); lia. }
pose proof (gcons_reg_add a a1 LB FS G RE X mb msz n GC REG CLS NX SOK AVR ltac:(lia)) as GC1.
pose proof (nmap_RDepot a LB FS G RE X GC mb msz MBP MBK MBC ltac:(lia) AVO AVP AVQ AVR) as ZND.
assert (SHM : SH (mb + msz) = SH mb + msz / 8) by (rewrite <- SH_plus8; f_equal; pose proof (sec_geom_facts n Hn HP); clear - MBP H; Z.div_mod_to_equations; lia).
pose proof (RDK m3 _ (nmap mb msz) ZND MU3 WM3 ltac:(intros lo' hi' z Hin Hz; apply in_app_iff in Hin; destruct Hin as [Hin|Hin];
[exact (WLZ _ lo' hi' z Hin Hz)| cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-; do 3 right;
[left; exact Hz| right; split; cbn [fst snd]; lia]])) as RD4.
assert (MS8 : 8 * (msz / 8) = msz /\ 4096 + ssz <= msz) by (pose proof (sec_geom_facts n Hn HP) as (_ & _ & _ & _ & _ & _ & G7 & G8 & _); fold msz ssz in G7, G8; clear - G7 G8; Z.div_mod_to_equations; lia).
pose proof (sec_geom_facts n Hn HP) as (GN' & _ & _ & _ & Gnd1' & Gssz' & _ & _ & _). fold ssz in Gssz'.
assert (MBH : 0x645000 <= mb) by (clear - MBK MS8 GN' Gnd1' Gssz'; lia).
assert (SHB : 0x80000000 <= SH mb /\ SH mb + msz / 8 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; clear - MBH MBC' MS8; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD.
rewrite SHM in MU3. unfold W_large, LARGE_STACK, A_INSTANCE in MU3.

apply (munch_weaken _ (((bv_unsigned sp - 1152, bv_unsigned sp) :: (1514848, 1514849) :: (rl_T X + 2800, rl_T X + 3168) :: (967832 + 104, 967832 + 728)
:: (ptrarr_lo RE, ptrarr_lo RE + 8388608) :: (1841608, 6363632) :: (rl_dn X, rl_dn X + 1048576) :: (rl_ssb X, rl_ssb X + 8388608) :: nil)
++ [(mb, mb + msz); (SH mb, SH mb + msz / 8)])) in MU.
2:{ intros z Hz. cbn [outside app] in Hz |- *. clear - Hz. tauto. }
cbn [app] in MU.
cbn [app] in MU3.
lazymatch type of MU3 with munch _ ?mp _ => phase_done MU mp m3 MU3 WM3 end.
clear RD3 RT3 RS3 RSE3. try clear MI3. try clear ST3.
rewrite KP. apply aimplT_from_evt.
step.
step. unfold_cond; cond_unsig; if_false.

destruct (sec_pieces RE X n mb RL Hn HP MBP MBK MBC AVO AVP m3 BODY HJ FAS) as (j1 & j & j2 & pb & MG & HJm & HDR & UZ & HJU & SHD1 & PZ & P3 & SHD2).
clear BODY HJ FAS.
change (sec_map_size n) with msz in HJU, SHD2.
set (AB := mb + 4096) in *. set (A := AB + rz_size n) in *. set (n' := used_size n) in *.
set (up := A + 8 * ngran n') in *.
pose proof (ngran_eq n' ltac:(lia)) as (NG1 & NG2 & NG3). pose proof (round_up_8 n' ltac:(lia)) as [RU8 RUm].
assert (N8 : 0 <= n' / 8 /\ 0 <= n' mod 8 < 8 /\ n' = 8 * (n' / 8) + n' mod 8 /\ 8064 <= n' / 8) by (clear - GN Gn'; Z.div_mod_to_equations; lia).
assert (NGB : n' / 8 <= ngran n' <= n' / 8 + 1) by (rewrite NG1; unfold round_up; clear - N8; Z.div_mod_to_equations; lia).
assert (RUE : round_up n' 8 = round_up n 8) by (rewrite Gn'; reflexivity).
clear NG1 RU8.
remember (msz / 8) as q8 eqn:EQ8.
assert (SHa : SH AB = SH mb + 512) by (subst AB; rewrite <- (SH_plus8 mb 512); reflexivity).
assert (SHA : SH A = SH mb + 768) by (subst A AB; rewrite Grz, <- (SH_plus8 mb 768); f_equal; lia).
assert (SHU : SH up = SH mb + 768 + ngran n') by (subst up; rewrite <- SHA, <- SH_plus8; reflexivity).
set (k2 := (AB + (msz - 4096) - up) / 8) in *.
assert (K2 : 8 * k2 = mb + msz - up /\ up + 2048 <= mb + msz /\ 8 * q8 = msz)
by (subst k2 q8 up A AB; rewrite Grz, <- NG3; clear - MS8 Gssz GndE GM1 Gnd1 RUm RUE; Z.div_mod_to_equations; lia).
clear EQ8 MS8 RUm.

pose proof (AVO _ (T_obj RE X)) as TD. pose proof (AVO _ (dn_obj RE X)) as ND. pose proof (AVO _ (ssb_obj RE X)) as BD. cbn [fst snd] in TD, ND, BD.

hide TD. hide ND. hide BD. hide AVP. hide AVQ. hide NR.

pose proof (szone_frame a a1 LB FS G RE X mb msz n GC GC1 REG MBP MBK MBC ltac:(lia) AVO AVP AVQ AVR) as SZF.
pose proof (nbody_RStats a a1 LB FS G RE X mb msz n GC GC1 REG MBP MBK MBC ltac:(lia) AVO AVP AVQ AVR) as NBs.
pose proof (nbody_RDepot a a1 LB FS G RE X mb msz n GC GC1 REG MBP MBK MBC ltac:(lia) AVO AVP AVQ AVR) as NBd.
assert (NSt : forall z, band_lo <= z -> ~ fp_RStats RE X z) by (intros z Hz Fz; pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(right; left; exact Fz)); idtac; lia).
assert (NDt : forall z, band_lo <= z -> ~ fp_RDepot RE X z) by (intros z Hz Fz; pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)); idtac; lia).
assert (NSd : forall z, fp_RDepot RE X z -> ~ fp_RStats RE X z) by (intros z Hz Fz; exact (fpS_excl _ _ _ _ _ _ GC z Fz ltac:(do 2 right; left; exact Hz))).
assert (NBb : forall z, AB <= z < mb + msz -> nbody mb msz z) by (intros z Hz; left; subst AB; lia).
assert (NBh : forall z, SH AB <= z < SH mb + q8 -> nbody mb msz z).
{ intros z Hz. right. split; cbn [fst snd]; [subst AB; lia|]. replace ((msz - 4096) / 8) with (q8 - 512) by (clear - K2; Z.div_mod_to_equations; lia). fold AB. lia. }

eapply (alloc_hdr_sec RE X n mb gp RL Hn HP MBP MBK MBC AVO AVP); [exact RT4| exact MI4| exact ST4| exact CEIL'| lia| exact FR1| exact HDR|].
intros m4 h0 h1 h2 h3 h5 h6 h7 MU4 WM4 MI5 ST5 FR5 HDR5 RT5.
fold msz ssz AB A n' in MU4, HDR5 |- *.
destruct (SZF _ _ _ MU4 WM4 ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; left; apply NBb; lia)) as (FS' & FD & FSE).
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; intros Fz; exact (NBs z ltac:(apply NBb; lia) Fz)) RS4) as RS5.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; intros Fz; exact (NBd z ltac:(apply NBb; lia) Fz)) RD4) as RD5.
pose proof (FSE RSE4) as RSE5. clear FS' FD FSE.
ctr P3 MU4 WM4. pose proof (hjunk_wmono _ _ _ _ HJm WM4) as HJm5. pose proof (hjunk_wmono _ _ _ _ HJU WM4) as HJU5.
clear HDR FR1 RS4 RD4 RSE4 RT4 HJm HJU. try clear MI4. try clear ST4.
phase_done MU m3 m4 MU4 WM4.

eapply (alloc_depot_sec RE X n mb gp RL Hn HP MBP MBK MBC AVO AVP);
[exact RT5| exact RD5| exact MI5| exact ST5| exact CEIL'| lia| exact OBJ| exact TRQ| exact LQ| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| lia| lia| exact HDR5|].
intros m5 d0 d1 d2 d5 d6 d7 d10 d11 d12 d13 d14 d15 d16 d17 id MU5 WM5 MI6 ST6 RT6 RD6 OBJ6 TRQ6 ID (dn6 & [DNC6 DNP6] & DNR6) HDR6. unfold DP_N in DNC6.
fold msz ssz AB A n' in MU5, HDR6 |- *. unfold depot_W, SS_BASE, DP_END in MU5. clear OBJ TRQ.
destruct (SZF _ _ _ MU5 WM5 ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-;
[left; apply NBb; lia| do 3 right; idtac; lia| do 2 right; left; left; split; cbn [fst snd]; lia
| do 2 right; left; right; left; split; cbn [fst snd]; lia| do 2 right; left; do 2 right; left; split; cbn [fst snd]; lia])) as (FS' & FD & FSE).
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-;
[intros Fz; exact (NBs z ltac:(apply NBb; lia) Fz)| apply NSt; lia| apply NSd; left; split; cbn [fst snd]; lia
| apply NSd; right; left; split; cbn [fst snd]; lia| apply NSd; do 2 right; left; split; cbn [fst snd]; lia]) RS5) as RS6.
pose proof (FSE RSE5) as RSE6. clear FS' FD FSE.
ctr P3 MU5 WM5. pose proof (hjunk_wmono _ _ _ _ HJm5 WM5) as HJm6. pose proof (hjunk_wmono _ _ _ _ HJU5 WM5) as HJU6.
clear HDR5 RT5 RS5 RD5 RSE5 HJm5 HJU5. try clear MI5. try clear ST5.
unhide ND. unhide BD. phase_done MU m4 m5 MU5 WM5. hide ND. hide BD.

pose proof (RSec_hdr_last a a1 LB FS G RE X mb msz n GC GC1 REG MBP MBK MBC ltac:(lia) AVO AVP AVQ AVR LB m5 RSE6) as HDRS. fold ssz in HDRS.
eapply (alloc_shadow_sec RE X n mb gp RL Hn HP MBP MBK MBC AVO AVP); [exact RT6| exact MI6| exact ST6| exact CEIL'| lia| exact HDRS| exact SHD1| exact SHD2|].
intros m6 e0 e1 e2 e3 e4 e5 e6 e7 e10 e11 e12 e14 e15 e16 e17 MU6 WM6 MI7 ST7 RT7 FA1 FA2.
fold msz ssz AB A n' up k2 in MU6, FA1, FA2 |- *.
assert (ZS : forall lo' hi' z, In (lo', hi') [(bv_unsigned sp - 192, bv_unsigned sp - 128); (SH AB, SH AB + 256); (SH up, SH up + k2)] -> lo' <= z < hi' ->
szone RE X mb msz z /\ ~ fp_RStats RE X z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- split; [do 3 right; idtac; lia|]. split; [apply NSt| apply NDt]; lia.
- assert (NB : nbody mb msz z) by (apply NBh; lia). split; [left; exact NB|]. split; intros Fz; [exact (NBs z NB Fz)| exact (NBd z NB Fz)].
- assert (NB : nbody mb msz z) by (apply NBh; lia). split; [left; exact NB|]. split; intros Fz; [exact (NBs z NB Fz)| exact (NBd z NB Fz)]. }
destruct (SZF _ _ _ MU6 WM6 ltac:(intros lo' hi' z Hin Hz; exact (proj1 (ZS lo' hi' z Hin Hz)))) as (FS' & FD & FSE).
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; exact (proj1 (proj2 (ZS lo' hi' z Hin Hz)))) RS6) as RS7.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (proj2 (ZS lo' hi' z Hin Hz)))) RD6) as RD7.
pose proof (FSE RSE6) as RSE7. clear FS' FD FSE ZS.
ctr P3 MU6 WM6. pose proof (hjunk_wmono _ _ _ _ HJm6 WM6) as HJm7. pose proof (hjunk_wmono _ _ _ _ HJU6 WM6) as HJU7.
clear HDRS SHD1 SHD2 RT6 RS6 RD6 RSE6 HJm6 HJU6. try clear MI6. try clear ST6.
phase_done MU m5 m6 MU6 WM6.

stp. stp.
step.
rewrite (unsigned_lit n'), land_mask8_48 by lia. replace (n' - n' mod 8) with (8 * (n' / 8)) by lia.
step. unfold_cond; cond_unsig; if_false.
step. step. stp.
step.
apply evt_done.
replace (mb + kSecUserOff) with A by (subst A AB; rewrite KU, Grz; lia).
replace (round_down n' 8) with (8 * (n' / 8)) by (unfold round_down; lia).
name_sp sp (-128). rewrite <- Hsp in ST7.
lazymatch goal with |- aimplT _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
eapply aimplT_bind;
[eapply (poison_zero_spec _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm A (8 * (n' / 8)) lo s j);
[exact RT7| exact RL| exact MI7| exact ST7| exact CEIL'| rewrite Hsp; unfold PZ_STACK; lia
| subst A AB; clear - MBP Grz; Z.div_mod_to_equations; lia| rewrite Z.mul_comm; apply Z.mod_mul; lia| lia| rewrite ?KHI_eq; change (2^47) with 140737488355328; subst A AB;
assert (MS8 : 8 * (msz / 8) = msz /\ 4096 + ssz <= msz) by (pose proof (sec_geom_facts n Hn HP) as (_ & _ & _ & _ & _ & _ & G7 & G8 & _); fold msz ssz in G7, G8; clear - G7 G8; Z.div_mod_to_equations; lia);
clear - MBK MBH MBC MS8 Gssz' Gnd1' Grz GN Gn' N8; lia| exact PZ] |] end.
intros [] s'' ms'' PZP. unfold pz_post in PZP. rewrite Hsp in PZP. unname_sp.
destruct PZP as (f0 & f1 & f2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & f3 & f4 & f5 & f6 & m7 & -> & -> & MUz & WMz & MIz & STz & RTz & ZSH).
replace (ret_pc (wz 259360)) with (wz 259360) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold PZ_STACK in MUz.
assert (D8 : 8 * (n' / 8) / 8 = n' / 8) by (rewrite Z.mul_comm; apply Z.div_mul; lia). rewrite D8 in MUz, ZSH. clear PZ.
assert (ZS : forall lo' hi' z, In (lo', hi') [(bv_unsigned sp + -128 - 640, bv_unsigned sp + -128); (SH A, SH A + n' / 8)] -> lo' <= z < hi' ->
szone RE X mb msz z /\ ~ fp_RStats RE X z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
- split; [do 3 right; idtac; lia|]. split; [apply NSt| apply NDt]; lia.
- assert (NB : nbody mb msz z) by (apply NBh; lia). split; [left; exact NB|]. split; intros Fz; [exact (NBs z NB Fz)| exact (NBd z NB Fz)]. }
destruct (SZF _ _ _ MUz WMz ltac:(intros lo' hi' z Hin Hz; exact (proj1 (ZS lo' hi' z Hin Hz)))) as (FS' & FD & FSE).
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; exact (proj1 (proj2 (ZS lo' hi' z Hin Hz)))) RS7) as RSz.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (proj2 (ZS lo' hi' z Hin Hz)))) RD7) as RDz.
pose proof (FSE RSE7) as RSEz. clear FS' FD FSE ZS.
ctr P3 MUz WMz. pose proof (hjunk_wmono _ _ _ _ HJm7 WMz) as HJmz. pose proof (hjunk_wmono _ _ _ _ HJU7 WMz) as HJUz.
clear RT7 RS7 RD7 RSE7 HJm7 HJU7. try clear MI7. try clear ST7.
phase_done MU m6 m7 MUz WMz.
apply aimplT_ret.

eapply (alloc_partial_sec RE X n mb gp RL Hn HP MBP MBK MBC AVO AVP); [exact RTz| exact MIz| exact P3|].
intros m8 p0 p1 p2 p3 p4 p5 p6 p7 p8 p10 p11 p12 p14 p15 p16 p17 p22 MU8 WM8 MI9 RT9 P3'.
fold AB A n' in MU8, P3' |- *.
assert (ZS : forall lo' hi' z, In (lo', hi') [(SH A + n' / 8, SH A + ngran n')] -> lo' <= z < hi' ->
szone RE X mb msz z /\ ~ fp_RStats RE X z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[]]; injection E as <- <-.
assert (NB : nbody mb msz z) by (apply NBh; lia). split; [left; exact NB|]. split; intros Fz; [exact (NBs z NB Fz)| exact (NBd z NB Fz)]. }
destruct (SZF _ _ _ MU8 WM8 ltac:(intros lo' hi' z Hin Hz; exact (proj1 (ZS lo' hi' z Hin Hz)))) as (FS' & FD & FSE).
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; exact (proj1 (proj2 (ZS lo' hi' z Hin Hz)))) RSz) as RS9.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (proj2 (ZS lo' hi' z Hin Hz)))) RDz) as RD9.
pose proof (FSE RSEz) as RSE9. clear FS' FD FSE ZS.
pose proof (hjunk_wmono _ _ _ _ HJmz WM8) as HJm9. pose proof (hjunk_wmono _ _ _ _ HJUz WM8) as HJU9.
clear P3 RTz RSz RDz RSEz HJmz HJUz. try clear MIz.
phase_done MU m7 m8 MU8 WM8.
match goal with H : stk asegs m8 lo _ |- _ => rename H into ST9 end.

eapply (alloc_stats_sec RE X n mb gp RL Hn HP MBP MBK MBC AVO AVP); [exact RT9| exact RS9| exact MI9| exact ST9| exact CEIL'| lia|].
intros m9 f10 f11 f12 f13 f14 f15 f16 f17 f20 f21 f22 f24 f25 f26 f27 MU9 WM9 MI10 ST10 RT10 RS10.
fold AB A n' ssz in MU9 |- *.
assert (ZS : forall lo' hi' z, In (lo', hi') [(bv_unsigned sp - 160, bv_unsigned sp - 128); (rl_T X + 2800, rl_T X + 2824); (rl_T X + 2904, rl_T X + 2904 + 8)] -> lo' <= z < hi' ->
szone RE X mb msz z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- split; [do 3 right; idtac; lia| apply NDt; lia].
- assert (FSt : fp_RStats RE X z) by (left; split; cbn [fst snd]; lia). split; [right; left; exact FSt| intros Fz; exact (NSd z Fz FSt)].
- assert (FSt : fp_RStats RE X z) by (left; split; cbn [fst snd]; lia). split; [right; left; exact FSt| intros Fz; exact (NSd z Fz FSt)]. }
destruct (SZF _ _ _ MU9 WM9 ltac:(intros lo' hi' z Hin Hz; exact (proj1 (ZS lo' hi' z Hin Hz)))) as (FS' & FD & FSE).
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (ZS lo' hi' z Hin Hz))) RD9) as RD10.
pose proof (FSE RSE9) as RSE10. clear FS' FD FSE ZS.
ctr P3' MU9 WM9. pose proof (hjunk_wmono _ _ _ _ HJm9 WM9) as HJm10. pose proof (hjunk_wmono _ _ _ _ HJU9 WM9) as HJU10.
clear RT9 RS9 RD9 RSE9 HJm9 HJU9. try clear MI9. try clear ST9.
unhide TD. phase_done MU m8 m9 MU9 WM9. hide TD.

assert (HJA : hjunk m9 A (AB + (msz - 4096))).
{ eapply hjunk_merge; [| exact HJU10]. eapply zeros_hjunk; [exact UZ| lia| subst A AB; lia]. }
assert (UZc : cf = 0 -> rw_cells asegs m9 A [CB (Z.to_nat n) (repeat (b8 0) (Z.to_nat n))]) by (intros _; exact UZ). clear UZ.
eapply (alloc_fill_sec RE X n mb gp RL Hn HP MBP MBK MBC AVO AVP); [exact RT10| exact MI10| exact ST10| exact CEIL'| lia| exact FR5| exact CF| exact HJA|].
intros m10 i0 i1 i2 i3 i4 i5 i6 i7 i8 i10 i11 i12 i14 i15 i16 i17 MU10 WM10 MI11 ST11 RT11 FR11 HJU11 E0.
fold AB A n' in MU10, HJU11 |- *.
assert (ZS : forall lo' hi' z, In (lo', hi') [(A, A + Z.min n' 4096)] -> lo' <= z < hi' ->
szone RE X mb msz z /\ ~ fp_RStats RE X z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[]]; injection E as <- <-.
assert (NB : nbody mb msz z) by (apply NBb; lia). split; [left; exact NB|]. split; intros Fz; [exact (NBs z NB Fz)| exact (NBd z NB Fz)]. }
destruct (SZF _ _ _ MU10 WM10 ltac:(intros lo' hi' z Hin Hz; exact (proj1 (ZS lo' hi' z Hin Hz)))) as (FS' & FD & FSE).
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; exact (proj1 (proj2 (ZS lo' hi' z Hin Hz)))) RS10) as RS11.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (proj2 (ZS lo' hi' z Hin Hz)))) RD10) as RD11.
pose proof (FSE RSE10) as RSE11. clear FS' FD FSE ZS.
ctr P3' MU10 WM10. pose proof (hjunk_wmono _ _ _ _ HJm10 WM10) as HJm11.
assert (UZc' : cf = 0 -> rw_cells asegs m10 A [CB (Z.to_nat n) (repeat (b8 0) (Z.to_nat n))]) by (intros E; rewrite (E0 E); exact (UZc E)). clear UZc E0.
clear FR5 HJA RT10 RS10 RD10 RSE10 HJm10 HJU10. try clear MI10. try clear ST10.
phase_done MU m9 m10 MU10 WM10.

eapply (alloc_fin_sec RE X n mb gp RL Hn HP MBP MBK MBC AVO AVP); [exact RT11| exact MI11| exact ST11| exact CEIL'| lia| exact FR11| exact HDR6| intros _; exact MG|].
intros m11 k0 k1 k3 k4 k5 k6 k7 k10 k11 k12 k14 k15 k16 k17 MU11 WM11 MI12 ST12 RT12 HDR12 MG12.
fold AB A n' in MU11, HDR12, MG12 |- *.
assert (ZS : forall lo' hi' z, In (lo', hi') [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (A + -16, A)] -> lo' <= z < hi' ->
szone RE X mb msz z /\ ~ fp_RStats RE X z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- split; [do 3 right; idtac; lia|]. split; [apply NSt| apply NDt]; lia.
- assert (NB : nbody mb msz z) by (apply NBb; lia). split; [left; exact NB|]. split; intros Fz; [exact (NBs z NB Fz)| exact (NBd z NB Fz)].
- assert (NB : nbody mb msz z) by (apply NBb; lia). split; [left; exact NB|]. split; intros Fz; [exact (NBs z NB Fz)| exact (NBd z NB Fz)]. }
destruct (SZF _ _ _ MU11 WM11 ltac:(intros lo' hi' z Hin Hz; exact (proj1 (ZS lo' hi' z Hin Hz)))) as (FS' & FD & FSE).
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; exact (proj1 (proj2 (ZS lo' hi' z Hin Hz)))) RS11) as RS12.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (proj2 (ZS lo' hi' z Hin Hz)))) RD11) as RD12.
pose proof (FSE RSE11) as RSE12. clear FS' FD FSE ZS.
ctr P3' MU11 WM11. ctr UZc' MU11 WM11. pose proof (hjunk_wmono _ _ _ _ HJm11 WM11) as HJm12. pose proof (hjunk_wmono _ _ _ _ HJU11 WM11) as HJU12.
clear FR11 HDR6 MG RT11 RS11 RD11 RSE11 HJm11 HJU11. try clear MI11. try clear ST11.
phase_done MU m10 m11 MU11 WM11.

apply evt_done. unfold alloc_post_sec. do 15 eexists. exists m11.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [exact MI12|]. split; [exact ST12|].
split; [exact RT12|]. split; [exact RS12|]. split; [exact RD12|].
split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn6; split; [split; [unfold DP_N; exact DNC6| exact DNP6]| exact DNR6]]|].
split; [exact OBJ6|]. split; [exact TRQ6|].
exists mb. cbv zeta. fold msz.
split; [reflexivity|]. split; [exact REG|]. split; [exact TQ|]. split; [exact GQ|]. split; [exact CLS|]. split; [exact CI|]. split; [exact NX|].
split; [unhide NR; exact NR|]. split; [exact SPN|]. split; [rewrite KP; exact MBP|]. split; [exact MBKr|]. split; [exact MBC|]. split; [exact ZA|].
split; [subst A AB; rewrite KU, Grz; f_equal; lia|].
split. { rewrite SHM. unfold alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_INSTANCE. exact MU. }
split; [exact RSE12|].
change (sec_map_size n) with msz in HJU12.
assert (CM : chunk_mem m11 AB (AB + (msz - 4096)) A n).
{ destruct (fas_split m11 (SH AB) 256 1 FA1 ltac:(lia)) as [P1 Q1]. apply fas_one in P1.
pose proof (hb1_facts (b8 0)) as [_ HBF].
eapply (slot_chunk m11 AB (msz - 4096) n (hb1f (b8 0)) (wz id));
[lia| rewrite Grz; lia| rewrite Grz; reflexivity| subst AB; clear - MBP; Z.div_mod_to_equations; lia
| fold n'; rewrite NG3, Grz; subst up A AB; clear - K2 Grz; lia| clear - K2; Z.div_mod_to_equations; lia| subst AB; lia| lia| exact HBF
| intros _; exact (MG12 ltac:(rewrite Grz; lia))| exact HJm12| exact HDR12| exact HJU12| exact P1
| rewrite Grz; change (2048 / 8 - 1) with 255; exact Q1
| intros _; fold n' A; exact ZSH| exact P3'|].
fold n' A. replace (SH A + ngran n') with (SH up) by (rewrite SHU, SHA; lia).
replace ((msz - 4096 - rz_size n - round_up n' 8) / 8) with k2 by (subst k2 up; rewrite NG3; f_equal; subst A; lia). exact FA2. }
split.
- rewrite KP, KU. replace (mb + msz) with (AB + (msz - 4096)) by (subst AB; lia). replace (mb + 6144) with A by (subst A AB; rewrite Grz; lia). exact CM.
- intros E. rewrite KU. replace (mb + 6144) with A by (subst A AB; rewrite Grz; lia). exact (UZc' E).
Qed.
End S.
