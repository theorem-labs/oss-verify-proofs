(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Q6sh QQwg QKTr QvDJ QJBH QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk QTVW QpY2 QOJv Q9Ho QqLk QnRU QmP7 QYyZ Qu3b QnaW QpME QkJ4 QEEn QsDw QcYs QcfN QlES QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QTVW.Mq3 QOJv.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk QnRU.Mqa QmP7.Mq0 QpY2.Mq1 Q9Ho.Mq1 QYyZ.Mq0 QnRU.Mq0 QOJv.Mq5 Qu3b.Mq2 QnaW.Mq1 QYyZ.Mq5 QYyZ.Mq3 QpME.Mq1 QkJ4 QEEn.Mq0.
Import QpY2.Mq2.
Import QsDw.Mq0 QcYs.Mq3.
Import QcfN.Mq1.
Import QlES.
Import QteI.Mq6.

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

Lemma calloc_icpt_spec : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PStateA) (a : AState) (G : ghost) (LB : list ablock) (FS : list fframe) (lo cnt sz dn : Z),
gcons a LB FS G RE X ->
RTconst RE X m -> RStats RE X m -> RPrim a G RE X m -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - CALLOC_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> from_primary (cnt * sz) = true ->
aimplT atn (asan_malloc (ae_L RE) a (cnt * sz)) s
(calloc_post RE X ra bp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G (cnt * sz) lo m)
(MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz cnt) (wz sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x632cc) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros GC RT RS RP RD MI ST CEIL LO BPR UNW DNH DCAP Hcnt Hsz HP.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof CEIL as CEIL'. idtac. unfold CALLOC_STACK, ALLOC_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (QSsj.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
unfold iv_disjoint in TD. cbn [fst snd] in TD. change (2^37) with 137438953472 in TD.
pose proof (rlay_pd RE X RL) as PD. pd_pair PD 0 1 D02. pd_pair PD 0 2 D03. clear PD.
set (n := cnt * sz) in *. assert (Hn : 0 <= n < 2^64) by (subst n; (first [ clear - CEIL' Hsz Hcnt BPR LO CEIL sz cnt lo bp BAND; nia | nia ])).
pose proof HP as HP'. apply from_primary_iff in HP'. unfold kMaxSize in HP'.
pose proof (class_of_facts n ltac:(lia) HP) as (Hc & _). cbv zeta in Hc. set (c := class_of n) in *.
pose proof (needed_facts n ltac:(lia)) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (SHB1 : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite FB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. (first [ clear - H9 q1 H5 H4 r0 q0 H0 H r q PH PCH PK PAL r1 Hc c TB n sz cnt X RE BAND; lia | lia ]). }
pose proof SH_band as SHBD0.
assert (SHB2 : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. (first [ clear - H9 q1 H5 H4 r0 q0 H0 H r q PH PCH PK PAL r1 Hc c TB n sz cnt X RE BAND; lia | lia ]). }
pose proof SH_band as SHBD1.
pose proof (gc_bounds _ _ _ _ _ _ GC c ltac:(rewrite K32; lia)) as (AU1 & AU2 & AU3). rewrite KO in AU2.
assert (SHB3 : SH (reg_beg (ae_L RE) c) <= SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048). apply SH_le. lia. }
clear PAL AU3.
pose proof (QSsj.rlay_obj_facts RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC. idtac. rewrite ?KHI_eq in NK.
pose proof (QSsj.rlay_obj_facts RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC. idtac. rewrite ?KHI_eq in BK.
pose proof (munch_refl (calloc_W RE X bp c (c_alloc_user (cls a c))) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold calloc_W, CALLOC_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
apply aimplT_from_evt.
eapply calloc_icpt_pre; [exact RT| exact RL| exact (RDepot_unw RE X _ RD)| exact MI| exact ST| exact CEIL'| unfold CALLOC_STACK, ALLOC_STACK; lia| exact BPR| exact UNW| lia| lia|].
intros m1 u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u13 tsz q rest junk8 junk8b MU1 WM1 MI1 ST1 J8 OBJ LQ SZR FR RT1 TU1.
unfold cicpt_W in MU1.
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU1| exact WM1|]. constructor; [first [st_avoid_solve| eapply st_avoid_T; [eassumption| lia| lia]]|]. constructor; [st_avoid_solve| constructor]. }
assert (RP1 : RPrim a G RE X m1).
{ eapply RPrim_frame; [exact RP| exact WM1|]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z Fz _. cbn [outside].
pose proof (fp_RPrim_lt_ceil G RE X z RL Fz). idtac.
split; [lia|]. split; [| exact I]. assert (z <> rl_T X + 3168) by (intros ->; exact (fpP_RDepot _ _ _ _ _ _ GC _ Fz ltac:(do 3 right; reflexivity))). lia. }
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame_unw; [exact RL| exact RD| exact WM1| | exact TU1]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z [Fz NZ] _. cbn [outside].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). idtac. (first [ clear - H NZ z LQ ks q BC NC PH PCH PK RZ1 NF TD TB TK CEIL' n LO sz cnt lo bp X RE BAND; lia | lia ]). }
phase_done MU m m1 MU1 WM1. clear RT RS RP RD MI. try clear ST.
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
rewrite (Z.div_small (sz * cnt) (2^64)) by (first [ clear - NZ LQ ks q BC BK NC NK PH PCH PK RZ2 RZ1 NF HP' Hn D03 D02 TD TB TK CEIL' n Hsz BPR LO CEIL sz cnt lo bp X RE BAND; nia | nia ]).
step. if_lit. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms1 [r' ->]. simp_regs.
step.
rewrite !(unsigned_lit sz), !(unsigned_lit cnt) by lia. replace (sz * cnt) with n by lia.
step. stp. step. stp. stp.
step. step. step. stp.
step.
lazymatch type of MUa with munch _ _ ?mm =>
destruct (sz_frame RE X a LB FS G m1 mm _ GC MUa WMa ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; right; idtac; lia)) as (FT & FP & FD);
pose proof (FT RT1) as RT2; pose proof (FP RP1) as RP2; pose proof (FD RD1) as RD2;
assert (RS2 : RStats RE X mm) by (eapply RStats_munch; [exact RS1| exact MUa| exact WMa| constructor; [st_avoid_solve| constructor]]) end.
clear FT FP FD RT1 RP1 RD1 RS1 MUa WMa.
apply evt_done. change (wz 967832) with (wz A_INSTANCE).
eapply aimplT_then.
{ eapply (allocate_prim_spec L RE X _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s a G LB FS n 0 lo (bp + -2136) tsz dn q30 GC RT2 RS2 RP2 RD2);
[assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| lia| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post in PO. rewrite !(unsigned_lit (bp + -2192)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & G1 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 260676)) with (wz 260676) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END in REST. rewrite ?KS, ?KO in REST.
change (536870912 / 8) with 67108864 in REST. change (3758096384 / 8) with 469762048 in REST.
fold c in REST.
clear OBJh TRQ RT2 RP2 RD2 RS2.

assert (FRALL : forall mx, rw_cells asegs mx (bp + -2144) [CB 8 junk8b] -> rw_cells asegs mx (bp + -2136) (unw_obj (bp + -2136) tsz q rest bp) ->
rw_cells asegs mx (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mx (bp + -2144) ([CB 8 junk8b] ++ unw_obj (bp + -2136) tsz q rest bp ++ [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ intros mx O0 O1 O2. apply (proj2 (rw_cells_app asegs mx _ [CB 8 junk8b] _)). split; [exact O0|]. cbn [cells_size csize Nat.add].
replace (bp + -2144 + Z.of_nat 8) with (bp + -2136) by lia.
apply (proj2 (rw_cells_app asegs mx _ _ _)). split; [exact O1|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (first [ clear - mx LQ ks junk8 rest tsz n sz cnt s6 s5 s4 s3 s2 s1 s0 bp ra BAND w0 w1 w2 w3 q' w5 w4; lia | lia ]).
unfold unw_obj. cbn [cells_size csize Nat.add map app length]. replace (bp + -2136 + Z.of_nat 2064) with (bp + -72) by lia. exact O2. }
destruct r as [p|].
-
destruct REST as (aa & i & -> & -> & QF & GS & TI & I0 & -> & MUk & RPF & CM & HJU).
pose proof GS as (_ & _ & _ & GCT). pose proof (GCT LB FS GC) as GC1.
pose proof (tag_slot _ _ _ _ _ _ GC1 c i TCached TI) as (_ & _ & _ & SL1 & SL2 & SL3 & SL4 & _). rewrite KO in SL4.
pose proof (class_size_facts c ltac:(lia)) as [CS1 CS2].
pose proof (class_of_facts n ltac:(lia) HP) as (_ & Csz & _). cbv zeta in Csz. fold c in Csz.
assert (N1 : n <= class_size c - rz_size n) by (unfold needed in Csz; pose proof (round_up_8 (Z.max n 8) ltac:(lia)); lia).
assert (SHS : SH (reg_beg (ae_L RE) c) <= SH (slot_beg RE c i) /\ SH (slot_beg RE c i) + class_size c / 8 <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048).
rewrite <- SH_plus8. replace (8 * (class_size c / 8)) with (class_size c) by (clear - CS2; Z.div_mod_to_equations; lia). apply SH_le. lia. }
hide CS2.
set (AB := slot_beg RE c i) in *.
apply (munch_weaken _ (calloc_W RE X bp c (c_alloc_user (cls a c)) ++ slot_W RE c i)) in MU.
2:{ unfold calloc_W, CALLOC_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. intros z Hz. cbn [outside] in Hz |- *. clear - Hz. (first [ clear - Hz z i c a bp X RE; tauto | tauto ]). }
unfold calloc_W, CALLOC_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU. fold AB in MU.
cbn [app] in MUk. lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
step. ifz.
rtc RT3 24%nat K24. change (al_space_beg (ae_L RE)) with (prim_lo RE) in K24. rtc RT3 19%nat K19. rtc RT3 23%nat K23.
unfold A_INSTANCE. step.
step. unfold_cond; cond_unsig; if_false.
stp. step.
step. unfold_cond; cond_unsig; if_false.
step. step. step.
step. stp. step.
destruct (hjunk_split _ _ (AB + rz_size n + n) _ HJU ltac:(lia)) as [HJ1 HJ2].
replace (AB + rz_size n + n) with (AB + rz_size n + Z.of_nat (Z.to_nat n)) in HJ1 by lia. destruct (hjunk_cells _ _ _ HJ1) as [ujunk UC].
step.
eapply evt_cut; [eapply memset_spec; [rewrite !unsigned_lit by lia; exact UC| assumption]|].
intros ms'' PO. unfold memset_post in PO. rewrite !unsigned_lit in PO by lia.
destruct PO as (v0 & v1 & v2 & pw1 & pw2 & pw3 & pw4 & pw5 & pw6 & pw7 & v3 & v4 & v5 & v6 & m4 & -> & MU4 & WM4 & MI4 & UC4).
replace (ret_pc (wz 260728)) with (wz 260728) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
change (0 mod 256) with 0 in UC4.
destruct (user_frame RE X aa LB FS G1 c i m3 m4 _ GC1 TI I0 MU4 WM4 ltac:(intros lo' hi' x Hin Hx; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; fold AB; lia)) as (FT & FS' & FD & FP).
pose proof (FT RT3) as RT4. pose proof (FS' RS3) as RS4. pose proof (FD RD3) as RD4. pose proof (FP RPF) as RPF4. clear FT FS' FD FP.
assert (CM4 : chunk_mem m4 AB (AB + class_size c) (AB + rz_size n) n).
{ eapply chunk_mem_agree_user; [exact CM| exact WM4|]. eapply agree_on_of_munch; [exact MU4| exact WM4|]. intros z Hz _. cbn [outside]. lia. }
phase_done MU m3 m4 MU4 WM4. clear RT3 RS3 RD3 RPF CM HJ1.
step. step.
step. step. step. step. step. step.
release_frame FR0 ST3 (bp + -2144).
step.
replace (ret_pc (wz 407572)) with (wz 407572) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 8 step. step.
pose proof (FRALL _ J8 OBJ FR) as FRX. clear OBJ OBJ3 FR J8.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (first [ clear - v6 v5 v4 v3 pw7 pw6 pw5 pw4 pw3 pw2 pw1 v2 v1 v0 aa AB i LQ ks m4 c n sz cnt lo G a s m fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 gp bp ra X RE BAND q'; lia | lia ]). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST3 bp.
step.
apply evt_done. unfold calloc_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST3|].
split; [exact RT4|]. split; [exact RS4|]. split; [exact RD4|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. exists aa, i. split; [reflexivity|]. split; [reflexivity|]. split; [exact QF|]. split; [exact GS|]. split; [exact TI|]. split; [exact I0|].
split; [reflexivity|]. split; [| split; [exact RPF4| split; [exact CM4| exact UC4]]].
unfold calloc_W, CALLOC_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold c. fold AB. exact MU.
-
destruct REST as (-> & MUk & QF & GS & RPk).
lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
step. if_lit.
pose proof (munch_refl [(bp - 2208, bp - 2192); (A_ERRNO, A_ERRNO + 4)] m3) as MUe. pose proof (wmono_refl asegs m3) as WMe. unfold A_ERRNO in MUe.
step. call_ch (set_errno_spec RE X) ltac:(fun PO => unfold A_ERRNO in PO; rewrite !(unsigned_lit (bp + -2192)) in PO by lia);
[exact RS3| assumption| rewrite unsigned_lit by lia; exact ST3| exact CEIL'| rewrite unsigned_lit by lia; lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST4 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS4 end.
lazymatch type of MUe with munch _ _ ?mm =>
destruct (sz_frame RE X a' LB FS G1 m3 mm _ (proj2 (proj2 (proj2 GS)) LB FS GC) MUe WMe
ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia])) as (FT & FP & FD) end.
pose proof (FT RT3) as RT4. pose proof (FP RPk) as RP4. pose proof (FD RD3) as RD4. clear FT FP FD MUe WMe RT3 RPk RD3 RS3.
stp.
step. step. step. step. step. step.
release_frame FR0 ST4 (bp + -2144).
step.
replace (ret_pc (wz 407572)) with (wz 407572) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 8 step. step.
pose proof (FRALL _ J8 OBJ FR) as FRX. clear OBJ OBJ3 FR J8.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (first [ clear - x13 x12 x11 x10 x9 x8 x7 x6 x5 x4 x3 x1 x0 x a' LQ ks x14 n sz cnt lo G a s m fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 gp bp ra X RE BAND q'; lia | lia ]). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST4 bp.
step.
apply evt_done. unfold calloc_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST4|].
split; [exact RT4|]. split; [exact RS4|]. split; [exact RD4|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. split; [reflexivity|]. split; [| split; [exact QF| split; [exact GS| exact RP4]]].
unfold calloc_W, CALLOC_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold c. exact MU.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV3O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV3O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mql. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnaW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnaW.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpF1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEEn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEEn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsDw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsDw.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcYs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcYs.Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcfN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcfN.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqf.

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

Lemma calloc_icpt_spec : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PStateA) (a : AState) (G : ghost) (LB : list ablock) (FS : list fframe) (lo cnt sz dn : Z),
gcons a LB FS G RE X ->
RTconst RE X m -> RStats RE X m -> RPrim a G RE X m -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - CALLOC_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> from_primary (cnt * sz) = true ->
aimplT atn (asan_malloc (ae_L RE) a (cnt * sz)) s
(calloc_post RE X ra bp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G (cnt * sz) lo m)
(MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz cnt) (wz sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x636a4) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros GC RT RS RP RD MI ST CEIL LO BPR UNW DNH DCAP Hcnt Hsz HP.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof CEIL as CEIL'. idtac. unfold CALLOC_STACK, ALLOC_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (QKBN.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
unfold iv_disjoint in TD. cbn [fst snd] in TD. change (2^37) with 137438953472 in TD.
pose proof (rlay_pd RE X RL) as PD. pd_pair PD 0 1 D02. pd_pair PD 0 2 D03. clear PD.
set (n := cnt * sz) in *. assert (Hn : 0 <= n < 2^64) by (subst n; (first [ clear - CEIL' Hsz Hcnt BPR LO CEIL sz cnt lo bp BAND; nia | nia ])).
pose proof HP as HP'. apply from_primary_iff in HP'. unfold kMaxSize in HP'.
pose proof (class_of_facts n ltac:(lia) HP) as (Hc & _). cbv zeta in Hc. set (c := class_of n) in *.
pose proof (needed_facts n ltac:(lia)) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (SHB1 : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite FB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. (first [ clear - H9 q1 H5 H4 r0 q0 H0 H r q PH PCH PK PAL r1 Hc c TB n sz cnt X RE BAND; lia | lia ]). }
pose proof SH_band as SHBD0.
assert (SHB2 : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. (first [ clear - H9 q1 H5 H4 r0 q0 H0 H r q PH PCH PK PAL r1 Hc c TB n sz cnt X RE BAND; lia | lia ]). }
pose proof SH_band as SHBD1.
pose proof (gc_bounds _ _ _ _ _ _ GC c ltac:(rewrite K32; lia)) as (AU1 & AU2 & AU3). rewrite KO in AU2.
assert (SHB3 : SH (reg_beg (ae_L RE) c) <= SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048). apply SH_le. lia. }
clear PAL AU3.
pose proof (QKBN.rlay_obj_facts RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC. idtac. rewrite ?KHI_eq in NK.
pose proof (QKBN.rlay_obj_facts RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC. idtac. rewrite ?KHI_eq in BK.
pose proof (munch_refl (calloc_W RE X bp c (c_alloc_user (cls a c))) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold calloc_W, CALLOC_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
apply aimplT_from_evt.
eapply calloc_icpt_pre; [exact RT| exact RL| exact (RDepot_unw RE X _ RD)| exact MI| exact ST| exact CEIL'| unfold CALLOC_STACK, ALLOC_STACK; lia| exact BPR| exact UNW| lia| lia|].
intros m1 u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u13 tsz q rest junk8 junk8b MU1 WM1 MI1 ST1 J8 OBJ LQ SZR FR RT1 TU1.
unfold cicpt_W in MU1.
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU1| exact WM1|]. constructor; [first [st_avoid_solve| eapply st_avoid_T; [eassumption| lia| lia]]|]. constructor; [st_avoid_solve| constructor]. }
assert (RP1 : RPrim a G RE X m1).
{ eapply RPrim_frame; [exact RP| exact WM1|]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z Fz _. cbn [outside].
pose proof (fp_RPrim_lt_ceil G RE X z RL Fz). idtac.
split; [lia|]. split; [| exact I]. assert (z <> rl_T X + 3168) by (intros ->; exact (fpP_RDepot _ _ _ _ _ _ GC _ Fz ltac:(do 3 right; reflexivity))). lia. }
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame_unw; [exact RL| exact RD| exact WM1| | exact TU1]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z [Fz NZ] _. cbn [outside].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). idtac. (first [ clear - H NZ z LQ ks q BC NC PH PCH PK RZ1 NF TD TB TK CEIL' n LO sz cnt lo bp X RE BAND; lia | lia ]). }
phase_done MU m m1 MU1 WM1. clear RT RS RP RD MI. try clear ST.
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
rewrite (Z.div_small (sz * cnt) (2^64)) by (first [ clear - NZ LQ ks q BC BK NC NK PH PCH PK RZ2 RZ1 NF HP' Hn D03 D02 TD TB TK CEIL' n Hsz BPR LO CEIL sz cnt lo bp X RE BAND; nia | nia ]).
step. if_lit. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms1 [r' ->]. simp_regs.
step.
rewrite !(unsigned_lit sz), !(unsigned_lit cnt) by lia. replace (sz * cnt) with n by lia.
step. stp. step. stp. stp.
step. step. step. stp.
step.
lazymatch type of MUa with munch _ _ ?mm =>
destruct (sz_frame RE X a LB FS G m1 mm _ GC MUa WMa ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; right; idtac; lia)) as (FT & FP & FD);
pose proof (FT RT1) as RT2; pose proof (FP RP1) as RP2; pose proof (FD RD1) as RD2;
assert (RS2 : RStats RE X mm) by (eapply RStats_munch; [exact RS1| exact MUa| exact WMa| constructor; [st_avoid_solve| constructor]]) end.
clear FT FP FD RT1 RP1 RD1 RS1 MUa WMa.
apply evt_done. change (wz 977752) with (wz A_INSTANCE).
eapply aimplT_then.
{ eapply (allocate_prim_spec L RE X _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s a G LB FS n 0 lo (bp + -2136) tsz dn q30 GC RT2 RS2 RP2 RD2);
[assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| lia| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post in PO. rewrite !(unsigned_lit (bp + -2192)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & G1 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 261232)) with (wz 261232) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END in REST. rewrite ?KS, ?KO in REST.
change (536870912 / 8) with 67108864 in REST. change (3758096384 / 8) with 469762048 in REST.
fold c in REST.
clear OBJh TRQ RT2 RP2 RD2 RS2.

assert (FRALL : forall mx, rw_cells asegs mx (bp + -2144) [CB 8 junk8b] -> rw_cells asegs mx (bp + -2136) (unw_obj (bp + -2136) tsz q rest bp) ->
rw_cells asegs mx (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mx (bp + -2144) ([CB 8 junk8b] ++ unw_obj (bp + -2136) tsz q rest bp ++ [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ intros mx O0 O1 O2. apply (proj2 (rw_cells_app asegs mx _ [CB 8 junk8b] _)). split; [exact O0|]. cbn [cells_size csize Nat.add].
replace (bp + -2144 + Z.of_nat 8) with (bp + -2136) by lia.
apply (proj2 (rw_cells_app asegs mx _ _ _)). split; [exact O1|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (first [ clear - mx LQ ks junk8 rest tsz n sz cnt s6 s5 s4 s3 s2 s1 s0 bp ra BAND w0 w1 w2 w3 q' w5 w4; lia | lia ]).
unfold unw_obj. cbn [cells_size csize Nat.add map app length]. replace (bp + -2136 + Z.of_nat 2064) with (bp + -72) by lia. exact O2. }
destruct r as [p|].
-
destruct REST as (aa & i & -> & -> & QF & GS & TI & I0 & -> & MUk & RPF & CM & HJU).
pose proof GS as (_ & _ & _ & GCT). pose proof (GCT LB FS GC) as GC1.
pose proof (tag_slot _ _ _ _ _ _ GC1 c i TCached TI) as (_ & _ & _ & SL1 & SL2 & SL3 & SL4 & _). rewrite KO in SL4.
pose proof (class_size_facts c ltac:(lia)) as [CS1 CS2].
pose proof (class_of_facts n ltac:(lia) HP) as (_ & Csz & _). cbv zeta in Csz. fold c in Csz.
assert (N1 : n <= class_size c - rz_size n) by (unfold needed in Csz; pose proof (round_up_8 (Z.max n 8) ltac:(lia)); lia).
assert (SHS : SH (reg_beg (ae_L RE) c) <= SH (slot_beg RE c i) /\ SH (slot_beg RE c i) + class_size c / 8 <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048).
rewrite <- SH_plus8. replace (8 * (class_size c / 8)) with (class_size c) by (clear - CS2; Z.div_mod_to_equations; lia). apply SH_le. lia. }
hide CS2.
set (AB := slot_beg RE c i) in *.
apply (munch_weaken _ (calloc_W RE X bp c (c_alloc_user (cls a c)) ++ slot_W RE c i)) in MU.
2:{ unfold calloc_W, CALLOC_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. intros z Hz. cbn [outside] in Hz |- *. clear - Hz. (first [ clear - Hz z i c a bp X RE; tauto | tauto ]). }
unfold calloc_W, CALLOC_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU. fold AB in MU.
cbn [app] in MUk. lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
step. ifz.
rtc RT3 24%nat K24. change (al_space_beg (ae_L RE)) with (prim_lo RE) in K24. rtc RT3 19%nat K19. rtc RT3 23%nat K23.
unfold A_INSTANCE. step.
step. unfold_cond; cond_unsig; if_false.
stp. step.
step. unfold_cond; cond_unsig; if_false.
step. step. step.
step. stp. step.
destruct (hjunk_split _ _ (AB + rz_size n + n) _ HJU ltac:(lia)) as [HJ1 HJ2].
replace (AB + rz_size n + n) with (AB + rz_size n + Z.of_nat (Z.to_nat n)) in HJ1 by lia. destruct (hjunk_cells _ _ _ HJ1) as [ujunk UC].
step.
eapply evt_cut; [eapply memset_spec; [rewrite !unsigned_lit by lia; exact UC| assumption]|].
intros ms'' PO. unfold memset_post in PO. rewrite !unsigned_lit in PO by lia.
destruct PO as (v0 & v1 & v2 & pw1 & pw2 & pw3 & pw4 & pw5 & pw6 & pw7 & v3 & v4 & v5 & v6 & m4 & -> & MU4 & WM4 & MI4 & UC4).
replace (ret_pc (wz 261284)) with (wz 261284) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
change (0 mod 256) with 0 in UC4.
destruct (user_frame RE X aa LB FS G1 c i m3 m4 _ GC1 TI I0 MU4 WM4 ltac:(intros lo' hi' x Hin Hx; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; fold AB; lia)) as (FT & FS' & FD & FP).
pose proof (FT RT3) as RT4. pose proof (FS' RS3) as RS4. pose proof (FD RD3) as RD4. pose proof (FP RPF) as RPF4. clear FT FS' FD FP.
assert (CM4 : chunk_mem m4 AB (AB + class_size c) (AB + rz_size n) n).
{ eapply chunk_mem_agree_user; [exact CM| exact WM4|]. eapply agree_on_of_munch; [exact MU4| exact WM4|]. intros z Hz _. cbn [outside]. lia. }
phase_done MU m3 m4 MU4 WM4. clear RT3 RS3 RD3 RPF CM HJ1.
step. step.
step. step. step. step. step. step.
release_frame FR0 ST3 (bp + -2144).
step.
replace (ret_pc (wz 408556)) with (wz 408556) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 8 step. step.
pose proof (FRALL _ J8 OBJ FR) as FRX. clear OBJ OBJ3 FR J8.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (first [ clear - v6 v5 v4 v3 pw7 pw6 pw5 pw4 pw3 pw2 pw1 v2 v1 v0 aa AB i LQ ks m4 c n sz cnt lo G a s m fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 gp bp ra X RE BAND q'; lia | lia ]). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST3 bp.
step.
apply evt_done. unfold calloc_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST3|].
split; [exact RT4|]. split; [exact RS4|]. split; [exact RD4|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. exists aa, i. split; [reflexivity|]. split; [reflexivity|]. split; [exact QF|]. split; [exact GS|]. split; [exact TI|]. split; [exact I0|].
split; [reflexivity|]. split; [| split; [exact RPF4| split; [exact CM4| exact UC4]]].
unfold calloc_W, CALLOC_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold c. fold AB. exact MU.
-
destruct REST as (-> & MUk & QF & GS & RPk).
lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
step. if_lit.
pose proof (munch_refl [(bp - 2208, bp - 2192); (A_ERRNO, A_ERRNO + 4)] m3) as MUe. pose proof (wmono_refl asegs m3) as WMe. unfold A_ERRNO in MUe.
step. call_ch (set_errno_spec RE X) ltac:(fun PO => unfold A_ERRNO in PO; rewrite !(unsigned_lit (bp + -2192)) in PO by lia);
[exact RS3| assumption| rewrite unsigned_lit by lia; exact ST3| exact CEIL'| rewrite unsigned_lit by lia; lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST4 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS4 end.
lazymatch type of MUe with munch _ _ ?mm =>
destruct (sz_frame RE X a' LB FS G1 m3 mm _ (proj2 (proj2 (proj2 GS)) LB FS GC) MUe WMe
ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia])) as (FT & FP & FD) end.
pose proof (FT RT3) as RT4. pose proof (FP RPk) as RP4. pose proof (FD RD3) as RD4. clear FT FP FD MUe WMe RT3 RPk RD3 RS3.
stp.
step. step. step. step. step. step.
release_frame FR0 ST4 (bp + -2144).
step.
replace (ret_pc (wz 408556)) with (wz 408556) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 8 step. step.
pose proof (FRALL _ J8 OBJ FR) as FRX. clear OBJ OBJ3 FR J8.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (first [ clear - x13 x12 x11 x10 x9 x8 x7 x6 x5 x4 x3 x1 x0 x a' LQ ks x14 n sz cnt lo G a s m fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 gp bp ra X RE BAND q'; lia | lia ]). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST4 bp.
step.
apply evt_done. unfold calloc_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST4|].
split; [exact RT4|]. split; [exact RS4|]. split; [exact RD4|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. split; [reflexivity|]. split; [| split; [exact QF| split; [exact GS| exact RP4]]].
unfold calloc_W, CALLOC_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold c. exact MU.
Qed.
End S.
