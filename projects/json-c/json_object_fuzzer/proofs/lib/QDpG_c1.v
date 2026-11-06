(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Q6sh QQwg QKTr QJBH QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QNQk QSsj Qu1d QpY2 QTVW QOJv QmP7 QYyZ Q9Ho QkfD QpME QcfN Qu3b QmvA QFd5 QteI QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QNQk.Mq2 QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QOJv.Mq4 QOJv.Mq3 QmP7.Mq0 QYyZ.Mq0 Q9Ho.Mq1 QkfD QpME.Mq0.
Import QpY2.Mq2 QcfN.Mq1.
Import Qu3b.Mq2 QYyZ.Mq5.
Import QmvA.Mq1.
Import QpME.Mq5 QOJv.Mq2 QFd5.Mq3 QteI.Mq5.
Import QlES.
Import QpME.Mq4. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.

Local Ltac QsGW.if_lit ::= if_lit_lit. Local Ltac mkr__if_lit_0 := if_lit_lit.

Local Ltac QoSL.addr_eq_tac ::= addr_eq_tac_w. Local Ltac mkr__addr_eq_tac_1 := addr_eq_tac_w.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Ltac Q0z1.sf_hide_poison ::= sf_hide_poison_divlit. Local Ltac mkr__sf_hide_poison_3 := sf_hide_poison_divlit.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Lemma K44 : forall m, RTconst RE X m -> ro_cells asegs m 0x0e5da0 [C8 (wz 0x0e7de8)] /\ ro_cells asegs m 0x0e7de8 [C8 (wz 0x1a35f)].
Proof. intros m RT. rtc RT 44%nat A. rtc RT 45%nat B. split; [exact A| exact B]. Qed.

Hypothesis map_or_die_spec : map_or_die_stmt L RE X.

Lemma largealloc_ensure : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (s : PStateA) (a : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (n lo : Z)
(rax t0 t1 t2 a1r a2 a5 a6 a7 s6x s7x s8x s9x t3 t4 t5 t6 : word) (m1 : mem)
(mb E : Z) (junk8 pj shu : list byte) (w0 w1 w2 w3 w4 g0 g1 g2 g3 g4 : word) (bsl : list word),
let msz := sec_map_size n in let sz := sec_size n in let reg := as_reg a in let nch := Z.of_nat (length reg) in let parr := ptrarr_lo RE in
let nres := as_nres a in
gcons a LB FS G RE X -> avoid_covers RE X -> RTconst RE X m -> RStats RE X m -> RSec a LB RE X m ->
band_lo <= lo -> lo <= bv_unsigned sp - LARGE_STACK -> 0 <= n <= 2^26 -> from_primary n = false ->
mb mod kPage = 0 -> appr mb msz -> mb + msz <= band_lo -> zavoids mb msz (avoid_of (ae_L RE) a) = true ->
munch [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8); (rl_T X + 2872, rl_T X + 2888);
(967936, 968560); (parr, parr + 0x800000)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -96) -> RTconst RE X m1 ->
rw_cells asegs m1 (bv_unsigned sp + -96) [CB 8 junk8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m1 967944 [C8 (wz nres); C8 (wz nch)] ->
rw_cells asegs m1 967960 [CB 8 (le8 w0); C8 w1; C8 w2; C8 w3; C8 w4] -> u64arr asegs m1 968000 bsl -> length bsl = 64%nat ->
rw_cells asegs m1 968512 [C4 (wz 1); C4 (wz 0)] ->
rw_cells asegs m1 968520 [C8 g0; C8 g1; C8 g2; C8 g3; C8 g4] ->
u64arr asegs m1 parr (map (fun e => wz (se_beg e)) reg) ->
rw_cells asegs m1 (parr + 8 * nch) [CB (Z.to_nat (8 * (nres - nch))) pj] ->
nch = nres -> nch < 2^20 ->
rw_cells asegs m1 mb [C8 (wz mb); C8 (wz msz); C8 (wz sz); C8 (wz 0)] ->
rw_cells asegs m1 (mb + 32) [CB 4064 (repeat (b8 0) 4064)] ->
rw_cells asegs m1 (mb + 4096) [CB (Z.to_nat (msz - 4096)) (repeat (b8 0) (Z.to_nat (msz - 4096)))] ->
rw_cells asegs m1 (SH mb) [CB (Z.to_nat 512) (repeat (b8 250) (Z.to_nat 512))] ->
rw_cells asegs m1 (SH (mb + 4096)) [CB (Z.to_nat (sz / 8)) shu] ->
rw_cells asegs m1 (SH (mb + 4096 + sz)) [CB (Z.to_nat ((msz - 4096 - sz) / 8)) (repeat (b8 250) (Z.to_nat ((msz - 4096 - sz) / 8)))] ->
0 <= E < 2^64 -> 16 <= Z.lxor E 63 <= 26 ->
aimplT atn
(tvis (EvMapFixed (al_ptrarr (ae_L RE) + 8 * as_nres a) kPtrArrBlockBytes)
(fun a2 => tbind (match a2 with AErr => tunr UCheck | AOk _ => tret (set_nres (as_nres a + kPtrArrBlock) a) end)
(fun s12 => tret (Some mb, add_spent (sec_cost msz) (set_reg (as_reg s12 ++ [mkSec mb msz n]) s12)))))
s (large_post RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB lo n m)
(MS (mkR rax (wz (bv_unsigned sp + -96)) gp (wz A_TP) t0 t1 t2 (wz 968520) (wz 967896)
(wz (mb + 4096)) a1r a2 (wz nch) (wz nres) a5 a6 a7 (wz msz) (wz E) (wz mb) (wz mb) s6x s7x s8x s9x s10 s11 t3 t4 t5 t6)
F (wz 0x43fb0) fc None m1 (seg_rom asegs)).
Proof.
intros until bsl; intros msz sz reg nch parr nres GC AVC RT RS RSE CEIL LO Hn HP MAL MK MC AVm MU WM MI1 ST1 RT1 FR I1 J1 BSL LBSL I3 GS P1 P2 EQN NCH
ZBh ZBp ZBb SFh SBu SFs HE HIDX.
pose proof CEIL as CEIL'. idtac. unfold LARGE_STACK in LO.
pose proof MC as MC'. idtac. pose proof MK as MK'. apply appr_to_lia in MK; [| unfold msz; pose proof (sec_map_size_ge n ltac:(lia) HP) as [SM _]; lia| lia].
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _). rewrite KP in MAL.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & _ & _ & QAL & QK & QH & _). unfold ptrarr_hi in QH. change (al_ptrarr (ae_L RE)) with parr in QH, QAL |- *. fold parr in QK.
pose proof QK as QK'. rewrite ?KHI_eq in QK. pose proof QH as QH'. idtac.
pose proof (sec_size_facts n Hn HP) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). fold sz msz in Z1, Z2, Z3, Z4, Z5, Z6.
pose proof (avoid_facts RE X a mb msz AVC ltac:(lia) ltac:(lia) AVm) as (_ & AVO & AVP & AVQ & AVR). fold parr in AVQ.
hide MK'. hide QK'. apply appr_to_lia in QK; [| lia| lia].
assert (MBH : 0x645000 <= mb) by (clear - MK Z1 Z6; lia).
assert (SHB : 0x80000000 <= SH mb /\ SH (mb + msz) = SH mb + msz / 8 /\ SH mb + msz / 8 <= 0x10007fff8000) by (rewrite !SH_eq; clear - MBH MAL Z5 MC; Z.div_mod_to_equations; lia).
destruct SHB as (SHB1 & SHB2 & SHB3).
assert (SHE1 : SH (mb + 4096) = SH mb + 512) by (change (mb + 4096) with (mb + 8 * 512); apply SH_plus8).
assert (SHE2 : SH (mb + 4096 + sz) = SH mb + 512 + sz / 8) by (rewrite !SH_eq; clear - Z3; Z.div_mod_to_equations; lia).
pose proof RSE as (_ & _ & _ & _ & _ & _ & _ & NLE & NMX & NMOD). fold reg nch nres in NLE, NMX, NMOD. unfold kMaxNumChunks in NMX. unfold kPtrArrBlock in NMOD.
assert (NR : nres + 16384 <= 1048576) by (clear - EQN NCH NMOD; Z.div_mod_to_equations; lia).
rtc RT1 43%nat K43. change (A_INSTANCE + 80) with 967912 in K43. fold parr in K43, QAL.
assert (AAL : (parr + 8 * nres) mod 4096 = 0) by (clear - QAL NMOD; Z.div_mod_to_equations; lia).
apply aimplT_from_evt.
step.
step. step. step.
rewrite (unsigned_lit nch), Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
replace (nch * 8 + parr) with (parr + 8 * nres) by lia.
stp. step. step. stp.
step.
clear K43.
apply evt_done. eapply aimplT_map_fixed.
{ eapply map_or_die_spec; rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by lia;
[exact RT1| exact RL| exact MI1| exact ST1| exact CEIL'| unfold MAPORDIE_STACK; lia| exact AAL| reflexivity| lia| lia| lia
| apply rt_avoid_ptrarr; [exact RL| subst parr; lia| subst parr; unfold ptrarr_hi, ptrarr_lo; lia]]. }
intros ans ms' PO. cbv beta iota. destruct ans as [|xA].
-
apply aimplT_unr.
-
destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MUp & WMp & MI2 & ST2 & RT2 & -> & -> & ZP).
rewrite tbind_tret. cbn [as_reg as_nres set_nres].
rewrite !(unsigned_lit (bv_unsigned sp + -96)) in MUp, ST2 by lia. unfold MAPORDIE_STACK in MUp.
apply (munch_chain' _ _ m2 _ m MUp) in MU; [| sub_fp_solve].
pose proof (wmono_trans asegs _ _ _ WM WMp) as WM2.
clear P2 ST1 RT1 MI1.
assert (LM : Z.of_nat (length (map (fun e => wz (se_beg e)) reg)) = nch) by (rewrite length_map; lia).
hide Z3; hide Z4; hide Z5; hide MAL; hide QAL; hide NMOD; hide HIDX; hide HE; hide AAL; hide Hn; hide AVP.
transport_after_call asegs m1 m2 MUp WMp.
unhide Z3; unhide Z4; unhide Z5; unhide MAL; unhide QAL; unhide NMOD; unhide HIDX; unhide HE; unhide AAL; unhide Hn; unhide AVP.
clear MUp WMp WM. rename WM2 into WM.
apply aimplT_from_evt.
replace (ret_pc (wz 278484)) with (wz 278484) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step.
step. step.
stp. step.
step.
step.
apply evt_done. apply aimplT_ret.
eapply (largealloc_finish RE X) with (nres1 := nres + 16384) (a := a);
[exact GC| exact AVC| exact RT| exact RS| exact RSE| exact CEIL'| unfold LARGE_STACK; lia| exact Hn| exact HP| rewrite KP; exact MAL| exact MK'| exact MC'| exact AVm
| exact MU| exact WM| eassumption| eassumption| | exact FR| exact I1| exact J1| exact BSL| exact LBSL| exact I3| exact GS| exact P1
| change (Z.of_nat (length (as_reg a))) with nch; change (ptrarr_lo RE) with parr; rewrite EQN; replace (8 * (nres + 16384 - nres)) with 131072 by (clear; lia); exact ZP
| change (Z.of_nat (length (as_reg a))) with nch; clear - EQN; lia| exact NR| unfold kPtrArrBlock; clear - NMOD; Z.div_mod_to_equations; lia| right; unfold kPtrArrBlock; reflexivity
| exact ZBh| exact ZBp| exact ZBb| exact SFh| exact SBu| exact SFs| exact HE| exact HIDX
| reflexivity| reflexivity| reflexivity| reflexivity| intros c; reflexivity| reflexivity| reflexivity| reflexivity].

pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
assert (FWrt : Forall (rt_avoid RE X) [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8);
(rl_T X + 2872, rl_T X + 2888); (967936, 968560); (parr, parr + 8388608)]).
{ clear - RL MK' AVO SHB1 SHB3 CEIL' CEIL LO SPR TK TB QK QH.
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_free; [exact RL| exact (proj2 MK')| intros o Ho; destruct (AVO o Ho); lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; lia| rewrite ?KHI_eq; lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [exact (rt_avoid_inst RE X RL)|].
constructor; [apply rt_avoid_ptrarr; [exact RL| subst parr; lia| subst parr; unfold ptrarr_hi, ptrarr_lo; lia]| constructor]. }
eapply RTconst_munch; [exact RT| exact MU| exact WM| exact FWrt].
Qed.

Lemma large_alloc_spec : large_alloc_stmt RE X L.
Proof.
unfold large_alloc_stmt.
intros until lo; intros GC AVC RT RS RSE MI ST CEIL LO Hn HP.
pose proof CEIL as CEIL'. idtac. unfold LARGE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC, TD. rewrite ?KHI_eq in PK. idtac.
pose proof (sec_size_facts n Hn HP) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
set (sz := sec_size n) in *. set (msz := sec_map_size n) in *.
unfold large_alloc. fold msz.
rtc RT 25%nat K25. rtc RT 43%nat K43. destruct (K44 m RT) as [K44a K45a].
unfold large_alloc_entry, SEC, A_INSTANCE in *.
pose proof (munch_refl [(bv_unsigned sp - 800, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
apply aimplT_from_evt.
carve_frame 96%nat ST.
do 12 step.
step.
step. step. lits.
step. if_lit.
step.
step.
step. step. lits. step. if_lit.
step.
stp. stp. stp. stp.
rewrite (unsigned_lit (sz + 4095)) by lia. rewrite land_negpage by lia.
stp. stp.
step.
lazymatch goal with |- context [wz (sz + 4095 - ?r + 4096)] => replace (sz + 4095 - r + 4096) with msz by lia end.
stp. step.
step. ifz.
step.
step. step. step.
step. step.
clear K44a K45a.
apply evt_done. eapply aimplT_map_anon.
{ eapply (mmap_or_die_spec L RE X); rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by lia;
[ eapply RTconst_stack; [exact RT| exact RL| exact MU0| exact WM0| apply Forall_cons; [cbn [fst]; lia| apply Forall_nil]]
| exact RL| assumption| exact ST| exact CEIL'| unfold MMAPANON_STACK; lia| exact Z5| lia| lia
| intros b Hb AVb; exact (proj1 (avoid_facts RE X a b msz AVC ltac:(lia) Hb AVb))
| intros b o Hb AVb Ho; exact (proj1 (proj2 (avoid_facts RE X a b msz AVC ltac:(lia) Hb AVb)) o Ho) ]. }
intros ans ms' PO. destruct ans as [|mb].
-
destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & WM2 & MI2 & ST2 & RT2 & -> & MU2).
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2, MU2 by lia.
apply aimplT_ret.
replace (ret_pc (wz 277556)) with (wz 277556) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold MMAPANON_STACK in MU2.
assert (MU : munch [(bv_unsigned sp - 800, bv_unsigned sp)] m m2) by (eapply munch_trans; [exact MU0| eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia]).
pose proof (wmono_trans asegs _ _ _ WM0 WM2) as WM.
transport_after_call asegs m0 m2 MU2 WM2. clear MU0 WM0 MU2 WM2 MI.
step. if_lit.
do 11 step. step. step.
release_frame FR ST2 (bv_unsigned sp).
apply evt_done. unfold large_post. do 16 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [exact MI2|]. split; [exact ST2|]. split; [exact WM|]. split; [exact RT2|]. split.
{ eapply RStats_munch; [exact RS| exact MU| exact WM| apply Forall_cons; [st_avoid_solve| apply Forall_nil]]. }
split; [reflexivity|]. split; [reflexivity|]. split.
{ eapply munch_weaken; [| exact MU]. unfold W_large, LARGE_STACK, sub_fp. cbn [outside]. intros; lia. }
eapply RSec_frame; [exact RSE| exact WM|]. eapply agree_on_of_munch; [exact MU| exact WM|]. intros z Fx _. cbn [outside].
pose proof (fp_RSec_lt_ceil RE X _ _ _ _ z GC Fx). lia.
-
destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & WM2 & MI2 & ST2 & RT2 & -> & MAL & MK & MC & AVm & MU2 & ZB & (shj & SB)).
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2, MU2 by lia.
pose proof MC as MC'. idtac. pose proof MK as MK'. apply appr_to_lia in MK; [| unfold msz; pose proof (sec_map_size_ge n ltac:(lia) HP) as [SM _]; lia| lia].
pose proof (avoid_facts RE X a mb msz AVC ltac:(lia) ltac:(lia) AVm) as (_ & AVO & AVP & AVQ & AVR).
unfold MMAPANON_STACK in MU2.

cbv beta iota zeta.
destruct (Z.leb_spec0 kMaxNumChunks (Z.of_nat (length (as_reg a)))) as [BIG|NCH]; [apply aimplT_unr|].
unfold kMaxNumChunks in NCH.
apply aimplT_from_evt.
replace (ret_pc (wz 277556)) with (wz 277556) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (MU : munch [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH (mb + msz))] m m2).
{ eapply munch_trans; [eapply munch_weaken; [| exact MU0]; unfold sub_fp; cbn [outside]; intros; lia|].
eapply munch_weaken; [| exact MU2]. rewrite <- (SH_add mb (msz / 8)) by lia. replace (mb + 8 * (msz / 8)) with (mb + msz) by lia.
unfold sub_fp; cbn [outside]; intros; lia. }
pose proof (wmono_trans asegs _ _ _ WM0 WM2) as WM.
assert (SHB : 0x80000000 <= SH mb /\ SH (mb + msz) = SH mb + msz / 8 /\ SH mb + msz / 8 <= 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
destruct SHB as (SHB1 & SHB2 & SHB3). rewrite SHB2 in MU.
clear MU0 WM0 K25 K43. transport_after_call asegs m0 m2 MU2 WM2. clear MU2 WM2 MI.
rtc RT2 25%nat K25.
step. ifz.
step.
step. step. step.
rewrite (unsigned_lit mb), (Z.land_comm 4095 mb) by lia. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096.
replace (mb mod 4096) with 0 by lia.
step. if_lit.
step. step.
step.
rewrite (unsigned_lit (4096 + mb)) by lia. rewrite land_7 by lia. replace ((4096 + mb) mod 8) with 0 by lia.
stp. stp. stp. stp.
step. step.
step. step. step.
replace (0 + (4096 + mb)) with (mb + 4096) by lia.
rewrite (unsigned_lit (mb + 4096 + sz)), (unsigned_lit (mb + 4096 + 7)) by lia. rewrite !land_mask8 by lia.
replace (mb + 4096 + sz - (mb + 4096 + sz) mod 8) with (mb + 4096 + sz) by lia.
replace (mb + 4096 + 7 - (mb + 4096 + 7) mod 8) with (mb + 4096) by (Z.div_mod_to_equations; lia).
replace (msz + mb) with (mb + msz) by lia.
step.
replace (mb + 4096 - mb) with 4096 by lia.
stp. step.
step.

assert (M8 : msz / 8 = 512 + (sz / 8 + (msz - 4096 - sz) / 8)) by lia.
lazymatch type of SB with rw_cells _ ?mc _ _ =>
replace (Z.to_nat (msz / 8)) with (512 + (Z.to_nat (sz / 8) + Z.to_nat ((msz - 4096 - sz) / 8)))%nat in SB by lia;
destruct (rw_cells_CB_split mc _ _ _ _ SB) as [SBh SBr]; clear SB;
destruct (rw_cells_CB_split mc _ _ _ _ SBr) as [SBu SBs]; clear SBr end.
change (Z.of_nat 512) with 512 in SBu, SBs. rewrite Z2Nat.id in SBs by lia.
assert (SHE1 : SH (mb + 4096) = SH mb + 512) by (change (mb + 4096) with (mb + 8 * 512); apply SH_plus8).
assert (SHE2 : SH (mb + 4096 + sz) = SH mb + 512 + sz / 8) by (rewrite !SH_eq; clear - Z3; Z.div_mod_to_equations; lia).
rewrite <- SHE1 in SBu. rewrite <- SHE2 in SBs.
rewrite (unsigned_lit (mb + 4096)), (unsigned_lit mb) by lia. replace (mb + 4096 - mb) with 4096 by lia.

eapply evt_cut.
{ eapply (poison_shadow_spec_lh RE X); rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by lia; [exact RT2| exact RL| exact MI2| exact ST2| exact CEIL'| lia
| lia| reflexivity| lia| rewrite ?KHI_eq; change (2^47) with 140737488355328; clear - MK MC Z1 Z6; lia| lia| left; lia| exact SBh]. }
cbv beta. intros ms' PO. clear SBh.
destruct PO as (t0_ & t1_ & t2_ & a0_ & a1_ & a2_ & a3_ & a4_ & a5_ & a6_ & a7_ & t3_ & t4_ & t5_ & t6_ & m3 & -> & MUp & WMp & MI3 & ST3 & RT3 & SFh).
change (4096 / 8) with 512 in MUp, SFh. rewrite !(unsigned_lit (bv_unsigned sp + -96)) in MUp, ST3 by lia.
apply (munch_chain' _ _ m3 _ m MUp) in MU; [| sub_fp_solve].
pose proof (wmono_trans asegs _ _ _ WM WMp) as WM3.
transport_after_call asegs m2 m3 MUp WMp. clear MUp WMp WM MI2 RT2. try clear ST2. rename WM3 into WM.
replace (ret_pc (wz 277644)) with (wz 277644) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step.
rewrite (unsigned_lit (mb + msz)), (unsigned_lit (mb + 4096 + sz)) by lia.
replace (mb + msz - (mb + 4096 + sz)) with (msz - 4096 - sz) by lia.
stp. step. step.

eapply evt_cut.
{ eapply (poison_shadow_spec_lh RE X); rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by lia; [exact RT3| exact RL| exact MI3| exact ST3| exact CEIL'| lia
| lia| lia| lia| rewrite ?KHI_eq; change (2^47) with 140737488355328; clear - MK MC Z1 Z6; lia| lia| left; lia| exact SBs]. }
cbv beta. intros ms' PO. clear SBs.
destruct PO as (t0c & t1c & t2c & a0c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m4 & -> & MUp & WMp & MI4 & ST4 & RT4 & SFs).
rewrite !(unsigned_lit (bv_unsigned sp + -96)) in MUp, ST4 by lia.
assert (SHE3 : SH (mb + 4096 + sz) + (msz - 4096 - sz) / 8 = SH mb + msz / 8) by (rewrite !SH_eq; clear - Z3 Z5; Z.div_mod_to_equations; lia).    rewrite SHE3 in MUp.
apply (munch_chain' _ _ m4 _ m MUp) in MU; [| sub_fp_solve].
pose proof (wmono_trans asegs _ _ _ WM WMp) as WM4.
clear t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_.
transport_after_call asegs m3 m4 MUp WMp. clear MUp WMp WM MI3 RT3. try clear ST3. rename WM4 into WM.
replace (ret_pc (wz 277660)) with (wz 277660) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

step.
call_sp_ch (get_thread_stats_spec RE X) ltac:(fun PO => idtac); try eassumption; try lia.
subst. rename POST into RT5.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RS5 : RStats RE X mc) by (eapply RStats_munch; [exact RS| exact MU| exact WM| repeat (apply Forall_cons || apply Forall_nil); st_avoid_solve]);
destruct (RStats_mmap_words _ _ _ RS5) as (w1 & w2 & STC);
apply (munch_weaken _ [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8); (rl_T X + 2872, rl_T X + 2888)]) in MU;
[| unfold sub_fp; cbn [outside]; intros xw Hxw; clear - Hxw; tauto] end.
pose proof (AVO _ (T_obj RE X)) as TMB. cbn [fst snd] in TMB.
step. step.
step.
rewrite (unsigned_lit (mb + 4096)) by lia. rewrite land_7 by lia. replace ((mb + 4096) mod 8) with 0 by lia.
step. step.
step. step.
step. if_lit.
step. step. step. step.
rewrite ?(unsigned_lit (mb + 4096)) by lia.
rewrite (Z.land_comm 4095 (mb + 4096)). change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096.
replace ((mb + 4096) mod 4096) with 0 by lia.
step. if_lit.
step. unfold_cond; cond_unsig; if_false.
step. unfold_cond; cond_unsig; if_false.
step.
rewrite (unsigned_lit (mb + 4096)) by lia. replace (mb + 4096 - 4096) with mb by lia.

lazymatch type of ZB with rw_cells _ ?mc _ _ =>
replace (Z.to_nat msz) with (32 + (4064 + Z.to_nat (msz - 4096)))%nat in ZB by lia;
destruct (rw_cells_CB_split mc _ _ _ _ ZB) as [ZBh ZBr]; clear ZB;
destruct (rw_cells_CB_split mc _ _ _ _ ZBr) as [ZBp ZBb]; clear ZBr end.
rewrite firstn_repeat' in ZBh by lia. rewrite skipn_repeat', firstn_repeat' in ZBp by lia. rewrite !skipn_repeat' in ZBb.
replace (32 + (4064 + Z.to_nat (msz - 4096)) - 32 - 4064)%nat with (Z.to_nat (msz - 4096)) in ZBb by lia.
change (Z.of_nat 32) with 32 in ZBp, ZBb. change (Z.of_nat 4064) with 4064 in ZBb. replace (mb + 32 + 4064) with (mb + 4096) in ZBb by lia.
recast ZBh [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
step. step. step.
step. unfold_cond; cond_unsig; if_false.

pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & _ & _ & _ & TQD). unfold iv_disjoint in TQD. cbn [fst snd] in TQD.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & _ & _ & _ & QK & QH & _). unfold ptrarr_hi in QH. rewrite ?KHI_eq in QK. idtac.
pose proof RSE as RSE0. destruct RSE as (I1 & I2 & I3 & I4 & P1 & P2 & HD & NLE & NMX & NMOD).
set (reg := as_reg a) in *. set (nch := Z.of_nat (length reg)) in *. set (nres := as_nres a) in *.
unfold SEC_NRES, SEC_JUNK, SEC_MUT, SEC_GST, A_INSTANCE in I1, I2, I3, I4. unfold kMaxNumChunks in NMX. unfold kPtrArrBlock in NMOD.
change (967832 + 112) with 967944 in I1. change (967832 + 128) with 967960 in I2. change (967832 + 680) with 968512 in I3. change (967832 + 688) with 968520 in I4.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGI : agree_on asegs (fun x => (967936 <= x < 968560) \/ (ptrarr_lo RE <= x < ptrarr_lo RE + 0x800000)) m mc)
by (eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Hz _; cbn [outside]; unfold ptrarr_lo in *;
repeat split; try exact I; intros [Y1 Y2]; destruct Hz as [Hz1|Hz1];
clear - Hz1 Y1 Y2 CEIL LO MK' SHB1 SHB3 TK QK QH AVQ TQD; lia);
apply (rw_cells_agree _ _ _ _ _ _ AGI) in I1; [| intros z Hz; cbn [cells_size csize Nat.add] in Hz; left; clear - Hz; lia];
apply (wjunk_agree _ _ _ _ _ AGI) in I2; [| intros z Hz; left; clear - Hz; lia];
apply (rw_cells_agree _ _ _ _ _ _ AGI) in I3; [| intros z Hz; cbn [cells_size csize Nat.add] in Hz; left; clear - Hz; lia];
apply (wjunk_agree _ _ _ _ _ AGI) in I4; [| intros z Hz; left; clear - Hz; lia];
destruct (wjunk69_open _ _ I2) as (jw0 & jw1 & jw2 & jw3 & jw4 & bsl & J1 & BSL & LBSL); clear I2; change (967960 + 40) with 968000 in BSL;
destruct (wjunk5_open _ _ I4) as (g0 & g1 & g2 & g3 & g4 & GS); clear I4;
apply (u64arr_agree _ _ _ _ _ _ AGI) in P1; [| intros z Hz; rewrite length_map in Hz; right; unfold ptrarr_lo in *; clear - Hz NLE NMX; subst nch nres; lia];
apply (hjunk_agree _ _ _ _ _ AGI) in P2; [| intros z Hz; right; unfold ptrarr_lo in *; clear - Hz NLE NMX; subst nch nres; lia];
clear AGI;
replace (ptrarr_lo RE + 8 * nres) with (ptrarr_lo RE + 8 * nch + Z.of_nat (Z.to_nat (8 * (nres - nch)))) in P2 by (clear - NLE; lia);
apply hjunk_cells in P2; destruct P2 as [pj P2];
apply (munch_weaken _ [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8); (rl_T X + 2872, rl_T X + 2888);
(967936, 968560); (ptrarr_lo RE, ptrarr_lo RE + 0x800000)]) in MU; [| unfold sub_fp; cbn [outside]; intros xw Hxw; clear - Hxw; tauto] end.

step. step. stp. step.
recast I3 [C4 (wz 0); C4 (wz 0)].
amo_step (amo_aligned_intro4 968512 ltac:(lia) ltac:(reflexivity)).
do 4 step. lits.
amo_step (amo_aligned_intro4 968512 ltac:(lia) ltac:(reflexivity)).
step. if_lit.
step. lits. step. if_lit.

step.
step. step.
rewrite (unsigned_lit nch), Z.shiftr_div_pow2 by lia. change (2^20) with 1048576. rewrite Z.div_small by (clear - NCH; lia). if_lit.

eapply evt_cut; [eapply swar_block; [eassumption| exists (msz / 4096); lia| exact I1]|].
intros ms' (a1s & a2s & a5s & a6s & E & -> & HE & HIDX).

step. if_cases EQN.
+
rewrite bv_eqb_Z, !unsigned_lit in EQN by lia.
apply evt_done. rewrite EQN. cbv beta iota. rewrite tbind_tvis.
lazymatch goal with |- aimplT _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RTj : RTconst RE X mc) end.
{ assert (FWrt : Forall (rt_avoid RE X) [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8);
(rl_T X + 2872, rl_T X + 2888); (967936, 968560); (ptrarr_lo RE, ptrarr_lo RE + 8388608)]).
{ clear - RL MK' AVO SHB1 SHB3 CEIL' CEIL LO SPR TK TB QK QH.
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_free; [exact RL| exact (proj2 MK')| intros o Ho; destruct (AVO o Ho); lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; lia| rewrite ?KHI_eq; lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [exact (rt_avoid_inst RE X RL)|].
constructor; [apply rt_avoid_ptrarr; [exact RL| lia| unfold ptrarr_hi, ptrarr_lo; lia]| constructor]. }
eapply RTconst_munch; [exact RT| exact MU| exact WM| exact FWrt]. }
apply Z.eqb_eq in EQN.
eapply largealloc_ensure; [exact GC| exact AVC| exact RT| exact RS| exact RSE0| exact CEIL'| unfold LARGE_STACK; clear - LO; lia| exact Hn| exact HP
| rewrite KP; exact MAL| exact MK'| exact MC'| exact AVm| exact MU| exact WM| eassumption| eassumption| exact RTj| exact FR| exact I1| exact J1| exact BSL| exact LBSL
| exact I3| exact GS| exact P1| exact P2| exact EQN| change (Z.of_nat (length (as_reg a))) with nch; clear - NCH; lia| exact ZBh| exact ZBp| exact ZBb| exact SFh| exact SBu| exact SFs| exact HE| exact HIDX].
+
rewrite bv_eqb_Z, !unsigned_lit in EQN by lia.
apply evt_done. rewrite EQN. cbv beta iota. rewrite tbind_tret. apply aimplT_ret.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RTj : RTconst RE X mc) end.
{ assert (FWrt : Forall (rt_avoid RE X) [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8);
(rl_T X + 2872, rl_T X + 2888); (967936, 968560); (ptrarr_lo RE, ptrarr_lo RE + 8388608)]).
{ clear - RL MK' AVO SHB1 SHB3 CEIL' CEIL LO SPR TK TB QK QH.
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_free; [exact RL| exact (proj2 MK')| intros o Ho; destruct (AVO o Ho); lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; lia| rewrite ?KHI_eq; lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [exact (rt_avoid_inst RE X RL)|].
constructor; [apply rt_avoid_ptrarr; [exact RL| lia| unfold ptrarr_hi, ptrarr_lo; lia]| constructor]. }
eapply RTconst_munch; [exact RT| exact MU| exact WM| exact FWrt]. }
apply Z.eqb_neq in EQN.
eapply (largealloc_finish RE X) with (nres1 := nres) (a := a);
[exact GC| exact AVC| exact RT| exact RS| exact RSE0| exact CEIL'| unfold LARGE_STACK; clear - LO; lia| exact Hn| exact HP| rewrite KP; exact MAL| exact MK'| exact MC'| exact AVm
| exact MU| exact WM| eassumption| eassumption| exact RTj| exact FR| exact I1| exact J1| exact BSL| exact LBSL| exact I3| exact GS| exact P1
| exact P2
| change (Z.of_nat (length (as_reg a))) with nch; clear - EQN NLE; lia| clear - NMX; lia| unfold kPtrArrBlock; exact NMOD| left; reflexivity
| exact ZBh| exact ZBp| exact ZBb| exact SFh| exact SBu| exact SFs| exact HE| exact HIDX
| reflexivity| reflexivity| reflexivity| reflexivity| intros c; reflexivity| reflexivity| reflexivity| reflexivity].
Qed.
End S.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QbcP_c1 Q61C QWRO Qu4g QFQR QKBN QN4c QjgW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QNQk QKBN QN4c QNQk.Mq6 QpY2.Mqb QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QOJv.Mqb QOJv.Mqa QmP7.Mq1 QYyZ.Mq8 Q9Ho.Mq3 QjgW QpME.Mq7.
Import QpY2.Mqc QcfN.Mq4.
Import Qu3b QYyZ.Mqc.
Import QmvA.Mq5.
Import QpME.Mqb QOJv.Mq9 QFd5.Mq7 QteI.Mqe.
Import QlES.
Import QpME. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.

Local Ltac QbcP_c1.if_lit ::= if_lit_lit. Local Ltac mkr__if_lit_0 := if_lit_lit.

Local Ltac QoSL.addr_eq_tac ::= addr_eq_tac_w. Local Ltac mkr__addr_eq_tac_1 := addr_eq_tac_w.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Ltac Q0z1.sf_hide_poison ::= sf_hide_poison_divlit. Local Ltac mkr__sf_hide_poison_3 := sf_hide_poison_divlit.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Lemma K44 : forall m, RTconst RE X m -> ro_cells asegs m 0x0e81a0 [C8 (wz 0x0ea208)] /\ ro_cells asegs m 0x0ea208 [C8 (wz 0x1a475)].
Proof. intros m RT. rtc RT 44%nat A. rtc RT 45%nat B. split; [exact A| exact B]. Qed.

Hypothesis map_or_die_spec : map_or_die_stmt L RE X.

Lemma largealloc_ensure : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (s : PStateA) (a : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (n lo : Z)
(rax t0 t1 t2 a1r a2 a5 a6 a7 s6x s7x s8x s9x t3 t4 t5 t6 : word) (m1 : mem)
(mb E : Z) (junk8 pj shu : list byte) (w0 w1 w2 w3 w4 g0 g1 g2 g3 g4 : word) (bsl : list word),
let msz := sec_map_size n in let sz := sec_size n in let reg := as_reg a in let nch := Z.of_nat (length reg) in let parr := ptrarr_lo RE in
let nres := as_nres a in
gcons a LB FS G RE X -> avoid_covers RE X -> RTconst RE X m -> RStats RE X m -> RSec a LB RE X m ->
band_lo <= lo -> lo <= bv_unsigned sp - LARGE_STACK -> 0 <= n <= 2^26 -> from_primary n = false ->
mb mod kPage = 0 -> appr mb msz -> mb + msz <= band_lo -> zavoids mb msz (avoid_of (ae_L RE) a) = true ->
munch [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8); (rl_T X + 2872, rl_T X + 2888);
(977856, 978480); (parr, parr + 0x800000)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -96) -> RTconst RE X m1 ->
rw_cells asegs m1 (bv_unsigned sp + -96) [CB 8 junk8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m1 977864 [C8 (wz nres); C8 (wz nch)] ->
rw_cells asegs m1 977880 [CB 8 (le8 w0); C8 w1; C8 w2; C8 w3; C8 w4] -> u64arr asegs m1 977920 bsl -> length bsl = 64%nat ->
rw_cells asegs m1 978432 [C4 (wz 1); C4 (wz 0)] ->
rw_cells asegs m1 978440 [C8 g0; C8 g1; C8 g2; C8 g3; C8 g4] ->
u64arr asegs m1 parr (map (fun e => wz (se_beg e)) reg) ->
rw_cells asegs m1 (parr + 8 * nch) [CB (Z.to_nat (8 * (nres - nch))) pj] ->
nch = nres -> nch < 2^20 ->
rw_cells asegs m1 mb [C8 (wz mb); C8 (wz msz); C8 (wz sz); C8 (wz 0)] ->
rw_cells asegs m1 (mb + 32) [CB 4064 (repeat (b8 0) 4064)] ->
rw_cells asegs m1 (mb + 4096) [CB (Z.to_nat (msz - 4096)) (repeat (b8 0) (Z.to_nat (msz - 4096)))] ->
rw_cells asegs m1 (SH mb) [CB (Z.to_nat 512) (repeat (b8 250) (Z.to_nat 512))] ->
rw_cells asegs m1 (SH (mb + 4096)) [CB (Z.to_nat (sz / 8)) shu] ->
rw_cells asegs m1 (SH (mb + 4096 + sz)) [CB (Z.to_nat ((msz - 4096 - sz) / 8)) (repeat (b8 250) (Z.to_nat ((msz - 4096 - sz) / 8)))] ->
0 <= E < 2^64 -> 16 <= Z.lxor E 63 <= 26 ->
aimplT atn
(tvis (EvMapFixed (al_ptrarr (ae_L RE) + 8 * as_nres a) kPtrArrBlockBytes)
(fun a2 => tbind (match a2 with AErr => tunr UCheck | AOk _ => tret (set_nres (as_nres a + kPtrArrBlock) a) end)
(fun s12 => tret (Some mb, add_spent (sec_cost msz) (set_reg (as_reg s12 ++ [mkSec mb msz n]) s12)))))
s (large_post RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB lo n m)
(MS (mkR rax (wz (bv_unsigned sp + -96)) gp (wz A_TP) t0 t1 t2 (wz 978440) (wz 977816)
(wz (mb + 4096)) a1r a2 (wz nch) (wz nres) a5 a6 a7 (wz msz) (wz E) (wz mb) (wz mb) s6x s7x s8x s9x s10 s11 t3 t4 t5 t6)
F (wz 0x441dc) fc None m1 (seg_rom asegs)).
Proof.
intros until bsl; intros msz sz reg nch parr nres GC AVC RT RS RSE CEIL LO Hn HP MAL MK MC AVm MU WM MI1 ST1 RT1 FR I1 J1 BSL LBSL I3 GS P1 P2 EQN NCH
ZBh ZBp ZBb SFh SBu SFs HE HIDX.
pose proof CEIL as CEIL'. idtac. unfold LARGE_STACK in LO.
pose proof MC as MC'. idtac. pose proof MK as MK'. apply appr_to_lia in MK; [| unfold msz; pose proof (sec_map_size_ge n ltac:(lia) HP) as [SM _]; lia| lia].
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _). rewrite KP in MAL.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & _ & _ & QAL & QK & QH & _). unfold ptrarr_hi in QH. change (al_ptrarr (ae_L RE)) with parr in QH, QAL |- *. fold parr in QK.
pose proof QK as QK'. rewrite ?KHI_eq in QK. pose proof QH as QH'. idtac.
pose proof (sec_size_facts n Hn HP) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). fold sz msz in Z1, Z2, Z3, Z4, Z5, Z6.
pose proof (avoid_facts RE X a mb msz AVC ltac:(lia) ltac:(lia) AVm) as (_ & AVO & AVP & AVQ & AVR). fold parr in AVQ.
hide MK'. hide QK'. apply appr_to_lia in QK; [| lia| lia].
assert (MBH : 0x647000 <= mb) by (clear - MK Z1 Z6; lia).
assert (SHB : 0x80000000 <= SH mb /\ SH (mb + msz) = SH mb + msz / 8 /\ SH mb + msz / 8 <= 0x10007fff8000) by (rewrite !SH_eq; clear - MBH MAL Z5 MC; Z.div_mod_to_equations; lia).
destruct SHB as (SHB1 & SHB2 & SHB3).
assert (SHE1 : SH (mb + 4096) = SH mb + 512) by (change (mb + 4096) with (mb + 8 * 512); apply SH_plus8).
assert (SHE2 : SH (mb + 4096 + sz) = SH mb + 512 + sz / 8) by (rewrite !SH_eq; clear - Z3; Z.div_mod_to_equations; lia).
pose proof RSE as (_ & _ & _ & _ & _ & _ & _ & NLE & NMX & NMOD). fold reg nch nres in NLE, NMX, NMOD. unfold kMaxNumChunks in NMX. unfold kPtrArrBlock in NMOD.
assert (NR : nres + 16384 <= 1048576) by (clear - EQN NCH NMOD; Z.div_mod_to_equations; lia).
rtc RT1 43%nat K43. change (A_INSTANCE + 80) with 977832 in K43. fold parr in K43, QAL.
assert (AAL : (parr + 8 * nres) mod 4096 = 0) by (clear - QAL NMOD; Z.div_mod_to_equations; lia).
apply aimplT_from_evt.
step.
step. step. step.
rewrite (unsigned_lit nch), Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
replace (nch * 8 + parr) with (parr + 8 * nres) by lia.
stp. step. step. stp.
step.
clear K43.
apply evt_done. eapply aimplT_map_fixed.
{ eapply map_or_die_spec; rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by lia;
[exact RT1| exact RL| exact MI1| exact ST1| exact CEIL'| unfold MAPORDIE_STACK; lia| exact AAL| reflexivity| lia| lia| lia
| apply rt_avoid_ptrarr; [exact RL| subst parr; lia| subst parr; unfold ptrarr_hi, ptrarr_lo; lia]]. }
intros ans ms' PO. cbv beta iota. destruct ans as [|xA].
-
apply aimplT_unr.
-
destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MUp & WMp & MI2 & ST2 & RT2 & -> & -> & ZP).
rewrite tbind_tret. cbn [as_reg as_nres set_nres].
rewrite !(unsigned_lit (bv_unsigned sp + -96)) in MUp, ST2 by lia. unfold MAPORDIE_STACK in MUp.
apply (munch_chain' _ _ m2 _ m MUp) in MU; [| sub_fp_solve].
pose proof (wmono_trans asegs _ _ _ WM WMp) as WM2.
clear P2 ST1 RT1 MI1.
assert (LM : Z.of_nat (length (map (fun e => wz (se_beg e)) reg)) = nch) by (rewrite length_map; lia).
hide Z3; hide Z4; hide Z5; hide MAL; hide QAL; hide NMOD; hide HIDX; hide HE; hide AAL; hide Hn; hide AVP.
transport_after_call asegs m1 m2 MUp WMp.
unhide Z3; unhide Z4; unhide Z5; unhide MAL; unhide QAL; unhide NMOD; unhide HIDX; unhide HE; unhide AAL; unhide Hn; unhide AVP.
clear MUp WMp WM. rename WM2 into WM.
apply aimplT_from_evt.
replace (ret_pc (wz 279040)) with (wz 279040) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step.
step. step.
stp. step.
step.
step.
apply evt_done. apply aimplT_ret.
eapply (largealloc_finish RE X) with (nres1 := nres + 16384) (a := a);
[exact GC| exact AVC| exact RT| exact RS| exact RSE| exact CEIL'| unfold LARGE_STACK; lia| exact Hn| exact HP| rewrite KP; exact MAL| exact MK'| exact MC'| exact AVm
| exact MU| exact WM| eassumption| eassumption| | exact FR| exact I1| exact J1| exact BSL| exact LBSL| exact I3| exact GS| exact P1
| change (Z.of_nat (length (as_reg a))) with nch; change (ptrarr_lo RE) with parr; rewrite EQN; replace (8 * (nres + 16384 - nres)) with 131072 by (clear; lia); exact ZP
| change (Z.of_nat (length (as_reg a))) with nch; clear - EQN; lia| exact NR| unfold kPtrArrBlock; clear - NMOD; Z.div_mod_to_equations; lia| right; unfold kPtrArrBlock; reflexivity
| exact ZBh| exact ZBp| exact ZBb| exact SFh| exact SBu| exact SFs| exact HE| exact HIDX
| reflexivity| reflexivity| reflexivity| reflexivity| intros c; reflexivity| reflexivity| reflexivity| reflexivity].

pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
assert (FWrt : Forall (rt_avoid RE X) [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8);
(rl_T X + 2872, rl_T X + 2888); (977856, 978480); (parr, parr + 8388608)]).
{ clear - RL MK' AVO SHB1 SHB3 CEIL' CEIL LO SPR TK TB QK QH.
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_free; [exact RL| exact (proj2 MK')| intros o Ho; destruct (AVO o Ho); lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; lia| rewrite ?KHI_eq; lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [exact (rt_avoid_inst RE X RL)|].
constructor; [apply rt_avoid_ptrarr; [exact RL| subst parr; lia| subst parr; unfold ptrarr_hi, ptrarr_lo; lia]| constructor]. }
eapply RTconst_munch; [exact RT| exact MU| exact WM| exact FWrt].
Qed.

Lemma large_alloc_spec : large_alloc_stmt RE X L.
Proof.
unfold large_alloc_stmt.
intros until lo; intros GC AVC RT RS RSE MI ST CEIL LO Hn HP.
pose proof CEIL as CEIL'. idtac. unfold LARGE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC, TD. rewrite ?KHI_eq in PK. idtac.
pose proof (sec_size_facts n Hn HP) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
set (sz := sec_size n) in *. set (msz := sec_map_size n) in *.
unfold large_alloc. fold msz.
rtc RT 25%nat K25. rtc RT 43%nat K43. destruct (K44 m RT) as [K44a K45a].
unfold large_alloc_entry, SEC, A_INSTANCE in *.
pose proof (munch_refl [(bv_unsigned sp - 800, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
apply aimplT_from_evt.
carve_frame 96%nat ST.
do 12 step.
step.
step. step. lits.
step. if_lit.
step.
step.
step. step. lits. step. if_lit.
step.
stp. stp. stp. stp.
rewrite (unsigned_lit (sz + 4095)) by lia. rewrite land_negpage by lia.
stp. stp.
step.
lazymatch goal with |- context [wz (sz + 4095 - ?r + 4096)] => replace (sz + 4095 - r + 4096) with msz by lia end.
stp. step.
step. ifz.
step.
step. step. step.
step. step.
clear K44a K45a.
apply evt_done. eapply aimplT_map_anon.
{ eapply (mmap_or_die_spec L RE X); rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by lia;
[ eapply RTconst_stack; [exact RT| exact RL| exact MU0| exact WM0| apply Forall_cons; [cbn [fst]; lia| apply Forall_nil]]
| exact RL| assumption| exact ST| exact CEIL'| unfold MMAPANON_STACK; lia| exact Z5| lia| lia
| intros b Hb AVb; exact (proj1 (avoid_facts RE X a b msz AVC ltac:(lia) Hb AVb))
| intros b o Hb AVb Ho; exact (proj1 (proj2 (avoid_facts RE X a b msz AVC ltac:(lia) Hb AVb)) o Ho) ]. }
intros ans ms' PO. destruct ans as [|mb].
-
destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & WM2 & MI2 & ST2 & RT2 & -> & MU2).
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2, MU2 by lia.
apply aimplT_ret.
replace (ret_pc (wz 278112)) with (wz 278112) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold MMAPANON_STACK in MU2.
assert (MU : munch [(bv_unsigned sp - 800, bv_unsigned sp)] m m2) by (eapply munch_trans; [exact MU0| eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia]).
pose proof (wmono_trans asegs _ _ _ WM0 WM2) as WM.
transport_after_call asegs m0 m2 MU2 WM2. clear MU0 WM0 MU2 WM2 MI.
step. if_lit.
do 11 step. step. step.
release_frame FR ST2 (bv_unsigned sp).
apply evt_done. unfold large_post. do 16 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [exact MI2|]. split; [exact ST2|]. split; [exact WM|]. split; [exact RT2|]. split.
{ eapply RStats_munch; [exact RS| exact MU| exact WM| apply Forall_cons; [st_avoid_solve| apply Forall_nil]]. }
split; [reflexivity|]. split; [reflexivity|]. split.
{ eapply munch_weaken; [| exact MU]. unfold W_large, LARGE_STACK, sub_fp. cbn [outside]. intros; lia. }
eapply RSec_frame; [exact RSE| exact WM|]. eapply agree_on_of_munch; [exact MU| exact WM|]. intros z Fx _. cbn [outside].
pose proof (fp_RSec_lt_ceil RE X _ _ _ _ z GC Fx). lia.
-
destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & WM2 & MI2 & ST2 & RT2 & -> & MAL & MK & MC & AVm & MU2 & ZB & (shj & SB)).
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2, MU2 by lia.
pose proof MC as MC'. idtac. pose proof MK as MK'. apply appr_to_lia in MK; [| unfold msz; pose proof (sec_map_size_ge n ltac:(lia) HP) as [SM _]; lia| lia].
pose proof (avoid_facts RE X a mb msz AVC ltac:(lia) ltac:(lia) AVm) as (_ & AVO & AVP & AVQ & AVR).
unfold MMAPANON_STACK in MU2.

cbv beta iota zeta.
destruct (Z.leb_spec0 kMaxNumChunks (Z.of_nat (length (as_reg a)))) as [BIG|NCH]; [apply aimplT_unr|].
unfold kMaxNumChunks in NCH.
apply aimplT_from_evt.
replace (ret_pc (wz 278112)) with (wz 278112) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (MU : munch [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH (mb + msz))] m m2).
{ eapply munch_trans; [eapply munch_weaken; [| exact MU0]; unfold sub_fp; cbn [outside]; intros; lia|].
eapply munch_weaken; [| exact MU2]. rewrite <- (SH_add mb (msz / 8)) by lia. replace (mb + 8 * (msz / 8)) with (mb + msz) by lia.
unfold sub_fp; cbn [outside]; intros; lia. }
pose proof (wmono_trans asegs _ _ _ WM0 WM2) as WM.
assert (SHB : 0x80000000 <= SH mb /\ SH (mb + msz) = SH mb + msz / 8 /\ SH mb + msz / 8 <= 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
destruct SHB as (SHB1 & SHB2 & SHB3). rewrite SHB2 in MU.
clear MU0 WM0 K25 K43. transport_after_call asegs m0 m2 MU2 WM2. clear MU2 WM2 MI.
rtc RT2 25%nat K25.
step. ifz.
step.
step. step. step.
rewrite (unsigned_lit mb), (Z.land_comm 4095 mb) by lia. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096.
replace (mb mod 4096) with 0 by lia.
step. if_lit.
step. step.
step.
rewrite (unsigned_lit (4096 + mb)) by lia. rewrite land_7 by lia. replace ((4096 + mb) mod 8) with 0 by lia.
stp. stp. stp. stp.
step. step.
step. step. step.
replace (0 + (4096 + mb)) with (mb + 4096) by lia.
rewrite (unsigned_lit (mb + 4096 + sz)), (unsigned_lit (mb + 4096 + 7)) by lia. rewrite !land_mask8 by lia.
replace (mb + 4096 + sz - (mb + 4096 + sz) mod 8) with (mb + 4096 + sz) by lia.
replace (mb + 4096 + 7 - (mb + 4096 + 7) mod 8) with (mb + 4096) by (Z.div_mod_to_equations; lia).
replace (msz + mb) with (mb + msz) by lia.
step.
replace (mb + 4096 - mb) with 4096 by lia.
stp. step.
step.

assert (M8 : msz / 8 = 512 + (sz / 8 + (msz - 4096 - sz) / 8)) by lia.
lazymatch type of SB with rw_cells _ ?mc _ _ =>
replace (Z.to_nat (msz / 8)) with (512 + (Z.to_nat (sz / 8) + Z.to_nat ((msz - 4096 - sz) / 8)))%nat in SB by lia;
destruct (rw_cells_CB_split mc _ _ _ _ SB) as [SBh SBr]; clear SB;
destruct (rw_cells_CB_split mc _ _ _ _ SBr) as [SBu SBs]; clear SBr end.
change (Z.of_nat 512) with 512 in SBu, SBs. rewrite Z2Nat.id in SBs by lia.
assert (SHE1 : SH (mb + 4096) = SH mb + 512) by (change (mb + 4096) with (mb + 8 * 512); apply SH_plus8).
assert (SHE2 : SH (mb + 4096 + sz) = SH mb + 512 + sz / 8) by (rewrite !SH_eq; clear - Z3; Z.div_mod_to_equations; lia).
rewrite <- SHE1 in SBu. rewrite <- SHE2 in SBs.
rewrite (unsigned_lit (mb + 4096)), (unsigned_lit mb) by lia. replace (mb + 4096 - mb) with 4096 by lia.

eapply evt_cut.
{ eapply (poison_shadow_spec_lh RE X); rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by lia; [exact RT2| exact RL| exact MI2| exact ST2| exact CEIL'| lia
| lia| reflexivity| lia| rewrite ?KHI_eq; change (2^47) with 140737488355328; clear - MK MC Z1 Z6; lia| lia| left; lia| exact SBh]. }
cbv beta. intros ms' PO. clear SBh.
destruct PO as (t0_ & t1_ & t2_ & a0_ & a1_ & a2_ & a3_ & a4_ & a5_ & a6_ & a7_ & t3_ & t4_ & t5_ & t6_ & m3 & -> & MUp & WMp & MI3 & ST3 & RT3 & SFh).
change (4096 / 8) with 512 in MUp, SFh. rewrite !(unsigned_lit (bv_unsigned sp + -96)) in MUp, ST3 by lia.
apply (munch_chain' _ _ m3 _ m MUp) in MU; [| sub_fp_solve].
pose proof (wmono_trans asegs _ _ _ WM WMp) as WM3.
transport_after_call asegs m2 m3 MUp WMp. clear MUp WMp WM MI2 RT2. try clear ST2. rename WM3 into WM.
replace (ret_pc (wz 278200)) with (wz 278200) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step.
rewrite (unsigned_lit (mb + msz)), (unsigned_lit (mb + 4096 + sz)) by lia.
replace (mb + msz - (mb + 4096 + sz)) with (msz - 4096 - sz) by lia.
stp. step. step.

eapply evt_cut.
{ eapply (poison_shadow_spec_lh RE X); rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by lia; [exact RT3| exact RL| exact MI3| exact ST3| exact CEIL'| lia
| lia| lia| lia| rewrite ?KHI_eq; change (2^47) with 140737488355328; clear - MK MC Z1 Z6; lia| lia| left; lia| exact SBs]. }
cbv beta. intros ms' PO. clear SBs.
destruct PO as (t0c & t1c & t2c & a0c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m4 & -> & MUp & WMp & MI4 & ST4 & RT4 & SFs).
rewrite !(unsigned_lit (bv_unsigned sp + -96)) in MUp, ST4 by lia.
assert (SHE3 : SH (mb + 4096 + sz) + (msz - 4096 - sz) / 8 = SH mb + msz / 8) by (rewrite !SH_eq; clear - Z3 Z5; Z.div_mod_to_equations; lia).    rewrite SHE3 in MUp.
apply (munch_chain' _ _ m4 _ m MUp) in MU; [| sub_fp_solve].
pose proof (wmono_trans asegs _ _ _ WM WMp) as WM4.
clear t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_.
transport_after_call asegs m3 m4 MUp WMp. clear MUp WMp WM MI3 RT3. try clear ST3. rename WM4 into WM.
replace (ret_pc (wz 278216)) with (wz 278216) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

step.
call_sp_ch (get_thread_stats_spec RE X) ltac:(fun PO => idtac); try eassumption; try lia.
subst. rename POST into RT5.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RS5 : RStats RE X mc) by (eapply RStats_munch; [exact RS| exact MU| exact WM| repeat (apply Forall_cons || apply Forall_nil); st_avoid_solve]);
destruct (RStats_mmap_words _ _ _ RS5) as (w1 & w2 & STC);
apply (munch_weaken _ [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8); (rl_T X + 2872, rl_T X + 2888)]) in MU;
[| unfold sub_fp; cbn [outside]; intros xw Hxw; clear - Hxw; tauto] end.
pose proof (AVO _ (T_obj RE X)) as TMB. cbn [fst snd] in TMB.
step. step.
step.
rewrite (unsigned_lit (mb + 4096)) by lia. rewrite land_7 by lia. replace ((mb + 4096) mod 8) with 0 by lia.
step. step.
step. step.
step. if_lit.
step. step. step. step.
rewrite ?(unsigned_lit (mb + 4096)) by lia.
rewrite (Z.land_comm 4095 (mb + 4096)). change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096.
replace ((mb + 4096) mod 4096) with 0 by lia.
step. if_lit.
step. unfold_cond; cond_unsig; if_false.
step. unfold_cond; cond_unsig; if_false.
step.
rewrite (unsigned_lit (mb + 4096)) by lia. replace (mb + 4096 - 4096) with mb by lia.

lazymatch type of ZB with rw_cells _ ?mc _ _ =>
replace (Z.to_nat msz) with (32 + (4064 + Z.to_nat (msz - 4096)))%nat in ZB by lia;
destruct (rw_cells_CB_split mc _ _ _ _ ZB) as [ZBh ZBr]; clear ZB;
destruct (rw_cells_CB_split mc _ _ _ _ ZBr) as [ZBp ZBb]; clear ZBr end.
rewrite firstn_repeat' in ZBh by lia. rewrite skipn_repeat', firstn_repeat' in ZBp by lia. rewrite !skipn_repeat' in ZBb.
replace (32 + (4064 + Z.to_nat (msz - 4096)) - 32 - 4064)%nat with (Z.to_nat (msz - 4096)) in ZBb by lia.
change (Z.of_nat 32) with 32 in ZBp, ZBb. change (Z.of_nat 4064) with 4064 in ZBb. replace (mb + 32 + 4064) with (mb + 4096) in ZBb by lia.
recast ZBh [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
step. step. step.
step. unfold_cond; cond_unsig; if_false.

pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & _ & _ & _ & TQD). unfold iv_disjoint in TQD. cbn [fst snd] in TQD.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & _ & _ & _ & QK & QH & _). unfold ptrarr_hi in QH. rewrite ?KHI_eq in QK. idtac.
pose proof RSE as RSE0. destruct RSE as (I1 & I2 & I3 & I4 & P1 & P2 & HD & NLE & NMX & NMOD).
set (reg := as_reg a) in *. set (nch := Z.of_nat (length reg)) in *. set (nres := as_nres a) in *.
unfold SEC_NRES, SEC_JUNK, SEC_MUT, SEC_GST, A_INSTANCE in I1, I2, I3, I4. unfold kMaxNumChunks in NMX. unfold kPtrArrBlock in NMOD.
change (977752 + 112) with 977864 in I1. change (977752 + 128) with 977880 in I2. change (977752 + 680) with 978432 in I3. change (977752 + 688) with 978440 in I4.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGI : agree_on asegs (fun x => (977856 <= x < 978480) \/ (ptrarr_lo RE <= x < ptrarr_lo RE + 0x800000)) m mc)
by (eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Hz _; cbn [outside]; unfold ptrarr_lo in *;
repeat split; try exact I; intros [Y1 Y2]; destruct Hz as [Hz1|Hz1];
clear - Hz1 Y1 Y2 CEIL LO MK' SHB1 SHB3 TK QK QH AVQ TQD; lia);
apply (rw_cells_agree _ _ _ _ _ _ AGI) in I1; [| intros z Hz; cbn [cells_size csize Nat.add] in Hz; left; clear - Hz; lia];
apply (wjunk_agree _ _ _ _ _ AGI) in I2; [| intros z Hz; left; clear - Hz; lia];
apply (rw_cells_agree _ _ _ _ _ _ AGI) in I3; [| intros z Hz; cbn [cells_size csize Nat.add] in Hz; left; clear - Hz; lia];
apply (wjunk_agree _ _ _ _ _ AGI) in I4; [| intros z Hz; left; clear - Hz; lia];
destruct (wjunk69_open _ _ I2) as (jw0 & jw1 & jw2 & jw3 & jw4 & bsl & J1 & BSL & LBSL); clear I2; change (977880 + 40) with 977920 in BSL;
destruct (wjunk5_open _ _ I4) as (g0 & g1 & g2 & g3 & g4 & GS); clear I4;
apply (u64arr_agree _ _ _ _ _ _ AGI) in P1; [| intros z Hz; rewrite length_map in Hz; right; unfold ptrarr_lo in *; clear - Hz NLE NMX; subst nch nres; lia];
apply (hjunk_agree _ _ _ _ _ AGI) in P2; [| intros z Hz; right; unfold ptrarr_lo in *; clear - Hz NLE NMX; subst nch nres; lia];
clear AGI;
replace (ptrarr_lo RE + 8 * nres) with (ptrarr_lo RE + 8 * nch + Z.of_nat (Z.to_nat (8 * (nres - nch)))) in P2 by (clear - NLE; lia);
apply hjunk_cells in P2; destruct P2 as [pj P2];
apply (munch_weaken _ [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8); (rl_T X + 2872, rl_T X + 2888);
(977856, 978480); (ptrarr_lo RE, ptrarr_lo RE + 0x800000)]) in MU; [| unfold sub_fp; cbn [outside]; intros xw Hxw; clear - Hxw; tauto] end.

step. step. stp. step.
recast I3 [C4 (wz 0); C4 (wz 0)].
amo_step (amo_aligned_intro4 978432 ltac:(lia) ltac:(reflexivity)).
do 4 step. lits.
amo_step (amo_aligned_intro4 978432 ltac:(lia) ltac:(reflexivity)).
step. if_lit.
step. lits. step. if_lit.

step.
step. step.
rewrite (unsigned_lit nch), Z.shiftr_div_pow2 by lia. change (2^20) with 1048576. rewrite Z.div_small by (clear - NCH; lia). if_lit.

eapply evt_cut; [eapply swar_block; [eassumption| exists (msz / 4096); lia| exact I1]|].
intros ms' (a1s & a2s & a5s & a6s & E & -> & HE & HIDX).

step. if_cases EQN.
+
rewrite bv_eqb_Z, !unsigned_lit in EQN by lia.
apply evt_done. rewrite EQN. cbv beta iota. rewrite tbind_tvis.
lazymatch goal with |- aimplT _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RTj : RTconst RE X mc) end.
{ assert (FWrt : Forall (rt_avoid RE X) [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8);
(rl_T X + 2872, rl_T X + 2888); (977856, 978480); (ptrarr_lo RE, ptrarr_lo RE + 8388608)]).
{ clear - RL MK' AVO SHB1 SHB3 CEIL' CEIL LO SPR TK TB QK QH.
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_free; [exact RL| exact (proj2 MK')| intros o Ho; destruct (AVO o Ho); lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; lia| rewrite ?KHI_eq; lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [exact (rt_avoid_inst RE X RL)|].
constructor; [apply rt_avoid_ptrarr; [exact RL| lia| unfold ptrarr_hi, ptrarr_lo; lia]| constructor]. }
eapply RTconst_munch; [exact RT| exact MU| exact WM| exact FWrt]. }
apply Z.eqb_eq in EQN.
eapply largealloc_ensure; [exact GC| exact AVC| exact RT| exact RS| exact RSE0| exact CEIL'| unfold LARGE_STACK; clear - LO; lia| exact Hn| exact HP
| rewrite KP; exact MAL| exact MK'| exact MC'| exact AVm| exact MU| exact WM| eassumption| eassumption| exact RTj| exact FR| exact I1| exact J1| exact BSL| exact LBSL
| exact I3| exact GS| exact P1| exact P2| exact EQN| change (Z.of_nat (length (as_reg a))) with nch; clear - NCH; lia| exact ZBh| exact ZBp| exact ZBb| exact SFh| exact SBu| exact SFs| exact HE| exact HIDX].
+
rewrite bv_eqb_Z, !unsigned_lit in EQN by lia.
apply evt_done. rewrite EQN. cbv beta iota. rewrite tbind_tret. apply aimplT_ret.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RTj : RTconst RE X mc) end.
{ assert (FWrt : Forall (rt_avoid RE X) [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8);
(rl_T X + 2872, rl_T X + 2888); (977856, 978480); (ptrarr_lo RE, ptrarr_lo RE + 8388608)]).
{ clear - RL MK' AVO SHB1 SHB3 CEIL' CEIL LO SPR TK TB QK QH.
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_free; [exact RL| exact (proj2 MK')| intros o Ho; destruct (AVO o Ho); lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; lia| rewrite ?KHI_eq; lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [exact (rt_avoid_inst RE X RL)|].
constructor; [apply rt_avoid_ptrarr; [exact RL| lia| unfold ptrarr_hi, ptrarr_lo; lia]| constructor]. }
eapply RTconst_munch; [exact RT| exact MU| exact WM| exact FWrt]. }
apply Z.eqb_neq in EQN.
eapply (largealloc_finish RE X) with (nres1 := nres) (a := a);
[exact GC| exact AVC| exact RT| exact RS| exact RSE0| exact CEIL'| unfold LARGE_STACK; clear - LO; lia| exact Hn| exact HP| rewrite KP; exact MAL| exact MK'| exact MC'| exact AVm
| exact MU| exact WM| eassumption| eassumption| exact RTj| exact FR| exact I1| exact J1| exact BSL| exact LBSL| exact I3| exact GS| exact P1
| exact P2
| change (Z.of_nat (length (as_reg a))) with nch; clear - EQN NLE; lia| clear - NMX; lia| unfold kPtrArrBlock; exact NMOD| left; reflexivity
| exact ZBh| exact ZBp| exact ZBb| exact SFh| exact SBu| exact SFs| exact HE| exact HIDX
| reflexivity| reflexivity| reflexivity| reflexivity| intros c; reflexivity| reflexivity| reflexivity| reflexivity].
Qed.
End S.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QYyZ.Mqb QmP7.Mq1 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QOJv.Mqa QOJv.Mqb QnRU.Mqi QVo2.Mq3.
Import QpY2.Mqc.
Import QteI.Mqg QteI.Mqh.
Import QlES.
Import QpME. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.

Local Ltac lia ::= lia_fast. Local Ltac mkr__lia_0 := lia_fast.
Local Ltac Q0z1.transport_lia ::= tslia_fast. Local Ltac mkr__transport_lia_1 := tslia_fast.
Local Ltac QbcP_c1.if_lit ::= if_lit_fast. Local Ltac mkr__if_lit_2 := if_lit_fast.
Local Ltac QN4c.sfp_cheap ::= sfp_fast. Local Ltac mkr__sfp_cheap_3 := sfp_fast.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Lemma coff_shift : forall c nc i sz, 1 <= c <= 31 -> 0 <= nc -> 0 <= i -> sz = class_size c ->
Z.shiftr (nc * sz + i * sz) 4 = coff c (nc + i).
Proof.
intros c nc i sz Hc Hn Hi ->. pose proof (class_size_facts c Hc) as [S1 S2]. unfold coff.
rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16.
assert (E : exists q, class_size c = 16 * q /\ 0 <= q) by (exists (class_size c / 16); Z.div_mod_to_equations; lia).
destruct E as (q & E & Q0). rewrite E.
replace (nc * (16 * q) + i * (16 * q)) with (((nc + i) * q) * 16) by lia. rewrite Z.div_mul by lia.
replace (16 * q) with (q * 16) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Lemma not_sll2_add : forall e i, 0 <= e < 2^64 -> 0 <= i < 2^60 ->
Z_to_bv 64 (e + Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 i)) 18446744073709551615))) 2) = Z_to_bv 64 (e - 4 * i - 4).
Proof.
intros e i He Hi. rewrite (unsigned_lit i) by lia. rewrite zb_lxor_ones by lia. rewrite unsigned_lit by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. apply Z_to_bv_eqm.
replace (e + (18446744073709551615 - i) * 4) with ((e - 4 * i - 4) + 4 * 2^64) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.

Section S.
Variables (L : lvp) (RE : aentry) (X : rlay).

Lemma carve_loop {BAND : Band} : forall k (i : Z) ra sp gp tp t0 t1 t2 s0 s1 s2 a3v a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (c nc nf endp alloc newc off : Z) (Q : machine_state -> Prop),
off = alloc + i * class_size c ->
Z.of_nat k = newc - i -> 0 <= i < newc -> 1 <= c <= 30 -> 0 <= nc -> 0 <= nf -> alloc = nc * class_size c ->
endp = fa_beg (ae_L RE) c + 4 * (nf + newc) -> 17594333495296 <= fa_beg (ae_L RE) c -> fa_beg (ae_L RE) c + 4 * (nf + newc) <= band_lo ->
alloc + newc * class_size c <= 3758096384 ->
mem_inv asegs m ->
hjunk m (fa_beg (ae_L RE) c + 4 * nf) (endp - 4 * i) ->
u32arr asegs m (endp - 4 * i) (rev (map (coffw c) (carved nc (Z.to_nat i)))) ->
(forall m' (a4' a5' : word), mem_inv asegs m' -> munch [(fa_beg (ae_L RE) c + 4 * nf, endp)] m m' -> wmono asegs m m' ->
u32arr asegs m' (fa_beg (ae_L RE) c + 4 * nf) (rev (map (coffw c) (carved nc (Z.to_nat newc)))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz newc) (wz endp) (wz (alloc + newc * class_size c)) a3v a4' a5' a6 a7
s2 (wz newc) s4 (wz (class_size c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x44800) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz i) (wz endp) (wz off) a3v a4 a5 a6 a7
s2 (wz newc) s4 (wz (class_size c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x447e0) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until Q; intros -> HK Hi Hc Hnc Hnf HA HE FLO FHI AB MI HJ ARR CONT; [lia|].
pose proof (class_size_facts c ltac:(lia)) as [S1 S2]. hide S2.
assert (SR : 0 <= i * class_size c /\ i * class_size c + class_size c <= newc * class_size c) by (clear - Hi S1; nia).
pose proof (munch_refl [(fa_beg (ae_L RE) c + 4 * nf, endp)] m) as MU. pose proof (wmono_refl asegs m) as WM.

destruct (hjunk_split _ _ (endp - 4 * i - 4) _ HJ ltac:(lia)) as [HJ0 HJ1].
assert (HJ1' : hjunk m (endp - 4 * i - 4) (endp - 4 * i - 4 + Z.of_nat 4)) by (replace (endp - 4 * i - 4 + Z.of_nat 4) with (endp - 4 * i) by lia; exact HJ1).
destruct (hjunk_cells _ _ _ HJ1') as [junk SC]. clear HJ1 HJ1'.
step.
rewrite (unsigned_lit (alloc + i * class_size c)) by lia.
replace (Z.shiftr (alloc + i * class_size c) 4) with (coff c (nc + i)) by (rewrite HA; symmetry; apply coff_shift; lia).
step. step. step. step.
rewrite (not_sll2_add endp i) by lia. replace (endp - 4 * i - 4) with (endp - 4 * i - 4) by lia.
step.
step.
replace (alloc + i * class_size c + class_size c) with (alloc + (i + 1) * class_size c) by lia.
with_mem ltac:(fun mm =>
assert (ARR1 : u32arr asegs mm (endp - 4 * (i + 1)) (rev (map (coffw c) (carved nc (Z.to_nat (i + 1))))));
[ replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; rewrite carved_S, map_app, rev_app_distr; cbn [map rev app];
rewrite Z2Nat.id by lia; replace (endp - 4 * (i + 1)) with (endp - 4 * i - 4) by (first [ clear - HK newc endp c i k BAND; lia | lia ]);
apply u32arr_cons; [exact SC| replace (endp - 4 * i - 4 + 4) with (endp - 4 * i) by lia; exact ARR] |]).
clear SC ARR.
step.
destruct (Z.ltb_spec (i + 1) newc) as [MORE|DONE].
- ifz. eapply (IH (i + 1) ra sp gp tp t0 t1 t2 s0 s1 s2 a3v _ _ a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ c nc nf endp alloc newc _ Q);
[reflexivity| lia| lia| lia| lia| lia| exact HA| exact HE| lia| lia| lia| assumption| | exact ARR1|].
+ eapply hjunk_wmono; [| exact WM]. replace (endp - 4 * (i + 1)) with (endp - 4 * i - 4) by lia. exact HJ0.
+ intros m' a4' a5' MI' MU' WM' ARR'. apply (CONT m' a4' a5' MI'); [| | exact ARR'].
* eapply munch_trans; [exact MU| exact MU'].
* eapply wmono_trans; [exact WM| exact WM'].
- ifz. assert (E : i + 1 = newc) by lia. rewrite E in ARR1 |- *.
replace (endp - 4 * newc) with (fa_beg (ae_L RE) c + 4 * nf) in ARR1 by lia.
apply (CONT _ _ _ MI MU WM ARR1).
Qed.
End S.

Definition pop_rest_tree (AL : ALay) (s1 : AState) (c : Z) : T (bool * AState) :=
let x1 := cls s1 c in
let size := class_size c in
let new_chunks := (c_mapped_user x1 - c_alloc_user x1) / size in
let total_freed := c_num_freed x1 + new_chunks in
tbind (ensure_fa AL s1 c total_freed) (fun r =>
let '(ok2, s2) := r in
if negb ok2 then tret (false, s2)
else let x2 := cls s2 c in
tret (true, set_cls c (set_alloc_user (c_alloc_user x2 + new_chunks * size) (set_num_freed total_freed x2)) s2)).

Lemma efa_rel_true : forall aa c tf s2, efa_rel aa c tf (true, s2) ->
c_alloc_user (cls s2 c) = c_alloc_user (cls aa c) /\ c_mapped_user (cls s2 c) = c_mapped_user (cls aa c)
/\ c_num_freed (cls s2 c) = c_num_freed (cls aa c) /\ c_count (cls s2 c) = c_count (cls aa c)
/\ as_cache_inited s2 = as_cache_inited aa /\ 4 * tf <= c_mapped_fa (cls s2 c)
/\ (forall c', c' <> c -> cls s2 c' = cls aa c').
Proof.
intros aa c tf s2 [[E LE]|[(v & E & LE & _)|E]]; [| | discriminate]; apply (f_equal snd) in E; cbn [snd] in E; subst s2.
- repeat split; auto; lia.
- rewrite cls_set_cls_eq. cbn. repeat split; auto; try lia. intros c' Hc'. apply cls_set_cls_ne. exact Hc'.
Qed.

Section S3.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Lemma populate_C : forall x1 t0 t1 t2 x9 a1 a2 a4 a5 a6 a7 x19 x22 t3 t4 t5 t6 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
(F : bvmap 5 word) fc (m0 m : word -> option byte) (s : PStateA) (aa : AState) (G : ghost) (c lo v : Z),
let x := cls aa c in
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrimL aa G RE X m c v -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp + -64) -> band_lo <= lo -> lo <= bv_unsigned sp - POPULATE_STACK ->
munch (pop_W RE X (bv_unsigned sp) c (c_alloc_user x)) m0 m -> wmono asegs m0 m ->
rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
1 <= c <= 30 ->
aimplT atn (pop_rest_tree (ae_L RE) aa c) s
(fun r s' ms' => s' = s /\ pop_post RE X ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s G c (c_alloc_user x) lo m0 v r s' ms')
(MS (mkR x1 (wz (bv_unsigned sp + -64)) gp (wz A_TP) t0 t1 t2 (wz (ri_addr RE c)) x9 (wz A_INSTANCE) a1 a2 (wz (c_alloc_user x)) a4 a5 a6 a7
(wz (reg_beg (ae_L RE) c)) x19 (wz (c_mapped_user x)) (wz (class_size c)) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x44798) fc None m (seg_rom asegs)).
Proof.
intros until v; intros x RT RL RS RP MI ST CEIL LO MU WM FR Hc.
pose proof CEIL as CEIL'. idtac. unfold POPULATE_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq). hide PAL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK. encode_or TD. hide TA. hide TK.
pose proof (class_size_facts c ltac:(lia)) as [SZ1 SZ2]. hide SZ2.

destruct (RPrimL_open _ _ _ _ _ _ _ RP) as (K & HJS & GNE & HCall & _ & HC). apply class_repL_split in HC.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC0 & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & P12 & P13 & _ & _ & _ & G2 & G3 & G4 & G5). hide G5.
pose proof (cr_pure_div8 aa G c (K c) PU ltac:(lia)) as ((qa & QA0 & QA & QAE) & (qm & QM0 & QM) & E8). hide QAE.
subst x. cbv beta delta [ri_cellsL] in RI. cbv beta delta [pc_cells] in PC0. unfold ri_addr, pc_addr in *. unfold A_INSTANCE in *.
set (newc := (c_mapped_user (cls aa c) - c_alloc_user (cls aa c)) / class_size c).
assert (NEWC : 0 <= newc /\ newc * class_size c <= c_mapped_user (cls aa c) - c_alloc_user (cls aa c) < newc * class_size c + class_size c).
{ subst newc. clear - G3 SZ1. Z.div_mod_to_equations. nia. }
apply aimplT_from_evt.
step.
step.
step.
rewrite (unsigned_lit (c_mapped_user (cls aa c))), (unsigned_lit (c_alloc_user (cls aa c))) by lia.
rewrite divu_word by (first [ clear - G4 G3 G2 SZ1 KO c aa X RE; lia | lia ]). fold newc.
stp. step. step. step.
assert (NB : newc * 32 <= 3758096384) by (clear - NEWC SZ1 G2 G4 KO; clearbody newc; rewrite ?KO in G4; nia).
assert (SFB : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ unhide PAL. rewrite FB. unfold SH, A_SHADOW_OFS. unfold prim_hi, prim_lo in *. Z.div_mod_to_equations. (first [ clear - H29 q5 H16 H15 H5 H4 r0 q0 H0 H r q r2 G3 LCH CH K SZ1 PCH PK PAL r5 KM Hc c aa RE BAND; lia | lia ]). }
pose proof SH_band as SHBD0.
assert (SRB : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH (fa_beg (ae_L RE) c)).
{ unhide PAL. rewrite FB, RB. unfold SH, A_SHADOW_OFS. unfold prim_hi, prim_lo in *. Z.div_mod_to_equations. (first [ clear - H29 q5 H16 H15 H5 H4 r0 q0 H0 H r q r2 G3 LCH CH K SZ1 PK PAL r5 KM Hc c aa RE BAND; lia | lia ]). }
step.
clear RI PC0 ACH HCH REG HCall HJS GNE.
apply evt_done. unfold pop_rest_tree. rewrite ?KM, ?KO. fold newc.
eapply aimplT_bind.
{ eapply (ensure_fa_spec L RE X) with (v := v); try eassumption.
- rewrite unsigned_lit by lia. exact ST.
- rewrite unsigned_lit by lia. unfold ENSUREFA_STACK. lia.
- rewrite K32. lia.
- lia. }
intros [ok2 a2'] s' ms' POST. unfold efa_post in POST.
destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m1 & -> & -> & MU2 & WM2 & MI2 & ST2 & RT2 & RS2 & RP2 & A0 & REL).
cbn [fst snd] in A0, RP2. subst ra0.
rewrite !(unsigned_lit (bv_unsigned sp + -64)) in * by (first [ clear - SPR CEIL' LO lo c aa sp X RE BAND; lia | lia ]).
replace (ret_pc (wz 280504)) with (wz 280504) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold efa_W, ENSUREFA_STACK, ri_addr in MU2. rewrite ?KS in MU2. change (536870912 / 8) with 67108864 in MU2.
hide MU. transport_after_call asegs m m1 MU2 WM2. unhide MU.
unfold pop_W, POPULATE_STACK, ri_addr in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
assert (MU' : munch _ m0 m1) by (eapply munch_chain; [exact MU| exact MU2| sub_fp_solve]).
clear MU MU2 WM2 MI RT RS RP; rename MU' into MU. rename MI2 into MI; rename RT2 into RT; rename RS2 into RS; rename ST2 into ST.
destruct ok2; cbn [negb].
2:{
apply aimplT_ret.
step. if_lit.
step. step.
step. do 8 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. split; [reflexivity|].
unfold pop_post. do 16 eexists. exists 0%nat. split; [reflexivity|]. split; [reflexivity|].
split. { unfold pop_W, POPULATE_STACK, ri_addr. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact RT|]. split; [exact RS|]. split; [| reflexivity].
cbn [snd repeat]. apply RPrimL_gappend_nil. exact RP2. }

rename a2' into a2s. destruct (efa_rel_true _ _ _ _ REL) as (EA & EM & EN & EC & EI & LE4 & EO).

destruct (RPrimL_open _ _ _ _ _ _ _ RP2) as (K2 & HJS & GNE & HCall & _ & HC). apply class_repL_split in HC.
destruct HC as (((k1 & k2 & k3 & k4 & RI) & PC0 & (CH2 & ACH & LCH2 & HCH2)) & PU2 & REG).
specialize (REG ltac:(lia)). destruct REG as (FA & FJ & HU & FS).
apply cr_user_split in HU. destruct HU as (HSL & UT & US & UJ).
rewrite ?KS, ?KM, ?KO, ?EA, ?EM, ?EN, ?EC, ?EI in *.
pose proof PU2 as (Q1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q11 & Q12 & Q13 & Q14 & _ & _ & _ & _ & _ & _). rewrite ?EN in Q1, Q11, Q12. hide Q14.
assert (LFA : Z.of_nat (length (map (fun i : Z => wz (coff c i)) (pk_fl (K2 c)))) = c_num_freed (cls aa c)) by (rewrite length_map; exact Q1).
cbv beta delta [ri_cellsL] in RI. cbv beta delta [pc_cells] in PC0. unfold ri_addr, pc_addr in RI, PC0, ACH.
rewrite EA, EM, EN in RI. rewrite EC in PC0.
rewrite QA in US. rewrite SH_plus8 in US. rewrite QM in UJ at 1. replace 3758096384 with (8 * 469762048) in UJ by reflexivity. rewrite !SH_plus8 in UJ.
assert (KS8 : 536870912 = 8 * 67108864) by reflexivity. rewrite KS8, SH_plus8 in FS.
pose proof (munch_refl [(bv_unsigned sp - 512, bv_unsigned sp); (rl_T X + 2768, rl_T X + 3168);
(region_info RE + 128 * c, region_info RE + 128 * c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + 536870912);
(SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + 67108864);
(reg_beg (ae_L RE) c + 8 * qa, reg_beg (ae_L RE) c + 3758096384);
(SH (reg_beg (ae_L RE) c) + qa, SH (reg_beg (ae_L RE) c) + 469762048)] m1) as MUm.
pose proof (wmono_refl asegs m1) as WMm.
lazymatch type of MUm with munch ?W _ _ =>
assert (FWrt : Forall (rt_avoid RE X) W);
[| assert (FWst : Forall st_avoid W); [| assert (FWc : Forall (wc_ok RE X c) W)]] end.
{ constructor; [apply rt_avoid_stack; [exact RL| (first [ clear - a2s qa PK CEIL' LO lo c aa sp X RE BAND; lia | lia ])]|].
constructor; [apply rt_avoid_Thigh; [exact RL| (first [ clear - a2s qa c aa X RE BAND; lia | lia ])| (first [ clear - a2s qa c aa X RE BAND; lia | lia ])]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; (first [ clear - a2s qa RIq PK Hc c aa X RE BAND; lia | lia ])| unfold prim_hi, prim_lo in *; (first [ clear - a2s qa RIq PK Hc c aa X RE BAND; lia | lia ])]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; (first [ clear - a2s qa PK FB Hc c aa X RE BAND; lia | lia ])| unfold prim_hi, prim_lo in *; (first [ clear - a2s qa PK FB Hc c aa X RE BAND; lia | lia ])]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; (first [ clear - a2s SFB qa c aa X RE BAND; lia | lia ])| rewrite ?KHI_eq; (first [ clear - a2s SHBD0 SFB qa c aa X RE BAND; lia | lia ])]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; (first [ clear - a2s QM qm QA qa G3 G2 SZ1 PK RB Hc c aa X RE BAND; lia | lia ])| unfold prim_hi, prim_lo in *; (first [ clear - a2s qa PK RB Hc c aa X RE BAND; lia | lia ])]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; (first [ clear - a2s SRB QA qa G3 G2 SZ1 c aa X RE BAND; lia | lia ])| rewrite ?KHI_eq; (first [ clear - a2s SRB SHBD0 SFB qa c aa X RE BAND; lia | lia ])]| constructor]. }
{ repeat (constructor; [st_avoid_solve|]). constructor. }
{ constructor; [cbn; left; (first [ clear - a2s qa PK CEIL' LO lo c aa sp X RE BAND; lia | lia ])|]. constructor; [cbn; right; left; (first [ clear - a2s qa c aa X RE BAND; lia | lia ])|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; left; unfold ri_addr; exact Hz|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; do 2 right; left; rewrite KS; exact Hz|].
constructor; [cbn -[fp_cls SH Z.div]; do 2 right; intros z Hz; do 3 right; left; split; cbn [fst snd]; rewrite ?KS; [(first [ clear - Hz z a2s qa c aa X RE BAND; lia | lia ])| change (536870912 / 8) with 67108864; (first [ clear - Hz z a2s qa c aa X RE BAND; lia | lia ])]|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; do 4 right; left; rewrite KO; (first [ clear - Hz z a2s NEWC newc QA qa G3 G2 PK c aa X RE BAND; lia | lia ])|].
constructor; [| constructor]. cbn -[fp_cls SH Z.div]; do 2 right; intros z Hz; do 5 right; split; cbn [fst snd]; rewrite ?KO; [(first [ clear - Hz z a2s NEWC newc QA qa G3 G2 c aa X RE BAND; lia | lia ])| change (3758096384 / 8) with 469762048; (first [ clear - Hz z a2s qa c aa X RE BAND; lia | lia ])]. }
apply aimplT_ret.
step. ifz.
step.
step.
set (nc := ncarved G c) in *.
assert (NC0 : 0 <= nc) by (subst nc; unfold ncarved; lia).

lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists (v9 v0 v1 v2 v4 v5 : word) m',
ms2 = MS (@bvmap_set 5 word 9 v9 (@bvmap_set 5 word 10 v0 (@bvmap_set 5 word 11 v1 (@bvmap_set 5 word 12 v2 (@bvmap_set 5 word 14 v4 (@bvmap_set 5 word 15 v5 R))))))
FF (wz 0x44800) fcc rv m' ro
/\ munch [(fa_beg (ae_L RE) c + 4 * c_num_freed (cls aa c), fa_beg (ae_L RE) c + 4 * (c_num_freed (cls aa c) + newc))] mm m'
/\ wmono asegs mm m' /\ mem_inv asegs m'
/\ u32arr asegs m' (fa_beg (ae_L RE) c + 4 * c_num_freed (cls aa c)) (rev (map (coffw c) (carved nc (Z.to_nat newc))))))
end.
{ destruct (Z.ltb_spec (c_mapped_user (cls aa c) - c_alloc_user (cls aa c)) (class_size c)) as [NO|GO].
- ifz. assert (NZ : newc = 0) by (subst newc; apply Z.div_small; (first [ clear - NO K2 a2s qa G3 K c G aa X RE; lia | lia ])).
apply evt_done. do 7 eexists. split; [simp_regs; reflexivity|].
split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [assumption|].
rewrite NZ. cbn. apply u32arr_nil. (first [ clear - LFA Q13 Q12 K2 a2s qa G3 K SZ1 PH PCH PK FB KS Hc c G aa X RE BAND; lia | lia ]).
- ifz. assert (NZ : 1 <= newc) by (subst newc; apply Z.div_le_lower_bound; (first [ clear - K2 a2s qa K SZ1 c G aa X RE GO; lia | lia ])).
step. step. step. step. stp. step. step.
rewrite (unsigned_lit (c_num_freed (cls aa c) + newc)) by (first [ clear - NZ LFA K2 LE4 a2s NB NEWC newc QM qm QA qa G3 G2 P13 P12 K SZ1 c G aa X RE; lia | lia ]). rewrite Z.shiftl_mul_pow2 by (first [ clear - K2 a2s qa K c G aa X RE; lia | lia ]). change (2^2) with 4.
replace (reg_beg (ae_L RE) c + 3758096384 + (c_num_freed (cls aa c) + newc) * 4) with (fa_beg (ae_L RE) c + 4 * (c_num_freed (cls aa c) + newc)) by (rewrite FB, RB; lia).
rewrite KS in Q13.
destruct (hjunk_split _ _ (fa_beg (ae_L RE) c + 4 * (c_num_freed (cls aa c) + newc)) _ FJ ltac:((first [ clear - NZ K2 LE4 a2s newc qa G3 K SZ1 PK c G aa X RE BAND; lia | lia ]))) as [FJa FJb].
eapply (carve_loop RE (Z.to_nat newc) 0) with (nc := nc) (nf := c_num_freed (cls aa c)) (alloc := c_alloc_user (cls aa c)).
+ (first [ clear - K2 a2s qa K c G aa X RE; lia | lia ]). + (first [ clear - NZ LFA K2 LE4 a2s NEWC newc QM qm QA qa G3 G2 K SZ1 c G aa X RE; lia | lia ]). + (first [ clear - NZ K2 a2s newc qa K c G aa X RE; lia | lia ]). + (first [ clear - a2s qa Hc c G aa X RE BAND; lia | lia ]). + exact NC0. + (first [ clear - K2 a2s qa P11 K c G aa X RE; lia | lia ]). + unhide QAE. subst nc. rewrite QA, QAE. clear - E8. nia.
+ reflexivity. + rewrite FB. (first [ clear - a2s qa PK Hc c G aa X RE BAND; lia | lia ]). + rewrite FB. unfold prim_hi, prim_lo in *. (first [ clear - Q13 K2 LE4 a2s newc qa G3 K SZ1 PCH PK Hc c G aa X RE BAND; lia | lia ]).
+ rewrite ?KO in G4. clear - NEWC G4. lia.
+ assumption.
+ replace (fa_beg (ae_L RE) c + 4 * (c_num_freed (cls aa c) + newc) - 4 * 0) with (fa_beg (ae_L RE) c + 4 * (c_num_freed (cls aa c) + newc)) by (first [ clear - K2 a2s newc qa K c G aa X RE BAND; lia | lia ]). exact FJa.
+ cbn. replace (fa_beg (ae_L RE) c + 4 * (c_num_freed (cls aa c) + newc) - 4 * 0) with (fa_beg (ae_L RE) c + 4 * (c_num_freed (cls aa c) + newc)) by (first [ clear - K2 a2s newc qa K c G aa X RE BAND; lia | lia ]). apply u32arr_nil. rewrite FB. (first [ clear - NZ LFA K2 LE4 a2s NB newc qa G3 P13 P12 K SZ1 PH PCH PK Hc c G aa X RE BAND; lia | lia ]).
+ intros m' a4' a5' MI' MU' WM' ARR'. apply evt_done. do 7 eexists. split; [simp_regs; reflexivity|].
split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. exact ARR'. }
intros ms2 (v9 & v0 & v1 & v2 & v4 & v5 & m2 & -> & MU3 & WM3 & MI3 & ARR). simp_regs.
assert (LARR : Z.of_nat (length (rev (map (coffw c) (carved nc (Z.to_nat newc))))) = newc) by (rewrite length_rev, length_map, carved_length; (first [ clear - LFA K2 LE4 a2s NEWC newc E8 QM qm QA qa G3 G2 K SZ1 c G aa X RE; lia | lia ])).

hide MU. hide MUm. transport_after_call asegs m1 m2 MU3 WM3. unhide MU. unhide MUm.
assert (MU' : munch _ m0 m2) by (eapply munch_chain; [exact MU| exact MU3| sub_fp_solve]).
assert (MUm' : munch _ m1 m2) by (eapply munch_chain; [exact MUm| exact MU3| sub_fp_solve]).
clear MU MUm MU3 WM3 MI; rename MU' into MU; rename MUm' into MUm; rename MI3 into MI.
step.
step.
rewrite (unsigned_lit newc), (unsigned_lit (class_size c)) by (first [ clear - K2 a2s NEWC newc nc qa G4 G3 G2 K SZ1 c G aa X RE; lia | lia ]).
step.
step. step.
step. step.
step. unfold_cond; cond_unsig; if_false.
step. step. step. if_lit.
stf.
step. step. do 8 step. step. step.
release_frame FR ST (bv_unsigned sp).
change (b8 (bv_unsigned (wz 0))) with (b8 0) in RI.
apply evt_done. split; [reflexivity|].
pose proof (RTconst_munch _ _ _ _ _ RT MUm WMm FWrt) as RT'. pose proof (RStats_munch _ _ _ _ _ RS MUm WMm FWst) as RS'.
epose proof (agree_other_classes _ _ _ _ _ _ RL _ MUm WMm FWc) as OTH. Unshelve. 2:{ lia. }
lazymatch goal with |- pop_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?m3 _) =>
assert (AGS : agree_on asegs (szone RE c (c_alloc_user (cls aa c))) m1 m3) end.
{ eapply agree_on_of_munch; [exact MUm| exact WMm|]. intros z Uz Hz. unfold szone in Uz. rewrite QA in Uz.
rewrite (Z.mul_comm 8 qa), Z.div_mul in Uz by (first [ clear - K2 a2s nc qa K newc c G aa X RE BAND; lia | lia ]). cbn [outside]. clear - Uz Hz QA0 SRB SFB CEIL LO RB FB PK PCH PH RIq TK TB TD G2 G3 G4 QA Hc. unhide TK. (first [ clear - Uz z SRB SFB QA qa G4 G3 G2 TD TK RIq PH PCH PK FB RB Hc LO CEIL lo c aa sp X RE BAND; lia | lia ]). }
unfold pop_post. do 16 eexists. exists (Z.to_nat newc). split; [reflexivity|]. split; [reflexivity|].
split. { unfold pop_W, POPULATE_STACK, ri_addr. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact RT'|]. split; [exact RS'|]. split; [| reflexivity].
cbn [snd]. unhide QAE.
eapply (populate_close aa a2s G RE X m1 _ c K2 k1 k2 k3 k4 CH2 qa qm newc v); try eassumption; try (first [ clear - K2 a2s NEWC nc qa K newc c G aa X RE; lia | lia ]).
Qed.
End S3.
End Mq2.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVo2.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq4. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.

Local Ltac lia ::= lia_fast. Local Ltac mkr__lia_0 := lia_fast.
Local Ltac Q0z1.transport_lia ::= tslia_fast. Local Ltac mkr__transport_lia_1 := tslia_fast.
Local Ltac QsGW.if_lit ::= if_lit_fast. Local Ltac mkr__if_lit_2 := if_lit_fast.
Local Ltac Qu1d.sfp_cheap ::= sfp_fast. Local Ltac mkr__sfp_cheap_3 := sfp_fast.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Lemma coff_shift : forall c nc i sz, 1 <= c <= 31 -> 0 <= nc -> 0 <= i -> sz = class_size c ->
Z.shiftr (nc * sz + i * sz) 4 = coff c (nc + i).
Proof.
intros c nc i sz Hc Hn Hi ->. pose proof (class_size_facts c Hc) as [S1 S2]. unfold coff.
rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16.
assert (E : exists q, class_size c = 16 * q /\ 0 <= q) by (exists (class_size c / 16); Z.div_mod_to_equations; lia).
destruct E as (q & E & Q0). rewrite E.
replace (nc * (16 * q) + i * (16 * q)) with (((nc + i) * q) * 16) by lia. rewrite Z.div_mul by lia.
replace (16 * q) with (q * 16) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Lemma not_sll2_add : forall e i, 0 <= e < 2^64 -> 0 <= i < 2^60 ->
Z_to_bv 64 (e + Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 i)) 18446744073709551615))) 2) = Z_to_bv 64 (e - 4 * i - 4).
Proof.
intros e i He Hi. rewrite (unsigned_lit i) by lia. rewrite zb_lxor_ones by lia. rewrite unsigned_lit by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. apply Z_to_bv_eqm.
replace (e + (18446744073709551615 - i) * 4) with ((e - 4 * i - 4) + 4 * 2^64) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.

Section S.
Variables (L : lvp) (RE : aentry) (X : rlay).

Lemma carve_loop {BAND : Band} : forall k (i : Z) ra sp gp tp t0 t1 t2 s0 s1 s2 a3v a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (c nc nf endp alloc newc off : Z) (Q : machine_state -> Prop),
off = alloc + i * class_size c ->
Z.of_nat k = newc - i -> 0 <= i < newc -> 1 <= c <= 30 -> 0 <= nc -> 0 <= nf -> alloc = nc * class_size c ->
endp = fa_beg (ae_L RE) c + 4 * (nf + newc) -> 17594333495296 <= fa_beg (ae_L RE) c -> fa_beg (ae_L RE) c + 4 * (nf + newc) <= band_lo ->
alloc + newc * class_size c <= 3758096384 ->
mem_inv asegs m ->
hjunk m (fa_beg (ae_L RE) c + 4 * nf) (endp - 4 * i) ->
u32arr asegs m (endp - 4 * i) (rev (map (coffw c) (carved nc (Z.to_nat i)))) ->
(forall m' (a4' a5' : word), mem_inv asegs m' -> munch [(fa_beg (ae_L RE) c + 4 * nf, endp)] m m' -> wmono asegs m m' ->
u32arr asegs m' (fa_beg (ae_L RE) c + 4 * nf) (rev (map (coffw c) (carved nc (Z.to_nat newc)))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz newc) (wz endp) (wz (alloc + newc * class_size c)) a3v a4' a5' a6 a7
s2 (wz newc) s4 (wz (class_size c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x445d4) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz i) (wz endp) (wz off) a3v a4 a5 a6 a7
s2 (wz newc) s4 (wz (class_size c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x445b4) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until Q; intros -> HK Hi Hc Hnc Hnf HA HE FLO FHI AB MI HJ ARR CONT; [lia|].
pose proof (class_size_facts c ltac:(lia)) as [S1 S2]. hide S2.
assert (SR : 0 <= i * class_size c /\ i * class_size c + class_size c <= newc * class_size c) by (clear - Hi S1; nia).
pose proof (munch_refl [(fa_beg (ae_L RE) c + 4 * nf, endp)] m) as MU. pose proof (wmono_refl asegs m) as WM.

destruct (hjunk_split _ _ (endp - 4 * i - 4) _ HJ ltac:(lia)) as [HJ0 HJ1].
assert (HJ1' : hjunk m (endp - 4 * i - 4) (endp - 4 * i - 4 + Z.of_nat 4)) by (replace (endp - 4 * i - 4 + Z.of_nat 4) with (endp - 4 * i) by lia; exact HJ1).
destruct (hjunk_cells _ _ _ HJ1') as [junk SC]. clear HJ1 HJ1'.
step.
rewrite (unsigned_lit (alloc + i * class_size c)) by lia.
replace (Z.shiftr (alloc + i * class_size c) 4) with (coff c (nc + i)) by (rewrite HA; symmetry; apply coff_shift; lia).
step. step. step. step.
rewrite (not_sll2_add endp i) by lia. replace (endp - 4 * i - 4) with (endp - 4 * i - 4) by lia.
step.
step.
replace (alloc + i * class_size c + class_size c) with (alloc + (i + 1) * class_size c) by lia.
with_mem ltac:(fun mm =>
assert (ARR1 : u32arr asegs mm (endp - 4 * (i + 1)) (rev (map (coffw c) (carved nc (Z.to_nat (i + 1))))));
[ replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; rewrite carved_S, map_app, rev_app_distr; cbn [map rev app];
rewrite Z2Nat.id by lia; replace (endp - 4 * (i + 1)) with (endp - 4 * i - 4) by (first [ clear - HK newc endp c i k BAND; lia | lia ]);
apply u32arr_cons; [exact SC| replace (endp - 4 * i - 4 + 4) with (endp - 4 * i) by lia; exact ARR] |]).
clear SC ARR.
step.
destruct (Z.ltb_spec (i + 1) newc) as [MORE|DONE].
- ifz. eapply (IH (i + 1) ra sp gp tp t0 t1 t2 s0 s1 s2 a3v _ _ a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ c nc nf endp alloc newc _ Q);
[reflexivity| lia| lia| lia| lia| lia| exact HA| exact HE| lia| lia| lia| assumption| | exact ARR1|].
+ eapply hjunk_wmono; [| exact WM]. replace (endp - 4 * (i + 1)) with (endp - 4 * i - 4) by lia. exact HJ0.
+ intros m' a4' a5' MI' MU' WM' ARR'. apply (CONT m' a4' a5' MI'); [| | exact ARR'].
* eapply munch_trans; [exact MU| exact MU'].
* eapply wmono_trans; [exact WM| exact WM'].
- ifz. assert (E : i + 1 = newc) by lia. rewrite E in ARR1 |- *.
replace (endp - 4 * newc) with (fa_beg (ae_L RE) c + 4 * nf) in ARR1 by lia.
apply (CONT _ _ _ MI MU WM ARR1).
Qed.
End S.

Definition pop_rest_tree (AL : ALay) (s1 : AState) (c : Z) : T (bool * AState) :=
let x1 := cls s1 c in
let size := class_size c in
let new_chunks := (c_mapped_user x1 - c_alloc_user x1) / size in
let total_freed := c_num_freed x1 + new_chunks in
tbind (ensure_fa AL s1 c total_freed) (fun r =>
let '(ok2, s2) := r in
if negb ok2 then tret (false, s2)
else let x2 := cls s2 c in
tret (true, set_cls c (set_alloc_user (c_alloc_user x2 + new_chunks * size) (set_num_freed total_freed x2)) s2)).

Lemma efa_rel_true : forall aa c tf s2, efa_rel aa c tf (true, s2) ->
c_alloc_user (cls s2 c) = c_alloc_user (cls aa c) /\ c_mapped_user (cls s2 c) = c_mapped_user (cls aa c)
/\ c_num_freed (cls s2 c) = c_num_freed (cls aa c) /\ c_count (cls s2 c) = c_count (cls aa c)
/\ as_cache_inited s2 = as_cache_inited aa /\ 4 * tf <= c_mapped_fa (cls s2 c)
/\ (forall c', c' <> c -> cls s2 c' = cls aa c').
Proof.
intros aa c tf s2 [[E LE]|[(v & E & LE & _)|E]]; [| | discriminate]; apply (f_equal snd) in E; cbn [snd] in E; subst s2.
- repeat split; auto; lia.
- rewrite cls_set_cls_eq. cbn. repeat split; auto; try lia. intros c' Hc'. apply cls_set_cls_ne. exact Hc'.
Qed.

Section S3.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Lemma populate_C : forall x1 t0 t1 t2 x9 a1 a2 a4 a5 a6 a7 x19 x22 t3 t4 t5 t6 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
(F : bvmap 5 word) fc (m0 m : word -> option byte) (s : PStateA) (aa : AState) (G : ghost) (c lo v : Z),
let x := cls aa c in
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrimL aa G RE X m c v -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp + -64) -> band_lo <= lo -> lo <= bv_unsigned sp - POPULATE_STACK ->
munch (pop_W RE X (bv_unsigned sp) c (c_alloc_user x)) m0 m -> wmono asegs m0 m ->
rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
1 <= c <= 30 ->
aimplT atn (pop_rest_tree (ae_L RE) aa c) s
(fun r s' ms' => s' = s /\ pop_post RE X ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s G c (c_alloc_user x) lo m0 v r s' ms')
(MS (mkR x1 (wz (bv_unsigned sp + -64)) gp (wz A_TP) t0 t1 t2 (wz (ri_addr RE c)) x9 (wz A_INSTANCE) a1 a2 (wz (c_alloc_user x)) a4 a5 a6 a7
(wz (reg_beg (ae_L RE) c)) x19 (wz (c_mapped_user x)) (wz (class_size c)) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4456c) fc None m (seg_rom asegs)).
Proof.
intros until v; intros x RT RL RS RP MI ST CEIL LO MU WM FR Hc.
pose proof CEIL as CEIL'. idtac. unfold POPULATE_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq). hide PAL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK. encode_or TD. hide TA. hide TK.
pose proof (class_size_facts c ltac:(lia)) as [SZ1 SZ2]. hide SZ2.

destruct (RPrimL_open _ _ _ _ _ _ _ RP) as (K & HJS & GNE & HCall & _ & HC). apply class_repL_split in HC.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC0 & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & P12 & P13 & _ & _ & _ & G2 & G3 & G4 & G5). hide G5.
pose proof (cr_pure_div8 aa G c (K c) PU ltac:(lia)) as ((qa & QA0 & QA & QAE) & (qm & QM0 & QM) & E8). hide QAE.
subst x. cbv beta delta [ri_cellsL] in RI. cbv beta delta [pc_cells] in PC0. unfold ri_addr, pc_addr in *. unfold A_INSTANCE in *.
set (newc := (c_mapped_user (cls aa c) - c_alloc_user (cls aa c)) / class_size c).
assert (NEWC : 0 <= newc /\ newc * class_size c <= c_mapped_user (cls aa c) - c_alloc_user (cls aa c) < newc * class_size c + class_size c).
{ subst newc. clear - G3 SZ1. Z.div_mod_to_equations. nia. }
apply aimplT_from_evt.
step.
step.
step.
rewrite (unsigned_lit (c_mapped_user (cls aa c))), (unsigned_lit (c_alloc_user (cls aa c))) by lia.
rewrite divu_word by (first [ clear - G4 G3 G2 SZ1 KO c aa X RE; lia | lia ]). fold newc.
stp. step. step. step.
assert (NB : newc * 32 <= 3758096384) by (clear - NEWC SZ1 G2 G4 KO; clearbody newc; rewrite ?KO in G4; nia).
assert (SFB : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ unhide PAL. rewrite FB. unfold SH, A_SHADOW_OFS. unfold prim_hi, prim_lo in *. Z.div_mod_to_equations. (first [ clear - H29 q5 H16 H15 H5 H4 r0 q0 H0 H r q r2 G3 LCH CH K SZ1 PCH PK PAL r5 KM Hc c aa RE BAND; lia | lia ]). }
pose proof SH_band as SHBD0.
assert (SRB : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH (fa_beg (ae_L RE) c)).
{ unhide PAL. rewrite FB, RB. unfold SH, A_SHADOW_OFS. unfold prim_hi, prim_lo in *. Z.div_mod_to_equations. (first [ clear - H29 q5 H16 H15 H5 H4 r0 q0 H0 H r q r2 G3 LCH CH K SZ1 PK PAL r5 KM Hc c aa RE BAND; lia | lia ]). }
step.
clear RI PC0 ACH HCH REG HCall HJS GNE.
apply evt_done. unfold pop_rest_tree. rewrite ?KM, ?KO. fold newc.
eapply aimplT_bind.
{ eapply (ensure_fa_spec L RE X) with (v := v); try eassumption.
- rewrite unsigned_lit by lia. exact ST.
- rewrite unsigned_lit by lia. unfold ENSUREFA_STACK. lia.
- rewrite K32. lia.
- lia. }
intros [ok2 a2'] s' ms' POST. unfold efa_post in POST.
destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m1 & -> & -> & MU2 & WM2 & MI2 & ST2 & RT2 & RS2 & RP2 & A0 & REL).
cbn [fst snd] in A0, RP2. subst ra0.
rewrite !(unsigned_lit (bv_unsigned sp + -64)) in * by (first [ clear - SPR CEIL' LO lo c aa sp X RE BAND; lia | lia ]).
replace (ret_pc (wz 279948)) with (wz 279948) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold efa_W, ENSUREFA_STACK, ri_addr in MU2. rewrite ?KS in MU2. change (536870912 / 8) with 67108864 in MU2.
hide MU. transport_after_call asegs m m1 MU2 WM2. unhide MU.
unfold pop_W, POPULATE_STACK, ri_addr in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
assert (MU' : munch _ m0 m1) by (eapply munch_chain; [exact MU| exact MU2| sub_fp_solve]).
clear MU MU2 WM2 MI RT RS RP; rename MU' into MU. rename MI2 into MI; rename RT2 into RT; rename RS2 into RS; rename ST2 into ST.
destruct ok2; cbn [negb].
2:{
apply aimplT_ret.
step. if_lit.
step. step.
step. do 8 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. split; [reflexivity|].
unfold pop_post. do 16 eexists. exists 0%nat. split; [reflexivity|]. split; [reflexivity|].
split. { unfold pop_W, POPULATE_STACK, ri_addr. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact RT|]. split; [exact RS|]. split; [| reflexivity].
cbn [snd repeat]. apply RPrimL_gappend_nil. exact RP2. }

rename a2' into a2s. destruct (efa_rel_true _ _ _ _ REL) as (EA & EM & EN & EC & EI & LE4 & EO).

destruct (RPrimL_open _ _ _ _ _ _ _ RP2) as (K2 & HJS & GNE & HCall & _ & HC). apply class_repL_split in HC.
destruct HC as (((k1 & k2 & k3 & k4 & RI) & PC0 & (CH2 & ACH & LCH2 & HCH2)) & PU2 & REG).
specialize (REG ltac:(lia)). destruct REG as (FA & FJ & HU & FS).
apply cr_user_split in HU. destruct HU as (HSL & UT & US & UJ).
rewrite ?KS, ?KM, ?KO, ?EA, ?EM, ?EN, ?EC, ?EI in *.
pose proof PU2 as (Q1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q11 & Q12 & Q13 & Q14 & _ & _ & _ & _ & _ & _). rewrite ?EN in Q1, Q11, Q12. hide Q14.
assert (LFA : Z.of_nat (length (map (fun i : Z => wz (coff c i)) (pk_fl (K2 c)))) = c_num_freed (cls aa c)) by (rewrite length_map; exact Q1).
cbv beta delta [ri_cellsL] in RI. cbv beta delta [pc_cells] in PC0. unfold ri_addr, pc_addr in RI, PC0, ACH.
rewrite EA, EM, EN in RI. rewrite EC in PC0.
rewrite QA in US. rewrite SH_plus8 in US. rewrite QM in UJ at 1. replace 3758096384 with (8 * 469762048) in UJ by reflexivity. rewrite !SH_plus8 in UJ.
assert (KS8 : 536870912 = 8 * 67108864) by reflexivity. rewrite KS8, SH_plus8 in FS.
pose proof (munch_refl [(bv_unsigned sp - 512, bv_unsigned sp); (rl_T X + 2768, rl_T X + 3168);
(region_info RE + 128 * c, region_info RE + 128 * c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + 536870912);
(SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + 67108864);
(reg_beg (ae_L RE) c + 8 * qa, reg_beg (ae_L RE) c + 3758096384);
(SH (reg_beg (ae_L RE) c) + qa, SH (reg_beg (ae_L RE) c) + 469762048)] m1) as MUm.
pose proof (wmono_refl asegs m1) as WMm.
lazymatch type of MUm with munch ?W _ _ =>
assert (FWrt : Forall (rt_avoid RE X) W);
[| assert (FWst : Forall st_avoid W); [| assert (FWc : Forall (wc_ok RE X c) W)]] end.
{ constructor; [apply rt_avoid_stack; [exact RL| (first [ clear - a2s qa PK CEIL' LO lo c aa sp X RE BAND; lia | lia ])]|].
constructor; [apply rt_avoid_Thigh; [exact RL| (first [ clear - a2s qa c aa X RE BAND; lia | lia ])| (first [ clear - a2s qa c aa X RE BAND; lia | lia ])]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; (first [ clear - a2s qa RIq PK Hc c aa X RE BAND; lia | lia ])| unfold prim_hi, prim_lo in *; (first [ clear - a2s qa RIq PK Hc c aa X RE BAND; lia | lia ])]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; (first [ clear - a2s qa PK FB Hc c aa X RE BAND; lia | lia ])| unfold prim_hi, prim_lo in *; (first [ clear - a2s qa PK FB Hc c aa X RE BAND; lia | lia ])]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; (first [ clear - a2s SFB qa c aa X RE BAND; lia | lia ])| rewrite ?KHI_eq; (first [ clear - a2s SHBD0 SFB qa c aa X RE BAND; lia | lia ])]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; (first [ clear - a2s QM qm QA qa G3 G2 SZ1 PK RB Hc c aa X RE BAND; lia | lia ])| unfold prim_hi, prim_lo in *; (first [ clear - a2s qa PK RB Hc c aa X RE BAND; lia | lia ])]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; (first [ clear - a2s SRB QA qa G3 G2 SZ1 c aa X RE BAND; lia | lia ])| rewrite ?KHI_eq; (first [ clear - a2s SRB SHBD0 SFB qa c aa X RE BAND; lia | lia ])]| constructor]. }
{ repeat (constructor; [st_avoid_solve|]). constructor. }
{ constructor; [cbn; left; (first [ clear - a2s qa PK CEIL' LO lo c aa sp X RE BAND; lia | lia ])|]. constructor; [cbn; right; left; (first [ clear - a2s qa c aa X RE BAND; lia | lia ])|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; left; unfold ri_addr; exact Hz|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; do 2 right; left; rewrite KS; exact Hz|].
constructor; [cbn -[fp_cls SH Z.div]; do 2 right; intros z Hz; do 3 right; left; split; cbn [fst snd]; rewrite ?KS; [(first [ clear - Hz z a2s qa c aa X RE BAND; lia | lia ])| change (536870912 / 8) with 67108864; (first [ clear - Hz z a2s qa c aa X RE BAND; lia | lia ])]|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; do 4 right; left; rewrite KO; (first [ clear - Hz z a2s NEWC newc QA qa G3 G2 PK c aa X RE BAND; lia | lia ])|].
constructor; [| constructor]. cbn -[fp_cls SH Z.div]; do 2 right; intros z Hz; do 5 right; split; cbn [fst snd]; rewrite ?KO; [(first [ clear - Hz z a2s NEWC newc QA qa G3 G2 c aa X RE BAND; lia | lia ])| change (3758096384 / 8) with 469762048; (first [ clear - Hz z a2s qa c aa X RE BAND; lia | lia ])]. }
apply aimplT_ret.
step. ifz.
step.
step.
set (nc := ncarved G c) in *.
assert (NC0 : 0 <= nc) by (subst nc; unfold ncarved; lia).

lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists (v9 v0 v1 v2 v4 v5 : word) m',
ms2 = MS (@bvmap_set 5 word 9 v9 (@bvmap_set 5 word 10 v0 (@bvmap_set 5 word 11 v1 (@bvmap_set 5 word 12 v2 (@bvmap_set 5 word 14 v4 (@bvmap_set 5 word 15 v5 R))))))
FF (wz 0x445d4) fcc rv m' ro
/\ munch [(fa_beg (ae_L RE) c + 4 * c_num_freed (cls aa c), fa_beg (ae_L RE) c + 4 * (c_num_freed (cls aa c) + newc))] mm m'
/\ wmono asegs mm m' /\ mem_inv asegs m'
/\ u32arr asegs m' (fa_beg (ae_L RE) c + 4 * c_num_freed (cls aa c)) (rev (map (coffw c) (carved nc (Z.to_nat newc))))))
end.
{ destruct (Z.ltb_spec (c_mapped_user (cls aa c) - c_alloc_user (cls aa c)) (class_size c)) as [NO|GO].
- ifz. assert (NZ : newc = 0) by (subst newc; apply Z.div_small; (first [ clear - NO K2 a2s qa G3 K c G aa X RE; lia | lia ])).
apply evt_done. do 7 eexists. split; [simp_regs; reflexivity|].
split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [assumption|].
rewrite NZ. cbn. apply u32arr_nil. (first [ clear - LFA Q13 Q12 K2 a2s qa G3 K SZ1 PH PCH PK FB KS Hc c G aa X RE BAND; lia | lia ]).
- ifz. assert (NZ : 1 <= newc) by (subst newc; apply Z.div_le_lower_bound; (first [ clear - K2 a2s qa K SZ1 c G aa X RE GO; lia | lia ])).
step. step. step. step. stp. step. step.
rewrite (unsigned_lit (c_num_freed (cls aa c) + newc)) by (first [ clear - NZ LFA K2 LE4 a2s NB NEWC newc QM qm QA qa G3 G2 P13 P12 K SZ1 c G aa X RE; lia | lia ]). rewrite Z.shiftl_mul_pow2 by (first [ clear - K2 a2s qa K c G aa X RE; lia | lia ]). change (2^2) with 4.
replace (reg_beg (ae_L RE) c + 3758096384 + (c_num_freed (cls aa c) + newc) * 4) with (fa_beg (ae_L RE) c + 4 * (c_num_freed (cls aa c) + newc)) by (rewrite FB, RB; lia).
rewrite KS in Q13.
destruct (hjunk_split _ _ (fa_beg (ae_L RE) c + 4 * (c_num_freed (cls aa c) + newc)) _ FJ ltac:((first [ clear - NZ K2 LE4 a2s newc qa G3 K SZ1 PK c G aa X RE BAND; lia | lia ]))) as [FJa FJb].
eapply (carve_loop RE (Z.to_nat newc) 0) with (nc := nc) (nf := c_num_freed (cls aa c)) (alloc := c_alloc_user (cls aa c)).
+ (first [ clear - K2 a2s qa K c G aa X RE; lia | lia ]). + (first [ clear - NZ LFA K2 LE4 a2s NEWC newc QM qm QA qa G3 G2 K SZ1 c G aa X RE; lia | lia ]). + (first [ clear - NZ K2 a2s newc qa K c G aa X RE; lia | lia ]). + (first [ clear - a2s qa Hc c G aa X RE BAND; lia | lia ]). + exact NC0. + (first [ clear - K2 a2s qa P11 K c G aa X RE; lia | lia ]). + unhide QAE. subst nc. rewrite QA, QAE. clear - E8. nia.
+ reflexivity. + rewrite FB. (first [ clear - a2s qa PK Hc c G aa X RE BAND; lia | lia ]). + rewrite FB. unfold prim_hi, prim_lo in *. (first [ clear - Q13 K2 LE4 a2s newc qa G3 K SZ1 PCH PK Hc c G aa X RE BAND; lia | lia ]).
+ rewrite ?KO in G4. clear - NEWC G4. lia.
+ assumption.
+ replace (fa_beg (ae_L RE) c + 4 * (c_num_freed (cls aa c) + newc) - 4 * 0) with (fa_beg (ae_L RE) c + 4 * (c_num_freed (cls aa c) + newc)) by (first [ clear - K2 a2s newc qa K c G aa X RE BAND; lia | lia ]). exact FJa.
+ cbn. replace (fa_beg (ae_L RE) c + 4 * (c_num_freed (cls aa c) + newc) - 4 * 0) with (fa_beg (ae_L RE) c + 4 * (c_num_freed (cls aa c) + newc)) by (first [ clear - K2 a2s newc qa K c G aa X RE BAND; lia | lia ]). apply u32arr_nil. rewrite FB. (first [ clear - NZ LFA K2 LE4 a2s NB newc qa G3 P13 P12 K SZ1 PH PCH PK Hc c G aa X RE BAND; lia | lia ]).
+ intros m' a4' a5' MI' MU' WM' ARR'. apply evt_done. do 7 eexists. split; [simp_regs; reflexivity|].
split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. exact ARR'. }
intros ms2 (v9 & v0 & v1 & v2 & v4 & v5 & m2 & -> & MU3 & WM3 & MI3 & ARR). simp_regs.
assert (LARR : Z.of_nat (length (rev (map (coffw c) (carved nc (Z.to_nat newc))))) = newc) by (rewrite length_rev, length_map, carved_length; (first [ clear - LFA K2 LE4 a2s NEWC newc E8 QM qm QA qa G3 G2 K SZ1 c G aa X RE; lia | lia ])).

hide MU. hide MUm. transport_after_call asegs m1 m2 MU3 WM3. unhide MU. unhide MUm.
assert (MU' : munch _ m0 m2) by (eapply munch_chain; [exact MU| exact MU3| sub_fp_solve]).
assert (MUm' : munch _ m1 m2) by (eapply munch_chain; [exact MUm| exact MU3| sub_fp_solve]).
clear MU MUm MU3 WM3 MI; rename MU' into MU; rename MUm' into MUm; rename MI3 into MI.
step.
step.
rewrite (unsigned_lit newc), (unsigned_lit (class_size c)) by (first [ clear - K2 a2s NEWC newc nc qa G4 G3 G2 K SZ1 c G aa X RE; lia | lia ]).
step.
step. step.
step. step.
step. unfold_cond; cond_unsig; if_false.
step. step. step. if_lit.
stf.
step. step. do 8 step. step. step.
release_frame FR ST (bv_unsigned sp).
change (b8 (bv_unsigned (wz 0))) with (b8 0) in RI.
apply evt_done. split; [reflexivity|].
pose proof (RTconst_munch _ _ _ _ _ RT MUm WMm FWrt) as RT'. pose proof (RStats_munch _ _ _ _ _ RS MUm WMm FWst) as RS'.
epose proof (agree_other_classes _ _ _ _ _ _ RL _ MUm WMm FWc) as OTH. Unshelve. 2:{ lia. }
lazymatch goal with |- pop_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?m3 _) =>
assert (AGS : agree_on asegs (szone RE c (c_alloc_user (cls aa c))) m1 m3) end.
{ eapply agree_on_of_munch; [exact MUm| exact WMm|]. intros z Uz Hz. unfold szone in Uz. rewrite QA in Uz.
rewrite (Z.mul_comm 8 qa), Z.div_mul in Uz by (first [ clear - K2 a2s nc qa K newc c G aa X RE BAND; lia | lia ]). cbn [outside]. clear - Uz Hz QA0 SRB SFB CEIL LO RB FB PK PCH PH RIq TK TB TD G2 G3 G4 QA Hc. unhide TK. (first [ clear - Uz z SRB SFB QA qa G4 G3 G2 TD TK RIq PH PCH PK FB RB Hc LO CEIL lo c aa sp X RE BAND; lia | lia ]). }
unfold pop_post. do 16 eexists. exists (Z.to_nat newc). split; [reflexivity|]. split; [reflexivity|].
split. { unfold pop_W, POPULATE_STACK, ri_addr. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact RT'|]. split; [exact RS'|]. split; [| reflexivity].
cbn [snd]. unhide QAE.
eapply (populate_close aa a2s G RE X m1 _ c K2 k1 k2 k3 k4 CH2 qa qm newc v); try eassumption; try (first [ clear - K2 a2s NEWC nc qa K newc c G aa X RE; lia | lia ]).
Qed.
End S3.
