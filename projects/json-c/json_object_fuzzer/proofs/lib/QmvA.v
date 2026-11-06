(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig QwAs Q6sh QKTr QJBH QvG1 QyW2 QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QUnM QpME QFd5 QlES Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq1 QNQk.Mq4.
Import QUnM QpME.Mq0 QFd5.Mq2.
Import QlES.
Import ListNotations. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_2 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition intalloc_entry : Z := 0x6f35c.
Definition INTALLOC_STACK : Z := 48.

Definition ia_W (sp : Z) : list (Z * Z) :=
[ (sp - INTALLOC_STACK, sp); (IA_FLAG, IA_FLAG + 4); (IA, IA + 8); (IA_MAP1, IA_MAP1 + 0x40000); (0x0130d40, 0x171d30) ].

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma ia_W_rt : forall sp, band_lo <= sp - INTALLOC_STACK -> rlay_ok RE X -> Forall (rt_avoid RE X) (ia_W sp).
Proof.
intros sp Hsp RL. unfold ia_W, IA_FLAG, IA, IA_MAP1.
assert (IMG : forall lo hi, 0x0f0d00 <= lo -> hi <= 0x17f58c -> (hi <= 0x171d61 \/ 0x17f588 <= lo) -> rt_avoid RE X (lo, hi)).
{ intros lo hi H1 H2 H3 x [Hx1 Hx2] Fx. cbn [fst snd] in Hx1, Hx2.
destruct (fp_RTconst_where RE X x Fx) as [L|(o & Ho & [O1 O2])].
- destruct Fx as [Fi|[Fo|[Fo|Fo]]].
+ destruct Fi as (iv & Hin & [I1 I2]). unfold rtconst_img in Hin. cbn in Hin.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in I1, I2; unfold A_INSTANCE, A_TLS_TSD, A_TSD_MAIN, A_TP in *; lia|]). destruct Hin.
+ pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & K & _). destruct Fo as [Fo1 Fo2]. cbn [fst snd] in K, Fo1, Fo2. rewrite ?KHI_eq in K. lia.
+ pose proof (rlay_obj_facts RE X _ RL (ctx_obj RE X)) as (_ & K & _). destruct Fo as [Fo1 Fo2]. cbn [fst snd] in K, Fo1, Fo2. rewrite ?KHI_eq in K. lia.
+ pose proof (rlay_obj_facts RE X _ RL (dtls_obj RE X)) as (_ & K & _). destruct Fo as [Fo1 Fo2]. cbn [fst snd] in K, Fo1, Fo2. rewrite ?KHI_eq in K. lia.
- pose proof (rlay_obj_facts RE X o RL Ho) as (_ & K & _). rewrite ?KHI_eq in K. lia. }
constructor; [apply rt_avoid_stack; [exact RL| exact Hsp]|].
constructor; [apply IMG; lia|]. constructor; [apply IMG; lia|]. constructor; [apply IMG; lia|]. constructor; [apply IMG; lia| constructor].
Qed.

Lemma intalloc_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> ia_inv m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - INTALLOC_STACK ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (ia_W (bv_unsigned sp)) lo m
(fun a0' m' => a0' = wz IA /\ RTconst RE X m' /\ ia_inv m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz intalloc_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL IAI MI ST CEIL LO. pose proof CEIL as CEIL'. idtac. unfold INTALLOC_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl (ia_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold ia_W, INTALLOC_STACK, IA_FLAG, IA, IA_MAP1 in MU.
assert (FWrt : Forall (rt_avoid RE X) (ia_W (bv_unsigned sp))) by (apply ia_W_rt; [unfold INTALLOC_STACK; lia| exact RL]).
destruct IAI as (b0 & FL & B01 & ZMAP & ZR).
unfold intalloc_entry, IA_FLAG, IA, IA_MAP1 in *.
destruct B01 as [-> | ->].
2:{
carve_frame 48%nat ST.
do 6 step. step. step.
stp. step. step. if_lit.
step. step. do 5 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity|].
split; [eapply RTconst_munch; [exact RT| exact MU| exact WM| exact FWrt]|].
exists 1. split; [exact FL|]. split; [right; reflexivity|]. split; [| left; reflexivity].
exact ZMAP. }

destruct ZR as [ZR|(ZIA & Z3 & Z4 & Z5)]; [discriminate|].
rtc RT 18%nat K18. rtc RT 8%nat K8.
carve_frame 48%nat ST.
do 6 step. step. step.
stp. step. step. if_lit.
do 8 step. fold_swrap.
recast FL [C4 (wz 0)].
amo_step (amo_aligned_intro4 1570184 ltac:(lia) ltac:(reflexivity)).
do 4 step. lits.
amo_step (amo_aligned_intro4 1570184 ltac:(lia) ltac:(reflexivity)).
step. if_lit.
step. step. fold_swrap. lits. step. if_lit.
recast FL [C1 (b8 0); C1 (b8 1); C1 (b8 0); C1 (b8 0)].
stp. step. if_lit.
do 7 step. lits.

step. call_zb (imemset_spec) ltac:(fun PO => idtac); try eassumption; try lia; try (first [left; vm_compute; lia | right; vm_compute; lia]).
clear POST.

match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (zbytes_store_ok_at mc _ _ 986368 1 ZIA ltac:(lia) ltac:(cbn; lia)) as SOK end.
step. zstore ZIA SOK.

do 4 step. lits.
step. call_zb (imemset_spec) ltac:(fun PO => idtac); try eassumption; try lia; try (first [left; vm_compute; lia | right; vm_compute; lia]).
rename POST into ZMAP.

do 5 step. lits.
step. call_zb (imemset_spec) ltac:(fun PO => idtac); try eassumption; try lia; try (first [left; vm_compute; lia | right; vm_compute; lia]).
clear POST.

do 5 step. lits.
step. call_zb (imemset_spec) ltac:(fun PO => idtac); try eassumption; try lia; try (first [left; vm_compute; lia | right; vm_compute; lia]).
rename POST into Z4.

step. step. step. step. if_lit.
do 4 step. lits.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (zbytes_cells_C8x2 mc _ _ 1252032 Z4 ltac:(lia) ltac:(lia)) as PG end.
stf. stf.
step. stp.
step. stp.
step. step.
do 5 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity|].
split; [eapply RTconst_munch; [exact RT| exact MU| exact WM| exact FWrt]|].
exists 1. split; [exact FL|]. split; [right; reflexivity|]. split; [exact ZMAP| left; reflexivity].
Qed.
End S.
End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I QJFf QBrp QDM6 QVsB Qsn5 QCiC QQwg Qp4j QUxU QTVW QmP7 QYyZ QkfD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QNQk.Mq1 QTVW.Mq0 QmP7.Mq0 QYyZ.Mq0.
Import QkfD.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Definition large_alloc_entry : Z := 0x43b78.

Definition LARGE_STACK : Z := 800.

Definition W_large (sp : Z) (RE : aentry) (X : rlay) : list (Z * Z) :=
[ (sp - LARGE_STACK, sp); (A_INSTANCE + 104, A_INSTANCE + 728);
(ptrarr_lo RE, ptrarr_lo RE + 0x800000); (rl_T X + 2800, rl_T X + 3168) ].

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Definition large_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (LB : list ablock) (lo n : Z) (m : mem)
(r : option Z * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1r a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1r a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ wmono asegs m m'
/\ RTconst RE X m' /\ RStats RE X m'
/\ match r with
| (None, a1) =>
a0 = wz 0 /\ a1 = a
/\ munch (W_large (bv_unsigned sp) RE X) m m'
/\ RSec a LB RE X m'
| (Some mb, a1) =>
let msz := sec_map_size n in
let sz := sec_size n in
a0 = wz (mb + kPage)

/\ as_reg a1 = as_reg a ++ [mkSec mb msz n]
/\ as_tq a1 = as_tq a /\ as_gq a1 = as_gq a /\ (forall c, cls a1 c = cls a c)
/\ as_cache_inited a1 = as_cache_inited a /\ as_next a1 = as_next a
/\ (as_nres a1 = as_nres a \/ as_nres a1 = as_nres a + kPtrArrBlock)
/\ as_spent a1 = as_spent a + sec_cost msz

/\ mb mod kPage = 0 /\ appr mb msz /\ mb + msz <= band_lo
/\ zavoids mb msz (avoid_of (ae_L RE) a) = true

/\ munch (W_large (bv_unsigned sp) RE X ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m m'
/\ RSec a1 LB RE X m'
/\ rw_cells asegs m' (mb + kPage) [CB (Z.to_nat (msz - kPage)) (repeat (b8 0) (Z.to_nat (msz - kPage)))]
/\ hjunk m' (SH (mb + kPage)) (SH (mb + kPage + sz))
/\ rw_cells asegs m' (SH (mb + kPage + sz)) [CB (Z.to_nat ((msz - kPage - sz) / 8)) (fas ((msz - kPage - sz) / 8))]
end.

Definition large_alloc_stmt (L : lvp) : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PStateA)
(a : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (n lo : Z),
gcons a LB FS G RE X -> avoid_covers RE X ->
RTconst RE X m -> RStats RE X m -> RSec a LB RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - LARGE_STACK ->
0 <= n <= 2^26 -> from_primary n = false ->
aimplT (at_nodeA L asegs) (large_alloc (ae_L RE) a n) s
(large_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB lo n m)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz (A_INSTANCE + 64)) (wz (A_INSTANCE + 688)) (wz (sec_size n)) (wz 8) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz large_alloc_entry) fc None m (seg_rom asegs)).
End S.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2 QOJv Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC QKTr Q6sh QQwg.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QpME.Mq0 QTVW.Mq0 QNQk.Mq4 QOJv.Mq3 QOJv.Mq4 QTVW.Mq3 Qu3b.Mq2.
Import QpME.Mq6.
Import QFd5.Mq3.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Definition sysconf_entry : Z := 0xcba68.
Definition gmg_entry : Z := 0x76e30.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Lemma rw_cells_CB0 : forall m A l, rw_cells asegs m A [CB 0 l] -> rw_cells asegs m A [CB 0 []].
Proof. intros m A l H. destruct l as [|x l]; [exact H|]. destruct H as [[[LL _] _] _]. cbn in LL. discriminate. Qed.

Lemma poison_zero_spec : poison_zero_stmt RE X L.
Proof.
unfold poison_zero_stmt. intros until junk; intros RT RL MI ST CEIL LO AAL SAL S0 AK AH SHD.
pose proof CEIL as CEIL'. idtac. pose proof AK as AK'. rewrite ?KHI_eq in AK. change (2^47) with 140737488355328 in AH.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold PZ_STACK in LO.
assert (SHa : SH addr = addr / 8 + 0x7fff8000) by reflexivity.
unfold clear_shadow, remap_range. unfold kClearShadowMmapThreshold, shadow_of, kShadowOffset, round_up, round_down, kPage.
destruct (Z.ltb_spec0 (size / 8) 18446744073709551615) as [SMALL|BIG].
{
apply aimplT_ret. eapply evt_mono.
{ eapply (poison_shadow_spec RE X); [exact RT| exact RL| exact MI| exact ST| exact CEIL'| lia| exact AAL| exact SAL| exact S0| exact AK'
| change (2^47) with 140737488355328; lia| lia| right; exact SMALL| exact SHD]. }
cbv beta. intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & RT' & Z').
unfold pz_post, PZ_STACK. do 16 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact RT'|]. exact Z'. }

exfalso. apply BIG. clear - AK AH S0. Z.div_mod_to_equations; lia.
Qed.

End S.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QNQk.Mq1 QTVW.Mq0.
Import QUnM.
Import QYyZ.Mq5.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).

Definition recycle_entry : Z := 0x40fb8.

Definition QOBJ : Z := A_INSTANCE + 728.

Definition RECYCLE_STACK : Z := 1024.

Section S.
Context {BAND : Band}.
Variables (C : arun_components) (RE : aentry) (X : rlay).

Definition qret_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (LB0 : list ablock) (FS0 : list fframe) (lo : Z) (m : word -> option byte)
(DR : (word -> option byte) -> (word -> option byte) -> Prop)
(a1 : AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1r a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' G',
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1r a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ aheap_presA asegs a_alayout LB0 FS0 (bv_unsigned sp) m m'
/\ DR m m'
/\ QRUN C 0 QB QB [] a1 LB0 FS0 G' RE X m'.

Definition recycle_stmt (L : lvp) : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s : PStateA)
(a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (lo : Z),
QRUN C 1 QB (4 * QB) [] a LB0 FS0 G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - RECYCLE_STACK ->
aimplT (at_nodeA L asegs) (recycle (ae_L RE) a) s
(qret_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 FS0 lo m (free_keep asegs))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz QOBJ) (wz kQMinSize) (wz (rl_T X + 208)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz recycle_entry) fc None m (seg_rom asegs)).
End S.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QbcP_c1 QWRO QFQR QKBN QN4c QXcn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq6 QNQk.Mq8.
Import QXcn QpME.Mq7 QFd5.Mq6.
Import QlES.
Import ListNotations. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_2 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition intalloc_entry : Z := 0x6f734.
Definition INTALLOC_STACK : Z := 48.

Definition ia_W (sp : Z) : list (Z * Z) :=
[ (sp - INTALLOC_STACK, sp); (IA_FLAG, IA_FLAG + 4); (IA, IA + 8); (IA_MAP1, IA_MAP1 + 0x40000); (0x0133400, 0x1743f0) ].

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma ia_W_rt : forall sp, band_lo <= sp - INTALLOC_STACK -> rlay_ok RE X -> Forall (rt_avoid RE X) (ia_W sp).
Proof.
intros sp Hsp RL. unfold ia_W, IA_FLAG, IA, IA_MAP1.
assert (IMG : forall lo hi, 0x0f33c0 <= lo -> hi <= 0x181c4c -> (hi <= 0x174421 \/ 0x181c48 <= lo) -> rt_avoid RE X (lo, hi)).
{ intros lo hi H1 H2 H3 x [Hx1 Hx2] Fx. cbn [fst snd] in Hx1, Hx2.
destruct (fp_RTconst_where RE X x Fx) as [L|(o & Ho & [O1 O2])].
- destruct Fx as [Fi|[Fo|[Fo|Fo]]].
+ destruct Fi as (iv & Hin & [I1 I2]). unfold rtconst_img in Hin. cbn in Hin.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in I1, I2; unfold A_INSTANCE, A_TLS_TSD, A_TSD_MAIN, A_TP in *; lia|]). destruct Hin.
+ pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & K & _). destruct Fo as [Fo1 Fo2]. cbn [fst snd] in K, Fo1, Fo2. rewrite ?KHI_eq in K. lia.
+ pose proof (rlay_obj_facts RE X _ RL (ctx_obj RE X)) as (_ & K & _). destruct Fo as [Fo1 Fo2]. cbn [fst snd] in K, Fo1, Fo2. rewrite ?KHI_eq in K. lia.
+ pose proof (rlay_obj_facts RE X _ RL (dtls_obj RE X)) as (_ & K & _). destruct Fo as [Fo1 Fo2]. cbn [fst snd] in K, Fo1, Fo2. rewrite ?KHI_eq in K. lia.
- pose proof (rlay_obj_facts RE X o RL Ho) as (_ & K & _). rewrite ?KHI_eq in K. lia. }
constructor; [apply rt_avoid_stack; [exact RL| exact Hsp]|].
constructor; [apply IMG; lia|]. constructor; [apply IMG; lia|]. constructor; [apply IMG; lia|]. constructor; [apply IMG; lia| constructor].
Qed.

Lemma intalloc_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> ia_inv m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - INTALLOC_STACK ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (ia_W (bv_unsigned sp)) lo m
(fun a0' m' => a0' = wz IA /\ RTconst RE X m' /\ ia_inv m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz intalloc_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL IAI MI ST CEIL LO. pose proof CEIL as CEIL'. idtac. unfold INTALLOC_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl (ia_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold ia_W, INTALLOC_STACK, IA_FLAG, IA, IA_MAP1 in MU.
assert (FWrt : Forall (rt_avoid RE X) (ia_W (bv_unsigned sp))) by (apply ia_W_rt; [unfold INTALLOC_STACK; lia| exact RL]).
destruct IAI as (b0 & FL & B01 & ZMAP & ZR).
unfold intalloc_entry, IA_FLAG, IA, IA_MAP1 in *.
destruct B01 as [-> | ->].
2:{
carve_frame 48%nat ST.
do 6 step. step. step.
stp. step. step. if_lit.
step. step. do 5 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity|].
split; [eapply RTconst_munch; [exact RT| exact MU| exact WM| exact FWrt]|].
exists 1. split; [exact FL|]. split; [right; reflexivity|]. split; [| left; reflexivity].
exact ZMAP. }

destruct ZR as [ZR|(ZIA & Z3 & Z4 & Z5)]; [discriminate|].
rtc RT 18%nat K18. rtc RT 8%nat K8.
carve_frame 48%nat ST.
do 6 step. step. step.
stp. step. step. if_lit.
do 8 step. fold_swrap.
recast FL [C4 (wz 0)].
amo_step (amo_aligned_intro4 1580104 ltac:(lia) ltac:(reflexivity)).
do 4 step. lits.
amo_step (amo_aligned_intro4 1580104 ltac:(lia) ltac:(reflexivity)).
step. if_lit.
step. step. fold_swrap. lits. step. if_lit.
recast FL [C1 (b8 0); C1 (b8 1); C1 (b8 0); C1 (b8 0)].
stp. step. if_lit.
do 7 step. lits.

step. call_zb (imemset_spec) ltac:(fun PO => idtac); try eassumption; try lia; try (first [left; vm_compute; lia | right; vm_compute; lia]).
clear POST.

match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (zbytes_store_ok_at mc _ _ 996288 1 ZIA ltac:(lia) ltac:(cbn; lia)) as SOK end.
step. zstore ZIA SOK.

do 4 step. lits.
step. call_zb (imemset_spec) ltac:(fun PO => idtac); try eassumption; try lia; try (first [left; vm_compute; lia | right; vm_compute; lia]).
rename POST into ZMAP.

do 5 step. lits.
step. call_zb (imemset_spec) ltac:(fun PO => idtac); try eassumption; try lia; try (first [left; vm_compute; lia | right; vm_compute; lia]).
clear POST.

do 5 step. lits.
step. call_zb (imemset_spec) ltac:(fun PO => idtac); try eassumption; try lia; try (first [left; vm_compute; lia | right; vm_compute; lia]).
rename POST into Z4.

step. step. step. step. if_lit.
do 4 step. lits.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (zbytes_cells_C8x2 mc _ _ 1261952 Z4 ltac:(lia) ltac:(lia)) as PG end.
stf. stf.
step. stp.
step. stp.
step. step.
do 5 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity|].
split; [eapply RTconst_munch; [exact RT| exact MU| exact WM| exact FWrt]|].
exists 1. split; [exact FL|]. split; [right; reflexivity|]. split; [exact ZMAP| left; reflexivity].
Qed.
End S.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C Qu4g QjgW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QNQk.Mq6 QTVW.Mq7 QmP7.Mq1 QYyZ.Mq8.
Import QjgW.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Definition large_alloc_entry : Z := 0x43da4.

Definition LARGE_STACK : Z := 800.

Definition W_large (sp : Z) (RE : aentry) (X : rlay) : list (Z * Z) :=
[ (sp - LARGE_STACK, sp); (A_INSTANCE + 104, A_INSTANCE + 728);
(ptrarr_lo RE, ptrarr_lo RE + 0x800000); (rl_T X + 2800, rl_T X + 3168) ].

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Definition large_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (LB : list ablock) (lo n : Z) (m : mem)
(r : option Z * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1r a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1r a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ wmono asegs m m'
/\ RTconst RE X m' /\ RStats RE X m'
/\ match r with
| (None, a1) =>
a0 = wz 0 /\ a1 = a
/\ munch (W_large (bv_unsigned sp) RE X) m m'
/\ RSec a LB RE X m'
| (Some mb, a1) =>
let msz := sec_map_size n in
let sz := sec_size n in
a0 = wz (mb + kPage)

/\ as_reg a1 = as_reg a ++ [mkSec mb msz n]
/\ as_tq a1 = as_tq a /\ as_gq a1 = as_gq a /\ (forall c, cls a1 c = cls a c)
/\ as_cache_inited a1 = as_cache_inited a /\ as_next a1 = as_next a
/\ (as_nres a1 = as_nres a \/ as_nres a1 = as_nres a + kPtrArrBlock)
/\ as_spent a1 = as_spent a + sec_cost msz

/\ mb mod kPage = 0 /\ appr mb msz /\ mb + msz <= band_lo
/\ zavoids mb msz (avoid_of (ae_L RE) a) = true

/\ munch (W_large (bv_unsigned sp) RE X ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m m'
/\ RSec a1 LB RE X m'
/\ rw_cells asegs m' (mb + kPage) [CB (Z.to_nat (msz - kPage)) (repeat (b8 0) (Z.to_nat (msz - kPage)))]
/\ hjunk m' (SH (mb + kPage)) (SH (mb + kPage + sz))
/\ rw_cells asegs m' (SH (mb + kPage + sz)) [CB (Z.to_nat ((msz - kPage - sz) / 8)) (fas ((msz - kPage - sz) / 8))]
end.

Definition large_alloc_stmt (L : lvp) : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PStateA)
(a : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (n lo : Z),
gcons a LB FS G RE X -> avoid_covers RE X ->
RTconst RE X m -> RStats RE X m -> RSec a LB RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - LARGE_STACK ->
0 <= n <= 2^26 -> from_primary n = false ->
aimplT (at_nodeA L asegs) (large_alloc (ae_L RE) a n) s
(large_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB lo n m)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz (A_INSTANCE + 64)) (wz (A_INSTANCE + 688)) (wz (sec_size n)) (wz 8) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz large_alloc_entry) fc None m (seg_rom asegs)).
End S.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC QKTr Q6sh QQwg.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QpME.Mq7 QTVW.Mq7 QNQk.Mq8 QOJv.Mqa QOJv.Mqb QTVW.Mqa Qu3b.
Import QpME.Mqc.
Import QFd5.Mq7.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Definition sysconf_entry : Z := 0xce12c.
Definition gmg_entry : Z := 0x77208.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Lemma rw_cells_CB0 : forall m A l, rw_cells asegs m A [CB 0 l] -> rw_cells asegs m A [CB 0 []].
Proof. intros m A l H. destruct l as [|x l]; [exact H|]. destruct H as [[[LL _] _] _]. cbn in LL. discriminate. Qed.

Lemma poison_zero_spec : poison_zero_stmt RE X L.
Proof.
unfold poison_zero_stmt. intros until junk; intros RT RL MI ST CEIL LO AAL SAL S0 AK AH SHD.
pose proof CEIL as CEIL'. idtac. pose proof AK as AK'. rewrite ?KHI_eq in AK. change (2^47) with 140737488355328 in AH.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold PZ_STACK in LO.
assert (SHa : SH addr = addr / 8 + 0x7fff8000) by reflexivity.
unfold clear_shadow, remap_range. unfold kClearShadowMmapThreshold, shadow_of, kShadowOffset, round_up, round_down, kPage.
destruct (Z.ltb_spec0 (size / 8) 18446744073709551615) as [SMALL|BIG].
{
apply aimplT_ret. eapply evt_mono.
{ eapply (poison_shadow_spec RE X); [exact RT| exact RL| exact MI| exact ST| exact CEIL'| lia| exact AAL| exact SAL| exact S0| exact AK'
| change (2^47) with 140737488355328; lia| lia| right; exact SMALL| exact SHD]. }
cbv beta. intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & RT' & Z').
unfold pz_post, PZ_STACK. do 16 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact RT'|]. exact Z'. }

exfalso. apply BIG. clear - AK AH S0. Z.div_mod_to_equations; lia.
Qed.

End S.
End Mq6.

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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4g.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4g. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXcn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).

Definition recycle_entry : Z := 0x411e4.

Definition QOBJ : Z := A_INSTANCE + 728.

Definition RECYCLE_STACK : Z := 1024.

Section S.
Context {BAND : Band}.
Variables (C : arun_components) (RE : aentry) (X : rlay).

Definition qret_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (LB0 : list ablock) (FS0 : list fframe) (lo : Z) (m : word -> option byte)
(DR : (word -> option byte) -> (word -> option byte) -> Prop)
(a1 : AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1r a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' G',
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1r a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ aheap_presA asegs a_alayout LB0 FS0 (bv_unsigned sp) m m'
/\ DR m m'
/\ QRUN C 0 QB QB [] a1 LB0 FS0 G' RE X m'.

Definition recycle_stmt (L : lvp) : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s : PStateA)
(a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (lo : Z),
QRUN C 1 QB (4 * QB) [] a LB0 FS0 G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - RECYCLE_STACK ->
aimplT (at_nodeA L asegs) (recycle (ae_L RE) a) s
(qret_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 FS0 lo m (free_keep asegs))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz QOBJ) (wz kQMinSize) (wz (rl_T X + 208)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz recycle_entry) fc None m (seg_rom asegs)).
End S.
