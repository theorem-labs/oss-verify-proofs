(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 QlEo_c1 Q5Rg QTp6 Q2qa Qy5Y Q4J3 QytA Qnxq QJE4 QZAi QUZl Q7S0 Ql2m QGeV QLsg QCwx QFqQ QQbX Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg.
Import QCwx.Mq1 QFqQ.Mq0 QQbX.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition RAS_STACK (sc : Z) : Z := 320 + 144 * Z.max 0 (27 - sc).

#[using="Type"] Lemma RAS_STACK_ge sc : 320 <= RAS_STACK sc.
Proof. unfold RAS_STACK. lia. Qed.
#[using="Type"] Lemma RAS_STACK_le sc : 0 <= sc -> RAS_STACK sc <= 4208.
Proof. unfold RAS_STACK. lia. Qed.
#[using="Type"] Lemma RAS_STACK_mono a b : a <= b -> RAS_STACK b <= RAS_STACK a.
Proof. unfold RAS_STACK. lia. Qed.
#[using="Type"] Lemma RAS_STACK_nest sc j : sc < j -> j <= 26 -> RAS_STACK j + 144 <= RAS_STACK sc.
Proof. unfold RAS_STACK. lia. Qed.

Definition ras_post (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
(st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
/\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
/\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
/\ mrel st st1 /\ brk_link_ps st1 s'
/\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ as_inv st0 st st1 sc idx
/\ 0 <= c_mmap_counter (ctx st1) < 2^32
/\ ((idx = -1 /\ errv' = Z_to_bv 64 12)
\/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
rmalloc_fp st0 st1 lo (bv_unsigned sp) a)

/\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Definition ralloc_slot_stmt (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop)
(as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop) : Prop :=
forall (fuel : nat) (R : Type) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
as_pre st0 st sc req fuel ->
rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
(forall st1 idx s' ms',
ras_post as_inv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms') ->
rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).

End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm QWTl Q98Z QkLq QdZ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QJE4.Mq1 QWTl.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 QdZ1.Mq2 QQbX.Mq1 QdZ1.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ram_carve2 : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m0 m : word -> option byte) (junk : list byte) (lo : Z) (st0 st : mstate) (p : aptr) (r : region),
rmrep st m -> mem_inv rsegs m -> s_regions st = s_regions st0 ->
(s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
pgal (snd p) -> lr_lo r <= r_base r + snd p ->
(s_areas st) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
0 <= c_secret (ctx st) < 2^64 ->
rw_cells rsegs m (conc st p) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)] ->
rw_cells rsegs m (conc st p + 24) [CB 4072 (zeros 4072)] ->
rpres_except (ram_fp st0 lo (bv_unsigned sp)) m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
let stC := upd_ctx (set_meta_area_tail (Some p)) st in
let stD := set_areas (<[p := mkArea (c_secret (ctx st)) None NSLOTS]> (s_areas stC)) stC in
evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(am_took stD (aadd p AREA_HDR) 100) (Z_to_bv 64 (conc st p + 24)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st p)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce59c) fc None m (seg_rom rsegs)).
Proof.
intros until r. intros MR MI ER0 Hr NK S0 S1 SAL SLR ANone FRESH SEC HDR0 REST PE0 WM0 FR ST LO LOLE stC stD.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (C1 & _) & _). pose proof WF as (Hres & WR & DJ & WA & WG).
pose proof (conc_region' st p r Hr) as Cp.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold alloc_ceiling in RBC.
pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
unfold ctx_head_cells in C1.
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD in *.

assert (PD : conc st p + 4096 <= 0xe2000 \/ 0x645000 <= conc st p) by lia.
assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
clear RBAL RL0 RB0 RF DR1 DR23 DR2 LRG RU Hres DJ WA WG.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928); (conc st p, conc st p + 4096)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM. unfold RCTX in MU.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 64, RCTX + 72)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC : rmrep stC mX) end.
{ eapply (rmrep_ctx_frameW st stC _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx stC upd_ctx s_ctx set_meta_area_tail c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 4. cbn [oconc]. change (conc stC p) with (conc st p). exact C1.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
clear MUc WMc.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(conc st p, conc st p + 4096)]%Z mX) as MUp; pose proof (wmono_refl rsegs mX) as WMp end.

st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC3 : rmrep stC mX) end.
{ eapply rmrep_transport_unowned; [exact MRC | exact MUp | exact WMp |].
intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. eapply (rfresh_page_avoids stC _ p r a MRC); try assumption. }
clear MUp WMp MRC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRD : rmrep stD mX) end.
{ unfold stD. eapply (rmrep_new_area stC _ p r (c_secret (ctx st))); try first [exact MRC3 | exact Hr | exact NK | exact S0 | exact S1 | exact SLR | exact ANone | exact FRESH | idtac].
- exact SAL.
- change (conc stC p) with (conc st p). exact HDR0.
- intros k Hk. change (conc stC p) with (conc st p). rewrite meta_cells_meta0.
destruct REST as [[_ B] W]. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
replace (conc st p + AREA_HDR + META_SIZE * k) with ((conc st p + 24) + 40 * k) by (unfold AREA_HDR, META_SIZE; lia).
eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 (40 * k)); [exact B| exact W| cbn; tauto| reflexivity| lia| cbn [cells_size csize Nat.add]; unfold NSLOTS in Hk; lia].
- change (conc stC p) with (conc st p).
destruct REST as [[_ B] W]. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
replace (conc st p + 4064) with ((conc st p + 24) + 4040) by lia.
eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 4040); [exact B| exact W| cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| lia| cbn [cells_size csize Nat.add]; lia]. }
clear MRC3 HDR0 REST.
assert (MSq : meta_slot stD (aadd p AREA_HDR)).
{ exists p, (mkArea (c_secret (ctx st)) None NSLOTS), 0. split; [| split; [unfold NSLOTS; lia| unfold AREA_HDR, META_SIZE; rewrite Z.mul_0_r, Z.add_0_r; reflexivity]].
unfold stD. cbn [s_areas set_areas]. rewrite lookup_insert_eq. reflexivity. }
assert (CQ : conc st p + 24 = conc stD (aadd p AREA_HDR)).
{ change (conc stD (aadd p AREA_HDR)) with (conc st (aadd p AREA_HDR)). rewrite (conc_aadd st p AREA_HDR) by (rewrite Hr; eauto). reflexivity. }
rewrite CQ. change (Z_to_bv 64 6565536) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 6566368) with (Z_to_bv 64 RMLOCK).
eapply evt_mono.
{ eapply (ram_b0 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo 100 stD (aadd p AREA_HDR));
[exact MRD | assumption | exact MSq | lia | | | unfold alloc_ceiling; lia | lia].
- lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [exact PE0|].
apply (rpres_except_of_munch_cov (ram_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha.
apply (proj1 (ram_fp_same st0 stD lo _ a ltac:(rewrite <- ER0; reflexivity))). exact Ha.
- cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
+ intros x Hx. eapply (ram_fp_region st0 lo _ x (fst p) r); [rewrite <- ER0; exact Hr| exact NK|].
pose proof (lr_lo_ge r). lia. }

split; [eapply wmono_trans; [exact WM0| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

#[using="Type"] Lemma ram_carve_walk : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (p : aptr) (r : region),
rmrep st m -> mem_inv rsegs m ->
(s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
pgal (snd p) -> lr_lo r <= r_base r + snd p ->
(s_areas st) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
(forall tl, c_meta_area_tail (ctx st) = Some tl -> is_Some ((s_areas st) !! tl)) ->
1 <= c_avail_meta_area_count (ctx st) < 2^64 -> 0 <= c_secret (ctx st) < 2^64 ->
bytes_at rsegs m (conc st p) (zeros 4096) -> wr_at rsegs m (conc st p) 4096 ->
rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo (carve_st st p) m
(am_took (carve_st st p) (aadd p AREA_HDR) 100) (Z_to_bv 64 (conc st p + 24)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st p)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce570) fc None m (seg_rom rsegs)).
Proof.
intros until r. intros MR MI Hr NK S0 S1 SAL SLR ANone FRESH TL CNT SEC ZB ZW FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (C1 & _) & _ & AR & _). pose proof WF as (Hres & WR & DJ & WA & WG).
pose proof (conc_region' st p r Hr) as Cp.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold alloc_ceiling in RBC.
pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
unfold ctx_head_cells in C1.

assert (HDR0 : rw_cells rsegs m (conc st p) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)]).
{ rewrite <- (Z.add_0_r (conc st p)). eapply (rrw_cells_of_zeros m (conc st p) 4096 0); [exact ZB| exact ZW| cbn; tauto| reflexivity| lia| cbn; lia]. }
assert (REST : rw_cells rsegs m (conc st p + 24) [CB 4072 (zeros 4072)]).
{ eapply (rrw_cells_of_zeros m (conc st p) 4096 24); [exact ZB| exact ZW| cbn [cells_wf]; split; [first [reflexivity | apply zeros_length]| exact I] | cbn [cells_bytes cbytes cells_size csize Nat.add]; rewrite app_nil_r; reflexivity| lia| cbn; lia]. }
clear ZB ZW.
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD in *.
assert (PD : conc st p + 4096 <= 0xe2000 \/ 0x645000 <= conc st p) by lia.
assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
clear RBAL RL0 RF DR1 DR23 DR2 RU.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928); (conc st p, conc st p + 4096)]%Z m) as MU0.
pose proof (wmono_refl rsegs m) as WM0. unfold RCTX in MU0.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.

st1. st1. st1. st1. st1. st1. st1.
set (st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
{ eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 5. cbn [oconc]. change (conc st1 (aadd p 4096)) with (conc st (aadd p 4096)).
rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz at 6 7.
lazymatch goal with H : rw_cells rsegs ?mX 6566376 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
clear MUc WMc.

st1.
destruct (c_meta_area_tail (ctx st)) as [tl|] eqn:HT.
-
destruct (TL tl eq_refl) as [ar Har].
destruct (rarea_conc st tl ar WF Har) as (rt & Hrt & Ct & St0 & St1 & StL & NKt & RBt & RBAt & RBCt). unfold alloc_ceiling in RBCt.
pose proof (rarea_lr_lo st tl ar rt WF Har Hrt) as LRt.
destruct (WR _ _ Hrt) as (_ & _ & _ & _ & RFt). destruct (rreserved_disjoint _ _ RFt) as (DT1 & _ & DT23 & DT2).
assert (TD : conc st tl + 4096 <= 0xe2000 \/ 0x645000 <= conc st tl) by lia.
assert (TB : 0 < conc st tl /\ conc st tl + 4096 <= lo) by lia.
assert (TP : conc st tl + 4096 <= conc st p \/ conc st p + 4096 <= conc st tl).
{ destruct (N.eq_dec (fst tl) (fst p)) as [E|NE].
- rewrite E, Hr in Hrt. assert (rt = r) by congruence. subst rt.
assert (NEo : snd tl <> snd p) by (intros E2; assert (tl = p) by (destruct tl, p; cbn in *; congruence); subst tl; rewrite ANone in Har; discriminate).
unfold pgal in SAL. clear - Ct Cp NEo SAL StL E. Z.div_mod_to_equations. lia.
- destruct (DJ _ _ _ _ Hrt Hr NE); lia. }
clear RBAt StL RFt DT1 DT23 DT2 St0 St1 LRt RBt RBCt DJ WA WG.
unfold pw. cbn [oconc]. unfold wz.
assert (CF : bv_eqb (Z_to_bv 64 (conc st tl)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF. clear CF.
pose proof MR1 as (_ & _ & _ & AR1 & _). destruct (AR1 tl ar Har) as (ARh & _ & _). clear AR1.
change (conc st1 tl) with (conc st tl) in ARh.
apply (munch_grow2 _ (conc st tl, conc st tl + 4096)) in MU0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(conc st tl + 8, conc st tl + 16)]%Z mX) as MUa; pose proof (wmono_refl rsegs mX) as WMa end.

st1. st1.
set (st2 := set_areas (<[tl := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st1)) st1).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
{ eapply (rmrep_set_area_next st1 _ _ tl ar p MR1 Har); [cbn; rewrite Hr; eauto| exact MUa| exact WMa|].
change (conc st1 tl) with (conc st tl). change (conc st1 p) with (conc st p). unfold wz at 2. exact ARh. }
clear MUa WMa ARh MR1.
rewrite (carve_st_some st p tl ar HT Har ANone). cbv zeta. fold st1. fold st2.
change (Z_to_bv 64 6565536) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 6566368) with (Z_to_bv 64 RMLOCK).
eapply evt_mono.
{ eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
first [exact MR2 | reflexivity | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact FRESH | exact SEC | exact WM0 | idtac].
- lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
- cbn [s_areas set_areas upd_ctx st2 st1]. rewrite lookup_insert_ne; [exact ANone|]. intros ->. rewrite ANone in Har; discriminate.
- lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- _ => exact H end.
- lazymatch goal with H : rw_cells rsegs ?mX (conc st p + 24) _ |- _ => exact H end.
- apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [exact MU0|exact WM0|].
cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. eapply ram_fp_area; [exact MR| exact Har| lia].
+ intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
+ intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [exact Hr| exact NK| lia].
- lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end.
- unfold alloc_ceiling; lia.
- lia. }
intros ms' RP. exact RP.
-
unfold pw. cbn [oconc]. unfold wz.
change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 56, RCTX + 64)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.

st1.
set (st2 := upd_ctx (set_meta_area_head (Some p)) st1).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
{ eapply (rmrep_ctx_frameW st1 st2 _ _ _ MR1 MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx st2 st1 upd_ctx s_ctx set_meta_area_head set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
rewrite HT. unfold pw. cbn [oconc]. change (conc st2 ?q) with (conc st q). change (conc st2 p) with (conc st p).
rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz.
lazymatch goal with H : rw_cells rsegs ?mX 6566376 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
clear MUc WMc MR1.
rewrite (carve_st_none st p HT ANone). cbv zeta. fold st1. fold st2.
change (Z_to_bv 64 6565536) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 6566368) with (Z_to_bv 64 RMLOCK).
eapply evt_mono.
{ eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
first [exact MR2 | reflexivity | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact ANone | exact FRESH | exact SEC | exact WM0 | idtac].
- lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
- lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- _ => exact H end.
- lazymatch goal with H : rw_cells rsegs ?mX (conc st p + 24) _ |- _ => exact H end.
- apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [exact MU0|exact WM0|].
cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
+ intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [exact Hr| exact NK| lia].
- lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end.
- unfold alloc_ceiling; lia.
- lia. }
intros ms' RP. exact RP.
Qed.

End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 QJE4.Mq3 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QWTl.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 QdZ1.Mq2 QQbX.Mq2 QQbX.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ctx_cells_cbn :=
cbn [ctx set_head upd_ctx s_ctx set_free_meta_head set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ram_deq : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (h nx pv : aptr),
rmrep st m -> mem_inv rsegs m ->
c_free_meta_head (ctx st) = Some h -> meta_slot st h ->
m_next (get_meta_rec st h) = Some nx -> m_prev (get_meta_rec st h) = Some pv ->
meta_slot st nx -> meta_slot st pv -> (nx = h <-> pv = h) ->
rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (dequeue LFree h st) (Z_to_bv 64 (conc st h)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce40c) fc None m (seg_rom rsegs)).
Proof.
intros until pv. intros MR MI FMH MSh HN HP MSn MSp SELF FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m h MR MSh) as (HB0 & HB1 & HB2 & _).
pose proof (rmeta_slot_bounds st m nx MR MSn) as (NB0 & NB1 & NB2 & _).
pose proof (rmeta_slot_bounds st m pv MR MSp) as (PB0 & PB1 & PB2 & _).
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH in C1.
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD in *.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st h, conc st h + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (6566376, 6566376 + 928)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.

unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
st1. st1.
assert (CF : bv_eqb (Z_to_bv 64 (conc st h)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.

rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.

st1. if_cases K; zify_cond K.
-
assert (Enx : nx = h).
{ rewrite ?unsigned_lit in K by lia. exact (rconc_meta_inj st m h nx MR MSh MSn ltac:(first [exact K | symmetry; exact K])). }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep (set_head LFree None st) mX) end.
{ eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold ctx_head_cells, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. unfold pw. unfold wz at 4.
lazymatch goal with H : rw_cells rsegs ?mX 6566376 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.
st1.
assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree None st)).
{ rewrite dequeue_mid. unfold deq_mid. rewrite HN, <- Enx, optr_eqb_refl. reflexivity. }
rewrite EQ.
change (conc st h) with (conc (set_head LFree None st) h). change (Z_to_bv 64 6565536) with (Z_to_bv 64 RSSP_GUARD).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree None st) h);
[exact MR1 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | unfold alloc_ceiling; lia | lia].
- lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
- lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
- cbn [ivs_covered]. repeat split; intros x Hx.
+ apply ram_fp_stack. lia.
+ eapply ram_fp_meta; [exact MR | exact MSh | lia].
+ eapply ram_fp_meta; [exact MR | exact MSp | lia].
+ eapply ram_fp_meta; [exact MR | exact MSn | lia].
+ apply ram_fp_ctx. unfold RCTX. lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
-
assert (NEn : nx <> h) by (intros ->; apply K; reflexivity).
assert (NEp : pv <> h) by (intros E; apply NEn; apply (proj2 SELF); exact E).

rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.

rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR MSp CH.
st1.
rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 HP HN.
set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh).
assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).

rmeta_chunk MR1 MSh1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
rewrite HN, HP in CH. cbn [oconc] in CH.
st1. st1. clear CH.

rmeta_open (conc st nx) MUn WMn.
rmeta_chunk MR1 MSn1 CH.
st1.
rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 HP HN.
set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).

st1. st1.
rewrite bv_eqb_refl. cbn [negb]. cbv iota.

rmeta_chunk MR2 MSh2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.

clear C1. pose proof MR2 as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1.
replace (c_free_meta_head (ctx st2)) with (Some h) in C1 by (symmetry; exact FMH).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR3 : rmrep (set_head LFree (Some nx) st2) mX) end.
{ eapply (rmrep_ctx_frameW st2 _ _ _ _ MR2 MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold ctx_head_cells, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. change (conc (set_head LFree (Some nx) st2) nx) with (conc st nx).
unfold pw. unfold wz at 4.
lazymatch goal with H : rw_cells rsegs ?mX 6566376 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.

st1.
assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree (Some nx) st2)).
{ rewrite dequeue_mid. unfold deq_mid. rewrite HN, HP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx h NEn). cbn [negb get_head].
rewrite !upd_meta_put. fold st1. fold st2. rewrite ctx_put_meta. unfold st1. rewrite ctx_put_meta. rewrite FMH, optr_eqb_refl. reflexivity. }
rewrite EQ.
change (conc st h) with (conc (set_head LFree (Some nx) st2) h). change (Z_to_bv 64 6565536) with (Z_to_bv 64 RSSP_GUARD).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree (Some nx) st2) h);
[exact MR3 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | unfold alloc_ceiling; lia | lia].
- lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
- lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
- cbn [ivs_covered]. repeat split; intros x Hx.
+ apply ram_fp_stack. lia.
+ eapply ram_fp_meta; [exact MR | exact MSh | lia].
+ eapply ram_fp_meta; [exact MR | exact MSp | lia].
+ eapply ram_fp_meta; [exact MR | exact MSn | lia].
+ apply ram_fp_ctx. unfold RCTX. lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

#[using="Type"] Lemma ram_take_walk : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (q : aptr),
rmrep st m -> mem_inv rsegs m ->
c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) <> 0 -> 0 <= c_avail_meta_count (ctx st) < 2^64 ->
c_avail_meta (ctx st) = Some q -> meta_slot st q ->
rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m
(am_took st q (c_avail_meta_count (ctx st) - 1)) (Z_to_bv 64 (conc st q)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce40c) fc None m (seg_rom rsegs)).
Proof.
intros until q. intros MR MI FMH CNT CR AVM MSq FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m q MR MSq) as (QB0 & QB1 & QB2 & _).
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH, AVM in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD in *.

st1. st1.
rewrite bv_eqb_refl. cbv iota.
st1. st1.
assert (CF : bv_eqb (Z_to_bv 64 (c_avail_meta_count (ctx st))) (Z_to_bv 64 0) = false)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact CNT).
rewrite CF; clear CF.
st1. st1. st1. rewrite ?(unsigned_lit (c_avail_meta_count (ctx st))) by lia.
replace (c_avail_meta_count (ctx st) + -1) with (c_avail_meta_count (ctx st) - 1) by lia.
change (Z_to_bv 64 6565536) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 6566368) with (Z_to_bv 64 RMLOCK).
eapply (ram_b0 sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m junk lo _ st q);
[exact MR | exact MI | exact MSq | lia | exact FR | exact ST | unfold alloc_ceiling; lia | lia].
Qed.

#[using="Type"] Lemma ram_disp0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate),
rmrep st m -> c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) = 0 ->
evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce460) fc None m (seg_rom rsegs))
(MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce40c) fc None m (seg_rom rsegs)).
Proof.
intros until st. intros MR FMH CNT.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH, CNT in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1. unfold RCTX, RMLOCK in *.
st1. st1. rewrite bv_eqb_refl. cbv iota.
st1. st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. reflexivity.
Qed.

End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qbf8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Qbf8.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QJE4.Mq1 QWTl.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 QdZ1.Mq2 QQbX.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmemcpy_callZ3 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
bytes_at rsegs m S src -> length src = Z.to_nat n ->
rw_cells rsegs m D [CB (Z.to_nat n) junk] ->
0 <= D -> D + n <= 2^64 -> 0 <= S -> S + n <= 2^64 -> 0 < n ->
(S + n <= D \/ D + n <= S) ->
mem_inv rsegs m ->
evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(D, D + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' D [CB (Z.to_nat n) src])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb34c) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros SRC LEN DST D0 D1 S0 S1 N0 SEP MI.
assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)); rewrite ?ED, ?ES, ?EN;
[exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
intros ms' P. unfold memcpy_post in P. rewrite !ED, !EN in P.
destruct P as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m' & -> & MU & WM & MI' & DST' & _).
do 15 eexists. split; [reflexivity|]. auto.
Qed.

#[using="Type"] Lemma ru64s_read : forall m A ws (i : Z) w a,
bytes_at rsegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 8 * i) ->
ov_read_bytes rsegs m a 8 = Some (le8 w).
Proof.
intros m A ws i w a Hb Hn Hi ->.
destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read rsegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma rrw_cells_app_split : forall m A cs1 cs2,
rw_cells rsegs m A (cs1 ++ cs2) -> rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros m A cs1 cs2 H. split; [eapply rw_cells_prefix; exact H|].
destruct H as [[WF B] W].
apply cells_wf_app in WF. destruct WF as [WF1 WF2].
rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [_ B2]. rewrite cells_bytes_length in B2 by exact WF1.
split; [split; [exact WF2 | exact B2] |].
rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

#[using="Type"] Lemma rrw_cells_app_join : forall m A cs1 cs2,
rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
- apply cells_wf_app. split; assumption.
- rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact WF1. exact B2.
- rewrite cells_size_app. destruct W1 as (H0 & H1 & X1). destruct W2 as (H2 & H3 & X2). split; [lia|]. split; [lia|].
intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
+ apply X1. lia.
+ replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply X2. lia.
Qed.

Definition ram_entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce40c) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)
/\ stk rsegs m' lo (bv_unsigned sp + -64)
/\ rmrep (am_init_st st) m'.

#[using="Type"] Lemma ram_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (lo : Z) (st : mstate),
rmrep st m -> mem_inv rsegs m -> rauxv_ok m (bv_unsigned sp) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
c_init_done (ctx st) = 1 -> s_secret st = rc_secret ->    0 <= c_secret (ctx st) < 2^64 ->
evt rsegs (ram_entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce358) fc None m (seg_rom rsegs)).
Proof.
intros until st. intros MR MI AUX ST LO LOLE INIT SEC0 SECR.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (C1 & _) & (_ & _ & PGS & G4 & G5 & G6) & _). unfold ctx_head_cells in C1.
unfold alloc_ceiling, RCTX, RGOT_SSP, RSSP_GUARD, RPAGE_SIZE in *. unfold wz in G4.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM. unfold RCTX in MU.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUh.

st1. carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.

st1. st1. st1. st1. st1. st1.

st1. rewrite sx32_wz by lia. st1. st1.

st1.
lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
rename INIT into I1.
{
rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|].
unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]. intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia. }
Qed.

End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq4.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 Q98Z.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := unfold alloc_ceiling, UNIT, IB in *; lia.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma zx32_wz x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. intros. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

#[using="Type"] Lemma meta_word_sc2 mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 5) 126 = 2 * m_sizeclass mr.
Proof.
intros (LI & FB & SCR & ML).
assert (E : 126 = Z.ldiff (Z.ones 7) (Z.ones 1)) by reflexivity. rewrite E, land_ldiff_distr.
rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
change (2^7) with 128. change (2^1) with 2. change (2^5) with 32. unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.div_add, (Z.div_small (m_last_idx mr)) by lia.
replace (0 + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr)) with ((m_freeable mr + 2 * m_sizeclass mr) + m_maplen mr * 128) by lia.
rewrite Z.mod_add, Z.mod_small by lia.
replace (m_freeable mr + 2 * m_sizeclass mr) with (m_freeable mr + m_sizeclass mr * 2) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed.

#[using="Type"] Lemma meta_word_pg mr : mw_ok mr -> meta_word mr - meta_word mr mod 4096 = 4096 * m_maplen mr.
Proof.
intros (LI & FB & SCR & ML). unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

Definition rfhead_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st1 : mstate) (g : aptr) (idx li : Z) : machine_state -> Prop :=
fun ms' => exists x1 x5 x6 x7 junk m',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (li + 1) - 1))) (Z_to_bv 64 0x642da4) x5 x6 x7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcdda8) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rmrep st1 m'.

#[using="Type"] Lemma rfree_head3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
(m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (b3 lo8 hi E rsv : Z),
let po := snd p in
let idx := Z.land b3 31 in
let mr := get_meta_rec st g in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
rmrep st m0 -> mem_inv rsegs m0 -> ticks_ok st ->
stk rsegs m0 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
rw_cells rsegs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono rsegs m m0 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
meta_slot st g ->
cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
0 <= b3 < 256 ->
r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
0 <= rsv <= E - (r_base r + po) -> bytes_at rsegs m0 (E - rsv) [b8 0] -> bytes_at rsegs m0 E [b8 0] ->
(forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
(Z_to_bv 64 E) a3 (wz rsv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcdd58) fc None m0 (seg_rom rsegs)).
Proof.
intros until rsv. intros po idx mr st1 MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL HK3 HK2 HK1 LI FBL SC ML B3 ELO EHI RSV RB0r RE0 HCLR.
pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
unfold alloc_ceiling, UNIT, IB in *.
pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
pose proof (munch_refl [(r_base r + po - 3, r_base r + po)]%Z m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
pose proof (bytes_at_read rsegs m0 _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
pose proof (bytes_at_read rsegs m0 _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.

st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }

st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }

change (Z_to_bv 64 E) with (wa E).
st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }

st1. st1. st1. st1. st1. st1.
rewrite (unsigned_lit idx) by lia. rewrite sllw1_word' by lia. rewrite (wz_unsigned (meta_word mr)) by (unfold meta_word; lia).

pose proof MR1 as (_ & _ & _ & _ & _ & SH1). destruct (SH1 (fst p) r Hr Hk) as [HWr _]. clear SH1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (SOK3 : store_ok rsegs mX (wa (bv_unsigned a0 + -3)) 1 = true)
by (replace (bv_unsigned a0 + -3) with (r_base r + (po - 3)) by lia; apply (wr_at_store_ok rsegs mX _ _ (po - 3) 1 HWr); cbn; lia) end.
st1.
pose proof (rmrep_wr8 st _ (aadd p (-3)) 255 r MR1 TK Hr Hk ltac:(cbn; lia)
ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR2.
cbn [aadd snd] in MR2. fold po in MR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -3))) [b8 255])
by (rewrite le1_neg1; f_equal; unfold wa; f_equal; lia) end.
store_done.
pose proof (ticks_ok_wr8 st (aadd p (-3)) 255 TK) as TK2.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof MR2 as (_ & _ & _ & _ & _ & SH2); destruct (SH2 (fst p) r Hr Hk) as [HWr2 _]; clear SH2;
assert (SOK2 : store_ok rsegs mX (wa (bv_unsigned a0 + -2)) 2 = true)
by (replace (bv_unsigned a0 + -2) with (r_base r + (po - 2)) by lia; apply (wr_at_store_ok rsegs mX _ _ (po - 2) 2 HWr2); cbn; lia) end.
st1.
pose proof (rmrep_wr16 _ _ (aadd p (-2)) 0 r MR2 TK2 Hr Hk ltac:(cbn; lia) ltac:(cbn; lia)
ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR3.
cbn [aadd snd] in MR3. fold po in MR3. fold st1 in MR3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -2))) (le2 (wz 0)))
by (f_equal; unfold wa; f_equal; lia) end.
store_done. clear MR2 TK2 HWr HWr2.

st1. rewrite (all_word (meta_word mr)) by (unfold meta_word; lia).
replace (meta_word mr mod 32) with (m_last_idx mr) by (unfold meta_word; Z.div_mod_to_equations; lia).
st1.

apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|exact I].
intros x Hx. right. right. exists (fst p), r.
assert (CASES : x - r_base r = po - 3 \/ x - r_base r = po - 2 \/ x - r_base r = po - 1) by lia.
destruct CASES as [E1|[E1|E1]]; [exists b3| exists lo8| exists hi]; rewrite E1; (split; [exact Hr|]); (split; [exact Hk|]); (split; [lia|]); assumption. }
apply evt_done. unfold rfhead_post.
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
do 6 eexists.
split; [reflexivity|].
split; [eapply rpres_except_trans; [exact PE0| exact MU]|]. split; [exact WM0|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. exact MR3.
Qed.

#[using="Type"] Lemma rfree_head2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
(m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (base : aptr) (b3 lo8 hi r32 : Z),
let po := snd p in
let idx := Z.land b3 31 in
let mr := get_meta_rec st g in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
let stride := get_stride mr in
let E := conc st base + UNIT + stride * idx + stride - IB in
let rsv0 := Z.shiftr b3 5 in
let rsv := if 160 <=? b3 then r32 else rsv0 in
rmrep st m0 -> mem_inv rsegs m0 -> ticks_ok st ->
stk rsegs m0 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
rw_cells rsegs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono rsegs m m0 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
meta_slot st g -> m_mem mr = Some base -> fst base = fst p -> 0 <= snd base ->
cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
0 <= b3 < 256 -> idx <= m_last_idx mr ->
UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
(160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at rsegs m0 (E - 4) (le4 (wz r32)) /\ bytes_at rsegs m0 (E - 5) [b8 0]) ->
rsv <= E - (r_base r + po) -> bytes_at rsegs m0 (E - rsv) [b8 0] -> bytes_at rsegs m0 E [b8 0] ->
(forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
(Z_to_bv 64 stride) (wz b3) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcdd10) fc None m0 (seg_rom rsegs)).
Proof.
intros until r32. intros po idx mr st1 stride E rsv0 rsv MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL Hmem FB SB0 HK3 HK2 HK1
AV FRD LI FBL SC ML B3 Hidx S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
assert (RSV0 : 0 <= rsv0 < 8).
{ unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
assert (RSVR : 0 <= rsv < 2^32).
{ unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
unfold alloc_ceiling, UNIT, IB in *.
pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (rmrep_meta_chunk st m0 g MR1 MSL) as MM.
fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.

st1. st1. st1. st1. st1. st1. st1. cbn [oconc].
replace (conc st base + stride + stride * idx + 12) with E by (unfold E; lia).
fold rsv0.

st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
-
replace (Z_to_bv 64 rsv0) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
subst mr.
eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
[exact MR1| exact MI| exact TK| exact ST| unfold alloc_ceiling; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
| exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
-
destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
pose proof (bytes_at_read rsegs m0 _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
cbn [skipn Z.to_nat] in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
replace (E - 4) with (conc st base + stride + stride * idx + 8) in RD4 by (unfold E; lia).
pose proof (bytes_at_read rsegs m0 _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.
replace (E - 5) with (conc st base + stride + stride * idx + 7) in RD5 by (unfold E; lia).

st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }

st1.
rewrite zx32_wz by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }

st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
replace (wz r32) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
subst mr.
eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
[exact MR1| exact MI| exact TK| exact ST| unfold alloc_ceiling; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
| exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
Qed.

#[using="Type"] Lemma rfree_head : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(lo : Z) st (p : aptr) r g gh ar (b3 lo8 hi r32 : Z),
let sh := get_shadow st (fst p) in
let po := snd p in
let off16 := lo8 + 256 * hi in
let idx := Z.land b3 31 in
let base := aadd p (- (UNIT * off16) - UNIT) in
let mr := get_meta_rec st g in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
let stride := get_stride mr in
let E := conc st base + UNIT + stride * idx + stride - IB in
let rsv0 := Z.shiftr b3 5 in
let rsv := if 160 <=? b3 then r32 else rsv0 in
rmrep st m -> mem_inv rsegs m -> ticks_ok st ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
cell_read sh (po - 2) = Known lo8 -> cell_read sh (po - 1) = Known hi ->
(s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
m_mem mr = Some base ->
(s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
(m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
(48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
(m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->

(m_maplen mr = 0 \/ m_last_idx mr <> 0 -> m_sizeclass mr < 48) ->
UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
(160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at rsegs m (E - 4) (le4 (wz r32)) /\ bytes_at rsegs m (E - 5) [b8 0]) ->
rsv <= E - (r_base r + po) -> bytes_at rsegs m (E - rsv) [b8 0] -> bytes_at rsegs m E [b8 0] ->
(forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs)).
Proof.
intros until r32. intros sh po off16 idx base mr st1 stride E rsv0 rsv MR MI TK ST LO SLO Hr Hk HP AL P16 PLO PHI HK4 HK3 HK2 HK1 Hgh Hg MSL G0 Hmem Har Hchk
AV FRD SE LI FBL SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48 S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MUs.
pose proof (wmono_refl rsegs m) as WM.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) HK3) as [_ B3].
assert (RSV0 : 0 <= rsv0 < 8).
{ unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
assert (RSVR : 0 <= rsv < 2^32).
{ unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
assert (FB : fst base = fst p) by reflexivity.
assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
assert (SB0 : 0 <= snd base) by (unfold base; cbn; unfold UNIT; lia).

revert BIG RB0r RE0.
unfold rfree_entry, alloc_ceiling, UNIT, IB in *. intros BIG RB0r RE0.

st1. if_cases K0; zify_cond K0. { exfalso. lia. }
carve_frame 48%nat ST.
st1. st1. st1. st1. st1. st1. st1.

st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM |]; intros l h [E1|[]]; inversion E1; subst; unfold alloc_ceiling; lia) end.
eapply evt_cut.
{ eapply rget_meta_spec with (st := st) (p := p) (r := r) (g := g) (gh := gh) (ar := ar) (b3 := b3) (lo := lo8) (hi := hi).
all: try eassumption. all: try lia. }
intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
replace (ret_pc (Z_to_bv 64 0xcdcc8)) with (Z_to_bv 64 0xcdcc8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rmrep_meta_chunk st mX g MR1 MSL) as MM;
destruct (rmrep_shadow_read st mX (fst p) r (po - 3) b3 MR1 Hr Hk ltac:(lia) HK3) as [R3 _] end.
fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
replace (r_base r + (po - 3)) with (bv_unsigned a0 + -3) in R3 by lia.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
assert (MW : mw_ok mr) by (unfold mw_ok; lia).
pose proof (meta_word_range mr MW) as MWR. pose proof (meta_word_maplen mr MW) as MW12.
pose proof (meta_word_last_idx mr MW) as MW31. pose proof (meta_word_sc2 mr MW) as MWS. pose proof (meta_word_pg mr MW) as MWP.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (K2 : forall a4v a5v a6v, evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR (Z_to_bv 64 0xcdcc8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
(Z_to_bv 64 stride) (wz b3) a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcdd10) fc None mX (seg_rom rsegs))) end.
{ intros a4v a5v a6v.
lazymatch type of MUs with munch ?W _ _ => assert (DJ : forall A n, A + n <= lo -> disjoint_from W A n) by (intros A n HA; cbn; lia) end.
lazymatch type of MUs with munch ?W m ?mY =>
assert (PE0 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m mY)
by (apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp)) W); [exact MUs| exact WM|];
cbn [ivs_covered]; split; [|exact I]; intros x Hx; apply rfree_fp_stack; lia) end.
subst rsv rsv0 E stride mr.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
eapply (rfree_head2 ra sp gp tp t0 t1 t2 s0 s1 a0 a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ F fc m mX _ lo st p r g base b3 lo8 hi r32) end;
[exact MR1| assumption| exact TK| exact ST| ulia| ulia| exact FR| exact PE0| exact WM| exact Hr| exact Hk| exact HP| exact AL| ulia| ulia
| exact MSL| exact Hmem| exact FB| exact SB0| exact HK3| exact HK2| exact HK1| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia
| intros Hb3; destruct (BIG Hb3) as (X1 & X2 & X3 & X4); split; [exact X1|]; split; [exact X2|]; split;
(eapply bytes_at_transport; [eassumption| exact MUs| apply DJ; cbn; try rewrite length_le4; ulia])
| ulia
| exact RB0r
| exact RE0
| exact HCLR]. }

st1. st1. st1. st1. fold idx. rewrite MW12.
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned).

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (KS : forall a2v a4v, (m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR (Z_to_bv 64 0xcdcc8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 gw (wz (meta_word mr))
a2v (wz b3) a4v ga5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcdcf4) fc None mX (seg_rom rsegs))) end.
{ intros a2v a4v COND. specialize (SC48 COND).
assert (STR : stride = 16 * size_class (m_sizeclass mr)).
{ unfold stride, get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }

assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
st1. st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite MWS. st1. st1.
replace (159560 + m_sizeclass mr * 2) with (159560 + 2 * m_sizeclass mr) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (RS' : ov_read_bytes rsegs mX (Z_to_bv 64 (159560 + 2 * m_sizeclass mr)) 2 = Some (le2 (wz (size_class (m_sizeclass mr))))) end.
{ replace (Z_to_bv 64 (159560 + 2 * m_sizeclass mr)) with (wa (RSIZE_CLASSES + 2 * m_sizeclass mr)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
apply rsize_classes_read; [assumption| lia]. }
pose proof (size_class_range (m_sizeclass mr) ltac:(lia)) as SZ.
st1. try rewrite (Z.mod_small (size_class (m_sizeclass mr))) by lia.
st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
replace (Z_to_bv 64 (size_class (m_sizeclass mr) * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
rewrite Egw. apply K2. }

st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
- apply KS. left. exact Km.
-
st1. rewrite MW31. st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
+ apply KS. right. exact Kl.
+
st1. st1. rewrite land_pgmask by lia. rewrite MWP. st1. st1.
replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 stride).
2:{ unfold stride, get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
rewrite Egw. apply K2.
Qed.

End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq5.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 Q98Z.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rfree_fp_meta0 : forall st st0 m lo sp q a, rmrep st m -> meta_slot st q -> s_regions st0 = s_regions st ->
conc st q <= a < conc st q + 40 -> rfree_fp st0 lo sp a.
Proof.
intros st st0 m lo sp q a MR (ar & arr & k & Har & Hk & Eq) ER Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
eapply rfree_fp_region; [rewrite ER; exact Hra | exact NK | lia].
Qed.

Definition rftriv_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (C : Z -> Prop) (m : word -> option byte) (st' : mstate) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ rpres_except C m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rmrep st' m'.

#[using="Type"] Lemma rfree_triv : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st0 st : mstate) (g : aptr) (idx : Z),
let mr := get_meta_rec st g in
let st' := upd_meta g (m_set_freed (m_freed mr + bit idx)) st in
rmrep st m -> mem_inv rsegs m -> meta_slot st g ->
s_regions st = s_regions st0 -> s_areas st = s_areas st0 ->
0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
m_freed mr <> 0 -> Z.lor (m_freed mr) (m_avail mr) + bit idx <> mask_upto (m_last_idx mr) ->
rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt rsegs (rftriv_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (rfree_fp st0 lo (bv_unsigned sp)) m st')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 0x642da4) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xcdda8) fc None m (seg_rom rsegs)).
Proof.
intros until idx. intros mr st' MR MI MSL ER EA HF HA HL HI TF TA Hfz Hall FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
pose proof (wmono_refl rsegs m) as WM.
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
clearbody gw.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
unfold alloc_ceiling, RNEED_LOCKS in *.

step. step. rewrite !sx32_wz_sxv by lia.

step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.

step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.land_comm _ (sxv (2 ^ idx))).
rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).

step. if_true.

st1.

step. if_cases K2; zify_cond K2.
{ exfalso. apply Hfz. apply (proj1 (sxv_zero (m_freed mr) ltac:(lia))). first [exact K2 | rewrite wz_unsigned in K2 by assumption; exact K2]. }
clear K2.

step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
step. if_cases K3; zify_cond K3.
{ exfalso. apply Hall. unfold bit, mask_upto. apply (proj1 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
rewrite !wz_unsigned in K3 by apply sxv_range. exact K3. }
clear K3 RSUM.

step. rewrite (wz_unsigned (sxv (2 ^ idx))), (wz_unsigned (sxv (m_freed mr))) by assumption.
rewrite (Z.add_comm (sxv (m_freed mr)) (sxv (2 ^ idx))). rewrite addw_word.
step. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
clear K4 RL.

step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR' : rmrep st' mX) end.
{ unfold st'. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
rewrite HG in MM.
eapply rw_cells_congr; [ | | | exact MM].
- unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
unfold bit. rewrite (free_store_val (m_freed mr) idx) by (assumption || lia). reflexivity.
- reflexivity.
- cbn. tauto. }
clear MUg MM.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z mX) as MUs;
pose proof (wmono_refl rsegs mX) as WMs end.
step. step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MR' MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
- intros x Hx. apply rfree_fp_stack. lia.
- intros x Hx. eapply (rfree_fp_meta0 st st0 m lo (bv_unsigned sp) g); [exact MR | exact MSL | symmetry; exact ER | lia]. }
finish.
Qed.

#[using="Type"] Lemma rfree_tocall : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate) (g : aptr) (idx : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv rsegs m -> meta_slot st g ->
0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
(m_freed mr = 0 \/ Z.lor (m_freed mr) (m_avail mr) + bit idx = mask_upto (m_last_idx mr)) ->
evt rsegs (fun ms' => exists x2 x3 x4 x5 x6 x7,
ms' = MS (mkR (Z_to_bv 64 0xcde18) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(Z_to_bv 64 (conc st g)) (Z_to_bv 64 idx) x2 x3 x4 x5 x6 x7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xcdf80) fc None m (seg_rom rsegs))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 0x642da4) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xcdda8) fc None m (seg_rom rsegs)).
Proof.
intros until idx. intros mr MR MI MSL HF HA HL HI TF TA HNT.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
replace (Z_to_bv 64 (conc st g)) with gw by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
clearbody gw.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
unfold alloc_ceiling, RNEED_LOCKS in *.

step. step. rewrite !sx32_wz_sxv by lia.

step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.

step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.land_comm _ (sxv (2 ^ idx))).
rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).

step. if_true. st1.

step. if_cases K2; zify_cond K2.
-
st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
st1. st1.
apply evt_done. do 6 eexists. reflexivity.
-
step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
step. if_cases K3; zify_cond K3.
+ st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
st1. st1.
apply evt_done. do 6 eexists. reflexivity.
+ exfalso. destruct HNT as [Hz|Hall].
* apply K2. rewrite ?wz_unsigned by apply sxv_range. rewrite Hz. reflexivity.
* apply K3. rewrite ?wz_unsigned by apply sxv_range.
apply (proj2 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
unfold bit, mask_upto in Hall. exact Hall.
Qed.

End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnOf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 QDUx.Mq6.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 Q98Z.Mq1 QnOf.Mq0.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rffin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
/\ rmrep st m'.

#[using="Type"] Lemma rfree_fin0 : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv rsegs m ->
rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt rsegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m st errv)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz 0) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xcde18) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros TP MR MI FR ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
unfold alloc_ceiling, RMLOCK, RNEED_LOCKS, RATP in *. subst tp.
rewrite (unsigned_lit 6434400) in ERR by lia. change (6434400 + -164) with 6434236 in ERR.

st1. st1. st1. st1.

st1.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0xcde2c)) with (Z_to_bv 64 0xcde2c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
rewrite (unsigned_lit 6434400) by lia. change (6434400 + -164) with 6434236. exact ERR.
Qed.

Definition rfmun_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0xcde48) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw bw lw a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (errno_addr tp)) (sx32 errv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmunmap_entry) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
/\ rmrep st m'.

#[using="Type"] Lemma rfree_tomunmap : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
(m : word -> option byte) (junk : list byte) (lo len : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv rsegs m -> 0 < len < 2^64 ->
rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt rsegs (rfmun_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo junk m st errv bw (wz len))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz len) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xcde18) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros TP MR MI HL FR ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
unfold alloc_ceiling, RMLOCK, RNEED_LOCKS, RATP in *. subst tp.
rewrite (unsigned_lit 6434400) in ERR by lia. change (6434400 + -164) with 6434236 in ERR.

st1. st1. st1. st1.

st1.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0xcde2c)) with (Z_to_bv 64 0xcde2c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

st1. if_cases K; zify_cond K. { exfalso. rewrite wz_unsigned in K by lia. lia. }

st1. st1. st1. st1.
replace (ret_pc (Z_to_bv 64 0xcde34)) with (Z_to_bv 64 0xcde34) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
apply evt_done. unfold rfmun_post. do 14 eexists. split; [rewrite (unsigned_lit 6434400) by lia; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
split; [rewrite (unsigned_lit 6434400) by lia; change (6434400 + -164) with 6434236; exact ERR| exact MR2].
Qed.

#[using="Type"] Lemma rerrno_avoids_repfoot : forall st m a, rmrep st m -> 6434236 <= a < 6434240 -> ~ rrepfoot st a.
Proof.
intros st m a MR Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
- unfold RCTX in C. lia.
- unfold RMLOCK in C. lia.
- unfold RNEED_LOCKS in C. lia.
- unfold RPAGE_SIZE in C. lia.
- destruct C as (ak & ar & Hak & Hin).
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len ra)). lia.
- destruct C as (b & gh & Hb & Hin).
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len rb)). lia.
- destruct C as (rid & r & v & Hr & Hk & Hin & HC).
destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. lia.
- unfold RGOT_SSP in C. lia.
- unfold RSSP_GUARD in C. lia.
Qed.

#[using="Type"] Lemma rmrep_transport_frame_errno : forall st m m' (sp : Z),
rmrep st m -> munch [(sp - 48, sp); (6434236, 6434240)]%Z m m' -> wmono rsegs m m' -> alloc_ceiling <= sp - 48 -> rmrep st m'.
Proof.
intros st m m' sp MR MU WM HS. eapply rmrep_transport_unowned; [exact MR | exact MU | exact WM |].
apply ivs_avoid_cons; [| apply ivs_avoid_cons; [| apply ivs_avoid_nil]].
- intros a Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in HS.
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
+ unfold RCTX in C. lia.
+ unfold RMLOCK in C. lia.
+ unfold RNEED_LOCKS in C. lia.
+ unfold RPAGE_SIZE in C. lia.
+ destruct C as (ak & ar & Hak & Hin).
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold alloc_ceiling in RBC. lia.
+ destruct C as (b & gh & Hb & Hin).
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC). unfold alloc_ceiling in RBC. lia.
+ destruct C as (rid & r & v & Hr & Hk & Hin & HC).
destruct (WR _ _ Hr) as (_ & _ & _ & RBC & _). unfold alloc_ceiling in RBC. lia.
+ unfold RGOT_SSP in C. lia.
+ unfold RSSP_GUARD in C. lia.
- intros a Ha. eapply rerrno_avoids_repfoot; [exact MR | exact Ha].
Qed.

#[using="Type"] Lemma rfree_fin1 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv rsegs m ->
rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
le4 ew = le4 errv ->
rw_cells rsegs m (errno_addr tp) [C4 e'] ->
stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt rsegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp); (6434236, 6434240)]%Z m st errv)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (errno_addr tp)) ew s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xcde48) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros TP MR MI FR EW ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (6434236, 6434240)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
unfold alloc_ceiling, RATP in *. subst tp.
rewrite (unsigned_lit 6434400) in ERR by lia. change (6434400 + -164) with 6434236 in ERR.
rewrite (unsigned_lit 6434400) by lia. change (6434400 + -164) with 6434236.

st1.

st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX) by (eapply (rmrep_transport_frame_errno st m mX (bv_unsigned sp)); [exact MR | exact MU | exact WM | unfold alloc_ceiling; lia]) end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
rewrite (unsigned_lit 6434400) by lia. change (6434400 + -164) with 6434236.
eapply rw_cells_congr; [| | | exact ERR]; [cbn [cells_bytes cbytes app]; rewrite EW; reflexivity| reflexivity| cbn; tauto].
Qed.

End RC__1.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn9M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 Qn9M.Mq0 QdZ1.Mq3 QQbX.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma renf_glue_walk : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw gw iw rav s0v s1v s2v s3v s4v : word)
F fc (m : mem) (st : mstate),
rw_cells rsegs m RCTX (ctx_head_cells st) ->
rw_cells rsegs m RMLOCK [C4 (wz 0)] ->
rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
48 <= bv_unsigned sp ->
0 <= c_mmap_counter (ctx st) < 2^32 ->
evt rsegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v gw iw nw (wz (sxv (c_mmap_counter (ctx st)))) a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 renframe_entry) fc None m (seg_rom rsegs))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7 gw iw s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce954) fc None m (seg_rom rsegs)).
Proof.
intros until st. intros CH LK FR SP48 CTR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold RCTX, RMLOCK in *. unfold ctx_head_cells in CH.

step. rewrite sx32_wz_sxv by lia.

step. step.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0xce960)) with (Z_to_bv 64 0xce960) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

do 12 step.
apply evt_done. unfold renframe_entry. reflexivity.
Qed.

#[using="Type"] Lemma bytes_at_enframe_user : forall m4 P0 stride off n k B bs,
0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= P0 -> P0 + stride <= 2^64 ->
bytes_at rsegs m4 (P0 + 16 * off) bs -> Z.of_nat (length bs) <= n ->
bytes_at rsegs (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)) (P0 + 16 * off) bs.
Proof.
intros m4 P0 stride off n k B bs OFF0 N0 FIT P4 PS HB LEN.
assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
assert (HO : bytes_at rsegs (renframe_off_mem m4 P0 off) (P0 + 16 * off) bs).
{ unfold renframe_off_mem. destruct (Z.eqb_spec off 0); [exact HB|].
apply bytes_at_write_other; [| lia | cbn; lia | cbn; lia].
apply bytes_at_write_other; [| lia | rewrite L2; lia | rewrite L2; lia].
apply bytes_at_write_other; [exact HB| lia | cbn; lia | cbn; lia]. }
unfold renframe_tail_mem. cbv zeta.
set (mE := write_to_mem (write_to_mem (renframe_off_mem m4 P0 off) _ _) _ _).
assert (HE : bytes_at rsegs mE (P0 + 16 * off) bs).
{ subst mE. apply bytes_at_write_other; [| lia | rewrite L2; lia | rewrite L2; lia].
apply bytes_at_write_other; [exact HO| lia | cbn; lia | cbn; lia]. }
clearbody mE.
set (rsv := P0 + stride - 4 - (P0 + 16 * off) - n).
set (mF := if rsv =? 0 then _ else _).
assert (HF : bytes_at rsegs mF (P0 + 16 * off) bs).
{ subst mF. destruct (Z.eqb_spec rsv 0); [exact HE|]. apply bytes_at_write_other; [exact HE| lia | cbn; lia | cbn; lia]. }
clearbody mF.
set (mG := if 5 <=? rsv then _ else _).
assert (HG : bytes_at rsegs (fst mG) (P0 + 16 * off) bs /\ 0 <= snd mG <= 5).
{ subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
- split; [|lia]. apply bytes_at_write_other; [| lia | rewrite L4; lia | rewrite L4; lia].
apply bytes_at_write_other; [exact HF| lia | cbn; lia | cbn; lia].
- split; [exact HF| lia]. }
clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
apply bytes_at_write_other; [exact HG| lia | cbn; lia | cbn; lia].
Qed.

Definition renf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (o m0 m1 : mem) (C : Z -> Prop) (st1 : mstate) (g b : aptr) (idx n : Z)
(r : mstate * optr) (ms' : machine_state) : Prop :=
exists st' p t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
r = (st', Some p)
/\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (conc st' p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rmrep st' m' /\ ticks_ok st' /\ rpres_except C m0 m'
/\ enf_leaf o st1 g b idx n st' p
/\ (forall bs, bytes_at rsegs m1 (conc st' p) bs -> Z.of_nat (length bs) <= n -> bytes_at rsegs m' (conc st' p) bs).

#[using="Type"] Lemma renf_implT :
forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' ra s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32)
(o m0 m1 : mem) (s : PState) (st1 : mstate) (g b : aptr) (r : region) (idx n lo : Z) (C : Z -> Prop),
let mr := get_meta_rec st1 g in
let stride := get_stride mr in
let ctr := c_mmap_counter (ctx st1) in
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 ->
mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rpres_except C m0 m1 -> (forall a, lo <= a < bv_unsigned sp -> C a) ->
(forall a, r_base r + snd b + 16 + stride * idx - 4 <= a < r_base r + snd b + 16 + stride * idx + stride - 4 -> C a) ->
0 <= ctr < 2^32 ->
slot_ok st1 g b r idx n ->
rimplT o (enframe_full st1 g idx n ctr (fun st2 p => ret (havoc p n st2, Some p))) s
(fun res s' ms' => s' = s /\ renf_post ra sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc lo o m0 m1 C st1 g b idx n res ms')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
a0 a1 a2 a3 a4 a5 a6 a7 (pw st1 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce954) fc None m1 (seg_rom rsegs)).
Proof.
intros until C. intros mr stride ctr MR TK UA MI ST CLO LO FR PE CST CSL CTR SO.
destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16, AVr, FRr, FBr, MPL, SCr.
fold stride in SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16.
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
clear SPAN. rename SPAN1 into SPAN.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in CLO.

destruct (rslot_facts st1 m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN S16 B16 SMOD HDR0)
as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND.
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
unfold alloc_ceiling in RC, GC.
set (G := conc st1 g) in *.
pose proof (GDJ (fst b) r Hr Hk) as GR.
change (get_meta_rec st1 g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM.
set (B := conc st1 b) in *.
pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.

pose proof (bytes_at_read rsegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
pose proof (bytes_at_read rsegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
pose proof (bytes_at_read rsegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
rewrite Z.add_0_r in RD4.
replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.

unfold enframe_full, enframe_read_off. change (get_meta_rec st1 g) with mr. fold stride. cbv zeta.
assert (Hp0 : slot_start' mr idx = (fst b, snd b + (16 + stride * idx))).
{ unfold slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT. cbn [fst snd]. fold stride. reflexivity. }
rewrite Hp0. unfold aadd. cbn [fst snd].
apply rimplT_rd8. rewrite E3.
change ((stride - IB - n) / UNIT) with ((stride - 4 - n) / 16). set (slack := (stride - 4 - n) / 16).
set (K := fun off : Z => let '(st2, p) := enframe_at st1 g idx n off in @ret (mstate * optr) (havoc p n st2, Some p)).
set (off0 := if bv_unsigned x3 =? 0 then Z.land ctr 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255).
set (off := fold_off off0 slack).
assert (OFF0 : 0 <= off0 < 256).
{ subst off0. destruct (bv_unsigned x3 =? 0).
- split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
- split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
assert (SL0 : 0 <= slack) by (subst slack; apply Z.div_pos; lia).
pose proof (fold_off_le_slack off0 slack OFF0 SL0) as OFF. fold off in OFF.
assert (FIT : 16 * off + n + 4 <= stride) by (subst slack; Z.div_mod_to_equations; lia).
match goal with |- rimplT _ _ _ ?Q ?ms =>
assert (GOAL : rimplT o (K off) s Q ms) end.
2:{ assert (OFFa : bv_unsigned x3 = 0 -> fold_off (Z.land ctr 255) slack = off).
{ intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
assert (OFFb : bv_unsigned x3 <> 0 -> fold_off (Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) slack = off).
{ intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
clearbody off.
destruct (Z.eqb_spec (bv_unsigned x3) 0) as [E0|NE0]; cbn [negb].
- rewrite (OFFa E0). exact GOAL.
- apply rimplT_rd16. unfold aadd; cbn [fst snd]. rewrite E2, E1. rewrite (OFFb NE0). exact GOAL. }
subst K. cbv beta. rewrite surj_pair_let. apply rimplT_ret.

pose proof MR as (WF' & CX & GL & _). destruct GL as (LK & _). destruct CX as (CH & _).
eapply evt_cut.
{ eapply (renf_glue_walk sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' (Z_to_bv 64 n) (pw st1 (Some g)) (wz idx) ra s0v s1v s2v s3v s4v F fc m1 st1);
[exact CH| exact LK| exact FR| lia| exact CTR]. }
intros ms' ->.
unfold renframe_entry.
eapply evt_mono.
{ eapply (renframe_walk ra sp gp tp t0 t1 t2 s0v s1v a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (pw st1 (Some g)) (Z_to_bv 64 n)
(pw st1 (m_prev mr)) (pw st1 (m_next mr)) F fc m1 B stride n idx ctr (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
all: lazymatch goal with
| |- rw_cells _ _ (bv_unsigned (pw _ _)) _ => unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia; exact MM
| |- mem_inv _ _ => exact MI
| |- wr_at _ _ _ _ => exact WRs
| |- ov_read_bytes _ _ _ 2 = _ => exact RD2
| |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
| |- ov_read_bytes _ _ _ _ = _ => exact RD3
| |- bv_unsigned (Z_to_bv 64 _) = _ => apply unsigned_lit; lia
| |- _ => idtac end.
all: try (unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia).
all: try lia.
- subst stride. unfold get_stride, UNIT. reflexivity.
- intros off' O1 O2. pose proof (Q16 off' O1 O2). lia. }

intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
split; [reflexivity|].
fold slack in EM. fold off0 in EM. fold off in EM. fold slack off0 off.
set (res := enframe_at st1 g idx n off) in *.

assert (S31n : stride - 4 - n < 2^31) by lia.
destruct (renframe_mrep st1 m1 g b r idx n off MR TK Hmem Hr Hk B0 ltac:(clear -IDX LI32; lia) ltac:(unfold stride, mr in SPAN; clear -SPAN S16; lia) S16 S31n NOGRP (proj1 OFF) N0 FIT (Q16 off (proj1 OFF) FIT))
as (MRr & TKr & CONCr & FSTr & SNDr).
fold stride B res in MRr, TKr, CONCr, FSTr, SNDr.
change (conc st1 b) with B in MRr, CONCr. change (get_stride (get_meta_rec st1 g)) with stride in MRr, CONCr, SNDr.
fold res in MRr, TKr, CONCr, FSTr, SNDr.
set (P0 := B + 16 + stride * idx) in *.
rewrite <- EM in MRr.
destruct (rmrep_havoc (fst res) m' (snd res) n MRr TKr) as [MR' TK'].

assert (PE0 : rpres_except (fun a => P0 - 4 <= a < P0 + stride - 4) m1 m').
{ rewrite EM. apply (rpres_enframe _ m1 m1 P0 stride off n idx B (rpres_except_refl _ _) (proj1 OFF) N0 FIT); [unfold P0; lia| unfold P0; lia|].
intros x Hx. exact Hx. }
assert (ST' : stk rsegs m' lo (bv_unsigned sp + -48)).
{ eapply rpres_except_stk; [exact PE0| exact ST|]. intros a Ha. cbv beta. unfold P0. lia. }
assert (FR' : rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
{ eapply rpres_except_rw_cells; [exact PE0| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat]. intros a Ha. cbv beta. unfold P0. lia. }
release_frame FR' ST' (bv_unsigned sp).
unfold renf_post. exists (havoc (snd res) n (fst res)), (snd res). do 14 eexists. exists m'.
split; [reflexivity|].
split. { unfold wz. rewrite conc_havoc. rewrite <- CONCr. unfold res. rewrite conc_enframe_at. reflexivity. }
split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|]. split; [exact TK'|].
split.
{ rewrite EM. apply (rpres_enframe C m0 m1 _ stride off n idx B PE (proj1 OFF) N0 FIT); [unfold B; lia| unfold B; lia|].
intros x Hx. apply CSL. unfold B in Hx. lia. }
split.
{ exists off. split; [exact (proj1 OFF)|]. split; [exact FIT|].
split. { clear - FSTr SNDr. destruct (snd res) as [p1 p2]. cbn [fst snd] in FSTr, SNDr. subst. reflexivity. }
split; [reflexivity|]. split; [reflexivity|].
unfold off, off0, slack, enf_off0. fold mr. fold stride. rewrite E3, E2, E1. reflexivity. }

assert (EC : conc (fst res) (snd res) = P0 + 16 * off) by (unfold res at 1; rewrite conc_enframe_at; exact CONCr).
intros bs HB LEN. rewrite conc_havoc, EC in HB |- *. rewrite EM.
apply (bytes_at_enframe_user m1 P0 stride off n _ B bs (proj1 OFF) N0 FIT); [unfold P0, B; lia| unfold P0, B; lia| exact HB| exact LEN].
Qed.

End RC__1.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq9.
Import QCwx.Mq1 QFqQ.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rDB32 : Z := 125613361.
Definition rdbi (k : Z) : Z := ((2 ^ k * rDB32) mod 2^32) / 2^27.

#[using="Type"] Lemma rdbi_range k : 0 <= rdbi k < 32.
Proof. unfold rdbi. pose proof (Z.mod_pos_bound (2^k * rDB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed.

Definition rdebruijn_bytes : list byte :=
Eval vm_compute in (match image_bytes rsegs RDEBRUIJN 32 with Some bs => bs | None => [] end).

#[using="Type"] Lemma rdebruijn_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m RDEBRUIJN [CB 32 rdebruijn_bytes].
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold RDEBRUIJN; lia | unfold RDEBRUIJN; cbn; lia]. Qed.

#[using="Type"] Lemma rdebruijn_read : forall m k, mem_inv rsegs m -> 0 <= k < 32 ->
ov_read_bytes rsegs m (wa (RDEBRUIJN + rdbi k)) 1 = Some [b8 k].
Proof.
intros m k MI Hk.
destruct (rdebruijn_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
pose proof (rdbi_range k) as R.
rewrite (bytes_at_read rsegs m RDEBRUIJN rdebruijn_bytes (rdbi k) 1 B) by (cbn; lia).
assert (Hn : exists n, k = Z.of_nat n /\ (n < 32)%nat) by (exists (Z.to_nat k); split; [lia|lia]).
destruct Hn as (n & -> & Hn).
Ltac solve_db := vm_compute; reflexivity.
do 32 (destruct n as [|n]; [solve_db |]). lia.
Qed.

#[using="Type"] Lemma mul_srliw27 k : 0 <= k < 32 ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (2 ^ k * rDB32)))) 27) = rdbi k.
Proof.
intros Hk. unfold rdbi.
assert (P : 0 < 2 ^ k <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
rewrite unsigned_lit by (unfold rDB32; nia).
change (bv_wrap 32 (2 ^ k * rDB32)) with ((2 ^ k * rDB32) mod 2^32).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

Definition rclz_v4 (x : Z) : Z :=
let v1 := Z.lor (Z.shiftr x 2) x in
let v2 := Z.lor v1 (Z.shiftr x 1) in
let w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1) in
let w3 := Z.lor (Z.shiftr w2 4) w2 in
Z.lor (Z.shiftr w3 8) w3.
Definition rclz_pow (x : Z) : Z := Z.land (rclz_v4 x + 1) (Z.lxor (rclz_v4 x) 18446744073709551615).
Definition rclz_fn (x : Z) : bool := (rclz_pow x =? 2 ^ Z.log2 x) && (rclz_v4 x <? 2 ^ 13).
#[using="Type"] Lemma rclz_check_true : forallb rclz_fn (zseq 11 8181) = true.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma rclz_pow_eq x : 11 <= x < 8192 -> rclz_pow x = 2 ^ Z.log2 x /\ 0 <= rclz_v4 x < 2 ^ 13.
Proof.
intros Hx. pose proof (forallb_zseq rclz_fn 11 8181 x rclz_check_true ltac:(lia) ltac:(lia)) as X. unfold rclz_fn in X.
apply andb_prop in X. destruct X as [X1 X2].
apply Z.eqb_eq in X1. apply Z.ltb_lt in X2. split; [exact X1| split; [|exact X2]].
unfold rclz_v4. repeat first [apply Z.lor_nonneg; split | apply Z.shiftr_nonneg]; lia.
Qed.

#[using="Type"] Lemma lxor_4k_124 k : 3 <= k <= 12 -> Z.lxor (k * 4) 124 = 124 - 4 * k.
Proof. intros Hk. assert (H : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; reflexivity. Qed.

#[using="Type"] Lemma lor_even_1 a : 0 <= a -> Z.even a = true -> Z.lor a 1 = a + 1.
Proof. intros Ha He.
assert (D : Z.land a 1 = 0). { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2. rewrite Zeven_mod in He. apply Z.eqb_eq in He. exact He. }
rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity. Qed.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 (size_to_class n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce83c) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

#[using="Type"] Lemma rmalloc_entry_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
a0 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
stk rsegs m lo (bv_unsigned sp) -> 0x645000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
rw_cells rsegs m RNEED_LOCKS [C1 (b8 0)] ->
evt rsegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs)).
Proof.
intros until n. intros HA N ST ILO LO MI NL. subst a0.
pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rmalloc_entry, RNEED_LOCKS in *.
step. carve_frame 48%nat ST. step. step. step. step. step. step.

step. step. step.
step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.

step. step. step. step. step.
step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
clear K1.

step. step. step. step. step.
rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).

assert (LOCKJ : forall (a0' a1' a2' a3' : word) (sc : Z) (mj : mem),
sc = size_to_class n ->
mem_inv rsegs mj -> rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk rsegs mj lo (bv_unsigned sp + -48) ->
munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono rsegs m mj -> rw_cells rsegs mj 6566131 [C1 (b8 0)] ->
evt rsegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 6566368) a0' a1' a2' a3' a4 a5 a6 a7
s2 (Z_to_bv 64 159528) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce824) fc None mj (seg_rom rsegs))).
{ intros a0' a1' a2' a3' sc mj -> MIj FRj STj MUj WMj NLj.
step. step. rewrite ?zxb_b8 by lia. step. if_cases KL; zify_cond KL. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in KL by lia. lia. }
apply evt_done. unfold rentry_post, RMLOCK, RDEBRUIJN. do 5 eexists. split; [reflexivity|].
split; [exact FRj|]. split; [exact STj|]. split; [exact MUj|]. split; [exact WMj| exact MIj]. }
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
-
apply LOCKJ; try assumption.
rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
-
assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
destruct (rclz_pow_eq x XR) as [PW RV4].

step.
step. rewrite (unsigned_lit x), srliw_small by lia.
pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
step. rewrite (unsigned_lit x), srliw_small by lia.
step.
step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.

step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.

step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.

step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
assert (EW4 : w4 = rclz_v4 x) by reflexivity.

step. step. step.
rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
rewrite (unsigned_lit 0), Z.lor_0_l by lia.

step. step. rewrite (unsigned_lit w4) by lia.
step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
set (k := Z.log2 x) in *.
assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
assert (EX : x = q + 1) by reflexivity. clearbody x.
assert (K13 : 3 <= k <= 12) by (apply LG; lia).

step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
step. rewrite (mul_srliw27 k) by lia.
pose proof (rdbi_range k) as DR.
step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
step. rewrite ?zxb_b8 by lia. clear DBR.

step. step. step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step.
rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
replace (124 - 4 * k) with (120 - i) by lia.
assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
{ unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
clearbody i. clear EK.
pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.

step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 - (120 - i)) with (i + 1) by lia.
step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. step. replace (159560 + (i + 1) * 2) with (159560 + 2 * (i + 1)) by lia.
lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rsize_classes_read mc (i + 1) HI ltac:(lia)) as RS1; unfold RSIZE_CLASSES in RS1 end.

step. rewrite ?zx16_wz by lia. clear RS1.

assert (J1 : forall (i1 c : Z) (mj : mem),
i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
mem_inv rsegs mj -> rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk rsegs mj lo (bv_unsigned sp + -48) ->
munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono rsegs m mj -> rw_cells rsegs mj 6566131 [C1 (b8 0)] ->
evt rsegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 6566368)
(Z_to_bv 64 (120 - i)) (Z_to_bv 64 159560) (Z_to_bv 64 c) (Z_to_bv 64 (159560 + 2 * (i + 1))) a4 a5 a6 a7
s2 (Z_to_bv 64 159528) (Z_to_bv 64 q) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce808) fc None mj (seg_rom rsegs))).
{ intros i1 c mj Hi1 Hc MIj FRj STj MUj WMj NLj.
assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
{ subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
destruct I1R as [I1R I1E].
pose proof (size_class_range i1 ltac:(lia)) as SR2.

step. rewrite (unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c - (120 - i)) with i1 by lia.
step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (159560 + i1 * 2) with (159560 + 2 * i1) by lia.
pose proof (rsize_classes_read mj i1 MIj ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
step. rewrite ?zx16_wz by lia. clear RS2.

step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
step. step.
destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
* rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
* rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
+
step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
+
step. step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.

Definition rentry_big_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a1 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce6a4) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

#[using="Type"] Lemma rentry_big_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
a0 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2^63 - 4097 ->
stk rsegs m lo (bv_unsigned sp) -> 0x645000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
evt rsegs (rentry_big_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs)).
Proof.
intros until n. intros HA N ST ILO LO MI. subst a0. unfold MMAP_THRESHOLD in N.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rmalloc_entry.
step. carve_frame 48%nat ST. step. step. step. step. step. step.
step. step. step.
step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.
step. step. step. step. step.
step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
clear K1.
apply evt_done. unfold rentry_big_post, RMLOCK. do 2 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -48) _ |- _ => split; [exact H|] end.
repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

Definition rentry_ovf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists a1 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ stk rsegs m' lo (bv_unsigned sp)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 12)].

#[using="Type"] Lemma rentry_ovf_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z) (errv : word),
a0 = Z_to_bv 64 n -> 2^63 - 4097 <= n < 2^64 ->
stk rsegs m lo (bv_unsigned sp) -> 0x645000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> tp = Z_to_bv 64 RATP ->
evt rsegs (rentry_ovf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros HA N ST ILO LO MI ERR TP. subst a0.
assert (ETP : bv_unsigned tp + -164 = 6434236) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rmalloc_entry.
step. carve_frame 48%nat ST. step. step. step. step. step. step.
step. step. step.
step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.

step. step. step. step.

step. step. step. step. step. step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m2 end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rentry_ovf_post. do 2 eexists. split; [reflexivity|].
split; [exact ST|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
lazymatch goal with H : rw_cells rsegs m2 (bv_unsigned tp + -164) _ |- _ => exact H end.
Qed.

End RC__1.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 QJE4.Mq3 QDUx.Mqa QDUx.Mqb.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 QdZ1.Mq2 QQbX.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
apply (stk_write rsegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
apply (wmono_write rsegs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv rsegs mX |- _ =>
apply (mem_inv_store rsegs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rat9c_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc : Z) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists a3 a4 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce144) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -96)
/\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="Type"] Lemma rntf_deqself : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g : aptr) (sc lo : Z),
rmrep st m -> mem_inv rsegs m -> meta_slot st g -> 0 <= sc < 48 ->
m_next (get_meta_rec st g) = Some g ->
rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
(deq_mid (LActive sc) g st) g sc fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce13c) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros MR MI MSL SC GN FR FRL ST LO LOLE.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
unfold alloc_ceiling, RCTX in *.
st1.
pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (6566376 + sc * 8 + 80)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc None MR SC) as MR2; unfold RCTX in MR2 end.
clear ACTS.
rraw_store_finish (6566376 + 80 + 8 * sc) (le8 (pw st None)) FR ST MU WM SOK.
assert (EQ : deq_mid (LActive sc) g st = set_active sc None st).
{ unfold deq_mid. rewrite GN, optr_eqb_refl. reflexivity. }
rewrite EQ.
apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.

#[using="Type"] Lemma rntf_deq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g nx pv : aptr) (sc lo : Z),
rmrep st m -> mem_inv rsegs m -> meta_slot st g -> 0 <= sc < 48 ->
m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv ->
nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
(active st sc = None \/ exists q, active st sc = Some q /\ meta_slot st q) ->
a2 = pw st (active st sc) ->
rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
(deq_mid (LActive sc) g st) g sc fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce0b8) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros MR MI MSL SC GN GP NEn NEp MSn MSp ACT HA2 FR FRL ST LO LOLE.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
pose proof (rmeta_slot_bounds st m nx MR MSn) as NB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
unfold alloc_ceiling, RCTX in *.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (6566376, 6566376 + 928)]%Z m) as MU.

rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1. clear CH.

rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR MSp CH.
st1.
rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 GP GN.
set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).

rmeta_chunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1. clear CH.

rmeta_open (conc st nx) MUn WMn.
rmeta_chunk MR1 MSn1 CH.
st1.
rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 GP GN.
set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).

pose proof (rmrep_active_read st2 _ sc (wa (RCTX + 80 + 8 * sc)) MR2 SC eq_refl) as RDA. unfold RCTX in RDA.
replace (wa (6566376 + 80 + 8 * sc)) with (Z_to_bv 64 (6566376 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
assert (HACT : active st2 sc = active st sc) by reflexivity. rewrite HACT in RDA.
assert (HPW : forall q, pw st2 q = pw st q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
st1. clear RDA.
assert (EQmid : deq_mid (LActive sc) g st =
if optr_eqb (active st sc) (Some g) then set_active sc (Some nx) st2 else st2).
{ unfold deq_mid. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head].
rewrite !upd_meta_put. fold st1. fold st2. rewrite HACT. reflexivity. }

st1. if_cases K; zify_cond K.
-
assert (HA : optr_eqb (active st sc) (Some g) = false).
{ destruct (active st sc) as [q|]; [|reflexivity]. cbn [optr_eqb]. apply aptr_eqb_neq. intros ->. apply K.
unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
rewrite HA in EQmid. rewrite <- EQmid in MR2. subst a2.
apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSp | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSn | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
-
assert (HA : active st sc = Some g).
{ destruct ACT as [A0|(q & Aq & MSq)].
- exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
- rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
pose proof (rmeta_slot_bounds st m q MR MSq) as QB. rewrite ?unsigned_lit in K by lia.
rewrite (rconc_meta_inj st m g q MR MSL MSq ltac:(lia)). reflexivity. }
rewrite HA, optr_eqb_refl in EQmid.
rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
rewrite GN, GP in CH. cbn [oconc] in CH.
st1. clear CH. st1.
pose proof MR2 as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives st2) sc (Z_to_bv 64 (6566376 + sc * 8 + 80)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
clear ACTS.
rraw_store_finish (6566376 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) FR ST MU WM SOK.
rewrite <- EQmid in MR3. subst a2.
apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSp | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSn | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR3].
Qed.

#[using="Type"] Lemma land_mod_pow2 a b n : 0 <= n -> (Z.land a b) mod 2^n = Z.land (a mod 2^n) (b mod 2^n).
Proof.
intros Hn. rewrite <- !Z.land_ones by lia.
apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
destruct (Z.testbit a k), (Z.testbit b k), (Z.testbit (Z.ones n) k); reflexivity.
Qed.

#[using="Type"] Lemma act_mask_le4 f y z : 0 <= f < 2^32 -> 1 <= y <= 2^32 -> z mod 2^32 = (y - 1) mod 2^32 ->
le4 (Z_to_bv 64 (Z.land (sxv f) (bv_unsigned (Z_to_bv 64 z)))) = le4 (wz (Z.land f (y - 1))).
Proof.
intros Hf Hy Hz. apply le4_congr.
pose proof (sxv_range f). rewrite (unsigned_lit_wrap z). pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)).
assert (R1 : 0 <= Z.land (sxv f) (z mod 2^64) < 2^64) by (apply land_range64; lia).
assert (R2 : 0 <= Z.land f (y - 1) < 2^32).
{ split; [apply Z.land_nonneg; lia|]. pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)). lia. }
rewrite unsigned_lit, wz_unsigned by lia.
rewrite land_mod_pow2, sxv_mod32, mod64_mod32, Hz by lia.
rewrite !Z.mod_small by lia. reflexivity.
Qed.

Definition rat00_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce1a8) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -96)
/\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="Type"] Lemma rntf_postdeq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) stm (g : aptr) (sc lo : Z) (an : bool),
let st1 := upd_meta g clr_links stm in
rmrep stm m -> mem_inv rsegs m -> meta_slot stm g -> 0 <= sc < 48 ->
(if an then bv_unsigned a2 = conc stm g else bv_unsigned a2 <> conc stm g) ->
(an = true -> forall a, active st1 sc = Some a ->
meta_slot st1 a /\ a <> g /\ m_avail (get_meta_rec st1 a) = 0 /\ 0 <= m_freed (get_meta_rec st1 a) < 2^32
/\ exists ba gh, m_mem (get_meta_rec st1 a) = Some ba /\ (s_groups st1) !! ba = Some gh /\ 0 <= g_active_idx gh <= 31) ->
rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rat00_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 F fc lo stm m (pd_st an st1 sc) g fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc stm g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce144) fc None m (seg_rom rsegs)).
Proof.
intros until an. intros st1 MR MI MSL SC HA2 HACT FR FRL ST LO LOLE.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (bv_unsigned_in_range _ a2) as A2R. change (bv_modulus 64) with (2^64) in A2R.
pose proof (rmeta_slot_bounds stm m g MR MSL) as GB.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
unfold alloc_ceiling, RCTX in *.
pose proof (munch_refl [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m) as MU.

rmeta_open (conc stm g) MUg WMg.
rmeta_chunk MR MSL CH.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st1 mX)
by (unfold st1; rewrite upd_meta_put; eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WMg |];
eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear MUg WMg CH
end.
assert (COV : forall m', munch [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m m' -> wmono rsegs m m' ->
rpres_except (rfree_fp stm lo (bv_unsigned sp)) m m').
{ intros m' MU' WM'. apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU'; [exact MU'|exact WM'|].
cbn [ivs_covered]. repeat split; intros x Hx; (eapply rfree_fp_meta; [exact MR | exact MSL | lia]). }
assert (MSg1 : meta_slot st1 g) by (unfold st1; rewrite upd_meta_put; apply meta_slot_put_meta; exact MSL).
assert (Hconc : forall q, conc st1 q = conc stm q) by (intros; reflexivity).

st1. if_cases K; zify_cond K.
-
destruct an. { exfalso. apply K. rewrite ?unsigned_lit by lia. lia. }
cbn [pd_st].
apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR1].
-
destruct an. 2:{ exfalso. apply HA2. rewrite ?unsigned_lit in K by lia. lia. }
cbn [pd_st].

pose proof (rmrep_active_read st1 _ sc (wa (RCTX + 80 + 8 * sc)) MR1 SC eq_refl) as RDA. unfold RCTX in RDA.
assert (HPW : forall q, pw st1 q = pw stm q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
replace (wa (6566376 + 80 + 8 * sc)) with (Z_to_bv 64 (6566376 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
st1. clear RDA.

st1. destruct (active st1 sc) as [a|] eqn:HA1.
+ destruct (HACT eq_refl a eq_refl) as (MSa & NEa & AV0 & FRR & ba & gh & Hmem & Hgh & AI).
pose proof (rmeta_slot_bounds st1 _ a MR1 MSa) as AB. rewrite !Hconc in AB.
munch_grow MU (conc stm a, conc stm a + 40).
unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.

rmeta_chunk MR1 MSa CHa. rewrite AV0, Hmem in CHa. cbn [oconc] in CHa.
st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. rewrite ?unsigned_lit by lia. reflexivity. } clear K3.

st1.

destruct (rmrep_group_read st1 _ ba gh MR1 Hgh) as [_ (w8 & RD8 & Hw8)].
rewrite Hconc in RD8.
st1.
pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
assert (MOD8 : bv_unsigned w8 mod 32 = g_active_idx gh).
{ rewrite <- Hw8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }

st1. st1. unfold zxb. rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite MOD8.
set (y := 2 ^ (g_active_idx gh + 1)).
st1. st1. rewrite negw_word.

clear CHa. rmeta_open (conc stm a) MUa WMa.
rmeta_chunk MR1 MSa CHa. rewrite Hmem in CHa. cbn [oconc] in CHa.
pose proof (sxv_range (m_freed (get_meta_rec st1 a))) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range y) as RY1.
st1. rewrite sx32_wz_sxv by lia.
st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.

assert (AMO : amo_aligned AW (Z_to_bv 64 (conc stm a + 28)) = true).
{ apply amo_aligned_intro; [lia|]. Z.div_mod_to_equations. lia. }
amo_step AMO. rewrite ?sx32_wz_sxv by lia.
st1. if_false.
amo_step AMO.
st1. if_false.
st1. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. st1. if_false.

st1. st1. st1.

set (f := m_freed (get_meta_rec st1 a)) in *.
assert (AI31 : Z.land (g_active_idx gh) 31 = g_active_idx gh).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
assert (ACT : act_of st1 a = y - 1).
{ unfold act_of. rewrite Hmem. cbn [default]. unfold group_active_idx, get_group. rewrite Hgh, AI31. unfold mask_upto, y. reflexivity. }
assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
assert (Y1 : 1 <= y <= 2^32).
{ unfold y. split; [pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh + 1)); lia| apply Z.pow_le_mono_r; lia]. }
pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (act_st st1 a (act_of st1 a)) mX)
end.
{ unfold act_st. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR1 | exact MSa | exact MUa | exact WMa |].
eapply rw_cells_congr; [ | | | exact CHa]; [ | reflexivity | cbn; tauto].
unfold meta_cells. unfold pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen oconc].
fold f. rewrite E1. rewrite (act_mask_le4 f y) ; [| lia | exact Y1 | rewrite <- Zplus_mod_idemp_l, swrap32_mod32, Zplus_mod_idemp_l; reflexivity].
rewrite !le4_sxv by lia. rewrite Hmem. cbn [oconc]. reflexivity. }
clear MUa WMa CHa.
apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split. { apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
- eapply rfree_fp_meta; [exact MR | exact MSL | lia].
- eapply rfree_fp_meta; [exact MR | exact MSa | lia].
- eapply rfree_fp_meta; [exact MR | exact MSL | lia]. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
unfold pd_st. rewrite ?HA1. exact MR2.
+
unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. rewrite ?unsigned_lit by lia. reflexivity. } clear K2.
apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
unfold pd_st. rewrite ?HA1. exact MR1.
Qed.

End RC__1.
End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 QytA QJE4.Mq4 Qy5Y.Mq5.
Export QWTl.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.

Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QdZ1.Mq3 QQbX.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

#[using="Hconc"] Lemma rpw_extP p : optr_in P p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.

#[using="Hmetas"] Lemma rget_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.

#[using="P HP Hconc"] Lemma rmeta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
unfold meta_cells. rewrite !rpw_extP by assumption. reflexivity.
Qed.

#[using="P HP Hconc Hctx"] Lemma rmrep_ctx_extP m : rmrep_ctx st m -> rmrep_ctx st' m.
Proof.
intros H. destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
assert (E1 : ctx_head_cells st' = ctx_head_cells st).
{ unfold ctx_head_cells. rewrite Hctx. rewrite !rpw_extP by assumption. reflexivity. }
assert (E2 : actives st' = actives st).
{ unfold actives. apply map_ext. intros a. unfold active. rewrite Hctx. apply rpw_extP. apply (H6 (Z.of_nat a)). }
assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hctx. reflexivity. }
assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hctx. reflexivity. }
assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hctx. reflexivity. }
assert (E6 : ctx_tail_cells st' = ctx_tail_cells st).
{ unfold ctx_tail_cells, brk_word. rewrite Hctx. destruct (c_brk (ctx st)) as [| |rid off]; try reflexivity.
rewrite (Hconc (rid, off)) by exact H7. reflexivity. }
unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6, Hctx. exact H.
Qed.

#[using="P HP Hconc Hmetas"] Lemma rarea_rep_extP m a ar : (s_areas st) !! a = Some ar -> rarea_rep st m a ar -> rarea_rep st' m a ar.
Proof.
intros Ha (A1 & A2 & A3). destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
destruct (H9 a ar Ha) as [Pa Pn].
unfold rarea_rep. rewrite (Hconc a Pa). rewrite (rpw_extP _ Pn). split; [exact A1|]. split; [|exact A3].
intros k Hk. rewrite rget_meta_rec_extP, rmeta_cells_extP. apply A2. exact Hk.
Qed.

#[using="P HP Hconc"] Lemma rgroup_rep_extP m b gh : (s_groups st) !! b = Some gh -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof.
intros Hb (w8 & R & Hw8). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (rpw_extP _ Pg). auto.
Qed.
End PEXT.

#[using="Type"] Lemma rbytes_at_agree m m' A bs : bytes_at rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at rsegs m' A bs.
Proof.
intros (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

#[using="Type"] Lemma rwr_at_agree m m' A n : wr_at rsegs m A n -> agree_on m m' A n -> wr_at rsegs m' A n.
Proof.
intros (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
unfold wview. rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma rrw_cells_agree m m' A cs : rw_cells rsegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs.
Proof.
intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
- eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
- eapply rwr_at_agree; eauto.
Qed.

#[using="Type"] Lemma ru64arr_agree m m' A ws : u64arr rsegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr rsegs m' A ws.
Proof.
intros [HB HW] AG. split.
- eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
- eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

#[using="Type"] Lemma ru8arr_agree m m' A bs : u8arr rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr rsegs m' A bs.
Proof. intros [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

#[using="Type"] Lemma rmrep_agree : forall st m m',
rmrep st m ->
agree_on m m' RMLOCK 4 -> agree_on m m' RLIBC 0x498 -> agree_on m m' RGOT_SSP 8 -> agree_on m m' RSSP_GUARD 8 -> agree_on m m' RVMLOCK 4 ->
(forall a ar, (s_areas st) !! a = Some ar -> agree_on m m' (conc st a) 4096) ->
(forall b gh, (s_groups st) !! b = Some gh -> agree_on m m' (conc st b) 9) ->
(forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
rmrep st m'.
Proof.
intros st m m' (WF & CX & GL & AR & GR & SH) AGL AGC AGS1 AGS2 AGV AGA AGG AGR.
split; [exact WF|]. split; [|split; [|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold rmrep_ctx.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
unfold RLIBC, RCTX in *.
split; [|split; [|split; [|split; [|split; [|split]]]]].
+ eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ exact C7.
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD, RVMLOCK in *.
split; [|split; [|split; [|split; [|split]]]].
+ eapply rrw_cells_agree; [exact G1|]. eapply agree_on_sub; [exact AGL| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G2|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G3|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G4|]. eapply agree_on_sub; [exact AGS1| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G5|]. eapply agree_on_sub; [exact AGS2| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G6|]. eapply agree_on_sub; [exact AGV| lia| cbn; lia].
- intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). pose proof (AGA a ar Ha) as AG.
split; [|split].
+ eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
+ intros k Hk. eapply rrw_cells_agree; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AG| lia| lia].
+ eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
eapply rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG. split.
+ eapply rwr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AG| lia| lia].
Qed.

Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).

Hypothesis MR : rmrep st m.
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= alloc_ceiling.
Hypothesis RF : ranges_free (live_ranges st) x L = true.

Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

#[using="Type"] Lemma rnr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rnr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. rewrite rnr_regions. apply lookup_insert_eq. Qed.
#[using="r0"] Lemma rnr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rnr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rnr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof.
intros H. destruct (N.eq_dec q rid) as [->|NE].
- left. rewrite rnr_lookup_new in H. inversion H. auto.
- right. rewrite rnr_lookup_old in H by exact NE. auto.
Qed.
#[using="r0"] Lemma rnr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite rnr_lookup_old by assumption. reflexivity. Qed.
#[using="r0"] Lemma rnr_conc_new off : conc st' (rid, off) = x + off.
Proof. unfold conc, get_region. cbn [fst snd]. rewrite rnr_lookup_new. reflexivity. Qed.
#[using="Type"] Lemma rnr_shadow q : get_shadow st' q = get_shadow st q.
Proof. reflexivity. Qed.
#[using="RC__ st m' rid L ZF"] Lemma rnr_lr_lo_new : x <= lr_lo r0.
Proof. unfold lr_lo, r0. cbn. destruct k; lia. Qed.

#[using="RC__ rid RF"] Lemma rnr_old_disjoint q r : (s_regions st) !! q = Some r ->
x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof.
intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

#[using="m m' rid L r0 MR PT X0 XA LEN XC RF ZF"] Lemma rnr_regions_wf : rregions_wf st'.
Proof.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
assert (RFimg : ranges_free ref_reserved x L = true).
{ apply ranges_free_intro. intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
split; [exact RS|]. split; [|split; [|split]].
- intros q r Hq. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
+ unfold r0. cbn. fold L. repeat split; try lia. exact RFimg.
+ exact (WR q r H).
- intros q1 r1 q2 r2 H1 H2 NE.
destruct (rnr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rnr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
+ congruence.
+ cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q2 r2 H2'). pose proof rnr_lr_lo_new. lia.
+ cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q1 r1 H1'). pose proof rnr_lr_lo_new. lia.
+ exact (DJ q1 r1 q2 r2 H1' H2' NE).
- intros a ar Ha. destruct (WA a ar Ha) as (r & Hr & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
exists r. rewrite rnr_lookup_old by exact Pa. auto.
- intros b gh Hb. destruct (WG b gh Hb) as (r & Hr & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
exists r. rewrite rnr_lookup_old by exact Pb. auto.
Qed.

#[using="m rid L r0 MR PT FRs X0 XA LEN XC RF AG ZF"] Lemma rmrep_new_region : rmrep st' m'.
Proof.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
assert (RI : forall b n, In (b, n) ref_reserved -> x + L <= b \/ b + n <= x).
{ intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
pose proof (RI _ _ ltac:(left; reflexivity)) as RI1. pose proof (RI _ _ ltac:(right; right; left; reflexivity)) as RI2.
pose proof (RI _ _ ltac:(right; right; right; left; reflexivity)) as RI3.
pose proof (round_up_pg_ge len) as LG. fold L in LG. unfold alloc_ceiling in XC.

assert (MR1 : rmrep st m').
{ eapply rmrep_agree; [exact MR| | | | | | | |].
- intros a Ha. apply AG; unfold RMLOCK in *; lia.
- intros a Ha. apply AG; unfold RLIBC in *; lia.
- intros a Ha. apply AG; unfold RGOT_SSP in *; lia.
- intros a Ha. apply AG; unfold RSSP_GUARD in *; lia.
- intros a Ha. apply AG; unfold RVMLOCK in *; lia.
- intros a ar Ha a0 Ha0.
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rnr_old_disjoint _ _ Hra).
unfold alloc_ceiling in RBC. apply AG; lia.
- intros b gh Hb a0 Ha0.
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
pose proof (lr_lo_group rb Kb). pose proof (rnr_old_disjoint _ _ Hrb). unfold alloc_ceiling in RBC. apply AG; lia.
- intros q r Hq Hk a0 Ha0. destruct (WR q r Hq) as (B0 & _ & _ & BC & _). unfold alloc_ceiling in BC.
pose proof (lr_lo_group r Hk). pose proof (rnr_old_disjoint _ _ Hq). apply AG; lia. }
pose proof MR1 as (_ & CX1 & GL1 & AR1 & GR1 & SH1).
assert (Hconc : forall q, (fun r => r <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rnr_conc; exact Hq).
split; [exact rnr_regions_wf|]. split; [|split; [exact GL1|split; [|split]]].
- eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl). exact CX1.
- intros a ar Ha. eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|]. exact (AR1 a ar Ha).
- intros b gh Hb. eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|]. exact (GR1 b gh Hb).
- intros q r Hq Hk. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
+
cbn [r_kind r0] in Hk. unfold rshadow_rep. cbn [r_base r_len r0]. fold L.
split.
* split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite (ZF Hk) by lia. discriminate.
* intros o v Ho Hc. rewrite rnr_shadow in Hc. unfold get_shadow in Hc. fold rid in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc.
rewrite cell_read_shadow0 in Hc. inversion Hc; subst v. split; [|lia].
split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia]. cbn [nth_error].
unfold mrd. rewrite Z.add_0_r. rewrite (ZF Hk) by lia. reflexivity.
+ eapply rshadow_rep_ext; [apply rnr_shadow|]. exact (SH1 q r H Hk).
Qed.

#[using="Type"] Lemma rticks_ok_new_region : ticks_ok st -> ticks_ok st'.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma rptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End NEWREGION.

Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
((RMLOCK <= a < RMLOCK + 4 \/ 0x6446f8 <= a < 0x6446f8 + 4) \/ RLIBC <= a < RLIBC + 0x498 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8
\/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
m' (wa a) = m (wa a).

#[using="Type"] Lemma rdr_regions : s_regions st' = delete rid (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rdr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof.
intros H. rewrite rdr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
- rewrite lookup_delete_eq in H. discriminate.
- rewrite lookup_delete_ne in H by congruence. auto.
Qed.
#[using="Type"] Lemma rdr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rdr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rdr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite rdr_lookup_old by assumption. reflexivity. Qed.
#[using="Type"] Lemma rdr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.

#[using="m r MR Hr PT AG"] Lemma rmrep_drop_region : rmrep st' m'.
Proof.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
assert (Hconc : forall q, (fun q => q <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rdr_conc; exact Hq).
destruct (WR rid r Hr) as (B0 & _ & RL0 & BC & RFr). unfold alloc_ceiling in BC.
assert (OTHER : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
r_base rq + round_up_pg (r_len rq) <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= lr_lo rq)
by (intros q rq Hq NE; exact (DJ q rq rid r Hq Hr NE)).
split; [|split; [|split; [|split; [|split]]]].
-
split; [exact RS|]. split; [|split; [|split]].
+ intros q rq Hq. destruct (rdr_lookup_inv q rq Hq) as [_ H]. exact (WR q rq H).
+ intros q1 r1 q2 r2 H1 H2 NE. destruct (rdr_lookup_inv _ _ H1) as [_ H1']. destruct (rdr_lookup_inv _ _ H2) as [_ H2']. exact (DJ _ _ _ _ H1' H2' NE).
+ intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
exists ra. rewrite rdr_lookup_old by exact Pa. auto.
+ intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
exists rb. rewrite rdr_lookup_old by exact Pb. auto.
-
eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl).
destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold rmrep_ctx.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0xe2000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0xe2000 \/ 0x645000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
{ destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [exact RFr| lia]]. }
assert (AGC : agree_on m m' RLIBC 0x498).
{ intros a Ha. unfold RLIBC in Ha. apply AG; [lia| lia| right; left; unfold RLIBC; lia]. }
unfold RLIBC, RCTX in *.
split; [|split; [|split; [|split; [|split; [|split]]]]].
+ eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ exact C7.
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0xe2000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0xe2000 \/ 0x645000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
{ destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [exact RFr| lia]]. }
unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD, RVMLOCK in *.
split; [|split; [|split; [|split; [|split]]]].
+ eapply rrw_cells_agree; [exact G1|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|left; left; lia].
+ eapply rrw_cells_agree; [exact G2|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
+ eapply rrw_cells_agree; [exact G3|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
+ eapply rrw_cells_agree; [exact G4|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; left; lia].
+ eapply rrw_cells_agree; [exact G5|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; right; left; lia].
+ eapply rrw_cells_agree; [exact G6|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|left; right; lia].
- intros a ar Ha. cbn [s_areas drop_region set_shadow set_regions] in Ha.
eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|].
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). unfold alloc_ceiling in RBC.
assert (NE : fst a <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _); exact (proj1 (P9 a ar Ha))).
pose proof (OTHER _ _ Hra NE). pose proof (lr_lo_ge r). pose proof (lr_lo_ge ra).
assert (AGA : agree_on m m' (conc st a) 4096).
{ intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists (fst a), ra. split; [exact Hra|]. lia. }
destruct (AR a ar Ha) as (A1 & A2 & A3). split; [|split].
+ eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
+ intros k0 Hk0. eapply rrw_cells_agree; [apply A2; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AGA| lia| lia].
+ eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
- intros b gh Hb. cbn [s_groups drop_region set_shadow set_regions] in Hb.
eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
assert (NE : fst b <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10); exact (proj1 (P10 b gh Hb))).
pose proof (OTHER _ _ Hrb NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rb Kb). unfold alloc_ceiling in RBC.
destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
eapply rrw_cells_agree; [exact R|]. intros a0 Ha0. cbn in Ha0. apply AG; [lia| lia|].
right; right; right; right. exists (fst b), rb. split; [exact Hrb|]. lia.
- intros q rq Hq Hk. destruct (rdr_lookup_inv q rq Hq) as [NE H].
eapply rshadow_rep_ext; [apply rdr_shadow; exact NE|].
destruct (WR q rq H) as (Bq & _ & _ & BCq & _). unfold alloc_ceiling in BCq.
pose proof (OTHER _ _ H NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rq Hk).
assert (AGR : agree_on m m' (r_base rq) (round_up_pg (r_len rq))).
{ intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists q, rq. split; [exact H|]. lia. }
destruct (SH q rq H Hk) as [HWr HB]. split.
+ eapply rwr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AGR| lia| lia].
Qed.

#[using="Type"] Lemma rticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
Proof.
intros [T1 T2]. split.
- intros q sh u hl ch Hq Hu Hin. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
rewrite lookup_delete_ne in Hq by congruence. exact (T1 q sh u hl ch Hq Hu Hin).
- intros q sh pg t Hq Hp. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
rewrite lookup_delete_ne in Hq by congruence. exact (T2 q sh pg t Hq Hp).
Qed.
End DROPREGION.

#[using="Type"] Lemma rmrep_put_group_new : forall st m b g ai r (w8 : byte),
rmrep st m -> (s_groups st) !! b = None ->
(s_regions st) !! (fst b) = Some r -> r_kind r = RKGroup -> 0 <= snd b -> snd b + 16 <= round_up_pg (r_len r) -> snd b mod 16 = 0 ->
rw_cells rsegs m (conc st b) [C8 (pw st (Some g)); C1 w8] -> Z.land (bv_unsigned w8) 31 = Z.land ai 31 ->
rmrep (put_group b (Some g) ai st) m.
Proof.
intros st m b g ai r w8 (WF & CX & GL & AR & GR & SH) Hb Hr Hk B0 B16 BA R Hw8.
pose proof WF as (RS & WR & DJ & WA & WG).
split; [|split; [exact CX|split; [exact GL|split; [exact AR|split; [|exact SH]]]]].
- split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
destruct (decide (b' = b)) as [->|NE].
+ rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists r. auto.
+ rewrite lookup_insert_ne in Hb' by congruence. exact (WG b' gh Hb').
- intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
destruct (decide (b' = b)) as [->|NE].
+ rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists w8. cbn [g_meta g_active_idx]. split; [exact R| exact Hw8].
+ rewrite lookup_insert_ne in Hb' by congruence. exact (GR b' gh Hb').
Qed.

#[using="Type"] Lemma rmrep_set_mmap_counter : forall st m v,
rmrep st m -> 0 <= v < 2^32 ->
rmrep (upd_ctx (set_mmap_counter v) st) (write_to_mem m (wa (RCTX + 12)) (le4 (wz v))).
Proof.
intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6 & X7) & _).
pose proof (length_le4 (wz v)) as L4.
pose proof (munch_write [(RCTX + 12, RCTX + 16)] m m (RCTX + 12) (le4 (wz v)) (munch_refl _ m)
ltac:(unfold RCTX; lia) ltac:(rewrite L4; unfold RCTX; lia) ltac:(rewrite L4; cbn [inside]; lia)) as MU.
pose proof (wmono_write rsegs m m (wa (RCTX + 12)) (le4 (wz v)) (wmono_refl rsegs m)) as WM.
eapply (rmrep_ctx_frameW st (upd_ctx (set_mmap_counter v) st) m _ _ MR MU WM); try reflexivity.
- intros lo hi [E|[]]; inversion E; subst. unfold RCTX. lia.
- left.
pose proof (rw_cells_write rsegs m RCTX (ctx_head_cells st) 12 (C4 (wz (c_mmap_counter (ctx st)))) (C4 (wz v)) X1 eq_refl eq_refl I) as W.
replace (RCTX + Z.of_nat 12) with (RCTX + 12) in W by reflexivity.
unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_mmap_counter c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
cbn [cell_upd csize Nat.eqb Nat.sub cbytes] in W. exact W.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold actives, active, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_active]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold usages, usage, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_usage]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold unmap_seqs, unmap_seq, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_unmap_seq]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold bouncess, bounces, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_bounces]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_seq c_brk]. reflexivity.
Qed.

End RC__1.
End Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg.
Import QCwx.Mq3 QFqQ.Mq1 QQbX.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition RAS_STACK (sc : Z) : Z := 320 + 144 * Z.max 0 (27 - sc).

#[using="Type"] Lemma RAS_STACK_ge sc : 320 <= RAS_STACK sc.
Proof. unfold RAS_STACK. lia. Qed.
#[using="Type"] Lemma RAS_STACK_le sc : 0 <= sc -> RAS_STACK sc <= 4208.
Proof. unfold RAS_STACK. lia. Qed.
#[using="Type"] Lemma RAS_STACK_mono a b : a <= b -> RAS_STACK b <= RAS_STACK a.
Proof. unfold RAS_STACK. lia. Qed.
#[using="Type"] Lemma RAS_STACK_nest sc j : sc < j -> j <= 26 -> RAS_STACK j + 144 <= RAS_STACK sc.
Proof. unfold RAS_STACK. lia. Qed.

Definition ras_post (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
(st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
/\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
/\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
/\ mrel st st1 /\ brk_link_ps st1 s'
/\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ as_inv st0 st st1 sc idx
/\ 0 <= c_mmap_counter (ctx st1) < 2^32
/\ ((idx = -1 /\ errv' = Z_to_bv 64 12)
\/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
rmalloc_fp st0 st1 lo (bv_unsigned sp) a)

/\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Definition ralloc_slot_stmt (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop)
(as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop) : Prop :=
forall (fuel : nat) (R : Type) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
as_pre st0 st sc req fuel ->
rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
(forall st1 idx s' ms',
ras_post as_inv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms') ->
rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).

End RC__1.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QJE4.Mq1 QWTl.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 QdZ1.Mq7 QQbX.Mq5 QdZ1.Mq5.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ram_carve2 : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m0 m : word -> option byte) (junk : list byte) (lo : Z) (st0 st : mstate) (p : aptr) (r : region),
rmrep st m -> mem_inv usegs m -> s_regions st = s_regions st0 ->
(s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
pgal (snd p) -> lr_lo r <= r_base r + snd p ->
(s_areas st) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
0 <= c_secret (ctx st) < 2^64 ->
rw_cells usegs m (conc st p) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)] ->
rw_cells usegs m (conc st p + 24) [CB 4072 (zeros 4072)] ->
rpres_except (ram_fp st0 lo (bv_unsigned sp)) m0 m -> wmono usegs m0 m ->
rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
let stC := upd_ctx (set_meta_area_tail (Some p)) st in
let stD := set_areas (<[p := mkArea (c_secret (ctx st)) None NSLOTS]> (s_areas stC)) stC in
evt usegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(am_took stD (aadd p AREA_HDR) 100) (Z_to_bv 64 (conc st p + 24)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st p)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0c60) fc None m (seg_rom usegs)).
Proof.
intros until r. intros MR MI ER0 Hr NK S0 S1 SAL SLR ANone FRESH SEC HDR0 REST PE0 WM0 FR ST LO LOLE stC stD.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (C1 & _) & _). pose proof WF as (Hres & WR & DJ & WA & WG).
pose proof (conc_region' st p r Hr) as Cp.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold alloc_ceiling in RBC.
pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
unfold ctx_head_cells in C1.
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD in *.

assert (PD : conc st p + 4096 <= 0xe4000 \/ 0x647000 <= conc st p) by lia.
assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
clear RBAL RL0 RB0 RF DR1 DR23 DR2 LRG RU Hres DJ WA WG.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928); (conc st p, conc st p + 4096)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM. unfold RCTX in MU.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 64, RCTX + 72)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
unfold RCTX in MUc.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC : rmrep stC mX) end.
{ eapply (rmrep_ctx_frameW st stC _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx stC upd_ctx s_ctx set_meta_area_tail c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 4. cbn [oconc]. change (conc stC p) with (conc st p). exact C1.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
clear MUc WMc.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(conc st p, conc st p + 4096)]%Z mX) as MUp; pose proof (wmono_refl usegs mX) as WMp end.

st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC3 : rmrep stC mX) end.
{ eapply rmrep_transport_unowned; [exact MRC | exact MUp | exact WMp |].
intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. eapply (rfresh_page_avoids stC _ p r a MRC); try assumption. }
clear MUp WMp MRC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRD : rmrep stD mX) end.
{ unfold stD. eapply (rmrep_new_area stC _ p r (c_secret (ctx st))); try first [exact MRC3 | exact Hr | exact NK | exact S0 | exact S1 | exact SLR | exact ANone | exact FRESH | idtac].
- exact SAL.
- change (conc stC p) with (conc st p). exact HDR0.
- intros k Hk. change (conc stC p) with (conc st p). rewrite meta_cells_meta0.
destruct REST as [[_ B] W]. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
replace (conc st p + AREA_HDR + META_SIZE * k) with ((conc st p + 24) + 40 * k) by (unfold AREA_HDR, META_SIZE; lia).
eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 (40 * k)); [exact B| exact W| cbn; tauto| reflexivity| lia| cbn [cells_size csize Nat.add]; unfold NSLOTS in Hk; lia].
- change (conc stC p) with (conc st p).
destruct REST as [[_ B] W]. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
replace (conc st p + 4064) with ((conc st p + 24) + 4040) by lia.
eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 4040); [exact B| exact W| cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| lia| cbn [cells_size csize Nat.add]; lia]. }
clear MRC3 HDR0 REST.
assert (MSq : meta_slot stD (aadd p AREA_HDR)).
{ exists p, (mkArea (c_secret (ctx st)) None NSLOTS), 0. split; [| split; [unfold NSLOTS; lia| unfold AREA_HDR, META_SIZE; rewrite Z.mul_0_r, Z.add_0_r; reflexivity]].
unfold stD. cbn [s_areas set_areas]. rewrite lookup_insert_eq. reflexivity. }
assert (CQ : conc st p + 24 = conc stD (aadd p AREA_HDR)).
{ change (conc stD (aadd p AREA_HDR)) with (conc st (aadd p AREA_HDR)). rewrite (conc_aadd st p AREA_HDR) by (rewrite Hr; eauto). reflexivity. }
rewrite CQ. change (Z_to_bv 64 6575456) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 6576288) with (Z_to_bv 64 RMLOCK).
eapply evt_mono.
{ eapply (ram_b0 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo 100 stD (aadd p AREA_HDR));
[exact MRD | assumption | exact MSq | lia | | | unfold alloc_ceiling; lia | lia].
- lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk usegs ?mX lo _ |- _ => exact H end. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [exact PE0|].
apply (rpres_except_of_munch_cov (ram_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha.
apply (proj1 (ram_fp_same st0 stD lo _ a ltac:(rewrite <- ER0; reflexivity))). exact Ha.
- cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
+ intros x Hx. eapply (ram_fp_region st0 lo _ x (fst p) r); [rewrite <- ER0; exact Hr| exact NK|].
pose proof (lr_lo_ge r). lia. }

split; [eapply wmono_trans; [exact WM0| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

#[using="Type"] Lemma ram_carve_walk : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (p : aptr) (r : region),
rmrep st m -> mem_inv usegs m ->
(s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
pgal (snd p) -> lr_lo r <= r_base r + snd p ->
(s_areas st) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
(forall tl, c_meta_area_tail (ctx st) = Some tl -> is_Some ((s_areas st) !! tl)) ->
1 <= c_avail_meta_area_count (ctx st) < 2^64 -> 0 <= c_secret (ctx st) < 2^64 ->
bytes_at usegs m (conc st p) (zeros 4096) -> wr_at usegs m (conc st p) 4096 ->
rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt usegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo (carve_st st p) m
(am_took (carve_st st p) (aadd p AREA_HDR) 100) (Z_to_bv 64 (conc st p + 24)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st p)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0c34) fc None m (seg_rom usegs)).
Proof.
intros until r. intros MR MI Hr NK S0 S1 SAL SLR ANone FRESH TL CNT SEC ZB ZW FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (C1 & _) & _ & AR & _). pose proof WF as (Hres & WR & DJ & WA & WG).
pose proof (conc_region' st p r Hr) as Cp.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold alloc_ceiling in RBC.
pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
unfold ctx_head_cells in C1.

assert (HDR0 : rw_cells usegs m (conc st p) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)]).
{ rewrite <- (Z.add_0_r (conc st p)). eapply (rrw_cells_of_zeros m (conc st p) 4096 0); [exact ZB| exact ZW| cbn; tauto| reflexivity| lia| cbn; lia]. }
assert (REST : rw_cells usegs m (conc st p + 24) [CB 4072 (zeros 4072)]).
{ eapply (rrw_cells_of_zeros m (conc st p) 4096 24); [exact ZB| exact ZW| cbn [cells_wf]; split; [first [reflexivity | apply zeros_length]| exact I] | cbn [cells_bytes cbytes cells_size csize Nat.add]; rewrite app_nil_r; reflexivity| lia| cbn; lia]. }
clear ZB ZW.
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD in *.
assert (PD : conc st p + 4096 <= 0xe4000 \/ 0x647000 <= conc st p) by lia.
assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
clear RBAL RL0 RF DR1 DR23 DR2 RU.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928); (conc st p, conc st p + 4096)]%Z m) as MU0.
pose proof (wmono_refl usegs m) as WM0. unfold RCTX in MU0.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
unfold RCTX in MUc.

st1. st1. st1. st1. st1. st1. st1.
set (st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
{ eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 5. cbn [oconc]. change (conc st1 (aadd p 4096)) with (conc st (aadd p 4096)).
rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz at 6 7.
lazymatch goal with H : rw_cells usegs ?mX 6576296 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
clear MUc WMc.

st1.
destruct (c_meta_area_tail (ctx st)) as [tl|] eqn:HT.
-
destruct (TL tl eq_refl) as [ar Har].
destruct (rarea_conc st tl ar WF Har) as (rt & Hrt & Ct & St0 & St1 & StL & NKt & RBt & RBAt & RBCt). unfold alloc_ceiling in RBCt.
pose proof (rarea_lr_lo st tl ar rt WF Har Hrt) as LRt.
destruct (WR _ _ Hrt) as (_ & _ & _ & _ & RFt). destruct (rreserved_disjoint _ _ RFt) as (DT1 & _ & DT23 & DT2).
assert (TD : conc st tl + 4096 <= 0xe4000 \/ 0x647000 <= conc st tl) by lia.
assert (TB : 0 < conc st tl /\ conc st tl + 4096 <= lo) by lia.
assert (TP : conc st tl + 4096 <= conc st p \/ conc st p + 4096 <= conc st tl).
{ destruct (N.eq_dec (fst tl) (fst p)) as [E|NE].
- rewrite E, Hr in Hrt. assert (rt = r) by congruence. subst rt.
assert (NEo : snd tl <> snd p) by (intros E2; assert (tl = p) by (destruct tl, p; cbn in *; congruence); subst tl; rewrite ANone in Har; discriminate).
unfold pgal in SAL. clear - Ct Cp NEo SAL StL E. Z.div_mod_to_equations. lia.
- destruct (DJ _ _ _ _ Hrt Hr NE); lia. }
clear RBAt StL RFt DT1 DT23 DT2 St0 St1 LRt RBt RBCt DJ WA WG.
unfold pw. cbn [oconc]. unfold wz.
assert (CF : bv_eqb (Z_to_bv 64 (conc st tl)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF. clear CF.
pose proof MR1 as (_ & _ & _ & AR1 & _). destruct (AR1 tl ar Har) as (ARh & _ & _). clear AR1.
change (conc st1 tl) with (conc st tl) in ARh.
apply (munch_grow2 _ (conc st tl, conc st tl + 4096)) in MU0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(conc st tl + 8, conc st tl + 16)]%Z mX) as MUa; pose proof (wmono_refl usegs mX) as WMa end.

st1. st1.
set (st2 := set_areas (<[tl := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st1)) st1).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
{ eapply (rmrep_set_area_next st1 _ _ tl ar p MR1 Har); [cbn; rewrite Hr; eauto| exact MUa| exact WMa|].
change (conc st1 tl) with (conc st tl). change (conc st1 p) with (conc st p). unfold wz at 2. exact ARh. }
clear MUa WMa ARh MR1.
rewrite (carve_st_some st p tl ar HT Har ANone). cbv zeta. fold st1. fold st2.
change (Z_to_bv 64 6575456) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 6576288) with (Z_to_bv 64 RMLOCK).
eapply evt_mono.
{ eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
first [exact MR2 | reflexivity | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact FRESH | exact SEC | exact WM0 | idtac].
- lazymatch goal with H : mem_inv usegs ?mX |- _ => exact H end.
- cbn [s_areas set_areas upd_ctx st2 st1]. rewrite lookup_insert_ne; [exact ANone|]. intros ->. rewrite ANone in Har; discriminate.
- lazymatch goal with H : rw_cells usegs ?mX (conc st p) _ |- _ => exact H end.
- lazymatch goal with H : rw_cells usegs ?mX (conc st p + 24) _ |- _ => exact H end.
- apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [exact MU0|exact WM0|].
cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. eapply ram_fp_area; [exact MR| exact Har| lia].
+ intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
+ intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [exact Hr| exact NK| lia].
- lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk usegs ?mX lo _ |- _ => exact H end.
- unfold alloc_ceiling; lia.
- lia. }
intros ms' RP. exact RP.
-
unfold pw. cbn [oconc]. unfold wz.
change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 56, RCTX + 64)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
unfold RCTX in MUc.

st1.
set (st2 := upd_ctx (set_meta_area_head (Some p)) st1).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
{ eapply (rmrep_ctx_frameW st1 st2 _ _ _ MR1 MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx st2 st1 upd_ctx s_ctx set_meta_area_head set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
rewrite HT. unfold pw. cbn [oconc]. change (conc st2 ?q) with (conc st q). change (conc st2 p) with (conc st p).
rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz.
lazymatch goal with H : rw_cells usegs ?mX 6576296 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
clear MUc WMc MR1.
rewrite (carve_st_none st p HT ANone). cbv zeta. fold st1. fold st2.
change (Z_to_bv 64 6575456) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 6576288) with (Z_to_bv 64 RMLOCK).
eapply evt_mono.
{ eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
first [exact MR2 | reflexivity | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact ANone | exact FRESH | exact SEC | exact WM0 | idtac].
- lazymatch goal with H : mem_inv usegs ?mX |- _ => exact H end.
- lazymatch goal with H : rw_cells usegs ?mX (conc st p) _ |- _ => exact H end.
- lazymatch goal with H : rw_cells usegs ?mX (conc st p + 24) _ |- _ => exact H end.
- apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [exact MU0|exact WM0|].
cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
+ intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [exact Hr| exact NK| lia].
- lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk usegs ?mX lo _ |- _ => exact H end.
- unfold alloc_ceiling; lia.
- lia. }
intros ms' RP. exact RP.
Qed.

End RC__1.
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 QJE4.Mq3 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QWTl.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 QdZ1.Mq7 QQbX.Mq6 QQbX.Mq5.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ctx_cells_cbn :=
cbn [ctx set_head upd_ctx s_ctx set_free_meta_head set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ram_deq : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (h nx pv : aptr),
rmrep st m -> mem_inv usegs m ->
c_free_meta_head (ctx st) = Some h -> meta_slot st h ->
m_next (get_meta_rec st h) = Some nx -> m_prev (get_meta_rec st h) = Some pv ->
meta_slot st nx -> meta_slot st pv -> (nx = h <-> pv = h) ->
rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt usegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (dequeue LFree h st) (Z_to_bv 64 (conc st h)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0ad0) fc None m (seg_rom usegs)).
Proof.
intros until pv. intros MR MI FMH MSh HN HP MSn MSp SELF FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m h MR MSh) as (HB0 & HB1 & HB2 & _).
pose proof (rmeta_slot_bounds st m nx MR MSn) as (NB0 & NB1 & NB2 & _).
pose proof (rmeta_slot_bounds st m pv MR MSp) as (PB0 & PB1 & PB2 & _).
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH in C1.
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD in *.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st h, conc st h + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (6576296, 6576296 + 928)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.

unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
st1. st1.
assert (CF : bv_eqb (Z_to_bv 64 (conc st h)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.

rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.

st1. if_cases K; zify_cond K.
-
assert (Enx : nx = h).
{ rewrite ?unsigned_lit in K by lia. exact (rconc_meta_inj st m h nx MR MSh MSn ltac:(first [exact K | symmetry; exact K])). }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
unfold RCTX in MUc.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep (set_head LFree None st) mX) end.
{ eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold ctx_head_cells, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. unfold pw. unfold wz at 4.
lazymatch goal with H : rw_cells usegs ?mX 6576296 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.
st1.
assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree None st)).
{ rewrite dequeue_mid. unfold deq_mid. rewrite HN, <- Enx, optr_eqb_refl. reflexivity. }
rewrite EQ.
change (conc st h) with (conc (set_head LFree None st) h). change (Z_to_bv 64 6575456) with (Z_to_bv 64 RSSP_GUARD).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree None st) h);
[exact MR1 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | unfold alloc_ceiling; lia | lia].
- lazymatch goal with H : mem_inv usegs ?mX |- _ => exact H end.
- lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk usegs ?mX lo _ |- _ => exact H end. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
- cbn [ivs_covered]. repeat split; intros x Hx.
+ apply ram_fp_stack. lia.
+ eapply ram_fp_meta; [exact MR | exact MSh | lia].
+ eapply ram_fp_meta; [exact MR | exact MSp | lia].
+ eapply ram_fp_meta; [exact MR | exact MSn | lia].
+ apply ram_fp_ctx. unfold RCTX. lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
-
assert (NEn : nx <> h) by (intros ->; apply K; reflexivity).
assert (NEp : pv <> h) by (intros E; apply NEn; apply (proj2 SELF); exact E).

rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.

rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR MSp CH.
st1.
rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 HP HN.
set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh).
assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).

rmeta_chunk MR1 MSh1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
rewrite HN, HP in CH. cbn [oconc] in CH.
st1. st1. clear CH.

rmeta_open (conc st nx) MUn WMn.
rmeta_chunk MR1 MSn1 CH.
st1.
rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 HP HN.
set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).

st1. st1.
rewrite bv_eqb_refl. cbn [negb]. cbv iota.

rmeta_chunk MR2 MSh2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.

clear C1. pose proof MR2 as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1.
replace (c_free_meta_head (ctx st2)) with (Some h) in C1 by (symmetry; exact FMH).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
unfold RCTX in MUc.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR3 : rmrep (set_head LFree (Some nx) st2) mX) end.
{ eapply (rmrep_ctx_frameW st2 _ _ _ _ MR2 MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold ctx_head_cells, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. change (conc (set_head LFree (Some nx) st2) nx) with (conc st nx).
unfold pw. unfold wz at 4.
lazymatch goal with H : rw_cells usegs ?mX 6576296 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.

st1.
assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree (Some nx) st2)).
{ rewrite dequeue_mid. unfold deq_mid. rewrite HN, HP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx h NEn). cbn [negb get_head].
rewrite !upd_meta_put. fold st1. fold st2. rewrite ctx_put_meta. unfold st1. rewrite ctx_put_meta. rewrite FMH, optr_eqb_refl. reflexivity. }
rewrite EQ.
change (conc st h) with (conc (set_head LFree (Some nx) st2) h). change (Z_to_bv 64 6575456) with (Z_to_bv 64 RSSP_GUARD).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree (Some nx) st2) h);
[exact MR3 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | unfold alloc_ceiling; lia | lia].
- lazymatch goal with H : mem_inv usegs ?mX |- _ => exact H end.
- lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk usegs ?mX lo _ |- _ => exact H end. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
- cbn [ivs_covered]. repeat split; intros x Hx.
+ apply ram_fp_stack. lia.
+ eapply ram_fp_meta; [exact MR | exact MSh | lia].
+ eapply ram_fp_meta; [exact MR | exact MSp | lia].
+ eapply ram_fp_meta; [exact MR | exact MSn | lia].
+ apply ram_fp_ctx. unfold RCTX. lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

#[using="Type"] Lemma ram_take_walk : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (q : aptr),
rmrep st m -> mem_inv usegs m ->
c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) <> 0 -> 0 <= c_avail_meta_count (ctx st) < 2^64 ->
c_avail_meta (ctx st) = Some q -> meta_slot st q ->
rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt usegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m
(am_took st q (c_avail_meta_count (ctx st) - 1)) (Z_to_bv 64 (conc st q)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0ad0) fc None m (seg_rom usegs)).
Proof.
intros until q. intros MR MI FMH CNT CR AVM MSq FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m q MR MSq) as (QB0 & QB1 & QB2 & _).
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH, AVM in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD in *.

st1. st1.
rewrite bv_eqb_refl. cbv iota.
st1. st1.
assert (CF : bv_eqb (Z_to_bv 64 (c_avail_meta_count (ctx st))) (Z_to_bv 64 0) = false)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact CNT).
rewrite CF; clear CF.
st1. st1. st1. rewrite ?(unsigned_lit (c_avail_meta_count (ctx st))) by lia.
replace (c_avail_meta_count (ctx st) + -1) with (c_avail_meta_count (ctx st) - 1) by lia.
change (Z_to_bv 64 6575456) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 6576288) with (Z_to_bv 64 RMLOCK).
eapply (ram_b0 sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m junk lo _ st q);
[exact MR | exact MI | exact MSq | lia | exact FR | exact ST | unfold alloc_ceiling; lia | lia].
Qed.

#[using="Type"] Lemma ram_disp0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate),
rmrep st m -> c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) = 0 ->
evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0b24) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0ad0) fc None m (seg_rom usegs)).
Proof.
intros until st. intros MR FMH CNT.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH, CNT in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1. unfold RCTX, RMLOCK in *.
st1. st1. rewrite bv_eqb_refl. cbv iota.
st1. st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. reflexivity.
Qed.

End RC__1.
End Mqd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeTw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import QeTw.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QJE4.Mq1 QWTl.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 QdZ1.Mq7 QQbX.Mq5.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmemcpy_callZ3 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
bytes_at usegs m S src -> length src = Z.to_nat n ->
rw_cells usegs m D [CB (Z.to_nat n) junk] ->
0 <= D -> D + n <= 2^64 -> 0 <= S -> S + n <= 2^64 -> 0 < n ->
(S + n <= D \/ D + n <= S) ->
mem_inv usegs m ->
evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(D, D + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' D [CB (Z.to_nat n) src])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdda10) fc None m (seg_rom usegs)).
Proof.
intros until junk. intros SRC LEN DST D0 D1 S0 S1 N0 SEP MI.
assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)); rewrite ?ED, ?ES, ?EN;
[exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
intros ms' P. unfold memcpy_post in P. rewrite !ED, !EN in P.
destruct P as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m' & -> & MU & WM & MI' & DST' & _).
do 15 eexists. split; [reflexivity|]. auto.
Qed.

#[using="Type"] Lemma ru64s_read : forall m A ws (i : Z) w a,
bytes_at usegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 8 * i) ->
ov_read_bytes usegs m a 8 = Some (le8 w).
Proof.
intros m A ws i w a Hb Hn Hi ->.
destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read usegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma rrw_cells_app_split : forall m A cs1 cs2,
rw_cells usegs m A (cs1 ++ cs2) -> rw_cells usegs m A cs1 /\ rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros m A cs1 cs2 H. split; [eapply rw_cells_prefix; exact H|].
destruct H as [[WF B] W].
apply cells_wf_app in WF. destruct WF as [WF1 WF2].
rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [_ B2]. rewrite cells_bytes_length in B2 by exact WF1.
split; [split; [exact WF2 | exact B2] |].
rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

#[using="Type"] Lemma rrw_cells_app_join : forall m A cs1 cs2,
rw_cells usegs m A cs1 -> rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells usegs m A (cs1 ++ cs2).
Proof.
intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
- apply cells_wf_app. split; assumption.
- rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact WF1. exact B2.
- rewrite cells_size_app. destruct W1 as (H0 & H1 & X1). destruct W2 as (H2 & H3 & X2). split; [lia|]. split; [lia|].
intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
+ apply X1. lia.
+ replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply X2. lia.
Qed.

Definition ram_entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0ad0) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)
/\ stk usegs m' lo (bv_unsigned sp + -64)
/\ rmrep (am_init_st st) m'.

#[using="Type"] Lemma ram_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (lo : Z) (st : mstate),
rmrep st m -> mem_inv usegs m -> rauxv_ok m (bv_unsigned sp) ->
stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
c_init_done (ctx st) = 1 -> s_secret st = rc_secret ->    0 <= c_secret (ctx st) < 2^64 ->
evt usegs (ram_entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0a1c) fc None m (seg_rom usegs)).
Proof.
intros until st. intros MR MI AUX ST LO LOLE INIT SEC0 SECR.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (C1 & _) & (_ & _ & PGS & G4 & G5 & G6) & _). unfold ctx_head_cells in C1.
unfold alloc_ceiling, RCTX, RGOT_SSP, RSSP_GUARD, RPAGE_SIZE in *. unfold wz in G4.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM. unfold RCTX in MU.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUh.

st1. carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.

st1. st1. st1. st1. st1. st1.

st1. rewrite sx32_wz by lia. st1. st1.

st1.
lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
rename INIT into I1.
{
rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|].
unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]. intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia. }
Qed.

End RC__1.
End Mqe.

Module Mqf.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq4.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 Q98Z.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := unfold alloc_ceiling, UNIT, IB in *; lia.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma zx32_wz x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. intros. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

#[using="Type"] Lemma meta_word_sc2 mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 5) 126 = 2 * m_sizeclass mr.
Proof.
intros (LI & FB & SCR & ML).
assert (E : 126 = Z.ldiff (Z.ones 7) (Z.ones 1)) by reflexivity. rewrite E, land_ldiff_distr.
rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
change (2^7) with 128. change (2^1) with 2. change (2^5) with 32. unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.div_add, (Z.div_small (m_last_idx mr)) by lia.
replace (0 + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr)) with ((m_freeable mr + 2 * m_sizeclass mr) + m_maplen mr * 128) by lia.
rewrite Z.mod_add, Z.mod_small by lia.
replace (m_freeable mr + 2 * m_sizeclass mr) with (m_freeable mr + m_sizeclass mr * 2) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed.

#[using="Type"] Lemma meta_word_pg mr : mw_ok mr -> meta_word mr - meta_word mr mod 4096 = 4096 * m_maplen mr.
Proof.
intros (LI & FB & SCR & ML). unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

Definition rfhead_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st1 : mstate) (g : aptr) (idx li : Z) : machine_state -> Prop :=
fun ms' => exists x1 x5 x6 x7 junk m',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (li + 1) - 1))) (Z_to_bv 64 0x645468) x5 x6 x7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd046c) fc None m' (seg_rom usegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp + -48)
/\ rw_cells usegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rmrep st1 m'.

#[using="Type"] Lemma rfree_head3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
(m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (b3 lo8 hi E rsv : Z),
let po := snd p in
let idx := Z.land b3 31 in
let mr := get_meta_rec st g in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
rmrep st m0 -> mem_inv usegs m0 -> ticks_ok st ->
stk usegs m0 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
rw_cells usegs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono usegs m m0 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
meta_slot st g ->
cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
0 <= b3 < 256 ->
r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
0 <= rsv <= E - (r_base r + po) -> bytes_at usegs m0 (E - rsv) [b8 0] -> bytes_at usegs m0 E [b8 0] ->
(forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
evt usegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
(Z_to_bv 64 E) a3 (wz rsv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd041c) fc None m0 (seg_rom usegs)).
Proof.
intros until rsv. intros po idx mr st1 MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL HK3 HK2 HK1 LI FBL SC ML B3 ELO EHI RSV RB0r RE0 HCLR.
pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
unfold alloc_ceiling, UNIT, IB in *.
pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
pose proof (munch_refl [(r_base r + po - 3, r_base r + po)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.
pose proof (bytes_at_read usegs m0 _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
pose proof (bytes_at_read usegs m0 _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.

st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }

st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }

change (Z_to_bv 64 E) with (wa E).
st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }

st1. st1. st1. st1. st1. st1.
rewrite (unsigned_lit idx) by lia. rewrite sllw1_word' by lia. rewrite (wz_unsigned (meta_word mr)) by (unfold meta_word; lia).

pose proof MR1 as (_ & _ & _ & _ & _ & SH1). destruct (SH1 (fst p) r Hr Hk) as [HWr _]. clear SH1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (SOK3 : store_ok usegs mX (wa (bv_unsigned a0 + -3)) 1 = true)
by (replace (bv_unsigned a0 + -3) with (r_base r + (po - 3)) by lia; apply (wr_at_store_ok usegs mX _ _ (po - 3) 1 HWr); cbn; lia) end.
st1.
pose proof (rmrep_wr8 st _ (aadd p (-3)) 255 r MR1 TK Hr Hk ltac:(cbn; lia)
ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR2.
cbn [aadd snd] in MR2. fold po in MR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -3))) [b8 255])
by (rewrite le1_neg1; f_equal; unfold wa; f_equal; lia) end.
store_done.
pose proof (ticks_ok_wr8 st (aadd p (-3)) 255 TK) as TK2.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof MR2 as (_ & _ & _ & _ & _ & SH2); destruct (SH2 (fst p) r Hr Hk) as [HWr2 _]; clear SH2;
assert (SOK2 : store_ok usegs mX (wa (bv_unsigned a0 + -2)) 2 = true)
by (replace (bv_unsigned a0 + -2) with (r_base r + (po - 2)) by lia; apply (wr_at_store_ok usegs mX _ _ (po - 2) 2 HWr2); cbn; lia) end.
st1.
pose proof (rmrep_wr16 _ _ (aadd p (-2)) 0 r MR2 TK2 Hr Hk ltac:(cbn; lia) ltac:(cbn; lia)
ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR3.
cbn [aadd snd] in MR3. fold po in MR3. fold st1 in MR3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -2))) (le2 (wz 0)))
by (f_equal; unfold wa; f_equal; lia) end.
store_done. clear MR2 TK2 HWr HWr2.

st1. rewrite (all_word (meta_word mr)) by (unfold meta_word; lia).
replace (meta_word mr mod 32) with (m_last_idx mr) by (unfold meta_word; Z.div_mod_to_equations; lia).
st1.

apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|exact I].
intros x Hx. right. right. exists (fst p), r.
assert (CASES : x - r_base r = po - 3 \/ x - r_base r = po - 2 \/ x - r_base r = po - 1) by lia.
destruct CASES as [E1|[E1|E1]]; [exists b3| exists lo8| exists hi]; rewrite E1; (split; [exact Hr|]); (split; [exact Hk|]); (split; [lia|]); assumption. }
apply evt_done. unfold rfhead_post.
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
do 6 eexists.
split; [reflexivity|].
split; [eapply rpres_except_trans; [exact PE0| exact MU]|]. split; [exact WM0|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. exact MR3.
Qed.

#[using="Type"] Lemma rfree_head2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
(m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (base : aptr) (b3 lo8 hi r32 : Z),
let po := snd p in
let idx := Z.land b3 31 in
let mr := get_meta_rec st g in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
let stride := get_stride mr in
let E := conc st base + UNIT + stride * idx + stride - IB in
let rsv0 := Z.shiftr b3 5 in
let rsv := if 160 <=? b3 then r32 else rsv0 in
rmrep st m0 -> mem_inv usegs m0 -> ticks_ok st ->
stk usegs m0 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
rw_cells usegs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono usegs m m0 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
meta_slot st g -> m_mem mr = Some base -> fst base = fst p -> 0 <= snd base ->
cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
0 <= b3 < 256 -> idx <= m_last_idx mr ->
UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
(160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at usegs m0 (E - 4) (le4 (wz r32)) /\ bytes_at usegs m0 (E - 5) [b8 0]) ->
rsv <= E - (r_base r + po) -> bytes_at usegs m0 (E - rsv) [b8 0] -> bytes_at usegs m0 E [b8 0] ->
(forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
evt usegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
(Z_to_bv 64 stride) (wz b3) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd03d4) fc None m0 (seg_rom usegs)).
Proof.
intros until r32. intros po idx mr st1 stride E rsv0 rsv MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL Hmem FB SB0 HK3 HK2 HK1
AV FRD LI FBL SC ML B3 Hidx S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
assert (RSV0 : 0 <= rsv0 < 8).
{ unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
assert (RSVR : 0 <= rsv < 2^32).
{ unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
unfold alloc_ceiling, UNIT, IB in *.
pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (rmrep_meta_chunk st m0 g MR1 MSL) as MM.
fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.

st1. st1. st1. st1. st1. st1. st1. cbn [oconc].
replace (conc st base + stride + stride * idx + 12) with E by (unfold E; lia).
fold rsv0.

st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
-
replace (Z_to_bv 64 rsv0) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
subst mr.
eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
[exact MR1| exact MI| exact TK| exact ST| unfold alloc_ceiling; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
| exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
-
destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
pose proof (bytes_at_read usegs m0 _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
cbn [skipn Z.to_nat] in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
replace (E - 4) with (conc st base + stride + stride * idx + 8) in RD4 by (unfold E; lia).
pose proof (bytes_at_read usegs m0 _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.
replace (E - 5) with (conc st base + stride + stride * idx + 7) in RD5 by (unfold E; lia).

st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }

st1.
rewrite zx32_wz by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }

st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
replace (wz r32) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
subst mr.
eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
[exact MR1| exact MI| exact TK| exact ST| unfold alloc_ceiling; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
| exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
Qed.

#[using="Type"] Lemma rfree_head : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(lo : Z) st (p : aptr) r g gh ar (b3 lo8 hi r32 : Z),
let sh := get_shadow st (fst p) in
let po := snd p in
let off16 := lo8 + 256 * hi in
let idx := Z.land b3 31 in
let base := aadd p (- (UNIT * off16) - UNIT) in
let mr := get_meta_rec st g in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
let stride := get_stride mr in
let E := conc st base + UNIT + stride * idx + stride - IB in
let rsv0 := Z.shiftr b3 5 in
let rsv := if 160 <=? b3 then r32 else rsv0 in
rmrep st m -> mem_inv usegs m -> ticks_ok st ->
stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
cell_read sh (po - 2) = Known lo8 -> cell_read sh (po - 1) = Known hi ->
(s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
m_mem mr = Some base ->
(s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
(m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
(48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
(m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->

(m_maplen mr = 0 \/ m_last_idx mr <> 0 -> m_sizeclass mr < 48) ->
UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
(160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at usegs m (E - 4) (le4 (wz r32)) /\ bytes_at usegs m (E - 5) [b8 0]) ->
rsv <= E - (r_base r + po) -> bytes_at usegs m (E - rsv) [b8 0] -> bytes_at usegs m E [b8 0] ->
(forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
evt usegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom usegs)).
Proof.
intros until r32. intros sh po off16 idx base mr st1 stride E rsv0 rsv MR MI TK ST LO SLO Hr Hk HP AL P16 PLO PHI HK4 HK3 HK2 HK1 Hgh Hg MSL G0 Hmem Har Hchk
AV FRD SE LI FBL SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48 S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MUs.
pose proof (wmono_refl usegs m) as WM.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) HK3) as [_ B3].
assert (RSV0 : 0 <= rsv0 < 8).
{ unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
assert (RSVR : 0 <= rsv < 2^32).
{ unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
assert (FB : fst base = fst p) by reflexivity.
assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
assert (SB0 : 0 <= snd base) by (unfold base; cbn; unfold UNIT; lia).

revert BIG RB0r RE0.
unfold rfree_entry, alloc_ceiling, UNIT, IB in *. intros BIG RB0r RE0.

st1. if_cases K0; zify_cond K0. { exfalso. lia. }
carve_frame 48%nat ST.
st1. st1. st1. st1. st1. st1. st1.

st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM |]; intros l h [E1|[]]; inversion E1; subst; unfold alloc_ceiling; lia) end.
eapply evt_cut.
{ eapply rget_meta_spec with (st := st) (p := p) (r := r) (g := g) (gh := gh) (ar := ar) (b3 := b3) (lo := lo8) (hi := hi).
all: try eassumption. all: try lia. }
intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
replace (ret_pc (Z_to_bv 64 0xd038c)) with (Z_to_bv 64 0xd038c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rmrep_meta_chunk st mX g MR1 MSL) as MM;
destruct (rmrep_shadow_read st mX (fst p) r (po - 3) b3 MR1 Hr Hk ltac:(lia) HK3) as [R3 _] end.
fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
replace (r_base r + (po - 3)) with (bv_unsigned a0 + -3) in R3 by lia.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
assert (MW : mw_ok mr) by (unfold mw_ok; lia).
pose proof (meta_word_range mr MW) as MWR. pose proof (meta_word_maplen mr MW) as MW12.
pose proof (meta_word_last_idx mr MW) as MW31. pose proof (meta_word_sc2 mr MW) as MWS. pose proof (meta_word_pg mr MW) as MWP.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (K2 : forall a4v a5v a6v, evt usegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR (Z_to_bv 64 0xd038c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
(Z_to_bv 64 stride) (wz b3) a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd03d4) fc None mX (seg_rom usegs))) end.
{ intros a4v a5v a6v.
lazymatch type of MUs with munch ?W _ _ => assert (DJ : forall A n, A + n <= lo -> disjoint_from W A n) by (intros A n HA; cbn; lia) end.
lazymatch type of MUs with munch ?W m ?mY =>
assert (PE0 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m mY)
by (apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp)) W); [exact MUs| exact WM|];
cbn [ivs_covered]; split; [|exact I]; intros x Hx; apply rfree_fp_stack; lia) end.
subst rsv rsv0 E stride mr.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
eapply (rfree_head2 ra sp gp tp t0 t1 t2 s0 s1 a0 a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ F fc m mX _ lo st p r g base b3 lo8 hi r32) end;
[exact MR1| assumption| exact TK| exact ST| ulia| ulia| exact FR| exact PE0| exact WM| exact Hr| exact Hk| exact HP| exact AL| ulia| ulia
| exact MSL| exact Hmem| exact FB| exact SB0| exact HK3| exact HK2| exact HK1| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia
| intros Hb3; destruct (BIG Hb3) as (X1 & X2 & X3 & X4); split; [exact X1|]; split; [exact X2|]; split;
(eapply bytes_at_transport; [eassumption| exact MUs| apply DJ; cbn; try rewrite length_le4; ulia])
| ulia
| exact RB0r
| exact RE0
| exact HCLR]. }

st1. st1. st1. st1. fold idx. rewrite MW12.
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned).

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (KS : forall a2v a4v, (m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
evt usegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR (Z_to_bv 64 0xd038c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 gw (wz (meta_word mr))
a2v (wz b3) a4v ga5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd03b8) fc None mX (seg_rom usegs))) end.
{ intros a2v a4v COND. specialize (SC48 COND).
assert (STR : stride = 16 * size_class (m_sizeclass mr)).
{ unfold stride, get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }

assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
st1. st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite MWS. st1. st1.
replace (159656 + m_sizeclass mr * 2) with (159656 + 2 * m_sizeclass mr) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (RS' : ov_read_bytes usegs mX (Z_to_bv 64 (159656 + 2 * m_sizeclass mr)) 2 = Some (le2 (wz (size_class (m_sizeclass mr))))) end.
{ replace (Z_to_bv 64 (159656 + 2 * m_sizeclass mr)) with (wa (RSIZE_CLASSES + 2 * m_sizeclass mr)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
apply rsize_classes_read; [assumption| lia]. }
pose proof (size_class_range (m_sizeclass mr) ltac:(lia)) as SZ.
st1. try rewrite (Z.mod_small (size_class (m_sizeclass mr))) by lia.
st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
replace (Z_to_bv 64 (size_class (m_sizeclass mr) * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
rewrite Egw. apply K2. }

st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
- apply KS. left. exact Km.
-
st1. rewrite MW31. st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
+ apply KS. right. exact Kl.
+
st1. st1. rewrite land_pgmask by lia. rewrite MWP. st1. st1.
replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 stride).
2:{ unfold stride, get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
rewrite Egw. apply K2.
Qed.

End RC__1.
End Mqf.

Module Mqg.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq5.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 Q98Z.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rfree_fp_meta0 : forall st st0 m lo sp q a, rmrep st m -> meta_slot st q -> s_regions st0 = s_regions st ->
conc st q <= a < conc st q + 40 -> rfree_fp st0 lo sp a.
Proof.
intros st st0 m lo sp q a MR (ar & arr & k & Har & Hk & Eq) ER Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
eapply rfree_fp_region; [rewrite ER; exact Hra | exact NK | lia].
Qed.

Definition rftriv_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (C : Z -> Prop) (m : word -> option byte) (st' : mstate) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ rpres_except C m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rmrep st' m'.

#[using="Type"] Lemma rfree_triv : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st0 st : mstate) (g : aptr) (idx : Z),
let mr := get_meta_rec st g in
let st' := upd_meta g (m_set_freed (m_freed mr + bit idx)) st in
rmrep st m -> mem_inv usegs m -> meta_slot st g ->
s_regions st = s_regions st0 -> s_areas st = s_areas st0 ->
0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
m_freed mr <> 0 -> Z.lor (m_freed mr) (m_avail mr) + bit idx <> mask_upto (m_last_idx mr) ->
rw_cells usegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk usegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt usegs (rftriv_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (rfree_fp st0 lo (bv_unsigned sp)) m st')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 0x645468) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd046c) fc None m (seg_rom usegs)).
Proof.
intros until idx. intros mr st' MR MI MSL ER EA HF HA HL HI TF TA Hfz Hall FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
pose proof (wmono_refl usegs m) as WM.
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
clearbody gw.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
unfold alloc_ceiling, RNEED_LOCKS in *.

step. step. rewrite !sx32_wz_sxv by lia.

step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.

step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.land_comm _ (sxv (2 ^ idx))).
rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).

step. if_true.

st1.

step. if_cases K2; zify_cond K2.
{ exfalso. apply Hfz. apply (proj1 (sxv_zero (m_freed mr) ltac:(lia))). first [exact K2 | rewrite wz_unsigned in K2 by assumption; exact K2]. }
clear K2.

step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
step. if_cases K3; zify_cond K3.
{ exfalso. apply Hall. unfold bit, mask_upto. apply (proj1 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
rewrite !wz_unsigned in K3 by apply sxv_range. exact K3. }
clear K3 RSUM.

step. rewrite (wz_unsigned (sxv (2 ^ idx))), (wz_unsigned (sxv (m_freed mr))) by assumption.
rewrite (Z.add_comm (sxv (m_freed mr)) (sxv (2 ^ idx))). rewrite addw_word.
step. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
clear K4 RL.

step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR' : rmrep st' mX) end.
{ unfold st'. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
rewrite HG in MM.
eapply rw_cells_congr; [ | | | exact MM].
- unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
unfold bit. rewrite (free_store_val (m_freed mr) idx) by (assumption || lia). reflexivity.
- reflexivity.
- cbn. tauto. }
clear MUg MM.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z mX) as MUs;
pose proof (wmono_refl usegs mX) as WMs end.
step. step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MR' MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
- intros x Hx. apply rfree_fp_stack. lia.
- intros x Hx. eapply (rfree_fp_meta0 st st0 m lo (bv_unsigned sp) g); [exact MR | exact MSL | symmetry; exact ER | lia]. }
finish.
Qed.

#[using="Type"] Lemma rfree_tocall : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate) (g : aptr) (idx : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv usegs m -> meta_slot st g ->
0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
(m_freed mr = 0 \/ Z.lor (m_freed mr) (m_avail mr) + bit idx = mask_upto (m_last_idx mr)) ->
evt usegs (fun ms' => exists x2 x3 x4 x5 x6 x7,
ms' = MS (mkR (Z_to_bv 64 0xd04dc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(Z_to_bv 64 (conc st g)) (Z_to_bv 64 idx) x2 x3 x4 x5 x6 x7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0644) fc None m (seg_rom usegs))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 0x645468) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd046c) fc None m (seg_rom usegs)).
Proof.
intros until idx. intros mr MR MI MSL HF HA HL HI TF TA HNT.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
replace (Z_to_bv 64 (conc st g)) with gw by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
clearbody gw.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
unfold alloc_ceiling, RNEED_LOCKS in *.

step. step. rewrite !sx32_wz_sxv by lia.

step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.

step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.land_comm _ (sxv (2 ^ idx))).
rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).

step. if_true. st1.

step. if_cases K2; zify_cond K2.
-
st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
st1. st1.
apply evt_done. do 6 eexists. reflexivity.
-
step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
step. if_cases K3; zify_cond K3.
+ st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
st1. st1.
apply evt_done. do 6 eexists. reflexivity.
+ exfalso. destruct HNT as [Hz|Hall].
* apply K2. rewrite ?wz_unsigned by apply sxv_range. rewrite Hz. reflexivity.
* apply K3. rewrite ?wz_unsigned by apply sxv_range.
apply (proj2 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
unfold bit, mask_upto in Hall. exact Hall.
Qed.

End RC__1.
End Mqg.

Module Mqh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 QDUx.Mq6.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 Q98Z.Mq4 QnOf.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rffin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch W m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' (errno_addr tp) [C4 errv]
/\ rmrep st m'.

#[using="Type"] Lemma rfree_fin0 : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv usegs m ->
rw_cells usegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
stk usegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt usegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m st errv)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz 0) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd04dc) fc None m (seg_rom usegs)).
Proof.
intros until errv. intros TP MR MI FR ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
unfold alloc_ceiling, RMLOCK, RNEED_LOCKS, RATP in *. subst tp.
rewrite (unsigned_lit 6444320) in ERR by lia. change (6444320 + -164) with 6444156 in ERR.

st1. st1. st1. st1.

st1.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0xd04f0)) with (Z_to_bv 64 0xd04f0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
rewrite (unsigned_lit 6444320) by lia. change (6444320 + -164) with 6444156. exact ERR.
Qed.

Definition rfmun_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0xd050c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw bw lw a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (errno_addr tp)) (sx32 errv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmunmap_entry) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp + -48)
/\ rw_cells usegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells usegs m' (errno_addr tp) [C4 errv]
/\ rmrep st m'.

#[using="Type"] Lemma rfree_tomunmap : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
(m : word -> option byte) (junk : list byte) (lo len : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv usegs m -> 0 < len < 2^64 ->
rw_cells usegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
stk usegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt usegs (rfmun_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo junk m st errv bw (wz len))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz len) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd04dc) fc None m (seg_rom usegs)).
Proof.
intros until errv. intros TP MR MI HL FR ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
unfold alloc_ceiling, RMLOCK, RNEED_LOCKS, RATP in *. subst tp.
rewrite (unsigned_lit 6444320) in ERR by lia. change (6444320 + -164) with 6444156 in ERR.

st1. st1. st1. st1.

st1.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0xd04f0)) with (Z_to_bv 64 0xd04f0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

st1. if_cases K; zify_cond K. { exfalso. rewrite wz_unsigned in K by lia. lia. }

st1. st1. st1. st1.
replace (ret_pc (Z_to_bv 64 0xd04f8)) with (Z_to_bv 64 0xd04f8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
apply evt_done. unfold rfmun_post. do 14 eexists. split; [rewrite (unsigned_lit 6444320) by lia; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
split; [rewrite (unsigned_lit 6444320) by lia; change (6444320 + -164) with 6444156; exact ERR| exact MR2].
Qed.

#[using="Type"] Lemma rerrno_avoids_repfoot : forall st m a, rmrep st m -> 6444156 <= a < 6444160 -> ~ rrepfoot st a.
Proof.
intros st m a MR Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
- unfold RCTX in C. lia.
- unfold RMLOCK in C. lia.
- unfold RNEED_LOCKS in C. lia.
- unfold RPAGE_SIZE in C. lia.
- destruct C as (ak & ar & Hak & Hin).
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len ra)). lia.
- destruct C as (b & gh & Hb & Hin).
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len rb)). lia.
- destruct C as (rid & r & v & Hr & Hk & Hin & HC).
destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. lia.
- unfold RGOT_SSP in C. lia.
- unfold RSSP_GUARD in C. lia.
Qed.

#[using="Type"] Lemma rmrep_transport_frame_errno : forall st m m' (sp : Z),
rmrep st m -> munch [(sp - 48, sp); (6444156, 6444160)]%Z m m' -> wmono usegs m m' -> alloc_ceiling <= sp - 48 -> rmrep st m'.
Proof.
intros st m m' sp MR MU WM HS. eapply rmrep_transport_unowned; [exact MR | exact MU | exact WM |].
apply ivs_avoid_cons; [| apply ivs_avoid_cons; [| apply ivs_avoid_nil]].
- intros a Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in HS.
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
+ unfold RCTX in C. lia.
+ unfold RMLOCK in C. lia.
+ unfold RNEED_LOCKS in C. lia.
+ unfold RPAGE_SIZE in C. lia.
+ destruct C as (ak & ar & Hak & Hin).
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold alloc_ceiling in RBC. lia.
+ destruct C as (b & gh & Hb & Hin).
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC). unfold alloc_ceiling in RBC. lia.
+ destruct C as (rid & r & v & Hr & Hk & Hin & HC).
destruct (WR _ _ Hr) as (_ & _ & _ & RBC & _). unfold alloc_ceiling in RBC. lia.
+ unfold RGOT_SSP in C. lia.
+ unfold RSSP_GUARD in C. lia.
- intros a Ha. eapply rerrno_avoids_repfoot; [exact MR | exact Ha].
Qed.

#[using="Type"] Lemma rfree_fin1 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv usegs m ->
rw_cells usegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
le4 ew = le4 errv ->
rw_cells usegs m (errno_addr tp) [C4 e'] ->
stk usegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt usegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp); (6444156, 6444160)]%Z m st errv)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (errno_addr tp)) ew s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd050c) fc None m (seg_rom usegs)).
Proof.
intros until errv. intros TP MR MI FR EW ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (6444156, 6444160)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
unfold alloc_ceiling, RATP in *. subst tp.
rewrite (unsigned_lit 6444320) in ERR by lia. change (6444320 + -164) with 6444156 in ERR.
rewrite (unsigned_lit 6444320) by lia. change (6444320 + -164) with 6444156.

st1.

st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX) by (eapply (rmrep_transport_frame_errno st m mX (bv_unsigned sp)); [exact MR | exact MU | exact WM | unfold alloc_ceiling; lia]) end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
rewrite (unsigned_lit 6444320) by lia. change (6444320 + -164) with 6444156.
eapply rw_cells_congr; [| | | exact ERR]; [cbn [cells_bytes cbytes app]; rewrite EW; reflexivity| reflexivity| cbn; tauto].
Qed.

End RC__1.
End Mqh.

Module Mqi.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq Qn9M QdZ1 QQbX.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma renf_glue_walk : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw gw iw rav s0v s1v s2v s3v s4v : word)
F fc (m : mem) (st : mstate),
rw_cells usegs m RCTX (ctx_head_cells st) ->
rw_cells usegs m RMLOCK [C4 (wz 0)] ->
rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
48 <= bv_unsigned sp ->
0 <= c_mmap_counter (ctx st) < 2^32 ->
evt usegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v gw iw nw (wz (sxv (c_mmap_counter (ctx st)))) a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 renframe_entry) fc None m (seg_rom usegs))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7 gw iw s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1018) fc None m (seg_rom usegs)).
Proof.
intros until st. intros CH LK FR SP48 CTR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold RCTX, RMLOCK in *. unfold ctx_head_cells in CH.

step. rewrite sx32_wz_sxv by lia.

step. step.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0xd1024)) with (Z_to_bv 64 0xd1024) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

do 12 step.
apply evt_done. unfold renframe_entry. reflexivity.
Qed.

#[using="Type"] Lemma bytes_at_enframe_user : forall m4 P0 stride off n k B bs,
0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= P0 -> P0 + stride <= 2^64 ->
bytes_at usegs m4 (P0 + 16 * off) bs -> Z.of_nat (length bs) <= n ->
bytes_at usegs (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)) (P0 + 16 * off) bs.
Proof.
intros m4 P0 stride off n k B bs OFF0 N0 FIT P4 PS HB LEN.
assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
assert (HO : bytes_at usegs (renframe_off_mem m4 P0 off) (P0 + 16 * off) bs).
{ unfold renframe_off_mem. destruct (Z.eqb_spec off 0); [exact HB|].
apply bytes_at_write_other; [| lia | cbn; lia | cbn; lia].
apply bytes_at_write_other; [| lia | rewrite L2; lia | rewrite L2; lia].
apply bytes_at_write_other; [exact HB| lia | cbn; lia | cbn; lia]. }
unfold renframe_tail_mem. cbv zeta.
set (mE := write_to_mem (write_to_mem (renframe_off_mem m4 P0 off) _ _) _ _).
assert (HE : bytes_at usegs mE (P0 + 16 * off) bs).
{ subst mE. apply bytes_at_write_other; [| lia | rewrite L2; lia | rewrite L2; lia].
apply bytes_at_write_other; [exact HO| lia | cbn; lia | cbn; lia]. }
clearbody mE.
set (rsv := P0 + stride - 4 - (P0 + 16 * off) - n).
set (mF := if rsv =? 0 then _ else _).
assert (HF : bytes_at usegs mF (P0 + 16 * off) bs).
{ subst mF. destruct (Z.eqb_spec rsv 0); [exact HE|]. apply bytes_at_write_other; [exact HE| lia | cbn; lia | cbn; lia]. }
clearbody mF.
set (mG := if 5 <=? rsv then _ else _).
assert (HG : bytes_at usegs (fst mG) (P0 + 16 * off) bs /\ 0 <= snd mG <= 5).
{ subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
- split; [|lia]. apply bytes_at_write_other; [| lia | rewrite L4; lia | rewrite L4; lia].
apply bytes_at_write_other; [exact HF| lia | cbn; lia | cbn; lia].
- split; [exact HF| lia]. }
clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
apply bytes_at_write_other; [exact HG| lia | cbn; lia | cbn; lia].
Qed.

Definition renf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (o m0 m1 : mem) (C : Z -> Prop) (st1 : mstate) (g b : aptr) (idx n : Z)
(r : mstate * optr) (ms' : machine_state) : Prop :=
exists st' p t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
r = (st', Some p)
/\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (conc st' p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
/\ rmrep st' m' /\ ticks_ok st' /\ rpres_except C m0 m'
/\ enf_leaf o st1 g b idx n st' p
/\ (forall bs, bytes_at usegs m1 (conc st' p) bs -> Z.of_nat (length bs) <= n -> bytes_at usegs m' (conc st' p) bs).

#[using="Type"] Lemma renf_implT :
forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' ra s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32)
(o m0 m1 : mem) (s : PState) (st1 : mstate) (g b : aptr) (r : region) (idx n lo : Z) (C : Z -> Prop),
let mr := get_meta_rec st1 g in
let stride := get_stride mr in
let ctr := c_mmap_counter (ctx st1) in
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 ->
mem_inv usegs m1 -> stk usegs m1 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rpres_except C m0 m1 -> (forall a, lo <= a < bv_unsigned sp -> C a) ->
(forall a, r_base r + snd b + 16 + stride * idx - 4 <= a < r_base r + snd b + 16 + stride * idx + stride - 4 -> C a) ->
0 <= ctr < 2^32 ->
slot_ok st1 g b r idx n ->
rimplT o (enframe_full st1 g idx n ctr (fun st2 p => ret (havoc p n st2, Some p))) s
(fun res s' ms' => s' = s /\ renf_post ra sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc lo o m0 m1 C st1 g b idx n res ms')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
a0 a1 a2 a3 a4 a5 a6 a7 (pw st1 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1018) fc None m1 (seg_rom usegs)).
Proof.
intros until C. intros mr stride ctr MR TK UA MI ST CLO LO FR PE CST CSL CTR SO.
destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16, AVr, FRr, FBr, MPL, SCr.
fold stride in SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16.
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
clear SPAN. rename SPAN1 into SPAN.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in CLO.

destruct (rslot_facts st1 m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN S16 B16 SMOD HDR0)
as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND.
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
unfold alloc_ceiling in RC, GC.
set (G := conc st1 g) in *.
pose proof (GDJ (fst b) r Hr Hk) as GR.
change (get_meta_rec st1 g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM.
set (B := conc st1 b) in *.
pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.

pose proof (bytes_at_read usegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
pose proof (bytes_at_read usegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
pose proof (bytes_at_read usegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
rewrite Z.add_0_r in RD4.
replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.

unfold enframe_full, enframe_read_off. change (get_meta_rec st1 g) with mr. fold stride. cbv zeta.
assert (Hp0 : slot_start' mr idx = (fst b, snd b + (16 + stride * idx))).
{ unfold slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT. cbn [fst snd]. fold stride. reflexivity. }
rewrite Hp0. unfold aadd. cbn [fst snd].
apply rimplT_rd8. rewrite E3.
change ((stride - IB - n) / UNIT) with ((stride - 4 - n) / 16). set (slack := (stride - 4 - n) / 16).
set (K := fun off : Z => let '(st2, p) := enframe_at st1 g idx n off in @ret (mstate * optr) (havoc p n st2, Some p)).
set (off0 := if bv_unsigned x3 =? 0 then Z.land ctr 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255).
set (off := fold_off off0 slack).
assert (OFF0 : 0 <= off0 < 256).
{ subst off0. destruct (bv_unsigned x3 =? 0).
- split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
- split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
assert (SL0 : 0 <= slack) by (subst slack; apply Z.div_pos; lia).
pose proof (fold_off_le_slack off0 slack OFF0 SL0) as OFF. fold off in OFF.
assert (FIT : 16 * off + n + 4 <= stride) by (subst slack; Z.div_mod_to_equations; lia).
match goal with |- rimplT _ _ _ ?Q ?ms =>
assert (GOAL : rimplT o (K off) s Q ms) end.
2:{ assert (OFFa : bv_unsigned x3 = 0 -> fold_off (Z.land ctr 255) slack = off).
{ intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
assert (OFFb : bv_unsigned x3 <> 0 -> fold_off (Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) slack = off).
{ intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
clearbody off.
destruct (Z.eqb_spec (bv_unsigned x3) 0) as [E0|NE0]; cbn [negb].
- rewrite (OFFa E0). exact GOAL.
- apply rimplT_rd16. unfold aadd; cbn [fst snd]. rewrite E2, E1. rewrite (OFFb NE0). exact GOAL. }
subst K. cbv beta. rewrite surj_pair_let. apply rimplT_ret.

pose proof MR as (WF' & CX & GL & _). destruct GL as (LK & _). destruct CX as (CH & _).
eapply evt_cut.
{ eapply (renf_glue_walk sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' (Z_to_bv 64 n) (pw st1 (Some g)) (wz idx) ra s0v s1v s2v s3v s4v F fc m1 st1);
[exact CH| exact LK| exact FR| lia| exact CTR]. }
intros ms' ->.
unfold renframe_entry.
eapply evt_mono.
{ eapply (renframe_walk ra sp gp tp t0 t1 t2 s0v s1v a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (pw st1 (Some g)) (Z_to_bv 64 n)
(pw st1 (m_prev mr)) (pw st1 (m_next mr)) F fc m1 B stride n idx ctr (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
all: lazymatch goal with
| |- rw_cells _ _ (bv_unsigned (pw _ _)) _ => unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia; exact MM
| |- mem_inv _ _ => exact MI
| |- wr_at _ _ _ _ => exact WRs
| |- ov_read_bytes _ _ _ 2 = _ => exact RD2
| |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
| |- ov_read_bytes _ _ _ _ = _ => exact RD3
| |- bv_unsigned (Z_to_bv 64 _) = _ => apply unsigned_lit; lia
| |- _ => idtac end.
all: try (unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia).
all: try lia.
- subst stride. unfold get_stride, UNIT. reflexivity.
- intros off' O1 O2. pose proof (Q16 off' O1 O2). lia. }

intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
split; [reflexivity|].
fold slack in EM. fold off0 in EM. fold off in EM. fold slack off0 off.
set (res := enframe_at st1 g idx n off) in *.

assert (S31n : stride - 4 - n < 2^31) by lia.
destruct (renframe_mrep st1 m1 g b r idx n off MR TK Hmem Hr Hk B0 ltac:(clear -IDX LI32; lia) ltac:(unfold stride, mr in SPAN; clear -SPAN S16; lia) S16 S31n NOGRP (proj1 OFF) N0 FIT (Q16 off (proj1 OFF) FIT))
as (MRr & TKr & CONCr & FSTr & SNDr).
fold stride B res in MRr, TKr, CONCr, FSTr, SNDr.
change (conc st1 b) with B in MRr, CONCr. change (get_stride (get_meta_rec st1 g)) with stride in MRr, CONCr, SNDr.
fold res in MRr, TKr, CONCr, FSTr, SNDr.
set (P0 := B + 16 + stride * idx) in *.
rewrite <- EM in MRr.
destruct (rmrep_havoc (fst res) m' (snd res) n MRr TKr) as [MR' TK'].

assert (PE0 : rpres_except (fun a => P0 - 4 <= a < P0 + stride - 4) m1 m').
{ rewrite EM. apply (rpres_enframe _ m1 m1 P0 stride off n idx B (rpres_except_refl _ _) (proj1 OFF) N0 FIT); [unfold P0; lia| unfold P0; lia|].
intros x Hx. exact Hx. }
assert (ST' : stk usegs m' lo (bv_unsigned sp + -48)).
{ eapply rpres_except_stk; [exact PE0| exact ST|]. intros a Ha. cbv beta. unfold P0. lia. }
assert (FR' : rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
{ eapply rpres_except_rw_cells; [exact PE0| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat]. intros a Ha. cbv beta. unfold P0. lia. }
release_frame FR' ST' (bv_unsigned sp).
unfold renf_post. exists (havoc (snd res) n (fst res)), (snd res). do 14 eexists. exists m'.
split; [reflexivity|].
split. { unfold wz. rewrite conc_havoc. rewrite <- CONCr. unfold res. rewrite conc_enframe_at. reflexivity. }
split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|]. split; [exact TK'|].
split.
{ rewrite EM. apply (rpres_enframe C m0 m1 _ stride off n idx B PE (proj1 OFF) N0 FIT); [unfold B; lia| unfold B; lia|].
intros x Hx. apply CSL. unfold B in Hx. lia. }
split.
{ exists off. split; [exact (proj1 OFF)|]. split; [exact FIT|].
split. { clear - FSTr SNDr. destruct (snd res) as [p1 p2]. cbn [fst snd] in FSTr, SNDr. subst. reflexivity. }
split; [reflexivity|]. split; [reflexivity|].
unfold off, off0, slack, enf_off0. fold mr. fold stride. rewrite E3, E2, E1. reflexivity. }

assert (EC : conc (fst res) (snd res) = P0 + 16 * off) by (unfold res at 1; rewrite conc_enframe_at; exact CONCr).
intros bs HB LEN. rewrite conc_havoc, EC in HB |- *. rewrite EM.
apply (bytes_at_enframe_user m1 P0 stride off n _ B bs (proj1 OFF) N0 FIT); [unfold P0, B; lia| unfold P0, B; lia| exact HB| exact LEN].
Qed.

End RC__1.
End Mqi.

Module Mqj.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 QJE4.Mq3 QDUx.Mqa QDUx.Mqb.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 QdZ1.Mq7 QQbX.Mq6.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame usegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
apply (stk_write usegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
apply (wmono_write usegs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv usegs mX |- _ =>
apply (mem_inv_store usegs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rat9c_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc : Z) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists a3 a4 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0808) fc None m' (seg_rom usegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp + -96)
/\ rw_cells usegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="Type"] Lemma rntf_deqself : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g : aptr) (sc lo : Z),
rmrep st m -> mem_inv usegs m -> meta_slot st g -> 0 <= sc < 48 ->
m_next (get_meta_rec st g) = Some g ->
rw_cells usegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk usegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt usegs (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
(deq_mid (LActive sc) g st) g sc fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0800) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros MR MI MSL SC GN FR FRL ST LO LOLE.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
unfold alloc_ceiling, RCTX in *.
st1.
pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok usegs _ _ (actives st) sc (Z_to_bv 64 (6576296 + sc * 8 + 80)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc None MR SC) as MR2; unfold RCTX in MR2 end.
clear ACTS.
rraw_store_finish (6576296 + 80 + 8 * sc) (le8 (pw st None)) FR ST MU WM SOK.
assert (EQ : deq_mid (LActive sc) g st = set_active sc None st).
{ unfold deq_mid. rewrite GN, optr_eqb_refl. reflexivity. }
rewrite EQ.
apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.

#[using="Type"] Lemma rntf_deq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g nx pv : aptr) (sc lo : Z),
rmrep st m -> mem_inv usegs m -> meta_slot st g -> 0 <= sc < 48 ->
m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv ->
nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
(active st sc = None \/ exists q, active st sc = Some q /\ meta_slot st q) ->
a2 = pw st (active st sc) ->
rw_cells usegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk usegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt usegs (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
(deq_mid (LActive sc) g st) g sc fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd077c) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros MR MI MSL SC GN GP NEn NEp MSn MSp ACT HA2 FR FRL ST LO LOLE.
pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
pose proof (rmeta_slot_bounds st m nx MR MSn) as NB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
unfold alloc_ceiling, RCTX in *.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (6576296, 6576296 + 928)]%Z m) as MU.

rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1. clear CH.

rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR MSp CH.
st1.
rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 GP GN.
set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).

rmeta_chunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1. clear CH.

rmeta_open (conc st nx) MUn WMn.
rmeta_chunk MR1 MSn1 CH.
st1.
rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 GP GN.
set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).

pose proof (rmrep_active_read st2 _ sc (wa (RCTX + 80 + 8 * sc)) MR2 SC eq_refl) as RDA. unfold RCTX in RDA.
replace (wa (6576296 + 80 + 8 * sc)) with (Z_to_bv 64 (6576296 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
assert (HACT : active st2 sc = active st sc) by reflexivity. rewrite HACT in RDA.
assert (HPW : forall q, pw st2 q = pw st q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
st1. clear RDA.
assert (EQmid : deq_mid (LActive sc) g st =
if optr_eqb (active st sc) (Some g) then set_active sc (Some nx) st2 else st2).
{ unfold deq_mid. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head].
rewrite !upd_meta_put. fold st1. fold st2. rewrite HACT. reflexivity. }

st1. if_cases K; zify_cond K.
-
assert (HA : optr_eqb (active st sc) (Some g) = false).
{ destruct (active st sc) as [q|]; [|reflexivity]. cbn [optr_eqb]. apply aptr_eqb_neq. intros ->. apply K.
unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
rewrite HA in EQmid. rewrite <- EQmid in MR2. subst a2.
apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSp | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSn | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
-
assert (HA : active st sc = Some g).
{ destruct ACT as [A0|(q & Aq & MSq)].
- exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
- rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
pose proof (rmeta_slot_bounds st m q MR MSq) as QB. rewrite ?unsigned_lit in K by lia.
rewrite (rconc_meta_inj st m g q MR MSL MSq ltac:(lia)). reflexivity. }
rewrite HA, optr_eqb_refl in EQmid.
rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
rewrite GN, GP in CH. cbn [oconc] in CH.
st1. clear CH. st1.
pose proof MR2 as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok usegs _ _ (actives st2) sc (Z_to_bv 64 (6576296 + sc * 8 + 80)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
clear ACTS.
rraw_store_finish (6576296 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) FR ST MU WM SOK.
rewrite <- EQmid in MR3. subst a2.
apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSp | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSn | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR3].
Qed.

#[using="Type"] Lemma land_mod_pow2 a b n : 0 <= n -> (Z.land a b) mod 2^n = Z.land (a mod 2^n) (b mod 2^n).
Proof.
intros Hn. rewrite <- !Z.land_ones by lia.
apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
destruct (Z.testbit a k), (Z.testbit b k), (Z.testbit (Z.ones n) k); reflexivity.
Qed.

#[using="Type"] Lemma act_mask_le4 f y z : 0 <= f < 2^32 -> 1 <= y <= 2^32 -> z mod 2^32 = (y - 1) mod 2^32 ->
le4 (Z_to_bv 64 (Z.land (sxv f) (bv_unsigned (Z_to_bv 64 z)))) = le4 (wz (Z.land f (y - 1))).
Proof.
intros Hf Hy Hz. apply le4_congr.
pose proof (sxv_range f). rewrite (unsigned_lit_wrap z). pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)).
assert (R1 : 0 <= Z.land (sxv f) (z mod 2^64) < 2^64) by (apply land_range64; lia).
assert (R2 : 0 <= Z.land f (y - 1) < 2^32).
{ split; [apply Z.land_nonneg; lia|]. pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)). lia. }
rewrite unsigned_lit, wz_unsigned by lia.
rewrite land_mod_pow2, sxv_mod32, mod64_mod32, Hz by lia.
rewrite !Z.mod_small by lia. reflexivity.
Qed.

Definition rat00_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd086c) fc None m' (seg_rom usegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp + -96)
/\ rw_cells usegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="Type"] Lemma rntf_postdeq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) stm (g : aptr) (sc lo : Z) (an : bool),
let st1 := upd_meta g clr_links stm in
rmrep stm m -> mem_inv usegs m -> meta_slot stm g -> 0 <= sc < 48 ->
(if an then bv_unsigned a2 = conc stm g else bv_unsigned a2 <> conc stm g) ->
(an = true -> forall a, active st1 sc = Some a ->
meta_slot st1 a /\ a <> g /\ m_avail (get_meta_rec st1 a) = 0 /\ 0 <= m_freed (get_meta_rec st1 a) < 2^32
/\ exists ba gh, m_mem (get_meta_rec st1 a) = Some ba /\ (s_groups st1) !! ba = Some gh /\ 0 <= g_active_idx gh <= 31) ->
rw_cells usegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk usegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt usegs (rat00_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 F fc lo stm m (pd_st an st1 sc) g fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc stm g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0808) fc None m (seg_rom usegs)).
Proof.
intros until an. intros st1 MR MI MSL SC HA2 HACT FR FRL ST LO LOLE.
pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (bv_unsigned_in_range _ a2) as A2R. change (bv_modulus 64) with (2^64) in A2R.
pose proof (rmeta_slot_bounds stm m g MR MSL) as GB.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
unfold alloc_ceiling, RCTX in *.
pose proof (munch_refl [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m) as MU.

rmeta_open (conc stm g) MUg WMg.
rmeta_chunk MR MSL CH.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st1 mX)
by (unfold st1; rewrite upd_meta_put; eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WMg |];
eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear MUg WMg CH
end.
assert (COV : forall m', munch [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m m' -> wmono usegs m m' ->
rpres_except (rfree_fp stm lo (bv_unsigned sp)) m m').
{ intros m' MU' WM'. apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU'; [exact MU'|exact WM'|].
cbn [ivs_covered]. repeat split; intros x Hx; (eapply rfree_fp_meta; [exact MR | exact MSL | lia]). }
assert (MSg1 : meta_slot st1 g) by (unfold st1; rewrite upd_meta_put; apply meta_slot_put_meta; exact MSL).
assert (Hconc : forall q, conc st1 q = conc stm q) by (intros; reflexivity).

st1. if_cases K; zify_cond K.
-
destruct an. { exfalso. apply K. rewrite ?unsigned_lit by lia. lia. }
cbn [pd_st].
apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR1].
-
destruct an. 2:{ exfalso. apply HA2. rewrite ?unsigned_lit in K by lia. lia. }
cbn [pd_st].

pose proof (rmrep_active_read st1 _ sc (wa (RCTX + 80 + 8 * sc)) MR1 SC eq_refl) as RDA. unfold RCTX in RDA.
assert (HPW : forall q, pw st1 q = pw stm q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
replace (wa (6576296 + 80 + 8 * sc)) with (Z_to_bv 64 (6576296 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
st1. clear RDA.

st1. destruct (active st1 sc) as [a|] eqn:HA1.
+ destruct (HACT eq_refl a eq_refl) as (MSa & NEa & AV0 & FRR & ba & gh & Hmem & Hgh & AI).
pose proof (rmeta_slot_bounds st1 _ a MR1 MSa) as AB. rewrite !Hconc in AB.
munch_grow MU (conc stm a, conc stm a + 40).
unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.

rmeta_chunk MR1 MSa CHa. rewrite AV0, Hmem in CHa. cbn [oconc] in CHa.
st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. rewrite ?unsigned_lit by lia. reflexivity. } clear K3.

st1.

destruct (rmrep_group_read st1 _ ba gh MR1 Hgh) as [_ (w8 & RD8 & Hw8)].
rewrite Hconc in RD8.
st1.
pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
assert (MOD8 : bv_unsigned w8 mod 32 = g_active_idx gh).
{ rewrite <- Hw8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }

st1. st1. unfold zxb. rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite MOD8.
set (y := 2 ^ (g_active_idx gh + 1)).
st1. st1. rewrite negw_word.

clear CHa. rmeta_open (conc stm a) MUa WMa.
rmeta_chunk MR1 MSa CHa. rewrite Hmem in CHa. cbn [oconc] in CHa.
pose proof (sxv_range (m_freed (get_meta_rec st1 a))) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range y) as RY1.
st1. rewrite sx32_wz_sxv by lia.
st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.

assert (AMO : amo_aligned AW (Z_to_bv 64 (conc stm a + 28)) = true).
{ apply amo_aligned_intro; [lia|]. Z.div_mod_to_equations. lia. }
amo_step AMO. rewrite ?sx32_wz_sxv by lia.
st1. if_false.
amo_step AMO.
st1. if_false.
st1. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. st1. if_false.

st1. st1. st1.

set (f := m_freed (get_meta_rec st1 a)) in *.
assert (AI31 : Z.land (g_active_idx gh) 31 = g_active_idx gh).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
assert (ACT : act_of st1 a = y - 1).
{ unfold act_of. rewrite Hmem. cbn [default]. unfold group_active_idx, get_group. rewrite Hgh, AI31. unfold mask_upto, y. reflexivity. }
assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
assert (Y1 : 1 <= y <= 2^32).
{ unfold y. split; [pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh + 1)); lia| apply Z.pow_le_mono_r; lia]. }
pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (act_st st1 a (act_of st1 a)) mX)
end.
{ unfold act_st. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR1 | exact MSa | exact MUa | exact WMa |].
eapply rw_cells_congr; [ | | | exact CHa]; [ | reflexivity | cbn; tauto].
unfold meta_cells. unfold pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen oconc].
fold f. rewrite E1. rewrite (act_mask_le4 f y) ; [| lia | exact Y1 | rewrite <- Zplus_mod_idemp_l, swrap32_mod32, Zplus_mod_idemp_l; reflexivity].
rewrite !le4_sxv by lia. rewrite Hmem. cbn [oconc]. reflexivity. }
clear MUa WMa CHa.
apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split. { apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
- eapply rfree_fp_meta; [exact MR | exact MSL | lia].
- eapply rfree_fp_meta; [exact MR | exact MSa | lia].
- eapply rfree_fp_meta; [exact MR | exact MSL | lia]. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
unfold pd_st. rewrite ?HA1. exact MR2.
+
unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. rewrite ?unsigned_lit by lia. reflexivity. } clear K2.
apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
unfold pd_st. rewrite ?HA1. exact MR1.
Qed.

End RC__1.
End Mqj.

Module Mqk.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 QytA QJE4.Mq4 Qy5Y.Mq5.
Export QWTl.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.

Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq QkLq.Mq3 QdZ1 QQbX.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

#[using="Hconc"] Lemma rpw_extP p : optr_in P p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.

#[using="Hmetas"] Lemma rget_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.

#[using="P HP Hconc"] Lemma rmeta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
unfold meta_cells. rewrite !rpw_extP by assumption. reflexivity.
Qed.

#[using="P HP Hconc Hctx"] Lemma rmrep_ctx_extP m : rmrep_ctx st m -> rmrep_ctx st' m.
Proof.
intros H. destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
assert (E1 : ctx_head_cells st' = ctx_head_cells st).
{ unfold ctx_head_cells. rewrite Hctx. rewrite !rpw_extP by assumption. reflexivity. }
assert (E2 : actives st' = actives st).
{ unfold actives. apply map_ext. intros a. unfold active. rewrite Hctx. apply rpw_extP. apply (H6 (Z.of_nat a)). }
assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hctx. reflexivity. }
assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hctx. reflexivity. }
assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hctx. reflexivity. }
assert (E6 : ctx_tail_cells st' = ctx_tail_cells st).
{ unfold ctx_tail_cells, brk_word. rewrite Hctx. destruct (c_brk (ctx st)) as [| |rid off]; try reflexivity.
rewrite (Hconc (rid, off)) by exact H7. reflexivity. }
unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6, Hctx. exact H.
Qed.

#[using="P HP Hconc Hmetas"] Lemma rarea_rep_extP m a ar : (s_areas st) !! a = Some ar -> rarea_rep st m a ar -> rarea_rep st' m a ar.
Proof.
intros Ha (A1 & A2 & A3). destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
destruct (H9 a ar Ha) as [Pa Pn].
unfold rarea_rep. rewrite (Hconc a Pa). rewrite (rpw_extP _ Pn). split; [exact A1|]. split; [|exact A3].
intros k Hk. rewrite rget_meta_rec_extP, rmeta_cells_extP. apply A2. exact Hk.
Qed.

#[using="P HP Hconc"] Lemma rgroup_rep_extP m b gh : (s_groups st) !! b = Some gh -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof.
intros Hb (w8 & R & Hw8). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (rpw_extP _ Pg). auto.
Qed.
End PEXT.

#[using="Type"] Lemma rbytes_at_agree m m' A bs : bytes_at usegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at usegs m' A bs.
Proof.
intros (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

#[using="Type"] Lemma rwr_at_agree m m' A n : wr_at usegs m A n -> agree_on m m' A n -> wr_at usegs m' A n.
Proof.
intros (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
unfold wview. rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma rrw_cells_agree m m' A cs : rw_cells usegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells usegs m' A cs.
Proof.
intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
- eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
- eapply rwr_at_agree; eauto.
Qed.

#[using="Type"] Lemma ru64arr_agree m m' A ws : u64arr usegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr usegs m' A ws.
Proof.
intros [HB HW] AG. split.
- eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
- eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

#[using="Type"] Lemma ru8arr_agree m m' A bs : u8arr usegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr usegs m' A bs.
Proof. intros [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

#[using="Type"] Lemma rmrep_agree : forall st m m',
rmrep st m ->
agree_on m m' RMLOCK 4 -> agree_on m m' RLIBC 0x498 -> agree_on m m' RGOT_SSP 8 -> agree_on m m' RSSP_GUARD 8 -> agree_on m m' RVMLOCK 4 ->
(forall a ar, (s_areas st) !! a = Some ar -> agree_on m m' (conc st a) 4096) ->
(forall b gh, (s_groups st) !! b = Some gh -> agree_on m m' (conc st b) 9) ->
(forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
rmrep st m'.
Proof.
intros st m m' (WF & CX & GL & AR & GR & SH) AGL AGC AGS1 AGS2 AGV AGA AGG AGR.
split; [exact WF|]. split; [|split; [|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold rmrep_ctx.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
unfold RLIBC, RCTX in *.
split; [|split; [|split; [|split; [|split; [|split]]]]].
+ eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ exact C7.
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD, RVMLOCK in *.
split; [|split; [|split; [|split; [|split]]]].
+ eapply rrw_cells_agree; [exact G1|]. eapply agree_on_sub; [exact AGL| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G2|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G3|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G4|]. eapply agree_on_sub; [exact AGS1| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G5|]. eapply agree_on_sub; [exact AGS2| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G6|]. eapply agree_on_sub; [exact AGV| lia| cbn; lia].
- intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). pose proof (AGA a ar Ha) as AG.
split; [|split].
+ eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
+ intros k Hk. eapply rrw_cells_agree; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AG| lia| lia].
+ eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
eapply rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG. split.
+ eapply rwr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AG| lia| lia].
Qed.

Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).

Hypothesis MR : rmrep st m.
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= alloc_ceiling.
Hypothesis RF : ranges_free (live_ranges st) x L = true.

Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

#[using="Type"] Lemma rnr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rnr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. rewrite rnr_regions. apply lookup_insert_eq. Qed.
#[using="r0"] Lemma rnr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rnr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rnr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof.
intros H. destruct (N.eq_dec q rid) as [->|NE].
- left. rewrite rnr_lookup_new in H. inversion H. auto.
- right. rewrite rnr_lookup_old in H by exact NE. auto.
Qed.
#[using="r0"] Lemma rnr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite rnr_lookup_old by assumption. reflexivity. Qed.
#[using="r0"] Lemma rnr_conc_new off : conc st' (rid, off) = x + off.
Proof. unfold conc, get_region. cbn [fst snd]. rewrite rnr_lookup_new. reflexivity. Qed.
#[using="Type"] Lemma rnr_shadow q : get_shadow st' q = get_shadow st q.
Proof. reflexivity. Qed.
#[using="RC__ st m' rid L ZF"] Lemma rnr_lr_lo_new : x <= lr_lo r0.
Proof. unfold lr_lo, r0. cbn. destruct k; lia. Qed.

#[using="RC__ rid RF"] Lemma rnr_old_disjoint q r : (s_regions st) !! q = Some r ->
x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof.
intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

#[using="m m' rid L r0 MR PT X0 XA LEN XC RF ZF"] Lemma rnr_regions_wf : rregions_wf st'.
Proof.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
assert (RFimg : ranges_free ref_reserved x L = true).
{ apply ranges_free_intro. intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
split; [exact RS|]. split; [|split; [|split]].
- intros q r Hq. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
+ unfold r0. cbn. fold L. repeat split; try lia. exact RFimg.
+ exact (WR q r H).
- intros q1 r1 q2 r2 H1 H2 NE.
destruct (rnr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rnr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
+ congruence.
+ cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q2 r2 H2'). pose proof rnr_lr_lo_new. lia.
+ cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q1 r1 H1'). pose proof rnr_lr_lo_new. lia.
+ exact (DJ q1 r1 q2 r2 H1' H2' NE).
- intros a ar Ha. destruct (WA a ar Ha) as (r & Hr & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
exists r. rewrite rnr_lookup_old by exact Pa. auto.
- intros b gh Hb. destruct (WG b gh Hb) as (r & Hr & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
exists r. rewrite rnr_lookup_old by exact Pb. auto.
Qed.

#[using="m rid L r0 MR PT FRs X0 XA LEN XC RF AG ZF"] Lemma rmrep_new_region : rmrep st' m'.
Proof.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
assert (RI : forall b n, In (b, n) ref_reserved -> x + L <= b \/ b + n <= x).
{ intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
pose proof (RI _ _ ltac:(left; reflexivity)) as RI1. pose proof (RI _ _ ltac:(right; right; left; reflexivity)) as RI2.
pose proof (RI _ _ ltac:(right; right; right; left; reflexivity)) as RI3.
pose proof (round_up_pg_ge len) as LG. fold L in LG. unfold alloc_ceiling in XC.

assert (MR1 : rmrep st m').
{ eapply rmrep_agree; [exact MR| | | | | | | |].
- intros a Ha. apply AG; unfold RMLOCK in *; lia.
- intros a Ha. apply AG; unfold RLIBC in *; lia.
- intros a Ha. apply AG; unfold RGOT_SSP in *; lia.
- intros a Ha. apply AG; unfold RSSP_GUARD in *; lia.
- intros a Ha. apply AG; unfold RVMLOCK in *; lia.
- intros a ar Ha a0 Ha0.
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rnr_old_disjoint _ _ Hra).
unfold alloc_ceiling in RBC. apply AG; lia.
- intros b gh Hb a0 Ha0.
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
pose proof (lr_lo_group rb Kb). pose proof (rnr_old_disjoint _ _ Hrb). unfold alloc_ceiling in RBC. apply AG; lia.
- intros q r Hq Hk a0 Ha0. destruct (WR q r Hq) as (B0 & _ & _ & BC & _). unfold alloc_ceiling in BC.
pose proof (lr_lo_group r Hk). pose proof (rnr_old_disjoint _ _ Hq). apply AG; lia. }
pose proof MR1 as (_ & CX1 & GL1 & AR1 & GR1 & SH1).
assert (Hconc : forall q, (fun r => r <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rnr_conc; exact Hq).
split; [exact rnr_regions_wf|]. split; [|split; [exact GL1|split; [|split]]].
- eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl). exact CX1.
- intros a ar Ha. eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|]. exact (AR1 a ar Ha).
- intros b gh Hb. eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|]. exact (GR1 b gh Hb).
- intros q r Hq Hk. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
+
cbn [r_kind r0] in Hk. unfold rshadow_rep. cbn [r_base r_len r0]. fold L.
split.
* split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite (ZF Hk) by lia. discriminate.
* intros o v Ho Hc. rewrite rnr_shadow in Hc. unfold get_shadow in Hc. fold rid in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc.
rewrite cell_read_shadow0 in Hc. inversion Hc; subst v. split; [|lia].
split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia]. cbn [nth_error].
unfold mrd. rewrite Z.add_0_r. rewrite (ZF Hk) by lia. reflexivity.
+ eapply rshadow_rep_ext; [apply rnr_shadow|]. exact (SH1 q r H Hk).
Qed.

#[using="Type"] Lemma rticks_ok_new_region : ticks_ok st -> ticks_ok st'.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma rptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End NEWREGION.

Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
((RMLOCK <= a < RMLOCK + 4 \/ 0x646db8 <= a < 0x646db8 + 4) \/ RLIBC <= a < RLIBC + 0x498 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8
\/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
m' (wa a) = m (wa a).

#[using="Type"] Lemma rdr_regions : s_regions st' = delete rid (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rdr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof.
intros H. rewrite rdr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
- rewrite lookup_delete_eq in H. discriminate.
- rewrite lookup_delete_ne in H by congruence. auto.
Qed.
#[using="Type"] Lemma rdr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rdr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rdr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite rdr_lookup_old by assumption. reflexivity. Qed.
#[using="Type"] Lemma rdr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.

#[using="m r MR Hr PT AG"] Lemma rmrep_drop_region : rmrep st' m'.
Proof.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
assert (Hconc : forall q, (fun q => q <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rdr_conc; exact Hq).
destruct (WR rid r Hr) as (B0 & _ & RL0 & BC & RFr). unfold alloc_ceiling in BC.
assert (OTHER : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
r_base rq + round_up_pg (r_len rq) <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= lr_lo rq)
by (intros q rq Hq NE; exact (DJ q rq rid r Hq Hr NE)).
split; [|split; [|split; [|split; [|split]]]].
-
split; [exact RS|]. split; [|split; [|split]].
+ intros q rq Hq. destruct (rdr_lookup_inv q rq Hq) as [_ H]. exact (WR q rq H).
+ intros q1 r1 q2 r2 H1 H2 NE. destruct (rdr_lookup_inv _ _ H1) as [_ H1']. destruct (rdr_lookup_inv _ _ H2) as [_ H2']. exact (DJ _ _ _ _ H1' H2' NE).
+ intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
exists ra. rewrite rdr_lookup_old by exact Pa. auto.
+ intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
exists rb. rewrite rdr_lookup_old by exact Pb. auto.
-
eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl).
destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold rmrep_ctx.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0xe4000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0xe4000 \/ 0x647000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
{ destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [exact RFr| lia]]. }
assert (AGC : agree_on m m' RLIBC 0x498).
{ intros a Ha. unfold RLIBC in Ha. apply AG; [lia| lia| right; left; unfold RLIBC; lia]. }
unfold RLIBC, RCTX in *.
split; [|split; [|split; [|split; [|split; [|split]]]]].
+ eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ exact C7.
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0xe4000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0xe4000 \/ 0x647000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
{ destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [exact RFr| lia]]. }
unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD, RVMLOCK in *.
split; [|split; [|split; [|split; [|split]]]].
+ eapply rrw_cells_agree; [exact G1|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|left; left; lia].
+ eapply rrw_cells_agree; [exact G2|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
+ eapply rrw_cells_agree; [exact G3|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
+ eapply rrw_cells_agree; [exact G4|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; left; lia].
+ eapply rrw_cells_agree; [exact G5|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; right; left; lia].
+ eapply rrw_cells_agree; [exact G6|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|left; right; lia].
- intros a ar Ha. cbn [s_areas drop_region set_shadow set_regions] in Ha.
eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|].
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). unfold alloc_ceiling in RBC.
assert (NE : fst a <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _); exact (proj1 (P9 a ar Ha))).
pose proof (OTHER _ _ Hra NE). pose proof (lr_lo_ge r). pose proof (lr_lo_ge ra).
assert (AGA : agree_on m m' (conc st a) 4096).
{ intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists (fst a), ra. split; [exact Hra|]. lia. }
destruct (AR a ar Ha) as (A1 & A2 & A3). split; [|split].
+ eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
+ intros k0 Hk0. eapply rrw_cells_agree; [apply A2; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AGA| lia| lia].
+ eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
- intros b gh Hb. cbn [s_groups drop_region set_shadow set_regions] in Hb.
eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
assert (NE : fst b <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10); exact (proj1 (P10 b gh Hb))).
pose proof (OTHER _ _ Hrb NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rb Kb). unfold alloc_ceiling in RBC.
destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
eapply rrw_cells_agree; [exact R|]. intros a0 Ha0. cbn in Ha0. apply AG; [lia| lia|].
right; right; right; right. exists (fst b), rb. split; [exact Hrb|]. lia.
- intros q rq Hq Hk. destruct (rdr_lookup_inv q rq Hq) as [NE H].
eapply rshadow_rep_ext; [apply rdr_shadow; exact NE|].
destruct (WR q rq H) as (Bq & _ & _ & BCq & _). unfold alloc_ceiling in BCq.
pose proof (OTHER _ _ H NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rq Hk).
assert (AGR : agree_on m m' (r_base rq) (round_up_pg (r_len rq))).
{ intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists q, rq. split; [exact H|]. lia. }
destruct (SH q rq H Hk) as [HWr HB]. split.
+ eapply rwr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AGR| lia| lia].
Qed.

#[using="Type"] Lemma rticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
Proof.
intros [T1 T2]. split.
- intros q sh u hl ch Hq Hu Hin. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
rewrite lookup_delete_ne in Hq by congruence. exact (T1 q sh u hl ch Hq Hu Hin).
- intros q sh pg t Hq Hp. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
rewrite lookup_delete_ne in Hq by congruence. exact (T2 q sh pg t Hq Hp).
Qed.
End DROPREGION.

#[using="Type"] Lemma rmrep_put_group_new : forall st m b g ai r (w8 : byte),
rmrep st m -> (s_groups st) !! b = None ->
(s_regions st) !! (fst b) = Some r -> r_kind r = RKGroup -> 0 <= snd b -> snd b + 16 <= round_up_pg (r_len r) -> snd b mod 16 = 0 ->
rw_cells usegs m (conc st b) [C8 (pw st (Some g)); C1 w8] -> Z.land (bv_unsigned w8) 31 = Z.land ai 31 ->
rmrep (put_group b (Some g) ai st) m.
Proof.
intros st m b g ai r w8 (WF & CX & GL & AR & GR & SH) Hb Hr Hk B0 B16 BA R Hw8.
pose proof WF as (RS & WR & DJ & WA & WG).
split; [|split; [exact CX|split; [exact GL|split; [exact AR|split; [|exact SH]]]]].
- split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
destruct (decide (b' = b)) as [->|NE].
+ rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists r. auto.
+ rewrite lookup_insert_ne in Hb' by congruence. exact (WG b' gh Hb').
- intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
destruct (decide (b' = b)) as [->|NE].
+ rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists w8. cbn [g_meta g_active_idx]. split; [exact R| exact Hw8].
+ rewrite lookup_insert_ne in Hb' by congruence. exact (GR b' gh Hb').
Qed.

#[using="Type"] Lemma rmrep_set_mmap_counter : forall st m v,
rmrep st m -> 0 <= v < 2^32 ->
rmrep (upd_ctx (set_mmap_counter v) st) (write_to_mem m (wa (RCTX + 12)) (le4 (wz v))).
Proof.
intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6 & X7) & _).
pose proof (length_le4 (wz v)) as L4.
pose proof (munch_write [(RCTX + 12, RCTX + 16)] m m (RCTX + 12) (le4 (wz v)) (munch_refl _ m)
ltac:(unfold RCTX; lia) ltac:(rewrite L4; unfold RCTX; lia) ltac:(rewrite L4; cbn [inside]; lia)) as MU.
pose proof (wmono_write usegs m m (wa (RCTX + 12)) (le4 (wz v)) (wmono_refl usegs m)) as WM.
eapply (rmrep_ctx_frameW st (upd_ctx (set_mmap_counter v) st) m _ _ MR MU WM); try reflexivity.
- intros lo hi [E|[]]; inversion E; subst. unfold RCTX. lia.
- left.
pose proof (rw_cells_write usegs m RCTX (ctx_head_cells st) 12 (C4 (wz (c_mmap_counter (ctx st)))) (C4 (wz v)) X1 eq_refl eq_refl I) as W.
replace (RCTX + Z.of_nat 12) with (RCTX + 12) in W by reflexivity.
unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_mmap_counter c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
cbn [cell_upd csize Nat.eqb Nat.sub cbytes] in W. exact W.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold actives, active, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_active]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold usages, usage, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_usage]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold unmap_seqs, unmap_seq, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_unmap_seq]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold bouncess, bounces, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_bounces]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_seq c_brk]. reflexivity.
Qed.

End RC__1.
End Mqk.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCwx.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFqQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFqQ.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rDB32 : Z := 125613361.
Definition rdbi (k : Z) : Z := ((2 ^ k * rDB32) mod 2^32) / 2^27.

#[using="Type"] Lemma rdbi_range k : 0 <= rdbi k < 32.
Proof. unfold rdbi. pose proof (Z.mod_pos_bound (2^k * rDB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed.

Definition rdebruijn_bytes : list byte :=
Eval vm_compute in (match image_bytes usegs RDEBRUIJN 32 with Some bs => bs | None => [] end).

#[using="Type"] Lemma rdebruijn_ro : forall m, mem_inv usegs m -> ro_cells usegs m RDEBRUIJN [CB 32 rdebruijn_bytes].
Proof. intros m MI. apply (ro_cells_image usegs m); [exact MI | vm_compute; reflexivity | unfold RDEBRUIJN; lia | unfold RDEBRUIJN; cbn; lia]. Qed.

#[using="Type"] Lemma rdebruijn_read : forall m k, mem_inv usegs m -> 0 <= k < 32 ->
ov_read_bytes usegs m (wa (RDEBRUIJN + rdbi k)) 1 = Some [b8 k].
Proof.
intros m k MI Hk.
destruct (rdebruijn_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
pose proof (rdbi_range k) as R.
rewrite (bytes_at_read usegs m RDEBRUIJN rdebruijn_bytes (rdbi k) 1 B) by (cbn; lia).
assert (Hn : exists n, k = Z.of_nat n /\ (n < 32)%nat) by (exists (Z.to_nat k); split; [lia|lia]).
destruct Hn as (n & -> & Hn).
Ltac solve_db := vm_compute; reflexivity.
do 32 (destruct n as [|n]; [solve_db |]). lia.
Qed.

#[using="Type"] Lemma mul_srliw27 k : 0 <= k < 32 ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (2 ^ k * rDB32)))) 27) = rdbi k.
Proof.
intros Hk. unfold rdbi.
assert (P : 0 < 2 ^ k <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
rewrite unsigned_lit by (unfold rDB32; nia).
change (bv_wrap 32 (2 ^ k * rDB32)) with ((2 ^ k * rDB32) mod 2^32).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

Definition rclz_v4 (x : Z) : Z :=
let v1 := Z.lor (Z.shiftr x 2) x in
let v2 := Z.lor v1 (Z.shiftr x 1) in
let w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1) in
let w3 := Z.lor (Z.shiftr w2 4) w2 in
Z.lor (Z.shiftr w3 8) w3.
Definition rclz_pow (x : Z) : Z := Z.land (rclz_v4 x + 1) (Z.lxor (rclz_v4 x) 18446744073709551615).
Definition rclz_fn (x : Z) : bool := (rclz_pow x =? 2 ^ Z.log2 x) && (rclz_v4 x <? 2 ^ 13).
#[using="Type"] Lemma rclz_check_true : forallb rclz_fn (zseq 11 8181) = true.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma rclz_pow_eq x : 11 <= x < 8192 -> rclz_pow x = 2 ^ Z.log2 x /\ 0 <= rclz_v4 x < 2 ^ 13.
Proof.
intros Hx. pose proof (forallb_zseq rclz_fn 11 8181 x rclz_check_true ltac:(lia) ltac:(lia)) as X. unfold rclz_fn in X.
apply andb_prop in X. destruct X as [X1 X2].
apply Z.eqb_eq in X1. apply Z.ltb_lt in X2. split; [exact X1| split; [|exact X2]].
unfold rclz_v4. repeat first [apply Z.lor_nonneg; split | apply Z.shiftr_nonneg]; lia.
Qed.

#[using="Type"] Lemma lxor_4k_124 k : 3 <= k <= 12 -> Z.lxor (k * 4) 124 = 124 - 4 * k.
Proof. intros Hk. assert (H : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; reflexivity. Qed.

#[using="Type"] Lemma lor_even_1 a : 0 <= a -> Z.even a = true -> Z.lor a 1 = a + 1.
Proof. intros Ha He.
assert (D : Z.land a 1 = 0). { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2. rewrite Zeven_mod in He. apply Z.eqb_eq in He. exact He. }
rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity. Qed.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 (size_to_class n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0f00) fc None m' (seg_rom usegs)
/\ rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk usegs m' lo (bv_unsigned sp + -48)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

#[using="Type"] Lemma rmalloc_entry_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
a0 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
stk usegs m lo (bv_unsigned sp) -> 0x647000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
rw_cells usegs m RNEED_LOCKS [C1 (b8 0)] ->
evt usegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).
Proof.
intros until n. intros HA N ST ILO LO MI NL. subst a0.
pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rmalloc_entry, RNEED_LOCKS in *.
step. carve_frame 48%nat ST. step. step. step. step. step. step.

step. step. step.
step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.

step. step. step. step. step.
step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
clear K1.

step. step. step. step. step.
rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).

assert (LOCKJ : forall (a0' a1' a2' a3' : word) (sc : Z) (mj : mem),
sc = size_to_class n ->
mem_inv usegs mj -> rw_cells usegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk usegs mj lo (bv_unsigned sp + -48) ->
munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono usegs m mj -> rw_cells usegs mj 6576051 [C1 (b8 0)] ->
evt usegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 6576288) a0' a1' a2' a3' a4 a5 a6 a7
s2 (Z_to_bv 64 159624) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0ee8) fc None mj (seg_rom usegs))).
{ intros a0' a1' a2' a3' sc mj -> MIj FRj STj MUj WMj NLj.
step. step. rewrite ?zxb_b8 by lia. step. if_cases KL; zify_cond KL. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in KL by lia. lia. }
apply evt_done. unfold rentry_post, RMLOCK, RDEBRUIJN. do 5 eexists. split; [reflexivity|].
split; [exact FRj|]. split; [exact STj|]. split; [exact MUj|]. split; [exact WMj| exact MIj]. }
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
-
apply LOCKJ; try assumption.
rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
-
assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
destruct (rclz_pow_eq x XR) as [PW RV4].

step.
step. rewrite (unsigned_lit x), srliw_small by lia.
pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
step. rewrite (unsigned_lit x), srliw_small by lia.
step.
step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.

step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.

step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.

step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
assert (EW4 : w4 = rclz_v4 x) by reflexivity.

step. step. step.
rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
rewrite (unsigned_lit 0), Z.lor_0_l by lia.

step. step. rewrite (unsigned_lit w4) by lia.
step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
set (k := Z.log2 x) in *.
assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
assert (EX : x = q + 1) by reflexivity. clearbody x.
assert (K13 : 3 <= k <= 12) by (apply LG; lia).

step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
step. rewrite (mul_srliw27 k) by lia.
pose proof (rdbi_range k) as DR.
step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv usegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
step. rewrite ?zxb_b8 by lia. clear DBR.

step. step. step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step.
rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
replace (124 - 4 * k) with (120 - i) by lia.
assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
{ unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
clearbody i. clear EK.
pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.

step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 - (120 - i)) with (i + 1) by lia.
step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. step. replace (159656 + (i + 1) * 2) with (159656 + 2 * (i + 1)) by lia.
lazymatch goal with HI : mem_inv usegs ?mc |- _ => pose proof (rsize_classes_read mc (i + 1) HI ltac:(lia)) as RS1; unfold RSIZE_CLASSES in RS1 end.

step. rewrite ?zx16_wz by lia. clear RS1.

assert (J1 : forall (i1 c : Z) (mj : mem),
i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
mem_inv usegs mj -> rw_cells usegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk usegs mj lo (bv_unsigned sp + -48) ->
munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono usegs m mj -> rw_cells usegs mj 6576051 [C1 (b8 0)] ->
evt usegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 6576288)
(Z_to_bv 64 (120 - i)) (Z_to_bv 64 159656) (Z_to_bv 64 c) (Z_to_bv 64 (159656 + 2 * (i + 1))) a4 a5 a6 a7
s2 (Z_to_bv 64 159624) (Z_to_bv 64 q) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0ecc) fc None mj (seg_rom usegs))).
{ intros i1 c mj Hi1 Hc MIj FRj STj MUj WMj NLj.
assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
{ subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
destruct I1R as [I1R I1E].
pose proof (size_class_range i1 ltac:(lia)) as SR2.

step. rewrite (unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c - (120 - i)) with i1 by lia.
step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (159656 + i1 * 2) with (159656 + 2 * i1) by lia.
pose proof (rsize_classes_read mj i1 MIj ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
step. rewrite ?zx16_wz by lia. clear RS2.

step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
step. step.
destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
* rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
* rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
+
step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
+
step. step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.

Definition rentry_big_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a1 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0d68) fc None m' (seg_rom usegs)
/\ rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk usegs m' lo (bv_unsigned sp + -48)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

#[using="Type"] Lemma rentry_big_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
a0 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2^63 - 4097 ->
stk usegs m lo (bv_unsigned sp) -> 0x647000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
evt usegs (rentry_big_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).
Proof.
intros until n. intros HA N ST ILO LO MI. subst a0. unfold MMAP_THRESHOLD in N.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rmalloc_entry.
step. carve_frame 48%nat ST. step. step. step. step. step. step.
step. step. step.
step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.
step. step. step. step. step.
step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
clear K1.
apply evt_done. unfold rentry_big_post, RMLOCK. do 2 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -48) _ |- _ => split; [exact H|] end.
repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

Definition rentry_ovf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists a1 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ stk usegs m' lo (bv_unsigned sp)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' (errno_addr tp) [C4 (Z_to_bv 64 12)].

#[using="Type"] Lemma rentry_ovf_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z) (errv : word),
a0 = Z_to_bv 64 n -> 2^63 - 4097 <= n < 2^64 ->
stk usegs m lo (bv_unsigned sp) -> 0x647000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
rw_cells usegs m (errno_addr tp) [C4 errv] -> tp = Z_to_bv 64 RATP ->
evt usegs (rentry_ovf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).
Proof.
intros until errv. intros HA N ST ILO LO MI ERR TP. subst a0.
assert (ETP : bv_unsigned tp + -164 = 6444156) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rmalloc_entry.
step. carve_frame 48%nat ST. step. step. step. step. step. step.
step. step. step.
step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.

step. step. step. step.

step. step. step. step. step. step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m2 end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rentry_ovf_post. do 2 eexists. split; [reflexivity|].
split; [exact ST|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
lazymatch goal with H : rw_cells usegs m2 (bv_unsigned tp + -164) _ |- _ => exact H end.
Qed.

End RC__1.
