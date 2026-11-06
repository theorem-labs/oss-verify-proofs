(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Q6sh QQwg QKTr QJBH QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk QTVW QpY2 QOJv Q9Ho QqLk QnRU QmP7 QYyZ Qu3b QnaW QcfN QpME QkJ4 QQNJ QRfV QlES QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QTVW.Mq3 QOJv.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk QnRU.Mqa QmP7.Mq0 QpY2.Mq1 Q9Ho.Mq1 QYyZ.Mq0 QnRU.Mq0 QOJv.Mq5 Qu3b.Mq2 QnaW.Mq1 QYyZ.Mq5.
Import QpY2.Mq2.
Import QcfN.Mq1.
Import QpME.Mq1 QkJ4 QQNJ.Mq4 QQNJ.Mq5 QRfV.
Import QlES.
Export QVo2.

Import QpME.Mq4.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_1 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_2 := lia_walk_nf.

Local Ltac QkJ4.ctr H MU WM ::=
lazymatch type of MU with munch ?W ?ma ?mb =>
lazymatch type of H with ?P -> rw_cells _ _ ?A ?cs =>
let H' := fresh "CT" in
assert (H' : P -> rw_cells asegs mb A cs)
by (let p := fresh "p" in intros p; eapply (rw_cells_transport asegs W ma mb A cs); [exact (H p)| exact MU| exact WM|
cbn [disjoint_from cells_size csize Nat.add]; repeat match goal with |- _ /\ _ => split end; first [exact I | lia]]);
clear H; rename H' into H end end. Local Ltac mkr__ctr_3 H MU WM := lazymatch type of MU with munch ?W ?ma ?mb =>
lazymatch type of H with ?P -> rw_cells _ _ ?A ?cs =>
let H' := fresh "CT" in
assert (H' : P -> rw_cells asegs mb A cs)
by (let p := fresh "p" in intros p; eapply (rw_cells_transport asegs W ma mb A cs); [exact (H p)| exact MU| exact WM|
cbn [disjoint_from cells_size csize Nat.add]; repeat match goal with |- _ /\ _ => split end; first [exact I | lia]]);
clear H; rename H' into H end end.
Local Unset Keyed Unification.

Local Ltac Q0z1.sf_hide_poison ::= sf_hide_poison_divlit. Local Ltac mkr__sf_hide_poison_4 := sf_hide_poison_divlit.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Let atn := at_nodeA L asegs.

Local Notation alloc_W := (QVo2.alloc_W RE X).
Local Notation slot_W := (QVo2.slot_W RE).
Local Notation tzone_frame := (QVo2.tzone_frame RE X).

Definition alloc_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (n lo : Z) (m : word -> option byte) (obj tsz : Z) (q : list word)
(r : option aptr * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' G1,
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ RDepot RE X m' /\ depot_step m m'
/\ rw_cells asegs m' obj [C8 (wz (obj + 16)); C8 (wz tsz)] /\ u64arr asegs m' (obj + 16) q
/\ match r with
| (None, a1) => a0 = wz 0 /\ munch (alloc_W (bv_unsigned sp) (class_of n) (c_alloc_user (cls a (class_of n)))) m m'
/\ qframe a a1 /\ gstep RE X a a1 G G1 /\ RPrim a1 G1 RE X m'
| (Some p, a2) => exists a1 i,
p = APrim (as_next a1) n /\ a2 = set_next (N.succ (as_next a1)) a1 /\ qframe a a1
/\ gstep RE X a a1 G G1 /\ tag_at G1 (class_of n) i = Some TCached /\ 0 <= i
/\ a0 = wz (slot_beg RE (class_of n) i + rz_size n)
/\ munch (alloc_W (bv_unsigned sp) (class_of n) (c_alloc_user (cls a (class_of n))) ++ slot_W (class_of n) i) m m'
/\ (forall t, tag_prim t = false -> RPrim a1 (set_tag (class_of n) i t G1) RE X m')
/\ chunk_mem m' (slot_beg RE (class_of n) i) (slot_beg RE (class_of n) i + class_size (class_of n)) (slot_beg RE (class_of n) i + rz_size n) n
/\ hjunk m' (slot_beg RE (class_of n) i + rz_size n) (slot_beg RE (class_of n) i + class_size (class_of n))
end.

Lemma comb_W_pz : forall a LB FS G (sp c x lo hi : Z),
gcons a LB FS G RE X -> 1 <= c <= 31 -> band_lo <= sp - COMB_STACK ->
In (lo, hi) (comb_W RE X sp c (c_alloc_user (cls a c))) -> lo <= x < hi ->
fp_RPrim G RE X x \/ fp_RStats RE X x \/ band_lo <= x.
Proof.
intros a LB FS G sp c x lo hi GC Hc CSP Hin Hx.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
pose proof (gc_bounds _ _ _ _ _ _ GC c ltac:(rewrite K32; lia)) as (B1 & B2 & B3). rewrite KO in B2.
assert (NSL : forall c' i t, tag_at G c' i = Some t -> reg_beg (ae_L RE) c + c_alloc_user (cls a c) <= x < reg_beg (ae_L RE) c + 3758096384 ->
in_iv (slot_beg RE c' i, class_size c') x -> False).
{ intros c' i t Ht [X1 X2] [S1 S2]. cbn [fst snd] in S1, S2.
pose proof (tag_slot _ _ _ _ _ _ GC c' i t Ht) as (C1 & I1 & N1 & R1 & R2 & Q1 & Q2 & Z1 & Z2 & AL). rewrite KO in Q2.
pose proof (reg_geom RE X RL c' ltac:(lia)) as (RB' & _).
destruct (Z.eq_dec c c') as [<-|NE]; [lia|].
rewrite RB in X1, X2. rewrite RB' in R1, R2. assert (c + 1 <= c' \/ c' + 1 <= c) as [D|D] by lia; nia. }
assert (NSS : forall c' i t, tag_at G c' i = Some t ->
SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) <= x < SH (reg_beg (ae_L RE) c) + 3758096384 / 8 ->
in_sh (slot_beg RE c' i, class_size c') x -> False).
{ intros c' i t Ht [X1 X2] SS.
pose proof (tag_slot _ _ _ _ _ _ GC c' i t Ht) as (C1 & I1 & N1 & R1 & R2 & Q1 & Q2 & Z1 & Z2 & AL). rewrite KO in Q2.
pose proof (reg_geom RE X RL c' ltac:(lia)) as (RB' & _ & _ & _ & _ & _ & _).
apply in_sh_bounds in SS; [| Z.div_mod_to_equations; lia| lia]. destruct SS as [S1 S2].
change (3758096384 / 8) with 469762048 in X2. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048) in X2. change (8 * 469762048) with 3758096384 in X2.
destruct (Z.eq_dec c c') as [<-|NE].
- pose proof (SH_le _ _ R2). pose proof (SH_le (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) ltac:(lia)). lia.
- assert (c + 1 <= c' \/ c' + 1 <= c) as [D|D] by lia.
+ assert (LE : reg_beg (ae_L RE) c + 3758096384 <= slot_beg RE c' i) by (rewrite RB; rewrite RB' in R1; lia).
pose proof (SH_le _ _ LE). lia.
+ assert (LE : slot_beg RE c' i + class_size c' <= reg_beg (ae_L RE) c + c_alloc_user (cls a c)) by (rewrite RB; rewrite RB' in R2; lia).
pose proof (SH_le _ _ LE). lia. }
unfold comb_W, COMB_STACK, ri_addr in Hin. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; injection E as <- <-.
- do 2 right. unfold COMB_STACK in CSP. lia.
- destruct (Z.lt_ge_cases x (rl_T X + 2800)) as [LT|GE].
+ left. right; left. split; cbn [fst snd]; lia.
+ right; left. left. split; cbn [fst snd]; lia.
- left. left. split; cbn [fst snd]; lia.
- left. do 2 right; left. exists c. rewrite K32. split; [lia| lia].
- left. do 3 right; left. exists c. rewrite K32. split; [lia|]. split; cbn [fst snd]; rewrite ?KS; [lia|]. change (536870912 / 8) with 67108864 in *. lia.
- left. do 4 right; left. split.
+ exists c. rewrite K32, KO. split; [lia| lia].
+ intros (c' & i & t & Ht & _ & IN). exact (NSL c' i t Ht ltac:(lia) IN).
- left. do 5 right. split.
+ exists c. rewrite K32, KO. split; [lia|]. split; cbn [fst snd]; [| change (3758096384 / 8) with 469762048; lia].
eapply Z.le_trans; [| apply (proj1 Hx)]. apply SH_le. lia.
+ intros (c' & i & t & Ht & _ & IN). exact (NSS c' i t Ht ltac:(change (3758096384 / 8) with 469762048; lia) IN).
Qed.

Lemma too_big_prim : forall n, 0 <= n -> from_primary n = true -> too_big n = false.
Proof.
intros n Hn HP. unfold too_big. rewrite HP. apply from_primary_iff in HP. unfold kMaxSize in HP. unfold kMaxAllowedMalloc.
replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb]. apply Z.ltb_ge. lia.
Qed.

Lemma allocate_prim_spec : forall ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (LB : list ablock) (FS : list fframe)
(n cf lo obj tsz dn : Z) (q : list word),
gcons a LB FS G RE X ->
RTconst RE X m -> RStats RE X m -> RPrim a G RE X m -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ALLOC_STACK ->
0 <= n -> from_primary n = true -> 0 <= cf <= 1 ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz tsz)] -> u64arr asegs m (obj + 16) q -> Z.of_nat (length q) = 30 ->
1 <= tsz <= 30 -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= obj -> obj + 256 < 2^64 ->
aimplT atn (asan_malloc (ae_L RE) a n) s
(alloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G n lo m obj tsz q)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz n) (wz 8) (wz obj) (wz 1) (wz cf) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz allocate_entry) fc None m (seg_rom asegs)).
Proof.
intros until q; intros GC RT RS RP RD MI ST CEIL LO Hn HP CF OBJ TRQ LQ SZR DNH DCAP OB1 OB2.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof CEIL as CEIL'. idtac. unfold ALLOC_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB. idtac. rewrite ?KHI_eq in TK.
unfold iv_disjoint in TD. cbn [fst snd] in TD.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & ND & _). cbn [fst snd] in NK, NC. unfold iv_disjoint in ND. cbn [fst snd] in ND. idtac. rewrite ?KHI_eq in NK.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & BD & _). cbn [fst snd] in BK, BC. unfold iv_disjoint in BD. cbn [fst snd] in BD. idtac. rewrite ?KHI_eq in BK.
pose proof (class_of_facts n Hn HP) as (Hc & Csz & Csz32 & Crz & _). cbv zeta in Hc, Csz, Csz32, Crz.
set (c := class_of n) in *.
pose proof (needed_facts n Hn) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
pose proof HP as HP'. apply from_primary_iff in HP'. unfold kMaxSize in HP'.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (SHB1 : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite FB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD0.
assert (SHB2 : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD1.
pose proof (gc_bounds _ _ _ _ _ _ GC c ltac:(rewrite K32; lia)) as (AU1 & AU2 & AU3). rewrite KO in AU2.
assert (SHB3 : SH (reg_beg (ae_L RE) c) <= SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048). apply SH_le. lia. }
clear PAL AU3.
pose proof (munch_refl (alloc_W (bv_unsigned sp) c (c_alloc_user (cls a c))) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
apply aimplT_from_evt.

eapply alloc_pre1; [exact RT| exact RL| exact MI| exact ST| exact CEIL'| lia| lia| lia|].
intros m1 u0 u1 u2 u3 v1 v2 v3 v4 v5 v6 v7 u4 u5 u6 u7 fj MU1 WM1 MI1 ST1 FR1.
assert (RT1 : RTconst RE X m1) by (eapply RTconst_munch; [exact RT| exact MU1| exact WM1| apply Forall_cons; [apply rt_avoid_stack; [exact RL| lia]| apply Forall_nil]]).
assert (RS1 : RStats RE X m1) by (eapply RStats_munch; [exact RS| exact MU1| exact WM1| apply Forall_cons; [st_avoid_solve| apply Forall_nil]]).
assert (RP1 : RPrim a G RE X m1) by (eapply RPrim_stack; [exact RP| exact RL| exact MU1| exact WM1| apply Forall_cons; [cbn [fst]; lia| apply Forall_nil]]).
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame; [exact RD| exact WM1|]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z Fz _. cbn [outside]. split; [| exact I].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). lia. }
phase_done MU m m1 MU1 WM1. clear MI RT RS RP RD.
eapply alloc_rzlog; [lia|]. intros a0'.
eapply alloc_pre3; [exact RT1| exact RL| exact MI1| exact ST1| exact CEIL'| lia| exact Hn| exact HP|].
intros m2 w0 w1 w2 w3 x0 x1 x2 x3 x4 x5 x6 x7 w4 w5 w6 w7 MU2 WM2 MI2 ST2.
assert (RT2 : RTconst RE X m2) by (eapply RTconst_munch; [exact RT1| exact MU2| exact WM2| apply Forall_cons; [apply rt_avoid_stack; [exact RL| lia]| apply Forall_nil]]).
assert (RS2 : RStats RE X m2) by (eapply RStats_munch; [exact RS1| exact MU2| exact WM2| apply Forall_cons; [st_avoid_solve| apply Forall_nil]]).
assert (RP2 : RPrim a G RE X m2) by (eapply RPrim_stack; [exact RP1| exact RL| exact MU2| exact WM2| apply Forall_cons; [cbn [fst]; lia| apply Forall_nil]]).
assert (RD2 : RDepot RE X m2).
{ eapply RDepot_frame; [exact RD1| exact WM2|]. eapply agree_on_of_munch; [exact MU2| exact WM2|]. intros z Fz _. cbn [outside]. split; [| exact I].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). lia. }
phase_done MU m1 m2 MU2 WM2. clear MI1 RT1 RS1 RP1 RD1. try clear ST1.

pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp - 128)] m2) as MUs. pose proof (wmono_refl asegs m2) as WMs.
step. call_sp_ch (get_current_thread_spec RE X) ltac:(fun _ => idtac); [exact RT2| exact RL| assumption| exact ST2| exact CEIL'| lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST3 end.
match goal with H : RTconst RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RT3; rename H2 into MI3 end.
lazymatch type of MUs with munch _ _ ?mm =>
assert (RS3 : RStats RE X mm) by (eapply RStats_munch; [exact RS2| exact MUs| exact WMs| apply Forall_cons; [st_avoid_solve| apply Forall_nil]]);
assert (RP3 : RPrim a G RE X mm) by (eapply RPrim_stack; [exact RP2| exact RL| exact MUs| exact WMs| apply Forall_cons; [cbn [fst]; lia| apply Forall_nil]]);
assert (RD3 : RDepot RE X mm) by
(eapply RDepot_frame; [exact RD2| exact WMs|]; eapply agree_on_of_munch; [exact MUs| exact WMs|]; intros z Fz _; cbn [outside]; split; [| exact I];
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)); lia)
end.
clear MUs WMs RT2 RS2 RP2 RD2. try clear ST2. try clear MI2.
step.
step. unfold_cond; cond_unsig; if_false.
step. stp. step. step.
step.
apply evt_done.
unfold asan_malloc. rewrite (too_big_prim n Hn HP), HP. fold c.
name_sp sp (-128). rewrite <- Hsp in ST3.
lazymatch goal with |- aimplT _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
eapply aimplT_bind;
[eapply aimplT_tall; [apply cache_alloc_qframe|
eapply (combined_prim_spec L RE X _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm s a G (needed n) lo);
[exact RT3| exact RL| exact RS3| exact RP3| exact MI3| exact ST3| exact CEIL'| rewrite Hsp; unfold COMB_STACK; lia| lia]] |] end.
intros [ok a1] s' ms' [QF PO]. cbn [snd] in QF. unfold comb_post in PO. rewrite Hsp in PO. unname_sp.
change (class_id (needed n)) with c in PO. cbn [fst snd] in PO.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & G1 & -> & -> & MU3 & WM3 & MI4 & ST4 & RT4 & RS4 & GS & REST).
replace (ret_pc (wz 258824)) with (wz 258824) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

lazymatch type of MU3 with munch _ ?mp _ =>
assert (RD4 : RDepot RE X m3) by
(eapply RDepot_frame; [exact RD3| exact WM3|]; eapply agree_on_of_munch; [exact MU3| exact WM3|]; intros z Fz _; apply outside_intro;
intros lo' hi' Hin Hz; destruct (comb_W_pz a LB FS G (bv_unsigned sp + -128) c z lo' hi' GC ltac:(lia) ltac:(idtac; unfold COMB_STACK; lia) Hin Hz) as [P|[P|P]];
[ exact (fpP_RDepot _ _ _ _ _ _ GC z P Fz) | exact (fpS_excl _ _ _ _ _ _ GC z P ltac:(do 2 right; left; exact Fz))
| pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)); lia ]) end.
unfold comb_W, COMB_STACK, ri_addr in MU3. rewrite ?KS, ?KO in MU3.
change (536870912 / 8) with 67108864 in MU3. change (3758096384 / 8) with 469762048 in MU3.
lazymatch type of MU3 with munch _ ?mp _ => phase_done MU mp m3 MU3 WM3 end.
clear RD3 RT3 RS3 RP3. try clear MI3. try clear ST3.
pose proof (GS) as (_ & _ & _ & GCT). pose proof (GCT LB FS GC) as GC1.
unfold alloc_frame in FR1.
destruct ok.
2:{
destruct REST as [-> RP4]. cbn [negb]. apply aimplT_ret.
step.
step. if_lit.
pose proof (munch_refl [(0x171d60, 0x171d61); (bv_unsigned sp - 144, bv_unsigned sp - 128)] m3) as MUs. pose proof (wmono_refl asegs m3) as WMs.
step. call_sp_ch (set_oom_spec RE X) ltac:(fun _ => idtac); [exact RS4| assumption| exact ST4| exact CEIL'|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST5 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS5; rename H2 into MI5 end.
lazymatch type of MUs with munch _ _ ?mm =>
destruct (sz_frame RE X a1 LB FS G1 m3 mm _ GC1 MUs WMs) as (FT & FP & FD);
[ intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-; [left; do 2 right; lia| right; idtac; lia] |] end.
pose proof (FT RT4) as RT5. pose proof (FP RP4) as RP5. pose proof (FD RD4) as RD5. clear FT FP FD MUs WMs RT4 RP4 RD4 RS4.
step. call0 (may_return_null_spec RE X); [exact RT5| assumption|]. subst_words.
step. if_lit.
stp. step.
step. do 13 step. step.
release_frame FR1 ST5 (bv_unsigned sp).
step.
apply evt_done. unfold alloc_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST5|].
split; [exact RT5|]. split; [exact RS5|]. split; [exact RD5|].
split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn; split; [split; [unfold DP_N; exact DNC| exact DNP]| lia]]|].
split; [exact OBJ|]. split; [exact TRQ|].
cbn [fst snd]. split; [reflexivity|]. split; [| split; [exact QF| split; [exact GS| exact RP5]]].
unfold alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }

destruct REST as (i & TI & -> & RPF & HJ & SHD). cbn [negb]. apply aimplT_ret.
pose proof (RPF TQOwn eq_refl) as RPq.
destruct (RPrim_open _ _ _ _ _ RPq) as (K & _ & GNE & HCall).
pose proof (rprim_slot_geom a1 (set_tag c i TQOwn G1) RE X K m3 c i TQOwn GNE HCall (tag_at_set_tag_eq _ _ _ _ _ TI))
as (_ & I0 & S32 & _ & RBq & SL1 & SL2 & AU1' & AU2' & SBE & _).
clear K GNE HCall. rewrite KO in AU2'.
pose proof (slot_beg_align RE X c i RL ltac:(lia)) as [AL16 _].
set (AB := slot_beg RE c i) in *.
assert (PAB : prim_lo RE <= AB) by lia.
assert (ABP : AB + class_size c <= prim_lo RE + 2^37) by lia.
assert (SHAB : 2201439137792 <= SH AB /\ SH AB + class_size c / 8 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; clear - PAB ABP PK PH PCH Csz; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD2.
assert (SHA : SH (AB + rz_size n) = SH AB + rz_size n / 8) by (rewrite <- SH_plus8; f_equal; clear - RZ2; Z.div_mod_to_equations; lia).
assert (FIT : rz_size n + round_up (used_size n) 8 <= class_size c).
{ assert (RU : round_up (used_size n) 8 <= round_up (Z.max n 8) 8) by (unfold round_up, used_size; clear; Z.div_mod_to_equations; lia).
unfold needed in Csz. lia. }
pose proof (ngran_eq (used_size n) ltac:(unfold used_size; lia)) as (NG1 & NG2 & NG3).
pose proof (round_up_8 (used_size n) ltac:(unfold used_size; lia)) as [RU8 _].
assert (US : 1 <= used_size n <= Z.max n 8) by (unfold used_size; lia).

apply (munch_weaken _ ((AB, AB + class_size c) :: (SH AB, SH AB + class_size c / 8) :: alloc_W (bv_unsigned sp) c (c_alloc_user (cls a c)))) in MU.
2:{ unfold alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048.
intros z Hz. cbn [outside] in Hz |- *. clear - Hz. tauto. }
unfold alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END in MU. rewrite ?KS, ?KO in MU. change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.

destruct (slot_pieces m3 AB (class_size c) (rz_size n) (used_size n) HJ SHD ltac:(lia) RZ2 AL16 ltac:(lia)
FIT ltac:(clear - Csz32; Z.div_mod_to_equations; lia))
as (b0 & b1 & h & w & d & g1 & g2 & HDR & HJU & HJm & MG & P1 & R1 & P2 & P3 & R4).

assert (Hsz8 : 8 * (class_size c / 8) = class_size c) by (clear - Csz32; Z.div_mod_to_equations; lia).
assert (Hrz8 : 8 * (rz_size n / 8) = rz_size n) by (clear - RZ2; Z.div_mod_to_equations; lia).
assert (Hrz16 : exists r16, rz_size n = 16 * r16) by (exists (rz_size n / 16); clear - RZ2; Z.div_mod_to_equations; lia). destruct Hrz16 as [r16 Hrz16].
assert (Hn8 : used_size n = 8 * (used_size n / 8) + used_size n mod 8 /\ 0 <= used_size n mod 8 < 8) by (clear - US; Z.div_mod_to_equations; lia).
assert (Hng : (used_size n mod 8 = 0 -> ngran (used_size n) = used_size n / 8) /\ (used_size n mod 8 <> 0 -> ngran (used_size n) = used_size n / 8 + 1))
by (rewrite NG1; unfold round_up; clear - US; Z.div_mod_to_equations; lia).
assert (Hk4 : 8 * ((class_size c - rz_size n - round_up (used_size n) 8) / 8) = class_size c - rz_size n - 8 * ngran (used_size n))
by (rewrite NG3; clear - Hsz8 Hrz8; Z.div_mod_to_equations; lia).
clear NG1. hide TA. hide Csz32. hide RZ2. hide AL16.
destruct NF as (NF1 & NF2 & NF8 & NF3). hide NF8.

set (Gq := set_tag c i TQOwn G1) in RPq.
assert (TIq : tag_at Gq c i = Some TQOwn) by (apply (tag_at_set_tag_eq _ _ _ _ _ TI)).
assert (GCq : gcons a1 LB FS Gq RE X) by (apply (gcons_retag_nonlive _ _ _ _ _ _ _ _ _ _ GC1 TI eq_refl); [intros q0; reflexivity| reflexivity]).
assert (QZs : forall z, AB <= z < AB + class_size c -> fp_RQuar a1 LB Gq RE X z).
{ intros z Hz. do 5 right; left. exists c, i, TQOwn. split; [exact TIq|]. split; [reflexivity|]. split; cbn [fst snd]; lia. }
assert (QZh : forall z, SH AB <= z < SH AB + class_size c / 8 -> fp_RQuar a1 LB Gq RE X z).
{ intros z Hz. do 6 right; left. exists c, i, TQOwn. split; [exact TIq|]. split; [reflexivity|]. split; cbn [fst snd]; fold AB; lia. }
assert (NSs : forall z, AB <= z < AB + class_size c -> ~ fp_RStats RE X z) by (intros z Hz Fz; exact (fpQ_RStats _ _ _ _ _ _ GCq z (QZs z Hz) Fz)).
assert (NSh : forall z, SH AB <= z < SH AB + class_size c / 8 -> ~ fp_RStats RE X z) by (intros z Hz Fz; exact (fpQ_RStats _ _ _ _ _ _ GCq z (QZh z Hz) Fz)).
assert (NSt : forall z, band_lo <= z -> ~ fp_RStats RE X z) by (intros z Hz Fz; pose proof (fp_lt_ceil _ _ _ _ _ _ GCq z ltac:(right; left; exact Fz)); lia).
assert (NSd : forall z, fp_RDepot RE X z -> ~ fp_RStats RE X z) by (intros z Hz Fz; exact (fpS_excl _ _ _ _ _ _ GCq z Fz ltac:(do 2 right; left; exact Hz))).
assert (NDs : forall z, AB <= z < AB + class_size c -> ~ fp_RDepot RE X z) by (intros z Hz Fz; exact (fpQ_RDepot _ _ _ _ _ _ GCq z (QZs z Hz) Fz)).
assert (NDh : forall z, SH AB <= z < SH AB + class_size c / 8 -> ~ fp_RDepot RE X z) by (intros z Hz Fz; exact (fpQ_RDepot _ _ _ _ _ _ GCq z (QZh z Hz) Fz)).
assert (NDt : forall z, band_lo <= z -> ~ fp_RDepot RE X z) by (intros z Hz Fz; pose proof (fp_lt_ceil _ _ _ _ _ _ GCq z ltac:(do 5 right; left; exact Fz)); lia).
assert (NDst : forall z, fp_RStats RE X z -> ~ fp_RDepot RE X z) by (intros z Hz Fz; exact (fpS_excl _ _ _ _ _ _ GCq z Hz ltac:(do 2 right; left; exact Fz))).
idtac.
step.
step. unfold_cond; cond_unsig; if_false.

eapply (alloc_hdr RE X n i gp RL Hn HP PAB ABP AL16); [exact RT4| exact MI4| exact ST4| exact CEIL'| lia| exact FR1| exact HDR|].
intros m4 h0 h1 h2 h3 h5 h6 h7 MU4 WM4 MI5 ST5 FR5 HDR5 RT5.
refold RE n c i AB MU4. refold RE n c i AB HDR5.
try replace (class_of n) with c by reflexivity. try replace (slot_beg RE c i) with AB by reflexivity.
destruct (tzone_frame a1 LB FS Gq c i m3 m4 _ GCq TIq MU4 WM4) as (FP & FS' & FD).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; left. split; cbn [fst snd]; lia. }
pose proof (FP RPq) as RP5.
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; apply NSs; lia) RS4) as RS5.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; apply NDs; lia) RD4) as RD5.
clear FP FS' FD.
ctr MG MU4 WM4. ctr P2 MU4 WM4. ctr P3 MU4 WM4.
pose proof (hjunk_wmono _ _ _ _ HJU WM4) as HJU5. pose proof (hjunk_wmono _ _ _ _ HJm WM4) as HJm5.
clear HDR FR1 SHD RPF HJ HJU HJm RT4 RS4 RD4 RPq. try clear MI4. try clear ST4.
phase_done MU m3 m4 MU4 WM4.

eapply (alloc_depot RE X n i gp RL Hn HP PAB ABP AL16);
[exact RT5| exact RD5| exact MI5| exact ST5| exact CEIL'| lia| exact OBJ| exact TRQ| exact LQ| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| lia| lia| exact HDR5|].
intros m5 d0 d1 d2 d5 d6 d7 d10 d11 d12 d13 d14 d15 d16 d17 id MU5 WM5 MI6 ST6 RT6 RD6 OBJ6 TRQ6 ID (dn6 & [DNC6 DNP6] & DNR6) HDR6. unfold DP_N in DNC6.
unfold depot_W, SS_BASE, DP_END in MU5. refold RE n c i AB MU5. refold RE n c i AB HDR6.
try replace (class_of n) with c by reflexivity. try replace (slot_beg RE c i) with AB by reflexivity.
clear OBJ TRQ.
destruct (tzone_frame a1 LB FS Gq c i m4 m5 _ GCq TIq MU5 WM5) as (FP & FS' & FD).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-.
- right; left. split; cbn [fst snd]; lia.
- left. idtac. lia.
- do 4 right. left. split; cbn [fst snd]; lia.
- do 4 right. right; left. split; cbn [fst snd]; lia.
- do 4 right. do 2 right; left. split; cbn [fst snd]; lia. }
pose proof (FP RP5) as RP6.
assert (NS5 : forall lo hi z, In (lo, hi) [(AB + rz_size n + -8, AB + rz_size n); (bv_unsigned sp - 352, bv_unsigned sp - 128); (1841608, 6363632); (rl_dn X, rl_dn X + 1048576); (rl_ssb X, rl_ssb X + 8388608)] -> lo <= z < hi -> ~ fp_RStats RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-.
- apply NSs. lia.
- apply NSt. lia.
- apply NSd. left. split; cbn [fst snd]; lia.
- apply NSd. right; left. split; cbn [fst snd]; lia.
- apply NSd. do 2 right; left. split; cbn [fst snd]; lia. }
pose proof (FS' NS5 RS5) as RS6. clear FP FS' FD NS5.
ctr MG MU5 WM5. ctr P2 MU5 WM5. ctr P3 MU5 WM5.
pose proof (hjunk_wmono _ _ _ _ HJU5 WM5) as HJU6. pose proof (hjunk_wmono _ _ _ _ HJm5 WM5) as HJm6.
clear HDR5 RT5 RS5 RD5 RP5 HJU5 HJm5. try clear MI5. try clear ST5.

assert (AGZ : agree_on asegs (fun z => SH AB <= z < SH AB + class_size c / 8) m4 m5).
{ eapply agree_on_of_munch; [exact MU5| exact WM5|]. intros z Hz _. cbn [outside].
repeat split; try exact I; intros [Y1 Y2]; clear - Hz Y1 Y2 SHAB SHBD0 PK PAB CEIL LO SPR NK BK RZ1; unfold prim_lo in *; lia. }
apply (rw_cells_agree asegs _ _ _ _ _ AGZ) in R4;
[| intros z Hz; cbn [cells_size csize Nat.add] in Hz; clear - Hz SHA Hk4 Hsz8 Hrz8 NG2 NG3 FIT RZ1; lia].
clear AGZ.
phase_done MU m4 m5 MU5 WM5.

eapply (alloc_shadow RE X n i gp RL Hn HP PAB ABP AL16);
[exact RT6| exact MI6| exact ST6| exact CEIL'| lia| exact P1| exact P2| exact P3|].
intros m6 e e0 e1 e2 e3 e4 e5 e6 e7 e10 e11 e12 e14 e15 e16 e17 e22 MU6 WM6 MI7 ST7 RT7 P1' P2' P3'.
refold RE n c i AB MU6. refold RE n c i AB P1'. refold RE n c i AB P2'. refold RE n c i AB P3'.
try replace (class_of n) with c by reflexivity. try replace (slot_beg RE c i) with AB by reflexivity.
clear P1 P2 P3.
assert (SHin : forall z, SH (AB + rz_size n) <= z < SH (AB + rz_size n) + ngran (used_size n) -> SH AB <= z < SH AB + class_size c / 8) by (intros z Hz; lia).
destruct (tzone_frame a1 LB FS Gq c i m5 m6 _ GCq TIq MU6 WM6) as (FP & FS' & FD).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
- left. idtac. lia.
- do 2 right; left. split; cbn [fst snd]; fold AB; pose proof (SHin z Hz); lia. }
pose proof (FP RP6) as RP7.
assert (NZ6 : forall lo hi z, In (lo, hi) [(bv_unsigned sp - 192, bv_unsigned sp - 128); (SH (AB + rz_size n), SH (AB + rz_size n) + ngran (used_size n))] -> lo <= z < hi ->
~ fp_RStats RE X z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
- split; [apply NSt| apply NDt]; lia.
- split; [apply NSh| apply NDh]; apply SHin; exact Hz. }
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; exact (proj1 (NZ6 lo' hi' z Hin Hz))) RS6) as RS7.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (NZ6 lo' hi' z Hin Hz))) RD6) as RD7.
clear FP FS' FD NZ6.
ctr MG MU6 WM6.
pose proof (hjunk_wmono _ _ _ _ HJU6 WM6) as HJU7. pose proof (hjunk_wmono _ _ _ _ HJm6 WM6) as HJm7.
clear RT6 RS6 RD6 RP6 HJU6 HJm6. try clear MI6. try clear ST6.
phase_done MU m5 m6 MU6 WM6.

eapply (alloc_stats RE X n i gp RL Hn HP PAB ABP AL16); [exact RT7| exact RS7| exact MI7| exact ST7| exact CEIL'| lia|].
intros m7 f0 f1 f2 f3 f4 f5 f6 f7 f10 f11 f12 f14 f15 f16 f17 MU7 WM7 MI8 ST8 RT8 RS8.
refold RE n c i AB MU7.
try replace (class_of n) with c by reflexivity. try replace (slot_beg RE c i) with AB by reflexivity.
destruct (tzone_frame a1 LB FS Gq c i m6 m7 _ GCq TIq MU7 WM7) as (FP & FS' & FD).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- left. idtac. lia.
- do 3 right; left. left. split; cbn [fst snd]; lia.
- do 3 right; left. left. split; cbn [fst snd]; lia. }
pose proof (FP RP7) as RP8.
assert (ND7 : forall lo hi z, In (lo, hi) [(bv_unsigned sp - 160, bv_unsigned sp - 128); (rl_T X + 2800, rl_T X + 2824); (rl_T X + 2912 + 8 * c, rl_T X + 2912 + 8 * c + 8)] -> lo <= z < hi -> ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- apply NDt. lia.
- apply NDst. left. split; cbn [fst snd]; lia.
- apply NDst. left. split; cbn [fst snd]; lia. }
pose proof (FD ND7 RD7) as RD8. clear FP FS' FD ND7.
ctr MG MU7 WM7. ctr P2' MU7 WM7. ctr P3' MU7 WM7.
pose proof (hjunk_wmono _ _ _ _ HJU7 WM7) as HJU8. pose proof (hjunk_wmono _ _ _ _ HJm7 WM7) as HJm8.
clear RT7 RS7 RD7 RP7 HJU7 HJm7. try clear MI7. try clear ST7.

assert (AGZ2 : agree_on asegs (fun z => (AB <= z < AB + class_size c) \/ (SH AB <= z < SH AB + class_size c / 8)) m6 m7).
{ eapply agree_on_of_munch; [exact MU7| exact WM7|]. intros z Hz _. cbn [outside].
repeat split; try exact I; intros [Y1 Y2];
clear - Hz Y1 Y2 SHAB SHBD0 PK PAB ABP PH PCH CEIL LO SPR TK TB TD RZ1 Hc; unfold prim_lo, prim_hi in *; lia. }
apply (rw_cells_agree asegs _ _ _ _ _ AGZ2) in R4;
[| intros z Hz; right; cbn [cells_size csize Nat.add] in Hz; clear - Hz SHA Hk4 Hsz8 Hrz8 NG2 NG3 FIT RZ1; lia].
apply (rw_cells_agree asegs _ _ _ _ _ AGZ2) in HDR6;
[| intros z Hz; left; cbn [cells_size csize Nat.add] in Hz; clear - Hz FIT RZ1 NG2 NG3; lia].
clear AGZ2.
lazymatch type of MU with munch ?W ?m0 _ => lazymatch type of MU7 with munch ?Wk _ _ =>
assert (SF : sub_fp Wk W) by sub_fp_solve;
pose proof (munch_chain W Wk m0 m6 m7 MU MU7 SF) as MU'; clear MU SF; rename MU' into MU end end.
transport_after_call asegs m6 m7 MU7 WM7. clear MU7 WM7.

eapply (alloc_fill RE X n i gp RL Hn HP PAB ABP AL16); [exact RT8| exact MI8| exact ST8| exact CEIL'| lia| exact FR5| exact CF| exact HJU8|].
intros m8 g g0 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g14 g15 g16 g17 MU8 WM8 MI9 ST9 RT9 FR9 HJU9.
refold RE n c i AB MU8. refold RE n c i AB HJU9.
try replace (class_of n) with c by reflexivity. try replace (slot_beg RE c i) with AB by reflexivity.
clear FR5.
destruct (tzone_frame a1 LB FS Gq c i m7 m8 _ GCq TIq MU8 WM8) as (FP & FS' & FD).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; left. split; cbn [fst snd]; lia. }
pose proof (FP RP8) as RP9.
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; apply NSs; lia) RS8) as RS9.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; apply NDs; lia) RD8) as RD9.
clear FP FS' FD.
ctr MG MU8 WM8. ctr P2' MU8 WM8. ctr P3' MU8 WM8.
pose proof (hjunk_wmono _ _ _ _ HJm8 WM8) as HJm9.
clear RT8 RS8 RD8 RP8 HJU8 HJm8. try clear MI8. try clear ST8.
phase_done MU m7 m8 MU8 WM8.

eapply (alloc_fin RE X n i gp RL Hn HP PAB ABP AL16); [exact RT9| exact MI9| exact ST9| exact CEIL'| lia| exact FR9| exact HDR6| exact MG|].
intros m9 k0 k1 k2 k4 k5 k6 k7 k10 k11 k12 k14 k15 k16 k17 MU9 WM9 MI10 ST10 RT10 HDR10 MG10.
refold RE n c i AB MU9. refold RE n c i AB HDR10. refold RE n c i AB MG10.
clear FR9 HDR6 MG.
destruct (tzone_frame a1 LB FS Gq c i m8 m9 _ GCq TIq MU9 WM9) as (FP & FS' & FD).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- left. idtac. lia.
- right; left. split; cbn [fst snd]; lia.
- right; left. split; cbn [fst snd]; lia. }
pose proof (FP RP9) as RP10.
assert (NZ9 : forall lo hi z, In (lo, hi) [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (AB + rz_size n + -16, AB + rz_size n)] -> lo <= z < hi ->
~ fp_RStats RE X z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- split; [apply NSt| apply NDt]; lia.
- split; [apply NSs| apply NDs]; lia.
- split; [apply NSs| apply NDs]; lia. }
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; exact (proj1 (NZ9 lo' hi' z Hin Hz))) RS9) as RS10.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (NZ9 lo' hi' z Hin Hz))) RD9) as RD10.
clear FP FS' FD NZ9.
ctr P2' MU9 WM9. ctr P3' MU9 WM9.
pose proof (hjunk_wmono _ _ _ _ HJU9 WM9) as HJU10. pose proof (hjunk_wmono _ _ _ _ HJm9 WM9) as HJm10.
clear RT9 RS9 RD9 RP9 HJU9 HJm9. try clear MI9. try clear ST9.
phase_done MU m8 m9 MU9 WM9.

try replace (class_of n) with c by reflexivity. try replace (slot_beg RE c i) with AB by reflexivity.
apply evt_done. unfold alloc_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [exact MI10|]. split; [exact ST10|].
split; [exact RT10|]. split; [exact RS10|]. split; [exact RD10|].
split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn6; split; [split; [unfold DP_N; exact DNC6| exact DNP6]| exact DNR6]]|].
split; [exact OBJ6|]. split; [exact TRQ6|].
cbn [fst snd]. exists a1, i.
split; [reflexivity|]. split; [reflexivity|]. split; [exact QF|]. split; [exact GS|]. split; [exact TI|]. split; [exact I0|]. split; [reflexivity|].
split.
{ unfold alloc_W, slot_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048.
fold c. fold AB. eapply munch_weaken; [| exact MU]. sub_fp_solve. }
split.
{ intros t Ht. pose proof (RPrim_retag _ _ _ _ _ _ _ _ t RP10 TIq eq_refl Ht) as RPt.
destruct (retag_twice G1 c i TCached TQOwn t tag_prim TI I0) as [SL SG].
eapply RPrim_ext; [exact RPt| intros; reflexivity| reflexivity| exact SL| exact SG]. }
split; [| exact HJU10].
unhide RZ2. unhide AL16. unhide Csz32.
pose proof (hb1_facts b1) as [_ HBF].
eapply (@slot_chunk BAND m9 AB (class_size c) n (hb1f b1) (wz id) Hn ltac:(lia) RZ2 AL16 FIT
ltac:(clear - Csz32; Z.div_mod_to_equations; lia) ltac:(rewrite ?KHI_eq; lia) ltac:(idtac; lia) HBF
MG10 HJm10 HDR10 HJU10 P1' R1 P2' P3' R4).
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcfN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcfN.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpF1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRfV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRfV.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QVo2.Mq2.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_1 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_2 := lia_walk_nf.

Local Ltac QpF1.ctr H MU WM ::=
lazymatch type of MU with munch ?W ?ma ?mb =>
lazymatch type of H with ?P -> rw_cells _ _ ?A ?cs =>
let H' := fresh "CT" in
assert (H' : P -> rw_cells asegs mb A cs)
by (let p := fresh "p" in intros p; eapply (rw_cells_transport asegs W ma mb A cs); [exact (H p)| exact MU| exact WM|
cbn [disjoint_from cells_size csize Nat.add]; repeat match goal with |- _ /\ _ => split end; first [exact I | lia]]);
clear H; rename H' into H end end. Local Ltac mkr__ctr_3 H MU WM := lazymatch type of MU with munch ?W ?ma ?mb =>
lazymatch type of H with ?P -> rw_cells _ _ ?A ?cs =>
let H' := fresh "CT" in
assert (H' : P -> rw_cells asegs mb A cs)
by (let p := fresh "p" in intros p; eapply (rw_cells_transport asegs W ma mb A cs); [exact (H p)| exact MU| exact WM|
cbn [disjoint_from cells_size csize Nat.add]; repeat match goal with |- _ /\ _ => split end; first [exact I | lia]]);
clear H; rename H' into H end end.
Local Unset Keyed Unification.

Local Ltac Q0z1.sf_hide_poison ::= sf_hide_poison_divlit. Local Ltac mkr__sf_hide_poison_4 := sf_hide_poison_divlit.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Let atn := at_nodeA L asegs.

Local Notation alloc_W := (QVo2.Mq2.alloc_W RE X).
Local Notation slot_W := (QVo2.Mq2.slot_W RE).
Local Notation tzone_frame := (QVo2.Mq2.tzone_frame RE X).

Definition alloc_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (n lo : Z) (m : word -> option byte) (obj tsz : Z) (q : list word)
(r : option aptr * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' G1,
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ RDepot RE X m' /\ depot_step m m'
/\ rw_cells asegs m' obj [C8 (wz (obj + 16)); C8 (wz tsz)] /\ u64arr asegs m' (obj + 16) q
/\ match r with
| (None, a1) => a0 = wz 0 /\ munch (alloc_W (bv_unsigned sp) (class_of n) (c_alloc_user (cls a (class_of n)))) m m'
/\ qframe a a1 /\ gstep RE X a a1 G G1 /\ RPrim a1 G1 RE X m'
| (Some p, a2) => exists a1 i,
p = APrim (as_next a1) n /\ a2 = set_next (N.succ (as_next a1)) a1 /\ qframe a a1
/\ gstep RE X a a1 G G1 /\ tag_at G1 (class_of n) i = Some TCached /\ 0 <= i
/\ a0 = wz (slot_beg RE (class_of n) i + rz_size n)
/\ munch (alloc_W (bv_unsigned sp) (class_of n) (c_alloc_user (cls a (class_of n))) ++ slot_W (class_of n) i) m m'
/\ (forall t, tag_prim t = false -> RPrim a1 (set_tag (class_of n) i t G1) RE X m')
/\ chunk_mem m' (slot_beg RE (class_of n) i) (slot_beg RE (class_of n) i + class_size (class_of n)) (slot_beg RE (class_of n) i + rz_size n) n
/\ hjunk m' (slot_beg RE (class_of n) i + rz_size n) (slot_beg RE (class_of n) i + class_size (class_of n))
end.

Lemma comb_W_pz : forall a LB FS G (sp c x lo hi : Z),
gcons a LB FS G RE X -> 1 <= c <= 31 -> band_lo <= sp - COMB_STACK ->
In (lo, hi) (comb_W RE X sp c (c_alloc_user (cls a c))) -> lo <= x < hi ->
fp_RPrim G RE X x \/ fp_RStats RE X x \/ band_lo <= x.
Proof.
intros a LB FS G sp c x lo hi GC Hc CSP Hin Hx.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
pose proof (gc_bounds _ _ _ _ _ _ GC c ltac:(rewrite K32; lia)) as (B1 & B2 & B3). rewrite KO in B2.
assert (NSL : forall c' i t, tag_at G c' i = Some t -> reg_beg (ae_L RE) c + c_alloc_user (cls a c) <= x < reg_beg (ae_L RE) c + 3758096384 ->
in_iv (slot_beg RE c' i, class_size c') x -> False).
{ intros c' i t Ht [X1 X2] [S1 S2]. cbn [fst snd] in S1, S2.
pose proof (tag_slot _ _ _ _ _ _ GC c' i t Ht) as (C1 & I1 & N1 & R1 & R2 & Q1 & Q2 & Z1 & Z2 & AL). rewrite KO in Q2.
pose proof (reg_geom RE X RL c' ltac:(lia)) as (RB' & _).
destruct (Z.eq_dec c c') as [<-|NE]; [lia|].
rewrite RB in X1, X2. rewrite RB' in R1, R2. assert (c + 1 <= c' \/ c' + 1 <= c) as [D|D] by lia; nia. }
assert (NSS : forall c' i t, tag_at G c' i = Some t ->
SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) <= x < SH (reg_beg (ae_L RE) c) + 3758096384 / 8 ->
in_sh (slot_beg RE c' i, class_size c') x -> False).
{ intros c' i t Ht [X1 X2] SS.
pose proof (tag_slot _ _ _ _ _ _ GC c' i t Ht) as (C1 & I1 & N1 & R1 & R2 & Q1 & Q2 & Z1 & Z2 & AL). rewrite KO in Q2.
pose proof (reg_geom RE X RL c' ltac:(lia)) as (RB' & _ & _ & _ & _ & _ & _).
apply in_sh_bounds in SS; [| Z.div_mod_to_equations; lia| lia]. destruct SS as [S1 S2].
change (3758096384 / 8) with 469762048 in X2. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048) in X2. change (8 * 469762048) with 3758096384 in X2.
destruct (Z.eq_dec c c') as [<-|NE].
- pose proof (SH_le _ _ R2). pose proof (SH_le (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) ltac:(lia)). lia.
- assert (c + 1 <= c' \/ c' + 1 <= c) as [D|D] by lia.
+ assert (LE : reg_beg (ae_L RE) c + 3758096384 <= slot_beg RE c' i) by (rewrite RB; rewrite RB' in R1; lia).
pose proof (SH_le _ _ LE). lia.
+ assert (LE : slot_beg RE c' i + class_size c' <= reg_beg (ae_L RE) c + c_alloc_user (cls a c)) by (rewrite RB; rewrite RB' in R2; lia).
pose proof (SH_le _ _ LE). lia. }
unfold comb_W, COMB_STACK, ri_addr in Hin. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; injection E as <- <-.
- do 2 right. unfold COMB_STACK in CSP. lia.
- destruct (Z.lt_ge_cases x (rl_T X + 2800)) as [LT|GE].
+ left. right; left. split; cbn [fst snd]; lia.
+ right; left. left. split; cbn [fst snd]; lia.
- left. left. split; cbn [fst snd]; lia.
- left. do 2 right; left. exists c. rewrite K32. split; [lia| lia].
- left. do 3 right; left. exists c. rewrite K32. split; [lia|]. split; cbn [fst snd]; rewrite ?KS; [lia|]. change (536870912 / 8) with 67108864 in *. lia.
- left. do 4 right; left. split.
+ exists c. rewrite K32, KO. split; [lia| lia].
+ intros (c' & i & t & Ht & _ & IN). exact (NSL c' i t Ht ltac:(lia) IN).
- left. do 5 right. split.
+ exists c. rewrite K32, KO. split; [lia|]. split; cbn [fst snd]; [| change (3758096384 / 8) with 469762048; lia].
eapply Z.le_trans; [| apply (proj1 Hx)]. apply SH_le. lia.
+ intros (c' & i & t & Ht & _ & IN). exact (NSS c' i t Ht ltac:(change (3758096384 / 8) with 469762048; lia) IN).
Qed.

Lemma too_big_prim : forall n, 0 <= n -> from_primary n = true -> too_big n = false.
Proof.
intros n Hn HP. unfold too_big. rewrite HP. apply from_primary_iff in HP. unfold kMaxSize in HP. unfold kMaxAllowedMalloc.
replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb]. apply Z.ltb_ge. lia.
Qed.

Lemma allocate_prim_spec : forall ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (LB : list ablock) (FS : list fframe)
(n cf lo obj tsz dn : Z) (q : list word),
gcons a LB FS G RE X ->
RTconst RE X m -> RStats RE X m -> RPrim a G RE X m -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ALLOC_STACK ->
0 <= n -> from_primary n = true -> 0 <= cf <= 1 ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz tsz)] -> u64arr asegs m (obj + 16) q -> Z.of_nat (length q) = 30 ->
1 <= tsz <= 30 -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= obj -> obj + 256 < 2^64 ->
aimplT atn (asan_malloc (ae_L RE) a n) s
(alloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G n lo m obj tsz q)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz n) (wz 8) (wz obj) (wz 1) (wz cf) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz allocate_entry) fc None m (seg_rom asegs)).
Proof.
intros until q; intros GC RT RS RP RD MI ST CEIL LO Hn HP CF OBJ TRQ LQ SZR DNH DCAP OB1 OB2.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof CEIL as CEIL'. idtac. unfold ALLOC_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB. idtac. rewrite ?KHI_eq in TK.
unfold iv_disjoint in TD. cbn [fst snd] in TD.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & ND & _). cbn [fst snd] in NK, NC. unfold iv_disjoint in ND. cbn [fst snd] in ND. idtac. rewrite ?KHI_eq in NK.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & BD & _). cbn [fst snd] in BK, BC. unfold iv_disjoint in BD. cbn [fst snd] in BD. idtac. rewrite ?KHI_eq in BK.
pose proof (class_of_facts n Hn HP) as (Hc & Csz & Csz32 & Crz & _). cbv zeta in Hc, Csz, Csz32, Crz.
set (c := class_of n) in *.
pose proof (needed_facts n Hn) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
pose proof HP as HP'. apply from_primary_iff in HP'. unfold kMaxSize in HP'.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (SHB1 : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite FB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD0.
assert (SHB2 : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD1.
pose proof (gc_bounds _ _ _ _ _ _ GC c ltac:(rewrite K32; lia)) as (AU1 & AU2 & AU3). rewrite KO in AU2.
assert (SHB3 : SH (reg_beg (ae_L RE) c) <= SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048). apply SH_le. lia. }
clear PAL AU3.
pose proof (munch_refl (alloc_W (bv_unsigned sp) c (c_alloc_user (cls a c))) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
apply aimplT_from_evt.

eapply alloc_pre1; [exact RT| exact RL| exact MI| exact ST| exact CEIL'| lia| lia| lia|].
intros m1 u0 u1 u2 u3 v1 v2 v3 v4 v5 v6 v7 u4 u5 u6 u7 fj MU1 WM1 MI1 ST1 FR1.
assert (RT1 : RTconst RE X m1) by (eapply RTconst_munch; [exact RT| exact MU1| exact WM1| apply Forall_cons; [apply rt_avoid_stack; [exact RL| lia]| apply Forall_nil]]).
assert (RS1 : RStats RE X m1) by (eapply RStats_munch; [exact RS| exact MU1| exact WM1| apply Forall_cons; [st_avoid_solve| apply Forall_nil]]).
assert (RP1 : RPrim a G RE X m1) by (eapply RPrim_stack; [exact RP| exact RL| exact MU1| exact WM1| apply Forall_cons; [cbn [fst]; lia| apply Forall_nil]]).
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame; [exact RD| exact WM1|]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z Fz _. cbn [outside]. split; [| exact I].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). lia. }
phase_done MU m m1 MU1 WM1. clear MI RT RS RP RD.
eapply alloc_rzlog; [lia|]. intros a0'.
eapply alloc_pre3; [exact RT1| exact RL| exact MI1| exact ST1| exact CEIL'| lia| exact Hn| exact HP|].
intros m2 w0 w1 w2 w3 x0 x1 x2 x3 x4 x5 x6 x7 w4 w5 w6 w7 MU2 WM2 MI2 ST2.
assert (RT2 : RTconst RE X m2) by (eapply RTconst_munch; [exact RT1| exact MU2| exact WM2| apply Forall_cons; [apply rt_avoid_stack; [exact RL| lia]| apply Forall_nil]]).
assert (RS2 : RStats RE X m2) by (eapply RStats_munch; [exact RS1| exact MU2| exact WM2| apply Forall_cons; [st_avoid_solve| apply Forall_nil]]).
assert (RP2 : RPrim a G RE X m2) by (eapply RPrim_stack; [exact RP1| exact RL| exact MU2| exact WM2| apply Forall_cons; [cbn [fst]; lia| apply Forall_nil]]).
assert (RD2 : RDepot RE X m2).
{ eapply RDepot_frame; [exact RD1| exact WM2|]. eapply agree_on_of_munch; [exact MU2| exact WM2|]. intros z Fz _. cbn [outside]. split; [| exact I].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). lia. }
phase_done MU m1 m2 MU2 WM2. clear MI1 RT1 RS1 RP1 RD1. try clear ST1.

pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp - 128)] m2) as MUs. pose proof (wmono_refl asegs m2) as WMs.
step. call_sp_ch (get_current_thread_spec RE X) ltac:(fun _ => idtac); [exact RT2| exact RL| assumption| exact ST2| exact CEIL'| lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST3 end.
match goal with H : RTconst RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RT3; rename H2 into MI3 end.
lazymatch type of MUs with munch _ _ ?mm =>
assert (RS3 : RStats RE X mm) by (eapply RStats_munch; [exact RS2| exact MUs| exact WMs| apply Forall_cons; [st_avoid_solve| apply Forall_nil]]);
assert (RP3 : RPrim a G RE X mm) by (eapply RPrim_stack; [exact RP2| exact RL| exact MUs| exact WMs| apply Forall_cons; [cbn [fst]; lia| apply Forall_nil]]);
assert (RD3 : RDepot RE X mm) by
(eapply RDepot_frame; [exact RD2| exact WMs|]; eapply agree_on_of_munch; [exact MUs| exact WMs|]; intros z Fz _; cbn [outside]; split; [| exact I];
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)); lia)
end.
clear MUs WMs RT2 RS2 RP2 RD2. try clear ST2. try clear MI2.
step.
step. unfold_cond; cond_unsig; if_false.
step. stp. step. step.
step.
apply evt_done.
unfold asan_malloc. rewrite (too_big_prim n Hn HP), HP. fold c.
name_sp sp (-128). rewrite <- Hsp in ST3.
lazymatch goal with |- aimplT _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
eapply aimplT_bind;
[eapply aimplT_tall; [apply cache_alloc_qframe|
eapply (combined_prim_spec L RE X _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm s a G (needed n) lo);
[exact RT3| exact RL| exact RS3| exact RP3| exact MI3| exact ST3| exact CEIL'| rewrite Hsp; unfold COMB_STACK; lia| lia]] |] end.
intros [ok a1] s' ms' [QF PO]. cbn [snd] in QF. unfold comb_post in PO. rewrite Hsp in PO. unname_sp.
change (class_id (needed n)) with c in PO. cbn [fst snd] in PO.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & G1 & -> & -> & MU3 & WM3 & MI4 & ST4 & RT4 & RS4 & GS & REST).
replace (ret_pc (wz 259380)) with (wz 259380) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

lazymatch type of MU3 with munch _ ?mp _ =>
assert (RD4 : RDepot RE X m3) by
(eapply RDepot_frame; [exact RD3| exact WM3|]; eapply agree_on_of_munch; [exact MU3| exact WM3|]; intros z Fz _; apply outside_intro;
intros lo' hi' Hin Hz; destruct (comb_W_pz a LB FS G (bv_unsigned sp + -128) c z lo' hi' GC ltac:(lia) ltac:(idtac; unfold COMB_STACK; lia) Hin Hz) as [P|[P|P]];
[ exact (fpP_RDepot _ _ _ _ _ _ GC z P Fz) | exact (fpS_excl _ _ _ _ _ _ GC z P ltac:(do 2 right; left; exact Fz))
| pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)); lia ]) end.
unfold comb_W, COMB_STACK, ri_addr in MU3. rewrite ?KS, ?KO in MU3.
change (536870912 / 8) with 67108864 in MU3. change (3758096384 / 8) with 469762048 in MU3.
lazymatch type of MU3 with munch _ ?mp _ => phase_done MU mp m3 MU3 WM3 end.
clear RD3 RT3 RS3 RP3. try clear MI3. try clear ST3.
pose proof (GS) as (_ & _ & _ & GCT). pose proof (GCT LB FS GC) as GC1.
unfold alloc_frame in FR1.
destruct ok.
2:{
destruct REST as [-> RP4]. cbn [negb]. apply aimplT_ret.
step.
step. if_lit.
pose proof (munch_refl [(0x174420, 0x174421); (bv_unsigned sp - 144, bv_unsigned sp - 128)] m3) as MUs. pose proof (wmono_refl asegs m3) as WMs.
step. call_sp_ch (set_oom_spec RE X) ltac:(fun _ => idtac); [exact RS4| assumption| exact ST4| exact CEIL'|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST5 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS5; rename H2 into MI5 end.
lazymatch type of MUs with munch _ _ ?mm =>
destruct (sz_frame RE X a1 LB FS G1 m3 mm _ GC1 MUs WMs) as (FT & FP & FD);
[ intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-; [left; do 2 right; lia| right; idtac; lia] |] end.
pose proof (FT RT4) as RT5. pose proof (FP RP4) as RP5. pose proof (FD RD4) as RD5. clear FT FP FD MUs WMs RT4 RP4 RD4 RS4.
step. call0 (may_return_null_spec RE X); [exact RT5| assumption|]. subst_words.
step. if_lit.
stp. step.
step. do 13 step. step.
release_frame FR1 ST5 (bv_unsigned sp).
step.
apply evt_done. unfold alloc_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST5|].
split; [exact RT5|]. split; [exact RS5|]. split; [exact RD5|].
split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn; split; [split; [unfold DP_N; exact DNC| exact DNP]| lia]]|].
split; [exact OBJ|]. split; [exact TRQ|].
cbn [fst snd]. split; [reflexivity|]. split; [| split; [exact QF| split; [exact GS| exact RP5]]].
unfold alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }

destruct REST as (i & TI & -> & RPF & HJ & SHD). cbn [negb]. apply aimplT_ret.
pose proof (RPF TQOwn eq_refl) as RPq.
destruct (RPrim_open _ _ _ _ _ RPq) as (K & _ & GNE & HCall).
pose proof (rprim_slot_geom a1 (set_tag c i TQOwn G1) RE X K m3 c i TQOwn GNE HCall (tag_at_set_tag_eq _ _ _ _ _ TI))
as (_ & I0 & S32 & _ & RBq & SL1 & SL2 & AU1' & AU2' & SBE & _).
clear K GNE HCall. rewrite KO in AU2'.
pose proof (slot_beg_align RE X c i RL ltac:(lia)) as [AL16 _].
set (AB := slot_beg RE c i) in *.
assert (PAB : prim_lo RE <= AB) by lia.
assert (ABP : AB + class_size c <= prim_lo RE + 2^37) by lia.
assert (SHAB : 2201439137792 <= SH AB /\ SH AB + class_size c / 8 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; clear - PAB ABP PK PH PCH Csz; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD2.
assert (SHA : SH (AB + rz_size n) = SH AB + rz_size n / 8) by (rewrite <- SH_plus8; f_equal; clear - RZ2; Z.div_mod_to_equations; lia).
assert (FIT : rz_size n + round_up (used_size n) 8 <= class_size c).
{ assert (RU : round_up (used_size n) 8 <= round_up (Z.max n 8) 8) by (unfold round_up, used_size; clear; Z.div_mod_to_equations; lia).
unfold needed in Csz. lia. }
pose proof (ngran_eq (used_size n) ltac:(unfold used_size; lia)) as (NG1 & NG2 & NG3).
pose proof (round_up_8 (used_size n) ltac:(unfold used_size; lia)) as [RU8 _].
assert (US : 1 <= used_size n <= Z.max n 8) by (unfold used_size; lia).

apply (munch_weaken _ ((AB, AB + class_size c) :: (SH AB, SH AB + class_size c / 8) :: alloc_W (bv_unsigned sp) c (c_alloc_user (cls a c)))) in MU.
2:{ unfold alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048.
intros z Hz. cbn [outside] in Hz |- *. clear - Hz. tauto. }
unfold alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END in MU. rewrite ?KS, ?KO in MU. change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.

destruct (slot_pieces m3 AB (class_size c) (rz_size n) (used_size n) HJ SHD ltac:(lia) RZ2 AL16 ltac:(lia)
FIT ltac:(clear - Csz32; Z.div_mod_to_equations; lia))
as (b0 & b1 & h & w & d & g1 & g2 & HDR & HJU & HJm & MG & P1 & R1 & P2 & P3 & R4).

assert (Hsz8 : 8 * (class_size c / 8) = class_size c) by (clear - Csz32; Z.div_mod_to_equations; lia).
assert (Hrz8 : 8 * (rz_size n / 8) = rz_size n) by (clear - RZ2; Z.div_mod_to_equations; lia).
assert (Hrz16 : exists r16, rz_size n = 16 * r16) by (exists (rz_size n / 16); clear - RZ2; Z.div_mod_to_equations; lia). destruct Hrz16 as [r16 Hrz16].
assert (Hn8 : used_size n = 8 * (used_size n / 8) + used_size n mod 8 /\ 0 <= used_size n mod 8 < 8) by (clear - US; Z.div_mod_to_equations; lia).
assert (Hng : (used_size n mod 8 = 0 -> ngran (used_size n) = used_size n / 8) /\ (used_size n mod 8 <> 0 -> ngran (used_size n) = used_size n / 8 + 1))
by (rewrite NG1; unfold round_up; clear - US; Z.div_mod_to_equations; lia).
assert (Hk4 : 8 * ((class_size c - rz_size n - round_up (used_size n) 8) / 8) = class_size c - rz_size n - 8 * ngran (used_size n))
by (rewrite NG3; clear - Hsz8 Hrz8; Z.div_mod_to_equations; lia).
clear NG1. hide TA. hide Csz32. hide RZ2. hide AL16.
destruct NF as (NF1 & NF2 & NF8 & NF3). hide NF8.

set (Gq := set_tag c i TQOwn G1) in RPq.
assert (TIq : tag_at Gq c i = Some TQOwn) by (apply (tag_at_set_tag_eq _ _ _ _ _ TI)).
assert (GCq : gcons a1 LB FS Gq RE X) by (apply (gcons_retag_nonlive _ _ _ _ _ _ _ _ _ _ GC1 TI eq_refl); [intros q0; reflexivity| reflexivity]).
assert (QZs : forall z, AB <= z < AB + class_size c -> fp_RQuar a1 LB Gq RE X z).
{ intros z Hz. do 5 right; left. exists c, i, TQOwn. split; [exact TIq|]. split; [reflexivity|]. split; cbn [fst snd]; lia. }
assert (QZh : forall z, SH AB <= z < SH AB + class_size c / 8 -> fp_RQuar a1 LB Gq RE X z).
{ intros z Hz. do 6 right; left. exists c, i, TQOwn. split; [exact TIq|]. split; [reflexivity|]. split; cbn [fst snd]; fold AB; lia. }
assert (NSs : forall z, AB <= z < AB + class_size c -> ~ fp_RStats RE X z) by (intros z Hz Fz; exact (fpQ_RStats _ _ _ _ _ _ GCq z (QZs z Hz) Fz)).
assert (NSh : forall z, SH AB <= z < SH AB + class_size c / 8 -> ~ fp_RStats RE X z) by (intros z Hz Fz; exact (fpQ_RStats _ _ _ _ _ _ GCq z (QZh z Hz) Fz)).
assert (NSt : forall z, band_lo <= z -> ~ fp_RStats RE X z) by (intros z Hz Fz; pose proof (fp_lt_ceil _ _ _ _ _ _ GCq z ltac:(right; left; exact Fz)); lia).
assert (NSd : forall z, fp_RDepot RE X z -> ~ fp_RStats RE X z) by (intros z Hz Fz; exact (fpS_excl _ _ _ _ _ _ GCq z Fz ltac:(do 2 right; left; exact Hz))).
assert (NDs : forall z, AB <= z < AB + class_size c -> ~ fp_RDepot RE X z) by (intros z Hz Fz; exact (fpQ_RDepot _ _ _ _ _ _ GCq z (QZs z Hz) Fz)).
assert (NDh : forall z, SH AB <= z < SH AB + class_size c / 8 -> ~ fp_RDepot RE X z) by (intros z Hz Fz; exact (fpQ_RDepot _ _ _ _ _ _ GCq z (QZh z Hz) Fz)).
assert (NDt : forall z, band_lo <= z -> ~ fp_RDepot RE X z) by (intros z Hz Fz; pose proof (fp_lt_ceil _ _ _ _ _ _ GCq z ltac:(do 5 right; left; exact Fz)); lia).
assert (NDst : forall z, fp_RStats RE X z -> ~ fp_RDepot RE X z) by (intros z Hz Fz; exact (fpS_excl _ _ _ _ _ _ GCq z Hz ltac:(do 2 right; left; exact Fz))).
idtac.
step.
step. unfold_cond; cond_unsig; if_false.

eapply (alloc_hdr RE X n i gp RL Hn HP PAB ABP AL16); [exact RT4| exact MI4| exact ST4| exact CEIL'| lia| exact FR1| exact HDR|].
intros m4 h0 h1 h2 h3 h5 h6 h7 MU4 WM4 MI5 ST5 FR5 HDR5 RT5.
refold RE n c i AB MU4. refold RE n c i AB HDR5.
try replace (class_of n) with c by reflexivity. try replace (slot_beg RE c i) with AB by reflexivity.
destruct (tzone_frame a1 LB FS Gq c i m3 m4 _ GCq TIq MU4 WM4) as (FP & FS' & FD).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; left. split; cbn [fst snd]; lia. }
pose proof (FP RPq) as RP5.
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; apply NSs; lia) RS4) as RS5.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; apply NDs; lia) RD4) as RD5.
clear FP FS' FD.
ctr MG MU4 WM4. ctr P2 MU4 WM4. ctr P3 MU4 WM4.
pose proof (hjunk_wmono _ _ _ _ HJU WM4) as HJU5. pose proof (hjunk_wmono _ _ _ _ HJm WM4) as HJm5.
clear HDR FR1 SHD RPF HJ HJU HJm RT4 RS4 RD4 RPq. try clear MI4. try clear ST4.
phase_done MU m3 m4 MU4 WM4.

eapply (alloc_depot RE X n i gp RL Hn HP PAB ABP AL16);
[exact RT5| exact RD5| exact MI5| exact ST5| exact CEIL'| lia| exact OBJ| exact TRQ| exact LQ| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| lia| lia| exact HDR5|].
intros m5 d0 d1 d2 d5 d6 d7 d10 d11 d12 d13 d14 d15 d16 d17 id MU5 WM5 MI6 ST6 RT6 RD6 OBJ6 TRQ6 ID (dn6 & [DNC6 DNP6] & DNR6) HDR6. unfold DP_N in DNC6.
unfold depot_W, SS_BASE, DP_END in MU5. refold RE n c i AB MU5. refold RE n c i AB HDR6.
try replace (class_of n) with c by reflexivity. try replace (slot_beg RE c i) with AB by reflexivity.
clear OBJ TRQ.
destruct (tzone_frame a1 LB FS Gq c i m4 m5 _ GCq TIq MU5 WM5) as (FP & FS' & FD).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-.
- right; left. split; cbn [fst snd]; lia.
- left. idtac. lia.
- do 4 right. left. split; cbn [fst snd]; lia.
- do 4 right. right; left. split; cbn [fst snd]; lia.
- do 4 right. do 2 right; left. split; cbn [fst snd]; lia. }
pose proof (FP RP5) as RP6.
assert (NS5 : forall lo hi z, In (lo, hi) [(AB + rz_size n + -8, AB + rz_size n); (bv_unsigned sp - 352, bv_unsigned sp - 128); (1851528, 6373552); (rl_dn X, rl_dn X + 1048576); (rl_ssb X, rl_ssb X + 8388608)] -> lo <= z < hi -> ~ fp_RStats RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-.
- apply NSs. lia.
- apply NSt. lia.
- apply NSd. left. split; cbn [fst snd]; lia.
- apply NSd. right; left. split; cbn [fst snd]; lia.
- apply NSd. do 2 right; left. split; cbn [fst snd]; lia. }
pose proof (FS' NS5 RS5) as RS6. clear FP FS' FD NS5.
ctr MG MU5 WM5. ctr P2 MU5 WM5. ctr P3 MU5 WM5.
pose proof (hjunk_wmono _ _ _ _ HJU5 WM5) as HJU6. pose proof (hjunk_wmono _ _ _ _ HJm5 WM5) as HJm6.
clear HDR5 RT5 RS5 RD5 RP5 HJU5 HJm5. try clear MI5. try clear ST5.

assert (AGZ : agree_on asegs (fun z => SH AB <= z < SH AB + class_size c / 8) m4 m5).
{ eapply agree_on_of_munch; [exact MU5| exact WM5|]. intros z Hz _. cbn [outside].
repeat split; try exact I; intros [Y1 Y2]; clear - Hz Y1 Y2 SHAB SHBD0 PK PAB CEIL LO SPR NK BK RZ1; unfold prim_lo in *; lia. }
apply (rw_cells_agree asegs _ _ _ _ _ AGZ) in R4;
[| intros z Hz; cbn [cells_size csize Nat.add] in Hz; clear - Hz SHA Hk4 Hsz8 Hrz8 NG2 NG3 FIT RZ1; lia].
clear AGZ.
phase_done MU m4 m5 MU5 WM5.

eapply (alloc_shadow RE X n i gp RL Hn HP PAB ABP AL16);
[exact RT6| exact MI6| exact ST6| exact CEIL'| lia| exact P1| exact P2| exact P3|].
intros m6 e e0 e1 e2 e3 e4 e5 e6 e7 e10 e11 e12 e14 e15 e16 e17 e22 MU6 WM6 MI7 ST7 RT7 P1' P2' P3'.
refold RE n c i AB MU6. refold RE n c i AB P1'. refold RE n c i AB P2'. refold RE n c i AB P3'.
try replace (class_of n) with c by reflexivity. try replace (slot_beg RE c i) with AB by reflexivity.
clear P1 P2 P3.
assert (SHin : forall z, SH (AB + rz_size n) <= z < SH (AB + rz_size n) + ngran (used_size n) -> SH AB <= z < SH AB + class_size c / 8) by (intros z Hz; lia).
destruct (tzone_frame a1 LB FS Gq c i m5 m6 _ GCq TIq MU6 WM6) as (FP & FS' & FD).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
- left. idtac. lia.
- do 2 right; left. split; cbn [fst snd]; fold AB; pose proof (SHin z Hz); lia. }
pose proof (FP RP6) as RP7.
assert (NZ6 : forall lo hi z, In (lo, hi) [(bv_unsigned sp - 192, bv_unsigned sp - 128); (SH (AB + rz_size n), SH (AB + rz_size n) + ngran (used_size n))] -> lo <= z < hi ->
~ fp_RStats RE X z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
- split; [apply NSt| apply NDt]; lia.
- split; [apply NSh| apply NDh]; apply SHin; exact Hz. }
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; exact (proj1 (NZ6 lo' hi' z Hin Hz))) RS6) as RS7.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (NZ6 lo' hi' z Hin Hz))) RD6) as RD7.
clear FP FS' FD NZ6.
ctr MG MU6 WM6.
pose proof (hjunk_wmono _ _ _ _ HJU6 WM6) as HJU7. pose proof (hjunk_wmono _ _ _ _ HJm6 WM6) as HJm7.
clear RT6 RS6 RD6 RP6 HJU6 HJm6. try clear MI6. try clear ST6.
phase_done MU m5 m6 MU6 WM6.

eapply (alloc_stats RE X n i gp RL Hn HP PAB ABP AL16); [exact RT7| exact RS7| exact MI7| exact ST7| exact CEIL'| lia|].
intros m7 f0 f1 f2 f3 f4 f5 f6 f7 f10 f11 f12 f14 f15 f16 f17 MU7 WM7 MI8 ST8 RT8 RS8.
refold RE n c i AB MU7.
try replace (class_of n) with c by reflexivity. try replace (slot_beg RE c i) with AB by reflexivity.
destruct (tzone_frame a1 LB FS Gq c i m6 m7 _ GCq TIq MU7 WM7) as (FP & FS' & FD).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- left. idtac. lia.
- do 3 right; left. left. split; cbn [fst snd]; lia.
- do 3 right; left. left. split; cbn [fst snd]; lia. }
pose proof (FP RP7) as RP8.
assert (ND7 : forall lo hi z, In (lo, hi) [(bv_unsigned sp - 160, bv_unsigned sp - 128); (rl_T X + 2800, rl_T X + 2824); (rl_T X + 2912 + 8 * c, rl_T X + 2912 + 8 * c + 8)] -> lo <= z < hi -> ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- apply NDt. lia.
- apply NDst. left. split; cbn [fst snd]; lia.
- apply NDst. left. split; cbn [fst snd]; lia. }
pose proof (FD ND7 RD7) as RD8. clear FP FS' FD ND7.
ctr MG MU7 WM7. ctr P2' MU7 WM7. ctr P3' MU7 WM7.
pose proof (hjunk_wmono _ _ _ _ HJU7 WM7) as HJU8. pose proof (hjunk_wmono _ _ _ _ HJm7 WM7) as HJm8.
clear RT7 RS7 RD7 RP7 HJU7 HJm7. try clear MI7. try clear ST7.

assert (AGZ2 : agree_on asegs (fun z => (AB <= z < AB + class_size c) \/ (SH AB <= z < SH AB + class_size c / 8)) m6 m7).
{ eapply agree_on_of_munch; [exact MU7| exact WM7|]. intros z Hz _. cbn [outside].
repeat split; try exact I; intros [Y1 Y2];
clear - Hz Y1 Y2 SHAB SHBD0 PK PAB ABP PH PCH CEIL LO SPR TK TB TD RZ1 Hc; unfold prim_lo, prim_hi in *; lia. }
apply (rw_cells_agree asegs _ _ _ _ _ AGZ2) in R4;
[| intros z Hz; right; cbn [cells_size csize Nat.add] in Hz; clear - Hz SHA Hk4 Hsz8 Hrz8 NG2 NG3 FIT RZ1; lia].
apply (rw_cells_agree asegs _ _ _ _ _ AGZ2) in HDR6;
[| intros z Hz; left; cbn [cells_size csize Nat.add] in Hz; clear - Hz FIT RZ1 NG2 NG3; lia].
clear AGZ2.
lazymatch type of MU with munch ?W ?m0 _ => lazymatch type of MU7 with munch ?Wk _ _ =>
assert (SF : sub_fp Wk W) by sub_fp_solve;
pose proof (munch_chain W Wk m0 m6 m7 MU MU7 SF) as MU'; clear MU SF; rename MU' into MU end end.
transport_after_call asegs m6 m7 MU7 WM7. clear MU7 WM7.

eapply (alloc_fill RE X n i gp RL Hn HP PAB ABP AL16); [exact RT8| exact MI8| exact ST8| exact CEIL'| lia| exact FR5| exact CF| exact HJU8|].
intros m8 g g0 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g14 g15 g16 g17 MU8 WM8 MI9 ST9 RT9 FR9 HJU9.
refold RE n c i AB MU8. refold RE n c i AB HJU9.
try replace (class_of n) with c by reflexivity. try replace (slot_beg RE c i) with AB by reflexivity.
clear FR5.
destruct (tzone_frame a1 LB FS Gq c i m7 m8 _ GCq TIq MU8 WM8) as (FP & FS' & FD).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; left. split; cbn [fst snd]; lia. }
pose proof (FP RP8) as RP9.
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; apply NSs; lia) RS8) as RS9.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; apply NDs; lia) RD8) as RD9.
clear FP FS' FD.
ctr MG MU8 WM8. ctr P2' MU8 WM8. ctr P3' MU8 WM8.
pose proof (hjunk_wmono _ _ _ _ HJm8 WM8) as HJm9.
clear RT8 RS8 RD8 RP8 HJU8 HJm8. try clear MI8. try clear ST8.
phase_done MU m7 m8 MU8 WM8.

eapply (alloc_fin RE X n i gp RL Hn HP PAB ABP AL16); [exact RT9| exact MI9| exact ST9| exact CEIL'| lia| exact FR9| exact HDR6| exact MG|].
intros m9 k0 k1 k2 k4 k5 k6 k7 k10 k11 k12 k14 k15 k16 k17 MU9 WM9 MI10 ST10 RT10 HDR10 MG10.
refold RE n c i AB MU9. refold RE n c i AB HDR10. refold RE n c i AB MG10.
clear FR9 HDR6 MG.
destruct (tzone_frame a1 LB FS Gq c i m8 m9 _ GCq TIq MU9 WM9) as (FP & FS' & FD).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- left. idtac. lia.
- right; left. split; cbn [fst snd]; lia.
- right; left. split; cbn [fst snd]; lia. }
pose proof (FP RP9) as RP10.
assert (NZ9 : forall lo hi z, In (lo, hi) [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (AB + rz_size n + -16, AB + rz_size n)] -> lo <= z < hi ->
~ fp_RStats RE X z /\ ~ fp_RDepot RE X z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- split; [apply NSt| apply NDt]; lia.
- split; [apply NSs| apply NDs]; lia.
- split; [apply NSs| apply NDs]; lia. }
pose proof (FS' ltac:(intros lo' hi' z Hin Hz; exact (proj1 (NZ9 lo' hi' z Hin Hz))) RS9) as RS10.
pose proof (FD ltac:(intros lo' hi' z Hin Hz; exact (proj2 (NZ9 lo' hi' z Hin Hz))) RD9) as RD10.
clear FP FS' FD NZ9.
ctr P2' MU9 WM9. ctr P3' MU9 WM9.
pose proof (hjunk_wmono _ _ _ _ HJU9 WM9) as HJU10. pose proof (hjunk_wmono _ _ _ _ HJm9 WM9) as HJm10.
clear RT9 RS9 RD9 RP9 HJU9 HJm9. try clear MI9. try clear ST9.
phase_done MU m8 m9 MU9 WM9.

try replace (class_of n) with c by reflexivity. try replace (slot_beg RE c i) with AB by reflexivity.
apply evt_done. unfold alloc_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [exact MI10|]. split; [exact ST10|].
split; [exact RT10|]. split; [exact RS10|]. split; [exact RD10|].
split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn6; split; [split; [unfold DP_N; exact DNC6| exact DNP6]| exact DNR6]]|].
split; [exact OBJ6|]. split; [exact TRQ6|].
cbn [fst snd]. exists a1, i.
split; [reflexivity|]. split; [reflexivity|]. split; [exact QF|]. split; [exact GS|]. split; [exact TI|]. split; [exact I0|]. split; [reflexivity|].
split.
{ unfold alloc_W, slot_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048.
fold c. fold AB. eapply munch_weaken; [| exact MU]. sub_fp_solve. }
split.
{ intros t Ht. pose proof (RPrim_retag _ _ _ _ _ _ _ _ t RP10 TIq eq_refl Ht) as RPt.
destruct (retag_twice G1 c i TCached TQOwn t tag_prim TI I0) as [SL SG].
eapply RPrim_ext; [exact RPt| intros; reflexivity| reflexivity| exact SL| exact SG]. }
split; [| exact HJU10].
unhide RZ2. unhide AL16. unhide Csz32.
pose proof (hb1_facts b1) as [_ HBF].
eapply (@slot_chunk BAND m9 AB (class_size c) n (hb1f b1) (wz id) Hn ltac:(lia) RZ2 AL16 FIT
ltac:(clear - Csz32; Z.div_mod_to_equations; lia) ltac:(rewrite ?KHI_eq; lia) ltac:(idtac; lia) HBF
MG10 HJm10 HDR10 HJU10 P1' R1 P2' P3' R4).
Qed.
End S.
