(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Q6sh QQwg QKTr QJBH QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk QpY2 QTVW QqLk QnRU Q9Ho QmP7 QYyZ QUnM QpME Qu3b QmvA QkZz QteI QQ8H Qx6U QcfN QlES Q0z1 QcA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QpY2.Mq3 QqLk QnRU.Mqa Q9Ho.Mq2 QmP7.Mq0 QYyZ.Mq0 Q9Ho.Mq1.
Import QpY2.Mq2.
Import QUnM QpME.Mq0.
Import QYyZ.Mq5.
Import Qu3b.Mq2 QnRU.Mq8 QmvA.Mq3 QkZz.Mq1 QteI.Mq9 QQ8H.Mq3 Qx6U.Mq4.
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
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_4 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).

Import QcA6.Mq1.

Definition deallocate_entry : Z := 0x3ed54.

Section S.
Context {BAND : Band}.
Variables (C : arun_components) (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).
Hypothesis recycle_spec : recycle_stmt C RE X L.
Hypothesis HRD : ac_RDepot C = RDepot.

Hypothesis HRSx : forall a a' LB LB' RE X m, ac_RSec C a LB RE X m ->
as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
(forall e, In e (as_reg a) -> sec_live LB' e -> sec_live LB e) -> ac_RSec C a' LB' RE X m.

Lemma dealloc_entry_spec : forall ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (p : aptr) (A n lo : Z)
(obj sz bp dn : Z) (q0 q1 q2 q3 q4 : word) (rest : list byte),
QRUN C 0 QB QB [] a LB0 FS0 G RE X m -> In (p, A, n) LB0 -> qroom a p -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - DEALLOC_STACK ->
rw_cells asegs m obj (unw_obj obj sz [q0; q1; q2; q3; q4] rest bp) ->
1 <= sz <= 30 -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= obj -> obj + 2080 < 2^64 ->
aimplT atn (asan_free (ae_L RE) a p) s
(qret_post C RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB0) FS0 lo m free_step)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz A) (wz 0) (wz 0) (wz obj) (wz 1) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz deallocate_entry) fc None m (seg_rom asegs)).
Proof.
intros until rest; intros QR INB QRM MI ST CEIL LO OBJ SZB DNH DCAP OLO OHI.
pose proof CEIL as CEIL'. idtac. unfold DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
change (2^64) with 18446744073709551616 in OHI.
pose proof kq_consts as (K24 & KBB & KBC & KMX & KMN & KMC). pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC, TD. rewrite ?KHI_eq in PK. idtac.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
pose proof (gc_block_small _ _ _ _ _ _ GC _ _ _ INB) as HN2.

pose proof (RChunks_open _ _ _ _ _ _ _ _ _ RC INB) as CR.
assert (PC0 : exists lo_ hi_, chunk_mem m lo_ hi_ A n /\ n = aptr_req p /\ 0 <= n
/\ (lo_, hi_) = chunk_cont p A n
/\ (forall x, lo_ <= x < hi_ -> in_live_user LB0 x \/ fp_RChunks a LB0 G RE X x)
/\ (forall x, in_sh (lo_, hi_ - lo_) x -> fp_RChunks a LB0 G RE X x)
/\ (forall x, lo_ <= x < hi_ -> ~ (rl_T X <= x < rl_T X + 4096) /\ ~ (rl_dn X <= x < rl_dn X + 1048576) /\ ~ (rl_ssb X <= x < rl_ssb X + 8388608))).
{ pose proof (rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & _ & _ & NPd & _). unfold iv_disjoint, prim_lo in NPd; cbn [fst snd] in NPd.
pose proof (rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & _ & _ & BPd & _). unfold iv_disjoint, prim_lo in BPd; cbn [fst snd] in BPd.
destruct (gc_blocks a LB0 FS0 G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn & HP & Ht0 & Hi0 & HA0)|(mb0 & E0 & Hn & HP & He0 & HA0)].
- subst p. cbn [chunk_rep] in CR. destruct CR as (_ & i & Ht & HA & CM).
pose proof (gc_unique a LB0 FS0 G RE X GC _ _ _ _ (APrim id0 n) _ _ Ht0 Ht ltac:(unfold holds; apply aptr_eqb_refl') ltac:(unfold holds; apply aptr_eqb_refl')) as [_ <-].
eexists _, _. split; [exact CM|]. split; [reflexivity|]. split; [exact Hn|]. split; [cbn [chunk_cont]; rewrite HA; f_equal; lia|].
pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht) as (P1 & P2 & _). unfold prim_hi, prim_lo in P1, P2.
split; [| split].
+ intros x Hx. destruct (decide (A <= x < A + n)) as [IN|OUT].
* left. exists (APrim id0 n, A, n). split; [exact INB| cbn [ablk_addr ablk_size fst snd]; lia].
* right. left. split; [left; exists (class_of n), i0, (TLive (APrim id0 n)); split; [exact Ht|]; split; [reflexivity| split; cbn [fst snd]; lia]|].
intros (b & Hb & Hbx). destruct b as [[pb Ab] nb]. cbn [ablk_addr ablk_size fst snd] in Hbx.
destruct (decide ((pb, Ab, nb) = (APrim id0 n, A, n))) as [E|NE]; [injection E; intros; subst; lia|].
refine (proj2 RC _ _ _ _ _ _ x Hb INB NE _ _).
-- pose proof (live_block_geom a LB0 FS0 G RE X GC pb Ab nb Hb) as (_ & _ & [(c' & i' & Ht' & Hc' & Epb & HA' & CT)|(e' & He' & Epb & Hr & HA' & CT)]); unfold blk_container in CT.
++ rewrite Epb in Hc' |- *. cbn [chunk_cont fst snd]. replace (class_of nb) with c' by (symmetry; exact Hc'). split; cbn [fst snd]; lia.
++ rewrite Epb. cbn [chunk_cont fst snd]. pose proof (sec_facts _ _ _ _ _ _ GC _ He') as (_ & _ & _ & E4' & _). cbn [se_size se_req] in E4'.
rewrite <- Hr, <- E4'. split; cbn [fst snd]; lia.
-- cbn [chunk_cont fst snd]. split; cbn [fst snd]; lia.
+ intros x Hx. right; left. exists (class_of n), i0, (TLive (APrim id0 n)). split; [exact Ht|]. split; [reflexivity|].
replace (slot_beg RE (class_of n) i0 + class_size (class_of n) - slot_beg RE (class_of n) i0) with (class_size (class_of n)) in Hx by lia. exact Hx.
+ intros x Hx. lia.
- subst p. cbn [chunk_rep] in CR. destruct CR as (_ & He & HA & CM).
eexists _, _. split; [exact CM|]. split; [reflexivity|]. split; [exact Hn|]. split; [reflexivity|].
pose proof (sec_facts _ _ _ _ _ _ GC _ He) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & D2 & D3). cbn [se_beg se_size se_req] in *.
assert (LIVE : sec_live LB0 (mkSec mb0 (sec_map_size n) n)) by (exists A; exact INB).
split; [| split].
+ intros x Hx. destruct (decide (A <= x < A + n)) as [IN|OUT].
* left. exists (ASec mb0 n, A, n). split; [exact INB| cbn [ablk_addr ablk_size fst snd]; lia].
* right. left. split; [right; exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size]; auto|].
intros (b & Hb & Hbx). destruct b as [[pb Ab] nb]. cbn [ablk_addr ablk_size fst snd] in Hbx.
destruct (decide ((pb, Ab, nb) = (ASec mb0 n, A, n))) as [E|NE]; [injection E; intros; subst; lia|].
refine (proj2 RC _ _ _ _ _ _ x Hb INB NE _ _).
-- pose proof (live_block_geom a LB0 FS0 G RE X GC pb Ab nb Hb) as (_ & _ & [(c' & i' & Ht' & Hc' & Epb & HA' & CT)|(e' & He' & Epb & Hr & HA' & CT)]); unfold blk_container in CT.
++ rewrite Epb in Hc' |- *. cbn [chunk_cont fst snd]. replace (class_of nb) with c' by (symmetry; exact Hc'). split; cbn [fst snd]; (first [ clear - CT HA' i' c' Hbx nb Ab x E1 HA0 KU mb0 ks A RE BAND; lia | lia ]).
++ rewrite Epb. cbn [chunk_cont fst snd]. pose proof (sec_facts _ _ _ _ _ _ GC _ He') as (_ & _ & _ & E4' & _). cbn [se_size se_req] in E4'.
rewrite <- Hr, <- E4'. split; cbn [fst snd]; lia.
-- cbn [chunk_cont fst snd]. split; cbn [fst snd]; lia.
+ intros x Hx. right; right. exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size]. split; [exact He|]. split; [exact LIVE|].
replace (mb0 + sec_map_size n - (mb0 + kPage)) with (sec_map_size n - kPage) in Hx by lia. exact Hx.
+ intros x Hx. pose proof (proj1 (List.Forall_forall _ _) D3 _ (T_obj RE X)) as D. unfold iv_disjoint in D; cbn [fst snd] in D.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (dn_obj RE X)) as Dn. unfold iv_disjoint in Dn; cbn [fst snd] in Dn.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (ssb_obj RE X)) as Db. unfold iv_disjoint in Db; cbn [fst snd] in Db. (first [ clear - Db Dn D Hx x E1 BPd NPd PK TD TK KP mb0 ks n X RE BAND; lia | lia ]). }
destruct PC0 as (plo & phi & CM & En & Hn0 & ECONT & PZ & PZS & PT3).
assert (PTT : phi <= rl_T X \/ rl_T X + 4096 <= plo).
{ pose proof CM as CM0. destruct CM0 as (_ & _ & _ & _ & _ & PU). destruct PU as (_ & _ & _ & P4 & _ & P6 & _).
pose proof (used_size_pos n ltac:(lia)) as [U1 _]. pose proof (round_up_ge (used_size n) 8 ltac:(lia)) as RU0.
destruct (Z.le_gt_cases phi (rl_T X)) as [H1|H1]; [left; exact H1|].
destruct (Z.le_gt_cases (rl_T X + 4096) plo) as [H2|H2]; [right; exact H2|].
exfalso. apply (proj1 (PT3 (Z.max plo (rl_T X)) ltac:(lia))). lia. }
destruct (free_switch a LB0 FS0 G RE X m p A n plo phi GC INB CR ECONT) as (G' & GC' & RPG & RCG & NFC & RQG & QZ').
pose proof (qchunk_geom m plo phi A n) as QG.
clear QG.
destruct CM as (LEFT & (b1 & idw & Hb1 & HDR) & WR & JUNK & SHD & PURE). unfold hdr_cells in HDR. hide SHD.
pose proof PURE as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9). rewrite ?KHI_eq in M8. idtac.
pose proof (used_size_pos n ltac:(lia)) as [U1 U2]. set (u := used_size n) in *.
pose proof (round_up_ge u 8 ltac:(lia)) as RU.
pose proof (ngran_eq u ltac:(lia)) as (NG1 & NG2 & NG3).
assert (AH : 0x645000 <= A).
{ destruct (gc_blocks a LB0 FS0 G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn' & HP' & Ht0 & Hi0 & HA0)|(mb0 & E0 & Hn' & HP' & He0 & HA0)].
- pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht0) as (P1 & _). pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PKx & _).
pose proof (rz_size_range n) as [RZx _]. unfold prim_user in HA0. unfold prim_lo, KHI in *. clear - P1 PKx HA0 RZx. lia.
- pose proof (sec_facts _ _ _ _ _ _ GC _ He0) as (_ & E2x & _ & _ & E5x & _). cbn [se_beg se_size se_req] in *.
pose proof (sec_map_size_ge n ltac:(lia) E5x) as [G1x _]. pose proof (sec_req_facts n ltac:(lia) E5x) as [_ RQx].
unfold kSecUserOff in HA0. clear - E2x G1x RQx HA0. lia. }

assert (JALL : hjunk m A phi).
{ pose proof (wr_at_hjunk _ _ _ WR ltac:(lia)) as (_ & _ & W1). destruct JUNK as (_ & J2 & J3).
split; [lia|]. split; [lia|]. intros x Hx. destruct (Z.lt_ge_cases x (A + u)); [apply W1; lia| apply J3; lia]. }
destruct (hjunk_split _ A (A + 8) phi JALL ltac:(lia)) as [J8 _]. destruct (hjunk_C8 _ A J8) as [w0 JC]. hide JALL.
destruct (RStats_free_words _ _ _ RS) as (f1 & f2 & STC).
unfold unw_obj in OBJ. cbn [map app] in OBJ.
replace (A - 16) with (A + -16) in HDR by lia.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)] m) as MU.
pose proof (wmono_refl asegs m) as WM.

assert (WCASE : forall lo' hi' x, In (lo', hi') [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)] -> lo' <= x < hi' ->
(band_lo <= x < bv_unsigned sp) \/ (plo <= x < phi) \/ (rl_T X + 2824 <= x < rl_T X + 2840)).
{ intros lo' hi' x Hin Hx. cbn in Hin. pose proof (qchunk_geom m plo phi A n) as XX || idtac.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; [left; lia| left; lia| right; left; lia| right; left; (first [ clear - Hx x AH NG3 NG1 RU U1 M6 M4 u phi plo ks n A BAND; lia | lia ])| right; right; lia]. }
assert (RTW : Forall (rt_avoid RE X) [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)]).
{ apply List.Forall_forall. intros [lo' hi'] Hin x Hx FT. cbn [fst snd] in Hx.
destruct (WCASE lo' hi' x Hin Hx) as [Z|[Z|Z]].
- pose proof (fp_lt_ceil a LB0 FS0 G RE X GC x ltac:(left; exact FT)). lia.
- destruct (PZ x Z) as [LU|FC]; [exact (fp_RTconst_cz a LB0 FS0 G RE X GC x FT ltac:(do 2 right; left; exact LU))| exact (fpC_excl a LB0 FS0 G RE X GC x FC (or_introl FT))].
- exact (rt_avoid_Thigh RE X (rl_T X + 2824) (rl_T X + 2840) RL ltac:(lia) ltac:(lia) x ltac:(split; cbn [fst snd]; lia) FT). }
assert (STW : Forall st_avoid [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)]).
{ repeat apply Forall_cons; try apply Forall_nil; st_avoid_solve. }

assert (QO1 : QOTH C a (alb_remove p LB0) FS0 G' RE X m).
{ apply QOTH_split. split; [exact RT|]. split; [exact RS|]. split; [exact (RPG m RP)|].
split; [exact (RCG RC)|]. split; [| split; [rewrite HRD; exact RD| exact RF]].
eapply HRSx; [exact RSE| reflexivity| reflexivity| reflexivity|].
intros e He (A' & HA'). exists A'. apply In_alb_remove in HA' as [HA' _]. exact HA'. }
unfold deallocate_entry, A_INSTANCE in *.
apply aimplT_from_evt.
carve_frame 64%nat ST.
do 9 step.
step. unfold_cond; cond_unsig; if_false.
do 7 step.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_sp_ch (run_free_hooks_spec RE X) ltac:(fun PO => idtac); try eassumption; try lia.
subst. rename POST into RT2.
step. if_true.

assert (AL16 : (A + -16) mod 16 = 0) by (Z.div_mod_to_equations; (first [ clear - H29 q10 H0 H r q AH U1 RU r0 M6 M4 M2 r5 u phi plo ks A p BAND; lia | lia ])).
assert (HK16 : 0x645000 <= A + -16) by (rewrite ?KHI_eq; (first [ clear - AH U1 RU NG1 NG3 M6 M5 M4 M2 PURE u phi plo ks A p BAND; lia | lia ])).
assert (HC16 : A + -16 + 16 <= band_lo) by (idtac; lia).
call_ch (cas_free_hdr) ltac:(fun PO => idtac); try eassumption; try lia.
rename POST into HDR3.
assert (LB1 : Z.land b1 3 = 1) by (destruct Hb1 as [-> | ->]; reflexivity).
assert (B1R : 0 <= b1 < 256) by (first [ clear - HK16 AH U1 RU M6 M5 M4 u Hb1 b1 phi plo ks A p BAND; lia | lia ]).
step. step.
stf.
step.
rewrite zxb_b8, (Z.mod_small b1 256) by lia.
step.
rewrite (unsigned_lit b1), LB1 by lia.
step. if_false.
step. lits.
step.
step. if_true.

step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT3 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_sp_ch (get_thread_stats_spec RE X) ltac:(fun PO => idtac); try eassumption; try lia.
subst. rename POST into RT4.
assert (UB : u <= 2^26 + 1) by (subst u; unfold used_size; lia).
step. step.
change (zx16 (wz 0)) with (wz 0). rewrite (zx32_small u) by lia.
step. step.
step. step.
rewrite (unsigned_lit u) by lia. rewrite Z.lor_0_l.
step. step.
step. step.
do 4 step.
do 8 step.
step. step.
lazymatch goal with ST' : stk _ _ lo _ |- _ => release_frame FR ST' (bv_unsigned sp); rename ST' into STF end.
apply evt_done.

unfold asan_free. rewrite (proj2 (Z.ltb_ge kQMaxSize (aptr_used p))) by (unfold aptr_used; lia).
replace (wz (A + -16)) with (wz (A - 16)) by (f_equal; lia).
unhide SHD. unhide JALL.
lazymatch type of MU with munch ?W m ?mf =>

assert (WZ' : forall lo' hi' z, In (lo', hi') W -> lo' <= z < hi' -> wzone a (alb_remove p LB0) G' RE X (bv_unsigned sp) z);
[ intros lo' hi' z Hin Hx; unfold wzone; destruct (WCASE lo' hi' z Hin Hx) as [Z|[Z|Z]];
[ do 3 right; exact Z
| left; apply QZ'; left; exact Z
| right; right; left; left; split; cbn [fst snd]; lia ]
| ];
assert (QO2 : QOTH C a (alb_remove p LB0) FS0 G' RE X mf);
[ apply QOTH_split in QO1 as (_ & _ & RP1 & QRE1); apply QOTH_split;
split; [eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]|];
split; [eapply RStats_munch; [exact RS| exact MU| exact WM| exact STW]|];
split;
[ eapply RPrim_frame; [exact RP1| exact WM|]; eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Fx _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]];
[ pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx); lia
| exact (fpQ_RPrim a (alb_remove p LB0) FS0 G' RE X GC' z (QZ' z (or_introl Z)) Fx)
| refine (fpP_RStats a (alb_remove p LB0) FS0 G' RE X GC' z Fx _); left; split; cbn [fst snd]; lia ]
| eapply QREST_munch; [exact GC'| exact QRE1| exact MU| exact WM|]; intros lo' hi' z Hin Hy; eapply wzone_pzone; exact (WZ' lo' hi' z Hin Hy) ]
| ];

assert (AGQ : agree_on asegs (fp_RQuar a LB0 G RE X) m mf);
[ eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Fx _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]];
[ exact (fp_RQuar_cz a LB0 FS0 G RE X GC z Fx ltac:(left; lia))
| destruct (PZ z Z) as [LU|FC]; [exact (fp_RQuar_cz a LB0 FS0 G RE X GC z Fx ltac:(do 2 right; left; exact LU))| exact (fpQ_RChunks a LB0 FS0 G RE X GC z Fx FC)]
| refine (fpQ_RStats a LB0 FS0 G RE X GC z Fx _); left; split; cbn [fst snd]; lia ]
| ];
assert (AGlow : agree_on asegs (fun z => 2147446784 <= z < 17594333495296) m mf);
[ eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Hz _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]]; [idtac; lia| (first [ clear - Z Hz z AH U1 RU NG1 NG3 M8 M6 M5 M4 PURE phi plo u ks A p BAND; lia | lia ])| (first [ clear - Z Hz z HK16 AH U1 RU M6 M5 M4 M1 phi plo PK TK u ks A p X RE BAND; lia | lia ])]
| ];
assert (AGlr : agree_on asegs (fun z => plo <= z < A + -16) m mf);
[ eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Hz _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]]; [idtac; lia| | (first [ clear - Z Hz z HK16 AH U1 RU M8 M6 M5 M4 PTT PURE phi plo PK TK u ks A p X RE BAND; lia | lia ])];
cbn in Hin; destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; (first [ clear - Hy Hz z HC16 AH U1 RU M6 M4 phi plo CEIL' u LO ks lo A p sp BAND Z HK16 M8 M5 PTT PURE PK TK X RE; lia | lia ])
| ];
assert (QM : qchunk_mem mf plo phi A (aptr_req p));
[ split; [| split; [| split; [| split]]];
[ intros Hrz; destruct (LEFT Hrz) as [LC LJ]; split; [| eapply hjunk_wmono; [exact LJ| exact WM]];
eapply rw_cells_agree; [exact AGlr| exact LC|]; intros z Hz; cbn [cells_size csize Nat.add] in Hz; (first [ clear - Hz z Hrz HK16 AH U1 RU NG1 NG3 M6 M5 M4 M2 M1 phi plo u ks A p BAND; lia | lia ])
| exists b1, idw; split; [exact Hb1| exact HDR3]
| eapply hjunk_wmono; [exact JALL| exact WM]
| exists (ush u); eapply rw_cells_agree; [exact AGlow| exact SHD|]; intros z Hz; cbn [cells_size csize] in Hz; change (used_size (aptr_req p)) with u in Hz;
rewrite !Nat.add_0_r, !Nat2Z.inj_add, !Z2Nat.id in Hz by (Z.div_mod_to_equations; (first [ clear - H34 q11 H29 q10 H0 H r Hz z HK16 U1 RU r1 M8 M6 M4 M2 M1 q5 q PURE r6 r5 r4 r3 phi plo u ks A p BAND NG2 H19 q8 NG1 q6 NG3 M5; lia | lia ])); unfold SH, A_SHADOW_OFS in Hz; cbn beta; Z.div_mod_to_equations; (first [ clear - H39 q12 H10 H9 r1 H5 H4 r0 H0 H r Hz q z HK16 U1 RU r2 NG3 M9 M8 M6 M4 M1 q6 q5 PURE r7 r6 r5 r4 phi plo TB u ks A p X BAND; lia | lia ])
| exact PURE ]
| ];
pose proof (RQG 0 QB QB mf RQ AGQ QM) as RQ2;
assert (QR2 : QRUN C 0 QB QB [(p, A)] a (alb_remove p LB0) FS0 G' RE X mf) by (split; [exact GC'| split; [exact QO2| exact RQ2]])
end.
eapply aimplT_mono.
{ eapply (qchunk_spec C L RE X HRD); [exact QR2| eassumption| exact STF| exact CEIL'| unfold QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; lia| lia
| exact QRM| exact OBJ| exact SZB| eapply (depot_keep_of_pzone _ _ _ _ RE X m _ _ GC' MU WM); [intros lo' hi' z Hin Hy; eapply wzone_pzone; exact (WZ' lo' hi' z Hin Hy)| exact DNH]
| exact DCAP| exact OLO| change (2^64) with 18446744073709551616; lia]. }
cbv beta. intros r1 s'' ms'' PO. unfold qret_post in PO |- *.
destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m5 & G5 & -> & -> & MI5 & ST5 & AP5 & DS5 & QR5).
do 15 eexists. exists m5, G5. split; [reflexivity|]. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [| split; [| exact QR5]].
2:{
destruct DS5 as [DS5 ES5]. split; [eapply depot_keep_step; [| exact DS5]; eapply (depot_keep_of_pzone _ _ _ _ RE X m _ _ GC' MU WM); intros lo' hi' z Hin Hy; eapply wzone_pzone; exact (WZ' lo' hi' z Hin Hy)|].
eapply errno_keep_trans; [| exact ES5]. eapply (errno_keep_of_ezone _ _ _ _ RE X m _ _ GC' MU WM). intros lo' hi' z Hin Hy. unfold ezone.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]]; [do 5 right; lia| left; apply QZ'; left; exact Z| right; right; left; unfold in_iv; cbn [fst snd]; lia]. }
eapply aheap_presA_trans; [| exact AP5].
eapply aheap_presA_of_munch_w; [exact GC'| apply Permutation_refl| apply Permutation_refl| lia| exact MU| exact WM| exact WZ'].
Qed.
End S.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QpY2.Mq3 QqLk QnRU.Mqa Q9Ho.Mq2 QmP7.Mq0 QYyZ.Mq0 Q9Ho.Mq1.
Import QpY2.Mq2.
Import QUnM QpME.Mq0.
Import QYyZ.Mq5.
Import Qu3b.Mq2 QnRU.Mq8 QmvA.Mq3 QkZz.Mq1 QteI.Mq9 QQ8H.Mq3 Qx6U.Mq4.
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
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_4 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Import QcA6.Mq1.

Section S.
Context {BAND : Band}.

Lemma live_chunk_facts : forall (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay) (m : word -> option byte)
(p : aptr) (A n : Z),
gcons a LB0 FS0 G RE X -> RChunks a LB0 G RE X m -> In (p, A, n) LB0 ->
(exists lo_ hi_, chunk_mem m lo_ hi_ A n /\ n = aptr_req p /\ 0 <= n
/\ (lo_, hi_) = chunk_cont p A n
/\ (forall x, lo_ <= x < hi_ -> in_live_user LB0 x \/ fp_RChunks a LB0 G RE X x)
/\ (forall x, in_sh (lo_, hi_ - lo_) x -> fp_RChunks a LB0 G RE X x)
/\ (forall x, lo_ <= x < hi_ -> ~ (rl_T X <= x < rl_T X + 4096) /\ ~ (rl_dn X <= x < rl_dn X + 1048576) /\ ~ (rl_ssb X <= x < rl_ssb X + 8388608)))
/\ 0x645000 <= A.
Proof.
intros a LB0 FS0 G RE X m p A n GC RC INB.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC, TD. rewrite ?KHI_eq in PK. idtac.
pose proof (gc_block_small _ _ _ _ _ _ GC _ _ _ INB) as HN2.
pose proof (RChunks_open _ _ _ _ _ _ _ _ _ RC INB) as CR.
assert (PC0 : exists lo_ hi_, chunk_mem m lo_ hi_ A n /\ n = aptr_req p /\ 0 <= n
/\ (lo_, hi_) = chunk_cont p A n
/\ (forall x, lo_ <= x < hi_ -> in_live_user LB0 x \/ fp_RChunks a LB0 G RE X x)
/\ (forall x, in_sh (lo_, hi_ - lo_) x -> fp_RChunks a LB0 G RE X x)
/\ (forall x, lo_ <= x < hi_ -> ~ (rl_T X <= x < rl_T X + 4096) /\ ~ (rl_dn X <= x < rl_dn X + 1048576) /\ ~ (rl_ssb X <= x < rl_ssb X + 8388608))).
{ pose proof (rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & _ & _ & NPd & _). unfold iv_disjoint, prim_lo in NPd; cbn [fst snd] in NPd.
pose proof (rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & _ & _ & BPd & _). unfold iv_disjoint, prim_lo in BPd; cbn [fst snd] in BPd.
destruct (gc_blocks a LB0 FS0 G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn & HP & Ht0 & Hi0 & HA0)|(mb0 & E0 & Hn & HP & He0 & HA0)].
- subst p. cbn [chunk_rep] in CR. destruct CR as (_ & i & Ht & HA & CM).
pose proof (gc_unique a LB0 FS0 G RE X GC _ _ _ _ (APrim id0 n) _ _ Ht0 Ht ltac:(unfold holds; apply aptr_eqb_refl') ltac:(unfold holds; apply aptr_eqb_refl')) as [_ <-].
eexists _, _. split; [exact CM|]. split; [reflexivity|]. split; [exact Hn|]. split; [cbn [chunk_cont]; rewrite HA; f_equal; lia|].
pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht) as (P1 & P2 & _). unfold prim_hi, prim_lo in P1, P2.
split; [| split].
+ intros x Hx. destruct (decide (A <= x < A + n)) as [IN|OUT].
* left. exists (APrim id0 n, A, n). split; [exact INB| cbn [ablk_addr ablk_size fst snd]; lia].
* right. left. split; [left; exists (class_of n), i0, (TLive (APrim id0 n)); split; [exact Ht|]; split; [reflexivity| split; cbn [fst snd]; lia]|].
intros (b & Hb & Hbx). destruct b as [[pb Ab] nb]. cbn [ablk_addr ablk_size fst snd] in Hbx.
destruct (decide ((pb, Ab, nb) = (APrim id0 n, A, n))) as [E|NE]; [injection E; intros; subst; lia|].
refine (proj2 RC _ _ _ _ _ _ x Hb INB NE _ _).
-- pose proof (live_block_geom a LB0 FS0 G RE X GC pb Ab nb Hb) as (_ & _ & [(c' & i' & Ht' & Hc' & Epb & HA' & CT)|(e' & He' & Epb & Hr & HA' & CT)]); unfold blk_container in CT.
++ rewrite Epb in Hc' |- *. cbn [chunk_cont fst snd]. replace (class_of nb) with c' by (symmetry; exact Hc'). split; cbn [fst snd]; lia.
++ rewrite Epb. cbn [chunk_cont fst snd]. pose proof (sec_facts _ _ _ _ _ _ GC _ He') as (_ & _ & _ & E4' & _). cbn [se_size se_req] in E4'.
rewrite <- Hr, <- E4'. split; cbn [fst snd]; lia.
-- cbn [chunk_cont fst snd]. split; cbn [fst snd]; lia.
+ intros x Hx. right; left. exists (class_of n), i0, (TLive (APrim id0 n)). split; [exact Ht|]. split; [reflexivity|].
replace (slot_beg RE (class_of n) i0 + class_size (class_of n) - slot_beg RE (class_of n) i0) with (class_size (class_of n)) in Hx by lia. exact Hx.
+ intros x Hx. lia.
- subst p. cbn [chunk_rep] in CR. destruct CR as (_ & He & HA & CM).
eexists _, _. split; [exact CM|]. split; [reflexivity|]. split; [exact Hn|]. split; [reflexivity|].
pose proof (sec_facts _ _ _ _ _ _ GC _ He) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & D2 & D3). cbn [se_beg se_size se_req] in *.
assert (LIVE : sec_live LB0 (mkSec mb0 (sec_map_size n) n)) by (exists A; exact INB).
split; [| split].
+ intros x Hx. destruct (decide (A <= x < A + n)) as [IN|OUT].
* left. exists (ASec mb0 n, A, n). split; [exact INB| cbn [ablk_addr ablk_size fst snd]; lia].
* right. left. split; [right; exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size]; auto|].
intros (b & Hb & Hbx). destruct b as [[pb Ab] nb]. cbn [ablk_addr ablk_size fst snd] in Hbx.
destruct (decide ((pb, Ab, nb) = (ASec mb0 n, A, n))) as [E|NE]; [injection E; intros; subst; lia|].
refine (proj2 RC _ _ _ _ _ _ x Hb INB NE _ _).
-- pose proof (live_block_geom a LB0 FS0 G RE X GC pb Ab nb Hb) as (_ & _ & [(c' & i' & Ht' & Hc' & Epb & HA' & CT)|(e' & He' & Epb & Hr & HA' & CT)]); unfold blk_container in CT.
++ rewrite Epb in Hc' |- *. cbn [chunk_cont fst snd]. replace (class_of nb) with c' by (symmetry; exact Hc'). split; cbn [fst snd]; (first [ clear - CT HA' i' c' Hbx nb Ab x E1 HA0 KU mb0 ks A RE BAND; lia | lia ]).
++ rewrite Epb. cbn [chunk_cont fst snd]. pose proof (sec_facts _ _ _ _ _ _ GC _ He') as (_ & _ & _ & E4' & _). cbn [se_size se_req] in E4'.
rewrite <- Hr, <- E4'. split; cbn [fst snd]; lia.
-- cbn [chunk_cont fst snd]. split; cbn [fst snd]; lia.
+ intros x Hx. right; right. exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size]. split; [exact He|]. split; [exact LIVE|].
replace (mb0 + sec_map_size n - (mb0 + kPage)) with (sec_map_size n - kPage) in Hx by lia. exact Hx.
+ intros x Hx. pose proof (proj1 (List.Forall_forall _ _) D3 _ (T_obj RE X)) as D. unfold iv_disjoint in D; cbn [fst snd] in D.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (dn_obj RE X)) as Dn. unfold iv_disjoint in Dn; cbn [fst snd] in Dn.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (ssb_obj RE X)) as Db. unfold iv_disjoint in Db; cbn [fst snd] in Db. (first [ clear - Db Dn D Hx x E1 BPd NPd PK TD TK KP mb0 ks n X RE BAND; lia | lia ]). }
assert (AH : 0x645000 <= A).
{ destruct (gc_blocks a LB0 FS0 G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn' & HP' & Ht0 & Hi0 & HA0)|(mb0 & E0 & Hn' & HP' & He0 & HA0)].
- pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht0) as (P1 & _). pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PKx & _).
pose proof (rz_size_range n) as [RZx _]. unfold prim_user in HA0. unfold prim_lo, KHI in *. clear - P1 PKx HA0 RZx. lia.
- pose proof (sec_facts _ _ _ _ _ _ GC _ He0) as (_ & E2x & _ & _ & E5x & _). cbn [se_beg se_size se_req] in *.
pose proof (sec_map_size_ge n ltac:(lia) E5x) as [G1x _]. pose proof (sec_req_facts n ltac:(lia) E5x) as [_ RQx].
unfold kSecUserOff in HA0. clear - E2x G1x RQx HA0. lia. }
split; [exact PC0| exact AH].
Qed.
End S.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5 QvDJ Qt1l QUYN QdWK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Qpj5.Mq1 Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QnRU.Mq2 QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq2 QqLk QmP7.Mq0 QpY2.Mq1 Q9Ho.Mq1 QYyZ.Mq0 QnRU.Mq0 Qu3b.Mq2 QYyZ.Mq5 QpY2.Mq5 QQ8H.Mq2 Qx6U.Mq2.
Import QlES.
Import Qt1l.Mq0 QUYN.Mq0 QdWK.Mq0.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section Lift.
Context {BAND : Band}.
Variable C : arun_components.
Variable LV : lvp.
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRQ : ac_RQuar C = QUnM.RQuar.
Hypothesis HRD : ac_RDepot C = RDepot.
Hypothesis HRF : ac_RFake C = QZbm.RFake.

Hypothesis OBL_RT_REPLACE_STR : forall RE X m, RTconst RE X m -> ro_cells asegs m (0x0ed2f8 + 29) [C1 (b8 1)].
Hypothesis OBL_RT_GOT_MEMCPY : forall RE X m, RTconst RE X m -> ro_cells asegs m 0x0e5de0 [C8 (wz 0x0e7da8)].
Hypothesis OBL_MEMCPY : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv asegs m ->
evt asegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb34c) fc None m (seg_rom asegs)).

Lemma mz_client : forall a LB0 FS0 G RE X LB FS SP x,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
aclient_addrA a_alayout LB FS SP x -> mz G RE X SP x -> False.
Proof.
intros a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA [Z|[Z|[Z|Z]]].
- exact (pzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_introl Z)).
- exact (pzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_intror Z)).
- exact (depot_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA Z).
- exact (qzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_intror Z)).
Qed.

Lemma strdup_prim_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (b : ablock) (src lo : Z) (str : list byte) (dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m ->
In b LB -> ablk_addr b <= src -> src + Z.of_nat (length str) + 1 <= ablk_addr b + ablk_size b ->
bytes_at asegs m src (str ++ [b8 0]) -> ~ In (b8 0) str -> Z.of_nat (length str) + 1 <= 2^26 ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - STRDUP_STACK ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 src ->
from_primary (Z.of_nat (length str) + 1) = true ->
@implMG PStateA asegs (at_nodeA LV asegs) _ (raw_malloc_A L (Z.of_nat (length str) + 1)) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some p => exists A,
a0' = Z_to_bv 64 A /\ ablock_rangeA A (Z.of_nat (length str) + 1) /\ aptr_req p = Z.of_nat (length str) + 1
/\ ARUN C s' ((p, A, Z.of_nat (length str) + 1) :: LB) FS RE m'
/\ rw_cells asegs m' A [CB (S (length str)) (str ++ [b8 0])]
/\ blk_shadow asegs m' A (Z.of_nat (length str) + 1)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 strdup_stub) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros EL AR Hb HA1 HA2 SRC NZ NMAX ST CEIL LO MI -> -> UNW DNH DCAP -> HP.
cbn [ala_tp ala_gp a_alayout] in *.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
set (n := Z.of_nat (length str) + 1) in *.

destruct b as [[p0 A0] n0]. cbn [ablk_addr ablk_size fst snd] in HA1, HA2.
pose proof (ARUN_block_range C _ _ _ _ _ _ AR Hb) as BR. cbn [ablk_addr ablk_size fst snd] in BR. destruct BR as ((APR & _) & _ & BN0 & BBL & _).

assert (KD : KHI <= src \/ (0 < src /\ src + n <= kLowEnd)).
{ rewrite ?KHI_eq. unfold kLowEnd. destruct APR as [[[AP1 AP2]|AP] _]; [right; unfold n; clear - AP1 AP2 HA1 HA2; lia| left; clear - AP HA1; lia]. }
pose proof (ARUN_block_shadow C _ _ _ _ _ _ _ _ AR Hb) as BSH.
pose proof (shadow_ok_sub m A0 n0 src n BSH HA1 ltac:(lia) ltac:(lia)) as SO.
destruct (ARUN_nbhd C HRP HRC HRQ HRF s LB FS RE m src n AR ltac:(left; exists p0, A0, n0; split; [exact Hb| split; lia]) ltac:(lia)) as [NW1 NW2].
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRD in R7.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
assert (Hn : 0 <= n <= 2^26) by lia.
pose proof (class_of_facts n ltac:(lia) HP) as (Hc & Csz & _). cbv zeta in Hc, Csz.
pose proof (bytes_at_bound _ _ _ _ SRC) as SBD. rewrite length_app in SBD. cbn [length] in SBD.

assert (SRCZ : forall x, src <= x < src + Z.of_nat (length (str ++ [b8 0])) -> ~ mz G RE X (bv_unsigned sp) x).
{ intros x Hx Z. rewrite length_app in Hx. cbn [length] in Hx.
apply (mz_client (ps_a s) LB0 FS0 G RE X LB FS (bv_unsigned sp) x GC PB PF ltac:(unfold STRDUP_STACK in LO; lia)); [| exact Z].
right. right. left. exists (p0, A0, n0). split; [exact Hb|]. cbn [ablk_addr ablk_size fst snd]. lia. }
assert (STU : src + Z.of_nat (length (str ++ [b8 0])) <= rl_T X + 3168 \/ rl_T X + 3169 <= src).
{ destruct (Z_le_gt_dec (src + Z.of_nat (length (str ++ [b8 0]))) (rl_T X + 3168)) as [|G1]; [left; assumption|].
destruct (Z_le_gt_dec (rl_T X + 3169) src) as [|G2]; [right; assumption|]. exfalso.
apply (SRCZ (rl_T X + 3168) ltac:(lia)). right. right. left. do 3 right. reflexivity. }
apply raw_malloc_A_intro. rewrite <- EL.
pose proof (strdup_icpt_spec LV RE X (OBL_RT_REPLACE_STR RE X) (OBL_RT_GOT_MEMCPY RE X) OBL_MEMCPY m src lo (bv_unsigned sp) str [] (str ++ [b8 0])
SRC eq_refl NZ ltac:(rewrite length_app; cbn [length]; lia) ltac:(lia) STU SO NW1 NW2 KD NMAX ltac:(lia)
ra (wz 67584) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc s (ps_a s) G LB0 FS0 dn GC R1 R2 R3 R7 MI ST CEIL' LO ltac:(lia) UNW DNH DCAP HP SRCZ) as M.
rewrite Z_to_bv_bv_unsigned in M.
eapply aimplT_mono; [exact M|]. clear M.
intros [r aa] s' ms' PO. cbn [fst snd]. unfold strdup_post in PO.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m' & G1 & -> & -> & WM & MI' & ST' & RT' & RS' & RD' & DS' & REST).
unfold std_postA. rewrite Z_to_bv_bv_unsigned. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
set (c := class_of n) in *.
destruct r as [p|].
- destruct REST as (aa1 & i & -> & -> & QF & GS & TI & I0 & -> & MU & RPF & CM & UC).
destruct (lift_some C HRT HRS HRP HRC HRD s LB FS RE X G LB0 FS0 aa1 G1 c i n m m' (bv_unsigned sp) _ PB PF GC R4 R5 R6 R8 eq_refl Hn HP ltac:(unfold STRDUP_STACK in LO; lia) QF GS TI I0 MU WM
ltac:(intros lo' hi' x Hin Hx; exact (strdup_W_mz RE X (bv_unsigned sp) (ps_a s) aa1 LB0 FS0 G G1 c i lo' hi' x GC GS TI ltac:(lia) ltac:(lia) Hin Hx))
RT' RS' RD' RPF CM) as (HP1 & HP2 & HP3 & HP4).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|].
exists (slot_beg RE c i + rz_size n). split; [reflexivity|]. split; [exact HP2|]. split; [reflexivity|]. split; [exact HP3|].
split; [| exact HP4]. replace (S (length str)) with (Z.to_nat n) by (unfold n; lia). exact UC.
- destruct REST as (-> & MU & QF & GS & RP').
destruct (lift_none C HRT HRS HRP HRC HRD s LB FS RE X G LB0 FS0 aa G1 c n m m' (bv_unsigned sp) _ PB PF GC R4 R5 R6 R8 eq_refl ltac:(unfold STRDUP_STACK in LO; lia) QF GS MU WM
ltac:(intros lo' hi' x Hin Hx; exact (strdup_W_mz0 RE X (bv_unsigned sp) (ps_a s) LB0 FS0 G c lo' hi' x GC ltac:(lia) ltac:(lia) Hin Hx))
RT' RS' RD' RP') as (HP1 & HP3).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|]. split; [reflexivity| exact HP3].
Qed.
End Lift.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QbcP_c1 Q61C QWRO Qu4g QFQR QKBN QN4c QV3O QXcn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QpY2.Mqd QV3O QnRU.Mql Q9Ho.Mq4 QmP7.Mq1 QYyZ.Mq8 Q9Ho.Mq3.
Import QpY2.Mqc.
Import QXcn QpME.Mq7.
Import QYyZ.Mqc.
Import Qu3b QnRU.Mqj QmvA QkZz.Mq2 QteI.Mqi QQ8H.Mq6 Qx6U.Mq8.
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
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_4 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Import QcA6.

Section S.
Context {BAND : Band}.

Lemma live_chunk_facts : forall (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay) (m : word -> option byte)
(p : aptr) (A n : Z),
gcons a LB0 FS0 G RE X -> RChunks a LB0 G RE X m -> In (p, A, n) LB0 ->
(exists lo_ hi_, chunk_mem m lo_ hi_ A n /\ n = aptr_req p /\ 0 <= n
/\ (lo_, hi_) = chunk_cont p A n
/\ (forall x, lo_ <= x < hi_ -> in_live_user LB0 x \/ fp_RChunks a LB0 G RE X x)
/\ (forall x, in_sh (lo_, hi_ - lo_) x -> fp_RChunks a LB0 G RE X x)
/\ (forall x, lo_ <= x < hi_ -> ~ (rl_T X <= x < rl_T X + 4096) /\ ~ (rl_dn X <= x < rl_dn X + 1048576) /\ ~ (rl_ssb X <= x < rl_ssb X + 8388608)))
/\ 0x647000 <= A.
Proof.
intros a LB0 FS0 G RE X m p A n GC RC INB.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC, TD. rewrite ?KHI_eq in PK. idtac.
pose proof (gc_block_small _ _ _ _ _ _ GC _ _ _ INB) as HN2.
pose proof (RChunks_open _ _ _ _ _ _ _ _ _ RC INB) as CR.
assert (PC0 : exists lo_ hi_, chunk_mem m lo_ hi_ A n /\ n = aptr_req p /\ 0 <= n
/\ (lo_, hi_) = chunk_cont p A n
/\ (forall x, lo_ <= x < hi_ -> in_live_user LB0 x \/ fp_RChunks a LB0 G RE X x)
/\ (forall x, in_sh (lo_, hi_ - lo_) x -> fp_RChunks a LB0 G RE X x)
/\ (forall x, lo_ <= x < hi_ -> ~ (rl_T X <= x < rl_T X + 4096) /\ ~ (rl_dn X <= x < rl_dn X + 1048576) /\ ~ (rl_ssb X <= x < rl_ssb X + 8388608))).
{ pose proof (rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & _ & _ & NPd & _). unfold iv_disjoint, prim_lo in NPd; cbn [fst snd] in NPd.
pose proof (rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & _ & _ & BPd & _). unfold iv_disjoint, prim_lo in BPd; cbn [fst snd] in BPd.
destruct (gc_blocks a LB0 FS0 G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn & HP & Ht0 & Hi0 & HA0)|(mb0 & E0 & Hn & HP & He0 & HA0)].
- subst p. cbn [chunk_rep] in CR. destruct CR as (_ & i & Ht & HA & CM).
pose proof (gc_unique a LB0 FS0 G RE X GC _ _ _ _ (APrim id0 n) _ _ Ht0 Ht ltac:(unfold holds; apply aptr_eqb_refl') ltac:(unfold holds; apply aptr_eqb_refl')) as [_ <-].
eexists _, _. split; [exact CM|]. split; [reflexivity|]. split; [exact Hn|]. split; [cbn [chunk_cont]; rewrite HA; f_equal; lia|].
pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht) as (P1 & P2 & _). unfold prim_hi, prim_lo in P1, P2.
split; [| split].
+ intros x Hx. destruct (decide (A <= x < A + n)) as [IN|OUT].
* left. exists (APrim id0 n, A, n). split; [exact INB| cbn [ablk_addr ablk_size fst snd]; lia].
* right. left. split; [left; exists (class_of n), i0, (TLive (APrim id0 n)); split; [exact Ht|]; split; [reflexivity| split; cbn [fst snd]; lia]|].
intros (b & Hb & Hbx). destruct b as [[pb Ab] nb]. cbn [ablk_addr ablk_size fst snd] in Hbx.
destruct (decide ((pb, Ab, nb) = (APrim id0 n, A, n))) as [E|NE]; [injection E; intros; subst; lia|].
refine (proj2 RC _ _ _ _ _ _ x Hb INB NE _ _).
-- pose proof (live_block_geom a LB0 FS0 G RE X GC pb Ab nb Hb) as (_ & _ & [(c' & i' & Ht' & Hc' & Epb & HA' & CT)|(e' & He' & Epb & Hr & HA' & CT)]); unfold blk_container in CT.
++ rewrite Epb in Hc' |- *. cbn [chunk_cont fst snd]. replace (class_of nb) with c' by (symmetry; exact Hc'). split; cbn [fst snd]; lia.
++ rewrite Epb. cbn [chunk_cont fst snd]. pose proof (sec_facts _ _ _ _ _ _ GC _ He') as (_ & _ & _ & E4' & _). cbn [se_size se_req] in E4'.
rewrite <- Hr, <- E4'. split; cbn [fst snd]; lia.
-- cbn [chunk_cont fst snd]. split; cbn [fst snd]; lia.
+ intros x Hx. right; left. exists (class_of n), i0, (TLive (APrim id0 n)). split; [exact Ht|]. split; [reflexivity|].
replace (slot_beg RE (class_of n) i0 + class_size (class_of n) - slot_beg RE (class_of n) i0) with (class_size (class_of n)) in Hx by lia. exact Hx.
+ intros x Hx. lia.
- subst p. cbn [chunk_rep] in CR. destruct CR as (_ & He & HA & CM).
eexists _, _. split; [exact CM|]. split; [reflexivity|]. split; [exact Hn|]. split; [reflexivity|].
pose proof (sec_facts _ _ _ _ _ _ GC _ He) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & D2 & D3). cbn [se_beg se_size se_req] in *.
assert (LIVE : sec_live LB0 (mkSec mb0 (sec_map_size n) n)) by (exists A; exact INB).
split; [| split].
+ intros x Hx. destruct (decide (A <= x < A + n)) as [IN|OUT].
* left. exists (ASec mb0 n, A, n). split; [exact INB| cbn [ablk_addr ablk_size fst snd]; lia].
* right. left. split; [right; exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size]; auto|].
intros (b & Hb & Hbx). destruct b as [[pb Ab] nb]. cbn [ablk_addr ablk_size fst snd] in Hbx.
destruct (decide ((pb, Ab, nb) = (ASec mb0 n, A, n))) as [E|NE]; [injection E; intros; subst; lia|].
refine (proj2 RC _ _ _ _ _ _ x Hb INB NE _ _).
-- pose proof (live_block_geom a LB0 FS0 G RE X GC pb Ab nb Hb) as (_ & _ & [(c' & i' & Ht' & Hc' & Epb & HA' & CT)|(e' & He' & Epb & Hr & HA' & CT)]); unfold blk_container in CT.
++ rewrite Epb in Hc' |- *. cbn [chunk_cont fst snd]. replace (class_of nb) with c' by (symmetry; exact Hc'). split; cbn [fst snd]; (first [ clear - CT HA' i' c' Hbx nb Ab x E1 HA0 KU mb0 ks A RE BAND; lia | lia ]).
++ rewrite Epb. cbn [chunk_cont fst snd]. pose proof (sec_facts _ _ _ _ _ _ GC _ He') as (_ & _ & _ & E4' & _). cbn [se_size se_req] in E4'.
rewrite <- Hr, <- E4'. split; cbn [fst snd]; lia.
-- cbn [chunk_cont fst snd]. split; cbn [fst snd]; lia.
+ intros x Hx. right; right. exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size]. split; [exact He|]. split; [exact LIVE|].
replace (mb0 + sec_map_size n - (mb0 + kPage)) with (sec_map_size n - kPage) in Hx by lia. exact Hx.
+ intros x Hx. pose proof (proj1 (List.Forall_forall _ _) D3 _ (T_obj RE X)) as D. unfold iv_disjoint in D; cbn [fst snd] in D.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (dn_obj RE X)) as Dn. unfold iv_disjoint in Dn; cbn [fst snd] in Dn.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (ssb_obj RE X)) as Db. unfold iv_disjoint in Db; cbn [fst snd] in Db. (first [ clear - Db Dn D Hx x E1 BPd NPd PK TD TK KP mb0 ks n X RE BAND; lia | lia ]). }
assert (AH : 0x647000 <= A).
{ destruct (gc_blocks a LB0 FS0 G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn' & HP' & Ht0 & Hi0 & HA0)|(mb0 & E0 & Hn' & HP' & He0 & HA0)].
- pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht0) as (P1 & _). pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PKx & _).
pose proof (rz_size_range n) as [RZx _]. unfold prim_user in HA0. unfold prim_lo, KHI in *. clear - P1 PKx HA0 RZx. lia.
- pose proof (sec_facts _ _ _ _ _ _ GC _ He0) as (_ & E2x & _ & _ & E5x & _). cbn [se_beg se_size se_req] in *.
pose proof (sec_map_size_ge n ltac:(lia) E5x) as [G1x _]. pose proof (sec_req_facts n ltac:(lia) E5x) as [_ RQx].
unfold kSecUserOff in HA0. clear - E2x G1x RQx HA0. lia. }
split; [exact PC0| exact AH].
Qed.
End S.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Qpj5.Mq1 Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QnRU.Mqe QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk QV3O QmP7.Mq1 QpY2.Mqb Q9Ho.Mq3 QYyZ.Mq8 QnRU.Mqc Qu3b QYyZ.Mqc QpY2.Mqf QQ8H.Mq5 Qx6U.Mq6.
Import QlES.
Import Qt1l QUYN QdWK.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section Lift.
Context {BAND : Band}.
Variable C : arun_components.
Variable LV : lvp.
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRQ : ac_RQuar C = QXcn.RQuar.
Hypothesis HRD : ac_RDepot C = RDepot.
Hypothesis HRF : ac_RFake C = QsJM.RFake.

Hypothesis OBL_RT_REPLACE_STR : forall RE X m, RTconst RE X m -> ro_cells asegs m (0x0ef9b8 + 29) [C1 (b8 1)].
Hypothesis OBL_RT_GOT_MEMCPY : forall RE X m, RTconst RE X m -> ro_cells asegs m 0x0e81e0 [C8 (wz 0x0ea1c8)].
Hypothesis OBL_MEMCPY : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv asegs m ->
evt asegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdda10) fc None m (seg_rom asegs)).

Lemma mz_client : forall a LB0 FS0 G RE X LB FS SP x,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
aclient_addrA a_alayout LB FS SP x -> mz G RE X SP x -> False.
Proof.
intros a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA [Z|[Z|[Z|Z]]].
- exact (pzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_introl Z)).
- exact (pzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_intror Z)).
- exact (depot_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA Z).
- exact (qzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_intror Z)).
Qed.

Lemma strdup_prim_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (b : ablock) (src lo : Z) (str : list byte) (dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m ->
In b LB -> ablk_addr b <= src -> src + Z.of_nat (length str) + 1 <= ablk_addr b + ablk_size b ->
bytes_at asegs m src (str ++ [b8 0]) -> ~ In (b8 0) str -> Z.of_nat (length str) + 1 <= 2^26 ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - STRDUP_STACK ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 src ->
from_primary (Z.of_nat (length str) + 1) = true ->
@implMG PStateA asegs (at_nodeA LV asegs) _ (raw_malloc_A L (Z.of_nat (length str) + 1)) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some p => exists A,
a0' = Z_to_bv 64 A /\ ablock_rangeA A (Z.of_nat (length str) + 1) /\ aptr_req p = Z.of_nat (length str) + 1
/\ ARUN C s' ((p, A, Z.of_nat (length str) + 1) :: LB) FS RE m'
/\ rw_cells asegs m' A [CB (S (length str)) (str ++ [b8 0])]
/\ blk_shadow asegs m' A (Z.of_nat (length str) + 1)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 strdup_stub) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros EL AR Hb HA1 HA2 SRC NZ NMAX ST CEIL LO MI -> -> UNW DNH DCAP -> HP.
cbn [ala_tp ala_gp a_alayout] in *.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
set (n := Z.of_nat (length str) + 1) in *.

destruct b as [[p0 A0] n0]. cbn [ablk_addr ablk_size fst snd] in HA1, HA2.
pose proof (ARUN_block_range C _ _ _ _ _ _ AR Hb) as BR. cbn [ablk_addr ablk_size fst snd] in BR. destruct BR as ((APR & _) & _ & BN0 & BBL & _).

assert (KD : KHI <= src \/ (0 < src /\ src + n <= kLowEnd)).
{ rewrite ?KHI_eq. unfold kLowEnd. destruct APR as [[[AP1 AP2]|AP] _]; [right; unfold n; clear - AP1 AP2 HA1 HA2; lia| left; clear - AP HA1; lia]. }
pose proof (ARUN_block_shadow C _ _ _ _ _ _ _ _ AR Hb) as BSH.
pose proof (shadow_ok_sub m A0 n0 src n BSH HA1 ltac:(lia) ltac:(lia)) as SO.
destruct (ARUN_nbhd C HRP HRC HRQ HRF s LB FS RE m src n AR ltac:(left; exists p0, A0, n0; split; [exact Hb| split; lia]) ltac:(lia)) as [NW1 NW2].
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRD in R7.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
assert (Hn : 0 <= n <= 2^26) by lia.
pose proof (class_of_facts n ltac:(lia) HP) as (Hc & Csz & _). cbv zeta in Hc, Csz.
pose proof (bytes_at_bound _ _ _ _ SRC) as SBD. rewrite length_app in SBD. cbn [length] in SBD.

assert (SRCZ : forall x, src <= x < src + Z.of_nat (length (str ++ [b8 0])) -> ~ mz G RE X (bv_unsigned sp) x).
{ intros x Hx Z. rewrite length_app in Hx. cbn [length] in Hx.
apply (mz_client (ps_a s) LB0 FS0 G RE X LB FS (bv_unsigned sp) x GC PB PF ltac:(unfold STRDUP_STACK in LO; lia)); [| exact Z].
right. right. left. exists (p0, A0, n0). split; [exact Hb|]. cbn [ablk_addr ablk_size fst snd]. lia. }
assert (STU : src + Z.of_nat (length (str ++ [b8 0])) <= rl_T X + 3168 \/ rl_T X + 3169 <= src).
{ destruct (Z_le_gt_dec (src + Z.of_nat (length (str ++ [b8 0]))) (rl_T X + 3168)) as [|G1]; [left; assumption|].
destruct (Z_le_gt_dec (rl_T X + 3169) src) as [|G2]; [right; assumption|]. exfalso.
apply (SRCZ (rl_T X + 3168) ltac:(lia)). right. right. left. do 3 right. reflexivity. }
apply raw_malloc_A_intro. rewrite <- EL.
pose proof (strdup_icpt_spec LV RE X (OBL_RT_REPLACE_STR RE X) (OBL_RT_GOT_MEMCPY RE X) OBL_MEMCPY m src lo (bv_unsigned sp) str [] (str ++ [b8 0])
SRC eq_refl NZ ltac:(rewrite length_app; cbn [length]; lia) ltac:(lia) STU SO NW1 NW2 KD NMAX ltac:(lia)
ra (wz 67584) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc s (ps_a s) G LB0 FS0 dn GC R1 R2 R3 R7 MI ST CEIL' LO ltac:(lia) UNW DNH DCAP HP SRCZ) as M.
rewrite Z_to_bv_bv_unsigned in M.
eapply aimplT_mono; [exact M|]. clear M.
intros [r aa] s' ms' PO. cbn [fst snd]. unfold strdup_post in PO.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m' & G1 & -> & -> & WM & MI' & ST' & RT' & RS' & RD' & DS' & REST).
unfold std_postA. rewrite Z_to_bv_bv_unsigned. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
set (c := class_of n) in *.
destruct r as [p|].
- destruct REST as (aa1 & i & -> & -> & QF & GS & TI & I0 & -> & MU & RPF & CM & UC).
destruct (lift_some C HRT HRS HRP HRC HRD s LB FS RE X G LB0 FS0 aa1 G1 c i n m m' (bv_unsigned sp) _ PB PF GC R4 R5 R6 R8 eq_refl Hn HP ltac:(unfold STRDUP_STACK in LO; lia) QF GS TI I0 MU WM
ltac:(intros lo' hi' x Hin Hx; exact (strdup_W_mz RE X (bv_unsigned sp) (ps_a s) aa1 LB0 FS0 G G1 c i lo' hi' x GC GS TI ltac:(lia) ltac:(lia) Hin Hx))
RT' RS' RD' RPF CM) as (HP1 & HP2 & HP3 & HP4).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|].
exists (slot_beg RE c i + rz_size n). split; [reflexivity|]. split; [exact HP2|]. split; [reflexivity|]. split; [exact HP3|].
split; [| exact HP4]. replace (S (length str)) with (Z.to_nat n) by (unfold n; lia). exact UC.
- destruct REST as (-> & MU & QF & GS & RP').
destruct (lift_none C HRT HRS HRP HRC HRD s LB FS RE X G LB0 FS0 aa G1 c n m m' (bv_unsigned sp) _ PB PF GC R4 R5 R6 R8 eq_refl ltac:(unfold STRDUP_STACK in LO; lia) QF GS MU WM
ltac:(intros lo' hi' x Hin Hx; exact (strdup_W_mz0 RE X (bv_unsigned sp) (ps_a s) LB0 FS0 G c lo' hi' x GC ltac:(lia) ltac:(lia) Hin Hx))
RT' RS' RD' RP') as (HP1 & HP3).
split; [exact HP1|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact (DS' dn DNH ltac:(unfold DEPOT_CAP in DCAP; lia))|]. split; [reflexivity| exact HP3].
Qed.
End Lift.
End Mq4.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqc.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx6U.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcfN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcfN.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqh.
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

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcA6.

Definition deallocate_entry : Z := 0x3ef80.

Section S.
Context {BAND : Band}.
Variables (C : arun_components) (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).
Hypothesis recycle_spec : recycle_stmt C RE X L.
Hypothesis HRD : ac_RDepot C = RDepot.

Hypothesis HRSx : forall a a' LB LB' RE X m, ac_RSec C a LB RE X m ->
as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
(forall e, In e (as_reg a) -> sec_live LB' e -> sec_live LB e) -> ac_RSec C a' LB' RE X m.

Lemma dealloc_entry_spec : forall ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (p : aptr) (A n lo : Z)
(obj sz bp dn : Z) (q0 q1 q2 q3 q4 : word) (rest : list byte),
QRUN C 0 QB QB [] a LB0 FS0 G RE X m -> In (p, A, n) LB0 -> qroom a p -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - DEALLOC_STACK ->
rw_cells asegs m obj (unw_obj obj sz [q0; q1; q2; q3; q4] rest bp) ->
1 <= sz <= 30 -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= obj -> obj + 2080 < 2^64 ->
aimplT atn (asan_free (ae_L RE) a p) s
(qret_post C RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB0) FS0 lo m free_step)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz A) (wz 0) (wz 0) (wz obj) (wz 1) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz deallocate_entry) fc None m (seg_rom asegs)).
Proof.
intros until rest; intros QR INB QRM MI ST CEIL LO OBJ SZB DNH DCAP OLO OHI.
pose proof CEIL as CEIL'. idtac. unfold DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
change (2^64) with 18446744073709551616 in OHI.
pose proof kq_consts as (K24 & KBB & KBC & KMX & KMN & KMC). pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC, TD. rewrite ?KHI_eq in PK. idtac.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
pose proof (gc_block_small _ _ _ _ _ _ GC _ _ _ INB) as HN2.

pose proof (RChunks_open _ _ _ _ _ _ _ _ _ RC INB) as CR.
assert (PC0 : exists lo_ hi_, chunk_mem m lo_ hi_ A n /\ n = aptr_req p /\ 0 <= n
/\ (lo_, hi_) = chunk_cont p A n
/\ (forall x, lo_ <= x < hi_ -> in_live_user LB0 x \/ fp_RChunks a LB0 G RE X x)
/\ (forall x, in_sh (lo_, hi_ - lo_) x -> fp_RChunks a LB0 G RE X x)
/\ (forall x, lo_ <= x < hi_ -> ~ (rl_T X <= x < rl_T X + 4096) /\ ~ (rl_dn X <= x < rl_dn X + 1048576) /\ ~ (rl_ssb X <= x < rl_ssb X + 8388608))).
{ pose proof (rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & _ & _ & NPd & _). unfold iv_disjoint, prim_lo in NPd; cbn [fst snd] in NPd.
pose proof (rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & _ & _ & BPd & _). unfold iv_disjoint, prim_lo in BPd; cbn [fst snd] in BPd.
destruct (gc_blocks a LB0 FS0 G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn & HP & Ht0 & Hi0 & HA0)|(mb0 & E0 & Hn & HP & He0 & HA0)].
- subst p. cbn [chunk_rep] in CR. destruct CR as (_ & i & Ht & HA & CM).
pose proof (gc_unique a LB0 FS0 G RE X GC _ _ _ _ (APrim id0 n) _ _ Ht0 Ht ltac:(unfold holds; apply aptr_eqb_refl') ltac:(unfold holds; apply aptr_eqb_refl')) as [_ <-].
eexists _, _. split; [exact CM|]. split; [reflexivity|]. split; [exact Hn|]. split; [cbn [chunk_cont]; rewrite HA; f_equal; lia|].
pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht) as (P1 & P2 & _). unfold prim_hi, prim_lo in P1, P2.
split; [| split].
+ intros x Hx. destruct (decide (A <= x < A + n)) as [IN|OUT].
* left. exists (APrim id0 n, A, n). split; [exact INB| cbn [ablk_addr ablk_size fst snd]; lia].
* right. left. split; [left; exists (class_of n), i0, (TLive (APrim id0 n)); split; [exact Ht|]; split; [reflexivity| split; cbn [fst snd]; lia]|].
intros (b & Hb & Hbx). destruct b as [[pb Ab] nb]. cbn [ablk_addr ablk_size fst snd] in Hbx.
destruct (decide ((pb, Ab, nb) = (APrim id0 n, A, n))) as [E|NE]; [injection E; intros; subst; lia|].
refine (proj2 RC _ _ _ _ _ _ x Hb INB NE _ _).
-- pose proof (live_block_geom a LB0 FS0 G RE X GC pb Ab nb Hb) as (_ & _ & [(c' & i' & Ht' & Hc' & Epb & HA' & CT)|(e' & He' & Epb & Hr & HA' & CT)]); unfold blk_container in CT.
++ rewrite Epb in Hc' |- *. cbn [chunk_cont fst snd]. replace (class_of nb) with c' by (symmetry; exact Hc'). split; cbn [fst snd]; lia.
++ rewrite Epb. cbn [chunk_cont fst snd]. pose proof (sec_facts _ _ _ _ _ _ GC _ He') as (_ & _ & _ & E4' & _). cbn [se_size se_req] in E4'.
rewrite <- Hr, <- E4'. split; cbn [fst snd]; lia.
-- cbn [chunk_cont fst snd]. split; cbn [fst snd]; lia.
+ intros x Hx. right; left. exists (class_of n), i0, (TLive (APrim id0 n)). split; [exact Ht|]. split; [reflexivity|].
replace (slot_beg RE (class_of n) i0 + class_size (class_of n) - slot_beg RE (class_of n) i0) with (class_size (class_of n)) in Hx by lia. exact Hx.
+ intros x Hx. lia.
- subst p. cbn [chunk_rep] in CR. destruct CR as (_ & He & HA & CM).
eexists _, _. split; [exact CM|]. split; [reflexivity|]. split; [exact Hn|]. split; [reflexivity|].
pose proof (sec_facts _ _ _ _ _ _ GC _ He) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & D2 & D3). cbn [se_beg se_size se_req] in *.
assert (LIVE : sec_live LB0 (mkSec mb0 (sec_map_size n) n)) by (exists A; exact INB).
split; [| split].
+ intros x Hx. destruct (decide (A <= x < A + n)) as [IN|OUT].
* left. exists (ASec mb0 n, A, n). split; [exact INB| cbn [ablk_addr ablk_size fst snd]; lia].
* right. left. split; [right; exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size]; auto|].
intros (b & Hb & Hbx). destruct b as [[pb Ab] nb]. cbn [ablk_addr ablk_size fst snd] in Hbx.
destruct (decide ((pb, Ab, nb) = (ASec mb0 n, A, n))) as [E|NE]; [injection E; intros; subst; lia|].
refine (proj2 RC _ _ _ _ _ _ x Hb INB NE _ _).
-- pose proof (live_block_geom a LB0 FS0 G RE X GC pb Ab nb Hb) as (_ & _ & [(c' & i' & Ht' & Hc' & Epb & HA' & CT)|(e' & He' & Epb & Hr & HA' & CT)]); unfold blk_container in CT.
++ rewrite Epb in Hc' |- *. cbn [chunk_cont fst snd]. replace (class_of nb) with c' by (symmetry; exact Hc'). split; cbn [fst snd]; (first [ clear - CT HA' i' c' Hbx nb Ab x E1 HA0 KU mb0 ks A RE BAND; lia | lia ]).
++ rewrite Epb. cbn [chunk_cont fst snd]. pose proof (sec_facts _ _ _ _ _ _ GC _ He') as (_ & _ & _ & E4' & _). cbn [se_size se_req] in E4'.
rewrite <- Hr, <- E4'. split; cbn [fst snd]; lia.
-- cbn [chunk_cont fst snd]. split; cbn [fst snd]; lia.
+ intros x Hx. right; right. exists (mkSec mb0 (sec_map_size n) n); cbn [se_beg se_size]. split; [exact He|]. split; [exact LIVE|].
replace (mb0 + sec_map_size n - (mb0 + kPage)) with (sec_map_size n - kPage) in Hx by lia. exact Hx.
+ intros x Hx. pose proof (proj1 (List.Forall_forall _ _) D3 _ (T_obj RE X)) as D. unfold iv_disjoint in D; cbn [fst snd] in D.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (dn_obj RE X)) as Dn. unfold iv_disjoint in Dn; cbn [fst snd] in Dn.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (ssb_obj RE X)) as Db. unfold iv_disjoint in Db; cbn [fst snd] in Db. (first [ clear - Db Dn D Hx x E1 BPd NPd PK TD TK KP mb0 ks n X RE BAND; lia | lia ]). }
destruct PC0 as (plo & phi & CM & En & Hn0 & ECONT & PZ & PZS & PT3).
assert (PTT : phi <= rl_T X \/ rl_T X + 4096 <= plo).
{ pose proof CM as CM0. destruct CM0 as (_ & _ & _ & _ & _ & PU). destruct PU as (_ & _ & _ & P4 & _ & P6 & _).
pose proof (used_size_pos n ltac:(lia)) as [U1 _]. pose proof (round_up_ge (used_size n) 8 ltac:(lia)) as RU0.
destruct (Z.le_gt_cases phi (rl_T X)) as [H1|H1]; [left; exact H1|].
destruct (Z.le_gt_cases (rl_T X + 4096) plo) as [H2|H2]; [right; exact H2|].
exfalso. apply (proj1 (PT3 (Z.max plo (rl_T X)) ltac:(lia))). lia. }
destruct (free_switch a LB0 FS0 G RE X m p A n plo phi GC INB CR ECONT) as (G' & GC' & RPG & RCG & NFC & RQG & QZ').
pose proof (qchunk_geom m plo phi A n) as QG.
clear QG.
destruct CM as (LEFT & (b1 & idw & Hb1 & HDR) & WR & JUNK & SHD & PURE). unfold hdr_cells in HDR. hide SHD.
pose proof PURE as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9). rewrite ?KHI_eq in M8. idtac.
pose proof (used_size_pos n ltac:(lia)) as [U1 U2]. set (u := used_size n) in *.
pose proof (round_up_ge u 8 ltac:(lia)) as RU.
pose proof (ngran_eq u ltac:(lia)) as (NG1 & NG2 & NG3).
assert (AH : 0x647000 <= A).
{ destruct (gc_blocks a LB0 FS0 G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn' & HP' & Ht0 & Hi0 & HA0)|(mb0 & E0 & Hn' & HP' & He0 & HA0)].
- pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht0) as (P1 & _). pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PKx & _).
pose proof (rz_size_range n) as [RZx _]. unfold prim_user in HA0. unfold prim_lo, KHI in *. clear - P1 PKx HA0 RZx. lia.
- pose proof (sec_facts _ _ _ _ _ _ GC _ He0) as (_ & E2x & _ & _ & E5x & _). cbn [se_beg se_size se_req] in *.
pose proof (sec_map_size_ge n ltac:(lia) E5x) as [G1x _]. pose proof (sec_req_facts n ltac:(lia) E5x) as [_ RQx].
unfold kSecUserOff in HA0. clear - E2x G1x RQx HA0. lia. }

assert (JALL : hjunk m A phi).
{ pose proof (wr_at_hjunk _ _ _ WR ltac:(lia)) as (_ & _ & W1). destruct JUNK as (_ & J2 & J3).
split; [lia|]. split; [lia|]. intros x Hx. destruct (Z.lt_ge_cases x (A + u)); [apply W1; lia| apply J3; lia]. }
destruct (hjunk_split _ A (A + 8) phi JALL ltac:(lia)) as [J8 _]. destruct (hjunk_C8 _ A J8) as [w0 JC]. hide JALL.
destruct (RStats_free_words _ _ _ RS) as (f1 & f2 & STC).
unfold unw_obj in OBJ. cbn [map app] in OBJ.
replace (A - 16) with (A + -16) in HDR by lia.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)] m) as MU.
pose proof (wmono_refl asegs m) as WM.

assert (WCASE : forall lo' hi' x, In (lo', hi') [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)] -> lo' <= x < hi' ->
(band_lo <= x < bv_unsigned sp) \/ (plo <= x < phi) \/ (rl_T X + 2824 <= x < rl_T X + 2840)).
{ intros lo' hi' x Hin Hx. cbn in Hin. pose proof (qchunk_geom m plo phi A n) as XX || idtac.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; [left; lia| left; lia| right; left; lia| right; left; (first [ clear - Hx x AH NG3 NG1 RU U1 M6 M4 u phi plo ks n A BAND; lia | lia ])| right; right; lia]. }
assert (RTW : Forall (rt_avoid RE X) [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)]).
{ apply List.Forall_forall. intros [lo' hi'] Hin x Hx FT. cbn [fst snd] in Hx.
destruct (WCASE lo' hi' x Hin Hx) as [Z|[Z|Z]].
- pose proof (fp_lt_ceil a LB0 FS0 G RE X GC x ltac:(left; exact FT)). lia.
- destruct (PZ x Z) as [LU|FC]; [exact (fp_RTconst_cz a LB0 FS0 G RE X GC x FT ltac:(do 2 right; left; exact LU))| exact (fpC_excl a LB0 FS0 G RE X GC x FC (or_introl FT))].
- exact (rt_avoid_Thigh RE X (rl_T X + 2824) (rl_T X + 2840) RL ltac:(lia) ltac:(lia) x ltac:(split; cbn [fst snd]; lia) FT). }
assert (STW : Forall st_avoid [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned sp - 64 - 32, bv_unsigned sp - 64); (A + -16, A + -16 + 4); (A, A + 8);
(rl_T X + 2824, rl_T X + 2840)]).
{ repeat apply Forall_cons; try apply Forall_nil; st_avoid_solve. }

assert (QO1 : QOTH C a (alb_remove p LB0) FS0 G' RE X m).
{ apply QOTH_split. split; [exact RT|]. split; [exact RS|]. split; [exact (RPG m RP)|].
split; [exact (RCG RC)|]. split; [| split; [rewrite HRD; exact RD| exact RF]].
eapply HRSx; [exact RSE| reflexivity| reflexivity| reflexivity|].
intros e He (A' & HA'). exists A'. apply In_alb_remove in HA' as [HA' _]. exact HA'. }
unfold deallocate_entry, A_INSTANCE in *.
apply aimplT_from_evt.
carve_frame 64%nat ST.
do 9 step.
step. unfold_cond; cond_unsig; if_false.
do 7 step.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_sp_ch (run_free_hooks_spec RE X) ltac:(fun PO => idtac); try eassumption; try lia.
subst. rename POST into RT2.
step. if_true.

assert (AL16 : (A + -16) mod 16 = 0) by (Z.div_mod_to_equations; (first [ clear - H29 q10 H0 H r q AH U1 RU r0 M6 M4 M2 r5 u phi plo ks A p BAND; lia | lia ])).
assert (HK16 : 0x647000 <= A + -16) by (rewrite ?KHI_eq; (first [ clear - AH U1 RU NG1 NG3 M6 M5 M4 M2 PURE u phi plo ks A p BAND; lia | lia ])).
assert (HC16 : A + -16 + 16 <= band_lo) by (idtac; lia).
call_ch (cas_free_hdr) ltac:(fun PO => idtac); try eassumption; try lia.
rename POST into HDR3.
assert (LB1 : Z.land b1 3 = 1) by (destruct Hb1 as [-> | ->]; reflexivity).
assert (B1R : 0 <= b1 < 256) by (first [ clear - HK16 AH U1 RU M6 M5 M4 u Hb1 b1 phi plo ks A p BAND; lia | lia ]).
step. step.
stf.
step.
rewrite zxb_b8, (Z.mod_small b1 256) by lia.
step.
rewrite (unsigned_lit b1), LB1 by lia.
step. if_false.
step. lits.
step.
step. if_true.

step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT3 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_sp_ch (get_thread_stats_spec RE X) ltac:(fun PO => idtac); try eassumption; try lia.
subst. rename POST into RT4.
assert (UB : u <= 2^26 + 1) by (subst u; unfold used_size; lia).
step. step.
change (zx16 (wz 0)) with (wz 0). rewrite (zx32_small u) by lia.
step. step.
step. step.
rewrite (unsigned_lit u) by lia. rewrite Z.lor_0_l.
step. step.
step. step.
do 4 step.
do 8 step.
step. step.
lazymatch goal with ST' : stk _ _ lo _ |- _ => release_frame FR ST' (bv_unsigned sp); rename ST' into STF end.
apply evt_done.

unfold asan_free. rewrite (proj2 (Z.ltb_ge kQMaxSize (aptr_used p))) by (unfold aptr_used; lia).
replace (wz (A + -16)) with (wz (A - 16)) by (f_equal; lia).
unhide SHD. unhide JALL.
lazymatch type of MU with munch ?W m ?mf =>

assert (WZ' : forall lo' hi' z, In (lo', hi') W -> lo' <= z < hi' -> wzone a (alb_remove p LB0) G' RE X (bv_unsigned sp) z);
[ intros lo' hi' z Hin Hx; unfold wzone; destruct (WCASE lo' hi' z Hin Hx) as [Z|[Z|Z]];
[ do 3 right; exact Z
| left; apply QZ'; left; exact Z
| right; right; left; left; split; cbn [fst snd]; lia ]
| ];
assert (QO2 : QOTH C a (alb_remove p LB0) FS0 G' RE X mf);
[ apply QOTH_split in QO1 as (_ & _ & RP1 & QRE1); apply QOTH_split;
split; [eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]|];
split; [eapply RStats_munch; [exact RS| exact MU| exact WM| exact STW]|];
split;
[ eapply RPrim_frame; [exact RP1| exact WM|]; eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Fx _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]];
[ pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx); lia
| exact (fpQ_RPrim a (alb_remove p LB0) FS0 G' RE X GC' z (QZ' z (or_introl Z)) Fx)
| refine (fpP_RStats a (alb_remove p LB0) FS0 G' RE X GC' z Fx _); left; split; cbn [fst snd]; lia ]
| eapply QREST_munch; [exact GC'| exact QRE1| exact MU| exact WM|]; intros lo' hi' z Hin Hy; eapply wzone_pzone; exact (WZ' lo' hi' z Hin Hy) ]
| ];

assert (AGQ : agree_on asegs (fp_RQuar a LB0 G RE X) m mf);
[ eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Fx _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]];
[ exact (fp_RQuar_cz a LB0 FS0 G RE X GC z Fx ltac:(left; lia))
| destruct (PZ z Z) as [LU|FC]; [exact (fp_RQuar_cz a LB0 FS0 G RE X GC z Fx ltac:(do 2 right; left; exact LU))| exact (fpQ_RChunks a LB0 FS0 G RE X GC z Fx FC)]
| refine (fpQ_RStats a LB0 FS0 G RE X GC z Fx _); left; split; cbn [fst snd]; lia ]
| ];
assert (AGlow : agree_on asegs (fun z => 2147446784 <= z < 17594333495296) m mf);
[ eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Hz _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]]; [idtac; lia| (first [ clear - Z Hz z AH U1 RU NG1 NG3 M8 M6 M5 M4 PURE phi plo u ks A p BAND; lia | lia ])| (first [ clear - Z Hz z HK16 AH U1 RU M6 M5 M4 M1 phi plo PK TK u ks A p X RE BAND; lia | lia ])]
| ];
assert (AGlr : agree_on asegs (fun z => plo <= z < A + -16) m mf);
[ eapply agree_on_of_munch; [exact MU| exact WM|]; intros z Hz _; apply outside_intro; intros lo' hi' Hin Hy;
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]]; [idtac; lia| | (first [ clear - Z Hz z HK16 AH U1 RU M8 M6 M5 M4 PTT PURE phi plo PK TK u ks A p X RE BAND; lia | lia ])];
cbn in Hin; destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; (first [ clear - Hy Hz z HC16 AH U1 RU M6 M4 phi plo CEIL' u LO ks lo A p sp BAND Z HK16 M8 M5 PTT PURE PK TK X RE; lia | lia ])
| ];
assert (QM : qchunk_mem mf plo phi A (aptr_req p));
[ split; [| split; [| split; [| split]]];
[ intros Hrz; destruct (LEFT Hrz) as [LC LJ]; split; [| eapply hjunk_wmono; [exact LJ| exact WM]];
eapply rw_cells_agree; [exact AGlr| exact LC|]; intros z Hz; cbn [cells_size csize Nat.add] in Hz; (first [ clear - Hz z Hrz HK16 AH U1 RU NG1 NG3 M6 M5 M4 M2 M1 phi plo u ks A p BAND; lia | lia ])
| exists b1, idw; split; [exact Hb1| exact HDR3]
| eapply hjunk_wmono; [exact JALL| exact WM]
| exists (ush u); eapply rw_cells_agree; [exact AGlow| exact SHD|]; intros z Hz; cbn [cells_size csize] in Hz; change (used_size (aptr_req p)) with u in Hz;
rewrite !Nat.add_0_r, !Nat2Z.inj_add, !Z2Nat.id in Hz by (Z.div_mod_to_equations; (first [ clear - H34 q11 H29 q10 H0 H r Hz z HK16 U1 RU r1 M8 M6 M4 M2 M1 q5 q PURE r6 r5 r4 r3 phi plo u ks A p BAND NG2 H19 q8 NG1 q6 NG3 M5; lia | lia ])); unfold SH, A_SHADOW_OFS in Hz; cbn beta; Z.div_mod_to_equations; (first [ clear - H39 q12 H10 H9 r1 H5 H4 r0 H0 H r Hz q z HK16 U1 RU r2 NG3 M9 M8 M6 M4 M1 q6 q5 PURE r7 r6 r5 r4 phi plo TB u ks A p X BAND; lia | lia ])
| exact PURE ]
| ];
pose proof (RQG 0 QB QB mf RQ AGQ QM) as RQ2;
assert (QR2 : QRUN C 0 QB QB [(p, A)] a (alb_remove p LB0) FS0 G' RE X mf) by (split; [exact GC'| split; [exact QO2| exact RQ2]])
end.
eapply aimplT_mono.
{ eapply (qchunk_spec C L RE X HRD); [exact QR2| eassumption| exact STF| exact CEIL'| unfold QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; lia| lia
| exact QRM| exact OBJ| exact SZB| eapply (depot_keep_of_pzone _ _ _ _ RE X m _ _ GC' MU WM); [intros lo' hi' z Hin Hy; eapply wzone_pzone; exact (WZ' lo' hi' z Hin Hy)| exact DNH]
| exact DCAP| exact OLO| change (2^64) with 18446744073709551616; lia]. }
cbv beta. intros r1 s'' ms'' PO. unfold qret_post in PO |- *.
destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m5 & G5 & -> & -> & MI5 & ST5 & AP5 & DS5 & QR5).
do 15 eexists. exists m5, G5. split; [reflexivity|]. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [| split; [| exact QR5]].
2:{
destruct DS5 as [DS5 ES5]. split; [eapply depot_keep_step; [| exact DS5]; eapply (depot_keep_of_pzone _ _ _ _ RE X m _ _ GC' MU WM); intros lo' hi' z Hin Hy; eapply wzone_pzone; exact (WZ' lo' hi' z Hin Hy)|].
eapply errno_keep_trans; [| exact ES5]. eapply (errno_keep_of_ezone _ _ _ _ RE X m _ _ GC' MU WM). intros lo' hi' z Hin Hy. unfold ezone.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[Z|Z]]; [do 5 right; lia| left; apply QZ'; left; exact Z| right; right; left; unfold in_iv; cbn [fst snd]; lia]. }
eapply aheap_presA_trans; [| exact AP5].
eapply aheap_presA_of_munch_w; [exact GC'| apply Permutation_refl| apply Permutation_refl| lia| exact MU| exact WM| exact WZ'].
Qed.
End S.
