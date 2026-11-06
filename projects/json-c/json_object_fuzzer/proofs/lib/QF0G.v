(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QCiC Qpj5 QvDJ Q67d Q6sh QQwg QKTr QJBH QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QNQk QjgW QXcn QV3O QsJM QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig Qc6I QJFf.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q67d QCiC.Mq0 Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QNQk.Mq6 QjgW QXcn QV3O QsJM.
Import QlES. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma RTconst_frame_nw {BAND : Band} : forall RE X m m', RTconst RE X m -> agree_on asegs (fp_RTconst RE X) m m' -> RTconst RE X m'.
Proof.
intros RE X m m' (HI & HT & HC1 & HC2 & HD & HW) AG. split; [|split; [|split; [|split; [|split]]]].
- apply List.Forall_forall. intros [a cs] Hin. pose proof (proj1 (List.Forall_forall _ _) HI _ Hin) as RC. cbn [fst snd] in *.
destruct (rt_img_cells_inside RE X a cs ltac:(apply in_or_app; left; exact Hin)) as (iv & Hiv & B1 & B2).
eapply ro_cells_agree; [exact AG| exact RC|]. intros x Hx. left. exists iv. split; [exact Hiv|]. split; lia.
- eapply ro_cells_agree; [exact AG| exact HT|]. intros x Hx. right; left. cbn [rt_T_cells cells_size csize Nat.add] in Hx. split; cbn [fst snd]; lia.
- eapply ro_cells_agree; [exact AG| exact HC1|]. intros x Hx. right; right; left. cbn [cells_size csize Nat.add] in Hx. split; cbn [fst snd]; lia.
- eapply ro_cells_agree; [exact AG| exact HC2|]. intros x Hx. right; right; left. cbn [cells_size csize Nat.add] in Hx. split; cbn [fst snd]; lia.
- eapply ro_cells_agree; [exact AG| exact HD|]. intros x Hx. right; right; right. cbn [cells_size csize Nat.add] in Hx. split; cbn [fst snd]; lia.
- apply List.Forall_forall. intros [a cs] Hin. pose proof (proj1 (List.Forall_forall _ _) HW _ Hin) as RC. cbn [fst snd] in *.
destruct (rt_img_cells_inside RE X a cs ltac:(apply in_or_app; right; exact Hin)) as (iv & Hiv & B1 & B2).
eapply rw_cells_agree; [exact AG| exact RC|]. intros x Hx. left. exists iv. split; [exact Hiv|]. split; lia.
Qed.

Lemma RStats_frame_nw : forall RE X m m', RStats RE X m -> agree_on asegs (fp_RStats RE X) m m' -> RStats RE X m'.
Proof.
intros RE X m m' (H1 & [e H2] & [b H3]) AG. split; [eapply hjunk_agree; [exact AG| exact H1|]; intros z Hz; left; split; cbn [fst snd]; lia|]. split.
- exists e. eapply rw_cells_agree; [exact AG| exact H2|]. intros z Hz. right; left. cbn [cells_size csize Nat.add] in Hz. split; cbn [fst snd]; lia.
- exists b. eapply rw_cells_agree; [exact AG| exact H3|]. intros z Hz. right; right. cbn [cells_size csize Nat.add] in Hz. lia.
Qed.

Section RPrimFrameNW.
Variables (a : AState) (G : ghost) (RE : aentry) (X : rlay).
Lemma RPrim_frame_nw : forall m m', RPrim a G RE X m -> agree_on asegs (fp_RPrim G RE X) m m' -> RPrim a G RE X m'.
Proof.
intros m m' (K & HJ & GNE & HCall) AG. exists K. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
split.
{ eapply hjunk_agree; [exact AG| exact HJ|]. intros z Hz. right; left. split; cbn [fst snd]; lia. }
split; [exact GNE|].
intros c Hc. pose proof (HCall c Hc) as HC. rewrite K32 in Hc.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5). rewrite KM in G5.
assert (INRI : forall z, ri_addr RE c <= z < ri_addr RE c + 128 -> fp_RPrim G RE X z).
{ intros z Hz. left. unfold ri_addr in Hz. split; cbn [fst snd]; lia. }
assert (INPC : forall z, pc_addr X c <= z < pc_addr X c + 80 -> fp_RPrim G RE X z).
{ intros z Hz. right; left. unfold pc_addr in Hz. split; cbn [fst snd]; lia. }
split; [split; [|split]|split].
- exists j1, j2, j3, j4. eapply rw_cells_agree; [exact AG| exact RI|]. intros z Hz. apply INRI. cbn [ri_cells cells_size csize Nat.add] in Hz. lia.
- eapply rw_cells_agree; [exact AG| exact PC|]. intros z Hz. apply INPC. cbn [pc_cells cells_size csize Nat.add] in Hz. lia.
- exists CH. split; [|split; [exact LCH| exact HCH]]. eapply u32arr_agree; [exact AG| exact ACH|]. intros z Hz. apply INPC. rewrite LCH in Hz. cbn in Hz. lia.
- exact PU.
- intros Hc1. specialize (REG Hc1). destruct REG as (FA & FJ & SL & UT & SS & US & UJ & FS).
assert (HCL : 1 <= c <= 31) by lia.
pose proof (class_size_facts c HCL) as [SZ1 SZ2].
assert (RB : reg_beg (ae_L RE) c = al_space_beg (ae_L RE) + c * 2^32) by (unfold reg_beg; rewrite KR; reflexivity).
assert (FB : fa_beg (ae_L RE) c = reg_beg (ae_L RE) c + kFreeArrayOffset) by reflexivity.
assert (INFA : forall z, fa_beg (ae_L RE) c <= z < fa_beg (ae_L RE) c + kFreeArraySize -> fp_RPrim G RE X z).
{ intros z Hz. right; right; left. exists c. rewrite K32. split; [lia| exact Hz]. }
assert (INFS : forall z, SH (fa_beg (ae_L RE) c) <= z < SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8 -> fp_RPrim G RE X z).
{ intros z Hz. right; right; right; left. exists c. rewrite K32. split; [lia|]. split; cbn [fst snd]; lia. }

assert (NSU : forall z, reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + kFreeArrayOffset ->
(forall i' t', tag_at G c i' = Some t' -> tag_prim t' = false -> ~ (slot_beg RE c i' <= z < slot_beg RE c i' + class_size c)) ->
fp_RPrim G RE X z).
{ intros z Hz NS. do 4 right; left. split; [exists c; rewrite K32; split; [lia| exact Hz]|].
intros (c' & i' & t' & Ht' & Hf & [Hin1 Hin2]). cbn [fst snd] in Hin1, Hin2.
destruct (Z.eq_dec c' c) as [->|NE].
- apply (NS i' t' Ht'); [destruct (tag_prim t'); [discriminate| reflexivity]| lia].
- pose proof (rprim_slot_geom a G RE X K m c' i' t' GNE HCall Ht') as (C1 & _ & S1 & _ & RB' & R1 & R2 & B1 & B2 & _).
rewrite RB' in R1, R2. rewrite RB in Hz. rewrite KO in *. clear - Hz Hin1 Hin2 NE C1 S1 R1 R2 B1 B2 HCL. lia. }
assert (NSS : forall z, in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) z ->
(forall i' t', tag_at G c i' = Some t' -> tag_prim t' = false -> ~ in_sh (slot_beg RE c i', class_size c) z) ->
fp_RPrim G RE X z).
{ intros z Hz NS. do 5 right. split; [exists c; rewrite K32; split; [lia| exact Hz]|].
intros (c' & i' & t' & Ht' & Hf & Hin).
destruct (Z.eq_dec c' c) as [->|NE].
- apply (NS i' t' Ht'); [destruct (tag_prim t'); [discriminate| reflexivity]| exact Hin].
- pose proof (rprim_slot_geom a G RE X K m c' i' t' GNE HCall Ht') as (C1 & I1 & S1 & S2 & RB' & R1 & R2 & B1 & B2 & SB' & k' & K0 & K1 & K2 & K3).
destruct Hz as [Z1 Z2]. destruct Hin as [Y1 Y2]. cbn [fst snd] in Z1, Z2, Y1, Y2.
rewrite SB', RB' in Y1, Y2. rewrite RB in Z1, Z2. rewrite KO in *.
replace (al_space_beg (ae_L RE) + c' * 2^32 + i' * class_size c') with (al_space_beg (ae_L RE) + 8 * (c' * 2^29 + k')) in Y1, Y2 by lia.
replace (al_space_beg (ae_L RE) + c * 2^32) with (al_space_beg (ae_L RE) + 8 * (c * 2^29)) in Z1, Z2 by lia.
rewrite !SH_plus8 in Y1, Y2, Z1, Z2. rewrite K2 in Y2.
replace (8 * (class_size c' / 8) / 8) with (class_size c' / 8) in Y2 by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
change (3758096384 / 8) with 469762048 in Z2.
clear - Z1 Z2 Y1 Y2 NE C1 I1 S1 K0 K1 K2 K3 B1 B2 HCL. lia. }
assert (KO8 : kFreeArrayOffset = 8 * 469762048) by (rewrite KO; reflexivity).
assert (KS8 : kFreeArraySize = 8 * 67108864) by (rewrite KS; reflexivity).
assert (AU8 : exists q, 0 <= q /\ c_alloc_user (cls a c) = 8 * q).
{ exists (Z.of_nat (length (G c)) * (class_size c / 8)). split; [(first [ clear - KS8 SZ1 G3 G2 G1 LCH CH c K G a; nia | nia ])|]. rewrite <- G1. Z.div_mod_to_equations. (first [ clear - H26 H25 H19 q3 H14 q2 H5 H4 r0 H0 H r KS8 KO8 q0 SZ2 r2 SZ1 G5 r3 G4 G3 G2 G1 P14 r4 q LCH CH c K G a; nia | nia ]). }
destruct AU8 as (qa & QA0 & QA).
assert (MU8 : exists q, c_mapped_user (cls a c) = 8 * q) by (exists (c_mapped_user (cls a c) / 8); Z.div_mod_to_equations; (first [ clear - H31 H30 H24 q4 H0 H r q G5 r4 P14 r5 LCH CH c K G a; lia | lia ])).
destruct MU8 as (qm & QM).
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
+
eapply u32arr_agree; [exact AG| exact FA|]. intros z Hz. rewrite map_length in Hz. apply INFA. lia.
+ eapply hjunk_agree; [exact AG| exact FJ|]. intros z Hz. apply INFA. lia.
+
intros i t Ht Hp. eapply hjunk_agree; [exact AG| exact (SL i t Ht Hp)|]. intros z Hz.
pose proof (rprim_slot_geom a G RE X K m c i t GNE HCall Ht) as (_ & I1 & _ & _ & _ & R1 & R2 & _ & _ & SB & _).
apply NSU; [lia|]. intros i' t' Ht' Hf [Y1 Y2].
pose proof (rprim_slot_geom a G RE X K m c i' t' GNE HCall Ht') as (_ & I1' & _ & _ & _ & R1' & R2' & _ & _ & SB' & _).
destruct (Z.eq_dec i i') as [->|NE]; [pose proof (tag_at_inj _ _ _ _ _ Ht Ht') as <-; rewrite Hp in Hf; discriminate|].
rewrite SB in Hz. rewrite SB' in Y1, Y2. pose proof (slots_apart i i' (class_size c) ltac:(lia) I1 I1' NE). clear - Hz Y1 Y2 H. lia.
+
eapply hjunk_agree; [exact AG| exact UT|]. intros z Hz. apply NSU; [lia|]. intros i' t' Ht' Hf [Y1 Y2].
pose proof (rprim_slot_geom a G RE X K m c i' t' GNE HCall Ht') as (_ & _ & _ & _ & _ & R1' & R2' & _). lia.
+
intros i t Ht Hp. eapply rw_cells_agree; [exact AG| exact (SS i t Ht Hp)|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by lia.
pose proof (rprim_slot_geom a G RE X K m c i t GNE HCall Ht) as (_ & I1 & _ & _ & _ & R1 & R2 & _ & _ & SB & k & K0 & K1 & K2 & K3).
rewrite SB, K1, SH_plus8 in Hz.
apply NSS.
* split; cbn [fst snd]; [clear - Hz K0 K1 K2 K3 G3 G4; lia|]. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz K0 K1 K2 K3 G3 G4 SZ1 KO8. lia.
* intros i' t' Ht' Hf [Y1 Y2]. cbn [fst snd] in Y1, Y2.
pose proof (rprim_slot_geom a G RE X K m c i' t' GNE HCall Ht') as (_ & I1' & _ & _ & _ & R1' & R2' & _ & _ & SB' & k' & K0' & K1' & K2' & K3').
destruct (Z.eq_dec i i') as [->|NE]; [pose proof (tag_at_inj _ _ _ _ _ Ht Ht') as <-; rewrite Hp in Hf; discriminate|].
rewrite SB', K1', SH_plus8 in Y1, Y2.
pose proof (slots_apart i i' (class_size c) ltac:(lia) I1 I1' NE) as D. clear - Hz Y1 Y2 D K1 K1' K2 SZ1. lia.
+
eapply rw_cells_agree; [exact AG| exact US|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by (Z.div_mod_to_equations; lia).
rewrite QA, QM in Hz. replace (8 * qm - 8 * qa) with (8 * (qm - qa)) in Hz by lia.
rewrite SH_plus8 in Hz. rewrite (Z.mul_comm 8 (qm - qa)), Z.div_mul in Hz by lia.
apply NSS.
* split; cbn [fst snd]; [clear - Hz QA0 QA QM G3; lia|]. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz QA0 QA QM G3 G4 KO8; lia.
* intros i' t' Ht' Hf [Y1 Y2]. cbn [fst snd] in Y1, Y2.
pose proof (rprim_slot_geom a G RE X K m c i' t' GNE HCall Ht') as (_ & I1' & _ & _ & _ & R1' & R2' & _ & _ & SB' & k' & K0' & K1' & K2' & K3').
rewrite SB', K1', SH_plus8 in Y1, Y2. clear - Hz Y1 Y2 K0' K1' K2' K3' QA QA0 SZ1. lia.
+
eapply hjunk_agree; [exact AG| exact UJ|]. intros z Hz. rewrite QM, KO8, !SH_plus8 in Hz.
apply NSS.
* split; cbn [fst snd]; [clear - Hz QM G3 G2; lia|]. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz QM G3 G2 G4 KO8; lia.
* intros i' t' Ht' Hf [Y1 Y2]. cbn [fst snd] in Y1, Y2.
pose proof (rprim_slot_geom a G RE X K m c i' t' GNE HCall Ht') as (_ & I1' & _ & _ & _ & R1' & R2' & _ & _ & SB' & k' & K0' & K1' & K2' & K3').
rewrite SB', K1', SH_plus8 in Y1, Y2. clear - Hz Y1 Y2 K0' K1' K2' K3' QM G3 SZ1. lia.
+
eapply hjunk_agree; [exact AG| exact FS|]. intros z Hz. rewrite KS8, SH_plus8 in Hz. apply INFS. rewrite KS8, Z.mul_comm, Z.div_mul by lia. lia.
Qed.
End RPrimFrameNW.

Definition in_live_used (LB : list ablock) (x : Z) : Prop := exists b, In b LB /\ ablk_addr b <= x < ablk_addr b + used_size (ablk_size b).

Lemma RChunks_frame_nw {BAND : Band} : forall a LB G RE X m m',
RChunks a LB G RE X m -> agree_on asegs (in_live_used LB) m m' -> agree_on asegs (fp_RChunks a LB G RE X) m m' -> RChunks a LB G RE X m'.
Proof.
intros a LB G RE X m m' RC AGU AG. pose proof RC as [H1 H2]. split; [|exact H2].
intros p A n Hin. pose proof (H1 p A n Hin) as CR.
pose proof (chunk_rep_cont a G RE m p A n CR) as (CM & C1 & C2 & C3 & C4).

assert (INC : forall z, fst (chunk_cont p A n) <= z < snd (chunk_cont p A n) -> ~ (A <= z < A + n) -> fp_RChunks a LB G RE X z).
{ intros z Hz NU. left. split; [| eapply nonuser_not_live; eassumption].
destruct p as [id n0|mb n0]; cbn [chunk_rep chunk_cont fst snd] in CR, Hz |- *.
- destruct CR as (-> & i & Ht & HA & _). left. exists (class_of n), i, (TLive (APrim id n)).
split; [exact Ht|]. split; [reflexivity|]. split; cbn [fst snd]; lia.
- destruct CR as (-> & HR & HA & _). right. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req].
split; [exact HR|]. split; [exists A; exact Hin| lia]. }
assert (INS : forall z, in_sh (fst (chunk_cont p A n), snd (chunk_cont p A n) - fst (chunk_cont p A n)) z -> fp_RChunks a LB G RE X z).
{ intros z Hz. right.
destruct p as [id n0|mb n0]; cbn [chunk_rep chunk_cont fst snd] in CR, Hz |- *.
- destruct CR as (-> & i & Ht & HA & _). left. exists (class_of n), i, (TLive (APrim id n)).
split; [exact Ht|]. split; [reflexivity|]. replace (slot_beg RE (class_of n) i) with (A - rz_size n) by lia.
destruct Hz as [Z1 Z2]; cbn [fst snd] in Z1, Z2. split; cbn [fst snd]; lia.
- destruct CR as (-> & HR & HA & _). right. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req].
split; [exact HR|]. split; [exists A; exact Hin|].
destruct Hz as [Z1 Z2]; cbn [fst snd] in Z1, Z2. split; cbn [fst snd]; lia. }
set (lo := fst (chunk_cont p A n)) in *. set (hi := snd (chunk_cont p A n)) in *.
assert (TRANS : chunk_mem m' lo hi A n).
{ destruct CM as (LEFT & (b1 & id & B1 & HDR) & WR & RIGHT & SHD & PURE).
pose proof PURE as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
pose proof (round_up_ge (used_size n) 8 ltac:(lia)) as (U1 & U2 & U3). pose proof (ngran_eq (used_size n) ltac:(unfold used_size; lia)) as (N1 & N2 & N3).
split; [|split; [|split; [|split; [|split; [|exact PURE]]]]].
- intros Hrz. destruct (LEFT Hrz) as [L1 L2]. split.
+ eapply rw_cells_agree; [exact AG| exact L1|]. intros z Hz. cbn [cells_size csize Nat.add] in Hz. apply INC; clearbody lo hi; lia.
+ eapply hjunk_agree; [exact AG| exact L2|]. intros z Hz. apply INC; clearbody lo hi; lia.
- exists b1, id. split; [exact B1|]. eapply rw_cells_agree; [exact AG| exact HDR|]. intros z Hz. cbn [hdr_cells cells_size csize Nat.add] in Hz. apply INC; clearbody lo hi; lia.
- destruct WR as (W0 & W1 & HWR). split; [exact W0|]. split; [exact W1|]. intros i Hi.
apply (proj2 (AGU (A + i) ltac:(lia) ltac:(exists (p, A, n); split; [exact Hin| unfold ablk_addr, ablk_size; cbn [fst snd]; lia]))). exact (HWR i Hi).
- eapply hjunk_agree; [exact AG| exact RIGHT|]. intros z Hz. apply INC; clearbody lo hi; unfold used_size in *; lia.
- eapply rw_cells_agree; [exact AG| exact SHD|]. intros z Hz. apply INS.
cbn [cells_size csize] in Hz. unfold fas in Hz. rewrite !Nat.add_0_r in Hz.
rewrite !Nat2Z.inj_add, !Z2Nat.id in Hz by (clearbody lo hi; unfold used_size in *; Z.div_mod_to_equations; (first [ clear - H26 q4 H16 q2 H0 H r Hz z N3 N1 q1 U1 M8 M6 M5 M4 M2 C3 C2 PURE r5 r4 r3 r2 q0 q hi lo n A BAND N2 H31 q5 M1; lia | lia ])).
clearbody lo hi. unfold used_size in *. split; cbn [fst snd]; [lia|].
unfold SH in *. Z.div_mod_to_equations. (first [ clear - H41 q7 H36 q6 H26 q4 H17 H16 r2 H12 H11 r1 H7 H6 r0 q0 Hz z N3 M8 M5 M4 M2 M1 C3 C2 PURE r7 r6 r5 r4 q2 q1 q hi lo n A BAND; lia | lia ]). }
destruct p as [id n0|mb n0]; cbn [chunk_rep] in CR |- *.
- destruct CR as (-> & i & Ht & HA & _). split; [reflexivity|]. exists i. split; [exact Ht|]. split; [exact HA|].
subst lo hi. cbn [chunk_cont fst snd] in TRANS. replace (A - rz_size n) with (slot_beg RE (class_of n) i) in TRANS by lia. exact TRANS.
- destruct CR as (-> & HR & HA & _). split; [reflexivity|]. split; [exact HR|]. split; [exact HA|].
subst lo hi. cbn [chunk_cont fst snd] in TRANS. exact TRANS.
Qed.

Section RSecNW.
Variables (a : AState) (LB : list ablock) (RE : aentry) (X : rlay).
Lemma RSec_frame_nw : forall m m', RSec a LB RE X m -> agree_on asegs (fp_RSec a RE X) m m' -> RSec a LB RE X m'.
Proof.
intros m m' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) AG. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
unfold RSec, RSec_mem.
assert (INST : forall x, A_INSTANCE + 104 <= x < A_INSTANCE + 728 -> fp_RSec a RE X x) by (intros x Hx; left; split; cbn [fst snd]; lia).
assert (PARR : forall x, ptrarr_lo RE <= x < ptrarr_lo RE + 0x800000 -> fp_RSec a RE X x) by (intros x Hx; right; left; split; cbn [fst snd]; lia).
pose proof H8 as (P1 & P2 & P3). unfold kMaxNumChunks in P2. pose proof (Nat2Z.is_nonneg (length (as_reg a))) as P0.
split; [eapply rw_cells_agree; [exact AG| exact H1|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply INST; unfold SEC_NRES in Hx; lia|].
split; [eapply wjunk_agree; [exact AG| exact H2|]; intros x Hx; apply INST; unfold SEC_JUNK in Hx; lia|].
split; [eapply rw_cells_agree; [exact AG| exact H3|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply INST; unfold SEC_MUT in Hx; lia|].
split; [eapply wjunk_agree; [exact AG| exact H4|]; intros x Hx; apply INST; unfold SEC_GST in Hx; lia|].
split; [eapply u64arr_agree; [exact AG| exact H5|]; intros x Hx; rewrite length_map in Hx; apply PARR; lia|].
split; [eapply hjunk_agree; [exact AG| exact H6|]; intros x Hx; apply PARR; lia|].
split; [| exact H8].
intros i e Hi. destruct (H7 i e Hi) as (A1 & A2 & A3). pose proof (nth_error_In _ _ Hi) as Hin.
split; [| split].
- eapply rw_cells_agree; [exact AG| exact A1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; right; left. exists e. split; [exact Hin| lia].
- eapply hjunk_agree; [exact AG| exact A2|]. intros x Hx. right; right; left. exists e. split; [exact Hin| lia].
- eapply rw_cells_agree; [exact AG| exact A3|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; right; right. exists e. split; [exact Hin|].
unfold in_sh. cbn [fst snd]. rewrite KP. change (4096 / 8) with 512. lia.
Qed.
End RSecNW.

Lemma RQuar_frame_nw {BAND : Band} : forall a LB G RE X m m', RQuar a LB G RE X m -> agree_on asegs (fp_RQuar a LB G RE X) m m' -> RQuar a LB G RE X m'.
Proof. intros a LB G RE X m m' H AG. eapply RQuarM_agree; [exact H| exact AG]. Qed.

Section RDepotNW.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Lemma RDepot_frame_nw : forall m m', RDepot RE X m -> agree_on asegs (fp_RDepot RE X) m m' -> RDepot RE X m'.
Proof.
intros m m' (n & tf & st & h0 & j40 & nh & ns & P1 & P2 & P3 & HU & ND & D1 & D2 & D3 & S1 & S2 & S3 & T1 & T2
& CSS & CTAB & CN & CMAP & CND & JD & JS & TU) AG.
assert (AGc : forall A cs, rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> fp_RDepot RE X a) -> rw_cells asegs m' A cs)
by (intros A cs H P; eapply rw_cells_agree; [exact AG| exact H| exact P]).
pose proof (depot_capacity n h0 nh ltac:(lia) (fun i Hi => proj1 (HU i Hi)) ND) as CAP.
exists n, tf, st, h0, j40, nh, ns. repeat (split; [assumption|]).
unfold fp_RDepot, in_iv, SS_BASE, DP_TAB, DP_N, DP_MAP1 in *. cbn [fst snd] in *.
split. { apply AGc; [exact CSS|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { intros b Hb. apply AGc; [exact (CTAB b Hb)|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { apply AGc; [exact CN|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { apply AGc; [exact CMAP|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { intros i Hi. apply AGc; [exact (CND i Hi)|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { eapply hjunk_agree; [exact AG| exact JD|]. intros z Hz. lia. }
split. { eapply hjunk_agree; [exact AG| exact JS|]. intros z Hz. lia. }
apply AGc; [exact TU|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia.
Qed.
End RDepotNW.

Section RFakeNW.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Local Notation FS := (ae_fs_base RE).
Lemma fs_area_in_map : forall z, fs_area_lo FS <= z < fs_area_hi FS -> in_iv (FS, A_FS_MAP_SIZE) z.
Proof. intros z Hz. unfold fs_area_lo, fs_area_hi, in_iv, A_FS_MAP_SIZE in *. cbn [fst snd]. lia. Qed.
Lemma fs_area_sh_in_map : forall z, SH (fs_area_lo FS) <= z < SH (fs_area_hi FS) -> in_sh (FS, A_FS_MAP_SIZE) z.
Proof.
intros z Hz. unfold fs_area_lo, fs_area_hi, in_sh, A_FS_MAP_SIZE in *. cbn [fst snd].
pose proof (SH_le FS (FS + 0x9000) ltac:(lia)) as L. replace (FS + 0xb09000) with (FS + 8 * 1446400) in Hz by lia. rewrite SH_plus8 in Hz. change (0xb09000 / 8) with 1446400. lia.
Qed.
Lemma RFake_frame_nw : forall FS0 m m', RFake FS0 RE X m ->
agree_on asegs (fun x => in_iv (FS, A_FS_MAP_SIZE) x \/ in_sh (FS, A_FS_MAP_SIZE) x) m m' -> agree_on asegs (fp_RFake FS0 RE X) m m' -> RFake FS0 RE X m'.
Proof.
intros FS0 m m' (AL & K1 & K2 & SHP & SSL & GC & HI & FL & SL & J1 & J2) AGM AG.
split; [exact AL|]. split; [exact K1|]. split; [exact K2|]. split; [exact SHP|].
split. { eapply ro_cells_agree; [exact AG| exact SSL|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (fp_meta RE X FS0 a SHP). lia. }
split. { eapply rw_cells_agree; [exact AG| exact GC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (fp_meta RE X FS0 a SHP). lia. }
split. { intros c Hc. destruct (HI c Hc) as [h H]. exists h. eapply rw_cells_agree; [exact AG| exact H|].
intros a Ha. cbn [cells_size csize Nat.add] in Ha. unfold fs_hint, kFsClasses in *. apply (fp_meta RE X FS0 a SHP). lia. }
split. { intros c Hc. pose proof (FL c Hc) as H. eapply u8arr_agree; [exact AG| exact H|].
intros a Ha. rewrite flags_of_length in Ha. pose proof (fs_flag_range FS c 0 Hc ltac:(pose proof (fs_N_pos c Hc); lia)).
pose proof (fs_foff_range c Hc). unfold fs_flag in *. apply (fp_meta RE X FS0 a SHP). lia. }
split. { intros c pos Hin Hp. pose proof (SL c pos Hin Hp) as H. eapply rw_cells_agree; [exact AG| exact H|].
intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (fp_slot RE X FS0 c pos a SHP Hin Hp). lia. }
split; [eapply hjunk_agree; [exact AGM| exact J1|]| eapply hjunk_agree; [exact AGM| exact J2|]].
- intros z Hz. left. exact (fs_area_in_map z Hz).
- intros z Hz. right. exact (fs_area_sh_in_map z Hz).
Qed.
End RFakeNW.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q67d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q67d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyW2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyW2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUxU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUxU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNwL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkfD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkfD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUnM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUnM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqLk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqLk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZbm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZbm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma RTconst_frame_nw {BAND : Band} : forall RE X m m', RTconst RE X m -> agree_on asegs (fp_RTconst RE X) m m' -> RTconst RE X m'.
Proof.
intros RE X m m' (HI & HT & HC1 & HC2 & HD & HW) AG. split; [|split; [|split; [|split; [|split]]]].
- apply List.Forall_forall. intros [a cs] Hin. pose proof (proj1 (List.Forall_forall _ _) HI _ Hin) as RC. cbn [fst snd] in *.
destruct (rt_img_cells_inside RE X a cs ltac:(apply in_or_app; left; exact Hin)) as (iv & Hiv & B1 & B2).
eapply ro_cells_agree; [exact AG| exact RC|]. intros x Hx. left. exists iv. split; [exact Hiv|]. split; lia.
- eapply ro_cells_agree; [exact AG| exact HT|]. intros x Hx. right; left. cbn [rt_T_cells cells_size csize Nat.add] in Hx. split; cbn [fst snd]; lia.
- eapply ro_cells_agree; [exact AG| exact HC1|]. intros x Hx. right; right; left. cbn [cells_size csize Nat.add] in Hx. split; cbn [fst snd]; lia.
- eapply ro_cells_agree; [exact AG| exact HC2|]. intros x Hx. right; right; left. cbn [cells_size csize Nat.add] in Hx. split; cbn [fst snd]; lia.
- eapply ro_cells_agree; [exact AG| exact HD|]. intros x Hx. right; right; right. cbn [cells_size csize Nat.add] in Hx. split; cbn [fst snd]; lia.
- apply List.Forall_forall. intros [a cs] Hin. pose proof (proj1 (List.Forall_forall _ _) HW _ Hin) as RC. cbn [fst snd] in *.
destruct (rt_img_cells_inside RE X a cs ltac:(apply in_or_app; right; exact Hin)) as (iv & Hiv & B1 & B2).
eapply rw_cells_agree; [exact AG| exact RC|]. intros x Hx. left. exists iv. split; [exact Hiv|]. split; lia.
Qed.

Lemma RStats_frame_nw : forall RE X m m', RStats RE X m -> agree_on asegs (fp_RStats RE X) m m' -> RStats RE X m'.
Proof.
intros RE X m m' (H1 & [e H2] & [b H3]) AG. split; [eapply hjunk_agree; [exact AG| exact H1|]; intros z Hz; left; split; cbn [fst snd]; lia|]. split.
- exists e. eapply rw_cells_agree; [exact AG| exact H2|]. intros z Hz. right; left. cbn [cells_size csize Nat.add] in Hz. split; cbn [fst snd]; lia.
- exists b. eapply rw_cells_agree; [exact AG| exact H3|]. intros z Hz. right; right. cbn [cells_size csize Nat.add] in Hz. lia.
Qed.

Section RPrimFrameNW.
Variables (a : AState) (G : ghost) (RE : aentry) (X : rlay).
Lemma RPrim_frame_nw : forall m m', RPrim a G RE X m -> agree_on asegs (fp_RPrim G RE X) m m' -> RPrim a G RE X m'.
Proof.
intros m m' (K & HJ & GNE & HCall) AG. exists K. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
split.
{ eapply hjunk_agree; [exact AG| exact HJ|]. intros z Hz. right; left. split; cbn [fst snd]; lia. }
split; [exact GNE|].
intros c Hc. pose proof (HCall c Hc) as HC. rewrite K32 in Hc.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5). rewrite KM in G5.
assert (INRI : forall z, ri_addr RE c <= z < ri_addr RE c + 128 -> fp_RPrim G RE X z).
{ intros z Hz. left. unfold ri_addr in Hz. split; cbn [fst snd]; lia. }
assert (INPC : forall z, pc_addr X c <= z < pc_addr X c + 80 -> fp_RPrim G RE X z).
{ intros z Hz. right; left. unfold pc_addr in Hz. split; cbn [fst snd]; lia. }
split; [split; [|split]|split].
- exists j1, j2, j3, j4. eapply rw_cells_agree; [exact AG| exact RI|]. intros z Hz. apply INRI. cbn [ri_cells cells_size csize Nat.add] in Hz. lia.
- eapply rw_cells_agree; [exact AG| exact PC|]. intros z Hz. apply INPC. cbn [pc_cells cells_size csize Nat.add] in Hz. lia.
- exists CH. split; [|split; [exact LCH| exact HCH]]. eapply u32arr_agree; [exact AG| exact ACH|]. intros z Hz. apply INPC. rewrite LCH in Hz. cbn in Hz. lia.
- exact PU.
- intros Hc1. specialize (REG Hc1). destruct REG as (FA & FJ & SL & UT & SS & US & UJ & FS).
assert (HCL : 1 <= c <= 31) by lia.
pose proof (class_size_facts c HCL) as [SZ1 SZ2].
assert (RB : reg_beg (ae_L RE) c = al_space_beg (ae_L RE) + c * 2^32) by (unfold reg_beg; rewrite KR; reflexivity).
assert (FB : fa_beg (ae_L RE) c = reg_beg (ae_L RE) c + kFreeArrayOffset) by reflexivity.
assert (INFA : forall z, fa_beg (ae_L RE) c <= z < fa_beg (ae_L RE) c + kFreeArraySize -> fp_RPrim G RE X z).
{ intros z Hz. right; right; left. exists c. rewrite K32. split; [lia| exact Hz]. }
assert (INFS : forall z, SH (fa_beg (ae_L RE) c) <= z < SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8 -> fp_RPrim G RE X z).
{ intros z Hz. right; right; right; left. exists c. rewrite K32. split; [lia|]. split; cbn [fst snd]; lia. }

assert (NSU : forall z, reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + kFreeArrayOffset ->
(forall i' t', tag_at G c i' = Some t' -> tag_prim t' = false -> ~ (slot_beg RE c i' <= z < slot_beg RE c i' + class_size c)) ->
fp_RPrim G RE X z).
{ intros z Hz NS. do 4 right; left. split; [exists c; rewrite K32; split; [lia| exact Hz]|].
intros (c' & i' & t' & Ht' & Hf & [Hin1 Hin2]). cbn [fst snd] in Hin1, Hin2.
destruct (Z.eq_dec c' c) as [->|NE].
- apply (NS i' t' Ht'); [destruct (tag_prim t'); [discriminate| reflexivity]| lia].
- pose proof (rprim_slot_geom a G RE X K m c' i' t' GNE HCall Ht') as (C1 & _ & S1 & _ & RB' & R1 & R2 & B1 & B2 & _).
rewrite RB' in R1, R2. rewrite RB in Hz. rewrite KO in *. clear - Hz Hin1 Hin2 NE C1 S1 R1 R2 B1 B2 HCL. lia. }
assert (NSS : forall z, in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) z ->
(forall i' t', tag_at G c i' = Some t' -> tag_prim t' = false -> ~ in_sh (slot_beg RE c i', class_size c) z) ->
fp_RPrim G RE X z).
{ intros z Hz NS. do 5 right. split; [exists c; rewrite K32; split; [lia| exact Hz]|].
intros (c' & i' & t' & Ht' & Hf & Hin).
destruct (Z.eq_dec c' c) as [->|NE].
- apply (NS i' t' Ht'); [destruct (tag_prim t'); [discriminate| reflexivity]| exact Hin].
- pose proof (rprim_slot_geom a G RE X K m c' i' t' GNE HCall Ht') as (C1 & I1 & S1 & S2 & RB' & R1 & R2 & B1 & B2 & SB' & k' & K0 & K1 & K2 & K3).
destruct Hz as [Z1 Z2]. destruct Hin as [Y1 Y2]. cbn [fst snd] in Z1, Z2, Y1, Y2.
rewrite SB', RB' in Y1, Y2. rewrite RB in Z1, Z2. rewrite KO in *.
replace (al_space_beg (ae_L RE) + c' * 2^32 + i' * class_size c') with (al_space_beg (ae_L RE) + 8 * (c' * 2^29 + k')) in Y1, Y2 by lia.
replace (al_space_beg (ae_L RE) + c * 2^32) with (al_space_beg (ae_L RE) + 8 * (c * 2^29)) in Z1, Z2 by lia.
rewrite !SH_plus8 in Y1, Y2, Z1, Z2. rewrite K2 in Y2.
replace (8 * (class_size c' / 8) / 8) with (class_size c' / 8) in Y2 by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
change (3758096384 / 8) with 469762048 in Z2.
clear - Z1 Z2 Y1 Y2 NE C1 I1 S1 K0 K1 K2 K3 B1 B2 HCL. lia. }
assert (KO8 : kFreeArrayOffset = 8 * 469762048) by (rewrite KO; reflexivity).
assert (KS8 : kFreeArraySize = 8 * 67108864) by (rewrite KS; reflexivity).
assert (AU8 : exists q, 0 <= q /\ c_alloc_user (cls a c) = 8 * q).
{ exists (Z.of_nat (length (G c)) * (class_size c / 8)). split; [(first [ clear - KS8 SZ1 G3 G2 G1 LCH CH c K G a; nia | nia ])|]. rewrite <- G1. Z.div_mod_to_equations. (first [ clear - H26 H25 H19 q3 H14 q2 H5 H4 r0 H0 H r KS8 KO8 q0 SZ2 r2 SZ1 G5 r3 G4 G3 G2 G1 P14 r4 q LCH CH c K G a; nia | nia ]). }
destruct AU8 as (qa & QA0 & QA).
assert (MU8 : exists q, c_mapped_user (cls a c) = 8 * q) by (exists (c_mapped_user (cls a c) / 8); Z.div_mod_to_equations; (first [ clear - H31 H30 H24 q4 H0 H r q G5 r4 P14 r5 LCH CH c K G a; lia | lia ])).
destruct MU8 as (qm & QM).
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
+
eapply u32arr_agree; [exact AG| exact FA|]. intros z Hz. rewrite map_length in Hz. apply INFA. lia.
+ eapply hjunk_agree; [exact AG| exact FJ|]. intros z Hz. apply INFA. lia.
+
intros i t Ht Hp. eapply hjunk_agree; [exact AG| exact (SL i t Ht Hp)|]. intros z Hz.
pose proof (rprim_slot_geom a G RE X K m c i t GNE HCall Ht) as (_ & I1 & _ & _ & _ & R1 & R2 & _ & _ & SB & _).
apply NSU; [lia|]. intros i' t' Ht' Hf [Y1 Y2].
pose proof (rprim_slot_geom a G RE X K m c i' t' GNE HCall Ht') as (_ & I1' & _ & _ & _ & R1' & R2' & _ & _ & SB' & _).
destruct (Z.eq_dec i i') as [->|NE]; [pose proof (tag_at_inj _ _ _ _ _ Ht Ht') as <-; rewrite Hp in Hf; discriminate|].
rewrite SB in Hz. rewrite SB' in Y1, Y2. pose proof (slots_apart i i' (class_size c) ltac:(lia) I1 I1' NE). clear - Hz Y1 Y2 H. lia.
+
eapply hjunk_agree; [exact AG| exact UT|]. intros z Hz. apply NSU; [lia|]. intros i' t' Ht' Hf [Y1 Y2].
pose proof (rprim_slot_geom a G RE X K m c i' t' GNE HCall Ht') as (_ & _ & _ & _ & _ & R1' & R2' & _). lia.
+
intros i t Ht Hp. eapply rw_cells_agree; [exact AG| exact (SS i t Ht Hp)|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by lia.
pose proof (rprim_slot_geom a G RE X K m c i t GNE HCall Ht) as (_ & I1 & _ & _ & _ & R1 & R2 & _ & _ & SB & k & K0 & K1 & K2 & K3).
rewrite SB, K1, SH_plus8 in Hz.
apply NSS.
* split; cbn [fst snd]; [clear - Hz K0 K1 K2 K3 G3 G4; lia|]. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz K0 K1 K2 K3 G3 G4 SZ1 KO8. lia.
* intros i' t' Ht' Hf [Y1 Y2]. cbn [fst snd] in Y1, Y2.
pose proof (rprim_slot_geom a G RE X K m c i' t' GNE HCall Ht') as (_ & I1' & _ & _ & _ & R1' & R2' & _ & _ & SB' & k' & K0' & K1' & K2' & K3').
destruct (Z.eq_dec i i') as [->|NE]; [pose proof (tag_at_inj _ _ _ _ _ Ht Ht') as <-; rewrite Hp in Hf; discriminate|].
rewrite SB', K1', SH_plus8 in Y1, Y2.
pose proof (slots_apart i i' (class_size c) ltac:(lia) I1 I1' NE) as D. clear - Hz Y1 Y2 D K1 K1' K2 SZ1. lia.
+
eapply rw_cells_agree; [exact AG| exact US|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by (Z.div_mod_to_equations; lia).
rewrite QA, QM in Hz. replace (8 * qm - 8 * qa) with (8 * (qm - qa)) in Hz by lia.
rewrite SH_plus8 in Hz. rewrite (Z.mul_comm 8 (qm - qa)), Z.div_mul in Hz by lia.
apply NSS.
* split; cbn [fst snd]; [clear - Hz QA0 QA QM G3; lia|]. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz QA0 QA QM G3 G4 KO8; lia.
* intros i' t' Ht' Hf [Y1 Y2]. cbn [fst snd] in Y1, Y2.
pose proof (rprim_slot_geom a G RE X K m c i' t' GNE HCall Ht') as (_ & I1' & _ & _ & _ & R1' & R2' & _ & _ & SB' & k' & K0' & K1' & K2' & K3').
rewrite SB', K1', SH_plus8 in Y1, Y2. clear - Hz Y1 Y2 K0' K1' K2' K3' QA QA0 SZ1. lia.
+
eapply hjunk_agree; [exact AG| exact UJ|]. intros z Hz. rewrite QM, KO8, !SH_plus8 in Hz.
apply NSS.
* split; cbn [fst snd]; [clear - Hz QM G3 G2; lia|]. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz QM G3 G2 G4 KO8; lia.
* intros i' t' Ht' Hf [Y1 Y2]. cbn [fst snd] in Y1, Y2.
pose proof (rprim_slot_geom a G RE X K m c i' t' GNE HCall Ht') as (_ & I1' & _ & _ & _ & R1' & R2' & _ & _ & SB' & k' & K0' & K1' & K2' & K3').
rewrite SB', K1', SH_plus8 in Y1, Y2. clear - Hz Y1 Y2 K0' K1' K2' K3' QM G3 SZ1. lia.
+
eapply hjunk_agree; [exact AG| exact FS|]. intros z Hz. rewrite KS8, SH_plus8 in Hz. apply INFS. rewrite KS8, Z.mul_comm, Z.div_mul by lia. lia.
Qed.
End RPrimFrameNW.

Definition in_live_used (LB : list ablock) (x : Z) : Prop := exists b, In b LB /\ ablk_addr b <= x < ablk_addr b + used_size (ablk_size b).

Lemma RChunks_frame_nw {BAND : Band} : forall a LB G RE X m m',
RChunks a LB G RE X m -> agree_on asegs (in_live_used LB) m m' -> agree_on asegs (fp_RChunks a LB G RE X) m m' -> RChunks a LB G RE X m'.
Proof.
intros a LB G RE X m m' RC AGU AG. pose proof RC as [H1 H2]. split; [|exact H2].
intros p A n Hin. pose proof (H1 p A n Hin) as CR.
pose proof (chunk_rep_cont a G RE m p A n CR) as (CM & C1 & C2 & C3 & C4).

assert (INC : forall z, fst (chunk_cont p A n) <= z < snd (chunk_cont p A n) -> ~ (A <= z < A + n) -> fp_RChunks a LB G RE X z).
{ intros z Hz NU. left. split; [| eapply nonuser_not_live; eassumption].
destruct p as [id n0|mb n0]; cbn [chunk_rep chunk_cont fst snd] in CR, Hz |- *.
- destruct CR as (-> & i & Ht & HA & _). left. exists (class_of n), i, (TLive (APrim id n)).
split; [exact Ht|]. split; [reflexivity|]. split; cbn [fst snd]; lia.
- destruct CR as (-> & HR & HA & _). right. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req].
split; [exact HR|]. split; [exists A; exact Hin| lia]. }
assert (INS : forall z, in_sh (fst (chunk_cont p A n), snd (chunk_cont p A n) - fst (chunk_cont p A n)) z -> fp_RChunks a LB G RE X z).
{ intros z Hz. right.
destruct p as [id n0|mb n0]; cbn [chunk_rep chunk_cont fst snd] in CR, Hz |- *.
- destruct CR as (-> & i & Ht & HA & _). left. exists (class_of n), i, (TLive (APrim id n)).
split; [exact Ht|]. split; [reflexivity|]. replace (slot_beg RE (class_of n) i) with (A - rz_size n) by lia.
destruct Hz as [Z1 Z2]; cbn [fst snd] in Z1, Z2. split; cbn [fst snd]; lia.
- destruct CR as (-> & HR & HA & _). right. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req].
split; [exact HR|]. split; [exists A; exact Hin|].
destruct Hz as [Z1 Z2]; cbn [fst snd] in Z1, Z2. split; cbn [fst snd]; lia. }
set (lo := fst (chunk_cont p A n)) in *. set (hi := snd (chunk_cont p A n)) in *.
assert (TRANS : chunk_mem m' lo hi A n).
{ destruct CM as (LEFT & (b1 & id & B1 & HDR) & WR & RIGHT & SHD & PURE).
pose proof PURE as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
pose proof (round_up_ge (used_size n) 8 ltac:(lia)) as (U1 & U2 & U3). pose proof (ngran_eq (used_size n) ltac:(unfold used_size; lia)) as (N1 & N2 & N3).
split; [|split; [|split; [|split; [|split; [|exact PURE]]]]].
- intros Hrz. destruct (LEFT Hrz) as [L1 L2]. split.
+ eapply rw_cells_agree; [exact AG| exact L1|]. intros z Hz. cbn [cells_size csize Nat.add] in Hz. apply INC; clearbody lo hi; lia.
+ eapply hjunk_agree; [exact AG| exact L2|]. intros z Hz. apply INC; clearbody lo hi; lia.
- exists b1, id. split; [exact B1|]. eapply rw_cells_agree; [exact AG| exact HDR|]. intros z Hz. cbn [hdr_cells cells_size csize Nat.add] in Hz. apply INC; clearbody lo hi; lia.
- destruct WR as (W0 & W1 & HWR). split; [exact W0|]. split; [exact W1|]. intros i Hi.
apply (proj2 (AGU (A + i) ltac:(lia) ltac:(exists (p, A, n); split; [exact Hin| unfold ablk_addr, ablk_size; cbn [fst snd]; lia]))). exact (HWR i Hi).
- eapply hjunk_agree; [exact AG| exact RIGHT|]. intros z Hz. apply INC; clearbody lo hi; unfold used_size in *; lia.
- eapply rw_cells_agree; [exact AG| exact SHD|]. intros z Hz. apply INS.
cbn [cells_size csize] in Hz. unfold fas in Hz. rewrite !Nat.add_0_r in Hz.
rewrite !Nat2Z.inj_add, !Z2Nat.id in Hz by (clearbody lo hi; unfold used_size in *; Z.div_mod_to_equations; (first [ clear - H26 q4 H16 q2 H0 H r Hz z N3 N1 q1 U1 M8 M6 M5 M4 M2 C3 C2 PURE r5 r4 r3 r2 q0 q hi lo n A BAND N2 H31 q5 M1; lia | lia ])).
clearbody lo hi. unfold used_size in *. split; cbn [fst snd]; [lia|].
unfold SH in *. Z.div_mod_to_equations. (first [ clear - H41 q7 H36 q6 H26 q4 H17 H16 r2 H12 H11 r1 H7 H6 r0 q0 Hz z N3 M8 M5 M4 M2 M1 C3 C2 PURE r7 r6 r5 r4 q2 q1 q hi lo n A BAND; lia | lia ]). }
destruct p as [id n0|mb n0]; cbn [chunk_rep] in CR |- *.
- destruct CR as (-> & i & Ht & HA & _). split; [reflexivity|]. exists i. split; [exact Ht|]. split; [exact HA|].
subst lo hi. cbn [chunk_cont fst snd] in TRANS. replace (A - rz_size n) with (slot_beg RE (class_of n) i) in TRANS by lia. exact TRANS.
- destruct CR as (-> & HR & HA & _). split; [reflexivity|]. split; [exact HR|]. split; [exact HA|].
subst lo hi. cbn [chunk_cont fst snd] in TRANS. exact TRANS.
Qed.

Section RSecNW.
Variables (a : AState) (LB : list ablock) (RE : aentry) (X : rlay).
Lemma RSec_frame_nw : forall m m', RSec a LB RE X m -> agree_on asegs (fp_RSec a RE X) m m' -> RSec a LB RE X m'.
Proof.
intros m m' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) AG. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
unfold RSec, RSec_mem.
assert (INST : forall x, A_INSTANCE + 104 <= x < A_INSTANCE + 728 -> fp_RSec a RE X x) by (intros x Hx; left; split; cbn [fst snd]; lia).
assert (PARR : forall x, ptrarr_lo RE <= x < ptrarr_lo RE + 0x800000 -> fp_RSec a RE X x) by (intros x Hx; right; left; split; cbn [fst snd]; lia).
pose proof H8 as (P1 & P2 & P3). unfold kMaxNumChunks in P2. pose proof (Nat2Z.is_nonneg (length (as_reg a))) as P0.
split; [eapply rw_cells_agree; [exact AG| exact H1|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply INST; unfold SEC_NRES in Hx; lia|].
split; [eapply wjunk_agree; [exact AG| exact H2|]; intros x Hx; apply INST; unfold SEC_JUNK in Hx; lia|].
split; [eapply rw_cells_agree; [exact AG| exact H3|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply INST; unfold SEC_MUT in Hx; lia|].
split; [eapply wjunk_agree; [exact AG| exact H4|]; intros x Hx; apply INST; unfold SEC_GST in Hx; lia|].
split; [eapply u64arr_agree; [exact AG| exact H5|]; intros x Hx; rewrite length_map in Hx; apply PARR; lia|].
split; [eapply hjunk_agree; [exact AG| exact H6|]; intros x Hx; apply PARR; lia|].
split; [| exact H8].
intros i e Hi. destruct (H7 i e Hi) as (A1 & A2 & A3). pose proof (nth_error_In _ _ Hi) as Hin.
split; [| split].
- eapply rw_cells_agree; [exact AG| exact A1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; right; left. exists e. split; [exact Hin| lia].
- eapply hjunk_agree; [exact AG| exact A2|]. intros x Hx. right; right; left. exists e. split; [exact Hin| lia].
- eapply rw_cells_agree; [exact AG| exact A3|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; right; right. exists e. split; [exact Hin|].
unfold in_sh. cbn [fst snd]. rewrite KP. change (4096 / 8) with 512. lia.
Qed.
End RSecNW.

Lemma RQuar_frame_nw {BAND : Band} : forall a LB G RE X m m', RQuar a LB G RE X m -> agree_on asegs (fp_RQuar a LB G RE X) m m' -> RQuar a LB G RE X m'.
Proof. intros a LB G RE X m m' H AG. eapply RQuarM_agree; [exact H| exact AG]. Qed.

Section RDepotNW.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Lemma RDepot_frame_nw : forall m m', RDepot RE X m -> agree_on asegs (fp_RDepot RE X) m m' -> RDepot RE X m'.
Proof.
intros m m' (n & tf & st & h0 & j40 & nh & ns & P1 & P2 & P3 & HU & ND & D1 & D2 & D3 & S1 & S2 & S3 & T1 & T2
& CSS & CTAB & CN & CMAP & CND & JD & JS & TU) AG.
assert (AGc : forall A cs, rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> fp_RDepot RE X a) -> rw_cells asegs m' A cs)
by (intros A cs H P; eapply rw_cells_agree; [exact AG| exact H| exact P]).
pose proof (depot_capacity n h0 nh ltac:(lia) (fun i Hi => proj1 (HU i Hi)) ND) as CAP.
exists n, tf, st, h0, j40, nh, ns. repeat (split; [assumption|]).
unfold fp_RDepot, in_iv, SS_BASE, DP_TAB, DP_N, DP_MAP1 in *. cbn [fst snd] in *.
split. { apply AGc; [exact CSS|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { intros b Hb. apply AGc; [exact (CTAB b Hb)|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { apply AGc; [exact CN|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { apply AGc; [exact CMAP|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { intros i Hi. apply AGc; [exact (CND i Hi)|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { eapply hjunk_agree; [exact AG| exact JD|]. intros z Hz. lia. }
split. { eapply hjunk_agree; [exact AG| exact JS|]. intros z Hz. lia. }
apply AGc; [exact TU|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia.
Qed.
End RDepotNW.

Section RFakeNW.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Local Notation FS := (ae_fs_base RE).
Lemma fs_area_in_map : forall z, fs_area_lo FS <= z < fs_area_hi FS -> in_iv (FS, A_FS_MAP_SIZE) z.
Proof. intros z Hz. unfold fs_area_lo, fs_area_hi, in_iv, A_FS_MAP_SIZE in *. cbn [fst snd]. lia. Qed.
Lemma fs_area_sh_in_map : forall z, SH (fs_area_lo FS) <= z < SH (fs_area_hi FS) -> in_sh (FS, A_FS_MAP_SIZE) z.
Proof.
intros z Hz. unfold fs_area_lo, fs_area_hi, in_sh, A_FS_MAP_SIZE in *. cbn [fst snd].
pose proof (SH_le FS (FS + 0x9000) ltac:(lia)) as L. replace (FS + 0xb09000) with (FS + 8 * 1446400) in Hz by lia. rewrite SH_plus8 in Hz. change (0xb09000 / 8) with 1446400. lia.
Qed.
Lemma RFake_frame_nw : forall FS0 m m', RFake FS0 RE X m ->
agree_on asegs (fun x => in_iv (FS, A_FS_MAP_SIZE) x \/ in_sh (FS, A_FS_MAP_SIZE) x) m m' -> agree_on asegs (fp_RFake FS0 RE X) m m' -> RFake FS0 RE X m'.
Proof.
intros FS0 m m' (AL & K1 & K2 & SHP & SSL & GC & HI & FL & SL & J1 & J2) AGM AG.
split; [exact AL|]. split; [exact K1|]. split; [exact K2|]. split; [exact SHP|].
split. { eapply ro_cells_agree; [exact AG| exact SSL|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (fp_meta RE X FS0 a SHP). lia. }
split. { eapply rw_cells_agree; [exact AG| exact GC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (fp_meta RE X FS0 a SHP). lia. }
split. { intros c Hc. destruct (HI c Hc) as [h H]. exists h. eapply rw_cells_agree; [exact AG| exact H|].
intros a Ha. cbn [cells_size csize Nat.add] in Ha. unfold fs_hint, kFsClasses in *. apply (fp_meta RE X FS0 a SHP). lia. }
split. { intros c Hc. pose proof (FL c Hc) as H. eapply u8arr_agree; [exact AG| exact H|].
intros a Ha. rewrite flags_of_length in Ha. pose proof (fs_flag_range FS c 0 Hc ltac:(pose proof (fs_N_pos c Hc); lia)).
pose proof (fs_foff_range c Hc). unfold fs_flag in *. apply (fp_meta RE X FS0 a SHP). lia. }
split. { intros c pos Hin Hp. pose proof (SL c pos Hin Hp) as H. eapply rw_cells_agree; [exact AG| exact H|].
intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (fp_slot RE X FS0 c pos a SHP Hin Hp). lia. }
split; [eapply hjunk_agree; [exact AGM| exact J1|]| eapply hjunk_agree; [exact AGM| exact J2|]].
- intros z Hz. left. exact (fs_area_in_map z Hz).
- intros z Hz. right. exact (fs_area_sh_in_map z Hz).
Qed.
End RFakeNW.
