(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN1u.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN22.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1r.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_fret : fetch_word src0segs (Z_to_bv 64 FRET) = Some (0x00008067%bv : bv 32).
Proof. rewrite <- (Z_to_bv_bv_unsigned 32 (0x00008067%bv : bv 32)). apply src0tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_ret' : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma SR_fret E ss ms md k Q :
st_ok src0segs E ss ms -> ss_resv ss = None -> ss_pc ss = FRET ->
sr_get (ss_regs ss) 1 = SOff k 0 -> YK0s.ret_ok (ew E k) ->
m_halted md = None -> m_vm_lazy md = [] ->
Q (mkCfg (mkst (ms_regs ms) (ew E k) (ms_mem ms) (seg_rom src0segs)) md) ->
SR src0segs (mkCfg ms md) Q.
Proof.
intros HS Hrv Hpc Hra Hret Hh Hlz HQ.
pose proof (st_ok_reg src0segs E ss ms 1 HS) as R1. rewrite Hra in R1. cbn [sv_denot] in R1.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R1.
rewrite (st_ok_mkst src0segs E ss ms HS Hrv). rewrite Hpc.
eapply SR_step; [exact Hh | exact Hlz | reflexivity | |].
- eapply step_jalr_x0; [apply fetch_fret | reflexivity | apply decode_ret' | exact R1].
- cbn [ms_regs ms_mem mkst]. change (bv_signed (0%bv : bv 12)) with 0. unfold YK0s.ret_ok in Hret. rewrite Hret.
apply SR_ret. exact HQ.
Qed.
Section T4.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (n : Z).
Hypothesis PRE : call_pre B (MRx B) L A regs mem md.
Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
Variables (regs1 : bvmap 5 word) (mem1 : word -> option byte).
Hypothesis AT : at_PA regs mem n regs1 mem1.
Variable regs2 : bvmap 5 word.
Hypothesis PBS : at_PB L A regs n regs2.
Hypothesis ASH : alloc_slot_hyp B.
Hypothesis GM0 : gmask A n = 0.
Let rom := seg_rom src0segs.
Let SP0 : Z := spZ regs.
Let scv : Z := sc A n.
Lemma PRE_facts : MRx B L A mem md /\ WF A /\ bounded A /\ YK0s.ret_ok (getr regs 1) /\
SP0 mod 16 = 0 /\ alloc_ceiling + 8192 <= SP0 /\ SP0 < 2 ^ 63 /\
(forall a, SP0 - 8192 <= a < SP0 -> writable_at src0segs mem a) /\ getr regs 4 = Z_to_bv 64 (ms_tp B) /\
(forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at src0segs mem a) /\
(st_init_done A = false -> auxv_pre B (ly_sec L) SP0 mem).
Proof. unfold call_pre, ALLOC_STACK in PRE. exact PRE. Qed.
Lemma HI : Inv [] None U0 A. Proof. exact (HI L A regs mem md PRE). Qed.
Lemma MID1 : midrep B L A mem1 md. Proof. exact (MID1 L A regs mem md n PRE regs1 mem1 AT). Qed.
Lemma SCR : 0 <= scv < 48 /\ n + IB <= class_size scv. Proof. exact (sc_range L A regs mem md n PRE Hn). Qed.
Definition xv3 (i : nat) : Z := bv_unsigned (getr regs2 (nat_to_reg i)).
Lemma XR3 : forall k, 0 <= xv3 k < 2 ^ 64. Proof. intros k. unfold xv3. apply u64_range. Qed.
Local Abbreviation E3 := (EV xv3).
Lemma X20 : xv3 20%nat = scv.
Proof. unfold xv3. change (nat_to_reg 20) with (20%bv : bv 5). rewrite (pb_20 _ _ _ _ _ PBS). apply lit64_small. pose proof SCR. lia. Qed.
Lemma X8 : xv3 8%nat = n.
Proof. unfold xv3. change (nat_to_reg 8) with (8%bv : bv 5). rewrite (pb_8 _ _ _ _ _ PBS). apply lit64_small. unfold MMAP_THRESHOLD in Hn. lia. Qed.
Lemma X2 : xv3 2%nat = SP0 - 48.
Proof.
pose proof PRE_facts as (_ & _ & _ & _ & _ & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val).
unfold xv3. change (nat_to_reg 2) with (2%bv : bv 5). rewrite (pb_2 _ _ _ _ _ PBS). apply lit64_small. unfold SP0 in *. lia.
Qed.
Lemma T2c_st_ok : st_ok src0segs E3 ss_T2c (mkst regs2 (Z_to_bv 64 PB) mem1 rom).
Proof.
pose proof PRE_facts as (_ & _ & _ & _ & Hal & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof SCR as [R _].
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_T2c resv_denot].
repeat (split; [reflexivity|]). split; [|split].
- apply regs_ok_lit. intros k Hk.
destruct (Nat.eq_dec k 10) as [->|Hk10]; [cbn; rewrite (pb_10 _ _ _ _ _ PBS), GM0; reflexivity|].
destruct (Nat.eq_dec k 9) as [->|Hk9]; [cbn; exact (pb_9 _ _ _ _ _ PBS)|].
destruct (Nat.eq_dec k 19) as [->|Hk19]; [cbn; exact (pb_19 _ _ _ _ _ PBS)|].
destruct (Nat.eq_dec k 4) as [->|Hk4]; [cbn; exact (pb_4 _ _ _ _ _ PBS)|].
replace (find (fun p : nat * Z => Nat.eqb (fst p) k) [(10%nat, 0); (9%nat, LOCK); (19%nat, DEB); (4%nat, TP)]) with (@None (nat * Z)).
2:{ cbn [find fst]. rewrite !(proj2 (Nat.eqb_neq _ _)) by lia. reflexivity. }
unfold xv3. symmetry. apply Z_to_bv_bv_unsigned.
- split; [vm_compute; reflexivity|]. split; [apply Forall_nil | exact I].
- split; [|split; exact I]. cbn [atoms_ok t2c_facts f_atoms]. unfold afact_ok; cbn [af_lo af_hi af_al2 F_sp48]; rewrite !(ew_EV xv3 XR3), X20, X8, X2.
unfold MMAP_THRESHOLD in Hn. unfold CEIL. change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
repeat split; try lia. unfold SP0 in *. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
Qed.
Record at_AS (regs3 : bvmap 5 word) : Prop := AS_ {
as_1 : getr regs3 1 = Z_to_bv 64 RA_AS;
as_10 : getr regs3 10 = Z_to_bv 64 scv;
as_11 : getr regs3 11 = Z_to_bv 64 n;
as_18 : getr regs3 18 = Z_to_bv 64 scv;
as_2 : getr regs3 2 = Z_to_bv 64 (SP0 - 48);
as_4 : getr regs3 4 = Z_to_bv 64 TP;
as_8 : getr regs3 8 = Z_to_bv 64 n;
as_9 : getr regs3 9 = Z_to_bv 64 LOCK;
as_cs : forall i, In i CSAVED -> getr regs3 (nat_to_reg i) = getr regs (nat_to_reg i) }.
Lemma T2c_post ms3 : st_ok src0segs E3 SST2c ms3 -> frame_of E3 [] mem1 (ms_mem ms3) ->
ms3 = mkst (ms_regs ms3) (Z_to_bv 64 ASLOT) mem1 rom /\ at_AS (ms_regs ms3).
Proof.
intros HS1 HF. pose proof SST2c_view as V. destruct (cview_regs _ _ _ _ _ _ V) as (Hpc & Hrv & Hmem & _).
pose proof (reg_of _ _ _ 1 _ HS1 ltac:(lia) ltac:(reg_eq V 0%nat)) as G1.
pose proof (reg_of _ _ _ 10 _ HS1 ltac:(lia) ltac:(reg_eq V 1%nat)) as G10.
pose proof (reg_of _ _ _ 11 _ HS1 ltac:(lia) ltac:(reg_eq V 2%nat)) as G11.
pose proof (reg_of _ _ _ 18 _ HS1 ltac:(lia) ltac:(reg_eq V 3%nat)) as G18.
pose proof (reg_of _ _ _ 2 _ HS1 ltac:(lia) ltac:(reg_eq V 5%nat)) as G2'.
pose proof (reg_of _ _ _ 4 _ HS1 ltac:(lia) ltac:(reg_eq V 6%nat)) as G4.
pose proof (reg_of _ _ _ 8 _ HS1 ltac:(lia) ltac:(reg_eq V 7%nat)) as G8'.
pose proof (reg_of _ _ _ 9 _ HS1 ltac:(lia) ltac:(reg_eq V 8%nat)) as G9.
assert (GS : forall i, In i CSAVED -> getr (ms_regs ms3) (nat_to_reg i) = sv_denot E3 (SOff i 0)).
{ intros i Hi. pose proof (csaved_cases i Hi) as C.
assert (E : nth i (ss_regs SST2c) (SLit 0) = SOff i 0).
{ decompose [or] C; subst i; [reg_eq V 10%nat | reg_eq V 11%nat | reg_eq V 12%nat | reg_eq V 13%nat | reg_eq V 14%nat | reg_eq V 15%nat | reg_eq V 16%nat | reg_eq V 17%nat]. }
exact (reg_of _ _ _ i _ HS1 ltac:(decompose [or] C; subst i; lia) E). }
assert (MM : ms_mem ms3 = mem1) by (apply (frame_of_nowin E3 []); [constructor | exact HF]).
pose proof (st_ok_mkst src0segs _ _ _ HS1 Hrv) as SHAPE. rewrite Hpc, MM in SHAPE. clear V Hpc Hrv Hmem.
split; [exact SHAPE|]. split.
- change (1%bv : bv 5) with (nat_to_reg 1). rewrite G1. reflexivity.
- change (10%bv : bv 5) with (nat_to_reg 10). rewrite G10, (den_off0 xv3 XR3), X20. reflexivity.
- change (11%bv : bv 5) with (nat_to_reg 11). rewrite G11, (den_off0 xv3 XR3), X8. reflexivity.
- change (18%bv : bv 5) with (nat_to_reg 18). rewrite G18, (den_off0 xv3 XR3), X20. reflexivity.
- change (2%bv : bv 5) with (nat_to_reg 2). rewrite G2', (den_off0 xv3 XR3), X2. reflexivity.
- change (4%bv : bv 5) with (nat_to_reg 4). rewrite G4. reflexivity.
- change (8%bv : bv 5) with (nat_to_reg 8). rewrite G8', (den_off0 xv3 XR3), X8. reflexivity.
- change (9%bv : bv 5) with (nat_to_reg 9). rewrite G9. reflexivity.
- intros i Hi. rewrite (GS i Hi), (den_off0 xv3 XR3). unfold xv3. rewrite Z_to_bv_bv_unsigned. apply (pb_cs _ _ _ _ _ PBS). exact Hi.
Qed.
Section c.
Variable regs3 : bvmap 5 word.
Hypothesis AS3 : at_AS regs3.
Lemma sp3 : spZ regs3 = SP0 - 48.
Proof.
pose proof PRE_facts as (_ & _ & _ & _ & _ & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val).
unfold spZ. rewrite (as_2 _ AS3). apply lit64_small. unfold SP0 in *. lia.
Qed.
Lemma call_ok :
(st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs3) mem1) /\ callee_pre B regs3 mem1 AS_STACK.
Proof.
pose proof PRE_facts as (MX & _ & _ & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & Haux). pose proof (proj1 alloc_ceiling_val) as HCV.
rewrite sp3. split.
- intros Hid. apply (auxv_pre_mono B (ly_sec L) SP0); [lia|]. apply (auxv_pre_ext (ly_sec L) SP0 mem).
+ intros x Hx. apply mbyte_ext. apply (pa_out _ _ _ _ _ AT); unfold YN1p.SP0; unfold SP0 in Hx; lia.
+ intros x Hx. apply mbyte_ext. change (ms_libc B) with src0_D_libc in Hx. apply (pa_out _ _ _ _ _ AT); unfold YN1p.SP0; unfold src0_D_libc in Hx; lia.
+ exact (Haux Hid).
- unfold callee_pre, AS_STACK, ALLOC_STACK. rewrite sp3. split; [rewrite (as_1 _ AS3); apply YK0s.ret_ok_even; vm_compute; reflexivity|].
split; [unfold SP0 in *; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
split; [lia|]. split; [lia|]. split.
{ intros a Ha. apply (proj1 (writable_ext mem mem1 a (pa_out _ _ _ _ _ AT a ltac:(lia) ltac:(unfold YN1p.SP0; lia)))). apply Hstk. lia. }
split; [exact (as_4 _ AS3)|].
intros a Ha. pose proof (src0_img_range' a (errno_img' a Ha)).
apply (proj1 (writable_ext mem mem1 a (pa_out _ _ _ _ _ AT a ltac:(lia) ltac:(unfold YN1p.SP0; lia)))). apply Herr. exact Ha.
Qed.
Definition as_post (r : Z * astate) (c' : config) : Prop :=
(exists L' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs3 1) mem' rom) md' /\
midrep B L' (snd r) mem' md' /\ ama_ok (snd r) /\ bounded (snd r) /\ rsv_ok (snd r) /\ span_ok (snd r) /\ layout_le A L L' /\
regs_preserved regs3 regs' /\ (exists vm', md' = with_vmmaps vm' md) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ owned B L A x -> ~ owned B L' (snd r) x -> ~ in_nonmap_region L' (snd r) x ->
~ call_scratch B (spZ regs3) AS_STACK x -> mem' (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x)) /\
(forall a, call_scratch B (spZ regs3) AS_STACK a -> writable_at src0segs mem' a) /\
getr regs' 10 = Z_to_bv 64 (fst r) /\
(0 <= fst r -> forall g am, active_hd (snd r) scv = Some g -> MT (snd r) g = Some (MUsed am) -> stride_of am < class_size scv ->
forall i, 0 <= i < stride_of am - IB -> mbyte src0segs mem' (ptr_addr L' (slot_start am (fst r)) + i) = Some (Z_to_bv 8 0)))
/\ slot_post [] U0 A scv n r.
Lemma call_mreal :
mreal src0segs (mkCfg (mkst regs3 (Z_to_bv 64 ASLOT) mem1 rom) md) (alloc_slot NEST_FUEL scv n A) as_post.
Proof.
pose proof PRE_facts as (MX & HW & HB & _). pose proof SCR as [R F]. destruct call_ok as [AUX CP].
apply mreal_itok.
- pose proof (ASH L A regs3 mem1 md scv n HI (MRx_ama _ _ _ _ _ MX) HB (MRx_rsv _ _ _ _ _ MX) (MRx_span _ _ _ _ _ MX) R Hn F MID1 AUX CP (as_10 _ AS3) (as_11 _ AS3)) as M.
rewrite B_segs in M. exact M.
- destruct (alloc_mutual NEST_FUEL) as [AS _]. apply (AS [] U0 A scv n); [exact HI | exact R | lia | exact F | apply need_le_fuel; lia | intros r Hr; exact Hr].
Qed.
Section d.
Variables (idx : Z) (s2 : astate) (L' : layout) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model).
Hypothesis MID2 : midrep B L' s2 mem' md'.
Hypothesis HA2 : ama_ok s2.
Hypothesis HB2 : bounded s2.
Hypothesis HR2 : rsv_ok s2.
Hypothesis HS2 : span_ok s2.
Hypothesis LE : layout_le A L L'.
Hypothesis RP : regs_preserved regs3 regs'.
Hypothesis VM : exists vm', md' = with_vmmaps vm' md.
Hypothesis FR : forall x, 0 <= x < 2 ^ 64 -> ~ owned B L A x -> ~ owned B L' s2 x -> ~ in_nonmap_region L' s2 x ->
~ call_scratch B (spZ regs3) AS_STACK x -> mem' (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x).
Hypothesis WS : forall a, call_scratch B (spZ regs3) AS_STACK a -> writable_at src0segs mem' a.
Hypothesis R10 : getr regs' 10 = Z_to_bv 64 idx.
Hypothesis UB : ub_same A s2.
Variables (Xr : option (sptr * Z)).
Hypothesis HI2 : Inv [] Xr U0 s2.
Lemma md'_facts : m_halted md' = None /\ m_vm_lazy md' = [] /\ m_vm_materialized md' = [].
Proof. exact (mid_md _ _ _ _ _ MID2). Qed.
Lemma owned2_low x : owned B L' s2 x -> 0 <= x < alloc_ceiling.
Proof.
pose proof (proj1 alloc_ceiling_val). intros [[Hfp _]|Hs].
- destruct Hfp as (e & He & Hxe).
pose proof (footprint_hi [] Xr U0 L' s2 md' HI2 (mid_syms _ _ _ _ _ MID2) (mid_ctx _ _ _ _ _ MID2) (mid_ledger _ _ _ _ _ MID2) e He).
pose proof (footprint_below [] Xr U0 L' s2 md' HI2 (mid_syms _ _ _ _ _ MID2) (mid_ctx _ _ _ _ _ MID2) (mid_ledger _ _ _ _ _ MID2) e x He Hxe). lia.
- pose proof (src0_img_range' x (so_statics_img _ (mid_syms _ _ _ _ _ MID2) x Hs)). lia.
Qed.
Lemma nonmap_guard x : alloc_ceiling <= x < 2 ^ 64 \/ in_img B x -> ~ in_nonmap_region L' s2 x.
Proof.
intros Hx [(r & rg & Hr & Hl & _ & Hxr) _]. destruct (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID2) r rg Hr Hl) as (_ & _ & Rc & Ri).
destruct Hx as [Hx|Hx]; [lia | exact (Ri x Hxr Hx)].
Qed.
Lemma frame_same x : alloc_ceiling <= x < 2 ^ 64 \/ in_img B x -> ~ owned B L A x -> ~ owned B L' s2 x -> ~ scratch B regs x ->
mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Proof.
intros Hx NO NO2 NS. pose proof (proj1 alloc_ceiling_val) as HCV.
assert (Hx64 : 0 <= x < 2 ^ 64) by (destruct Hx as [Hx'|Hx']; [lia | pose proof (src0_img_range' x Hx'); lia]).
rewrite (FR x Hx64 NO NO2 (nonmap_guard x Hx)).
- apply (pa_out _ _ _ _ _ AT x Hx64). unfold scratch, ALLOC_STACK in NS. unfold YN1p.SP0. intros W. apply NS. left. lia.
- unfold call_scratch, AS_STACK, ALLOC_STACK. rewrite sp3. unfold scratch, ALLOC_STACK in NS. intros W. apply NS. destruct W as [W|W]; [left; lia | right; exact W].
Qed.
Lemma frame_bytes x : SP0 - 48 <= x < SP0 -> mem' (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x).
Proof.
intros Hx. pose proof PRE_facts as (MX & _ & _ & _ & _ & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
apply FR; [lia | | | apply nonmap_guard; lia |].
- intros Ho. pose proof (mr_owned_low _ _ (MRx_laws B) L A mem md x MX Ho). lia.
- intros Ho. pose proof (owned2_low x Ho). lia.
- unfold call_scratch, AS_STACK, ALLOC_STACK. rewrite sp3. intros [W|W]; [lia|]. pose proof (src0_img_range' x (errno_img' x W)). lia.
Qed.
Lemma frame_kept off r : In (off, r) FRAME_SLOTS -> bytes_are mem' (SP0 - 48 + off) 8 (bv_unsigned (getr regs (nat_to_reg r))).
Proof.
intros Hin. assert (Hoff : 0 <= off <= 40).
{ unfold FRAME_SLOTS in Hin. cbn in Hin. decompose [or] Hin; try contradiction; match goal with H : (_, _) = (off, r) |- _ => injection H as <- <- end; lia. }
apply (bytes_are_ext mem1); [| exact (pa_frame _ _ _ _ _ AT off r Hin)]. intros i Hi. apply frame_bytes. unfold YN1p.SP0. lia.
Qed.
Lemma scratch_writable a : scratch B regs a -> writable_at src0segs mem' a.
Proof.
intros Hs. pose proof PRE_facts as (MX & _ & _ & _ & _ & Hceil & Hsp63 & Hstk & _ & Herr & _). pose proof (proj1 alloc_ceiling_val) as HCV.
destruct (Z_le_dec (SP0 - 48) a) as [L1|L1]; [destruct (Z_lt_dec a SP0) as [L2|L2]|].
- apply (proj1 (writable_ext mem1 mem' a (frame_bytes a ltac:(lia)))). apply (pa_win _ _ _ _ _ AT). unfold YN1p.SP0. lia.
- apply WS. unfold call_scratch, AS_STACK, ALLOC_STACK. rewrite sp3. unfold scratch, ALLOC_STACK in Hs. destruct Hs as [Hs|Hs]; [lia | right; exact Hs].
- apply WS. unfold call_scratch, AS_STACK, ALLOC_STACK. rewrite sp3. unfold scratch, ALLOC_STACK in Hs. destruct Hs as [Hs|Hs]; [left; lia | right; exact Hs].
Qed.
Lemma regs'_facts : getr regs' 2 = Z_to_bv 64 (SP0 - 48) /\ getr regs' 4 = Z_to_bv 64 TP /\ getr regs' 8 = Z_to_bv 64 n /\
getr regs' 9 = Z_to_bv 64 LOCK /\ getr regs' 18 = Z_to_bv 64 scv /\ (forall i, In i CSAVED -> getr regs' (nat_to_reg i) = getr regs (nat_to_reg i)).
Proof.
assert (P : forall k : nat, (k <= 31)%nat -> callee_saved (Z.of_nat k) -> getr regs' (nat_to_reg k) = getr regs3 (nat_to_reg k)).
{ intros k Hk Hc. pose proof (RP (Z.of_nat k) Hc) as E.
replace (Z_to_bv 5 (Z.of_nat k)) with (nat_to_reg k) in E; [exact E|].
apply bv_eq. rewrite nat_to_reg_unsigned, Z_to_bv_unsigned by exact Hk. symmetry. apply bv_wrap_small. change (bv_modulus 5) with 32. lia. }
split; [change (2%bv : bv 5) with (nat_to_reg 2); rewrite (P 2%nat ltac:(lia) ltac:(unfold callee_saved; lia)); exact (as_2 _ AS3)|].
split; [change (4%bv : bv 5) with (nat_to_reg 4); rewrite (P 4%nat ltac:(lia) ltac:(unfold callee_saved; lia)); exact (as_4 _ AS3)|].
split; [change (8%bv : bv 5) with (nat_to_reg 8); rewrite (P 8%nat ltac:(lia) ltac:(unfold callee_saved; lia)); exact (as_8 _ AS3)|].
split; [change (9%bv : bv 5) with (nat_to_reg 9); rewrite (P 9%nat ltac:(lia) ltac:(unfold callee_saved; lia)); exact (as_9 _ AS3)|].
split; [change (18%bv : bv 5) with (nat_to_reg 18); rewrite (P 18%nat ltac:(lia) ltac:(unfold callee_saved; lia)); exact (as_18 _ AS3)|].
intros i Hi. pose proof (csaved_cases i Hi) as C.
rewrite <- (as_cs _ AS3 i Hi). apply P; [decompose [or] C; subst i; lia | unfold callee_saved; decompose [or] C; subst i; cbn; lia].
Qed.
Let POSTQ := fun (r : option sptr * astate) (c' : config) => malloc_post [] U0 A n r -> malloc_leaf B (MRx B) L A regs mem md n r c'.
Section f.
Hypothesis Hm1 : idx = -1.
Definition xvF (i : nat) : Z :=
if (i <? 32)%nat then bv_unsigned (getr regs' (nat_to_reg i))
else match i with
| 34%nat => bv_unsigned (getr regs 20) | 35%nat => bv_unsigned (getr regs 19) | 36%nat => bv_unsigned (getr regs 18)
| 37%nat => bv_unsigned (getr regs 9) | 38%nat => bv_unsigned (getr regs 8) | 39%nat => bv_unsigned (getr regs 1)
| _ => 0 end.
Lemma XRF : forall k, 0 <= xvF k < 2 ^ 64.
Proof. intros k. unfold xvF. destruct (k <? 32)%nat; [apply u64_range|]. do 40 (destruct k as [|k]; [lia || apply u64_range|]). lia. Qed.
Lemma xvF_reg k : (k <= 31)%nat -> xvF k = bv_unsigned (getr regs' (nat_to_reg k)).
Proof. intros Hk. unfold xvF. replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. Qed.
Lemma T4f_st_ok : st_ok src0segs (EV xvF) ss_T4f (mkst regs' (Z_to_bv 64 RA_AS) mem' rom).
Proof.
pose proof PRE_facts as (_ & _ & _ & _ & Hal & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof regs'_facts as (Q2 & Q4 & Q8 & Q9 & Q18 & QCS).
assert (XSP : xvF 2%nat = SP0 - 48) by (rewrite xvF_reg by lia; change (nat_to_reg 2) with (2%bv : bv 5); rewrite Q2; apply lit64_small; unfold SP0 in *; lia).
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_T4f resv_denot].
repeat (split; [reflexivity|]). split; [|split].
- apply regs_ok_lit. intros k Hk.
destruct (Nat.eq_dec k 10) as [->|Hk10]; [cbn; change (nat_to_reg 10) with (10%bv : bv 5); rewrite R10, Hm1; reflexivity|].
destruct (Nat.eq_dec k 9) as [->|Hk9]; [cbn; exact Q9|].
destruct (Nat.eq_dec k 4) as [->|Hk4]; [cbn; exact Q4|].
replace (find (fun p : nat * Z => Nat.eqb (fst p) k) [(10%nat, -1); (9%nat, LOCK); (4%nat, TP)]) with (@None (nat * Z)).
2:{ cbn [find fst]. rewrite !(proj2 (Nat.eqb_neq _ _)) by lia. reflexivity. }
rewrite xvF_reg by lia. symmetry. apply Z_to_bv_bv_unsigned.
- split; [vm_compute; reflexivity|]. split.
+ unfold t4f_mem. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
* apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_frame]; rewrite (base_val_EV xvF XRF); unfold aSP; rewrite XSP; [lia | lia | intros; lia |].
repeat apply Forall_cons; [| | | | | | apply Forall_nil];
(eapply (chunk_ok_val xvF _ _ _ 8); [apply (U_off0 xvF XRF) | apply XRF |]);
[ exact (frame_kept 0 20%nat ltac:(cbn; auto 10)) | exact (frame_kept 8 19%nat ltac:(cbn; auto 10)) | exact (frame_kept 16 18%nat ltac:(cbn; auto 10))
| exact (frame_kept 24 9%nat ltac:(cbn; auto 10)) | exact (frame_kept 32 8%nat ltac:(cbn; auto 10)) | exact (frame_kept 40 1%nat ltac:(cbn; auto 10)) ].
* apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_lock base_val]; unfold LOCK, src0_D_malloc_lock; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_lit0. intros k Hk. rewrite Z.add_0_l.
apply (st_lock _ _ (mid_statics _ _ _ _ _ MID2)). exact Hk.
+ cbn [pairwise_disjoint all_disjoint t4f_mem]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_frame R_lock]. rewrite (base_val_EV xvF XRF). unfold aSP. rewrite XSP.
cbn [base_val]. unfold LOCK, src0_D_malloc_lock. repeat split; try exact I. lia.
- split; [|split; exact I]. cbn [atoms_ok t4f_facts f_atoms]. split; [|exact I].
unfold afact_ok. cbn [af_lo af_hi af_al2 F_sp48]. rewrite (ew_EV xvF XRF), XSP. unfold CEIL. change (2 ^ 4) with 16.
split; [lia|]. split; [|lia]. unfold SP0 in *. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
Qed.
Record at_FRET (rg : bvmap 5 word) : Prop := FR_ {
fr_2 : getr rg 2 = Z_to_bv 64 SP0; fr_4 : getr rg 4 = Z_to_bv 64 TP; fr_8 : getr rg 8 = getr regs 8; fr_9 : getr rg 9 = getr regs 9;
fr_10 : getr rg 10 = Z_to_bv 64 0; fr_18 : getr rg 18 = getr regs 18; fr_19 : getr rg 19 = getr regs 19; fr_20 : getr rg 20 = getr regs 20;
fr_cs : forall i, In i CSAVED -> getr rg (nat_to_reg i) = getr regs (nat_to_reg i) }.
Lemma T4f_post ms5 : st_ok src0segs (EV xvF) SST4f ms5 -> frame_of (EV xvF) t4f_mem mem' (ms_mem ms5) ->
ms_mem ms5 = mem' /\ at_FRET (ms_regs ms5).
Proof.
intros HS1 HF. pose proof SST4f_view as V. destruct (cview_regs _ _ _ _ _ _ V) as (Hpc & Hrv & Hmem & _).
pose proof PRE_facts as (_ & _ & _ & _ & Hal & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof regs'_facts as (Q2 & Q4 & Q8 & Q9 & Q18 & QCS).
assert (XSP : xvF 2%nat = SP0 - 48) by (rewrite xvF_reg by lia; change (nat_to_reg 2) with (2%bv : bv 5); rewrite Q2; apply lit64_small; unfold SP0 in *; lia).
pose proof (reg_of _ _ _ 2 _ HS1 ltac:(lia) ltac:(reg_eq V 1%nat)) as G2'.
pose proof (reg_of _ _ _ 4 _ HS1 ltac:(lia) ltac:(reg_eq V 2%nat)) as G4.
pose proof (reg_of _ _ _ 8 _ HS1 ltac:(lia) ltac:(reg_eq V 3%nat)) as G8'.
pose proof (reg_of _ _ _ 9 _ HS1 ltac:(lia) ltac:(reg_eq V 4%nat)) as G9.
pose proof (reg_of _ _ _ 10 _ HS1 ltac:(lia) ltac:(reg_eq V 5%nat)) as G10.
pose proof (reg_of _ _ _ 18 _ HS1 ltac:(lia) ltac:(reg_eq V 6%nat)) as G18.
pose proof (reg_of _ _ _ 19 _ HS1 ltac:(lia) ltac:(reg_eq V 7%nat)) as G19.
pose proof (reg_of _ _ _ 20 _ HS1 ltac:(lia) ltac:(reg_eq V 8%nat)) as G20.
assert (GS : forall i, In i CSAVED -> getr (ms_regs ms5) (nat_to_reg i) = sv_denot (EV xvF) (SOff i 0)).
{ intros i Hi. pose proof (csaved_cases i Hi) as C.
assert (E : nth i (ss_regs SST4f) (SLit 0) = SOff i 0).
{ decompose [or] C; subst i; [reg_eq V 9%nat | reg_eq V 10%nat | reg_eq V 11%nat | reg_eq V 12%nat | reg_eq V 13%nat | reg_eq V 14%nat | reg_eq V 15%nat | reg_eq V 16%nat]. }
exact (reg_of _ _ _ i _ HS1 ltac:(decompose [or] C; subst i; lia) E). }
assert (MM : ms_mem ms5 = mem') by (apply (frame_of_nowin (EV xvF) t4f_mem); [repeat constructor | exact HF]).
clear V Hpc Hrv Hmem. split; [exact MM|]. split.
- change (2%bv : bv 5) with (nat_to_reg 2). rewrite G2', (den_off xvF XRF) by (rewrite XSP; lia). rewrite XSP. f_equal. lia.
- change (4%bv : bv 5) with (nat_to_reg 4). rewrite G4. reflexivity.
- change (8%bv : bv 5) with (nat_to_reg 8). rewrite G8', (den_off0 xvF XRF). apply Z_to_bv_bv_unsigned.
- change (9%bv : bv 5) with (nat_to_reg 9). rewrite G9, (den_off0 xvF XRF). apply Z_to_bv_bv_unsigned.
- change (10%bv : bv 5) with (nat_to_reg 10). rewrite G10. reflexivity.
- change (18%bv : bv 5) with (nat_to_reg 18). rewrite G18, (den_off0 xvF XRF). apply Z_to_bv_bv_unsigned.
- change (19%bv : bv 5) with (nat_to_reg 19). rewrite G19, (den_off0 xvF XRF). apply Z_to_bv_bv_unsigned.
- change (20%bv : bv 5) with (nat_to_reg 20). rewrite G20, (den_off0 xvF XRF). apply Z_to_bv_bv_unsigned.
- intros i Hi. rewrite (GS i Hi), (den_off0 xvF XRF), xvF_reg by (pose proof (csaved_cases i Hi); lia). rewrite Z_to_bv_bv_unsigned. apply QCS. exact Hi.
Qed.
Lemma fail_leaf rg : at_FRET rg -> malloc_post [] U0 A n (None, s2) ->
malloc_leaf B (MRx B) L A regs mem md n (None, s2) (mkCfg (mkst rg (getr regs 1) mem' rom) md').
Proof.
intros FRT [HW2 _]. cbn [fst snd] in HW2.
pose proof PRE_facts as (MX & HW & HB & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & _). pose proof (proj1 alloc_ceiling_val) as HCV.
assert (MX2 : MRx B L' s2 mem' md') by (apply midrep_MRx; assumption).
assert (UBe : user_blocks s2 = user_blocks A) by (apply ub_same_user_blocks; [exact (proj1 (inv_keys HI)) | exact (proj1 (inv_keys HW2)) | exact UB]).
assert (EP : forall p k, In (p, k) (user_blocks A) -> ptr_addr L' p = ptr_addr L p).
{ intros p k Hin. destruct (block_region A p k HW Hin) as (kk & o & rg' & -> & Hr' & _). unfold ptr_addr. cbn [loc_addr].
destruct LE as (_ & _ & _ & LR). rewrite (LR kk (region_of_lt A kk rg' Hr')). reflexivity. }
exists L', rg, mem', md'. split; [reflexivity|]. split.
- unfold call_post. change (ms_segs B) with src0segs.
split; [exact MX2|]. split; [exact HW2|]. split; [exact HB2|]. split; [exact LE|]. split; [intros p k Hin _; exact (EP p k Hin)|].
split.
{ intros r Hcr. unfold callee_saved in Hcr.
assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hcr. decompose [or] C; subst r;
first [ exact (eq_trans (fr_2 _ FRT) (Z_to_bv_bv_unsigned 64 (getr regs 2%bv)))
| exact (eq_trans (fr_4 _ FRT) (eq_sym Htp)) | exact (fr_8 _ FRT) | exact (fr_9 _ FRT) | exact (fr_18 _ FRT) | exact (fr_19 _ FRT) | exact (fr_20 _ FRT)
| exact (fr_cs _ FRT 3%nat ltac:(cbn; auto 10))
| exact (fr_cs _ FRT 21%nat ltac:(cbn; auto 10)) | exact (fr_cs _ FRT 22%nat ltac:(cbn; auto 10)) | exact (fr_cs _ FRT 23%nat ltac:(cbn; auto 10))
| exact (fr_cs _ FRT 24%nat ltac:(cbn; auto 10)) | exact (fr_cs _ FRT 25%nat ltac:(cbn; auto 10)) | exact (fr_cs _ FRT 26%nat ltac:(cbn; auto 10)) | exact (fr_cs _ FRT 27%nat ltac:(cbn; auto 10)) ]. }
split; [exact VM|].
split.
{ intros a Hg HnA HnA2 Hns _. pose proof (frame_same a Hg HnA HnA2 Hns) as E. unfold mbyte, writable_at, wview. rewrite E. tauto. }
split.
{ intros p k i Hin Hin2 Hi.
pose proof (mr_blocks _ _ (MRx_laws B) L A mem md p k i MX Hin Hi) as (Pp & Plo & Phi & Pno).
assert (NIMG : ~ in_img B (ptr_addr L p + i)).
{ destruct (block_region A p k HW Hin) as (kk & o & rg' & Ep & Hr' & _ & Hl' & Ho' & Hk' & Hlen' & _).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)) kk rg' Hr' Hl') as (_ & _ & _ & Himg).
apply Himg. rewrite Ep. unfold ptr_addr. cbn [loc_addr]. lia. }
apply mbyte_ext. rewrite (FR (ptr_addr L p + i) ltac:(lia) Pno).
- apply (pa_out _ _ _ _ _ AT); [lia|]. unfold YN1p.SP0. lia.
- intros [[_ Hnb] | Hs].
+ apply Hnb. exists (p, k). split; [exact Hin2|]. cbn [fst snd]. change (loc_addr L' (LMem p)) with (ptr_addr L' p). rewrite (EP p k Hin). lia.
+ apply NIMG. apply (so_statics_img _ (mid_syms _ _ _ _ _ MID2)). exact Hs.
- intros [_ NM]. apply NM. destruct (block_region s2 p k HW2 Hin2) as (kk & o & rg' & Ep & Hr' & Hk' & Hl' & Ho' & Hn' & Hlen' & _).
exists kk, rg'. split; [exact Hr'|]. split; [exact Hl'|]. split; [exact Hk'|]. rewrite <- (EP p k Hin). rewrite Ep. unfold ptr_addr. cbn [loc_addr]. lia.
- unfold call_scratch, AS_STACK, ALLOC_STACK. rewrite sp3. intros [W|W]; [lia|]. apply NIMG. apply errno_img'. exact W. }
exact scratch_writable.
- cbn [fst snd]. split; [exact (fr_10 _ FRT) | exact UBe].
Qed.
Theorem fail_tail : mreal src0segs (mkCfg (mkst regs' (Z_to_bv 64 RA_AS) mem' rom) md') (IRet (None, s2)) POSTQ.
Proof.
pose proof PRE_facts as (MX & _ & _ & Hret & _). destruct md'_facts as (Hh & Hlz & _).
cbn [mreal]. eapply SR_bind; [eapply (T4f_run (EV xvF)); [exact T4f_st_ok | exact Hh | exact Hlz]|].
intros c' (ms5 & -> & HS5 & HF). cbn [ms_mem mkst] in HF. destruct (T4f_post ms5 HS5 HF) as [MM FRT].
eapply (SR_fret (EV xvF) SST4f ms5 md' aRA); [exact HS5 | reflexivity | reflexivity | vm_compute; reflexivity | | exact Hh | exact Hlz |].
- cbn [ew EV]. unfold xvF, aRA. cbn. rewrite Z_to_bv_bv_unsigned. exact Hret.
- cbn [ew EV]. unfold xvF at 1. unfold aRA. cbn. rewrite Z_to_bv_bv_unsigned, MM. unfold POSTQ. intros MP. exact (fail_leaf (ms_regs ms5) FRT MP).
Qed.
End f.
Section Ok.
Variables (g : sptr) (am : ameta).
Hypothesis HIo : Inv [] (Some (g, idx)) U0 s2.
Hypothesis Hhd2 : active_hd s2 scv = Some g.
Hypothesis Hu2 : usedX [] s2 g am.
Hypothesis Hsc2 : am_sc am = scv.
Hypothesis Hfit2 : n + IB <= stride_of am.
Hypothesis Hidx : 0 <= idx <= am_last am.
Hypothesis ZR : forall g' am', active_hd s2 scv = Some g' -> MT s2 g' = Some (MUsed am') -> stride_of am' < class_size scv ->
forall i, 0 <= i < stride_of am' - IB -> mbyte src0segs mem' (ptr_addr L' (slot_start am' idx) + i) = Some (Z_to_bv 8 0).
Definition G' : Z := ptr_addr L' g.
Definition ACT' : Z := CTX + 80 + 8 * scv.
Lemma g_facts : 4096 <= G' /\ G' + 40 <= alloc_ceiling /\ G' mod 8 = 0 /\ (forall x, G' <= x < G' + 40 -> ~ in_img B x) /\ 0 <= am_last am <= 31.
Proof.
destruct (meta_facts [] (Some (g, idx)) U0 L' s2 md' HIo (mid_ledger _ _ _ _ _ MID2) g am Hu2) as (M1 & M2 & M3 & M4 & _).
pose proof (inv_groups HIo g am Hu2) as ((Glast & _) & _). unfold G'. repeat (split; [assumption|]). exact Glast.
Qed.
Definition xvO (i : nat) : Z :=
if (i <? 32)%nat then bv_unsigned (getr regs' (nat_to_reg i)) else match i with 40%nat => ACT' | 41%nat => G' | _ => 0 end.
Lemma XRO : forall k, 0 <= xvO k < 2 ^ 64.
Proof.
intros k. pose proof g_facts as (G1 & G2 & _). pose proof SCR as [R _]. pose proof (proj1 alloc_ceiling_val).
unfold xvO. destruct (k <? 32)%nat; [apply u64_range|]. unfold ACT'. pose proof statics_facts. do 42 (destruct k as [|k]; [lia|]). lia.
Qed.
Lemma xvO_reg k : (k <= 31)%nat -> xvO k = bv_unsigned (getr regs' (nat_to_reg k)).
Proof. intros Hk. unfold xvO. replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. Qed.
Lemma T4ok_st_ok : st_ok src0segs (EV xvO) ss_T4ok (mkst regs' (Z_to_bv 64 RA_AS) mem' rom).
Proof.
pose proof PRE_facts as (_ & _ & _ & _ & Hal & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof SCR as [R _].
pose proof regs'_facts as (Q2 & Q4 & Q8 & Q9 & Q18 & QCS). pose proof g_facts as (G1 & G2 & G8 & Gimg & Glast).
assert (XSP : xvO 2%nat = SP0 - 48) by (rewrite xvO_reg by lia; change (nat_to_reg 2) with (2%bv : bv 5); rewrite Q2; apply lit64_small; unfold SP0 in *; lia).
assert (X18 : xvO 18%nat = scv) by (rewrite xvO_reg by lia; change (nat_to_reg 18) with (18%bv : bv 5); rewrite Q18; apply lit64_small; lia).
assert (X10 : xvO 10%nat = idx) by (rewrite xvO_reg by lia; change (nat_to_reg 10) with (10%bv : bv 5); rewrite R10; apply lit64_small; lia).
pose proof (proj2 (memrepX_nil B L' s2 mem') (mid_mem _ _ _ _ _ MID2)) as MR2.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_T4ok resv_denot].
repeat (split; [reflexivity|]). split; [|split].
- apply regs_ok_lit. intros k Hk.
destruct (Nat.eq_dec k 9) as [->|Hk9]; [cbn; exact Q9|].
destruct (Nat.eq_dec k 4) as [->|Hk4]; [cbn; exact Q4|].
replace (find (fun p : nat * Z => Nat.eqb (fst p) k) [(9%nat, LOCK); (4%nat, TP)]) with (@None (nat * Z)).
2:{ cbn [find fst]. rewrite !(proj2 (Nat.eqb_neq _ _)) by lia. reflexivity. }
rewrite xvO_reg by lia. symmetry. apply Z_to_bv_bv_unsigned.
- split; [vm_compute; reflexivity|]. split; [| cbn [pairwise_disjoint all_disjoint]; exact (conj I I)].
apply Forall_cons; [|apply Forall_nil].
pose proof statics_facts as STF. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_act4]; rewrite (base_val_EV xvO XRO); change (xvO aACT) with ACT'; [unfold ACT'; lia | unfold ACT'; lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val xvO _ _ _ 8); [apply (U_off0 xvO XRO) | apply XRO |]. change (xvO aG) with G'.
pose proof (ctx_active_cell [] L' s2 mem' (mid_ctx _ _ _ _ _ MID2) MR2 (Z.to_nat scv) ltac:(lia)) as C. rewrite Z2Nat.id in C by lia.
unfold active_hd in Hhd2. rewrite Hhd2 in C. cbn [optrZ] in C. rewrite Z.add_0_r. unfold ACT', G'. exact C.
- split; [|split; [exact I|]].
+ cbn [atoms_ok t4ok_facts f_atoms]. unfold afact_ok; cbn [af_lo af_hi af_al2 F_sp48]; rewrite !(ew_EV xvO XRO), X10, X18, XSP.
change (xvO aACT) with ACT'. change (xvO aG) with G'. unfold ACT', CEIL. pose proof statics_facts as (ST1 & ST2 & ST3 & ST8).
change (2 ^ 0) with 1. change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
repeat split; try lia.
* unfold SP0 in *. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
* rewrite Z.mul_comm, Z_mod_plus_full. exact ST8.
+ cbn [alias_ok t4ok_facts f_alias AL4]. split; [|exact I].
rewrite !UZ_sound. f_equal. cbn [UZ]. rewrite X18. change (xvO aACT) with ACT'. unfold zalu64, ACT'. cbn [zalu_raw].
pose proof statics_facts. rewrite ?Z.add_0_r, !(zcanon_id scv), !(zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite (zcanon_id (CTX + 80 + 8 * scv)) by (unfold M64; lia).
rewrite !zcanon_id by (unfold M64; lia). lia.
Qed.
Record at_PC' (rg : bvmap 5 word) : Prop := PC'_ {
po_18 : getr rg 18 = Z_to_bv 64 G'; po_19 : getr rg 19 = Z_to_bv 64 idx; po_8 : getr rg 8 = Z_to_bv 64 n; po_9 : getr rg 9 = Z_to_bv 64 LOCK;
po_2 : getr rg 2 = Z_to_bv 64 (SP0 - 48); po_4 : getr rg 4 = Z_to_bv 64 TP;
po_cs : forall i, In i CSAVED -> getr rg (nat_to_reg i) = getr regs (nat_to_reg i) }.
Lemma T4ok_post ms5 : st_ok src0segs (EV xvO) SST4ok ms5 -> frame_of (EV xvO) [R_act4] mem' (ms_mem ms5) ->
ms5 = mkst (ms_regs ms5) (Z_to_bv 64 PC) mem' rom /\ at_PC' (ms_regs ms5).
Proof.
intros HS1 HF. pose proof SST4ok_view as V. destruct (cview_regs _ _ _ _ _ _ V) as (Hpc & Hrv & Hmem & _).
pose proof PRE_facts as (_ & _ & _ & _ & Hal & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof regs'_facts as (Q2 & Q4 & Q8 & Q9 & Q18 & QCS). pose proof g_facts as (_ & _ & _ & _ & Glast).
pose proof (reg_of _ _ _ 18 _ HS1 ltac:(lia) ltac:(reg_eq V 0%nat)) as G18.
pose proof (reg_of _ _ _ 19 _ HS1 ltac:(lia) ltac:(reg_eq V 1%nat)) as G19.
pose proof (reg_of _ _ _ 2 _ HS1 ltac:(lia) ltac:(reg_eq V 2%nat)) as G2'.
pose proof (reg_of _ _ _ 4 _ HS1 ltac:(lia) ltac:(reg_eq V 3%nat)) as G4.
pose proof (reg_of _ _ _ 8 _ HS1 ltac:(lia) ltac:(reg_eq V 4%nat)) as G8'.
pose proof (reg_of _ _ _ 9 _ HS1 ltac:(lia) ltac:(reg_eq V 5%nat)) as G9.
assert (GS : forall i, In i CSAVED -> getr (ms_regs ms5) (nat_to_reg i) = sv_denot (EV xvO) (SOff i 0)).
{ intros i Hi. pose proof (csaved_cases i Hi) as C.
assert (E : nth i (ss_regs SST4ok) (SLit 0) = SOff i 0).
{ decompose [or] C; subst i; [reg_eq V 6%nat | reg_eq V 7%nat | reg_eq V 8%nat | reg_eq V 9%nat | reg_eq V 10%nat | reg_eq V 11%nat | reg_eq V 12%nat | reg_eq V 13%nat]. }
exact (reg_of _ _ _ i _ HS1 ltac:(decompose [or] C; subst i; lia) E). }
assert (MM : ms_mem ms5 = mem') by (apply (frame_of_nowin (EV xvO) [R_act4]); [repeat constructor | exact HF]).
pose proof (st_ok_mkst src0segs _ _ _ HS1 Hrv) as SHAPE. rewrite Hpc, MM in SHAPE. clear V Hpc Hrv Hmem.
split; [exact SHAPE|]. split.
- change (18%bv : bv 5) with (nat_to_reg 18). rewrite G18, (den_off0 xvO XRO). reflexivity.
- change (19%bv : bv 5) with (nat_to_reg 19). rewrite G19, (den_off0 xvO XRO), xvO_reg by lia. change (nat_to_reg 10) with (10%bv : bv 5). rewrite R10, lit64_small by lia. reflexivity.
- change (8%bv : bv 5) with (nat_to_reg 8). rewrite G8', (den_off0 xvO XRO), xvO_reg by lia. rewrite Z_to_bv_bv_unsigned. exact Q8.
- change (9%bv : bv 5) with (nat_to_reg 9). rewrite G9. reflexivity.
- change (2%bv : bv 5) with (nat_to_reg 2). rewrite G2', (den_off0 xvO XRO), xvO_reg by lia. rewrite Z_to_bv_bv_unsigned. exact Q2.
- change (4%bv : bv 5) with (nat_to_reg 4). rewrite G4. reflexivity.
- intros i Hi. rewrite (GS i Hi), (den_off0 xvO XRO), xvO_reg by (pose proof (csaved_cases i Hi); lia). rewrite Z_to_bv_bv_unsigned. apply QCS. exact Hi.
Qed.
Theorem ok_tail :
mreal src0segs (mkCfg (mkst regs' (Z_to_bv 64 RA_AS) mem' rom) md')
(ibind (enframe g idx n (st_mmap_counter s2) FUser s2) (fun ps => IRet (Some (fst ps), snd ps))) POSTQ.
Proof.
pose proof PRE_facts as (MX & _ & _ & Hret & _). destruct md'_facts as (Hh & Hlz & _). pose proof SCR as [R _].
eapply mreal_SR_pre; [eapply (T4ok_run (EV xvO)); [exact T4ok_st_ok | exact Hh | exact Hlz]|].
intros c' (ms5 & -> & HS5 & HF). cbn [ms_mem mkst] in HF. destruct (T4ok_post ms5 HS5 HF) as [SHAPE PCS]. rewrite SHAPE.
change (st_mmap_counter s2) with (ctr s2). unfold POSTQ.
apply (succ_tail L A regs mem md n PRE Hn L' s2 mem' md' g am idx scv (ms_regs ms5) MID2 HIo Hu2 (conj Hsc2 R) Hfit2 Hidx HB2 HA2 HR2 HS2 LE VM UB
(po_18 _ PCS) (po_19 _ PCS) (po_8 _ PCS) (po_9 _ PCS)).
- unfold SPv. exact (po_2 _ PCS).
- exact (po_4 _ PCS).
- exact (po_cs _ PCS).
- unfold SPv. exact frame_kept.
- intros x Hx NO NO2 NNM NS. rewrite (FR x Hx NO NO2 NNM).
+ apply (pa_out _ _ _ _ _ AT x Hx). unfold scratch, ALLOC_STACK in NS. unfold YN1p.SP0. intros W. apply NS. left. lia.
+ unfold call_scratch, AS_STACK, ALLOC_STACK. rewrite sp3. unfold scratch, ALLOC_STACK in NS. intros W. apply NS. destruct W as [W|W]; [left; lia | right; exact W].
- exact scratch_writable.
- intros US i Hi. exact (ZR g am Hhd2 (proj1 (usedX_MT _ _ _ _ Hu2)) US i Hi).
Qed.
End Ok.
End d.
End c.
Theorem slow_path :
mreal src0segs (mkCfg (mkst regs2 (Z_to_bv 64 PB) mem1 rom) md)
(ibind (alloc_slot NEST_FUEL scv n A) (slow_k n scv))
(fun r c' => malloc_post [] U0 A n r -> malloc_leaf B (MRx B) L A regs mem md n r c').
Proof.
pose proof PRE_facts as (MX & _). destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)) as (Hh & Hlz & _).
eapply mreal_SR_pre; [eapply (T2c_run E3); [exact T2c_st_ok | exact Hh | exact Hlz]|].
intros c' (ms3 & -> & HS3 & HF). cbn [ms_mem mkst] in HF. destruct (T2c_post ms3 HS3 HF) as [SHAPE AS3]. rewrite SHAPE.
eapply mreal_ibind; [apply (call_mreal (ms_regs ms3) AS3)|].
intros [idx s2] c'' [(L' & regs' & mem' & md' & -> & MID2 & HA2 & HB2 & HR2 & HS2 & LE & RP & VM & FR & WS & R10 & ZR) SP]. cbn [fst snd] in *.
rewrite (as_1 _ AS3). unfold slot_post in SP. cbn [fst snd] in SP.
destruct SP as (_ & UB & [[Hm1 HI2] | (Hidx0 & g & am & HI2 & Hhd2 & Hu2 & Hsc2 & Hfit2 & Hlast)]).
- unfold slow_k. replace (idx <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
exact (fail_tail (ms_regs ms3) AS3 idx s2 L' regs' mem' md' MID2 HA2 HB2 HR2 HS2 LE RP VM FR WS R10 UB None HI2 Hm1).
- unfold slow_k. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Hhd2.
exact (ok_tail (ms_regs ms3) AS3 idx s2 L' regs' mem' md' MID2 HA2 HB2 HR2 HS2 LE RP VM FR WS R10 UB (Some (g, idx)) HI2
g am HI2 Hhd2 Hu2 Hsc2 Hfit2 (conj Hidx0 Hlast) (ZR Hidx0)).
Qed.
End T4.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
