(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0a YO0b YO0c YO0g YO0w YO0s YO0q
YO0x YO0y YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YM06 YK0s YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN2b YN25 YN0b YN07 YN0a
YN0k YN2u YN0p YN1z YN21 YN1y YN2z YN1p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma statics_facts : 0x10000 <= NLK /\ NLK + 1 <= CTX /\ CTX + 928 <= 0x51000 /\ (CTX + 80) mod 8 = 0.
Proof. unfold NLK, CTX, src0_D_libc, src0_D_malloc_context. repeat split; reflexivity || lia. Qed.
Section T1.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (n : Z).
Hypothesis PRE : call_pre B (MRx B) L A regs mem md.
Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
Variables (regs1 : bvmap 5 word) (mem1 : word -> option byte).
Hypothesis AT : at_PA regs mem n regs1 mem1.
Let rom := seg_rom src0segs.
Let SP0 : Z := spZ regs.
Definition sc0 : Z := size_to_class n.
Definition g0 : option sptr := active_hd A sc0.
Definition h0 : option sptr := if sc0 <? 47 then active_hd A (sc0 + 1) else None.
Definition amo (o : option sptr) : option ameta :=
match o with Some g => match MT A g with Some (MUsed am) => Some am | _ => None end | None => None end.
Definition avail_of (o : option sptr) : Z := match amo o with Some am => am_avail am | None => 0 end.
Definition freed_of (o : option sptr) : Z := match amo o with Some am => am_freed am | None => 0 end.
Definition ACT : Z := CTX + 80 + 8 * sc0.
Definition sc : Z := msc A n.
Definition gaddr : Z := optrZ L (active_hd A sc).
Definition gmask : Z := sx32 (avail_of (active_hd A sc)).
Lemma PRE_facts : MRx B L A mem md /\ WF A /\ bounded A /\ YK0s.ret_ok (getr regs 1) /\
SP0 mod 16 = 0 /\ alloc_ceiling + 8192 <= SP0 /\ SP0 < 2 ^ 63 /\
(forall a, SP0 - 8192 <= a < SP0 -> writable_at src0segs mem a) /\ getr regs 4 = Z_to_bv 64 (ms_tp B) /\
(forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at src0segs mem a) /\
(st_init_done A = false -> auxv_pre B (ly_sec L) SP0 mem).
Proof. unfold call_pre, ALLOC_STACK in PRE. exact PRE. Qed.
Lemma HI : Inv [] None U0 A.
Proof. exact (proj1 (proj2 PRE_facts)). Qed.
Lemma sc0_range : 0 <= sc0 < 48 /\ n + IB <= class_size sc0.
Proof. exact (size_to_class_range n Hn). Qed.
Lemma MX1 : MRx B L A mem1 md.
Proof.
pose proof PRE_facts as (MX & _ & _ & _ & Hal & Hceil & _). pose proof (proj1 alloc_ceiling_val).
destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)) as (Hh & Hlz & Hmat).
assert (OWN : forall a, owned B L A a -> mem1 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ho. pose proof (mr_owned_low _ _ (MRx_laws B) L A mem md a MX Ho). apply (pa_out _ _ _ _ _ AT); unfold SP0, YN1p.SP0 in *; lia. }
apply (mr_frame _ _ (MRx_laws B) L A mem mem1 md md MX).
- intros a Ho. apply mbyte_ext. apply OWN. exact Ho.
- intros a Ho [b Hb]. exists b. rewrite (OWN a Ho). exact Hb.
- intros p k i Hin Hi. pose proof (mr_blocks _ _ (MRx_laws B) L A mem md p k i MX Hin Hi) as (Pp & Plo & Phi & _).
destruct Pp as [b Hb]. exists b. rewrite (pa_out _ _ _ _ _ AT); [exact Hb | lia | unfold YN1p.SP0; lia].
- reflexivity. - exact Hh. - exact Hlz. - exact Hmat.
Qed.
Lemma MID1 : midrep B L A mem1 md.
Proof. exact (MRx_midrep B L A mem1 md MX1). Qed.
Lemma MR1 : memrepX B [] L A mem1.
Proof. apply (proj2 (memrepX_nil B L A mem1)). exact (mid_mem _ _ _ _ _ MID1). Qed.
Lemma Hctx : ly_ctx L = YN0t.CTX.
Proof. exact (mid_ctx _ _ _ _ _ MID1). Qed.
Lemma head_am k g : 0 <= k < 48 -> active_hd A k = Some g -> exists am, usedX [] A g am /\ am_sc am = k /\ MT A g = Some (MUsed am).
Proof.
intros Hk Hg. destruct (head_used [] None U0 A k g HI Hk Hg) as (am & Hu & Hsc). exists am.
split; [exact Hu|]. split; [exact Hsc | exact (proj1 (usedX_MT _ _ _ _ Hu))].
Qed.
Lemma amo_head k g : 0 <= k < 48 -> active_hd A k = Some g -> exists am, amo (Some g) = Some am /\ usedX [] A g am /\ am_sc am = k.
Proof.
intros Hk Hg. destruct (head_am k g Hk Hg) as (am & Hu & Hsc & M). exists am. unfold amo. rewrite M. auto.
Qed.
Lemma mask_range g am : usedX [] A g am -> 0 <= am_avail am < 2 ^ 32 /\ 0 <= am_freed am < 2 ^ 32.
Proof.
intros Hu. pose proof (inv_groups HI g am Hu) as ((Glast & _ & _ & Gav & Gfr & _ & Gabove & _) & _).
split; split; try lia; apply (mask_u32 _ (am_last am)); try lia; intros i Hi; [apply (proj1 (Gabove i Hi)) | apply (proj2 (Gabove i Hi))].
Qed.
Definition uadj (h : hcase) : Z := usage_of A (sc0 + 1) + match h with HN | H3 => 3 | _ => 0 end.
Definition hsel (h : hcase) : Prop :=
match h with
| HN => h0 = None
| H1 => h0 <> None /\ avail_of h0 <> 0
| H2 => h0 <> None /\ avail_of h0 = 0 /\ freed_of h0 <> 0
| H3 => h0 <> None /\ avail_of h0 = 0 /\ freed_of h0 = 0
end.
Definition coarse_ok : Prop := 4 <= sc0 < 32 /\ sc0 <> 6 /\ Z.even sc0 = true.
Definition vsel (v : t1v) : Prop :=
match v with
| VA => g0 <> None
| VB6 => g0 = None /\ sc0 = 6
| VBout => g0 = None /\ (sc0 < 4 \/ 32 <= sc0)
| VBodd => g0 = None /\ 4 <= sc0 < 32 /\ sc0 <> 6 /\ Z.even sc0 = false
| VC => g0 = None /\ coarse_ok /\ usage_of A sc0 <> 0
| VD h lt => g0 = None /\ coarse_ok /\ usage_of A sc0 = 0 /\ hsel h /\ lt = (uadj h <? 13)
end.
Lemma vsel_exists : exists v, vsel v.
Proof.
destruct g0 as [g|] eqn:Eg.
{ exists VA. cbn. rewrite Eg. discriminate. }
destruct (Z.eq_dec sc0 6) as [E6|N6]; [exists VB6; cbn; auto|].
destruct (Z_lt_le_dec sc0 4) as [L4|L4]; [exists VBout; cbn; auto|].
destruct (Z_lt_le_dec sc0 32) as [L32|L32]; [|exists VBout; cbn; auto].
destruct (Z.even sc0) eqn:Ev; [|exists VBodd; cbn; auto 6].
assert (CO : coarse_ok) by (unfold coarse_ok; auto).
destruct (Z.eq_dec (usage_of A sc0) 0) as [U0z|U0nz]; [|exists VC; cbn; auto].
assert (pick : forall h, hsel h -> exists v, vsel v).
{ intros h Hh. exists (VD h (uadj h <? 13)). cbn. auto 6. }
destruct h0 as [h|] eqn:Eh; [|apply (pick HN); cbn; exact Eh].
destruct (Z.eq_dec (avail_of (Some h)) 0) as [Av|Av].
- destruct (Z.eq_dec (freed_of (Some h)) 0) as [Fr|Fr].
+ apply (pick H3). cbn. rewrite Eh. split; [discriminate | auto].
+ apply (pick H2). cbn. rewrite Eh. split; [discriminate | auto].
- apply (pick H1). cbn. rewrite Eh. split; [discriminate | auto].
Qed.
Lemma msc_eval v : vsel v -> sc = match v with VD _ true => sc0 + 1 | _ => sc0 end.
Proof.
intros Hv. pose proof sc0_range as [R0 _]. unfold sc, msc. change (size_to_class n) with sc0.
change (nth (Z.to_nat sc0) (st_active A) None) with g0.
assert (ELSE : (osptr_eqb g0 None && (4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage_of A sc0 =? 0)) = false ->
(if osptr_eqb g0 None && (4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage_of A sc0 =? 0) then
if (if match nth (Z.to_nat (sc0 + 1)) (st_active A) None with
| Some h => match mlookup (st_metas A) h with Some (MUsed am) => (am_avail am =? 0) && (am_freed am =? 0) | _ => true end
| None => true end
then usage_of A (sc0 + 1) + 3 else usage_of A (sc0 + 1)) <=? 12
then sc0 + 1 else sc0
else sc0) = sc0) by (intros E; rewrite E; reflexivity).
destruct v as [| | | | |h lt]; cbn in Hv.
- apply ELSE. destruct g0; [reflexivity | exfalso; apply Hv; reflexivity].
- apply ELSE. destruct Hv as [-> ->]. reflexivity.
- apply ELSE. destruct Hv as [-> Ho]. cbn [osptr_eqb andb].
destruct Ho as [Ho|Ho]; [replace (4 <=? sc0) with false by (symmetry; apply Z.leb_gt; lia); reflexivity|].
replace (sc0 <? 32) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r. reflexivity.
- apply ELSE. destruct Hv as (-> & R1 & R2 & Ev). rewrite Ev. rewrite !Bool.andb_false_r. reflexivity.
- apply ELSE. destruct Hv as (-> & _ & U). replace (usage_of A sc0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact U). rewrite Bool.andb_false_r. reflexivity.
- destruct Hv as (-> & (R1 & R2 & Ev) & U & Hh & Hlt). cbn [osptr_eqb].
replace (4 <=? sc0) with true by (symmetry; apply Z.leb_le; lia). replace (sc0 <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
replace (sc0 =? 6) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Ev, U. cbn [negb andb Z.eqb].
change (nth (Z.to_nat (sc0 + 1)) (st_active A) None) with (active_hd A (sc0 + 1)).
assert (Eh0 : h0 = active_hd A (sc0 + 1)) by (unfold h0; replace (sc0 <? 47) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
rewrite <- Eh0.
assert (HF : (if match h0 with
| Some h1 => match mlookup (st_metas A) h1 with Some (MUsed am) => (am_avail am =? 0) && (am_freed am =? 0) | _ => true end
| None => true end
then usage_of A (sc0 + 1) + 3 else usage_of A (sc0 + 1)) = uadj h).
{ unfold uadj. destruct h; cbn in Hh.
- rewrite Hh. reflexivity.
- destruct h0 as [h1|]; [|exfalso; exact (proj1 Hh eq_refl)].
destruct (amo_head (sc0 + 1) h1 ltac:(lia) ltac:(rewrite Eh0; reflexivity)) as (am & Eam & Hu & _).
unfold avail_of in Hh. rewrite Eam in Hh. change (mlookup (st_metas A) h1) with (MT A h1). rewrite (proj1 (usedX_MT _ _ _ _ Hu)).
replace (am_avail am =? 0) with false by (symmetry; apply Z.eqb_neq; exact (proj2 Hh)). cbn. lia.
- destruct h0 as [h1|]; [|exfalso; exact (proj1 Hh eq_refl)].
destruct (amo_head (sc0 + 1) h1 ltac:(lia) ltac:(rewrite Eh0; reflexivity)) as (am & Eam & Hu & _).
unfold avail_of, freed_of in Hh. rewrite Eam in Hh. change (mlookup (st_metas A) h1) with (MT A h1). rewrite (proj1 (usedX_MT _ _ _ _ Hu)).
destruct Hh as (_ & Ha & Hf). rewrite Ha. replace (am_freed am =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hf). cbn. lia.
- destruct h0 as [h1|]; [|exfalso; exact (proj1 Hh eq_refl)].
destruct (amo_head (sc0 + 1) h1 ltac:(lia) ltac:(rewrite Eh0; reflexivity)) as (am & Eam & Hu & _).
unfold avail_of, freed_of in Hh. rewrite Eam in Hh. change (mlookup (st_metas A) h1) with (MT A h1). rewrite (proj1 (usedX_MT _ _ _ _ Hu)).
destruct Hh as (_ & Ha & Hf). rewrite Ha, Hf. reflexivity. }
rewrite HF. replace (uadj h <=? 12) with (uadj h <? 13).
2:{ destruct (uadj h <? 13) eqn:E1; symmetry; [apply Z.leb_le; apply Z.ltb_lt in E1; lia | apply Z.leb_gt; apply Z.ltb_ge in E1; lia]. }
rewrite <- Hlt. destruct lt; reflexivity.
Qed.
Lemma sc_range : 0 <= sc < 48 /\ n + IB <= class_size sc.
Proof.
destruct vsel_exists as [v Hv]. rewrite (msc_eval v Hv). pose proof sc0_range as [R F].
destruct v as [| | | | |h [|]]; try (split; [exact R | exact F]).
cbn in Hv. destruct Hv as (_ & (R1 & _) & _). split; [lia|].
pose proof (class_size_mono sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma sc_head g : active_hd A sc = Some g -> exists am, usedX [] A g am /\ am_sc am = sc /\ MT A g = Some (MUsed am).
Proof. intros Hg. exact (head_am sc g (proj1 sc_range) Hg). Qed.
Definition xv1 (i : nat) : Z :=
if (i <? 32)%nat then bv_unsigned (getr regs1 (nat_to_reg i))
else match i with
| 40%nat => ACT | 41%nat => optrZ L g0 | 42%nat => avail_of g0 | 43%nat => usage_of A sc0
| 44%nat => optrZ L h0 | 45%nat => usage_of A (sc0 + 1) | 46%nat => avail_of h0 | 47%nat => freed_of h0
| _ => 0
end.
Lemma xv1_reg k : (k <= 31)%nat -> xv1 k = bv_unsigned (getr regs1 (nat_to_reg k)).
Proof. intros Hk. unfold xv1. replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. Qed.
Lemma head_facts k g : 0 <= k < 48 -> active_hd A k = Some g ->
exists am, amo (Some g) = Some am /\ usedX [] A g am /\ am_sc am = k /\
4096 <= ptr_addr L g /\ ptr_addr L g + 40 <= alloc_ceiling /\ ptr_addr L g mod 8 = 0 /\
(forall x, ptr_addr L g <= x < ptr_addr L g + 40 -> ~ in_img B x) /\
0 <= am_avail am < 2 ^ 32 /\ 0 <= am_freed am < 2 ^ 32.
Proof.
intros Hk Hg. destruct (amo_head k g Hk Hg) as (am & Eam & Hu & Hsc). exists am.
destruct (meta_facts [] None U0 L A md HI (mid_ledger _ _ _ _ _ MID1) g am Hu) as (M1 & M2 & M3 & M4 & _).
pose proof (mask_range g am Hu) as [R1 R2]. repeat (split; [assumption|]). exact R2.
Qed.
Lemma g0_val g : g0 = Some g -> optrZ L g0 = ptr_addr L g. Proof. intros ->. reflexivity. Qed.
Lemma h0_some h : h0 = Some h -> sc0 < 47 /\ active_hd A (sc0 + 1) = Some h.
Proof. unfold h0. destruct (sc0 <? 47) eqn:E; [apply Z.ltb_lt in E; auto | discriminate]. Qed.
Lemma h0_eq : sc0 < 47 -> h0 = active_hd A (sc0 + 1).
Proof. intros H. unfold h0. replace (sc0 <? 47) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma XR1 : forall k, 0 <= xv1 k < 2 ^ 64.
Proof.
intros k. pose proof sc0_range as [R0 _]. pose proof (proj1 (proj2 (proj2 PRE_facts))) as (HBu & _ & _). pose proof (proj1 alloc_ceiling_val).
unfold xv1. destruct (k <? 32)%nat; [apply u64_range|].
assert (OG : 0 <= optrZ L g0 < 2 ^ 64 /\ 0 <= avail_of g0 < 2 ^ 64).
{ destruct g0 as [g|] eqn:Eg; [|cbn; lia]. destruct (head_facts sc0 g R0 Eg) as (am & Eam & _ & _ & M1 & M2 & _ & _ & Av & _).
unfold avail_of. rewrite Eam. cbn [optrZ]. lia. }
assert (OH : 0 <= optrZ L h0 < 2 ^ 64 /\ 0 <= avail_of h0 < 2 ^ 64 /\ 0 <= freed_of h0 < 2 ^ 64).
{ destruct h0 as [h|] eqn:Eh; [|cbn; lia]. destruct (h0_some h Eh) as [S47 Hh].
destruct (head_facts (sc0 + 1) h ltac:(lia) Hh) as (am & Eam & _ & _ & M1 & M2 & _ & _ & Av & Fr).
unfold avail_of, freed_of. rewrite Eam. cbn [optrZ]. lia. }
pose proof (HBu sc0). pose proof (HBu (sc0 + 1)). pose proof statics_facts. unfold ACT.
do 48 (destruct k as [|k]; [lia|]). lia.
Qed.
Let E1 := EV xv1.
Lemma regs_ok1 : regs_ok E1 (regs_lit [(9%nat, LOCK); (19%nat, DEB); (4%nat, TP)]) regs1.
Proof.
apply regs_ok_lit. intros k Hk.
destruct (Nat.eq_dec k 9) as [->|Hk9]; [cbn; exact (pa_9 _ _ _ _ _ AT)|].
destruct (Nat.eq_dec k 19) as [->|Hk19]; [cbn; exact (pa_19 _ _ _ _ _ AT)|].
destruct (Nat.eq_dec k 4) as [->|Hk4]; [cbn; exact (pa_4 _ _ _ _ _ AT)|].
replace (find (fun p : nat * Z => Nat.eqb (fst p) k) [(9%nat, LOCK); (19%nat, DEB); (4%nat, TP)]) with (@None (nat * Z)).
2:{ cbn [find fst]. rewrite !(proj2 (Nat.eqb_neq _ _)) by lia. reflexivity. }
rewrite xv1_reg by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma X20 : xv1 20%nat = sc0.
Proof. rewrite xv1_reg by lia. change (nat_to_reg 20) with (20%bv : bv 5). rewrite (pa_20 _ _ _ _ _ AT). apply lit64_small. pose proof sc0_range. lia. Qed.
Lemma X8 : xv1 8%nat = n.
Proof. rewrite xv1_reg by lia. change (nat_to_reg 8) with (8%bv : bv 5). rewrite (pa_8 _ _ _ _ _ AT). apply lit64_small. unfold MMAP_THRESHOLD in Hn. lia. Qed.
Lemma X2 : xv1 2%nat = SP0 - 48.
Proof.
pose proof PRE_facts as (_ & _ & _ & _ & _ & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val).
rewrite xv1_reg by lia. change (nat_to_reg 2) with (2%bv : bv 5). rewrite (pa_2 _ _ _ _ _ AT). unfold YN1p.SP0. apply lit64_small. unfold SP0 in *. lia.
Qed.
Lemma rok_nl : region_ok src0segs E1 mem1 R_nl.
Proof.
pose proof statics_facts. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_nl base_val]; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_lit0. intros k Hk. replace k with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, Z.add_0_l.
exact (st_needlocks _ _ (mid_statics _ _ _ _ _ MID1)).
Qed.
Lemma rok_act cs : Forall (chunk_ok src0segs E1 mem1 ACT) cs -> region_ok src0segs E1 mem1 (R_act cs).
Proof.
intros Hcs. pose proof sc0_range as [R0 _]. pose proof statics_facts.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_act]; unfold E1; rewrite (base_val_EV xv1 XR1); change (xv1 aACT) with ACT;
[unfold ACT; lia | unfold ACT; lia | intros; lia | exact Hcs].
Qed.
Lemma act_cell : bytes_are mem1 ACT 8 (optrZ L g0).
Proof.
pose proof sc0_range as [R0 _]. pose proof (ctx_active_cell [] L A mem1 Hctx MR1 (Z.to_nat sc0) ltac:(lia)) as C.
rewrite Z2Nat.id in C by lia. unfold g0, active_hd, ACT. exact C.
Qed.
Lemma us0_cell : bytes_are mem1 (ACT + 384) 8 (usage_of A sc0).
Proof.
pose proof sc0_range as [R0 _]. pose proof (ctx_usage_cell [] L A mem1 Hctx MR1 (Z.to_nat sc0) ltac:(lia)) as C.
rewrite Z2Nat.id in C by lia. unfold usage_of, znth. replace (sc0 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
eapply bytes_are_at; [exact C | unfold ACT; change YN0t.CTX with CTX; lia].
Qed.
Lemma act1_cell : sc0 < 47 -> bytes_are mem1 (ACT + 8) 8 (optrZ L h0).
Proof.
intros S. pose proof sc0_range as [R0 _]. pose proof (ctx_active_cell [] L A mem1 Hctx MR1 (Z.to_nat (sc0 + 1)) ltac:(lia)) as C.
rewrite Z2Nat.id in C by lia. rewrite (h0_eq S). unfold active_hd.
eapply bytes_are_at; [exact C | unfold ACT; change YN0t.CTX with CTX; lia].
Qed.
Lemma us1_cell : sc0 < 47 -> bytes_are mem1 (ACT + 392) 8 (usage_of A (sc0 + 1)).
Proof.
intros S. pose proof sc0_range as [R0 _]. pose proof (ctx_usage_cell [] L A mem1 Hctx MR1 (Z.to_nat (sc0 + 1)) ltac:(lia)) as C.
rewrite Z2Nat.id in C by lia. unfold usage_of, znth. replace (sc0 + 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
eapply bytes_are_at; [exact C | unfold ACT; change YN0t.CTX with CTX; lia].
Qed.
Lemma ck_act0_t : g0 <> None -> chunk_ok src0segs E1 mem1 ACT (c_act0 true).
Proof.
intros Hg. unfold c_act0, E1. eapply (chunk_ok_val xv1 _ _ _ 8); [apply (U_off0 xv1 XR1) | apply XR1 |]. change (xv1 aG) with (optrZ L g0). rewrite Z.add_0_r. apply act_cell.
Qed.
Lemma ck_act0_f : g0 = None -> chunk_ok src0segs E1 mem1 ACT (c_act0 false).
Proof.
intros Hg. unfold c_act0, E1. apply chunk_ok_lit0. intros k Hk. rewrite Z.add_0_r. pose proof act_cell as C. rewrite Hg in C. cbn [optrZ] in C.
rewrite (C k Hk). f_equal. f_equal. apply le_byte_0.
Qed.
Lemma ck_us0_t : usage_of A sc0 = 0 -> chunk_ok src0segs E1 mem1 ACT (c_us0 true).
Proof.
intros Hu. unfold c_us0, E1. apply chunk_ok_lit0. intros k Hk. pose proof us0_cell as C. rewrite Hu in C. rewrite (C k Hk). f_equal. f_equal. apply le_byte_0.
Qed.
Lemma ck_us0_f : chunk_ok src0segs E1 mem1 ACT (c_us0 false).
Proof. unfold c_us0, E1. eapply (chunk_ok_val xv1 _ _ _ 8); [apply (U_off0 xv1 XR1) | apply XR1 | apply us0_cell]. Qed.
Lemma ck_act1_N : sc0 < 47 -> h0 = None -> chunk_ok src0segs E1 mem1 ACT (c_act1 HN).
Proof.
intros S Hh. unfold c_act1, E1. apply chunk_ok_lit0. intros k Hk. pose proof (act1_cell S) as C. rewrite Hh in C. cbn [optrZ] in C.
rewrite (C k Hk). f_equal. f_equal. apply le_byte_0.
Qed.
Lemma ck_act1_S h : sc0 < 47 -> h <> HN -> chunk_ok src0segs E1 mem1 ACT (c_act1 h).
Proof.
intros S Hh. replace (c_act1 h) with (mkChunk 8 (CVal 8 (SOff aH 0))) by (destruct h; [congruence| | |]; reflexivity).
unfold E1. eapply (chunk_ok_val xv1 _ _ _ 8); [apply (U_off0 xv1 XR1) | apply XR1 | apply (act1_cell S)].
Qed.
Lemma ck_us1 : sc0 < 47 -> chunk_ok src0segs E1 mem1 ACT c_us1.
Proof. intros S. unfold c_us1, E1. eapply (chunk_ok_val xv1 _ _ _ 8); [apply (U_off0 xv1 XR1) | apply XR1 | apply (us1_cell S)]. Qed.
Lemma meta_mask_cells g am : usedX [] A g am ->
bytes_are mem1 (ptr_addr L g + 24) 4 (am_avail am) /\ bytes_are mem1 (ptr_addr L g + 28) 4 (am_freed am).
Proof.
intros Hu.
pose proof (meta_cell [] None U0 L A mem1 HI MR1 g am _ Hu ltac:(cbn; do 3 right; left; reflexivity)) as C1.
pose proof (meta_cell [] None U0 L A mem1 HI MR1 g am _ Hu ltac:(cbn; do 4 right; left; reflexivity)) as C2.
unfold cell_mem in C1, C2. cbn [mc_val mc_loc mc_w sval_num] in C1, C2. rewrite loc_addr_padd' in C1, C2.
change (ms_segs B) with src0segs in C1, C2. unfold META_avail in C1. unfold META_freed in C2. unfold ptr_addr. split; [exact C1 | exact C2].
Qed.
Lemma rok_g : g0 <> None -> region_ok src0segs E1 mem1 R_g.
Proof.
intros Hg. pose proof sc0_range as [R0 _]. pose proof (proj1 alloc_ceiling_val).
destruct g0 as [g|] eqn:Eg; [|congruence]. destruct (head_facts sc0 g R0 Eg) as (am & Eam & Hu & _ & M1 & M2 & _ & _ & Av & _).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_g]; unfold E1; rewrite (base_val_EV xv1 XR1); change (xv1 aG) with (optrZ L g0); rewrite Eg; cbn [optrZ];
[lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val xv1 _ _ _ 4); [apply (U_off0 xv1 XR1) | |];
change (xv1 aAV) with (avail_of g0); unfold avail_of; rewrite Eg, Eam; [change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | apply (proj1 (meta_mask_cells g am Hu))].
Qed.
Lemma rok_h h : hsel h -> h <> HN -> region_ok src0segs E1 mem1 (R_h h).
Proof.
intros Hs HN'. pose proof sc0_range as [R0 _]. pose proof (proj1 alloc_ceiling_val).
assert (Hh0 : h0 <> None) by (destruct h; cbn in Hs; [congruence | | |]; exact (proj1 Hs)).
destruct h0 as [hp|] eqn:Eh; [|congruence]. destruct (h0_some hp Eh) as [S47 Hhp].
destruct (head_facts (sc0 + 1) hp ltac:(lia) Hhp) as (am & Eam & Hu & _ & M1 & M2 & _ & _ & Av & Fr).
destruct (meta_mask_cells hp am Hu) as [CA CF].
assert (AVv : avail_of h0 = am_avail am) by (unfold avail_of; rewrite Eh, Eam; reflexivity).
assert (FRv : freed_of h0 = am_freed am) by (unfold freed_of; rewrite Eh, Eam; reflexivity).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_h]; unfold E1; rewrite (base_val_EV xv1 XR1); change (xv1 aH) with (optrZ L h0); rewrite Eh; cbn [optrZ];
[lia | lia | intros; lia |].
destruct h; [congruence| | |]; cbn in Hs; rewrite AVv, ?FRv in Hs; unfold h_chunks.
- apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val xv1 _ _ _ 4); [apply (U_off0 xv1 XR1) | |]; change (xv1 aHAV) with (avail_of h0); rewrite AVv;
[change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact CA].
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ apply chunk_ok_lit0. intros k Hk. rewrite (CA k Hk), (proj1 (proj2 Hs)). f_equal. f_equal. apply le_byte_0.
+ eapply (chunk_ok_val xv1 _ _ _ 4); [apply (U_off0 xv1 XR1) | |]; change (xv1 aHFR) with (freed_of h0); rewrite FRv;
[change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact CF].
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ apply chunk_ok_lit0. intros k Hk. rewrite (CA k Hk), (proj1 (proj2 Hs)). f_equal. f_equal. apply le_byte_0.
+ apply chunk_ok_lit0. intros k Hk. rewrite (CF k Hk), (proj2 (proj2 Hs)). f_equal. f_equal. apply le_byte_0.
Qed.
Lemma g_far : g0 <> None -> optrZ L g0 + 40 <= 0x10000 \/ 0x51000 <= optrZ L g0.
Proof.
intros Hg. pose proof sc0_range as [R0 _]. destruct g0 as [g|] eqn:Eg; [|congruence].
destruct (head_facts sc0 g R0 Eg) as (am & _ & _ & _ & _ & _ & _ & NI & _). cbn [optrZ]. apply off_img. exact NI.
Qed.
Lemma h_far : h0 <> None -> optrZ L h0 + 40 <= 0x10000 \/ 0x51000 <= optrZ L h0.
Proof.
intros Hh. destruct h0 as [hp|] eqn:Eh; [|congruence]. destruct (h0_some hp Eh) as [S47 Hhp].
destruct (head_facts (sc0 + 1) hp ltac:(pose proof sc0_range; lia) Hhp) as (am & _ & _ & _ & _ & _ & _ & NI & _). cbn [optrZ]. apply off_img. exact NI.
Qed.
Lemma mem_ok1 v : vsel v -> mem_ok src0segs E1 mem1 (t1_mem v).
Proof.
intros Hv. pose proof sc0_range as [R0 _].
pose proof statics_facts as STF. assert (ACTR : CTX + 80 <= ACT <= CTX + 80 + 8 * 47) by (unfold ACT; lia).
split; [destruct v as [| | | | |[| | |] [|]]; vm_compute; reflexivity|].
assert (BA : base_val E1 (Some aACT) = ACT) by (unfold E1; rewrite (base_val_EV xv1 XR1); reflexivity).
assert (BG : base_val E1 (Some aG) = optrZ L g0) by (unfold E1; rewrite (base_val_EV xv1 XR1); reflexivity).
assert (BH : base_val E1 (Some aH) = optrZ L h0) by (unfold E1; rewrite (base_val_EV xv1 XR1); reflexivity).
destruct v as [| | | | |h lt]; cbn in Hv; unfold t1_mem, act_chunks.
- split.
+ repeat apply Forall_cons; [apply rok_nl | apply rok_act | apply (rok_g Hv) | apply Forall_nil].
apply Forall_cons; [apply (ck_act0_t Hv) | apply Forall_nil].
+ pose proof (g_far Hv) as GF. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_nl R_act R_g]. rewrite BA, BG. cbn [base_val].
repeat split; try exact I; lia.
- destruct Hv as [Hg _]. split.
+ repeat apply Forall_cons; [apply rok_nl | apply rok_act | apply Forall_nil]. apply Forall_cons; [apply (ck_act0_f Hg) | apply Forall_nil].
+ cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_nl R_act]. rewrite BA. cbn [base_val]. repeat split; try exact I; lia.
- destruct Hv as [Hg _]. split.
+ repeat apply Forall_cons; [apply rok_nl | apply rok_act | apply Forall_nil]. apply Forall_cons; [apply (ck_act0_f Hg) | apply Forall_nil].
+ cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_nl R_act]. rewrite BA. cbn [base_val]. repeat split; try exact I; lia.
- destruct Hv as [Hg _]. split.
+ repeat apply Forall_cons; [apply rok_nl | apply rok_act | apply Forall_nil]. apply Forall_cons; [apply (ck_act0_f Hg) | apply Forall_nil].
+ cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_nl R_act]. rewrite BA. cbn [base_val]. repeat split; try exact I; lia.
- destruct Hv as (Hg & _ & Hu). split.
+ repeat apply Forall_cons; [apply rok_nl | apply rok_act | apply Forall_nil].
apply Forall_cons; [apply (ck_act0_f Hg) | apply Forall_cons; [apply ck_us0_f | apply Forall_nil]].
+ cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_nl R_act]. rewrite BA. cbn [base_val]. repeat split; try exact I; lia.
- destruct Hv as (Hg & (R1 & R2 & Ev) & Hu & Hs & Hlt).
assert (CK : Forall (chunk_ok src0segs E1 mem1 ACT) [c_act0 false; c_us0 true; c_act1 h; c_us1]).
{ apply Forall_cons; [apply (ck_act0_f Hg)|]. apply Forall_cons; [apply (ck_us0_t Hu)|].
apply Forall_cons; [| apply Forall_cons; [apply ck_us1; lia | apply Forall_nil]].
destruct h; [apply ck_act1_N; [lia | exact Hs] | | |]; (apply ck_act1_S; [lia | discriminate]). }
destruct h.
+ split; [repeat apply Forall_cons; [apply rok_nl | apply rok_act; exact CK | apply Forall_nil]|].
cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_nl R_act]. rewrite BA. cbn [base_val]. repeat split; try exact I; lia.
+ assert (Hh : h0 <> None) by exact (proj1 Hs). pose proof (h_far Hh) as HF.
split; [repeat apply Forall_cons; [apply rok_nl | apply rok_act; exact CK | apply (rok_h H1 Hs ltac:(discriminate)) | apply Forall_nil]|].
cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_nl R_act R_h]. rewrite BA, BH. cbn [base_val]. repeat split; try exact I; lia.
+ assert (Hh : h0 <> None) by exact (proj1 Hs). pose proof (h_far Hh) as HF.
split; [repeat apply Forall_cons; [apply rok_nl | apply rok_act; exact CK | apply (rok_h H2 Hs ltac:(discriminate)) | apply Forall_nil]|].
cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_nl R_act R_h]. rewrite BA, BH. cbn [base_val]. repeat split; try exact I; lia.
+ assert (Hh : h0 <> None) by exact (proj1 Hs). pose proof (h_far Hh) as HF.
split; [repeat apply Forall_cons; [apply rok_nl | apply rok_act; exact CK | apply (rok_h H3 Hs ltac:(discriminate)) | apply Forall_nil]|].
cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_nl R_act R_h]. rewrite BA, BH. cbn [base_val]. repeat split; try exact I; lia.
Qed.
Lemma atoms_ok_cons E k f l : afact_ok E k f -> atoms_ok E l -> atoms_ok E ((k, f) :: l).
Proof. intros. cbn. auto. Qed.
Lemma conds_ok_cons E c l : acond_ok E c -> conds_ok E l -> conds_ok E (c :: l).
Proof. intros. cbn. auto. Qed.
Lemma alias_ok_cons E a b l : sv_denot E a = sv_denot E b -> alias_ok E l -> alias_ok E ((a, b) :: l).
Proof. intros. cbn. auto. Qed.
Ltac af := unfold afact_ok; cbn [af_lo af_hi af_al2]; unfold E1; rewrite (ew_EV xv1 XR1).
Lemma af_common : atoms_ok E1 [(8%nat, mkAF 0 131051 0); (2%nat, F_sp48); (aACT, mkAF (CTX+80) (CTX+80+8*47) 3)].
Proof.
pose proof sc0_range as [R0 _]. pose proof PRE_facts as (_ & _ & _ & _ & Hal & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val).
apply atoms_ok_cons; [|apply atoms_ok_cons; [|apply atoms_ok_cons; [|exact I]]]; af.
- rewrite X8. unfold MMAP_THRESHOLD in Hn. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
- rewrite X2. unfold F_sp48, CEIL. cbn [af_lo af_hi af_al2]. change (2 ^ 4) with 16. unfold SP0 in *.
split; [lia|]. split; [|lia]. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
- pose proof statics_facts as (_ & _ & _ & A8). change (xv1 aACT) with ACT. unfold ACT. change (2 ^ 3) with 8. split; [lia|]. split; [|lia].
rewrite Z.mul_comm, Z_mod_plus_full. exact A8.
Qed.
Lemma af_20 lo hi : lo <= sc0 <= hi -> afact_ok E1 20%nat (mkAF lo hi 0).
Proof. intros H. af. rewrite X20. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. Qed.
Lemma af_aG : g0 <> None -> afact_ok E1 aG (mkAF 4096 (2^63) 3).
Proof.
intros Hg. pose proof sc0_range as [R0 _]. pose proof (proj1 alloc_ceiling_val). destruct g0 as [g|] eqn:Eg; [|congruence].
destruct (head_facts sc0 g R0 Eg) as (am & _ & _ & _ & M1 & M2 & M3 & _). af. change (xv1 aG) with (optrZ L g0). rewrite Eg. cbn [optrZ]. change (2 ^ 3) with 8. lia.
Qed.
Lemma af_aAV : afact_ok E1 aAV (mkAF 0 (2^32-1) 0).
Proof.
pose proof sc0_range as [R0 _]. af. change (xv1 aAV) with (avail_of g0). change (2 ^ 0) with 1. rewrite Z.mod_1_r.
unfold avail_of. destruct g0 as [g|] eqn:Eg; [|cbn; lia]. destruct (head_facts sc0 g R0 Eg) as (am & -> & _ & _ & _ & _ & _ & _ & Av & _). lia.
Qed.
Lemma af_aUS : usage_of A sc0 <> 0 -> afact_ok E1 aUS (mkAF 1 (2^48) 0).
Proof.
intros Hu. pose proof (proj1 (proj2 (proj2 PRE_facts))) as (HBu & _). pose proof (HBu sc0). af. change (xv1 aUS) with (usage_of A sc0). change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
Qed.
Lemma af_aHU : afact_ok E1 aHU (mkAF 0 (2^48) 0).
Proof.
pose proof (proj1 (proj2 (proj2 PRE_facts))) as (HBu & _). pose proof (HBu (sc0 + 1)). af. change (xv1 aHU) with (usage_of A (sc0 + 1)). change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
Qed.
Lemma af_aH : h0 <> None -> afact_ok E1 aH (mkAF 4096 (2^63) 3).
Proof.
intros Hh. pose proof sc0_range as [R0 _]. pose proof (proj1 alloc_ceiling_val). destruct h0 as [hp|] eqn:Eh; [|congruence]. destruct (h0_some hp Eh) as [S47 Hhp].
destruct (head_facts (sc0 + 1) hp ltac:(lia) Hhp) as (am & _ & _ & _ & M1 & M2 & M3 & _). af. change (xv1 aH) with (optrZ L h0). rewrite Eh. cbn [optrZ]. change (2 ^ 3) with 8. lia.
Qed.
Lemma h_masks : h0 <> None -> 0 <= avail_of h0 < 2 ^ 32 /\ 0 <= freed_of h0 < 2 ^ 32.
Proof.
intros Hh. pose proof sc0_range as [R0 _]. destruct h0 as [hp|] eqn:Eh; [|congruence]. destruct (h0_some hp Eh) as [S47 Hhp].
destruct (head_facts (sc0 + 1) hp ltac:(lia) Hhp) as (am & Eam & _ & _ & _ & _ & _ & _ & Av & Fr). unfold avail_of, freed_of. rewrite Eam. lia.
Qed.
Lemma af_aHAV : h0 <> None -> avail_of h0 <> 0 -> afact_ok E1 aHAV (mkAF 1 (2^32-1) 0).
Proof. intros Hh Ha. pose proof (h_masks Hh). af. change (xv1 aHAV) with (avail_of h0). change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. Qed.
Lemma af_aHFR : h0 <> None -> freed_of h0 <> 0 -> afact_ok E1 aHFR (mkAF 1 (2^32-1) 0).
Proof. intros Hh Hf. pose proof (h_masks Hh). af. change (xv1 aHFR) with (freed_of h0). change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. Qed.
Ltac cd := unfold acond_ok; cbn [ac_c ac_a ac_b C_eq6 C_ne6 C_lt4 C_in C_odd C_even C_u C_hav C_hfr]; unfold E1.
Lemma cd_eq6 : sc0 = 6 -> acond_ok E1 C_eq6.
Proof. intros H. cd. rewrite (den_off0 xv1 XR1), X20. cbn [sv_denot]. rewrite bt_eq by lia. rewrite H. reflexivity. Qed.
Lemma cd_ne6 : sc0 <> 6 -> acond_ok E1 C_ne6.
Proof. intros H. pose proof sc0_range. cd. rewrite (den_off0 xv1 XR1), X20. cbn [sv_denot]. rewrite bt_ne by lia. replace (sc0 =? 6) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity. Qed.
Lemma cd_lt4 : sc0 < 4 \/ 32 <= sc0 -> acond_ok E1 C_lt4.
Proof.
intros H. pose proof sc0_range. cd. cbn [sv_denot]. rewrite (ew_EV xv1 XR1), X20. cbn [branch_taken]. unfold bv_ltu.
rewrite lit64_small by lia. rewrite Z_to_bv_unsigned. apply Z.ltb_lt. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct H as [H|H].
- replace (sc0 + -4) with ((2 ^ 64 + sc0 - 4) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia.
Qed.
Lemma cd_in : 4 <= sc0 < 32 -> acond_ok E1 C_in.
Proof.
intros H. cd. cbn [sv_denot]. rewrite (ew_EV xv1 XR1), X20. cbn [branch_taken]. unfold bv_ltu.
rewrite lit64_small by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
replace (27 <? sc0 + -4) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma land1_val : Z.land sc0 1 = if Z.even sc0 then 0 else 1.
Proof.
pose proof sc0_range. pose proof (land1_even sc0 ltac:(lia)) as E. pose proof (Z_land_upper sc0 1 ltac:(lia)) as U0'.
destruct (Z.even sc0); [apply Z.eqb_eq in E; exact E | apply Z.eqb_neq in E; lia].
Qed.
Lemma cd_odd : Z.even sc0 = false -> acond_ok E1 C_odd.
Proof.
intros H. pose proof sc0_range. cd. rewrite !UZ_sound. cbn [UZ]. rewrite X20. unfold zalu64. cbn [zalu_raw].
rewrite ?Z.add_0_r, !(zcanon_id sc0), !(zcanon_id 1), land1_val, H, !(zcanon_id 1), !(zcanon_id 0) by (unfold M64; lia).
rewrite bt_ne by lia. reflexivity.
Qed.
Lemma cd_even : Z.even sc0 = true -> acond_ok E1 C_even.
Proof.
intros H. pose proof sc0_range. cd. rewrite !UZ_sound. cbn [UZ]. rewrite X20. unfold zalu64. cbn [zalu_raw].
rewrite ?Z.add_0_r, !(zcanon_id sc0), !(zcanon_id 1), land1_val, H, !(zcanon_id 0) by (unfold M64; lia).
rewrite bt_eq by lia. reflexivity.
Qed.
Lemma cd_u h lt : sc0 < 47 -> lt = (uadj h <? 13) -> acond_ok E1 (C_u h lt).
Proof.
intros S Hlt. pose proof (proj1 (proj2 (proj2 PRE_facts))) as (HBu & _). pose proof (HBu (sc0 + 1)).
assert (DU : sv_denot (EV xv1) (UX h) = Z_to_bv 64 (uadj h)).
{ unfold UX, uadj. destruct h; (rewrite (den_off xv1 XR1); [|change (xv1 aHU) with (usage_of A (sc0 + 1)); lia]); change (xv1 aHU) with (usage_of A (sc0 + 1)); f_equal; lia. }
assert (UR : 0 <= uadj h < 2 ^ 64) by (unfold uadj; destruct h; lia).
cd. rewrite DU. cbn [sv_denot]. subst lt. destruct (uadj h <? 13) eqn:E; [rewrite bt_ltu by lia; exact E | rewrite bt_geu by lia; rewrite E; reflexivity].
Qed.
Lemma cd_hav : h0 <> None -> avail_of h0 <> 0 -> acond_ok E1 C_hav.
Proof.
intros Hh Ha. pose proof (h_masks Hh) as [Av _]. cd. apply Bool.negb_true_iff. apply bv_eqb_false_iff. intros EQ.
apply (f_equal bv_unsigned) in EQ. rewrite (U_sext32 xv1), (U_off0 xv1 XR1) in EQ. change (xv1 aHAV) with (avail_of h0) in EQ.
cbn [sv_denot] in EQ. rewrite Z_to_bv_unsigned in EQ. change (bv_wrap 64 0) with 0 in EQ. exact (sx32_nonzero_u32 (avail_of h0) ltac:(lia) EQ).
Qed.
Lemma cd_hfr : h0 <> None -> freed_of h0 <> 0 -> acond_ok E1 C_hfr.
Proof.
intros Hh Hf. pose proof (h_masks Hh) as [_ Fr]. cd. apply Bool.negb_true_iff. apply bv_eqb_false_iff. intros EQ.
apply (f_equal bv_unsigned) in EQ. rewrite (U_sext32 xv1), (U_off0 xv1 XR1) in EQ. change (xv1 aHFR) with (freed_of h0) in EQ.
cbn [sv_denot] in EQ. rewrite Z_to_bv_unsigned in EQ. change (bv_wrap 64 0) with 0 in EQ. exact (sx32_nonzero_u32 (freed_of h0) ltac:(lia) EQ).
Qed.
Lemma al1 : sv_denot E1 (fst AL1) = sv_denot E1 (snd AL1).
Proof.
pose proof sc0_range. cbn [fst snd AL1]. unfold E1. rewrite !UZ_sound. f_equal. cbn [UZ]. rewrite X20. change (xv1 aACT) with ACT. unfold zalu64, ACT. cbn [zalu_raw].
pose proof statics_facts. rewrite ?Z.add_0_r, !(zcanon_id sc0), !(zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite (zcanon_id (CTX + 80 + 8 * sc0)) by (unfold M64; lia).
rewrite !zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma al2 : Z.even sc0 = true -> sv_denot E1 (fst AL2) = sv_denot E1 (snd AL2).
Proof.
intros Ev. pose proof sc0_range. cbn [fst snd AL2]. unfold E1. rewrite !UZ_sound. f_equal. cbn [UZ]. rewrite X20. change (xv1 aACT) with ACT. unfold zalu64, ACT. cbn [zalu_raw].
pose proof statics_facts. rewrite ?Z.add_0_r, !(zcanon_id sc0), !(zcanon_id 1), (lor1_even sc0) by (unfold M64; try lia; exact Ev).
rewrite ?Z.add_0_r, !(zcanon_id (sc0 + 1)), !(zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite (zcanon_id (CTX + 80 + 8 * sc0)) by (unfold M64; lia).
rewrite !zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma facts_ok1 v : vsel v -> facts_ok E1 (t1_facts v).
Proof.
pose proof (proj1 alloc_ceiling_val) as ACV_p9.
intros Hv. pose proof sc0_range as [R0 _]. unfold t1_facts, facts_ok. cbn [f_atoms f_conds f_alias].
destruct v as [| | | | |h lt]; cbn in Hv; unfold t1_atoms, t1_conds, t1_alias.
- split; [|split; [exact I | apply alias_ok_cons; [apply al1 | exact I]]].
cbn [app]. apply atoms_ok_cons; [apply af_20; lia|]. apply atoms_ok_cons; [apply (af_aG Hv)|]. apply atoms_ok_cons; [apply af_aAV | apply af_common].
- destruct Hv as [Hg H6]. split; [|split; [apply conds_ok_cons; [apply (cd_eq6 H6) | exact I] | apply alias_ok_cons; [apply al1 | exact I]]].
cbn [app]. apply atoms_ok_cons; [apply af_20; lia | apply af_common].
- destruct Hv as [Hg Ho]. split; [|split; [apply conds_ok_cons; [apply cd_ne6; lia | apply conds_ok_cons; [apply (cd_lt4 Ho) | exact I]] | apply alias_ok_cons; [apply al1 | exact I]]].
cbn [app]. apply atoms_ok_cons; [apply af_20; lia | apply af_common].
- destruct Hv as (Hg & R1 & N6 & Ev).
split; [|split; [apply conds_ok_cons; [apply cd_ne6; lia | apply conds_ok_cons; [apply (cd_in R1) | apply conds_ok_cons; [apply (cd_odd Ev) | exact I]]] | apply alias_ok_cons; [apply al1 | exact I]]].
cbn [app]. apply atoms_ok_cons; [apply af_20; lia | apply af_common].
- destruct Hv as (Hg & (R1 & N6 & Ev) & Hu).
split; [|split; [apply conds_ok_cons; [apply cd_ne6; lia | apply conds_ok_cons; [apply (cd_in R1) | apply conds_ok_cons; [apply (cd_even Ev) | exact I]]] | apply alias_ok_cons; [apply al1 | exact I]]].
cbn [app]. apply atoms_ok_cons; [apply af_20; lia |]. apply atoms_ok_cons; [apply (af_aUS Hu) | apply af_common].
- destruct Hv as (Hg & (R1 & N6 & Ev) & Hu & Hs & Hlt).
split; [|split].
+ cbn [app]. apply atoms_ok_cons; [apply af_20; lia |]. apply atoms_ok_cons; [apply af_aHU |].
destruct h; cbn in Hs; cbn [app].
* apply af_common.
* apply atoms_ok_cons; [apply af_aH; exact (proj1 Hs)|]. apply atoms_ok_cons; [apply af_aHAV; [exact (proj1 Hs) | exact (proj2 Hs)] | apply af_common].
* apply atoms_ok_cons; [apply af_aH; exact (proj1 Hs)|]. apply atoms_ok_cons; [apply af_aHFR; [exact (proj1 Hs) | exact (proj2 (proj2 Hs))] | apply af_common].
* apply atoms_ok_cons; [apply af_aH; exact (proj1 Hs) | apply af_common].
+ cbn [app]. apply conds_ok_cons; [apply cd_ne6; lia|]. apply conds_ok_cons; [apply (cd_in R1)|]. apply conds_ok_cons; [apply (cd_even Ev)|].
apply conds_ok_cons; [apply cd_u; [lia | exact Hlt]|].
destruct h; cbn in Hs; [exact I | apply conds_ok_cons; [apply cd_hav; [exact (proj1 Hs) | exact (proj2 Hs)] | exact I]
| apply conds_ok_cons; [apply cd_hfr; [exact (proj1 Hs) | exact (proj2 (proj2 Hs))] | exact I] | exact I].
+ apply alias_ok_cons; [apply al1|]. apply alias_ok_cons; [apply (al2 Ev) | exact I].
Qed.
Lemma T1_st_ok v : vsel v -> st_ok src0segs E1 (ss_T1 v) (mkst regs1 (Z_to_bv 64 PA) mem1 rom).
Proof.
intros Hv. unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_T1 resv_denot].
repeat (split; [reflexivity|]). split; [apply regs_ok1|]. split; [apply (mem_ok1 v Hv) | apply (facts_ok1 v Hv)].
Qed.
Record at_PB (regs2 : bvmap 5 word) : Prop := PB_ {
pb_20 : getr regs2 20 = Z_to_bv 64 sc;
pb_18 : getr regs2 18 = Z_to_bv 64 gaddr;
pb_10 : getr regs2 10 = Z_to_bv 64 gmask;
pb_8 : getr regs2 8 = Z_to_bv 64 n;
pb_9 : getr regs2 9 = Z_to_bv 64 LOCK;
pb_19 : getr regs2 19 = Z_to_bv 64 DEB;
pb_2 : getr regs2 2 = Z_to_bv 64 (SP0 - 48);
pb_4 : getr regs2 4 = Z_to_bv 64 TP;
pb_cs : forall i, In i CSAVED -> getr regs2 (nat_to_reg i) = getr regs (nat_to_reg i) }.
Lemma outs_denot v : vsel v ->
sv_denot E1 (t1_s4 v) = Z_to_bv 64 sc /\ sv_denot E1 (t1_s2 v) = Z_to_bv 64 gaddr /\ sv_denot E1 (t1_a0 v) = Z_to_bv 64 gmask.
Proof.
intros Hv. pose proof sc0_range as [R0 _]. pose proof (msc_eval v Hv) as Esc. unfold gaddr, gmask. rewrite Esc. unfold E1.
assert (S4 : sv_denot (EV xv1) (SOff 20 0) = Z_to_bv 64 sc0) by (rewrite (den_off0 xv1 XR1), X20; reflexivity).
assert (OR : Z.even sc0 = true -> sv_denot (EV xv1) OR1 = Z_to_bv 64 (sc0 + 1)).
{ intros Ev. unfold OR1. rewrite UZ_sound. f_equal. cbn [UZ]. rewrite X20. unfold zalu64. cbn [zalu_raw].
rewrite ?Z.add_0_r, !(zcanon_id sc0), !(zcanon_id 1), (lor1_even sc0) by (unfold M64; try lia; exact Ev).
rewrite ?Z.add_0_r. rewrite !(zcanon_id (sc0 + 1)) by (unfold M64; lia). reflexivity. }
assert (NONE : g0 = None -> Z_to_bv 64 (optrZ L (active_hd A sc0)) = Z_to_bv 64 0 /\ Z_to_bv 64 (sx32 (avail_of (active_hd A sc0))) = Z_to_bv 64 0).
{ intros Hg. change (active_hd A sc0) with g0. rewrite Hg. cbn. rewrite sx32_small by lia. auto. }
destruct v as [| | | | |h lt]; cbn in Hv; cbn [t1_s4 t1_s2 t1_a0].
- split; [exact S4|]. change (active_hd A sc0) with g0. split; [rewrite (den_off0 xv1 XR1); reflexivity|].
rewrite (denot_lit_U (EV xv1)). unfold U. rewrite (U_sext32 xv1), (U_off0 xv1 XR1). reflexivity.
- destruct Hv as [Hg _]. destruct (NONE Hg) as [-> ->]. auto.
- destruct Hv as [Hg _]. destruct (NONE Hg) as [-> ->]. auto.
- destruct Hv as [Hg _]. destruct (NONE Hg) as [-> ->]. auto.
- destruct Hv as (Hg & _). destruct (NONE Hg) as [-> ->]. auto.
- destruct Hv as (Hg & (R1 & N6 & Ev) & Hu & Hs & Hlt). destruct lt.
+ rewrite <- (h0_eq ltac:(lia)). split; [destruct h; apply (OR Ev)|].
destruct h; cbn in Hs.
* rewrite Hs. cbn. rewrite sx32_small by lia. auto.
* split; [rewrite (den_off0 xv1 XR1); reflexivity|]. rewrite (denot_lit_U (EV xv1)). unfold U. rewrite (U_sext32 xv1), (U_off0 xv1 XR1). reflexivity.
* split; [rewrite (den_off0 xv1 XR1); reflexivity|]. rewrite (proj1 (proj2 Hs)). cbn. rewrite sx32_small by lia. reflexivity.
* split; [rewrite (den_off0 xv1 XR1); reflexivity|]. rewrite (proj1 (proj2 Hs)). cbn. rewrite sx32_small by lia. reflexivity.
+ destruct (NONE Hg) as [-> ->]. destruct h; auto.
Qed.
Lemma T1_post v ms2 : vsel v -> st_ok src0segs E1 (SST1 v) ms2 -> frame_of E1 (t1_mem v) mem1 (ms_mem ms2) ->
ms2 = mkst (ms_regs ms2) (Z_to_bv 64 PB) mem1 rom /\ at_PB (ms_regs ms2).
Proof.
intros Hv HS1 HF. pose proof (SST1_view v) as V. destruct (cview_regs _ _ _ _ _ _ V) as (Hpc & Hrv & Hmem & _).
pose proof (outs_denot v Hv) as (D4 & D2 & D0).
pose proof (reg_of _ _ _ 20 _ HS1 ltac:(lia) ltac:(reg_eq V 0%nat)) as G20.
pose proof (reg_of _ _ _ 18 _ HS1 ltac:(lia) ltac:(reg_eq V 1%nat)) as G18.
pose proof (reg_of _ _ _ 10 _ HS1 ltac:(lia) ltac:(reg_eq V 2%nat)) as G10.
pose proof (reg_of _ _ _ 2 _ HS1 ltac:(lia) ltac:(reg_eq V 3%nat)) as G2.
pose proof (reg_of _ _ _ 4 _ HS1 ltac:(lia) ltac:(reg_eq V 4%nat)) as G4.
pose proof (reg_of _ _ _ 8 _ HS1 ltac:(lia) ltac:(reg_eq V 5%nat)) as G8.
pose proof (reg_of _ _ _ 9 _ HS1 ltac:(lia) ltac:(reg_eq V 6%nat)) as G9.
pose proof (reg_of _ _ _ 19 _ HS1 ltac:(lia) ltac:(reg_eq V 7%nat)) as G19.
assert (GS : forall i, In i CSAVED -> getr (ms_regs ms2) (nat_to_reg i) = sv_denot E1 (SOff i 0)).
{ intros i Hi. pose proof (csaved_cases i Hi) as C.
assert (E : nth i (ss_regs (SST1 v)) (SLit 0) = SOff i 0).
{ decompose [or] C; subst i; [reg_eq V 8%nat | reg_eq V 9%nat | reg_eq V 10%nat | reg_eq V 11%nat | reg_eq V 12%nat | reg_eq V 13%nat | reg_eq V 14%nat | reg_eq V 15%nat]. }
exact (reg_of _ _ _ i _ HS1 ltac:(decompose [or] C; subst i; lia) E). }
assert (MM : ms_mem ms2 = mem1).
{ apply (frame_of_nowin E1 (t1_mem v)); [|exact HF]. destruct v as [| | | | |[| | |] ?]; repeat constructor. }
pose proof (st_ok_mkst src0segs _ _ _ HS1 Hrv) as SHAPE. rewrite Hpc, MM in SHAPE. clear V Hpc Hrv Hmem.
split; [exact SHAPE|]. split.
- change (20%bv : bv 5) with (nat_to_reg 20). rewrite G20. exact D4.
- change (18%bv : bv 5) with (nat_to_reg 18). rewrite G18. exact D2.
- change (10%bv : bv 5) with (nat_to_reg 10). rewrite G10. exact D0.
- change (8%bv : bv 5) with (nat_to_reg 8). rewrite G8. unfold E1. rewrite (den_off0 xv1 XR1), X8. reflexivity.
- change (9%bv : bv 5) with (nat_to_reg 9). rewrite G9. reflexivity.
- change (19%bv : bv 5) with (nat_to_reg 19). rewrite G19. reflexivity.
- change (2%bv : bv 5) with (nat_to_reg 2). rewrite G2. unfold E1. rewrite (den_off0 xv1 XR1), X2. reflexivity.
- change (4%bv : bv 5) with (nat_to_reg 4). rewrite G4. reflexivity.
- intros i Hi. rewrite (GS i Hi). unfold E1. rewrite (den_off0 xv1 XR1), xv1_reg by (pose proof (csaved_cases i Hi); lia).
rewrite Z_to_bv_bv_unsigned. apply (pa_cs _ _ _ _ _ AT). exact Hi.
Qed.
Theorem T1_SR :
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 PA) mem1 rom) md)
(fun c' => exists regs2, c' = mkCfg (mkst regs2 (Z_to_bv 64 PB) mem1 rom) md /\ at_PB regs2).
Proof.
pose proof PRE_facts as (MX & _). destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)) as (Hh & Hlz & _).
destruct vsel_exists as [v Hv].
eapply SR_mono; [eapply (T1_run v E1); [exact (T1_st_ok v Hv) | exact Hh | exact Hlz]|].
intros c' (ms2 & -> & HS2 & HF). cbn [ms_mem mkst] in HF.
destruct (T1_post v ms2 Hv HS2 HF) as [SHAPE POST].
exists (ms_regs ms2). split; [rewrite SHAPE at 1; reflexivity | exact POST].
Qed.
End T1.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
