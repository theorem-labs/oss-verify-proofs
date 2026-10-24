(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02 YK1j YK0v YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0b YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0u YO15 YO10 YO12 YO14 YO0t YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN02 YN2b YN25 YN26
YN2a YN2q YN2o YN0b YN07 YN0a YN08
YN0t YN2u YN2t YN0k YN0p YN2r YN2s
YN0u YN0v YN0r YN0s YN0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma lor_not_hi5 b : 0 <= b < 2 ^ 64 ->
Z.lor (Z.lxor b (2 ^ 64 - 1)) (2 ^ 64 - 32) = 2 ^ 64 - 1 - b mod 32.
Proof.
intros Hb.
assert (E1 : Z.lxor b (2 ^ 64 - 1) = Z.land (Z.lnot b) (Z.ones 64)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
change (2 ^ 64 - 1) with (Z.ones 64).
destruct (Z_lt_dec i 64).
- rewrite Z.ones_spec_low by lia. destruct (Z.testbit b i); reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite (Z.bits_above_log2 b i); [reflexivity| lia |].
destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|].
apply (Z.lt_le_trans _ 64); [|lia]. apply Z.log2_lt_pow2; lia. }
rewrite E1. change (2 ^ 64 - 32) with (Z.land (Z.lnot (Z.ones 5)) (Z.ones 64)).
rewrite <- Z.land_lor_distr_l, <- Z.lnot_land, Z.land_ones by lia.
rewrite Z.land_ones by lia. unfold Z.lnot. change (2 ^ 5) with 32.
pose proof (Z.mod_pos_bound b 32 ltac:(lia)).
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Definition usage_cell (k : nat) (v : Z) : mcell := MCell (LCtx (CTX_usage + 8 * Z.of_nat k)) 8 (VZ v).
Definition seq_cell (v : Z) : mcell := MCell (LCtx CTX_seq) 1 (VZ v).
Definition useq_cell (k : nat) (v : Z) : mcell := MCell (LCtx (CTX_unmap_seq + Z.of_nat k)) 1 (VZ v).
Lemma ctx_cells_usq s s' c :
st_init_done s' = st_init_done s -> st_mmap_counter s' = st_mmap_counter s -> st_free_meta_head s' = st_free_meta_head s ->
st_areas s' = st_areas s -> st_avail_meta s' = st_avail_meta s -> st_avail_meta_count s' = st_avail_meta_count s ->
st_avail_meta_area_count s' = st_avail_meta_area_count s -> st_meta_alloc_shift s' = st_meta_alloc_shift s ->
st_area_head s' = st_area_head s -> st_area_tail s' = st_area_tail s -> st_avail_meta_areas s' = st_avail_meta_areas s ->
st_brk s' = st_brk s -> st_active s' = st_active s -> st_bounces s' = st_bounces s ->
In c (ctx_cells s') ->
c = seq_cell (st_seq s') \/
(exists k, (k < 48)%nat /\ c = usage_cell k (nth k (st_usage s') 0)) \/
(exists k, (k < 32)%nat /\ c = useq_cell k (nth k (st_unmap_seq s') 0)) \/
In c (ctx_cells s).
Proof.
intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 Hc. unfold ctx_cells in *.
rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14 in Hc.
apply in_app_iff in Hc as [Hc|Hc].
- cbn [In] in Hc.
destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]];
try (right; right; right; apply in_app_iff; left; rewrite <- H; cbn; tauto).
left. symmetry. exact H.
- apply in_app_iff in Hc as [Hc|Hc]; [right; right; right; apply in_app_iff; right; apply in_app_iff; left; exact Hc|].
apply in_app_iff in Hc as [Hc|Hc].
+ apply in_map_iff in Hc as (k & <- & Hk). apply in_seq in Hk. right; left. exists k. split; [lia | reflexivity].
+ apply in_app_iff in Hc as [Hc|Hc].
* apply in_map_iff in Hc as (k & <- & Hk). apply in_seq in Hk. right; right; left. exists k. split; [lia | reflexivity].
* right; right; right. rewrite !in_app_iff. right; right; right; right. exact Hc.
Qed.
Section f.
Variables (X : list sptr) (U1 U : Z -> Z) (fuel : nat) (L : layout) (A s1 : astate) (g : sptr) (am1 : ameta).
Variables (regs regs1 : bvmap 5 word) (mem mem1 : word -> option byte) (md : Model) (gv : Z).
Variables (r : nat) (rg : YO0i.region).
Hypothesis NM : ntmid (g :: X) fuel L A s1 g regs regs1 mem mem1 md gv.
Hypothesis HI1 : Inv (g :: X) None U1 s1.
Hypothesis Mg1 : MT s1 g = Some (MUsed am1).
Hypothesis Hsc : 0 <= am_sc am1 < 64.
Hypothesis Hlast : 0 <= am_last am1 <= 31.
Hypothesis Hml : 0 < am_maplen am1.
Hypothesis Hmem : am_mem am1 = YO0i.SP r 0.
Hypothesis Hrg : region_of s1 r = Some rg /\ rg_live rg = true /\ rg_len rg = am_maplen am1 * PGSZ.
Hypothesis Eus : st_usage s1 = st_usage A.
Hypothesis AO1 : forall a, alloc_owned L s1 a -> alloc_owned L A a.
Let sc := am_sc am1.
Let G := ptr_addr L g.
Let SP0 := spZ regs.
Definition u : bool := sc <? 48.
Definition z : bool := st_seq s1 =? 255.
Definition b : bool := (7 <=? sc) && (sc <? 39).
Definition newseq : Z := if z then 1 else st_seq s1 + 1.
Definition s2 : astate := A_usg A sc am1 s1.
Definition s3 : astate := A_seq s2.
Definition s4 : astate := A_rec sc s3.
Definition mi : option (nat * Z) := Some (prid (am_mem am1), am_maplen am1 * 4096).
Definition MEMA : Z := ptr_addr L (am_mem am1).
Definition MP : Z := am_maplen am1 * 4096.
Hypothesis HI4 : Inv (g :: X) None U s4.
Lemma HL1 : layout_ok L s1. Proof. exact (nm_layout _ _ _ _ _ _ _ _ _ _ _ _ NM). Qed.
Lemma SO : syms_ok B1. Proof. exact (nm_syms _ _ _ _ _ _ _ _ _ _ _ _ NM). Qed.
Lemma Hctx : ly_ctx L = CTX. Proof. exact (nm_ctx _ _ _ _ _ _ _ _ _ _ _ _ NM). Qed.
Lemma MR1 : memrepX B1 (g :: X) L s1 mem1. Proof. exact (nm_rep _ _ _ _ _ _ _ _ _ _ _ _ NM). Qed.
Lemma ST1 : statics_ok B1 mem1. Proof. exact (nm_statics _ _ _ _ _ _ _ _ _ _ _ _ NM). Qed.
Lemma LG1 : ledger_ok B1 L s1 md. Proof. exact (nm_ledger _ _ _ _ _ _ _ _ _ _ _ _ NM). Qed.
Lemma g_facts2 : 4096 <= G /\ G + 40 <= alloc_ceiling /\ G mod 8 = 0 /\ (forall y, G <= y < G + 40 -> ~ in_img B1 y).
Proof. destruct (key_facts (g :: X) None U1 L s1 md HI1 LG1 g _ Mg1) as (A1 & A2 & A3 & A4 & _). unfold G. auto. Qed.
Lemma Ebits : meta_bits am1 = bits_enc (am_last am1) sc (am_maplen am1).
Proof. reflexivity. Qed.
Lemma mem_facts : 4096 <= MEMA /\ MEMA + MP <= alloc_ceiling /\ MEMA = ly_reg L r /\ 0 < MP < 2 ^ 47 /\ MEMA mod 4096 = 0 /\
0 <= meta_bits am1 < 2 ^ 64.
Proof.
destruct Hrg as (R1 & R2 & R3). destruct (lg_placed _ _ _ _ LG1 r rg R1 R2) as (Aal & A4096 & Aceil & _). pose proof (proj1 alloc_ceiling_val).
assert (EM : MEMA = ly_reg L r) by (unfold MEMA, ptr_addr, loc_addr; rewrite Hmem; cbn; lia).
rewrite R3 in Aceil. unfold PGSZ in *. unfold MP. rewrite EM.
repeat match goal with |- _ /\ _ => split end; try lia.
- rewrite Ebits. apply bits_nonneg; lia.
- rewrite Ebits. apply bits_lt64; lia.
Qed.
Lemma sp_facts2 :
SP0 mod 16 = 0 /\ alloc_ceiling + 96 + 96 * Z.of_nat fuel <= SP0 /\ SP0 < 2 ^ 63 /\
(forall x, SP0 - 96 * Z.of_nat (S fuel) <= x < SP0 -> writable_at src0segs mem1 x).
Proof.
pose proof (nm_spf _ _ _ _ _ _ _ _ _ _ _ _ NM) as (S1 & S2 & S3). pose proof (nm_stkw _ _ _ _ _ _ _ _ _ _ _ _ NM) as W.
unfold NT_FRAME in *. unfold SP0. split; [exact S1|]. split; [lia|]. split; [exact S3|]. intros x Hx. apply W. lia.
Qed.
Lemma ctx_facts : length (st_usage s1) = 48%nat /\ length (st_unmap_seq s1) = 32%nat /\ 0 <= st_seq s1 <= 255 /\
(forall v, In v (st_unmap_seq s1) -> 0 <= v <= 255).
Proof. pose proof (inv_ctx HI1) as (_ & Lu & Lq & _ & _ & Bq & _ & Bs & _). auto. Qed.
Definition xv1 (k : nat) : Z :=
if (k <? 32)%nat then bv_unsigned (getr regs1 (nat_to_reg k))
else match k with
| 43%nat => MEMA
| 46%nat => meta_bits am1
| 48%nat => sc
| 49%nat => CTX + 80 + 8 * sc
| 54%nat => usage_of A sc mod 2 ^ 64
| 56%nat => am_last am1
| 64%nat => st_seq s1
| _ => 0
end.
Lemma XR1 : forall k, 0 <= xv1 k < 2 ^ 64.
Proof.
intros k. pose proof mem_facts as (M1 & M2 & _ & M4 & _ & Hbits). pose proof ctx_facts as (_ & _ & Bs & _). pose proof (proj1 alloc_ceiling_val) as HCV.
unfold xv1. destruct (k <? 32)%nat; [apply u64_range|].
assert (M64 : forall q, 0 <= q mod 2 ^ 64 < 2 ^ 64) by (intros q; apply Z.mod_pos_bound; lia).
unfold CTX, src0_D_malloc_context. unfold sc in *.
do 65 (destruct k as [|k]; [first [apply M64 | lia] |]). lia.
Qed.
Lemma EG1 : xv1 10 = G.
Proof.
pose proof (nm_a0 _ _ _ _ _ _ _ _ _ _ _ _ NM) as R. pose proof g_facts2 as (G1 & G2 & _). pose proof (proj1 alloc_ceiling_val).
unfold xv1. cbn [Nat.ltb Nat.leb]. rewrite R. apply lit64_small. unfold G in *. lia.
Qed.
Lemma ESP1 : xv1 2 = SP0 - 96.
Proof.
pose proof (nm_sp _ _ _ _ _ _ _ _ _ _ _ _ NM) as R. pose proof sp_facts2 as (_ & S2 & S3 & _). pose proof (proj1 alloc_ceiling_val).
unfold xv1. cbn [Nat.ltb Nat.leb]. rewrite R. apply lit64_small. unfold SP0 in *. lia.
Qed.
Ltac facts1 := pose proof XR1 as XR0; pose proof EG1 as EG0; pose proof ESP1 as ESP0.
Lemma regs1_ok : regs_ok (EV xv1) (regs_lit [(18%nat, CTX)]) regs1.
Proof.
pose proof (nm_s2 _ _ _ _ _ _ _ _ _ _ _ _ NM) as R18.
apply regs_ok_lit. intros n Hn.
do 32 (destruct n as [|n]; [cbn [find fst Nat.eqb]; first [exact R18 | unfold xv1; cbn [Nat.ltb Nat.leb]; symmetry; apply Z_to_bv_bv_unsigned] |]). lia.
Qed.
Lemma atoms1_ok : atoms_ok (EV xv1) (m1_atoms u z).
Proof.
facts1. pose proof g_facts2 as (G1 & G2 & G8 & _). pose proof mem_facts as (M1 & M2 & _ & M4 & _ & Hbits). pose proof ctx_facts as (_ & _ & Bs & _).
pose proof (proj1 alloc_ceiling_val) as HCV.
assert (M64 : forall q, 0 <= q mod 2 ^ 64 <= 2 ^ 64 - 1) by (intros q; pose proof (Z.mod_pos_bound q (2 ^ 64) ltac:(lia)); lia).
unfold m1_atoms. apply atoms_ok_app.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite !(ew_EV xv1 XR0). unfold aNG. rewrite EG0.
unfold aGMEM, aGBITS, aSC, aLAST, aSEQ, xv1. cbn [Nat.ltb Nat.leb].
change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite ?Z.mod_1_r. unfold G, sc in *. repeat split; lia.
- unfold u. destruct (Z.ltb_spec sc 48); cbn [atoms_ok]; [|exact I].
unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite !(ew_EV xv1 XR0). unfold aACT, aUSG, xv1. cbn [Nat.ltb Nat.leb].
change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite ?Z.mod_1_r. pose proof (M64 (usage_of A sc)).
unfold CTX, src0_D_malloc_context. unfold sc in *. repeat split; try lia.
apply ctx_al8.
Qed.
Ltac den1 :=
let xr := match goal with H : forall k : nat, 0 <= xv1 k < 2 ^ 64 |- _ => H end in
cbn [sv_denot]; rewrite ?alu64_and, ?alu64_or, ?alu64_srl, ?alu64_sll, ?alu64_add, ?alu64_sub;
rewrite ?(ew_EV xv1 xr); unfold aNG, aGMEM, aGBITS, aSC, aACT, aUSG, aLAST, aSEQ; unfold xv1; cbn [Nat.ltb Nat.leb nat_to_reg]; rewrite ?Z.add_0_r.
Ltac weq := apply (proj2 (word_eq _ _)).
Ltac cprep := unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite ?branch_geu, ?branch_ltu, ?branch_eq, ?branch_ne.
Lemma alias1_ok : alias_ok (EV xv1) (m1_alias u).
Proof.
facts1. pose proof mem_facts as (_ & _ & _ & _ & _ & Hbits).
unfold m1_alias. cbn [alias_ok]. split.
- weq. unfold SCX. den1. rewrite !lit64_small by lia.
change (52 mod 64) with 52. change (58 mod 64) with 58. rewrite Ebits. apply bits_sc; unfold sc; lia.
- unfold u. destruct (Z.ltb_spec sc 48); cbn [alias_ok]; [|exact I]. split; [|exact I].
weq. den1. unfold CTX, src0_D_malloc_context. rewrite !lit64_small by lia.
change (3 mod 64) with 3. unfold sll64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite Z.mod_small by lia. unfold sc. lia.
Qed.
Lemma conds1_ok : conds_ok (EV xv1) (m1_conds u z).
Proof.
facts1. pose proof mem_facts as (_ & _ & _ & _ & _ & Hbits). pose proof ctx_facts as (_ & _ & Bs & _).
unfold m1_conds. cbn [conds_ok]. split; [|split; [|split; [|exact I]]].
- cprep. den1. rewrite !lit64_small by lia. change (12 mod 64) with 12. change (0 mod 2 ^ 64) with 0.
rewrite Ebits, bits_shiftr12 by (unfold sc; lia). apply negb_true_iff. apply Z.eqb_neq. lia.
- unfold u. destruct (Z.ltb_spec sc 48); cprep; den1; rewrite !lit64_small by lia; change (47 mod 2 ^ 64) with 47.
+ apply negb_true_iff. apply Z.ltb_ge. lia.
+ apply Z.ltb_lt. lia.
- unfold z. destruct (Z.eqb_spec (st_seq s1) 255); cprep; den1; rewrite !lit64_small by lia; change (255 mod 2 ^ 64) with 255.
+ apply Z.eqb_eq. lia.
+ apply negb_true_iff. apply Z.eqb_neq. lia.
Qed.
Lemma facts1_ok : facts_ok (EV xv1) (mkFacts (m1_atoms u z) (m1_conds u z) (m1_alias u)).
Proof. split; [apply atoms1_ok | split; [apply conds1_ok | apply alias1_ok]]. Qed.
Lemma g_bytes : bytes_are mem1 (G + 16) 8 MEMA /\ bytes_are mem1 (G + 32) 8 (meta_bits am1).
Proof.
assert (BY : forall dd w val, match val with VLo5 _ => False | _ => True end -> In (MCell (LMem (padd g dd)) w val) (meta_slot_cells g (Some (MUsed am1))) ->
bytes_are mem1 (G + dd) w (sval_num L val)).
{ intros dd w val Hv Hc kk Hkk. pose proof (key_cell (g :: X) None U1 L s1 mem1 HI1 MR1 g _ _ Mg1 Hc) as C. unfold cell_mem in C. cbn [mc_val mc_loc mc_w] in C.
rewrite loc_addr_padd in C. destruct val; first [exact (C kk Hkk) | destruct Hv]. }
split.
- exact (BY 16 8%nat (VP (am_mem am1)) I ltac:(cbn; tauto)).
- exact (BY 32 8%nat (VZ (meta_bits am1)) I ltac:(cbn; tauto)).
Qed.
Lemma seq_bytes : bytes_are mem1 (CTX + 912) 1 (st_seq s1).
Proof.
pose proof Hctx as HC.
assert (Hc : In (MCell (LCtx CTX_seq) 1 (VZ (st_seq s1))) (ctx_cells s1)) by (unfold ctx_cells; apply in_app_iff; left; cbn; tauto).
pose proof (CELL (g :: X) L s1 mem1 MR1 _ ltac:(unfold imageX; apply in_app_iff; left; exact Hc)) as C.
unfold cell_mem in C. cbn [mc_val mc_loc mc_w loc_addr sval_num] in C. rewrite HC in C. unfold CTX_seq in C. exact C.
Qed.
Lemma usage_bytes : sc < 48 -> bytes_are mem1 (CTX + 464 + 8 * sc) 8 (usage_of A sc).
Proof.
intros H48. pose proof (ctx_usage_cell (g :: X) L s1 mem1 Hctx MR1 (Z.to_nat sc) ltac:(unfold sc in *; lia)) as C.
rewrite Z2Nat.id in C by (unfold sc in *; lia). unfold usage_of, znth. rewrite <- Eus. exact C.
Qed.
Lemma rok_gM : region_ok src0segs (EV xv1) mem1 reg_gM.
Proof.
facts1. pose proof g_facts2 as (G1 & G2 & G8 & _). pose proof mem_facts as (M1 & M2 & _ & M4 & _ & Hbits). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof g_bytes as [B16 B32].
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_gM]; rewrite (base_val_EV _ XR0); unfold aNG; rewrite EG0; [unfold G in *; lia | unfold G in *; lia | intros o Ho; lia |].
repeat apply Forall_cons; [| | apply Forall_nil].
- apply (chunk_ok_val _ _ _ _ 8%N _ MEMA); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; lia | exact B16].
- apply (chunk_ok_val _ _ _ _ 8%N _ (meta_bits am1)); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; lia | exact B32].
Qed.
Lemma rok_seq : region_ok src0segs (EV xv1) mem1 (reg_seq true).
Proof.
facts1. pose proof SO as SO0. pose proof ctx_facts as (_ & _ & Bs & _). pose proof seq_bytes as B.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_seq base_val]; unfold CTX, src0_D_malloc_context; [lia | lia | |].
- intros o Ho. apply (ctx_writable mem1 SO0). unfold CTX, src0_D_malloc_context, CTX_SIZE. lia.
- apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 1%N _ (st_seq s1)); [apply (U_off0 _ XR0) | change (8 * Z.of_N 1) with 8; lia | rewrite Z.add_0_l; exact B].
Qed.
Lemma rok_m1 : Forall (region_ok src0segs (EV xv1) mem1) (m1_mem u z).
Proof.
facts1. pose proof SO as SO0. pose proof usage_bytes as UB.
assert (M64 : forall q, 0 <= q mod 2 ^ 64 < 2 ^ (8 * Z.of_N 8)) by (intros q; apply Z.mod_pos_bound; cbn; lia).
unfold m1_mem. apply Forall_app. split; [repeat apply Forall_cons; [apply rok_gM | apply rok_seq | apply Forall_nil]|].
apply Forall_app. split.
- unfold u. destruct (Z.ltb_spec sc 48); [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
pose proof (so_ctx_lo _ SO0) as CL. pose proof (so_ctx_hi _ SO0) as CH. cbn [ms_ctx src0_msyms] in CL, CH. fold CTX in CL, CH. unfold CTX_SIZE in CH. pose proof (proj1 alloc_ceiling_val).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_usgw]; rewrite (base_val_EV _ XR0); unfold aACT, xv1; cbn [Nat.ltb Nat.leb]; [unfold sc in *; lia | unfold sc in *; lia | |].
+ intros o Ho. apply (ctx_writable mem1 SO0). unfold CTX_SIZE. unfold sc in *. lia.
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ (usage_of A sc mod 2 ^ 64)); [apply (U_off0 _ XR0) | apply M64 |].
intros kk Hkk. rewrite le_byte_mod64. replace (CTX + 80 + 8 * sc + 384) with (CTX + 464 + 8 * sc) by lia. exact (UB ltac:(lia) kk Hkk).
- unfold z. destruct (Z.eqb_spec (st_seq s1) 255); [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_useq0 base_val]; unfold CTX, src0_D_malloc_context; [lia | lia | | apply Forall_nil].
intros o Ho. apply (ctx_writable mem1 SO0). unfold CTX, src0_D_malloc_context, CTX_SIZE. lia.
Qed.
Lemma pd1 : pairwise_disjoint (EV xv1) (m1_mem u z).
Proof.
facts1. pose proof g_facts2 as (G1 & G2 & G8 & Gimg). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof (off_img G Gimg) as GI.
unfold m1_mem, u, z.
destruct (sc <? 48) eqn:E48; [apply Z.ltb_lt in E48|apply Z.ltb_ge in E48]; destruct (st_seq s1 =? 255);
cbn [app pairwise_disjoint all_disjoint]; unfold extent_disjoint;
cbn [r_base r_lo r_hi reg_gM reg_seq reg_usgw reg_useq0]; rewrite !(base_val_EV _ XR0); cbn [base_val];
unfold aNG, aACT; rewrite EG0; unfold xv1; cbn [Nat.ltb Nat.leb];
unfold CTX, src0_D_malloc_context; unfold G, sc in *; repeat split; lia.
Qed.
Theorem mem1_ok : mem_ok src0segs (EV xv1) mem1 (m1_mem u z).
Proof. split; [unfold u, z; destruct (sc <? 48), (st_seq s1 =? 255); vm_compute; reflexivity|]. split; [apply rok_m1 | apply pd1]. Qed.
Theorem M1_entry_st_ok : st_ok src0segs (EV xv1) (ss_M1 u z) (mkst regs1 (Z_to_bv 64 XU) mem1 (seg_rom src0segs)).
Proof.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_M1 resv_denot].
repeat (split; [reflexivity|]). split; [apply regs1_ok|]. split; [apply mem1_ok | apply facts1_ok].
Qed.
Lemma chunk_ok_bytes xv m base off (w : N) e v :
chunk_ok src0segs (EV xv) m base (mkChunk off (CVal w e)) ->
bv_unsigned (sv_denot (EV xv) e) = v -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
bytes_are m (base + off) (N.to_nat w) v.
Proof.
intros Hc Hv Hr k Hk. destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (bb & Eb & Mb). cbn [c_off c_val cbyte] in Eb, Mb.
rewrite Mb. injection Eb as <-. f_equal. unfold byte_of_word, le_byte. rewrite Hv, Z_to_bv8_mod. f_equal. rewrite N_nat_Z. rewrite Z.mod_small by lia. reflexivity.
Qed.
Section h.
Variable msM : machine_state.
Hypothesis HSM : st_ok src0segs (EV xv1) (SSM1 u z) msM.
Hypothesis HFM : frame_of (EV xv1) (m1_mem u z) mem1 (ms_mem msM).
Let memM := ms_mem msM.
Let regsM := ms_regs msM.
Lemma shapeM : msM = mkst regsM (Z_to_bv 64 XM) memM (seg_rom src0segs).
Proof.
pose proof (SSM1_shape u z) as SH. pose proof HSM as HS. remember (SSM1 u z) as ss eqn:Ess. clear Ess.
destruct SH as (Hpc & Hrv & _). rewrite <- Hpc. apply (st_ok_mkst src0segs _ _ _ HS Hrv).
Qed.
Lemma newseq_range : 1 <= newseq <= 255.
Proof. pose proof ctx_facts as (_ & _ & Bs & _). unfold newseq, z. destruct (Z.eqb_spec (st_seq s1) 255); lia. Qed.
Lemma regsM_facts :
(forall k, In k ([1; 2; 8; 9; 10; 19]%nat ++ kept) -> getr regsM (nat_to_reg k) = getr regs1 (nat_to_reg k)) /\
getr regsM (nat_to_reg 11) = Z_to_bv 64 (sc - 7) /\ getr regsM (nat_to_reg 12) = Z_to_bv 64 newseq /\
getr regsM (nat_to_reg 13) = Z_to_bv 64 31 /\ getr regsM (nat_to_reg 18) = Z_to_bv 64 CTX.
Proof.
facts1. pose proof ctx_facts as (_ & _ & Bs & _).
pose proof (SSM1_shape u z) as SH. pose proof HSM as HS. remember (SSM1 u z) as ss eqn:Ess. clear Ess.
destruct SH as (Hpc & Hrv & Hview & _).
pose proof (fun rr => st_ok_reg src0segs _ _ msM rr HS) as RR.
unfold view, kept, keptU in Hview. cbn [map app] in Hview.
injection Hview as V1 V2 V8 V9 V10 V11 V12 V13 V18 V19 V3 V4 V20 V21 V22 V23 V24 V25 V26 V27.
assert (NR : forall k, (1 <= k <= 31)%nat -> nat_to_reg k = Z_to_bv 5 (Z.of_nat k)).
{ intros k Hk. clear -Hk. apply bv_eq. rewrite nat_to_reg_unsigned by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
assert (K : forall k ex (V : sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat k)) = ex), (1 <= k <= 31)%nat -> getr regsM (nat_to_reg k) = sv_denot (EV xv1) ex).
{ intros k ex V Hk. unfold regsM. rewrite (NR k Hk), (RR (Z_to_bv 5 (Z.of_nat k))), V. reflexivity. }
assert (KE : forall k (V : sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat k)) = SOff k 0), (1 <= k <= 31)%nat -> getr regsM (nat_to_reg k) = getr regs1 (nat_to_reg k)).
{ intros k V Hk. rewrite (K k _ V Hk), (den_off0 _ XR0). unfold xv1. replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). apply Z_to_bv_bv_unsigned. }
split; [| split; [| split; [| split]]].
- intros k Hk. cbn [In app] in Hk.
repeat (destruct Hk as [<-|Hk]; [eapply KE; [eassumption | lia] |]). destruct Hk.
- rewrite (K 11%nat _ V11 ltac:(lia)). cbn [sv_denot]. rewrite (ew_EV xv1 XR0). unfold aSC, xv1. cbn [Nat.ltb Nat.leb]. unfold sc. f_equal; lia.
- rewrite (K 12%nat _ V12 ltac:(lia)). unfold NEWSEQ, newseq, z. destruct (st_seq s1 =? 255); [reflexivity|].
rewrite (den_off _ XR0) by (unfold aSEQ, xv1; cbn [Nat.ltb Nat.leb]; lia). unfold aSEQ, xv1. cbn [Nat.ltb Nat.leb]. reflexivity.
- rewrite (K 13%nat _ V13 ltac:(lia)). reflexivity.
- rewrite (K 18%nat _ V18 ltac:(lia)). reflexivity.
Qed.
Lemma regionsM :
region_ok src0segs (EV xv1) memM reg_gM /\
region_ok src0segs (EV xv1) memM (YP09.mkRegion None (CTX + 912) (CTX + 913) (CTX + 912) (CTX + 913) [mkChunk (CTX + 912) (CVal 1 (NEWSEQ z))]) /\
(u = true -> region_ok src0segs (EV xv1) memM (YP09.mkRegion (Some aACT) 384 392 384 392
[mkChunk 384 (CVal 8 (SAlu ALU_ADD (SOff aUSG 0) (SAlu ALU_OR (SAlu ALU_XOR (SOff aGBITS 0) (SLit (-1))) (SLit (-32)))))])) /\
(z = true -> region_ok src0segs (EV xv1) memM (YP09.mkRegion None (CTX + 848) (CTX + 880) (CTX + 848) (CTX + 880)
[mkChunk (CTX + 872) (CVal 8 (SLit 0)); mkChunk (CTX + 864) (CVal 8 (SLit 0)); mkChunk (CTX + 856) (CVal 8 (SLit 0)); mkChunk (CTX + 848) (CVal 8 (SLit 0))])).
Proof.
pose proof (SSM1_shape u z) as SH. pose proof HSM as HS. remember (SSM1 u z) as ss eqn:Ess. clear Ess.
destruct SH as (_ & _ & _ & Hm). pose proof (st_ok_mem_ok _ _ _ _ HS) as (_ & ROK & _). rewrite Hm in ROK. unfold m1_mem_out in ROK.
apply Forall_app in ROK as [R1 R2]. apply Forall_app in R2 as [R2 R3].
apply Forall_cons_iff in R1 as [Ra R1]. apply Forall_cons_iff in R1 as [Rb _].
unfold memM. split; [exact Ra|]. split; [exact Rb|]. split.
- intros Eu. rewrite Eu in R2. apply Forall_cons_iff in R2 as [Rc _]. exact Rc.
- intros Ez. rewrite Ez in R3. apply Forall_cons_iff in R3 as [Rd _]. exact Rd.
Qed.
Lemma bytesM :
bytes_are memM (G + 16) 8 MEMA /\ bytes_are memM (G + 32) 8 (meta_bits am1) /\
bytes_are memM (CTX + 912) 1 newseq /\
(u = true -> bytes_are memM (CTX + 464 + 8 * sc) 8 (usage_of A sc - (am_last am1 + 1))) /\
(z = true -> forall k, 0 <= k < 32 -> mbyte src0segs memM (CTX + 848 + k) = Some (Z_to_bv 8 0)).
Proof.
facts1. pose proof mem_facts as (M1 & M2 & _ & M4 & _ & Hbits). pose proof newseq_range as NR. pose proof ctx_facts as (_ & _ & Bs & _). pose proof (proj1 alloc_ceiling_val) as HCV.
destruct regionsM as (Rg & Rs & Ru & Rz).
destruct Rg as (_ & _ & _ & Cg). cbn [r_chunks r_base reg_gM] in Cg. rewrite (base_val_EV _ XR0) in Cg. unfold aNG in Cg. rewrite EG0 in Cg.
apply Forall_cons_iff in Cg as [C16 Cg]. apply Forall_cons_iff in Cg as [C32 _].
destruct Rs as (_ & _ & _ & Cs). cbn [r_chunks r_base base_val] in Cs. apply Forall_cons_iff in Cs as [Cs _].
split; [apply (chunk_ok_bytes xv1 memM G 16 8 _ _ C16); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; unfold MEMA in *; lia]|].
split; [apply (chunk_ok_bytes xv1 memM G 32 8 _ _ C32); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; lia]|].
split.
{ rewrite <- (Z.add_0_l (CTX + 912)). apply (chunk_ok_bytes xv1 memM 0 (CTX + 912) 1 _ _ Cs); [| change (8 * Z.of_N 1) with 8; lia].
unfold NEWSEQ, newseq, z. destruct (st_seq s1 =? 255); [apply U_lit|]. rewrite (U_off _ XR0) by (unfold aSEQ, xv1; cbn [Nat.ltb Nat.leb]; lia).
unfold aSEQ, xv1. cbn [Nat.ltb Nat.leb]. reflexivity. }
split.
- intros Eu. pose proof Eu as Eu'. unfold u in Eu'. apply Z.ltb_lt in Eu'.
destruct (Ru Eu) as (_ & _ & _ & Cu). cbn [r_chunks r_base] in Cu. rewrite (base_val_EV _ XR0) in Cu. apply Forall_cons_iff in Cu as [Cu _].
unfold aACT, xv1 in Cu. cbn [Nat.ltb Nat.leb] in Cu.
replace (CTX + 464 + 8 * sc) with (CTX + 80 + 8 * sc + 384) by lia.
intros kk Hkk. rewrite <- le_byte_mod64.
apply (chunk_ok_bytes xv1 memM _ 384 8 _ _ Cu); [| apply Z.mod_pos_bound; cbn; lia | exact Hkk].
change (sv_denot (EV xv1) (SAlu ALU_ADD (SOff aUSG 0) (SAlu ALU_OR (SAlu ALU_XOR (SOff aGBITS 0) (SLit (-1))) (SLit (-32))))) with
(alu64 ALU_ADD (sv_denot (EV xv1) (SOff aUSG 0)) (alu64 ALU_OR (alu64 ALU_XOR (sv_denot (EV xv1) (SOff aGBITS 0)) (sv_denot (EV xv1) (SLit (-1)))) (sv_denot (EV xv1) (SLit (-32))))).
rewrite alu64_add, alu64_or, alu64_xor, !(U_off0 _ XR0), !U_lit. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). change ((-32) mod 2 ^ 64) with (2 ^ 64 - 32).
unfold aUSG, aGBITS, xv1. cbn [Nat.ltb Nat.leb]. rewrite lor_not_hi5 by lia. rewrite Ebits, bits_mod32 by (unfold sc; lia).
unfold add64. rewrite Zplus_mod_idemp_l. replace (usage_of A sc + (2 ^ 64 - 1 - am_last am1)) with ((usage_of A sc - (am_last am1 + 1)) + 1 * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. reflexivity.
- intros Ez. destruct (Rz Ez) as (_ & _ & _ & Cz). cbn [r_chunks r_base base_val] in Cz.
apply Forall_cons_iff in Cz as [C72 Cz]. apply Forall_cons_iff in Cz as [C64 Cz]. apply Forall_cons_iff in Cz as [C56 Cz]. apply Forall_cons_iff in Cz as [C48 _].
assert (ZB : forall off k, chunk_ok src0segs (EV xv1) memM 0 (mkChunk off (CVal 8 (SLit 0))) -> 0 <= k < 8 -> mbyte src0segs memM (off + k) = Some (Z_to_bv 8 0)).
{ intros off k Hc Hk. destruct (Hc k ltac:(cbn; lia)) as (bb & Eb & Mb). cbn [c_off c_val cbyte] in Eb, Mb. rewrite Z.add_0_l in Mb. rewrite Mb.
injection Eb as <-. f_equal. unfold byte_of_word. change (bv_unsigned (sv_denot (EV xv1) (SLit 0))) with 0. rewrite Z.shiftr_0_l. reflexivity. }
intros k Hk.
destruct (Z_lt_dec k 8); [replace (CTX + 848 + k) with (CTX + 848 + k) by lia; apply (ZB _ k C48); lia|].
destruct (Z_lt_dec k 16); [replace (CTX + 848 + k) with (CTX + 856 + (k - 8)) by lia; apply (ZB _ (k - 8) C56); lia|].
destruct (Z_lt_dec k 24); [replace (CTX + 848 + k) with (CTX + 864 + (k - 16)) by lia; apply (ZB _ (k - 16) C64); lia|].
replace (CTX + 848 + k) with (CTX + 872 + (k - 24)) by lia. apply (ZB _ (k - 24) C72); lia.
Qed.
Definition xv2 (k : nat) : Z :=
if (k <? 32)%nat then bv_unsigned (getr regsM (nat_to_reg k))
else match k with
| 43%nat => MEMA
| 46%nat => meta_bits am1
| 57%nat => MP
| _ => 0
end.
Lemma XR2 : forall k, 0 <= xv2 k < 2 ^ 64.
Proof.
intros k. pose proof mem_facts as (M1 & M2 & _ & M4 & _ & Hbits). pose proof (proj1 alloc_ceiling_val) as HCV.
unfold xv2. destruct (k <? 32)%nat; [apply u64_range|].
unfold MEMA, MP in *. do 58 (destruct k as [|k]; [lia |]). lia.
Qed.
Lemma EG2 : xv2 10 = G.
Proof.
pose proof regsM_facts as (RK & _). pose proof (nm_a0 _ _ _ _ _ _ _ _ _ _ _ _ NM) as R. pose proof g_facts2 as (G1 & G2 & _). pose proof (proj1 alloc_ceiling_val).
unfold xv2. cbn [Nat.ltb Nat.leb]. rewrite (RK 10%nat ltac:(cbn; tauto)), R. apply lit64_small. unfold G in *. lia.
Qed.
Lemma E11 : xv2 11 = (sc - 7) mod 2 ^ 64.
Proof.
pose proof regsM_facts as (_ & R & _). unfold xv2. cbn [Nat.ltb Nat.leb]. rewrite R. rewrite Z_to_bv_unsigned. reflexivity.
Qed.
Lemma E12 : xv2 12 = newseq.
Proof.
pose proof regsM_facts as (_ & _ & R & _). pose proof newseq_range. unfold xv2. cbn [Nat.ltb Nat.leb]. rewrite R. apply lit64_small. lia.
Qed.
Ltac facts2 := pose proof XR2 as XR0; pose proof EG2 as EG0; pose proof E11 as E110; pose proof E12 as E120.
Lemma sc7 : (b = true -> (sc - 7) mod 2 ^ 64 = sc - 7 /\ 7 <= sc <= 38) /\ (b = false -> 31 < (sc - 7) mod 2 ^ 64).
Proof.
unfold b. split; intros E.
- apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite Z.mod_small by lia. lia.
- apply Bool.andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E].
+ replace (sc - 7) with ((sc - 7 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small; unfold sc in *; lia.
+ rewrite Z.mod_small; unfold sc in *; lia.
Qed.
Lemma regs2_ok : regs_ok (EV xv2) (regs_lit [(13%nat, 31); (18%nat, CTX)]) regsM.
Proof.
pose proof regsM_facts as (_ & _ & _ & R13 & R18).
apply regs_ok_lit. intros n Hn.
do 32 (destruct n as [|n]; [cbn [find fst Nat.eqb]; first [exact R13 | exact R18 | unfold xv2; cbn [Nat.ltb Nat.leb]; symmetry; apply Z_to_bv_bv_unsigned] |]). lia.
Qed.
Lemma facts2_ok : facts_ok (EV xv2) (mkFacts (m2_atoms b) (m2_conds b) m2_alias).
Proof.
pose proof (proj1 alloc_ceiling_val) as ACV_p9.
facts2. pose proof g_facts2 as (G1 & G2 & G8 & _). pose proof mem_facts as (M1 & M2 & _ & M4 & M5 & Hbits). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof newseq_range as NR. pose proof sc7 as [B1' B2'].
unfold facts_ok. cbn [YP0m.f_atoms YP0m.f_conds YP0m.f_alias]. split; [|split].
- unfold m2_atoms.
destruct b; [destruct (B1' eq_refl) as [E7 R7] | pose proof (B2' eq_refl); pose proof (Z.mod_pos_bound (sc - 7) (2 ^ 64) ltac:(lia))];
cbn [atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite !(ew_EV xv2 XR0); unfold aNG; rewrite EG0, E110, E120; rewrite ?E7;
unfold aGMEM, aGBITS, aMP, xv2; cbn [Nat.ltb Nat.leb];
change (2 ^ 3) with 8; change (2 ^ 0) with 1; change (2 ^ 12) with 4096; rewrite ?Z.mod_1_r; unfold G, MEMA, MP in *;
repeat split; try lia; apply Z_mod_mult.
- unfold m2_conds. pose proof (Z.mod_pos_bound (sc - 7) (2 ^ 64) ltac:(lia)) as MB.
destruct b; cbn [conds_ok]; (split; [|exact I]); cprep; cbn [sv_denot]; rewrite (ew_EV xv2 XR0), !Z.add_0_r, E110, !lit64_small by lia.
+ destruct (B1' eq_refl) as [E7 R7]. rewrite E7. apply negb_true_iff. apply Z.ltb_ge. lia.
+ pose proof (B2' eq_refl). apply Z.ltb_lt. lia.
- unfold m2_alias. cbn [alias_ok]. split; [|exact I]. weq.
change (sv_denot (EV xv2) (SAlu ALU_AND (SOff aGBITS 0) (SLit (-4096)))) with (alu64 ALU_AND (sv_denot (EV xv2) (SOff aGBITS 0)) (sv_denot (EV xv2) (SLit (-4096)))).
rewrite alu64_and, !(U_off0 _ XR0), U_lit. change ((-4096) mod 2 ^ 64) with (2 ^ 64 - 4096). unfold aGBITS, aMP, xv2. cbn [Nat.ltb Nat.leb].
unfold MP in *. rewrite Ebits, bits_maplen_bytes by (unfold sc in *; lia). reflexivity.
Qed.
Lemma mem2_ok : mem_ok src0segs (EV xv2) memM (m2_mem b).
Proof.
facts2. pose proof SO as SO0. pose proof g_facts2 as (G1 & G2 & G8 & Gimg). pose proof mem_facts as (M1 & M2 & _ & M4 & M5 & Hbits). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof (off_img G Gimg) as GI. pose proof sc7 as [B1' B2']. pose proof bytesM as (B16 & B32 & _).
split; [destruct b; vm_compute; reflexivity|]. split.
- unfold m2_mem. apply Forall_app. split.
+ apply Forall_cons; [|apply Forall_nil].
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_gM]; rewrite (base_val_EV _ XR0); unfold aNG; rewrite EG0; [unfold G in *; lia | unfold G in *; lia | intros o Ho; lia |].
repeat apply Forall_cons; [| | apply Forall_nil].
* apply (chunk_ok_val _ _ _ _ 8%N _ MEMA); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; unfold MEMA in *; lia | exact B16].
* apply (chunk_ok_val _ _ _ _ 8%N _ (meta_bits am1)); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; lia | exact B32].
+ destruct b; [|apply Forall_nil]. destruct (B1' eq_refl) as [E7 R7]. apply Forall_cons; [|apply Forall_nil].
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_useqb]; rewrite (base_val_EV _ XR0), E110, E7; unfold CTX, src0_D_malloc_context; [lia | lia | | apply Forall_nil].
intros o Ho. apply (ctx_writable memM SO0). unfold CTX, src0_D_malloc_context, CTX_SIZE. lia.
- unfold m2_mem. destruct b; cbn [app pairwise_disjoint all_disjoint]; [|split; exact I]. destruct (B1' eq_refl) as [E7 R7].
unfold extent_disjoint. cbn [r_base r_lo r_hi reg_gM reg_useqb]. rewrite !(base_val_EV _ XR0). unfold aNG. rewrite EG0, E110, E7.
unfold CTX, src0_D_malloc_context. unfold G in *. repeat split; lia.
Qed.
Theorem M2_entry_st_ok : st_ok src0segs (EV xv2) (ss_M2 b) msM.
Proof.
rewrite shapeM. unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_M2 resv_denot].
repeat (split; [reflexivity|]). split; [apply regs2_ok|]. split; [apply mem2_ok | apply facts2_ok].
Qed.
Section j.
Variable ms3 : machine_state.
Hypothesis HS3 : st_ok src0segs (EV xv2) (SSM2 b) ms3.
Hypothesis HF3 : frame_of (EV xv2) (m2_mem b) memM (ms_mem ms3).
Let mem3 := ms_mem ms3.
Let regs3 := ms_regs ms3.
Lemma shape3 : ms3 = mkst regs3 (Z_to_bv 64 XF) mem3 (seg_rom src0segs).
Proof.
pose proof (SSM2_shape b) as SH. pose proof HS3 as HS. remember (SSM2 b) as ss eqn:Ess. clear Ess.
destruct SH as (Hpc & Hrv & _). rewrite <- Hpc. apply (st_ok_mkst src0segs _ _ _ HS Hrv).
Qed.
Lemma regs3_facts :
(forall k, In k ([1; 2; 8; 9; 10; 19]%nat ++ kept) -> getr regs3 (nat_to_reg k) = getr regs1 (nat_to_reg k)) /\
getr regs3 (nat_to_reg 11) = Z_to_bv 64 MP /\ getr regs3 (nat_to_reg 12) = Z_to_bv 64 MEMA /\ getr regs3 (nat_to_reg 18) = Z_to_bv 64 CTX.
Proof.
facts2. pose proof regsM_facts as (RK & _).
pose proof (SSM2_shape b) as SH. pose proof HS3 as HS. remember (SSM2 b) as ss eqn:Ess. clear Ess.
destruct SH as (Hpc & Hrv & Hview & _).
pose proof (fun rr => st_ok_reg src0segs _ _ ms3 rr HS) as RR.
unfold view, kept, keptU in Hview. cbn [map app] in Hview.
injection Hview as V1 V2 V8 V9 V10 V11 V12 V18 V19 V3 V4 V20 V21 V22 V23 V24 V25 V26 V27.
assert (NR : forall k, (1 <= k <= 31)%nat -> nat_to_reg k = Z_to_bv 5 (Z.of_nat k)).
{ intros k Hk. clear -Hk. apply bv_eq. rewrite nat_to_reg_unsigned by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
assert (K : forall k ex (V : sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat k)) = ex), (1 <= k <= 31)%nat -> getr regs3 (nat_to_reg k) = sv_denot (EV xv2) ex).
{ intros k ex V Hk. unfold regs3. rewrite (NR k Hk), (RR (Z_to_bv 5 (Z.of_nat k))), V. reflexivity. }
assert (KE : forall k (V : sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat k)) = SOff k 0), (1 <= k <= 31)%nat -> In k ([1; 2; 8; 9; 10; 19]%nat ++ kept) -> getr regs3 (nat_to_reg k) = getr regs1 (nat_to_reg k)).
{ intros k V Hk HK. rewrite (K k _ V Hk), (den_off0 _ XR0). unfold xv2. replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite Z_to_bv_bv_unsigned. apply RK. exact HK. }
split; [| split; [| split]].
- intros k Hk. pose proof Hk as Hk'. cbn [In app] in Hk.
repeat (destruct Hk as [<-|Hk]; [eapply KE; [eassumption | lia | exact Hk'] |]). destruct Hk.
- rewrite (K 11%nat _ V11 ltac:(lia)), (den_off0 _ XR0). reflexivity.
- rewrite (K 12%nat _ V12 ltac:(lia)), (den_off0 _ XR0). reflexivity.
- rewrite (K 18%nat _ V18 ltac:(lia)). reflexivity.
Qed.
Lemma frame3 a : 0 <= a < 2 ^ 64 -> ~ (b = true /\ a = CTX + 841 + sc) -> mem3 (Z_to_bv 64 a) = memM (Z_to_bv 64 a).
Proof.
facts2. pose proof sc7 as [B1' _]. intros Ha Hn. unfold mem3. apply (HF3 (Z_to_bv 64 a)). intros (rr & Hr & Hin). apply Hn.
rewrite Z_to_bv_unsigned in Hin. unfold bv_wrap in Hin. change (bv_modulus 64) with (2 ^ 64) in Hin. rewrite Z.mod_small in Hin by lia.
unfold m2_mem in Hr. apply in_app_iff in Hr as [Hr|Hr].
- destruct Hr as [<-|[]]. cbn [reg_gM r_base r_wlo r_whi] in Hin. lia.
- destruct b; [|destruct Hr]. destruct Hr as [<-|[]]. destruct (B1' eq_refl) as [E7 _].
cbn [reg_useqb r_base r_wlo r_whi] in Hin. rewrite (base_val_EV _ XR0), E110, E7 in Hin. split; [reflexivity | lia].
Qed.
Lemma byte3 : b = true -> mbyte src0segs mem3 (CTX + 841 + sc) = Some (Z_to_bv 8 newseq).
Proof.
facts2. pose proof sc7 as [B1' _]. pose proof newseq_range as NR. intros Eb. destruct (B1' Eb) as [E7 _].
pose proof (SSM2_shape b) as SH. pose proof HS3 as HS. remember (SSM2 b) as ss eqn:Ess. clear Ess.
destruct SH as (_ & _ & _ & Hm). pose proof (st_ok_mem_ok _ _ _ _ HS) as (_ & ROK & _). rewrite Hm in ROK. unfold m2_mem_out in ROK.
apply Forall_app in ROK as [_ R2]. rewrite Eb in R2. apply Forall_cons_iff in R2 as [Rq _].
destruct Rq as (_ & _ & _ & Cq). cbn [r_chunks r_base] in Cq. rewrite (base_val_EV _ XR0), E110, E7 in Cq. apply Forall_cons_iff in Cq as [Cq _].
pose proof (chunk_ok_bytes xv2 mem3 _ _ 1 _ newseq Cq ltac:(rewrite (U_off0 _ XR0); exact E120) ltac:(change (8 * Z.of_N 1) with 8; lia) 0%nat ltac:(lia)) as B0.
cbn [Z.of_nat] in B0. rewrite Z.add_0_r in B0. replace (CTX + 841 + sc) with (sc - 7 + (CTX + 848)) by lia. rewrite B0. f_equal.
unfold le_byte. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.mod_mod by lia. apply Z_to_bv8_mod.
Qed.
Lemma s4_facts :
st_usage s4 = (if u then zset sc (usage_of A sc - (am_last am1 + 1)) (st_usage s1) else st_usage s1) /\
st_seq s4 = newseq /\
st_unmap_seq s4 = (if b then zset (sc - 7) newseq else fun l => l) (if z then repeat 0 32 else st_unmap_seq s1) /\
st_metas s4 = st_metas s1 /\ st_regions s4 = st_regions s1 /\ st_areas s4 = st_areas s1 /\ st_active s4 = st_active s1 /\
st_bounces s4 = st_bounces s1 /\ st_free_meta_head s4 = st_free_meta_head s1 /\ st_brk s4 = st_brk s1 /\
st_init_done s4 = st_init_done s1 /\ st_mmap_counter s4 = st_mmap_counter s1 /\ st_avail_meta s4 = st_avail_meta s1 /\
st_avail_meta_count s4 = st_avail_meta_count s1 /\ st_avail_meta_area_count s4 = st_avail_meta_area_count s1 /\
st_meta_alloc_shift s4 = st_meta_alloc_shift s1 /\ st_area_head s4 = st_area_head s1 /\ st_area_tail s4 = st_area_tail s1 /\
st_avail_meta_areas s4 = st_avail_meta_areas s1.
Proof.
unfold s4, s3, s2, A_rec, A_seq, A_usg, bounce_idx, newseq, u, z, b. fold sc.
destruct (sc <? 48); cbn [st_seq set_usage]; destruct (st_seq s1 =? 255); cbn [st_seq st_unmap_seq set_seq set_unmap_seq set_usage];
destruct ((7 <=? sc) && (sc <? 39)); repeat split; reflexivity.
Qed.
Lemma footprint_s4 : footprint s4 = footprint s1.
Proof. pose proof s4_facts as (_&_&_&_&Er&Ea&_). exact (footprint_regions_areas s1 s4 Er Ea). Qed.
Definition NEWu : list mcell := if u then [usage_cell (Z.to_nat sc) (usage_of A sc - (am_last am1 + 1))] else [].
Definition NEWs : list mcell := [seq_cell newseq].
Definition NEWq : list mcell :=
if z then map (fun k => useq_cell k (nth k (st_unmap_seq s4) 0)) (seq 0 32)
else if b then [useq_cell (Z.to_nat (sc - 7)) newseq] else [].
Definition NEW : list mcell := NEWu ++ NEWs ++ NEWq.
Lemma useq_val k : (k < 32)%nat -> nth k (st_unmap_seq s4) 0 = if (b && Nat.eqb k (Z.to_nat (sc - 7)))%bool then newseq else if z then 0 else nth k (st_unmap_seq s1) 0.
Proof.
intros Hk. pose proof s4_facts as (_&_&Eq&_). pose proof ctx_facts as (_ & Lq & _). pose proof sc7 as [B1' _]. rewrite Eq.
destruct b.
- destruct (B1' eq_refl) as [_ R7]. unfold zset. rewrite nth_zupd.
destruct z; [rewrite repeat_length | rewrite Lq]; (replace (Nat.ltb (Z.to_nat (sc - 7)) 32) with true by (symmetry; apply Nat.ltb_lt; lia)); rewrite andb_true_r; cbn [andb];
destruct (Nat.eqb k (Z.to_nat (sc - 7))); try reflexivity. apply nth_repeat.
- cbn [andb]. destruct z; [apply nth_repeat | reflexivity].
Qed.
Lemma cells2 c : In c (imageX (g :: X) s4 ++ tail_cellsX (g :: X) s4) -> In c NEW \/ In c (imageX (g :: X) s1 ++ tail_cellsX (g :: X) s1).
Proof.
pose proof s4_facts as (Eu&Es&Eq&Em&Er&Ea&Eac&Eb&Ef&Ebk&E1&E2&E3&E4&E5&E6&E7&E8&E9). pose proof ctx_facts as (Lu & Lq & _). pose proof sc7 as [B1' _].
pose proof useq_val as UV.
assert (EUM : used_metasX (g :: X) s4 = used_metasX (g :: X) s1) by (unfold used_metasX, used_metas; rewrite Em; reflexivity).
intros Hc. apply in_app_iff in Hc as [Hc|Hc].
2:{ right. apply in_app_iff. right. unfold tail_cellsX in *. rewrite EUM in Hc. exact Hc. }
unfold imageX in Hc. rewrite EUM, Ea, (areas_cells_ext' s1 s4 _ Em) in Hc.
apply in_app_iff in Hc as [Hc|Hc].
2:{ right. apply in_app_iff. left. unfold imageX. apply in_app_iff. right. exact Hc. }
destruct (ctx_cells_usq s1 s4 c E1 E2 Ef Ea E3 E4 E5 E6 E7 E8 E9 Ebk Eac Eb Hc) as [-> | [(k & Hk & ->) | [(k & Hk & ->) | Hold]]].
- left. unfold NEW, NEWs. rewrite Es. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
- rewrite Eu. unfold NEW, NEWu, u in *. destruct (Z.ltb_spec sc 48).
+ unfold zset. rewrite nth_zupd, Lu. destruct (Nat.eqb_spec k (Z.to_nat sc)).
* replace (Nat.ltb (Z.to_nat sc) 48) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb]. left. apply in_app_iff. left. subst k. left. reflexivity.
* cbn [andb]. right. apply in_app_iff. left. unfold imageX. apply in_app_iff. left. unfold ctx_cells. rewrite !in_app_iff. right; right; left.
apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia].
+ right. apply in_app_iff. left. unfold imageX. apply in_app_iff. left. unfold ctx_cells. rewrite !in_app_iff. right; right; left.
apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia].
- unfold NEW, NEWq. destruct z.
+ left. apply in_app_iff. right. apply in_app_iff. right. apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia].
+ rewrite (UV k Hk). destruct b.
* destruct (B1' eq_refl) as [_ R7]. destruct (Nat.eqb_spec k (Z.to_nat (sc - 7))); cbn [andb].
{ left. apply in_app_iff. right. apply in_app_iff. right. subst k. left. reflexivity. }
right. apply in_app_iff. left. unfold imageX. apply in_app_iff. left. unfold ctx_cells. rewrite !in_app_iff. right; right; right; left.
apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia].
* cbn [andb]. right. apply in_app_iff. left. unfold imageX. apply in_app_iff. left. unfold ctx_cells. rewrite !in_app_iff. right; right; right; left.
apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia].
- right. apply in_app_iff. left. unfold imageX. apply in_app_iff. left. exact Hold.
Qed.
Lemma new_home2 c : In c NEW -> In c (areas_cells s4 (st_areas s4)) \/ In c (ctx_cells s4).
Proof.
pose proof s4_facts as (Eu&Es&Eq&_). pose proof ctx_facts as (Lu & Lq & _). pose proof sc7 as [B1' _]. pose proof useq_val as UV.
intros Hn. right. unfold NEW, NEWu, NEWs, NEWq in Hn. unfold ctx_cells. rewrite !in_app_iff.
apply in_app_iff in Hn as [Hn|Hn]; [|apply in_app_iff in Hn as [Hn|Hn]].
- unfold u in *. destruct (Z.ltb_spec sc 48); [|destruct Hn]. destruct Hn as [<-|[]]. right; right; left.
apply in_map_iff. exists (Z.to_nat sc). split; [|apply in_seq; lia]. unfold usage_cell. f_equal. rewrite Eu. unfold zset. rewrite nth_zupd, Nat.eqb_refl, Lu.
replace (Nat.ltb (Z.to_nat sc) 48) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
- destruct Hn as [<-|[]]. left. rewrite <- Es. cbn. tauto.
- right; right; right; left. destruct z.
+ apply in_map_iff in Hn as (k & <- & Hk). apply in_map_iff. exists k. auto.
+ destruct b; [|destruct Hn]. destruct Hn as [<-|[]]. destruct (B1' eq_refl) as [_ R7]. apply in_map_iff. exists (Z.to_nat (sc - 7)).
split; [|apply in_seq; lia]. unfold useq_cell. f_equal. rewrite (UV (Z.to_nat (sc - 7)) ltac:(lia)). rewrite Nat.eqb_refl. reflexivity.
Qed.
Lemma new_mem2 c : In c NEW -> cell_mem B1 L mem3 c.
Proof.
pose proof Hctx as HC. pose proof bytesM as (_ & _ & Bs & Bu & Bz). pose proof sc7 as [B1' _]. pose proof useq_val as UV. pose proof newseq_range as NR.
pose proof frame3 as F3. pose proof byte3 as Y3. pose proof ctx_facts as (Lu & Lq & _ & Bq).
assert (F3' : forall a, CTX <= a < CTX + CTX_SIZE -> ~ (b = true /\ a = CTX + 841 + sc) -> mbyte src0segs mem3 a = mbyte src0segs memM a).
{ intros a Ha Hn. unfold mbyte. rewrite (F3 a ltac:(unfold CTX, src0_D_malloc_context, CTX_SIZE in Ha; lia) Hn). reflexivity. }
intros Hn. unfold NEW, NEWu, NEWs, NEWq in Hn.
apply in_app_iff in Hn as [Hn|Hn]; [|apply in_app_iff in Hn as [Hn|Hn]].
- unfold u in *. destruct (Z.ltb_spec sc 48); [|destruct Hn]. destruct Hn as [<-|[]].
unfold usage_cell, cell_mem. cbn [mc_val mc_loc mc_w sval_num loc_addr]. rewrite HC. unfold CTX_usage. rewrite Z2Nat.id by lia.
intros k Hk. rewrite F3'; [| unfold CTX_SIZE; lia | intros [_ E]; lia]. replace (CTX + (464 + 8 * sc) + Z.of_nat k) with (CTX + 464 + 8 * sc + Z.of_nat k) by lia. exact (Bu eq_refl k Hk).
- destruct Hn as [<-|[]]. unfold seq_cell, cell_mem. cbn [mc_val mc_loc mc_w sval_num loc_addr]. rewrite HC. unfold CTX_seq.
intros k Hk. rewrite F3'; [| unfold CTX_SIZE; lia | intros [_ E]; lia]. exact (Bs k Hk).
- assert (ONE : forall k v, (k < 32)%nat -> 0 <= v < 256 -> mbyte src0segs mem3 (CTX + 848 + Z.of_nat k) = Some (Z_to_bv 8 v) -> cell_mem B1 L mem3 (useq_cell k v)).
{ intros k v Hk Hv Hb. unfold useq_cell, cell_mem. cbn [mc_val mc_loc mc_w sval_num loc_addr]. rewrite HC. unfold CTX_unmap_seq.
intros kk Hkk. destruct kk; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
enough (E : mbyte src0segs mem3 (CTX + (848 + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte v 1 0))) by exact E.
replace (CTX + (848 + Z.of_nat k)) with (CTX + 848 + Z.of_nat k) by lia. rewrite Hb. f_equal. unfold le_byte. rewrite Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.mod_mod by lia. rewrite Z.mod_small by lia. reflexivity. }
destruct z.
+ apply in_map_iff in Hn as (k & <- & Hk). apply in_seq in Hk. apply ONE; [lia | |].
* rewrite (UV k ltac:(lia)). destruct (b && Nat.eqb k (Z.to_nat (sc - 7)))%bool; lia.
* rewrite (UV k ltac:(lia)). destruct b.
-- destruct (B1' eq_refl) as [_ R7]. destruct (Nat.eqb_spec k (Z.to_nat (sc - 7))); cbn [andb].
++ subst k. rewrite Z2Nat.id by lia. replace (CTX + 848 + (sc - 7)) with (CTX + 841 + sc) by lia. exact (Y3 eq_refl).
++ rewrite F3'; [| unfold CTX_SIZE; lia | intros [_ E]; lia]. apply (Bz eq_refl). lia.
-- cbn [andb]. rewrite F3'; [| unfold CTX_SIZE; lia | intros [E _]; discriminate]. apply (Bz eq_refl). lia.
+ destruct b; [|destruct Hn]. destruct Hn as [<-|[]]. destruct (B1' eq_refl) as [_ R7]. apply ONE; [lia | lia |].
rewrite Z2Nat.id by lia. replace (CTX + 848 + (sc - 7)) with (CTX + 841 + sc) by lia. exact (Y3 eq_refl).
Qed.
Lemma new_present2 c k : In c NEW -> (k < mc_w c)%nat -> (exists q, mc_loc c = LMem q) -> present mem3 (loc_addr L (mc_loc c) + Z.of_nat k).
Proof.
intros Hn _ [q Hq]. exfalso. unfold NEW, NEWu, NEWs, NEWq in Hn.
apply in_app_iff in Hn as [Hn|Hn]; [|apply in_app_iff in Hn as [Hn|Hn]].
- unfold u in Hn. destruct (sc <? 48); [|destruct Hn]. destruct Hn as [<-|[]]. discriminate Hq.
- destruct Hn as [<-|[]]. discriminate Hq.
- destruct z; [apply in_map_iff in Hn as (kk & <- & _); discriminate Hq|]. destruct b; [|destruct Hn]. destruct Hn as [<-|[]]. discriminate Hq.
Qed.
Definition in_win2 (a : Z) : Prop :=
(u = true /\ CTX + 464 + 8 * sc <= a < CTX + 464 + 8 * sc + 8) \/ a = CTX + 912 \/
(z = true /\ CTX + 848 <= a < CTX + 880) \/ (b = true /\ a = CTX + 841 + sc).
Lemma frame13 a : 0 <= a < 2 ^ 64 -> ~ in_win2 a -> mem3 (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a).
Proof.
facts1. intros Ha Hw. rewrite (frame3 a Ha) by (intros W; apply Hw; unfold in_win2; tauto).
unfold memM. apply (HFM (Z_to_bv 64 a)). intros (rr & Hr & Hin). apply Hw.
rewrite Z_to_bv_unsigned in Hin. unfold bv_wrap in Hin. change (bv_modulus 64) with (2 ^ 64) in Hin. rewrite Z.mod_small in Hin by lia.
unfold m1_mem in Hr. unfold in_win2. rewrite !in_app_iff in Hr. destruct Hr as [[<-|[<-|[]]] | [Hr | Hr]].
- cbn [reg_gM r_base r_wlo r_whi] in Hin. lia.
- cbn [reg_seq r_base r_wlo r_whi base_val] in Hin. lia.
- destruct u; [|destruct Hr]. destruct Hr as [<-|[]]. cbn [reg_usgw r_base r_wlo r_whi] in Hin. rewrite (base_val_EV _ XR0) in Hin.
unfold aACT, xv1 in Hin. cbn [Nat.ltb Nat.leb] in Hin. left. split; [reflexivity | lia].
- destruct z; [|destruct Hr]. destruct Hr as [<-|[]]. cbn [reg_useq0 r_base r_wlo r_whi base_val] in Hin. right; right; left. split; [reflexivity | lia].
Qed.
Lemma win_ctx a : in_win2 a -> CTX <= a < CTX + CTX_SIZE.
Proof.
pose proof sc7 as [B1' _]. unfold in_win2, u, CTX_SIZE. intros [[E W]|[->|[[_ W]|[E ->]]]].
- apply Z.ltb_lt in E. unfold sc in *. lia.
- lia.
- lia.
- destruct (B1' E) as [_ R]. lia.
Qed.
Lemma win_covered2 a : in_win2 a -> exists c, In c NEW /\ in_range a (cell_range L c).
Proof.
pose proof Hctx as HC. pose proof sc7 as [B1' _].
assert (CU : forall k v, In (useq_cell k v) NEW -> a = CTX + 848 + Z.of_nat k -> exists c, In c NEW /\ in_range a (cell_range L c)).
{ intros k v Hc Ha. exists (useq_cell k v). split; [exact Hc|]. unfold useq_cell, in_range, cell_range. cbn [mc_loc mc_w fst snd loc_addr]. rewrite HC. unfold CTX_unmap_seq. lia. }
unfold in_win2. intros [[E W]|[->|[[E W]|[E ->]]]]; unfold NEW, NEWu, NEWs, NEWq in *.
- exists (usage_cell (Z.to_nat sc) (usage_of A sc - (am_last am1 + 1))). rewrite E. split; [apply in_app_iff; left; left; reflexivity|].
unfold u in E. apply Z.ltb_lt in E. unfold usage_cell, in_range, cell_range. cbn [mc_loc mc_w fst snd loc_addr]. rewrite HC. unfold CTX_usage. rewrite Z2Nat.id by (unfold sc in *; lia). lia.
- exists (seq_cell newseq). split; [apply in_app_iff; right; apply in_app_iff; left; left; reflexivity|].
unfold seq_cell, in_range, cell_range. cbn [mc_loc mc_w fst snd loc_addr]. rewrite HC. unfold CTX_seq. lia.
- apply (CU (Z.to_nat (a - (CTX + 848))) (nth (Z.to_nat (a - (CTX + 848))) (st_unmap_seq s4) 0)); [|lia].
rewrite E. apply in_app_iff. right. apply in_app_iff. right. apply in_map_iff. eexists. split; [reflexivity | apply in_seq; lia].
- destruct (B1' E) as [_ R7]. rewrite E in *. destruct z.
+ apply (CU (Z.to_nat (sc - 7)) (nth (Z.to_nat (sc - 7)) (st_unmap_seq s4) 0)); [|lia].
apply in_app_iff. right. apply in_app_iff. right. apply in_map_iff. eexists. split; [reflexivity | apply in_seq; lia].
+ apply (CU (Z.to_nat (sc - 7)) newseq); [|lia]. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
Qed.
Theorem memrep4 : memrepX B1 (g :: X) L s4 mem3.
Proof.
pose proof sp_facts2 as (S16 & Sceil & S63 & _). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof footprint_s4 as Efp. pose proof s4_facts as (_&_&_&_&Erg&_).
pose proof SO as SO0. pose proof Hctx as HC. pose proof LG1 as LG0.
refine (memrepX_after B1 (g :: X) (g :: X) None None U1 U s1 s4 L mem1 mem3 NEW [] (SP0 - 96, 96) HI1 HI4 HL1 Efp Erg MR1 cells2 new_home2 new_mem2 new_present2 _ _ _ _).
- intros dd c [].
- intros dd a [].
- intros e0 He. cbn [fst]. pose proof (footprint_hi (g :: X) None U1 L s1 md HI1 SO0 HC LG0 e0 He). lia.
- intros a Ha Hno _ _.
assert (NW : ~ in_win2 a) by (intros W; destruct (win_covered2 a W) as (c & Hc & Hin); exact (Hno c Hc Hin)).
pose proof (frame13 a Ha NW) as E. split; [exact (proj1 (same_byte_views mem1 mem3 a E))|].
intros [bb Hb]. exists bb. rewrite E. exact Hb.
Qed.
Lemma statics4 : statics_ok B1 mem3.
Proof.
pose proof ST1 as ST0. pose proof win_ctx as WC.
apply (statics_ok_ext B1 mem1 mem3 ST0). intros x Hs.
assert (R : 0 <= x < 2 ^ 64 /\ ~ (CTX <= x < CTX + CTX_SIZE)).
{ unfold static_owned in Hs. cbn [ms_lock ms_libc ms_got_guard ms_guard ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt B1 src0_msyms] in Hs.
unfold src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in Hs.
unfold CTX, src0_D_malloc_context, CTX_SIZE. lia. }
destruct R as [R1 R2]. exact (proj1 (same_byte_views mem1 mem3 x (frame13 x R1 (fun W => R2 (WC x W))))).
Qed.
Theorem A2_post : ntmidF FE_XF (g :: X) fuel L A s4 g mi regs regs3 mem mem3 md gv.
Proof.
pose proof NM as NM0. destruct NM0 as [Hso HLo Hcx Hsec Hrep Hst Hlg Hmd Ha0 Hs1 Hs2 Hsp Hkeep Hfr Hgd Hret Htp Hspf Hstkw Hunch].
pose proof sp_facts2 as (S16 & Sceil & S63 & WSTK). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof mem_facts as (M1 & M2 & M3 & M4 & _).
pose proof regs3_facts as (RK & R11 & R12 & R18). pose proof s4_facts as (_&_&_&_&Erg&_&_&_&_&Ebk&_). pose proof footprint_s4 as Efp.
pose proof win_ctx as WC. pose proof frame13 as F13. pose proof SO as SO0. pose proof (so_ctx_hi _ SO0) as CH. cbn [ms_ctx B1 src0_msyms] in CH. fold CTX in CH.
assert (OUT : forall a, 0 <= a < 2 ^ 64 -> alloc_ceiling <= a \/ ~ alloc_owned L s1 a -> mem3 (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a)).
{ intros a Ha Ho. apply (F13 a Ha). intros W. pose proof (WC a W) as R. destruct Ho as [Ho|Ho]; [lia|].
apply Ho. apply (ctx_bytes_owned (g :: X) None U1 s1 L HI1 HLo). rewrite Hcx. exact R. }
assert (STK : forall a w v, SP0 - 96 <= a -> a + Z.of_nat w <= SP0 -> bytes_are mem1 a w v -> bytes_are mem3 a w v).
{ intros a w v Ha Haw Hb k Hk. rewrite <- (Hb k Hk). apply (proj1 (same_byte_views mem1 mem3 _ (OUT (a + Z.of_nat k) ltac:(unfold SP0 in *; lia) ltac:(left; unfold SP0 in *; lia)))). }
unfold NT_FRAME in *. fold SP0 in Hfr, Hstkw, Hunch, Hspf |- *.
split.
- exact Hso.
- exact (layout_ok_same' L s1 s4 HLo Erg Efp).
- exact Hcx.
- exact Hsec.
- apply memrep4.
- apply statics4.
- exact (ledger_ok_same' L s1 s4 md Hlg Erg Ebk).
- exact Hmd.
- cbn [aGF]. rewrite (RK 10%nat ltac:(cbn; tauto)). exact Ha0.
- cbn [aBASE]. rewrite R12, M3. unfold mi, mi_base. rewrite Hmem. reflexivity.
- rewrite R11. reflexivity.
- unfold mi, mi_base, mi_len. rewrite Hmem. cbn [prid]. unfold MEMA, MP in *. rewrite <- M3. lia.
- rewrite (RK 9%nat ltac:(cbn; tauto)). exact Hs1.
- exact R18.
- rewrite (RK 2%nat ltac:(cbn; tauto)). exact Hsp.
- intros rr Hr. rewrite (RK rr ltac:(apply in_app_iff; right; exact Hr)). apply Hkeep. exact Hr.
- destruct Hfr as (F1 & F2 & F3 & F4 & F5 & F6). repeat split; (apply STK; [lia | cbn; lia | assumption]).
- intros k Hk. rewrite <- (Hgd k Hk).
assert (NW : ~ in_win2 (GUARD + Z.of_nat k)) by (intros W; pose proof (WC _ W); unfold GUARD, src0_D_stack_chk_guard, CTX, src0_D_malloc_context, CTX_SIZE in *; lia).
exact (proj1 (same_byte_views mem1 mem3 _ (F13 (GUARD + Z.of_nat k) ltac:(unfold GUARD, src0_D_stack_chk_guard; lia) NW))).
- exact Hret.
- exact Htp.
- exact Hspf.
- intros a Ha. unfold NT_FRAME in Ha. fold SP0 in Ha. apply (writable_same mem1 mem3 a (OUT a ltac:(lia) ltac:(left; lia))). apply Hstkw. exact Ha.
- intros a Ha NO NS. unfold NT_FRAME in NS. fold SP0 in NS. exact (same_byte_views mem mem3 a (eq_trans (OUT a Ha (or_intror (fun W => NO (AO1 a W)))) (Hunch a Ha NO NS))).
Qed.
End j.
End h.
Theorem A2_SR :
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 XU) mem1 (seg_rom src0segs)) md)
(fun c' => exists regs3 mem3, c' = mkCfg (mkst regs3 (Z_to_bv 64 XF) mem3 (seg_rom src0segs)) md /\
ntmidF FE_XF (g :: X) fuel L A s4 g mi regs regs3 mem mem3 md gv).
Proof.
pose proof (nm_md _ _ _ _ _ _ _ _ _ _ _ _ NM) as (Hh & Hlz & Hmat).
eapply SR_bind; [eapply (stage_run XM (ss_M1 u z) (SSM1 u z) (EV xv1) _ md (M1_run_ok u z) M1_entry_st_ok Hh Hlz)|].
intros c' (msM & -> & HSM & HFM). cbn [ms_mem mkst] in HFM.
eapply SR_bind; [eapply (stage_run XF (ss_M2 b) (SSM2 b) (EV (xv2 msM)) _ md (M2_run_ok b) (M2_entry_st_ok msM HSM) Hh Hlz)|].
intros c'' (ms3 & -> & HS3 & HF3).
apply SR_ret. exists (ms_regs ms3), (ms_mem ms3). split; [rewrite (shape3 msM ms3 HS3) at 1; reflexivity|].
exact (A2_post msM HSM HFM ms3 HS3 HF3).
Qed.
End f.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
