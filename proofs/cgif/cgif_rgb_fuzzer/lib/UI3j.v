(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI07
UI1e UI1i YI0x YP14 YI08 YI0c YI0f YI0d UI3h.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM01 YM02 YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition NT_L1 : Z := Eval vm_compute in (ubs2_A_new_tree_node + 0x9c).
Definition NT_L1END : Z := Eval vm_compute in (ubs2_A_new_tree_node + 0x12c).
Definition NT_MD : Z := Eval vm_compute in (ubs2_A_new_tree_node + 0x130).
Definition NT_L2 : Z := Eval vm_compute in (ubs2_A_new_tree_node + 0x180).
Definition NT_L2END : Z := Eval vm_compute in (ubs2_A_new_tree_node + 0x220).
Definition NT_VA : Z := Eval vm_compute in (ubs2_A_new_tree_node + 0x224).
Definition NT_TAIL : Z := Eval vm_compute in (ubs2_A_new_tree_node + 0x294).
Local Abbreviation D := fmt_double.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Local Notation segs := ubs2segs.
Local Notation rom := (seg_rom ubs2segs).
Variables (STK sp0 : Z) (FP : list (Z * Z)) (L : layout) (A : astate) (mem0 : word -> option byte) (md0 : Model).
Variables (L2 : layout) (A2 : astate) (md2 : Model).
Variables (regs0 : bvmap 5 word) (palp frp nln imin imax cidx res : Z) (pal fr : list Z).
Local Notation spc := (spZ regs0 - 160).
Hypothesis Hii : 0 <= imin <= imax.
Hypothesis Himax : imax < 2 ^ 30.
Hypothesis Hlenp : 3 * (imax + 1) <= zlen pal.
Hypothesis Hlenf : imax + 1 <= zlen fr.
Hypothesis Hpalv : forall j, (j < length pal)%nat -> 0 <= nth j pal 0 < 256.
Hypothesis Hfrv : forall j, (j < length fr)%nat -> 0 <= nth j fr 0 < 2 ^ 32.
Hypothesis Hfr1 : forall i, imin <= i <= imax -> 1 <= getz fr i.
Hypothesis Hsum : wsum (node_list pal fr imin imax 0) <= RGB_NMAX.
Hypothesis Hpalp : 4096 <= palp. Hypothesis Hpalhi : palp + zlen pal <= alloc_ceiling.
Hypothesis Hfrp : 4096 <= frp. Hypothesis Hfrhi : frp + 4 * zlen fr <= alloc_ceiling. Hypothesis Hfr4 : frp mod 4 = 0.
Hypothesis Hpfd : palp + zlen pal <= frp \/ frp + 4 * zlen fr <= palp.
Hypothesis Hres0 : 4096 <= res. Hypothesis Hres1 : res + NODE_SIZE <= alloc_ceiling. Hypothesis Hres16 : res mod 16 = 0.
Hypothesis Hbud : sp0 - STK <= spZ regs0 - NTN_STK. Hypothesis Hsptop : spZ regs0 <= sp0. Hypothesis Hal16 : spZ regs0 mod 16 = 0.
Hypothesis Hceil : alloc_ceiling + STK <= sp0. Hypothesis H63 : sp0 < 2 ^ 63.
Lemma ntn_consts : NODE_SIZE = 56 /\ NTN_STK = 160 + ALLOC_STACK /\ ALLOC_STACK = 8192 /\ RGB_NMAX = 10000 /\ (CEIL_MIN <= alloc_ceiling <= CEIL_MAX)  .
Proof. repeat match goal with H : _ |- _ => clear H end.   pose proof (proj1 alloc_ceiling_val). repeat split; first [reflexivity | lia]. Qed.
Definition ss_L1x : sstate :=
mkSS NT_L1 (sr_set sr_atoms 13%bv (SLit 1))
[ YQ0b.mkRegion (Some 2%nat) 0 160 56 104
[mkChunk 56 (CVal 8 (SOff 32 0)); mkChunk 64 (CVal 8 (SOff 32 0)); mkChunk 72 (CVal 8 (SOff 32 0));
mkChunk 80 (CVal 8 (SOff 33 0)); mkChunk 88 (CVal 8 (SOff 34 0)); mkChunk 96 (CVal 8 (SOff 35 0))];
YQ0b.mkRegion (Some 40%nat) 0 3 0 0 [mkChunk 0 (CVal 1 (SOff 36 0)); mkChunk 1 (CVal 1 (SOff 37 0)); mkChunk 2 (CVal 1 (SOff 38 0))];
YQ0b.mkRegion (Some 41%nat) 0 4 0 0 [mkChunk 0 (CVal 4 (SOff 39 0))] ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (14%nat, mkAF 0 (2^30) 0); (12%nat, mkAF 0 (3 * 2^30) 0); (18%nat, mkAF 0 (2^30) 0);
(21%nat, mkAF 4096 CEIL_MAX 0); (20%nat, mkAF 4096 CEIL_MAX 2); (40%nat, mkAF 4096 CEIL_MAX 0); (41%nat, mkAF 4096 CEIL_MAX 2);
(36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 (2^32 - 1) 0);
(11%nat, mkAF (2^64 - 1 - CEIL_MAX) (2^64 - 1 - 4096) 0) ]
[ mkAC BC_GEU (SOff 40 0) (SOff 21 0); mkAC BC_GEU (SOff 40 1) (SOff 21 0); mkAC BC_GEU (SOff 40 2) (SOff 21 0) ]
[ (SAlu ALU_ADD (SOff 21 0) (SOff 12 0), SOff 40%nat 0);
(SAlu ALU_ADD (SOff 20 0) (SAlu ALU_SLL (SOff 14 0) (SLit 2)), SOff 41%nat 0) ]).
Definition ss_L1 : sstate := mkSST NT_L1 (ss_regs ss_L1x) (sfr_atoms 64) (ss_mem ss_L1x) None (ss_facts ss_L1x).
Definition L1_KEEP : list reg := [1; 2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition L1_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (i : Z) : Prop :=
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 L2 A2 mem md2 /\
frm_zero (@fp_csr fy) /\
getr regs 2 = Z_to_bv 64 spc /\ getr regs 10 = Z_to_bv 64 res /\ getr regs 11 = Z_to_bv 64 (2 ^ 64 - 1 - frp) /\
getr regs 13 = Z_to_bv 64 1 /\
getr regs 12 = Z_to_bv 64 (3 * i) /\ getr regs 14 = Z_to_bv 64 i /\ getr regs 18 = Z_to_bv 64 imax /\
getr regs 20 = Z_to_bv 64 frp /\ getr regs 21 = Z_to_bv 64 palp /\
arr8 segs mem palp pal /\ arr32 segs mem frp fr /\
exists xs xm0 xm1 xm2,
val_mem segs mem (spc + 56) 8 xs /\ val_mem segs mem (spc + 64) 8 xs /\ val_mem segs mem (spc + 72) 8 xs /\
val_mem segs mem (spc + 80) 8 xm0 /\ val_mem segs mem (spc + 88) 8 xm1 /\ val_mem segs mem (spc + 96) 8 xm2 /\
0 <= xs < 2 ^ 64 /\ 0 <= xm0 < 2 ^ 64 /\ 0 <= xm1 < 2 ^ 64 /\ 0 <= xm2 < 2 ^ 64 /\
is_intd xs (wsum (nlp pal fr imin i 0)) /\
is_intd xm0 (wdot (nlp pal fr imin i 0)) /\ is_intd xm1 (wdot (nlp pal fr imin i 1)) /\ is_intd xm2 (wdot (nlp pal fr imin i 2)).
Lemma L1_entry : forall (fy : FPState) (regs : bvmap 5 word) mem (i xs xm0 xm1 xm2 : Z),
imin <= i <= imax ->
frm_zero (@fp_csr fy) ->
getr regs 2 = Z_to_bv 64 spc -> getr regs 11 = Z_to_bv 64 (2 ^ 64 - 1 - frp) -> getr regs 13 = Z_to_bv 64 1 ->
getr regs 12 = Z_to_bv 64 (3 * i) -> getr regs 14 = Z_to_bv 64 i -> getr regs 18 = Z_to_bv 64 imax ->
getr regs 20 = Z_to_bv 64 frp -> getr regs 21 = Z_to_bv 64 palp ->
arr8 segs mem palp pal -> arr32 segs mem frp fr ->
val_mem segs mem (spc + 56) 8 xs -> val_mem segs mem (spc + 64) 8 xs -> val_mem segs mem (spc + 72) 8 xs ->
val_mem segs mem (spc + 80) 8 xm0 -> val_mem segs mem (spc + 88) 8 xm1 -> val_mem segs mem (spc + 96) 8 xm2 ->
0 <= xs < 2 ^ 64 -> 0 <= xm0 < 2 ^ 64 -> 0 <= xm1 < 2 ^ 64 -> 0 <= xm2 < 2 ^ 64 ->
(forall a, spc + 56 <= a < spc + 104 -> writable_at segs mem a) ->
let vals := [xs; xm0; xm1; xm2; getz pal (3 * i); getz pal (3 * i + 1); getz pal (3 * i + 2); getz fr i; palp + 3 * i; frp + 4 * i] in
let E0 := Ereg regs (map (Z_to_bv 64) vals ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF segs E ss_L1 (@mkst fy regs (Z_to_bv 64 NT_L1) mem rom) /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
(forall r : reg, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
(forall k j v, nth_error vals j = Some v -> k = (32 + j)%nat -> ew E k = Z_to_bv 64 v) /\
bv_unsigned (ew E 2) = spc.
Proof.
intros fy regs mem i xs xm0 xm1 xm2 Hi Hfrm Hr2 Hr11 Hr13 Hr12 Hr14 Hr18 Hr20 Hr21 Hpa Hfa V56 V64 V72 V80 V88 V96 Rs R0 R1 R2 Hw vals E0 E.
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
pose proof (pal_byte pal Hpalv) as Hpb. pose proof (fr_word fr Hfrv) as Hfw.
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HU2 : bv_unsigned (ew E0 2) = spc) by (rewrite (HE0 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU12 : bv_unsigned (ew E0 12) = 3 * i) by (rewrite (HE0 12%nat 12%bv eq_refl), Hr12; apply unsigned_lit_small; lia).
assert (HU14 : bv_unsigned (ew E0 14) = i) by (rewrite (HE0 14%nat 14%bv eq_refl), Hr14; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E0 18) = imax) by (rewrite (HE0 18%nat 18%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU20 : bv_unsigned (ew E0 20) = frp) by (rewrite (HE0 20%nat 20%bv eq_refl), Hr20; apply unsigned_lit_small; lia).
assert (HU21 : bv_unsigned (ew E0 21) = palp) by (rewrite (HE0 21%nat 21%bv eq_refl), Hr21; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E0 11) = 2 ^ 64 - 1 - frp) by (rewrite (HE0 11%nat 11%bv eq_refl), Hr11; apply unsigned_lit_small; lia).
assert (HA : forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E0 (32 + j)) = v).
{ intros j v Hj Hv. rewrite (HV j v Hj). apply unsigned_lit_small. exact Hv. }
pose proof (Hpb (3 * i) ltac:(lia)) as P0. pose proof (Hpb (3 * i + 1) ltac:(lia)) as P1. pose proof (Hpb (3 * i + 2) ltac:(lia)) as P2.
pose proof (Hfw i ltac:(lia)) as Fi.
pose proof (HA 0%nat xs eq_refl Rs) as A32. pose proof (HA 1%nat xm0 eq_refl R0) as A33. pose proof (HA 2%nat xm1 eq_refl R1) as A34.
pose proof (HA 3%nat xm2 eq_refl R2) as A35. pose proof (HA 4%nat _ eq_refl ltac:(lia)) as A36. pose proof (HA 5%nat _ eq_refl ltac:(lia)) as A37.
pose proof (HA 6%nat _ eq_refl ltac:(lia)) as A38. pose proof (HA 7%nat _ eq_refl ltac:(lia)) as A39.
pose proof (HA 8%nat _ eq_refl ltac:(lia)) as A40. pose proof (HA 9%nat _ eq_refl ltac:(lia)) as A41.
cbn [Nat.add] in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41.
assert (HS0 : @st_ok segs fy E0 ss_L1x (@mkst fy regs (Z_to_bv 64 NT_L1) mem rom)).
{ unfold ss_L1x. subst E0. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |]. rewrite Hr13. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia|].
repeat apply Forall_cons; [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?A32, ?A33, ?A34, ?A35; reflexivity | cbn; lia | cbn; lia | assumption]).
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite A40.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?A36, ?A37, ?A38; reflexivity | cbn; lia | cbn; lia |]);
[ apply val_mem_byte; [rewrite Z.add_0_r; exact (proj1 (arr8_getz segs mem palp pal (3 * i) Hpa ltac:(lia))) | lia]
| apply val_mem_byte; [replace (palp + 3 * i + 1) with (palp + (3 * i + 1)) by lia; exact (proj1 (arr8_getz segs mem palp pal (3 * i + 1) Hpa ltac:(lia))) | lia]
| apply val_mem_byte; [replace (palp + 3 * i + 2) with (palp + (3 * i + 2)) by lia; exact (proj1 (arr8_getz segs mem palp pal (3 * i + 2) Hpa ltac:(lia))) | lia] ].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite A41.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A39; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact (proj1 (arr32_getz segs mem frp fr i Hfa ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, A40, A41. repeat split; lia.
- split; [|split].
 + cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU12, HU14, HU18, HU20, HU21, HU11, A36, A37, A38, A39, A40, A41. change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 0) with 1.
rewrite !Z.mod_1_r.
assert (spc mod 16 = 0) by (replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert ((frp + 4 * i) mod 4 = 0) by (replace (frp + 4 * i) with (frp + i * 4) by lia; rewrite Z.mod_add by lia; exact Hfr4).
repeat split; lia.
+ cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite !branch_geu_U, !U_SOff, A40, HU21, !Z.add_0_r.
rewrite (zcanon_id palp), (zcanon_id (palp + 3 * i)), (zcanon_id (palp + 3 * i + 1)), (zcanon_id (palp + 3 * i + 2)) by (unfold M64; lia).
repeat split; apply negb_true_iff, Z.ltb_ge; lia.
+ cbn [f_alias alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, HU21, HU12, A40, !Z.add_0_r. rewrite (zcanon_id palp), (zcanon_id (3 * i)) by (unfold M64; lia). reflexivity.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, HU20, HU14, A41, !Z.add_0_r.
rewrite (zcanon_id frp), (zcanon_id i) by (unfold M64; lia). change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 2) with 4. rewrite (zcanon_id (i * 4)) by (unfold M64; lia). f_equal. lia. }
split; [exact (st_ok_enterF segs fy 64 E0 ss_L1x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|].
split; [| rewrite HEE by lia; exact HU2].
intros k j v Hj ->. rewrite HEE; [apply HV; exact Hj|].
assert (Hl : (j < length vals)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). cbn in Hl. lia.
Qed.
Definition ss_L1_out : sstate := Eval vm_compute in (fst (sym_run_toFN segs ubs2tbl FUEL NT_L1END ss_L1)).
Lemma L1_read : forall E ss ms (i xs xm0 xm1 xm2 : Z),
st_okF segs E ss ms -> ss_mem ss = ss_mem ss_L1_out -> ss_regs ss = ss_regs ss_L1_out ->
imin <= i <= imax ->
bv_unsigned (ew E 2) = spc ->
bv_unsigned (ew E 32) = xs -> bv_unsigned (ew E 33) = xm0 -> bv_unsigned (ew E 34) = xm1 -> bv_unsigned (ew E 35) = xm2 ->
bv_unsigned (ew E 36) = getz pal (3 * i) -> bv_unsigned (ew E 37) = getz pal (3 * i + 1) -> bv_unsigned (ew E 38) = getz pal (3 * i + 2) ->
bv_unsigned (ew E 39) = getz fr i ->
bv_unsigned (ew E 12) = 3 * i -> bv_unsigned (ew E 14) = i ->
is_intd xs (wsum (nlp pal fr imin i 0)) ->
is_intd xm0 (wdot (nlp pal fr imin i 0)) -> is_intd xm1 (wdot (nlp pal fr imin i 1)) -> is_intd xm2 (wdot (nlp pal fr imin i 2)) ->
exists xs' xm0' xm1' xm2',
val_mem segs (ms_mem ms) (spc + 56) 8 xs' /\ val_mem segs (ms_mem ms) (spc + 64) 8 xs' /\ val_mem segs (ms_mem ms) (spc + 72) 8 xs' /\
val_mem segs (ms_mem ms) (spc + 80) 8 xm0' /\ val_mem segs (ms_mem ms) (spc + 88) 8 xm1' /\ val_mem segs (ms_mem ms) (spc + 96) 8 xm2' /\
0 <= xs' < 2 ^ 64 /\ 0 <= xm0' < 2 ^ 64 /\ 0 <= xm1' < 2 ^ 64 /\ 0 <= xm2' < 2 ^ 64 /\
is_intd xs' (wsum (nlp pal fr imin (i + 1) 0)) /\
is_intd xm0' (wdot (nlp pal fr imin (i + 1) 0)) /\ is_intd xm1' (wdot (nlp pal fr imin (i + 1) 1)) /\ is_intd xm2' (wdot (nlp pal fr imin (i + 1) 2)) /\
getr (ms_regs ms) 12 = Z_to_bv 64 (3 * (i + 1)) /\ getr (ms_regs ms) 14 = Z_to_bv 64 (i + 1).
Proof.
intros E ss ms i xs xm0 xm1 xm2 HS Hm Hr Hi HU2 A32 A33 A34 A35 A36 A37 A38 A39 HU12 HU14 Is I0 I1 I2.
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
pose proof (pal_byte pal Hpalv) as Hpb. pose proof (fr_word fr Hfrv) as Hfw.
pose proof (Hpb (3 * i) ltac:(lia)) as P0. pose proof (Hpb (3 * i + 1) ltac:(lia)) as P1. pose proof (Hpb (3 * i + 2) ltac:(lia)) as P2.
pose proof (Hfw i ltac:(lia)) as Fi.
pose proof (wsum_nlp_le pal fr imin imax Hii Hfr1 Hsum (i + 1) 0 ltac:(lia)) as Ws.
pose proof (wdot_nlp_le pal fr imin imax Hii Hpalv Hfr1 Hlenp Hsum i) as Wd.
rewrite (nlp_snoc pal fr imin i 0) in Ws by lia. rewrite wsum_snoc in Ws.
rewrite (nlp_snoc pal fr imin i 0), (nlp_snoc pal fr imin i 1), (nlp_snoc pal fr imin i 2) by lia.
rewrite !wsum_snoc, !wdot_snoc. rewrite !(Z.add_0_r (3 * i)).
pose proof (wsum_nlp_le pal fr imin imax Hii Hfr1 Hsum i 0 ltac:(lia)) as Ws0.
assert (Hf : 0 <= getz fr i <= RGB_NMAX) by lia.
assert (HfP : forall p, 0 <= p < 256 -> getz fr i * p < 2 ^ 32) by (intros p Hp; rewrite HNM in Hf; nia).
assert (HdP : forall d w, 0 <= d <= 2 -> 0 <= w <= 255 * RGB_NMAX -> Z.abs (w + getz fr i * getz pal (3 * i + d)) <= 2 ^ 53).
{ intros d w Hd Hw. pose proof (Hpb (3 * i + d) ltac:(lia)). rewrite HNM in Hf, Hw. nia. }
pose proof (st_okF_to_legacy segs E ss ms HS) as HSL.
set (es := SF2 (FP2_ari F_ADD FMT_D RNE) (SOff 32 0) (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff 39 0))).
set (em0 := SF2 (FP2_ari F_ADD FMT_D RNE) (SOff 33 0) (SF1 (FP1_cvt FC_D FC_WU RNE) (SMd M_MUL (SOff 39 0) (SOff 36 0)))).
set (em1 := SF2 (FP2_ari F_ADD FMT_D RNE) (SOff 34 0) (SF1 (FP1_cvt FC_D FC_WU RNE) (SMd M_MUL (SOff 39 0) (SOff 37 0)))).
set (em2 := SF2 (FP2_ari F_ADD FMT_D RNE) (SOff 35 0) (SF1 (FP1_cvt FC_D FC_WU RNE) (SMd M_MUL (SOff 39 0) (SOff 38 0)))).
assert (Dat : forall n v, bv_unsigned (ew E n) = v -> bv_unsigned (sv_denot E (SOff n 0)) = v).
{ intros n v H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. }
assert (CV : forall off e, In (mkChunk off (CVal 8 e)) (r_chunks (nth 0 (ss_mem ss) (YQ0b.mkRegion None 0 0 0 0 []))) ->
val_mem segs (ms_mem ms) (spc + off) 8 (bv_unsigned (sv_denot E e))).
{ intros off e Hin. rewrite Hm in Hin. eapply (st_chunk_val segs E ss ms 0%nat _ 2%nat off 8%N e spc _ HSL);
[rewrite Hm; reflexivity | reflexivity | cbn in Hin |- *; exact Hin | exact HU2 | symmetry; apply Z_to_bv_bv_unsigned | change (8 * Z.of_N 8) with 64; apply u64_rangeN | cbn; lia]. }
exists (bv_unsigned (sv_denot E es)), (bv_unsigned (sv_denot E em0)), (bv_unsigned (sv_denot E em1)), (bv_unsigned (sv_denot E em2)).
split; [apply CV; rewrite Hm; cbn; tauto|]. split; [apply CV; rewrite Hm; cbn; tauto|]. split; [apply CV; rewrite Hm; cbn; tauto|].
split; [apply CV; rewrite Hm; cbn; tauto|]. split; [apply CV; rewrite Hm; cbn; tauto|]. split; [apply CV; rewrite Hm; cbn; tauto|].
split; [apply u64_rangeN|]. split; [apply u64_rangeN|]. split; [apply u64_rangeN|]. split; [apply u64_rangeN|].
split; [subst es; apply val_fadd; [rewrite (Dat 32%nat xs A32); exact Is | apply val_cvt_wu; [apply Dat; exact A39 | lia] | lia]|].
split; [subst em0; apply val_fadd; [rewrite (Dat 33%nat xm0 A33); exact I0 | apply val_cvt_mul; [apply Dat; exact A39 | apply Dat; exact A36 | lia | lia | apply HfP; lia] | pose proof (HdP 0 _ ltac:(lia) (Wd 0 ltac:(lia) ltac:(lia))) as X; rewrite Z.add_0_r in X; exact X]|].
split; [subst em1; apply val_fadd; [rewrite (Dat 34%nat xm1 A34); exact I1 | apply val_cvt_mul; [apply Dat; exact A39 | apply Dat; exact A37 | lia | lia | apply HfP; lia] | exact (HdP 1 _ ltac:(lia) (Wd 1 ltac:(lia) ltac:(lia)))]|].
split; [subst em2; apply val_fadd; [rewrite (Dat 35%nat xm2 A35); exact I2 | apply val_cvt_mul; [apply Dat; exact A39 | apply Dat; exact A38 | lia | lia | apply HfP; lia] | exact (HdP 2 _ ltac:(lia) (Wd 2 ltac:(lia) ltac:(lia)))]|].
split.
- rewrite (st_okF_reg segs E ss ms 12%bv HS), Hr. match goal with |- sv_denot _ ?v = _ => let v' := eval vm_compute in v in change v with v' end.
cbn [sv_denot]. rewrite HU12. f_equal; lia.
- rewrite (st_okF_reg segs E ss ms 14%bv HS), Hr. match goal with |- sv_denot _ ?v = _ => let v' := eval vm_compute in v in change v with v' end.
cbn [sv_denot]. rewrite HU14. reflexivity.
Qed.
Lemma ntn_stack_w : forall Lx Ax m mdx, journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lx Ax m mdx ->
forall a, spc <= a < spZ regs0 -> writable_at segs m a.
Proof.
intros Lx Ax m mdx HJ a Ha. pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _). apply Hstw. lia.
Qed.
Ltac ntn_wr HU2 :=
wr_ok_eval; eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia |];
repeat (apply wr_ok_cons_ro; [cbn; lia|]); apply wr_ok_nil.
Ltac L1_post HS HE HEf HU2 Hread Hpa Hfa :=
lazymatch type of HS with st_okF _ ?E1 ?ss1 ?ms1 =>
rewrite (st_okF_mkst segs E1 ss1 ms1 HS eq_refl); cbn [ss_pc];
apply SR_ret; exists (fp_of ms1), (ms_regs ms1), (ms_mem ms1);
pose proof (st_okF_regs_kept segs E1 ss1 ms1 _ L1_KEEP HS ltac:(intros r _; apply HE; pose proof (u5_range r); unfold ridx; lia) ltac:(vm_compute; reflexivity)) as Hk
end.
Lemma L1_step : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
imin <= i <= imax -> L1_inv fy regs mem i ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 NT_L1) mem rom) md2)
(fun c' => exists (fy' : FPState) regs' mem',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if i <? imax then NT_L1 else NT_MD)) mem' rom) md2 /\
L1_inv fy' regs' mem' (i + 1) /\
(forall r : reg, In r L1_KEEP -> getr regs' r = getr regs r) /\
fregs_preserved (@fp_regs fy) (@fp_regs fy') /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 56 <= a < spc + 104) -> mbyte segs mem' a = mbyte segs mem a)).
Proof.
intros fy regs mem i Hi (HJ & Hfrm & Hr2 & Hr10 & Hr11 & Hr13 & Hr12 & Hr14 & Hr18 & Hr20 & Hr21 & Hpa & Hfa & xs & xm0 & xm1 & xm2 &
V56 & V64 & V72 & V80 & V88 & V96 & Rs & R0 & R1 & R2 & Is & I0 & I1 & I2).
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
pose proof (ntn_stack_w _ _ _ _ HJ) as Hstw.
destruct (L1_entry fy regs mem i xs xm0 xm1 xm2 Hi Hfrm Hr2 Hr11 Hr13 Hr12 Hr14 Hr18 Hr20 Hr21 Hpa Hfa V56 V64 V72 V80 V88 V96 Rs R0 R1 R2
ltac:(intros a Ha; apply Hstw; lia)) as (HS & HE & HEf & HV & HU2).
set (E := ew_fregs _ 64 _) in HS, HE, HEf, HV, HU2.
assert (HA : forall k j v, nth_error [xs; xm0; xm1; xm2; getz pal (3 * i); getz pal (3 * i + 1); getz pal (3 * i + 2); getz fr i; palp + 3 * i; frp + 4 * i] j = Some v ->
k = (32 + j)%nat -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E k) = v).
{ intros k j v Hj Hk Hv. rewrite (HV k j v Hj Hk). apply unsigned_lit_small. exact Hv. }
pose proof (pal_byte pal Hpalv) as Hpb. pose proof (fr_word fr Hfrv) as Hfw.
pose proof (HA 32%nat 0%nat xs eq_refl eq_refl Rs) as A32. pose proof (HA 33%nat 1%nat xm0 eq_refl eq_refl R0) as A33.
pose proof (HA 34%nat 2%nat xm1 eq_refl eq_refl R1) as A34. pose proof (HA 35%nat 3%nat xm2 eq_refl eq_refl R2) as A35.
pose proof (HA 36%nat 4%nat _ eq_refl eq_refl (ltac:(pose proof (Hpb (3 * i) ltac:(lia)); lia))) as A36.
pose proof (HA 37%nat 5%nat _ eq_refl eq_refl (ltac:(pose proof (Hpb (3 * i + 1) ltac:(lia)); lia))) as A37.
pose proof (HA 38%nat 6%nat _ eq_refl eq_refl (ltac:(pose proof (Hpb (3 * i + 2) ltac:(lia)); lia))) as A38.
pose proof (HA 39%nat 7%nat _ eq_refl eq_refl (ltac:(pose proof (Hfw i ltac:(lia)); lia))) as A39.
assert (HU12 : bv_unsigned (ew E 12) = 3 * i) by (rewrite (HE 12%nat 12%bv eq_refl), Hr12; apply unsigned_lit_small; lia).
assert (HU14 : bv_unsigned (ew E 14) = i) by (rewrite (HE 14%nat 14%bv eq_refl), Hr14; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 18) = imax) by (rewrite (HE 18%nat 18%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 NT_L1) mem rom)) in HJ.
jrunF_to LAWS ubs2tbl_ok HS HJ NT_L1END. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF, HJ.
jbranchF ubs2tbl HS.
-
rewrite branch_geu_U, !U_SOff, HU18, HU14, !zcanon_id in Hc by (unfold M64; lia). rewrite !Z.add_0_r in Hc.
destruct (Z_lt_ge_dec i imax) as [Hlt|Hge]; [| exfalso; destruct (Z.ltb_spec imax (i + 1)); [discriminate Hc | lia]].
jrunF_to LAWS ubs2tbl_ok HS HJ NT_L1. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF0, HJ.
destruct (L1_read E _ _ i xs xm0 xm1 xm2 HS eq_refl eq_refl Hi HU2 A32 A33 A34 A35 A36 A37 A38 A39 HU12 HU14 Is I0 I1 I2)
as (xs' & xm0' & xm1' & xm2' & W56 & W64 & W72 & W80 & W88 & W96 & Rs' & R0' & R1' & R2' & Is' & I0' & I1' & I2' & Hq12 & Hq14).
L1_post HS HE HEf HU2 L1_read Hpa Hfa.
replace (i <? imax) with true by (symmetry; apply Z.ltb_lt; lia).
split; [reflexivity|].
assert (Hmb : forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 56 <= a < spc + 104) -> mbyte segs (ms_mem ms0) a = mbyte segs mem a).
{ intros a Ha Hna. mb_frames ltac:(exact Ha) ltac:(rewrite ?HU2; lia). reflexivity. }
split.
{ split; [exact HJ|]. split; [exact (st_okF_frm segs E _ _ HS)|].
split; [rewrite (Hk 2%bv ltac:(cbv; tauto)); exact Hr2|]. split; [rewrite (Hk 10%bv ltac:(cbv; tauto)); exact Hr10|].
split; [rewrite (Hk 11%bv ltac:(cbv; tauto)); exact Hr11|]. split; [jregF HS (13%bv:reg) as Hq13; rewrite Hq13; reflexivity|].
split; [exact Hq12|]. split; [exact Hq14|].
split; [rewrite (Hk 18%bv ltac:(cbv; tauto)); exact Hr18|]. split; [rewrite (Hk 20%bv ltac:(cbv; tauto)); exact Hr20|].
split; [rewrite (Hk 21%bv ltac:(cbv; tauto)); exact Hr21|].
split; [eapply arr8_frame; [exact Hpa|]; intros a Ha; apply Hmb; lia|].
split; [eapply arr32_frame; [exact Hfa|]; intros a Ha; apply Hmb; lia|].
exists xs', xm0', xm1', xm2'. repeat (split; [assumption|]). exact I2'. }
split; [exact Hk|].
split; [intros rr Hrr; cbn [fp_regs fp_of]; exact (st_okF_fregs_kept segs E _ _ 64 (@fp_regs fy) FCALLEE_SAVED HS HEf ltac:(vm_compute; reflexivity) rr Hrr)|].
exact Hmb.
-
rewrite branch_geu_U, !U_SOff, HU18, HU14, !zcanon_id in Hc by (unfold M64; lia). rewrite !Z.add_0_r in Hc.
destruct (Z_lt_ge_dec i imax) as [Hlt|Hge]; [exfalso; destruct (Z.ltb_spec imax (i + 1)); [lia | discriminate Hc] |].
jrunF_to LAWS ubs2tbl_ok HS HJ NT_MD. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF0, HJ.
destruct (L1_read E _ _ i xs xm0 xm1 xm2 HS eq_refl eq_refl Hi HU2 A32 A33 A34 A35 A36 A37 A38 A39 HU12 HU14 Is I0 I1 I2)
as (xs' & xm0' & xm1' & xm2' & W56 & W64 & W72 & W80 & W88 & W96 & Rs' & R0' & R1' & R2' & Is' & I0' & I1' & I2' & Hq12 & Hq14).
L1_post HS HE HEf HU2 L1_read Hpa Hfa.
replace (i <? imax) with false by (symmetry; apply Z.ltb_ge; lia).
split; [reflexivity|].
assert (Hmb : forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 56 <= a < spc + 104) -> mbyte segs (ms_mem ms0) a = mbyte segs mem a).
{ intros a Ha Hna. mb_frames ltac:(exact Ha) ltac:(rewrite ?HU2; lia). reflexivity. }
split.
{ split; [exact HJ|]. split; [exact (st_okF_frm segs E _ _ HS)|].
split; [rewrite (Hk 2%bv ltac:(cbv; tauto)); exact Hr2|]. split; [rewrite (Hk 10%bv ltac:(cbv; tauto)); exact Hr10|].
split; [rewrite (Hk 11%bv ltac:(cbv; tauto)); exact Hr11|]. split; [jregF HS (13%bv:reg) as Hq13; rewrite Hq13; reflexivity|].
split; [exact Hq12|]. split; [exact Hq14|].
split; [rewrite (Hk 18%bv ltac:(cbv; tauto)); exact Hr18|]. split; [rewrite (Hk 20%bv ltac:(cbv; tauto)); exact Hr20|].
split; [rewrite (Hk 21%bv ltac:(cbv; tauto)); exact Hr21|].
split; [eapply arr8_frame; [exact Hpa|]; intros a Ha; apply Hmb; lia|].
split; [eapply arr32_frame; [exact Hfa|]; intros a Ha; apply Hmb; lia|].
exists xs', xm0', xm1', xm2'. repeat (split; [assumption|]). exact I2'. }
split; [exact Hk|].
split; [intros rr Hrr; cbn [fp_regs fp_of]; exact (st_okF_fregs_kept segs E _ _ 64 (@fp_regs fy) FCALLEE_SAVED HS HEf ltac:(vm_compute; reflexivity) rr Hrr)|].
exact Hmb.
Qed.
Definition L1_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc : Z) (j : Z) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' rom) md2 /\
L1_inv fy' regs' mem' j /\
(forall r : reg, In r L1_KEEP -> getr regs' r = getr regs r) /\
fregs_preserved (@fp_regs fy) (@fp_regs fy') /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 56 <= a < spc + 104) -> mbyte segs mem' a = mbyte segs mem a).
Lemma ntn_loop1 : forall (k : nat) (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
imin <= i <= imax -> Z.of_nat k = imax - i -> L1_inv fy regs mem i ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 NT_L1) mem rom) md2) (L1_post fy regs mem NT_MD (imax + 1)).
Proof.
induction k as [|k IH]; intros fy regs mem i Hi Hk HI.
- assert (Hii' : i = imax) by lia. subst i.
eapply SR_mono; [exact (L1_step fy regs mem imax Hi HI)|].
cbv beta. intros c' (fy' & regs' & mem' & -> & HI' & Hk' & Hf' & Hm'). rewrite Z.ltb_irrefl.
exists fy', regs', mem'. repeat (split; [first [reflexivity | assumption]|]). exact Hm'.
- eapply SR_bind; [exact (L1_step fy regs mem i Hi HI)|].
cbv beta. intros c' (fy' & regs' & mem' & -> & HI' & Hk' & Hf' & Hm').
replace (i <? imax) with true by (symmetry; apply Z.ltb_lt; lia).
eapply SR_mono; [exact (IH fy' regs' mem' (i + 1) ltac:(lia) ltac:(lia) HI')|].
cbv beta. intros c'' (fy'' & regs'' & mem'' & -> & HI'' & Hk'' & Hf'' & Hm'').
exists fy'', regs'', mem''. split; [reflexivity|]. split; [exact HI''|].
split; [intros r Hr; rewrite (Hk'' r Hr); apply Hk'; exact Hr|].
split; [eapply fregs_preserved_trans; [exact Hf' | exact Hf'']|].
intros a Ha Hna. rewrite (Hm'' a Ha Hna). apply Hm'; assumption.
Qed.
Definition ss_MDx : sstate :=
mkSS NT_MD sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 160 0 0
[mkChunk 56 (CVal 8 (SOff 32 0)); mkChunk 64 (CVal 8 (SOff 32 0)); mkChunk 72 (CVal 8 (SOff 32 0));
mkChunk 80 (CVal 8 (SOff 33 0)); mkChunk 88 (CVal 8 (SOff 34 0)); mkChunk 96 (CVal 8 (SOff 35 0))];
YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 16 40 [] ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4);
(18%nat, mkAF 0 (2^30) 0); (19%nat, mkAF 0 (2^30) 0); (21%nat, mkAF 4096 CEIL_MAX 0) ]
[ mkAC BC_GEU (SAlu ALU_XOR (SOff 10 16) (SLit (-1))) (SLit 0); mkAC BC_GEU (SAlu ALU_XOR (SOff 10 16) (SLit (-1))) (SLit 8);
mkAC BC_GEU (SAlu ALU_XOR (SOff 10 16) (SLit (-1))) (SLit 16) ] []).
Definition ss_MD : sstate := mkSST NT_MD sr_atoms (sfr_atoms 64) (ss_mem ss_MDx) None (ss_facts ss_MDx).
Definition MD_KEEP : list reg := [1; 2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma MD_entry : forall (fy : FPState) (regs : bvmap 5 word) mem (xs xm0 xm1 xm2 : Z),
frm_zero (@fp_csr fy) ->
getr regs 2 = Z_to_bv 64 spc -> getr regs 10 = Z_to_bv 64 res -> getr regs 18 = Z_to_bv 64 imax -> getr regs 19 = Z_to_bv 64 imin ->
getr regs 21 = Z_to_bv 64 palp ->
val_mem segs mem (spc + 56) 8 xs -> val_mem segs mem (spc + 64) 8 xs -> val_mem segs mem (spc + 72) 8 xs ->
val_mem segs mem (spc + 80) 8 xm0 -> val_mem segs mem (spc + 88) 8 xm1 -> val_mem segs mem (spc + 96) 8 xm2 ->
0 <= xs < 2 ^ 64 -> 0 <= xm0 < 2 ^ 64 -> 0 <= xm1 < 2 ^ 64 -> 0 <= xm2 < 2 ^ 64 ->
(forall a, res + 16 <= a < res + 40 -> writable_at segs mem a) ->
let vals := [xs; xm0; xm1; xm2] in
let E0 := Ereg regs (map (Z_to_bv 64) vals ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF segs E ss_MD (@mkst fy regs (Z_to_bv 64 NT_MD) mem rom) /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
(forall r : reg, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
bv_unsigned (ew E 32) = xs /\ bv_unsigned (ew E 33) = xm0 /\ bv_unsigned (ew E 34) = xm1 /\ bv_unsigned (ew E 35) = xm2 /\
bv_unsigned (ew E 2) = spc /\ bv_unsigned (ew E 10) = res.
Proof.
intros fy regs mem xs xm0 xm1 xm2 Hfrm Hr2 Hr10 Hr18 Hr19 Hr21 V56 V64 V72 V80 V88 V96 Rs R0 R1 R2 Hw vals E0 E.
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HU2 : bv_unsigned (ew E0 2) = spc) by (rewrite (HE0 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E0 10) = res) by (rewrite (HE0 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E0 18) = imax) by (rewrite (HE0 18%nat 18%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU19 : bv_unsigned (ew E0 19) = imin) by (rewrite (HE0 19%nat 19%bv eq_refl), Hr19; apply unsigned_lit_small; lia).
assert (HA : forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E0 (32 + j)) = v).
{ intros j v Hj Hv. rewrite (HV j v Hj). apply unsigned_lit_small. exact Hv. }
pose proof (HA 0%nat xs eq_refl Rs) as A32. pose proof (HA 1%nat xm0 eq_refl R0) as A33.
pose proof (HA 2%nat xm1 eq_refl R1) as A34. pose proof (HA 3%nat xm2 eq_refl R2) as A35.
cbn [Nat.add] in A32, A33, A34, A35.
assert (HX10 : ew E0 10 = Z_to_bv 64 res) by (rewrite (HE0 10%nat 10%bv eq_refl); exact Hr10).
assert (HX21 : bv_unsigned (ew E0 21) = palp) by (rewrite (HE0 21%nat 21%bv eq_refl), Hr21; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok segs fy E0 ss_MDx (@mkst fy regs (Z_to_bv 64 NT_MD) mem rom)).
{ unfold ss_MDx. subst E0. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?A32, ?A33, ?A34, ?A35; reflexivity | cbn; lia | cbn; lia | assumption]).
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia|]. constructor.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10. repeat split; lia.
- split; [|split; [|exact I]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HX21.
rewrite HU2, HU10, HU18, HU19. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert (spc mod 16 = 0) by (replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
repeat split; lia.
+ cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite !branch_geu_U, !(U_not_off _ 10 res 16 HX10 ltac:(lia) ltac:(lia)), !U_SLit.
rewrite !(zcanon_id 0), !(zcanon_id 8), !(zcanon_id 16) by (unfold M64; lia).
repeat split; apply negb_true_iff, Z.ltb_ge; lia. }
split; [exact (st_ok_enterF segs fy 64 E0 ss_MDx _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|].
rewrite !HEE by lia. repeat (split; [assumption|]). exact HU10.
Qed.
Definition MD_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 NT_L2) mem' rom) md2 /\
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 L2 A2 mem' md2 /\ frm_zero (@fp_csr fy') /\
getr regs' 12 = Z_to_bv 64 (res + 16) /\ getr regs' 13 = Z_to_bv 64 (3 * imin) /\ getr regs' 14 = Z_to_bv 64 1 /\
(forall r : reg, In r MD_KEEP -> getr regs' r = getr regs r) /\
fregs_preserved (@fp_regs fy) (@fp_regs fy') /\
(exists mn0 mn1 mn2,
val_mem segs mem' (res + 16) 8 mn0 /\ val_mem segs mem' (res + 24) 8 mn1 /\ val_mem segs mem' (res + 32) 8 mn2 /\
0 <= mn0 < 2 ^ 64 /\ 0 <= mn1 < 2 ^ 64 /\ 0 <= mn2 < 2 ^ 64 /\
is_quot mn0 (wdot (node_list pal fr imin imax 0)) (wsum (node_list pal fr imin imax 0)) /\
is_quot mn1 (wdot (node_list pal fr imin imax 1)) (wsum (node_list pal fr imin imax 1)) /\
is_quot mn2 (wdot (node_list pal fr imin imax 2)) (wsum (node_list pal fr imin imax 2)) /\
wdot (node_list pal fr imin imax 0) <= 255 * wsum (node_list pal fr imin imax 0) /\
wdot (node_list pal fr imin imax 1) <= 255 * wsum (node_list pal fr imin imax 1) /\
wdot (node_list pal fr imin imax 2) <= 255 * wsum (node_list pal fr imin imax 2)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (res + 16 <= a < res + 40) -> mbyte segs mem' a = mbyte segs mem a).
Lemma ntn_meandiv : forall (fy : FPState) (regs : bvmap 5 word) mem (xs xm0 xm1 xm2 : Z),
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 L2 A2 mem md2 ->
frm_zero (@fp_csr fy) ->
getr regs 2 = Z_to_bv 64 spc -> getr regs 10 = Z_to_bv 64 res -> getr regs 21 = Z_to_bv 64 palp ->
getr regs 18 = Z_to_bv 64 imax -> getr regs 19 = Z_to_bv 64 imin ->
val_mem segs mem (spc + 56) 8 xs -> val_mem segs mem (spc + 64) 8 xs -> val_mem segs mem (spc + 72) 8 xs ->
val_mem segs mem (spc + 80) 8 xm0 -> val_mem segs mem (spc + 88) 8 xm1 -> val_mem segs mem (spc + 96) 8 xm2 ->
0 <= xs < 2 ^ 64 -> 0 <= xm0 < 2 ^ 64 -> 0 <= xm1 < 2 ^ 64 -> 0 <= xm2 < 2 ^ 64 ->
is_intd xs (wsum (node_list pal fr imin imax 0)) ->
is_intd xm0 (wdot (node_list pal fr imin imax 0)) -> is_intd xm1 (wdot (node_list pal fr imin imax 1)) -> is_intd xm2 (wdot (node_list pal fr imin imax 2)) ->
(forall i, 0 <= i < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) (blocks L2 A2) (res + i)) ->
(forall a, res + 16 <= a < res + 40 -> writable_at segs mem a) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 NT_MD) mem rom) md2) (MD_post fy regs mem).
Proof.
intros fy regs mem xs xm0 xm1 xm2 HJ Hfrm Hr2 Hr10 Hr21 Hr18 Hr19 V56 V64 V72 V80 V88 V96 Rs R0 R1 R2 Is I0 I1 I2 Hwb Hw.
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
destruct (MD_entry fy regs mem xs xm0 xm1 xm2 Hfrm Hr2 Hr10 Hr18 Hr19 Hr21 V56 V64 V72 V80 V88 V96 Rs R0 R1 R2 Hw)
as (HS & HE & HEf & A32 & A33 & A34 & A35 & HU2 & HU10).
set (E := ew_fregs _ 64 _) in HS, HE, HEf, A32, A33, A34, A35, HU2, HU10.
assert (HU18 : bv_unsigned (ew E 18) = imax) by (rewrite (HE 18%nat 18%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU19 : bv_unsigned (ew E 19) = imin) by (rewrite (HE 19%nat 19%bv eq_refl), Hr19; apply unsigned_lit_small; lia).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 NT_MD) mem rom)) in HJ.
assert (Hwr : forall cs1 cs2, wr_ok E [YQ0b.mkRegion (Some 2%nat) 0 160 0 0 cs1; YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 16 40 cs2] STK sp0 FP (blocks L A) (blocks L2 A2)).
{ intros cs1 cs2. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_gen; [reflexivity | exact HU10 | cbn [r_wlo r_whi]; intros a Ha; replace a with (res + (a - res)) by lia; apply Hwb; lia | apply wr_ok_nil]. }
jrunF_to LAWS ubs2tbl_ok HS HJ NT_L2. { wr_ok_eval. apply Hwr. }
cbn [ms_mem mkst] in HF, HJ.
jbranchF ubs2tbl HS.
{ exfalso. rewrite branch_ltu_U, !U_SOff, HU18, HU19, !zcanon_id in Hc by (unfold M64; lia). rewrite !Z.add_0_r in Hc.
destruct (Z.ltb_spec imax imin); [lia | discriminate Hc]. }
clear Hc. jrunF_to LAWS ubs2tbl_ok HS HJ NT_L2. { wr_ok_eval. apply Hwr. }
cbn [ms_mem mkst] in HF0, HJ.
lazymatch type of HS with st_okF _ ?E1 ?ss1 ?ms1 =>
rewrite (st_okF_mkst segs E1 ss1 ms1 HS eq_refl); cbn [ss_pc];
apply SR_ret; exists (fp_of ms1), (ms_regs ms1), (ms_mem ms1);
pose proof (st_okF_regs_kept segs E1 ss1 ms1 _ MD_KEEP HS ltac:(intros r _; apply HE; pose proof (u5_range r); unfold ridx; lia) ltac:(vm_compute; reflexivity)) as Hk;
pose proof (st_okF_to_legacy segs E1 ss1 ms1 HS) as HSL
end.
split; [reflexivity|]. split; [exact HJ|]. split; [exact (st_okF_frm segs E _ _ HS)|].
split; [jregF HS (12%bv:reg) as Hq; rewrite Hq, HU10; reflexivity|].
split; [rewrite (st_okF_reg segs E _ _ 13%bv HS); match goal with |- sv_denot _ ?v = _ => let v' := eval vm_compute in v in change v with v' end;
rewrite denot_lit_U; f_equal; rewrite U_SMd; cbn [zmd_raw]; rewrite U_SOff, U_SLit, HU19, Z.add_0_r;
rewrite (zcanon_id imin), (zcanon_id 3) by (unfold M64; lia); rewrite zcanon_id by (unfold M64; lia); lia|].
split; [jregF HS (14%bv:reg) as Hq; rewrite Hq; reflexivity|].
split; [exact Hk|].
split; [intros rr Hrr; cbn [fp_regs fp_of]; exact (st_okF_fregs_kept segs E _ _ 64 (@fp_regs fy) FCALLEE_SAVED HS HEf ltac:(vm_compute; reflexivity) rr Hrr)|].
assert (Dat : forall n v, bv_unsigned (ew E n) = v -> bv_unsigned (sv_denot E (SOff n 0)) = v).
{ intros n v H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. }
assert (CV : forall off e, In (mkChunk off (CVal 8 e)) [mkChunk 32 (CVal 8 (SF2 (FP2_ari F_DIV FMT_D RNE) (SOff 35 0) (SOff 32 0)));
mkChunk 24 (CVal 8 (SF2 (FP2_ari F_DIV FMT_D RNE) (SOff 34 0) (SOff 32 0)));
mkChunk 16 (CVal 8 (SF2 (FP2_ari F_DIV FMT_D RNE) (SOff 33 0) (SOff 32 0)))] ->
val_mem segs (ms_mem ms0) (res + off) 8 (bv_unsigned (sv_denot E e))).
{ intros off e Hin. eapply (st_chunk_val segs E _ _ 1%nat _ 10%nat off 8%N e res _ HSL);
[reflexivity | reflexivity | exact Hin | exact HU10 | symmetry; apply Z_to_bv_bv_unsigned | change (8 * Z.of_N 8) with 64; apply u64_rangeN | cbn; lia]. }
assert (TM : forall d xm, 0 <= d <= 2 -> is_intd xm (wdot (node_list pal fr imin imax d)) ->
is_quot (fst (fp_div D RNE xm xs)) (wdot (node_list pal fr imin imax d)) (wsum (node_list pal fr imin imax d)) /\
wdot (node_list pal fr imin imax d) <= 255 * wsum (node_list pal fr imin imax d)).
{ intros d xm Hd Hxm. rewrite <- (nlp_full pal fr imin imax d) in *.
pose proof (nlp_node_ok pal fr imin imax Hii Hpalv Hfr1 Hlenp (imax + 1) d ltac:(lia) Hd) as Hok.
pose proof (wsum_nlp_le pal fr imin imax Hii Hfr1 Hsum (imax + 1) d ltac:(lia)) as Hws.
assert (Hne : nlp pal fr imin (imax + 1) d <> []).
{ unfold nlp, node_list. intros Hnil. apply (f_equal (@length _)) in Hnil. rewrite length_map, zseq_length in Hnil. cbn in Hnil. lia. }
rewrite <- (nlp_full pal fr imin imax 0) in Is. rewrite (wsum_nlp_dim pal fr imin (imax + 1) 0 d) in Is.
destruct (tree_mean xm xs _ Hok Hne ltac:(lia) Is Hxm) as (Hq & Hle & _). split; [exact Hq | exact Hle]. }
split.
{ exists (bv_unsigned (sv_denot E (SF2 (FP2_ari F_DIV FMT_D RNE) (SOff 33 0) (SOff 32 0)))),
(bv_unsigned (sv_denot E (SF2 (FP2_ari F_DIV FMT_D RNE) (SOff 34 0) (SOff 32 0)))),
(bv_unsigned (sv_denot E (SF2 (FP2_ari F_DIV FMT_D RNE) (SOff 35 0) (SOff 32 0)))).
split; [apply CV; cbn; tauto|]. split; [apply CV; cbn; tauto|]. split; [apply CV; cbn; tauto|].
split; [apply u64_rangeN|]. split; [apply u64_rangeN|]. split; [apply u64_rangeN|].
rewrite !val_fdiv, (Dat 32%nat xs A32), (Dat 33%nat xm0 A33), (Dat 34%nat xm1 A34), (Dat 35%nat xm2 A35).
destruct (TM 0 xm0 ltac:(lia) I0) as [Q0 L0]. destruct (TM 1 xm1 ltac:(lia) I1) as [Q1 L1']. destruct (TM 2 xm2 ltac:(lia) I2) as [Q2 L2'].
repeat (split; [assumption|]). exact L2'. }
intros a Ha Hna. mb_frames ltac:(exact Ha) ltac:(rewrite ?HU10; lia). reflexivity.
Qed.
End c.
End b.
