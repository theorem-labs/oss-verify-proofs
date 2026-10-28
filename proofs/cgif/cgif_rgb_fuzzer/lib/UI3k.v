(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals Lra.
From Flocq Require Import Core.Raux Core.Defs.
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
UI1e UI1i YI0x YP14 YI08 YI0c YI0f YI0d UI3h UI3j.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM07 YM05 YM04 YM01 YM02 YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
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
Hypothesis Hnp : res + NODE_SIZE <= palp \/ palp + zlen pal <= res. Hypothesis Hnf : res + NODE_SIZE <= frp \/ frp + 4 * zlen fr <= res.
Hypothesis Hbud : sp0 - STK <= spZ regs0 - NTN_STK. Hypothesis Hsptop : spZ regs0 <= sp0. Hypothesis Hal16 : spZ regs0 mod 16 = 0.
Hypothesis Hceil : alloc_ceiling + STK <= sp0. Hypothesis H63 : sp0 < 2 ^ 63.
Lemma ntn_consts : NODE_SIZE = 56 /\ NTN_STK = 160 + ALLOC_STACK /\ ALLOC_STACK = 8192 /\ RGB_NMAX = 10000 /\ (CEIL_MIN <= alloc_ceiling <= CEIL_MAX)  .
Proof. repeat match goal with H : _ |- _ => clear H end.   pose proof (proj1 alloc_ceiling_val). repeat split; first [reflexivity | lia]. Qed.
Local Ltac ntn_wr HU2 :=
wr_ok_eval; eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia |];
repeat (apply wr_ok_cons_ro; [cbn; lia|]); apply wr_ok_nil.
Variables (mn0 mn1 mn2 : Z).
Let l0 := node_list pal fr imin imax 0. Let l1 := node_list pal fr imin imax 1. Let l2 := node_list pal fr imin imax 2.
Hypothesis Rmn0 : 0 <= mn0 < 2 ^ 64. Hypothesis Rmn1 : 0 <= mn1 < 2 ^ 64. Hypothesis Rmn2 : 0 <= mn2 < 2 ^ 64.
Hypothesis Qmn0 : is_quot mn0 (wdot l0) (wsum l0). Hypothesis Qmn1 : is_quot mn1 (wdot l1) (wsum l1). Hypothesis Qmn2 : is_quot mn2 (wdot l2) (wsum l2).
Hypothesis Lmn0 : wdot l0 <= 255 * wsum l0. Hypothesis Lmn1 : wdot l1 <= 255 * wsum l1. Hypothesis Lmn2 : wdot l2 <= 255 * wsum l2.
Definition ss_L2x : sstate :=
mkSS NT_L2 (sr_set (sr_set sr_atoms 12%bv (SOff 10%nat 16)) 14%bv (SLit 1))
[ YQ0b.mkRegion (Some 2%nat) 0 160 8 56
[mkChunk 8 (CVal 8 (SOff 32 0)); mkChunk 16 (CVal 8 (SOff 32 0)); mkChunk 24 (CVal 8 (SOff 32 0));
mkChunk 32 (CVal 8 (SOff 33 0)); mkChunk 40 (CVal 8 (SOff 34 0)); mkChunk 48 (CVal 8 (SOff 35 0))];
YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 0 0 [mkChunk 16 (CVal 8 (SOff 42 0)); mkChunk 24 (CVal 8 (SOff 43 0)); mkChunk 32 (CVal 8 (SOff 44 0))];
YQ0b.mkRegion (Some 40%nat) 0 3 0 0 [mkChunk 0 (CVal 1 (SOff 36 0)); mkChunk 1 (CVal 1 (SOff 37 0)); mkChunk 2 (CVal 1 (SOff 38 0))];
YQ0b.mkRegion (Some 41%nat) 0 4 0 0 [mkChunk 0 (CVal 4 (SOff 39 0))] ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4); (19%nat, mkAF 0 (2^30) 0); (13%nat, mkAF 0 (3 * 2^30) 0); (18%nat, mkAF 0 (2^30) 0);
(21%nat, mkAF 4096 CEIL_MAX 0); (20%nat, mkAF 4096 CEIL_MAX 2); (40%nat, mkAF 4096 CEIL_MAX 0); (41%nat, mkAF 4096 CEIL_MAX 2);
(36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 (2^32 - 1) 0);
(11%nat, mkAF (2^64 - 1 - CEIL_MAX) (2^64 - 1 - 4096) 0) ]
[ mkAC BC_GEU (SOff 40 0) (SOff 21 0); mkAC BC_GEU (SOff 40 1) (SOff 21 0); mkAC BC_GEU (SOff 40 2) (SOff 21 0) ]
[ (SAlu ALU_ADD (SOff 21 0) (SOff 13 0), SOff 40%nat 0);
(SAlu ALU_ADD (SOff 20 0) (SAlu ALU_SLL (SOff 19 0) (SLit 2)), SOff 41%nat 0) ]).
Definition ss_L2 : sstate := mkSST NT_L2 (ss_regs ss_L2x) (sfr_atoms 64) (ss_mem ss_L2x) None (ss_facts ss_L2x).
Definition L2_KEEP : list reg := [1; 2; 3; 4; 8; 9; 10; 11; 18; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition L2_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (i : Z) : Prop :=
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 L2 A2 mem md2 /\
frm_zero (@fp_csr fy) /\
getr regs 2 = Z_to_bv 64 spc /\ getr regs 10 = Z_to_bv 64 res /\ getr regs 12 = Z_to_bv 64 (res + 16) /\
getr regs 13 = Z_to_bv 64 (3 * i) /\ getr regs 14 = Z_to_bv 64 1 /\ getr regs 11 = Z_to_bv 64 (2 ^ 64 - 1 - frp) /\
getr regs 18 = Z_to_bv 64 imax /\ getr regs 19 = Z_to_bv 64 i /\
getr regs 20 = Z_to_bv 64 frp /\ getr regs 21 = Z_to_bv 64 palp /\
arr8 segs mem palp pal /\ arr32 segs mem frp fr /\
val_mem segs mem (res + 16) 8 mn0 /\ val_mem segs mem (res + 24) 8 mn1 /\ val_mem segs mem (res + 32) 8 mn2 /\
exists xs xv0 xv1 xv2,
val_mem segs mem (spc + 8) 8 xs /\ val_mem segs mem (spc + 16) 8 xs /\ val_mem segs mem (spc + 24) 8 xs /\
val_mem segs mem (spc + 32) 8 xv0 /\ val_mem segs mem (spc + 40) 8 xv1 /\ val_mem segs mem (spc + 48) 8 xv2 /\
0 <= xs < 2 ^ 64 /\ 0 <= xv0 < 2 ^ 64 /\ 0 <= xv1 < 2 ^ 64 /\ 0 <= xv2 < 2 ^ 64 /\
is_intd xs (wsum (nlp pal fr imin i 0)) /\
vacc xv0 (i - imin) (neq_meanb (wsum l0) (wdot l0) (nlp pal fr imin i 0)) /\
vacc xv1 (i - imin) (neq_meanb (wsum l1) (wdot l1) (nlp pal fr imin i 1)) /\
vacc xv2 (i - imin) (neq_meanb (wsum l2) (wdot l2) (nlp pal fr imin i 2)).
Lemma L2_entry : forall (fy : FPState) (regs : bvmap 5 word) mem (i xs xv0 xv1 xv2 : Z),
imin <= i <= imax ->
frm_zero (@fp_csr fy) ->
getr regs 2 = Z_to_bv 64 spc -> getr regs 10 = Z_to_bv 64 res -> getr regs 12 = Z_to_bv 64 (res + 16) ->
getr regs 13 = Z_to_bv 64 (3 * i) -> getr regs 14 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 (2 ^ 64 - 1 - frp) ->
getr regs 18 = Z_to_bv 64 imax -> getr regs 19 = Z_to_bv 64 i ->
getr regs 20 = Z_to_bv 64 frp -> getr regs 21 = Z_to_bv 64 palp ->
arr8 segs mem palp pal -> arr32 segs mem frp fr ->
val_mem segs mem (res + 16) 8 mn0 -> val_mem segs mem (res + 24) 8 mn1 -> val_mem segs mem (res + 32) 8 mn2 ->
val_mem segs mem (spc + 8) 8 xs -> val_mem segs mem (spc + 16) 8 xs -> val_mem segs mem (spc + 24) 8 xs ->
val_mem segs mem (spc + 32) 8 xv0 -> val_mem segs mem (spc + 40) 8 xv1 -> val_mem segs mem (spc + 48) 8 xv2 ->
0 <= xs < 2 ^ 64 -> 0 <= xv0 < 2 ^ 64 -> 0 <= xv1 < 2 ^ 64 -> 0 <= xv2 < 2 ^ 64 ->
(forall a, spc + 8 <= a < spc + 56 -> writable_at segs mem a) ->
let vals := [xs; xv0; xv1; xv2; getz pal (3 * i); getz pal (3 * i + 1); getz pal (3 * i + 2); getz fr i; palp + 3 * i; frp + 4 * i; mn0; mn1; mn2] in
let E0 := Ereg regs (map (Z_to_bv 64) vals ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF segs E ss_L2 (@mkst fy regs (Z_to_bv 64 NT_L2) mem rom) /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
(forall r : reg, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
(forall k j v, nth_error vals j = Some v -> k = (32 + j)%nat -> ew E k = Z_to_bv 64 v) /\
bv_unsigned (ew E 2) = spc.
Proof.
intros fy regs mem i xs xv0 xv1 xv2 Hi Hfrm Hr2 Hr10 Hr12 Hr13 Hr14 Hr11 Hr18 Hr19 Hr20 Hr21 Hpa Hfa M16 M24 M32 V8 V16 V24 V32 V40 V48 Rs R0 R1 R2 Hw vals E0 E.
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
pose proof (pal_byte pal Hpalv) as Hpb. pose proof (fr_word fr Hfrv) as Hfw.
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HU2 : bv_unsigned (ew E0 2) = spc) by (rewrite (HE0 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E0 10) = res) by (rewrite (HE0 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
assert (HU13 : bv_unsigned (ew E0 13) = 3 * i) by (rewrite (HE0 13%nat 13%bv eq_refl), Hr13; apply unsigned_lit_small; lia).
assert (HU19 : bv_unsigned (ew E0 19) = i) by (rewrite (HE0 19%nat 19%bv eq_refl), Hr19; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E0 18) = imax) by (rewrite (HE0 18%nat 18%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU20 : bv_unsigned (ew E0 20) = frp) by (rewrite (HE0 20%nat 20%bv eq_refl), Hr20; apply unsigned_lit_small; lia).
assert (HU21 : bv_unsigned (ew E0 21) = palp) by (rewrite (HE0 21%nat 21%bv eq_refl), Hr21; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E0 11) = 2 ^ 64 - 1 - frp) by (rewrite (HE0 11%nat 11%bv eq_refl), Hr11; apply unsigned_lit_small; lia).
assert (HA : forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E0 (32 + j)) = v).
{ intros j v Hj Hv. rewrite (HV j v Hj). apply unsigned_lit_small. exact Hv. }
pose proof (Hpb (3 * i) ltac:(lia)) as P0. pose proof (Hpb (3 * i + 1) ltac:(lia)) as P1. pose proof (Hpb (3 * i + 2) ltac:(lia)) as P2.
pose proof (Hfw i ltac:(lia)) as Fi.
pose proof (HA 0%nat xs eq_refl Rs) as A32. pose proof (HA 1%nat xv0 eq_refl R0) as A33. pose proof (HA 2%nat xv1 eq_refl R1) as A34.
pose proof (HA 3%nat xv2 eq_refl R2) as A35. pose proof (HA 4%nat _ eq_refl ltac:(lia)) as A36. pose proof (HA 5%nat _ eq_refl ltac:(lia)) as A37.
pose proof (HA 6%nat _ eq_refl ltac:(lia)) as A38. pose proof (HA 7%nat _ eq_refl ltac:(lia)) as A39.
pose proof (HA 8%nat _ eq_refl ltac:(lia)) as A40. pose proof (HA 9%nat _ eq_refl ltac:(lia)) as A41.
pose proof (HA 10%nat mn0 eq_refl Rmn0) as A42. pose proof (HA 11%nat mn1 eq_refl Rmn1) as A43. pose proof (HA 12%nat mn2 eq_refl Rmn2) as A44.
cbn [Nat.add] in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44.
assert (HS0 : @st_ok segs fy E0 ss_L2x (@mkst fy regs (Z_to_bv 64 NT_L2) mem rom)).
{ unfold ss_L2x. subst E0. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 | cbn [sv_denot]; rewrite HU10; exact Hr12] | intros HH0; discriminate HH0 |].
rewrite Hr14. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia|].
repeat apply Forall_cons; [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?A32, ?A33, ?A34, ?A35; reflexivity | cbn; lia | cbn; lia | assumption]).
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?A42, ?A43, ?A44; reflexivity | cbn; lia | cbn; lia | assumption]).
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
rewrite HU2, HU10, A40, A41. repeat split; lia.
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU13, HU19, HU18, HU20, HU21, HU11, A36, A37, A38, A39, A40, A41. change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 0) with 1.
rewrite !Z.mod_1_r.
assert (spc mod 16 = 0) by (replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert ((frp + 4 * i) mod 4 = 0) by (replace (frp + 4 * i) with (frp + i * 4) by lia; rewrite Z.mod_add by lia; exact Hfr4).
repeat split; lia.
+ cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite !branch_geu_U, !U_SOff, A40, HU21, !Z.add_0_r.
rewrite (zcanon_id palp), (zcanon_id (palp + 3 * i)), (zcanon_id (palp + 3 * i + 1)), (zcanon_id (palp + 3 * i + 2)) by (unfold M64; lia).
repeat split; apply negb_true_iff, Z.ltb_ge; lia.
+ cbn [f_alias alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, HU21, HU13, A40, !Z.add_0_r. rewrite (zcanon_id palp), (zcanon_id (3 * i)) by (unfold M64; lia). reflexivity.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, HU20, HU19, A41, !Z.add_0_r.
rewrite (zcanon_id frp), (zcanon_id i) by (unfold M64; lia). change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 2) with 4. rewrite (zcanon_id (i * 4)) by (unfold M64; lia). f_equal. lia. }
split; [exact (st_ok_enterF segs fy 64 E0 ss_L2x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|].
split; [| rewrite HEE by lia; exact HU2].
intros k j v Hj ->. rewrite HEE; [apply HV; exact Hj|].
assert (Hl : (j < length vals)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). cbn in Hl. lia.
Qed.
Definition ss_L2_out : sstate := Eval vm_compute in (fst (sym_run_toFN segs ubs2tbl FUEL NT_L2END ss_L2)).
Lemma L2_read : forall E ss ms (i xs xv0 xv1 xv2 : Z),
st_okF segs E ss ms -> ss_mem ss = ss_mem ss_L2_out -> ss_regs ss = ss_regs ss_L2_out ->
imin <= i <= imax ->
bv_unsigned (ew E 2) = spc ->
bv_unsigned (ew E 32) = xs -> bv_unsigned (ew E 33) = xv0 -> bv_unsigned (ew E 34) = xv1 -> bv_unsigned (ew E 35) = xv2 ->
bv_unsigned (ew E 36) = getz pal (3 * i) -> bv_unsigned (ew E 37) = getz pal (3 * i + 1) -> bv_unsigned (ew E 38) = getz pal (3 * i + 2) ->
bv_unsigned (ew E 39) = getz fr i ->
bv_unsigned (ew E 42) = mn0 -> bv_unsigned (ew E 43) = mn1 -> bv_unsigned (ew E 44) = mn2 ->
bv_unsigned (ew E 13) = 3 * i -> bv_unsigned (ew E 19) = i ->
is_intd xs (wsum (nlp pal fr imin i 0)) ->
vacc xv0 (i - imin) (neq_meanb (wsum l0) (wdot l0) (nlp pal fr imin i 0)) ->
vacc xv1 (i - imin) (neq_meanb (wsum l1) (wdot l1) (nlp pal fr imin i 1)) ->
vacc xv2 (i - imin) (neq_meanb (wsum l2) (wdot l2) (nlp pal fr imin i 2)) ->
exists xs' xv0' xv1' xv2',
val_mem segs (ms_mem ms) (spc + 8) 8 xs' /\ val_mem segs (ms_mem ms) (spc + 16) 8 xs' /\ val_mem segs (ms_mem ms) (spc + 24) 8 xs' /\
val_mem segs (ms_mem ms) (spc + 32) 8 xv0' /\ val_mem segs (ms_mem ms) (spc + 40) 8 xv1' /\ val_mem segs (ms_mem ms) (spc + 48) 8 xv2' /\
0 <= xs' < 2 ^ 64 /\ 0 <= xv0' < 2 ^ 64 /\ 0 <= xv1' < 2 ^ 64 /\ 0 <= xv2' < 2 ^ 64 /\
is_intd xs' (wsum (nlp pal fr imin (i + 1) 0)) /\
vacc xv0' (i + 1 - imin) (neq_meanb (wsum l0) (wdot l0) (nlp pal fr imin (i + 1) 0)) /\
vacc xv1' (i + 1 - imin) (neq_meanb (wsum l1) (wdot l1) (nlp pal fr imin (i + 1) 1)) /\
vacc xv2' (i + 1 - imin) (neq_meanb (wsum l2) (wdot l2) (nlp pal fr imin (i + 1) 2)) /\
getr (ms_regs ms) 13 = Z_to_bv 64 (3 * (i + 1)) /\ getr (ms_regs ms) 19 = Z_to_bv 64 (i + 1).
Proof.
intros E ss ms i xs xv0 xv1 xv2 HS Hm Hr Hi HU2 A32 A33 A34 A35 A36 A37 A38 A39 A42 A43 A44 HU13 HU19 Is I0 I1 I2.
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
pose proof (pal_byte pal Hpalv) as Hpb. pose proof (fr_word fr Hfrv) as Hfw.
pose proof (Hpb (3 * i) ltac:(lia)) as P0. pose proof (Hpb (3 * i + 1) ltac:(lia)) as P1. pose proof (Hpb (3 * i + 2) ltac:(lia)) as P2.
pose proof (Hfw i ltac:(lia)) as Fi.
pose proof (wsum_nlp_le pal fr imin imax Hii Hfr1 Hsum (i + 1) 0 ltac:(lia)) as Ws.
rewrite (nlp_snoc pal fr imin i 0) in Ws by lia. rewrite wsum_snoc in Ws.
pose proof (wsum_nlp_le pal fr imin imax Hii Hfr1 Hsum i 0 ltac:(lia)) as Ws0.
assert (Hf : 1 <= getz fr i <= RGB_NMAX) by (pose proof (Hfr1 i ltac:(lia)); lia).
rewrite (nlp_snoc pal fr imin i 0), (nlp_snoc pal fr imin i 1), (nlp_snoc pal fr imin i 2) by lia.
rewrite !wsum_snoc, !neq_meanb_snoc. rewrite !(Z.add_0_r (3 * i)).
pose proof (st_okF_to_legacy segs E ss ms HS) as HSL.
assert (Dat : forall n v, bv_unsigned (ew E n) = v -> bv_unsigned (sv_denot E (SOff n 0)) = v).
{ intros n v H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. }
assert (CV : forall off e, In (mkChunk off (CVal 8 e)) (r_chunks (nth 0 (ss_mem ss) (YQ0b.mkRegion None 0 0 0 0 []))) ->
val_mem segs (ms_mem ms) (spc + off) 8 (bv_unsigned (sv_denot E e))).
{ intros off e Hin. rewrite Hm in Hin. eapply (st_chunk_val segs E ss ms 0%nat _ 2%nat off 8%N e spc _ HSL);
[rewrite Hm; reflexivity | reflexivity | cbn in Hin |- *; exact Hin | exact HU2 | symmetry; apply Z_to_bv_bv_unsigned | change (8 * Z.of_N 8) with 64; apply u64_rangeN | cbn; lia]. }
set (es := SF2 (FP2_ari F_ADD FMT_D RNE) (SOff 32 0) (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff 39 0))).
set (ev := fun (ep em ea : nat) =>
let t1 := SF2 (FP2_ari F_SUB FMT_D RNE) (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff ep 0)) (SOff em 0) in
SF3 (FP3_fma F_MADD FMT_D RNE) (SF2 (FP2_ari F_MUL FMT_D RNE) t1 (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff 39 0))) t1 (SOff ea 0)).
exists (bv_unsigned (sv_denot E es)), (bv_unsigned (sv_denot E (ev 36%nat 42%nat 33%nat))),
(bv_unsigned (sv_denot E (ev 37%nat 43%nat 34%nat))), (bv_unsigned (sv_denot E (ev 38%nat 44%nat 35%nat))).
split; [apply CV; rewrite Hm; cbn; tauto|]. split; [apply CV; rewrite Hm; cbn; tauto|]. split; [apply CV; rewrite Hm; cbn; tauto|].
split; [apply CV; rewrite Hm; cbn; tauto|]. split; [apply CV; rewrite Hm; cbn; tauto|]. split; [apply CV; rewrite Hm; cbn; tauto|].
split; [apply u64_rangeN|]. split; [apply u64_rangeN|]. split; [apply u64_rangeN|]. split; [apply u64_rangeN|].
split; [subst es; apply val_fadd; [rewrite (Dat 32%nat xs A32); exact Is | apply val_cvt_wu; [apply Dat; exact A39 | lia] | rewrite HNM in Ws; lia]|].
assert (VS : forall (ep em ea : nat) (p mean acc : Z) (l : list (Z * Z)) (pos : bool),
bv_unsigned (ew E ep) = p -> 0 <= p < 256 -> bv_unsigned (ew E em) = mean -> bv_unsigned (ew E ea) = acc ->
is_quot mean (wdot l) (wsum l) -> wdot l <= 255 * wsum l ->
vacc acc (i - imin) pos ->
vacc (bv_unsigned (sv_denot E (ev ep em ea))) (i + 1 - imin) (pos || negb (p * wsum l =? wdot l))%bool).
{ intros ep em ea p mean acc l pos Hp Hpr Hmean Hacc Hq Hle Hv.
unfold ev. rewrite val_vstep. cbv zeta. rewrite (Dat em mean Hmean), (Dat ea acc Hacc).
replace (i + 1 - imin) with (i - imin + 1) by lia.
refine (proj1 (variance_step _ p mean (wdot l) (wsum l) _ (getz fr i) acc (i - imin) pos _ _ Hq Hle _ _ Hv _ _));
[apply val_cvt_wu; [apply Dat; exact Hp | lia] | lia | apply val_cvt_wu; [apply Dat; exact A39 | lia] | lia | lia | lia]. }
split; [apply (VS 36%nat 42%nat 33%nat _ mn0 xv0 l0); assumption || lia|].
split; [apply (VS 37%nat 43%nat 34%nat _ mn1 xv1 l1); assumption || lia|].
split; [apply (VS 38%nat 44%nat 35%nat _ mn2 xv2 l2); assumption || lia|].
split.
- rewrite (st_okF_reg segs E ss ms 13%bv HS), Hr. match goal with |- sv_denot _ ?v = _ => let v' := eval vm_compute in v in change v with v' end.
cbn [sv_denot]. rewrite HU13. f_equal; lia.
- rewrite (st_okF_reg segs E ss ms 19%bv HS), Hr. match goal with |- sv_denot _ ?v = _ => let v' := eval vm_compute in v in change v with v' end.
cbn [sv_denot]. rewrite HU19. reflexivity.
Qed.
Definition L2_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc : Z) (j : Z) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' rom) md2 /\
L2_inv fy' regs' mem' j /\
(forall r : reg, In r L2_KEEP -> getr regs' r = getr regs r) /\
fregs_preserved (@fp_regs fy) (@fp_regs fy') /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 8 <= a < spc + 56) -> mbyte segs mem' a = mbyte segs mem a).
Lemma L2_step : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
imin <= i <= imax -> L2_inv fy regs mem i ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 NT_L2) mem rom) md2) (L2_post fy regs mem (if i <? imax then NT_L2 else NT_VA) (i + 1)).
Proof.
intros fy regs mem i Hi (HJ & Hfrm & Hr2 & Hr10 & Hr12 & Hr13 & Hr14 & Hr11 & Hr18 & Hr19 & Hr20 & Hr21 & Hpa & Hfa & M16 & M24 & M32 & xs & xv0 & xv1 & xv2 &
V8 & V16 & V24 & V32 & V40 & V48 & Rs & R0 & R1 & R2 & Is & I0 & I1 & I2).
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _).
destruct (L2_entry fy regs mem i xs xv0 xv1 xv2 Hi Hfrm Hr2 Hr10 Hr12 Hr13 Hr14 Hr11 Hr18 Hr19 Hr20 Hr21 Hpa Hfa M16 M24 M32 V8 V16 V24 V32 V40 V48 Rs R0 R1 R2
ltac:(intros a Ha; apply Hstw; lia)) as (HS & HE & HEf & HV & HU2).
set (E := ew_fregs _ 64 _) in HS, HE, HEf, HV, HU2.
assert (HA : forall k j v, nth_error [xs; xv0; xv1; xv2; getz pal (3 * i); getz pal (3 * i + 1); getz pal (3 * i + 2); getz fr i; palp + 3 * i; frp + 4 * i; mn0; mn1; mn2] j = Some v ->
k = (32 + j)%nat -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E k) = v).
{ intros k j v Hj Hk Hv. rewrite (HV k j v Hj Hk). apply unsigned_lit_small. exact Hv. }
pose proof (pal_byte pal Hpalv) as Hpb. pose proof (fr_word fr Hfrv) as Hfw.
pose proof (HA 32%nat 0%nat xs eq_refl eq_refl Rs) as A32. pose proof (HA 33%nat 1%nat xv0 eq_refl eq_refl R0) as A33.
pose proof (HA 34%nat 2%nat xv1 eq_refl eq_refl R1) as A34. pose proof (HA 35%nat 3%nat xv2 eq_refl eq_refl R2) as A35.
pose proof (HA 36%nat 4%nat _ eq_refl eq_refl (ltac:(pose proof (Hpb (3 * i) ltac:(lia)); lia))) as A36.
pose proof (HA 37%nat 5%nat _ eq_refl eq_refl (ltac:(pose proof (Hpb (3 * i + 1) ltac:(lia)); lia))) as A37.
pose proof (HA 38%nat 6%nat _ eq_refl eq_refl (ltac:(pose proof (Hpb (3 * i + 2) ltac:(lia)); lia))) as A38.
pose proof (HA 39%nat 7%nat _ eq_refl eq_refl (ltac:(pose proof (Hfw i ltac:(lia)); lia))) as A39.
pose proof (HA 42%nat 10%nat mn0 eq_refl eq_refl Rmn0) as A42. pose proof (HA 43%nat 11%nat mn1 eq_refl eq_refl Rmn1) as A43.
pose proof (HA 44%nat 12%nat mn2 eq_refl eq_refl Rmn2) as A44.
assert (HU13 : bv_unsigned (ew E 13) = 3 * i) by (rewrite (HE 13%nat 13%bv eq_refl), Hr13; apply unsigned_lit_small; lia).
assert (HU19 : bv_unsigned (ew E 19) = i) by (rewrite (HE 19%nat 19%bv eq_refl), Hr19; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 18) = imax) by (rewrite (HE 18%nat 18%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = res) by (rewrite (HE 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 NT_L2) mem rom)) in HJ.
jrunF_to LAWS ubs2tbl_ok HS HJ NT_L2END. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF, HJ.
assert (POST : forall ss1 ms1 pc, st_okF segs E ss1 ms1 -> ss_mem ss1 = ss_mem ss_L2_out -> ss_regs ss1 = ss_regs ss_L2_out -> ss_resv ss1 = None -> ss_pc ss1 = pc ->
ss_fregs ss1 = ss_fregs ss_L2_out ->
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 L2 A2 (ms_mem ms1) md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 8 <= a < spc + 56) -> mbyte segs (ms_mem ms1) a = mbyte segs mem a) ->
L2_post fy regs mem pc (i + 1) (mkCfg ms1 md2)).
{ intros ss1 ms1 pc HS1 Hm1 Hr1 Hrv1 Hpc1 Hf1 HJ1 Hmb.
destruct (L2_read E _ _ i xs xv0 xv1 xv2 HS1 Hm1 Hr1 Hi HU2 A32 A33 A34 A35 A36 A37 A38 A39 A42 A43 A44 HU13 HU19 Is I0 I1 I2)
as (xs' & xv0' & xv1' & xv2' & W8 & W16 & W24 & W32 & W40 & W48 & Rs' & R0' & R1' & R2' & Is' & I0' & I1' & I2' & Hq13 & Hq19).
pose proof (st_okF_regs_kept segs E ss1 ms1 _ L2_KEEP HS1 ltac:(intros r _; apply HE; pose proof (u5_range r); unfold ridx; lia) ltac:(rewrite Hr1; vm_compute; reflexivity)) as Hk.
exists (fp_of ms1), (ms_regs ms1), (ms_mem ms1).
split; [rewrite (st_okF_mkst segs E ss1 ms1 HS1 Hrv1), Hpc1; reflexivity|].
split.
{ split; [exact HJ1|]. split; [exact (st_okF_frm segs E _ _ HS1)|].
split; [rewrite (Hk 2%bv ltac:(cbv; tauto)); exact Hr2|]. split; [rewrite (Hk 10%bv ltac:(cbv; tauto)); exact Hr10|].
split; [rewrite (st_okF_reg segs E ss1 ms1 12%bv HS1), Hr1; match goal with |- sv_denot _ ?v = _ => let v' := eval vm_compute in v in change v with v' end;
cbn [sv_denot]; rewrite HU10; reflexivity|].
split; [exact Hq13|].
split; [rewrite (st_okF_reg segs E ss1 ms1 14%bv HS1), Hr1; match goal with |- sv_denot _ ?v = _ => let v' := eval vm_compute in v in change v with v' end;
reflexivity|].
split; [rewrite (Hk 11%bv ltac:(cbv; tauto)); exact Hr11|].
split; [rewrite (Hk 18%bv ltac:(cbv; tauto)); exact Hr18|]. split; [exact Hq19|].
split; [rewrite (Hk 20%bv ltac:(cbv; tauto)); exact Hr20|]. split; [rewrite (Hk 21%bv ltac:(cbv; tauto)); exact Hr21|].
split; [eapply arr8_frame; [exact Hpa|]; intros a Ha; apply Hmb; lia|].
split; [eapply arr32_frame; [exact Hfa|]; intros a Ha; apply Hmb; lia|].
split; [intros k Hk'; rewrite Hmb by lia; apply M16; exact Hk'|].
split; [intros k Hk'; rewrite Hmb by lia; apply M24; exact Hk'|].
split; [intros k Hk'; rewrite Hmb by lia; apply M32; exact Hk'|].
exists xs', xv0', xv1', xv2'. repeat (split; [assumption|]). exact I2'. }
split; [exact Hk|].
split; [intros rr Hrr; cbn [fp_regs fp_of]; apply (st_okF_fregs_kept segs E _ _ 64 (@fp_regs fy) FCALLEE_SAVED HS1 HEf); [rewrite Hf1; vm_compute; reflexivity|exact Hrr]|].
exact Hmb. }
jbranchF ubs2tbl HS.
- rewrite branch_geu_U, !U_SOff, HU18, HU19, !zcanon_id in Hc by (unfold M64; lia). rewrite !Z.add_0_r in Hc.
destruct (Z_lt_ge_dec i imax) as [Hlt|Hge]; [| exfalso; destruct (Z.ltb_spec imax (i + 1)); [discriminate Hc | lia]].
jrunF_to LAWS ubs2tbl_ok HS HJ NT_L2. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF0, HJ. replace (i <? imax) with true by (symmetry; apply Z.ltb_lt; lia).
apply SR_ret. eapply (POST _ _ NT_L2 HS); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HJ |].
intros a Ha Hna. mb_frames ltac:(exact Ha) ltac:(rewrite ?HU2; lia). reflexivity.
- rewrite branch_geu_U, !U_SOff, HU18, HU19, !zcanon_id in Hc by (unfold M64; lia). rewrite !Z.add_0_r in Hc.
destruct (Z_lt_ge_dec i imax) as [Hlt|Hge]; [exfalso; destruct (Z.ltb_spec imax (i + 1)); [lia | discriminate Hc] |].
jrunF_to LAWS ubs2tbl_ok HS HJ NT_VA. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF0, HJ. replace (i <? imax) with false by (symmetry; apply Z.ltb_ge; lia).
apply SR_ret. eapply (POST _ _ NT_VA HS); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HJ |].
intros a Ha Hna. mb_frames ltac:(exact Ha) ltac:(rewrite ?HU2; lia). reflexivity.
Qed.
Lemma ntn_loop2 : forall (k : nat) (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
imin <= i <= imax -> Z.of_nat k = imax - i -> L2_inv fy regs mem i ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 NT_L2) mem rom) md2) (L2_post fy regs mem NT_VA (imax + 1)).
Proof.
induction k as [|k IH]; intros fy regs mem i Hi Hk HI.
- assert (Hii' : i = imax) by lia. subst i.
eapply SR_mono; [exact (L2_step fy regs mem imax Hi HI)|].
cbv beta. intros c' (fy' & regs' & mem' & -> & HI' & Hk' & Hf' & Hm'). rewrite Z.ltb_irrefl.
exists fy', regs', mem'. repeat (split; [first [reflexivity | assumption]|]). exact Hm'.
- eapply SR_bind; [exact (L2_step fy regs mem i Hi HI)|].
cbv beta. intros c' (fy' & regs' & mem' & -> & HI' & Hk' & Hf' & Hm').
replace (i <? imax) with true by (symmetry; apply Z.ltb_lt; lia).
eapply SR_mono; [exact (IH fy' regs' mem' (i + 1) ltac:(lia) ltac:(lia) HI')|].
cbv beta. intros c'' (fy'' & regs'' & mem'' & -> & HI'' & Hk'' & Hf'' & Hm'').
exists fy'', regs'', mem''. split; [reflexivity|]. split; [exact HI''|].
split; [intros r Hr; rewrite (Hk'' r Hr); apply Hk'; exact Hr|].
split; [eapply fregs_preserved_trans; [exact Hf' | exact Hf'']|].
intros a Ha Hna. rewrite (Hm'' a Ha Hna). apply Hm'; assumption.
Qed.
Definition ss_VAx : sstate :=
mkSS NT_VA sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 160 80 104
[mkChunk 8 (CVal 8 (SOff 32 0)); mkChunk 16 (CVal 8 (SOff 32 0)); mkChunk 24 (CVal 8 (SOff 32 0));
mkChunk 32 (CVal 8 (SOff 33 0)); mkChunk 40 (CVal 8 (SOff 34 0)); mkChunk 48 (CVal 8 (SOff 35 0))] ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Definition ss_VA : sstate := mkSST NT_VA (ss_regs ss_VAx) (sfr_atoms 64) (ss_mem ss_VAx) None (ss_facts ss_VAx).
Definition VA_KEEP : list reg := [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma VA_entry : forall (fy : FPState) (regs : bvmap 5 word) mem (xs xv0 xv1 xv2 : Z),
frm_zero (@fp_csr fy) ->
getr regs 2 = Z_to_bv 64 spc ->
val_mem segs mem (spc + 8) 8 xs -> val_mem segs mem (spc + 16) 8 xs -> val_mem segs mem (spc + 24) 8 xs ->
val_mem segs mem (spc + 32) 8 xv0 -> val_mem segs mem (spc + 40) 8 xv1 -> val_mem segs mem (spc + 48) 8 xv2 ->
0 <= xs < 2 ^ 64 -> 0 <= xv0 < 2 ^ 64 -> 0 <= xv1 < 2 ^ 64 -> 0 <= xv2 < 2 ^ 64 ->
(forall a, spc + 80 <= a < spc + 104 -> writable_at segs mem a) ->
let vals := [xs; xv0; xv1; xv2] in
let E0 := Ereg regs (map (Z_to_bv 64) vals ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF segs E ss_VA (@mkst fy regs (Z_to_bv 64 NT_VA) mem rom) /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
(forall r : reg, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
bv_unsigned (ew E 32) = xs /\ bv_unsigned (ew E 33) = xv0 /\ bv_unsigned (ew E 34) = xv1 /\ bv_unsigned (ew E 35) = xv2 /\
bv_unsigned (ew E 2) = spc.
Proof.
intros fy regs mem xs xv0 xv1 xv2 Hfrm Hr2 V8 V16 V24 V32 V40 V48 Rs R0 R1 R2 Hw vals E0 E.
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HU2 : bv_unsigned (ew E0 2) = spc) by (rewrite (HE0 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HA : forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E0 (32 + j)) = v).
{ intros j v Hj Hv. rewrite (HV j v Hj). apply unsigned_lit_small. exact Hv. }
pose proof (HA 0%nat xs eq_refl Rs) as A32. pose proof (HA 1%nat xv0 eq_refl R0) as A33.
pose proof (HA 2%nat xv1 eq_refl R1) as A34. pose proof (HA 3%nat xv2 eq_refl R2) as A35.
cbn [Nat.add] in A32, A33, A34, A35.
assert (HS0 : @st_ok segs fy E0 ss_VAx (@mkst fy regs (Z_to_bv 64 NT_VA) mem rom)).
{ unfold ss_VAx. subst E0. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia|].
repeat apply Forall_cons; [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?A32, ?A33, ?A34, ?A35; reflexivity | cbn; lia | cbn; lia | assumption]).
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16.
assert (spc mod 16 = 0) by (replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
repeat split; lia. }
split; [exact (st_ok_enterF segs fy 64 E0 ss_VAx _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|].
rewrite !HEE by lia. repeat (split; [assumption|]). exact HU2.
Qed.
End c.
End b.
