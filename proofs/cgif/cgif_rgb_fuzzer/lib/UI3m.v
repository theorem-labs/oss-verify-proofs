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
UI1e UI1i YI0x YP14 YI08 YI0c YI0f YI0d UI3h UI3j UI3k UI3l.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM07 YM05 YM04 YM01 YM02 YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Local Abbreviation D := fmt_double.
Definition NT_RET0 : Z := Eval vm_compute in (ubs2_A_new_tree_node + 0x40).
Definition NT_EPI : Z := Eval vm_compute in (ubs2_A_new_tree_node + 0x2b0).
Definition NT_RET : Z := Eval vm_compute in (ubs2_A_new_tree_node + 0x2d0).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Local Notation segs := ubs2segs.
Local Notation rom := (seg_rom ubs2segs).
Local Notation tp := (ms_tp ubs2_msyms).
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
Hypothesis Hcidx : 0 <= cidx < 256.
Hypothesis Hnln0 : spZ regs0 <= nln. Hypothesis Hnln1 : nln + 2 <= sp0. Hypothesis Hnln2 : nln mod 2 = 0.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Lemma ntn_consts : NODE_SIZE = 56 /\ NTN_STK = 160 + ALLOC_STACK /\ ALLOC_STACK = 8192 /\ RGB_NMAX = 10000 /\ (CEIL_MIN <= alloc_ceiling <= CEIL_MAX)  .
Proof. repeat match goal with H : _ |- _ => clear H end.   pose proof (proj1 alloc_ceiling_val). repeat split; first [reflexivity | lia]. Qed.
Definition NT_KEEP : list reg := [3; 4; 22; 23; 24; 25; 26; 27]%bv.
Definition saved_ok (mem : word -> option byte) : Prop :=
val_mem segs mem (spc + 104) 8 (bv_unsigned (getr regs0 21)) /\ val_mem segs mem (spc + 112) 8 (bv_unsigned (getr regs0 20)) /\
val_mem segs mem (spc + 120) 8 (bv_unsigned (getr regs0 19)) /\ val_mem segs mem (spc + 128) 8 (bv_unsigned (getr regs0 18)) /\
val_mem segs mem (spc + 136) 8 (bv_unsigned (getr regs0 9)) /\ val_mem segs mem (spc + 144) 8 (bv_unsigned (getr regs0 8)) /\
val_mem segs mem (spc + 152) 8 (bv_unsigned (getr regs0 1)).
Lemma saved_ok_frame : forall mem mem', saved_ok mem ->
(forall a, spc + 104 <= a < spc + 160 -> mbyte segs mem' a = mbyte segs mem a) -> saved_ok mem'.
Proof.
intros mem mem' (S1 & S2 & S3 & S4 & S5 & S6 & S7) Hf.
clear Hii Himax Hlenp Hlenf Hpalv Hfrv Hfr1 Hsum Hpalp Hpalhi Hfrp Hfrhi Hfr4 Hpfd Hres0 Hres1 Hres16 Hnp Hnf Hcidx Hnln0 Hnln1 Hnln2 Hra Hbud Hsptop Hal16 Hceil H63.
repeat split; intros k Hk; (rewrite Hf; [first [apply S1 | apply S2 | apply S3 | apply S4 | apply S5 | apply S6 | apply S7]; exact Hk | lia]).
Qed.
Definition ss_TL : sstate :=
mkSS NT_TAIL sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 160 0 0
[mkChunk 104 (CVal 8 (SOff 32 0)); mkChunk 112 (CVal 8 (SOff 33 0)); mkChunk 120 (CVal 8 (SOff 34 0));
mkChunk 128 (CVal 8 (SOff 35 0)); mkChunk 136 (CVal 8 (SOff 36 0)); mkChunk 144 (CVal 8 (SOff 37 0)); mkChunk 152 (CVal 8 (SOff 38 0))];
YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 48 51 [];
YQ0b.mkRegion (Some 8%nat) 0 2 0 2 [mkChunk 0 (CVal 2 (SOff 39 0))] ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4); (8%nat, mkAF CEIL_MIN (2^63) 1);
(39%nat, mkAF 0 (2^16 - 2) 0); (15%nat, mkAF 0 2 0); (9%nat, mkAF 0 255 0) ] [] []).
Definition TL_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (cut n0 : Z) : config -> Prop :=
fun c' => exists regs' mem',
c' = mkCfg (@mkst fy regs' (getr regs0 1) mem' rom) md2 /\
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 L2 A2 mem' md2 /\
getr regs' 2 = getr regs0 2 /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\
getr regs' 18 = getr regs0 18 /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21 /\
getr regs' 10 = Z_to_bv 64 res /\
(forall r : reg, In r NT_KEEP -> getr regs' r = getr regs r) /\
val_mem segs mem' (res + 48) 1 cut /\ val_mem segs mem' (res + 49) 1 cidx /\ val_mem segs mem' (res + 50) 1 1 /\
val_mem segs mem' nln 2 (n0 + 1) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (res + 48 <= a < res + 51) -> ~ (nln <= a < nln + 2) -> mbyte segs mem' a = mbyte segs mem a).
Lemma ntn_tail : forall (fy : FPState) (regs : bvmap 5 word) mem (cut n0 : Z),
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 L2 A2 mem md2 ->
getr regs 2 = Z_to_bv 64 spc -> getr regs 8 = Z_to_bv 64 nln -> getr regs 9 = Z_to_bv 64 cidx -> getr regs 10 = Z_to_bv 64 res ->
getr regs 15 = Z_to_bv 64 cut -> 0 <= cut <= 2 ->
saved_ok mem -> val_mem segs mem nln 2 n0 -> 0 <= n0 < 2 ^ 16 - 1 ->
(forall i, 0 <= i < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) (blocks L2 A2) (res + i)) ->
(forall a, res + 48 <= a < res + 51 -> writable_at segs mem a) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 NT_TAIL) mem rom) md2) (TL_post fy regs mem cut n0).
Proof.
intros fy regs mem cut n0 HJ Hr2 Hr8 Hr9 Hr10 Hr15 Hcut HSV Vn Rn0 Hwb Hw.
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
clear Hii Himax Hlenp Hlenf Hpalv Hfrv Hfr1 Hsum Hpalp Hpalhi Hfrp Hfrhi Hfr4 Hpfd Hnp Hnf.
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _).
pose proof HSV as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
set (vals := [bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 18);
bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 1); n0]).
set (E := Ereg regs (map (Z_to_bv 64) vals ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = spc) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = nln) by (rewrite (HE 8%nat 8%bv eq_refl), Hr8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = cidx) by (rewrite (HE 9%nat 9%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = res) by (rewrite (HE 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
assert (HU15 : bv_unsigned (ew E 15) = cut) by (rewrite (HE 15%nat 15%bv eq_refl), Hr15; apply unsigned_lit_small; lia).
pose proof (u64_rangeN (getr regs0 21)) as R21. pose proof (u64_rangeN (getr regs0 20)) as R20. pose proof (u64_rangeN (getr regs0 19)) as R19.
pose proof (u64_rangeN (getr regs0 18)) as R18. pose proof (u64_rangeN (getr regs0 9)) as R9. pose proof (u64_rangeN (getr regs0 8)) as R8.
pose proof (u64_rangeN (getr regs0 1)) as R1.
assert (A32 : ew E 32 = getr regs0 21) by (change 32%nat with (32 + 0)%nat; rewrite (HV 0%nat _ eq_refl); apply Z_to_bv_bv_unsigned).
assert (A33 : ew E 33 = getr regs0 20) by (change 33%nat with (32 + 1)%nat; rewrite (HV 1%nat _ eq_refl); apply Z_to_bv_bv_unsigned).
assert (A34 : ew E 34 = getr regs0 19) by (change 34%nat with (32 + 2)%nat; rewrite (HV 2%nat _ eq_refl); apply Z_to_bv_bv_unsigned).
assert (A35 : ew E 35 = getr regs0 18) by (change 35%nat with (32 + 3)%nat; rewrite (HV 3%nat _ eq_refl); apply Z_to_bv_bv_unsigned).
assert (A36 : ew E 36 = getr regs0 9) by (change 36%nat with (32 + 4)%nat; rewrite (HV 4%nat _ eq_refl); apply Z_to_bv_bv_unsigned).
assert (A37 : ew E 37 = getr regs0 8) by (change 37%nat with (32 + 5)%nat; rewrite (HV 5%nat _ eq_refl); apply Z_to_bv_bv_unsigned).
assert (A38 : ew E 38 = getr regs0 1) by (change 38%nat with (32 + 6)%nat; rewrite (HV 6%nat _ eq_refl); apply Z_to_bv_bv_unsigned).
assert (A39 : ew E 39 = Z_to_bv 64 n0) by (change 39%nat with (32 + 7)%nat; apply (HV 7%nat _ eq_refl)).
assert (HS : @st_ok segs fy E ss_TL (@mkst fy regs (Z_to_bv 64 NT_TAIL) mem rom)).
{ unfold ss_TL. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?A32, ?A33, ?A34, ?A35, ?A36, ?A37, ?A38; reflexivity
| cbn; lia | cbn; lia | assumption]).
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia|]. constructor.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A39, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vn].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU8, HU10. repeat split; lia.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU8, HU9, HU10, HU15, A39, unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 1) with 2. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert (spc mod 16 = 0) by (replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
repeat split; lia. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 NT_TAIL) mem rom)) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ NT_RET.
{ wr_ok_eval. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_gen; [reflexivity | exact HU10 | cbn [r_wlo r_whi]; intros a Ha; replace a with (res + (a - res)) by lia; apply Hwb; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU8 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (SR_ret_at (fx:=fy) segs ubs2tbl E1 ss1 ms1 _ _ ubs2tbl_ok);
[ exact Hh | exact Hlz | exact HS | reflexivity | vm_compute; reflexivity | ];
exists (ms_regs ms1), (ms_mem ms1)
end.
jreg HS (1%bv:reg) as Q1. jreg HS (2%bv:reg) as Q2. jreg HS (8%bv:reg) as Q8. jreg HS (9%bv:reg) as Q9. jreg HS (10%bv:reg) as Q10.
jreg HS (18%bv:reg) as Q18. jreg HS (19%bv:reg) as Q19. jreg HS (20%bv:reg) as Q20. jreg HS (21%bv:reg) as Q21.
cbn [ms_regs mkst] in Q1, Q2, Q8, Q9, Q10, Q18, Q19, Q20, Q21.
split; [rewrite Q1, A38, Hra; reflexivity|].
split; [exact HJ|].
split; [rewrite Q2, HU2; unfold spZ; rewrite Z.sub_add; apply Z_to_bv_bv_unsigned|].
split; [rewrite Q8, A37; reflexivity|]. split; [rewrite Q9, A36; reflexivity|].
split; [rewrite Q18, A35; reflexivity|]. split; [rewrite Q19, A34; reflexivity|].
split; [rewrite Q20, A33; reflexivity|]. split; [rewrite Q21, A32; reflexivity|].
split; [rewrite Q10, (HE 10%nat 10%bv eq_refl); exact Hr10|].
split; [exact (regs_kept_of_st_ok _ _ _ _ regs _ NT_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity))|].
split; [eapply (st_chunk_val segs E _ _ 1%nat _ 10%nat 48 1%N (SOff 15 0) res cut HS); [reflexivity | reflexivity | cbv; tauto | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, (HE 15%nat 15%bv eq_refl), Z_to_bv_bv_unsigned; exact Hr15 | cbn; lia | cbn; lia]|].
split; [eapply (st_chunk_val segs E _ _ 1%nat _ 10%nat 49 1%N (SOff 9 0) res cidx HS); [reflexivity | reflexivity | cbv; tauto | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, (HE 9%nat 9%bv eq_refl), Z_to_bv_bv_unsigned; exact Hr9 | cbn; lia | cbn; lia]|].
split; [eapply (st_chunk_val segs E _ _ 1%nat _ 10%nat 50 1%N (SLit 1) res 1 HS); [reflexivity | reflexivity | cbv; tauto | exact HU10 | reflexivity | cbn; lia | cbn; lia]|].
split.
{ pose proof (st_region_chunks segs E _ _ 2%nat _ 8%nat nln HS eq_refl eq_refl HU8) as Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ ltac:(left; reflexivity)) as Hc.
pose proof (val_mem_low_of_chunk segs E _ nln 0 2%N _ Hc ltac:(cbn; lia)) as V. rewrite Z.add_0_r in V.
replace (bv_unsigned _ mod _) with (n0 + 1) in V; [exact V|].
change (bv_unsigned ?x) with (U E (SAlu ALU_ADD (SExt true 16 (SOff 39 0)) (SLit 1))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SExt, U_SLit, (U_atom E 39 n0 A39) by lia.
change (2 ^ Z.of_N 16) with (2 ^ 16). change (8 * Z.of_N 2) with 16.
unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.mul Z.modulo Z.div Z.sub Z.pow].
clear - Rn0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
change (2 ^ 16) with 65536. change (2 ^ 64) with 18446744073709551616. change (Z.of_N 64) with 64. change (Z.of_N 16) with 16.
change (2 ^ 64) with 18446744073709551616. change (2 ^ (16 - 1)) with 32768.
nia. }
intros a Ha Hn1 Hn2. mb_frame_g HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8, ?HU10; lia). reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition ss_P0 : sstate :=
mkSS ubs2_A_new_tree_node sr_atoms [ YQ0b.mkRegion (Some 2%nat) (-160) 0 (-160) 0 [] ] None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + 160) (2^63) 4) ] [] []).
Definition P0_post (Lc : layout) (Ac : astate) (mem : word -> option byte) : config -> Prop :=
fun c' => exists Lm Am regs2 mem2 mdm (r : Z),
c' = mkCfg (@mkst fx regs2 (Z_to_bv 64 NT_RET0) mem2 rom) mdm /\
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lm Am mem2 mdm /\ st_init_done Am = true /\
getr regs2 2 = Z_to_bv 64 spc /\ getr regs2 8 = Z_to_bv 64 nln /\ getr regs2 9 = Z_to_bv 64 cidx /\
getr regs2 18 = Z_to_bv 64 imax /\ getr regs2 19 = Z_to_bv 64 imin /\ getr regs2 20 = Z_to_bv 64 frp /\ getr regs2 21 = Z_to_bv 64 palp /\
getr regs2 4 = Z_to_bv 64 tp /\ getr regs2 10 = Z_to_bv 64 r /\
(forall rr : reg, In rr NT_KEEP -> getr regs2 rr = getr regs0 rr) /\
saved_ok mem2 /\
((r = 0 /\ blocks Lm Am = blocks Lc Ac)
\/ (r <> 0 /\ r mod 16 = 0 /\
(exists b1 b2, blocks Lm Am = b1 ++ (r, NODE_SIZE) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (r, NODE_SIZE) blc -> 0 <= i < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) blc (r + i)))) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte segs mem2 (b + i) = mbyte segs mem (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spZ regs0) -> mbyte segs mem2 x = mbyte segs mem x).
Lemma ntn_p0 : forall Lc Ac mem mdc,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem mdc -> st_init_done Ac = true ->
getr regs0 4 = Z_to_bv 64 tp ->
getr regs0 10 = Z_to_bv 64 palp -> getr regs0 11 = Z_to_bv 64 frp -> getr regs0 12 = Z_to_bv 64 nln ->
getr regs0 13 = Z_to_bv 64 imin -> getr regs0 14 = Z_to_bv 64 imax -> getr regs0 15 = Z_to_bv 64 cidx ->
SR segs (mkCfg (@mkst fx regs0 (Z_to_bv 64 ubs2_A_new_tree_node) mem rom) mdc) (P0_post Lc Ac mem).
Proof.
intros Lc Ac mem mdc HJ Hid Htp Ha0 Ha1 Ha2 Ha3 Ha4 Ha5.
clear Hii Himax Hlenp Hlenf Hpalv Hfrv Hfr1 Hsum Hpalp Hpalhi Hfrp Hfrhi Hfr4 Hpfd Hres0 Hres1 Hres16 Hnp Hnf Hcidx Hnln0 Hnln1 Hnln2 Hra.
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _).
set (E := Ereg regs0 ([] : list word)).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs0 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = spZ regs0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : @st_ok segs fx E ss_P0 (@mkst fx regs0 (Z_to_bv 64 ubs2_A_new_tree_node) mem rom)).
{ unfold ss_P0. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
apply (region_ok_stack segs _ mem 2 (spZ regs0)); [exact HU2 | lia | lia | intros a Ha; apply Hstw; lia].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16. repeat split; lia. }
change mem with (ms_mem (@mkst fx regs0 (Z_to_bv 64 ubs2_A_new_tree_node) mem rom)) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc.
{ wr_ok_eval. eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
jreg HS (10%bv:reg) as M10. jreg HS (2%bv:reg) as M2. jreg HS (4%bv:reg) as M4. jreg HS (1%bv:reg) as M1.
jreg HS (8%bv:reg) as M8. jreg HS (9%bv:reg) as M9. jreg HS (18%bv:reg) as M18. jreg HS (19%bv:reg) as M19. jreg HS (20%bv:reg) as M20. jreg HS (21%bv:reg) as M21.
rewrite HU2 in M2. rewrite (HE 4%nat 4%bv eq_refl), Htp in M4.
rewrite (HE 12%nat 12%bv eq_refl), Ha2 in M8. rewrite (HE 15%nat 15%bv eq_refl), Ha5 in M9. rewrite (HE 14%nat 14%bv eq_refl), Ha4 in M18.
rewrite (HE 13%nat 13%bv eq_refl), Ha3 in M19. rewrite (HE 11%nat 11%bv eq_refl), Ha1 in M20. rewrite (HE 10%nat 10%bv eq_refl), Ha0 in M21.
pose proof (regs_kept_of_st_ok _ _ _ _ regs0 _ NT_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as Mk.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => set (msP := msx) in * end.
assert (SV : saved_ok (ms_mem msP)).
{ pose proof (fun off e v Hin He Hv => st_chunk_val segs E _ msP 0%nat _ 2%nat off 8%N e (spZ regs0) v HS eq_refl eq_refl Hin HU2 He Hv ltac:(cbn; lia)) as CV.
unfold saved_ok.
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- val_mem _ _ (spZ regs0 - 160 + ?o) 8 (bv_unsigned (getr regs0 ?rr)) =>
replace (spZ regs0 - 160 + o) with (spZ regs0 + (o - 160)) by lia;
let n := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in
apply (CV (o - 160) (SOff n 0)); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, (HE n rr eq_refl), Z_to_bv_bv_unsigned; reflexivity
| change (8 * Z.of_N 8) with 64; apply u64_rangeN ]
end. }
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spc <= a < spZ regs0) -> mbyte segs (ms_mem msP) a = mbyte segs mem a).
{ intros a Ha Hna. mb_frame_g HF ltac:(exact Ha) ltac:(rewrite ?HU2; lia). reflexivity. }
eapply SR_mono.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := NODE_SIZE) (spc := spZ regs0 - 160);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | rewrite HNS; exact M10 | lia
| rewrite M2; f_equal; lia | lia
| replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16
| lia | lia | exact M4 | exact M1 | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (Lm & Am & regs2 & mem2 & mdm & r & -> & HJ2 & Hid2 & HP2 & Hr10 & Hres & Hkeep & Hhi).
cbn [ms_regs ms_mem mkst] in HP2, Hkeep, Hhi, HJ2. change (ms_segs ubs2_msyms) with segs in Hkeep, Hhi.
exists Lm, Am, regs2, mem2, mdm, r.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|].
pose proof (fun (rr : reg) (Hc : In rr CALLEE_SAVED) => regs_preserved_in _ _ rr HP2 Hc) as HPk. cbn [ms_regs mkst] in HPk.
split; [rewrite (HPk 2%bv ltac:(cbv; tauto)), M2; f_equal; lia|].
split; [rewrite (HPk 8%bv ltac:(cbv; tauto)); exact M8|]. split; [rewrite (HPk 9%bv ltac:(cbv; tauto)); exact M9|].
split; [rewrite (HPk 18%bv ltac:(cbv; tauto)); exact M18|]. split; [rewrite (HPk 19%bv ltac:(cbv; tauto)); exact M19|].
split; [rewrite (HPk 20%bv ltac:(cbv; tauto)); exact M20|]. split; [rewrite (HPk 21%bv ltac:(cbv; tauto)); exact M21|].
split; [rewrite (HPk 4%bv ltac:(cbv; tauto)); exact M4|]. split; [exact Hr10|].
split; [intros rr Hrr; rewrite (HPk rr ltac:(cbv [NT_KEEP In] in Hrr; cbv [CALLEE_SAVED In]; tauto)); apply Mk; exact Hrr|].
split.
{ eapply saved_ok_frame; [exact SV|]. intros a Ha. apply (proj1 (Hhi a ltac:(lia) ltac:(lia))). }
split; [exact Hres|].
split.
{ intros b m i Hb Hi. rewrite (Hkeep b m i Hb Hi). apply K0; [|].
- pose proof (heap_blocks_range _ _ LAWS _ _ _ _ b m (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hb ltac:(lia)). lia.
- pose proof (heap_blocks_range _ _ LAWS _ _ _ _ b m (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hb ltac:(lia)). lia. }
intros x Hx Hnx. rewrite (proj1 (Hhi x Hx ltac:(lia))). apply K0; lia.
Qed.
Definition saved_chunks : list YQ0b.chunk :=
[mkChunk 104 (CVal 8 (SOff 32 0)); mkChunk 112 (CVal 8 (SOff 33 0)); mkChunk 120 (CVal 8 (SOff 34 0));
mkChunk 128 (CVal 8 (SOff 35 0)); mkChunk 136 (CVal 8 (SOff 36 0)); mkChunk 144 (CVal 8 (SOff 37 0)); mkChunk 152 (CVal 8 (SOff 38 0))].
Definition ss_PF : sstate :=
mkSS NT_RET0 (sr_set sr_atoms 10%bv (SLit 0)) [ YQ0b.mkRegion (Some 2%nat) 0 160 0 0 saved_chunks ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Definition PF_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : config -> Prop :=
fun c' => exists regs',
c' = mkCfg (@mkst fy regs' (getr regs0 1) mem rom) md2 /\
getr regs' 2 = getr regs0 2 /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\
getr regs' 18 = getr regs0 18 /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21 /\
getr regs' 10 = Z_to_bv 64 0 /\
(forall r : reg, In r NT_KEEP -> getr regs' r = getr regs r).
Definition savedE (regs : bvmap 5 word) (n0 : Z) : env :=
Ereg regs (map (Z_to_bv 64) [bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 18);
bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 1); n0] ++ []).
Lemma savedE_facts : forall regs n0, let E := savedE regs n0 in
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
ew E 32 = getr regs0 21 /\ ew E 33 = getr regs0 20 /\ ew E 34 = getr regs0 19 /\ ew E 35 = getr regs0 18 /\
ew E 36 = getr regs0 9 /\ ew E 37 = getr regs0 8 /\ ew E 38 = getr regs0 1 /\ ew E 39 = Z_to_bv 64 n0.
Proof.
intros regs n0 E.
assert (HV : forall j v, nth_error [bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 18);
bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 1); n0] j = Some v -> ew E (32 + j) = Z_to_bv 64 v)
by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
split; [intros; subst E; apply ew_Ereg_nat; assumption|].
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- ew E ?k = _ =>
let j := eval vm_compute in (k - 32)%nat in change k with (32 + j)%nat; rewrite (HV j _ eq_refl); rewrite ?Z_to_bv_bv_unsigned; reflexivity end.
Qed.
Lemma saved_region_ok : forall regs n0 mem, saved_ok mem -> bv_unsigned (ew (savedE regs n0) 2) = spc ->
@region_ok segs (savedE regs n0) mem (YQ0b.mkRegion (Some 2%nat) 0 160 0 0 saved_chunks).
Proof.
intros regs n0 mem (S1 & S2 & S3 & S4 & S5 & S6 & S7) HU2.
clear Hii Himax Hlenp Hlenf Hpalv Hfrv Hfr1 Hsum Hpalp Hpalhi Hfrp Hfrhi Hfr4 Hpfd Hres0 Hres1 Hres16 Hnp Hnf Hcidx Hnln0 Hnln1 Hnln2 Hra.
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
destruct (savedE_facts regs n0) as (HE & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39).
pose proof (u64_rangeN (getr regs0 21)) as R21. pose proof (u64_rangeN (getr regs0 20)) as R20. pose proof (u64_rangeN (getr regs0 19)) as R19.
pose proof (u64_rangeN (getr regs0 18)) as R18. pose proof (u64_rangeN (getr regs0 9)) as R9. pose proof (u64_rangeN (getr regs0 8)) as R8.
pose proof (u64_rangeN (getr regs0 1)) as R1.
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. unfold saved_chunks.
repeat apply Forall_cons; [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?A32, ?A33, ?A34, ?A35, ?A36, ?A37, ?A38; reflexivity
| cbn; lia | cbn; lia | assumption]).
Qed.
Lemma ntn_pfail : forall (fy : FPState) (regs : bvmap 5 word) mem,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 L2 A2 mem md2 ->
getr regs 2 = Z_to_bv 64 spc -> getr regs 10 = Z_to_bv 64 0 -> saved_ok mem ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 NT_RET0) mem rom) md2) (PF_post fy regs mem).
Proof.
intros fy regs mem HJ Hr2 Hr10 HSV.
clear Hii Himax Hlenp Hlenf Hpalv Hfrv Hfr1 Hsum Hpalp Hpalhi Hfrp Hfrhi Hfr4 Hpfd Hres0 Hres1 Hres16 Hnp Hnf Hcidx Hnln0 Hnln1 Hnln2.
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
destruct (savedE_facts regs 0) as (HE & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39).
set (E := savedE regs 0) in *.
assert (HU2 : bv_unsigned (ew E 2) = spc) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HS : @st_ok segs fy E ss_PF (@mkst fy regs (Z_to_bv 64 NT_RET0) mem rom)).
{ unfold ss_PF. apply entry_st_ok_env.
- apply regs_ok_pin; [subst E; unfold savedE; apply regs_ok_Ereg | intros HH0; discriminate HH0 | cbn [sv_denot]; exact Hr10].
- vm_compute. reflexivity.
- constructor; [apply saved_region_ok; [exact HSV | exact HU2] | constructor].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16.
assert (spc mod 16 = 0) by (replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
repeat split; lia. }
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
pure_to ubs2tbl_ok HS NT_RET.
eapply (SR_msteps segs _ _ md2 _ Hh Hlz Hms).
eapply (SR_ret_at (fx:=fy) segs ubs2tbl E _ _ _ _ ubs2tbl_ok Hh Hlz HS eq_refl ltac:(vm_compute; reflexivity)).
cbn [ms_regs ms_mem mkst].
jreg HS (1%bv:reg) as Q1. jreg HS (2%bv:reg) as Q2. jreg HS (8%bv:reg) as Q8. jreg HS (9%bv:reg) as Q9. jreg HS (10%bv:reg) as Q10.
jreg HS (18%bv:reg) as Q18. jreg HS (19%bv:reg) as Q19. jreg HS (20%bv:reg) as Q20. jreg HS (21%bv:reg) as Q21.
cbn [ms_regs mkst] in Q1, Q2, Q8, Q9, Q10, Q18, Q19, Q20, Q21.
exists regs1.
split; [rewrite Q1, A38, Hra; reflexivity|].
split; [rewrite Q2, HU2; unfold spZ; rewrite Z.sub_add; apply Z_to_bv_bv_unsigned|].
split; [rewrite Q8, A37; reflexivity|]. split; [rewrite Q9, A36; reflexivity|].
split; [rewrite Q18, A35; reflexivity|]. split; [rewrite Q19, A34; reflexivity|].
split; [rewrite Q20, A33; reflexivity|]. split; [rewrite Q21, A32; reflexivity|].
split; [exact Q10|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ NT_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_P1 : sstate :=
mkSS NT_RET0 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 160 8 104 [];
YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 40 48 [] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4);
(19%nat, mkAF 0 (2^30) 0); (18%nat, mkAF 0 (2^30) 0); (21%nat, mkAF 4096 CEIL_MAX 0) ] [] []).
Definition P1_KEEP : list reg := [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition P1_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : config -> Prop :=
fun c' => exists regs' mem',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 NT_L1) mem' rom) md2 /\
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 L2 A2 mem' md2 /\
getr regs' 11 = Z_to_bv 64 (2 ^ 64 - 1 - frp) /\ getr regs' 12 = Z_to_bv 64 (3 * imin) /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 imin /\
(forall r : reg, In r P1_KEEP -> getr regs' r = getr regs r) /\
(forall o, In o [8; 16; 24; 32; 40; 48; 56; 64; 72; 80; 88; 96] -> val_mem segs mem' (spc + o) 8 0) /\
val_mem segs mem' (res + 40) 4 imin /\ val_mem segs mem' (res + 44) 4 imax /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 8 <= a < spc + 104) -> ~ (res + 40 <= a < res + 48) -> mbyte segs mem' a = mbyte segs mem a).
Lemma ntn_p1 : forall (fy : FPState) (regs : bvmap 5 word) mem,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 L2 A2 mem md2 ->
getr regs 2 = Z_to_bv 64 spc -> getr regs 10 = Z_to_bv 64 res -> getr regs 18 = Z_to_bv 64 imax -> getr regs 19 = Z_to_bv 64 imin ->
getr regs 20 = Z_to_bv 64 frp -> getr regs 21 = Z_to_bv 64 palp ->
(forall i, 0 <= i < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) (blocks L2 A2) (res + i)) ->
(forall a, res + 40 <= a < res + 48 -> writable_at segs mem a) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 NT_RET0) mem rom) md2) (P1_post fy regs mem).
Proof.
intros fy regs mem HJ Hr2 Hr10 Hr18 Hr19 Hr20 Hr21 Hwb Hw.
clear Hpalv Hfrv Hfr1 Hsum Hfr4 Hpfd Hnp Hnf Hcidx Hnln0 Hnln1 Hnln2 Hra.
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _).
set (E := Ereg regs ([] : list word)).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = spc) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = res) by (rewrite (HE 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 18) = imax) by (rewrite (HE 18%nat 18%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU19 : bv_unsigned (ew E 19) = imin) by (rewrite (HE 19%nat 19%bv eq_refl), Hr19; apply unsigned_lit_small; lia).
assert (HU21 : bv_unsigned (ew E 21) = palp) by (rewrite (HE 21%nat 21%bv eq_refl), Hr21; apply unsigned_lit_small; lia).
assert (HS : @st_ok segs fy E ss_P1 (@mkst fy regs (Z_to_bv 64 NT_RET0) mem rom)).
{ unfold ss_P1. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia | constructor].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia | constructor].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU10. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU10, HU18, HU19, HU21. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert (spc mod 16 = 0) by (replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
repeat split; lia. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 NT_RET0) mem rom)) in HJ.
assert (Hwr : forall cs1 cs2, wr_ok E [YQ0b.mkRegion (Some 2%nat) 0 160 8 104 cs1; YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 40 48 cs2] STK sp0 FP (blocks L A) (blocks L2 A2)).
{ intros cs1 cs2. eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia |].
eapply wr_ok_cons_gen; [reflexivity | exact HU10 | cbn [r_wlo r_whi]; intros a Ha; replace a with (res + (a - res)) by lia; apply Hwb; lia | apply wr_ok_nil]. }
jrun_to LAWS ubs2tbl_ok HS HJ NT_L1. { wr_ok_eval. apply Hwr. }
cbn [ms_mem mkst] in HF, HJ.
jbranch ubs2tbl HS.
{ exfalso. rewrite branch_ltu_U, !U_SOff, HU18, HU19, !zcanon_id in Hc by (unfold M64; lia). rewrite !Z.add_0_r in Hc.
destruct (Z.ltb_spec imax imin); [lia | discriminate Hc]. }
clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ NT_L1. { wr_ok_eval. apply Hwr. }
cbn [ms_mem mkst] in HF0, HJ.
rewrite (st_ok_mkst segs E _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch goal with |- P1_post _ _ _ (mkCfg (mkst (ms_regs ?m) _ (ms_mem _) _) _) => exists (ms_regs m), (ms_mem m) end.
split; [reflexivity|]. split; [exact HJ|].
split.
{ pose proof (st_ok_reg segs E _ _ 11%bv HS) as Q11. eval_sr_get_in Q11. cbn [ms_regs mkst] in Q11. rewrite Q11.
rewrite denot_lit_U. f_equal. apply (U_not E 20 frp); [rewrite (HE 20%nat 20%bv eq_refl); exact Hr20 | lia]. }
split.
{ pose proof (st_ok_reg segs E _ _ 12%bv HS) as Q12. eval_sr_get_in Q12. cbn [ms_regs mkst] in Q12. rewrite Q12.
rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SOff. rewrite U_SLit, HU19, Z.add_0_r.
rewrite (zcanon_id imin), (zcanon_id 3) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
split.
{ jreg HS (13%bv:reg) as Q13. cbn [ms_regs mkst] in Q13. rewrite Q13. reflexivity. }
jreg HS (14%bv:reg) as Q14. cbn [ms_regs mkst] in Q14. split; [rewrite Q14, (HE 19%nat 19%bv eq_refl); exact Hr19|].
split; [exact (regs_kept_of_st_ok _ _ _ _ regs _ P1_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity))|].
split.
{ intros o Ho. replace (spZ regs0 - 160 + o) with (spc + o) by lia.
eapply (st_chunk_val segs E _ _ 0%nat _ 2%nat o 8%N (SLit 0) spc 0 HS); [reflexivity | reflexivity | | exact HU2 | reflexivity | cbn; lia | cbn; lia].
cbv [In] in Ho. cbn [ss_mem nth_error r_chunks].
repeat (destruct Ho as [<-|Ho]; [cbv; tauto|]). destruct Ho. }
split; [eapply (st_chunk_val segs E _ _ 1%nat _ 10%nat 40 4%N (SOff 19 0) res imin HS); [reflexivity | reflexivity | cbv; tauto | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, (HE 19%nat 19%bv eq_refl), Z_to_bv_bv_unsigned; exact Hr19 | cbn; lia | cbn; lia]|].
split; [eapply (st_chunk_val segs E _ _ 1%nat _ 10%nat 44 4%N (SOff 18 0) res imax HS); [reflexivity | reflexivity | cbv; tauto | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, (HE 18%nat 18%bv eq_refl), Z_to_bv_bv_unsigned; exact Hr18 | cbn; lia | cbn; lia]|].
intros a Ha Hn1 Hn2. mb_frames ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU10; lia). reflexivity.
Qed.
End d.
End c.
