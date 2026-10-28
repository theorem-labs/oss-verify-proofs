(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI07
UI1e UI1i YI0x UI56 UI1h YP14 YP16 YI08 YI0c YI0f YI09 UI3q.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition PC_PR : Z := 0x141c4.
Definition PC_SPLIT : Z := 0x1436c.
Definition PC_PRL : Z := 0x141e8.
Definition PART_KEEP : list reg := [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 27; 29; 30; 31]%bv.
Definition PR_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition PR1_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 14; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition PR2_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition ALL_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition SW_KEEP : list reg := [1; 2; 3; 4; 7; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition SW_KEEP0 : list reg := [1; 2; 3; 4; 7; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Ltac wr_ok_eval :=
lazymatch goal with |- wr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc =>
let rs' := eval vm_compute in rs in change (wr_ok E rs' stk sp0 fp b0 bc) end.
Definition disj_blocks (p n q m : Z) : Prop := p + n <= q \/ q + m <= p.
Lemma in_bv5 : forall (r : reg) (L : list reg), existsb (bv_eqb r) L = true -> In r L.
Proof. intros r L H. apply existsb_exists in H as (r' & Hin & Heq). apply bv_eqb_eq in Heq. subst. exact Hin. Qed.
Ltac inl := apply in_bv5; vm_compute; reflexivity.
Lemma keep_sub : forall (l L : list reg) (f g : reg -> word),
forallb (fun r => existsb (bv_eqb r) L) l = true ->
(forall r, In r L -> f r = g r) -> forall r, In r l -> f r = g r.
Proof.
intros l L f g Hs H r Hr. apply H. pose proof (proj1 (forallb_forall _ _) Hs r Hr) as Hx. cbn beta in Hx.
apply existsb_exists in Hx as (r' & Hin & Heq). apply bv_eqb_eq in Heq. subst r'. exact Hin.
Qed.
Lemma keep_pin : forall (L : list reg) (f g : reg -> word) (r0 : reg),
(forall r, In r L -> f r = g r) -> f r0 = g r0 -> forall r, In r (r0 :: L) -> f r = g r.
Proof. intros L f g r0 H H0 r [<- | Hr]; [exact H0 | exact (H r Hr)]. Qed.
Lemma val_mem_frame : forall (m m' : word -> option byte) a n v,
val_mem ubs2segs m a n v -> (forall i, 0 <= i < Z.of_nat n -> mbyte ubs2segs m' (a + i) = mbyte ubs2segs m (a + i)) -> val_mem ubs2segs m' a n v.
Proof. intros m m' a n v H Hf k Hk. rewrite Hf by lia. apply H. exact Hk. Qed.
Lemma U_lin : forall E v X,
match lin_nf v with Some (l, c) => lin_denot E l + c = X | None => False end -> 0 <= X < 2 ^ 64 -> U E v = X.
Proof.
intros E v X H HX. destruct (lin_nf v) as [[l c]|] eqn:Hn; [|destruct H].
rewrite (lin_nf_sound E v l c Hn), H. apply Z.mod_small. unfold M64. lia.
Qed.
Lemma denot_U : forall E v X, U E v = X -> sv_denot E v = Z_to_bv 64 X.
Proof. intros E v X H. rewrite denot_lit_U, H. reflexivity. Qed.
Ltac p3_lin :=
apply U_lin;
[ lazymatch goal with |- context [lin_nf ?v] => let r := eval vm_compute in (lin_nf v) in change (lin_nf v) with r end;
cbv beta iota; cbn [lin_denot] | ].
Ltac p3_reg HS r Hr :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss ?ms => pose proof (st_ok_reg sg E ss ms r HS) as Hr; eval_sr_get_in Hr; cbn [ms_regs mkst] in Hr
end.
Definition pack2 (n1 n0 : nat) : sv := SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SOff n0 0).
Lemma U_pack2 : forall E n1 n0 b1 b0, ew E n1 = Z_to_bv 64 b1 -> ew E n0 = Z_to_bv 64 b0 -> 0 <= b1 < 256 -> 0 <= b0 < 256 ->
U E (pack2 n1 n0) = b0 + 256 * b1.
Proof.
intros E n1 n0 b1 b0 H1 H0 R1 R0. unfold pack2. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
change (Z.land (zcanon 8) 63) with 8. rewrite (U_atom E n1 b1 H1), (U_atom E n0 b0 H0) by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (b1 * 256)) by (unfold M64; lia). rewrite lor_shl8 by lia. apply zcanon_id. unfold M64; lia.
Qed.
Lemma denot_pack2_hi : forall E n1 n0 b1 b0, ew E n1 = Z_to_bv 64 b1 -> ew E n0 = Z_to_bv 64 b0 -> 0 <= b1 < 256 -> 0 <= b0 < 256 ->
sv_denot E (SAlu ALU_SRL (pack2 n1 n0) (SLit 8)) = Z_to_bv 64 b1.
Proof.
intros E n1 n0 b1 b0 H1 H0 R1 R0. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_pack2 E n1 n0 b1 b0 H1 H0 R1 R0), U_SLit.
change (Z.land (zcanon 8) 63) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite div_256 by lia.
apply zcanon_id. unfold M64; lia.
Qed.
Lemma denot_pack2_lo : forall E n1 n0 b1 b0, ew E n1 = Z_to_bv 64 b1 -> ew E n0 = Z_to_bv 64 b0 -> 0 <= b1 < 256 -> 0 <= b0 < 256 ->
sv_denot E (SExt false 8 (pack2 n1 n0)) = Z_to_bv 64 b0.
Proof.
intros E n1 n0 b1 b0 H1 H0 R1 R0. rewrite denot_lit_U. f_equal. rewrite U_SExt. rewrite (U_pack2 E n1 n0 b1 b0 H1 H0 R1 R0).
change (2 ^ Z.of_N 8) with 256. rewrite mod_256 by lia. apply zcanon_id. unfold M64; lia.
Qed.
Lemma denot_sext32_small : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv. rewrite denot_lit_U. f_equal. rewrite U_SExt. rewrite (U_atom E n v Hn) by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite Z.mod_small by lia. rewrite swrap32_id by lia. apply zcanon_id. unfold M64; lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Notation segs := ubs2segs (only parsing).
Local Notation rom := (seg_rom ubs2segs) (only parsing).
Definition pr_alias : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 25 0) (SMd M_MUL (SOff 26 0) (SLit 3))) (SOff 32 0).
Definition ss_PR1 : sstate :=
mkSS PC_PR sr_atoms
[ YQ0b.mkRegion (Some 27%nat) 48 49 0 0 [mkChunk 48 (CVal 1 (SOff 32 0))] ] None
(mkFacts [ (25%nat, mkAF 4096 (2^48) 0); (26%nat, mkAF 0 (2^29) 0); (27%nat, mkAF 4096 (2^48) 3);
(32%nat, mkAF 0 2 0); (33%nat, mkAF 4096 (2^49) 0) ]
[mkAC BC_GEU (SOff 33 0) (SOff 25 0)] [(pr_alias, SOff 33%nat 0)]).
Definition ss_PR2 : sstate :=
mkSS PC_PRL (sr_set sr_atoms 13%bv (SLit 0))
[ YQ0b.mkRegion (Some 2%nat) 56 64 0 0 [mkChunk 56 (CVal 8 (SLit 1))] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (25%nat, mkAF 4096 (2^48) 0); (27%nat, mkAF 4096 (2^48) 3) ] [] []).
Lemma PR_to_RH : forall (fy : FPState) (regs : bvmap 5 word) mem (a i cut p sp : Z),
getr regs 27 = Z_to_bv 64 a -> getr regs 26 = Z_to_bv 64 i -> getr regs 25 = Z_to_bv 64 p -> getr regs 2 = Z_to_bv 64 sp ->
0 <= i < 2 ^ 29 -> 4096 <= a -> a + 56 < 2 ^ 48 -> a mod 8 = 0 -> 0 <= cut <= 2 -> 4096 <= p < 2 ^ 48 ->
0 <= sp < 2 ^ 63 -> sp mod 16 = 0 ->
val_mem segs mem (a + 48) 1 cut -> word_mem segs mem (sp + 56) 1 ->
exists regs', msteps segs (@mkst fy regs (Z_to_bv 64 PC_PR) mem rom) (@mkst fy regs' (Z_to_bv 64 PC_RH) mem rom) /\
getr regs' 15 = Z_to_bv 64 cut /\ getr regs' 13 = Z_to_bv 64 (a + 16) /\ getr regs' 14 = Z_to_bv 64 (2 ^ 64 - 1 - (a + 16)) /\
getr regs' 12 = Z_to_bv 64 (3 * i) /\ getr regs' 17 = Z_to_bv 64 (3 * i + cut) /\
(forall r : reg, In r PR_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem a i cut p sp G27 G26 G25 G2 Hi Ha0 Ha1 Ha8 Hcut Hp Hsp Hsp16 Vcut Vslot.
set (E1 := Ereg regs (map (Z_to_bv 64) [cut; p + 3 * i + cut] ++ [])).
assert (HE1 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E1 k = getr regs rr) by (intros; subst E1; apply ew_Ereg_nat; assumption).
assert (HV1 : forall j v, nth_error [cut; p + 3 * i + cut] j = Some v -> ew E1 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E1; apply Ereg_vals; exact Hj).
assert (U25 : bv_unsigned (ew E1 25) = p) by (rewrite (HE1 25%nat 25%bv eq_refl), G25; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E1 26) = i) by (rewrite (HE1 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E1 27) = a) by (rewrite (HE1 27%nat 27%bv eq_refl), G27; apply unsigned_lit_small; lia).
assert (A32 : ew E1 32 = Z_to_bv 64 cut) by (apply (HV1 0%nat); reflexivity).
assert (A33 : ew E1 33 = Z_to_bv 64 (p + 3 * i + cut)) by (apply (HV1 1%nat); reflexivity).
assert (U32 : bv_unsigned (ew E1 32) = cut) by (rewrite A32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E1 33) = p + 3 * i + cut) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HS1 : @st_ok segs fy E1 ss_PR1 (@mkst fy regs (Z_to_bv 64 PC_PR) mem rom)).
{ unfold ss_PR1. subst E1. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U27.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, U32; reflexivity | cbn; lia | cbn; lia | exact Vcut].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite U25, U26, U27, U32, U33. change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, !U_SOff, U33, U25, !Z.add_0_r, !zcanon_id by (unfold M64; lia).
apply Bool.negb_true_iff. apply Z.ltb_ge. lia.
+ cbn [f_alias alias_ok]. split; [|exact I]. apply U_inj.
rewrite (U_atom _ 33 _ A33) by lia. unfold pr_alias. p3_lin; [rewrite ?U25, ?U26, ?U32; lia | lia]. }
pure_to ubs2tbl_ok HS1 PC_PRL.
p3_reg HS1 (12%bv:reg) Q12. p3_reg HS1 (13%bv:reg) Q13. p3_reg HS1 (15%bv:reg) Q15. p3_reg HS1 (17%bv:reg) Q17.
assert (K1 : forall r : reg, In r PR1_KEEP -> getr regs0 r = getr regs r)
by exact (regs_kept_of_st_ok _ _ _ _ regs _ PR1_KEEP HS1 (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
set (E2 := Ereg regs0 []).
assert (HE2 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E2 k = getr regs0 rr) by (intros; subst E2; apply ew_Ereg_nat; assumption).
assert (V2 : bv_unsigned (ew E2 2) = sp) by (rewrite (HE2 2%nat 2%bv eq_refl), (K1 2%bv ltac:(inl)), G2; apply unsigned_lit_small; lia).
assert (V25 : bv_unsigned (ew E2 25) = p) by (rewrite (HE2 25%nat 25%bv eq_refl), (K1 25%bv ltac:(inl)), G25; apply unsigned_lit_small; lia).
assert (B27 : ew E2 27 = Z_to_bv 64 a) by (rewrite (HE2 27%nat 27%bv eq_refl), (K1 27%bv ltac:(inl)); exact G27).
assert (V27 : bv_unsigned (ew E2 27) = a) by (rewrite B27; apply unsigned_lit_small; lia).
assert (HS2 : @st_ok segs fy E2 ss_PR2 (@mkst fy regs0 (Z_to_bv 64 PC_PRL) mem rom)).
{ unfold ss_PR2. subst E2. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |]. rewrite Q13. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite V2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Vslot].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite V2, V25, V27. change (2 ^ 0) with 1. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.mod_1_r. repeat split; lia. }
pure_to ubs2tbl_ok HS2 PC_RH.
p3_reg HS2 (13%bv:reg) R13. p3_reg HS2 (14%bv:reg) R14.
assert (K2 : forall r : reg, In r PR2_KEEP -> getr regs1 r = getr regs0 r)
by exact (regs_kept_of_st_ok _ _ _ _ regs0 _ PR2_KEEP HS2 (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
exists regs1. split; [eapply msteps_trans; [exact Hms | exact Hms0]|].
split; [rewrite (K2 15%bv ltac:(inl)), Q15; apply denot_U; apply (U_atom _ 32 cut A32); lia|].
split; [rewrite R13; apply denot_U; apply (U_atom_off _ 27 a 16 B27); lia|].
split; [rewrite R14; apply denot_U; apply (U_not_off _ 27 a 16 B27); lia|].
split; [rewrite (K2 12%bv ltac:(inl)), Q12; apply denot_U; p3_lin; [rewrite ?U26; lia | lia]|].
split; [rewrite (K2 17%bv ltac:(inl)), Q17; apply denot_U; p3_lin; [rewrite ?U26, ?U32; lia | lia]|].
intros r Hr. rewrite (keep_sub PR_KEEP PR2_KEEP _ _ ltac:(vm_compute; reflexivity) K2 r Hr).
apply (keep_sub PR_KEEP PR1_KEEP _ _ ltac:(vm_compute; reflexivity) K1 r Hr).
Qed.
Definition ss_BGD : sstate :=
mkSS PC_BG sr_atoms [] None
(mkFacts [ (26%nat, mkAF 0 (2^29) 0); (11%nat, mkAF 0 (2^29) 0) ]
[mkAC BC_GEU (SOff 26%nat 0) (SOff 11%nat 0)] []).
Lemma BG_done : forall (fy : FPState) (regs : bvmap 5 word) mem (i1 k1 : Z),
getr regs 26 = Z_to_bv 64 i1 -> getr regs 11 = Z_to_bv 64 k1 -> 0 <= k1 <= i1 -> i1 < 2 ^ 29 ->
exists regs', msteps segs (@mkst fy regs (Z_to_bv 64 PC_BG) mem rom) (@mkst fy regs' (Z_to_bv 64 PC_SPLIT) mem rom) /\
(forall r : reg, In r ALL_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem i1 k1 G26 G11 Hki Hi1.
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U26 : bv_unsigned (ew E 26) = i1) by (rewrite (HE 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = k1) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : @st_ok segs fy E ss_BGD (@mkst fy regs (Z_to_bv 64 PC_BG) mem rom)).
{ unfold ss_BGD. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [|split; [|exact I]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite U26, U11. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, !U_SOff, U26, U11, !Z.add_0_r, !zcanon_id by (unfold M64; lia).
apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
pure_to ubs2tbl_ok HS PC_SPLIT.
exists regs0. split; [exact Hms|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ ALL_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition sw_aliases : list (sv * sv) :=
[(SAlu ALU_ADD (SOff 25 0) (SOff 16 0), SOff 40%nat 0);
(SAlu ALU_ADD (SOff 25 0) (SOff 17 0), SOff 41%nat 0);
(SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLL (SOff 26 0) (SLit 2)), SOff 42%nat 0);
(SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLL (SOff 11 0) (SLit 2)), SOff 43%nat 0)].
Definition ss_SW : sstate :=
mkSS PC_BG (sr_set sr_atoms 22%bv (SOff 2%nat 5038))
[ YQ0b.mkRegion (Some 40%nat) 0 3 0 3 [mkChunk 0 (CVal 1 (SOff 44 0)); mkChunk 1 (CVal 1 (SOff 45 0)); mkChunk 2 (CVal 1 (SOff 46 0))];
YQ0b.mkRegion (Some 41%nat) 0 3 0 3 [mkChunk 0 (CVal 1 (SOff 47 0)); mkChunk 1 (CVal 1 (SOff 48 0)); mkChunk 2 (CVal 1 (SOff 49 0))];
YQ0b.mkRegion (Some 42%nat) 0 4 0 4 [mkChunk 0 (CVal 4 (SOff 50 0))];
YQ0b.mkRegion (Some 43%nat) 0 4 0 4 [mkChunk 0 (CVal 4 (SOff 51 0))];
YQ0b.mkRegion (Some 2%nat) 5036 5039 5036 5039 [];
YQ0b.mkRegion (Some 27%nat) 48 49 0 0 [mkChunk 48 (CVal 1 (SOff 32 0))] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (11%nat, mkAF 0 (2^29) 0); (12%nat, mkAF 0 (2^31) 0);
(16%nat, mkAF 0 (2^31) 0); (17%nat, mkAF 0 (2^31) 0);
(18%nat, mkAF (2^64 - 1 - 2^48) (2^64 - 1 - 4096) 0); (23%nat, mkAF (2^64 - 1 - 2^48) (2^64 - 1 - 4096) 0);
(24%nat, mkAF 4096 (2^48) 2); (25%nat, mkAF 4096 (2^48) 0); (26%nat, mkAF 0 (2^29) 0); (27%nat, mkAF 4096 (2^48) 3);
(32%nat, mkAF 0 2 0);
(40%nat, mkAF 4096 (2^49) 0); (41%nat, mkAF 4096 (2^49) 0); (42%nat, mkAF 4096 (2^49) 2); (43%nat, mkAF 4096 (2^49) 2);
(44%nat, mkAF 0 255 0); (45%nat, mkAF 0 255 0); (46%nat, mkAF 0 255 0);
(47%nat, mkAF 0 255 0); (48%nat, mkAF 0 255 0); (49%nat, mkAF 0 255 0);
(50%nat, mkAF 0 (2^31) 0); (51%nat, mkAF 0 (2^31) 0) ]
[mkAC BC_LTU (SOff 26%nat 0) (SOff 11%nat 0)] sw_aliases).
Definition ss_SW_out : sstate := Eval vm_compute in (fst (sym_run_toN segs ubs2tbl FUEL PC_RH ss_SW)).
Section J.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Lemma SW_stretch : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md
(E : list entry) (tail : list Z) (i1 k1 p fdp sp T a cut : Z) Q,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
In (p, 3 * T) (blocks Lc Ac) -> ~ In (p, 3 * T) (blocks L A) ->
In (fdp, 4 * elen E) (blocks Lc Ac) -> ~ In (fdp, 4 * elen E) (blocks L A) ->
disj_blocks p (3 * T) fdp (4 * elen E) ->
arr8 segs mem p (pal_bytes E ++ tail) -> 3 * elen E + zlen tail = 3 * T -> arr32 segs mem fdp (fr_vals E) ->
ent_ok E -> Forall (fun e => snd e < 2 ^ 31) E ->
0 <= i1 -> i1 < k1 -> k1 < elen E -> elen E < 2 ^ 29 ->
sp0 - STK <= sp + 5036 -> sp + 5168 <= sp0 -> sp mod 16 = 0 ->
4096 <= a -> a + 56 <= alloc_ceiling -> a mod 8 = 0 -> 0 <= cut <= 2 -> val_mem segs mem (a + 48) 1 cut ->
~ (p <= a + 48 < p + 3 * elen E) -> ~ (fdp <= a + 48 < fdp + 4 * elen E) -> ~ (sp + 5036 <= a + 48 < sp + 5039) ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 27 = Z_to_bv 64 a -> getr regs 26 = Z_to_bv 64 i1 -> getr regs 11 = Z_to_bv 64 k1 ->
getr regs 12 = Z_to_bv 64 (3 * i1) -> getr regs 16 = Z_to_bv 64 (3 * i1) -> getr regs 17 = Z_to_bv 64 (3 * k1) ->
getr regs 25 = Z_to_bv 64 p -> getr regs 24 = Z_to_bv 64 fdp ->
getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - p) -> getr regs 18 = Z_to_bv 64 (2 ^ 64 - 1 - fdp) -> getr regs 22 = Z_to_bv 64 (sp + 5038) ->
(forall regs' mem',
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
arr8 segs mem' p (pal_bytes (eswap dentry E i1 k1) ++ tail) -> arr32 segs mem' fdp (fr_vals (eswap dentry E i1 k1)) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (p <= x < p + 3 * elen E) -> ~ (fdp <= x < fdp + 4 * elen E) -> ~ (sp + 5036 <= x < sp + 5039) ->
mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 15 = Z_to_bv 64 cut -> getr regs' 17 = Z_to_bv 64 (3 * i1 + cut) ->
(forall r : reg, In r SW_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 PC_RH) mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_BG) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md E tail i1 k1 p fdp sp T a cut Q
HJ Hpin Hpn0 Hfin Hfn0 Hdisj Hpa Hlen Hfa HE Hf31 Hi0 Hik Hk1 Hcnt Hwlo Hwhi Hal16
Ha0 Ha1 Ha8 Hcut Vcut Hna Hnf Hnw
Hr2 Hr27 Hr26 Hr11 Hr12 Hr16 Hr17 Hr25 Hr24 Hr23 Hr18 Hr22 HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (Htl : 0 <= zlen tail) by (unfold zlen; lia).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac mem md p (3 * T) HH Hpin ltac:(lia)) as (Hp0 & Hp1 & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac mem md fdp (4 * elen E) HH Hfin ltac:(lia)) as (Hf0 & Hf1 & Hf16).
assert (F4 : fdp mod 4 = 0) by (pose proof (Z.div_mod fdp 16 ltac:(lia)) as Hdm; rewrite Hf16 in Hdm; rewrite Hdm; replace (16 * (fdp / 16) + 0) with ((4 * (fdp / 16)) * 4) by lia; apply Z.mod_mul; lia).
assert (M42 : (fdp + 4 * i1) mod 4 = 0) by (rewrite (Z.mul_comm 4 i1), Z.mod_add by lia; exact F4).
assert (M43 : (fdp + 4 * k1) mod 4 = 0) by (rewrite (Z.mul_comm 4 k1), Z.mod_add by lia; exact F4).
pose proof (pal_bytes_bytes E HE) as HB. pose proof (zlen_pal_bytes E) as HLp. pose proof (zlen_fr_vals E) as HLf.
assert (PB : forall x, 0 <= x < 3 * elen E -> mbyte segs mem (p + x) = Some (Z_to_bv 8 (getz (pal_bytes E) x)) /\ 0 <= getz (pal_bytes E) x < 256).
{ intros x Hx. destruct (arr8_getz segs mem p (pal_bytes E ++ tail) x Hpa ltac:(rewrite zlen_app_pal; lia)) as [H1 H2].
rewrite getz_app_l in H1, H2 by lia. auto. }
assert (FB : forall j, 0 <= j < elen E -> val_mem segs mem (fdp + 4 * j) 4 (getz (fr_vals E) j) /\ 0 <= getz (fr_vals E) j < 2 ^ 31).
{ intros j Hj. destruct (arr32_getz segs mem fdp (fr_vals E) j Hfa ltac:(lia)) as [H1 H2]. split; [exact H1|].
rewrite getz_fr_vals by lia. pose proof (proj1 (Forall_forall _ _) Hf31 _ (znth_In dentry E j Hj)) as X. cbn beta in X.
pose proof (proj2 (ent_ok_at E j HE Hj)). unfold efreq in *. lia. }
destruct (PB (3 * i1) ltac:(lia)) as [B0 R0]. destruct (PB (3 * i1 + 1) ltac:(lia)) as [B1 R1]. destruct (PB (3 * i1 + 2) ltac:(lia)) as [B2 R2].
destruct (PB (3 * k1) ltac:(lia)) as [C0 Q0]. destruct (PB (3 * k1 + 1) ltac:(lia)) as [C1 Q1]. destruct (PB (3 * k1 + 2) ltac:(lia)) as [C2 Q2].
destruct (FB i1 ltac:(lia)) as [Fi Ri]. destruct (FB k1 ltac:(lia)) as [Fk Rk].
set (vals := [cut; 0; 0; 0; 0; 0; 0; 0; p + 3 * i1; p + 3 * k1; fdp + 4 * i1; fdp + 4 * k1;
getz (pal_bytes E) (3 * i1); getz (pal_bytes E) (3 * i1 + 1); getz (pal_bytes E) (3 * i1 + 2);
getz (pal_bytes E) (3 * k1); getz (pal_bytes E) (3 * k1 + 1); getz (pal_bytes E) (3 * k1 + 2);
getz (fr_vals E) i1; getz (fr_vals E) k1]).
set (Ev := Ereg regs (map (Z_to_bv 64) vals ++ [])).
assert (HE' : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew Ev k = getr regs rr) by (intros; subst Ev; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew Ev (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst Ev; apply Ereg_vals; exact Hj).
assert (HA : forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew Ev (32 + j)) = v).
{ intros j v Hj Hv. rewrite (HV j v Hj). apply unsigned_lit_small. exact Hv. }
assert (HU2 : bv_unsigned (ew Ev 2) = sp) by (rewrite (HE' 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU27 : bv_unsigned (ew Ev 27) = a) by (rewrite (HE' 27%nat 27%bv eq_refl), Hr27; apply unsigned_lit_small; lia).
assert (HU26 : bv_unsigned (ew Ev 26) = i1) by (rewrite (HE' 26%nat 26%bv eq_refl), Hr26; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew Ev 11) = k1) by (rewrite (HE' 11%nat 11%bv eq_refl), Hr11; apply unsigned_lit_small; lia).
assert (HU12 : bv_unsigned (ew Ev 12) = 3 * i1) by (rewrite (HE' 12%nat 12%bv eq_refl), Hr12; apply unsigned_lit_small; lia).
assert (HU16 : bv_unsigned (ew Ev 16) = 3 * i1) by (rewrite (HE' 16%nat 16%bv eq_refl), Hr16; apply unsigned_lit_small; lia).
assert (HU17 : bv_unsigned (ew Ev 17) = 3 * k1) by (rewrite (HE' 17%nat 17%bv eq_refl), Hr17; apply unsigned_lit_small; lia).
assert (HU25 : bv_unsigned (ew Ev 25) = p) by (rewrite (HE' 25%nat 25%bv eq_refl), Hr25; apply unsigned_lit_small; lia).
assert (HU24 : bv_unsigned (ew Ev 24) = fdp) by (rewrite (HE' 24%nat 24%bv eq_refl), Hr24; apply unsigned_lit_small; lia).
assert (HU23 : bv_unsigned (ew Ev 23) = 2 ^ 64 - 1 - p) by (rewrite (HE' 23%nat 23%bv eq_refl), Hr23; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew Ev 18) = 2 ^ 64 - 1 - fdp) by (rewrite (HE' 18%nat 18%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
pose proof (HA 0%nat cut eq_refl ltac:(lia)) as A32.
pose proof (HA 8%nat (p + 3 * i1) eq_refl ltac:(lia)) as A40. pose proof (HA 9%nat (p + 3 * k1) eq_refl ltac:(lia)) as A41.
pose proof (HA 10%nat (fdp + 4 * i1) eq_refl ltac:(lia)) as A42. pose proof (HA 11%nat (fdp + 4 * k1) eq_refl ltac:(lia)) as A43.
pose proof (HA 12%nat _ eq_refl ltac:(lia)) as A44. pose proof (HA 13%nat _ eq_refl ltac:(lia)) as A45. pose proof (HA 14%nat _ eq_refl ltac:(lia)) as A46.
pose proof (HA 15%nat _ eq_refl ltac:(lia)) as A47. pose proof (HA 16%nat _ eq_refl ltac:(lia)) as A48. pose proof (HA 17%nat _ eq_refl ltac:(lia)) as A49.
pose proof (HA 18%nat _ eq_refl ltac:(lia)) as A50. pose proof (HA 19%nat _ eq_refl ltac:(lia)) as A51.
cbn [Nat.add] in A32, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51.
assert (D32 : ew Ev 32 = Z_to_bv 64 cut) by (apply (HV 0%nat); reflexivity).
assert (HS : @st_ok segs fy Ev ss_SW (@mkst fy regs (Z_to_bv 64 PC_BG) mem rom)).
{ unfold ss_SW. subst Ev. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |]. cbn [sv_denot]. rewrite HU2. exact Hr22.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite A40.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). rewrite <- Z.add_assoc. apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac mem md p (3 * T) (3 * i1 + o) HH Hpin ltac:(lia))). }
repeat apply Forall_cons; [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?A44, ?A45, ?A46; reflexivity | cbn; lia | cbn; lia |]);
(apply val_mem_1; [|lia]); [rewrite Z.add_0_r; exact B0 | rewrite <- Z.add_assoc; exact B1 | rewrite <- Z.add_assoc; exact B2].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite A41.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). rewrite <- Z.add_assoc. apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac mem md p (3 * T) (3 * k1 + o) HH Hpin ltac:(lia))). }
repeat apply Forall_cons; [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?A47, ?A48, ?A49; reflexivity | cbn; lia | cbn; lia |]);
(apply val_mem_1; [|lia]); [rewrite Z.add_0_r; exact C0 | rewrite <- Z.add_assoc; exact C1 | rewrite <- Z.add_assoc; exact C2].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite A42.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). rewrite <- Z.add_assoc. apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac mem md fdp (4 * elen E) (4 * i1 + o) HH Hfin ltac:(lia))). }
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A50; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Fi].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite A43.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). rewrite <- Z.add_assoc. apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac mem md fdp (4 * elen E) (4 * k1 + o) HH Hfin ltac:(lia))). }
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A51; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Fk].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia | apply Forall_nil].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU27.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A32; reflexivity | cbn; lia | cbn; lia | exact Vcut].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU27, A40, A41, A42, A43. unfold disj_blocks in Hdisj. repeat split; lia.
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU11, HU12, HU16, HU17, HU18, HU23, HU24, HU25, HU26, HU27, A32, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
repeat split; lia.
+ cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_ltu_U, !U_SOff, HU26, HU11, !Z.add_0_r, !zcanon_id by (unfold M64; lia). apply Z.ltb_lt. lia.
+ cbn [f_alias alias_ok sw_aliases]. repeat split.
* apply U_inj. rewrite (U_SOff _ 40%nat), A40, Z.add_0_r, zcanon_id by (unfold M64; lia). p3_lin; [rewrite ?HU25, ?HU16; lia | lia].
* apply U_inj. rewrite (U_SOff _ 41%nat), A41, Z.add_0_r, zcanon_id by (unfold M64; lia). p3_lin; [rewrite ?HU25, ?HU17; lia | lia].
* apply U_inj. rewrite (U_SOff _ 42%nat), A42, Z.add_0_r, zcanon_id by (unfold M64; lia). p3_lin; [rewrite ?HU24, ?HU26; lia | lia].
* apply U_inj. rewrite (U_SOff _ 43%nat), A43, Z.add_0_r, zcanon_id by (unfold M64; lia). p3_lin; [rewrite ?HU24, ?HU11; lia | lia]. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_BG) mem rom)) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ PC_RH.
{ wr_ok_eval.
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 40); [reflexivity | exact A40 | cbn [r_wlo r_whi]; intros x Hx; right; right; exists p, (3 * T); split; [exact Hpin | split; [exact Hpn0 | lia]] |].
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 41); [reflexivity | exact A41 | cbn [r_wlo r_whi]; intros x Hx; right; right; exists p, (3 * T); split; [exact Hpin | split; [exact Hpn0 | lia]] |].
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 42); [reflexivity | exact A42 | cbn [r_wlo r_whi]; intros x Hx; right; right; exists fdp, (4 * elen E); split; [exact Hfin | split; [exact Hfn0 | lia]] |].
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 43); [reflexivity | exact A43 | cbn [r_wlo r_whi]; intros x Hx; right; right; exists fdp, (4 * elen E); split; [exact Hfin | split; [exact Hfn0 | lia]] |].
eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 2); [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia |].
apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs Ev _ ms HS eq_refl). cbn [ss_pc ss_SW_out].
assert (NB : forall (off : Z) (e : sv) (v : Z) (i : nat) (n : nat) (b : Z),
nth_error (ss_mem ss_SW_out) i = Some (nth i (ss_mem ss_SW_out) (YQ0b.mkRegion None 0 0 0 0 [])) ->
r_base (nth i (ss_mem ss_SW_out) (YQ0b.mkRegion None 0 0 0 0 [])) = Some n ->
In (mkChunk off (CVal 1 e)) (r_chunks (nth i (ss_mem ss_SW_out) (YQ0b.mkRegion None 0 0 0 0 []))) ->
bv_unsigned (ew Ev n) = b -> sv_denot Ev e = Z_to_bv 64 v -> 0 <= v < 256 ->
mbyte segs (ms_mem ms) (b + off) = Some (Z_to_bv 8 v)).
{ intros off e v i n b Hi Hb Hin Hn He Hv. exact (st_chunk_byte Ev ss_SW_out ms i _ n off e b v HS Hi Hb Hin Hn He Hv). }
assert (D44 : ew Ev 44 = Z_to_bv 64 (getz (pal_bytes E) (3 * i1))) by (rewrite <- A44; symmetry; apply Z_to_bv_bv_unsigned).
assert (D45 : ew Ev 45 = Z_to_bv 64 (getz (pal_bytes E) (3 * i1 + 1))) by (rewrite <- A45; symmetry; apply Z_to_bv_bv_unsigned).
assert (D50 : ew Ev 50 = Z_to_bv 64 (getz (fr_vals E) i1)) by (rewrite <- A50; symmetry; apply Z_to_bv_bv_unsigned).
assert (D51 : ew Ev 51 = Z_to_bv 64 (getz (fr_vals E) k1)) by (rewrite <- A51; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dat : forall n v, bv_unsigned (ew Ev n) = v -> sv_denot Ev (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn. cbn [sv_denot]. rewrite Z.add_0_r, Hn. reflexivity. }
pose proof (NB 0 _ _ 0%nat 40%nat _ eq_refl eq_refl ltac:(cbn; tauto) A40 (Dat 47%nat _ A47) ltac:(lia)) as M0.
pose proof (NB 1 _ _ 0%nat 40%nat _ eq_refl eq_refl ltac:(cbn; tauto) A40 (Dat 48%nat _ A48) ltac:(lia)) as M1.
pose proof (NB 2 _ _ 0%nat 40%nat _ eq_refl eq_refl ltac:(cbn; tauto) A40 (Dat 49%nat _ A49) ltac:(lia)) as M2.
pose proof (NB 2 _ _ 1%nat 41%nat _ eq_refl eq_refl ltac:(cbn; tauto) A41 (Dat 46%nat _ A46) ltac:(lia)) as N2.
pose proof (NB 1 _ _ 1%nat 41%nat _ eq_refl eq_refl ltac:(cbn; tauto) A41 (denot_pack2_hi Ev 45 44 _ _ D45 D44 ltac:(lia) ltac:(lia)) ltac:(lia)) as N1.
pose proof (NB 0 _ _ 1%nat 41%nat _ eq_refl eq_refl ltac:(cbn; tauto) A41 (denot_pack2_lo Ev 45 44 _ _ D45 D44 ltac:(lia) ltac:(lia)) ltac:(lia)) as N0.
pose proof (st_chunk_val segs Ev ss_SW_out ms 2%nat _ 42%nat 0 4%N _ _ _ HS eq_refl eq_refl ltac:(cbn; tauto) A42 (denot_sext32_small Ev 51 _ D51 Rk) ltac:(cbn; lia) ltac:(cbn; lia)) as W1.
pose proof (st_chunk_val segs Ev ss_SW_out ms 3%nat _ 43%nat 0 4%N _ _ _ HS eq_refl eq_refl ltac:(cbn; tauto) A43 (denot_sext32_small Ev 50 _ D50 Ri) ltac:(cbn; lia) ltac:(cbn; lia)) as W2.
change (N.to_nat 4) with 4%nat in W1, W2. rewrite Z.add_0_r in M0, N0, W1, W2.
apply HK.
- exact HJ.
- apply (arr8_eswap segs mem (ms_mem ms) p E tail i1 k1 Hpa HE ltac:(lia) ltac:(lia) Hik).
+ intros x Hx Hn1 Hn2. mb_frame_g HF ltac:(lia) ltac:(rewrite ?A40, ?A41, ?A42, ?A43, ?HU2, ?HU27; unfold disj_blocks in Hdisj; lia). reflexivity.
+ intros d Hd. assert (Hd3 : d = 0 \/ d = 1 \/ d = 2) by lia.
destruct Hd3 as [-> | [-> | ->]]; [rewrite !Z.add_0_r; exact M0 | exact M1 | exact M2].
+ intros d Hd. assert (Hd3 : d = 0 \/ d = 1 \/ d = 2) by lia.
destruct Hd3 as [-> | [-> | ->]]; [rewrite !Z.add_0_r; exact N0 | exact N1 | exact N2].
- apply (arr32_eswap segs mem (ms_mem ms) fdp E i1 k1 Hfa ltac:(lia) ltac:(lia) Hik).
+ intros x Hx Hn1 Hn2. mb_frame_g HF ltac:(lia) ltac:(rewrite ?A40, ?A41, ?A42, ?A43, ?HU2, ?HU27; unfold disj_blocks in Hdisj; lia). reflexivity.
+ exact W1.
+ exact W2.
- intros x Hx Hn1 Hn2 Hn3. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?A40, ?A41, ?A42, ?A43, ?HU2, ?HU27; lia). reflexivity.
- p3_reg HS (15%bv:reg) Q15. rewrite Q15. apply denot_U. apply (U_atom _ 32 cut D32). lia.
- p3_reg HS (17%bv:reg) Q17. rewrite Q17. apply denot_U. p3_lin; [rewrite ?HU12, ?A32; lia | lia].
- assert (K0 : forall r : reg, In r SW_KEEP0 -> getr (ms_regs ms) r = getr regs r)
by exact (regs_kept_of_st_ok _ _ _ _ regs _ SW_KEEP0 HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
p3_reg HS (22%bv:reg) Q22.
apply (keep_sub SW_KEEP (22%bv :: SW_KEEP0) _ _ ltac:(vm_compute; reflexivity)).
apply keep_pin; [exact K0 | rewrite Q22, Hr22; cbn [sv_denot]; rewrite HU2; reflexivity].
Qed.
Section h.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (L : layout) (A : astate) (mem0 : word -> option byte) (md0 : Model).
Variables (Lc : layout) (Ac : astate) (md : Model).
Variables (p fdp sp T a lo hi cut mean : Z) (Ep : list entry) (tail : list Z).
Let l := dseg cut Ep lo hi.
Let P := Ptest cut (wsum l) (wdot l).
Let cnt := elen Ep.
Hypothesis Hpn0 : ~ In (p, 3 * T) (blocks L A).
Hypothesis Hfn0 : ~ In (fdp, 4 * cnt) (blocks L A).
Hypothesis Hlen : 3 * cnt + zlen tail = 3 * T.
Hypothesis HEp : ent_ok Ep.
Hypothesis Hf31 : Forall (fun e => snd e < 2 ^ 31) Ep.
Hypothesis Hpf : disj_blocks p (3 * T) fdp (4 * cnt).
Hypothesis Hcnt : cnt < 2 ^ 29.
Hypothesis Hlohi : 0 <= lo /\ lo < hi /\ hi < cnt.
Hypothesis Hcut : 0 <= cut <= 2.
Hypothesis Hmean : 0 <= mean < 2 ^ 64.
Hypothesis Hq : is_quot mean (wdot l) (wsum l).
Hypothesis Hwin : sp0 - STK <= sp + 5036 /\ sp + 5168 <= sp0 /\ sp mod 16 = 0.
Hypothesis Ha : 4096 <= a /\ a + 56 <= alloc_ceiling /\ a mod 8 = 0.
Hypothesis HaN : forall x, 0 <= x < 56 ->
~ (p <= a + x < p + 3 * cnt) /\ ~ (fdp <= a + x < fdp + 4 * cnt) /\ ~ (sp + 5036 <= a + x < sp + 5039).
Definition at_PR (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (E : list entry) (i k : Z) : Prop :=
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md /\ frm_zero (@fp_csr fy) /\
In (p, 3 * T) (blocks Lc Ac) /\ In (fdp, 4 * cnt) (blocks Lc Ac) /\
getr regs 2 = Z_to_bv 64 sp /\ getr regs 27 = Z_to_bv 64 a /\ getr regs 26 = Z_to_bv 64 i /\ getr regs 11 = Z_to_bv 64 k /\
getr regs 25 = Z_to_bv 64 p /\ getr regs 24 = Z_to_bv 64 fdp /\ getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - p) /\
getr regs 18 = Z_to_bv 64 (2 ^ 64 - 1 - fdp) /\ getr regs 19 = Z_to_bv 64 2 /\ getr regs 22 = Z_to_bv 64 (sp + 5038) /\
word_mem segs mem (sp + 56) 1 /\
arr8 segs mem p (pal_bytes E ++ tail) /\ arr32 segs mem fdp (fr_vals E) /\
val_mem segs mem (a + 48) 1 cut /\ val_mem segs mem (a + 16 + 8 * cut) 8 mean /\
pinv dentry P lo hi Ep E i k.
Definition K_SPLIT (regs : bvmap 5 word) (mem : word -> option byte) (Q : config -> Prop) : Prop :=
forall (fy' : FPState) regs' mem' E' i',
frm_zero (@fp_csr fy') -> journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
pdone dentry P lo hi Ep E' i' ->
getr regs' 26 = Z_to_bv 64 i' ->
(forall r : reg, In r PART_KEEP -> getr regs' r = getr regs r) ->
arr8 segs mem' p (pal_bytes E' ++ tail) -> arr32 segs mem' fdp (fr_vals E') ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (p <= x < p + 3 * cnt) -> ~ (fdp <= x < fdp + 4 * cnt) -> ~ (sp + 5036 <= x < sp + 5039) ->
mbyte segs mem' x = mbyte segs mem x) ->
SR segs (mkCfg (@mkst fy' regs' (Z_to_bv 64 PC_SPLIT) mem' rom) md) Q.
Lemma ptest_of_smallb : forall E x, Permutation Ep E -> 0 <= x < cnt ->
ptest (pal_bytes E ++ tail) cut (wsum l) (wdot l) x = smallb dentry P E x.
Proof.
intros E x HP Hx. symmetry. apply smallb_ptest; [apply pal_agrees_app | lia |].
unfold cnt in Hx. unfold elen in *. rewrite <- (Permutation_length HP). exact Hx.
Qed.
Definition at_RH (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (E : list entry) (i k : Z) : Prop :=
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md /\ frm_zero (@fp_csr fy) /\
In (p, 3 * T) (blocks Lc Ac) /\ In (fdp, 4 * cnt) (blocks Lc Ac) /\
getr regs 2 = Z_to_bv 64 sp /\ getr regs 27 = Z_to_bv 64 a /\ getr regs 26 = Z_to_bv 64 i /\ getr regs 11 = Z_to_bv 64 k /\
getr regs 25 = Z_to_bv 64 p /\ getr regs 24 = Z_to_bv 64 fdp /\ getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - p) /\
getr regs 18 = Z_to_bv 64 (2 ^ 64 - 1 - fdp) /\ getr regs 19 = Z_to_bv 64 2 /\ getr regs 22 = Z_to_bv 64 (sp + 5038) /\
getr regs 15 = Z_to_bv 64 cut /\ getr regs 13 = Z_to_bv 64 (a + 16) /\ getr regs 14 = Z_to_bv 64 (2 ^ 64 - 1 - (a + 16)) /\
getr regs 12 = Z_to_bv 64 (3 * i) /\ getr regs 17 = Z_to_bv 64 (3 * i + cut) /\
arr8 segs mem p (pal_bytes E ++ tail) /\ arr32 segs mem fdp (fr_vals E) /\
val_mem segs mem (a + 48) 1 cut /\ val_mem segs mem (a + 16 + 8 * cut) 8 mean /\
pinv dentry P lo hi Ep E i k.
Lemma rounds : forall n (fy : FPState) (regs : bvmap 5 word) mem E i k Q,
part_meas dentry P E i k < Z.of_nat n ->
at_RH fy regs mem E i k -> K_SPLIT regs mem Q ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_RH) mem rom) md) Q.
Proof.
induction n as [|n IH]; intros fy regs mem E i k Q Hn HAT HK.
{ exfalso. destruct HAT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PI).
pose proof (pinv_meas_bound dentry P _ _ _ _ _ _ PI). lia. }
destruct HAT as (HJ & Hfrm & Hpin & Hfin & G2 & G27 & G26 & G11 & G25 & G24 & G23 & G18 & G19 & G22 & G15 & G13 & G14 & G12 & G17
& Hpa & Hfa & Vcut & Vmean & PI).
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof Hwin as (Hw1 & Hw2 & Hw3). pose proof Ha as (Ha1 & Ha2 & Ha3).
pose proof Hlohi as (Hlo0 & Hlh & Hhc). assert (Htl : 0 <= zlen tail) by (unfold zlen; lia).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac mem md p (3 * T) HH Hpin ltac:(lia)) as (Hp0 & Hp1 & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac mem md fdp (4 * cnt) HH Hfin ltac:(lia)) as (Hq0 & Hq1 & _).
pose proof PI as (PIik & PIk & _ & PIhi & PIlen & PIperm & _).
assert (HlenE : elen E = cnt) by (unfold cnt, elen in *; rewrite PIlen; reflexivity).
destruct (part_round_spec dentry P lo hi Ep E i k PI) as (i' & k' & _ & _ & Hi' & Hk' & Sbig & Ssmall & Sup & Sdn & Hcase).
destruct (heap_model _ _ LAWS _ _ _ _ HH) as (Hh & Hlz & _).
assert (HpaZ : 3 * i' + cut < zlen (pal_bytes E ++ tail)) by (rewrite zlen_app_pal; lia).
destruct (SU_loop (Z.to_nat (i' - i)) fy regs mem i i' a cut p mean (wsum l) (wdot l) (pal_bytes E ++ tail)
ltac:(lia) ltac:(lia) ltac:(lia) Hpa HpaZ ltac:(lia) ltac:(rewrite zlen_app_pal; lia)
ltac:(intros z Hz; rewrite (ptest_of_smallb E z PIperm ltac:(lia)); apply Sup; lia)
ltac:(rewrite (ptest_of_smallb E i' PIperm ltac:(lia)); exact Sbig)
Hcut ltac:(lia) Ha2 Vmean Hfrm Hmean Hq G15 G13 G14 G26 G12 G17 G25 G19 G23)
as (fy2 & regs2 & Hms2 & Hfrm2 & Hf2 & S26 & S12 & S16 & K2).
eapply (SR_msteps segs _ _ md _ Hh Hlz Hms2).
assert (HpaZ' : 3 * k + cut < zlen (pal_bytes E ++ tail)) by (rewrite zlen_app_pal; lia).
destruct (SD_loop (Z.to_nat (k - k')) fy2 regs2 mem k k' cut p mean (wsum l) (wdot l) (pal_bytes E ++ tail)
ltac:(lia) ltac:(lia) ltac:(lia) Hpa HpaZ' ltac:(lia) ltac:(rewrite zlen_app_pal; lia)
ltac:(intros z Hz; rewrite (ptest_of_smallb E z PIperm ltac:(lia)); apply Sdn; lia)
ltac:(rewrite (ptest_of_smallb E k' PIperm ltac:(lia)); exact Ssmall)
Hcut Hfrm2 Hf2 Hmean Hq
ltac:(rewrite (K2 15%bv ltac:(inl)); exact G15) ltac:(rewrite (K2 11%bv ltac:(inl)); exact G11)
ltac:(rewrite (K2 25%bv ltac:(inl)); exact G25) ltac:(rewrite (K2 23%bv ltac:(inl)); exact G23))
as (fy3 & regs3 & Hms3 & Hfrm3 & T11 & T17 & K3).
eapply (SR_msteps segs _ _ md _ Hh Hlz Hms3).
assert (T2 : getr regs3 2 = Z_to_bv 64 sp) by (rewrite (K3 2%bv ltac:(inl)), (K2 2%bv ltac:(inl)); exact G2).
assert (T27 : getr regs3 27 = Z_to_bv 64 a) by (rewrite (K3 27%bv ltac:(inl)), (K2 27%bv ltac:(inl)); exact G27).
assert (T25 : getr regs3 25 = Z_to_bv 64 p) by (rewrite (K3 25%bv ltac:(inl)), (K2 25%bv ltac:(inl)); exact G25).
assert (T24 : getr regs3 24 = Z_to_bv 64 fdp) by (rewrite (K3 24%bv ltac:(inl)), (K2 24%bv ltac:(inl)); exact G24).
assert (T23 : getr regs3 23 = Z_to_bv 64 (2 ^ 64 - 1 - p)) by (rewrite (K3 23%bv ltac:(inl)), (K2 23%bv ltac:(inl)); exact G23).
assert (T18 : getr regs3 18 = Z_to_bv 64 (2 ^ 64 - 1 - fdp)) by (rewrite (K3 18%bv ltac:(inl)), (K2 18%bv ltac:(inl)); exact G18).
assert (T19 : getr regs3 19 = Z_to_bv 64 2) by (rewrite (K3 19%bv ltac:(inl)), (K2 19%bv ltac:(inl)); exact G19).
assert (T22 : getr regs3 22 = Z_to_bv 64 (sp + 5038)) by (rewrite (K3 22%bv ltac:(inl)), (K2 22%bv ltac:(inl)); exact G22).
assert (T13 : getr regs3 13 = Z_to_bv 64 (a + 16)) by (rewrite (K3 13%bv ltac:(inl)), (K2 13%bv ltac:(inl)); exact G13).
assert (T14 : getr regs3 14 = Z_to_bv 64 (2 ^ 64 - 1 - (a + 16))) by (rewrite (K3 14%bv ltac:(inl)), (K2 14%bv ltac:(inl)); exact G14).
assert (T26 : getr regs3 26 = Z_to_bv 64 i') by (rewrite (K3 26%bv ltac:(inl)); exact S26).
assert (T12 : getr regs3 12 = Z_to_bv 64 (3 * i')) by (rewrite (K3 12%bv ltac:(inl)); exact S12).
assert (T16 : getr regs3 16 = Z_to_bv 64 (3 * i')) by (rewrite (K3 16%bv ltac:(inl)); exact S16).
destruct Hcase as [(Hle & _ & Hk'eq & Hdone) | (Hlt & _ & PI' & Hmeas)].
- destruct (BG_done fy3 regs3 mem i' k' T26 T11 ltac:(lia) ltac:(lia)) as (regs4 & Hms4 & K4).
eapply (SR_msteps segs _ _ md _ Hh Hlz Hms4).
apply (HK fy3 regs4 mem E i' Hfrm3 HJ Hdone).
+ rewrite (K4 26%bv ltac:(inl)). exact T26.
+ intros r Hr. rewrite (keep_sub PART_KEEP ALL_KEEP _ _ ltac:(vm_compute; reflexivity) K4 r Hr).
rewrite (keep_sub PART_KEEP SD_KEEP _ _ ltac:(vm_compute; reflexivity) K3 r Hr).
apply (keep_sub PART_KEEP SU_KEEP _ _ ltac:(vm_compute; reflexivity) K2 r Hr).
+ exact Hpa.
+ exact Hfa.
+ intros; reflexivity.
- destruct (HaN 48 ltac:(lia)) as (N1 & N2 & N3).
eapply (SW_stretch fy3 regs3 mem STK sp0 FP L A mem0 md0 Lc Ac md E tail i' k' p fdp sp T a cut _ HJ Hpin Hpn0);
[rewrite HlenE; exact Hfin | rewrite HlenE; exact Hfn0 | rewrite HlenE; exact Hpf | exact Hpa | rewrite HlenE; exact Hlen | exact Hfa
| exact (ent_ok_perm _ _ PIperm HEp) | exact (Permutation_Forall PIperm Hf31) | lia | exact Hlt | lia | lia
| exact Hw1 | exact Hw2 | exact Hw3 | exact Ha1 | exact Ha2 | exact Ha3 | exact Hcut | exact Vcut
| rewrite HlenE; exact N1 | rewrite HlenE; exact N2 | exact N3
| exact T2 | exact T27 | exact T26 | exact T11 | exact T12 | exact T16 | exact T17 | exact T25 | exact T24 | exact T23 | exact T18 | exact T22 | ].
intros regs5 mem5 HJ5 Hpa5 Hfa5 Hfr5 U15 U17 K5.
apply (IH fy3 regs5 mem5 (eswap dentry E i' k') i' k' Q ltac:(lia)).
+ split; [exact HJ5|]. split; [exact Hfrm3|]. split; [exact Hpin|]. split; [exact Hfin|].
split; [rewrite (K5 2%bv ltac:(inl)); exact T2|]. split; [rewrite (K5 27%bv ltac:(inl)); exact T27|].
split; [rewrite (K5 26%bv ltac:(inl)); exact T26|]. split; [rewrite (K5 11%bv ltac:(inl)); exact T11|].
split; [rewrite (K5 25%bv ltac:(inl)); exact T25|]. split; [rewrite (K5 24%bv ltac:(inl)); exact T24|].
split; [rewrite (K5 23%bv ltac:(inl)); exact T23|]. split; [rewrite (K5 18%bv ltac:(inl)); exact T18|].
split; [rewrite (K5 19%bv ltac:(inl)); exact T19|]. split; [rewrite (K5 22%bv ltac:(inl)); exact T22|].
split; [exact U15|]. split; [rewrite (K5 13%bv ltac:(inl)); exact T13|]. split; [rewrite (K5 14%bv ltac:(inl)); exact T14|].
split; [rewrite (K5 12%bv ltac:(inl)); exact T12|]. split; [exact U17|].
split; [exact Hpa5|]. split; [exact Hfa5|].
assert (NF : forall i0, 0 <= i0 < 56 -> mbyte segs mem5 (a + i0) = mbyte segs mem (a + i0)).
{ intros i0 Hi0. destruct (HaN i0 Hi0) as (X1 & X2 & X3). apply Hfr5; [lia | rewrite HlenE; exact X1 | rewrite HlenE; exact X2 | exact X3]. }
split; [eapply val_mem_frame; [exact Vcut | intros; rewrite <- Z.add_assoc; apply NF; lia]|].
split; [eapply val_mem_frame; [exact Vmean | intros; rewrite <- !Z.add_assoc; apply NF; lia]|].
exact PI'.
+ intros fy' regs' mem' E' i'' Hfrm' HJ' Hdone' W26 K' Hpa' Hfa' Hfr'.
apply (HK fy' regs' mem' E' i'' Hfrm' HJ' Hdone' W26); [| exact Hpa' | exact Hfa' |].
* intros r Hr. rewrite (K' r Hr), (keep_sub PART_KEEP SW_KEEP _ _ ltac:(vm_compute; reflexivity) K5 r Hr),
(keep_sub PART_KEEP SD_KEEP _ _ ltac:(vm_compute; reflexivity) K3 r Hr).
apply (keep_sub PART_KEEP SU_KEEP _ _ ltac:(vm_compute; reflexivity) K2 r Hr).
* intros x Hx X1 X2 X3. rewrite (Hfr' x Hx X1 X2 X3). apply Hfr5; [exact Hx | rewrite HlenE; exact X1 | rewrite HlenE; exact X2 | exact X3].
Qed.
Theorem partition_SR : forall n (fy : FPState) (regs : bvmap 5 word) mem E i k Q,
part_meas dentry P E i k < Z.of_nat n ->
at_PR fy regs mem E i k -> K_SPLIT regs mem Q ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_PR) mem rom) md) Q.
Proof.
intros n fy regs mem E i k Q Hn HAT HK.
destruct HAT as (HJ & Hfrm & Hpin & Hfin & G2 & G27 & G26 & G11 & G25 & G24 & G23 & G18 & G19 & G22 & Hslot
& Hpa & Hfa & Vcut & Vmean & PI).
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof Hwin as (Hw1 & Hw2 & Hw3). pose proof Ha as (Ha1 & Ha2 & Ha3).
pose proof Hlohi as (Hlo0 & Hlh & Hhc). assert (Htl : 0 <= zlen tail) by (unfold zlen; lia).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac mem md p (3 * T) HH Hpin ltac:(lia)) as (Hp0 & Hp1 & _).
pose proof PI as (PIik & PIk & _ & PIhi & _).
destruct (heap_model _ _ LAWS _ _ _ _ HH) as (Hh & Hlz & _).
destruct (PR_to_RH fy regs mem a i cut p sp G27 G26 G25 G2 ltac:(lia) Ha1 ltac:(lia) Ha3 Hcut ltac:(lia) ltac:(lia) Hw3 Vcut Hslot)
as (regs1 & Hms1 & R15 & R13 & R14 & R12 & R17 & K1).
eapply (SR_msteps segs _ _ md _ Hh Hlz Hms1).
apply (rounds n fy regs1 mem E i k Q Hn).
- split; [exact HJ|]. split; [exact Hfrm|]. split; [exact Hpin|]. split; [exact Hfin|].
split; [rewrite (K1 2%bv ltac:(inl)); exact G2|]. split; [rewrite (K1 27%bv ltac:(inl)); exact G27|].
split; [rewrite (K1 26%bv ltac:(inl)); exact G26|]. split; [rewrite (K1 11%bv ltac:(inl)); exact G11|].
split; [rewrite (K1 25%bv ltac:(inl)); exact G25|]. split; [rewrite (K1 24%bv ltac:(inl)); exact G24|].
split; [rewrite (K1 23%bv ltac:(inl)); exact G23|]. split; [rewrite (K1 18%bv ltac:(inl)); exact G18|].
split; [rewrite (K1 19%bv ltac:(inl)); exact G19|]. split; [rewrite (K1 22%bv ltac:(inl)); exact G22|].
split; [exact R15|]. split; [exact R13|]. split; [exact R14|]. split; [exact R12|]. split; [exact R17|].
split; [exact Hpa|]. split; [exact Hfa|]. split; [exact Vcut|]. split; [exact Vmean|]. exact PI.
- intros fy' regs' mem' E' i' Hfrm' HJ' Hd W26 K' Hpa' Hfa' Hfr'.
apply (HK fy' regs' mem' E' i' Hfrm' HJ' Hd W26); [| exact Hpa' | exact Hfa' | exact Hfr'].
intros r Hr. rewrite (K' r Hr). apply (keep_sub PART_KEEP PR_KEEP _ _ ltac:(vm_compute; reflexivity) K1 r Hr).
Qed.
End h.
End J.
End c.
