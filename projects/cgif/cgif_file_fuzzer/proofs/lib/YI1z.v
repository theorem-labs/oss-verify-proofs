(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YI06 YI5b YI09 YI08 YI0r
YI1w YI4l YI21 YI2m YI5o YI5l YI6b YI5n   YI20.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI5c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI3u YI22 YI5a YI05 YI18 YI0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI1x.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Local Lemma u64_range' : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition CLOSE : Z := src0_A_cgif_close.
Definition CL_LOOP : Z := Eval vm_compute in (src0_A_cgif_close + 0x28).
Definition CL_CURW : Z := Eval vm_compute in (src0_A_cgif_close + 0x50).
Definition CL_CLEAN : Z := Eval vm_compute in (src0_A_cgif_close + 0x54).
Definition CL_FILE : Z := Eval vm_compute in (src0_A_cgif_close + 0x64).
Definition CL_FREE : Z := Eval vm_compute in (src0_A_cgif_close + 0x84).
Definition lits15 : list (option Z) :=
[None; None; None; None; None; None; None; None; None; None; None; Some 0; Some 0; None; None].
Lemma lits15_ok : forall s, forall j z, nth_error lits15 j = Some (Some z) -> nth_error (vals15 s) j = Some z.
Proof.
intros s j z Hj. do 15 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
Qed.
Definition cl_saved : list YP09.chunk :=
[mkChunk 24 (CVal 8 (SOff 49 0)); mkChunk 16 (CVal 8 (SOff 50 0)); mkChunk 8 (CVal 8 (SOff 51 0)); mkChunk 0 (CVal 8 (SOff 52 0))].
Definition cl_saved_vals (regs0 : bvmap 5 word) : list Z :=
[bv_unsigned (getr regs0 1); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18)].
Definition cl_saved_ok (mem : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
word_mem src0segs mem (sp0 - 8) (bv_unsigned (getr regs0 1)) /\ word_mem src0segs mem (sp0 - 16) (bv_unsigned (getr regs0 8)) /\
word_mem src0segs mem (sp0 - 24) (bv_unsigned (getr regs0 9)) /\ word_mem src0segs mem (sp0 - 32) (bv_unsigned (getr regs0 18)).
Definition cl_R1 : YP09.region := YP09.mkRegion (Some 8%nat) 0 88 0 0 (obj_chunks_gen LAY15 32 lits15).
Definition cl_R2 : YP09.region := YP09.mkRegion (Some 8%nat) 88 96 88 92 [mkChunk 88 (CVal 4 (SOff 47 0)); mkChunk 92 (CVal 4 (SOff 48 0))].
Definition cl_facts : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + CLOSE_STK - 32) (2^63 - 32) 4); (8%nat, mkAF 4096 (CEIL_MAX - 96) 4);
(47%nat, mkAF 0 4294967295 0); (48%nat, mkAF 0 4294967295 0) ].
Definition cl_untouched (regs0 regs1 : bvmap 5 word) : Prop :=
getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 19 = getr regs0 19 /\ getr regs1 20 = getr regs0 20 /\ getr regs1 21 = getr regs0 21 /\ getr regs1 22 = getr regs0 22 /\
getr regs1 23 = getr regs0 23 /\ getr regs1 24 = getr regs0 24 /\ getr regs1 25 = getr regs0 25 /\ getr regs1 26 = getr regs0 26 /\
getr regs1 27 = getr regs0 27.
Definition ss_free (k : Z) : sstate :=
mkSS CL_FREE (sr_set (sr_set sr_atoms 9%bv (SOff 8 24)) 18%bv (SOff 8 (8 * k)))
[ YP09.mkRegion (Some 2%nat) 0 32 0 32 cl_saved ; cl_R1 ; cl_R2 ]
None (mkFacts cl_facts [] []).
End d.
Ltac wr_cl HU2 HU8 Hgin HFPin :=
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_cons_ro; [cbn; lia|];
eapply wr_ok_cons_block with (n := 8%nat) (m := CGIF_SIZE);
[ reflexivity | ew_havocA; exact HU8 | exact Hgin | cbn; lia | unfold CGIF_SIZE; cbn; lia
| unfold cl_R2; cbn [r_wlo r_whi]; intros a Ha; eapply (HFPin _ CGIF_SIZE a); [left; reflexivity | unfold CGIF_SIZE; lia]
| apply wr_ok_nil ].
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma region_kept_live : forall E (mem mem' : word -> option byte) r n b m,
r_base r = Some n -> bv_unsigned (ew E n) = b ->
(forall i, 0 <= i < m -> mbyte src0segs mem' (b + i) = mbyte src0segs mem (b + i)) ->
(forall i, r_wlo r <= i < r_whi r -> writable_at src0segs mem' (b + i)) ->
0 <= r_lo r -> r_hi r <= m ->
region_kept src0segs E mem mem' r.
Proof.
intros E mem mem' r n b m Hb Hn Hk Hw Hlo Hhi. split; rewrite Hb; cbn [base_val]; rewrite Hn; intros a Ha.
- replace a with (b + (a - b)) by lia. apply Hk. lia.
- intros _. replace a with (b + (a - b)) by lia. apply Hw. lia.
Qed.
End h.
Ltac cgif_obj_now_at i1 i2 HS HU8 HXn Rg s cur ecur tcur :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch type of HU8 with bv_unsigned _ = ?g =>
assert (obj_at src0segs (ms_mem msc) g LAY_CGIF (vals15 s ++ [cur; cg_ihead s]));
[ apply obj_cgif_join;
[ eapply (st_obj_at src0segs _ _ _ i1 _ 8%nat g LAY15 (vals15 s) 32 lits15 HS eq_refl eq_refl ltac:(ew_havocA; exact HU8));
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ];
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; split;
[ let Hlj := fresh "Hlj" in assert (Hlj : (j < length (vals15 s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate); change (length (vals15 s)) with 15%nat in Hlj;
replace (nth j LAY15 (0, 8%N)) with (nth j LAY_CGIF (0, 8%N)) by (do 15 (destruct j as [|j]; [reflexivity|]); exfalso; lia);
apply (Rg j v); rewrite cgif_vals_split, nth_error_app1 by exact Hlj; exact Hj
| do 15 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [nth_error lits15];
first [reflexivity | ew_havocA; apply (HXn _ _ _ eq_refl); reflexivity] |]);
exfalso; destruct j; cbn in Hj; discriminate Hj ]
| replace (g + 88) with (bv_unsigned (ew Ec 8) + 88) by (ew_havocA; rewrite HU8; reflexivity);
eapply (st_chunk_val src0segs _ _ _ i2 _ 8%nat 88 4%N ecur _ cur HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | tcur | change (2 ^ (8 * Z.of_N 4%N)) with (2 ^ 32); assumption | cbn; lia]
| assumption
| replace (g + 92) with (bv_unsigned (ew Ec 8) + 92) by (ew_havocA; rewrite HU8; reflexivity);
eapply (st_chunk_val src0segs _ _ _ i2 _ 8%nat 92 4%N (SOff 48 0) _ (cg_ihead s) HS);
[reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 48%nat 16%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 4%N)) with (2 ^ 32); assumption | cbn; lia]
| assumption ]
| ] end end.
Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma st_chunk_lowv : forall E ss ms i rg p off (n : N) e a (k : nat) (m : Z),
st_ok src0segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CVal n e)) (r_chunks rg) -> bv_unsigned (ew E p) = a -> Z.of_N n <= 8 ->
k = N.to_nat n -> m = 2 ^ (8 * Z.of_N n) ->
val_mem src0segs (ms_mem ms) (a + off) k (U E e mod m).
Proof.
intros E ss ms i rg p off n e a k m HS Hi Hb Hin Hp Hn -> ->.
pose proof (st_region_chunks src0segs E ss ms i rg p a HS Hi Hb Hp) as Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
unfold U. exact (val_mem_low_of_chunk src0segs E (ms_mem ms) a off n e Hc Hn).
Qed.
End l.
Ltac cgif_obj_low_at i1 i2 HS HU8 HXn Rg s k :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch type of HU8 with bv_unsigned _ = ?g =>
assert (obj_at src0segs (ms_mem msc) g LAY_CGIF (vals15 s ++ [U Ec (SOff k 0) mod 2 ^ 32; cg_ihead s]));
[ apply obj_cgif_join;
[ eapply (st_obj_at src0segs _ _ _ i1 _ 8%nat g LAY15 (vals15 s) 32 lits15 HS eq_refl eq_refl ltac:(ew_havocA; exact HU8));
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ];
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; split;
[ let Hlj := fresh "Hlj" in assert (Hlj : (j < length (vals15 s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate); change (length (vals15 s)) with 15%nat in Hlj;
replace (nth j LAY15 (0, 8%N)) with (nth j LAY_CGIF (0, 8%N)) by (do 15 (destruct j as [|j]; [reflexivity|]); exfalso; lia);
apply (Rg j v); rewrite cgif_vals_split, nth_error_app1 by exact Hlj; exact Hj
| do 15 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [nth_error lits15];
first [reflexivity | ew_havocA; apply (HXn _ _ _ eq_refl); reflexivity] |]);
exfalso; destruct j; cbn in Hj; discriminate Hj ]
| replace (g + 88) with (bv_unsigned (ew Ec 8) + 88) by (ew_havocA; rewrite HU8; reflexivity);
eapply (st_chunk_lowv _ _ _ i2 _ 8%nat 88 4%N (SOff k 0) _ 4%nat (2 ^ 32) HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn; lia | reflexivity | reflexivity]
| pose proof (Z.mod_pos_bound (U Ec (SOff k 0)) (2 ^ 32) ltac:(lia)); lia
| replace (g + 92) with (bv_unsigned (ew Ec 8) + 92) by (ew_havocA; rewrite HU8; reflexivity);
eapply (st_chunk_val src0segs _ _ _ i2 _ 8%nat 92 4%N (SOff 48 0) _ (cg_ihead s) HS);
[reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 48%nat 16%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 4%N)) with (2 ^ 32); assumption | cbn; lia]
| assumption ]
| ] end end.
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Hypothesis FWRITE : fwrite_spec src0_msyms MR src0_A_fwrite.
Hypothesis FCLOSE : fclose_spec_res src0_msyms MR src0_A_fclose.
Definition close_postR (regs0 : bvmap 5 word) (FP : list (Z * Z)) L A mem md (rest : list (Z * Z)) (bF : rbound) (c' : config) : Prop :=
exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom src0segs)) md' /\
journal src0_msyms MR CLOSE_STK (spZ regs0) FP L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\
Permutation (blocks L' A') rest /\ st_init_done A' = true /\ res_ok A' bF.
Definition fr_rb (N : Z) (o : option frame_st) (b : rbound) : rbound := match o with Some _ => rb_free b N | None => b end.
Lemma cgif_fp_in : forall g s N b n a,
In (b, n) (cgif_blocks0 g s N) -> b <= a < b + n -> inFP (blocks_fp (cgif_blocks0 g s N)) a.
Proof. intros g s N b n a Hin Ha. apply inFP_blocks_fp. exists b, n. auto. Qed.
Lemma heap_sep_app : forall L A mem md (l1 l2 : list (Z * Z)) x y,
heap_ok MR L A mem md -> Permutation (blocks L A) (l1 ++ l2) -> In x l1 -> In y l2 ->
fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
intros L A mem md l1 l2 x y HH HP Hx Hy. destruct (in_split _ _ Hx) as (a & b & ->).
apply (heap_sep_perm _ _ LAWS L A mem md x (a ++ b ++ l2) y HH).
- eapply Permutation_trans; [exact HP|]. rewrite <- app_assoc. cbn [app]. apply Permutation_sym.
replace (a ++ b ++ l2) with (a ++ (b ++ l2)) by reflexivity. apply Permutation_middle.
- apply in_app_iff. right. apply in_app_iff. right. exact Hy.
Qed.
Lemma close_free2 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (rest FP : list (Z * Z)) (o0 o1 o2 : option frame_st) (br : rbound),
let sp0 := spZ regs0 in
journal src0_msyms MR CLOSE_STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp src0_msyms) -> sp0 mod 16 = 0 ->
cg_frames s = [o0; o1; o2] ->
(forall b n a, In (b, n) (cgif_blocks0 g s N) -> b <= a < b + n -> inFP FP a) ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
Permutation (blocks Lc Ac) ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N [o2] ++ rest) ->
obj_at src0segs memc g LAY_CGIF (cgif_vals s) ->
frames_at memc [o2] ->
cl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 32) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 (g + 24) -> getr regs1 18 = Z_to_bv 64 (g + 16) ->
cl_untouched regs0 regs1 -> res_ok Ac br ->
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom src0segs)) mdc) (close_postR regs0 FP L A mem md rest (fr_rb N o2 br)).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s rest FP o0 o1 o2 br sp0 HJ Hra0 Htp0 Hal16 Hfs HFPin HFPlow HB Hobj Hfr HSV G2 G8 G9 G18 HUT HRb.
assert (Ho2 : nth_error (cg_frames s) 2 = Some o2) by (rewrite Hfs; reflexivity).
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HCSv : CLOSE_STK = 9728) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hspm : (sp0 - 32) mod 16 = 0) by (replace (sp0 - 32) with (sp0 + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc g CGIF_SIZE HH0 Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
set (E := Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error (cgif_vals s) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HXn : forall n j v, n = (32 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew E n = Z_to_bv 64 v) by (intros n j v -> Hj; apply HX; exact Hj).
assert (HY : forall j v, nth_error (cl_saved_vals regs0) j = Some v -> ew E (49 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (49 + j)%nat with (32 + (length (cgif_vals s) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HW49 : ew E 49 = getr regs0 1) by (etransitivity; [apply (HY 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW50 : ew E 50 = getr regs0 8) by (etransitivity; [apply (HY 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW51 : ew E 51 = getr regs0 9) by (etransitivity; [apply (HY 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW52 : ew E 52 = getr regs0 18) by (etransitivity; [apply (HY 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
pose proof HSV as (W1 & W8 & W9 & W18).
destruct (obj_cgif_parts memc g s Hobj) as (H15 & Hcur & Rcur & Hih & Rih).
assert (HS : st_ok src0segs E (ss_free 2) (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom src0segs))).
{ unfold ss_free. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |] | intros H0; discriminate H0 |];
cbn [sv_denot]; rewrite (ew_Ereg_nat regs1 _ 8 8%bv eq_refl), G8, unsigned_lit_small by lia; [exact G9 | rewrite G18; f_equal; lia].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : Z), nth_error (cl_saved_vals regs0) j = Some w -> word_mem src0segs memc (sp0 - 32 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok src0segs (Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])) memc (sp0 - 32) (mkChunk off (CVal 8 (SOff (49 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HY j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold cl_saved.
apply Forall_cons; [apply (CK 24 0%nat _ eq_refl); [replace (sp0 - 32 + 24) with (sp0 - 8) by lia; exact W1 | apply u64_range']|].
apply Forall_cons; [apply (CK 16 1%nat _ eq_refl); [replace (sp0 - 32 + 16) with (sp0 - 16) by lia; exact W8 | apply u64_range']|].
apply Forall_cons; [apply (CK 8 2%nat _ eq_refl); [replace (sp0 - 32 + 8) with (sp0 - 24) by lia; exact W9 | apply u64_range']|].
apply Forall_cons; [apply (CK 0 3%nat _ eq_refl); [replace (sp0 - 32 + 0) with (sp0 - 32) by lia; exact W18 | apply u64_range']|].
apply Forall_nil.
+ unfold cl_R1. eapply (region_ok_obj_gen src0segs _ memc 8 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[exact HU8 | lia | lia | exact H15 | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj|].
apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
+ unfold cl_R2, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable src0_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE o HH0 Hgin ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih]. }
apply Forall_nil.
- unfold cl_R1, cl_R2. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU8. repeat split; lia.
- split; [| split; constructor].
cbn [f_atoms atoms_ok cl_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
pose proof (Rg 15%nat _ eq_refl) as R47. pose proof (Rg 16%nat _ eq_refl) as R48.
cbn [nth snd LAY_CGIF Z.of_N] in R47, R48.
rewrite HU2, HU8, (HXn 47%nat 15%nat _ eq_refl eq_refl), (HXn 48%nat 16%nat _ eq_refl eq_refl).
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ src0_A_freeFrame.
{ wr_cl HU2 HU8 Hgin HFPin. }
jreg HS (10%bv:reg) as Hf10. jreg HS (2%bv:reg) as Hf2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hf2.
jreg HS (4%bv:reg) as Hf4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hf4. jreg HS (1%bv:reg) as Hf1x.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 32) by (unfold spZ; rewrite Hf2; apply unsigned_lit_small; lia) end.
set (rest0 := (g, CGIF_SIZE) :: pal_blocks s ++ rest).
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 (Z_to_bv 64 (src0_A_cgif_close + 0x8c)) mem2 (seg_rom src0segs)) md2 /\
journal src0_msyms MR CLOSE_STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs msx) regs2 /\ Permutation (blocks L2 A2) rest0 /\ res_ok A2 (fr_rb N o2 br) /\
(forall b n i, In (b, n) rest0 -> 0 <= i < n -> mbyte src0segs mem2 (b + i) = mbyte src0segs (ms_mem msx) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 32 - FREEFRAME_STK <= x < sp0 - 32) ->
mbyte src0segs mem2 x = mbyte src0segs (ms_mem msx) x /\ (writable_at src0segs (ms_mem msx) x <-> writable_at src0segs mem2 x)))
end.
{ destruct o2 as [f|].
-
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Ho2).
cbn [frames_blocks flat_map] in HB. rewrite app_nil_r in HB.
assert (HBf : Permutation (blocks Lc Ac) ((fr_ptr f, FRAME_SIZE) :: (fr_img f, N) :: pals_of (fr_attr f) (fr_lpal f) (3 * fr_nlp f) ++ rest0)).
{ pose proof (perm_front_mid (g, CGIF_SIZE) (pal_blocks s) (frame_blocks N f) [] rest) as PM. rewrite !app_nil_r in PM. cbn [app] in PM.
eapply Permutation_trans; [exact HB|]. eapply Permutation_trans; [exact PM|]. subst rest0. unfold pals_of, frame_blocks. cbn [app]. apply Permutation_refl. }
assert (Hsepf : forall b n, In (b, n) (frame_blocks N f) -> g + CGIF_SIZE <= b \/ b + n <= g).
{ intros b n Hbn. apply (heap_sep_perm _ _ LAWS Lc Ac _ mdc (g, CGIF_SIZE) (pal_blocks s ++ frame_blocks N f ++ rest) (b, n) HH0 HB).
apply in_app_iff. right. apply in_app_iff. left. exact Hbn. }
pose proof (Hsepf (fr_ptr f) FRAME_SIZE ltac:(left; reflexivity)) as Hsep1.
assert (Hfbl : In (fr_ptr f, FRAME_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HBf | left; reflexivity]).
destruct (blocks_range _ _ LAWS Lc Ac _ mdc (fr_ptr f) FRAME_SIZE HH0 Hfbl) as [Hf0 Hf1].
eapply SR_mono.
{ eapply (jcall src0_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := fp_freeFrame (fr_ptr f) (fr_img f) N (fr_attr f) (fr_lpal f) (3 * fr_nlp f))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => Permutation (blocks L2 A2) rest0 /\ res_ok A2 (rb_free br N));
[ exact HS | reflexivity | exact HJ | exact Hf1x | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp; unfold FREEFRAME_STK; lia | rewrite Hsp; lia | exact Hf4 | ].
+ intros HPRE1. eapply SR_mono.
{ eapply (src0_freeFrame_resc API IMG _ _ _ _ _ (fr_ptr f) (frame_vals f) (fr_img f) N (fr_attr f) (fr_lpal f) (3 * fr_nlp f) rest0 br HPRE1);
[ | | reflexivity | reflexivity | reflexivity | exact HBf | exact HRb ].
- rewrite Hf10, (HXn 34%nat 2%nat _ eq_refl eq_refl). rewrite (@nth_error_nth _ (cg_frames s) 2 _ None Ho2). reflexivity.
- eapply obj_at_transport_range; [exact (Hfr f ltac:(left; reflexivity)) | exact (proj1 LAY_Frame_ok) |].
intros i Hi. cbn [ms_mem mkst] in *. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJc & HP & HB2 & _ & HR2).
exists L2, A2, regs2, mem2, md2. split; [rewrite Hf1x; reflexivity|]. split; [exact HJc|]. split; [exact HP | split; [exact HB2 | exact HR2]].
+ intros a Ha. split; [| apply HFPlow].
all: unfold fp_freeFrame in Ha; apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[apply (HFPin (fr_ptr f) FRAME_SIZE a); [apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | left; reflexivity] | unfold FRAME_SIZE; lia] |];
apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[apply (HFPin (fr_img f) N a); [apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | right; left; reflexivity] | lia] |];
(destruct (Z.land (fr_attr f) 1 =? 0) eqn:Hz; [exfalso; exact (YI04.inFP_nil a Ha)|]);
apply inFP_cons in Ha; (destruct Ha as [Ha|Ha]; [|exfalso; exact (YI04.inFP_nil a Ha)]);
(apply (HFPin (fr_lpal f) (3 * fr_nlp f) a); [apply (frame_blocks_in_cgif0 g s N f); [exact Hfin|]; unfold frame_blocks; rewrite Hz; right; right; left; reflexivity | lia]). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HB2 & HR2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|]. split; [exact HR2|].
pose proof HJc2 as (_ & _ & Hhi2 & Hkeep2 & _). rewrite Hsp in Hhi2. split; [| exact Hhi2].
intros b n i Hbn Hi.
assert (HsepR : forall x, In x (frame_blocks N f) -> fst x + snd x <= b \/ b + n <= fst x).
{ intros x Hx. pose proof (heap_sep_app Lc Ac _ mdc (frame_blocks N f) rest0 x (b, n) HH0 ltac:(eapply Permutation_trans; [exact HBf|]; unfold frame_blocks, pals_of; cbn [app]; apply Permutation_refl) Hx Hbn) as Hs.
cbn [fst snd] in Hs. exact Hs. }
apply (Hkeep2 b n i); [eapply blocks_perm_in; [exact HB | ] | eapply blocks_perm_in; [exact HB2 |] | exact Hi |].
{ subst rest0. destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right]. apply in_app_iff in Hbn. apply in_app_iff.
destruct Hbn as [Hbn|Hbn]; [left; exact Hbn | right]. apply in_app_iff. right. exact Hbn. }
{ destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn]. }
intros Hin. unfold fp_freeFrame in Hin. apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [pose proof (HsepR _ ltac:(left; reflexivity)); cbn [fst snd] in *; lia|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [pose proof (HsepR _ ltac:(right; left; reflexivity)); cbn [fst snd] in *; lia|].
destruct (Z.land (fr_attr f) 1 =? 0) eqn:Hz; [exact (YI04.inFP_nil _ Hin)|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [| exact (YI04.inFP_nil _ Hin)].
pose proof (HsepR (fr_lpal f, 3 * fr_nlp f) ltac:(unfold frame_blocks; rewrite Hz; right; right; left; reflexivity)). cbn [fst snd] in *. lia.
-
cbn [frames_blocks flat_map app] in HB.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_mono.
{ eapply (jcall src0_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := @nil (Z * Z))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => Permutation (blocks L2 A2) rest0 /\ res_ok A2 br);
[ exact HS | reflexivity | exact HJ | exact Hf1x | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp; unfold FREEFRAME_STK; lia | rewrite Hsp; lia | exact Hf4
| intros a Ha; exfalso; exact (YI04.inFP_nil a Ha) ].
intros HPRE1. eapply SR_mono.
{ eapply (src0_freeFrame_null API IMG _ _ _ _ _ HPRE1). rewrite Hf10, (HXn 34%nat 2%nat _ eq_refl eq_refl). rewrite (@nth_error_nth _ (cg_frames s) 2 _ None Ho2). reflexivity. }
cbv beta. intros c' (regs2 & mem2 & -> & HJc & HP).
exists Lc, Ac, regs2, mem2, mdc. split; [rewrite Hf1x; reflexivity|]. split; [exact HJc|]. split; [exact HP | split; [exact HB | exact HRb]]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HB2 & HR2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|]. split; [exact HR2|].
pose proof HJc2 as (_ & _ & Hhi2 & Hkeep2 & _). rewrite Hsp in Hhi2. split; [| exact Hhi2].
intros b n i Hbn Hi. apply (Hkeep2 b n i); [eapply blocks_perm_in; [exact HB |] | eapply blocks_perm_in; [exact HB2 |] | exact Hi | intros Hin; exact (YI04.inFP_nil _ Hin)];
(destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn]). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HB2 & HR2 & Hkg & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hkg, Hhi2, HJ2.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
jafter_call_keep HS 53%nat regs2 mem2 HP2 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack src0segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | cbn; intros i Hi; lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | | cbn; lia | cbn; lia].
cbn [r_wlo r_whi cl_R2]. intros i Hi. apply (present_writable src0_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 g CGIF_SIZE i HH2 Hgin2 ltac:(lia))). }
clear HS. rename HS2 into HS.
jrun_to LAWS src0tbl_ok HS HJ2 src0_A_freeCGIF. { wr_cl HU2 HU8 Hgin2 HFPin. }
jreg HS (10%bv:reg) as Hc10. jreg HS (2%bv:reg) as Hc2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hc2.
jreg HS (4%bv:reg) as Hc4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hc4. jreg HS (1%bv:reg) as Hc1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp2 : spZ (ms_regs msx) = sp0 - 32) by (unfold spZ; rewrite Hc2; apply unsigned_lit_small; lia) end.
cgif_obj_now_at 1%nat 2%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end.
assert (Hpalsep : Z.land (cg_attr s) 4 = 0 -> g + CGIF_SIZE <= cg_pal s \/ cg_pal s + 3 * cg_ngp s <= g).
{ intros Hz. apply (heap_sep_perm _ _ LAWS L2 A2 mem2 md2 (g, CGIF_SIZE) (pal_blocks s ++ rest) (cg_pal s, 3 * cg_ngp s) HH2 HB2).
apply in_app_iff. left. unfold pal_blocks. rewrite Hz. left. reflexivity. }
eapply SR_bind.
{ eapply (jcall src0_msyms MR) with (STK1 := FREECGIF_STK) (FP1 := fp_freeCGIF g (cg_attr s) (cg_pal s) (3 * cg_ngp s))
(K := fun L3 A3 (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) => Permutation (blocks L3 A3) rest /\ st_init_done A3 = true /\ res_ok A3 (fr_rb N o2 br));
[ exact HS | reflexivity | exact HJ2 | exact Hc1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp2; exact Hspm | unfold FREECGIF_STK; lia | rewrite Hsp2; unfold FREECGIF_STK; lia | rewrite Hsp2; lia | exact Hc4 | ].
- intros HPRE2. eapply SR_mono.
{ eapply (src0_freeCGIF_resc API IMG _ _ _ _ _ g _ (cg_attr s) (cg_pal s) (3 * cg_ngp s) rest (fr_rb N o2 br) HPRE2); [ | exact Hobj2 | reflexivity | reflexivity | exact HB2 | exact HR2 ].
rewrite Hc10. ew_havocA. rewrite <- HU8. symmetry. apply Z_to_bv_bv_unsigned. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJc & HP & HB3 & Hid3 & HR3).
exists L3, A3, regs3, mem3, md3. split; [rewrite Hc1; reflexivity|]. split; [exact HJc|]. split; [exact HP | split; [exact HB3 | split; [exact Hid3 | exact HR3]]].
- intros a Ha. split; [| apply HFPlow].
all: unfold fp_freeCGIF in Ha; apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[apply (HFPin g CGIF_SIZE a); [left; reflexivity | lia] |];
(destruct (Z.land (cg_attr s) 4 =? 0) eqn:Hz; [|exfalso; exact (YI04.inFP_nil a Ha)]);
apply inFP_cons in Ha; (destruct Ha as [Ha|Ha]; [|exfalso; exact (YI04.inFP_nil a Ha)]);
(apply (HFPin (cg_pal s) (3 * cg_ngp s) a); [unfold cgif_blocks0, pal_blocks; rewrite Hz; right; right; left; reflexivity | lia]). }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & (HB3 & Hid3 & HR3)). clear HJ2.
cbn [ms_regs ms_mem mkst] in HP3, HJc3, HJ3.
pose proof HJc3 as (_ & _ & Hhi3 & _). rewrite Hsp2 in Hhi3.
jafter_call_keep HS 69%nat regs3 mem3 HP3 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack src0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi3 | lia | lia | unfold FREECGIF_STK; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS src0tbl_ok HS HJ3.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
eapply (SR_ret_at src0segs src0tbl); [exact src0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3)))). }
unfold close_postR.
lazymatch type of HS with st_ok _ _ _ ?msf => exists L3, A3, (ms_regs msf), (ms_mem msf), md3 end.
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg src0segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|nat_lt_lit]); rewrite ?Z.add_0_r, HW49, Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end. }
split; [exact HJ3|].
split; [| split; [exact HB3 | split; [exact Hid3 | exact HR3]]].
apply regs_preserved_intro; cbn [ms_regs mkst].
- reg_nowF HS ltac:(rewrite HU2; replace (sp0 - 32 + 32) with sp0 by lia; subst sp0; unfold spZ; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
- reg_nowF HS ltac:(rewrite HW50; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW51; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW52; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G19).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
Qed.
Lemma frames_blocks_ptr_in : forall N fs f, In (Some f) fs -> In (fr_ptr f, FRAME_SIZE) (frames_blocks N fs).
Proof. intros N fs f Hin. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hin | left; reflexivity]. Qed.
Lemma close_free1 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (rest FP : list (Z * Z)) (o0 o1 o2 : option frame_st) (br : rbound),
let sp0 := spZ regs0 in
journal src0_msyms MR CLOSE_STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp src0_msyms) -> sp0 mod 16 = 0 ->
cg_frames s = [o0; o1; o2] ->
(forall b n a, In (b, n) (cgif_blocks0 g s N) -> b <= a < b + n -> inFP FP a) ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
Permutation (blocks Lc Ac) ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N [o1; o2] ++ rest) ->
obj_at src0segs memc g LAY_CGIF (cgif_vals s) ->
frames_at memc [o1; o2] ->
cl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 32) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 (g + 24) -> getr regs1 18 = Z_to_bv 64 (g + 8) ->
cl_untouched regs0 regs1 -> res_ok Ac br ->
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom src0segs)) mdc) (close_postR regs0 FP L A mem md rest (fr_rb N o2 (fr_rb N o1 br))).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s rest FP o0 o1 o2 br sp0 HJ Hra0 Htp0 Hal16 Hfs HFPin HFPlow HB Hobj Hfr HSV G2 G8 G9 G18 HUT HRb.
assert (Ho1 : nth_error (cg_frames s) 1 = Some o1) by (rewrite Hfs; reflexivity).
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HCSv : CLOSE_STK = 9728) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hspm : (sp0 - 32) mod 16 = 0) by (replace (sp0 - 32) with (sp0 + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc g CGIF_SIZE HH0 Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
set (E := Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error (cgif_vals s) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HXn : forall n j v, n = (32 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew E n = Z_to_bv 64 v) by (intros n j v -> Hj; apply HX; exact Hj).
assert (HY : forall j v, nth_error (cl_saved_vals regs0) j = Some v -> ew E (49 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (49 + j)%nat with (32 + (length (cgif_vals s) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HW49 : ew E 49 = getr regs0 1) by (etransitivity; [apply (HY 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW50 : ew E 50 = getr regs0 8) by (etransitivity; [apply (HY 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW51 : ew E 51 = getr regs0 9) by (etransitivity; [apply (HY 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW52 : ew E 52 = getr regs0 18) by (etransitivity; [apply (HY 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
pose proof HSV as (W1 & W8 & W9 & W18).
destruct (obj_cgif_parts memc g s Hobj) as (H15 & Hcur & Rcur & Hih & Rih).
assert (HS : st_ok src0segs E (ss_free 1) (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom src0segs))).
{ unfold ss_free. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |] | intros H0; discriminate H0 |];
cbn [sv_denot]; rewrite (ew_Ereg_nat regs1 _ 8 8%bv eq_refl), G8, unsigned_lit_small by lia; [exact G9 | rewrite G18; f_equal; lia].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : Z), nth_error (cl_saved_vals regs0) j = Some w -> word_mem src0segs memc (sp0 - 32 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok src0segs (Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])) memc (sp0 - 32) (mkChunk off (CVal 8 (SOff (49 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HY j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold cl_saved.
apply Forall_cons; [apply (CK 24 0%nat _ eq_refl); [replace (sp0 - 32 + 24) with (sp0 - 8) by lia; exact W1 | apply u64_range']|].
apply Forall_cons; [apply (CK 16 1%nat _ eq_refl); [replace (sp0 - 32 + 16) with (sp0 - 16) by lia; exact W8 | apply u64_range']|].
apply Forall_cons; [apply (CK 8 2%nat _ eq_refl); [replace (sp0 - 32 + 8) with (sp0 - 24) by lia; exact W9 | apply u64_range']|].
apply Forall_cons; [apply (CK 0 3%nat _ eq_refl); [replace (sp0 - 32 + 0) with (sp0 - 32) by lia; exact W18 | apply u64_range']|].
apply Forall_nil.
+ unfold cl_R1. eapply (region_ok_obj_gen src0segs _ memc 8 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[exact HU8 | lia | lia | exact H15 | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj|].
apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
+ unfold cl_R2, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable src0_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE o HH0 Hgin ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih]. }
apply Forall_nil.
- unfold cl_R1, cl_R2. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU8. repeat split; lia.
- split; [| split; constructor].
cbn [f_atoms atoms_ok cl_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
pose proof (Rg 15%nat _ eq_refl) as R47. pose proof (Rg 16%nat _ eq_refl) as R48.
cbn [nth snd LAY_CGIF Z.of_N] in R47, R48.
rewrite HU2, HU8, (HXn 47%nat 15%nat _ eq_refl eq_refl), (HXn 48%nat 16%nat _ eq_refl eq_refl).
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ src0_A_freeFrame.
{ wr_cl HU2 HU8 Hgin HFPin. }
jreg HS (10%bv:reg) as Hf10. jreg HS (2%bv:reg) as Hf2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hf2.
jreg HS (4%bv:reg) as Hf4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hf4. jreg HS (1%bv:reg) as Hf1x.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 32) by (unfold spZ; rewrite Hf2; apply unsigned_lit_small; lia) end.
set (rest0 := (g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N [o2] ++ rest).
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 (Z_to_bv 64 (src0_A_cgif_close + 0x8c)) mem2 (seg_rom src0segs)) md2 /\
journal src0_msyms MR CLOSE_STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs msx) regs2 /\ Permutation (blocks L2 A2) rest0 /\ res_ok A2 (fr_rb N o1 br) /\
(forall b n i, In (b, n) rest0 -> 0 <= i < n -> mbyte src0segs mem2 (b + i) = mbyte src0segs (ms_mem msx) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 32 - FREEFRAME_STK <= x < sp0 - 32) ->
mbyte src0segs mem2 x = mbyte src0segs (ms_mem msx) x /\ (writable_at src0segs (ms_mem msx) x <-> writable_at src0segs mem2 x)))
end.
{ destruct o1 as [f|].
-
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Ho1).
rewrite frames_blocks_cons_some in HB.
assert (HBf : Permutation (blocks Lc Ac) ((fr_ptr f, FRAME_SIZE) :: (fr_img f, N) :: pals_of (fr_attr f) (fr_lpal f) (3 * fr_nlp f) ++ rest0)).
{ pose proof (perm_front_mid (g, CGIF_SIZE) (pal_blocks s) (frame_blocks N f) (frames_blocks N [o2]) rest) as PM.
eapply Permutation_trans; [exact HB|]. eapply Permutation_trans; [exact PM|]. subst rest0. unfold pals_of, frame_blocks. cbn [app]. apply Permutation_refl. }
assert (Hsepf : forall b n, In (b, n) (frame_blocks N f) -> g + CGIF_SIZE <= b \/ b + n <= g).
{ intros b n Hbn. apply (heap_sep_perm _ _ LAWS Lc Ac _ mdc (g, CGIF_SIZE) (pal_blocks s ++ (frame_blocks N f ++ frames_blocks N [o2]) ++ rest) (b, n) HH0 HB).
apply in_app_iff. right. apply in_app_iff. left. apply in_app_iff. left. exact Hbn. }
pose proof (Hsepf (fr_ptr f) FRAME_SIZE ltac:(left; reflexivity)) as Hsep1.
assert (Hfbl : In (fr_ptr f, FRAME_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HBf | left; reflexivity]).
destruct (blocks_range _ _ LAWS Lc Ac _ mdc (fr_ptr f) FRAME_SIZE HH0 Hfbl) as [Hf0 Hf1].
eapply SR_mono.
{ eapply (jcall src0_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := fp_freeFrame (fr_ptr f) (fr_img f) N (fr_attr f) (fr_lpal f) (3 * fr_nlp f))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => Permutation (blocks L2 A2) rest0 /\ res_ok A2 (rb_free br N));
[ exact HS | reflexivity | exact HJ | exact Hf1x | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp; unfold FREEFRAME_STK; lia | rewrite Hsp; lia | exact Hf4 | ].
+ intros HPRE1. eapply SR_mono.
{ eapply (src0_freeFrame_resc API IMG _ _ _ _ _ (fr_ptr f) (frame_vals f) (fr_img f) N (fr_attr f) (fr_lpal f) (3 * fr_nlp f) rest0 br HPRE1);
[ | | reflexivity | reflexivity | reflexivity | exact HBf | exact HRb ].
- rewrite Hf10, (HXn 33%nat 1%nat _ eq_refl eq_refl). rewrite (@nth_error_nth _ (cg_frames s) 1 _ None Ho1). reflexivity.
- eapply obj_at_transport_range; [exact (Hfr f ltac:(left; reflexivity)) | exact (proj1 LAY_Frame_ok) |].
intros i Hi. cbn [ms_mem mkst] in *. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJc & HP & HB2 & _ & HR2).
exists L2, A2, regs2, mem2, md2. split; [rewrite Hf1x; reflexivity|]. split; [exact HJc|]. split; [exact HP | split; [exact HB2 | exact HR2]].
+ intros a Ha. split; [| apply HFPlow].
all: unfold fp_freeFrame in Ha; apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[apply (HFPin (fr_ptr f) FRAME_SIZE a); [apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | left; reflexivity] | unfold FRAME_SIZE; lia] |];
apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[apply (HFPin (fr_img f) N a); [apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | right; left; reflexivity] | lia] |];
(destruct (Z.land (fr_attr f) 1 =? 0) eqn:Hz; [exfalso; exact (YI04.inFP_nil a Ha)|]);
apply inFP_cons in Ha; (destruct Ha as [Ha|Ha]; [|exfalso; exact (YI04.inFP_nil a Ha)]);
(apply (HFPin (fr_lpal f) (3 * fr_nlp f) a); [apply (frame_blocks_in_cgif0 g s N f); [exact Hfin|]; unfold frame_blocks; rewrite Hz; right; right; left; reflexivity | lia]). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HB2 & HR2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|]. split; [exact HR2|].
pose proof HJc2 as (_ & _ & Hhi2 & Hkeep2 & _). rewrite Hsp in Hhi2. split; [| exact Hhi2].
intros b n i Hbn Hi.
assert (HsepR : forall x, In x (frame_blocks N f) -> fst x + snd x <= b \/ b + n <= fst x).
{ intros x Hx. pose proof (heap_sep_app Lc Ac _ mdc (frame_blocks N f) rest0 x (b, n) HH0 ltac:(eapply Permutation_trans; [exact HBf|]; unfold frame_blocks, pals_of; cbn [app]; apply Permutation_refl) Hx Hbn) as Hs.
cbn [fst snd] in Hs. exact Hs. }
apply (Hkeep2 b n i); [eapply blocks_perm_in; [exact HB | ] | eapply blocks_perm_in; [exact HB2 |] | exact Hi |].
{ subst rest0. destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right]. apply in_app_iff in Hbn. apply in_app_iff.
destruct Hbn as [Hbn|Hbn]; [left; exact Hbn | right]. apply in_app_iff in Hbn. apply in_app_iff.
destruct Hbn as [Hbn|Hbn]; [left; apply in_app_iff; right; exact Hbn | right; exact Hbn]. }
{ destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn]. }
intros Hin. unfold fp_freeFrame in Hin. apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [pose proof (HsepR _ ltac:(left; reflexivity)); cbn [fst snd] in *; lia|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [pose proof (HsepR _ ltac:(right; left; reflexivity)); cbn [fst snd] in *; lia|].
destruct (Z.land (fr_attr f) 1 =? 0) eqn:Hz; [exact (YI04.inFP_nil _ Hin)|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [| exact (YI04.inFP_nil _ Hin)].
pose proof (HsepR (fr_lpal f, 3 * fr_nlp f) ltac:(unfold frame_blocks; rewrite Hz; right; right; left; reflexivity)). cbn [fst snd] in *. lia.
-
rewrite frames_blocks_cons_none in HB.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_mono.
{ eapply (jcall src0_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := @nil (Z * Z))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => Permutation (blocks L2 A2) rest0 /\ res_ok A2 br);
[ exact HS | reflexivity | exact HJ | exact Hf1x | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp; unfold FREEFRAME_STK; lia | rewrite Hsp; lia | exact Hf4
| intros a Ha; exfalso; exact (YI04.inFP_nil a Ha) ].
intros HPRE1. eapply SR_mono.
{ eapply (src0_freeFrame_null API IMG _ _ _ _ _ HPRE1). rewrite Hf10, (HXn 33%nat 1%nat _ eq_refl eq_refl). rewrite (@nth_error_nth _ (cg_frames s) 1 _ None Ho1). reflexivity. }
cbv beta. intros c' (regs2 & mem2 & -> & HJc & HP).
exists Lc, Ac, regs2, mem2, mdc. split; [rewrite Hf1x; reflexivity|]. split; [exact HJc|]. split; [exact HP | split; [exact HB | exact HRb]]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HB2 & HR2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|]. split; [exact HR2|].
pose proof HJc2 as (_ & _ & Hhi2 & Hkeep2 & _). rewrite Hsp in Hhi2. split; [| exact Hhi2].
intros b n i Hbn Hi. apply (Hkeep2 b n i); [eapply blocks_perm_in; [exact HB |] | eapply blocks_perm_in; [exact HB2 |] | exact Hi | intros Hin; exact (YI04.inFP_nil _ Hin)];
(destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn]). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HB2 & HR2 & Hkg & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hkg, Hhi2, HJ2.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
jafter_call_keep HS 53%nat regs2 mem2 HP2 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack src0segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | cbn; intros i Hi; lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | | cbn; lia | cbn; lia].
cbn [r_wlo r_whi cl_R2]. intros i Hi. apply (present_writable src0_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 g CGIF_SIZE i HH2 Hgin2 ltac:(lia))). }
clear HS. rename HS2 into HS.
jrun_to LAWS src0tbl_ok HS HJ2 CL_FREE. { wr_cl HU2 HU8 Hgin2 HFPin. }
cgif_obj_now_at 1%nat 2%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end.
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_free2 L A mem md regs0 rg L2 A2 mm md2 g N s rest FP o0 o1 o2 (fr_rb N o1 br)) end.
+ exact HJ2. + exact Hra0. + exact Htp0. + exact Hal16. + exact Hfs. + exact HFPin. + exact HFPlow. + exact HB2.
+ rewrite cgif_vals_split. exact Hobj2.
+ apply (frames_at_kept memc); [exact (frames_at_tl _ _ _ Hfr)|]. intros f' i Hin' Hi'. cbn [ms_mem mkst] in *.
assert (Hm' : In (fr_ptr f', FRAME_SIZE) (pal_blocks s ++ frames_blocks N [o2] ++ rest)).
{ apply in_app_iff. right. apply in_app_iff. left. apply frames_blocks_ptr_in. exact Hin'. }
pose proof (heap_sep_perm _ _ LAWS L2 A2 mem2 md2 (g, CGIF_SIZE) _ (fr_ptr f', FRAME_SIZE) HH2 HB2 Hm') as Hs'. cbn [fst snd] in Hs'.
destruct (blocks_range _ _ LAWS L2 A2 mem2 md2 (fr_ptr f') FRAME_SIZE HH2 ltac:(eapply blocks_perm_in; [exact HB2 | right; exact Hm'])) as [Hp0' Hp1'].
mb_frame_with HF0 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia).
rewrite (Hkg (fr_ptr f') FRAME_SIZE i ltac:(right; exact Hm') Hi').
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity.
+ unfold cl_saved_ok.
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv - 32 + (32 - dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 24 (SOff 49 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW49, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 16 (SOff 50 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW50, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 8 (SOff 51 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW51, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 0 (SOff 52 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW52, Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
+ reg_nowF HS ltac:(rewrite HU2; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; f_equal; lia).
+ unfold cl_untouched. repeat match goal with |- _ /\ _ => split end;
[ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G19)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27) ].
+ exact HR2.
Qed.
Lemma close_free0 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (rest FP : list (Z * Z)) (o0 o1 o2 : option frame_st) (br : rbound),
let sp0 := spZ regs0 in
journal src0_msyms MR CLOSE_STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp src0_msyms) -> sp0 mod 16 = 0 ->
cg_frames s = [o0; o1; o2] ->
(forall b n a, In (b, n) (cgif_blocks0 g s N) -> b <= a < b + n -> inFP FP a) ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
Permutation (blocks Lc Ac) ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N [o0; o1; o2] ++ rest) ->
obj_at src0segs memc g LAY_CGIF (cgif_vals s) ->
frames_at memc [o0; o1; o2] ->
cl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 32) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 (g + 24) -> getr regs1 18 = Z_to_bv 64 (g + 0) ->
cl_untouched regs0 regs1 -> res_ok Ac br ->
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom src0segs)) mdc) (close_postR regs0 FP L A mem md rest (fr_rb N o2 (fr_rb N o1 (fr_rb N o0 br)))).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s rest FP o0 o1 o2 br sp0 HJ Hra0 Htp0 Hal16 Hfs HFPin HFPlow HB Hobj Hfr HSV G2 G8 G9 G18 HUT HRb.
assert (Ho0 : nth_error (cg_frames s) 0 = Some o0) by (rewrite Hfs; reflexivity).
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HCSv : CLOSE_STK = 9728) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hspm : (sp0 - 32) mod 16 = 0) by (replace (sp0 - 32) with (sp0 + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc g CGIF_SIZE HH0 Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
set (E := Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error (cgif_vals s) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HXn : forall n j v, n = (32 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew E n = Z_to_bv 64 v) by (intros n j v -> Hj; apply HX; exact Hj).
assert (HY : forall j v, nth_error (cl_saved_vals regs0) j = Some v -> ew E (49 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (49 + j)%nat with (32 + (length (cgif_vals s) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HW49 : ew E 49 = getr regs0 1) by (etransitivity; [apply (HY 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW50 : ew E 50 = getr regs0 8) by (etransitivity; [apply (HY 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW51 : ew E 51 = getr regs0 9) by (etransitivity; [apply (HY 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW52 : ew E 52 = getr regs0 18) by (etransitivity; [apply (HY 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
pose proof HSV as (W1 & W8 & W9 & W18).
destruct (obj_cgif_parts memc g s Hobj) as (H15 & Hcur & Rcur & Hih & Rih).
assert (HS : st_ok src0segs E (ss_free 0) (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom src0segs))).
{ unfold ss_free. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |] | intros H0; discriminate H0 |];
cbn [sv_denot]; rewrite (ew_Ereg_nat regs1 _ 8 8%bv eq_refl), G8, unsigned_lit_small by lia; [exact G9 | rewrite G18; f_equal; lia].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : Z), nth_error (cl_saved_vals regs0) j = Some w -> word_mem src0segs memc (sp0 - 32 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok src0segs (Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])) memc (sp0 - 32) (mkChunk off (CVal 8 (SOff (49 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HY j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold cl_saved.
apply Forall_cons; [apply (CK 24 0%nat _ eq_refl); [replace (sp0 - 32 + 24) with (sp0 - 8) by lia; exact W1 | apply u64_range']|].
apply Forall_cons; [apply (CK 16 1%nat _ eq_refl); [replace (sp0 - 32 + 16) with (sp0 - 16) by lia; exact W8 | apply u64_range']|].
apply Forall_cons; [apply (CK 8 2%nat _ eq_refl); [replace (sp0 - 32 + 8) with (sp0 - 24) by lia; exact W9 | apply u64_range']|].
apply Forall_cons; [apply (CK 0 3%nat _ eq_refl); [replace (sp0 - 32 + 0) with (sp0 - 32) by lia; exact W18 | apply u64_range']|].
apply Forall_nil.
+ unfold cl_R1. eapply (region_ok_obj_gen src0segs _ memc 8 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[exact HU8 | lia | lia | exact H15 | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj|].
apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
+ unfold cl_R2, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable src0_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE o HH0 Hgin ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih]. }
apply Forall_nil.
- unfold cl_R1, cl_R2. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU8. repeat split; lia.
- split; [| split; constructor].
cbn [f_atoms atoms_ok cl_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
pose proof (Rg 15%nat _ eq_refl) as R47. pose proof (Rg 16%nat _ eq_refl) as R48.
cbn [nth snd LAY_CGIF Z.of_N] in R47, R48.
rewrite HU2, HU8, (HXn 47%nat 15%nat _ eq_refl eq_refl), (HXn 48%nat 16%nat _ eq_refl eq_refl).
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ src0_A_freeFrame.
{ wr_cl HU2 HU8 Hgin HFPin. }
jreg HS (10%bv:reg) as Hf10. jreg HS (2%bv:reg) as Hf2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hf2.
jreg HS (4%bv:reg) as Hf4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hf4. jreg HS (1%bv:reg) as Hf1x.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 32) by (unfold spZ; rewrite Hf2; apply unsigned_lit_small; lia) end.
set (rest0 := (g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N [o1; o2] ++ rest).
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 (Z_to_bv 64 (src0_A_cgif_close + 0x8c)) mem2 (seg_rom src0segs)) md2 /\
journal src0_msyms MR CLOSE_STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs msx) regs2 /\ Permutation (blocks L2 A2) rest0 /\ res_ok A2 (fr_rb N o0 br) /\
(forall b n i, In (b, n) rest0 -> 0 <= i < n -> mbyte src0segs mem2 (b + i) = mbyte src0segs (ms_mem msx) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 32 - FREEFRAME_STK <= x < sp0 - 32) ->
mbyte src0segs mem2 x = mbyte src0segs (ms_mem msx) x /\ (writable_at src0segs (ms_mem msx) x <-> writable_at src0segs mem2 x)))
end.
{ destruct o0 as [f|].
-
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Ho0).
rewrite frames_blocks_cons_some in HB.
assert (HBf : Permutation (blocks Lc Ac) ((fr_ptr f, FRAME_SIZE) :: (fr_img f, N) :: pals_of (fr_attr f) (fr_lpal f) (3 * fr_nlp f) ++ rest0)).
{ pose proof (perm_front_mid (g, CGIF_SIZE) (pal_blocks s) (frame_blocks N f) (frames_blocks N [o1; o2]) rest) as PM.
eapply Permutation_trans; [exact HB|]. eapply Permutation_trans; [exact PM|]. subst rest0. unfold pals_of, frame_blocks. cbn [app]. apply Permutation_refl. }
assert (Hsepf : forall b n, In (b, n) (frame_blocks N f) -> g + CGIF_SIZE <= b \/ b + n <= g).
{ intros b n Hbn. apply (heap_sep_perm _ _ LAWS Lc Ac _ mdc (g, CGIF_SIZE) (pal_blocks s ++ (frame_blocks N f ++ frames_blocks N [o1; o2]) ++ rest) (b, n) HH0 HB).
apply in_app_iff. right. apply in_app_iff. left. apply in_app_iff. left. exact Hbn. }
pose proof (Hsepf (fr_ptr f) FRAME_SIZE ltac:(left; reflexivity)) as Hsep1.
assert (Hfbl : In (fr_ptr f, FRAME_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HBf | left; reflexivity]).
destruct (blocks_range _ _ LAWS Lc Ac _ mdc (fr_ptr f) FRAME_SIZE HH0 Hfbl) as [Hf0 Hf1].
eapply SR_mono.
{ eapply (jcall src0_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := fp_freeFrame (fr_ptr f) (fr_img f) N (fr_attr f) (fr_lpal f) (3 * fr_nlp f))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => Permutation (blocks L2 A2) rest0 /\ res_ok A2 (rb_free br N));
[ exact HS | reflexivity | exact HJ | exact Hf1x | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp; unfold FREEFRAME_STK; lia | rewrite Hsp; lia | exact Hf4 | ].
+ intros HPRE1. eapply SR_mono.
{ eapply (src0_freeFrame_resc API IMG _ _ _ _ _ (fr_ptr f) (frame_vals f) (fr_img f) N (fr_attr f) (fr_lpal f) (3 * fr_nlp f) rest0 br HPRE1);
[ | | reflexivity | reflexivity | reflexivity | exact HBf | exact HRb ].
- rewrite Hf10, (HXn 32%nat 0%nat _ eq_refl eq_refl). rewrite (@nth_error_nth _ (cg_frames s) 0 _ None Ho0). reflexivity.
- eapply obj_at_transport_range; [exact (Hfr f ltac:(left; reflexivity)) | exact (proj1 LAY_Frame_ok) |].
intros i Hi. cbn [ms_mem mkst] in *. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJc & HP & HB2 & _ & HR2).
exists L2, A2, regs2, mem2, md2. split; [rewrite Hf1x; reflexivity|]. split; [exact HJc|]. split; [exact HP | split; [exact HB2 | exact HR2]].
+ intros a Ha. split; [| apply HFPlow].
all: unfold fp_freeFrame in Ha; apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[apply (HFPin (fr_ptr f) FRAME_SIZE a); [apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | left; reflexivity] | unfold FRAME_SIZE; lia] |];
apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[apply (HFPin (fr_img f) N a); [apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | right; left; reflexivity] | lia] |];
(destruct (Z.land (fr_attr f) 1 =? 0) eqn:Hz; [exfalso; exact (YI04.inFP_nil a Ha)|]);
apply inFP_cons in Ha; (destruct Ha as [Ha|Ha]; [|exfalso; exact (YI04.inFP_nil a Ha)]);
(apply (HFPin (fr_lpal f) (3 * fr_nlp f) a); [apply (frame_blocks_in_cgif0 g s N f); [exact Hfin|]; unfold frame_blocks; rewrite Hz; right; right; left; reflexivity | lia]). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HB2 & HR2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|]. split; [exact HR2|].
pose proof HJc2 as (_ & _ & Hhi2 & Hkeep2 & _). rewrite Hsp in Hhi2. split; [| exact Hhi2].
intros b n i Hbn Hi.
assert (HsepR : forall x, In x (frame_blocks N f) -> fst x + snd x <= b \/ b + n <= fst x).
{ intros x Hx. pose proof (heap_sep_app Lc Ac _ mdc (frame_blocks N f) rest0 x (b, n) HH0 ltac:(eapply Permutation_trans; [exact HBf|]; unfold frame_blocks, pals_of; cbn [app]; apply Permutation_refl) Hx Hbn) as Hs.
cbn [fst snd] in Hs. exact Hs. }
apply (Hkeep2 b n i); [eapply blocks_perm_in; [exact HB | ] | eapply blocks_perm_in; [exact HB2 |] | exact Hi |].
{ subst rest0. destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right]. apply in_app_iff in Hbn. apply in_app_iff.
destruct Hbn as [Hbn|Hbn]; [left; exact Hbn | right]. apply in_app_iff in Hbn. apply in_app_iff.
destruct Hbn as [Hbn|Hbn]; [left; apply in_app_iff; right; exact Hbn | right; exact Hbn]. }
{ destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn]. }
intros Hin. unfold fp_freeFrame in Hin. apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [pose proof (HsepR _ ltac:(left; reflexivity)); cbn [fst snd] in *; lia|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [pose proof (HsepR _ ltac:(right; left; reflexivity)); cbn [fst snd] in *; lia|].
destruct (Z.land (fr_attr f) 1 =? 0) eqn:Hz; [exact (YI04.inFP_nil _ Hin)|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [| exact (YI04.inFP_nil _ Hin)].
pose proof (HsepR (fr_lpal f, 3 * fr_nlp f) ltac:(unfold frame_blocks; rewrite Hz; right; right; left; reflexivity)). cbn [fst snd] in *. lia.
-
rewrite frames_blocks_cons_none in HB.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_mono.
{ eapply (jcall src0_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := @nil (Z * Z))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => Permutation (blocks L2 A2) rest0 /\ res_ok A2 br);
[ exact HS | reflexivity | exact HJ | exact Hf1x | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp; unfold FREEFRAME_STK; lia | rewrite Hsp; lia | exact Hf4
| intros a Ha; exfalso; exact (YI04.inFP_nil a Ha) ].
intros HPRE1. eapply SR_mono.
{ eapply (src0_freeFrame_null API IMG _ _ _ _ _ HPRE1). rewrite Hf10, (HXn 32%nat 0%nat _ eq_refl eq_refl). rewrite (@nth_error_nth _ (cg_frames s) 0 _ None Ho0). reflexivity. }
cbv beta. intros c' (regs2 & mem2 & -> & HJc & HP).
exists Lc, Ac, regs2, mem2, mdc. split; [rewrite Hf1x; reflexivity|]. split; [exact HJc|]. split; [exact HP | split; [exact HB | exact HRb]]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HB2 & HR2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|]. split; [exact HR2|].
pose proof HJc2 as (_ & _ & Hhi2 & Hkeep2 & _). rewrite Hsp in Hhi2. split; [| exact Hhi2].
intros b n i Hbn Hi. apply (Hkeep2 b n i); [eapply blocks_perm_in; [exact HB |] | eapply blocks_perm_in; [exact HB2 |] | exact Hi | intros Hin; exact (YI04.inFP_nil _ Hin)];
(destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn]). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HB2 & HR2 & Hkg & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hkg, Hhi2, HJ2.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
jafter_call_keep HS 53%nat regs2 mem2 HP2 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack src0segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | cbn; intros i Hi; lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | | cbn; lia | cbn; lia].
cbn [r_wlo r_whi cl_R2]. intros i Hi. apply (present_writable src0_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 g CGIF_SIZE i HH2 Hgin2 ltac:(lia))). }
clear HS. rename HS2 into HS.
jrun_to LAWS src0tbl_ok HS HJ2 CL_FREE. { wr_cl HU2 HU8 Hgin2 HFPin. }
cgif_obj_now_at 1%nat 2%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end.
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_free1 L A mem md regs0 rg L2 A2 mm md2 g N s rest FP o0 o1 o2 (fr_rb N o0 br)) end.
+ exact HJ2. + exact Hra0. + exact Htp0. + exact Hal16. + exact Hfs. + exact HFPin. + exact HFPlow. + exact HB2.
+ rewrite cgif_vals_split. exact Hobj2.
+ apply (frames_at_kept memc); [exact (frames_at_tl _ _ _ Hfr)|]. intros f' i Hin' Hi'. cbn [ms_mem mkst] in *.
assert (Hm' : In (fr_ptr f', FRAME_SIZE) (pal_blocks s ++ frames_blocks N [o1; o2] ++ rest)).
{ apply in_app_iff. right. apply in_app_iff. left. apply frames_blocks_ptr_in. exact Hin'. }
pose proof (heap_sep_perm _ _ LAWS L2 A2 mem2 md2 (g, CGIF_SIZE) _ (fr_ptr f', FRAME_SIZE) HH2 HB2 Hm') as Hs'. cbn [fst snd] in Hs'.
destruct (blocks_range _ _ LAWS L2 A2 mem2 md2 (fr_ptr f') FRAME_SIZE HH2 ltac:(eapply blocks_perm_in; [exact HB2 | right; exact Hm'])) as [Hp0' Hp1'].
mb_frame_with HF0 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia).
rewrite (Hkg (fr_ptr f') FRAME_SIZE i ltac:(right; exact Hm') Hi').
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity.
+ unfold cl_saved_ok.
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv - 32 + (32 - dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 24 (SOff 49 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW49, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 16 (SOff 50 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW50, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 8 (SOff 51 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW51, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 0 (SOff 52 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW52, Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
+ reg_nowF HS ltac:(rewrite HU2; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; f_equal; lia).
+ unfold cl_untouched. repeat match goal with |- _ /\ _ => split end;
[ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G19)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27) ].
+ exact HR2.
Qed.
Definition close_postX (regs0 : bvmap 5 word) (FP : list (Z * Z)) L A mem md (rest : list (Z * Z)) (S : list Z) (bF : rbound) (c' : config) : Prop :=
exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom src0segs)) md' /\
journal src0_msyms MR CLOSE_STK (spZ regs0) FP L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\ st_init_done A' = true /\
sink_none src0_msyms mem' md' /\
Permutation (blocks L' A') rest /\
Fs.fs_lookup (m_fs md') sink_path = Some (bytes S) /\
res_ok A' bF.
Definition frs_rb (N : Z) (os : list (option frame_st)) (b : rbound) : rbound := fold_left (fun b' o => fr_rb N o b') os b.
Definition ss_fin : sstate :=
mkSS CL_FILE sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 32 0 32 cl_saved ; cl_R1 ; cl_R2 ]
None (mkFacts (cl_facts ++ [(46%nat, mkAF 4096 (CEIL_MAX - FILE_BLOCK) 4)]) [] []).
Lemma close_fin :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (rest FP : list (Z * Z)) (S : list Z) (br : rbound),
let sp0 := spZ regs0 in
let f := cg_file s in
journal src0_msyms MR CLOSE_STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp src0_msyms) -> sp0 mod 16 = 0 -> sp0 <= 2 ^ 47 ->
(forall b n a, In (b, n) (cgif_blocks0 g s N) -> b <= a < b + n -> inFP FP a) ->
(forall a, inFP (sink_fp f) a -> inFP FP a) ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
4096 <= cg_raw s -> length (cg_frames s) = 3%nat ->
Permutation (blocks Lc Ac) ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N (cg_frames s) ++ (f, FILE_BLOCK) :: rest) ->
obj_at src0segs memc g LAY_CGIF (cgif_vals s) ->
frames_at memc (cg_frames s) ->
sink_at src0_msyms memc mdc f S ->
cl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 32) -> getr regs1 8 = Z_to_bv 64 g ->
cl_untouched regs0 regs1 -> res_ok Ac br ->
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 CL_FILE) memc (seg_rom src0segs)) mdc)
(close_postX regs0 FP L A mem md rest S (frs_rb N (cg_frames s) br)).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s rest FP S br sp0 f HJ Hra0 Htp0 Hal16 Hsp47 HFPin HFPs HFPlow Hraw0 Hlen HB Hobj Hfrs HSK HSV G2 G8 HUT HRb.
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HCSv : CLOSE_STK = 9728) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity. assert (HFBv : FILE_BLOCK = 1264) by reflexivity. assert (HFCv : FCLOSE_STK = 8704) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hspm : (sp0 - 32) mod 16 = 0) by (replace (sp0 - 32) with (sp0 + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hfin : In (f, FILE_BLOCK) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc g CGIF_SIZE HH0 Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc f FILE_BLOCK HH0 Hfin ltac:(lia)) as (Hf0 & Hf1 & Hf16).
pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (g, CGIF_SIZE) _ (f, FILE_BLOCK) HH0 HB ltac:(apply in_app_iff; right; apply in_app_iff; right; left; reflexivity)) as Hsepf. cbn [fst snd] in Hsepf.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
set (E := Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error (cgif_vals s) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HXn : forall n j v, n = (32 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew E n = Z_to_bv 64 v) by (intros n j v -> Hj; apply HX; exact Hj).
assert (HY : forall j v, nth_error (cl_saved_vals regs0) j = Some v -> ew E (49 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (49 + j)%nat with (32 + (length (cgif_vals s) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HW49 : ew E 49 = getr regs0 1) by (etransitivity; [apply (HY 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW50 : ew E 50 = getr regs0 8) by (etransitivity; [apply (HY 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW51 : ew E 51 = getr regs0 9) by (etransitivity; [apply (HY 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW52 : ew E 52 = getr regs0 18) by (etransitivity; [apply (HY 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
pose proof HSV as (W1 & W8 & W9 & W18).
destruct (obj_cgif_parts memc g s Hobj) as (H15 & Hcur & Rcur & Hih & Rih).
assert (HS : st_ok src0segs E ss_fin (mkst regs1 (Z_to_bv 64 CL_FILE) memc (seg_rom src0segs))).
{ unfold ss_fin. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : Z), nth_error (cl_saved_vals regs0) j = Some w -> word_mem src0segs memc (sp0 - 32 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok src0segs (Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])) memc (sp0 - 32) (mkChunk off (CVal 8 (SOff (49 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HY j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold cl_saved.
apply Forall_cons; [apply (CK 24 0%nat _ eq_refl); [replace (sp0 - 32 + 24) with (sp0 - 8) by lia; exact W1 | apply u64_range']|].
apply Forall_cons; [apply (CK 16 1%nat _ eq_refl); [replace (sp0 - 32 + 16) with (sp0 - 16) by lia; exact W8 | apply u64_range']|].
apply Forall_cons; [apply (CK 8 2%nat _ eq_refl); [replace (sp0 - 32 + 8) with (sp0 - 24) by lia; exact W9 | apply u64_range']|].
apply Forall_cons; [apply (CK 0 3%nat _ eq_refl); [replace (sp0 - 32 + 0) with (sp0 - 32) by lia; exact W18 | apply u64_range']|].
apply Forall_nil.
+ unfold cl_R1. eapply (region_ok_obj_gen src0segs _ memc 8 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[exact HU8 | lia | lia | exact H15 | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj|].
apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
+ unfold cl_R2, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable src0_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE o HH0 Hgin ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih]. }
apply Forall_nil.
- unfold cl_R1, cl_R2. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU8. repeat split; lia.
- cbn [f_atoms atoms_ok cl_facts app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
pose proof (Rg 15%nat _ eq_refl) as R47. pose proof (Rg 16%nat _ eq_refl) as R48.
cbn [nth snd LAY_CGIF Z.of_N] in R47, R48.
rewrite HU2, HU8, (HXn 47%nat 15%nat _ eq_refl eq_refl), (HXn 48%nat 16%nat _ eq_refl eq_refl), (HXn 46%nat 14%nat _ eq_refl eq_refl).
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 CL_FILE) memc (seg_rom src0segs))) in HJ.
assert (Hfnz : f <> 0) by exact (sink_at_nonnull src0_msyms _ _ _ _ HSK).
assert (Henvblk : forall L1 A1 m1 md1 bb n a, heap_ok MR L1 A1 m1 md1 -> In (bb, n) (blocks L1 A1) -> env_addr a -> ~ (bb <= a < bb + n)).
{ intros L1 A1 m1 md1 bb n a HHx Hin1 Hea Hr. apply blocks_In in Hin1 as (q & Hq & Hqin).
destruct (skl_env src0_msyms a Hea) as (Himg1 & _). assert (Hrg : 0 <= a - bb < n) by lia.
apply (il_blocks IMG L1 A1 m1 md1 q n (a - bb) (proj1 HHx) Hqin Hrg). rewrite Hq. replace (bb + (a - bb)) with a by lia. exact Himg1. }
set (restF := (pal_blocks s ++ frames_blocks N (cg_frames s)) ++ rest).
assert (HBf : Permutation (blocks Lc Ac) ((f, FILE_BLOCK) :: (g, CGIF_SIZE) :: restF)).
{ eapply Permutation_trans; [exact HB|]. eapply Permutation_trans; [| apply perm_swap]. apply perm_skip. subst restF. apply Permutation_sym. rewrite (app_assoc (pal_blocks s)). apply Permutation_middle. }
assert (HinF : forall x, In x restF -> In x (blocks Lc Ac)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HBf|]. right. right. exact Hx. }
jrun_to LAWS src0tbl_ok HS HJ src0_A_fclose. { wr_cl HU2 HU8 Hgin HFPin. }
jreg HS (10%bv:reg) as Hm10. jreg HS (2%bv:reg) as Hm2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hm2.
jreg HS (4%bv:reg) as Hm4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hm4. jreg HS (1%bv:reg) as Hm1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 32) by (unfold spZ; rewrite Hm2; apply unsigned_lit_small; lia) end.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (HSKc : sink_at src0_msyms (ms_mem msx) mdc f S);
[ apply (sink_at_frame src0_msyms memc _ mdc f S); [|exact HSK];
intros a Ha; assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + CGIF_SIZE)) by (destruct Ha as [Ha|Ha]; [lia | pose proof (src0_env_addr_range a Ha); pose proof (Henvblk Lc Ac memc mdc g CGIF_SIZE a HH0 Hgin Ha); lia]);
cbn [ms_mem mkst] in *; mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia); reflexivity |] end.
assert (Hid : st_init_done Ac = true).
{ destruct (proj1 (blocks_In _ _ _ _) Hgin) as (p & _ & Hp). exact (init_done_of_block _ _ (proj1 (proj2 HH0)) Hp). }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L3 A3 regs3 mem3 md3,
c' = mkCfg (mkst regs3 (Z_to_bv 64 (src0_A_cgif_close + 0x70)) mem3 (seg_rom src0segs)) md3 /\
journal src0_msyms MR CLOSE_STK sp0 FP L A mem md L3 A3 mem3 md3 /\
regs_preserved (ms_regs msx) regs3 /\ getr regs3 10 = Z_to_bv 64 0 /\
Permutation (blocks L3 A3) ((g, CGIF_SIZE) :: restF) /\
sink_none src0_msyms mem3 md3 /\ Fs.fs_lookup (m_fs md3) sink_path = Some (bytes S) /\ res_ok A3 br /\
(forall b n i, In (b, n) ((g, CGIF_SIZE) :: restF) -> 0 <= i < n -> mbyte src0segs mem3 (b + i) = mbyte src0segs (ms_mem msx) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 32 - FCLOSE_STK <= x < sp0 - 32) ->
mbyte src0segs mem3 x = mbyte src0segs (ms_mem msx) x /\ (writable_at src0segs (ms_mem msx) x <-> writable_at src0segs mem3 x)))
end.
{ eapply SR_mono.
{ eapply (jcall src0_msyms MR) with (STK1 := FCLOSE_STK) (FP1 := sink_fp f)
(K := fun L3 A3 (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) =>
getr regs3 10 = Z_to_bv 64 0 /\ Permutation (blocks L3 A3) ((g, CGIF_SIZE) :: restF) /\
sink_none src0_msyms mem3 md3 /\ Fs.fs_lookup (m_fs md3) sink_path = Some (bytes S) /\ res_ok A3 br);
[ exact HS | reflexivity | exact HJ | exact Hm1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FCLOSE_STK; lia | rewrite Hsp; unfold FCLOSE_STK; lia | rewrite Hsp; lia | exact Hm4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (FCLOSE _ _ _ _ _ f S ((g, CGIF_SIZE) :: restF) br HPRE1);
[ exact Hid | rewrite Hsp; lia | | exact HBf | exact HSKc | exact HRb ].
rewrite Hm10, (HXn 46%nat 14%nat _ eq_refl eq_refl). reflexivity. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJc & HP & Hr10 & HB3 & HSN & Hfs3 & HR3).
exists L3, A3, regs3, mem3, md3. split; [rewrite Hm1; reflexivity|]. split; [exact HJc|]. split; [exact HP|].
split; [exact Hr10|]. split; [exact HB3|]. split; [exact HSN|]. split; [exact Hfs3 | exact HR3].
- intros a Ha. split; [apply HFPs; exact Ha | apply HFPlow; apply HFPs; exact Ha]. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & (Hr10 & HB3 & HSN & Hfs3 & HR3)).
exists L3, A3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact HP3|]. split; [exact Hr10|].
split; [exact HB3|]. split; [exact HSN|]. split; [exact Hfs3|]. split; [exact HR3|].
pose proof HJc3 as (_ & _ & Hhi3 & Hkeep3 & _). rewrite Hsp in Hhi3. split; [| exact Hhi3].
intros b n i Hbn Hi.
assert (Hbn' : In (b, n) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HBf | right; exact Hbn]).
destruct (blocks_range _ _ LAWS Lc Ac _ mdc b n HH0 Hbn') as [Hb0 Hb1].
pose proof (heap_sep_perm _ _ LAWS Lc Ac _ mdc (f, FILE_BLOCK) _ (b, n) HH0 HBf Hbn) as Hs. cbn [fst snd] in Hs.
apply (Hkeep3 b n i); [exact Hbn' | eapply blocks_perm_in; [exact HB3 | destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn]] | exact Hi |].
intros Hin. unfold sink_fp in Hin. apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [unfold sink_token in Hin; cbn [fst snd] in Hin; lia|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [cbn [fst snd] in Hin; lia | exact (YI04.inFP_nil _ Hin)]. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hr10c & HB3 & HSN3 & Hfs3 & HR3 & Hkg & Hhi3). clear HJ.
cbn [ms_regs ms_mem mkst] in HP3, Hkg, Hhi3, HJ3.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
assert (Hgin3 : In (g, CGIF_SIZE) (blocks L3 A3)) by (eapply blocks_perm_in; [exact HB3 | left; reflexivity]).
jafter_call_keep HS 53%nat regs3 mem3 HP3 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack src0segs _ _ _ 2); [exact HU2 | exact Hhi3 | lia | lia | unfold FCLOSE_STK; lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | cbn; intros i Hi; lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | | cbn; lia | cbn; lia].
cbn [r_wlo r_whi cl_R2]. intros i Hi. apply (present_writable src0_msyms). apply (proj1 (heap_blocks _ _ LAWS L3 A3 mem3 md3 g CGIF_SIZE i HH3 Hgin3 ltac:(lia))). }
clear HS. rename HS2 into HS.
pin_reg' HS (10%bv:reg) 0 Hr10c.
jrun_to LAWS src0tbl_ok HS HJ3 CL_FREE. { wr_cl HU2 HU8 Hgin3 HFPin. }
cgif_obj_now_at 1%nat 2%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end. rewrite <- cgif_vals_split in Hobj2.
destruct (cg_frames s) as [|o0 [|o1 [|o2 [|]]]] eqn:Hfs; try (cbn in Hlen; discriminate Hlen).
assert (Hfm : forall f', In (Some f') [o0; o1; o2] -> In (fr_ptr f', FRAME_SIZE) restF /\ 4096 <= fr_ptr f' /\ fr_ptr f' + FRAME_SIZE <= alloc_ceiling /\ (g + CGIF_SIZE <= fr_ptr f' \/ fr_ptr f' + FRAME_SIZE <= g)).
{ intros f' Hin'.
assert (Hm' : In (fr_ptr f', FRAME_SIZE) restF) by (subst restF; apply in_app_iff; left; apply in_app_iff; right; apply frames_blocks_ptr_in; exact Hin').
split; [exact Hm'|].
destruct (blocks_range _ _ LAWS L3 A3 mem3 md3 (fr_ptr f') FRAME_SIZE HH3 ltac:(eapply blocks_perm_in; [exact HB3 | right; exact Hm'])) as [Hp0' Hp1'].
pose proof (heap_sep_perm _ _ LAWS L3 A3 mem3 md3 (g, CGIF_SIZE) _ (fr_ptr f', FRAME_SIZE) HH3 HB3 Hm') as Hs'. cbn [fst snd] in Hs'. lia. }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
set (FP' := blocks_fp (cgif_blocks0 g s N)).
assert (HFPin' : forall b n a, In (b, n) (cgif_blocks0 g s N) -> b <= a < b + n -> inFP FP' a) by (intros b n a Hbn Ha; subst FP'; apply (cgif_fp_in g s N b n a Hbn Ha)).
assert (HFPsub : forall a, inFP FP' a -> inFP FP a /\ a < alloc_ceiling).
{ intros a Ha. subst FP'. apply (proj1 (inFP_blocks_fp _ _)) in Ha as (bb & nn & Hbn & Hab). split; [exact (HFPin bb nn a Hbn Hab) | exact (HFPlow a (HFPin bb nn a Hbn Hab))]. }
assert (Hnot : ~ sink_open_fp FP').
{ unfold sink_open_fp, in_fp. intros (r & Hr & Hrz). subst FP'. unfold blocks_fp in Hr. apply in_map_iff in Hr as ([bb nn] & <- & Hbn). cbn [fst snd] in Hrz.
unfold cgif_blocks0 in Hbn. rewrite Hfs in Hbn. destruct Hbn as [Hbn|[Hbn|Hbn]]; [injection Hbn as <- <-; lia | injection Hbn as <- <-; lia |].
assert (Hl : In (bb, nn) (blocks L3 A3)) by (eapply blocks_perm_in; [exact HB3 | right; subst restF; apply in_app_iff; left; exact Hbn]).
destruct (blocks_range _ _ LAWS L3 A3 mem3 md3 bb nn HH3 Hl) as [R0 R1]. lia. }
pose proof (journal_restart src0_msyms MR _ _ _ _ _ _ _ _ _ _ _ FP' HJ3) as HJl.
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply SR_mono; [eapply (close_free0 L3 A3 mm md3 regs0 rg L3 A3 mm md3 g N s rest FP' o0 o1 o2 br) |] end.
+ exact HJl. + exact Hra0. + exact Htp0. + exact Hal16. + exact Hfs. + exact HFPin'. + intros a Ha; exact (proj2 (HFPsub a Ha)).
+ eapply Permutation_trans; [exact HB3|]. subst restF. rewrite <- app_assoc. apply Permutation_refl.
+ exact Hobj2.
+ intros f' Hin'. destruct (Hfm f' Hin') as (Hm' & Hp0' & Hp1' & Hs').
eapply obj_at_transport_range; [apply Hfrs; rewrite ?Hfs; exact Hin' | exact (proj1 LAY_Frame_ok) |].
intros i Hi. cbn [ms_mem mkst] in *.
mb_frame_with HF0 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia).
rewrite (Hkg (fr_ptr f') FRAME_SIZE i ltac:(right; exact Hm') Hi).
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity.
+ unfold cl_saved_ok;
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv - 32 + (32 - dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 24 (SOff 49 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW49, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 16 (SOff 50 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW50, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 8 (SOff 51 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW51, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 0 (SOff 52 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW52, Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
+ reg_nowF HS ltac:(rewrite HU2; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; f_equal; lia).
+ unfold cl_untouched; repeat match goal with |- _ /\ _ => split end;
[ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G19)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27) ].
+ exact HR3.
+
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HB4 & Hid4 & HR4).
exists L4, A4, regs4, mem4, md4. split; [reflexivity|].
split; [eapply (journal_sub src0_msyms MR); [exact HJ3 | exact HJ4 | lia | lia | exact HFPsub]|].
split; [exact HP4|]. split; [exact Hid4|].
split.
{ eapply (sink_none_kept src0_msyms MR); [exact HJ4 | exact Hnot |].
apply (sink_none_frame src0_msyms mem3); [| exact HSN3]. intros a Ha. pose proof (src0_env_addr_range a Ha). pose proof (Henvblk L3 A3 mem3 md3 g CGIF_SIZE a HH3 Hgin3 Ha).
cbn [ms_mem mkst] in *. mb_frame_with HF0 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
split; [exact HB4|].
split; [| exact HR4].
pose proof HJ4 as (_ & Hos4 & _). destruct (os_step_shielded FP' md3 md4 Hos4 Hnot) as (_ & Efs & _). rewrite Efs. exact Hfs3.
Qed.
Definition ss_clean : sstate :=
mkSS CL_CLEAN sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 32 0 32 cl_saved ; cl_R1 ; cl_R2 ]
None (mkFacts (cl_facts ++ [(45%nat, mkAF 4096 (CEIL_MAX - 48) 4)]) [] []).
Lemma close_clean :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (rest FP : list (Z * Z)) (S : list Z) (br : rbound),
let sp0 := spZ regs0 in
let f := cg_file s in
journal src0_msyms MR CLOSE_STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp src0_msyms) -> sp0 mod 16 = 0 -> sp0 <= 2 ^ 47 ->
(forall b n a, In (b, n) (cgif_blocks0 g s N) -> b <= a < b + n -> inFP FP a) ->
(forall a, inFP (sink_fp f) a -> inFP FP a) ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
cgif_at memc g s -> cgif_wf s N ->
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ (f, FILE_BLOCK) :: rest) ->
sink_at src0_msyms memc mdc f S -> Z.of_nat (length S) + 1 <= SINK_MAX ->
cl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 32) -> getr regs1 8 = Z_to_bv 64 g ->
cl_untouched regs0 regs1 -> res_ok Ac br ->
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 CL_CLEAN) memc (seg_rom src0segs)) mdc)
(close_postX regs0 FP L A mem md rest (S ++ sink_trailer_Z) (frs_rb N (cg_frames s) br)).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s rest FP S br sp0 f HJ Hra0 Htp0 Hal16 Hsp47 HFPin HFPs HFPlow Hat Hwf HB HSK HSlen HSV G2 G8 HUT HRb.
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof Hat as (Hobj & Hraw & Hfrs). pose proof Hwf as (Hlen & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HCSv : CLOSE_STK = 9728) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hspm : (sp0 - 32) mod 16 = 0) by (replace (sp0 - 32) with (sp0 + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hrin : In (cg_raw s, RAW_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc g CGIF_SIZE HH0 Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc (cg_raw s) RAW_SIZE HH0 Hrin ltac:(lia)) as (Hr0 & Hr1 & Hr16).
pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (g, CGIF_SIZE) _ (cg_raw s, RAW_SIZE) HH0 HB ltac:(left; reflexivity)) as Hsepr. cbn [fst snd] in Hsepr.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
set (E := Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error (cgif_vals s) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HXn : forall n j v, n = (32 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew E n = Z_to_bv 64 v) by (intros n j v -> Hj; apply HX; exact Hj).
assert (HY : forall j v, nth_error (cl_saved_vals regs0) j = Some v -> ew E (49 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (49 + j)%nat with (32 + (length (cgif_vals s) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HW49 : ew E 49 = getr regs0 1) by (etransitivity; [apply (HY 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW50 : ew E 50 = getr regs0 8) by (etransitivity; [apply (HY 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW51 : ew E 51 = getr regs0 9) by (etransitivity; [apply (HY 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW52 : ew E 52 = getr regs0 18) by (etransitivity; [apply (HY 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
pose proof HSV as (W1 & W8 & W9 & W18).
destruct (obj_cgif_parts memc g s Hobj) as (H15 & Hcur & Rcur & Hih & Rih).
assert (HS : st_ok src0segs E ss_clean (mkst regs1 (Z_to_bv 64 CL_CLEAN) memc (seg_rom src0segs))).
{ unfold ss_clean. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : Z), nth_error (cl_saved_vals regs0) j = Some w -> word_mem src0segs memc (sp0 - 32 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok src0segs (Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])) memc (sp0 - 32) (mkChunk off (CVal 8 (SOff (49 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HY j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold cl_saved.
apply Forall_cons; [apply (CK 24 0%nat _ eq_refl); [replace (sp0 - 32 + 24) with (sp0 - 8) by lia; exact W1 | apply u64_range']|].
apply Forall_cons; [apply (CK 16 1%nat _ eq_refl); [replace (sp0 - 32 + 16) with (sp0 - 16) by lia; exact W8 | apply u64_range']|].
apply Forall_cons; [apply (CK 8 2%nat _ eq_refl); [replace (sp0 - 32 + 8) with (sp0 - 24) by lia; exact W9 | apply u64_range']|].
apply Forall_cons; [apply (CK 0 3%nat _ eq_refl); [replace (sp0 - 32 + 0) with (sp0 - 32) by lia; exact W18 | apply u64_range']|].
apply Forall_nil.
+ unfold cl_R1. eapply (region_ok_obj_gen src0segs _ memc 8 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[exact HU8 | lia | lia | exact H15 | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj|].
apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
+ unfold cl_R2, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable src0_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE o HH0 Hgin ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih]. }
apply Forall_nil.
- unfold cl_R1, cl_R2. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU8. repeat split; lia.
- cbn [f_atoms atoms_ok cl_facts app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
pose proof (Rg 15%nat _ eq_refl) as R47. pose proof (Rg 16%nat _ eq_refl) as R48.
cbn [nth snd LAY_CGIF Z.of_N] in R47, R48.
rewrite HU2, HU8, (HXn 47%nat 15%nat _ eq_refl eq_refl), (HXn 48%nat 16%nat _ eq_refl eq_refl), (HXn 45%nat 13%nat _ eq_refl eq_refl).
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 CL_CLEAN) memc (seg_rom src0segs))) in HJ.
assert (Henvblk : forall L1 A1 m1 md1 bb n a, heap_ok MR L1 A1 m1 md1 -> In (bb, n) (blocks L1 A1) -> env_addr a -> ~ (bb <= a < bb + n)).
{ intros L1 A1 m1 md1 bb n a HHx Hin1 Hea Hr. apply blocks_In in Hin1 as (q & Hq & Hqin).
destruct (skl_env src0_msyms a Hea) as (Himg1 & _). assert (Hrg : 0 <= a - bb < n) by lia.
apply (il_blocks IMG L1 A1 m1 md1 q n (a - bb) (proj1 HHx) Hqin Hrg). rewrite Hq. replace (bb + (a - bb)) with a by lia. exact Himg1. }
assert (Hfin : In (f, FILE_BLOCK) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | right; right; apply in_app_iff; right; left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc f FILE_BLOCK HH0 Hfin ltac:(unfold FILE_BLOCK; lia)) as (Hf0 & Hf1 & Hf16).
pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (g, CGIF_SIZE) _ (f, FILE_BLOCK) HH0 HB ltac:(right; apply in_app_iff; right; left; reflexivity)) as Hsepf0. cbn [fst snd] in Hsepf0.
set (ownB := pal_blocks s ++ frames_blocks N (cg_frames s)).
set (restR := ownB ++ (f, FILE_BLOCK) :: rest).
assert (HBr : Permutation (blocks Lc Ac) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: restR)).
{ eapply Permutation_trans; [exact HB|]. apply perm_swap. }
assert (HBfl : Permutation (blocks Lc Ac) ((f, FILE_BLOCK) :: (cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: ownB ++ rest)).
{ eapply Permutation_trans; [exact HBr|]. subst restR. apply Permutation_sym.
change ((f, FILE_BLOCK) :: (cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: ownB ++ rest) with ((f, FILE_BLOCK) :: ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: ownB) ++ rest).
apply (Permutation_middle ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: ownB) rest (f, FILE_BLOCK)). }
jrun_to LAWS src0tbl_ok HS HJ src0_A_cgif_raw_close. { wr_cl HU2 HU8 Hgin HFPin. }
jreg HS (10%bv:reg) as Hm10. jreg HS (2%bv:reg) as Hm2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hm2.
jreg HS (4%bv:reg) as Hm4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hm4. jreg HS (1%bv:reg) as Hm1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 32) by (unfold spZ; rewrite Hm2; apply unsigned_lit_small; lia) end.
cgif_obj_now_at 1%nat 2%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj1 end. rewrite <- cgif_vals_split in Hobj1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (HSKc : sink_at src0_msyms (ms_mem msx) mdc f S);
[ apply (sink_at_frame src0_msyms memc _ mdc f S); [|exact HSK];
intros a Ha; assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + CGIF_SIZE)) by (destruct Ha as [Ha|Ha]; [lia | pose proof (src0_env_addr_range a Ha); pose proof (Henvblk Lc Ac memc mdc g CGIF_SIZE a HH0 Hgin Ha); lia]);
cbn [ms_mem mkst] in *; mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia); reflexivity |] end.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 (Z_to_bv 64 (src0_A_cgif_close + 0x5c)) mem2 (seg_rom src0segs)) md2 /\
journal src0_msyms MR CLOSE_STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs msx) regs2 /\ Permutation (blocks L2 A2) ((g, CGIF_SIZE) :: restR) /\
sink_at src0_msyms mem2 md2 f (S ++ sink_trailer_Z) /\ res_ok A2 br /\
(forall b n i, In (b, n) ((g, CGIF_SIZE) :: ownB) -> 0 <= i < n -> mbyte src0segs mem2 (b + i) = mbyte src0segs (ms_mem msx) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 32 - RAWCLOSE_STK <= x < sp0 - 32) ->
mbyte src0segs mem2 x = mbyte src0segs (ms_mem msx) x /\ (writable_at src0segs (ms_mem msx) x <-> writable_at src0segs mem2 x)))
end.
{ eapply SR_mono.
{ eapply (jcall src0_msyms MR) with (STK1 := RAWCLOSE_STK) (FP1 := (cg_raw s, cg_raw s + RAW_SIZE) :: sink_fp f)
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) =>
Permutation (blocks L2 A2) ((g, CGIF_SIZE) :: restR) /\ sink_at src0_msyms mem2 md2 f (S ++ sink_trailer_Z) /\ res_ok A2 br);
[ exact HS | reflexivity | exact HJ | exact Hm1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold RAWCLOSE_STK; lia | rewrite Hsp; unfold RAWCLOSE_STK; lia | rewrite Hsp; lia | exact Hm4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (src0_cgif_raw_close_resc API IMG FWRITE _ _ _ _ _ (cg_raw s) (raw_vals g s) g (cgif_vals s) restR f S br HPRE1);
[ | | reflexivity | reflexivity | exact Hobj1 | reflexivity | reflexivity | exact HBr
| subst restR; apply in_app_iff; right; left; reflexivity | exact HSKc | exact HSlen | rewrite Hsp; lia | exact HRb ].
+ rewrite Hm10, (HXn 45%nat 13%nat _ eq_refl eq_refl). reflexivity.
+ eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |].
intros i Hi. cbn [ms_mem mkst] in *. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJc & HP & HB2 & HSK2 & _ & HR2).
exists L2, A2, regs2, mem2, md2. split; [rewrite Hm1; reflexivity|]. split; [exact HJc|]. split; [exact HP | split; [exact HB2 | split; [exact HSK2 | exact HR2]]].
- intros a Ha. apply inFP_cons in Ha. destruct Ha as [Ha|Ha].
+ split; [| apply HFPlow]; (apply (HFPin (cg_raw s) RAW_SIZE a); [right; left; reflexivity | lia]).
+ split; [apply HFPs; exact Ha | apply HFPlow; apply HFPs; exact Ha]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (HB2 & HSK2 & HR2)).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|]. split; [exact HSK2|]. split; [exact HR2|].
pose proof HJc2 as (_ & _ & Hhi2 & Hkeep2 & _). rewrite Hsp in Hhi2. split; [| exact Hhi2].
intros b n i Hbn Hi.
assert (HbnR : In (b, n) ((g, CGIF_SIZE) :: restR)) by (destruct Hbn as [Hbn|Hbn]; [left; first [exact Hbn | symmetry; exact Hbn] | right; subst restR; apply in_app_iff; left; exact Hbn]).
assert (Hbl : In (b, n) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HBr | right; destruct HbnR as [E1|E1]; [left; first [exact E1 | symmetry; exact E1] | right; exact E1]]).
destruct (blocks_range _ _ LAWS Lc Ac _ mdc b n HH0 Hbl) as [Hb0 Hb1].
pose proof (heap_sep_perm _ _ LAWS Lc Ac _ mdc (cg_raw s, RAW_SIZE) _ (b, n) HH0 HBr HbnR) as Hs. cbn [fst snd] in Hs.
pose proof (heap_sep_perm _ _ LAWS Lc Ac _ mdc (f, FILE_BLOCK) _ (b, n) HH0 HBfl ltac:(destruct Hbn as [E1|E1]; [right; left; exact E1 | right; right; apply in_app_iff; left; exact E1])) as Hsf. cbn [fst snd] in Hsf.
apply (Hkeep2 b n i); [exact Hbl | eapply blocks_perm_in; [exact HB2 | destruct HbnR as [E1|E1]; [left; first [exact E1 | symmetry; exact E1] | right; exact E1]] | exact Hi |].
intros Hin. apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [cbn [fst snd] in Hin; lia |].
unfold sink_fp in Hin. apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [unfold sink_token in Hin; cbn [fst snd] in Hin; lia|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [cbn [fst snd] in Hin; lia | exact (YI04.inFP_nil _ Hin)]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HB2 & HSK2 & HR2 & Hkg & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hkg, Hhi2, HJ2.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
jafter_call_keep HS 53%nat regs2 mem2 HP2 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack src0segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | unfold RAWCLOSE_STK; lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | cbn; intros i Hi; lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | | cbn; lia | cbn; lia].
cbn [r_wlo r_whi cl_R2]. intros i Hi. apply (present_writable src0_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 g CGIF_SIZE i HH2 Hgin2 ltac:(lia))). }
clear HS. rename HS2 into HS.
assert (Hfm : forall f', In (Some f') (cg_frames s) -> In (fr_ptr f', FRAME_SIZE) ownB /\ 4096 <= fr_ptr f' /\ fr_ptr f' + FRAME_SIZE <= alloc_ceiling /\ (g + CGIF_SIZE <= fr_ptr f' \/ fr_ptr f' + FRAME_SIZE <= g)).
{ intros f' Hin'.
assert (Hm' : In (fr_ptr f', FRAME_SIZE) ownB) by (subst ownB; apply in_app_iff; right; apply frames_blocks_ptr_in; exact Hin').
split; [exact Hm'|].
assert (HmR : In (fr_ptr f', FRAME_SIZE) restR) by (subst restR; apply in_app_iff; left; exact Hm').
destruct (blocks_range _ _ LAWS L2 A2 mem2 md2 (fr_ptr f') FRAME_SIZE HH2 ltac:(eapply blocks_perm_in; [exact HB2 | right; exact HmR])) as [Hp0' Hp1'].
pose proof (heap_sep_perm _ _ LAWS L2 A2 mem2 md2 (g, CGIF_SIZE) _ (fr_ptr f', FRAME_SIZE) HH2 HB2 HmR) as Hs'. cbn [fst snd] in Hs'. lia. }
assert (Hfin2 : In (f, FILE_BLOCK) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | right; subst restR; apply in_app_iff; right; left; reflexivity]).
pose proof (heap_sep_perm _ _ LAWS L2 A2 mem2 md2 (g, CGIF_SIZE) _ (f, FILE_BLOCK) HH2 HB2 ltac:(subst restR; apply in_app_iff; right; left; reflexivity)) as Hsepf. cbn [fst snd] in Hsepf.
jrun LAWS src0tbl_ok HS HJ2. { wr_cl HU2 HU8 Hgin2 HFPin. }
jbranch src0tbl HS; clear Hc.
-
jrun_to LAWS src0tbl_ok HS HJ2 CL_FILE. { wr_cl HU2 HU8 Hgin2 HFPin. }
cgif_obj_now_at 1%nat 2%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end. rewrite <- cgif_vals_split in Hobj2.
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_fin L A mem md regs0 rg L2 A2 mm md2 g N s rest FP (S ++ sink_trailer_Z) br) end.
+ exact HJ2. + exact Hra0. + exact Htp0. + exact Hal16. + exact Hsp47. + exact HFPin. + exact HFPs. + exact HFPlow. + exact Hr0. + exact Hlen.
+ eapply Permutation_trans; [exact HB2|]. subst restR ownB. rewrite <- app_assoc. apply Permutation_refl.
+ exact Hobj2.
+ intros f' Hin'. destruct (Hfm f' Hin') as (Hm' & Hp0' & Hp1' & Hs').
eapply obj_at_transport_range; [apply Hfrs; exact Hin' | exact (proj1 LAY_Frame_ok) |].
intros i Hi. cbn [ms_mem mkst] in *.
mb_frame_with HF1 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia).
mb_frame_with HF0 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia).
rewrite (Hkg (fr_ptr f') FRAME_SIZE i ltac:(right; exact Hm') Hi).
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity.
+ apply (sink_at_frame src0_msyms mem2 _ md2 f _); [|exact HSK2].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + CGIF_SIZE)) by (destruct Ha as [Ha|Ha]; [lia | pose proof (src0_env_addr_range a Ha); pose proof (Henvblk L2 A2 mem2 md2 g CGIF_SIZE a HH2 Hgin2 Ha); lia]).
cbn [ms_mem mkst] in *. mb_frame_with HF1 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). mb_frame_with HF0 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity.
+ unfold cl_saved_ok;
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv - 32 + (32 - dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 24 (SOff 49 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW49, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 16 (SOff 50 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW50, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 8 (SOff 51 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW51, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 0 (SOff 52 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW52, Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
+ reg_nowF HS ltac:(rewrite HU2; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; reflexivity).
+ unfold cl_untouched; repeat match goal with |- _ /\ _ => split end;
[ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G19)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27) ].
+ exact HR2.
-
jrun_to LAWS src0tbl_ok HS HJ2 CL_FILE. { wr_cl HU2 HU8 Hgin2 HFPin. }
cgif_obj_low_at 1%nat 2%nat HS HU8 HXn Rg s 57%nat.
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ [?cc; _]) |- _ => rename Hx into Hobj2; set (c := cc) in Hobj2 end.
rewrite <- (cgif_vals_set_cur s c) in Hobj2.
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_fin L A mem md regs0 rg L2 A2 mm md2 g N (set_cur s c) rest FP (S ++ sink_trailer_Z) br) end.
+ exact HJ2. + exact Hra0. + exact Htp0. + exact Hal16. + exact Hsp47. + exact HFPin. + exact HFPs. + exact HFPlow. + exact Hr0. + exact Hlen.
+ eapply Permutation_trans; [exact HB2|]. subst restR ownB. rewrite <- app_assoc. apply Permutation_refl.
+ exact Hobj2.
+ intros f' Hin'. destruct (Hfm f' Hin') as (Hm' & Hp0' & Hp1' & Hs').
eapply obj_at_transport_range; [apply Hfrs; exact Hin' | exact (proj1 LAY_Frame_ok) |].
intros i Hi. cbn [ms_mem mkst] in *.
mb_frame_with HF1 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia).
mb_frame_with HF0 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia).
rewrite (Hkg (fr_ptr f') FRAME_SIZE i ltac:(right; exact Hm') Hi).
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity.
+ apply (sink_at_frame src0_msyms mem2 _ md2 f _); [|exact HSK2].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + CGIF_SIZE)) by (destruct Ha as [Ha|Ha]; [lia | pose proof (src0_env_addr_range a Ha); pose proof (Henvblk L2 A2 mem2 md2 g CGIF_SIZE a HH2 Hgin2 Ha); lia]).
cbn [ms_mem mkst] in *. mb_frame_with HF1 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). mb_frame_with HF0 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity.
+ unfold cl_saved_ok;
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv - 32 + (32 - dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 24 (SOff 49 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW49, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 16 (SOff 50 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW50, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 8 (SOff 51 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW51, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 0 (SOff 52 0) (sp0 - 32) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW52, Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
+ reg_nowF HS ltac:(rewrite HU2; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; reflexivity).
+ unfold cl_untouched; repeat match goal with |- _ /\ _ => split end;
[ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G19)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27) ].
+ exact HR2.
Qed.
End S.
End t.
