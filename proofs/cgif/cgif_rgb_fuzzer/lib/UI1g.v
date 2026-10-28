(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI39 UI1i UI20 UI59 UI56 YI0x UI57   UI1h.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Local Lemma u64_range' : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition CLOSE : Z := ubs2_A_cgif_close.
Definition CL_LOOP : Z := Eval vm_compute in (ubs2_A_cgif_close + 0x44).
Definition CL_CURW : Z := Eval vm_compute in (ubs2_A_cgif_close + 0x70).
Definition CL_CLEAN : Z := Eval vm_compute in (ubs2_A_cgif_close + 0x74).
Definition CL_FREE : Z := Eval vm_compute in (ubs2_A_cgif_close + 0xa4).
Definition lits15 : list (option Z) :=
[None; None; None; None; Some 0; None; None; None; None; None; None; Some ubs2_A_writecb; Some 0; None; Some 0].
Lemma lits15_ok : forall s, forall j z, nth_error lits15 j = Some (Some z) -> nth_error (vals15 s) j = Some z.
Proof.
intros s j z Hj. do 15 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
Qed.
Definition cl_saved : list YQ0b.chunk :=
[mkChunk 40 (CVal 8 (SOff 49 0)); mkChunk 32 (CVal 8 (SOff 50 0)); mkChunk 24 (CVal 8 (SOff 51 0)); mkChunk 16 (CVal 8 (SOff 52 0));
mkChunk 8 (CVal 8 (SOff 53 0)); mkChunk 0 (CVal 8 (SOff 54 0))].
Definition cl_saved_vals (regs0 : bvmap 5 word) : list Z :=
[bv_unsigned (getr regs0 1); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18);
bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 20)].
Definition cl_saved_ok (mem : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
word_mem ubs2segs mem (sp0 - 8) (bv_unsigned (getr regs0 1)) /\ word_mem ubs2segs mem (sp0 - 16) (bv_unsigned (getr regs0 8)) /\
word_mem ubs2segs mem (sp0 - 24) (bv_unsigned (getr regs0 9)) /\ word_mem ubs2segs mem (sp0 - 32) (bv_unsigned (getr regs0 18)) /\
word_mem ubs2segs mem (sp0 - 40) (bv_unsigned (getr regs0 19)) /\ word_mem ubs2segs mem (sp0 - 48) (bv_unsigned (getr regs0 20)).
Definition cl_R1 : YQ0b.region := YQ0b.mkRegion (Some 8%nat) 0 88 0 0 (obj_chunks_gen LAY15 32 lits15).
Definition cl_R2 : YQ0b.region := YQ0b.mkRegion (Some 8%nat) 88 96 88 92 [mkChunk 88 (CVal 4 (SOff 47 0)); mkChunk 92 (CVal 4 (SOff 48 0))].
Definition cl_facts : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + CLOSE_STK - 48) (2^63 - 48) 4); (8%nat, mkAF 4096 (CEIL_MAX - 96) 4);
(9%nat, mkAF (2 ^ 64 - 1 - (CEIL_MAX - 96)) (2 ^ 64 - 4097) 0);
(47%nat, mkAF 0 4294967295 0); (48%nat, mkAF 0 4294967295 0) ].
Definition cl_untouched (regs0 regs1 : bvmap 5 word) : Prop :=
getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 21 = getr regs0 21 /\ getr regs1 22 = getr regs0 22 /\
getr regs1 23 = getr regs0 23 /\ getr regs1 24 = getr regs0 24 /\ getr regs1 25 = getr regs0 25 /\ getr regs1 26 = getr regs0 26 /\
getr regs1 27 = getr regs0 27.
Definition ss_free (k : Z) : sstate :=
mkSS CL_FREE (sr_set (sr_set sr_atoms 18%bv (SLit (8 * k))) 19%bv (SLit 24))
[ YQ0b.mkRegion (Some 2%nat) 0 48 0 48 cl_saved ; cl_R1 ; cl_R2 ]
None (mkFacts cl_facts [] []).
End d.
Ltac wr_cl HU2 HU8 Hgin HFPin :=
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_cons_ro; [cbn; lia|];
eapply wr_ok_cons_block with (n := 8%nat) (m := CGIF_SIZE);
[ reflexivity | ew_havocA; exact HU8 | exact Hgin | cbn; lia | unfold CGIF_SIZE; cbn; lia
| unfold cl_R2; cbn [r_wlo r_whi]; intros a Ha; eapply (HFPin _ CGIF_SIZE a); [left; reflexivity | unfold CGIF_SIZE; lia]
| apply wr_ok_nil ].
Section h. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma region_kept_live : forall E (mem mem' : word -> option byte) r n b m,
r_base r = Some n -> bv_unsigned (ew E n) = b ->
(forall i, 0 <= i < m -> mbyte ubs2segs mem' (b + i) = mbyte ubs2segs mem (b + i)) ->
(forall i, r_wlo r <= i < r_whi r -> writable_at ubs2segs mem' (b + i)) ->
0 <= r_lo r -> r_hi r <= m ->
region_kept ubs2segs E mem mem' r.
Proof.
intros E mem mem' r n b m Hb Hn Hk Hw Hlo Hhi. split; rewrite Hb; cbn [base_val]; rewrite Hn; intros a Ha.
- replace a with (b + (a - b)) by lia. apply Hk. lia.
- intros _. replace a with (b + (a - b)) by lia. apply Hw. lia.
Qed.
End h.
Ltac cgif_obj_now_at i1 i2 HS HU8 HXn Rg s cur ecur tcur :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch type of HU8 with bv_unsigned _ = ?g =>
assert (obj_at ubs2segs (ms_mem msc) g LAY_CGIF (vals15 s ++ [cur; cg_ihead s]));
[ apply obj_cgif_join;
[ eapply (st_obj_at ubs2segs _ _ _ i1 _ 8%nat g LAY15 (vals15 s) 32 lits15 HS eq_refl eq_refl ltac:(ew_havocA; exact HU8));
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
eapply (st_chunk_val ubs2segs _ _ _ i2 _ 8%nat 88 4%N ecur _ cur HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | tcur | change (2 ^ (8 * Z.of_N 4%N)) with (2 ^ 32); assumption | cbn; lia]
| assumption
| replace (g + 92) with (bv_unsigned (ew Ec 8) + 92) by (ew_havocA; rewrite HU8; reflexivity);
eapply (st_chunk_val ubs2segs _ _ _ i2 _ 8%nat 92 4%N (SOff 48 0) _ (cg_ihead s) HS);
[reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 48%nat 16%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 4%N)) with (2 ^ 32); assumption | cbn; lia]
| assumption ]
| ] end end.
Section l. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma st_chunk_lowv : forall E ss ms i rg p off (n : N) e a (k : nat) (m : Z),
st_ok ubs2segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CVal n e)) (r_chunks rg) -> bv_unsigned (ew E p) = a -> Z.of_N n <= 8 ->
k = N.to_nat n -> m = 2 ^ (8 * Z.of_N n) ->
val_mem ubs2segs (ms_mem ms) (a + off) k (U E e mod m).
Proof.
intros E ss ms i rg p off n e a k m HS Hi Hb Hin Hp Hn -> ->.
pose proof (st_region_chunks ubs2segs E ss ms i rg p a HS Hi Hb Hp) as Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
unfold U. exact (val_mem_low_of_chunk ubs2segs E (ms_mem ms) a off n e Hc Hn).
Qed.
End l.
Ltac cgif_obj_low_at i1 i2 HS HU8 HXn Rg s k :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch type of HU8 with bv_unsigned _ = ?g =>
assert (obj_at ubs2segs (ms_mem msc) g LAY_CGIF (vals15 s ++ [U Ec (SOff k 0) mod 2 ^ 32; cg_ihead s]));
[ apply obj_cgif_join;
[ eapply (st_obj_at ubs2segs _ _ _ i1 _ 8%nat g LAY15 (vals15 s) 32 lits15 HS eq_refl eq_refl ltac:(ew_havocA; exact HU8));
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
eapply (st_chunk_val ubs2segs _ _ _ i2 _ 8%nat 92 4%N (SOff 48 0) _ (cg_ihead s) HS);
[reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 48%nat 16%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 4%N)) with (2 ^ 32); assumption | cbn; lia]
| assumption ]
| ] end end.
Section q. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition close_post (regs0 : bvmap 5 word) (FP : list (Z * Z)) L A mem md (rest : list (Z * Z)) (c' : config) : Prop :=
exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR CLOSE_STK (spZ regs0) FP L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\
Permutation (blocks L' A') rest.
Lemma cgif_fp_in : forall g s N b n a,
In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP (blocks_fp (cgif_blocks g s N)) a.
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
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (rest FP : list (Z * Z)) (o0 o1 o2 : option frame_st),
let sp0 := spZ regs0 in
journal ubs2_msyms MR CLOSE_STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) -> sp0 mod 16 = 0 ->
cg_frames s = [o0; o1; o2] ->
(forall b n a, In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP FP a) ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
Permutation (blocks Lc Ac) ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N [o2] ++ rest) ->
obj_at ubs2segs memc g LAY_CGIF (cgif_vals s) ->
frames_at memc [o2] ->
cl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 48) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 (2 ^ 64 - 1 - g) -> getr regs1 18 = Z_to_bv 64 16 -> getr regs1 19 = Z_to_bv 64 24 ->
cl_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom ubs2segs)) mdc) (close_post regs0 FP L A mem md rest).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s rest FP o0 o1 o2 sp0 HJ Hra0 Htp0 Hal16 Hfs HFPin HFPlow HB Hobj Hfr HSV G2 G8 G9 G18 G19 HUT.
assert (Ho2 : nth_error (cg_frames s) 2 = Some o2) by (rewrite Hfs; reflexivity).
pose proof HUT as (G3 & G4 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HCSv : CLOSE_STK = 9728) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hspm : (sp0 - 48) mod 16 = 0) by (replace (sp0 - 48) with (sp0 + (-3) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
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
assert (HW53 : ew E 53 = getr regs0 19) by (etransitivity; [apply (HY 4%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW54 : ew E 54 = getr regs0 20) by (etransitivity; [apply (HY 5%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 48) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = 2 ^ 64 - 1 - g) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
pose proof HSV as (W1 & W8 & W9 & W18 & W19 & W20).
destruct (obj_cgif_parts memc g s Hobj) as (H15 & Hcur & Rcur & Hih & Rih).
assert (HS : st_ok ubs2segs E (ss_free 2) (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom ubs2segs))).
{ unfold ss_free. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |] | intros H0; discriminate H0 |];
cbn [sv_denot]; [first [exact G18 | rewrite G18; f_equal; lia] | exact G19].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : Z), nth_error (cl_saved_vals regs0) j = Some w -> word_mem ubs2segs memc (sp0 - 48 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs2segs (Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])) memc (sp0 - 48) (mkChunk off (CVal 8 (SOff (49 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HY j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold cl_saved.
apply Forall_cons; [apply (CK 40 0%nat _ eq_refl); [replace (sp0 - 48 + 40) with (sp0 - 8) by lia; exact W1 | apply u64_range']|].
apply Forall_cons; [apply (CK 32 1%nat _ eq_refl); [replace (sp0 - 48 + 32) with (sp0 - 16) by lia; exact W8 | apply u64_range']|].
apply Forall_cons; [apply (CK 24 2%nat _ eq_refl); [replace (sp0 - 48 + 24) with (sp0 - 24) by lia; exact W9 | apply u64_range']|].
apply Forall_cons; [apply (CK 16 3%nat _ eq_refl); [replace (sp0 - 48 + 16) with (sp0 - 32) by lia; exact W18 | apply u64_range']|].
apply Forall_cons; [apply (CK 8 4%nat _ eq_refl); [replace (sp0 - 48 + 8) with (sp0 - 40) by lia; exact W19 | apply u64_range']|].
apply Forall_cons; [apply (CK 0 5%nat _ eq_refl); [replace (sp0 - 48 + 0) with (sp0 - 48) by lia; exact W20 | apply u64_range']|].
apply Forall_nil.
+ unfold cl_R1. eapply (region_ok_obj_gen ubs2segs _ memc 8 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[exact HU8 | lia | lia | exact H15 | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj|].
apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
+ unfold cl_R2, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE o HH0 Hgin ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih]. }
apply Forall_nil.
- unfold cl_R1, cl_R2. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU8. repeat split; lia.
- split; [| split; constructor].
cbn [f_atoms atoms_ok cl_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
pose proof (Rg 15%nat _ eq_refl) as R47. pose proof (Rg 16%nat _ eq_refl) as R48.
cbn [nth snd LAY_CGIF Z.of_N] in R47, R48.
rewrite HU2, HU8, HU9, (HXn 47%nat 15%nat _ eq_refl eq_refl), (HXn 48%nat 16%nat _ eq_refl eq_refl).
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_freeFrame.
{ wr_cl HU2 HU8 Hgin HFPin. }
jreg HS (10%bv:reg) as Hf10. jreg HS (2%bv:reg) as Hf2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hf2.
jreg HS (4%bv:reg) as Hf4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hf4. jreg HS (1%bv:reg) as Hf1x.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 48) by (unfold spZ; rewrite Hf2; apply unsigned_lit_small; lia) end.
set (rest0 := (g, CGIF_SIZE) :: pal_blocks s ++ rest).
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 (Z_to_bv 64 (ubs2_A_cgif_close + 0xb4)) mem2 (seg_rom ubs2segs)) md2 /\
journal ubs2_msyms MR CLOSE_STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs msx) regs2 /\ Permutation (blocks L2 A2) rest0 /\
(forall b n i, In (b, n) rest0 -> 0 <= i < n -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs (ms_mem msx) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 48 - FREEFRAME_STK <= x < sp0 - 48) ->
mbyte ubs2segs mem2 x = mbyte ubs2segs (ms_mem msx) x /\ (writable_at ubs2segs (ms_mem msx) x <-> writable_at ubs2segs mem2 x)))
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
{ eapply (jcall ubs2_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := fp_freeFrame (fr_ptr f) (fr_img f) N (fr_attr f) (fr_lpal f) (3 * fr_nlp f))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => Permutation (blocks L2 A2) rest0);
[ exact HS | reflexivity | exact HJ | exact Hf1x | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp; unfold FREEFRAME_STK; lia | rewrite Hsp; lia | exact Hf4 | ].
+ intros HPRE1. eapply SR_mono.
{ eapply (ubs2_freeFrame API IMG _ _ _ _ _ (fr_ptr f) (frame_vals f) (fr_img f) N (fr_attr f) (fr_lpal f) (3 * fr_nlp f) rest0 HPRE1);
[ | | reflexivity | reflexivity | reflexivity | exact HBf ].
- rewrite Hf10, (HXn 34%nat 2%nat _ eq_refl eq_refl). rewrite (@nth_error_nth _ (cg_frames s) 2 _ None Ho2). reflexivity.
- eapply obj_at_transport_range; [exact (Hfr f ltac:(left; reflexivity)) | exact (proj1 LAY_Frame_ok) |].
intros i Hi. cbn [ms_mem mkst] in *. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJc & HP & HB2).
exists L2, A2, regs2, mem2, md2. split; [rewrite Hf1x; reflexivity|]. split; [exact HJc|]. split; [exact HP | exact HB2].
+ intros a Ha. split; [| apply HFPlow].
all: unfold fp_freeFrame in Ha; apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[apply (HFPin (fr_ptr f) FRAME_SIZE a); [apply (frame_blocks_in_cgif g s N f); [exact Hfin | left; reflexivity] | unfold FRAME_SIZE; lia] |];
apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[apply (HFPin (fr_img f) N a); [apply (frame_blocks_in_cgif g s N f); [exact Hfin | right; left; reflexivity] | lia] |];
(destruct (Z.land (fr_attr f) 1 =? 0) eqn:Hz; [exfalso; exact (inFP_nil a Ha)|]);
apply inFP_cons in Ha; (destruct Ha as [Ha|Ha]; [|exfalso; exact (inFP_nil a Ha)]);
(apply (HFPin (fr_lpal f) (3 * fr_nlp f) a); [apply (frame_blocks_in_cgif g s N f); [exact Hfin|]; unfold frame_blocks; rewrite Hz; right; right; left; reflexivity | lia]). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HB2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|].
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
destruct (Z.land (fr_attr f) 1 =? 0) eqn:Hz; [exact (inFP_nil _ Hin)|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [| exact (inFP_nil _ Hin)].
pose proof (HsepR (fr_lpal f, 3 * fr_nlp f) ltac:(unfold frame_blocks; rewrite Hz; right; right; left; reflexivity)). cbn [fst snd] in *. lia.
-
cbn [frames_blocks flat_map app] in HB.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_mono.
{ eapply (jcall ubs2_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := @nil (Z * Z))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => Permutation (blocks L2 A2) rest0);
[ exact HS | reflexivity | exact HJ | exact Hf1x | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp; unfold FREEFRAME_STK; lia | rewrite Hsp; lia | exact Hf4
| intros a Ha; exfalso; exact (inFP_nil a Ha) ].
intros HPRE1. eapply SR_mono.
{ eapply (ubs2_freeFrame_null API IMG _ _ _ _ _ HPRE1). rewrite Hf10, (HXn 34%nat 2%nat _ eq_refl eq_refl). rewrite (@nth_error_nth _ (cg_frames s) 2 _ None Ho2). reflexivity. }
cbv beta. intros c' (regs2 & mem2 & -> & HJc & HP).
exists Lc, Ac, regs2, mem2, mdc. split; [rewrite Hf1x; reflexivity|]. split; [exact HJc|]. split; [exact HP | exact HB]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HB2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|].
pose proof HJc2 as (_ & _ & Hhi2 & Hkeep2 & _). rewrite Hsp in Hhi2. split; [| exact Hhi2].
intros b n i Hbn Hi. apply (Hkeep2 b n i); [eapply blocks_perm_in; [exact HB |] | eapply blocks_perm_in; [exact HB2 |] | exact Hi | intros Hin; exact (inFP_nil _ Hin)];
(destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn]). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HB2 & Hkg & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hkg, Hhi2, HJ2.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
jafter_call_keep HS 55%nat regs2 mem2 HP2 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | cbn; intros i Hi; lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | | cbn; lia | cbn; lia].
cbn [r_wlo r_whi cl_R2]. intros i Hi. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 g CGIF_SIZE i HH2 Hgin2 ltac:(lia))). }
clear HS. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ2 ubs2_A_freeCGIF. { wr_cl HU2 HU8 Hgin2 HFPin. }
jreg HS (10%bv:reg) as Hc10. jreg HS (2%bv:reg) as Hc2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hc2.
jreg HS (4%bv:reg) as Hc4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hc4. jreg HS (1%bv:reg) as Hc1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp2 : spZ (ms_regs msx) = sp0 - 48) by (unfold spZ; rewrite Hc2; apply unsigned_lit_small; lia) end.
cgif_obj_now_at 1%nat 2%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end.
assert (Hpalsep : Z.land (cg_attr s) 4 = 0 -> g + CGIF_SIZE <= cg_pal s \/ cg_pal s + 3 * cg_ngp s <= g).
{ intros Hz. apply (heap_sep_perm _ _ LAWS L2 A2 mem2 md2 (g, CGIF_SIZE) (pal_blocks s ++ rest) (cg_pal s, 3 * cg_ngp s) HH2 HB2).
apply in_app_iff. left. unfold pal_blocks. rewrite Hz. left. reflexivity. }
eapply SR_bind.
{ eapply (jcall ubs2_msyms MR) with (STK1 := FREECGIF_STK) (FP1 := fp_freeCGIF g (cg_attr s) (cg_pal s) (3 * cg_ngp s))
(K := fun L3 A3 (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) => Permutation (blocks L3 A3) rest);
[ exact HS | reflexivity | exact HJ2 | exact Hc1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp2; exact Hspm | unfold FREECGIF_STK; lia | rewrite Hsp2; unfold FREECGIF_STK; lia | rewrite Hsp2; lia | exact Hc4 | ].
- intros HPRE2. eapply SR_mono.
{ eapply (ubs2_freeCGIF API IMG _ _ _ _ _ g _ (cg_attr s) (cg_pal s) (3 * cg_ngp s) rest HPRE2); [ | exact Hobj2 | reflexivity | reflexivity | exact HB2 ].
rewrite Hc10. ew_havocA. rewrite <- HU8. symmetry. apply Z_to_bv_bv_unsigned. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJc & HP & HB3).
exists L3, A3, regs3, mem3, md3. split; [rewrite Hc1; reflexivity|]. split; [exact HJc|]. split; [exact HP | exact HB3].
- intros a Ha. split; [| apply HFPlow].
all: unfold fp_freeCGIF in Ha; apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[apply (HFPin g CGIF_SIZE a); [left; reflexivity | lia] |];
(destruct (Z.land (cg_attr s) 4 =? 0) eqn:Hz; [|exfalso; exact (inFP_nil a Ha)]);
apply inFP_cons in Ha; (destruct Ha as [Ha|Ha]; [|exfalso; exact (inFP_nil a Ha)]);
(apply (HFPin (cg_pal s) (3 * cg_ngp s) a); [unfold cgif_blocks, pal_blocks; rewrite Hz; right; right; left; reflexivity | lia]). }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HB3). clear HJ2.
cbn [ms_regs ms_mem mkst] in HP3, HJc3, HJ3.
pose proof HJc3 as (_ & _ & Hhi3 & _). rewrite Hsp2 in Hhi3.
jafter_call_keep HS 71%nat regs3 mem3 HP3 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi3 | lia | lia | unfold FREECGIF_STK; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs2tbl_ok HS HJ3.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3)))). }
unfold close_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists L3, A3, (ms_regs msf), (ms_mem msf), md3 end.
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|nat_lt_lit]); rewrite ?Z.add_0_r, HW49, Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end. }
split; [exact HJ3|].
split; [| exact HB3].
apply regs_preserved_intro; cbn [ms_regs mkst].
- reg_nowF HS ltac:(rewrite HU2; replace (sp0 - 48 + 48) with sp0 by lia; subst sp0; unfold spZ; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
- reg_nowF HS ltac:(rewrite HW50; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW51; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW52; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW53; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW54; apply Z_to_bv_bv_unsigned).
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
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (rest FP : list (Z * Z)) (o0 o1 o2 : option frame_st),
let sp0 := spZ regs0 in
journal ubs2_msyms MR CLOSE_STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) -> sp0 mod 16 = 0 ->
cg_frames s = [o0; o1; o2] ->
(forall b n a, In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP FP a) ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
Permutation (blocks Lc Ac) ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N [o1; o2] ++ rest) ->
obj_at ubs2segs memc g LAY_CGIF (cgif_vals s) ->
frames_at memc [o1; o2] ->
cl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 48) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 (2 ^ 64 - 1 - g) -> getr regs1 18 = Z_to_bv 64 8 -> getr regs1 19 = Z_to_bv 64 24 ->
cl_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom ubs2segs)) mdc) (close_post regs0 FP L A mem md rest).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s rest FP o0 o1 o2 sp0 HJ Hra0 Htp0 Hal16 Hfs HFPin HFPlow HB Hobj Hfr HSV G2 G8 G9 G18 G19 HUT.
assert (Ho1 : nth_error (cg_frames s) 1 = Some o1) by (rewrite Hfs; reflexivity).
pose proof HUT as (G3 & G4 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HCSv : CLOSE_STK = 9728) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hspm : (sp0 - 48) mod 16 = 0) by (replace (sp0 - 48) with (sp0 + (-3) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
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
assert (HW53 : ew E 53 = getr regs0 19) by (etransitivity; [apply (HY 4%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW54 : ew E 54 = getr regs0 20) by (etransitivity; [apply (HY 5%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 48) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = 2 ^ 64 - 1 - g) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
pose proof HSV as (W1 & W8 & W9 & W18 & W19 & W20).
destruct (obj_cgif_parts memc g s Hobj) as (H15 & Hcur & Rcur & Hih & Rih).
assert (HS : st_ok ubs2segs E (ss_free 1) (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom ubs2segs))).
{ unfold ss_free. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |] | intros H0; discriminate H0 |];
cbn [sv_denot]; [first [exact G18 | rewrite G18; f_equal; lia] | exact G19].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : Z), nth_error (cl_saved_vals regs0) j = Some w -> word_mem ubs2segs memc (sp0 - 48 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs2segs (Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])) memc (sp0 - 48) (mkChunk off (CVal 8 (SOff (49 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HY j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold cl_saved.
apply Forall_cons; [apply (CK 40 0%nat _ eq_refl); [replace (sp0 - 48 + 40) with (sp0 - 8) by lia; exact W1 | apply u64_range']|].
apply Forall_cons; [apply (CK 32 1%nat _ eq_refl); [replace (sp0 - 48 + 32) with (sp0 - 16) by lia; exact W8 | apply u64_range']|].
apply Forall_cons; [apply (CK 24 2%nat _ eq_refl); [replace (sp0 - 48 + 24) with (sp0 - 24) by lia; exact W9 | apply u64_range']|].
apply Forall_cons; [apply (CK 16 3%nat _ eq_refl); [replace (sp0 - 48 + 16) with (sp0 - 32) by lia; exact W18 | apply u64_range']|].
apply Forall_cons; [apply (CK 8 4%nat _ eq_refl); [replace (sp0 - 48 + 8) with (sp0 - 40) by lia; exact W19 | apply u64_range']|].
apply Forall_cons; [apply (CK 0 5%nat _ eq_refl); [replace (sp0 - 48 + 0) with (sp0 - 48) by lia; exact W20 | apply u64_range']|].
apply Forall_nil.
+ unfold cl_R1. eapply (region_ok_obj_gen ubs2segs _ memc 8 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[exact HU8 | lia | lia | exact H15 | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj|].
apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
+ unfold cl_R2, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE o HH0 Hgin ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih]. }
apply Forall_nil.
- unfold cl_R1, cl_R2. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU8. repeat split; lia.
- split; [| split; constructor].
cbn [f_atoms atoms_ok cl_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
pose proof (Rg 15%nat _ eq_refl) as R47. pose proof (Rg 16%nat _ eq_refl) as R48.
cbn [nth snd LAY_CGIF Z.of_N] in R47, R48.
rewrite HU2, HU8, HU9, (HXn 47%nat 15%nat _ eq_refl eq_refl), (HXn 48%nat 16%nat _ eq_refl eq_refl).
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_freeFrame.
{ wr_cl HU2 HU8 Hgin HFPin. }
jreg HS (10%bv:reg) as Hf10. jreg HS (2%bv:reg) as Hf2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hf2.
jreg HS (4%bv:reg) as Hf4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hf4. jreg HS (1%bv:reg) as Hf1x.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 48) by (unfold spZ; rewrite Hf2; apply unsigned_lit_small; lia) end.
set (rest0 := (g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N [o2] ++ rest).
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 (Z_to_bv 64 (ubs2_A_cgif_close + 0xb4)) mem2 (seg_rom ubs2segs)) md2 /\
journal ubs2_msyms MR CLOSE_STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs msx) regs2 /\ Permutation (blocks L2 A2) rest0 /\
(forall b n i, In (b, n) rest0 -> 0 <= i < n -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs (ms_mem msx) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 48 - FREEFRAME_STK <= x < sp0 - 48) ->
mbyte ubs2segs mem2 x = mbyte ubs2segs (ms_mem msx) x /\ (writable_at ubs2segs (ms_mem msx) x <-> writable_at ubs2segs mem2 x)))
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
{ eapply (jcall ubs2_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := fp_freeFrame (fr_ptr f) (fr_img f) N (fr_attr f) (fr_lpal f) (3 * fr_nlp f))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => Permutation (blocks L2 A2) rest0);
[ exact HS | reflexivity | exact HJ | exact Hf1x | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp; unfold FREEFRAME_STK; lia | rewrite Hsp; lia | exact Hf4 | ].
+ intros HPRE1. eapply SR_mono.
{ eapply (ubs2_freeFrame API IMG _ _ _ _ _ (fr_ptr f) (frame_vals f) (fr_img f) N (fr_attr f) (fr_lpal f) (3 * fr_nlp f) rest0 HPRE1);
[ | | reflexivity | reflexivity | reflexivity | exact HBf ].
- rewrite Hf10, (HXn 33%nat 1%nat _ eq_refl eq_refl). rewrite (@nth_error_nth _ (cg_frames s) 1 _ None Ho1). reflexivity.
- eapply obj_at_transport_range; [exact (Hfr f ltac:(left; reflexivity)) | exact (proj1 LAY_Frame_ok) |].
intros i Hi. cbn [ms_mem mkst] in *. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJc & HP & HB2).
exists L2, A2, regs2, mem2, md2. split; [rewrite Hf1x; reflexivity|]. split; [exact HJc|]. split; [exact HP | exact HB2].
+ intros a Ha. split; [| apply HFPlow].
all: unfold fp_freeFrame in Ha; apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[apply (HFPin (fr_ptr f) FRAME_SIZE a); [apply (frame_blocks_in_cgif g s N f); [exact Hfin | left; reflexivity] | unfold FRAME_SIZE; lia] |];
apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[apply (HFPin (fr_img f) N a); [apply (frame_blocks_in_cgif g s N f); [exact Hfin | right; left; reflexivity] | lia] |];
(destruct (Z.land (fr_attr f) 1 =? 0) eqn:Hz; [exfalso; exact (inFP_nil a Ha)|]);
apply inFP_cons in Ha; (destruct Ha as [Ha|Ha]; [|exfalso; exact (inFP_nil a Ha)]);
(apply (HFPin (fr_lpal f) (3 * fr_nlp f) a); [apply (frame_blocks_in_cgif g s N f); [exact Hfin|]; unfold frame_blocks; rewrite Hz; right; right; left; reflexivity | lia]). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HB2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|].
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
destruct (Z.land (fr_attr f) 1 =? 0) eqn:Hz; [exact (inFP_nil _ Hin)|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [| exact (inFP_nil _ Hin)].
pose proof (HsepR (fr_lpal f, 3 * fr_nlp f) ltac:(unfold frame_blocks; rewrite Hz; right; right; left; reflexivity)). cbn [fst snd] in *. lia.
-
rewrite frames_blocks_cons_none in HB.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_mono.
{ eapply (jcall ubs2_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := @nil (Z * Z))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => Permutation (blocks L2 A2) rest0);
[ exact HS | reflexivity | exact HJ | exact Hf1x | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp; unfold FREEFRAME_STK; lia | rewrite Hsp; lia | exact Hf4
| intros a Ha; exfalso; exact (inFP_nil a Ha) ].
intros HPRE1. eapply SR_mono.
{ eapply (ubs2_freeFrame_null API IMG _ _ _ _ _ HPRE1). rewrite Hf10, (HXn 33%nat 1%nat _ eq_refl eq_refl). rewrite (@nth_error_nth _ (cg_frames s) 1 _ None Ho1). reflexivity. }
cbv beta. intros c' (regs2 & mem2 & -> & HJc & HP).
exists Lc, Ac, regs2, mem2, mdc. split; [rewrite Hf1x; reflexivity|]. split; [exact HJc|]. split; [exact HP | exact HB]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HB2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|].
pose proof HJc2 as (_ & _ & Hhi2 & Hkeep2 & _). rewrite Hsp in Hhi2. split; [| exact Hhi2].
intros b n i Hbn Hi. apply (Hkeep2 b n i); [eapply blocks_perm_in; [exact HB |] | eapply blocks_perm_in; [exact HB2 |] | exact Hi | intros Hin; exact (inFP_nil _ Hin)];
(destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn]). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HB2 & Hkg & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hkg, Hhi2, HJ2.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
jafter_call_keep HS 55%nat regs2 mem2 HP2 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | cbn; intros i Hi; lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | | cbn; lia | cbn; lia].
cbn [r_wlo r_whi cl_R2]. intros i Hi. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 g CGIF_SIZE i HH2 Hgin2 ltac:(lia))). }
clear HS. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ2 CL_FREE. { wr_cl HU2 HU8 Hgin2 HFPin. }
cgif_obj_now_at 1%nat 2%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_free2 L A mem md regs0 rg L2 A2 mm md2 g N s rest FP o0 o1 o2) end.
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
replace (spv - dd) with (spv - 48 + (48 - dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 40 (SOff 49 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW49, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 32 (SOff 50 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW50, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 24 (SOff 51 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW51, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 16 (SOff 52 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW52, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 8 (SOff 53 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW53, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 0 (SOff 54 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW54, Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
+ reg_nowF HS ltac:(rewrite HU2; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ unfold cl_untouched. repeat match goal with |- _ /\ _ => split end;
[ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27) ].
Qed.
Lemma close_free0 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (rest FP : list (Z * Z)) (o0 o1 o2 : option frame_st),
let sp0 := spZ regs0 in
journal ubs2_msyms MR CLOSE_STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) -> sp0 mod 16 = 0 ->
cg_frames s = [o0; o1; o2] ->
(forall b n a, In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP FP a) ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
Permutation (blocks Lc Ac) ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N [o0; o1; o2] ++ rest) ->
obj_at ubs2segs memc g LAY_CGIF (cgif_vals s) ->
frames_at memc [o0; o1; o2] ->
cl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 48) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 (2 ^ 64 - 1 - g) -> getr regs1 18 = Z_to_bv 64 0 -> getr regs1 19 = Z_to_bv 64 24 ->
cl_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom ubs2segs)) mdc) (close_post regs0 FP L A mem md rest).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s rest FP o0 o1 o2 sp0 HJ Hra0 Htp0 Hal16 Hfs HFPin HFPlow HB Hobj Hfr HSV G2 G8 G9 G18 G19 HUT.
assert (Ho0 : nth_error (cg_frames s) 0 = Some o0) by (rewrite Hfs; reflexivity).
pose proof HUT as (G3 & G4 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HCSv : CLOSE_STK = 9728) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hspm : (sp0 - 48) mod 16 = 0) by (replace (sp0 - 48) with (sp0 + (-3) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
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
assert (HW53 : ew E 53 = getr regs0 19) by (etransitivity; [apply (HY 4%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW54 : ew E 54 = getr regs0 20) by (etransitivity; [apply (HY 5%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 48) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = 2 ^ 64 - 1 - g) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
pose proof HSV as (W1 & W8 & W9 & W18 & W19 & W20).
destruct (obj_cgif_parts memc g s Hobj) as (H15 & Hcur & Rcur & Hih & Rih).
assert (HS : st_ok ubs2segs E (ss_free 0) (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom ubs2segs))).
{ unfold ss_free. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |] | intros H0; discriminate H0 |];
cbn [sv_denot]; [first [exact G18 | rewrite G18; f_equal; lia] | exact G19].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : Z), nth_error (cl_saved_vals regs0) j = Some w -> word_mem ubs2segs memc (sp0 - 48 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs2segs (Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])) memc (sp0 - 48) (mkChunk off (CVal 8 (SOff (49 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HY j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold cl_saved.
apply Forall_cons; [apply (CK 40 0%nat _ eq_refl); [replace (sp0 - 48 + 40) with (sp0 - 8) by lia; exact W1 | apply u64_range']|].
apply Forall_cons; [apply (CK 32 1%nat _ eq_refl); [replace (sp0 - 48 + 32) with (sp0 - 16) by lia; exact W8 | apply u64_range']|].
apply Forall_cons; [apply (CK 24 2%nat _ eq_refl); [replace (sp0 - 48 + 24) with (sp0 - 24) by lia; exact W9 | apply u64_range']|].
apply Forall_cons; [apply (CK 16 3%nat _ eq_refl); [replace (sp0 - 48 + 16) with (sp0 - 32) by lia; exact W18 | apply u64_range']|].
apply Forall_cons; [apply (CK 8 4%nat _ eq_refl); [replace (sp0 - 48 + 8) with (sp0 - 40) by lia; exact W19 | apply u64_range']|].
apply Forall_cons; [apply (CK 0 5%nat _ eq_refl); [replace (sp0 - 48 + 0) with (sp0 - 48) by lia; exact W20 | apply u64_range']|].
apply Forall_nil.
+ unfold cl_R1. eapply (region_ok_obj_gen ubs2segs _ memc 8 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[exact HU8 | lia | lia | exact H15 | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj|].
apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
+ unfold cl_R2, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE o HH0 Hgin ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih]. }
apply Forall_nil.
- unfold cl_R1, cl_R2. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU8. repeat split; lia.
- split; [| split; constructor].
cbn [f_atoms atoms_ok cl_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
pose proof (Rg 15%nat _ eq_refl) as R47. pose proof (Rg 16%nat _ eq_refl) as R48.
cbn [nth snd LAY_CGIF Z.of_N] in R47, R48.
rewrite HU2, HU8, HU9, (HXn 47%nat 15%nat _ eq_refl eq_refl), (HXn 48%nat 16%nat _ eq_refl eq_refl).
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 CL_FREE) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_freeFrame.
{ wr_cl HU2 HU8 Hgin HFPin. }
jreg HS (10%bv:reg) as Hf10. jreg HS (2%bv:reg) as Hf2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hf2.
jreg HS (4%bv:reg) as Hf4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hf4. jreg HS (1%bv:reg) as Hf1x.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 48) by (unfold spZ; rewrite Hf2; apply unsigned_lit_small; lia) end.
set (rest0 := (g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N [o1; o2] ++ rest).
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 (Z_to_bv 64 (ubs2_A_cgif_close + 0xb4)) mem2 (seg_rom ubs2segs)) md2 /\
journal ubs2_msyms MR CLOSE_STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs msx) regs2 /\ Permutation (blocks L2 A2) rest0 /\
(forall b n i, In (b, n) rest0 -> 0 <= i < n -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs (ms_mem msx) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 48 - FREEFRAME_STK <= x < sp0 - 48) ->
mbyte ubs2segs mem2 x = mbyte ubs2segs (ms_mem msx) x /\ (writable_at ubs2segs (ms_mem msx) x <-> writable_at ubs2segs mem2 x)))
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
{ eapply (jcall ubs2_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := fp_freeFrame (fr_ptr f) (fr_img f) N (fr_attr f) (fr_lpal f) (3 * fr_nlp f))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => Permutation (blocks L2 A2) rest0);
[ exact HS | reflexivity | exact HJ | exact Hf1x | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp; unfold FREEFRAME_STK; lia | rewrite Hsp; lia | exact Hf4 | ].
+ intros HPRE1. eapply SR_mono.
{ eapply (ubs2_freeFrame API IMG _ _ _ _ _ (fr_ptr f) (frame_vals f) (fr_img f) N (fr_attr f) (fr_lpal f) (3 * fr_nlp f) rest0 HPRE1);
[ | | reflexivity | reflexivity | reflexivity | exact HBf ].
- rewrite Hf10, (HXn 32%nat 0%nat _ eq_refl eq_refl). rewrite (@nth_error_nth _ (cg_frames s) 0 _ None Ho0). reflexivity.
- eapply obj_at_transport_range; [exact (Hfr f ltac:(left; reflexivity)) | exact (proj1 LAY_Frame_ok) |].
intros i Hi. cbn [ms_mem mkst] in *. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJc & HP & HB2).
exists L2, A2, regs2, mem2, md2. split; [rewrite Hf1x; reflexivity|]. split; [exact HJc|]. split; [exact HP | exact HB2].
+ intros a Ha. split; [| apply HFPlow].
all: unfold fp_freeFrame in Ha; apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[apply (HFPin (fr_ptr f) FRAME_SIZE a); [apply (frame_blocks_in_cgif g s N f); [exact Hfin | left; reflexivity] | unfold FRAME_SIZE; lia] |];
apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[apply (HFPin (fr_img f) N a); [apply (frame_blocks_in_cgif g s N f); [exact Hfin | right; left; reflexivity] | lia] |];
(destruct (Z.land (fr_attr f) 1 =? 0) eqn:Hz; [exfalso; exact (inFP_nil a Ha)|]);
apply inFP_cons in Ha; (destruct Ha as [Ha|Ha]; [|exfalso; exact (inFP_nil a Ha)]);
(apply (HFPin (fr_lpal f) (3 * fr_nlp f) a); [apply (frame_blocks_in_cgif g s N f); [exact Hfin|]; unfold frame_blocks; rewrite Hz; right; right; left; reflexivity | lia]). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HB2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|].
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
destruct (Z.land (fr_attr f) 1 =? 0) eqn:Hz; [exact (inFP_nil _ Hin)|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [| exact (inFP_nil _ Hin)].
pose proof (HsepR (fr_lpal f, 3 * fr_nlp f) ltac:(unfold frame_blocks; rewrite Hz; right; right; left; reflexivity)). cbn [fst snd] in *. lia.
-
rewrite frames_blocks_cons_none in HB.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_mono.
{ eapply (jcall ubs2_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := @nil (Z * Z))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => Permutation (blocks L2 A2) rest0);
[ exact HS | reflexivity | exact HJ | exact Hf1x | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp; unfold FREEFRAME_STK; lia | rewrite Hsp; lia | exact Hf4
| intros a Ha; exfalso; exact (inFP_nil a Ha) ].
intros HPRE1. eapply SR_mono.
{ eapply (ubs2_freeFrame_null API IMG _ _ _ _ _ HPRE1). rewrite Hf10, (HXn 32%nat 0%nat _ eq_refl eq_refl). rewrite (@nth_error_nth _ (cg_frames s) 0 _ None Ho0). reflexivity. }
cbv beta. intros c' (regs2 & mem2 & -> & HJc & HP).
exists Lc, Ac, regs2, mem2, mdc. split; [rewrite Hf1x; reflexivity|]. split; [exact HJc|]. split; [exact HP | exact HB]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HB2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|].
pose proof HJc2 as (_ & _ & Hhi2 & Hkeep2 & _). rewrite Hsp in Hhi2. split; [| exact Hhi2].
intros b n i Hbn Hi. apply (Hkeep2 b n i); [eapply blocks_perm_in; [exact HB |] | eapply blocks_perm_in; [exact HB2 |] | exact Hi | intros Hin; exact (inFP_nil _ Hin)];
(destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn]). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HB2 & Hkg & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hkg, Hhi2, HJ2.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
jafter_call_keep HS 55%nat regs2 mem2 HP2 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | cbn; intros i Hi; lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | | cbn; lia | cbn; lia].
cbn [r_wlo r_whi cl_R2]. intros i Hi. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 g CGIF_SIZE i HH2 Hgin2 ltac:(lia))). }
clear HS. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ2 CL_FREE. { wr_cl HU2 HU8 Hgin2 HFPin. }
cgif_obj_now_at 1%nat 2%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_free1 L A mem md regs0 rg L2 A2 mm md2 g N s rest FP o0 o1 o2) end.
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
replace (spv - dd) with (spv - 48 + (48 - dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 40 (SOff 49 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW49, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 32 (SOff 50 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW50, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 24 (SOff 51 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW51, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 16 (SOff 52 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW52, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 8 (SOff 53 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW53, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 0 (SOff 54 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW54, Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
+ reg_nowF HS ltac:(rewrite HU2; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ unfold cl_untouched. repeat match goal with |- _ /\ _ => split end;
[ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27) ].
Qed.
Definition ss_clean : sstate :=
mkSS CL_CLEAN sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 48 0 48 cl_saved ; cl_R1 ; cl_R2 ]
None (mkFacts (cl_facts ++ [(45%nat, mkAF 4096 (CEIL_MAX - 48) 4)]) [] []).
Lemma close_clean :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (rest FP : list (Z * Z)),
let sp0 := spZ regs0 in
journal ubs2_msyms MR CLOSE_STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) -> sp0 mod 16 = 0 ->
(forall b n a, In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP FP a) ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
cgif_at memc g s -> cgif_wf s N ->
Permutation (blocks Lc Ac) (cgif_blocks g s N ++ rest) ->
cl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 48) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 (2 ^ 64 - 1 - g) ->
cl_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 CL_CLEAN) memc (seg_rom ubs2segs)) mdc) (close_post regs0 FP L A mem md rest).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s rest FP sp0 HJ Hra0 Htp0 Hal16 HFPin HFPlow Hat Hwf HB HSV G2 G8 G9 HUT.
pose proof HUT as (G3 & G4 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof Hat as (Hobj & Hraw & Hfrs). pose proof Hwf as (Hlen & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HCSv : CLOSE_STK = 9728) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hspm : (sp0 - 48) mod 16 = 0) by (replace (sp0 - 48) with (sp0 + (-3) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
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
assert (HW53 : ew E 53 = getr regs0 19) by (etransitivity; [apply (HY 4%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW54 : ew E 54 = getr regs0 20) by (etransitivity; [apply (HY 5%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 48) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = 2 ^ 64 - 1 - g) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
pose proof HSV as (W1 & W8 & W9 & W18 & W19 & W20).
destruct (obj_cgif_parts memc g s Hobj) as (H15 & Hcur & Rcur & Hih & Rih).
assert (HS : st_ok ubs2segs E ss_clean (mkst regs1 (Z_to_bv 64 CL_CLEAN) memc (seg_rom ubs2segs))).
{ unfold ss_clean. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : Z), nth_error (cl_saved_vals regs0) j = Some w -> word_mem ubs2segs memc (sp0 - 48 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs2segs (Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])) memc (sp0 - 48) (mkChunk off (CVal 8 (SOff (49 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HY j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold cl_saved.
apply Forall_cons; [apply (CK 40 0%nat _ eq_refl); [replace (sp0 - 48 + 40) with (sp0 - 8) by lia; exact W1 | apply u64_range']|].
apply Forall_cons; [apply (CK 32 1%nat _ eq_refl); [replace (sp0 - 48 + 32) with (sp0 - 16) by lia; exact W8 | apply u64_range']|].
apply Forall_cons; [apply (CK 24 2%nat _ eq_refl); [replace (sp0 - 48 + 24) with (sp0 - 24) by lia; exact W9 | apply u64_range']|].
apply Forall_cons; [apply (CK 16 3%nat _ eq_refl); [replace (sp0 - 48 + 16) with (sp0 - 32) by lia; exact W18 | apply u64_range']|].
apply Forall_cons; [apply (CK 8 4%nat _ eq_refl); [replace (sp0 - 48 + 8) with (sp0 - 40) by lia; exact W19 | apply u64_range']|].
apply Forall_cons; [apply (CK 0 5%nat _ eq_refl); [replace (sp0 - 48 + 0) with (sp0 - 48) by lia; exact W20 | apply u64_range']|].
apply Forall_nil.
+ unfold cl_R1. eapply (region_ok_obj_gen ubs2segs _ memc 8 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[exact HU8 | lia | lia | exact H15 | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj|].
apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
+ unfold cl_R2, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE o HH0 Hgin ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih]. }
apply Forall_nil.
- unfold cl_R1, cl_R2. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU8. repeat split; lia.
- cbn [f_atoms atoms_ok cl_facts app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
pose proof (Rg 15%nat _ eq_refl) as R47. pose proof (Rg 16%nat _ eq_refl) as R48.
cbn [nth snd LAY_CGIF Z.of_N] in R47, R48.
rewrite HU2, HU8, HU9, (HXn 47%nat 15%nat _ eq_refl eq_refl), (HXn 48%nat 16%nat _ eq_refl eq_refl), (HXn 45%nat 13%nat _ eq_refl eq_refl).
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 CL_CLEAN) memc (seg_rom ubs2segs))) in HJ.
set (restR := (pal_blocks s ++ frames_blocks N (cg_frames s)) ++ rest).
assert (HBr : Permutation (blocks Lc Ac) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: restR)).
{ eapply Permutation_trans; [exact HB|]. apply perm_swap. }
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_cgif_raw_close. { wr_cl HU2 HU8 Hgin HFPin. }
jreg HS (10%bv:reg) as Hm10. jreg HS (2%bv:reg) as Hm2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hm2.
jreg HS (4%bv:reg) as Hm4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hm4. jreg HS (1%bv:reg) as Hm1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 48) by (unfold spZ; rewrite Hm2; apply unsigned_lit_small; lia) end.
cgif_obj_now_at 1%nat 2%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj1 end. rewrite <- cgif_vals_split in Hobj1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 (Z_to_bv 64 (ubs2_A_cgif_close + 0x7c)) mem2 (seg_rom ubs2segs)) md2 /\
journal ubs2_msyms MR CLOSE_STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs msx) regs2 /\ Permutation (blocks L2 A2) ((g, CGIF_SIZE) :: restR) /\
(forall b n i, In (b, n) ((g, CGIF_SIZE) :: restR) -> 0 <= i < n -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs (ms_mem msx) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 48 - RAWCLOSE_STK <= x < sp0 - 48) ->
mbyte ubs2segs mem2 x = mbyte ubs2segs (ms_mem msx) x /\ (writable_at ubs2segs (ms_mem msx) x <-> writable_at ubs2segs mem2 x)))
end.
{ eapply SR_mono.
{ eapply (jcall ubs2_msyms MR) with (STK1 := RAWCLOSE_STK) (FP1 := [(cg_raw s, cg_raw s + RAW_SIZE)])
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => Permutation (blocks L2 A2) ((g, CGIF_SIZE) :: restR));
[ exact HS | reflexivity | exact HJ | exact Hm1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold RAWCLOSE_STK; lia | rewrite Hsp; unfold RAWCLOSE_STK; lia | rewrite Hsp; lia | exact Hm4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (ubs2_cgif_raw_close API IMG _ _ _ _ _ (cg_raw s) (raw_vals g s) g (cgif_vals s) restR HPRE1);
[ | | reflexivity | reflexivity | exact Hobj1 | reflexivity | reflexivity | exact HBr ].
+ rewrite Hm10, (HXn 45%nat 13%nat _ eq_refl eq_refl). reflexivity.
+ eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |].
intros i Hi. cbn [ms_mem mkst] in *. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJc & HP & HB2).
exists L2, A2, regs2, mem2, md2. split; [rewrite Hm1; reflexivity|]. split; [exact HJc|]. split; [exact HP | exact HB2].
- intros a Ha. apply inFP_cons in Ha. destruct Ha as [Ha|Ha]; [| exfalso; exact (inFP_nil a Ha)].
split; [| apply HFPlow]; (apply (HFPin (cg_raw s) RAW_SIZE a); [right; left; reflexivity | lia]). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HB2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|].
pose proof HJc2 as (_ & _ & Hhi2 & Hkeep2 & _). rewrite Hsp in Hhi2. split; [| exact Hhi2].
intros b n i Hbn Hi.
pose proof (heap_sep_perm _ _ LAWS Lc Ac _ mdc (cg_raw s, RAW_SIZE) _ (b, n) HH0 HBr Hbn) as Hs. cbn [fst snd] in Hs.
apply (Hkeep2 b n i); [eapply blocks_perm_in; [exact HBr | right; exact Hbn] | eapply blocks_perm_in; [exact HB2 |] | exact Hi |].
{ destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn]. }
intros Hin. apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [lia | exact (inFP_nil _ Hin)]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HB2 & Hkg & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hkg, Hhi2, HJ2.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
jafter_call_keep HS 55%nat regs2 mem2 HP2 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | unfold RAWCLOSE_STK; lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | cbn; intros i Hi; lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 8%nat g CGIF_SIZE); [reflexivity | exact HU8 | intros i Hi; apply (Hkg g CGIF_SIZE i ltac:(left; reflexivity) Hi) | | cbn; lia | cbn; lia].
cbn [r_wlo r_whi cl_R2]. intros i Hi. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 g CGIF_SIZE i HH2 Hgin2 ltac:(lia))). }
clear HS. rename HS2 into HS.
destruct (cg_frames s) as [|o0 [|o1 [|o2 [|]]]] eqn:Hfs; try (cbn in Hlen; discriminate Hlen).
assert (Hfm : forall f', In (Some f') [o0; o1; o2] -> In (fr_ptr f', FRAME_SIZE) restR /\ 4096 <= fr_ptr f' /\ fr_ptr f' + FRAME_SIZE <= alloc_ceiling /\ (g + CGIF_SIZE <= fr_ptr f' \/ fr_ptr f' + FRAME_SIZE <= g)).
{ intros f' Hin'.
assert (Hm' : In (fr_ptr f', FRAME_SIZE) restR) by (subst restR; apply in_app_iff; left; apply in_app_iff; right; apply frames_blocks_ptr_in; exact Hin').
split; [exact Hm'|].
destruct (blocks_range _ _ LAWS L2 A2 mem2 md2 (fr_ptr f') FRAME_SIZE HH2 ltac:(eapply blocks_perm_in; [exact HB2 | right; exact Hm'])) as [Hp0' Hp1'].
pose proof (heap_sep_perm _ _ LAWS L2 A2 mem2 md2 (g, CGIF_SIZE) _ (fr_ptr f', FRAME_SIZE) HH2 HB2 Hm') as Hs'. cbn [fst snd] in Hs'. lia. }
jrun LAWS ubs2tbl_ok HS HJ2. { wr_cl HU2 HU8 Hgin2 HFPin. }
jbranch ubs2tbl HS; clear Hc.
-
jrun_to LAWS ubs2tbl_ok HS HJ2 CL_FREE. { wr_cl HU2 HU8 Hgin2 HFPin. }
cgif_obj_now_at 1%nat 2%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end. rewrite <- cgif_vals_split in Hobj2.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_free0 L A mem md regs0 rg L2 A2 mm md2 g N s rest FP o0 o1 o2) end.
+ exact HJ2. + exact Hra0. + exact Htp0. + exact Hal16. + exact Hfs. + exact HFPin. + exact HFPlow.
+ eapply Permutation_trans; [exact HB2|]. subst restR. rewrite <- app_assoc. apply Permutation_refl.
+ exact Hobj2.
+ intros f' Hin'. destruct (Hfm f' Hin') as (Hm' & Hp0' & Hp1' & Hs').
eapply obj_at_transport_range; [apply Hfrs; rewrite ?Hfs; exact Hin' | exact (proj1 LAY_Frame_ok) |].
intros i Hi. cbn [ms_mem mkst] in *.
mb_frame_with HF1 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia).
mb_frame_with HF0 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia).
rewrite (Hkg (fr_ptr f') FRAME_SIZE i ltac:(right; exact Hm') Hi).
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity.
+ unfold cl_saved_ok;
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv - 48 + (48 - dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 40 (SOff 49 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW49, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 32 (SOff 50 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW50, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 24 (SOff 51 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW51, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 16 (SOff 52 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW52, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 8 (SOff 53 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW53, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 0 (SOff 54 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW54, Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
+ reg_nowF HS ltac:(rewrite HU2; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ unfold cl_untouched; repeat match goal with |- _ /\ _ => split end;
[ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27) ].
-
jrun_to LAWS ubs2tbl_ok HS HJ2 CL_FREE. { wr_cl HU2 HU8 Hgin2 HFPin. }
cgif_obj_low_at 1%nat 2%nat HS HU8 HXn Rg s 59%nat.
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ [?cc; _]) |- _ => rename Hx into Hobj2; set (c := cc) in Hobj2 end.
rewrite <- (cgif_vals_set_cur s c) in Hobj2.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_free0 L A mem md regs0 rg L2 A2 mm md2 g N (set_cur s c) rest FP o0 o1 o2) end.
+ exact HJ2. + exact Hra0. + exact Htp0. + exact Hal16. + exact Hfs. + exact HFPin. + exact HFPlow.
+ eapply Permutation_trans; [exact HB2|]. subst restR. rewrite <- app_assoc. apply Permutation_refl.
+ exact Hobj2.
+ intros f' Hin'. destruct (Hfm f' Hin') as (Hm' & Hp0' & Hp1' & Hs').
eapply obj_at_transport_range; [apply Hfrs; rewrite ?Hfs; exact Hin' | exact (proj1 LAY_Frame_ok) |].
intros i Hi. cbn [ms_mem mkst] in *.
mb_frame_with HF1 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia).
mb_frame_with HF0 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia).
rewrite (Hkg (fr_ptr f') FRAME_SIZE i ltac:(right; exact Hm') Hi).
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity.
+ unfold cl_saved_ok;
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv - 48 + (48 - dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 40 (SOff 49 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW49, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 32 (SOff 50 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW50, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 24 (SOff 51 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW51, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 16 (SOff 52 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW52, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 8 (SOff 53 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW53, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 0 (SOff 54 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW54, Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
+ reg_nowF HS ltac:(rewrite HU2; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ unfold cl_untouched; repeat match goal with |- _ /\ _ => split end;
[ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27) ].
Qed.
End S.
End q.
