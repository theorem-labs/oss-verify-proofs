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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YN3b YI06 YI5b YI09 YI08 YI0r
YI1w YI4l YI21 YI5o YI5l YI6b YL0g
YI16 YI17 YI14 YI18 YI1a YI5c YI00 YI3u YI22 YI2u YI0l YI5m
YI5a YI23 YI0a YL00 YI05 YI5n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5f YI5e YI5h YI5j.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ss_lnchk : sstate :=
mkSS L_NCHK sr_atoms
[ YP09.mkRegion (Some 2%nat) 8 192 8 192
([mkChunk 8 (CVal 8 (SOff 42 0)); mkChunk 16 (CVal 8 (SOff 43 0)); mkChunk 24 (CVal 8 (SOff 44 0))]
++ obj_chunks_gen (lay_shift 64 LAY_Config) 45 lits_Config0 ++ saved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK - 192) (2^63 - 192) 4);
(20%nat, mkAF 0 65535 0); (21%nat, mkAF 0 65535 0);
(42%nat, mkAF 0 CEIL_MAX 0); (43%nat, mkAF 0 CEIL_MAX 0); (44%nat, mkAF 0 CEIL_MAX 0) ] [] []).
Definition ss_lnchk_c : sstate := Eval vm_compute in ss_lnchk.
Definition L_CPYRET : Z := Eval vm_compute in (src0_A_LLVMFuzzerTestOneInput + 0x1e4).
Definition L_PALFREE : Z := Eval vm_compute in (src0_A_LLVMFuzzerTestOneInput + 0x208).
Definition ss_lfree : sstate :=
mkSS L_PALFREE sr_atoms
[ YP09.mkRegion (Some 2%nat) 8 192 8 192 (saved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK - 192) (2^63 - 192) 4) ] [] []).
Lemma garr8_skipn : forall m p (P : list Z) (c : nat),
garr8 src0segs m p P -> garr8 src0segs m (p + Z.of_nat c) (skipn c P).
Proof.
intros m p P c H. destruct (Nat.le_gt_cases c (length P)) as [Hc|Hc].
- rewrite <- (firstn_skipn c P) in H. apply garr8_app in H as [_ H2]. rewrite firstn_length_le in H2 by exact Hc. exact H2.
- rewrite skipn_all2 by lia. apply garr8_nil.
Qed.
Lemma garr8_firstn : forall m p (l : list Z) (n : nat), garr8 src0segs m p l -> garr8 src0segs m p (firstn n l).
Proof. intros m p l n H. rewrite <- (firstn_skipn n l) in H. apply garr8_app in H as [H1 _]. exact H1. Qed.
Lemma garr8_copy : forall m m' s d (l : list Z),
garr8 src0segs m s l -> (forall i, 0 <= i < Z.of_nat (length l) -> mbyte src0segs m' (d + i) = mbyte src0segs m (s + i)) ->
garr8 src0segs m' d l.
Proof.
intros m m' s d l H Hc j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. replace (d + Z.of_nat j + Z.of_nat k) with (d + (Z.of_nat j + Z.of_nat k)) by lia.
rewrite Hc by (cbn in Hk; lia). replace (s + (Z.of_nat j + Z.of_nat k)) with (s + Z.of_nat j + Z.of_nat k) by lia. apply Hv. exact Hk.
Qed.
Lemma garr8_slice_copy : forall m m' p (P : list Z) d c n,
garr8 src0segs m p P -> 0 <= c -> 0 <= n -> c + n <= Z.of_nat (length P) ->
(forall i, 0 <= i < n -> mbyte src0segs m' (d + i) = mbyte src0segs m (p + c + i)) ->
garr8 src0segs m' d (firstn (Z.to_nat n) (skipn (Z.to_nat c) P)) /\ Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat c) P))) = n.
Proof.
intros m m' p P d c n H Hc Hn Hcn Hcp.
assert (Hlen : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat c) P))) = n) by (rewrite length_firstn, length_skipn; lia).
split; [|exact Hlen]. eapply garr8_copy.
- apply garr8_firstn. apply (garr8_skipn m p P (Z.to_nat c)). exact H.
- intros i Hi. rewrite Hlen in Hi. rewrite Hcp by lia. f_equal. lia.
Qed.
Lemma U_or_zero : forall E e1 e2, U E (SAlu ALU_OR e1 e2) = 0 -> U E e1 = 0 /\ U E e2 = 0.
Proof.
intros E e1 e2 H. rewrite U_SAlu in H. cbn [zalu_raw] in H. pose proof (U_range E e1) as R1. pose proof (U_range E e2) as R2.
unfold M64 in R1, R2. rewrite zcanon_id in H by (unfold M64; apply Z_lor_range; lia). apply Z.lor_eq_0_iff. exact H.
Qed.
Lemma U_or_zero_intro : forall E e1 e2, U E e1 = 0 -> U E e2 = 0 -> U E (SAlu ALU_OR e1 e2) = 0.
Proof. intros E e1 e2 H1 H2. rewrite U_SAlu. cbn [zalu_raw]. rewrite H1, H2. reflexivity. Qed.
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Hypothesis CLOSE : close_specX API.
Hypothesis ADDF : addframe_specX API.
Hypothesis UNLINK : unlink_x src0_msyms MR src0_A_unlink.
Hypothesis RFC : rfc_specX API.
Hypothesis NEWGIF : newgif_x API.
Variables (regs0 : bvmap 5 word) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (b0 : rbound) (plen : Z) (K : lleaf -> TSet).
Hypothesis HSORT : Fs.fs_sorted (m_fs md) = true.
Hypothesis HK : forall fs' c', leaf_post API regs0 L A mem md (ff_delta plen b0) fs' c' -> realizes src0segs c' (K (LL 0 fs' [])).
Hypothesis HROOM : ff_room b0 plen.
Hypothesis HFD : fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None.
Lemma llvm_freeret_x :
forall (regs1 : bvmap 5 word) Lc Ac memc mdc (q m : Z) (bc : rbound),
journal src0_msyms MR LIB_STACK (spZ regs0) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp src0_msyms) -> spZ regs0 mod 16 = 0 ->
((q = 0 /\ forall b, In b (blocks L A) -> In b (blocks Lc Ac)) \/
(Permutation (blocks Lc Ac) ((q, m) :: blocks L A) /\ (In (q, m) (blocks L A) -> m <= 0))) ->
saved_ok memc (spZ regs0) regs0 ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 192) -> getr regs1 18 = Z_to_bv 64 q -> untouched_ok regs0 regs1 ->
sink_none src0_msyms mem md ->
res_ok Ac bc -> rb_le bc (ff_delta plen b0) ->
realizes src0segs (mkCfg (mkst regs1 (Z_to_bv 64 L_PALFREE) memc (seg_rom src0segs)) mdc) (K (LL 0 (m_fs md) [])).
Proof.
intros regs1 Lc Ac memc mdc q m bc HJ Hid Hra0 Htp0 Hal16 Hq HSV G2 G18 (G3 & G4 & G25 & G26 & G27) HSN0 HRES HBLE.
apply realizes_via_SR.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK = 16384) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 192) mod 16 = 0) by (replace (sp0 - 192) with (sp0 + (-12) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
set (E := Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW36 : ew E 36 = getr regs0 19) by (etransitivity; [apply (HSV' 4%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW37 : ew E 37 = getr regs0 20) by (etransitivity; [apply (HSV' 5%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW38 : ew E 38 = getr regs0 21) by (etransitivity; [apply (HSV' 6%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW39 : ew E 39 = getr regs0 22) by (etransitivity; [apply (HSV' 7%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW40 : ew E 40 = getr regs0 23) by (etransitivity; [apply (HSV' 8%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW41 : ew E 41 = getr regs0 24) by (etransitivity; [apply (HSV' 9%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 192) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
pose proof HSV as (W1 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24).
assert (HS : st_ok src0segs E ss_lfree (mkst regs1 (Z_to_bv 64 L_PALFREE) memc (seg_rom src0segs))).
{ unfold ss_lfree. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : Z), nth_error (saved_vals regs0) j = Some w -> word_mem src0segs memc (sp0 - 192 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok src0segs (Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ [])) memc (sp0 - 192) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HSV' j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold saved_chunks. cbn [Nat.add].
repeat (apply Forall_cons;
[ first [ apply (CK 184 0%nat _ eq_refl); [replace (sp0 - 192 + 184) with (sp0 - 8) by lia; exact W1 | apply u64_range']
| apply (CK 176 1%nat _ eq_refl); [replace (sp0 - 192 + 176) with (sp0 - 16) by lia; exact W8 | apply u64_range']
| apply (CK 168 2%nat _ eq_refl); [replace (sp0 - 192 + 168) with (sp0 - 24) by lia; exact W9 | apply u64_range']
| apply (CK 160 3%nat _ eq_refl); [replace (sp0 - 192 + 160) with (sp0 - 32) by lia; exact W18 | apply u64_range']
| apply (CK 152 4%nat _ eq_refl); [replace (sp0 - 192 + 152) with (sp0 - 40) by lia; exact W19 | apply u64_range']
| apply (CK 144 5%nat _ eq_refl); [replace (sp0 - 192 + 144) with (sp0 - 48) by lia; exact W20 | apply u64_range']
| apply (CK 136 6%nat _ eq_refl); [replace (sp0 - 192 + 136) with (sp0 - 56) by lia; exact W21 | apply u64_range']
| apply (CK 128 7%nat _ eq_refl); [replace (sp0 - 192 + 128) with (sp0 - 64) by lia; exact W22 | apply u64_range']
| apply (CK 120 8%nat _ eq_refl); [replace (sp0 - 192 + 120) with (sp0 - 72) by lia; exact W23 | apply u64_range']
| apply (CK 112 9%nat _ eq_refl); [replace (sp0 - 192 + 112) with (sp0 - 80) by lia; exact W24 | apply u64_range'] ] | ]).
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. repeat split; try lia; exact Hspm. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 L_PALFREE) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ src0_A_free.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hc10. rewrite (HE 18%nat 18%bv eq_refl), G18 in Hc10.
jreg HS (2%bv:reg) as Hc2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hc2.
jreg HS (4%bv:reg) as Hc4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hc4.
jreg HS (1%bv:reg) as Hc1.
lazymatch goal with |- SR _ (mkCfg ?msq ?mdq) _ =>
eapply SR_bind with (R := fun c' => exists L6 A6 regs6 mem6 md6,
c' = mkCfg (mkst regs6 (Z_to_bv 64 L_RET0) mem6 (seg_rom src0segs)) md6 /\
journal src0_msyms MR LIB_STACK sp0 [] L A mem md L6 A6 mem6 md6 /\ st_init_done A6 = true /\
regs_preserved (ms_regs msq) regs6 /\ (forall b, In b (blocks L A) -> In b (blocks L6 A6)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 192 - ALLOC_STACK <= x < sp0 - 192) ->
mbyte src0segs mem6 x = mbyte src0segs (ms_mem msq) x /\ (writable_at src0segs (ms_mem msq) x <-> writable_at src0segs mem6 x)) /\
res_ok A6 bc)
end.
{ destruct Hq as [(-> & Hbase) | (HBq & Hfresh)].
- destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_mono; [eapply (jfree_null _ (aa_free_null API)); [exact HS | reflexivity | reflexivity | exact Hh | exact Hl | exact Hc10 | exact Hc1 | apply ret_ok_even; vm_compute; reflexivity] |].
intros c' ->. lazymatch goal with |- context [mkst (ms_regs ?m0) _ (ms_mem _) _] => exists Lc, Ac, (ms_regs m0), (ms_mem m0), mdc end.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hid|]. split; [intros rr _; reflexivity|].
split; [exact Hbase|]. split; [intros x _ _; split; [reflexivity | tauto] | exact HRES].
- assert (Hqin : In (q, m) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HBq | left; reflexivity]).
eapply SR_mono.
{ eapply (jfree_at_res API IMG) with (a := q) (n := m) (spc := sp0 - 192);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hqin | exact HRES | exact Hc10
| exact Hc2 | lia | exact Hspm | lia | lia | exact Hc4 | exact Hc1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hin i Hi. exfalso. pose proof (Hfresh Hin). lia. }
intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hrm6 & Hkeep6 & Hhi6 & Hid6 & HR6).
exists L6, A6, regs6, mem6, md6. split; [reflexivity|]. split; [exact HJ6|]. split; [exact Hid6|]. split; [exact HP6|].
split; [| split; [exact Hhi6 | eapply res_ok_mono; [apply rb_free_le | exact HR6]]].
intros b Hb. pose proof (perm_after_rm1 _ _ _ _ HBq Hrm6) as HP. eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hb]. }
cbv beta. intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & Hid6 & HP6 & Hbase6 & Hhi6 & HR6'). clear HJ.
cbn [ms_regs ms_mem mkst] in HP6, Hhi6.
jafter_call_keep HS 42%nat regs6 mem6 HP6 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
{ constructor; [|constructor].
eapply (region_kept_stack src0segs _ _ _ 2); [exact HU2 | exact Hhi6 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS src0tbl_ok HS HJ6.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
eapply (SR_ret_at src0segs src0tbl); [exact src0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ6))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ6)))). }
apply HK. unfold leaf_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists L6, A6, (ms_regs msf), (ms_mem msf), md6 end.
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg src0segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|nat_lt_lit]); rewrite ?Z.add_0_r, HW32, Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end. }
split; [exact (journal_nil_token API _ _ _ _ _ _ _ _ _ _ HJ6)|].
split.
{ apply regs_preserved_intro; cbn [ms_regs mkst].
- reg_nowF HS ltac:(rewrite HU2; replace (sp0 - 192 + 192) with sp0 by lia; subst sp0; unfold spZ; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
- reg_nowF HS ltac:(rewrite HW33; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW34; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW35; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW36; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW37; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW38; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW39; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW40; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW41; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27). }
split; [exact Hid6|].
split; [reg_nowF HS ltac:(reflexivity)|].
split; [exact (nil_sink_none API _ _ _ _ _ _ _ _ _ _ HJ6 HSN0)|].
split; [exact Hbase6|].
split; [exact (nil_fs API _ _ _ _ _ _ _ _ _ _ HJ6)|].
eapply res_ok_mono; [exact HBLE | exact HR6'].
Qed.
Lemma denot_mulHW : forall E nh nw H W,
ew E nh = Z_to_bv 64 H -> ew E nw = Z_to_bv 64 W -> 0 <= H < 65536 -> 0 <= W < 65536 ->
sv_denot E (SMd M_MUL (SOff nh 0) (SOff nw 0)) = Z_to_bv 64 (W * H).
Proof.
intros E nh nw H W Hh Hw RH RW. rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E nh H Hh), (U_atom E nw W Hw) by lia. rewrite zcanon_id by (unfold M64; nia). lia.
Qed.
Lemma llvm_nchk_x :
forall (regs1 : bvmap 5 word) Lc Ac memc mdc
(pdata nb cur pal0 attr gen W H ngp : Z) (PAYLOAD GPAL : list Z) (bc : rbound),
journal src0_msyms MR LIB_STACK (spZ regs0) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp src0_msyms) -> spZ regs0 mod 16 = 0 ->
In (pdata, nb) (blocks L A) -> 0 < nb ->
Permutation (blocks Lc Ac) ((if Z.land attr 4 =? 0 then [(pal0, 3 * ngp)] else []) ++ blocks L A) ->
(Z.land attr 4 <> 0 -> pal0 = 0) ->
(In (pal0, 3 * ngp) (blocks L A) -> 3 * ngp <= 0) ->
obj_at src0segs memc (spZ regs0 - 128) LAY_Config [pal0; 0; attr; gen; W; H; ngp; 0; 0; 0] ->
saved_ok memc (spZ regs0) regs0 ->
word_mem src0segs memc (spZ regs0 - 184) pdata -> word_mem src0segs memc (spZ regs0 - 176) nb ->
word_mem src0segs memc (spZ regs0 - 168) cur -> 0 <= cur <= nb ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 192) -> getr regs1 18 = Z_to_bv 64 pal0 ->
getr regs1 20 = Z_to_bv 64 W -> getr regs1 21 = Z_to_bv 64 H ->
untouched_ok regs0 regs1 ->
sink_none src0_msyms mem md -> spZ regs0 <= 2 ^ 47 ->
garr8 src0segs mem pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb ->
hdr5 PAYLOAD = (false, (W, H, attr, gen, ngp), skipn 14 PAYLOAD) ->
cur = 14 + (if Z.land attr 4 =? 0 then 3 * ngp else 0) ->
(Z.land attr 4 = 0 -> 14 + 3 * ngp <= Z.of_nat (length PAYLOAD) /\ GPAL = firstn (Z.to_nat (3 * ngp)) (skipn 14 PAYLOAD)) ->
(Z.land attr 4 <> 0 -> GPAL = []) ->
(Z.land attr 4 = 0 -> garr8 src0segs memc pal0 GPAL /\ Z.of_nat (length GPAL) = 3 * ngp) ->
res_ok Ac bc -> rb_le bc (main_bud b0) ->
realizes src0segs (mkCfg (mkst regs1 (Z_to_bv 64 L_NCHK) memc (seg_rom src0segs)) mdc) (ff_tree K (m_fs md) PAYLOAD).
Proof.
intros regs1 Lc Ac memc mdc pdata nb cur pal0 attr gen W H ngp PAYLOAD GPAL bc
HJ Hid Hra0 Htp0 Hal16 Hpd Hnb HB Hpal00 Hpalfresh Hcfg HSV Wp Wn Wc Hcur G2 G18 G20 G21 HUT
HSN0 Hsp47 HPL HPLn HHDR HcurV HGPs HGPn HGP HRES HBLE.
apply realizes_via_SR.
pose proof HUT as (G3 & G4 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK = 16384) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 192) mod 16 = 0) by (replace (sp0 - 192) with (sp0 + (-12) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. exact Hpd. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH0 Hpdc) as [Hp0 Hp1].
pose proof (obj_at_range _ _ _ _ _ Hcfg) as Rcfg.
pose proof (Rcfg 4%nat W eq_refl) as RW. pose proof (Rcfg 5%nat H eq_refl) as RH. pose proof (Rcfg 6%nat ngp eq_refl) as RN. cbn in RW, RH, RN.
assert (Hpr : Z.land attr 4 = 0 -> 4096 <= pal0 /\ pal0 + 3 * ngp <= alloc_ceiling).
{ intros Hz. eapply (blocks_range _ _ LAWS); [exact HH0|]. eapply Permutation_in; [apply Permutation_sym; exact HB|]. rewrite (proj2 (Z.eqb_eq _ _) Hz). left. reflexivity. }
set (cvals := [pal0; 0; attr; gen; W; H; ngp; 0; 0; 0]) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur] ++ cvals) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HY : forall j v, nth_error ([pdata; nb; cur] ++ cvals) j = Some v -> ew E (42 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (42 + j)%nat with (32 + (length (saved_vals regs0) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HCV : forall j v, nth_error cvals j = Some v -> ew E (45 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (45 + j)%nat with (42 + (3 + j))%nat by lia. apply HY. exact Hj. }
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW36 : ew E 36 = getr regs0 19) by (etransitivity; [apply (HSV' 4%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW37 : ew E 37 = getr regs0 20) by (etransitivity; [apply (HSV' 5%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW38 : ew E 38 = getr regs0 21) by (etransitivity; [apply (HSV' 6%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW39 : ew E 39 = getr regs0 22) by (etransitivity; [apply (HSV' 7%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW40 : ew E 40 = getr regs0 23) by (etransitivity; [apply (HSV' 8%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW41 : ew E 41 = getr regs0 24) by (etransitivity; [apply (HSV' 9%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 192) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HE18 : ew E 18 = Z_to_bv 64 pal0) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE20 : ew E 20 = Z_to_bv 64 W) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HE21 : ew E 21 = Z_to_bv 64 H) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (HX42 : ew E 42 = Z_to_bv 64 pdata) by (apply (HY 0%nat); reflexivity).
assert (HX43 : ew E 43 = Z_to_bv 64 nb) by (apply (HY 1%nat); reflexivity).
assert (HX44 : ew E 44 = Z_to_bv 64 cur) by (apply (HY 2%nat); reflexivity).
pose proof HSV as (W1 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24).
assert (HS : st_ok src0segs E ss_lnchk_c (mkst regs1 (Z_to_bv 64 L_NCHK) memc (seg_rom src0segs))).
{ change ss_lnchk_c with ss_lnchk. unfold ss_lnchk. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_app; split; [|apply Forall_app; split].
+ apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX42, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 192 + 8) with (sp0 - 184) by lia; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX43, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 192 + 16) with (sp0 - 176) by lia; apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX44, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 192 + 24) with (sp0 - 168) by lia; apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+ eapply (obj_chunks_gen_ok src0segs _ _ (sp0 - 192) _ cvals 45 lits_Config0); [| reflexivity | | apply lits_Config0_ok].
* apply (proj1 (obj_at_shift _ _ (sp0 - 192) 64 LAY_Config cvals)). replace (sp0 - 192 + 64) with (sp0 - 128) by lia. exact Hcfg.
* intros j v Hj. apply (HCV j v Hj).
+ assert (CK : forall off j (w : Z), nth_error (saved_vals regs0) j = Some w -> word_mem src0segs memc (sp0 - 192 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok src0segs (Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur] ++ cvals) ++ [])) memc (sp0 - 192) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HSV' j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold saved_chunks. cbn [Nat.add].
repeat (apply Forall_cons;
[ first [ apply (CK 184 0%nat _ eq_refl); [replace (sp0 - 192 + 184) with (sp0 - 8) by lia; exact W1 | apply u64_range']
| apply (CK 176 1%nat _ eq_refl); [replace (sp0 - 192 + 176) with (sp0 - 16) by lia; exact W8 | apply u64_range']
| apply (CK 168 2%nat _ eq_refl); [replace (sp0 - 192 + 168) with (sp0 - 24) by lia; exact W9 | apply u64_range']
| apply (CK 160 3%nat _ eq_refl); [replace (sp0 - 192 + 160) with (sp0 - 32) by lia; exact W18 | apply u64_range']
| apply (CK 152 4%nat _ eq_refl); [replace (sp0 - 192 + 152) with (sp0 - 40) by lia; exact W19 | apply u64_range']
| apply (CK 144 5%nat _ eq_refl); [replace (sp0 - 192 + 144) with (sp0 - 48) by lia; exact W20 | apply u64_range']
| apply (CK 136 6%nat _ eq_refl); [replace (sp0 - 192 + 136) with (sp0 - 56) by lia; exact W21 | apply u64_range']
| apply (CK 128 7%nat _ eq_refl); [replace (sp0 - 192 + 128) with (sp0 - 64) by lia; exact W22 | apply u64_range']
| apply (CK 120 8%nat _ eq_refl); [replace (sp0 - 192 + 120) with (sp0 - 72) by lia; exact W23 | apply u64_range']
| apply (CK 112 9%nat _ eq_refl); [replace (sp0 - 192 + 112) with (sp0 - 80) by lia; exact W24 | apply u64_range'] ] | ]).
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE20, HE21, HX42, HX43, HX44, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 L_NCHK) memc (seg_rom src0segs))) in HJ.
jrun LAWS src0tbl_ok HS HJ.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jbranch src0tbl HS.
-
rewrite branch_ltu_U, U_lit in Hc by lia.
lazymatch type of Hc with (U ?E1 ?e <? _) = true => rewrite <- (denot_lit_U E1 e) in Hc || idtac end.
assert (HWH : W * H <= 100000000).
{ revert Hc. unfold U. rewrite (denot_mulHW E 21 20 H W HE21 HE20) by lia. rewrite unsigned_lit_small by nia.
intros Hc. destruct (Z.ltb_spec (W * H) 100000001); [lia | discriminate Hc]. }
clear Hc.
jrun_to LAWS src0tbl_ok HS HJ L_MAIN.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
unfold ff_tree. rewrite (ff_cfg_of_walk PAYLOAD W H attr gen ngp GPAL cur HHDR HWH HcurV ltac:(clear - RN; lia) HGPs HGPn).
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_main_x API IMG CLOSE ADDF UNLINK RFC NEWGIF regs0 L A mem md b0 plen K HSORT HK HROOM HFD rg Lc Ac mm mdc pdata nb cur pal0 attr gen W H ngp PAYLOAD GPAL bc) end.
+ exact HJ. + exact Hid. + exact Hra0. + exact Htp0. + exact Hal16. + exact Hpd. + exact Hnb. + exact HB. + exact Hpal00. + exact Hpalfresh. + exact HWH.
+ fold sp0. replace (sp0 - 128) with (sp0 - 192 + 64) by lia. apply (proj2 (obj_at_shift _ _ (sp0 - 192) 64 LAY_Config _)).
eapply (st_obj_at src0segs _ _ _ 0%nat _ 2%nat (sp0 - 192) _ _ 45 lits_Config0 HS eq_refl eq_refl HU2);
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ].
intros j v Hj. split; [rewrite nth_lay_shift_snd; exact (Rcfg j v Hj)|].
assert (Hlj : (j < 10)%nat) by (destruct (Nat.lt_ge_cases j 10) as [Hl|Hl]; [exact Hl|]; rewrite (proj2 (nth_error_None [pal0; 0; attr; gen; W; H; ngp; 0; 0; 0] j) Hl) in Hj; discriminate).
do 10 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [nth_error lits_Config0]; first [reflexivity | apply HCV; reflexivity] |]). exfalso; lia.
+ fold sp0. saved_ok_tac HS HU2 HW32 HW33 HW34 HW35 HW36 HW37 HW38 HW39 HW40 HW41.
+ fold sp0. stack_word HS HU2 42%nat HX42. lia.
+ fold sp0. stack_word HS HU2 43%nat HX43. lia.
+ fold sp0. stack_word HS HU2 44%nat HX44. lia.
+ exact Hcur.
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 8%bv HS) as T; eval_sr_get_in T;
rewrite (denot_mulHW _ 21 20 H W HE21 HE20) in T by lia; exact T end.
+ reg_nowF HS ltac:(rewrite HE18, Z_to_bv_bv_unsigned; reflexivity).
+ split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)|].
reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
+ exact HSN0. + exact Hsp47. + exact HPL. + exact HPLn. + exact HHDR. + exact HcurV. + lia. + exact HGPs. + exact HGPn.
+ intros Hz. destruct (HGP Hz) as [HGPm HGPl]. destruct (Hpr Hz) as [Hq0 Hq1]. split; [|exact HGPl].
eapply garr8_frame; [exact HGPm|]. intros a Ha. rewrite HGPl in Ha. fold sp0. cbn [ms_mem mkst] in *.
mem_back ltac:(rewrite ?HU2) ltac:(clear - Ha Hq0 Hq1 Hac Hsp0al Hstk0 Hceil Hsp063 HLSv; lia).
+ exact HRES. + exact HBLE.
-
rewrite branch_ltu_U, U_lit in Hc by lia.
lazymatch type of Hc with (U ?E1 ?e <? _) = false => rewrite <- (denot_lit_U E1 e) in Hc || idtac end.
assert (HWH : 100000000 < W * H).
{ revert Hc. unfold U. rewrite (denot_mulHW E 21 20 H W HE21 HE20) by lia. rewrite unsigned_lit_small by nia.
intros Hc. destruct (Z.ltb_spec (W * H) 100000001); [discriminate Hc | lia]. }
clear Hc.
jrun_to LAWS src0tbl_ok HS HJ L_PALFREE.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
unfold ff_tree. rewrite (ff_cfg_too_large PAYLOAD W H attr gen ngp HHDR HWH). unfold ff_leaf.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_freeret_x rg Lc Ac mm mdc pal0 (3 * ngp) bc) end.
+ exact HJ. + exact Hid. + exact Hra0. + exact Htp0. + exact Hal16.
+ destruct (Z.eqb_spec (Z.land attr 4) 0) as [Hz|Hz].
* right. split; [exact HB | exact Hpalfresh].
* left. split; [apply Hpal00; exact Hz|]. intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HB | exact Hb].
+ fold sp0. saved_ok_tac HS HU2 HW32 HW33 HW34 HW35 HW36 HW37 HW38 HW39 HW40 HW41.
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(rewrite HE18, Z_to_bv_bv_unsigned; reflexivity).
+ split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)|].
reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
+ exact HSN0.
+ exact HRES. + apply (main_bud_fin b0 plen). exact HBLE.
Qed.
Definition ss_ltail : sstate :=
mkSS L_TAIL sr_atoms
[ YP09.mkRegion (Some 2%nat) 8 192 8 192
([mkChunk 8 (CVal 8 (SOff 42 0)); mkChunk 16 (CVal 8 (SOff 43 0))]
++ obj_chunks_gen (lay_shift 64 LAY_Config) 45 lits_Config0 ++ saved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK - 192) (2^63 - 192) 4);
(8%nat, mkAF 1 CEIL_MAX 0); (9%nat, mkAF 4096 CEIL_MAX 0);
(19%nat, mkAF 0 196605 0); (20%nat, mkAF 0 65535 0); (21%nat, mkAF 0 65535 0); (23%nat, mkAF 0 CEIL_MAX 0);
(42%nat, mkAF 4096 CEIL_MAX 0); (43%nat, mkAF 1 CEIL_MAX 0) ] [] []).
Lemma denot_add_atoms : forall E a b x y,
ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= x + y < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (x + y).
Proof.
intros E a b x y Ha Hb Hx Hy Hxy. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E a x Ha), (U_atom E b y Hb) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Ltac untouched_tac HS HE G3 G4 G25 G26 G27 :=
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)|];
reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
Ltac stack_word_e HS HU2 e tac :=
lazymatch goal with |- word_mem _ _ (?spv - ?dd) ?v =>
replace (spv - dd) with (spv - 192 + (192 - dd)) by lia;
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (192 - dd) e (spv - 192) v HS);
[ reflexivity | reflexivity | cbv; auto 60 | ew_havocA; exact HU2 | tac | ]
end.
Ltac config_obj_tac HS HU2 e0 tac0 Rcfg HCV :=
lazymatch goal with |- obj_at ?sg ?m (?spv - 128) LAY_Config (?v0 :: ?vs) =>
change (obj_at sg m (spv - 128) LAY_Config (v0 :: vs)) with (field_ok sg m (spv - 128) (0, 8%N) v0 /\ obj_at sg m (spv - 128) (tl LAY_Config) vs);
split;
[ unfold field_ok; cbn [fst snd]; split;
[ apply val_mem_word_mem; rewrite Z.add_0_r; stack_word_e HS HU2 e0 tac0; lia | lia ]
| replace (spv - 128) with (spv - 192 + 64) by lia; apply (proj2 (obj_at_shift _ _ (spv - 192) 64 (tl LAY_Config) _));
change (lay_shift 64 (tl LAY_Config)) with (tl (lay_shift 64 LAY_Config));
eapply (st_obj_at sg _ _ _ 0%nat _ 2%nat (spv - 192) _ _ 46 (tl lits_Config0) HS eq_refl eq_refl ltac:(ew_havocA; exact HU2));
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ];
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; split; [change (tl (lay_shift 64 LAY_Config)) with (lay_shift 64 (tl LAY_Config)); rewrite nth_lay_shift_snd;
change (nth j (tl LAY_Config) (0, 8%N)) with (nth (Datatypes.S j) LAY_Config (0, 8%N)); exact (Rcfg (Datatypes.S j) v Hj) |];
do 9 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [nth_error lits_Config0 tl]; first [reflexivity | ew_havocA; apply HCV; reflexivity] |]);
exfalso; destruct j; cbn in Hj; discriminate Hj ]
end.
Lemma llvm_tail_x :
forall (regs1 : bvmap 5 word) Lc Ac memc mdc
(pdata nb cur0 cur1 flag attr gen W H ngp r1 r2 : Z) (PAYLOAD : list Z),
journal src0_msyms MR LIB_STACK (spZ regs0) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp src0_msyms) -> spZ regs0 mod 16 = 0 ->
In (pdata, nb) (blocks L A) -> 0 < nb ->
Permutation (blocks Lc Ac) (blocks L A) ->
flag = (if Z.land attr 4 =? 0 then 1 else 0) ->
obj_at src0segs memc (spZ regs0 - 128) LAY_Config [0; 0; attr; gen; W; H; ngp; 0; 0; 0] ->
saved_ok memc (spZ regs0) regs0 ->
word_mem src0segs memc (spZ regs0 - 184) pdata -> word_mem src0segs memc (spZ regs0 - 176) nb ->
0 <= cur1 <= nb ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 192) -> getr regs1 8 = Z_to_bv 64 nb -> getr regs1 9 = Z_to_bv 64 pdata ->
getr regs1 10 = Z_to_bv 64 flag -> getr regs1 19 = Z_to_bv 64 (3 * ngp) -> getr regs1 20 = Z_to_bv 64 W ->
getr regs1 21 = Z_to_bv 64 H -> getr regs1 23 = Z_to_bv 64 cur1 ->
untouched_ok regs0 regs1 ->
getr regs1 11 = Z_to_bv 64 r1 -> getr regs1 12 = Z_to_bv 64 r2 -> 0 <= r1 < 2 ^ 64 -> 0 <= r2 < 2 ^ 64 ->
sink_none src0_msyms mem md -> spZ regs0 <= 2 ^ 47 ->
garr8 src0segs mem pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb ->
(r1 = 0 -> r2 = 0 -> cur1 = 14 /\ hdr5 PAYLOAD = (false, (W, H, attr, gen, ngp), skipn 14 PAYLOAD)) ->
(14 <= Z.of_nat (length PAYLOAD) -> r1 = 0 /\ r2 = 0) ->
res_ok Ac b0 ->
realizes src0segs (mkCfg (mkst regs1 (Z_to_bv 64 L_TAIL) memc (seg_rom src0segs)) mdc) (ff_tree K (m_fs md) PAYLOAD).
Proof.
intros regs1 Lc Ac memc mdc pdata nb cur0 cur1 flag attr gen W H ngp r1 r2 PAYLOAD
HJ Hid Hra0 Htp0 Hal16 Hpd Hnb HB Hflag Hcfg HSV Wp Wn Hcur1 G2 G8 G9 G10 G19 G20 G21 G23 HUT
G11 G12 Rr1 Rr2 HSN0 Hsp47 HPL HPLn HDRV HDRS HRES0.
apply realizes_via_SR.
assert (HSHORT : Z.of_nat (length PAYLOAD) < 14 -> ff_cfg PAYLOAD = None) by (intros Hsh; exact (ff_cfg_hdr_short _ (hdr5_short _ Hsh))).
pose proof HUT as (G3 & G4 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK = 16384) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 192) mod 16 = 0) by (replace (sp0 - 192) with (sp0 + (-12) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. exact Hpd. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH0 Hpdc) as [Hp0 Hp1].
pose proof (obj_at_range _ _ _ _ _ Hcfg) as Rcfg.
pose proof (Rcfg 4%nat W eq_refl) as RW. pose proof (Rcfg 5%nat H eq_refl) as RH. pose proof (Rcfg 6%nat ngp eq_refl) as RN. cbn in RW, RH, RN.
set (cvals := [0; 0; attr; gen; W; H; ngp; 0; 0; 0]) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur0] ++ cvals) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HY : forall j v, nth_error ([pdata; nb; cur0] ++ cvals) j = Some v -> ew E (42 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (42 + j)%nat with (32 + (length (saved_vals regs0) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HCV : forall j v, nth_error cvals j = Some v -> ew E (45 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (45 + j)%nat with (42 + (3 + j))%nat by lia. apply HY. exact Hj. }
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW36 : ew E 36 = getr regs0 19) by (etransitivity; [apply (HSV' 4%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW37 : ew E 37 = getr regs0 20) by (etransitivity; [apply (HSV' 5%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW38 : ew E 38 = getr regs0 21) by (etransitivity; [apply (HSV' 6%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW39 : ew E 39 = getr regs0 22) by (etransitivity; [apply (HSV' 7%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW40 : ew E 40 = getr regs0 23) by (etransitivity; [apply (HSV' 8%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW41 : ew E 41 = getr regs0 24) by (etransitivity; [apply (HSV' 9%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 192) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 nb) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE9 : ew E 9 = Z_to_bv 64 pdata) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE19 : ew E 19 = Z_to_bv 64 (3 * ngp)) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE20 : ew E 20 = Z_to_bv 64 W) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HE21 : ew E 21 = Z_to_bv 64 H) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (HE23 : ew E 23 = Z_to_bv 64 cur1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE11 : ew E 11 = Z_to_bv 64 r1) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
assert (HE12 : ew E 12 = Z_to_bv 64 r2) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (HDR0 : forall E', ew E' 11 = ew E 11 -> ew E' 12 = ew E 12 -> U E' (SAlu ALU_OR (SOff 11 0) (SOff 12 0)) = 0 ->
cur1 = 14 /\ hdr5 PAYLOAD = (false, (W, H, attr, gen, ngp), skipn 14 PAYLOAD)).
{ intros E' E11 E12 Hor. apply U_or_zero in Hor as [U11 U12].
rewrite (U_atom E' 11 r1 ltac:(rewrite E11; exact HE11) Rr1) in U11. rewrite (U_atom E' 12 r2 ltac:(rewrite E12; exact HE12) Rr2) in U12. exact (HDRV U11 U12). }
assert (HX42 : ew E 42 = Z_to_bv 64 pdata) by (apply (HY 0%nat); reflexivity).
assert (HX43 : ew E 43 = Z_to_bv 64 nb) by (apply (HY 1%nat); reflexivity).
pose proof HSV as (W1 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24).
assert (HS : st_ok src0segs E ss_ltail (mkst regs1 (Z_to_bv 64 L_TAIL) memc (seg_rom src0segs))).
{ unfold ss_ltail. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_app; split; [|apply Forall_app; split].
+ apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX42, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; replace (sp0 - 192 + 8) with (sp0 - 184) by lia; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX43, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; replace (sp0 - 192 + 16) with (sp0 - 176) by lia; exact Wn]. }
apply Forall_nil.
+ eapply (obj_chunks_gen_ok src0segs _ _ (sp0 - 192) _ cvals 45 lits_Config0); [| reflexivity | | apply lits_Config0_ok].
* apply (proj1 (obj_at_shift _ _ (sp0 - 192) 64 LAY_Config cvals)). replace (sp0 - 192 + 64) with (sp0 - 128) by lia. exact Hcfg.
* intros j v Hj. apply (HCV j v Hj).
+ assert (CK : forall off j (w : Z), nth_error (saved_vals regs0) j = Some w -> word_mem src0segs memc (sp0 - 192 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok src0segs (Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur0] ++ cvals) ++ [])) memc (sp0 - 192) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HSV' j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold saved_chunks. cbn [Nat.add].
repeat (apply Forall_cons;
[ first [ apply (CK 184 0%nat _ eq_refl); [replace (sp0 - 192 + 184) with (sp0 - 8) by lia; exact W1 | apply u64_range']
| apply (CK 176 1%nat _ eq_refl); [replace (sp0 - 192 + 176) with (sp0 - 16) by lia; exact W8 | apply u64_range']
| apply (CK 168 2%nat _ eq_refl); [replace (sp0 - 192 + 168) with (sp0 - 24) by lia; exact W9 | apply u64_range']
| apply (CK 160 3%nat _ eq_refl); [replace (sp0 - 192 + 160) with (sp0 - 32) by lia; exact W18 | apply u64_range']
| apply (CK 152 4%nat _ eq_refl); [replace (sp0 - 192 + 152) with (sp0 - 40) by lia; exact W19 | apply u64_range']
| apply (CK 144 5%nat _ eq_refl); [replace (sp0 - 192 + 144) with (sp0 - 48) by lia; exact W20 | apply u64_range']
| apply (CK 136 6%nat _ eq_refl); [replace (sp0 - 192 + 136) with (sp0 - 56) by lia; exact W21 | apply u64_range']
| apply (CK 128 7%nat _ eq_refl); [replace (sp0 - 192 + 128) with (sp0 - 64) by lia; exact W22 | apply u64_range']
| apply (CK 120 8%nat _ eq_refl); [replace (sp0 - 192 + 120) with (sp0 - 72) by lia; exact W23 | apply u64_range']
| apply (CK 112 9%nat _ eq_refl); [replace (sp0 - 192 + 112) with (sp0 - 80) by lia; exact W24 | apply u64_range'] ] | ]).
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE8, HE9, HE19, HE20, HE21, HE23, HX42, HX43, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 L_TAIL) memc (seg_rom src0segs))) in HJ.
assert (Hpal0fresh : forall n, In (0, n) (blocks L A) -> n <= 0).
{ intros n Hin. exfalso. destruct (blocks_range _ _ LAWS Lc Ac _ mdc 0 n HH0 ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | exact Hin])) as [H0 _]. lia. }
destruct (Z.eqb_spec (Z.land attr 4) 0) as [Hattr4|Hattr4]; subst flag.
-
pin_reg HS (10%bv:reg) 1 G10.
jrun_to LAWS src0tbl_ok HS HJ src0_A_malloc.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hm10. rewrite HE19 in Hm10.
jreg HS (2%bv:reg) as Hm2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hm2.
jreg HS (4%bv:reg) as Hm4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hm4.
jreg HS (1%bv:reg) as Hm1.
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := 3 * ngp) (spc := sp0 - 192);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact Hm10 | exact HRES0 | apply (hdr_pal_room b0 plen HROOM); unfold PALMAX; clear - RN; lia
| exact Hm2 | lia | exact Hspm | lia | lia | exact Hm4 | exact Hm1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hres10 & Hres & Hkeep2 & Hhi2 & HR2). clear HJ.
change (ms_segs src0_msyms) with src0segs in Hkeep2, Hhi2. cbn [ms_regs ms_mem mkst] in HP2, Hkeep2, Hhi2, HJ2, Hres10.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
jafter_call_keep HS 55%nat regs2 mem2 HP2 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
{ constructor; [|constructor].
eapply (region_kept_stack src0segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq59. cbn [ms_regs mkst] in Hq59. rewrite Hres10 in Hq59. symmetry in Hq59.
destruct Hres as (Hnz & Hres16 & (b1 & b2 & Hbl2 & Hblc) & Hwr).
assert (Hpin : In (res, 3 * ngp) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
destruct (blocks_range _ _ LAWS L2 A2 mem2 md2 res (3 * ngp) HH2 Hpin) as [Hr0 Hr1].
assert (HB2 : Permutation (blocks L2 A2) ((res, 3 * ngp) :: blocks L A)).
{ rewrite Hbl2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite <- Hblc. exact HB. }
assert (Hfresh : In (res, 3 * ngp) (blocks L A) -> 3 * ngp <= 0).
{ intros Hin. destruct (Z_lt_le_dec 0 (3 * ngp)) as [Hl|Hl]; [|exact Hl]. exfalso.
apply (fresh_not_in API L2 A2 mem2 md2 b1 b2 res (3 * ngp) HH2 Hbl2 Hl). rewrite <- Hblc. eapply Permutation_in; [apply Permutation_sym; exact HB|]. exact Hin. }
assert (Hpd2 : In (pdata, nb) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | right; exact Hpd]).
add_fact HS 59%nat (mkAF 4096 CEIL_MAX 4).
2:{ rewrite Hq59, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
jrun LAWS src0tbl_ok HS HJ2.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
assert (TONCHK : forall (msx : machine_state) (Ex : env) (ssx : sstate) (cur : Z),
st_ok src0segs Ex ssx msx -> ss_pc ssx = L_NCHK -> ss_resv ssx = None ->
journal src0_msyms MR LIB_STACK sp0 [] L A mem md L2 A2 (ms_mem msx) md2 ->
obj_at src0segs (ms_mem msx) (sp0 - 128) LAY_Config [res; 0; attr; gen; W; H; ngp; 0; 0; 0] ->
saved_ok (ms_mem msx) sp0 regs0 ->
word_mem src0segs (ms_mem msx) (sp0 - 184) pdata -> word_mem src0segs (ms_mem msx) (sp0 - 176) nb ->
word_mem src0segs (ms_mem msx) (sp0 - 168) cur -> 0 <= cur <= nb ->
getr (ms_regs msx) 2 = Z_to_bv 64 (sp0 - 192) -> getr (ms_regs msx) 18 = Z_to_bv 64 res ->
getr (ms_regs msx) 20 = Z_to_bv 64 W -> getr (ms_regs msx) 21 = Z_to_bv 64 H -> untouched_ok regs0 (ms_regs msx) ->
cur = 14 + 3 * ngp -> hdr5 PAYLOAD = (false, (W, H, attr, gen, ngp), skipn 14 PAYLOAD) ->
garr8 src0segs (ms_mem msx) res (firstn (Z.to_nat (3 * ngp)) (skipn (Z.to_nat 14) PAYLOAD)) ->
SR src0segs (mkCfg msx md2) (fun c1 => realizes src0segs c1 (ff_tree K (m_fs md) PAYLOAD))).
{ intros msx Ex ssx cur HSx Hpcx Hrvx HJx Hcfgx HSVx Wpx Wnx Wcx Hcurx X2 X18 X20 X21 HUTx Hc14 HH5 HGPx.
rewrite (st_ok_mkst src0segs Ex ssx msx HSx Hrvx), Hpcx. apply SR_here.
eapply (llvm_nchk_x (ms_regs msx) L2 A2 (ms_mem msx) md2 pdata nb cur res attr gen W H ngp PAYLOAD (firstn (Z.to_nat (3 * ngp)) (skipn (Z.to_nat 14) PAYLOAD)) (rb_malloc b0 (3 * ngp)));
try assumption.
- rewrite (proj2 (Z.eqb_eq _ _) Hattr4). cbn [app]. exact HB2.
- intros Hne. exfalso. exact (Hne Hattr4).
- rewrite (proj2 (Z.eqb_eq _ _) Hattr4). exact Hc14.
- intros _. split; [rewrite HPLn; lia | reflexivity].
- intros Hne. exfalso. exact (Hne Hattr4).
- intros _. split; [exact HGPx | rewrite length_firstn, length_skipn; lia].
- apply (hdr_pal_bud b0). unfold PALMAX. clear - RN. lia. }
assert (TOFREE : forall (msx : machine_state) (Ex : env) (ssx : sstate),
st_ok src0segs Ex ssx msx -> ss_pc ssx = L_PALFREE -> ss_resv ssx = None ->
journal src0_msyms MR LIB_STACK sp0 [] L A mem md L2 A2 (ms_mem msx) md2 ->
saved_ok (ms_mem msx) sp0 regs0 ->
getr (ms_regs msx) 2 = Z_to_bv 64 (sp0 - 192) -> getr (ms_regs msx) 18 = Z_to_bv 64 res -> untouched_ok regs0 (ms_regs msx) ->
ff_cfg PAYLOAD = None ->
SR src0segs (mkCfg msx md2) (fun c1 => realizes src0segs c1 (ff_tree K (m_fs md) PAYLOAD))).
{ intros msx Ex ssx HSx Hpcx Hrvx HJx HSVx X2 X18 HUTx HNONE.
rewrite (st_ok_mkst src0segs Ex ssx msx HSx Hrvx), Hpcx. apply SR_here. unfold ff_tree. rewrite HNONE. unfold ff_leaf.
eapply (llvm_freeret_x (ms_regs msx) L2 A2 (ms_mem msx) md2 res (3 * ngp) (rb_malloc b0 (3 * ngp))); try assumption.
- right. split; [exact HB2 | exact Hfresh].
- apply (main_bud_fin b0 plen). apply (hdr_pal_bud b0). unfold PALMAX. clear - RN. lia. }
jbranch src0tbl HS.
*
rewrite branch_geu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
rewrite (U_atom _ 8 nb) in Hc by first [ew_havocA; exact HE8 | lia].
rewrite (U_atom _ 19 (3 * ngp)) in Hc by first [ew_havocA; exact HE19 | lia].
rewrite (U_atom _ 23 cur1) in Hc by first [ew_havocA; exact HE23 | lia].
rewrite zcanon_id in Hc by (unfold M64; lia).
assert (Hfit : cur1 + 3 * ngp <= nb) by (destruct (Z.ltb_spec nb (3 * ngp + cur1)); [discriminate Hc | lia]). clear Hc.
jrun_to LAWS src0tbl_ok HS HJ2 src0_A_memcpy.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as M10. rewrite Hq59 in M10.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg src0segs Ec ssc msc 11%bv HS) as M11; eval_sr_get_in M11;
rewrite (denot_add_atoms _ 9 23 pdata cur1) in M11 by first [ew_havocA; exact HE9 | ew_havocA; exact HE23 | lia] end.
jreg HS (12%bv:reg) as M12. rewrite HE19 in M12.
jreg HS (1%bv:reg) as M1.
eapply SR_bind.
{ eapply (jmemcpy_rd API IMG _ src0_memcpy) with (d := res) (src := pdata + cur1) (n := 3 * ngp);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact M10 | exact M11 | exact M12 | exact M1
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | | ].
- intros i Hi. repeat match goal with HGx : mem_grows ?m0 ?m |- present ?m _ => apply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 res (3 * ngp) i HH2 Hpin Hi)).
- intros i Hi. apply (present_mbyte src0_msyms). repeat match goal with HGx : mem_grows ?m0 ?m |- present ?m _ => apply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
replace (pdata + cur1 + i) with (pdata + (cur1 + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 pdata nb (cur1 + i) HH2 Hpd2 ltac:(lia))).
- destruct (Z_le_gt_dec (3 * ngp) 0) as [Hz|Hgt]; [lia|].
destruct (heap_sep _ _ LAWS L2 A2 mem2 md2 b1 (res, 3 * ngp) b2 (pdata, nb) HH2 Hbl2 ltac:(rewrite <- Hblc; exact Hpdc)) as [H0|H0]; cbn [fst snd] in H0; lia.
- intros a Ha. replace a with (res + (a - res)) by lia. apply (Hwr (blocks L2 A2)); [exact Hpin | lia]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & Hd10 & Hfr3 & Hout3 & Hgr3 & Hcp3). clear HJ2.
jafter_stretch_keep HS 71%nat regs3 mem3 MEMCPY_CLOB L_CPYRET [0%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr3. exact Hrr. }
{ constructor; [|constructor].
eapply region_kept_out; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU2; lia
| cbn [r_base r_hi base_val]; ew_havocA; rewrite HU2; lia
| cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (HPLm : garr8 src0segs mem3 pdata PAYLOAD).
{ eapply garr8_frame; [exact HPL|]. intros a Ha. rewrite HPLn in Ha.
pose proof HJ3 as (_ & _ & _ & Hblk3 & _). replace a with (pdata + (a - pdata)) by lia.
apply (Hblk3 pdata nb (a - pdata) Hpd Hpd2); [lia | intros (rr & [] & _)]. }
assert (HGP3 : garr8 src0segs mem3 res (firstn (Z.to_nat (3 * ngp)) (skipn (Z.to_nat cur1) PAYLOAD))).
{ refine (proj1 (garr8_slice_copy mem3 mem3 pdata PAYLOAD res cur1 (3 * ngp) HPLm ltac:(lia) ltac:(lia) ltac:(rewrite HPLn; lia) _)).
intros i Hi. rewrite (Hcp3 i Hi). replace (pdata + cur1 + i) with (pdata + (cur1 + i)) by lia. symmetry.
unfold mbyte. rewrite (Hout3 (Z_to_bv 64 (pdata + (cur1 + i)))); [reflexivity|].
rewrite unsigned_lit_small by lia.
destruct (heap_sep _ _ LAWS L2 A2 mem2 md2 b1 (res, 3 * ngp) b2 (pdata, nb) HH2 Hbl2 ltac:(rewrite <- Hblc; exact Hpdc)) as [H0|H0]; cbn [fst snd] in H0; lia. }
jrun LAWS src0tbl_ok HS HJ3.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jbranch src0tbl HS.
--
assert (HNONE : ff_cfg PAYLOAD = None).
{ destruct (Z_lt_le_dec (Z.of_nat (length PAYLOAD)) 14) as [Hsh|Hge]; [exact (HSHORT Hsh)|]. exfalso.
destruct (HDRS Hge) as [Z1 Z2]. rewrite branch_ne_U, U_lit in Hc by lia.
lazymatch type of Hc with context [U ?E1 (SAlu ALU_OR ?ea (SAlu ALU_OR ?eb ?ec))] =>
rewrite (U_or_zero_intro E1 ea (SAlu ALU_OR eb ec) ltac:(apply U_lit; lia)
(U_or_zero_intro E1 eb ec (U_atom E1 11 0 ltac:(ew_havocA; rewrite HE11, Z1; reflexivity) ltac:(lia))
(U_atom E1 12 0 ltac:(ew_havocA; rewrite HE12, Z2; reflexivity) ltac:(lia)))) in Hc end.
discriminate Hc. }
clear Hc.
jrun_to LAWS src0tbl_ok HS HJ3 L_PALFREE.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
eapply TOFREE; [exact HS | reflexivity | reflexivity | exact HJ3 | | | | | exact HNONE]; cbn [ms_regs ms_mem mkst].
++ saved_ok_tac HS HU2 HW32 HW33 HW34 HW35 HW36 HW37 HW38 HW39 HW40 HW41.
++ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
++ reg_nowF HS ltac:(rewrite Hq59, Z_to_bv_bv_unsigned; reflexivity).
++ untouched_tac HS HE G3 G4 G25 G26 G27.
--
rewrite branch_ne_U, U_lit in Hc by lia. apply Bool.negb_false_iff in Hc. apply Z.eqb_eq in Hc.
apply U_or_zero in Hc as [_ Hc]. destruct (HDR0 _ ltac:(ew_havocA; reflexivity) ltac:(ew_havocA; reflexivity) Hc) as [Hc14 HH5]. clear Hc.
jrun_to LAWS src0tbl_ok HS HJ3 L_NCHK.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
eapply (TONCHK _ _ _ (cur1 + 3 * ngp)); [exact HS | reflexivity | reflexivity | exact HJ3 | | | | | | lia | | | | | | lia | exact HH5 | ]; cbn [ms_regs ms_mem mkst].
++ config_obj_tac HS HU2 (SOff 59 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite ?Z.add_0_r, Hq59, Z_to_bv_bv_unsigned; reflexivity) Rcfg HCV.
++ saved_ok_tac HS HU2 HW32 HW33 HW34 HW35 HW36 HW37 HW38 HW39 HW40 HW41.
++ stack_word HS HU2 42%nat HX42. lia.
++ stack_word HS HU2 43%nat HX43. lia.
++ stack_word_e HS HU2 (SAlu ALU_ADD (SOff 19 0) (SOff 23 0)) ltac:(rewrite (denot_add_atoms _ 19 23 (3 * ngp) cur1) by first [ew_havocA; exact HE19 | ew_havocA; exact HE23 | lia]; f_equal; lia). lia.
++ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
++ reg_nowF HS ltac:(rewrite Hq59, Z_to_bv_bv_unsigned; reflexivity).
++ reg_nowF HS ltac:(rewrite HE20, Z_to_bv_bv_unsigned; reflexivity).
++ reg_nowF HS ltac:(rewrite HE21, Z_to_bv_bv_unsigned; reflexivity).
++ untouched_tac HS HE G3 G4 G25 G26 G27.
++ subst cur1. eapply garr8_frame; [exact HGP3|]. intros a Ha. rewrite length_firstn, length_skipn in Ha.
mem_back ltac:(rewrite ?HU2) ltac:(clear - Ha Hr0 Hr1 HPLn Hfit Hac Hsp0al Hstk0 Hceil Hsp063 HLSv HALv; lia).
*
rewrite branch_geu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
rewrite (U_atom _ 8 nb) in Hc by first [ew_havocA; exact HE8 | lia].
rewrite (U_atom _ 19 (3 * ngp)) in Hc by first [ew_havocA; exact HE19 | lia].
rewrite (U_atom _ 23 cur1) in Hc by first [ew_havocA; exact HE23 | lia].
rewrite zcanon_id in Hc by (unfold M64; lia).
assert (Hnfit : nb < cur1 + 3 * ngp) by (destruct (Z.ltb_spec nb (3 * ngp + cur1)); [lia | discriminate Hc]). clear Hc.
assert (HNONE : ff_cfg PAYLOAD = None).
{ destruct (Z_lt_le_dec (Z.of_nat (length PAYLOAD)) 14) as [Hsh|Hge]; [exact (HSHORT Hsh)|].
destruct (HDRS Hge) as [Z1 Z2]. destruct (HDRV Z1 Z2) as [Hc14 HH5].
apply (ff_cfg_pal_short PAYLOAD W H attr gen ngp HH5 Hattr4); [exact Hge | rewrite HPLn; lia]. }
jrun LAWS src0tbl_ok HS HJ2.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jbranch src0tbl HS.
--
clear Hc.
jrun_to LAWS src0tbl_ok HS HJ2 L_PALFREE.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
eapply TOFREE; [exact HS | reflexivity | reflexivity | exact HJ2 | | | | | exact HNONE]; cbn [ms_regs ms_mem mkst].
++ saved_ok_tac HS HU2 HW32 HW33 HW34 HW35 HW36 HW37 HW38 HW39 HW40 HW41.
++ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
++ reg_nowF HS ltac:(rewrite Hq59, Z_to_bv_bv_unsigned; reflexivity).
++ untouched_tac HS HE G3 G4 G25 G26 G27.
--
exfalso. rewrite branch_ne_U, U_lit in Hc by lia. apply Bool.negb_false_iff in Hc. apply Z.eqb_eq in Hc.
apply U_or_zero in Hc as [Hc _]. rewrite U_lit in Hc by lia. lia.
-
pin_reg HS (10%bv:reg) 0 G10.
jrun LAWS src0tbl_ok HS HJ.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jbranch src0tbl HS.
+
rewrite branch_eq_U, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
destruct (HDR0 _ ltac:(ew_havocA; reflexivity) ltac:(ew_havocA; reflexivity) Hc) as [Hc14 HH5]. clear Hc.
jrun_to LAWS src0tbl_ok HS HJ L_NCHK.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_nchk_x rg Lc Ac mm mdc pdata nb cur1 0 attr gen W H ngp PAYLOAD [] b0) end; try assumption.
* replace (Z.land attr 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hattr4). cbn [app]. exact HB.
* intros _. reflexivity.
* apply Hpal0fresh.
* fold sp0. config_obj_tac HS HU2 (SOff 45 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite ?Z.add_0_r; etransitivity; [apply (HCV 0%nat 0 eq_refl) | reflexivity]) Rcfg HCV.
* fold sp0. saved_ok_tac HS HU2 HW32 HW33 HW34 HW35 HW36 HW37 HW38 HW39 HW40 HW41.
* fold sp0. stack_word HS HU2 42%nat HX42. lia.
* fold sp0. stack_word HS HU2 43%nat HX43. lia.
* fold sp0. stack_word HS HU2 23%nat HE23. lia.
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* reg_nowF HS ltac:(reflexivity).
* reg_nowF HS ltac:(rewrite HE20, Z_to_bv_bv_unsigned; reflexivity).
* reg_nowF HS ltac:(rewrite HE21, Z_to_bv_bv_unsigned; reflexivity).
* untouched_tac HS HE G3 G4 G25 G26 G27.
* replace (Z.land attr 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hattr4). lia.
* intros Hz. exfalso. exact (Hattr4 Hz).
* intros _. reflexivity.
* intros Hz. exfalso. exact (Hattr4 Hz).
* apply (hdr_nopal_bud b0).
+
assert (HNONE : ff_cfg PAYLOAD = None).
{ destruct (Z_lt_le_dec (Z.of_nat (length PAYLOAD)) 14) as [Hsh|Hge]; [exact (HSHORT Hsh)|]. exfalso.
destruct (HDRS Hge) as [Z1 Z2]. rewrite branch_eq_U, U_lit in Hc by lia.
lazymatch type of Hc with context [U ?E1 (SAlu ALU_OR ?eb ?ec)] =>
rewrite (U_or_zero_intro E1 eb ec (U_atom E1 11 0 ltac:(ew_havocA; rewrite HE11, Z1; reflexivity) ltac:(lia))
(U_atom E1 12 0 ltac:(ew_havocA; rewrite HE12, Z2; reflexivity) ltac:(lia))) in Hc end.
discriminate Hc. }
clear Hc.
jrun_to LAWS src0tbl_ok HS HJ L_PALFREE.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here. unfold ff_tree. rewrite HNONE. unfold ff_leaf.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_freeret_x rg Lc Ac mm mdc 0 0 b0) end; try assumption.
* left. split; [reflexivity|]. intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HB | exact Hb].
* fold sp0. saved_ok_tac HS HU2 HW32 HW33 HW34 HW35 HW36 HW37 HW38 HW39 HW40 HW41.
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* reg_nowF HS ltac:(reflexivity).
* untouched_tac HS HE G3 G4 G25 G26 G27.
* apply b0_fin.
Qed.
End S.
End f.
