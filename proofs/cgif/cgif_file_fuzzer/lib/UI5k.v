(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r
UI1w UI4l UI21 UI5o UI5l YI6b YL0g
YI16 YI17 YI14 YI18 YI1a UI5c YI00 UI3u UI22 UI2u UI0l UI5m
YI5a UI23 YI0a YL00 YI05 UI5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI5f UI5e UI5h UI5j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UIZs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma garr8_skipn : forall m p (P : list Z) (c : nat),
garr8 ubs0segs m p P -> garr8 ubs0segs m (p + Z.of_nat c) (skipn c P).
Proof using.
intros m p P c H. destruct (Nat.le_gt_cases c (length P)) as [Hc|Hc].
- rewrite <- (firstn_skipn c P) in H. apply garr8_app in H as [_ H2]. rewrite firstn_length_le in H2 by exact Hc. exact H2.
- rewrite skipn_all2 by lia. apply garr8_nil.
Qed.
Lemma garr8_firstn : forall m p (l : list Z) (n : nat), garr8 ubs0segs m p l -> garr8 ubs0segs m p (firstn n l).
Proof using. intros m p l n H. rewrite <- (firstn_skipn n l) in H. apply garr8_app in H as [H1 _]. exact H1. Qed.
Lemma garr8_copy : forall m m' s d (l : list Z),
garr8 ubs0segs m s l -> (forall i, 0 <= i < Z.of_nat (length l) -> mbyte ubs0segs m' (d + i) = mbyte ubs0segs m (s + i)) ->
garr8 ubs0segs m' d l.
Proof using.
intros m m' s d l H Hc j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. replace (d + Z.of_nat j + Z.of_nat k) with (d + (Z.of_nat j + Z.of_nat k)) by lia.
rewrite Hc by (cbn in Hk; lia). replace (s + (Z.of_nat j + Z.of_nat k)) with (s + Z.of_nat j + Z.of_nat k) by lia. apply Hv. exact Hk.
Qed.
Lemma garr8_slice_copy : forall m m' p (P : list Z) d c n,
garr8 ubs0segs m p P -> 0 <= c -> 0 <= n -> c + n <= Z.of_nat (length P) ->
(forall i, 0 <= i < n -> mbyte ubs0segs m' (d + i) = mbyte ubs0segs m (p + c + i)) ->
garr8 ubs0segs m' d (firstn (Z.to_nat n) (skipn (Z.to_nat c) P)) /\ Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat c) P))) = n.
Proof using.
intros m m' p P d c n H Hc Hn Hcn Hcp.
assert (Hlen : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat c) P))) = n) by (rewrite length_firstn, length_skipn; lia).
split; [|exact Hlen]. eapply garr8_copy.
- apply garr8_firstn. apply (garr8_skipn m p P (Z.to_nat c)). exact H.
- intros i Hi. rewrite Hlen in Hi. rewrite Hcp by lia. f_equal. lia.
Qed.
Lemma U_or_zero : forall E e1 e2, U E (SAlu ALU_OR e1 e2) = 0 -> U E e1 = 0 /\ U E e2 = 0.
Proof using.
intros E e1 e2 H. rewrite U_SAlu in H. cbn [zalu_raw] in H. pose proof (U_range E e1) as R1. pose proof (U_range E e2) as R2.
unfold M64 in R1, R2. rewrite zcanon_id in H by (unfold M64; apply Z_lor_range; lia). apply Z.lor_eq_0_iff. exact H.
Qed.
Lemma U_or_zero_intro : forall E e1 e2, U E e1 = 0 -> U E e2 = 0 -> U E (SAlu ALU_OR e1 e2) = 0.
Proof using. intros E e1 e2 H1 H2. rewrite U_SAlu. cbn [zalu_raw]. rewrite H1, H2. reflexivity. Qed.
Lemma denot_mulHW : forall E nh nw H W,
ew E nh = Z_to_bv 64 H -> ew E nw = Z_to_bv 64 W -> 0 <= H < 65536 -> 0 <= W < 65536 ->
sv_denot E (SMd M_MUL (SOff nh 0) (SOff nw 0)) = Z_to_bv 64 (W * H).
Proof using.
intros E nh nw H W Hh Hw RH RW. rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E nh H Hh), (U_atom E nw W Hw) by lia. rewrite zcanon_id by (unfold M64; nia). lia.
Qed.
Lemma denot_add_atoms : forall E a b x y,
ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= x + y < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (x + y).
Proof using.
intros E a b x y Ha Hb Hx Hy Hxy. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E a x Ha), (U_atom E b y Hb) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis CLOSE : close_specX API.
Hypothesis ADDF : addframe_specX API.
Hypothesis UNLINK : unlink_x ubs0_msyms MR ubs0_A_unlink.
Hypothesis RFC : rfc_specX API.
Hypothesis NEWGIF : newgif_x API.
Variables (regs0 : bvmap 5 word) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (b0 : rbound) (plen : Z) (K : lleaf -> TSet).
Hypothesis HSORT : Fs.fs_sorted (m_fs md) = true.
Hypothesis HK : forall fs' c', leaf_post API regs0 L A mem md (ff_delta plen b0) fs' c' -> realizes ubs0segs c' (K (LL 0 fs' [])).
Hypothesis HROOM : ff_room b0 plen.
Hypothesis HFD : fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None.
Definition ss_lfree : sstate :=
mkSS L_FREERET sr_atoms
[ YP09.mkRegion (Some 2%nat) 8 144 8 144 (mkChunk 64 (CVal 8 (SOff 36 0)) :: saved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK - 144) (2^63 - 144) 4) ] [] []).
Lemma word_mem_zcanon : forall m a q, word_mem ubs0segs m a q -> word_mem ubs0segs m a (zcanon q).
Proof using. intros m a q H k Hk. rewrite (H k Hk). unfold zcanon, M64, le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. Qed.
Ltac reg_now_c HS tac :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch goal with |- getr _ ?rr = _ =>
let T := fresh "T" in
pose proof (st_ok_reg ubs0segs Ec ssc msc rr HS) as T; eval_sr_get_in T; cbn [sv_denot ms_regs mkst] in T;
repeat (rewrite ew_havoc_old in T; [|nat_lt_lit]); rewrite ?Z.add_0_r in T;
rewrite T; clear T; tac
end end.
Lemma llvm_freeret_x :
forall (regs1 : bvmap 5 word) Lc Ac memc mdc (q m : Z) (bc : rbound),
journal ubs0_msyms MR LIB_STACK (spZ regs0) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) -> spZ regs0 mod 16 = 0 ->
((q = 0 /\ forall b, In b (blocks L A) -> In b (blocks Lc Ac)) \/
(Permutation (blocks Lc Ac) ((q, m) :: blocks L A) /\ (In (q, m) (blocks L A) -> m <= 0))) ->
saved_ok memc (spZ regs0) regs0 ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 144) -> word_mem ubs0segs memc (spZ regs0 - 80) q -> untouched_ok regs0 regs1 ->
sink_none ubs0_msyms mem md ->
res_ok Ac bc -> rb_le bc (ff_delta plen b0) ->
realizes ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 L_FREERET) memc (seg_rom ubs0segs)) mdc) (K (LL 0 (m_fs md) [])).
Proof using HK IMG LAWS.
intros regs1 Lc Ac memc mdc q m bc HJ Hid Hra0 Htp0 Hal16 Hq HSV G2 Wq HUT HSN0 HRES HBLE.
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
apply realizes_via_SR.
pose proof (proj1 alloc_ceiling_val) as Hac.
let v := eval vm_compute in LIB_STACK in assert (HLSv : LIB_STACK = v) by reflexivity.
assert (HALv : ALLOC_STACK = 8192) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 144) mod 16 = 0) by (replace (sp0 - 144) with (sp0 + (-9) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
set (E := Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ map (Z_to_bv 64) [q] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HY : forall j v, nth_error [q] j = Some v -> ew E (36 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (36 + j)%nat with (32 + (length (saved_vals regs0) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HX36 : ew E 36 = Z_to_bv 64 q) by (apply (HY 0%nat); reflexivity).
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (Rq : 0 <= zcanon q < 2 ^ (8 * Z.of_N 8%N)) by (change (8 * Z.of_N 8%N) with 64; unfold zcanon, M64; apply Z.mod_pos_bound; lia).
pose proof HSV as (W1 & W8 & W9 & W18).
assert (HS : st_ok ubs0segs E ss_lfree (mkst regs1 (Z_to_bv 64 L_FREERET) memc (seg_rom ubs0segs))).
{ unfold ss_lfree. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons.
{ eapply (chunk_ok_val _ _ _ _ _ _ _ (zcanon q)); [cbn [sv_denot]; rewrite Z.add_0_r, HX36, unsigned_lit; reflexivity | exact Rq | cbn; lia
| replace (sp0 - 144 + 64) with (sp0 - 80) by lia; apply val_mem_word_mem; apply word_mem_zcanon; exact Wq]. }
assert (CK : forall off j (w : Z), nth_error (saved_vals regs0) j = Some w -> word_mem ubs0segs memc (sp0 - 144 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs0segs (Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ map (Z_to_bv 64) [q] ++ [])) memc (sp0 - 144) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HSV' j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold saved_chunks. cbn [Nat.add].
repeat (apply Forall_cons;
[ first [ apply (CK 136 0%nat _ eq_refl); [replace (sp0 - 144 + 136) with (sp0 - 8) by lia; exact W1 | apply u64_range']
| apply (CK 128 1%nat _ eq_refl); [replace (sp0 - 144 + 128) with (sp0 - 16) by lia; exact W8 | apply u64_range']
| apply (CK 120 2%nat _ eq_refl); [replace (sp0 - 144 + 120) with (sp0 - 24) by lia; exact W9 | apply u64_range']
| apply (CK 112 3%nat _ eq_refl); [replace (sp0 - 144 + 112) with (sp0 - 32) by lia; exact W18 | apply u64_range'] ] | ]).
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. repeat split; try lia; exact Hspm. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 L_FREERET) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_free.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hc10. rewrite HX36 in Hc10.
jreg HS (2%bv:reg) as Hc2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hc2.
jreg HS (4%bv:reg) as Hc4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hc4.
jreg HS (1%bv:reg) as Hc1.
lazymatch goal with |- SR _ (mkCfg ?msq ?mdq) _ =>
eapply SR_bind with (R := fun c' => exists L6 A6 regs6 mem6 md6,
c' = mkCfg (mkst regs6 (Z_to_bv 64 L_RET0) mem6 (seg_rom ubs0segs)) md6 /\
journal ubs0_msyms MR LIB_STACK sp0 [] L A mem md L6 A6 mem6 md6 /\ st_init_done A6 = true /\
regs_preserved (ms_regs msq) regs6 /\ (forall b, In b (blocks L A) -> In b (blocks L6 A6)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 144 - ALLOC_STACK <= x < sp0 - 144) ->
mbyte ubs0segs mem6 x = mbyte ubs0segs (ms_mem msq) x /\ (writable_at ubs0segs (ms_mem msq) x <-> writable_at ubs0segs mem6 x)) /\
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
{ eapply (jfree_at_res API IMG) with (a := q) (n := m) (spc := sp0 - 144);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hqin | exact HRES | exact Hc10
| exact Hc2 | lia | exact Hspm | lia | lia | exact Hc4 | exact Hc1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hin i Hi. exfalso. pose proof (Hfresh Hin). lia. }
intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hrm6 & Hkeep6 & Hhi6 & Hid6 & HR6).
exists L6, A6, regs6, mem6, md6. split; [reflexivity|]. split; [exact HJ6|]. split; [exact Hid6|]. split; [exact HP6|].
split; [| split; [exact Hhi6 | eapply res_ok_mono; [apply rb_free_le | exact HR6]]].
intros b Hb. pose proof (perm_after_rm1 _ _ _ _ HBq Hrm6) as HP. eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hb]. }
cbv beta. intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & Hid6 & HP6 & Hbase6 & Hhi6 & HR6'). clear HJ.
cbn [ms_regs ms_mem mkst] in HP6, Hhi6.
jafter_call_keep HS 37%nat regs6 mem6 HP6 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HU2 | exact Hhi6 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
apply SR_here.
eapply (llvm_ret0_x API IMG regs0 L A mem md b0 plen K HK regs6 L6 A6 mem6 md6 bc); try assumption.
- fold sp0. saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
- reg_now_c HS ltac:(rewrite HU2; f_equal; lia).
- unfold untouched_ok; repeat match goal with |- _ /\ _ => split end; reg_now_c HS ltac:(he_reg_tac HE).
Qed.
Definition ss_lnchk : sstate :=
mkSS L_NCHK sr_atoms
[ YP09.mkRegion (Some 2%nat) 8 144 8 144
([mkChunk 8 (CVal 8 (SOff 36 0)); mkChunk 16 (CVal 8 (SOff 37 0)); mkChunk 24 (CVal 8 (SOff 38 0))]
++ obj_chunks_gen (lay_shift 64 LAY_Config) 39 lits_Config0 ++ saved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK - 144) (2^63 - 144) 4); (43%nat, mkAF 0 65535 0); (44%nat, mkAF 0 65535 0) ] [] []).
Definition ss_lnchk_c : sstate := Eval vm_compute in ss_lnchk.
Lemma llvm_nchk_x :
forall (regs1 : bvmap 5 word) Lc Ac memc mdc
(pdata nb cur pal0 attr gen W H ngp : Z) (PAYLOAD GPAL : list Z) (bc : rbound),
journal ubs0_msyms MR LIB_STACK (spZ regs0) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) -> spZ regs0 mod 16 = 0 ->
In (pdata, nb) (blocks L A) -> 0 < nb ->
Permutation (blocks Lc Ac) ((if Z.land attr 4 =? 0 then [(pal0, 3 * ngp)] else []) ++ blocks L A) ->
(Z.land attr 4 <> 0 -> pal0 = 0) ->
(In (pal0, 3 * ngp) (blocks L A) -> 3 * ngp <= 0) ->
obj_at ubs0segs memc (spZ regs0 - 80) LAY_Config [pal0; 0; attr; gen; W; H; ngp; 0; 0; 0] ->
saved_ok memc (spZ regs0) regs0 ->
word_mem ubs0segs memc (spZ regs0 - 136) pdata -> word_mem ubs0segs memc (spZ regs0 - 128) nb ->
word_mem ubs0segs memc (spZ regs0 - 120) cur -> 0 <= cur <= nb ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 144) ->
untouched_ok regs0 regs1 ->
sink_none ubs0_msyms mem md -> spZ regs0 <= 2 ^ 47 ->
garr8 ubs0segs mem pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb ->
hdr5 PAYLOAD = (false, (W, H, attr, gen, ngp), skipn 14 PAYLOAD) ->
cur = 14 + (if Z.land attr 4 =? 0 then 3 * ngp else 0) ->
(Z.land attr 4 = 0 -> 14 + 3 * ngp <= Z.of_nat (length PAYLOAD) /\ GPAL = firstn (Z.to_nat (3 * ngp)) (skipn 14 PAYLOAD)) ->
(Z.land attr 4 <> 0 -> GPAL = []) ->
(Z.land attr 4 = 0 -> garr8 ubs0segs memc pal0 GPAL /\ Z.of_nat (length GPAL) = 3 * ngp) ->
res_ok Ac bc -> rb_le bc (main_bud b0) ->
realizes ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 L_NCHK) memc (seg_rom ubs0segs)) mdc) (ff_tree K (m_fs md) PAYLOAD).
Proof using ADDF CLOSE HFD HK HROOM HSORT IMG LAWS NEWGIF RFC UNLINK.
intros regs1 Lc Ac memc mdc pdata nb cur pal0 attr gen W H ngp PAYLOAD GPAL bc
HJ Hid Hra0 Htp0 Hal16 Hpd Hnb HB Hpal00 Hpalfresh Hcfg HSV Wp Wn Wc Hcur G2 HUT
HSN0 Hsp47 HPL HPLn HHDR HcurV HGPs HGPn HGP HRES HBLE.
apply realizes_via_SR.
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK = 16384) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 144) mod 16 = 0) by (replace (sp0 - 144) with (sp0 + (-9) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. exact Hpd. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH0 Hpdc) as [Hp0 Hp1].
pose proof (obj_at_range _ _ _ _ _ Hcfg) as Rcfg.
pose proof (Rcfg 0%nat pal0 eq_refl) as RP. pose proof (Rcfg 4%nat W eq_refl) as RW.
pose proof (Rcfg 5%nat H eq_refl) as RH. pose proof (Rcfg 6%nat ngp eq_refl) as RN. cbn in RP, RW, RH, RN.
assert (Hpr : Z.land attr 4 = 0 -> 4096 <= pal0 /\ pal0 + 3 * ngp <= alloc_ceiling).
{ intros Hz. eapply (blocks_range _ _ LAWS); [exact HH0|]. eapply Permutation_in; [apply Permutation_sym; exact HB|].
  rewrite (proj2 (Z.eqb_eq _ _) Hz). left. reflexivity. }
set (cvals := [pal0; 0; attr; gen; W; H; ngp; 0; 0; 0]) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur] ++ cvals) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HY : forall j v, nth_error ([pdata; nb; cur] ++ cvals) j = Some v -> ew E (36 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (36 + j)%nat with (32 + (length (saved_vals regs0) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HCV : forall j v, nth_error cvals j = Some v -> ew E (39 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (39 + j)%nat with (36 + (3 + j))%nat by lia. apply HY. exact Hj. }
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HX36 : ew E 36 = Z_to_bv 64 pdata) by (apply (HY 0%nat); reflexivity).
assert (HX37 : ew E 37 = Z_to_bv 64 nb) by (apply (HY 1%nat); reflexivity).
assert (HX38 : ew E 38 = Z_to_bv 64 cur) by (apply (HY 2%nat); reflexivity).
assert (HX39 : ew E 39 = Z_to_bv 64 pal0) by (apply (HCV 0%nat); reflexivity).
assert (HX43 : ew E 43 = Z_to_bv 64 W) by (apply (HCV 4%nat); reflexivity).
assert (HX44 : ew E 44 = Z_to_bv 64 H) by (apply (HCV 5%nat); reflexivity).
pose proof HSV as (W1 & W8 & W9 & W18).
assert (HS : st_ok ubs0segs E ss_lnchk_c (mkst regs1 (Z_to_bv 64 L_NCHK) memc (seg_rom ubs0segs))).
{ change ss_lnchk_c with ss_lnchk. unfold ss_lnchk. subst E. apply entry_st_ok.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
    split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
    apply Forall_app; split; [|apply Forall_app; split].
    + apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX36, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 8) with (sp0 - 136) by lia; apply val_mem_word_mem; exact Wp]. }
      apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX37, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 16) with (sp0 - 128) by lia; apply val_mem_word_mem; exact Wn]. }
      apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX38, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 24) with (sp0 - 120) by lia; apply val_mem_word_mem; exact Wc]. }
      apply Forall_nil.
    + eapply (obj_chunks_gen_ok ubs0segs _ _ (sp0 - 144) _ cvals 39 lits_Config0); [| reflexivity | | apply lits_Config0_ok].
      * apply (proj1 (obj_at_shift _ _ (sp0 - 144) 64 LAY_Config cvals)). replace (sp0 - 144 + 64) with (sp0 - 80) by lia. exact Hcfg.
      * intros j v Hj. apply (HCV j v Hj).
    + assert (CK : forall off j (w : Z), nth_error (saved_vals regs0) j = Some w -> word_mem ubs0segs memc (sp0 - 144 + off) w -> 0 <= w < 2 ^ 64 ->
        chunk_ok ubs0segs (Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur] ++ cvals) ++ [])) memc (sp0 - 144) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
      { intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
        cbn [sv_denot]. rewrite Z.add_0_r, (HSV' j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
      unfold saved_chunks. cbn [Nat.add].
      repeat (apply Forall_cons;
      [ first [ apply (CK 136 0%nat _ eq_refl); [replace (sp0 - 144 + 136) with (sp0 - 8) by lia; exact W1 | apply u64_range']
      | apply (CK 128 1%nat _ eq_refl); [replace (sp0 - 144 + 128) with (sp0 - 16) by lia; exact W8 | apply u64_range']
      | apply (CK 120 2%nat _ eq_refl); [replace (sp0 - 144 + 120) with (sp0 - 24) by lia; exact W9 | apply u64_range']
      | apply (CK 112 3%nat _ eq_refl); [replace (sp0 - 144 + 112) with (sp0 - 32) by lia; exact W18 | apply u64_range'] ] | ]).
      apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. repeat split.
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HX43, HX44, !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 L_NCHK) memc (seg_rom ubs0segs))) in HJ.
jrun LAWS ubs0tbl_ok HS HJ.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jbranch ubs0tbl HS.
- rewrite branch_ltu_U, U_lit in Hc by lia.
  lazymatch type of Hc with (U ?E1 ?e <? _) = true => rewrite <- (denot_lit_U E1 e) in Hc || idtac end.
  assert (HWH : W * H <= 100000000).
  { revert Hc. unfold U. rewrite (denot_mulHW E 44 43 H W HX44 HX43) by lia. rewrite unsigned_lit_small by nia.
    intros Hc. destruct (Z.ltb_spec (W * H) 100000001); [lia | discriminate Hc]. }
  clear Hc.
  jrun_to LAWS ubs0tbl_ok HS HJ L_MAIN.
  { eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
  rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
  unfold ff_tree. rewrite (ff_cfg_of_walk PAYLOAD W H attr gen ngp GPAL cur HHDR HWH HcurV ltac:(clear - RN; lia) HGPs HGPn).
  lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply (llvm_main_x API IMG CLOSE ADDF UNLINK RFC NEWGIF regs0 L A mem md b0 plen K HSORT HK HROOM HFD rg Lc Ac mm mdc pdata nb cur pal0 attr gen W H ngp PAYLOAD GPAL bc) end.
  + exact HJ. + exact Hid. + exact Hra0. + exact Htp0. + exact Hal16. + exact Hpd. + exact Hnb. + exact HB. + exact Hpal00. + exact Hpalfresh. + exact HWH.
  + fold sp0. replace (sp0 - 80) with (sp0 - 144 + 64) by lia. apply (proj2 (obj_at_shift _ _ (sp0 - 144) 64 LAY_Config _)).
    eapply (st_obj_at ubs0segs _ _ _ 0%nat _ 2%nat (sp0 - 144) _ _ 39 lits_Config0 HS eq_refl eq_refl HU2);
    [ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ].
    intros j v Hj. split; [rewrite nth_lay_shift_snd; exact (Rcfg j v Hj)|].
    assert (Hlj : (j < 10)%nat) by (destruct (Nat.lt_ge_cases j 10) as [Hl|Hl]; [exact Hl|]; rewrite (proj2 (nth_error_None [pal0; 0; attr; gen; W; H; ngp; 0; 0; 0] j) Hl) in Hj; discriminate).
    do 10 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [nth_error lits_Config0]; first [reflexivity | apply HCV; reflexivity] |]). exfalso; lia.
  + fold sp0. saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
  + fold sp0. stack_word HS HU2 36%nat HX36. lia.
  + fold sp0. stack_word HS HU2 37%nat HX37. lia.
  + fold sp0. stack_word HS HU2 38%nat HX38. lia.
  + exact Hcur.
  + reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
  + lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
    let T := fresh "T" in pose proof (st_ok_reg ubs0segs Ec ssc msc 8%bv HS) as T; eval_sr_get_in T;
    rewrite (denot_mulHW _ 44 43 H W HX44 HX43) in T by lia; exact T end.
  + ut_tac HS HE.
  + exact HSN0. + exact Hsp47. + exact HPL. + exact HPLn. + exact HHDR. + exact HcurV. + lia. + exact HGPs. + exact HGPn.
  + intros Hz. destruct (HGP Hz) as [HGPm HGPl]. destruct (Hpr Hz) as [Hq0 Hq1]. split; [|exact HGPl].
    eapply garr8_frame; [exact HGPm|]. intros a Ha. rewrite HGPl in Ha. fold sp0. cbn [ms_mem mkst] in *.
    mem_back ltac:(rewrite ?HU2) ltac:(clear - Ha Hq0 Hq1 Hac Hsp0al Hstk0 Hceil Hsp063 HLSv; lia).
  + exact HRES. + exact HBLE.
- rewrite branch_ltu_U, U_lit in Hc by lia.
  lazymatch type of Hc with (U ?E1 ?e <? _) = false => rewrite <- (denot_lit_U E1 e) in Hc || idtac end.
  assert (HWH : 100000000 < W * H).
  { revert Hc. unfold U. rewrite (denot_mulHW E 44 43 H W HX44 HX43) by lia. rewrite unsigned_lit_small by nia.
    intros Hc. destruct (Z.ltb_spec (W * H) 100000001); [discriminate Hc | lia]. }
  clear Hc.
  jrun_to LAWS ubs0tbl_ok HS HJ L_FREERET.
  { eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
  rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
  unfold ff_tree. rewrite (ff_cfg_too_large PAYLOAD W H attr gen ngp HHDR HWH). unfold ff_leaf.
  lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply (llvm_freeret_x rg Lc Ac mm mdc pal0 (3 * ngp) bc) end.
  + exact HJ. + exact Hid. + exact Hra0. + exact Htp0. + exact Hal16.
  + destruct (Z.eqb_spec (Z.land attr 4) 0) as [Hz|Hz].
    * right. split; [exact HB | exact Hpalfresh].
    * left. split; [apply Hpal00; exact Hz|]. intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HB | exact Hb].
  + fold sp0. saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
  + reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
  + fold sp0. stack_word HS HU2 39%nat HX39. lia.
  + ut_tac HS HE.
  + exact HSN0.
  + exact HRES. + apply (main_bud_fin b0 plen). exact HBLE.
Qed.
Definition ss_ltail : sstate :=
mkSS L_TAIL sr_atoms
[ YP09.mkRegion (Some 2%nat) 64 144 64 144 (obj_chunks_gen (lay_shift 64 LAY_Config) 39 lits_Config0 ++ saved_chunks 32);
YP09.mkRegion (Some 2%nat) 8 24 8 24 [mkChunk 8 (CVal 8 (SOff 36 0)); mkChunk 16 (CVal 8 (SOff 37 0))];
YP09.mkRegion (Some 2%nat) 24 32 24 32 [mkChunk 24 (CVal 8 (SOff 38 0))] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK - 144) (2^63 - 144) 4);
(36%nat, mkAF 4096 CEIL_MAX 0); (37%nat, mkAF 1 CEIL_MAX 0); (38%nat, mkAF 0 CEIL_MAX 0) ] [] []).
Lemma land4_byte : forall x, Z.land (x mod 2 ^ 8) 4 = Z.land x 4.
Proof using. intros x. rewrite <- (Z.land_ones x 8) by lia. rewrite <- Z.land_assoc. reflexivity. Qed.
Ltac tail_word HS HU2 i off e tac :=
lazymatch goal with |- word_mem _ _ ?a ?v =>
lazymatch type of HU2 with bv_unsigned _ = ?b =>
replace a with (b + off) by lia;
eapply (st_chunk_word _ _ _ i _ 2%nat off e b v HS);
[ reflexivity | reflexivity | cbv; auto 60 | ew_havocA; exact HU2 | tac | ]
end end.
Ltac wr_tail HU2 :=
repeat (eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]); apply wr_ok_nil.
Ltac cfg_obj_u HS HU2 e0 tac0 Rcfg HCV :=
lazymatch goal with |- obj_at ?sg ?m (?spv - 80) LAY_Config (?v0 :: ?vs) =>
change (obj_at sg m (spv - 80) LAY_Config (v0 :: vs)) with (field_ok sg m (spv - 80) (0, 8%N) v0 /\ obj_at sg m (spv - 80) (tl LAY_Config) vs);
split;
[ unfold field_ok; cbn [fst snd]; split;
[ apply val_mem_word_mem; rewrite Z.add_0_r; tail_word HS HU2 0%nat 64 e0 tac0; lia | lia ]
| replace (spv - 80) with (spv - 144 + 64) by lia; apply (proj2 (obj_at_shift _ _ (spv - 144) 64 (tl LAY_Config) _));
change (lay_shift 64 (tl LAY_Config)) with (tl (lay_shift 64 LAY_Config));
eapply (st_obj_at sg _ _ _ 0%nat _ 2%nat (spv - 144) _ _ 40 (tl lits_Config0) HS eq_refl eq_refl ltac:(ew_havocA; exact HU2));
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ];
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; split; [change (tl (lay_shift 64 LAY_Config)) with (lay_shift 64 (tl LAY_Config)); rewrite nth_lay_shift_snd;
change (nth j (tl LAY_Config) (0, 8%N)) with (nth (Datatypes.S j) LAY_Config (0, 8%N)); exact (Rcfg (Datatypes.S j) v Hj) |];
do 9 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [nth_error lits_Config0 tl]; first [reflexivity | ew_havocA; apply HCV; reflexivity] |]);
exfalso; destruct j; cbn in Hj; discriminate Hj ]
end.
Ltac atom_tac Hx := cbn [sv_denot]; ew_havocA; rewrite ?Z.add_0_r, Hx; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity].
Lemma U_three0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 16 ->
U E (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff n 0)) (SLit 1)) (SExt false 16 (SOff n 0))) = 3 * v.
Proof using.
intros E n v Hn Hv. rewrite !U_SAlu, U_zext, (U_atom E n v Hn), !U_SLit by lia. cbn [zalu_raw].
change (Z.of_N 16) with 16. rewrite Z.mod_small by lia.
rewrite (zcanon_id 1) by (unfold M64; lia). change (Z.land 1 63) with 1.
rewrite Z.shiftl_mul_pow2 by lia. rewrite (zcanon_id (v * 2 ^ 1)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma U_three : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 16 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff n 0)) (SLit 1)) (SExt false 16 (SOff n 0))) (SLit 0)) = 3 * v.
Proof using.
intros E n v Hn Hv. rewrite U_SAlu, (U_three0 E n v Hn Hv), U_SLit. cbn [zalu_raw].
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma llvm_tail_x :
forall (regs1 : bvmap 5 word) Lc Ac memc mdc
(pdata nb cur attr gen W H ngp r1 r2 : Z) (PAYLOAD : list Z),
journal ubs0_msyms MR LIB_STACK (spZ regs0) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) -> spZ regs0 mod 16 = 0 ->
In (pdata, nb) (blocks L A) -> 0 < nb ->
Permutation (blocks Lc Ac) (blocks L A) ->
obj_at ubs0segs memc (spZ regs0 - 80) LAY_Config [0; 0; attr; gen; W; H; ngp; 0; 0; 0] ->
saved_ok memc (spZ regs0) regs0 ->
word_mem ubs0segs memc (spZ regs0 - 136) pdata -> word_mem ubs0segs memc (spZ regs0 - 128) nb ->
word_mem ubs0segs memc (spZ regs0 - 120) cur -> 0 <= cur <= nb ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 144) -> getr regs1 8 = Z_to_bv 64 r1 -> getr regs1 10 = Z_to_bv 64 r2 ->
0 <= r1 < 2 ^ 64 -> 0 <= r2 < 2 ^ 64 ->
untouched_ok regs0 regs1 ->
sink_none ubs0_msyms mem md -> spZ regs0 <= 2 ^ 47 ->
garr8 ubs0segs mem pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb ->
(r1 = 0 -> r2 = 0 -> cur = 14 /\ hdr5 PAYLOAD = (false, (W, H, attr, gen, ngp), skipn 14 PAYLOAD)) ->
(14 <= Z.of_nat (length PAYLOAD) -> r1 = 0 /\ r2 = 0) ->
res_ok Ac b0 ->
realizes ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 L_TAIL) memc (seg_rom ubs0segs)) mdc) (ff_tree K (m_fs md) PAYLOAD).
Proof using ADDF CLOSE HFD HK HROOM HSORT IMG LAWS NEWGIF RFC UNLINK.
intros regs1 Lc Ac memc mdc pdata nb cur attr gen W H ngp r1 r2 PAYLOAD
HJ Hid Hra0 Htp0 Hal16 Hpd Hnb HB Hcfg HSV Wp Wn Wc Hcur G2 G8 G10 Rr1 Rr2 HUT HSN0 Hsp47 HPL HPLn HDRV HDRS HRES0.
apply realizes_via_SR.
assert (HSHORT : Z.of_nat (length PAYLOAD) < 14 -> ff_cfg PAYLOAD = None) by (intros Hsh; exact (ff_cfg_hdr_short _ (hdr5_short _ Hsh))).
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac.
let v := eval vm_compute in LIB_STACK in assert (HLSv : LIB_STACK = v) by reflexivity.
assert (HALv : ALLOC_STACK = 8192) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 144) mod 16 = 0) by (replace (sp0 - 144) with (sp0 + (-9) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB | exact Hpd]).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH0 Hpdc) as [Hp0 Hp1].
pose proof (obj_at_range _ _ _ _ _ Hcfg) as Rcfg.
pose proof (Rcfg 2%nat attr eq_refl) as RA. pose proof (Rcfg 4%nat W eq_refl) as RW.
pose proof (Rcfg 5%nat H eq_refl) as RH. pose proof (Rcfg 6%nat ngp eq_refl) as RN. cbn in RA, RW, RH, RN.
set (cvals := [0; 0; attr; gen; W; H; ngp; 0; 0; 0]) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur] ++ cvals) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HY : forall j v, nth_error ([pdata; nb; cur] ++ cvals) j = Some v -> ew E (36 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (36 + j)%nat with (32 + (length (saved_vals regs0) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HCV : forall j v, nth_error cvals j = Some v -> ew E (39 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (39 + j)%nat with (36 + (3 + j))%nat by lia. apply HY. exact Hj. }
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 r1) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE10 : ew E 10 = Z_to_bv 64 r2) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HX36 : ew E 36 = Z_to_bv 64 pdata) by (apply (HY 0%nat); reflexivity).
assert (HX37 : ew E 37 = Z_to_bv 64 nb) by (apply (HY 1%nat); reflexivity).
assert (HX38 : ew E 38 = Z_to_bv 64 cur) by (apply (HY 2%nat); reflexivity).
assert (HX39 : ew E 39 = Z_to_bv 64 0) by (apply (HCV 0%nat); reflexivity).
assert (HX41 : ew E 41 = Z_to_bv 64 attr) by (apply (HCV 2%nat); reflexivity).
assert (HX45 : ew E 45 = Z_to_bv 64 ngp) by (apply (HCV 6%nat); reflexivity).
pose proof HSV as (W1 & W8 & W9 & W18).
assert (HS : st_ok ubs0segs E ss_ltail (mkst regs1 (Z_to_bv 64 L_TAIL) memc (seg_rom ubs0segs))).
{ unfold ss_ltail. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX36, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 8) with (sp0 - 136) by lia; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX37, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 16) with (sp0 - 128) by lia; apply val_mem_word_mem; exact Wn]. }
apply Forall_nil. }
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX38, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 24) with (sp0 - 120) by lia; apply val_mem_word_mem; exact Wc]. }
apply Forall_nil. }
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_app; split.
+ eapply (obj_chunks_gen_ok ubs0segs _ _ (sp0 - 144) _ cvals 39 lits_Config0); [| reflexivity | | apply lits_Config0_ok].
-- apply (proj1 (obj_at_shift _ _ (sp0 - 144) 64 LAY_Config cvals)). replace (sp0 - 144 + 64) with (sp0 - 80) by lia. exact Hcfg.
-- intros j v Hj. apply (HCV j v Hj).
+ assert (CK : forall off j (w : Z), nth_error (saved_vals regs0) j = Some w -> word_mem ubs0segs memc (sp0 - 144 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs0segs (Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur] ++ cvals) ++ [])) memc (sp0 - 144) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HSV' j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold saved_chunks. cbn [Nat.add].
repeat (apply Forall_cons;
[ first [ apply (CK 136 0%nat _ eq_refl); [replace (sp0 - 144 + 136) with (sp0 - 8) by lia; exact W1 | apply u64_range']
| apply (CK 128 1%nat _ eq_refl); [replace (sp0 - 144 + 128) with (sp0 - 16) by lia; exact W8 | apply u64_range']
| apply (CK 120 2%nat _ eq_refl); [replace (sp0 - 144 + 120) with (sp0 - 24) by lia; exact W9 | apply u64_range']
| apply (CK 112 3%nat _ eq_refl); [replace (sp0 - 144 + 112) with (sp0 - 32) by lia; exact W18 | apply u64_range'] ] | ]).
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HX36, HX37, HX38, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 L_TAIL) memc (seg_rom ubs0segs))) in HJ.
assert (HDR0 : forall E', ew E' 8 = ew E 8 -> ew E' 10 = ew E 10 -> U E' (SAlu ALU_OR (SOff 8 0) (SOff 10 0)) = 0 ->
cur = 14 /\ hdr5 PAYLOAD = (false, (W, H, attr, gen, ngp), skipn 14 PAYLOAD)).
{ intros E' E8 E10 Hor. apply U_or_zero in Hor as [U8 U10].
rewrite (U_atom E' 8 r1 ltac:(rewrite E8; exact HE8) Rr1) in U8. rewrite (U_atom E' 10 r2 ltac:(rewrite E10; exact HE10) Rr2) in U10. exact (HDRV U8 U10). }
assert (Hpal0fresh : forall n, In (0, n) (blocks L A) -> n <= 0).
{ intros n Hin. exfalso. destruct (blocks_range _ _ LAWS Lc Ac _ mdc 0 n HH0 ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | exact Hin])) as [H0 _]. lia. }
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_tail HU2. }
jbranch ubs0tbl HS.
- rewrite branch_ne_U, U_lit, U_and_lit, U_zext in Hc by lia.
rewrite (U_atom _ 41 attr) in Hc by first [ew_havocA; exact HX41 | lia]. rewrite land4_byte in Hc.
apply Bool.negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hattr4.
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_tail HU2. }
jbranch ubs0tbl HS.
+ assert (HNONE : ff_cfg PAYLOAD = None).
{ destruct (Z_lt_le_dec (Z.of_nat (length PAYLOAD)) 14) as [Hsh|Hge]; [exact (HSHORT Hsh)|]. exfalso.
destruct (HDRS Hge) as [Z1 Z2]. rewrite branch_ne_U, U_lit in Hc by lia.
lazymatch type of Hc with context [U ?E1 (SAlu ALU_OR ?eb ?ec)] =>
rewrite (U_or_zero_intro E1 eb ec (U_atom E1 8 0 ltac:(ew_havocA; rewrite HE8, Z1; reflexivity) ltac:(lia))
(U_atom E1 10 0 ltac:(ew_havocA; rewrite HE10, Z2; reflexivity) ltac:(lia))) in Hc end.
discriminate Hc. }
clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ L_FREERET.
{ wr_tail HU2. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here. unfold ff_tree. rewrite HNONE. unfold ff_leaf.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_freeret_x rg Lc Ac mm mdc 0 0 b0) end; try assumption.
* left. split; [reflexivity|]. intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HB | exact Hb].
* fold sp0. saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* fold sp0. tail_word HS HU2 0%nat 64 (SOff 39 0) ltac:(atom_tac HX39). lia.
* ut_tac HS HE.
* apply b0_fin.
+ rewrite branch_ne_U, U_lit in Hc by lia. apply Bool.negb_false_iff in Hc. apply Z.eqb_eq in Hc.
destruct (HDR0 _ ltac:(ew_havocA; reflexivity) ltac:(ew_havocA; reflexivity) Hc) as [Hc14 HH5]. clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ L_NCHK.
{ wr_tail HU2. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_nchk_x rg Lc Ac mm mdc pdata nb cur 0 attr gen W H ngp PAYLOAD [] b0) end; try assumption.
* replace (Z.land attr 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hattr4). cbn [app]. exact HB.
* intros _. reflexivity.
* apply Hpal0fresh.
* fold sp0. cfg_obj_u HS HU2 (SOff 39 0) ltac:(atom_tac HX39) Rcfg HCV.
* fold sp0. saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
* fold sp0. tail_word HS HU2 1%nat 8 (SOff 36 0) ltac:(atom_tac HX36). lia.
* fold sp0. tail_word HS HU2 1%nat 16 (SOff 37 0) ltac:(atom_tac HX37). lia.
* fold sp0. tail_word HS HU2 2%nat 24 (SOff 38 0) ltac:(atom_tac HX38). lia.
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* ut_tac HS HE.
* replace (Z.land attr 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hattr4). lia.
* intros Hz. exfalso. exact (Hattr4 Hz).
* intros _. reflexivity.
* intros Hz. exfalso. exact (Hattr4 Hz).
* apply (hdr_nopal_bud b0).
- rewrite branch_ne_U, U_lit, U_and_lit, U_zext in Hc by lia.
rewrite (U_atom _ 41 attr) in Hc by first [ew_havocA; exact HX41 | lia]. rewrite land4_byte in Hc.
apply Bool.negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hattr4.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_malloc.
{ wr_tail HU2. }
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs0segs Ec ssc msc 10%bv HS) as Hm10; eval_sr_get_in Hm10 end.
rewrite denot_lit_U, (U_three _ 45 ngp) in Hm10 by first [ew_havocA; exact HX45 | lia].
jreg HS (2%bv:reg) as Hm2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hm2.
jreg HS (4%bv:reg) as Hm4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hm4.
jreg HS (1%bv:reg) as Hm1.
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := 3 * ngp) (spc := sp0 - 144);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact Hm10 | exact HRES0 | apply (hdr_pal_room b0 plen HROOM); unfold PALMAX; clear - RN; lia
| exact Hm2 | lia | exact Hspm | lia | lia | exact Hm4 | exact Hm1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hres10 & Hres & Hkeep2 & Hhi2 & HR2). clear HJ.
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep2, Hhi2. cbn [ms_regs ms_mem mkst] in HP2, Hkeep2, Hhi2, HJ2, Hres10.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
jafter_call_keep HS 49%nat regs2 mem2 HP2 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
{ repeat (apply Forall_cons; [eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia] |]). apply Forall_nil. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq.
cbn [ms_regs mkst] in Hq. rewrite Hres10 in Hq. symmetry in Hq.
destruct Hres as (Hnz & Hres16 & (b1 & b2 & Hbl2 & Hblc) & Hwr).
assert (Hpin : In (res, 3 * ngp) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
destruct (blocks_range _ _ LAWS L2 A2 mem2 md2 res (3 * ngp) HH2 Hpin) as [Hr0 Hr1].
assert (HB2 : Permutation (blocks L2 A2) ((res, 3 * ngp) :: blocks L A)).
{ rewrite Hbl2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite <- Hblc. exact HB. }
assert (Hfresh : In (res, 3 * ngp) (blocks L A) -> 3 * ngp <= 0).
{ intros Hin. destruct (Z_lt_le_dec 0 (3 * ngp)) as [Hl|Hl]; [|exact Hl]. exfalso.
apply (fresh_not_in API L2 A2 mem2 md2 b1 b2 res (3 * ngp) HH2 Hbl2 Hl). rewrite <- Hblc. eapply Permutation_in; [apply Permutation_sym; exact HB|]. exact Hin. }
assert (Hpd2 : In (pdata, nb) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | right; exact Hpd]).
add_fact HS 53%nat (mkAF 4096 CEIL_MAX 4).
2:{ rewrite Hq, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
jrun_to LAWS ubs0tbl_ok HS HJ2 ubs0_A_readdata.
{ wr_tail HU2. }
jreg HS (10%bv:reg) as R10. rewrite HU2 in R10. replace (sp0 - 144 + 8) with (sp0 - 136) in R10 by lia.
jreg HS (11%bv:reg) as R11. rewrite Hq in R11.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs0segs Ec ssc msc 12%bv HS) as R12; eval_sr_get_in R12 end.
rewrite denot_lit_U, (U_three _ 45 ngp) in R12 by first [ew_havocA; exact HX45 | lia].
jreg HS (2%bv:reg) as R2. rewrite (HE 2%nat 2%bv eq_refl), G2 in R2.
jreg HS (1%bv:reg) as R1.
assert (Hst8 : (sp0 - 136) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16. replace (sp0 - 136) with ((2 * (sp0 / 16) - 17) * 8) by lia. apply Z_mod_mult. }
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH3.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => assert (HPLc : garr8 ubs0segs (ms_mem msx) pdata PAYLOAD) end.
{ eapply garr8_frame; [exact HPL|]. intros a Ha. rewrite HPLn in Ha.
pose proof HJ2 as (_ & _ & _ & Hblk3 & _). replace a with (pdata + (a - pdata)) by lia.
apply (Hblk3 pdata nb (a - pdata) Hpd Hpd2); [lia | intros (rr & [] & _)]. }
eapply SR_bind.
{ eapply (jreaddata API IMG) with (st := sp0 - 136) (d := res) (n := 3 * ngp) (pdata := pdata) (nb := nb) (cur := cur) (spc := sp0 - 144);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact R10 | exact R11 | exact R12 | exact R2 | exact Hspm
| unfold RD_FRAME; lia | lia | lia | exact R1 | apply ret_ok_even; vm_compute; reflexivity
| lia | lia | exact Hst8
| tail_word HS HU2 1%nat 8 (SOff 36 0) ltac:(atom_tac HX36); lia
| tail_word HS HU2 1%nat 16 (SOff 37 0) ltac:(atom_tac HX37); lia
| tail_word HS HU2 2%nat 24 (SOff 38 0) ltac:(atom_tac HX38); lia
| lia | lia | lia | lia | lia | lia
| intros j Hj; exact (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 pdata nb j HH3 Hpd2 Hj))
| lia | lia
| intros i Hi; exact (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 res (3 * ngp) i HH3 Hpin Hi))
| intros a Ha; replace a with (res + (a - res)) by lia; apply (Hwr (blocks L2 A2)); [exact Hpin | lia]
| intros a Ha; left; lia
| unfold RD_FRAME; lia | unfold RD_FRAME; lia | unfold RD_FRAME; lia | lia | lia
| intros _; destruct (heap_sep _ _ LAWS L2 A2 mem2 md2 b1 (res, 3 * ngp) b2 (pdata, nb) HH2 Hbl2 ltac:(rewrite <- Hblc; exact Hpdc)) as [H0|H0]; cbn [fst snd] in H0; lia ]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & HP3 & Hout3 & Hgr3 & Hrd3). clear HJ2.
jafter_call_keep HS 65%nat regs3 mem3 HP3 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK3 : P); [|specialize (HS2 HK3); clear HK3] end.
{ repeat (apply Forall_cons; [eapply region_kept_rd; [exact Hout3 | exact Hgr3 | ..]; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocA; rewrite ?HU2; unfold RD_FRAME; lia |]). apply Forall_nil. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq3. cbn [ms_regs mkst] in Hq3. symmetry in Hq3.
jrun LAWS ubs0tbl_ok HS HJ3.
{ wr_tail HU2. }
jbranch ubs0tbl HS.
+ assert (HNONE : ff_cfg PAYLOAD = None).
{ destruct (Z_lt_le_dec (Z.of_nat (length PAYLOAD)) 14) as [Hsh|Hge]; [exact (HSHORT Hsh)|].
destruct (HDRS Hge) as [Z1 Z2]. destruct (HDRV Z1 Z2) as [Hc14 HH5].
destruct Hrd3 as [(Hfit & H10 & _ & _) | (Hnfit & _ & _ & _)].
- exfalso. rewrite branch_ne_U, U_lit in Hc by lia.
lazymatch type of Hc with context [U ?E1 (SAlu ALU_OR ?ea (SAlu ALU_OR ?eb ?ec))] =>
rewrite (U_or_zero_intro E1 ea (SAlu ALU_OR eb ec) (U_atom E1 69 0 ltac:(rewrite Hq3, H10; reflexivity) ltac:(lia))
(U_or_zero_intro E1 eb ec (U_atom E1 8 0 ltac:(ew_havocA; rewrite HE8, Z1; reflexivity) ltac:(lia))
(U_atom E1 10 0 ltac:(ew_havocA; rewrite HE10, Z2; reflexivity) ltac:(lia)))) in Hc end.
discriminate Hc.
- apply (ff_cfg_pal_short PAYLOAD W H attr gen ngp HH5 Hattr4); [exact Hge | rewrite HPLn; lia]. }
clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ3 L_FREERET.
{ wr_tail HU2. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here. unfold ff_tree. rewrite HNONE. unfold ff_leaf.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_freeret_x rg L2 A2 mm md2 res (3 * ngp) (rb_malloc b0 (3 * ngp))) end; try assumption.
* right. split; [exact HB2 | exact Hfresh].
* fold sp0. saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* fold sp0. tail_word HS HU2 0%nat 64 (SOff 53 0) ltac:(atom_tac Hq). lia.
* ut_tac HS HE.
* apply (main_bud_fin b0 plen). apply (hdr_pal_bud b0). unfold PALMAX. clear - RN. lia.
+ rewrite branch_ne_U, U_lit in Hc by lia. apply Bool.negb_false_iff in Hc. apply Z.eqb_eq in Hc.
apply U_or_zero in Hc as [Hc69 Hc].
destruct (HDR0 _ ltac:(ew_havocA; reflexivity) ltac:(ew_havocA; reflexivity) Hc) as [Hc14 HH5]. clear Hc.
destruct Hrd3 as [(Hfit & H10 & Wc3 & Hcp3) | (Hnfit & H10 & _ & _)].
2:{ exfalso. rewrite (U_atom _ 69 (2 ^ 64 - 1)) in Hc69 by first [rewrite Hq3, H10; reflexivity | lia]. lia. }
assert (HGP3 : garr8 ubs0segs mem3 res (firstn (Z.to_nat (3 * ngp)) (skipn (Z.to_nat cur) PAYLOAD)) /\ Z.of_nat (length (firstn (Z.to_nat (3 * ngp)) (skipn (Z.to_nat cur) PAYLOAD))) = 3 * ngp).
{ apply (garr8_slice_copy _ mem3 pdata PAYLOAD res cur (3 * ngp) HPLc); [lia | lia | rewrite HPLn; lia | ]. intros i Hi. exact (Hcp3 i Hi). }
destruct HGP3 as [HGP3 HGPn]. rewrite Hc14 in HGP3, HGPn. change (Z.to_nat 14) with 14%nat in HGP3, HGPn.
jrun_to LAWS ubs0tbl_ok HS HJ3 L_NCHK.
{ wr_tail HU2. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_nchk_x rg L2 A2 mm md2 pdata nb (cur + 3 * ngp) res attr gen W H ngp PAYLOAD (firstn (Z.to_nat (3 * ngp)) (skipn 14 PAYLOAD)) (rb_malloc b0 (3 * ngp))) end; try assumption.
* rewrite (proj2 (Z.eqb_eq _ _) Hattr4). cbn [app]. exact HB2.
* intros Hne. exfalso. exact (Hne Hattr4).
* fold sp0. cfg_obj_u HS HU2 (SOff 53 0) ltac:(atom_tac Hq) Rcfg HCV.
* fold sp0. saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
* fold sp0. tail_word HS HU2 1%nat 8 (SOff 36 0) ltac:(atom_tac HX36). lia.
* fold sp0. tail_word HS HU2 1%nat 16 (SOff 37 0) ltac:(atom_tac HX37). lia.
* fold sp0. apply (word_mem_frame mem3); [replace (sp0 - 120) with (sp0 - 136 + 16) by lia; exact Wc3 |].
intros i Hi. mem_back ltac:(rewrite ?HU2) ltac:(lia).
* lia.
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* ut_tac HS HE.
* rewrite (proj2 (Z.eqb_eq _ _) Hattr4). lia.
* intros _. split; [rewrite HPLn; lia | reflexivity].
* intros Hne. exfalso. exact (Hne Hattr4).
* intros _. split; [|exact HGPn]. eapply garr8_frame; [exact HGP3|]. intros a Ha. rewrite HGPn in Ha.
mem_back ltac:(rewrite ?HU2) ltac:(lia).
* apply (hdr_pal_bud b0). unfold PALMAX. clear - RN. lia.
Qed.
End S.
End f.
