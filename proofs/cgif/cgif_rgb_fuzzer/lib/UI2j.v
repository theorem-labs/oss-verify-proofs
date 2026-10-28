(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m UO3n
YI00 YI02 YI01 YI07 YI03 YI04 YI05 YI06 UI2m UI2a UI2b UI25.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac inlist := cbv; repeat (first [ left; reflexivity | right ]).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition TPC_INIT : Z := ubs2_A_LZW_GenerateStream + 0x11c.
Definition TPC_EALLOC2 : Z := ubs2_A_LZW_GenerateStream + 0x720.
Definition ss_tentry : sstate :=
mkSS ubs2_A_LZW_GenerateStream sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-112) 0 (-112) 0 [] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + 8400) (2^63 - 16) 4); (13%nat, mkAF 2 256 0); (11%nat, mkAF 1 100000000 0);
(14%nat, mkAF 0 12 0); (10%nat, mkAF CEIL_MIN (2^63 - 16) 3); (12%nat, mkAF 4096 CEIL_MAX 0) ] [] []).
Definition ss_tentry_c : sstate := Eval vm_compute in ss_tentry.
Definition gzero_chunks : list YQ0b.chunk :=
[ mkChunk 0 (CVal 8 (SLit 0)); mkChunk 8 (CVal 8 (SLit 0)); mkChunk 16 (CVal 8 (SLit 0)); mkChunk 24 (CVal 8 (SLit 0));
mkChunk 32 (CVal 8 (SLit 0)); mkChunk 40 (CVal 8 (SLit 0)); mkChunk 48 (CVal 8 (SLit 0)); mkChunk 56 (CVal 4 (SLit 0));
mkChunk 60 (CVal 4 (SLit 0)); mkChunk 64 (CVal 2 (SLit 0)); mkChunk 66 (CVal 2 (SLit 0)) ].
Definition gzero_region : YQ0b.region := YQ0b.mkRegion (Some 36%nat) 0 72 0 72 gzero_chunks.
Lemma tblocks_after_malloc : forall (res n : Z) prev B0 (bl1 bl2 : list (Z * Z)),
Permutation bl1 (nz prev ++ B0) ->
(res = 0 /\ bl2 = bl1) \/ (res <> 0 /\ exists b1 b2, bl2 = b1 ++ (res, n) :: b2 /\ bl1 = b1 ++ b2) ->
Permutation bl2 (nz ((res, n) :: prev) ++ B0).
Proof.
intros res n prev B0 bl1 bl2 HP [[-> ->] | (Hnz & b1 & b2 & -> & ->)].
- rewrite nz_cons0. exact HP.
- rewrite nz_cons_nz by exact Hnz. cbn [app]. rewrite <- HP. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma tblocks_after_malloc_end : forall (res n : Z) prev B0 (bl1 bl2 : list (Z * Z)),
Permutation bl1 (nz prev ++ B0) ->
(res = 0 /\ bl2 = bl1) \/ (res <> 0 /\ exists b1 b2, bl2 = b1 ++ (res, n) :: b2 /\ bl1 = b1 ++ b2) ->
Permutation bl2 (nz (prev ++ [(res, n)]) ++ B0).
Proof.
intros res n prev B0 bl1 bl2 HP [[-> ->] | (Hnz & b1 & b2 & -> & ->)]; unfold nz in *; rewrite filter_app; cbn [List.filter fst].
- change (0 =? 0) with true. cbn. rewrite app_nil_r. exact HP.
- destruct (Z.eqb_spec res 0); [lia|]. cbn [negb]. rewrite <- app_assoc. cbn [app].
eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
eapply Permutation_trans; [apply perm_skip; exact HP|]. apply Permutation_middle.
Qed.
Lemma tnz_cases_front : forall (b : Z * Z) res n prev,
In b (nz ((res, n) :: prev)) -> (b = (res, n) /\ res <> 0) \/ In b (nz prev).
Proof.
intros b res n prev H. destruct (Z.eq_dec res 0) as [Hz|Hnz].
- right. rewrite Hz, nz_cons0 in H. exact H.
- rewrite nz_cons_nz in H by exact Hnz. destruct H as [<-|H]; [left; auto | right; exact H].
Qed.
Lemma tnz_cases_end : forall (b : Z * Z) res n prev,
In b (nz (prev ++ [(res, n)])) -> (b = (res, n) /\ res <> 0) \/ In b (nz prev).
Proof.
intros b res n prev H. unfold nz in *. rewrite filter_app in H.
apply in_app_iff in H as [H|H]; [right; exact H|].
cbn [List.filter fst] in H. destruct (Z.eqb_spec res 0); cbn [negb] in H; [destruct H|].
destruct H as [<-|[]]. left. auto.
Qed.
Lemma tnz_id : forall l : list (Z * Z), (forall b, In b l -> fst b <> 0) -> nz l = l.
Proof.
induction l as [|[p n] l IH]; intros H; [reflexivity|].
rewrite nz_cons_nz by (apply (H (p, n)); left; reflexivity). f_equal. apply IH. intros b Hb. apply H. right. exact Hb.
Qed.

Lemma region_kept_block_w : forall E (mem mem' : word -> option byte) n lo hi wlo whi cs b m (bl : list (Z * Z)),
bv_unsigned (ew E n) = b -> In (b, m) bl ->
(forall b' m' i, In (b', m') bl -> 0 <= i < m' -> mbyte ubs2segs mem' (b' + i) = mbyte ubs2segs mem (b' + i)) ->
(forall i, 0 <= i < m -> present mem' (b + i)) ->
0 <= lo -> hi <= m -> lo <= wlo -> whi <= hi ->
region_kept ubs2segs E mem mem' (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E mem mem' n lo hi wlo whi cs b m bl Hn Hin Hk Hp Hlo Hhi Hwlo Hwhi.
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; rewrite Hn; intros a Ha.
- replace a with (b + (a - b)) by lia. apply (Hk b m (a - b) Hin). lia.
- intros _. apply (present_writable ubs2_msyms). replace a with (b + (a - b)) by lia. apply Hp. lia.
Qed.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition tlzw_post (STK sp0 : Z) FP L A mem md Lc Ac (memc : word -> option byte) (regs : bvmap 5 word) (pR : Z) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom ubs2segs)) md2 /\
journal ubs2_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\ regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - LZW_STK <= a < spZ regs) -> ~ (pR <= a < pR + 12) ->
mbyte ubs2segs mem2 a = mbyte ubs2segs memc a) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs memc (b + i)) /\
((res = 0 /\
exists bb Lbb M,
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks Lc Ac) /\
(forall blc i, In (bb, Lbb) blc -> 0 <= i < Lbb -> wr_byte STK sp0 FP (blocks L A) blc (bb + i)) /\
word_mem ubs2segs mem2 pR bb /\ val_mem ubs2segs mem2 (pR + 8) 4 M /\ 1 <= M <= Lbb)
\/ ((res = 2 \/ res = 5) /\
Permutation (blocks L2 A2) (blocks Lc Ac) /\
(forall a, pR <= a < pR + 12 -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a))).
Definition tpro_ok (STK sp0 : Z) FP L A mem md Lc Ac (memc : word -> option byte) (regs : bvmap 5 word)
(pR nP img idl icl : Z) (c' : config) : Prop :=
exists L6 A6 regs6 mem6 md6 (g ti lm lc li tm ld : Z),
c' = mkCfg (mkst regs6 (Z_to_bv 64 TPC_INIT) mem6 (seg_rom ubs2segs)) md6 /\
journal ubs2_msyms MR STK sp0 FP L A mem md L6 A6 mem6 md6 /\ st_init_done A6 = true /\
getr regs6 2 = Z_to_bv 64 (spZ regs - 112) /\ getr regs6 3 = getr regs 3 /\ getr regs6 4 = getr regs 4 /\
getr regs6 8 = Z_to_bv 64 g /\ getr regs6 20 = Z_to_bv 64 idl /\ getr regs6 21 = Z_to_bv 64 (2 * idl) /\
getr regs6 18 = Z_to_bv 64 pR /\ getr regs6 19 = Z_to_bv 64 icl /\ getr regs6 9 = Z_to_bv 64 2 /\
frame_saved ubs2_msyms regs mem6 (spZ regs) /\
word_mem ubs2segs mem6 g ti /\ word_mem ubs2segs mem6 (g + 8) lm /\ word_mem ubs2segs mem6 (g + 16) lc /\
word_mem ubs2segs mem6 (g + 24) li /\ word_mem ubs2segs mem6 (g + 32) tm /\ word_mem ubs2segs mem6 (g + 40) ld /\
word_mem ubs2segs mem6 (g + 48) img /\ val_mem ubs2segs mem6 (g + 56) 4 nP /\
val_mem ubs2segs mem6 (g + 60) 4 0 /\ val_mem ubs2segs mem6 (g + 64) 2 0 /\ val_mem ubs2segs mem6 (g + 66) 2 0 /\
let tabs := [ (ld, 2 * (nP / (4094 - idl) + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl) ] in
Permutation (blocks L6 A6) (tabs ++ (g, 72) :: blocks Lc Ac) /\
(forall b, In b tabs -> wtok' STK sp0 FP (blocks L A) b /\ fst b <> 0) /\ wtok' STK sp0 FP (blocks L A) (g, 72) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> ~ (g <= b + i < g + 72)) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - LZW_STK <= a < spZ regs) ->
mbyte ubs2segs mem6 a = mbyte ubs2segs memc a) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte ubs2segs mem6 (b + i) = mbyte ubs2segs memc (b + i)).
Lemma tlzw_pro :
forall STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (pR nP img idl icl bi Li : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs 1) -> getr regs 4 = Z_to_bv 64 (ms_tp ubs2_msyms) ->
getr regs 10 = Z_to_bv 64 pR -> getr regs 11 = Z_to_bv 64 nP -> getr regs 12 = Z_to_bv 64 img ->
getr regs 13 = Z_to_bv 64 idl -> getr regs 14 = Z_to_bv 64 icl ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LZW_STK ->
spZ regs <= pR -> pR + 16 <= sp0 -> pR mod 8 = 0 ->
1 <= nP <= 100000000 -> 2 <= idl <= 256 -> 0 <= icl <= 12 ->
In (bi, Li) (blocks Lc Ac) -> bi <= img -> img + nP <= bi + Li ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_LZW_GenerateStream) memc (seg_rom ubs2segs)) mdc)
(fun c' => tlzw_post STK sp0 FP L A mem md Lc Ac memc regs pR c' \/
tpro_ok STK sp0 FP L A mem md Lc Ac memc regs pR nP img idl icl c').
Proof.
intros STK sp0 FP L A mem md Lc Ac mdc regs memc pR nP img idl icl bi Li
HJ Hid Hra0 Htp0 G10 G11 G12 G13 G14 Hal16 Hwlo HpR1 HpR2 HpR8 HnP Hidl Hicl Hbi Hbi1 Hbi2.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HCSv : CALLOC_STACK = 8224) by reflexivity.
assert (HSTKv : LZW_STK = 8400) by reflexivity.
pose proof HJ as (HH0 & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc bi Li HH0 Hbi ltac:(lia)) as (Hbi0 & Hbi3 & _).
set (sp := spZ regs) in *.
assert (Hspm : (sp - 112) mod 16 = 0).
{ replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
remember (Ereg regs []) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HE13 : ew E 13 = Z_to_bv 64 idl) by (rewrite (HE 13%nat 13%bv eq_refl); exact G13).
assert (HE11 : ew E 11 = Z_to_bv 64 nP) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
assert (HE14 : ew E 14 = Z_to_bv 64 icl) by (rewrite (HE 14%nat 14%bv eq_refl); exact G14).
assert (HE10 : ew E 10 = Z_to_bv 64 pR) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE12 : ew E 12 = Z_to_bv 64 img) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (HS : st_ok ubs2segs E ss_tentry_c (mkst regs (Z_to_bv 64 ubs2_A_LZW_GenerateStream) memc (seg_rom ubs2segs))).
{ change ss_tentry_c with ss_tentry. unfold ss_tentry. rewrite HE0. apply entry_st_ok; rewrite <- ?HE0.
- vm_compute. reflexivity.
- constructor; [|constructor].
apply (region_ok_stack ubs2segs _ memc 2 sp); [exact HE2 | lia | lia |].
intros a Ha. apply Hstw. lia.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE13, HE11, HE14, HE10, HE12, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
clear HE0.
change memc with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_LZW_GenerateStream) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc.
{ eapply wr_ok_cons_win; [reflexivity | exact HE2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
assert (MHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - LZW_STK <= a < sp) ->
mbyte ubs2segs (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_LZW_GenerateStream) memc (seg_rom ubs2segs))) a = mbyte ubs2segs memc a)
by (intros; reflexivity).
assert (MBL : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte ubs2segs (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_LZW_GenerateStream) memc (seg_rom ubs2segs))) (b + i) = mbyte ubs2segs memc (b + i))
by (intros; reflexivity).
Ltac fold_frame MHI MBL HE2 HH0 Hgnot :=
lazymatch goal with HF : frame_of ?E1 ?rs ?m ?m' |- _ =>
let MHI2 := fresh "MHI" in let MBL2 := fresh "MBL" in
lazymatch type of MHI with forall a, _ -> ~ (?spv - LZW_STK <= a < _) -> _ = mbyte _ ?m0 a =>
lazymatch type of MBL with forall b mm i, In (b, mm) ?Bf -> _ =>
assert (MHI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spv - LZW_STK <= a < spv) -> mbyte ubs2segs m' a = mbyte ubs2segs m0 a)
by (intros a Ha Hna; rewrite <- (MHI a Ha Hna); apply tmbyte_eq_of1; apply HF;
rewrite unsigned_lit_small by lia;
intros (r0 & Hr0 & Hin0); cbv [In] in Hr0;
repeat (destruct Hr0 as [<- | Hr0]; [cbn [r_base r_wlo r_whi base_val] in Hin0; repeat (rewrite ew_havoc_old in Hin0; [|cbv; lia]); rewrite ?HE2 in Hin0;
first [lia | Hgnot Hin0] |]);
destruct Hr0);
assert (MBL2 : forall b mm i, In (b, mm) Bf -> 0 <= i < mm -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs m0 (b + i))
by (intros b mm i Hb Hi; rewrite <- (MBL b mm i Hb Hi); apply tmbyte_eq_of1; apply HF;
destruct (heap_blocks _ _ LAWS _ _ _ _ b mm i HH0 Hb Hi) as (_ & Hb0 & Hb1 & _);
rewrite unsigned_lit_small by lia;
intros (r0 & Hr0 & Hin0); cbv [In] in Hr0;
repeat (destruct Hr0 as [<- | Hr0]; [cbn [r_base r_wlo r_whi base_val] in Hin0; repeat (rewrite ew_havoc_old in Hin0; [|cbv; lia]); rewrite ?HE2 in Hin0;
first [lia | Hgnot Hin0 b mm i Hb Hi] |]);
destruct Hr0);
clear MHI MBL HF; rename MHI2 into MHI; rename MBL2 into MBL
end end end.
Ltac no_g H := fail.
fold_frame MHI MBL HE2 HH0 no_g.
Ltac reg_U HS r Utac H :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
pose proof (st_ok_reg segs E1 ss1 ms1 r HS) as H; eval_sr_get_in H;
rewrite denot_lit_U in H;
lazymatch type of H with _ = Z_to_bv 64 (U ?E2 ?e) =>
let v := fresh "v" in let Hv := fresh "Hv" in
evar (v : Z); assert (Hv : U E2 e = v); [subst v; Utac | rewrite Hv in H; subst v; clear Hv] end end.
Ltac regq HS HE rr :=
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q := fresh "Q" in
pose proof (st_ok_reg ubs2segs Ef ssf msf rr HS) as Q; eval_sr_get_in Q; cbn [sv_denot] in Q;
repeat (rewrite ew_havoc_old in Q; [|cbv; lia]); rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Q;
repeat match type of Q with context [ew _ ?n] => rewrite (HE n (Z_to_bv 5 (Z.of_nat n))) in Q by reflexivity end;
cbn [ms_regs mkst]; rewrite Q; clear Q
end.
(jreg HS (10%bv:reg) as M10); (jreg HS (2%bv:reg) as M2); (jreg HS (4%bv:reg) as M4); (jreg HS (1%bv:reg) as M1).
cbn [ms_regs mkst] in M10, M2, M4, M1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low_lzw IMG (aa_malloc API)) with (n := 72) (spc := sp - 112);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact M10 | lia
| rewrite M2, HE2; reflexivity | lia | exact Hspm | lia | lia
| rewrite M4, (HE 4%nat (4%bv:reg) eq_refl); exact Htp0
| exact M1 | apply ret_ok_even; vm_compute; reflexivity ]. }
clear M10 M2 M4 M1.
intros c' (L1 & A1 & regs1 & mem1 & md1 & g & -> & HJ1 & Hid1 & HP1 & Hr10 & Hres & Hkeep & Hhi).
clear HJ Hid. change (ms_segs ubs2_msyms) with ubs2segs in Hkeep, Hhi.
lazymatch type of MHI with forall a, _ -> _ -> _ = mbyte _ ?m1 a =>
assert (MHI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - LZW_STK <= a < sp) -> mbyte ubs2segs mem1 a = mbyte ubs2segs m1 a)
by (intros a Ha Hna; rewrite (proj1 (Hhi a Ha ltac:(clear - Ha Hna HCSv HSTKv HASv; lia))); exact (MHI a Ha Hna));
assert (MBL2 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mem1 (b + i) = mbyte ubs2segs m1 (b + i))
by (intros b m i Hb Hi; rewrite (Hkeep b m i Hb Hi); exact (MBL b m i Hb Hi))
end.
clear MHI MBL Hkeep; rename MHI2 into MHI; rename MBL2 into MBL.
jafter_call HS 32%nat regs1 mem1 HP1 HS1.
match type of HS1 with ?P -> _ => assert (HK : P);
[ constructor; [|constructor];
eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HE2 | exact Hhi | lia | lia | lia | cbn; lia | cbn; lia]
| specialize (HS1 HK); clear HK HS Hhi HP1; rename HS1 into HS ] end.
(jreg HS (10%bv:reg) as Hatom); cbn [ms_regs mkst] in Hatom; rewrite Hr10 in Hatom; symmetry in Hatom.
rename HJ1 into HJ; rename Hid1 into Hid.
destruct Hres as [[-> HBeq] | (Hgnz & Hg16 & (gb1 & gb2 & HBg & HBc) & Wg)].
{
pin_reg' HS (10%bv:reg) 0 Hr10.
jrun LAWS ubs2tbl_ok HS HJ.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
fold_frame MHI MBL HE2 HH0 no_g.
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
left. unfold tlzw_post.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf => exists L1, A1, (ms_regs msf), (ms_mem msf), md1, 2 end.
split. { regq HS HE (1%bv:reg). rewrite Hra0. reflexivity. }
split; [exact HJ|]. split; [exact Hid|].
split.
{ apply regs_preserved_intro_lzw.
- regq HS HE (2%bv:reg). reflexivity.
- regq HS HE (3%bv:reg). reflexivity.
- regq HS HE (4%bv:reg). reflexivity.
- regq HS HE (8%bv:reg). reflexivity.
- regq HS HE (9%bv:reg). reflexivity.
- regq HS HE (18%bv:reg). reflexivity.
- regq HS HE (19%bv:reg). reflexivity.
- regq HS HE (20%bv:reg). reflexivity.
- regq HS HE (21%bv:reg). reflexivity.
- regq HS HE (22%bv:reg). reflexivity.
- regq HS HE (23%bv:reg). reflexivity.
- regq HS HE (24%bv:reg). reflexivity.
- regq HS HE (25%bv:reg). reflexivity.
- regq HS HE (26%bv:reg). reflexivity.
- regq HS HE (27%bv:reg). reflexivity. }
split; [regq HS HE (10%bv:reg); reflexivity|].
cbn [ms_mem mkst].
split; [intros a Ha Hna Hnp; apply MHI; [exact Ha | exact Hna]|].
split; [exact MBL|].
right. split; [left; reflexivity|]. split; [rewrite HBeq; apply Permutation_refl|].
intros a Ha. apply MHI; lia. }
assert (HBg1 : In (g, 72) (blocks L1 A1)) by (rewrite HBg; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ g 72 (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) HBg1 ltac:(lia)) as (Rg0 & Rg1 & _).
assert (Hgsep : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> ~ (g <= b + i < g + 72)).
{ intros b m i Hb Hi.
pose proof (mr_blocks_disjoint ubs2_msyms MR LAWS L1 A1 mem1 md1 (proj1 (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ))) as HPW.
rewrite HBg in HPW. rewrite HBc in Hb.
destruct (pairwise_app_mid _ _ _ _ _ HPW Hb) as [Hd|Hd]; unfold ranges_disjoint in Hd; cbn [fst snd] in Hd; lia. }
assert (HB : Permutation (blocks L1 A1) (nz [] ++ (g, 72) :: blocks Lc Ac)).
{ cbn [nz List.filter app]. rewrite HBg, HBc. apply Permutation_sym. apply Permutation_middle. }
assert (Htok : forall b, In b (nz []) -> wtok' STK sp0 FP (blocks L A) b /\ fst b <> 0) by (intros b Hb; destruct Hb).
assert (Wg' : wtok' STK sp0 FP (blocks L A) (g, 72)) by (intros blc i Hin Hi; apply (Wg blc i Hin Hi)).
clear HBg HBc gb1 gb2 Wg Hr10.
add_fact' HS 36%nat (mkAF 4096 CEIL_MAX 4); [| rewrite Hatom, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia].
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
fold_frame MHI MBL HE2 HH0 no_g.
(jreg HS (10%bv:reg) as Mm10); (jreg HS (11%bv:reg) as Mm11); (jreg HS (12%bv:reg) as Mm12); (jreg HS (1%bv:reg) as Mm1).
cbn [ms_regs mkst] in Mm10, Mm11, Mm12, Mm1. rewrite Hatom in Mm10.
eapply SR_bind.
{ lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset ubs2_memset_spec E1 ss1 ms1 _ _ _ _ _ _ _ _ _ _ g 0 72);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Mm10 | exact Mm11 | exact Mm12 | exact Mm1
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia
| intros i Hi; apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ g 72 i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) HBg1 Hi))
| intros a Ha; eapply (wr_byte_of_wtok _ _ _ _ _ g 72); [exact Wg' | exact HBg1 | lia] ] end. }
clear Mm10 Mm11 Mm12 Mm1.
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Zg). clear HJ. rename HJ2 into HJ.
lazymatch type of MHI with forall a, _ -> _ -> _ = mbyte _ ?m1 a =>
assert (MHI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - LZW_STK <= a < sp) -> mbyte ubs2segs mem2 a = mbyte ubs2segs m1 a)
by (intros a Ha Hna; rewrite <- (MHI a Ha Hna); apply tmbyte_eq_of1; apply Hout2; rewrite unsigned_lit_small by lia; lia);
assert (MBL2 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs m1 (b + i))
by (intros b m i Hb Hi; rewrite <- (MBL b m i Hb Hi); apply tmbyte_eq_of1; apply Hout2;
destruct (heap_blocks _ _ LAWS _ _ _ _ b m i HH0 Hb Hi) as (_ & Hb0 & Hb1 & _);
pose proof (Hgsep b m i Hb Hi); rewrite unsigned_lit_small by lia; lia)
end.
clear MHI MBL; rename MHI2 into MHI; rename MBL2 into MBL.
jafter_stretch HS 48%nat regs2 mem2 MEMSET_CLOB (ubs2_A_LZW_GenerateStream + 0x68) HS2.
specialize (HS2 Hfr2).
match type of HS2 with ?P -> _ => assert (HK : P);
[ constructor; [|constructor];
(eapply region_kept_outside; [exact Hout2 | exact Hgr2 | | | | cbn; lia | cbn; lia]);
cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite ?HE2; lia
| specialize (HS2 HK); clear HK HS Hfr2 Hout2 Hgr2 Hd10; rename HS2 into HS ] end.
clear HBg1.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
pose proof (st_ok_add_region' ubs2segs E1 ss1 ms1 gzero_region HS ltac:(vm_compute; reflexivity)) as HS' end.
match type of HS' with ?P -> ?Q -> _ => assert (HRG : P); [| assert (HDJ : Q); [| specialize (HS' HRG HDJ); clear HS HRG HDJ; rename HS' into HS]] end.
{ unfold region_ok, gzero_region. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havoc. rewrite Hatom, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. cbn [ms_mem]. apply (present_writable ubs2_msyms).
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ g 72 o (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | left; reflexivity]) Ho)). }
unfold gzero_chunks.
Ltac zck Zg := eapply chunk_ok_val; [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia
| intros k Hk; cbn [ms_mem]; rewrite <- Z.add_assoc; rewrite Zg by (cbn in Hk; lia); rewrite le_byte_small by (cbn in Hk |- *; lia); rewrite Z.shiftr_0_l; reflexivity].
repeat (apply Forall_cons; [zck Zg|]). apply Forall_nil. }
{ lazymatch type of HS with st_ok _ _ ?ss1 _ => let m := eval vm_compute in (ss_mem ss1) in change (ss_mem ss1) with m end.
cbn [all_disjoint]. unfold extent_disjoint, gzero_region. cbn [r_base r_lo r_hi base_val].
ew_havoc. rewrite Hatom, unsigned_lit_small by lia. ew_havoc. rewrite HE2. split; [lia | exact I]. }
lazymatch type of HS with st_ok _ _ ?ss1 _ => let v := eval vm_compute in ss1 in change ss1 with v in HS end.
assert (Htisz : 8 <= 2 * idl * idl <= 131072) by (apply ttisz_range; exact Hidl).
Ltac run_wr HE2 Hatom Wg' HB :=
wr_norm;
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 36); [reflexivity | ew_havoc; rewrite Hatom; apply unsigned_lit_small; lia | |];
[ cbn [r_wlo r_whi]; intros a Ha;
lazymatch type of Wg' with wtok' _ _ _ _ (?g, _) =>
eapply (wr_byte_of_wtok _ _ _ _ _ g 72); [exact Wg' | eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; right; left; reflexivity] | lia] end
| eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |]; apply wr_ok_nil ].
Ltac gsep Hgsep Hin0 b mm i Hb Hi := pose proof (Hgsep b mm i Hb Hi); lia.
Ltac gsep1 Hgsep Hin0 := fail.
Ltac do_malloc HS HJ Hid nsz Utac k MHI MBL HB Htok HE2 Hspm Htp0 HE Hatom Lblocks Lcases :=
let M10 := fresh "M10" in let M2 := fresh "M2" in let M4 := fresh "M4" in let M1 := fresh "M1" in
reg_U HS (10%bv:reg) Utac M10;
(jreg HS (2%bv:reg) as M2); (jreg HS (4%bv:reg) as M4); (jreg HS (1%bv:reg) as M1);
eapply SR_bind;
[ eapply (jmalloc_at _ _ LAWS ubs2_errno_low_lzw IMG (aa_malloc API)) with (n := nsz) (spc := _);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact M10 | lia
| rewrite M2, HE2; reflexivity | lia | exact Hspm | lia | lia
| rewrite M4, (HE 4%nat (4%bv:reg) eq_refl); exact Htp0
| exact M1 | apply ret_ok_even; vm_compute; reflexivity ]
| ];
clear M10 M2 M4 M1;
let L2 := fresh "L" in let A2 := fresh "A" in let regs2 := fresh "regs" in let mem2 := fresh "mem" in let md2 := fresh "md" in
let res := fresh "res" in
let HJ2 := fresh "HJ" in let Hid2 := fresh "Hid" in let HP2 := fresh "HP" in let Hr10 := fresh "Hr10" in let Hres := fresh "Hres" in
let Hkeep := fresh "Hkeep" in let Hhi := fresh "Hhi" in
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hr10 & Hres & Hkeep & Hhi);
clear HJ Hid; change (ms_segs ubs2_msyms) with ubs2segs in Hkeep, Hhi;
let Hrr := fresh "Hrr" in
assert (Hrr : 0 <= res < alloc_ceiling)
by (destruct Hres as [[Hz _]|(Hnz & _ & (b1 & b2 & HB2eq & _) & _)];
[ rewrite Hz; pose proof alloc_ceiling_val; lia
| pose proof (heap_blocks_range _ _ LAWS _ _ _ _ res nsz (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2)
ltac:(rewrite HB2eq; apply in_app_iff; right; left; reflexivity) ltac:(lia)); lia ]);
let Hgin := fresh "Hgin" in
pose proof (Permutation_in _ (Permutation_sym HB) ltac:(apply in_app_iff; right; left; reflexivity)) as Hgin;
let MHI2 := fresh "MHI" in let MBL2 := fresh "MBL" in
lazymatch type of MHI with forall a, _ -> ~ (?spv - LZW_STK <= a < _) -> _ = mbyte _ ?m1 a =>
lazymatch type of MBL with forall b m i, In (b, m) ?Bf -> _ =>
assert (MHI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spv - LZW_STK <= a < spv) -> mbyte ubs2segs mem2 a = mbyte ubs2segs m1 a)
by (intros a Ha Hna; rewrite (proj1 (Hhi a Ha ltac:(clear - Ha Hna; unfold LZW_STK, CALLOC_STACK, ALLOC_STACK in *; lia))); exact (MHI a Ha Hna));
assert (MBL2 : forall b m i, In (b, m) Bf -> 0 <= i < m -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs m1 (b + i))
by (intros b m i Hb Hi; rewrite (Hkeep b m i ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; right; right; exact Hb]) Hi);
exact (MBL b m i Hb Hi))
end end;
clear MHI MBL; rename MHI2 into MHI; rename MBL2 into MBL;
let HB2 := fresh "HB" in
pose proof (Lblocks res nsz _ _ _ (blocks L2 A2) HB ltac:(clear - Hres; destruct Hres as [[Hz Hb0]|(Hnz & _ & Hex & _)]; [left; split; [exact Hz | exact Hb0] | right; split; [exact Hnz | exact Hex]])) as HB2;
let Htok2 := fresh "Htok" in
lazymatch type of HB2 with Permutation _ (nz ?cur ++ _) =>
lazymatch type of Htok with forall b, In b _ -> ?W b /\ _ =>
assert (Htok2 : forall b, In b (nz cur) -> W b /\ fst b <> 0)
by (let b := fresh "b" in let Hb := fresh "Hb" in
intros b Hb; destruct (Lcases b res nsz _ Hb) as [[Hbe Hnz]|Hb'];
[ subst b; split; [| exact Hnz]; destruct Hres as [[Hz _]|(_ & _ & _ & Hw)]; [exfalso; exact (Hnz Hz)|]; exact Hw
| exact (Htok b Hb') ])
end end;
let HS2 := fresh "HS" in
jafter_call HS k regs2 mem2 HP2 HS2;
let HK := fresh "HK" in
lazymatch type of HS2 with ?P -> _ => assert (HK : P);
[ constructor; [|constructor; [|constructor]];
[ eapply (region_kept_block_w _ _ _ 36 0 72 0 72 _ _ 72 _); [ew_havoc; rewrite Hatom; apply unsigned_lit_small; lia | exact Hgin
| intros b' m' i' Hb' Hi'; exact (Hkeep b' m' i' Hb' Hi')
| let i := fresh "i" in let Hi := fresh "Hi" in
intros i Hi; apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ _ 72 i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2)
ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB2 | apply in_app_iff; right; left; reflexivity]) Hi))
| lia | lia | lia | lia ]
| eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HE2 | exact Hhi | lia | lia | lia | cbn; lia | cbn; lia] ]
| specialize (HS2 HK); clear HK HS Hhi HP2 Hkeep Hgin HB Htok; rename HS2 into HS; rename HB2 into HB; rename Htok2 into Htok ] end;
let Ha := fresh "Hatom" in
(jreg HS (10%bv:reg) as Ha); cbn [ms_regs mkst] in Ha; rewrite Hr10 in Ha; symmetry in Ha;
rename HJ2 into HJ; rename Hid2 into Hid.
Ltac fold_frameG MHI MBL HE2 HH0 Hgsep Hatom :=
lazymatch goal with HF : frame_of ?E1 ?rs ?m ?m' |- _ =>
let MHI2 := fresh "MHI" in let MBL2 := fresh "MBL" in
lazymatch type of MHI with forall a, _ -> ~ (?spv - LZW_STK <= a < _) -> _ = mbyte _ ?m0 a =>
lazymatch type of MBL with forall b mm i, In (b, mm) ?Bf -> _ =>
assert (MHI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spv - LZW_STK <= a < spv) -> mbyte ubs2segs m' a = mbyte ubs2segs m0 a)
by (intros a Ha Hna; rewrite <- (MHI a Ha Hna); apply tmbyte_eq_of1; apply HF;
rewrite unsigned_lit_small by lia;
intros (r0 & Hr0 & Hin0); cbv [In] in Hr0;
repeat (destruct Hr0 as [<- | Hr0]; [cbn [r_base r_wlo r_whi base_val] in Hin0; repeat (rewrite ew_havoc_old in Hin0; [|cbv; lia]);
rewrite ?HE2, ?Hatom, ?unsigned_lit_small in Hin0 by lia; lia |]);
destruct Hr0);
assert (MBL2 : forall b mm i, In (b, mm) Bf -> 0 <= i < mm -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs m0 (b + i))
by (intros b mm i Hb Hi; rewrite <- (MBL b mm i Hb Hi); apply tmbyte_eq_of1; apply HF;
destruct (heap_blocks _ _ LAWS _ _ _ _ b mm i HH0 Hb Hi) as (_ & Hb0 & Hb1 & _);
pose proof (Hgsep b mm i Hb Hi);
rewrite unsigned_lit_small by lia;
intros (r0 & Hr0 & Hin0); cbv [In] in Hr0;
repeat (destruct Hr0 as [<- | Hr0]; [cbn [r_base r_wlo r_whi base_val] in Hin0; repeat (rewrite ew_havoc_old in Hin0; [|cbv; lia]);
rewrite ?HE2, ?Hatom, ?unsigned_lit_small in Hin0 by lia; lia |]);
destruct Hr0);
clear MHI MBL HF; rename MHI2 into MHI; rename MBL2 into MBL
end end end.
Ltac greg HS HE rr G :=
let Q := fresh "Q" in
(jreg HS rr as Q); cbn [ms_regs mkst] in Q; rewrite Q;
let n := eval cbv in (Z.to_nat (bv_unsigned rr)) in try rewrite (HE n rr eq_refl); cbn [fst];
first [exact G | reflexivity | assumption | rewrite G; reflexivity | rewrite G; f_equal; lia | symmetry; exact G | idtac ].
Ltac frame_tac HS HE HE2 :=
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (frame_saved_of_region ubs2_msyms E1);
[ eapply (tst_ok_region_nth E1 ss1 ms1 1%nat); [exact HS | reflexivity]
| ew_havoc; exact HE2
| let r := fresh "r" in let d := fresh "d" in let Hrd := fresh "Hrd" in
intros r d Hrd; cbv [SAVED In] in Hrd;
repeat (destruct Hrd as [Hrd | Hrd];
[ apply pair_equal_spec in Hrd as [<- <-]; eexists; split;
[ inlist
| cbn [sv_denot]; ew_havoc; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply HE; reflexivity ] | ]);
destruct Hrd ] end.
Ltac gptr HS Hatom off :=
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
lazymatch goal with |- word_mem _ ?m ?a ?v =>
apply (proj1 (val_mem_word_mem ubs2segs m a v));
replace a with (bv_unsigned (ew E1 36) + off) by (ew_havoc; rewrite Hatom, unsigned_lit_small by lia; lia);
change 8%nat with (N.to_nat 8);
eapply (tval_mem_of_chunk E1 _ _ 36%nat _ off 8);
[ eapply (tst_ok_region_nth E1 ss1 ms1 0%nat); [exact HS | reflexivity]
| reflexivity | inlist | reflexivity
| cbn [sv_denot]; ew_havoc; rewrite ?Z.add_0_r;
repeat match goal with H : ew _ ?n = Z_to_bv 64 _ |- context [ew _ ?n] => rewrite H end;
rewrite ?unsigned_lit_small by lia; reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
| cbn; lia ] end end.
Ltac to_clean HS HJ Hid HB Htok Wg' Rg1 MHI MBL HE HE2 Hatom Hra0 Htp0 Hal16 Hwlo regs g ld ti lm lc li tm :=
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc];
eapply SR_mono;
[ eapply (tlzw_clean API IMG _ _ _ _ _ _ _ _ _ _ regs _ _ g ld ti lm lc li tm _ 2);
[ exact HJ | exact Hid | exact HB
| let b := fresh "b" in let Hb := fresh "Hb" in
intros b Hb; destruct (Htok b Hb) as [Hw Hnz]; destruct b as [pb nb];
assert (Hnb : 0 < nb) by (pose proof (proj1 (In_nz _ _) Hb) as [Hin _]; cbv [In app] in Hin; cbn [fst] in Hnz;
repeat (destruct Hin as [Hin|Hin]; [apply pair_equal_spec in Hin as [<- <-]; lia |]); destruct Hin);
eapply (ftok_of_wtok _ _ _ _ pb nb Hw); [| eassumption];
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?L1 ?A1 ?m1 ?md1 =>
eapply (proj1 (proj2 (heap_blocks_range _ _ LAWS L1 A1 m1 md1 pb nb (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; left; exact Hb]) Hnb))) end
| eapply (ftok_of_wtok _ _ _ _ g 72 Wg'); [exact Rg1 | eassumption]
| unfold gptrs; cbn [fst]; split; [gptr HS Hatom 40|]; split; [gptr HS Hatom 0|]; split; [gptr HS Hatom 8|];
split; [gptr HS Hatom 16|]; split; [gptr HS Hatom 24 | gptr HS Hatom 32]
| let b := fresh "b" in let Hb := fresh "Hb" in
intros b Hb; cbv [In] in Hb; repeat (destruct Hb as [<-|Hb]; [cbn [fst]; lia|]); destruct Hb
| exact Hra0 | exact Htp0 | exact Hal16 | exact Hwlo | lia
| greg HS HE (2%bv:reg) HE2
| greg HS HE (3%bv:reg) HE2 | greg HS HE (4%bv:reg) HE2
| greg HS HE (8%bv:reg) Hatom | greg HS HE (9%bv:reg) HE2 | lia
| frame_tac HS HE HE2 ]
| cbv beta;
let L2 := fresh "L" in let A2 := fresh "A" in let regs2 := fresh "regs" in let mem2 := fresh "mem" in let md2 := fresh "md" in
let HJ2 := fresh "HJ_" in let Hid2 := fresh "Hid_" in let HP2 := fresh "HP_" in let H10 := fresh "H10_" in
let MHI' := fresh "MHI_" in let MBL' := fresh "MBL_" in let HB2 := fresh "HB_" in
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & Hid2 & HP2 & H10 & MHI' & MBL' & HB2);
left; exists L2, A2, regs2, mem2, md2, 2;
split; [reflexivity|]; split; [exact HJ2|]; split; [exact Hid2|]; split; [exact HP2|]; split; [exact H10|];
split; [intros a Ha Hna Hnp; rewrite (MHI' a Ha Hna); exact (MHI a Ha Hna)|];
split; [intros b m i Hb Hi; rewrite (MBL' b m i Hb Hi); exact (MBL b m i Hb Hi)|];
right; split; [left; reflexivity|]; split; [exact HB2|];
intros a Ha; rewrite (MHI' a) by lia; apply MHI; lia ].
Ltac res_fact HS HJ HB k res nsz Hatom Hnz :=
let R := fresh "R" in
pose proof (heap_blocks_range _ _ LAWS _ _ _ _ res nsz (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; left; apply (proj2 (In_nz _ _)); split; [cbv [app In]; tauto | exact Hnz]]) ltac:(lia)) as R;
add_fact' HS k (mkAF 4096 CEIL_MAX 4); [| ew_havoc; rewrite Hatom, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia].
Ltac pin_from HS rr Hatom :=
let P := fresh "P" in
(jreg HS rr as P); cbn [ms_regs mkst] in P; rewrite Hatom in P; pin_reg' HS rr 0 P; clear P.
Ltac null_atom HS k Hatom :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
let H2 := fresh "HSc" in
pose proof (st_ok_add_cond segs E1 ss1 ms1 BC_EQ (SOff k 0) (SLit 0) HS
ltac:(apply (cond_eq_lit E1 k 0 0); [ew_havoc; exact Hatom | lia | lia | reflexivity])) as H2;
let v := eval vm_compute in (add_cond ss1 (mkAC BC_EQ (SOff k 0) (SLit 0))) in
change (add_cond ss1 (mkAC BC_EQ (SOff k 0) (SLit 0))) with v in H2;
clear HS; rename H2 into HS end.
rename Hatom into Hg.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc; [run_wr HE2 Hg Wg' HB|].
fold_frameG MHI MBL HE2 HH0 Hgsep Hg.
do_malloc HS HJ Hid (2 * idl * idl) ltac:(rewrite ?U_add0; apply (U_tisz _ 13 idl); [ew_havoc; exact HE13 | exact Hidl]) 54%nat
MHI MBL HB Htok HE2 Hspm Htp0 HE Hg tblocks_after_malloc_end tnz_cases_end.
destruct Hres as [[-> _] | (Hnz1 & _ & _ & _)].
{
pin_reg' HS (10%bv:reg) 0 Hr10.
jrun_to LAWS ubs2tbl_ok HS HJ TPC_CLEAN; [run_wr HE2 Hg Wg' HB|]. fold_frameG MHI MBL HE2 HH0 Hgsep Hg.
to_clean HS HJ Hid HB Htok Wg' Rg1 MHI MBL HE HE2 Hg Hra0 Htp0 Hal16 Hwlo regs g (0, 0) (0, 2 * idl * idl) (0, 0) (0, 0) (0, 0) (0, 0). }
rename Hatom into Ha1. rename Hrr into Hrr1. res_fact HS HJ HB 58%nat res (2 * idl * idl) Ha1 Hnz1. clear Hr10.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc; [run_wr HE2 Hg Wg' HB|]. fold_frameG MHI MBL HE2 HH0 Hgsep Hg.
do_malloc HS HJ Hid 8192 ltac:(apply U_lit; lia) 70%nat MHI MBL HB Htok HE2 Hspm Htp0 HE Hg tblocks_after_malloc_end tnz_cases_end.
rename Hres into Hres2. rename Hatom into Ha2. rename Hr10 into Hr2. rename res0 into res2. rename Hrr into Hrr2.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc; [run_wr HE2 Hg Wg' HB|]. fold_frameG MHI MBL HE2 HH0 Hgsep Hg.
do_malloc HS HJ Hid 4096 ltac:(apply U_lit; lia) 86%nat MHI MBL HB Htok HE2 Hspm Htp0 HE Hg tblocks_after_malloc_end tnz_cases_end.
rename Hres into Hres3. rename Hatom into Ha3. rename Hr10 into Hr3. rename res0 into res3. rename Hrr into Hrr3.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc; [run_wr HE2 Hg Wg' HB|]. fold_frameG MHI MBL HE2 HH0 Hgsep Hg.
do_malloc HS HJ Hid 8192 ltac:(apply U_lit; lia) 102%nat MHI MBL HB Htok HE2 Hspm Htp0 HE Hg tblocks_after_malloc_end tnz_cases_end.
rename Hres into Hres4. rename Hatom into Ha4. rename Hr10 into Hr4. rename res0 into res4. rename Hrr into Hrr4.
destruct Hres2 as [[-> _] | (Hnz2 & _ & _ & _)].
{
null_atom HS 74%nat Ha2.
jrun_to LAWS ubs2tbl_ok HS HJ TPC_CLEAN; [run_wr HE2 Hg Wg' HB|]. fold_frameG MHI MBL HE2 HH0 Hgsep Hg.
to_clean HS HJ Hid HB Htok Wg' Rg1 MHI MBL HE HE2 Hg Hra0 Htp0 Hal16 Hwlo regs g (0, 0) (res, 2 * idl * idl) (0, 8192) (res3, 4096) (res4, 8192) (0, 0). }
res_fact HS HJ HB 74%nat res2 8192 Ha2 Hnz2. clear Hr2.
destruct Hres3 as [[-> _] | (Hnz3 & _ & _ & _)].
{
null_atom HS 90%nat Ha3.
jrun_to LAWS ubs2tbl_ok HS HJ TPC_CLEAN; [run_wr HE2 Hg Wg' HB|]. fold_frameG MHI MBL HE2 HH0 Hgsep Hg.
to_clean HS HJ Hid HB Htok Wg' Rg1 MHI MBL HE HE2 Hg Hra0 Htp0 Hal16 Hwlo regs g (0, 0) (res, 2 * idl * idl) (res2, 8192) (0, 4096) (res4, 8192) (0, 0). }
res_fact HS HJ HB 90%nat res3 4096 Ha3 Hnz3. clear Hr3.
destruct Hres4 as [[-> _] | (Hnz4 & _ & _ & _)].
{
pin_reg' HS (10%bv:reg) 0 Hr4.
jrun_to LAWS ubs2tbl_ok HS HJ TPC_CLEAN; [run_wr HE2 Hg Wg' HB|]. fold_frameG MHI MBL HE2 HH0 Hgsep Hg.
to_clean HS HJ Hid HB Htok Wg' Rg1 MHI MBL HE HE2 Hg Hra0 Htp0 Hal16 Hwlo regs g (0, 0) (res, 2 * idl * idl) (res2, 8192) (res3, 4096) (0, 8192) (0, 0). }
res_fact HS HJ HB 106%nat res4 8192 Ha4 Hnz4. clear Hr4.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc; [run_wr HE2 Hg Wg' HB|]. fold_frameG MHI MBL HE2 HH0 Hgsep Hg.
do_malloc HS HJ Hid (4098 * idl) ltac:(apply (U_tmsz _ 13 idl); [ew_havoc; exact HE13 | exact Hidl]) 118%nat
MHI MBL HB Htok HE2 Hspm Htp0 HE Hg tblocks_after_malloc_end tnz_cases_end.
rename Hres into Hres5. rename Hatom into Ha5. rename Hr10 into Hr5. rename res0 into res5. rename Hrr into Hrr5.
destruct Hres5 as [[-> _] | (Hnz5 & _ & _ & _)].
{
pin_reg' HS (10%bv:reg) 0 Hr5.
jrun_to LAWS ubs2tbl_ok HS HJ TPC_CLEAN; [run_wr HE2 Hg Wg' HB|]. fold_frameG MHI MBL HE2 HH0 Hgsep Hg.
to_clean HS HJ Hid HB Htok Wg' Rg1 MHI MBL HE HE2 Hg Hra0 Htp0 Hal16 Hwlo regs g (0, 0) (res, 2 * idl * idl) (res2, 8192) (res3, 4096) (res4, 8192) (0, 4098 * idl). }
res_fact HS HJ HB 122%nat res5 (4098 * idl) Ha5 Hnz5. clear Hr5.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc; [run_wr HE2 Hg Wg' HB|]. fold_frameG MHI MBL HE2 HH0 Hgsep Hg.
pose proof (maxres_bounds idl nP Hidl ltac:(lia)) as [HMR HMR0].
remember (nP / (4094 - idl)) as MRv eqn:HMRv.
assert (HMRle : MRv <= nP) by (clear - HMR HMR0 Hidl HnP; nia).
do_malloc HS HJ Hid (2 * (MRv + nP + 2))
ltac:(etransitivity; [apply (U_ldsz _ 13 11 idl nP); [ew_havoc; exact HE13 | ew_havoc; exact HE11 | exact Hidl | exact HnP] | rewrite <- HMRv; reflexivity]) 134%nat
MHI MBL HB Htok HE2 Hspm Htp0 HE Hg tblocks_after_malloc tnz_cases_front.
rename Hres into Hres6. rename Hatom into Ha6. rename Hr10 into Hr6. rename res0 into res6. rename Hrr into Hrr6.
destruct Hres6 as [[-> _] | (Hnz6 & _ & _ & _)].
{
pin_reg' HS (10%bv:reg) 0 Hr6.
jrun_to LAWS ubs2tbl_ok HS HJ TPC_CLEAN; [run_wr HE2 Hg Wg' HB|]. fold_frameG MHI MBL HE2 HH0 Hgsep Hg.
to_clean HS HJ Hid HB Htok Wg' Rg1 MHI MBL HE HE2 Hg Hra0 Htp0 Hal16 Hwlo regs g (0, 2 * (MRv + nP + 2)) (res, 2 * idl * idl) (res2, 8192) (res3, 4096) (res4, 8192) (res5, 4098 * idl). }
res_fact HS HJ HB 138%nat res6 (2 * (MRv + nP + 2)) Ha6 Hnz6. clear Hr6.
jrun_to LAWS ubs2tbl_ok HS HJ TPC_INIT; [run_wr HE2 Hg Wg' HB|]. fold_frameG MHI MBL HE2 HH0 Hgsep Hg.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret. right. unfold tpro_ok. rewrite <- !HMRv.
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?L6 ?A6 _ ?md6 =>
lazymatch goal with |- context [mkst (ms_regs ?msf) _ (ms_mem _) _] =>
exists L6, A6, (ms_regs msf), (ms_mem msf), md6 end end.
exists g, res, res2, res3, res4, res5, res6.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hid|].
split; [greg HS HE (2%bv:reg) HE2|]. split; [greg HS HE (3%bv:reg) HE2|]. split; [greg HS HE (4%bv:reg) HE2|].
split; [greg HS HE (8%bv:reg) Hg|]. split; [greg HS HE (20%bv:reg) HE13|].
split. { let M := fresh "M" in reg_U HS (21%bv:reg) ltac:(apply (U_idl2 _ 13 idl); [ew_havoc; exact HE13 | exact Hidl]) M; cbn [ms_regs mkst] in M; exact M. }
split; [greg HS HE (18%bv:reg) HE10|]. split; [greg HS HE (19%bv:reg) HE14|]. split; [greg HS HE (9%bv:reg) HE2|].
split; [frame_tac HS HE HE2|].
cbn [ms_mem mkst].
split; [gptr HS Hg 0|]. split; [gptr HS Hg 8|]. split; [gptr HS Hg 16|]. split; [gptr HS Hg 24|]. split; [gptr HS Hg 32|]. split; [gptr HS Hg 40|].
split; [gptr HS Hg 48|].
Ltac gval HS Hatom off n :=
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
lazymatch goal with |- val_mem _ ?m ?a _ ?v =>
replace a with (bv_unsigned (ew E1 36) + off) by (ew_havoc; rewrite Hatom, unsigned_lit_small by lia; lia);
change 4%nat with (N.to_nat 4); change 2%nat with (N.to_nat 2);
eapply (tval_mem_of_chunk E1 _ _ 36%nat _ off n);
[ eapply (tst_ok_region_nth E1 ss1 ms1 0%nat); [exact HS | reflexivity]
| reflexivity | inlist | reflexivity
| cbn [sv_denot]; ew_havoc; rewrite ?Z.add_0_r;
repeat match goal with H : ew _ ?k = Z_to_bv 64 _ |- context [ew _ ?k] => rewrite H end;
rewrite ?unsigned_lit_small by lia; reflexivity
| cbn; lia
| cbn; lia ] end end.
split; [gval HS Hg 56 4%N|]. split; [gval HS Hg 60 4%N|]. split; [gval HS Hg 64 2%N|]. split; [gval HS Hg 66 2%N|].
assert (Hall : forall b, In b ((res6, 2 * (MRv + nP + 2)) :: (((([] ++ [(res, 2 * idl * idl)]) ++ [(res2, 8192)]) ++ [(res3, 4096)]) ++ [(res4, 8192)]) ++ [(res5, 4098 * idl)]) -> fst b <> 0).
{ intros b Hb. cbv [app In] in Hb.
repeat (destruct Hb as [<- | Hb]; [cbn [fst]; assumption|]). destruct Hb. }
rewrite (tnz_id _ Hall) in HB, Htok. cbn [app] in HB, Htok, Hall.
split; [exact HB|]. split; [exact Htok|]. split; [exact Wg'|]. split; [exact Hgsep|]. split; [exact MHI | exact MBL].
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
