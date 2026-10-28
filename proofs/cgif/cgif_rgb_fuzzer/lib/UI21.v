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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3l YI00 YI02 YI01 YI03
UI1e UI1c UI39 UI1i UI20 UI2r UI59 UI56 YI0x UI57
UI1h UI16 UI1z UI1k.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require YI0d.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_flret : sstate :=
mkSS FL_RET sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 272 0 0 (fl_stk_saved 32) ] None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4) ] [] []).
Definition FL_CFG : Z := Eval vm_compute in (ubs2_A_flushFrame + 0xa68).
Lemma land1_cases : forall a, 0 <= a -> Z.land a 1 = 0 \/ Z.land a 1 = 1.
Proof.
intros a Ha. rewrite Z.land_ones with (n := 1) by lia. change (2 ^ 1) with 2.
pose proof (Z.mod_pos_bound a 2 ltac:(lia)). lia.
Qed.
Definition fl_RgM : YQ0b.region := YQ0b.mkRegion (Some 80%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF A_X fl_litsG).
Definition fl_RfM : YQ0b.region := YQ0b.mkRegion (Some 81%nat) 0 40 0 0 (obj_chunks_gen LAY_Frame A_F []).
Definition fl_factsM : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (80%nat, mkAF 4096 (CEIL_MAX - 96) 4);
(81%nat, mkAF 4096 (CEIL_MAX - 40) 3) ].
Lemma fl_RgM_ok : forall regs1 regs0 s f fb more mem g,
bv_unsigned (ew (fl_E regs1 regs0 s f fb more) 80) = g -> 0 <= g -> g + 96 <= 2 ^ 64 ->
obj_at ubs2segs mem g LAY_CGIF (cgif_vals s) -> region_ok ubs2segs (fl_E regs1 regs0 s f fb more) mem fl_RgM.
Proof.
intros regs1 regs0 s f fb more mem g H Hlo Hhi Hobj. unfold fl_RgM, fl_litsG, A_X.
eapply (region_ok_obj_gen ubs2segs _ mem 80 g 96 0 0 LAY_CGIF (cgif_vals s) 45 (litsG None None None None));
[exact H | lia | lia | exact Hobj | reflexivity | | apply (litsG_ok s); exact I | intros k Hk; lia].
intros j v Hj. apply (fl_HX regs1 regs0 s f fb more (45 + j) j v eq_refl Hj).
Qed.
Lemma fl_RfM_ok : forall regs1 regs0 s f fb more mem p,
bv_unsigned (ew (fl_E regs1 regs0 s f fb more) 81) = p -> 0 <= p -> p + 40 <= 2 ^ 64 ->
obj_at ubs2segs mem p LAY_Frame (frame_vals f) -> region_ok ubs2segs (fl_E regs1 regs0 s f fb more) mem fl_RfM.
Proof.
intros regs1 regs0 s f fb more mem p H Hlo Hhi Hobj. unfold fl_RfM, A_F.
eapply (region_ok_obj_gen ubs2segs _ mem 81 p 40 0 0 LAY_Frame (frame_vals f) 62 []);
[exact H | lia | lia | exact Hobj | reflexivity | | intros [|j] z Hz; discriminate Hz | intros k Hk; lia].
intros j v Hj. apply (fl_HF regs1 regs0 s f fb more (62 + j) j v eq_refl Hj).
Qed.
Definition fl_cfg_stk (u : Z) : list YQ0b.chunk :=
fl_stk_saved 32 ++ [mkChunk 56 (CVal 8 (SLit u)); mkChunk 96 (CVal 8 (SOff 82 0)); mkChunk 112 (CVal 8 (SOff 80 0));
mkChunk 120 (CVal 8 (SOff 81 0)); mkChunk 128 (CVal 8 (SOff 62 0)); mkChunk 136 (CVal 8 (SOff 83 0))].
Definition ss_cfg (u : Z) : sstate :=
mkSS FL_CFG sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 272 0 168 (fl_cfg_stk u) ; fl_RgM ; fl_RfM ] None
(mkFacts (fl_factsM ++ fl_gfacts ++ fl_ffacts ++ [(23%nat, mkAF 1 65535 0); (16%nat, mkAF 1 65535 0); (83%nat, mkAF 4096 CEIL_MAX 0)]) [] []).
Lemma fok_eq : forall segs mem a fd v' v, field_ok segs mem a fd v' -> v' = v -> field_ok segs mem a fd v.
Proof. intros segs mem a fd v' v H <-. exact H. Qed.
End c.
Ltac stfld HS HU2 OFF N M :=
eapply fok_eq; [ eapply (st_field_low ubs2segs _ _ _ 0 _ 2 _ OFF N _ M HS);
[ reflexivity | reflexivity | cbn [r_chunks]; repeat (first [left; reflexivity | right]) | exact HU2 | cbn; lia | reflexivity ] | ].
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma chunk_word : forall E mem base off e v,
chunk_ok ubs2segs E mem base (mkChunk off (CVal 8 e)) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
word_mem ubs2segs mem (base + off) v.
Proof.
intros E mem base off e v Hc He Hv. apply val_mem_word_mem.
eapply (val_of_chunk_ok ubs2segs E mem base off 8%N e); [exact Hc | exact He | cbn; lia | cbn; lia].
Qed.
Definition FL_IMG : Z := Eval vm_compute in (ubs2_A_flushFrame + 0xa44).
Definition fl_raw_stk (r2 : bool) : list YQ0b.chunk :=
fl_stk_saved 32 ++ [mkChunk 16 (CVal 8 (SOff 86 0)); mkChunk 24 (CVal 8 (SOff 83 0)); mkChunk 32 (CVal 8 (SOff 88 0));
mkChunk 56 (CVal 8 (SOff 87 0)); mkChunk 96 (CVal 8 (SOff 82 0)); mkChunk 112 (CVal 8 (SOff 80 0)); mkChunk 120 (CVal 8 (SOff 81 0))] ++
(if r2 then [mkChunk 40 (CVal 8 (SOff 84 0)); mkChunk 48 (CVal 8 (SOff 85 0))] else []).
Definition ss_raw (pc : Z) (pz r2 : bool) : sstate :=
mkSS pc (if pz then sr_set sr_atoms 8%bv (SLit 0) else sr_atoms)
[ YQ0b.mkRegion (Some 2%nat) 0 272 0 168 (fl_raw_stk r2) ; fl_RgM ; fl_RfM ] None
(mkFacts (fl_factsM ++ fl_gfacts ++ fl_ffacts ++ (if pz then [] else [(8%nat, mkAF 1 (2^64 - 1) 0)])) [] []).
End d.
Ltac get_HS := match goal with H : st_ok _ _ _ _ |- _ => H end.
Ltac get_HJ := match goal with H : journal _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => H end.
Ltac get_HF := match goal with H : frame_of _ _ _ _ |- _ => H end.
Ltac rgq HS :=
lazymatch goal with |- getr _ ?r = _ =>
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
rewrite (st_ok_reg segs E ss ms r HS);
match goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ assumption | reflexivity | match goal with H : ?x = 0 |- _ = Z_to_bv 64 ?x => rewrite H; reflexivity end ]
end end.
Ltac clear_HG := repeat match goal with H : mem_grows _ _ |- _ => clear H end.
Ltac runW LAWS stop WRT HU2 lo hi :=
let HS := get_HS in let HJ := get_HJ in
jrun_to LAWS ubs2tbl_ok HS HJ stop; [WRT |];
let HF := get_HF in
cbn [ms_mem mkst] in HF; clear_HG;
lazymatch goal with K : forall a, _ -> _ -> mbyte ubs2segs ?m a = mbyte ubs2segs ?m0 a |- _ =>
lazymatch type of HF with frame_of ?E1 ?rs m ?m2 =>
let K2 := fresh "K" in
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> mbyte ubs2segs m2 a = mbyte ubs2segs m0 a);
[ intros a Ha Hna; try rewrite <- (K a Ha Hna);
apply (mbyte_of_frame E1 rs m m2 a HF Ha);
intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; repeat (rewrite ew_havoc_old; [|cbv; lia]); rewrite ?HU2; lia |]); destruct Hr
| clear HF K ]
end
end.
Ltac clear_Hc := match goal with H : branch_taken _ _ _ = _ |- _ => clear H end.
Ltac br_tree RUN LEAF n :=
lazymatch n with
| O => fail "br_tree: out of depth"
| Datatypes.S ?m => RUN; first [ LEAF | let HS := get_HS in jbranch ubs2tbl HS; [ clear_Hc; br_tree RUN LEAF m | clear_Hc; br_tree RUN LEAF m ] ]
end.
Section l. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition hidePs (P : Prop) : Prop := P.
End l.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (hidePs (A \/ B)) in H end.
Section p. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis RAWADD : rawadd_spec API.
Lemma fl_ret :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f : frame_st) (gen1 rc1 : Z) (rest FP : list (Z * Z)),
let sp0 := spZ regs0 in
journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 ->
cgif_at memc g (flush_upd s i gen1 rc1) -> cgif_wf s N -> nth_error (cg_frames s) i = Some (Some f) ->
Permutation (blocks Lc Ac) (cgif_blocks g s N ++ rest) ->
fl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 272) -> fl_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_RET) memc (seg_rom ubs2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof using IMG.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f gen1 rc1 rest FP sp0 HJ Hid Hra0 Hal16 Hat Hwf Hf HB HSV G2 [G3 G4].
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (E := Ereg regs1 (map (Z_to_bv 64) (fl_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HK : forall j v, nth_error (fl_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HKr : forall n j (r : reg), n = (32 + j)%nat -> nth_error FL_SAVED j = Some r -> ew E n = getr regs0 r).
{ intros n j r -> Hr. rewrite (HK j _ (fl_saved_vals_nth regs0 j r Hr)). apply Z_to_bv_bv_unsigned. }
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 272 0 0 (fl_stk_saved 32))).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV HK). }
assert (HFA : atoms_ok E [ (2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16.
repeat split; try lia. replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HS : st_ok ubs2segs E ss_flret (mkst regs1 (Z_to_bv 64 FL_RET) memc (seg_rom ubs2segs))).
{ unfold ss_flret. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; exact I]].
constructor; [exact HR0 | constructor]. }
clear HR0 HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_RET) memc (seg_rom ubs2segs))) in HJ.
jrun LAWS ubs2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold fl_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists Lc, Ac, (ms_regs msf), (ms_mem msf), mdc, (bv_unsigned (getr regs1 9)), gen1, rc1 end.
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
rewrite ?Z.add_0_r, (HKr 32%nat 0%nat 1%bv eq_refl eq_refl), Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end. }
split. { cbn [ms_mem mkst]. exact HJ. }
split.
{ apply regs_preserved_intro; cbn [ms_regs mkst].
- reg_nowF HS ltac:(rewrite HU2; replace (sp0 - 272 + 272) with sp0 by lia; subst sp0; unfold spZ; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
- reg_nowF HS ltac:(rewrite (HKr 33%nat 1%nat 8%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 34%nat 2%nat 9%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 35%nat 3%nat 18%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 36%nat 4%nat 19%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 37%nat 5%nat 20%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 38%nat 6%nat 21%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 39%nat 7%nat 22%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 40%nat 8%nat 23%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 41%nat 9%nat 24%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 42%nat 10%nat 25%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 43%nat 11%nat 26%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 44%nat 12%nat 27%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned). }
split; [exact Hid|].
split. { cbn [ms_regs mkst]. reg_nowF HS ltac:(rewrite (HE 9%nat 9%bv eq_refl); reflexivity). }
split; [apply u64_range_getr|].
split.
{ cbn [ms_mem mkst]. lazymatch goal with |- cgif_at ?m' g ?s' =>
eapply (cgif_at_low _ memc m' g s' N Lc Ac memc mdc rest HH0 _ Hat) end.
intros a Ha. cbn [ms_mem mkst] in HF. unfold mbyte.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
split; [exact (cgif_wf_flush_upd s N i gen1 rc1 f Hf Hwf) | exact HB].
Unshelve. rewrite (cgif_blocks_flush_upd g s N i gen1 rc1 f Hf). exact HB.
Qed.
Lemma fl_cfg :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f : frame_st) (gen1 : Z)
(rest FP tmp : list (Z * Z)) (pTmp Nt img w h top : Z),
let sp0 := spZ regs0 in
journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) ->
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) -> cgif_wf s N -> (i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some (Some f) ->
(forall b n a, In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP FP a) ->
Permutation (blocks Lc Ac) (tmp ++ cgif_blocks g s N ++ rest) ->
((tmp = [] /\ pTmp = 0 /\ img = fr_img f /\ w * h <= N) \/ (tmp = [(pTmp, Nt)] /\ pTmp <> 0 /\ img = pTmp /\ w * h <= Nt)) ->
(In (pTmp, Nt) (blocks L A) -> forall k, 0 <= k < Nt -> inFP FP (pTmp + k)) ->
1 <= w <= cg_W s -> 1 <= h <= cg_H s ->
fl_saved_ok memc sp0 regs0 ->
word_mem ubs2segs memc (sp0 - 272 + 112) g -> word_mem ubs2segs memc (sp0 - 272 + 120) (fr_ptr f) ->
word_mem ubs2segs memc (sp0 - 272 + 128) (fr_lpal f) -> word_mem ubs2segs memc (sp0 - 272 + 136) img ->
word_mem ubs2segs memc (sp0 - 272 + 56) (Z.land (fr_attr f) 1) -> word_mem ubs2segs memc (sp0 - 272 + 96) top ->
getr regs1 2 = Z_to_bv 64 (sp0 - 272) -> getr regs1 8 = Z_to_bv 64 pTmp ->
getr regs1 23 = Z_to_bv 64 w -> getr regs1 16 = Z_to_bv 64 h ->
fl_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_CFG) memc (seg_rom ubs2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof using IMG RAWADD.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f gen1 rest FP tmp pTmp Nt img w h top sp0
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hi Hf HFP HB Htmp Htmp_fp Hw Hh HSV Wg Wfr Wlct Wimg Wu Wtop G2 G8 G23 G16 [G3 G4].
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity. assert (HRSv : RAWADD_STK = 8704) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & Hih & Hfwf).
set (s1 := flush_upd s i gen1 (rw_cur s)) in Hat. set (f1 := set_fr_gen f gen1).
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hf1in : In (Some f1) (cg_frames s1)) by (rewrite Hfr1; eapply nth_error_In; apply nth_error_list_set_same; exact Hilt).
assert (HBc : Permutation (blocks Lc Ac) (cgif_blocks g s N ++ (tmp ++ rest))).
{ eapply Permutation_trans; [exact HB|]. apply Permutation_app_swap_app. }
destruct (af_cgif_geom API Lc Ac memc mdc g s N _ HH0 HBc) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom f Hfin) as (Hp0 & Hp1 & Hpg).
pose proof (af_raw_frame_sep API Lc Ac memc mdc g s N _ f HH0 HBc Hfin) as Hpr.
destruct (fl_img_geom API Lc Ac memc mdc g s N _ f HH0 HBc Hfin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Him0 Him1].
pose proof Hat as (Hobj & Hraw & Hfrs). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s) : cgif_vals s1 = cgif_vals s) in Hobj.
change (cg_raw s1) with (cg_raw s) in Hraw.
pose proof (Hfrs f1 Hf1in) as Hfobj. change (fr_ptr f1) with (fr_ptr f) in Hfobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf.
pose proof (Rf 0%nat (fr_lpal f) eq_refl) as Rlpal. pose proof (Rf 2%nat (fr_attr f) eq_refl) as Rfattr. pose proof (Rf 5%nat (fr_nlp f) eq_refl) as Rnlp.
cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rlpal, Rfattr, Rnlp.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
assert (Himg : 4096 <= img /\ img + w * h <= alloc_ceiling /\ In (img, if pTmp =? 0 then N else Nt) (blocks Lc Ac)).
{ destruct Htmp as [(-> & -> & -> & Hle) | (-> & Hnz & -> & Hle)].
- rewrite Z.eqb_refl. split; [lia|]. split; [clear - Him1 Hle Hw Hh; nia|].
apply (Permutation_in _ (Permutation_sym HBc)). apply in_app_iff. left. apply (frame_blocks_in_cgif g s N f); [exact Hfin | right; left; reflexivity].
- destruct (Z.eqb_spec pTmp 0); [lia|].
assert (Hin : In (pTmp, Nt) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); left; reflexivity).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pTmp Nt HH0 Hin) as [T0 T1]. split; [lia|]. split; [clear - T1 Hle Hw Hh; nia | exact Hin]. }
destruct Himg as (Him0' & Him1' & Himgin).
clear Hih Hi.
assert (Ht0 : pTmp = 0 -> tmp = [] /\ img = fr_img f /\ w * h <= N) by (intros H0; destruct Htmp as [(A1 & A2 & A3 & A4)|(A1 & A2 & A3 & A4)]; [auto | lia]).
assert (Ht1 : pTmp <> 0 -> tmp = [(pTmp, Nt)] /\ img = pTmp /\ w * h <= Nt) by (intros H0; destruct Htmp as [(A1 & A2 & A3 & A4)|(A1 & A2 & A3 & A4)]; [lia | auto]).
clear Htmp.
hide_disj.
set (u := Z.land (fr_attr f) 1) in Wu.
assert (Hu01 : 0 <= u <= 1) by (subst u; pose proof (land1_cases (fr_attr f) ltac:(clear - Rfattr; lia)); lia).
set (E := fl_E regs1 regs0 s f1 None [g; fr_ptr f; top; img]).
pose proof (fl_HE regs1 regs0 s f1 None [g; fr_ptr f; top; img] : forall n rr, _ -> ew E n = _) as HE.
pose proof (fl_HK regs1 regs0 s f1 None [g; fr_ptr f; top; img] : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (fl_HKr regs1 regs0 s f1 None [g; fr_ptr f; top; img] : forall n j r, _ -> _ -> ew E n = _) as HKr.
pose proof (fl_HX regs1 regs0 s f1 None [g; fr_ptr f; top; img] : forall n j v, _ -> _ -> ew E n = _) as HX.
pose proof (fl_HF regs1 regs0 s f1 None [g; fr_ptr f; top; img] : forall n j v, _ -> _ -> ew E n = _) as HFf.
pose proof (fl_HM regs1 regs0 s f1 None [g; fr_ptr f; top; img] : forall n j v, _ -> _ -> ew E n = _) as HM.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HE80 : ew E 80 = Z_to_bv 64 g) by (apply (HM 80%nat 0%nat g eq_refl eq_refl)).
assert (HE81 : ew E 81 = Z_to_bv 64 (fr_ptr f)) by (apply (HM 81%nat 1%nat (fr_ptr f) eq_refl eq_refl)).
assert (HE82 : ew E 82 = Z_to_bv 64 top) by (apply (HM 82%nat 2%nat top eq_refl eq_refl)).
assert (HE83 : ew E 83 = Z_to_bv 64 img) by (apply (HM 83%nat 3%nat img eq_refl eq_refl)).
assert (HU80 : bv_unsigned (ew E 80) = g) by (rewrite HE80; apply unsigned_lit_small; lia).
assert (HU81 : bv_unsigned (ew E 81) = fr_ptr f) by (rewrite HE81; apply unsigned_lit_small; lia).
assert (HE62 : ew E 62 = Z_to_bv 64 (fr_lpal f)) by (apply (HFf 62%nat 0%nat _ eq_refl eq_refl)).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 272 0 168 (fl_cfg_stk u))).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
unfold fl_cfg_stk. apply Forall_app; split; [apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV); intros j v Hj; exact (HK _ j v eq_refl Hj)|].
constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ u); [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wu].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (top mod 2 ^ 64)); [cbn [sv_denot]; rewrite Z.add_0_r, HE82, Z_to_bv_bv_unsigned | change (8 * Z.of_N 8) with 64; apply Z.mod_pos_bound; lia | cbn; lia |].
+ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
+ apply val_mem_word_mem. intros k Hk. rewrite (Wtop k Hk). unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
- eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, HE80, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wg].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_ptr f)); [cbn [sv_denot]; rewrite Z.add_0_r, HE81, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wfr].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_lpal f)); [cbn [sv_denot]; rewrite Z.add_0_r, HE62, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wlct].
- eapply (chunk_ok_val _ _ _ _ _ _ _ img); [cbn [sv_denot]; rewrite Z.add_0_r, HE83, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wimg]. }
pose proof (fl_RgM_ok regs1 regs0 s f1 None [g; fr_ptr f; top; img] memc g HU80 ltac:(lia) ltac:(lia) Hobj) as HR1.
pose proof (fl_RfM_ok regs1 regs0 s f1 None [g; fr_ptr f; top; img] memc (fr_ptr f) HU81 ltac:(lia) ltac:(lia) Hfobj) as HR2.
assert (HPD : pairwise_disjoint E (ss_mem (ss_cfg u))).
{ cbn [ss_mem ss_cfg]. unfold fl_RgM, fl_RfM. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU80, HU81. clear - Hg1 Hp1 Hpg Hceil HFSv HGSv HFRv Hac; unfold hidePs in *. repeat split; lia. }
assert (HFA : atoms_ok E (fl_factsM ++ fl_gfacts ++ fl_ffacts ++ [(23%nat, mkAF 1 65535 0); (16%nat, mkAF 1 65535 0); (83%nat, mkAF 4096 CEIL_MAX 0)])).
{ apply atoms_ok_app; [| apply atoms_ok_app; [exact (fl_gfacts_ok regs1 regs0 s f1 None [g; fr_ptr f; top; img] memc g N Hobj Hwf ltac:(lia) ltac:(lia))
| apply atoms_ok_app; [exact (fl_ffacts_ok regs1 regs0 s f1 None [g; fr_ptr f; top; img] memc (fr_ptr f) Hfobj Him0 ltac:(change (fr_img f1) with (fr_img f); clear - Him1 HN HW1 HH1; nia)) |]]].
- cbn [atoms_ok fl_factsM]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU80, HU81.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia.
 + replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16.
 + pose proof (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr f) FRAME_SIZE HH0 ltac:(apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; apply (frame_blocks_in_cgif g s N f); [exact Hfin | left; reflexivity]) ltac:(lia)) as (_ & _ & Hp16).
clear - Hp16. apply Z.mod_divide in Hp16; [|lia]. apply Z.mod_divide; [lia|]. destruct Hp16 as [q Hq]. exists (q * 2). lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (HE 23%nat 23%bv eq_refl), (HE 16%nat 16%bv eq_refl), G23, G16, HE83.
rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Hw Hh RW RH Him0' Him1'. repeat split; try lia; nia. }
assert (HS : st_ok ubs2segs E (ss_cfg u) (mkst regs1 (Z_to_bv 64 FL_CFG) memc (seg_rom ubs2segs))).
{ unfold ss_cfg. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | split; [exact HFA | split; exact I]].
constructor; [exact HR0|]. constructor; [exact HR1|]. constructor; [exact HR2|]. constructor. }
clear HR0 HR1 HR2 HPD HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_CFG) memc (seg_rom ubs2segs))) in HJ.
assert (WR : forall E0 cs, bv_unsigned (ew E0 2) = sp0 - 272 ->
wr_ok E0 [YQ0b.mkRegion (Some 2%nat) 0 272 0 168 cs; fl_RgM; fl_RfM] FLUSH_STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 cs H2. eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HBc)); left; reflexivity).
assert (Hrin : In (cg_raw s, RAW_SIZE) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HBc)); right; left; reflexivity).
assert (Hfr_any : forall x rcur, In (Some x) (cg_frames (flush_upd s i gen1 rcur)) ->
exists y, In (Some y) (cg_frames s) /\ fr_ptr y = fr_ptr x /\ In (Some x) (cg_frames s1)).
{ intros x rcur Hx. assert (Hx1 : In (Some x) (cg_frames s1)) by exact Hx.
destruct (In_frames_flush_upd s i gen1 rcur f x Hf Hx) as [-> | [Hin _]].
- exists f. split; [exact Hfin|]. split; [reflexivity | exact Hx1].
- exists x. split; [exact Hin|]. split; [reflexivity | exact Hx1]. }
assert (CG : forall (m3 : word -> option byte) rcur,
(forall a n k, In (a, n) (cgif_blocks g s N) -> 0 <= k < n -> ~ (cg_raw s + 40 <= a + k < cg_raw s + 44) ->
mbyte ubs2segs m3 (a + k) = mbyte ubs2segs memc (a + k)) ->
obj_at ubs2segs m3 (cg_raw s) LAY_Raw [ubs2_A_cgif_writecb; g; rw_gct s; rw_attr s; cg_W s; cg_H s; raw_sgct s; rw_loops s; rcur] ->
cgif_at m3 g (flush_upd s i gen1 rcur)).
{ intros m3 rcur KB Hraw3. split; [| split; [exact Hraw3|]].
- rewrite cgif_vals_flush_upd. eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) |].
intros k Hk. apply (KB g CGIF_SIZE k ltac:(left; reflexivity) ltac:(lia)). clear - Hrg Hk HGSv HRWv; unfold hidePs in *. lia.
- intros x Hx. destruct (Hfr_any x rcur Hx) as (y & Hy & Hyx & Hx1).
destruct (Hfgeom y Hy) as (Y0 & Y1 & Yg). pose proof (af_raw_frame_sep API Lc Ac memc mdc g s N _ y HH0 HBc Hy) as Yr.
eapply obj_at_transport_range; [exact (Hfrs x Hx1) | exact (proj1 LAY_Frame_ok) |].
intros k Hk. rewrite <- Hyx. apply (KB (fr_ptr y) FRAME_SIZE k); [| lia | clear - Yr Hk HFRv HRWv; unfold hidePs in *; lia].
apply (frame_blocks_in_cgif g s N y); [exact Hy | left; reflexivity]. }
assert (Hu : u = 0 \/ u = 1) by (clear - Hu01; lia). clear Hu01.
destruct Hu as [Hu | Hu]; rewrite Hu in HS, Wu.
all: jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_cgif_raw_addframe; [apply WR; exact HU2|].
all: cbn [ms_mem mkst] in HF.
all: assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a)
by (intros a Ha Hna; apply (mbyte_of_frame _ _ _ _ a HF Ha); intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?HU2; lia |]); destruct Hr).
all: clear HF HG.
all: jreg HS (10%bv:reg) as Ha0; rewrite (HX 58%nat 13%nat (cg_raw s) eq_refl eq_refl) in Ha0.
all: jreg HS (11%bv:reg) as Ha1; rewrite HU2 in Ha1.
all: jreg HS (2%bv:reg) as Hsp; rewrite (HE 2%nat 2%bv eq_refl), G2 in Hsp.
all: jreg HS (4%bv:reg) as Htp; rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Htp.
all: jreg HS (1%bv:reg) as Hra.
all: lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hspv : spZ (ms_regs msx) = sp0 - 272) by (unfold spZ; rewrite Hsp; apply unsigned_lit_small; lia) end.
all: assert (Hcfg : exists fa tp lf dl sl dp tx,
obj_at ubs2segs (ms_mem ms) (sp0 - 272 + 128) LAY_RawFrameConfig [fr_lpal f; img; fa; w; h; tp; lf; dl; sl; dp; tx] /\
(0 < sl <= 256 -> u = 1 /\ sl = fr_nlp f));
[ do 7 eexists; split;
[ apply (proj2 (obj_at_shift ubs2segs (ms_mem ms) (sp0 - 272) 128 LAY_RawFrameConfig _));
apply obj_at_of_fields; [reflexivity|]; intros j fd v Hj Hv;
assert (Hjlt : (j < length (lay_shift 128 LAY_RawFrameConfig))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate);
destruct j as [|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]; [..|cbn in Hjlt; lia]; cbn in Hj, Hv; injection Hj as <-; injection Hv as <-;
[ stfld HS HU2 128 8%N (2 ^ 64); rewrite (U_atom _ 62 (fr_lpal f) HE62) by lia; apply Z.mod_small; lia
| stfld HS HU2 136 8%N (2 ^ 64); rewrite (U_atom _ 83 img HE83) by lia; apply Z.mod_small; lia
| stfld HS HU2 144 4%N (2 ^ 32); reflexivity
| stfld HS HU2 148 2%N (2 ^ 16); rewrite (U_atom _ 23 w ltac:(rewrite (HE 23%nat 23%bv eq_refl); exact G23)) by lia; apply Z.mod_small; lia
| stfld HS HU2 150 2%N (2 ^ 16); rewrite (U_atom _ 16 h ltac:(rewrite (HE 16%nat 16%bv eq_refl); exact G16)) by lia; apply Z.mod_small; lia
| stfld HS HU2 152 2%N (2 ^ 16); reflexivity
| stfld HS HU2 154 2%N (2 ^ 16); reflexivity
| stfld HS HU2 156 2%N (2 ^ 16); reflexivity
| stfld HS HU2 158 2%N (2 ^ 16); reflexivity
| stfld HS HU2 160 1%N (2 ^ 8); reflexivity
| stfld HS HU2 161 1%N (2 ^ 8); reflexivity ]
| first [ rewrite U_lit by lia; intros Hsl; exfalso; rewrite Z.mod_0_l in Hsl by lia; lia
| rewrite (U_atom _ 67 (fr_nlp f) (HFf 67%nat 5%nat _ eq_refl eq_refl)) by lia; rewrite Z.mod_small by lia; intros _; split; [exact Hu | reflexivity] ] ]
| ].
all: destruct Hcfg as (fa & tp & lf & dl & sl & dp & tx & Hcfg & Hsl).
all: assert (Hperm : exists Nimg rest0, Permutation (blocks Lc Ac) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest0) /\
w * h <= Nimg /\ (Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) rest0));
[ destruct (Z.eq_dec pTmp 0) as [Hpz | Hpz];
[ destruct (Ht0 Hpz) as (Htm & Him & Hle); destruct (flush_blocks_img0 g s N rest i f Hf) as (rest0 & HP & HL);
exists N, rest0; split; [rewrite Him; eapply Permutation_trans; [exact HBc | rewrite Htm; exact HP] | split; [exact Hle | exact HL]]
| destruct (Ht1 Hpz) as (Htm & Him & Hle); destruct (flush_blocks_img1 g s N rest f pTmp Nt Hfin) as (rest0 & HP & HL);
exists Nt, rest0; split; [rewrite Him; eapply Permutation_trans; [exact HB | rewrite Htm; exact HP] | split; [exact Hle | exact HL]] ]
| ].
all: destruct Hperm as (Nimg & rest0 & Hperm & HleN & Hlct).
all: eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2 (rcur : Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 FL_CALLRET) mem2 (seg_rom ubs2segs)) md2 /\
journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ st_init_done A2 = true /\
obj_at ubs2segs mem2 (cg_raw s) LAY_Raw [ubs2_A_cgif_writecb; g; rw_gct s; rw_attr s; cg_W s; cg_H s; raw_sgct s; rw_loops s; rcur] /\
Permutation (blocks L2 A2) (blocks Lc Ac) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 272 - RAWADD_STK <= x < sp0 - 272) ->
mbyte ubs2segs mem2 x = mbyte ubs2segs (ms_mem ms) x /\ (writable_at ubs2segs (ms_mem ms) x <-> writable_at ubs2segs mem2 x)) /\
(forall a n k, In (a, n) (blocks Lc Ac) -> 0 <= k < n -> ~ (cg_raw s + 40 <= a + k < cg_raw s + 44) ->
mbyte ubs2segs mem2 (a + k) = mbyte ubs2segs (ms_mem ms) (a + k))).
1,3: eapply SR_mono;
[ eapply (jcall ubs2_msyms MR) with (STK1 := RAWADD_STK) (FP1 := [(cg_raw s + 40, cg_raw s + 44)])
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => exists rcur : Z,
st_init_done A2 = true /\
obj_at ubs2segs mem2 (cg_raw s) LAY_Raw [ubs2_A_cgif_writecb; g; rw_gct s; rw_attr s; cg_W s; cg_H s; raw_sgct s; rw_loops s; rcur] /\
Permutation (blocks L2 A2) (blocks Lc Ac));
[ exact HS | reflexivity | exact HJ | exact Hra | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspv; replace (sp0 - 272) with (sp0 + (-17) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16
| clear - HRSv; lia | rewrite Hspv; clear - Hceil HFSv HRSv; lia | rewrite Hspv; lia | exact Htp
| intros a Ha; unfold inFP in Ha; cbn [In fst snd] in Ha; destruct Ha as (r & [<-|[]] & Hr); cbn [fst snd] in Hr;
split; [apply (HFP (cg_raw s) RAW_SIZE a); [right; left; reflexivity | lia] | lia] ];
intros HPRE1; eapply SR_mono;
[ eapply (RAWADD Lc Ac (ms_regs ms) (ms_mem ms) mdc (cg_raw s) g (sp0 - 272 + 128) (cgif_vals s)
(rw_gct s) (rw_attr s) (cg_W s) (cg_H s) (raw_sgct s) (rw_loops s) (rw_cur s)
(fr_lpal f) img fa w h tp lf dl sl dp tx Nimg rest0 HPRE1 Hid Ha0 Ha1);
[ clear - Hal16; apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hal16; [|lia]; destruct Hal16 as [q Hq]; exists (q * 2 - 18); lia
| rewrite Hspv; clear; lia | clear - Hsp063; lia | exact Hcfg
| eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply K1; lia]
| unfold raw_sgct; destruct (Z.eqb_spec (Z.land (cg_attr s) 4) 0); [apply Hngp; assumption | lia]
| eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply K1; lia]
| reflexivity | reflexivity | clear - Hw; lia | clear - Hh; lia | clear - Hw Hh HN HNle; nia | exact HleN | exact Hperm
| intros Hs; destruct (Hsl Hs) as [Hu1 ->]; exists (3 * fr_nlp f); split; [apply Hlct; change (Z.land (fr_attr f) 1) with u; rewrite Hu1; clear; lia | clear; lia] ]
| cbv beta; intros c' (L2 & A2 & regs2 & mem2 & md2 & res & rcur & -> & HJc & HP & Hid2 & Hr10 & Hraw2 & HB2);
exists L2, A2, regs2, mem2, md2; split; [rewrite Hra; reflexivity|]; split; [exact HJc|]; split; [exact HP|];
exists rcur; split; [exact Hid2 | split; [exact Hraw2 | exact HB2]] ]
| cbv beta; intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (rcur & Hid2 & Hraw2 & HB2));
exists L2, A2, regs2, mem2, md2, rcur; split; [reflexivity|]; split; [exact HJ2|]; split; [exact HP2|]; split; [exact Hid2|];
split; [exact Hraw2|]; split; [exact HB2|];
pose proof HJc2 as (_ & _ & Hhi2 & Hblk2 & _); rewrite Hspv in Hhi2; split; [exact Hhi2|];
intros a n k Hin Hk Hnot; apply (Hblk2 a n k Hin); [apply (Permutation_in _ (Permutation_sym HB2)); exact Hin | exact Hk |];
unfold inFP; cbn [In fst snd]; intros (r & [<-|[]] & Hr); cbn [fst snd] in Hr; lia ].
all: cbv beta; intros c' (L2 & A2 & regs2 & mem2 & md2 & rcur & -> & HJ2 & HP2 & Hid2 & Hraw2 & HB2 & Hhi2 & Hblk2); clear HJ.
all: cbn [ms_regs ms_mem mkst] in HP2, Hhi2, HJ2, Hblk2.
all: pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
all: jafter_call_keep HS 84%nat regs2 mem2 HP2 [0%nat] HS2.
all: match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end;
[ constructor; [|constructor]; eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi2 | lia | lia | clear - HRSv; lia | cbn; lia | cbn; lia] |].
all: clear HS; rename HS2 into HS.
all: jrun_to LAWS ubs2tbl_ok HS HJ2 ubs2_A_free; [eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia | apply wr_ok_nil] |].
all: jreg HS (10%bv:reg) as Hf10; rewrite (HE 8%nat 8%bv eq_refl), G8 in Hf10.
all: jreg HS (2%bv:reg) as Hf2; rewrite (HE 2%nat 2%bv eq_refl), G2 in Hf2.
all: jreg HS (4%bv:reg) as Hf4; rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hf4.
all: jreg HS (1%bv:reg) as Hfra.
all: jreg HS (3%bv:reg) as Hf3; rewrite (HE 3%nat 3%bv eq_refl), G3 in Hf3.
all: cbn [ms_mem mkst] in HF.
all: assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte ubs2segs (ms_mem ms0) a = mbyte ubs2segs mem2 a)
by (intros a Ha Hna; apply (mbyte_of_frame _ _ _ _ a HF Ha); intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; ew_havocA; rewrite ?HU2; lia |]); destruct Hr).
all: clear HF HG.
all: assert (GO : forall L3 A3 (regs3 : bvmap 5 word) (mem3 : word -> option byte) md3,
journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md L3 A3 mem3 md3 -> st_init_done A3 = true ->
Permutation (blocks L3 A3) (cgif_blocks g s N ++ rest) ->
(forall b m k, In (b, m) (cgif_blocks g s N) -> 0 <= k < m -> mbyte ubs2segs mem3 (b + k) = mbyte ubs2segs (ms_mem ms0) (b + k)) ->
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 272 - ALLOC_STACK <= x < sp0 - 272) -> mbyte ubs2segs mem3 x = mbyte ubs2segs (ms_mem ms0) x) ->
getr regs3 2 = getr (ms_regs ms0) 2 -> getr regs3 3 = getr (ms_regs ms0) 3 -> getr regs3 4 = getr (ms_regs ms0) 4 ->
SR ubs2segs (mkCfg (mkst regs3 (Z_to_bv 64 FL_RET) mem3 (seg_rom ubs2segs)) md3) (fl_post API regs0 g s N i rest FP L A mem md)).
1,3: intros L3 A3 regs3 mem3 md3 HJ3 Hid3 HB3 Kb Khi R2 R3 R4;
assert (ASv : ALLOC_STACK = 8192) by reflexivity;
assert (Kall : forall a n k, In (a, n) (cgif_blocks g s N) -> 0 <= k < n -> ~ (cg_raw s + 40 <= a + k < cg_raw s + 44) ->
mbyte ubs2segs mem3 (a + k) = mbyte ubs2segs memc (a + k))
by (intros a n k Hin Hk Hnot;
assert (Hin' : In (a, n) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; exact Hin);
destruct (blocks_range _ _ LAWS Lc Ac memc mdc a n HH0 Hin') as [B0 B1];
rewrite (Kb a n k Hin Hk), (K2 (a + k)) by (clear - B0 B1 Hk Hceil HFSv Hac; lia);
rewrite (Hblk2 a n k Hin' Hk Hnot); apply K1; clear - B0 B1 Hk Hceil HFSv Hac; lia);
eapply (fl_ret L A mem md regs0 regs3 L3 A3 mem3 md3 g N s i f gen1 rcur rest FP);
[ exact HJ3 | exact Hid3 | exact Hra0 | exact Hal16
| apply (CG mem3 rcur); [exact Kall|];
eapply obj_at_transport_range; [exact Hraw2 | exact (proj1 LAY_Raw_ok) |];
intros k Hk; rewrite (Kb (cg_raw s) RAW_SIZE k ltac:(right; left; reflexivity) ltac:(clear - Hk HRWv; lia));
apply K2; clear - Hk Hr0 Hr1 Hceil HFSv HRWv Hac; lia
| exact Hwf | exact Hf | exact HB3
| apply (fl_saved_ok_kept memc); [exact HSV|]; intros a Ha;
rewrite Khi, K2 by (clear - Ha Hceil Hsp063 HFSv ASv Hac; lia); rewrite (proj1 (Hhi2 a ltac:(clear - Ha Hceil Hsp063 HFSv Hac; lia) ltac:(clear - Ha HRSv; lia)));
apply K1; clear - Ha Hceil Hsp063 HFSv Hac; lia
| rewrite R2; exact Hf2
| split; [rewrite R3; exact Hf3 | rewrite R4, Hf4, Htp0; reflexivity] ].
all: destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)) as (Hh2 & Hl2 & _).
all: assert (ASv : ALLOC_STACK = 8192) by reflexivity.
all: assert (Hspm : (sp0 - 272) mod 16 = 0) by (replace (sp0 - 272) with (sp0 + (-17) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
all: destruct (Z.eq_dec pTmp 0) as [Hpz | Hpz].
1,3: rewrite Hpz in Hf10; eapply SR_bind;
[ eapply (jfree_null _ (aa_free_null API)); [exact HS | reflexivity | reflexivity | exact Hh2 | exact Hl2 | exact Hf10 | exact Hfra | apply ret_ok_even; vm_compute; reflexivity]
| cbv beta; intros c' ->; cbn [ms_regs ms_mem mkst];
destruct (Ht0 Hpz) as (Htm & _ & _);
apply (GO L2 A2 (ms_regs ms0) (ms_mem ms0) md2 HJ2 Hid2);
[ eapply Permutation_trans; [exact HB2 | rewrite <- (app_nil_l (cgif_blocks g s N ++ rest)), <- Htm; exact HB]
| intros; reflexivity | intros; reflexivity | reflexivity | reflexivity | reflexivity ] ].
all: destruct (Ht1 Hpz) as (Htm & _ & _).
all: assert (Hpin : In (pTmp, Nt) (blocks L2 A2)) by (apply (Permutation_in _ (Permutation_sym HB2)), (Permutation_in _ (Permutation_sym HB)); rewrite Htm; left; reflexivity).
all: eapply SR_bind;
[ eapply (jfree_at _ _ LAWS ubs2_errno_low IMG (aa_free API)) with (a := pTmp) (n := Nt) (spc := sp0 - 272);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact Hpin | exact Hf10
| exact Hf2 | clear - Hceil Hsp063 HFSv Hac; lia | exact Hspm | clear - HFSv ASv; lia | lia | exact Hf4 | exact Hfra | apply ret_ok_even; vm_compute; reflexivity
| exact Htmp_fp ]
| ].
all: cbv beta; intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hrm3 & Hkeep3 & Hhi3 & Hid3).
all: change (ms_segs ubs2_msyms) with ubs2segs in Hkeep3, Hhi3; cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, HJ3.
all: assert (HB3 : Permutation (blocks L3 A3) (cgif_blocks g s N ++ rest))
by (eapply perm_after_rm1; [| exact Hrm3]; eapply Permutation_trans; [exact HB2 | rewrite Htm in HB; exact HB]).
all: apply (GO L3 A3 regs3 mem3 md3 HJ3 Hid3 HB3);
[ intros b m k Hin Hk; apply (Hkeep3 b m k); [apply (Permutation_in _ (Permutation_sym HB3)); apply in_app_iff; left; exact Hin | exact Hk]
| intros x Hx Hnx; apply (proj1 (Hhi3 x Hx Hnx))
| exact (HP3 2 ltac:(unfold callee_saved; lia)) | exact (HP3 3 ltac:(unfold callee_saved; lia)) | exact (HP3 4 ltac:(unfold callee_saved; lia)) ].
Qed.
Lemma fl_word_any : forall (m : word -> option byte) a, CEIL_MIN <= a -> a + 8 <= 2 ^ 64 ->
(forall k, 0 <= k < 8 -> writable_at ubs2segs m (a + k)) -> exists v, 0 <= v < 2 ^ 64 /\ word_mem ubs2segs m a v.
Proof.
intros m a Ha0 Ha1 Hw.
assert (Hb : forallb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? CEIL_MIN) ubs2segs = true) by (vm_compute; reflexivity).
destruct (YI0d.val_mem_of_present8 ubs2segs m a) as (v & Hv & HV).
- intros k Hk. specialize (Hw k Hk). unfold writable_at, wview in Hw. unfold mbyte.
destruct (m (Z_to_bv 64 (a + k))) as [b|]; [exists b; reflexivity|]. exfalso.
destruct (find_segment ubs2segs (bv_unsigned (Z_to_bv 64 (a + k))) 1) as [sg|] eqn:Hf; [| apply Hw; reflexivity].
pose proof (YK1j.find_segment_range _ _ _ _ Hf) as [H1 H2]. pose proof (YK1j.find_segment_in _ _ _ _ Hf) as Hin.
pose proof (proj1 (forallb_forall _ _) Hb sg Hin) as Hle. cbn beta in Hle. apply Z.leb_le in Hle.
rewrite unsigned_lit_small in H2 by lia. lia.
- exists v. split; [exact Hv|]. apply val_mem_word_mem. exact HV.
Qed.
Lemma fl_tail :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f : frame_st) (gen1 : Z)
(rest FP tmp : list (Z * Z)) (pTmp Nt tv w h pc top left : Z),
let sp0 := spZ regs0 in
journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) ->
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) -> cgif_wf s N -> (i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some (Some f) ->
(forall b n a, In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP FP a) ->
Permutation (blocks Lc Ac) (tmp ++ cgif_blocks g s N ++ rest) ->
((tmp = [] /\ pTmp = 0 /\ w * h <= N) \/ (tmp = [(pTmp, Nt)] /\ pTmp <> 0 /\ w * h <= Nt)) ->
(In (pTmp, Nt) (blocks L A) -> forall k, 0 <= k < Nt -> inFP FP (pTmp + k)) ->
(pc = FL_RAW \/ (pc = FL_RAW2 /\ pTmp <> 0)) ->
1 <= w <= cg_W s -> 1 <= h <= cg_H s -> 0 <= tv < 2 ^ 64 ->
fl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 272) -> getr regs1 8 = Z_to_bv 64 pTmp -> getr regs1 9 = Z_to_bv 64 tv -> getr regs1 16 = Z_to_bv 64 h ->
word_mem ubs2segs memc (sp0 - 272 + 112) g -> word_mem ubs2segs memc (sp0 - 272 + 120) (fr_ptr f) ->
word_mem ubs2segs memc (sp0 - 272 + 56) (Z.land (fr_attr f) 1) ->
word_mem ubs2segs memc (sp0 - 272 + 96) top ->
(pc = FL_RAW2 -> word_mem ubs2segs memc (sp0 - 272 + 40) w /\ word_mem ubs2segs memc (sp0 - 272 + 48) left) ->
(pc = FL_RAW -> getr regs1 22 = Z_to_bv 64 left /\ getr regs1 23 = Z_to_bv 64 w) ->
fl_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 pc) memc (seg_rom ubs2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof using IMG RAWADD.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f gen1 rest FP tmp pTmp Nt tv w h pc top left sp0
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hi Hf HFP HB Htmp Htmp_fp Hpc Hw Hh Htv HSV G2 G8 G9 G16 Wg Wfr Wu1 Wtop W2 R1 [G3 G4].
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & _ & Hfwf).
set (s1 := flush_upd s i gen1 (rw_cur s)) in Hat. set (f1 := set_fr_gen f gen1).
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hf1in : In (Some f1) (cg_frames s1)) by (rewrite Hfr1; eapply nth_error_In; apply nth_error_list_set_same; exact Hilt).
assert (HBc : Permutation (blocks Lc Ac) (cgif_blocks g s N ++ (tmp ++ rest))) by (eapply Permutation_trans; [exact HB|]; apply Permutation_app_swap_app).
destruct (af_cgif_geom API Lc Ac memc mdc g s N _ HH0 HBc) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom f Hfin) as (Hp0 & Hp1 & Hpg).
destruct (fl_img_geom API Lc Ac memc mdc g s N _ f HH0 HBc Hfin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Him0 Him1].
pose proof Hat as (Hobj & Hraw & Hfrs). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s) : cgif_vals s1 = cgif_vals s) in Hobj.
pose proof (Hfrs f1 Hf1in) as Hfobj. change (fr_ptr f1) with (fr_ptr f) in Hfobj.
pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf.
pose proof (Rf 0%nat (fr_lpal f) eq_refl) as Rlpal. pose proof (Rf 1%nat (fr_img f) eq_refl) as Rimg. pose proof (Rf 2%nat (fr_attr f) eq_refl) as Rfattr.
cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rlpal, Rimg, Rfattr.
change (fr_img f1) with (fr_img f) in Rimg.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. cbn [nth snd LAY_CGIF Z.of_N] in RH, RW.
assert (Hu1r : 0 <= Z.land (fr_attr f) 1 <= 1) by (pose proof (land1_cases (fr_attr f) ltac:(clear - Rfattr; lia)); lia).
destruct (fl_word_any memc (sp0 - 272 + 16) ltac:(clear - Hac Hceil HFSv; lia) ltac:(clear - Hsp063; lia)
  ltac:(intros k Hk; apply Hstw; clear - Hk Hac Hceil HFSv; lia)) as (d16 & Rd16 & Wd16).
destruct (fl_word_any memc (sp0 - 272 + 24) ltac:(clear - Hac Hceil HFSv; lia) ltac:(clear - Hsp063; lia)
  ltac:(intros k Hk; apply Hstw; clear - Hk Hac Hceil HFSv; lia)) as (d24 & Rd24 & Wd24).
destruct (fl_word_any memc (sp0 - 272 + 32) ltac:(clear - Hac Hceil HFSv; lia) ltac:(clear - Hsp063; lia)
  ltac:(intros k Hk; apply Hstw; clear - Hk Hac Hceil HFSv; lia)) as (d32 & Rd32 & Wd32).
destruct (fl_word_any memc (sp0 - 272 + 48) ltac:(clear - Hac Hceil HFSv; lia) ltac:(clear - Hsp063; lia)
  ltac:(intros k Hk; apply Hstw; clear - Hk Hac Hceil HFSv; lia)) as (d48 & Rd48 & Wd48).
destruct (fl_word_any memc (sp0 - 272 + 96) ltac:(clear - Hac Hceil HFSv; lia) ltac:(clear - Hsp063; lia)
  ltac:(intros k Hk; apply Hstw; clear - Hk Hac Hceil HFSv; lia)) as (d96 & Rd96 & Wd96).
set (mo := [g; fr_ptr f; d96; d24; w; d48; d16; Z.land (fr_attr f) 1; d32] : list Z).
set (E := fl_E regs1 regs0 s f1 None mo).
pose proof (fl_HE regs1 regs0 s f1 None mo : forall n rr, _ -> ew E n = _) as HE.
pose proof (fl_HK regs1 regs0 s f1 None mo : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (fl_HF regs1 regs0 s f1 None mo : forall n j v, _ -> _ -> ew E n = _) as HFf.
pose proof (fl_HM regs1 regs0 s f1 None mo : forall n j v, _ -> _ -> ew E n = _) as HM.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HE80 : ew E 80 = Z_to_bv 64 g) by (apply (HM 80%nat 0%nat g eq_refl eq_refl)).
assert (HE81 : ew E 81 = Z_to_bv 64 (fr_ptr f)) by (apply (HM 81%nat 1%nat (fr_ptr f) eq_refl eq_refl)).
assert (HE82 : ew E 82 = Z_to_bv 64 d96) by (apply (HM 82%nat 2%nat d96 eq_refl eq_refl)).
assert (HE83 : ew E 83 = Z_to_bv 64 d24) by (apply (HM 83%nat 3%nat d24 eq_refl eq_refl)).
assert (HE84 : ew E 84 = Z_to_bv 64 w) by (apply (HM 84%nat 4%nat w eq_refl eq_refl)).
assert (HE85 : ew E 85 = Z_to_bv 64 d48) by (apply (HM 85%nat 5%nat d48 eq_refl eq_refl)).
assert (HE86 : ew E 86 = Z_to_bv 64 d16) by (apply (HM 86%nat 6%nat d16 eq_refl eq_refl)).
assert (HE87 : ew E 87 = Z_to_bv 64 (Z.land (fr_attr f) 1)) by (apply (HM 87%nat 7%nat _ eq_refl eq_refl)).
assert (HE88 : ew E 88 = Z_to_bv 64 d32) by (apply (HM 88%nat 8%nat d32 eq_refl eq_refl)).
assert (HU80 : bv_unsigned (ew E 80) = g) by (rewrite HE80; apply unsigned_lit_small; lia).
assert (HU81 : bv_unsigned (ew E 81) = fr_ptr f) by (rewrite HE81; apply unsigned_lit_small; lia).
assert (HE62 : ew E 62 = Z_to_bv 64 (fr_lpal f)) by (apply (HFf 62%nat 0%nat _ eq_refl eq_refl)).
assert (HE63 : ew E 63 = Z_to_bv 64 (fr_img f)) by (apply (HFf 63%nat 1%nat _ eq_refl eq_refl)).
assert (HE2 : ew E 2 = Z_to_bv 64 (sp0 - 272)) by (rewrite (HE 2%nat 2%bv eq_refl); exact G2).
assert (HE3 : ew E 3 = getr regs0 3) by (rewrite (HE 3%nat 3%bv eq_refl); exact G3).
assert (HE4 : ew E 4 = getr regs0 4) by (rewrite (HE 4%nat 4%bv eq_refl); exact G4).
assert (HE8 : ew E 8 = Z_to_bv 64 pTmp) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE16 : ew E 16 = Z_to_bv 64 h) by (rewrite (HE 16%nat 16%bv eq_refl); exact G16).
assert (GO : forall ss ms' rg0 (isv : sv) (img : Z), st_ok ubs2segs E ss ms' -> ss_pc ss = FL_CFG -> ss_resv ss = None ->
nth_error (ss_mem ss) 0 = Some rg0 -> r_base rg0 = Some 2%nat ->
incl_chunks (fl_stk_saved 32 ++ [mkChunk 56 (CVal 8 (SOff 87 0)); mkChunk 96 (CVal 8 (SOff 82 0)); mkChunk 112 (CVal 8 (SOff 80 0));
mkChunk 120 (CVal 8 (SOff 81 0)); mkChunk 128 (CVal 8 (SOff 62 0)); mkChunk 136 (CVal 8 isv)]) (r_chunks rg0) = true ->
sv_denot E isv = Z_to_bv 64 img -> ((pTmp = 0 /\ img = fr_img f) \/ (pTmp <> 0 /\ img = pTmp)) ->
getr (ms_regs ms') 2 = Z_to_bv 64 (sp0 - 272) -> getr (ms_regs ms') 3 = getr regs0 3 -> getr (ms_regs ms') 4 = getr regs0 4 ->
getr (ms_regs ms') 8 = Z_to_bv 64 pTmp -> getr (ms_regs ms') 16 = Z_to_bv 64 h -> getr (ms_regs ms') 23 = Z_to_bv 64 w ->
journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte ubs2segs (ms_mem ms') a = mbyte ubs2segs memc a) ->
SR ubs2segs (mkCfg ms' mdc) (fl_post API regs0 g s N i rest FP L A mem md)).
{ intros ss ms' rg0 isv img HS' Hpc' Hrv Hrg0 Hb0 Hincl Hisv Himg Q2 Q3 Q4 Q8 Q16 Q23 HJ' K.
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc'.
pose proof (st_region_chunks ubs2segs E ss ms' 0 rg0 2%nat (sp0 - 272) HS' Hrg0 Hb0 HU2) as Hcs.
pose proof (incl_Forall (incl_chunks_sound _ _ Hincl) Hcs) as Hcs'.
apply Forall_app in Hcs' as [Hsaved Hc3].
pose proof (proj1 (Forall_forall _ _) Hc3 _ ltac:(left; reflexivity)) as C56.
pose proof (proj1 (Forall_forall _ _) Hc3 _ ltac:(right; left; reflexivity)) as C96.
pose proof (proj1 (Forall_forall _ _) Hc3 _ ltac:(right; right; left; reflexivity)) as C112.
pose proof (proj1 (Forall_forall _ _) Hc3 _ ltac:(right; right; right; left; reflexivity)) as C120.
pose proof (proj1 (Forall_forall _ _) Hc3 _ ltac:(right; right; right; right; left; reflexivity)) as C128.
pose proof (proj1 (Forall_forall _ _) Hc3 _ ltac:(right; right; right; right; right; left; reflexivity)) as C136.
assert (Himr : 0 <= img < 2 ^ 64).
{ destruct Himg as [[_ ->] | [Hnz ->]]; [lia|].
destruct Htmp as [(_ & Hz & _) | (Htm & _ & Hle)]; [lia|].
assert (Hin : In (pTmp, Nt) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); rewrite Htm; left; reflexivity).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pTmp Nt HH0 Hin) as [T0 T1]. clear - T0 T1 Hle Hw Hh Hac. nia. }
eapply (fl_cfg L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s i f gen1 rest FP tmp pTmp Nt img w h d96);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hi | exact Hf | exact HFP | exact HB
| destruct Htmp as [(A1 & A2 & A3) | (A1 & A2 & A3)]; destruct Himg as [[B1 B2] | [B1 B2]]; try lia; [left | right]; auto
| exact Htmp_fp | exact Hw | exact Hh
| apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply K; lia]
| apply (chunk_word E _ _ _ _ _ C112); [cbn [sv_denot]; rewrite Z.add_0_r, HE80, Z_to_bv_bv_unsigned; reflexivity | lia]
| apply (chunk_word E _ _ _ _ _ C120); [cbn [sv_denot]; rewrite Z.add_0_r, HE81, Z_to_bv_bv_unsigned; reflexivity | lia]
| apply (chunk_word E _ _ _ _ _ C128); [cbn [sv_denot]; rewrite Z.add_0_r, HE62, Z_to_bv_bv_unsigned; reflexivity | lia]
| apply (chunk_word E _ _ _ _ _ C136); [exact Hisv | exact Himr]
| apply (chunk_word E _ _ _ _ _ C56); [cbn [sv_denot]; rewrite Z.add_0_r, HE87, Z_to_bv_bv_unsigned; reflexivity | lia]
| apply (chunk_word E _ _ _ _ _ C96); [cbn [sv_denot]; rewrite Z.add_0_r, HE82, Z_to_bv_bv_unsigned; reflexivity | lia]
| exact Q2 | exact Q8 | exact Q23 | exact Q16
| split; [exact Q3 | exact Q4] ].
destruct Hat as (_ & _ & _).
split; [| split].
- rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s)). eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply K; clear - Hk Hg0 Hg1 Hceil HFSv HGSv Hac; lia].
- change (cg_raw (flush_upd s i gen1 (rw_cur s))) with (cg_raw s).
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply K; clear - Hk Hr0 Hr1 Hceil HFSv HRWv Hac; lia].
- intros x Hx. assert (Hx1 : In (Some x) (cg_frames s1)) by exact Hx.
destruct (In_frames_flush_upd s i gen1 (rw_cur s) f x Hf Hx) as [-> | [Hin _]].
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply K; change (fr_ptr (set_fr_gen f gen1)) with (fr_ptr f); clear - Hk Hp0 Hp1 Hceil HFSv HFRv Hac; lia].
+ destruct (Hfgeom x Hin) as (X0 & X1 & _).
eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply K; clear - Hk X0 X1 Hceil HFSv HFRv Hac; lia]. }
assert (WR : forall E0 cs, bv_unsigned (ew E0 2) = sp0 - 272 ->
wr_ok E0 [YQ0b.mkRegion (Some 2%nat) 0 272 0 168 cs; fl_RgM; fl_RfM] FLUSH_STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 cs H2. eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (HR0 : forall r2 : bool, (r2 = true -> word_mem ubs2segs memc (sp0 - 272 + 40) w) ->
region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 272 0 168 (fl_raw_stk r2))).
{ intros r2 Hr2. unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
unfold fl_raw_stk. apply Forall_app; split; [apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV); intros j v Hj; exact (HK _ j v eq_refl Hj)|].
apply Forall_app; split.
- constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]]].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ d16); [cbn [sv_denot]; rewrite Z.add_0_r, HE86, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wd16].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ d24); [cbn [sv_denot]; rewrite Z.add_0_r, HE83, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wd24].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ d32); [cbn [sv_denot]; rewrite Z.add_0_r, HE88, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wd32].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ (Z.land (fr_attr f) 1)); [cbn [sv_denot]; rewrite Z.add_0_r, HE87, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wu1].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ d96); [cbn [sv_denot]; rewrite Z.add_0_r, HE82, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wd96].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, HE80, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wg].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_ptr f)); [cbn [sv_denot]; rewrite Z.add_0_r, HE81, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wfr].
- destruct r2; [| constructor]. pose proof (Hr2 eq_refl) as W40.
constructor; [| constructor; [| constructor]].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ w); [cbn [sv_denot]; rewrite Z.add_0_r, HE84, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W40].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ d48); [cbn [sv_denot]; rewrite Z.add_0_r, HE85, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wd48]. }
pose proof (fl_RgM_ok regs1 regs0 s f1 None mo memc g HU80 ltac:(lia) ltac:(lia) Hobj) as HR1.
pose proof (fl_RfM_ok regs1 regs0 s f1 None mo memc (fr_ptr f) HU81 ltac:(lia) ltac:(lia) Hfobj) as HR2.
assert (HPD : forall (pc' : Z) (pz r2 : bool), pairwise_disjoint E (ss_mem (ss_raw pc' pz r2))).
{ intros pc' pz r2. cbn [ss_mem ss_raw]. unfold fl_RgM, fl_RfM. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU80, HU81. clear - Hg1 Hp1 Hpg Hceil HFSv HGSv HFRv Hac. repeat split; lia. }
pose proof (fl_gfacts_ok regs1 regs0 s f1 None mo memc g N Hobj Hwf ltac:(lia) ltac:(lia)) as HFAb.
pose proof (fl_ffacts_ok regs1 regs0 s f1 None mo memc (fr_ptr f) Hfobj Him0 ltac:(change (fr_img f1) with (fr_img f); clear - Him1 HN HW1 HH1; nia)) as HFAc.
assert (HFAa : atoms_ok E fl_factsM).
{ cbn [atoms_ok fl_factsM]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU80, HU81.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia.
+ replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16.
+ pose proof (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr f) FRAME_SIZE HH0 ltac:(apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; apply (frame_blocks_in_cgif g s N f); [exact Hfin | left; reflexivity]) ltac:(lia)) as (_ & _ & Hp16).
clear - Hp16. apply Z.mod_divide in Hp16; [|lia]. apply Z.mod_divide; [lia|]. destruct Hp16 as [q Hq]. exists (q * 2). lia. }
assert (HFAd : pTmp <> 0 -> atoms_ok E [(8%nat, mkAF 1 (2^64 - 1) 0)]).
{ intros Hpz. destruct Htmp as [(_ & Hz & _) | (Htm & _ & Hle)]; [lia|].
assert (Hin : In (pTmp, Nt) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); rewrite Htm; left; reflexivity).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pTmp Nt HH0 Hin) as [T0 T1].
assert (T2 : pTmp < alloc_ceiling) by (clear - T1 Hle Hw Hh; nia).
cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE8, unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite Z.mod_1_r. clear - T0 T2 Hac. repeat split; lia. }
assert (MK : forall (pc' : Z) (pz r2 : bool), (if pz then pTmp = 0 else pTmp <> 0) ->
(r2 = true -> word_mem ubs2segs memc (sp0 - 272 + 40) w) ->
st_ok ubs2segs E (ss_raw pc' pz r2) (mkst regs1 (Z_to_bv 64 pc') memc (seg_rom ubs2segs))).
{ intros pc' pz r2 Hpz Hr2. unfold ss_raw. apply entry_st_ok_full; [| destruct pz, r2; vm_compute; reflexivity | | exact (HPD pc' pz r2) |].
- destruct pz; [| apply regs_ok_Ereg]. apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx |]. rewrite G8, Hpz. reflexivity.
- constructor; [exact (HR0 r2 Hr2)|]. constructor; [exact HR1|]. constructor; [exact HR2|]. constructor.
- split; [| split; exact I]. apply atoms_ok_app; [exact HFAa|]. apply atoms_ok_app; [exact HFAb|]. apply atoms_ok_app; [exact HFAc|].
destruct pz; [exact I | exact (HFAd Hpz)]. }
clear HR0 HR1 HR2 HPD HFAa HFAb HFAc HFAd.
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte ubs2segs memc a = mbyte ubs2segs memc a) by (intros; reflexivity).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 pc) memc (seg_rom ubs2segs))) in HJ.
assert (CASES : (pc = FL_RAW /\ pTmp = 0) \/ (pc = FL_RAW /\ pTmp <> 0) \/ (pc = FL_RAW2 /\ pTmp <> 0))
by (destruct (Z.eq_dec pTmp 0); destruct Hpc as [H1 | [H2 H3]]; [left; auto | exfalso; exact (H3 e) | right; left; auto | right; right; auto]).
clear Hpc.
destruct CASES as [[-> Hpz] | [[-> Hpz] | [-> Hpz]]];
[ pose proof (MK FL_RAW true false Hpz ltac:(intros Hx; discriminate Hx)) as HS; destruct (R1 eq_refl) as (G22 & G23)
| pose proof (MK FL_RAW false false Hpz ltac:(intros Hx; discriminate Hx)) as HS; destruct (R1 eq_refl) as (G22 & G23)
| pose proof (MK FL_RAW2 false true Hpz (fun _ => proj1 (W2 eq_refl))) as HS ]; clear MK.
all: try (assert (HE23 : ew E 23 = Z_to_bv 64 w) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23)).
all: br_tree ltac:(idtac; runW LAWS FL_CFG ltac:(apply WR; repeat (rewrite ew_havoc_old; [|cbv; lia]); exact HU2) HU2 (sp0 - 272) (sp0 - 272 + 168))
ltac:(idtac; let HS := get_HS in let HJ := get_HJ in
lazymatch goal with K : forall a, _ -> _ -> mbyte ubs2segs _ a = mbyte ubs2segs _ a |- _ =>
first [ eapply (GO _ _ _ (SOff 63 0) (fr_img f) HS);
[ reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
| cbn [sv_denot]; rewrite Z.add_0_r, HE63, Z_to_bv_bv_unsigned; reflexivity | left; split; [assumption | reflexivity]
| rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | exact HJ | exact K ]
| eapply (GO _ _ _ (SOff 8 0) pTmp HS);
[ reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
| cbn [sv_denot]; rewrite Z.add_0_r, HE8, Z_to_bv_bv_unsigned; reflexivity | right; split; [assumption | reflexivity]
| rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | exact HJ | exact K ] ] end)
4%nat.
Qed.
End S.
End p.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
