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
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b UN3c
YI06 UI5b YI09 YI08 YI0t YI0r YI0o UI3p UI3n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma tfree_pre_case : forall (p n : Z) rest Bfin (bl : list (Z * Z)) (T : Z * Z -> Prop),
Permutation bl (nz ((p, n) :: rest) ++ Bfin) -> (forall b, In b (nz ((p, n) :: rest)) -> T b) ->
p = 0 \/ (In (p, n) bl /\ T (p, n)).
Proof using.
intros p n rest Bfin bl T HP HT. destruct (Z.eq_dec p 0) as [-> | Hp]; [left; reflexivity | right].
assert (Hin : In (p, n) (nz ((p, n) :: rest))) by (rewrite nz_cons_nz by exact Hp; left; reflexivity).
split; [| exact (HT _ Hin)].
eapply Permutation_in; [apply Permutation_sym; exact HP |]. apply in_app_iff. left. exact Hin.
Qed.
Lemma tfree_post_step : forall (p n : Z) rest Bfin (blc bl2 : list (Z * Z)),
Permutation blc (nz ((p, n) :: rest) ++ Bfin) ->
(p = 0 /\ bl2 = blc \/ p <> 0 /\ rm1 (p, n) blc bl2) ->
Permutation bl2 (nz rest ++ Bfin).
Proof using.
intros p n rest Bfin blc bl2 HP [[-> ->] | [Hp Hrm]].
- rewrite nz_cons0 in HP. exact HP.
- rewrite nz_cons_nz in HP by exact Hp. eapply perm_after_rm1; [exact HP | exact Hrm].
Qed.
Lemma tnz_tl : forall (b : Z * Z) rest (T : Z * Z -> Prop),
(forall x, In x (nz (b :: rest)) -> T x) -> forall x, In x (nz rest) -> T x.
Proof using.
intros b rest T H x Hx. apply H. unfold nz in *. cbn [List.filter]. destruct (negb (fst b =? 0)); [right|]; exact Hx.
Qed.
Lemma tin_bfin : forall (l Bfin bl : list (Z * Z)) x, Permutation bl (l ++ Bfin) -> In x Bfin -> In x bl.
Proof using. intros l Bfin bl x HP Hx. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. right. exact Hx. Qed.
Definition tsaved_chunks (k : nat) : list YP09.chunk :=
map (fun jd => mkChunk (112 - snd jd) (CVal 8 (SOff (k + fst jd)%nat 0)))
(combine (seq 0 13) (map snd SAVED)).
Lemma tsaved_chunks_ok : forall E m regs0 spe k,
(forall j, (j < 13)%nat -> ew E (k + j)%nat = nth j (saved_vals regs0) (Z_to_bv 64 0)) ->
frame_saved ubs0_msyms regs0 m spe ->
Forall (chunk_ok ubs0segs E m (spe - 112)) (tsaved_chunks k).
Proof using.
intros E m regs0 spe k HE HF.
unfold tsaved_chunks. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([j d] & <- & Hjd).
cbn [fst snd].
apply in_combine_r in Hjd as Hd0. pose proof (in_combine_l _ _ _ _ Hjd) as Hj0. apply in_seq in Hj0.
assert (Hnth : nth_error (map snd SAVED) j = Some d /\ exists r, nth_error SAVED j = Some (r, d)).
{ clear - Hjd. cbv [SAVED map snd combine seq] in Hjd.
repeat (destruct Hjd as [Hjd|Hjd]; [inversion Hjd; subst; split; [reflexivity | eexists; reflexivity] |]). destruct Hjd. }
destruct Hnth as [Hnd (r & Hr)].
assert (Hin : In (r, d) SAVED) by (eapply nth_error_In; exact Hr).
pose proof (HF r d Hin) as W.
pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
eapply (chunk_ok_val ubs0segs E m (spe - 112) _ 8%N _ (bv_unsigned (getr regs0 r))).
- cbn [sv_denot]. rewrite Z.add_0_r, (HE j ltac:(lia)).
unfold saved_vals. erewrite (nth_error_nth _ _ _ (map_nth_error _ _ _ Hr)). cbn [fst]. rewrite Z_to_bv_bv_unsigned. reflexivity.
- cbn. lia.
- cbn. lia.
- replace (spe - 112 + (112 - d)) with (spe - d) by lia. apply val_mem_word_mem. exact W.
Qed.
Definition tclean_gregion : YP09.region :=
YP09.mkRegion (Some 8%nat) 0 72 0 0
[ mkChunk 40 (CVal 8 (SOff 45%nat 0)); mkChunk 0 (CVal 8 (SOff 46%nat 0)); mkChunk 8 (CVal 8 (SOff 47%nat 0));
mkChunk 16 (CVal 8 (SOff 48%nat 0)); mkChunk 24 (CVal 8 (SOff 49%nat 0)); mkChunk 32 (CVal 8 (SOff 50%nat 0)) ].
Definition ss_tclean : sstate :=
mkSS TPC_CLEAN sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 112 0 0 (tsaved_chunks 32); tclean_gregion ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + 8224) (2^63) 4); (8%nat, mkAF 4096 CEIL_MAX 4) ] [] []).
Definition ss_tclean_c : sstate := Eval vm_compute in ss_tclean.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Definition tclean_post (STK sp0 : Z) FP L A mem md (regs0 : bvmap 5 word) (mem1 : word -> option byte)
(Bfin : list (Z * Z)) (r : Z) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 (getr regs0 1) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\ st_init_done A2 = true /\
regs_preserved regs0 regs2 /\ getr regs2 10 = Z_to_bv 64 r /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs0 - LZW_STK <= a < spZ regs0) ->
mbyte ubs0segs mem2 a = mbyte ubs0segs mem1 a) /\
(forall b m i, In (b, m) Bfin -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs mem1 (b + i)) /\
Permutation (blocks L2 A2) Bfin.
Definition gptrs (mem : word -> option byte) (g : Z) (ld ti lm lc li tm : Z * Z) : Prop :=
word_mem ubs0segs mem (g + 40) (fst ld) /\ word_mem ubs0segs mem g (fst ti) /\ word_mem ubs0segs mem (g + 8) (fst lm) /\
word_mem ubs0segs mem (g + 16) (fst lc) /\ word_mem ubs0segs mem (g + 24) (fst li) /\ word_mem ubs0segs mem (g + 32) (fst tm).
Lemma tlzw_clean :
forall STK sp0 FP L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte)
(g : Z) (ld ti lm lc li tm : Z * Z) (Bfin : list (Z * Z)) (r : Z),
journal ubs0_msyms MR STK sp0 FP L A mem md L1 A1 mem1 md1 -> st_init_done A1 = true ->
Permutation (blocks L1 A1) (nz [ld; ti; lm; lc; li; tm] ++ (g, 72) :: Bfin) ->
(forall b, In b (nz [ld; ti; lm; lc; li; tm]) -> ftok FP (blocks L A) b) -> ftok FP (blocks L A) (g, 72) ->
gptrs mem1 g ld ti lm lc li tm -> (forall b, In b [ld; ti; lm; lc; li; tm] -> 0 <= fst b < 2 ^ 64) ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
spZ regs0 mod 16 = 0 -> sp0 - STK <= spZ regs0 - LZW_STK -> spZ regs0 <= sp0 ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 112) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 r -> 0 <= r < 2 ^ 64 ->
frame_saved ubs0_msyms regs0 mem1 (spZ regs0) ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 TPC_CLEAN) mem1 (seg_rom ubs0segs)) md1)
(tclean_post STK sp0 FP L A mem md regs0 mem1 Bfin r).
Proof using IMG.
intros STK sp0 FP L A mem md L1 A1 md1 regs0 regs1 mem1 g ld ti lm lc li tm Bfin r
HJ Hid HB Htok Hgtok HG Hrng Hra0 Htp0 Hal16 Hwlo Hwhi G2 G3 G4 G8 G9 Hr HFS.
destruct ld as [pld nld], ti as [pti nti], lm as [plm nlm], lc as [plc nlc], li as [pli nli], tm as [ptm ntm].
destruct HG as (W40 & W0 & W8 & W16 & W24 & W32). cbn [fst] in W40, W0, W8, W16, W24, W32.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HSTKv : LZW_STK = 8400) by reflexivity.
pose proof HJ as (HH1 & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp := spZ regs0) in *.
assert (Hspm : (sp - 112) mod 16 = 0).
{ replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (Hgin : In (g, 72) (blocks L1 A1)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. left. reflexivity. }
destruct (heap_blocks_range _ _ LAWS _ _ _ _ g 72 HH1 Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
pose proof (Hrng _ ltac:(left; reflexivity)) as R40. pose proof (Hrng _ ltac:(right; left; reflexivity)) as R0.
pose proof (Hrng _ ltac:(right; right; left; reflexivity)) as R8. pose proof (Hrng _ ltac:(right; right; right; left; reflexivity)) as R16.
pose proof (Hrng _ ltac:(right; right; right; right; left; reflexivity)) as R24. pose proof (Hrng _ ltac:(do 5 right; left; reflexivity)) as R32.
cbn [fst] in R40, R0, R8, R16, R24, R32. clear Hrng.
set (extra := saved_vals regs0 ++ [Z_to_bv 64 pld; Z_to_bv 64 pti; Z_to_bv 64 plm; Z_to_bv 64 plc; Z_to_bv 64 pli; Z_to_bv 64 ptm]).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs1 extra) n = getr regs1 rr) by (intros; apply ew_Ereg_nat; assumption).
assert (Hlen13 : length (saved_vals regs0) = 13%nat) by reflexivity.
assert (HX : forall j, (j < 13)%nat -> ew (Ereg regs1 extra) (32 + j)%nat = nth j (saved_vals regs0) (Z_to_bv 64 0)).
{ intros j Hj. rewrite ew_Ereg_extra. subst extra. rewrite app_nth1 by (rewrite Hlen13; exact Hj). reflexivity. }
assert (HX' : forall n j, (n = 32 + j)%nat -> (j < 13)%nat -> ew (Ereg regs1 extra) n = nth j (saved_vals regs0) (Z_to_bv 64 0)).
{ intros n j -> Hj. exact (HX j Hj). }
assert (HY : forall j, ew (Ereg regs1 extra) (32 + (13 + j))%nat = nth j [Z_to_bv 64 pld; Z_to_bv 64 pti; Z_to_bv 64 plm; Z_to_bv 64 plc; Z_to_bv 64 pli; Z_to_bv 64 ptm] (Z_to_bv 64 0)).
{ intros j. rewrite ew_Ereg_extra. subst extra. rewrite <- Hlen13. apply app_nth2_plus. }
pose proof (HY 0%nat) as H45. pose proof (HY 1%nat) as H46. pose proof (HY 2%nat) as H47.
pose proof (HY 3%nat) as H48. pose proof (HY 4%nat) as H49. pose proof (HY 5%nat) as H50.
cbn [nth Nat.add] in H45, H46, H47, H48, H49, H50. clear HY.
assert (HE2 : bv_unsigned (ew (Ereg regs1 extra) 2) = sp - 112) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HE8 : ew (Ereg regs1 extra) 8 = Z_to_bv 64 g) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HS : st_ok ubs0segs (Ereg regs1 extra) ss_tclean_c (mkst regs1 (Z_to_bv 64 TPC_CLEAN) mem1 (seg_rom ubs0segs))).
{ change ss_tclean_c with ss_tclean. unfold ss_tclean. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply (tsaved_chunks_ok _ mem1 regs0 sp 32 HX HFS).
+ unfold region_ok, tclean_gregion. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE8, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
Ltac gck H W R := eapply chunk_ok_val; [cbn [sv_denot]; rewrite H, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; first [exact W | rewrite Z.add_0_r; exact W]].
constructor; [gck H45 W40 R40|]. constructor; [gck H46 W0 R0|]. constructor; [gck H47 W8 R8|].
constructor; [gck H48 W16 R16|]. constructor; [gck H49 W24 R24|]. constructor; [gck H50 W32 R32|]. constructor.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, tclean_gregion. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE8, unsigned_lit_small by lia. repeat split. lia.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE2, HE8, unsigned_lit_small by lia.
change (2 ^ 4) with 16. repeat split; first [lia | exact Hspm | exact Hg16]. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 TPC_CLEAN) mem1 (seg_rom ubs0segs))) in HJ.
assert (MHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - LZW_STK <= a < sp) ->
mbyte ubs0segs (ms_mem (mkst regs1 (Z_to_bv 64 TPC_CLEAN) mem1 (seg_rom ubs0segs))) a = mbyte ubs0segs mem1 a)
by (intros; reflexivity).
assert (MBL : forall b m i, In (b, m) Bfin -> 0 <= i < m ->
mbyte ubs0segs (ms_mem (mkst regs1 (Z_to_bv 64 TPC_CLEAN) mem1 (seg_rom ubs0segs))) (b + i) = mbyte ubs0segs mem1 (b + i))
by (intros; reflexivity).
clear HFS W40 W0 W8 W16 W24 W32.
Ltac free_step LAWS IMG API HS HJ Hid HB Htok Hgin MHI MBL HE2 HE8 Hspm G4 Htp0 Gatom k :=
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_free; [wr_ok_tac|];
let F10 := fresh "F10" in let F2 := fresh "F2" in let F4 := fresh "F4" in let F1 := fresh "F1" in
(jreg HS (10%bv:reg) as F10); (jreg HS (2%bv:reg) as F2); (jreg HS (4%bv:reg) as F4); (jreg HS (1%bv:reg) as F1);
eapply SR_bind;
[ eapply (jfree_tok _ _ LAWS ubs0_errno_low_lzw IMG (aa_free API) (aa_free_null API)) with (spc := _);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid
| eapply tfree_pre_case; [exact HB | exact Htok]
| rewrite F10, Gatom; reflexivity
| rewrite F2, <- (Z_to_bv_bv_unsigned 64 (ew _ 2)), HE2; reflexivity | lia | exact Hspm | lia | lia
| rewrite F4, (ew_Ereg_nat _ _ _ (4%bv:reg)) by reflexivity; rewrite G4; exact Htp0
| exact F1 | apply ret_ok_even; vm_compute; reflexivity ]
| ];
clear F10 F2 F4 F1;
let L2 := fresh "L" in let A2 := fresh "A" in let regs2 := fresh "regs" in let mem2 := fresh "mem" in let md2 := fresh "md" in
let HJ2 := fresh "HJ" in let Hid2 := fresh "Hid" in let HP2 := fresh "HP" in let Hres := fresh "Hres" in
let Hkeep := fresh "Hkeep" in let Hhi := fresh "Hhi" in
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & Hid2 & HP2 & Hres & Hkeep & Hhi);
clear HJ Hid; change (ms_segs ubs0_msyms) with ubs0segs in Hkeep, Hhi;
let HB2 := fresh "HB" in
pose proof (tfree_post_step _ _ _ _ _ _ HB Hres) as HB2;
let Htok2 := fresh "Htok" in
pose proof (tnz_tl _ _ _ Htok) as Htok2; cbv beta in Htok2;
let Hgin2 := fresh "Hgin" in
pose proof (tin_bfin _ _ _ _ HB2 ltac:(left; reflexivity)) as Hgin2;
clear HB Htok Hres Hgin; rename HB2 into HB; rename Htok2 into Htok; rename Hgin2 into Hgin;
let MHI2 := fresh "MHI" in let MBL2 := fresh "MBL" in
lazymatch type of MHI with forall a, _ -> ~ (?spv - LZW_STK <= a < _) -> _ = mbyte _ ?m1 a =>
lazymatch type of MBL with forall b m i, In (b, m) ?Bf -> _ =>
assert (MHI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spv - LZW_STK <= a < spv) -> mbyte ubs0segs mem2 a = mbyte ubs0segs m1 a)
by (intros a Ha Hna; rewrite (proj1 (Hhi a Ha ltac:(clear - Ha Hna; unfold LZW_STK, CALLOC_STACK, ALLOC_STACK in *; lia)));
lazymatch goal with HF : frame_of _ _ _ _ |- _ => rewrite (tmbyte_eq_of1 _ _ a (tframe_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _)) end;
exact (MHI a Ha Hna));
assert (MBL2 : forall b m i, In (b, m) Bf -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs m1 (b + i))
by (intros b m i Hb Hi; rewrite (Hkeep b m i (tin_bfin _ _ _ _ HB ltac:(right; exact Hb)) Hi);
lazymatch goal with HF : frame_of _ _ _ _ |- _ => rewrite (tmbyte_eq_of1 _ _ (b + i) (tframe_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _)) end;
exact (MBL b m i Hb Hi))
end end;
clear MHI MBL; rename MHI2 into MHI; rename MBL2 into MBL;
let HS2 := fresh "HS" in
jafter_call HS k regs2 mem2 HP2 HS2;
let HK := fresh "HK" in
lazymatch type of HS2 with ?P -> _ => assert (HK : P);
[ constructor; [|constructor; [|constructor]];
[ eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havoc; exact HE2 | exact Hhi | lia | lia | lia | cbn; lia | cbn; lia]
| eapply (region_kept_block_ro ubs0segs _ _ _ 8 0 72 0 0 _ _ 72 _); [ew_havoc; rewrite HE8; apply unsigned_lit_small; lia | exact Hgin
| intros b' m' i' Hb' Hi'; exact (Hkeep b' m' i' Hb' Hi')
| lia | lia | cbn; lia ] ]
| specialize (HS2 HK); clear HK HS Hhi HP2 Hkeep; rename HS2 into HS ] end;
lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
try lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end;
rename HJ2 into HJ; rename Hid2 into Hid.
free_step LAWS IMG API HS HJ Hid HB Htok Hgin MHI MBL HE2 HE8 Hspm G4 Htp0 H45 51%nat.
free_step LAWS IMG API HS HJ Hid HB Htok Hgin MHI MBL HE2 HE8 Hspm G4 Htp0 H46 67%nat.
free_step LAWS IMG API HS HJ Hid HB Htok Hgin MHI MBL HE2 HE8 Hspm G4 Htp0 H47 83%nat.
free_step LAWS IMG API HS HJ Hid HB Htok Hgin MHI MBL HE2 HE8 Hspm G4 Htp0 H48 99%nat.
free_step LAWS IMG API HS HJ Hid HB Htok Hgin MHI MBL HE2 HE8 Hspm G4 Htp0 H49 115%nat.
free_step LAWS IMG API HS HJ Hid HB Htok Hgin MHI MBL HE2 HE8 Hspm G4 Htp0 H50 131%nat.
cbn [nz List.filter app] in HB.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_free; [wr_ok_tac|].
(jreg HS (10%bv:reg) as F10); (jreg HS (2%bv:reg) as F2); (jreg HS (4%bv:reg) as F4); (jreg HS (1%bv:reg) as F1).
eapply SR_bind.
{ eapply (jfree_tok _ _ LAWS ubs0_errno_low_lzw IMG (aa_free API) (aa_free_null API)) with (spc := _);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid
| right; split; [exact Hgin | exact Hgtok]
| rewrite F10, HE8; reflexivity
| rewrite F2, <- (Z_to_bv_bv_unsigned 64 (ew _ 2)), HE2; reflexivity | lia | exact Hspm | lia | lia
| rewrite F4, (ew_Ereg_nat _ _ _ (4%bv:reg)) by reflexivity; rewrite G4; exact Htp0
| exact F1 | apply ret_ok_even; vm_compute; reflexivity ]. }
clear F10 F2 F4 F1.
intros c' (Lg & Ag & regsg & memg & mdg & -> & HJ2 & Hid2 & HP2 & Hres & Hkeep & Hhi).
clear HJ Hid. change (ms_segs ubs0_msyms) with ubs0segs in Hkeep, Hhi.
assert (HB2 : Permutation (blocks Lg Ag) Bfin).
{ destruct Hres as [[Hz _] | [_ Hrm]]; [exfalso; lia|]. eapply perm_after_rm1; [exact HB | exact Hrm]. }
lazymatch type of MHI with forall a, _ -> _ -> _ = mbyte _ ?m1 a =>
assert (MHI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - LZW_STK <= a < sp) -> mbyte ubs0segs memg a = mbyte ubs0segs m1 a)
by (intros a Ha Hna; rewrite (proj1 (Hhi a Ha ltac:(clear - Ha Hna HASv HSTKv Hwlo Hwhi Hceil; lia)));
lazymatch goal with HF : frame_of _ _ _ _ |- _ => rewrite (tmbyte_eq_of1 _ _ a (tframe_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _)) end;
exact (MHI a Ha Hna));
assert (MBL2 : forall b m i, In (b, m) Bfin -> 0 <= i < m -> mbyte ubs0segs memg (b + i) = mbyte ubs0segs m1 (b + i))
by (intros b m i Hb Hi; rewrite (Hkeep b m i ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB2 | exact Hb]) Hi);
lazymatch goal with HF : frame_of _ _ _ _ |- _ => rewrite (tmbyte_eq_of1 _ _ (b + i) (tframe_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _)) end;
exact (MBL b m i Hb Hi))
end.
clear MHI MBL; rename MHI2 into MHI; rename MBL2 into MBL.
jafter_call_keep HS 147%nat regsg memg HP2 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P);
[ constructor; [|constructor];
eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havoc; exact HE2 | exact Hhi | lia | lia | lia | cbn; lia | cbn; lia]
| specialize (HS2 HK); clear HK HS Hhi HP2 Hkeep; rename HS2 into HS ] end.
lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end.
rename HJ2 into HJ. rename Hid2 into Hid.
jrun LAWS ubs0tbl_ok HS HJ; [wr_ok_tac|].
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold tclean_post.
Ltac regq HS HX' rr j :=
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q := fresh "Q" in
pose proof (st_ok_reg ubs0segs Ef ssf msf rr HS) as Q; eval_sr_get_in Q; cbn [sv_denot] in Q;
repeat (rewrite ew_havoc_old in Q; [|cbv; lia]); rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Q;
let n := eval cbv in (32 + j)%nat in
try rewrite (HX' n j eq_refl ltac:(lia)) in Q; cbn [nth saved_vals SAVED map fst] in Q;
cbn [ms_regs mkst]; rewrite Q; clear Q
end.
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?Lf ?Af _ ?mdf =>
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
exists Lf, Af, (ms_regs msf), (ms_mem msf), mdf end end.
split. { regq HS HX' (1%bv:reg) 0%nat. rewrite Hra0. reflexivity. }
split; [exact HJ|]. split; [exact Hid|].
split.
{ apply regs_preserved_intro_lzw.
- regq HS HX' (2%bv:reg) 0%nat. rewrite HE2.
replace (sp - 112 + 112) with sp by lia. subst sp. unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
- regq HS HX' (3%bv:reg) 0%nat. rewrite (HE 3%nat 3%bv eq_refl). exact G3.
- regq HS HX' (4%bv:reg) 0%nat. rewrite (HE 4%nat 4%bv eq_refl). exact G4.
- regq HS HX' (8%bv:reg) 1%nat. reflexivity.
- regq HS HX' (9%bv:reg) 2%nat. reflexivity.
- regq HS HX' (18%bv:reg) 3%nat. reflexivity.
- regq HS HX' (19%bv:reg) 4%nat. reflexivity.
- regq HS HX' (20%bv:reg) 5%nat. reflexivity.
- regq HS HX' (21%bv:reg) 6%nat. reflexivity.
- regq HS HX' (22%bv:reg) 7%nat. reflexivity.
- regq HS HX' (23%bv:reg) 8%nat. reflexivity.
- regq HS HX' (24%bv:reg) 9%nat. reflexivity.
- regq HS HX' (25%bv:reg) 10%nat. reflexivity.
- regq HS HX' (26%bv:reg) 11%nat. reflexivity.
- regq HS HX' (27%bv:reg) 12%nat. reflexivity. }
split. { regq HS HX' (10%bv:reg) 0%nat. rewrite (HE 9%nat 9%bv eq_refl). exact G9. }
split.
{ intros a Ha Hna. cbn [ms_mem mkst].
lazymatch goal with HF : frame_of _ _ _ _ |- _ => rewrite (tmbyte_eq_of1 _ _ a (tframe_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _)) end.
exact (MHI a Ha Hna). }
split.
{ intros b m i Hb Hi. cbn [ms_mem mkst].
lazymatch goal with HF : frame_of _ _ _ _ |- _ => rewrite (tmbyte_eq_of1 _ _ (b + i) (tframe_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _)) end.
exact (MBL b m i Hb Hi). }
exact HB2.
Qed.
Definition ss_teidx : sstate := mkSS TPC_EIDX (ss_regs ss_tclean) (ss_mem ss_tclean) None (ss_facts ss_tclean).
Definition ss_teidx_c : sstate := Eval vm_compute in ss_teidx.
Lemma tlzw_eidx :
forall STK sp0 FP L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte)
(g : Z) (ld ti lm lc li tm : Z * Z) (Bfin : list (Z * Z)),
journal ubs0_msyms MR STK sp0 FP L A mem md L1 A1 mem1 md1 -> st_init_done A1 = true ->
Permutation (blocks L1 A1) (nz [ld; ti; lm; lc; li; tm] ++ (g, 72) :: Bfin) ->
(forall b, In b (nz [ld; ti; lm; lc; li; tm]) -> ftok FP (blocks L A) b) -> ftok FP (blocks L A) (g, 72) ->
gptrs mem1 g ld ti lm lc li tm -> (forall b, In b [ld; ti; lm; lc; li; tm] -> 0 <= fst b < 2 ^ 64) ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
spZ regs0 mod 16 = 0 -> sp0 - STK <= spZ regs0 - LZW_STK -> spZ regs0 <= sp0 ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 112) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 8 = Z_to_bv 64 g ->
frame_saved ubs0_msyms regs0 mem1 (spZ regs0) ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 TPC_EIDX) mem1 (seg_rom ubs0segs)) md1)
(tclean_post STK sp0 FP L A mem md regs0 mem1 Bfin 5).
Proof using IMG.
intros STK sp0 FP L A mem md L1 A1 md1 regs0 regs1 mem1 g ld ti lm lc li tm Bfin
HJ Hid HB Htok Hgtok HG Hrng Hra0 Htp0 Hal16 Hwlo Hwhi G2 G3 G4 G8 HFS.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : LZW_STK = 8400) by reflexivity.
pose proof HJ as (HH1 & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp := spZ regs0) in *.
assert (Hspm : (sp - 112) mod 16 = 0).
{ replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (Hgin : In (g, 72) (blocks L1 A1)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. left. reflexivity. }
destruct (heap_blocks_range _ _ LAWS _ _ _ _ g 72 HH1 Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
destruct ld as [pld nld], ti as [pti nti], lm as [plm nlm], lc as [plc nlc], li as [pli nli], tm as [ptm ntm].
pose proof HG as (W40 & W0 & W8 & W16 & W24 & W32). cbn [fst] in W40, W0, W8, W16, W24, W32.
pose proof (Hrng _ ltac:(left; reflexivity)) as R40. pose proof (Hrng _ ltac:(right; left; reflexivity)) as R0.
pose proof (Hrng _ ltac:(right; right; left; reflexivity)) as R8. pose proof (Hrng _ ltac:(right; right; right; left; reflexivity)) as R16.
pose proof (Hrng _ ltac:(right; right; right; right; left; reflexivity)) as R24. pose proof (Hrng _ ltac:(do 5 right; left; reflexivity)) as R32.
cbn [fst] in R40, R0, R8, R16, R24, R32.
set (extra := saved_vals regs0 ++ [Z_to_bv 64 pld; Z_to_bv 64 pti; Z_to_bv 64 plm; Z_to_bv 64 plc; Z_to_bv 64 pli; Z_to_bv 64 ptm]).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs1 extra) n = getr regs1 rr) by (intros; apply ew_Ereg_nat; assumption).
assert (Hlen13 : length (saved_vals regs0) = 13%nat) by reflexivity.
assert (HX : forall j, (j < 13)%nat -> ew (Ereg regs1 extra) (32 + j)%nat = nth j (saved_vals regs0) (Z_to_bv 64 0)).
{ intros j Hj. rewrite ew_Ereg_extra. subst extra. rewrite app_nth1 by (rewrite Hlen13; exact Hj). reflexivity. }
assert (HY : forall j, ew (Ereg regs1 extra) (32 + (13 + j))%nat = nth j [Z_to_bv 64 pld; Z_to_bv 64 pti; Z_to_bv 64 plm; Z_to_bv 64 plc; Z_to_bv 64 pli; Z_to_bv 64 ptm] (Z_to_bv 64 0)).
{ intros j. rewrite ew_Ereg_extra. subst extra. rewrite <- Hlen13. apply app_nth2_plus. }
pose proof (HY 0%nat) as H45. pose proof (HY 1%nat) as H46. pose proof (HY 2%nat) as H47.
pose proof (HY 3%nat) as H48. pose proof (HY 4%nat) as H49. pose proof (HY 5%nat) as H50.
cbn [nth Nat.add] in H45, H46, H47, H48, H49, H50. clear HY.
assert (HE2 : bv_unsigned (ew (Ereg regs1 extra) 2) = sp - 112) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HE8 : ew (Ereg regs1 extra) 8 = Z_to_bv 64 g) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HS : st_ok ubs0segs (Ereg regs1 extra) ss_teidx_c (mkst regs1 (Z_to_bv 64 TPC_EIDX) mem1 (seg_rom ubs0segs))).
{ change ss_teidx_c with ss_teidx. unfold ss_teidx, ss_tclean. cbn [ss_regs ss_mem ss_resv ss_facts]. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply (tsaved_chunks_ok _ mem1 regs0 sp 32 HX HFS).
+ unfold region_ok, tclean_gregion. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE8, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
Ltac gck' H W R := eapply chunk_ok_val; [cbn [sv_denot]; rewrite H, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; first [exact W | rewrite Z.add_0_r; exact W]].
constructor; [gck' H45 W40 R40|]. constructor; [gck' H46 W0 R0|]. constructor; [gck' H47 W8 R8|].
constructor; [gck' H48 W16 R16|]. constructor; [gck' H49 W24 R24|]. constructor; [gck' H50 W32 R32|]. constructor.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, tclean_gregion. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE8, unsigned_lit_small by lia. repeat split. lia.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE2, HE8, unsigned_lit_small by lia.
change (2 ^ 4) with 16. repeat split; first [lia | exact Hspm | exact Hg16]. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 TPC_EIDX) mem1 (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ TPC_CLEAN; [wr_ok_tac|].
lazymatch goal with HF : frame_of _ _ _ _ |- _ =>
pose proof (tframe_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm; cbn [ms_mem] in Hm end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
Ltac greg' HS HE rr G :=
let Q := fresh "Q" in
(jreg HS rr as Q); rewrite Q; try rewrite (HE _ rr eq_refl); first [exact G | reflexivity | rewrite G; reflexivity].
eapply SR_mono.
{ eapply (tlzw_clean STK sp0 FP L A mem md L1 A1 md1 regs0 _ _ g (pld, nld) (pti, nti) (plm, nlm) (plc, nlc) (pli, nli) (ptm, ntm) Bfin 5).
- exact HJ.
- exact Hid.
- exact HB.
- exact Htok.
- exact Hgtok.
- destruct HG as (V1 & V2 & V3 & V4 & V5 & V6).
unfold gptrs; cbn [fst]; repeat split; intros k Hk; cbn [ms_mem]; unfold mbyte; rewrite Hm;
first [apply V1 | apply V2 | apply V3 | apply V4 | apply V5 | apply V6]; exact Hk.
- exact Hrng.
- exact Hra0.
- exact Htp0.
- exact Hal16.
- exact Hwlo.
- exact Hwhi.
- greg' HS HE (2%bv:reg) G2.
- greg' HS HE (3%bv:reg) G3.
- greg' HS HE (4%bv:reg) G4.
- greg' HS HE (8%bv:reg) G8.
- greg' HS HE (9%bv:reg) G2.
- lia.
- eapply (frame_saved_kept ubs0_msyms); [exact HFS|]. intros a Ha. apply tmbyte_eq_of1. apply Hm. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & Hid2 & HP & H10 & MHI & MBL & HB2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP|].
split; [exact H10|]. split.
{ intros a Ha Hna. rewrite (MHI a Ha Hna). cbn [ms_mem]. apply tmbyte_eq_of1. apply Hm. }
split; [|exact HB2].
intros b m i Hb Hi. rewrite (MBL b m i Hb Hi). cbn [ms_mem]. apply tmbyte_eq_of1. apply Hm.
Qed.
End S.
End e.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
