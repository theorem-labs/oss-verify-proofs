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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 YI0r UI1w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 UI5c YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis FWRITE : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Definition WDB_HEAD : Z := Eval vm_compute in (ubs0_A_cgif_raw_newgif + 0x21c).
Definition WDB_EXIT : Z := Eval vm_compute in (ubs0_A_cgif_raw_newgif + 0x238).
Definition WDB_CLOB : list reg := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31; 22; 23]%bv.
Definition ss_wdb : sstate :=
mkSS WDB_HEAD (sr_set (sr_set sr_atoms 23%bv (SLit 0)) 21%bv (SLit ubs0_A_cgif_writecb))
[ YP09.mkRegion (Some 20%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 32 lits_CGIF) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + WRITECB_STK) (2^63) 4);
(20%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 3);
(22%nat, mkAF 1 65536 0) ] [] []).
Lemma frame_of_win : forall E r rs m m' b (x : word),
frame_of E (r :: rs) m m' ->
forallb (fun r' => r_whi r' <=? r_wlo r') rs = true ->
base_val E (r_base r) = b ->
(bv_unsigned x < b + r_wlo r \/ b + r_whi r <= bv_unsigned x) -> m' x = m x.
Proof using.
intros E r rs m m' b x HF Hro Hb Hx. apply HF. intros (r' & [<-|Hin] & Ha); [lia|].
pose proof (proj1 (forallb_forall _ _) Hro r' Hin) as H. cbn beta in H. apply Z.leb_le in H. lia.
Qed.
Lemma wdb_kept_in : forall r : reg, reg_in r WDB_CLOB = false -> r = 0%bv \/ r = 21%bv \/
In r ([2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 26; 27]%bv : list reg).
Proof using.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | vm_compute in Hr; discriminate | right; right; cbv; tauto] |]).
destruct Hin.
Qed.
Lemma repeat_cons_app : forall (n : nat), (0 : Z) :: repeat 0 n = repeat 0 n ++ [0].
Proof using. induction n as [|n IH]; [reflexivity|]. cbn [repeat app]. rewrite <- IH. reflexivity. Qed.
Lemma wdb_loop : forall (k : nat) (n : Z) regs memc STK sp0 FP L A mem md Lc Ac mdc g gvals spc (f : Z) (S : list Z),
Z.of_nat k = n -> 1 <= n <= 65536 ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
obj_at ubs0segs memc g LAY_CGIF gvals ->
nth_error gvals CG_wfn = Some 0 -> nth_error gvals CG_file = Some f ->
In (g, CGIF_SIZE) (blocks Lc Ac) -> In (f, FILE_BLOCK) (blocks Lc Ac) ->
sink_at ubs0_msyms memc mdc f S -> Z.of_nat (length S) + n <= SINK_MAX ->
garr8 ubs0segs memc (spc + 21) [0] ->
(forall a, inFP (sink_fp f) a -> inFP FP a) ->
getr regs 2 = Z_to_bv 64 spc -> spc mod 16 = 0 -> sp0 - STK <= spc - WRITECB_STK -> spc + 22 <= sp0 -> sp0 <= 2 ^ 47 ->
getr regs 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr regs 20 = Z_to_bv 64 g -> getr regs 23 = Z_to_bv 64 0 ->
getr regs 21 = Z_to_bv 64 ubs0_A_cgif_writecb -> getr regs 22 = Z_to_bv 64 n ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 WDB_HEAD) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 WDB_EXIT) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' md' /\
(forall r, reg_in r WDB_CLOB = false -> getr regs' r = getr regs r) /\
getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 22 = Z_to_bv 64 0 /\
sink_at ubs0_msyms mem' md' f (S ++ repeat 0 k) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - WRITECB_STK <= x < spc) ->
mbyte ubs0segs mem' x = mbyte ubs0segs memc x /\ (writable_at ubs0segs memc x <-> writable_at ubs0segs mem' x)) /\
(forall a m i, In (a, m) (blocks Lc Ac) -> 0 <= i < m -> ~ inFP (sink_fp f) (a + i) ->
mbyte ubs0segs mem' (a + i) = mbyte ubs0segs memc (a + i))).
Proof using FWRITE IMG LAWS.
induction k as [|k IH]; intros n regs memc STK sp0 FP L A mem md Lc Ac mdc g gvals spc f S Hk Hn HJ Hobj Hwfn Hfile Hgin Hfin HSK Hroom HGd HFP
H2 Hal Hlo Hhi H47 H4 H20 H21 H22 H23; [lia|].
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HGS : CGIF_SIZE = 96) by reflexivity.
assert (HFBv : FILE_BLOCK = 1264) by reflexivity. assert (HWv : WRITECB_STK = 528) by reflexivity.
pose proof HJ as (HHc & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & H63' & Hstw) & _).
destruct (heap_blocks_range ubs0_msyms MR LAWS Lc Ac memc mdc g CGIF_SIZE HHc Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
destruct (heap_blocks_range ubs0_msyms MR LAWS Lc Ac memc mdc f FILE_BLOCK HHc Hfin ltac:(lia)) as (Hf0 & Hf1 & Hf16).
assert (HE2 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 2 = Z_to_bv 64 spc) by (rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity); exact H2).
assert (HE4 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 4 = Z_to_bv 64 (ms_tp ubs0_msyms)) by (rewrite (ew_Ereg_nat regs _ 4 4%bv) by (vm_compute; reflexivity); exact H4).
assert (HE20 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 20 = Z_to_bv 64 g) by (rewrite (ew_Ereg_nat regs _ 20 20%bv) by (vm_compute; reflexivity); exact H20).
assert (HE23 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 22 = Z_to_bv 64 n) by (rewrite (ew_Ereg_nat regs _ 22 22%bv) by (vm_compute; reflexivity); exact H23).
assert (HS : st_ok ubs0segs (Ereg regs (map (Z_to_bv 64) gvals ++ [])) ss_wdb (mkst regs (Z_to_bv 64 WDB_HEAD) memc (seg_rom ubs0segs))).
{ apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H21] | intros X; discriminate X | cbn [sv_denot]; exact H22].
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen ubs0segs _ memc 20 g); [ | lia | lia | exact Hobj | reflexivity | | apply (lits_CGIF_ok gvals Hwfn Hfile) | intros i Hi; lia].
* rewrite HE20. apply unsigned_lit_small. lia.
* intros j v Hj. apply Ereg_vals. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE20, HE23, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert (g mod 8 = 0) by (rewrite (Znumtheory.Zmod_div_mod 8 16 g); [rewrite Hg16; reflexivity | lia | lia | exists 2; reflexivity]).
repeat split; lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 WDB_HEAD) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_writecb.
{ wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hm10. jreg HS (11%bv:reg) as Hm11. jreg HS (12%bv:reg) as Hm12.
jreg HS (2%bv:reg) as Hm2. jreg HS (4%bv:reg) as Hm4. jreg HS (1%bv:reg) as Hm1.
rewrite HE20 in Hm10. rewrite HE2, unsigned_lit_small in Hm11 by lia. rewrite HE2 in Hm2. rewrite HE4 in Hm4.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = spc) by (unfold spZ; rewrite Hm2; apply unsigned_lit_small; lia) end.
cbn [ms_mem mkst] in HF, HJ.
assert (K1 : forall a, mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs memc a).
{ intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
assert (Hobjc : obj_at ubs0segs (ms_mem ms) g LAY_CGIF gvals).
{ eapply (obj_at_transport_range ubs0segs memc); [exact Hobj | exact (proj1 LAY_CGIF_ok) |]. intros i Hi. apply K1. }
assert (HSKc : sink_at ubs0_msyms (ms_mem ms) mdc f S).
{ apply (sink_at_frame ubs0_msyms memc (ms_mem ms) mdc f S); [|exact HSK]. intros a _. apply K1. }
assert (HGc : garr8 ubs0segs (ms_mem ms) (spc + 21) [0]).
{ eapply garr8_frame; [exact HGd|]. intros a _. apply K1. }
eapply SR_bind.
{ eapply (jwrite ubs0_msyms MR LAWS ubs0_A_cgif_writecb (ubs0_cgif_writecb API IMG FWRITE))
with (g := g) (gvals := gvals) (src := spc + 21) (n := 1) (f := f) (S := S) (bs := [0]);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hm1 | apply ret_ok_even; vm_compute; reflexivity
| exact Hm10 | exact Hm11 | exact Hm12 | rewrite Hsp; exact Hal | rewrite Hsp; exact Hlo | rewrite Hsp; lia | rewrite Hsp; lia
| exact Hm4 | exact Hobjc | exact Hwfn | exact Hfile | exact Hgin | exact Hfin | exact HSKc | exact HGc | reflexivity
| lia | lia | lia | rewrite Hsp; lia | lia | lia | exact HFP ]. }
cbv beta. intros c' (regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hr10 & HSK2 & Hhi2 & Hblk2). rewrite Hsp in Hhi2. clear HJ.
jafter_call_keep HS 49%nat regs2 mem2 HP2 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor].
eapply (region_kept_pointwise ubs0segs _ _ _ 20 _ _ _ _ _ g); [exact (eq_trans (f_equal bv_unsigned HE20) (unsigned_lit_small g ltac:(lia))) | | cbn; lia].
intros a Ha. cbn [r_lo r_hi] in Ha. replace a with (g + (a - g)) by lia. apply (Hblk2 g CGIF_SIZE (a - g) Hgin); [lia|].
replace (g + (a - g)) with a by lia.
intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; [lia|].
pose proof (heap_sep_in2 ubs0_msyms MR LAWS Lc Ac memc mdc (g, CGIF_SIZE) (f, FILE_BLOCK) HHc Hgin Hfin) as Hd.
cbn [fst snd] in Hd. destruct Hd as [Hd|Hd]; [intros E; injection E as E1 E2; lia | lia | lia]. }
clear HS. rename HS2 into HS.
pin_reg' HS (10%bv:reg) 0 Hr10.
jrun LAWS ubs0tbl_ok HS HJ2.
{ wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jbranch ubs0tbl HS.
- idtac.
assert (HE23c : ew (havoc (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 49 (map (getr regs2) CLOB)) 22 = Z_to_bv 64 n) by (ew_havoc; exact HE23).
rewrite branch_ne_U, (U_atom_off _ 22 n (-1)), U_lit in Hc by (first [exact HE23c | lia]).
assert (Hn2 : 2 <= n) by (destruct (Z.eqb_spec (n + -1) 0); [discriminate | lia]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ2 WDB_HEAD.
{ wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 26; 27]%bv HS
(env_agree_havoc_ge 32 49 _ _ _ ltac:(lia) (env_agree_refl _ _)) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (22%bv:reg) as Hn23.
rewrite HE23 in Hn23.
jreg HS (23%bv:reg) as Hn21. jreg HS (21%bv:reg) as Hn22. jreg HS (20%bv:reg) as Hn20. rewrite HE20 in Hn20.
jreg HS (2%bv:reg) as Hn2'. rewrite HE2 in Hn2'.
jreg HS (4%bv:reg) as Hn4. rewrite HE4 in Hn4.
cbn [ms_mem mkst] in HF0, HF1.
assert (K2 : forall a, mbyte ubs0segs (ms_mem ms1) a = mbyte ubs0segs mem2 a).
{ intros a. unfold mbyte.
lazymatch type of HF1 with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF1) end.
lazymatch type of HF0 with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF0) end. reflexivity. }
assert (Hgkeep : forall i, 0 <= i < CGIF_SIZE -> mbyte ubs0segs mem2 (g + i) = mbyte ubs0segs (ms_mem ms) (g + i)).
{ intros i Hi. apply (Hblk2 g CGIF_SIZE i Hgin Hi).
intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; [lia|].
pose proof (heap_sep_in2 ubs0_msyms MR LAWS Lc Ac memc mdc (g, CGIF_SIZE) (f, FILE_BLOCK) HHc Hgin Hfin) as Hd.
cbn [fst snd] in Hd. destruct Hd as [Hd|Hd]; [intros E; injection E as E1 E2; lia | lia | lia]. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (n - 1) _ _ STK sp0 FP L A mem md Lc Ac md2 g gvals spc f (S ++ [0]));
[ lia | lia | exact HJ2 | | exact Hwfn | exact Hfile | exact Hgin | exact Hfin | | | | exact HFP
| exact Hn2' | exact Hal | exact Hlo | exact Hhi | exact H47 | exact Hn4 | exact Hn20 | exact Hn21 | exact Hn22
| rewrite Hn23, unsigned_lit_small by lia; f_equal; lia ].
- eapply (obj_at_transport_range ubs0segs (ms_mem ms)); [exact Hobjc | exact (proj1 LAY_CGIF_ok) |].
intros i Hi. rewrite K2. apply Hgkeep. exact Hi.
- apply (sink_at_frame ubs0_msyms mem2 _ md2 f _); [|exact HSK2]. intros a _. apply K2.
- rewrite length_app. cbn [length]. lia.
- eapply garr8_frame; [exact HGc|]. intros a Ha. cbn [length Z.of_nat] in Ha. rewrite K2.
apply (proj1 (Hhi2 a ltac:(lia) ltac:(lia))). }
cbv beta. intros c' (regs3 & mem3 & md3 & -> & HJ3 & HK3 & H21' & H23' & HSK3 & Hhi3 & Hblk3).
exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split; [|split; [exact H21'|split; [exact H23'|split; [|split]]]].
+ intros r Hr. rewrite (HK3 r Hr). destruct (wdb_kept_in r Hr) as [->|[->|Hin]]; [rewrite !getr_zero; reflexivity | rewrite Hn22, H22; reflexivity | apply HK; exact Hin].
+ replace (S ++ repeat 0 (Datatypes.S k)) with ((S ++ [0]) ++ repeat 0 k); [exact HSK3|].
rewrite <- app_assoc. reflexivity.
+ intros x Hx Hns. destruct (Hhi3 x Hx Hns) as [E1 E2]. destruct (Hhi2 x Hx Hns) as [F1 F2].
assert (R1 : forall w : word, ms_mem ms w = memc w).
{ intros w. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF w) end. }
assert (R2 : forall w : word, ms_mem ms1 w = mem2 w).
{ intros w.
lazymatch type of HF1 with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF1 w) end.
lazymatch type of HF0 with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF0 w) end. }
change (ms_segs ubs0_msyms) with ubs0segs in *.
split.
* rewrite E1. transitivity (mbyte ubs0segs mem2 x); [exact (mbyte_eq_of ubs0_msyms mem2 (ms_mem ms1) x (R2 _))|].
rewrite F1. exact (mbyte_eq_of ubs0_msyms memc (ms_mem ms) x (R1 _)).
* pose proof (writable_iff_of ubs0_msyms memc (ms_mem ms) x (R1 _)) as W1.
pose proof (writable_iff_of ubs0_msyms mem2 (ms_mem ms1) x (R2 _)) as W2.
change (ms_segs ubs0_msyms) with ubs0segs in W1, W2. tauto.
+ intros a m i Hin Hi Hnf. rewrite (Hblk3 a m i Hin Hi Hnf).
assert (R1 : forall w : word, ms_mem ms w = memc w).
{ intros w. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF w) end. }
transitivity (mbyte ubs0segs mem2 (a + i)); [apply K2|]. change (ms_segs ubs0_msyms) with ubs0segs in Hblk2. rewrite (Hblk2 a m i Hin Hi Hnf). apply K1.
-
assert (HE23c : ew (havoc (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 49 (map (getr regs2) CLOB)) 22 = Z_to_bv 64 n) by (ew_havoc; exact HE23).
rewrite branch_ne_U, (U_atom_off _ 22 n (-1)), U_lit in Hc by (first [exact HE23c | lia]).
assert (Hn1 : n = 1) by (destruct (Z.eqb_spec (n + -1) 0); [lia | discriminate]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ2 WDB_EXIT.
{ wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 26; 27]%bv HS
(env_agree_havoc_ge 32 49 _ _ _ ltac:(lia) (env_agree_refl _ _)) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (22%bv:reg) as Hn23. rewrite HE23, unsigned_lit_small in Hn23 by lia.
jreg HS (23%bv:reg) as Hn21. jreg HS (21%bv:reg) as Hn22.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
cbn [ms_mem mkst] in HF0, HF1.
assert (R1 : forall w : word, ms_mem ms w = memc w).
{ intros w. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF w) end. }
assert (R2 : forall w : word, ms_mem ms1 w = mem2 w).
{ intros w.
lazymatch type of HF1 with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF1 w) end.
lazymatch type of HF0 with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF0 w) end. }
assert (K2 : forall a, mbyte ubs0segs (ms_mem ms1) a = mbyte ubs0segs mem2 a) by (intros a; exact (mbyte_eq_of ubs0_msyms mem2 (ms_mem ms1) a (R2 _))).
change (ms_segs ubs0_msyms) with ubs0segs in *.
apply SR_ret. eexists _, _, _. split; [reflexivity|]. split; [exact HJ2|].
split; [|split; [exact Hn21 | split; [rewrite Hn23; f_equal; lia | split; [|split]]]].
+ intros r Hr. destruct (wdb_kept_in r Hr) as [->|[->|Hin]]; [rewrite !getr_zero; reflexivity | rewrite Hn22, H22; reflexivity | apply HK; exact Hin].
+ assert (k = 0%nat) by lia. subst k. cbn [repeat].
apply (sink_at_frame ubs0_msyms mem2 _ md2 f _); [|exact HSK2]. intros a _. apply K2.
+ intros x Hx Hns. destruct (Hhi2 x Hx Hns) as [F1 F2]. split.
* rewrite K2, F1. exact (mbyte_eq_of ubs0_msyms memc (ms_mem ms) x (R1 _)).
* pose proof (writable_iff_of ubs0_msyms memc (ms_mem ms) x (R1 _)) as W1.
pose proof (writable_iff_of ubs0_msyms mem2 (ms_mem ms1) x (R2 _)) as W2.
change (ms_segs ubs0_msyms) with ubs0segs in W1, W2. tauto.
+ intros a m i Hin Hi Hnf. rewrite K2, (Hblk2 a m i Hin Hi Hnf). apply K1.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
