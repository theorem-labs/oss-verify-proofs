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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ubs0_errno_low' : errno_addr ubs0_msyms + 4 <= alloc_ceiling.
Proof using.   pose proof (proj1 alloc_ceiling_val). enough (errno_addr ubs0_msyms + 4 <= CEIL_MIN) by lia. vm_compute. intros H'. discriminate H'. Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Definition CBB_LOOP_CLOB : list reg := [10; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 1; 19]%bv.
Definition CBB_LOOP_KEPT : list reg := [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 26; 27; 29; 30; 31]%bv.
Lemma cbb_kept_in : forall r : reg, reg_in r CBB_LOOP_CLOB = false -> r = 0%bv \/ r = 25%bv \/ In r CBB_LOOP_KEPT.
Proof using.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | vm_compute in Hr; discriminate | right; right; cbv; tauto] |]).
destruct Hin.
Qed.
Definition NOTB : afact := mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0.
Definition NOTB1 : afact := mkAF (2 ^ 64 - 2 - CEIL_MAX) (2 ^ 64 - 2 - 4096) 0.
Definition ss_cbb_loop : sstate :=
mkSS (ubs0_A_create_byte_list_block + 0x74) (sr_set sr_atoms 25%bv (SLit 18446744073709551615))
[ YP09.mkRegion (Some 32%nat) 0 1 0 1 [] ]
None
(mkFacts [ (8%nat, mkAF 4096 CEIL_MAX 4); (9%nat, mkAF 4096 CEIL_MAX 4); (19%nat, mkAF 0 (2^21) 0); (23%nat, mkAF 0 (2^21) 0);
(20%nat, NOTB); (22%nat, NOTB); (24%nat, NOTB1); (21%nat, mkAF 4097 (CEIL_MAX + 1) 0);
(32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 4096 CEIL_MAX 0) ]
[]
[ (SAlu ALU_ADD (SOff 8%nat 0) (SMd M_MUL (SOff 19%nat 0) (SLit 256)), SOff 32%nat 0);
(SAlu ALU_ADD (SOff 21%nat 0) (SMd M_MUL (SOff 19%nat 0) (SLit 256)), SOff 32%nat 1);
(SAlu ALU_ADD (SOff 9%nat 0) (SMd M_MUL (SOff 19%nat 0) (SLit 255)), SOff 33%nat 0) ]).
Lemma cbb_loop : forall (k : nat) (i : Z) regs memc STK sp0 FP L A mem md bb Lbb bl Lbl q,
Z.of_nat k = q - i -> 0 <= i < q ->
journal ubs0_msyms MR STK sp0 FP L A mem md L A memc md ->
In (bb, Lbb) (blocks L A) -> In (bl, Lbl) (blocks L A) -> (bb + Lbb <= bl \/ bl + Lbl <= bb) ->
256 * q + 1 <= Lbb -> 255 * q <= Lbl -> q < 2 ^ 21 ->
(forall a, bb <= a < bb + Lbb -> inFP FP a) ->
getr regs 19 = Z_to_bv 64 i -> getr regs 23 = Z_to_bv 64 q ->
getr regs 8 = Z_to_bv 64 bb -> getr regs 9 = Z_to_bv 64 bl ->
getr regs 20 = Z_to_bv 64 (2 ^ 64 - 1 - bb) -> getr regs 21 = Z_to_bv 64 (bb + 1) ->
getr regs 22 = Z_to_bv 64 (2 ^ 64 - 1 - bl) -> getr regs 24 = Z_to_bv 64 (2 ^ 64 - 2 - bb) ->
getr regs 25 = Z_to_bv 64 18446744073709551615 ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 (ubs0_A_create_byte_list_block + 0x74)) memc (seg_rom ubs0segs)) md)
(fun c' => exists regs' mem',
c' = mkCfg (mkst regs' (Z_to_bv 64 (ubs0_A_create_byte_list_block + 0xb4)) mem' (seg_rom ubs0segs)) md /\
journal ubs0_msyms MR STK sp0 FP L A mem md L A mem' md /\
(forall r, reg_in r CBB_LOOP_CLOB = false -> getr regs' r = getr regs r) /\
(forall x : word, bv_unsigned x < bb \/ bb + 256 * q <= bv_unsigned x -> mem' x = memc x) /\
mem_grows memc mem').
Proof using IMG LAWS.
induction k as [|k IH]; intros i regs memc STK sp0 FP L A mem md bb Lbb bl Lbl q Hk Hi HJ Hbb Hbl Hdisj HLbb HLbl Hq HFP
H19 H23 H8 H9 H20 H21 H22 H24 H25; [lia|].
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HH.
destruct (heap_blocks_range _ _ LAWS _ _ _ _ bb Lbb HH Hbb ltac:(lia)) as (Bb0 & Bb1 & Bb16).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ bl Lbl HH Hbl ltac:(lia)) as (Bl0 & Bl1 & Bl16).
assert (HE8 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i); Z_to_bv 64 (bl + 255 * i)]) 8 = Z_to_bv 64 bb) by (rewrite (ew_Ereg_nat regs _ 8 8%bv) by (vm_compute; reflexivity); exact H8).
assert (HE9 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i); Z_to_bv 64 (bl + 255 * i)]) 9 = Z_to_bv 64 bl) by (rewrite (ew_Ereg_nat regs _ 9 9%bv) by (vm_compute; reflexivity); exact H9).
assert (HE19 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i); Z_to_bv 64 (bl + 255 * i)]) 19 = Z_to_bv 64 i) by (rewrite (ew_Ereg_nat regs _ 19 19%bv) by (vm_compute; reflexivity); exact H19).
assert (HE20 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i); Z_to_bv 64 (bl + 255 * i)]) 20 = Z_to_bv 64 (2 ^ 64 - 1 - bb)) by (rewrite (ew_Ereg_nat regs _ 20 20%bv) by (vm_compute; reflexivity); exact H20).
assert (HE21 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i); Z_to_bv 64 (bl + 255 * i)]) 21 = Z_to_bv 64 (bb + 1)) by (rewrite (ew_Ereg_nat regs _ 21 21%bv) by (vm_compute; reflexivity); exact H21).
assert (HE22 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i); Z_to_bv 64 (bl + 255 * i)]) 22 = Z_to_bv 64 (2 ^ 64 - 1 - bl)) by (rewrite (ew_Ereg_nat regs _ 22 22%bv) by (vm_compute; reflexivity); exact H22).
assert (HE23 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i); Z_to_bv 64 (bl + 255 * i)]) 23 = Z_to_bv 64 q) by (rewrite (ew_Ereg_nat regs _ 23 23%bv) by (vm_compute; reflexivity); exact H23).
assert (HE24 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i); Z_to_bv 64 (bl + 255 * i)]) 24 = Z_to_bv 64 (2 ^ 64 - 2 - bb)) by (rewrite (ew_Ereg_nat regs _ 24 24%bv) by (vm_compute; reflexivity); exact H24).
assert (HE32 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i); Z_to_bv 64 (bl + 255 * i)]) 32 = Z_to_bv 64 (bb + 256 * i))
by (rewrite (ew_Ereg_extra regs _ 0); reflexivity).
assert (HE33 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i); Z_to_bv 64 (bl + 255 * i)]) 33 = Z_to_bv 64 (bl + 255 * i))
by (rewrite (ew_Ereg_extra regs _ 1); reflexivity).
assert (HS : st_ok ubs0segs (Ereg regs [Z_to_bv 64 (bb + 256 * i); Z_to_bv 64 (bl + 255 * i)]) ss_cbb_loop
(mkst regs (Z_to_bv 64 (ubs0_A_create_byte_list_block + 0x74)) memc (seg_rom ubs0segs))).
{ apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H25].
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (present_writable ubs0_msyms). replace (bb + 256 * i + o) with (bb + (256 * i + o)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bb Lbb (256 * i + o) HH Hbb ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok, NOTB, NOTB1. cbn [af_lo af_hi af_al2].
rewrite HE8, HE9, HE19, HE23, HE20, HE22, HE24, HE21, HE32, HE33, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; first [exact Bb16 | exact Bl16 | lia].
+ cbn [f_alias alias_ok]. split; [|split; [|split; [|exact I]]].
* apply U_inj. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom _ 8 bb HE8), (U_atom _ 19 i HE19), (U_atom _ 32 _ HE32), U_SLit by lia.
change (zcanon 256) with 256. rewrite (zcanon_id (i * 256)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
* apply U_inj. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom _ 21 (bb + 1) HE21), (U_atom _ 19 i HE19), (U_atom_off _ 32 _ 1 HE32), U_SLit by lia.
change (zcanon 256) with 256. rewrite (zcanon_id (i * 256)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
* apply U_inj. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom _ 9 bl HE9), (U_atom _ 19 i HE19), (U_atom _ 33 _ HE33), U_SLit by lia.
change (zcanon 255) with 255. rewrite (zcanon_id (i * 255)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 (ubs0_A_create_byte_list_block + 0x74)) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_memcpy.
{ wr_ok_tac. eapply (wr_ok_cons_inblock _ _ _ _ _ _ _ _ 32 (bb + 256 * i) bb Lbb);
[reflexivity | rewrite HE32; apply unsigned_lit_small; lia | exact Hbb | cbn; lia | cbn; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. apply HFP. lia. }
jreg HS (10%bv:reg) as Ha0. jreg HS (11%bv:reg) as Ha1. jreg HS (12%bv:reg) as Ha2. jreg HS (1%bv:reg) as Hra.
rewrite HE32, unsigned_lit_small in Ha0 by lia. rewrite HE33 in Ha1.
eapply SR_bind.
{ eapply (jmemcpy _ _ LAWS IMG _ ubs0_memcpy) with (d := bb + 256 * i + 1) (src := bl + 255 * i) (n := 255);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Ha0 | exact Ha1 | exact Ha2 | exact Hra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | lia | ].
- intros j Hj. replace (bb + 256 * i + 1 + j) with (bb + (256 * i + 1 + j)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bb Lbb (256 * i + 1 + j) (proj1 HJ) Hbb ltac:(lia))).
- intros j Hj. replace (bl + 255 * i + j) with (bl + (255 * i + j)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bl Lbl (255 * i + j) (proj1 HJ) Hbl ltac:(lia))).
- intros a Ha. right. left. split; [apply HFP; lia|]. exists bb, Lbb. split; [exact Hbb | lia]. }
intros c' (regs2 & mem2 & -> & HJ2 & Hr10 & Hfr2 & Hout2 & Hgr2 & _).
pose proof (st_ok_after_stretch ubs0segs 34 _ _ _ regs2 mem2 [] (ubs0_A_create_byte_list_block + 0xac)
(10%bv :: MEMCPY_CLOB) HS eq_refl ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl
(submem_nil _) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HP : P); [|assert (HQ : Q); [constructor | specialize (HS2 HP HQ); clear HP HQ]] end.
{ intros r Hr. apply Hfr2. cbn [reg_in] in Hr |- *. destruct (bv_eqb r 10); [discriminate | exact Hr]. }
lazymatch type of HS2 with st_ok _ _ ?ss2 _ => let ss3 := eval vm_compute in ss2 in change ss2 with ss3 in HS2 end.
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (ubs0_A_create_byte_list_block + 0xac)) mem2 (seg_rom ubs0segs))) in HJ2.
jrun LAWS ubs0tbl_ok HS HJ2.
{ wr_ok_tac. }
jbranch ubs0tbl HS.
-
rewrite branch_ne_U in Hc. rewrite (U_atom _ 23 q) in Hc; [| ew_havoc; exact HE23 | lia].
rewrite (U_atom_off _ 19 i 1) in Hc; [| ew_havoc; exact HE19 | lia | lia].
assert (Hlt : i + 1 < q) by (destruct (Z.eqb_spec (i + 1) q); [discriminate | lia]).
jrun_to LAWS ubs0tbl_ok HS HJ2 (ubs0_A_create_byte_list_block + 0x74).
{ wr_ok_tac. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ CBB_LOOP_KEPT HS
(env_agree_havoc_ge 32 34 _ _ _ ltac:(lia) (env_agree_refl _ _)) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (19%bv:reg) as Hn19. jreg HS (25%bv:reg) as Hn25.
rewrite HE19, unsigned_lit_small in Hn19 by lia.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 1) _ _ STK sp0 FP L A mem md bb Lbb bl Lbl q); [lia | lia | exact HJ2 | exact Hbb | exact Hbl | exact Hdisj | exact HLbb | exact HLbl | exact Hq | exact HFP
| rewrite Hn19; f_equal; lia
| rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23 | rewrite (HK 8%bv ltac:(cbv; tauto)); exact H8
| rewrite (HK 9%bv ltac:(cbv; tauto)); exact H9 | rewrite (HK 20%bv ltac:(cbv; tauto)); exact H20
| rewrite (HK 21%bv ltac:(cbv; tauto)); exact H21 | rewrite (HK 22%bv ltac:(cbv; tauto)); exact H22
| rewrite (HK 24%bv ltac:(cbv; tauto)); exact H24 | exact Hn25 ]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & HK3 & Hout3 & Hgr3).
exists regs3, mem3. split; [reflexivity|]. split; [exact HJ3|]. split; [|split].
+ intros r Hr. rewrite (HK3 r Hr). destruct (cbb_kept_in r Hr) as [->|[->|Hin]]; [rewrite !getr_zero; reflexivity| |].
* rewrite Hn25, H25. reflexivity.
* rewrite (HK r Hin). reflexivity.
+ intros x Hx. rewrite (Hout3 x Hx).
lazymatch goal with |- ms_mem ?msb x = _ =>
lazymatch goal with HFa : frame_of _ [] (ms_mem ?msa) (ms_mem msb) |- _ =>
rewrite (frame_of_nil _ _ _ x HFa);
lazymatch goal with HFb : frame_of _ [] ?m2 (ms_mem msa) |- _ =>
rewrite (frame_of_nil _ _ _ x HFb); cbn [ms_mem mkst] end end end.
rewrite (Hout2 x) by lia.
lazymatch goal with HF1 : frame_of _ [_] _ _ |- _ =>
rewrite (frame_of_one _ _ _ _ (bb + 256 * i) (bb + 256 * i + 1) x HF1);
[reflexivity | | | lia];
cbn [base_val r_base r_wlo r_whi]; rewrite HE32, unsigned_lit_small by lia; lia end.
+ eapply mem_grows_trans; [|exact Hgr3].
lazymatch goal with |- mem_grows _ (ms_mem ?msb) =>
lazymatch goal with HGa : mem_grows (ms_mem ?msa) (ms_mem msb) |- _ =>
eapply mem_grows_trans; [|exact HGa];
lazymatch goal with HGb : mem_grows ?m2 (ms_mem msa) |- _ =>
eapply mem_grows_trans; [|exact HGb]; cbn [ms_mem mkst] end end end.
eapply mem_grows_trans; [|exact Hgr2].
lazymatch goal with HG1 : mem_grows (ms_mem (mkst regs _ memc _)) _ |- _ => exact HG1 end.
-
rewrite branch_ne_U in Hc. rewrite (U_atom _ 23 q) in Hc; [| ew_havoc; exact HE23 | lia].
rewrite (U_atom_off _ 19 i 1) in Hc; [| ew_havoc; exact HE19 | lia | lia].
assert (Heq : i + 1 = q) by (destruct (Z.eqb_spec (i + 1) q); [lia | discriminate]).
jrun_to LAWS ubs0tbl_ok HS HJ2 (ubs0_A_create_byte_list_block + 0xb4).
{ wr_ok_tac. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ CBB_LOOP_KEPT HS
(env_agree_havoc_ge 32 34 _ _ _ ltac:(lia) (env_agree_refl _ _)) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (25%bv:reg) as Hn25.
apply SR_ret. rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- context [mkst (ms_regs ?msx) _ (ms_mem _) _] => exists (ms_regs msx), (ms_mem msx) end.
split; [reflexivity|]. split; [exact HJ2|]. split; [|split].
+ intros r Hr. destruct (cbb_kept_in r Hr) as [->|[->|Hin]]; [rewrite !getr_zero; reflexivity| |].
* rewrite Hn25, H25. reflexivity.
* apply (HK r Hin).
+ intros x Hx.
lazymatch goal with |- ms_mem ?msb x = _ =>
lazymatch goal with HFa : frame_of _ [] (ms_mem ?msa) (ms_mem msb) |- _ =>
rewrite (frame_of_nil _ _ _ x HFa);
lazymatch goal with HFb : frame_of _ [] ?m2 (ms_mem msa) |- _ =>
rewrite (frame_of_nil _ _ _ x HFb); cbn [ms_mem mkst] end end end.
rewrite (Hout2 x) by lia.
lazymatch goal with HF1 : frame_of _ [_] _ _ |- _ =>
rewrite (frame_of_one _ _ _ _ (bb + 256 * i) (bb + 256 * i + 1) x HF1);
[reflexivity | | | lia];
cbn [base_val r_base r_wlo r_whi]; rewrite HE32, unsigned_lit_small by lia; lia end.
+ lazymatch goal with |- mem_grows _ (ms_mem ?msb) =>
lazymatch goal with HGa : mem_grows (ms_mem ?msa) (ms_mem msb) |- _ =>
eapply mem_grows_trans; [|exact HGa];
lazymatch goal with HGb : mem_grows ?m2 (ms_mem msa) |- _ =>
eapply mem_grows_trans; [|exact HGb]; cbn [ms_mem mkst] end end end.
eapply mem_grows_trans; [|exact Hgr2].
lazymatch goal with HG1 : mem_grows (ms_mem (mkst regs _ memc _)) _ |- _ => exact HG1 end.
Qed.
Definition cbb_facts_u (rzero : bool) : list (nat * afact) :=
cbb_facts rzero ++ [ (37%nat, NOTB); (38%nat, NOTB); (39%nat, NOTB1) ].
Definition cbb_aliases_u : list (sv * sv) :=
cbb_aliases ++
[ (SAlu ALU_XOR (SOff 11%nat 0) (SLit (-1)), SOff 37%nat 0);
(SAlu ALU_XOR (SOff 10%nat 0) (SLit (-1)), SOff 38%nat 0);
(SAlu ALU_XOR (SOff 11%nat 1) (SLit (-1)), SOff 39%nat 0) ].
Lemma alias_ok_app_u : forall E l1 l2, alias_ok E l1 -> alias_ok E l2 -> alias_ok E (l1 ++ l2).
Proof using. intros E l1 l2 H1 H2. induction l1 as [|[a b] l1 IH]; [exact H2|]. destruct H1 as [Hf H1]. split; [exact Hf | apply IH; exact H1]. Qed.
Lemma alu64_xor_m1 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof using.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small x) by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite lxor_allones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma cbb_xor_aliases_ok : forall E bl bb,
ew E 10 = Z_to_bv 64 bl -> ew E 11 = Z_to_bv 64 bb -> 4096 <= bl <= alloc_ceiling -> 4096 <= bb <= alloc_ceiling ->
ew E 37 = Z_to_bv 64 (2 ^ 64 - 1 - bb) -> ew E 38 = Z_to_bv 64 (2 ^ 64 - 1 - bl) -> ew E 39 = Z_to_bv 64 (2 ^ 64 - 2 - bb) ->
alias_ok E [ (SAlu ALU_XOR (SOff 11%nat 0) (SLit (-1)), SOff 37%nat 0);
(SAlu ALU_XOR (SOff 10%nat 0) (SLit (-1)), SOff 38%nat 0);
(SAlu ALU_XOR (SOff 11%nat 1) (SLit (-1)), SOff 39%nat 0) ].
Proof using.
intros E bl bb E10 E11 Hbl Hbb E37 E38 E39. pose proof (proj1 alloc_ceiling_val) as Hac.
cbn [alias_ok sv_denot]. rewrite E10, E11, E37, E38, E39, !unsigned_lit_small by lia. rewrite !Z.add_0_r.
repeat split; rewrite alu64_xor_m1 by lia; f_equal; lia.
Qed.
Definition ss_cbb0 : sstate :=
mkSS ubs0_A_create_byte_list_block sr_atoms [ reg_stack96; reg_at 34 ] None (mkFacts (cbb_facts_u true) [] cbb_aliases_u).
Definition ss_cbb1 : sstate :=
mkSS ubs0_A_create_byte_list_block sr_atoms [ reg_stack96; reg_at 34; reg_at 36 ] None (mkFacts (cbb_facts_u false) [] cbb_aliases_u).
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Theorem ubs0_cbl_block : forall L A regs mem md bl Lbl bb Lbb n rest,
fn_pre ubs0_msyms MR CBB_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 bl -> getr regs 11 = Z_to_bv 64 bb -> getr regs 12 = Z_to_bv 64 n ->
0 <= n < 2 ^ 28 -> n <= Lbl -> 0 < Lbl -> cbb_len n <= Lbb ->
Permutation (blocks L A) ((bl, Lbl) :: (bb, Lbb) :: rest) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_create_byte_list_block) mem (seg_rom ubs0segs)) md)
(fun c' => exists regs' mem',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md /\
journal ubs0_msyms MR CBB_STK (spZ regs) [(bb, bb + Lbb)] L A mem md L A mem' md /\
regs_preserved regs regs' /\
getr regs' 10 = Z_to_bv 64 (cbb_len n - 1)).
Proof using IMG LAWS.
intros L A regs mem md bl Lbl bb Lbb n rest HPRE H10 H11 H12 Hn HLbl HLbl0 HLbb HB.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : CBB_STK = 96) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (Hblin : In (bl, Lbl) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hbbin : In (bb, Lbb) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
pose proof (Z.div_mod n 255 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound n 255 ltac:(lia)) as Hmb.
assert (Hcl : cbb_len n = 256 * (n / 255) + (if n mod 255 =? 0 then 1 else n mod 255 + 2)) by reflexivity.
rewrite Hcl in HLbb |- *. clear Hcl.
set (q := n / 255) in *. set (r := n mod 255) in *.
assert (Hqdef : q = n / 255) by reflexivity. assert (Hrdef : r = n mod 255) by reflexivity. clearbody q r.
assert (Hqr : 0 <= q < 2 ^ 21) by (rewrite Hqdef; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
clear Hqdef Hrdef.
assert (Hlen' : 256 * q + r + 1 <= Lbb) by (destruct (Z.eqb_spec r 0); lia).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md bl Lbl HH Hblin ltac:(lia)) as (Bl0 & Bl1 & Bl16).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md bb Lbb HH Hbbin ltac:(lia)) as (Bb0 & Bb1 & Bb16).
pose proof (heap_sep_perm ubs0_msyms MR LAWS L A mem md (bl, Lbl) _ (bb, Lbb) HH HB ltac:(left; reflexivity)) as Hsep.
cbn [fst snd] in Hsep.
remember (Ereg regs [Z_to_bv 64 q; Z_to_bv 64 r; Z_to_bv 64 (bb + 256 * q); Z_to_bv 64 (bl + 255 * q); Z_to_bv 64 (bb + 256 * q + r + 1);
Z_to_bv 64 (2 ^ 64 - 1 - bb); Z_to_bv 64 (2 ^ 64 - 1 - bl); Z_to_bv 64 (2 ^ 64 - 2 - bb)]) as E0 eqn:HE0.
assert (HA0 : env_agree 32 (Ereg regs [Z_to_bv 64 q; Z_to_bv 64 r; Z_to_bv 64 (bb + 256 * q); Z_to_bv 64 (bl + 255 * q); Z_to_bv 64 (bb + 256 * q + r + 1);
Z_to_bv 64 (2 ^ 64 - 1 - bb); Z_to_bv 64 (2 ^ 64 - 1 - bl); Z_to_bv 64 (2 ^ 64 - 2 - bb)]) E0)
by (rewrite HE0; apply env_agree_refl).
assert (HE2 : ew E0 2 = getr regs 2) by (subst E0; apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (HE1 : ew E0 1 = getr regs 1) by (subst E0; apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
assert (HE10 : ew E0 10 = Z_to_bv 64 bl) by (subst E0; rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity); exact H10).
assert (HE11 : ew E0 11 = Z_to_bv 64 bb) by (subst E0; rewrite (ew_Ereg_nat regs _ 11 11%bv) by (vm_compute; reflexivity); exact H11).
assert (HE12 : ew E0 12 = Z_to_bv 64 n) by (subst E0; rewrite (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity); exact H12).
assert (HE32 : ew E0 32 = Z_to_bv 64 q) by (subst E0; rewrite (ew_Ereg_extra regs _ 0); reflexivity).
assert (HE33 : ew E0 33 = Z_to_bv 64 r) by (subst E0; rewrite (ew_Ereg_extra regs _ 1); reflexivity).
assert (HE34 : ew E0 34 = Z_to_bv 64 (bb + 256 * q)) by (subst E0; rewrite (ew_Ereg_extra regs _ 2); reflexivity).
assert (HE35 : ew E0 35 = Z_to_bv 64 (bl + 255 * q)) by (subst E0; rewrite (ew_Ereg_extra regs _ 3); reflexivity).
assert (HE36 : ew E0 36 = Z_to_bv 64 (bb + 256 * q + r + 1)) by (subst E0; rewrite (ew_Ereg_extra regs _ 4); reflexivity).
assert (HE37 : ew E0 37 = Z_to_bv 64 (2 ^ 64 - 1 - bb)) by (subst E0; rewrite (ew_Ereg_extra regs _ 5); reflexivity).
assert (HE38 : ew E0 38 = Z_to_bv 64 (2 ^ 64 - 1 - bl)) by (subst E0; rewrite (ew_Ereg_extra regs _ 6); reflexivity).
assert (HE39 : ew E0 39 = Z_to_bv 64 (2 ^ 64 - 2 - bb)) by (subst E0; rewrite (ew_Ereg_extra regs _ 7); reflexivity).
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
assert (Hwr0 : forall E' cs1 cs2, ew E' 2 = getr regs 2 -> ew E' 34 = Z_to_bv 64 (bb + 256 * q) ->
wr_ok E' [YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 cs1; YP09.mkRegion (Some 34%nat) 0 1 0 1 cs2]
CBB_STK (spZ regs) [(bb, bb + Lbb)] (blocks L A) (blocks L A)).
{ intros E' cs1 cs2 HE2' HE34'.
eapply wr_ok_cons_stack; [reflexivity | rewrite HE2'; exact Hspw | cbn; lia | cbn; lia |].
eapply (wr_ok_cons_inblock _ _ _ _ _ _ _ _ 34 (bb + 256 * q) bb Lbb);
[reflexivity | rewrite HE34'; apply unsigned_lit_small; lia | exact Hbbin | cbn; lia | cbn; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. exists (bb, bb + Lbb). split; [left; reflexivity | cbn; lia]. }
assert (Hwr1 : r <> 0 -> forall E' cs1 cs2 cs3, ew E' 2 = getr regs 2 -> ew E' 34 = Z_to_bv 64 (bb + 256 * q) ->
ew E' 36 = Z_to_bv 64 (bb + 256 * q + r + 1) ->
wr_ok E' [YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 cs1; YP09.mkRegion (Some 34%nat) 0 1 0 1 cs2;
YP09.mkRegion (Some 36%nat) 0 1 0 1 cs3]
CBB_STK (spZ regs) [(bb, bb + Lbb)] (blocks L A) (blocks L A)).
{ intros Hr0 E' cs1 cs2 cs3 HE2' HE34' HE36'.
eapply wr_ok_cons_stack; [reflexivity | rewrite HE2'; exact Hspw | cbn; lia | cbn; lia |].
eapply (wr_ok_cons_inblock _ _ _ _ _ _ _ _ 34 (bb + 256 * q) bb Lbb);
[reflexivity | rewrite HE34'; apply unsigned_lit_small; lia | exact Hbbin | cbn; lia | cbn; lia | | ].
{ cbn [r_wlo r_whi]. intros a Ha. exists (bb, bb + Lbb). split; [left; reflexivity | cbn; lia]. }
assert (256 * q + r + 2 <= Lbb) by (destruct (Z.eqb_spec r 0); lia).
eapply (wr_ok_cons_inblock _ _ _ _ _ _ _ _ 36 (bb + 256 * q + r + 1) bb Lbb);
[reflexivity | rewrite HE36'; apply unsigned_lit_small; lia | exact Hbbin | cbn; lia | cbn; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. exists (bb, bb + Lbb). split; [left; reflexivity | cbn; lia]. }
set (ms0 := mkst regs (Z_to_bv 64 ubs0_A_create_byte_list_block) mem (seg_rom ubs0segs)).
pose proof (journal_init ubs0_msyms MR CBB_STK [(bb, bb + Lbb)] L A regs mem md HPRE) as HJ.
change mem with (ms_mem ms0) in HJ.
destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
-
assert (HS : st_ok ubs0segs E0 ss_cbb0 ms0).
{ rewrite HE0. apply entry_st_ok_full; rewrite <- ?HE0; unfold reg_stack96, reg_at.
- rewrite HE0. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite HE2. exact Hspw.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val reg_at]. rewrite HE34, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (present_writable ubs0_msyms).
replace (bb + 256 * q + o) with (bb + (256 * q + o)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bb Lbb (256 * q + o) HH Hbbin ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint reg_at reg_stack96]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE34, Hspw, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok cbb_facts_u cbb_facts app]. unfold afact_ok, NOTB, NOTB1. cbn [af_lo af_hi af_al2].
rewrite HE2, HE10, HE11, HE12, HE32, HE33, HE34, HE35, HE37, HE38, HE39, Hspw, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_alias cbb_aliases_u]. apply alias_ok_app_u; [eapply (cbb_aliases_ok E0 n q r bl bb); try eassumption; lia|].
apply (cbb_xor_aliases_ok E0 bl bb); assumption || lia. }
clear Hwr1 Hal16 Bl16 Bb16.
Local Ltac tail0 LAWS HS HJ Hwr0 HE2 HE34 HE33 HE32 HE1 HA0 Hra Hqr Hr0 :=
lazymatch type of Hr0 with ?r = 0 =>
jbranch ubs0tbl HS;
[ jrun LAWS ubs0tbl_ok HS HJ; [ wr_norm; apply Hwr0; ew_havoc; [exact HE2 | exact HE34] |];
let HPR := fresh "HPR" in
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS
ltac:(repeat (first [exact HA0 | eapply (env_agree_havoc_ge 32); [lia|]])) ltac:(vm_compute; reflexivity)) as HPR;
let Hr10 := fresh "Hr10" in let Hr1 := fresh "Hr1" in
jreg HS (10%bv:reg) as Hr10; jreg HS (1%bv:reg) as Hr1;
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |];
[ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))
| exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))))
| lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx) end;
rewrite Hr1, HE1, Hra; split; [reflexivity|]; split; [exact HJ|]; split; [exact HPR|];
rewrite Hr10, HE32, alu64_sll_lit by lia; f_equal; rewrite (proj2 (Z.eqb_eq r 0) Hr0); lia ]
| exfalso;
lazymatch goal with Hc : branch_taken _ _ _ = false |- _ =>
rewrite branch_eq_U, (U_atom _ 33 r), U_lit in Hc; [| lia | ew_havoc; exact HE33 | lia];
rewrite (proj2 (Z.eqb_eq r 0) Hr0) in Hc; discriminate Hc end ]
end.
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE34]. }
jbranch ubs0tbl HS.
+
rewrite branch_ltu_U, (U_atom _ 12 n), U_lit in Hc; [| lia | exact HE12 | lia].
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE34]. }
tail0 LAWS HS HJ Hwr0 HE2 HE34 HE33 HE32 HE1 HA0 Hra Hqr Hr0.
+
rewrite branch_ltu_U, (U_atom _ 12 n), U_lit in Hc; [| lia | exact HE12 | lia].
assert (Hq1 : 1 <= q) by (destruct (Z.ltb_spec n 255); [discriminate|]; lia).
jrun_to LAWS ubs0tbl_ok HS HJ (ubs0_A_create_byte_list_block + 0x74).
{ wr_norm. apply Hwr0; [exact HE2 | exact HE34]. }
jreg HS (19%bv:reg) as Hl19. jreg HS (23%bv:reg) as Hl23. jreg HS (8%bv:reg) as Hl8. jreg HS (9%bv:reg) as Hl9.
jreg HS (20%bv:reg) as Hl20. jreg HS (21%bv:reg) as Hl21. jreg HS (22%bv:reg) as Hl22. jreg HS (24%bv:reg) as Hl24. jreg HS (25%bv:reg) as Hl25.
rewrite ?HE32 in Hl23. rewrite ?HE11 in Hl8. rewrite ?HE10 in Hl9. rewrite ?HE37 in Hl20. rewrite ?HE11, ?unsigned_lit_small in Hl21 by lia.
rewrite ?HE38 in Hl22. rewrite ?HE39 in Hl24.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (cbb_loop API IMG (Z.to_nat q) 0 _ _ CBB_STK (spZ regs) [(bb, bb + Lbb)] L A mem md bb Lbb bl Lbl q);
[ lia | lia | exact HJ | exact Hbbin | exact Hblin | lia | lia | lia | lia
| intros a Ha; exists (bb, bb + Lbb); split; [left; reflexivity | cbn; lia]
| exact Hl19 | exact Hl23 | exact Hl8 | exact Hl9 | exact Hl20 | exact Hl21 | exact Hl22 | exact Hl24 | rewrite Hl25; vm_compute; reflexivity ]. }
intros c' (regsL & memL & -> & HJL & HKL & HoutL & HgrL).
jafter_stretch HS 40%nat regsL memL CBB_LOOP_CLOB (ubs0_A_create_byte_list_block + 0xb4) HS2.
match type of HS2 with ?P -> ?Q -> _ =>
assert (HQ : Q); [| specialize (HS2 HKL HQ); clear HQ] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_outside _ _ _ _ _ bb (256 * q) HoutL HgrL); cbn [r_base r_lo r_hi r_wlo r_whi base_val];
rewrite ?HE2, ?Hspw; lia.
- eapply (region_kept_outside _ _ _ _ _ bb (256 * q) HoutL HgrL); cbn [r_base r_lo r_hi r_wlo r_whi base_val];
rewrite ?HE34, ?unsigned_lit_small by lia; lia. }
clear HS HJ. rename HS2 into HS. rename HJL into HJ.
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_norm. apply Hwr0; ew_havoc; [exact HE2 | exact HE34]. }
tail0 LAWS HS HJ Hwr0 HE2 HE34 HE33 HE32 HE1 HA0 Hra Hqr Hr0.
-
specialize (Hwr1 Hr0). clear Hwr0.
assert (Hlen2 : 256 * q + r + 2 <= Lbb) by (destruct (Z.eqb_spec r 0); lia).
assert (HS : st_ok ubs0segs E0 ss_cbb1 ms0).
{ rewrite HE0. apply entry_st_ok_full; rewrite <- ?HE0; unfold reg_stack96, reg_at.
- rewrite HE0. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite HE2. exact Hspw.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val reg_at]. rewrite HE34, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (present_writable ubs0_msyms).
replace (bb + 256 * q + o) with (bb + (256 * q + o)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bb Lbb (256 * q + o) HH Hbbin ltac:(lia))).
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val reg_at]. rewrite HE36, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (present_writable ubs0_msyms).
replace (bb + 256 * q + r + 1 + o) with (bb + (256 * q + r + 1 + o)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bb Lbb (256 * q + r + 1 + o) HH Hbbin ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint reg_at reg_stack96]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE34, HE36, Hspw, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok cbb_facts_u cbb_facts app]. unfold afact_ok, NOTB, NOTB1. cbn [af_lo af_hi af_al2].
rewrite HE2, HE10, HE11, HE12, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, Hspw, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_alias cbb_aliases_u]. apply alias_ok_app_u; [eapply (cbb_aliases_ok E0 n q r bl bb); try eassumption; lia|].
apply (cbb_xor_aliases_ok E0 bl bb); assumption || lia. }
clear Hal16 Bl16 Bb16.
Local Ltac tail1 LAWS HS HJ Hwr1 HE2 Hspw HE34 HE36 HE35 HE33 HE32 HE1 HA0 Hra Hqr Hr0 Hbbin Hblin k :=
lazymatch type of HE35 with ew _ 35 = Z_to_bv 64 (?bl + 255 * ?q) =>
lazymatch type of HE36 with ew _ 36 = Z_to_bv 64 (?bb + 256 * q + ?r + 1) =>
lazymatch type of Hbbin with In (_, ?Lbb) _ =>
let Ha0 := fresh "Ha0" in let Ha1 := fresh "Ha1" in let Ha2 := fresh "Ha2" in let Hra' := fresh "Hra'" in
jreg HS (10%bv:reg) as Ha0; jreg HS (11%bv:reg) as Ha1; jreg HS (12%bv:reg) as Ha2; jreg HS (1%bv:reg) as Hra';
rewrite HE34, unsigned_lit_small in Ha0 by lia; rewrite HE35 in Ha1; rewrite HE33 in Ha2;
eapply SR_bind;
[ eapply (jmemcpy _ _ LAWS IMG _ ubs0_memcpy) with (n := r);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Ha0 | exact Ha1 | exact Ha2 | exact Hra'
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | lia | ];
[ intros j Hj; replace (bb + 256 * q + 1 + j) with (bb + (256 * q + 1 + j)) by lia;
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bb _ (256 * q + 1 + j) (proj1 HJ) Hbbin ltac:(lia)))
| intros j Hj; replace (bl + 255 * q + j) with (bl + (255 * q + j)) by lia;
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bl _ (255 * q + j) (proj1 HJ) Hblin ltac:(lia)))
| intros a Ha; right; left; split; [exists (bb, bb + Lbb); split; [left; reflexivity | cbn; lia]|];
exists bb, Lbb; split; [exact Hbbin | lia] ]
| ];
let regs2 := fresh "regsM" in let mem2 := fresh "memM" in
let HJ2 := fresh "HJM" in let Hfr2 := fresh "HfrM" in let Hout2 := fresh "HoutM" in let Hgr2 := fresh "HgrM" in
intros c' (regs2 & mem2 & -> & HJ2 & _ & Hfr2 & Hout2 & Hgr2 & _);
let HS2 := fresh "HS2" in
jafter_stretch HS k regs2 mem2 (10%bv :: MEMCPY_CLOB) (ubs0_A_create_byte_list_block + 0x10c) HS2;
match type of HS2 with ?P -> ?Q -> _ =>
assert (HP : P); [intros rr Hrr; apply Hfr2; exact (reg_in_cons_false _ _ _ Hrr)|];
assert (HQ : Q); [| specialize (HS2 HP HQ); clear HP HQ] end;
[ constructor; [|constructor; [|constructor; [|constructor]]];
eapply (region_kept_outside _ _ _ _ _ (bb + 256 * q + 1) r Hout2 Hgr2); cbn [r_base r_lo r_hi r_wlo r_whi base_val];
ew_havoc; rewrite ?HE2, ?Hspw, ?HE34, ?HE36, ?unsigned_lit_small by lia; lia
| ];
clear HS HJ; rename HS2 into HS; rename HJ2 into HJ;
jrun LAWS ubs0tbl_ok HS HJ; [ wr_norm; apply Hwr1; ew_havoc; [exact HE2 | exact HE34 | exact HE36] |];
let HPR := fresh "HPR" in
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS
ltac:(repeat (first [exact HA0 | eapply (env_agree_havoc_ge 32); [lia|]])) ltac:(vm_compute; reflexivity)) as HPR;
let Hr10 := fresh "Hr10" in let Hr1 := fresh "Hr1" in
jreg HS (10%bv:reg) as Hr10; jreg HS (1%bv:reg) as Hr1;
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |];
[ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))
| exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))))
| lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx) end;
rewrite Hr1, HE1, Hra; split; [reflexivity|]; split; [exact HJ|]; split; [exact HPR|];
rewrite Hr10, HE32, HE33, alu64_sll_lit, !alu64_add_lit by lia; f_equal;
rewrite (proj2 (Z.eqb_neq r 0) Hr0); lia ]
end end end.
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_norm. apply Hwr1; [exact HE2 | exact HE34 | exact HE36]. }
jbranch ubs0tbl HS.
+
rewrite branch_ltu_U, (U_atom _ 12 n), U_lit in Hc; [| lia | exact HE12 | lia].
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_memcpy.
{ wr_norm. apply Hwr1; [exact HE2 | exact HE34 | exact HE36]. }
tail1 LAWS HS HJ Hwr1 HE2 Hspw HE34 HE36 HE35 HE33 HE32 HE1 HA0 Hra Hqr Hr0 Hbbin Hblin 40%nat.
+
rewrite branch_ltu_U, (U_atom _ 12 n), U_lit in Hc; [| lia | exact HE12 | lia].
assert (Hq1 : 1 <= q) by (destruct (Z.ltb_spec n 255); [discriminate|]; lia).
jrun_to LAWS ubs0tbl_ok HS HJ (ubs0_A_create_byte_list_block + 0x74).
{ wr_norm. apply Hwr1; [exact HE2 | exact HE34 | exact HE36]. }
jreg HS (19%bv:reg) as Hl19. jreg HS (23%bv:reg) as Hl23. jreg HS (8%bv:reg) as Hl8. jreg HS (9%bv:reg) as Hl9.
jreg HS (20%bv:reg) as Hl20. jreg HS (21%bv:reg) as Hl21. jreg HS (22%bv:reg) as Hl22. jreg HS (24%bv:reg) as Hl24. jreg HS (25%bv:reg) as Hl25.
rewrite ?HE32 in Hl23. rewrite ?HE11 in Hl8. rewrite ?HE10 in Hl9. rewrite ?HE37 in Hl20. rewrite ?HE11, ?unsigned_lit_small in Hl21 by lia.
rewrite ?HE38 in Hl22. rewrite ?HE39 in Hl24.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (cbb_loop API IMG (Z.to_nat q) 0 _ _ CBB_STK (spZ regs) [(bb, bb + Lbb)] L A mem md bb Lbb bl Lbl q);
[ lia | lia | exact HJ | exact Hbbin | exact Hblin | lia | lia | lia | lia
| intros a Ha; exists (bb, bb + Lbb); split; [left; reflexivity | cbn; lia]
| exact Hl19 | exact Hl23 | exact Hl8 | exact Hl9 | exact Hl20 | exact Hl21 | exact Hl22 | exact Hl24 | rewrite Hl25; vm_compute; reflexivity ]. }
intros c' (regsL & memL & -> & HJL & HKL & HoutL & HgrL).
jafter_stretch HS 40%nat regsL memL CBB_LOOP_CLOB (ubs0_A_create_byte_list_block + 0xb4) HS2.
match type of HS2 with ?P -> ?Q -> _ =>
assert (HQ : Q); [| specialize (HS2 HKL HQ); clear HQ] end.
{ constructor; [|constructor; [|constructor; [|constructor]]];
eapply (region_kept_outside _ _ _ _ _ bb (256 * q) HoutL HgrL); cbn [r_base r_lo r_hi r_wlo r_whi base_val];
rewrite ?HE2, ?Hspw, ?HE34, ?HE36, ?unsigned_lit_small by lia; lia. }
clear HS HJ. rename HS2 into HS. rename HJL into HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_memcpy.
{ wr_norm. apply Hwr1; ew_havoc; [exact HE2 | exact HE34 | exact HE36]. }
tail1 LAWS HS HJ Hwr1 HE2 Hspw HE34 HE36 HE35 HE33 HE32 HE1 HA0 Hra Hqr Hr0 Hbbin Hblin 54%nat.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
