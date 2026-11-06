(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YO3m YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.

Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Definition CBB_LOOP_CLOB : list reg := [10; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 1; 20; 23]%bv.
Definition CBB_LOOP_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 21; 24; 25; 26; 27; 29; 30; 31]%bv.
Lemma cbb_kept_in : forall r : reg, reg_in r CBB_LOOP_CLOB = false -> r = 0%bv \/ r = 22%bv \/ In r CBB_LOOP_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | vm_compute in Hr; discriminate | right; right; cbv; tauto] |]).
destruct Hin.
Qed.
Definition ss_cbb_loop : sstate :=
mkSS (src2_A_create_byte_list_block + 0x74) (sr_set sr_atoms 22%bv (SLit 255))
[ YQ0b.mkRegion (Some 32%nat) 0 1 0 1 [] ]
None
(mkFacts [ (9%nat, mkAF 4096 CEIL_MAX 4); (23%nat, mkAF 0 (2^36) 8); (32%nat, mkAF 4096 CEIL_MAX 0);
(24%nat, mkAF 4096 CEIL_MAX 0); (20%nat, mkAF 4096 CEIL_MAX 0); (25%nat, mkAF 0 (2^36) 8) ]
[]
[ (SAlu ALU_SLL (SAluw ALU_SRL (SOff 23%nat 0) (SLit 8)) (SLit 8), SOff 23%nat 0);
(SAlu ALU_ADD (SOff 9%nat 0) (SOff 23%nat 0), SOff 32%nat 0) ]).
Lemma alias_srlw_sll : forall E v, ew E 23 = Z_to_bv 64 (256 * v) -> 0 <= v < 2 ^ 22 ->
sv_denot E (SAlu ALU_SLL (SAluw ALU_SRL (SOff 23 0) (SLit 8)) (SLit 8)) = sv_denot E (SOff 23 0).
Proof.
intros E v H23 Hv. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite (U_atom E 23 (256 * v) H23) by lia. rewrite !U_SLit.
change (zcanon 8 mod 2 ^ 32) with 8. change (Z.land 8 31) with 8. change (Z.land (zcanon 8) 63) with 8.
rewrite (Z.mod_small (256 * v)) by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
replace (256 * v / 2 ^ 8) with v by (change (2 ^ 8) with 256; rewrite Z.mul_comm, Z.div_mul; lia).
unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
replace (bv_modulus 32) with (2 ^ 32) by reflexivity. replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
rewrite (Z.mod_small (v + 2 ^ 31)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
rewrite (Z.mod_small v) by lia. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma cbb_loop : forall (k : nat) (i : Z) regs memc STK sp0 FP L A mem md bb Lbb bl Lbl q,
Z.of_nat k = q - i -> 0 <= i < q ->
journal src2_msyms MR STK sp0 FP L A mem md L A memc md ->
In (bb, Lbb) (blocks L A) -> In (bl, Lbl) (blocks L A) -> (bb + Lbb <= bl \/ bl + Lbl <= bb) ->
256 * q + 1 <= Lbb -> 255 * q <= Lbl -> q < 2 ^ 21 ->
(forall a, bb <= a < bb + Lbb -> inFP FP a) ->
getr regs 23 = Z_to_bv 64 (256 * i) -> getr regs 20 = Z_to_bv 64 (bl + 255 * i) ->
getr regs 24 = Z_to_bv 64 (bb + 1) -> getr regs 25 = Z_to_bv 64 (256 * q) ->
getr regs 9 = Z_to_bv 64 bb -> getr regs 22 = Z_to_bv 64 255 ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 (src2_A_create_byte_list_block + 0x74)) memc (seg_rom src2segs)) md)
(fun c' => exists regs' mem',
c' = mkCfg (mkst regs' (Z_to_bv 64 (src2_A_create_byte_list_block + 0xa0)) mem' (seg_rom src2segs)) md /\
journal src2_msyms MR STK sp0 FP L A mem md L A mem' md /\
(forall r, reg_in r CBB_LOOP_CLOB = false -> getr regs' r = getr regs r) /\
(forall x : word, bv_unsigned x < bb \/ bb + 256 * q <= bv_unsigned x -> mem' x = memc x) /\
mem_grows memc mem').
Proof.
induction k as [|k IH]; intros i regs memc STK sp0 FP L A mem md bb Lbb bl Lbl q Hk Hi HJ Hbb Hbl Hdisj HLbb HLbl Hq HFP
H23 H20 H24 H25 H9 H22; [lia|].
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HH.
destruct (heap_blocks_range _ _ LAWS _ _ _ _ bb Lbb HH Hbb ltac:(lia)) as (Bb0 & Bb1 & Bb16).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ bl Lbl HH Hbl ltac:(lia)) as (Bl0 & Bl1 & Bl16).
assert (HS : st_ok src2segs (Ereg regs [Z_to_bv 64 (bb + 256 * i)]) ss_cbb_loop
(mkst regs (Z_to_bv 64 (src2_A_create_byte_list_block + 0x74)) memc (seg_rom src2segs))).
{ apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H22].
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite (ew_Ereg_extra regs _ 0). cbn [nth]. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (present_writable src2_msyms). replace (bb + 256 * i + o) with (bb + (256 * i + o)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bb Lbb (256 * i + o) HH Hbb ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs _ 9 9%bv), (ew_Ereg_nat regs _ 23 23%bv), (ew_Ereg_nat regs _ 24 24%bv),
(ew_Ereg_nat regs _ 20 20%bv), (ew_Ereg_nat regs _ 25 25%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_extra regs _ 0). cbn [nth].
rewrite H9, H23, H24, H20, H25, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 8) with 256. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia.
all: try (rewrite Z.mul_comm; apply Z_mod_mult).
all: match goal with |- ?g => idtac g end.
+ cbn [f_alias alias_ok]. split; [|split; [|exact I]].
* apply (alias_srlw_sll _ i); [|lia]. rewrite (ew_Ereg_nat regs _ 23 23%bv) by (vm_compute; reflexivity). exact H23.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom _ 9 bb), (U_atom _ 23 (256 * i)), (U_atom _ 32 (bb + 256 * i));
[ apply zcanon_id; unfold M64; lia | | lia | | lia | | lia ].
-- rewrite (ew_Ereg_extra regs _ 0). reflexivity.
-- rewrite (ew_Ereg_nat regs _ 23 23%bv) by (vm_compute; reflexivity). exact H23.
-- rewrite (ew_Ereg_nat regs _ 9 9%bv) by (vm_compute; reflexivity). exact H9. }
assert (HE9 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i)]) 9 = Z_to_bv 64 bb)
by (rewrite (ew_Ereg_nat regs _ 9 9%bv) by (vm_compute; reflexivity); exact H9).
assert (HE23 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i)]) 23 = Z_to_bv 64 (256 * i))
by (rewrite (ew_Ereg_nat regs _ 23 23%bv) by (vm_compute; reflexivity); exact H23).
assert (HE24 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i)]) 24 = Z_to_bv 64 (bb + 1))
by (rewrite (ew_Ereg_nat regs _ 24 24%bv) by (vm_compute; reflexivity); exact H24).
assert (HE20 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i)]) 20 = Z_to_bv 64 (bl + 255 * i))
by (rewrite (ew_Ereg_nat regs _ 20 20%bv) by (vm_compute; reflexivity); exact H20).
assert (HE25 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i)]) 25 = Z_to_bv 64 (256 * q))
by (rewrite (ew_Ereg_nat regs _ 25 25%bv) by (vm_compute; reflexivity); exact H25).
assert (HE32 : ew (Ereg regs [Z_to_bv 64 (bb + 256 * i)]) 32 = Z_to_bv 64 (bb + 256 * i))
by (rewrite (ew_Ereg_extra regs _ 0); reflexivity).
change memc with (ms_mem (mkst regs (Z_to_bv 64 (src2_A_create_byte_list_block + 0x74)) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_memcpy.
{ wr_ok_tac. eapply (wr_ok_cons_inblock _ _ _ _ _ _ _ _ 32 (bb + 256 * i) bb Lbb);
[reflexivity | rewrite HE32; apply unsigned_lit_small; lia | exact Hbb | cbn; lia | cbn; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. apply HFP. lia. }
jreg HS (10%bv:reg) as Ha0. jreg HS (11%bv:reg) as Ha1. jreg HS (12%bv:reg) as Ha2. jreg HS (1%bv:reg) as Hra.
rewrite HE23, HE24, alu64_add_lit in Ha0. rewrite HE20 in Ha1.
eapply SR_bind.
{ eapply (jmemcpy _ _ LAWS IMG _ src2_memcpy) with (d := 256 * i + (bb + 1)) (src := bl + 255 * i) (n := 255);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Ha0 | exact Ha1 | exact Ha2 | exact Hra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | lia | ].
- intros j Hj. replace (256 * i + (bb + 1) + j) with (bb + (256 * i + 1 + j)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bb Lbb (256 * i + 1 + j) (proj1 HJ) Hbb ltac:(lia))).
- intros j Hj. replace (bl + 255 * i + j) with (bl + (255 * i + j)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bl Lbl (255 * i + j) (proj1 HJ) Hbl ltac:(lia))).
- intros a Ha. right. left. split; [apply HFP; lia|]. exists bb, Lbb. split; [exact Hbb | lia]. }
intros c' (regs2 & mem2 & -> & HJ2 & Hr10 & Hfr2 & Hout2 & Hgr2 & _).
pose proof (st_ok_after_stretch src2segs 33 _ _ _ regs2 mem2 [] (src2_A_create_byte_list_block + 0x94)
(10%bv :: MEMCPY_CLOB) HS eq_refl ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl
(submem_nil _) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HP : P); [|assert (HQ : Q); [constructor | specialize (HS2 HP HQ); clear HP HQ]] end.
{ intros r Hr. apply Hfr2. cbn [reg_in] in Hr |- *. destruct (bv_eqb r 10); [discriminate | exact Hr]. }
lazymatch type of HS2 with st_ok _ _ ?ss2 _ => let ss3 := eval vm_compute in ss2 in change ss2 with ss3 in HS2 end.
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (src2_A_create_byte_list_block + 0x94)) mem2 (seg_rom src2segs))) in HJ2.
jrun LAWS src2tbl_ok HS HJ2.
{ wr_ok_tac. }
jbranch src2tbl HS.
-
rewrite branch_ne_U in Hc. rewrite (U_atom _ 25 (256 * q)) in Hc; [| ew_havoc; exact HE25 | lia].
rewrite (U_atom_off _ 23 (256 * i) 256) in Hc; [| ew_havoc; exact HE23 | lia | lia].
assert (Hlt : i + 1 < q) by (destruct (Z.eqb_spec (256 * q) (256 * i + 256)); [discriminate | lia]).
jrun_to LAWS src2tbl_ok HS HJ2 (src2_A_create_byte_list_block + 0x74).
{ wr_ok_tac. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ CBB_LOOP_KEPT HS
(env_agree_havoc_ge 32 33 _ _ _ ltac:(lia) (env_agree_refl _ _)) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (23%bv:reg) as Hn23. jreg HS (20%bv:reg) as Hn20. jreg HS (24%bv:reg) as Hn24.
jreg HS (25%bv:reg) as Hn25. jreg HS (9%bv:reg) as Hn9. jreg HS (22%bv:reg) as Hn22.
rewrite HE23, unsigned_lit_small in Hn23 by lia. rewrite HE20, unsigned_lit_small in Hn20 by lia.
rewrite HE24 in Hn24. rewrite HE25 in Hn25. rewrite HE9 in Hn9.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 1) _ _ STK sp0 FP L A mem md bb Lbb bl Lbl q); [lia | lia | exact HJ2 | exact Hbb | exact Hbl | exact Hdisj | exact HLbb | exact HLbl | exact Hq | exact HFP
| rewrite Hn23; f_equal; lia | rewrite Hn20; f_equal; lia | exact Hn24 | exact Hn25 | exact Hn9 | exact Hn22 ]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & HK3 & Hout3 & Hgr3).
exists regs3, mem3. split; [reflexivity|]. split; [exact HJ3|]. split; [|split].
+ intros r Hr. rewrite (HK3 r Hr). destruct (cbb_kept_in r Hr) as [->|[->|Hin]]; [rewrite !getr_zero; reflexivity| |].
* rewrite Hn22, H22. reflexivity.
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
rewrite branch_ne_U in Hc. rewrite (U_atom _ 25 (256 * q)) in Hc; [| ew_havoc; exact HE25 | lia].
rewrite (U_atom_off _ 23 (256 * i) 256) in Hc; [| ew_havoc; exact HE23 | lia | lia].
assert (Heq : i + 1 = q) by (destruct (Z.eqb_spec (256 * q) (256 * i + 256)); [lia | discriminate]).
jrun_to LAWS src2tbl_ok HS HJ2 (src2_A_create_byte_list_block + 0xa0).
{ wr_ok_tac. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ CBB_LOOP_KEPT HS
(env_agree_havoc_ge 32 33 _ _ _ ltac:(lia) (env_agree_refl _ _)) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (22%bv:reg) as Hn22.
apply SR_ret. rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- context [mkst (ms_regs ?msx) _ (ms_mem _) _] => exists (ms_regs msx), (ms_mem msx) end.
split; [reflexivity|]. split; [exact HJ2|]. split; [|split].
+ intros r Hr. destruct (cbb_kept_in r Hr) as [->|[->|Hin]]; [rewrite !getr_zero; reflexivity| |].
* rewrite Hn22, H22. reflexivity.
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
Definition ss_cbb0 : sstate :=
mkSS src2_A_create_byte_list_block sr_atoms [ reg_stack96; reg_at 34 ] None (mkFacts (cbb_facts true) [] cbb_aliases).
Definition ss_cbb1 : sstate :=
mkSS src2_A_create_byte_list_block sr_atoms [ reg_stack96; reg_at 34; reg_at 36 ] None (mkFacts (cbb_facts false) [] cbb_aliases).
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Theorem src2_cbl_block : forall L A regs mem md bl Lbl bb Lbb n rest,
fn_pre src2_msyms MR CBB_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 bl -> getr regs 11 = Z_to_bv 64 bb -> getr regs 12 = Z_to_bv 64 n ->
0 <= n < 2 ^ 28 -> n <= Lbl -> 0 < Lbl -> cbb_len n <= Lbb ->
Permutation (blocks L A) ((bl, Lbl) :: (bb, Lbb) :: rest) ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 src2_A_create_byte_list_block) mem (seg_rom src2segs)) md)
(fun c' => exists regs' mem',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom src2segs)) md /\
journal src2_msyms MR CBB_STK (spZ regs) [(bb, bb + Lbb)] L A mem md L A mem' md /\
regs_preserved regs regs' /\
getr regs' 10 = Z_to_bv 64 (cbb_len n - 1)).
Proof.
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
destruct (heap_blocks_range src2_msyms MR LAWS L A mem md bl Lbl HH Hblin ltac:(lia)) as (Bl0 & Bl1 & Bl16).
destruct (heap_blocks_range src2_msyms MR LAWS L A mem md bb Lbb HH Hbbin ltac:(lia)) as (Bb0 & Bb1 & Bb16).
pose proof (heap_sep_perm src2_msyms MR LAWS L A mem md (bl, Lbl) _ (bb, Lbb) HH HB ltac:(left; reflexivity)) as Hsep.
cbn [fst snd] in Hsep.
remember (Ereg regs [Z_to_bv 64 q; Z_to_bv 64 r; Z_to_bv 64 (bb + 256 * q); Z_to_bv 64 (bl + 255 * q); Z_to_bv 64 (bb + 256 * q + r + 1)]) as E0 eqn:HE0.
assert (HA0 : env_agree 32 (Ereg regs [Z_to_bv 64 q; Z_to_bv 64 r; Z_to_bv 64 (bb + 256 * q); Z_to_bv 64 (bl + 255 * q); Z_to_bv 64 (bb + 256 * q + r + 1)]) E0)
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
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
assert (Hwr0 : forall E' cs1 cs2, ew E' 2 = getr regs 2 -> ew E' 34 = Z_to_bv 64 (bb + 256 * q) ->
wr_ok E' [YQ0b.mkRegion (Some 2%nat) (-96) 0 (-96) 0 cs1; YQ0b.mkRegion (Some 34%nat) 0 1 0 1 cs2]
CBB_STK (spZ regs) [(bb, bb + Lbb)] (blocks L A) (blocks L A)).
{ intros E' cs1 cs2 HE2' HE34'.
eapply wr_ok_cons_stack; [reflexivity | rewrite HE2'; exact Hspw | cbn; lia | cbn; lia |].
eapply (wr_ok_cons_inblock _ _ _ _ _ _ _ _ 34 (bb + 256 * q) bb Lbb);
[reflexivity | rewrite HE34'; apply unsigned_lit_small; lia | exact Hbbin | cbn; lia | cbn; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. exists (bb, bb + Lbb). split; [left; reflexivity | cbn; lia]. }
assert (Hwr1 : r <> 0 -> forall E' cs1 cs2 cs3, ew E' 2 = getr regs 2 -> ew E' 34 = Z_to_bv 64 (bb + 256 * q) ->
ew E' 36 = Z_to_bv 64 (bb + 256 * q + r + 1) ->
wr_ok E' [YQ0b.mkRegion (Some 2%nat) (-96) 0 (-96) 0 cs1; YQ0b.mkRegion (Some 34%nat) 0 1 0 1 cs2;
YQ0b.mkRegion (Some 36%nat) 0 1 0 1 cs3]
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
set (ms0 := mkst regs (Z_to_bv 64 src2_A_create_byte_list_block) mem (seg_rom src2segs)).
pose proof (journal_init src2_msyms MR CBB_STK [(bb, bb + Lbb)] L A regs mem md HPRE) as HJ.
change mem with (ms_mem ms0) in HJ.
destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
-
assert (HS : st_ok src2segs E0 ss_cbb0 ms0).
{ rewrite HE0. apply entry_st_ok_full; rewrite <- ?HE0; unfold reg_stack96, reg_at.
- rewrite HE0. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack src2segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite HE2. exact Hspw.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val reg_at]. rewrite HE34, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (present_writable src2_msyms).
replace (bb + 256 * q + o) with (bb + (256 * q + o)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bb Lbb (256 * q + o) HH Hbbin ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint reg_at reg_stack96]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE34, Hspw, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok cbb_facts app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE10, HE11, HE12, HE32, HE33, HE34, HE35, Hspw, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_alias]. eapply (cbb_aliases_ok E0 n q r bl bb); try eassumption; lia. }
clear Hwr1 Hal16 Bl16 Bb16.
Local Ltac tail0 LAWS HS HJ Hwr0 HE2 HE34 HE33 HE32 HE1 HA0 Hra Hqr Hr0 :=
lazymatch type of Hr0 with ?r = 0 =>
jbranch src2tbl HS;
[ jrun LAWS src2tbl_ok HS HJ; [ wr_norm; apply Hwr0; ew_havoc; [exact HE2 | exact HE34] |];
let HPR := fresh "HPR" in
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS
ltac:(repeat (first [exact HA0 | eapply (env_agree_havoc_ge 32); [lia|]])) ltac:(vm_compute; reflexivity)) as HPR;
let Hr10 := fresh "Hr10" in let Hr1 := fresh "Hr1" in
jreg HS (10%bv:reg) as Hr10; jreg HS (1%bv:reg) as Hr1;
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |];
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
jrun LAWS src2tbl_ok HS HJ.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE34]. }
jbranch src2tbl HS.
+
rewrite branch_ltu_U, (U_atom _ 12 n), U_lit in Hc; [| lia | exact HE12 | lia].
jrun LAWS src2tbl_ok HS HJ.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE34]. }
tail0 LAWS HS HJ Hwr0 HE2 HE34 HE33 HE32 HE1 HA0 Hra Hqr Hr0.
+
rewrite branch_ltu_U, (U_atom _ 12 n), U_lit in Hc; [| lia | exact HE12 | lia].
assert (Hq1 : 1 <= q) by (destruct (Z.ltb_spec n 255); [discriminate|]; lia).
jrun_to LAWS src2tbl_ok HS HJ (src2_A_create_byte_list_block + 0x74).
{ wr_norm. apply Hwr0; [exact HE2 | exact HE34]. }
jreg HS (23%bv:reg) as Hl23. jreg HS (20%bv:reg) as Hl20. jreg HS (24%bv:reg) as Hl24.
jreg HS (25%bv:reg) as Hl25. jreg HS (9%bv:reg) as Hl9. jreg HS (22%bv:reg) as Hl22.
rewrite HE10 in Hl20. rewrite HE11, unsigned_lit_small in Hl24 by lia.
rewrite HE32, alu64_sll_lit in Hl25 by lia. rewrite HE11 in Hl9.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (cbb_loop API IMG (Z.to_nat q) 0 _ _ CBB_STK (spZ regs) [(bb, bb + Lbb)] L A mem md bb Lbb bl Lbl q);
[ lia | lia | exact HJ | exact Hbbin | exact Hblin | lia | lia | lia | lia
| intros a Ha; exists (bb, bb + Lbb); split; [left; reflexivity | cbn; lia]
| rewrite Hl23; reflexivity | rewrite Hl20; f_equal; lia | exact Hl24 | rewrite Hl25; f_equal; lia | exact Hl9 | exact Hl22 ]. }
intros c' (regsL & memL & -> & HJL & HKL & HoutL & HgrL).
jafter_stretch HS 37%nat regsL memL CBB_LOOP_CLOB (src2_A_create_byte_list_block + 0xa0) HS2.
match type of HS2 with ?P -> ?Q -> _ =>
assert (HQ : Q); [| specialize (HS2 HKL HQ); clear HQ] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_outside _ _ _ _ _ bb (256 * q) HoutL HgrL); cbn [r_base r_lo r_hi r_wlo r_whi base_val];
rewrite ?HE2, ?Hspw; lia.
- eapply (region_kept_outside _ _ _ _ _ bb (256 * q) HoutL HgrL); cbn [r_base r_lo r_hi r_wlo r_whi base_val];
rewrite ?HE34, ?unsigned_lit_small by lia; lia. }
clear HS HJ. rename HS2 into HS. rename HJL into HJ.
jrun LAWS src2tbl_ok HS HJ.
{ wr_norm. apply Hwr0; ew_havoc; [exact HE2 | exact HE34]. }
tail0 LAWS HS HJ Hwr0 HE2 HE34 HE33 HE32 HE1 HA0 Hra Hqr Hr0.
-
specialize (Hwr1 Hr0). clear Hwr0.
assert (Hlen2 : 256 * q + r + 2 <= Lbb) by (destruct (Z.eqb_spec r 0); lia).
assert (HS : st_ok src2segs E0 ss_cbb1 ms0).
{ rewrite HE0. apply entry_st_ok_full; rewrite <- ?HE0; unfold reg_stack96, reg_at.
- rewrite HE0. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ apply (region_ok_stack src2segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite HE2. exact Hspw.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val reg_at]. rewrite HE34, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (present_writable src2_msyms).
replace (bb + 256 * q + o) with (bb + (256 * q + o)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bb Lbb (256 * q + o) HH Hbbin ltac:(lia))).
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val reg_at]. rewrite HE36, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (present_writable src2_msyms).
replace (bb + 256 * q + r + 1 + o) with (bb + (256 * q + r + 1 + o)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bb Lbb (256 * q + r + 1 + o) HH Hbbin ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint reg_at reg_stack96]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE34, HE36, Hspw, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok cbb_facts app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE10, HE11, HE12, HE32, HE33, HE34, HE35, HE36, Hspw, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_alias]. eapply (cbb_aliases_ok E0 n q r bl bb); try eassumption; lia. }
clear Hal16 Bl16 Bb16.
Local Ltac tail1 LAWS HS HJ Hwr1 HE2 Hspw HE34 HE36 HE35 HE33 HE32 HE1 HA0 Hra Hqr Hr0 Hbbin Hblin k :=
lazymatch type of HE35 with ew _ 35 = Z_to_bv 64 (?bl + 255 * ?q) =>
lazymatch type of HE36 with ew _ 36 = Z_to_bv 64 (?bb + 256 * q + ?r + 1) =>
lazymatch type of Hbbin with In (_, ?Lbb) _ =>
let Ha0 := fresh "Ha0" in let Ha1 := fresh "Ha1" in let Ha2 := fresh "Ha2" in let Hra' := fresh "Hra'" in
jreg HS (10%bv:reg) as Ha0; jreg HS (11%bv:reg) as Ha1; jreg HS (12%bv:reg) as Ha2; jreg HS (1%bv:reg) as Hra';
rewrite HE34, unsigned_lit_small in Ha0 by lia; rewrite HE35 in Ha1; rewrite HE33 in Ha2;
eapply SR_bind;
[ eapply (jmemcpy _ _ LAWS IMG _ src2_memcpy) with (n := r);
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
jafter_stretch HS k regs2 mem2 (10%bv :: MEMCPY_CLOB) (src2_A_create_byte_list_block + 0xd0) HS2;
match type of HS2 with ?P -> ?Q -> _ =>
assert (HP : P); [intros rr Hrr; apply Hfr2; exact (reg_in_cons_false _ _ _ Hrr)|];
assert (HQ : Q); [| specialize (HS2 HP HQ); clear HP HQ] end;
[ constructor; [|constructor; [|constructor; [|constructor]]];
eapply (region_kept_outside _ _ _ _ _ (bb + 256 * q + 1) r Hout2 Hgr2); cbn [r_base r_lo r_hi r_wlo r_whi base_val];
ew_havoc; rewrite ?HE2, ?Hspw, ?HE34, ?HE36, ?unsigned_lit_small by lia; lia
| ];
clear HS HJ; rename HS2 into HS; rename HJ2 into HJ;
jrun LAWS src2tbl_ok HS HJ; [ wr_norm; apply Hwr1; ew_havoc; [exact HE2 | exact HE34 | exact HE36] |];
let HPR := fresh "HPR" in
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS
ltac:(repeat (first [exact HA0 | eapply (env_agree_havoc_ge 32); [lia|]])) ltac:(vm_compute; reflexivity)) as HPR;
let Hr10 := fresh "Hr10" in let Hr1 := fresh "Hr1" in
jreg HS (10%bv:reg) as Hr10; jreg HS (1%bv:reg) as Hr1;
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |];
[ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))
| exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))))
| lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx) end;
rewrite Hr1, HE1, Hra; split; [reflexivity|]; split; [exact HJ|]; split; [exact HPR|];
rewrite Hr10, HE32, HE33, alu64_sll_lit, !alu64_add_lit by lia; f_equal;
rewrite (proj2 (Z.eqb_neq r 0) Hr0); lia ]
end end end.
jrun LAWS src2tbl_ok HS HJ.
{ wr_norm. apply Hwr1; [exact HE2 | exact HE34 | exact HE36]. }
jbranch src2tbl HS.
+
rewrite branch_ltu_U, (U_atom _ 12 n), U_lit in Hc; [| lia | exact HE12 | lia].
jrun_to LAWS src2tbl_ok HS HJ src2_A_memcpy.
{ wr_norm. apply Hwr1; [exact HE2 | exact HE34 | exact HE36]. }
tail1 LAWS HS HJ Hwr1 HE2 Hspw HE34 HE36 HE35 HE33 HE32 HE1 HA0 Hra Hqr Hr0 Hbbin Hblin 37%nat.
+
rewrite branch_ltu_U, (U_atom _ 12 n), U_lit in Hc; [| lia | exact HE12 | lia].
assert (Hq1 : 1 <= q) by (destruct (Z.ltb_spec n 255); [discriminate|]; lia).
jrun_to LAWS src2tbl_ok HS HJ (src2_A_create_byte_list_block + 0x74).
{ wr_norm. apply Hwr1; [exact HE2 | exact HE34 | exact HE36]. }
jreg HS (23%bv:reg) as Hl23. jreg HS (20%bv:reg) as Hl20. jreg HS (24%bv:reg) as Hl24.
jreg HS (25%bv:reg) as Hl25. jreg HS (9%bv:reg) as Hl9. jreg HS (22%bv:reg) as Hl22.
rewrite HE10 in Hl20. rewrite HE11, unsigned_lit_small in Hl24 by lia.
rewrite HE32, alu64_sll_lit in Hl25 by lia. rewrite HE11 in Hl9.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (cbb_loop API IMG (Z.to_nat q) 0 _ _ CBB_STK (spZ regs) [(bb, bb + Lbb)] L A mem md bb Lbb bl Lbl q);
[ lia | lia | exact HJ | exact Hbbin | exact Hblin | lia | lia | lia | lia
| intros a Ha; exists (bb, bb + Lbb); split; [left; reflexivity | cbn; lia]
| rewrite Hl23; reflexivity | rewrite Hl20; f_equal; lia | exact Hl24 | rewrite Hl25; f_equal; lia | exact Hl9 | exact Hl22 ]. }
intros c' (regsL & memL & -> & HJL & HKL & HoutL & HgrL).
jafter_stretch HS 37%nat regsL memL CBB_LOOP_CLOB (src2_A_create_byte_list_block + 0xa0) HS2.
match type of HS2 with ?P -> ?Q -> _ =>
assert (HQ : Q); [| specialize (HS2 HKL HQ); clear HQ] end.
{ constructor; [|constructor; [|constructor; [|constructor]]];
eapply (region_kept_outside _ _ _ _ _ bb (256 * q) HoutL HgrL); cbn [r_base r_lo r_hi r_wlo r_whi base_val];
rewrite ?HE2, ?Hspw, ?HE34, ?HE36, ?unsigned_lit_small by lia; lia. }
clear HS HJ. rename HS2 into HS. rename HJL into HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_memcpy.
{ wr_norm. apply Hwr1; ew_havoc; [exact HE2 | exact HE34 | exact HE36]. }
tail1 LAWS HS HJ Hwr1 HE2 Hspw HE34 HE36 HE35 HE33 HE32 HE1 HA0 Hra Hqr Hr0 Hbbin Hblin 52%nat.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
