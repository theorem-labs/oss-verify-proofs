(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03
UI1e UI1i UI59 YI0x YL0e YI08 YI0c UO0e UIZe.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition RD_RET : Z := Eval vm_compute in (ubs2_A_readdata + 0x64).
Definition rd_frame : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
Definition ss_rd_ok : sstate :=
mkSS ubs2_A_readdata sr_atoms
[ rd_frame ;
YQ0b.mkRegion (Some 10%nat) 0 24 16 24 [mkChunk 0 (CVal 8 (SOff 32 0)); mkChunk 8 (CVal 8 (SOff 33 0)); mkChunk 16 (CVal 8 (SOff 34 0))] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + 32) (2^63) 4); (10%nat, mkAF CEIL_MIN (2^63) 3); (12%nat, mkAF 1 RD_NMAX 0);
(32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 0 CEIL_MAX 0); (34%nat, mkAF 0 CEIL_MAX 0) ]
[ mkAC BC_GEU (SOff 33 0) (SAlu ALU_ADD (SOff 12 0) (SOff 34 0)); mkAC BC_GEU (SAlu ALU_ADD (SOff 32 0) (SOff 34 0)) (SOff 32 0) ] []).
Definition ss_rd_no : sstate :=
mkSS ubs2_A_readdata sr_atoms
[ rd_frame ;
YQ0b.mkRegion (Some 10%nat) 0 24 16 24 [mkChunk 8 (CVal 8 (SOff 33 0)); mkChunk 16 (CVal 8 (SOff 34 0))] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + 32) (2^63) 4); (10%nat, mkAF CEIL_MIN (2^63) 3); (12%nat, mkAF 1 RD_NMAX 0);
(33%nat, mkAF 0 (2^63) 0); (34%nat, mkAF 0 (2^63) 0) ]
[ mkAC BC_LTU (SOff 33 0) (SAlu ALU_ADD (SOff 12 0) (SOff 34 0)) ] []).
Lemma U_add_atoms : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x + y < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = x + y.
Proof.
intros E a b x y Ha Hb Rx Ry Rxy. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E a x Ha Rx), (U_atom E b y Hb Ry). apply zcanon_id. unfold M64. lia.
Qed.
Lemma present_of_frame : forall E rs (m m' : word -> option byte) a,
frame_of E rs m m' -> 0 <= a < 2 ^ 64 ->
(forall r, In r rs -> ~ (base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r)) ->
present m a -> present m' a.
Proof.
intros E rs m m' a HF Ha Hout [b Hb]. exists b. rewrite HF; [exact Hb|].
rewrite unsigned_lit_small by exact Ha. intros (r & Hin & Hr). exact (Hout r Hin Hr).
Qed.
Ltac rd_out HF :=
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; repeat (rewrite ew_havoc_old; [|cbv; lia]) |]);
[ .. | destruct Hr ].
Ltac wr2 HE2 HEs := wr_norm;
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HEs | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_nil.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Theorem ubs2_readdata : readdata_spec API.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs st dst n pdata nb cur
HJ Hra Hal16 Hbud Hst0 Hst1 Hst8 G10 G11 G12 Hn Hcur Hnb Wp Wn Wc Hok.
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HRS : RD_STK = 32) by reflexivity. assert (HRN : RD_NMAX = 40000) by reflexivity.
rewrite HRS in Hbud, Hok |- *. rewrite HRN in Hn.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp := spZ regs) in *.
set (extra := [Z_to_bv 64 pdata; Z_to_bv 64 nb; Z_to_bv 64 cur]).
set (E := Ereg regs extra).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall k j v, (k = 32 + j)%nat -> nth_error extra j = Some v -> ew E k = v).
{ intros k j v -> Hj. subst E. rewrite ew_Ereg_extra. apply nth_error_nth. exact Hj. }
assert (HE2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HEs : bv_unsigned (ew E 10) = st) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HE12 : ew E 12 = Z_to_bv 64 n) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (HE32 : ew E 32 = Z_to_bv 64 pdata) by (apply (HX 32%nat 0%nat _ eq_refl eq_refl)).
assert (HE33 : ew E 33 = Z_to_bv 64 nb) by (apply (HX 33%nat 1%nat _ eq_refl eq_refl)).
assert (HE34 : ew E 34 = Z_to_bv 64 cur) by (apply (HX 34%nat 2%nat _ eq_refl eq_refl)).
assert (HEA : env_agree 32 (Ereg regs extra) E) by (subst E; split; [intros k Hk; reflexivity | reflexivity]).
assert (R1' : forall ms, getr (ms_regs ms) 1 = ew E 1 -> getr (ms_regs ms) 1 = getr regs 1).
{ intros ms H. rewrite H. exact (HE 1%nat 1%bv eq_refl). }
destruct (Z_le_gt_dec (cur + n) nb) as [Hfit | Hnofit].
-
destruct (Hok Hfit) as (Hp0 & Hp1 & Hpsrc & Hd0 & Hd1 & Hpdst & Hwdst & Hds & Hdst & Hdf). clear Hok.
assert (HS : st_ok ubs2segs E ss_rd_ok (mkst regs (Z_to_bv 64 ubs2_A_readdata) memc (seg_rom ubs2segs))).
{ unfold ss_rd_ok, rd_frame. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs2segs _ memc 2 sp); [exact HE2 | lia | lia | intros a Ha; apply Hstw; lia].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HEs.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply Hstw. lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HEs. repeat split; lia.
- split; [|split; [|exact I]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HEs, HE12, HE32, HE33, HE34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia.
+ cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite !branch_geu_U, (U_atom _ 33 nb HE33 ltac:(lia)), (U_atom _ 32 pdata HE32 ltac:(lia)),
(U_add_atoms _ 12 34 n cur HE12 HE34 ltac:(lia) ltac:(lia) ltac:(lia)),
(U_add_atoms _ 32 34 pdata cur HE32 HE34 ltac:(lia) ltac:(lia) ltac:(lia)).
split; [apply negb_true_iff, Z.ltb_ge; lia|]. split; [apply negb_true_iff, Z.ltb_ge; lia | exact I]. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_readdata) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memcpy. { wr2 HE2 HEs. }
cbn [ms_mem mkst] in HF.
jreg HS (10%bv:reg) as M10. rewrite (HE 11%nat 11%bv eq_refl), G11 in M10.
jreg HS (11%bv:reg) as M11. rewrite HE32, HE34, alu64_add_lit in M11.
jreg HS (12%bv:reg) as M12. rewrite HE12 in M12.
jreg HS (1%bv:reg) as M1.
eapply SR_bind.
{ eapply (jmemcpy _ _ LAWS IMG _ ubs2_memcpy) with (d := dst) (src := pdata + cur) (n := n);
[ exact HS | reflexivity | reflexivity | exact HJ | exact M10 | exact M11
| exact M12 | exact M1 | apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | | ].
- intros i Hi. apply (present_of_frame _ _ _ _ _ HF); [lia | rd_out HF; rewrite ?HE2, ?HEs; lia | apply Hpdst; exact Hi].
- intros i Hi. apply (present_of_frame _ _ _ _ _ HF); [lia | rd_out HF; rewrite ?HE2, ?HEs; lia | apply Hpsrc; exact Hi].
- lia.
- exact Hwdst. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & Hd10 & Hfr3 & Hout3 & Hgr3 & Hcp3).
change (ms_segs ubs2_msyms) with ubs2segs in Hcp3.
jafter_stretch HS 48%nat regs3 mem3 MEMCPY_CLOB RD_RET HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr3. exact Hrr. }
{ constructor; [|constructor; [|constructor]].
- eapply region_kept_outside; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HE2; lia
| cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HE2; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HE2; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HEs; lia
| cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HEs; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HEs; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs2tbl_ok HS HJ3. { wr2 HE2 HEs. }
cbn [ms_mem mkst] in HF0.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3)) as (Hh & Hl & _).
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | exact Hh | exact Hl | exact HS | reflexivity | vm_compute; reflexivity |].
exists (ms_regs ms0), (ms_mem ms0).
split.
{ jreg HS (1%bv:reg) as X. rewrite (R1' ms0); [rewrite Hra; reflexivity|]. rewrite X. ew_havoc. reflexivity. }
split; [exact HJ3|].
split.
{ apply (regs_preserved_of_st_ok ubs2segs _ _ ms0 regs extra HS (env_agree_havoc_ge 32 48 _ _ _ ltac:(lia) HEA)).
vm_compute. reflexivity. }
split.
{ left. split; [exact Hfit|]. split.
{ jreg HS (10%bv:reg) as X. rewrite X. reflexivity. }
split.
{ eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 _ st (cur + n) HS); [reflexivity | reflexivity
| cbn [r_chunks]; repeat first [left; reflexivity | right] | ew_havoc; exact HEs | | lia].
lazymatch goal with |- sv_denot ?Eh _ = _ =>
assert (H12h : ew Eh 12 = Z_to_bv 64 n) by (ew_havoc; exact HE12);
assert (H34h : ew Eh 34 = Z_to_bv 64 cur) by (ew_havoc; exact HE34);
rewrite denot_lit_U; f_equal;
first [ rewrite (U_add_atoms Eh 12 34 n cur H12h H34h ltac:(lia) ltac:(lia) ltac:(lia)); lia
| rewrite (U_add_atoms Eh 34 12 cur n H34h H12h ltac:(lia) ltac:(lia) ltac:(lia)); lia ] end. }
intros i Hi.
rewrite (mbyte_of_frame _ _ _ _ _ HF0); [| lia | rd_out HF0; rewrite ?HE2, ?HEs; lia].
rewrite (Hcp3 i Hi).
rewrite (mbyte_of_frame _ _ _ _ _ HF); [reflexivity | lia | rd_out HF; rewrite ?HE2, ?HEs; lia]. }
intros a Ha Hn1 Hn2 Hn3.
rewrite (mbyte_of_frame _ _ _ _ _ HF0); [| lia | rd_out HF0; rewrite ?HE2, ?HEs; lia].
rewrite (mbyte_of_out _ _ dst n a Hout3 Ha) by lia.
rewrite (mbyte_of_frame _ _ _ _ _ HF); [reflexivity | lia | rd_out HF; rewrite ?HE2, ?HEs; lia].
-
clear Hok.
assert (HS : st_ok ubs2segs E ss_rd_no (mkst regs (Z_to_bv 64 ubs2_A_readdata) memc (seg_rom ubs2segs))).
{ unfold ss_rd_no, rd_frame. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs2segs _ memc 2 sp); [exact HE2 | lia | lia | intros a Ha; apply Hstw; lia].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HEs.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply Hstw. lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HEs. repeat split; lia.
- split; [|split; [|exact I]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HEs, HE12, HE33, HE34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia.
+ cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_ltu_U, (U_atom _ 33 nb HE33 ltac:(lia)), (U_add_atoms _ 12 34 n cur HE12 HE34 ltac:(lia) ltac:(lia) ltac:(lia)).
split; [apply Z.ltb_lt; lia | exact I]. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_readdata) memc (seg_rom ubs2segs))) in HJ.
jrun LAWS ubs2tbl_ok HS HJ. { wr2 HE2 HEs. }
cbn [ms_mem mkst] in HF.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | exact Hh | exact Hl | exact HS | reflexivity | vm_compute; reflexivity |].
exists (ms_regs ms), (ms_mem ms).
split.
{ jreg HS (1%bv:reg) as X. rewrite (R1' ms); [rewrite Hra; reflexivity|]. rewrite X. reflexivity. }
split; [exact HJ|].
split.
{ apply (regs_preserved_of_st_ok ubs2segs _ _ ms regs extra HS HEA). vm_compute. reflexivity. }
split.
{ right. split; [lia|]. split.
{ jreg HS (10%bv:reg) as X. rewrite X. first [reflexivity | vm_compute; reflexivity]. }
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 _ st nb HS); [reflexivity | reflexivity
| cbn [r_chunks]; repeat first [left; reflexivity | right] | exact HEs | | lia].
cbn [sv_denot]. rewrite Z.add_0_r, HE33, unsigned_lit_small by lia. reflexivity. }
intros a Ha Hn1 Hn2 Hn3.
rewrite (mbyte_of_frame _ _ _ _ _ HF); [reflexivity | lia | rd_out HF; rewrite ?HE2, ?HEs; lia].
Qed.
End S.
End b.
