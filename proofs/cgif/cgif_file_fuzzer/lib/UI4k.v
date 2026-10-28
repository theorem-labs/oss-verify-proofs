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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 YI0r UI1w UI55 UI3w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 UI5c UI2z YI0j YI0k YI6c YI01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
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
Variables (IMGV LCTV : list Z).
Hypothesis FWRITE : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Definition RWDB_HEAD : Z := Eval vm_compute in PC_WDB.
Definition RWDB_EXIT : Z := Eval vm_compute in PC_WDBX.
Definition RWDB_CLOB : list reg := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 22; 28; 29; 30; 31]%bv.
Definition ss_rwdb : sstate :=
mkSS RWDB_HEAD (sr_set (sr_set sr_atoms 21%bv (SLit 0)) 20%bv (SLit ubs0_A_cgif_writecb))
[ YP09.mkRegion (Some 2%nat) 0 48 0 0 [mkChunk 47 (CVal 1 (SLit 0))] ;
YP09.mkRegion (Some 18%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 32 lits_CGIF) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + 8560) (2^47 - 128) 4);
(18%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4);
(22%nat, mkAF 1 65536 0) ] [] []).
Lemma frame_of_win' : forall E r rs m m' b (x : word),
frame_of E (r :: rs) m m' ->
forallb (fun r' => r_whi r' <=? r_wlo r') rs = true ->
base_val E (r_base r) = b ->
(bv_unsigned x < b + r_wlo r \/ b + r_whi r <= bv_unsigned x) -> m' x = m x.
Proof using.
intros E r rs m m' b x HF Hro Hb Hx. apply HF. intros (r' & [<-|Hin] & Ha); [lia|].
pose proof (proj1 (forallb_forall _ _) Hro r' Hin) as H. cbn beta in H. apply Z.leb_le in H. lia.
Qed.
Lemma rwdb_kept_in : forall r : reg, reg_in r RWDB_CLOB = false -> r = 0%bv \/ r = 20%bv \/
In r ([2; 3; 4; 8; 9; 18; 19; 23; 24; 25; 26; 27]%bv : list reg).
Proof using.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | vm_compute in Hr; discriminate | right; right; cbv; tauto] |]).
destruct Hin.
Qed.
Lemma rwdb_loop : forall (k : nat) (n : Z) regs memc STK sp0 FP L A mem md Lc Ac mdc g gvals spc f (S : list Z),
Z.of_nat k = n -> 1 <= n <= 65536 ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
obj_at ubs0segs memc g LAY_CGIF gvals -> nth_error gvals CG_wfn = Some 0 -> nth_error gvals CG_file = Some f ->
4096 <= g -> g + CGIF_SIZE <= alloc_ceiling -> g mod 16 = 0 ->
In (g, CGIF_SIZE) (blocks Lc Ac) -> In (f, FILE_BLOCK) (blocks Lc Ac) -> (g + CGIF_SIZE <= f \/ f + FILE_BLOCK <= g) -> 4096 <= f -> f + FILE_BLOCK <= alloc_ceiling ->
(forall a, inFP (sink_fp f) a -> inFP FP a) ->
getr regs 2 = Z_to_bv 64 spc -> spc mod 16 = 0 -> alloc_ceiling + 8560 <= spc -> sp0 - STK <= spc - WRITECB_STK -> spc + 128 <= sp0 -> sp0 <= 2 ^ 47 ->
getr regs 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr regs 18 = Z_to_bv 64 g -> getr regs 21 = Z_to_bv 64 0 ->
getr regs 20 = Z_to_bv 64 ubs0_A_cgif_writecb -> getr regs 22 = Z_to_bv 64 n ->
val_mem ubs0segs memc (spc + 47) 1 0 ->
sink_at ubs0_msyms memc mdc f S -> Z.of_nat (length S) + n <= SINK_MAX ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 RWDB_HEAD) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 RWDB_EXIT) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' md' /\
(forall r, reg_in r RWDB_CLOB = false -> getr regs' r = getr regs r) /\
getr regs' 21 = Z_to_bv 64 0 /\ getr regs' 22 = Z_to_bv 64 0 /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - WRITECB_STK <= x < spc) -> mbyte ubs0segs mem' x = mbyte ubs0segs memc x) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> ~ inFP (sink_fp f) (b + i) -> mbyte ubs0segs mem' (b + i) = mbyte ubs0segs memc (b + i)) /\
sink_at ubs0_msyms mem' md' f (S ++ repeat 0 k)).
Proof using FWRITE IMG LAWS.
induction k as [|k IH]; intros n regs memc STK sp0 FP L A mem md Lc Ac mdc g gvals spc f S Hk Hn HJ Hobj Hwfn Hfile Hg0 Hg1 Hg16 Hgin Hfin Hgf Hf0 Hf1 HFPI
H2 Hal Hsplo Hlo Hhi H47 H4 H20 H21 H22 H23 V47 HSK Hroom; [lia|].
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HGS : CGIF_SIZE = 96) by reflexivity.
assert (HWv : WRITECB_STK = 528) by reflexivity.
assert (HFBv : FILE_BLOCK = 1264) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & H63' & Hstw) & _).
pose proof (obj_at_length _ _ _ _ _ Hobj) as LG.
cbn [length LAY_CGIF] in LG.
remember (Ereg regs (map (Z_to_bv 64) gvals ++ [])) as E eqn:HE0.
assert (HE2 : ew E 2 = Z_to_bv 64 spc) by (rewrite HE0, (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity); exact H2).
assert (HE2u : bv_unsigned (ew E 2) = spc) by (rewrite HE2; apply unsigned_lit_small; lia).
assert (HE20 : ew E 18 = Z_to_bv 64 g) by (rewrite HE0, (ew_Ereg_nat regs _ 18 18%bv) by (vm_compute; reflexivity); exact H20).
assert (HE23 : ew E 22 = Z_to_bv 64 n) by (rewrite HE0, (ew_Ereg_nat regs _ 22 22%bv) by (vm_compute; reflexivity); exact H23).
assert (HE4 : ew E 4 = Z_to_bv 64 (ms_tp ubs0_msyms)) by (rewrite HE0, (ew_Ereg_nat regs _ 4 4%bv) by (vm_compute; reflexivity); exact H4).
assert (HS : st_ok ubs0segs E ss_rwdb (mkst regs (Z_to_bv 64 RWDB_HEAD) memc (seg_rom ubs0segs))).
{
rewrite HE0.
apply entry_st_ok_full; rewrite <- ?HE0.
-
apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE0; apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H21] | intros X; discriminate X | cbn [sv_denot]; exact H22].
-
vm_compute.
reflexivity.
-
constructor; [|constructor; [|constructor]].
+
unfold region_ok.
cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE2u.
split; [lia|].
split; [lia|].
split; [intros o Ho; lia|].
constructor; [|constructor].
eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | exact V47].
+
eapply (region_ok_obj_gen ubs0segs _ memc 18 g); [ | lia | lia | exact Hobj | reflexivity | | apply (lits_CGIF_ok gvals Hwfn Hfile) | intros i Hi; lia].
*
rewrite HE20.
apply unsigned_lit_small.
lia.
*
intros j v Hj.
rewrite HE0.
apply Ereg_vals.
exact Hj.
-
cbn [pairwise_disjoint all_disjoint].
unfold extent_disjoint.
cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE20, !unsigned_lit_small by lia.
repeat split.
lia.
-
split; [|split; exact I].
cbn [f_atoms atoms_ok].
unfold afact_ok, AC.
cbn [af_lo af_hi af_al2].
rewrite HE2, HE20, HE23, !unsigned_lit_small by lia.
change (2 ^ 4) with 16.
change (2 ^ 0) with 1.
rewrite !Z.mod_1_r.
repeat split; lia.
}
change memc with (ms_mem (mkst regs (Z_to_bv 64 RWDB_HEAD) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_writecb.
{
apply wr_ok_cons_ro; [cbn; lia|].
apply wr_ok_cons_ro; [cbn; lia|].
apply wr_ok_nil.
}
jreg HS (10%bv:reg) as Wa10.
jreg HS (11%bv:reg) as Wa11.
jreg HS (12%bv:reg) as Wa12.
jreg HS (2%bv:reg) as Wa2.
jreg HS (4%bv:reg) as Wa4.
jreg HS (1%bv:reg) as Wa1.
rewrite HE20 in Wa10.
rewrite HE2u in Wa11.
rewrite HE2 in Wa2.
rewrite HE4 in Wa4.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => assert (Wsp : spZ (ms_regs msx) = spc) by (unfold spZ; rewrite Wa2; apply unsigned_lit_small; lia) end.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (MEQ1 : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs memc a) by (intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2u in H));
assert (Hobj1 : obj_at ubs0segs (ms_mem msx) g LAY_CGIF gvals) by (eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros i Hi; apply MEQ1; lia]);
assert (HSK1 : sink_at ubs0_msyms (ms_mem msx) mdc f S) by (apply (sink_at_frame ubs0_msyms memc _ mdc f S); [intros a Ha; apply MEQ1; destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia] | exact HSK]);
assert (HG1 : garr8 ubs0segs (ms_mem msx) (spc + 47) [0]) by (apply garr8_cons_val1; [eapply fb_kept1; [exact V47 | intros a Ha; apply MEQ1; cbn in Ha; lia] | lia | apply garr8_nil])
end.
eapply SR_bind.
{
eapply (jwrite ubs0_msyms MR LAWS ubs0_A_cgif_writecb (ubs0_cgif_writecb API IMG FWRITE))
with (g := g) (gvals := gvals) (src := spc + 47) (n := 1) (f := f) (S := S) (bs := [0]);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Wa1 | apply ret_ok_even; vm_compute; reflexivity
| exact Wa10 | exact Wa11 | exact Wa12 | rewrite Wsp; exact Hal | rewrite Wsp; lia | rewrite Wsp; lia | rewrite Wsp; lia
| exact Wa4 | exact Hobj1 | exact Hwfn | exact Hfile | exact Hgin | exact Hfin | exact HSK1 | exact HG1 | reflexivity
| lia | lia | lia | rewrite Wsp; lia | lia | lia | exact HFPI ].
}
cbv beta.
intros c' (regsW & memW & mdW & -> & HJW & HPW & Hr10W & HSKW & HhiW & HblkW).
rewrite Wsp in HhiW.
jafter_call2 HS 49%nat regsW memW HPW 0 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{
constructor; [|constructor; [|constructor]].
-
eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HE2u | exact HhiW | lia | lia | lia | cbn; lia | cbn; lia].
-
eapply (region_kept_pointwise ubs0segs _ _ _ 18); [rewrite HE20; apply unsigned_lit_small; lia | | cbn; lia].
cbn [r_lo r_hi].
intros a Ha.
replace a with (g + (a - g)) by lia.
apply (HblkW g CGIF_SIZE (a - g) Hgin); [lia|].
replace (g + (a - g)) with a by lia.
intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia.
}
clear HS.
rename HS2 into HS.
assert (PINR : forall segs E0 ss ms1 (r : reg) z, st_ok segs E0 ss ms1 -> getr (ms_regs ms1) r = Z_to_bv 64 z -> bv_eqb r 0 = false ->
st_ok segs E0 (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SLit z)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms1).
{
intros segs E0 ss ms1 r z HS0 Hr Hr0.
apply st_ok_regs; [exact HS0|].
intros rr.
destruct (decide (rr = r)) as [->|Hne].
-
rewrite sr_get_set_same by exact Hr0.
cbn [sv_denot].
rewrite <- (st_ok_reg segs E0 ss ms1 r HS0), Hr.
reflexivity.
-
rewrite sr_get_set_other by exact Hne.
reflexivity.
}
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
pose proof (PINR segs E1 ss1 ms1 (10%bv:reg) 0 HS ltac:(cbn [ms_regs]; exact Hr10W) eq_refl) as HSp;
let v := eval vm_compute in (mkSS (ss_pc ss1) (sr_set (ss_regs ss1) (10%bv:reg) (SLit 0)) (ss_mem ss1) (ss_resv ss1) (ss_facts ss1)) in
change (mkSS (ss_pc ss1) (sr_set (ss_regs ss1) (10%bv:reg) (SLit 0)) (ss_mem ss1) (ss_resv ss1) (ss_facts ss1)) with v in HSp;
clear HS; rename HSp into HS end.
lazymatch type of HS with st_ok _ _ _ ?msx => change memW with (ms_mem msx) in HJW end.
jrun LAWS ubs0tbl_ok HS HJW.
{
apply wr_ok_cons_ro; [cbn; lia|].
apply wr_ok_cons_ro; [cbn; lia|].
apply wr_ok_nil.
}
assert (KF_stk : forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - WRITECB_STK <= x < spc) -> mbyte ubs0segs memW x = mbyte ubs0segs memc x)
by (clear - HhiW MEQ1 Hac; intros x Hx Hnx; etransitivity; [apply (proj1 (HhiW x Hx Hnx)) | apply MEQ1; lia]).
assert (KF_blk : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> ~ inFP (sink_fp f) (b + i) -> mbyte ubs0segs memW (b + i) = mbyte ubs0segs memc (b + i)).
{
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJW) as HHW.
clear - HblkW MEQ1 HHW LAWS Hac.
intros b m i Hin Hi Hnf.
etransitivity; [apply (HblkW b m i Hin Hi Hnf)|].
apply MEQ1.
pose proof (heap_blocks_range ubs0_msyms MR LAWS Lc Ac _ _ b m HHW Hin ltac:(lia)).
lia.
}
jbranch ubs0tbl HS.
-
rewrite branch_ne_U, U_lit in Hc by lia.
rewrite (U_atom_off _ 22 n (-1)) in Hc by (first [ew_havoc; exact HE23 | lia]).
assert (Hn2 : 2 <= n) by (destruct (Z.eqb_spec (n + -1) 0); [discriminate | lia]).
clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJW RWDB_HEAD.
{
apply wr_ok_cons_ro; [cbn; lia|].
apply wr_ok_cons_ro; [cbn; lia|].
apply wr_ok_nil.
}
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 23; 24; 25; 26; 27]%bv HS
ltac:(apply env_agree_havoc_ge; [cbv; lia | rewrite HE0; apply env_agree_refl]) ltac:(vm_compute; reflexivity)) as HK2.
jreg HS (22%bv:reg) as Hn23.
ew_havoc.
rewrite HE23 in Hn23.
jreg HS (21%bv:reg) as Hn21.
jreg HS (20%bv:reg) as Hn22.
lazymatch type of HS with st_ok _ _ _ ?msx =>
cbn [ms_regs mkst] in HK2, Hn23, Hn21, Hn22;
assert (MEQ4 : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs memW a) by (intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2u in H))
end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl).
cbn [ss_pc].
eapply SR_mono.
{
eapply (IH (n - 1) _ _ STK sp0 FP L A mem md Lc Ac mdW g gvals spc f (S ++ [0]));
[ lia | lia | exact HJW | | exact Hwfn | exact Hfile | lia | lia | exact Hg16 | exact Hgin | exact Hfin | exact Hgf | exact Hf0 | exact Hf1 | exact HFPI
| rewrite HK2 by (cbv; tauto); exact H2 | exact Hal | exact Hsplo | exact Hlo | exact Hhi | exact H47
| rewrite HK2 by (cbv; tauto); exact H4 | rewrite HK2 by (cbv; tauto); exact H20 | exact Hn21 | exact Hn22
| rewrite Hn23, unsigned_lit_small by lia; f_equal; lia | | | rewrite length_app; cbn [length]; lia ].
-
eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) |].
intros i Hi.
cbn [ms_mem].
rewrite MEQ4 by lia.
apply (KF_blk g CGIF_SIZE i Hgin); [lia|].
intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia.
-
cbn [ms_mem].
eapply fb_kept1; [exact V47 | intros a Ha; cbn in Ha; rewrite MEQ4 by lia; apply KF_stk; lia].
-
cbn [ms_mem].
apply (sink_at_frame ubs0_msyms memW _ mdW f); [| exact HSKW].
intros a Ha.
apply MEQ4.
destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia].
}
cbv beta.
intros c' (regs3 & mem3 & md3 & -> & HJ3 & HK3 & H21' & H23' & Hout3 & Hblk3 & HSK3).
exists regs3, mem3, md3.
split; [reflexivity|].
split; [exact HJ3|].
split; [|split; [exact H21'|split; [exact H23'|split; [|split]]]].
+
intros r Hr.
rewrite (HK3 r Hr).
destruct (rwdb_kept_in r Hr) as [->|[->|Hin]]; [rewrite !getr_zero; reflexivity | rewrite Hn22, H22; reflexivity | apply HK2; exact Hin].
+
intros x Hx Hnx.
rewrite (Hout3 x Hx Hnx).
cbn [ms_mem].
rewrite MEQ4 by lia.
apply KF_stk; [exact Hx | exact Hnx].
+
intros b m i Hin Hi Hnf.
rewrite (Hblk3 b m i Hin Hi Hnf).
cbn [ms_mem].
pose proof (heap_blocks_range ubs0_msyms MR LAWS Lc Ac _ _ b m (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJW) Hin ltac:(lia)) as (Rb0 & Rb1 & _).
rewrite MEQ4 by lia.
apply (KF_blk b m i Hin Hi Hnf).
+
rewrite <- app_assoc in HSK3.
exact HSK3.
-
rewrite branch_ne_U, U_lit in Hc by lia.
rewrite (U_atom_off _ 22 n (-1)) in Hc by (first [ew_havoc; exact HE23 | lia]).
assert (Hn1 : n = 1) by (destruct (Z.eqb_spec (n + -1) 0); [lia | discriminate]).
clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJW RWDB_EXIT.
{
apply wr_ok_cons_ro; [cbn; lia|].
apply wr_ok_cons_ro; [cbn; lia|].
apply wr_ok_nil.
}
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 23; 24; 25; 26; 27]%bv HS
ltac:(apply env_agree_havoc_ge; [cbv; lia | rewrite HE0; apply env_agree_refl]) ltac:(vm_compute; reflexivity)) as HK2.
jreg HS (22%bv:reg) as Hn23.
rewrite HE23, unsigned_lit_small in Hn23 by lia.
jreg HS (21%bv:reg) as Hn21.
jreg HS (20%bv:reg) as Hn22.
lazymatch type of HS with st_ok _ _ _ ?msx =>
cbn [ms_regs mkst] in HK2, Hn23, Hn21, Hn22;
assert (MEQ4 : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs memW a) by (intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2u in H))
end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl).
cbn [ss_pc].
apply SR_ret.
eexists _, _, mdW.
split; [reflexivity|].
split; [exact HJW|].
split; [|split; [exact Hn21 | split; [rewrite Hn23; f_equal; lia | split; [|split]]]].
+
intros r Hr.
destruct (rwdb_kept_in r Hr) as [->|[->|Hin]]; [rewrite !getr_zero; reflexivity | rewrite Hn22, H22; reflexivity | apply HK2; exact Hin].
+
intros x Hx Hnx.
cbn [ms_mem].
rewrite MEQ4 by lia.
apply KF_stk; [exact Hx | exact Hnx].
+
intros b m i Hin Hi Hnf.
cbn [ms_mem].
pose proof (heap_blocks_range ubs0_msyms MR LAWS Lc Ac _ _ b m (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJW) Hin ltac:(lia)) as (Rb0 & Rb1 & _).
rewrite MEQ4 by lia.
apply (KF_blk b m i Hin Hi Hnf).
+
cbn [ms_mem].
subst n.
replace k with 0%nat by lia.
cbn [repeat].
apply (sink_at_frame ubs0_msyms memW _ mdW f); [| exact HSKW].
intros a Ha.
apply MEQ4.
destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia].
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
