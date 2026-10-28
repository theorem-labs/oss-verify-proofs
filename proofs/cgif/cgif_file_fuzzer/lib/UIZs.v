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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r
YI00 YI05 YI5a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05 YI6c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition RD_FRAME : Z := 32.
Lemma region_kept_rd : forall E (mem mem' : word -> option byte) r spc d n st,
(forall x : word, ~ (spc - RD_FRAME <= bv_unsigned x < spc) -> ~ (d <= bv_unsigned x < d + n) ->
~ (st + 16 <= bv_unsigned x < st + 24) -> mem' x = mem x) ->
mem_grows mem mem' ->
0 <= base_val E (r_base r) + r_lo r -> base_val E (r_base r) + r_hi r <= 2 ^ 64 ->
(base_val E (r_base r) + r_hi r <= spc - RD_FRAME \/ spc <= base_val E (r_base r) + r_lo r) ->
(base_val E (r_base r) + r_hi r <= d \/ d + n <= base_val E (r_base r) + r_lo r) ->
(base_val E (r_base r) + r_hi r <= st + 16 \/ st + 24 <= base_val E (r_base r) + r_lo r) ->
r_lo r <= r_wlo r -> r_whi r <= r_hi r ->
region_kept ubs0segs E mem mem' r.
Proof using.
intros E mem mem' r spc d n st Hout Hgr Hlo Hhi H1 H2 H3 Hw1 Hw2. split; intros a Ha.
- unfold mbyte. rewrite (Hout (Z_to_bv 64 a)); [reflexivity | rewrite unsigned_lit_small by lia; lia ..].
- apply (writable_at_grows ubs0segs mem mem'); assumption.
Qed.
Definition ss_rd : sstate :=
mkSS ubs0_A_readdata sr_atoms
[ YP09.mkRegion (Some 2%nat) (-RD_FRAME) 0 (-RD_FRAME) 0 [] ;
YP09.mkRegion (Some 10%nat) 0 24 16 24 [mkChunk 0 (CVal 8 (SOff 32 0)); mkChunk 8 (CVal 8 (SOff 33 0)); mkChunk 16 (CVal 8 (SOff 34 0))] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + RD_FRAME) (2^63) 4); (10%nat, mkAF 0 (2^64 - 25) 3) ] [] []).
Definition kept2 (lo1 hi1 lo2 hi2 : Z) (m m0 : word -> option byte) : Prop :=
forall x : word, ~ (lo1 <= bv_unsigned x < hi1) -> ~ (lo2 <= bv_unsigned x < hi2) -> m x = m0 x.
Lemma kept2_step : forall E rs (m0 m1 m2 : word -> option byte) lo1 hi1 lo2 hi2,
kept2 lo1 hi1 lo2 hi2 m1 m0 -> frame_of E rs m1 m2 ->
(forall r, In r rs -> forall a, base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r -> lo1 <= a < hi1 \/ lo2 <= a < hi2) ->
kept2 lo1 hi1 lo2 hi2 m2 m0.
Proof using.
intros E rs m0 m1 m2 lo1 hi1 lo2 hi2 HP HF Hc x H1 H2. rewrite <- (HP x H1 H2). apply HF.
intros (r & Hr & Ha). destruct (Hc r Hr _ Ha); tauto.
Qed.
Lemma denot_add_rd : forall E a b x y,
ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= x + y < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (x + y).
Proof using.
intros E a b x y Ha Hb Hx Hy Hxy. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E a x Ha), (U_atom E b y Hb) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Ltac rd_cover HU2 HU10 :=
let r := fresh "r" in let Hr := fresh "Hr" in let a := fresh "a" in let Ha := fresh "Ha" in
intros r Hr a Ha; cbv [In] in Hr;
repeat (destruct Hr as [<-|Hr]; [cbn [r_base r_wlo r_whi base_val] in Ha; repeat (rewrite ew_havoc_old in Ha; [|cbv; lia]);
rewrite ?HU2, ?HU10 in Ha; lia|]); destruct Hr.
Ltac rd_step HP HGr HU2 HU10 :=
repeat match goal with HF : frame_of _ _ _ _ |- _ => progress cbn [ms_mem mkst] in HF end;
repeat match goal with HG : mem_grows _ _ |- _ => progress cbn [ms_mem mkst] in HG end;
lazymatch type of HP with kept2 ?l1 ?h1 ?l2 ?h2 ?m1 ?m0 =>
lazymatch goal with HF : frame_of ?E1 ?rs m1 ?m2 |- _ =>
let HP2 := fresh "HP" in
pose proof (kept2_step E1 rs m0 m1 m2 l1 h1 l2 h2 HP HF ltac:(rd_cover HU2 HU10)) as HP2; clear HP HF; rename HP2 into HP end end;
lazymatch type of HGr with mem_grows ?m0 ?m1 =>
lazymatch goal with HG : mem_grows m1 ?m2 |- _ =>
let HG2 := fresh "HGr" in
pose proof (mem_grows_trans m0 m1 m2 HGr HG) as HG2; clear HGr HG; rename HG2 into HGr end end.
Ltac rd_wr HU2 HU10 Hcw :=
wr_norm; eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_gen; [reflexivity | ew_havoc; exact HU10 | cbn [r_wlo r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hcw; lia |]; apply wr_ok_nil.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Lemma wr_byte_writable : forall STK sp0 FP L A mem md Lc Ac memc mdc a,
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a -> writable_at ubs0segs memc a.
Proof using LAWS.
intros STK sp0 FP L A mem md Lc Ac memc mdc a HJ Hw.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
destruct (wr_byte_low _ _ LAWS _ _ _ _ _ _ _ _ _ _ HH Hw) as [Hs | (_ & _ & b & m & Hin & Hr & _)].
- exact (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Hs).
- destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m (a - b) HH Hin ltac:(lia)) as (Hp & _).
replace (b + (a - b)) with a in Hp by lia. exact (present_writable ubs0_msyms _ _ Hp).
Qed.
Lemma jreaddata :
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc (st d n pdata nb cur spc : Z) raw,
st_ok ubs0segs E ss ms -> ss_pc ss = ubs0_A_readdata -> ss_resv ss = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 10 = Z_to_bv 64 st -> getr (ms_regs ms) 11 = Z_to_bv 64 d -> getr (ms_regs ms) 12 = Z_to_bv 64 n ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> spc mod 16 = 0 -> sp0 - STK <= spc - RD_FRAME -> spc <= sp0 -> sp0 < 2 ^ 63 ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
0 <= st -> st + 24 < 2 ^ 64 -> st mod 8 = 0 ->
word_mem ubs0segs (ms_mem ms) st pdata -> word_mem ubs0segs (ms_mem ms) (st + 8) nb ->
word_mem ubs0segs (ms_mem ms) (st + 16) cur ->
0 <= n -> 0 <= cur <= nb -> nb + n < 2 ^ 64 -> 0 <= pdata -> pdata + nb < 2 ^ 64 -> (pdata = 0 -> nb = 0) ->
(forall j, 0 <= j < nb -> present (ms_mem ms) (pdata + j)) ->
0 <= d -> d + n < 2 ^ 64 ->
(forall i, 0 <= i < n -> present (ms_mem ms) (d + i)) ->
(forall a, d <= a < d + n -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a) ->
(forall a, st + 16 <= a < st + 24 -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a) ->
(st + 24 <= spc - RD_FRAME \/ spc <= st) ->
(d + n <= spc - RD_FRAME \/ spc <= d) ->
(0 < nb -> pdata + nb <= spc - RD_FRAME \/ spc <= pdata) ->
(0 < nb -> pdata + nb <= st \/ st + 24 <= pdata) ->
(d + n <= st \/ st + 24 <= d) ->
(0 < nb -> d + n <= pdata \/ pdata + nb <= d) ->
SR ubs0segs (mkCfg ms mdc)
(fun c' => exists regs2 mem2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
regs_preserved (ms_regs ms) regs2 /\
(forall x : word, ~ (spc - RD_FRAME <= bv_unsigned x < spc) -> ~ (d <= bv_unsigned x < d + n) ->
~ (st + 16 <= bv_unsigned x < st + 24) -> mem2 x = ms_mem ms x) /\
mem_grows (ms_mem ms) mem2 /\
((cur + n <= nb /\ getr regs2 10 = Z_to_bv 64 0 /\ word_mem ubs0segs mem2 (st + 16) (cur + n) /\
(forall i, 0 <= i < n -> mbyte ubs0segs mem2 (d + i) = mbyte ubs0segs (ms_mem ms) (pdata + cur + i))) \/
(nb < cur + n /\ getr regs2 10 = Z_to_bv 64 (2 ^ 64 - 1) /\ word_mem ubs0segs mem2 (st + 16) nb /\
(forall i, 0 <= i < n -> mbyte ubs0segs mem2 (d + i) = mbyte ubs0segs (ms_mem ms) (d + i))))).
Proof using IMG LAWS.
intros E0 ss ms STK sp0 FP L A mem md Lc Ac mdc st d n pdata nb cur spc raw HS0 Hpc Hrv HJ G10 G11 G12 G2 Hal16 Hlo Hhi H63 G1 Hraw
Hst0 Hst1 Hst8 Wp Wn Wc Hn Hcur Hnbn Hp0 Hp1 Hpz Hpres Hd0 Hd1 Hdpres Hdw Hcw Hsf Hdf Hpf Hps Hds Hdp.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HRD : RD_FRAME = 32) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
rewrite (st_ok_mkst ubs0segs _ _ _ HS0 Hrv), Hpc. clear HS0 Hpc Hrv E0 ss.
set (E := Ereg (ms_regs ms) [Z_to_bv 64 pdata; Z_to_bv 64 nb; Z_to_bv 64 cur]).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr (ms_regs ms) rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = spc) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = st) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HX32 : ew E 32 = Z_to_bv 64 pdata) by reflexivity.
assert (HX33 : ew E 33 = Z_to_bv 64 nb) by reflexivity.
assert (HX34 : ew E 34 = Z_to_bv 64 cur) by reflexivity.
assert (HS : st_ok ubs0segs E ss_rd (mkst (ms_regs ms) (Z_to_bv 64 ubs0_A_readdata) (ms_mem ms) (seg_rom ubs0segs))).
{ unfold ss_rd. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs0segs _ (ms_mem ms) 2 spc); [exact HU2 | lia | lia |].
intros a Ha. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (wr_byte_writable _ _ _ _ _ _ _ _ _ _ _ _ HJ). apply Hcw. lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX34, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10. repeat split; lia.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
repeat split; lia. }
assert (HP : kept2 (spc - RD_FRAME) spc (st + 16) (st + 24) (ms_mem ms) (ms_mem ms)) by (intros x _ _; reflexivity).
pose proof (mem_grows_refl (ms_mem ms)) as HGr.
change (ms_mem ms) with (ms_mem (mkst (ms_regs ms) (Z_to_bv 64 ubs0_A_readdata) (ms_mem ms) (seg_rom ubs0segs))) in HJ.
jrun LAWS ubs0tbl_ok HS HJ. { rd_wr HU2 HU10 Hcw. }
rd_step HP HGr HU2 HU10.
jbranch ubs0tbl HS.
- rewrite branch_geu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
rewrite (U_atom E 33 nb HX33), (U_atom E 12 n), (U_atom E 34 cur HX34) in Hc by (try rewrite (HE 12%nat 12%bv eq_refl), G12; try reflexivity; lia).
rewrite zcanon_id in Hc by (unfold M64; lia).
assert (Hok : cur + n <= nb) by (destruct (Z.ltb_spec nb (n + cur)); [discriminate | lia]). clear Hc.
jrun LAWS ubs0tbl_ok HS HJ. { rd_wr HU2 HU10 Hcw. }
rd_step HP HGr HU2 HU10.
jbranch ubs0tbl HS.
{ exfalso. rewrite branch_ltu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
rewrite (U_atom E 32 pdata HX32), (U_atom E 34 cur HX34) in Hc by lia.
rewrite zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc. lia. }
clear Hc.
jrun LAWS ubs0tbl_ok HS HJ. { rd_wr HU2 HU10 Hcw. }
rd_step HP HGr HU2 HU10.
jbranch ubs0tbl HS.
{ exfalso. rewrite branch_eq_U, !U_SAlu, (U_atom E 32 pdata HX32), (U_atom E 34 cur HX34), !U_SLit in Hc by lia.
cbn [zalu_raw] in Hc. rewrite (zcanon_id (pdata + cur)) in Hc by (unfold M64; lia).
rewrite ?(zcanon_id 0), ?(zcanon_id 1) in Hc by (unfold M64; lia).
destruct (Z.eq_dec pdata 0) as [Hz|Hnz].
- assert (Hnb0 : nb = 0) by (apply Hpz; exact Hz).
replace (0 <? pdata) with false in Hc by (symmetry; apply Z.ltb_ge; lia).
replace (pdata + cur <? 1) with true in Hc by (symmetry; apply Z.ltb_lt; lia).
vm_compute in Hc. discriminate Hc.
- replace (0 <? pdata) with true in Hc by (symmetry; apply Z.ltb_lt; lia).
replace (pdata + cur <? 1) with false in Hc by (symmetry; apply Z.ltb_ge; lia).
vm_compute in Hc. discriminate Hc. }
clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_memcpy. { rd_wr HU2 HU10 Hcw. }
rd_step HP HGr HU2 HU10.
assert (Hnb : 0 < nb \/ n = 0) by lia.
jreg HS (10%bv:reg) as Ha0. rewrite (HE 11%nat 11%bv eq_refl), G11 in Ha0.
jreg HS (12%bv:reg) as Ha2. rewrite (HE 12%nat 12%bv eq_refl), G12 in Ha2.
jreg HS (1%bv:reg) as Hra1.
pose proof (st_ok_reg ubs0segs _ _ _ 11%bv HS) as Ha1. eval_sr_get_in Ha1.
rewrite (denot_add_rd E 32 34 pdata cur HX32 HX34) in Ha1 by lia.
eapply SR_bind.
{ eapply (jmemcpy _ _ LAWS IMG _ ubs0_memcpy) with (d := d) (src := pdata + cur) (n := n);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Ha0 | exact Ha1 | exact Ha2 | exact Hra1
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | | ].
- intros i Hi. eapply present_grows; [exact HGr|]. apply Hdpres. exact Hi.
- intros i Hi. eapply present_grows; [exact HGr|]. replace (pdata + cur + i) with (pdata + (cur + i)) by lia. apply Hpres. lia.
- destruct (Z.eq_dec n 0) as [Hn0|Hn0]; [lia|]. destruct (Hdp ltac:(lia)); lia.
- exact Hdw. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hr10m & Hfr2 & Hout2 & Hgr2 & Hcp2).
change (ms_segs ubs0_msyms) with ubs0segs in Hcp2.
jafter_stretch HS 35%nat regs2 mem2 (10%bv :: MEMCPY_CLOB) (ubs0_A_readdata + 0x64) HS2.
match type of HS2 with ?P -> ?Q -> _ =>
assert (HQ1 : P); [intros rr Hrr; apply Hfr2; exact (reg_in_cons_false _ _ _ Hrr)|];
assert (HQ2 : Q); [| specialize (HS2 HQ1 HQ2); clear HQ1 HQ2] end.
{ constructor; [|constructor; [|constructor]];
eapply (region_kept_outside _ _ _ _ _ d n Hout2 Hgr2); cbn [r_base r_lo r_hi r_wlo r_whi base_val]; rewrite ?HU2, ?HU10; lia. }
rename HP into HPa.
assert (HP : kept2 (spc - RD_FRAME) spc (st + 16) (st + 24) mem2 mem2) by (intros x _ _; reflexivity).
pose proof (mem_grows_trans _ _ _ HGr Hgr2) as HGr2. clear HGr Hgr2. rename HGr2 into HGr.
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (ubs0_A_readdata + 0x64)) mem2 (seg_rom ubs0segs))) in HJ2.
jrun LAWS ubs0tbl_ok HS HJ2. { rd_wr HU2 HU10 Hcw. }
rd_step HP HGr HU2 HU10.
jreg HS (1%bv:reg) as Hr1. rewrite (HE 1%nat 1%bv eq_refl), G1 in Hr1.
jreg HS (10%bv:reg) as Hr10.
pose proof (regs_preserved_of_st_ok _ _ _ _ (ms_regs ms) [Z_to_bv 64 pdata; Z_to_bv 64 nb; Z_to_bv 64 cur] HS
ltac:(first [apply env_agree_refl | apply env_agree_havoc_ge; [lia | apply env_agree_refl]]) ltac:(vm_compute; reflexivity)) as HPR.
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)))). }
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx) end.
split. { rewrite Hr1. unfold YK0s.ret_ok in Hraw. rewrite Hraw. reflexivity. }
split; [exact HJ2|]. split; [exact HPR|].
split. { intros x H1 H2 H3. rewrite (HP x H1 H3), Hout2 by lia. apply HPa; assumption. }
split; [exact HGr|].
left. split; [exact Hok|]. split; [rewrite Hr10; reflexivity|]. split.
+ replace (cur + n) with (n + cur) by lia. apply (proj1 (val_mem_word_mem ubs0segs _ _ _)).
eapply (vval_mem_of_chunk ubs0segs _ _ _ 10%nat st 16 8%N (SAlu ALU_ADD (SOff 12 0) (SOff 34 0)) (n + cur));
[eapply (vst_ok_region_nth ubs0segs _ _ _ 1 _ HS); reflexivity | reflexivity
| first [cbv; auto 20 | cbn; repeat (first [left; reflexivity | right])] | ew_havoc; exact HU10
| apply denot_add_rd; [ew_havoc; rewrite (HE 12%nat 12%bv eq_refl); exact G12 | ew_havoc; exact HX34 | lia | lia | lia]
| cbn; lia | cbn; lia].
+ intros i Hi. assert (Hnb0 : 0 < nb) by lia. specialize (Hpf Hnb0). specialize (Hps Hnb0).
transitivity (mbyte ubs0segs mem2 (d + i)).
{ apply (mbyte_eq_of ubs0_msyms). apply HP; rewrite unsigned_lit_small by lia; lia. }
rewrite Hcp2 by lia. apply (mbyte_eq_of ubs0_msyms). apply HPa; rewrite unsigned_lit_small by lia; lia.
- rewrite branch_geu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
rewrite (U_atom E 33 nb HX33), (U_atom E 12 n), (U_atom E 34 cur HX34) in Hc by (try rewrite (HE 12%nat 12%bv eq_refl), G12; try reflexivity; lia).
rewrite zcanon_id in Hc by (unfold M64; lia).
assert (Hfail : nb < cur + n) by (destruct (Z.ltb_spec nb (n + cur)); [lia | discriminate]). clear Hc.
jrun LAWS ubs0tbl_ok HS HJ. { rd_wr HU2 HU10 Hcw. }
rd_step HP HGr HU2 HU10.
jreg HS (1%bv:reg) as Hr1. rewrite (HE 1%nat 1%bv eq_refl), G1 in Hr1.
jreg HS (10%bv:reg) as Hr10.
pose proof (regs_preserved_of_st_ok _ _ _ _ (ms_regs ms) [Z_to_bv 64 pdata; Z_to_bv 64 nb; Z_to_bv 64 cur] HS
ltac:(first [apply env_agree_refl | apply env_agree_havoc_ge; [lia | apply env_agree_refl]]) ltac:(vm_compute; reflexivity)) as HPR.
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx) end.
split. { rewrite Hr1. unfold YK0s.ret_ok in Hraw. rewrite Hraw. reflexivity. }
split; [exact HJ|]. split; [exact HPR|]. split; [intros x H1 _ H3; apply HP; assumption|]. split; [exact HGr|].
right. split; [exact Hfail|]. split; [rewrite Hr10; first [reflexivity | apply bv_eq; vm_compute; reflexivity]|]. split.
+ apply (proj1 (val_mem_word_mem ubs0segs _ _ _)).
eapply (vval_mem_of_chunk ubs0segs _ _ _ 10%nat st 16 8%N (SOff 33 0) nb);
[eapply (vst_ok_region_nth ubs0segs _ _ _ 1 _ HS); reflexivity | reflexivity
| first [cbv; auto 20 | cbn; repeat (first [left; reflexivity | right])] | exact HU10
| cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia].
+ intros i Hi. apply (mbyte_eq_of ubs0_msyms). apply HP; rewrite unsigned_lit_small by lia; lia.
Qed.
End S.
End e.
