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
YI00 YI02 YI01 YI07 YI03 YI04 YI06 YI5a.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05 UIYs UIYu.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Theorem ubs2_resetDict : reset_spec API.
Proof using IMG LAWS.
unfold reset_spec.
intros L A regs mem md g ti lm lc li ld Lld idl lp HPRE H10 H11 Hidl Hlp HLld Bg Bti Blm Blc Bli Bld HND Vti Vlm Vlc Vli Vld Vlp.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof alloc_ceiling_val as Hac.
assert (HSTKv : RESET_STK = 16) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
assert (Htisz : 8 <= 2 * idl * idl <= 131072) by nia.
destruct (heap_blocks_range ubs2_msyms MR LAWS L A mem md g 72 HH Bg ltac:(lia)) as (Rg1 & Rg2 & Rg3).
destruct (heap_blocks_range ubs2_msyms MR LAWS L A mem md ti (2 * idl * idl) HH Bti ltac:(lia)) as (Rti1 & Rti2 & Rti3).
destruct (heap_blocks_range ubs2_msyms MR LAWS L A mem md lm 8192 HH Blm ltac:(lia)) as (Rlm1 & Rlm2 & Rlm3).
destruct (heap_blocks_range ubs2_msyms MR LAWS L A mem md lc 4096 HH Blc ltac:(lia)) as (Rlc1 & Rlc2 & Rlc3).
destruct (heap_blocks_range ubs2_msyms MR LAWS L A mem md li 8192 HH Bli ltac:(lia)) as (Rli1 & Rli2 & Rli3).
destruct (heap_blocks_range ubs2_msyms MR LAWS L A mem md ld Lld HH Bld ltac:(lia)) as (Rld1 & Rld2 & Rld3).
assert (Pblk : forall d n i, In (d, n) (blocks L A) -> 0 <= i < n -> writable_at ubs2segs mem (d + i)).
{ intros d n i Hin Hi. apply (present_writable ubs2_msyms).
  exact (proj1 (heap_blocks ubs2_msyms MR LAWS L A mem md d n i HH Hin Hi)). }
assert (Pres : forall d n i, In (d, n) (blocks L A) -> 0 <= i < n -> present mem (d + i)).
{ intros d n i Hin Hi. exact (proj1 (heap_blocks ubs2_msyms MR LAWS L A mem md d n i HH Hin Hi)). }
pose proof (rst_nodup6 g ti lm lc li ld HND) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
assert (SEP : forall x nx y ny, In (x, nx) (blocks L A) -> In (y, ny) (blocks L A) -> x <> y -> rst_sep x nx y ny).
{ intros x nx y ny Hx Hy Hne. unfold rst_sep.
  pose proof (heap_sep_in2 ubs2_msyms MR LAWS L A mem md (x, nx) (y, ny) HH Hx Hy ltac:(congruence)) as Hs.
  cbn [fst snd] in Hs. exact Hs. }
pose proof (SEP _ _ _ _ Bg Bti N1) as S_g_ti. pose proof (SEP _ _ _ _ Bg Blm N2) as S_g_lm.
pose proof (SEP _ _ _ _ Bg Blc N3) as S_g_lc. pose proof (SEP _ _ _ _ Bg Bli N4) as S_g_li.
pose proof (SEP _ _ _ _ Bg Bld N5) as S_g_ld. pose proof (SEP _ _ _ _ Bti Blm N6) as S_ti_lm.
pose proof (SEP _ _ _ _ Bti Blc N7) as S_ti_lc. pose proof (SEP _ _ _ _ Bti Bli N8) as S_ti_li.
pose proof (SEP _ _ _ _ Bti Bld N9) as S_ti_ld. pose proof (SEP _ _ _ _ Blm Blc N10) as S_lm_lc.
pose proof (SEP _ _ _ _ Blm Bli N11) as S_lm_li. pose proof (SEP _ _ _ _ Blm Bld N12) as S_lm_ld.
pose proof (SEP _ _ _ _ Blc Bli N13) as S_lc_li. pose proof (SEP _ _ _ _ Blc Bld N14) as S_lc_ld.
pose proof (SEP _ _ _ _ Bli Bld N15) as S_li_ld.
clear SEP N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12 N13 N14 N15.
Ltac us H := let H' := fresh "Hs" in pose proof H as H'; unfold rst_sep in H'.
set (E := Ereg regs (map (Z_to_bv 64) [ti; lm; lc; li; ld; lp; ld + 2 * lp] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error [ti; lm; lc; li; ld; lp; ld + 2 * lp] j = Some v -> ew E (32 + j) = Z_to_bv 64 v)
  by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HE32 : ew E 32 = Z_to_bv 64 ti) by (apply (HX 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 lm) by (apply (HX 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 lc) by (apply (HX 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 li) by (apply (HX 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 ld) by (apply (HX 4%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 lp) by (apply (HX 5%nat); reflexivity).
assert (HE38 : ew E 38 = Z_to_bv 64 (ld + 2 * lp)) by (apply (HX 6%nat); reflexivity).
assert (HE10 : ew E 10 = Z_to_bv 64 g) by (rewrite (HE 10%nat 10%bv eq_refl); exact H10).
assert (HE11 : ew E 11 = Z_to_bv 64 idl) by (rewrite (HE 11%nat 11%bv eq_refl); exact H11).
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok ubs2segs E ss_rst (mkst regs (Z_to_bv 64 ubs2_A_resetDict) mem (seg_rom ubs2segs))).
{ unfold ss_rst. subst E. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (region_ok_stack ubs2segs _ mem 2 sp0); [exact HU2 | lia | lia | intros a Ha; apply Hstw; lia].
    + unfold region_ok, rst_greg. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
      rewrite HE10, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply (Pblk g 72); [exact Bg | lia]|].
      unfold rst_gchunks.
      Ltac rck S HEn := eapply chunk_ok_val;
        [ cbn [sv_denot]; rewrite HEn, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
        | cbn; lia | cbn; lia | first [exact S | rewrite Z.add_0_r; exact S] ].
      constructor; [rck Vti HE32|]. constructor; [rck Vlm HE33|]. constructor; [rck Vlc HE34|].
      constructor; [rck Vli HE35|]. constructor; [rck Vld HE36|]. constructor; [rck Vlp HE37|]. constructor.
    + apply (region_ok_regw _ _ mem 38 2 (ld + 2 * lp) HE38); [lia | lia | lia |].
      intros o Ho. replace (ld + 2 * lp + o) with (ld + (2 * lp + o)) by lia. apply (Pblk ld Lld); [exact Bld | lia].
  - cbv [rst_stk rst_greg rst_slot regw]. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
    rewrite HU2, HE10, HE38, !unsigned_lit_small by lia.
    us S_g_ld. repeat split; lia.
  - split; [|split].
    + cbn [f_atoms]. unfold rst_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite HU2, HE10, HE11, HE36, HE37, HE38, !unsigned_lit_small by lia.
      change (2 ^ 4) with 16. change (2 ^ 1) with 2. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      repeat split; lia.
    + cbn [f_conds]. unfold rst_conds. cbn [conds_ok]. split; [|exact I].
      apply (cond_geu _ 38 0 36 0 (ld + 2 * lp) ld HE38 HE36); lia.
    + cbn [f_alias]. unfold rst_alias. cbn [alias_ok]. split; [|exact I].
      apply (alias_b2i' _ 36 37 38 ld lp HE36 HE37 HE38); lia. }
set (FP := [(g + 60, g + 68); (ld + 2 * lp, ld + 2 * lp + 2); (ti, ti + 2 * idl * idl); (lm, lm + 8192); (lc, lc + 4096); (li, li + 8192)]).
pose proof (journal_init ubs2_msyms MR RESET_STK FP L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_resetDict) mem (seg_rom ubs2segs))) in HJ.
fold sp0 in HJ.
assert (FPg : forall a, g + 60 <= a < g + 68 -> inFP FP a)
  by (intros a Ha; exists (g + 60, g + 68); split; [unfold FP; cbn [In]; left; reflexivity | cbn [fst snd]; lia]).
assert (FPs : forall a, ld + 2 * lp <= a < ld + 2 * lp + 2 -> inFP FP a)
  by (intros a Ha; exists (ld + 2 * lp, ld + 2 * lp + 2); split; [unfold FP; cbn [In]; right; left; reflexivity | cbn [fst snd]; lia]).
assert (FPti : forall a, ti <= a < ti + 2 * idl * idl -> inFP FP a)
  by (intros a Ha; exists (ti, ti + 2 * idl * idl); split; [unfold FP; cbn [In]; right; right; left; reflexivity | cbn [fst snd]; lia]).
assert (FPlm : forall a, lm <= a < lm + 8192 -> inFP FP a)
  by (intros a Ha; exists (lm, lm + 8192); split; [unfold FP; cbn [In]; right; right; right; left; reflexivity | cbn [fst snd]; lia]).
assert (FPlc : forall a, lc <= a < lc + 4096 -> inFP FP a)
  by (intros a Ha; exists (lc, lc + 4096); split; [unfold FP; cbn [In]; right; right; right; right; left; reflexivity | cbn [fst snd]; lia]).
assert (FPli : forall a, li <= a < li + 8192 -> inFP FP a)
  by (intros a Ha; exists (li, li + 8192); split; [unfold FP; cbn [In]; right; right; right; right; right; left; reflexivity | cbn [fst snd]; lia]).
Ltac rwr HU2 HE10 HE38 HSTKv Bg Bld FPg FPs g ld lp :=
  wr_norm;
  eapply wr_ok_cons_stack; [reflexivity | ew_havoc; exact HU2 | rewrite HSTKv; cbn; lia | cbn; lia |];
  eapply (wr_ok_cons_block _ _ _ _ _ _ _ _ 10%nat g 72);
  [reflexivity | ew_havoc; rewrite HE10; apply unsigned_lit_small; lia | exact Bg | cbn; lia | cbn; lia
  | cbn [r_wlo r_whi]; intros ? ?; apply FPg; lia |];
  eapply (wr_ok_cons_inblock _ _ _ _ _ _ _ _ 38%nat (ld + 2 * lp) ld);
  [reflexivity | ew_havoc; rewrite HE38; apply unsigned_lit_small; lia | exact Bld | cbn; lia | cbn; lia
  | cbn [r_wlo r_whi]; intros ? ?; apply FPs; lia |];
  apply wr_ok_nil.
Ltac rms HS HJ HEd d n Bd FPd Pres M12tac :=
  let M10 := fresh "M10" in let M11 := fresh "M11" in let M1 := fresh "M1" in let M12 := fresh "M12" in
  jreg HS (10%bv:reg) as M10; jreg HS (11%bv:reg) as M11; jreg HS (1%bv:reg) as M1;
  lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
  assert (M12 : getr (ms_regs ms1) 12 = Z_to_bv 64 n) by M12tac;
  eapply SR_bind;
  [ eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset rst_memset_spec E1 ss1 ms1 RESET_STK _ _ _ _ _ _ _ _ _ d 0 n);
    [ exact HS | reflexivity | reflexivity | exact HJ | rewrite M10; exact HEd | rewrite M11; reflexivity | exact M12 | exact M1
    | apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia
    | let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
      repeat (cbn [ms_mem mkst]; match goal with HG : mem_grows _ ?m' |- present ?m' _ => apply (present_grows _ _ _ HG) end);
      apply (Pres d n); [exact Bd | exact Hi]
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      right; left; split; [apply FPd; exact Ha | exists d, n; split; [exact Bd | exact Ha]] ]
  | ] end; clear M10 M11 M1 M12.
Ltac rsx HS k regs2 mem2 pc Hregs Hout Hgr S1 S2 HU2 HE10 HE38 :=
  let HS2 := fresh "HS" in
  jafter_stretch HS k regs2 mem2 MEMSET_CLOB pc HS2;
  specialize (HS2 Hregs);
  let HK := fresh "HK" in
  match type of HS2 with ?P -> _ => assert (HK : P) end;
  [ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
    (eapply region_kept_outside; [exact Hout | exact Hgr | | | | cbn; lia | cbn; lia]);
    cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite ?HU2, ?HE10, ?HE38, ?unsigned_lit_small by lia;
    first [lia | us S1; lia | us S2; lia]
  | specialize (HS2 HK); clear HK HS; rename HS2 into HS ].
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memset.
{ unfold ss_rst. cbn [ss_mem]. rwr HU2 HE10 HE38 HSTKv Bg Bld FPg FPs g ld lp. }
cbn [ms_mem mkst] in HF, HG. rename HF into HF1, HG into HG1, ms into ms1.
rms HS HJ HE32 ti (2 * idl * idl) Bti FPti Pres
  ltac:(let T := fresh "T" in pose proof (st_ok_reg ubs2segs _ _ _ 12%bv HS) as T; eval_sr_get_in T; rewrite T;
        rewrite <- (rst_U_tisz _ 11 idl HE11 Hidl); unfold U; rewrite Z_to_bv_bv_unsigned; reflexivity).
intros c' (regs1 & mem1 & -> & HJ1 & _ & Hregs1 & Hout1 & Hgr1 & Z1).
rsx HS 39%nat regs1 mem1 (ubs2_A_resetDict + 120) Hregs1 Hout1 Hgr1 S_g_ti S_ti_ld HU2 HE10 HE38.
jrun_to LAWS ubs2tbl_ok HS HJ1 ubs2_A_memset.
{ rwr HU2 HE10 HE38 HSTKv Bg Bld FPg FPs g ld lp. }
cbn [ms_mem mkst] in HF, HG. rename HF into HF2, HG into HG2, ms into ms2.
rms HS HJ1 HE33 lm 8192 Blm FPlm Pres ltac:(let T := fresh "T" in jreg HS (12%bv:reg) as T; exact T).
intros c' (regs2 & mem2 & -> & HJ2 & _ & Hregs2 & Hout2 & Hgr2 & Z2).
rsx HS 45%nat regs2 mem2 (ubs2_A_resetDict + 136) Hregs2 Hout2 Hgr2 S_g_lm S_lm_ld HU2 HE10 HE38.
jrun_to LAWS ubs2tbl_ok HS HJ2 ubs2_A_memset.
{ rwr HU2 HE10 HE38 HSTKv Bg Bld FPg FPs g ld lp. }
cbn [ms_mem mkst] in HF, HG. rename HF into HF3, HG into HG3, ms into ms3.
rms HS HJ2 HE34 lc 4096 Blc FPlc Pres ltac:(let T := fresh "T" in jreg HS (12%bv:reg) as T; exact T).
intros c' (regs3 & mem3 & -> & HJ3 & _ & Hregs3 & Hout3 & Hgr3 & Z3).
rsx HS 51%nat regs3 mem3 (ubs2_A_resetDict + 152) Hregs3 Hout3 Hgr3 S_g_lc S_lc_ld HU2 HE10 HE38.
jrun_to LAWS ubs2tbl_ok HS HJ3 ubs2_A_memset.
{ rwr HU2 HE10 HE38 HSTKv Bg Bld FPg FPs g ld lp. }
cbn [ms_mem mkst] in HF, HG. rename HF into HF4, HG into HG4, ms into ms4.
Ltac rin := cbn [r_chunks]; cbv [In]; repeat (first [left; reflexivity | right]).
Ltac rbase HE := cbn [r_base base_val]; ew_havoc; rewrite HE; apply unsigned_lit_small; lia.
assert (V60 : val_mem ubs2segs (ms_mem ms4) (g + 60) 4 (lp + 1)).
{ eapply (rst_chunk_val _ _ ms4 1%nat _ 60 4 (SOff 37 1) (lp + 1) (g + 60) g HS);
  [reflexivity | rin | rbase HE10 | lia | cbn [sv_denot]; ew_havoc; rewrite HE37, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia]. }
assert (V64 : val_mem ubs2segs (ms_mem ms4) (g + 64) 2 (idl + 2)).
{ eapply (rst_chunk_val _ _ ms4 1%nat _ 64 2 (SOff 11 2) (idl + 2) (g + 64) g HS);
  [reflexivity | rin | rbase HE10 | lia | cbn [sv_denot]; ew_havoc; rewrite HE11, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia]. }
assert (V66 : val_mem ubs2segs (ms_mem ms4) (g + 66) 2 1).
{ eapply (rst_chunk_val _ _ ms4 1%nat _ 66 2 (SLit 1) 1 (g + 66) g HS);
  [reflexivity | rin | rbase HE10 | lia | reflexivity | cbn; lia | cbn; lia]. }
assert (VS : val_mem ubs2segs (ms_mem ms4) (ld + 2 * lp) 2 idl).
{ eapply (rst_chunk_val _ _ ms4 2%nat _ 0 2 (SOff 11 0) idl (ld + 2 * lp) (ld + 2 * lp) HS);
  [reflexivity | rin | rbase HE38 | lia | cbn [sv_denot]; ew_havoc; rewrite HE11, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | cbn; lia]. }
jreg HS (10%bv:reg) as M10. jreg HS (11%bv:reg) as M11. jreg HS (12%bv:reg) as M12. jreg HS (1%bv:reg) as M1.
rewrite (HE 1%nat 1%bv eq_refl) in M1.
assert (HK4 : forall r, In r rst_cs -> getr (ms_regs ms4) r = getr regs r).
{ apply (regs_kept_of_st_ok ubs2segs _ _ ms4 regs (map (Z_to_bv 64) [ti; lm; lc; li; ld; lp; ld + 2 * lp] ++ []) rst_cs HS);
  [| vm_compute; reflexivity].
  repeat (apply env_agree_havoc_ge; [lia|]). apply env_agree_refl. }
eapply SR_mono.
{ eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset rst_memset_spec _ _ ms4 RESET_STK _ _ _ _ _ _ _ _ _ li 0 8192);
  [ exact HS | reflexivity | reflexivity | exact HJ3 | rewrite M10; exact HE35 | rewrite M11; reflexivity | rewrite M12; reflexivity
  | exact M1 | exact Hra | lia | lia | lia | lia
  | intros i Hi; repeat (cbn [ms_mem mkst]; match goal with HG : mem_grows _ ?m' |- present ?m' _ => apply (present_grows _ _ _ HG) end);
    apply (Pres li 8192); [exact Bli | exact Hi]
  | intros a Ha; right; left; split; [apply FPli; exact Ha | exists li, 8192; split; [exact Bli | exact Ha]] ]. }
cbv beta. intros c' (regs5 & mem5 & -> & HJ5 & _ & Hregs5 & Hout5 & Hgr5 & Z4).
exists regs5, mem5. split; [reflexivity|]. split; [exact HJ5|].
split.
{ apply rst_regs_pres. intros r Hr. rewrite (Hregs5 r (rst_cs_clob r Hr)). exact (HK4 r Hr). }
Ltac rvo Hout V S :=
  let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk; rewrite (rst_out _ _ _ _ _ Hout) by (us S; lia); apply V; exact Hk.
split; [rvo Hout5 V60 S_g_li|]. split; [rvo Hout5 V64 S_g_li|]. split; [rvo Hout5 V66 S_g_li|]. split; [rvo Hout5 VS S_li_ld|].
Ltac rft HU2 HE10 HE38 S1 S2 :=
  cbn [r_base r_wlo r_whi base_val]; ew_havoc; rewrite ?HU2, ?HE10, ?HE38, ?unsigned_lit_small by lia; us S1; us S2; lia.
split.
{ intros i Hi.
  rewrite (rst_out _ _ li 8192 _ Hout5) by (us S_ti_li; lia).
  rewrite (rst_frame3 _ _ _ _ _ _ _ HF4) by rft HU2 HE10 HE38 S_g_ti S_ti_ld.
  rewrite (rst_out _ _ lc 4096 _ Hout3) by (us S_ti_lc; lia).
  rewrite (rst_frame3 _ _ _ _ _ _ _ HF3) by rft HU2 HE10 HE38 S_g_ti S_ti_ld.
  rewrite (rst_out _ _ lm 8192 _ Hout2) by (us S_ti_lm; lia).
  rewrite (rst_frame3 _ _ _ _ _ _ _ HF2) by rft HU2 HE10 HE38 S_g_ti S_ti_ld.
  apply Z1. exact Hi. }
split.
{ intros i Hi.
  rewrite (rst_out _ _ li 8192 _ Hout5) by (us S_lm_li; lia).
  rewrite (rst_frame3 _ _ _ _ _ _ _ HF4) by rft HU2 HE10 HE38 S_g_lm S_lm_ld.
  rewrite (rst_out _ _ lc 4096 _ Hout3) by (us S_lm_lc; lia).
  rewrite (rst_frame3 _ _ _ _ _ _ _ HF3) by rft HU2 HE10 HE38 S_g_lm S_lm_ld.
  apply Z2. exact Hi. }
split.
{ intros i Hi.
  rewrite (rst_out _ _ li 8192 _ Hout5) by (us S_lc_li; lia).
  rewrite (rst_frame3 _ _ _ _ _ _ _ HF4) by rft HU2 HE10 HE38 S_g_lc S_lc_ld.
  apply Z3. exact Hi. }
exact Z4.
Qed.
End S.
End c.
