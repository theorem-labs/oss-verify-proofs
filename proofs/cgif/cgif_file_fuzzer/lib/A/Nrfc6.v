(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YO08 YI59.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACey ACev.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma rfc_frame_of_stackI : forall E m (regs : bvmap 5 word) cs lo hi wlo whi,
region_ok tfibsegs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = spZ regs - 96 ->
(forall j, (j < 12)%nat -> In (YP09.mkChunk (88 - 8 * Z.of_nat j) (CVal 8 (SOff (36 + j) 0))) cs) ->
(forall j, (j < 12)%nat -> ew E (36 + j) = getr regs (Z_to_bv 5 (nth j rfc_saved 0))) ->
rfc_frame m (spZ regs) regs.
Proof.
intros E m regs cs lo hi wlo whi HR Hsp Hcs Hval j r Hj.
assert (Hlt : (j < 12)%nat) by (destruct (Nat.lt_ge_cases j 12) as [Hl|Hl]; [exact Hl|]; rewrite (proj2 (nth_error_None rfc_saved j)) in Hj; [discriminate | cbn; lia]).
assert (Hr : nth j rfc_saved 0 = r) by (apply nth_error_nth; exact Hj).
replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs - 96 + (88 - 8 * Z.of_nat j)) by lia. change 8%nat with (N.to_nat 8).
apply (field_of_region E m 2 (spZ regs - 96) cs lo hi wlo whi (88 - 8 * Z.of_nat j) 8 (SOff (36 + j) 0) _ HR Hsp (Hcs j Hlt)).
- cbn [sv_denot]. rewrite Z.add_0_r, (Hval j Hlt), Hr, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRg. change (bv_modulus 64) with (2 ^ 64) in HRg. cbn. lia.
- cbn. lia.
Qed.
Lemma denot_mul3 : forall E n i, ew E n = Z_to_bv 64 i -> 0 <= i < 2 ^ 16 ->
sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = Z_to_bv 64 (3 * i).
Proof.
intros E n i Hn Hi. rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E n i Hn) by lia. rewrite U_SLit. rewrite (zcanon_id 3) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma U_mul3 : forall E n i, ew E n = Z_to_bv 64 i -> 0 <= i < 2 ^ 16 -> U E (SMd M_MUL (SOff n 0) (SLit 3)) = 3 * i.
Proof.
intros E n i Hn Hi. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E n i Hn) by lia. rewrite U_SLit. rewrite (zcanon_id 3) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma rfcJ_alu_or_lits : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
alu64 ALU_OR (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof.
intros x y Hx Hy. set (E0 := mkEnv (fun _ => Z_to_bv 64 0) (fun _ => [])).
change (alu64 _ _ _) with (sv_denot E0 (SAlu ALU_OR (SLit x) (SLit y))).
rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite !U_SLit. rewrite (zcanon_id x), (zcanon_id y) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; apply Z_lor_bound; lia). reflexivity.
Qed.
Ltac rkeep RD H2 m2 etac :=
lazymatch type of RD with ?rk = 0 -> forall i, 0 <= i < ?nk -> aview _ ?Hh ?m (?a + i) = aview _ ?Hc ?mc (?pb + (?o + i)) =>
let RD2 := fresh "RD" in
assert (RD2 : rk = 0 -> forall i, 0 <= i < nk -> aview tfibsegs H2 m2 (a + i) = aview tfibsegs Hc mc (pb + (o + i)))
by (let Hz := fresh "Hz" in intros Hz i Hi; rewrite <- (RD Hz i Hi); etac);
clear RD; rename RD2 into RD
| ?ty => fail "rkeep: unexpected shape" ty end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section RJ.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy A_asan_memcpy_tfb.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B MT.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma rfc_J_ok : RFC_I_stmt B MT -> RFC_J_stmt B MT.
Proof.
intros RI.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
W1 regs1 mem1 md1 racc curv nlp fattr fgen delay tidx T P
RC HPL Hhdrv HprogH HJ1 HV HRJ HFR HM RAdst1 KEPT1 HIO1.
pose proof RC as ((HMOK & HCOST & HlenP) & HPerm & Hpd & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hown & HfinC & Hcid & Hfal & Hst1 & Hst2 & Hdst1 & Hdst2 & Hsd
& Hst8 & Hdst8 & HN & Hcur & Hnb & HSEP & HlyF & Hev & Hlive & (HFhi1 & HFimg & HFhi2) & HFceil & (Hph & Hpimg & Hpapp) & Hpceil & HnbM).
rbox HFimg. rbox HFhi2. rbox Hpimg. rbox Hpapp.
pose proof HV as (HR & Hcurv & Hlpa0 & Hnlp & Hfattr & Hfgen & Hdelay & Htidx).
pose proof HM as (Wp & Wn & Wc & _).
pose proof HRJ as ((R2 & R3 & R4 & R8 & R18 & R19 & R25 & R22 & R9 & R20 & R23 & R24 & R27) & RJ21 & RJ10).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HJ1 as (HAR1 & Hly1 & _ & _ & _ & _ & Hnev1 & _ & _ & _ & _ & _ & _ & Hpres1 & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (EFA1 : forall c p, frame_addr lyc c p = frame_addr lyc c p) by reflexivity.
pose proof (mo_le_refl MT MTL Sc : mo_le MT Sc Sc 0) as HMLE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TRFC_STK = 112 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (ESTACK = 4096) as Hes by reflexivity. assert (HEV : EV_RFC = 6) by reflexivity.
assert (HBb1 : forall b m, In (b, m) Bb -> In (b, m) (ablocks B lyc Sc)) by (intros b m Hb; eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb]).
assert (Hpdc : In (pdata, nb) (ablocks B lyc Sc)) by (apply HBb1; exact Hpd).
pose proof (req_size_pos nb ltac:(lia)) as [Hrq1 Hrq2].
pose proof (fs_frame_bytes_nonneg cid) as HFB.
assert (HSPB : alloc_ceiling <= spZ regs - TRFC_STK /\ spZ regs <= 2 ^ 47) by (clear - Hwlo Hwhi Hceil Hslo Hshi H47 Hstk0; lia).
assert (HSTB : spZ regs <= st /\ st + 24 <= 2 ^ 47 /\ alloc_ceiling <= st) by (clear - Hst1 Hst2 Hwlo Hwhi Hceil Hslo Hshi H47 Hstk0 HTS Has C1; lia).
assert (HDST0 : 4096 <= dst) by (clear - Hdst1 HFhi1; lia). assert (HDSTC : dst + 32 <= alloc_ceiling) by (clear - Hdst2 HFceil; lia).
assert (HDSTH : rboxed (dst + 32 <= 2147446784 \/ 17594333495296 <= dst)) by (unfold rboxed in *; clear - Hdst1 Hdst2 HFhi2; lia).
assert (Hpdst : rboxed (pdata + req_size nb <= frame_addr lyc cid pos \/ frame_addr lyc cid pos + fs_frame_bytes cid <= pdata)).
{ pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ pdata nb cid pos HAR1 Hpdc HfinC) as D. unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
assert (Hlive1 : blocks_bytes Sc + 3 * nlp <= LIVE_MAX) by (unfold LIVE_RFC in Hlive; clear - Hlive Hnlp; lia).
remember (Ereg regs1 (I_extra regs pdata nb curv 0 fattr fgen delay nlp tidx)) as E eqn:HE.
pose proof (rfc_J_entry B TL LAWS W1 regs regs1 mem1 lyc Sc md1 ly STK sp0 st dst N pdata nb curv 0 fattr fgen delay nlp tidx cid pos racc cur (Z.land fattr 1)
HAR1 Hpdc HfinC Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 HN Hnb HV ltac:(clear - Hcur; lia) Hstk Hal16 Hwlo Hwhi Hpres1 HRJ HFR HM) as HS. rewrite <- HE in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 96) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; clear - HSPB C1 HTS Has; lia).
assert (E3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = Z_to_bv 64 dst) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 N) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 st) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E25 : ew E 25 = Z_to_bv 64 racc) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E27 : ew E 27 = getr regs 27) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (E10 : ew E 10 = Z_to_bv 64 (Z.land fattr 1)) by (rewrite (EE 10%nat 10%bv eq_refl); exact RJ10).
assert (E21 : ew E 21 = Z_to_bv 64 (dst + 26)) by (rewrite (EE 21%nat 21%bv eq_refl); exact RJ21).
assert (EX : forall j, ew E (32 + j) = nth j (I_extra regs pdata nb curv 0 fattr fgen delay nlp tidx) (Z_to_bv 64 0)) by (intros j; rewrite HE; apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 pdata) by exact (EX 0%nat). assert (E33 : ew E 33 = Z_to_bv 64 nb) by exact (EX 1%nat).
assert (E34 : ew E 34 = Z_to_bv 64 curv) by exact (EX 2%nat). assert (E35 : ew E 35 = Z_to_bv 64 0) by exact (EX 3%nat).
assert (E36 : ew E 36 = getr regs 1) by exact (EX 4%nat). assert (E37 : ew E 37 = getr regs 8) by exact (EX 5%nat).
assert (E38 : ew E 38 = getr regs 9) by exact (EX 6%nat). assert (E39 : ew E 39 = getr regs 18) by exact (EX 7%nat).
assert (E40 : ew E 40 = getr regs 19) by exact (EX 8%nat). assert (E41 : ew E 41 = getr regs 20) by exact (EX 9%nat).
assert (E42 : ew E 42 = getr regs 21) by exact (EX 10%nat). assert (E43 : ew E 43 = getr regs 22) by exact (EX 11%nat).
assert (E44 : ew E 44 = getr regs 23) by exact (EX 12%nat). assert (E45 : ew E 45 = getr regs 24) by exact (EX 13%nat).
assert (E46 : ew E 46 = getr regs 25) by exact (EX 14%nat). assert (E47 : ew E 47 = getr regs 26) by exact (EX 15%nat).
assert (E48 : ew E 48 = Z_to_bv 64 fattr) by exact (EX 16%nat). assert (E49 : ew E 49 = Z_to_bv 64 fgen) by exact (EX 17%nat).
assert (E50 : ew E 50 = Z_to_bv 64 delay) by exact (EX 18%nat). assert (E51 : ew E 51 = Z_to_bv 64 nlp) by exact (EX 19%nat).
assert (E52 : ew E 52 = Z_to_bv 64 tidx) by exact (EX 20%nat).
clear EX.
assert (B19 : bv_unsigned (ew E 19) = st) by (rewrite E19; apply unsigned_lit_small; lia).
assert (B8 : bv_unsigned (ew E 8) = dst) by (rewrite E8; apply unsigned_lit_small; lia).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
clear HE.
set (Zs := fun a : Z => spZ regs - TRFC_STK <= a < spZ regs \/ dst <= a < dst + 32 \/ st + 16 <= a < st + 24).
set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs \/ dst <= a < dst + 16 \/ st + 16 <= a < st + 24).
set (Zsn := fun a : Z => spZ regs - 96 <= a < spZ regs \/ dst <= a < dst + 16).
assert (ZBsm : forall a, SB <= a < kHighShadowEnd -> ~ Zsm a).
{ intros a Ha. subst Zsm. cbn beta. clear - Ha HSPB HSTB HDST0 HDSTH HTS Has C1 C2 C3 C4 C5. unfold rboxed in HDSTH. unfold SB in Ha. lia. }
reshok_bx HS 22%nat.
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 RFC_J) mem1 (seg_rom tfibsegs))) in HJ1.
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
- assert (Lb : Z.land fattr 1 = fattr mod 2) by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
  pose proof (Z.mod_pos_bound fattr 2 ltac:(lia)) as Hb2.
  assert (Hbit : Z.land fattr 1 = 0).
  { rewrite branch_eq_U, (U_atom _ 10 (Z.land fattr 1) E10), U_SLit in Hc by (unfold M64; lia). change (zcanon 0) with 0 in Hc.
    destruct (Z.eqb_spec (Z.land fattr 1) 0); [assumption | discriminate Hc]. }
  clear Hc. norm_ss HS. reshok_bx HS 22%nat.
  aj_run_to_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan RFC_I.
  { awrI Usp E19 E8 Hown EFA1. }
  unrunRD HFr Zsm Usp B8 Usp UN1. clear HF HFr HG.
  pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT1 HSEP UN1 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT2. clear KEPT1.
  assert (SHK1 : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem ms) a = aview tfibsegs (w_H W1) mem1 a)
by (intros a Ha; apply UN1; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]).
  pose proof (RA_kept_band _ _ dst 32 SHK1 ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst1) as RAdstI. clear SHK1 RAdst1.
  vkeepUN2 UN1 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
  clear Wc. rename Wp into Vp. rename Wn into Vn.
  field_at HS 4%nat 19%nat st B19 16 8%N 34%nat curv E34 Vc.
  field_at HS 3%nat 8%nat dst B8 0 8%N 35%nat 0 E35 Vl.
  field_at HS 3%nat 8%nat dst B8 16 4%N 48%nat fattr E48 Vfa.
  field_at HS 3%nat 8%nat dst B8 20 4%N 49%nat fgen E49 Vfg.
  field_at HS 3%nat 8%nat dst B8 24 2%N 50%nat delay E50 Vde.
  field_at HS 3%nat 8%nat dst B8 26 2%N 51%nat nlp E51 Vnl.
  field_at HS 3%nat 8%nat dst B8 28 1%N 52%nat tidx E52 Vti.
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 3%nat _ HS ltac:(vm_compute; reflexivity)) as HRd; cbn [ms_mem restrict] in HRd;
  pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRs; cbn [ms_mem restrict] in HRs end.
  pose proof (zero_of_region _ _ 8%nat dst _ _ _ _ _ 8 8 (dst + 8) 8 HRd B8 ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as Vz.
  pose proof (rfc_frame_of_stackI _ _ regs _ _ _ _ _ HRs Usp
  ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn; tauto|]); exfalso; clear - Hj; lia)
  ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn [nth rfc_saved Nat.add]; first [exact E36 | exact E37 | exact E38 | exact E39 | exact E40 | exact E41 | exact E42 | exact E43 | exact E44 | exact E45 | exact E46 | exact E47]|]); exfalso; clear - Hj; lia)) as HFR2.
  clear HRd HRs.
  rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4. rreg HS (8%bv : bv 5) Q8. rreg HS (9%bv : bv 5) Q9.
  rreg HS (18%bv : bv 5) Q18. rreg HS (19%bv : bv 5) Q19. rreg HS (20%bv : bv 5) Q20. rreg HS (22%bv : bv 5) Q22. rreg HS (23%bv : bv 5) Q23.
  rreg HS (24%bv : bv 5) Q24. rreg HS (25%bv : bv 5) Q25. rreg HS (27%bv : bv 5) Q27.
  pose proof (denot_shx _ 19 22 16 st SB E19 E22 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D16. cbn [sv_denot] in D16. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D16.
  pose proof (denot_shx _ 19 22 8 st SB E19 E22 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D8. cbn [sv_denot] in D8. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D8.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ => change p with RFC_I end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
  lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
  eapply (RI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
  W1 (ms_regs msX) (ms_mem msX) mdX lyc Sc k racc curv 0 nlp fattr fgen delay tidx [] T 0 P);
  [ exact RC | exact HPL | exact HMLE | apply (mo_malloc_nonneg MT MTL); clear; lia | exact Hhdrv
  | unfold rfc_progP, palsz; rewrite Hbit; cbn [Z.eqb]; rewrite !Z.add_0_r;
    destruct HprogH as [(Hz & Hfit & Ecv) | (Hnz & Hsh & Ecv)];
    [ left; split; [exact Hz|]; split; [exact Hfit|]; split; [exact Ecv | intros X; exfalso; apply X; reflexivity]
    | right; split; [exact Hnz|]; split; [exact Hsh | exact Ecv] ]
  | exact HJc | clear; lia | reflexivity | cbn [app]; exact HPerm
  | unfold rfc_pal; rewrite Hbit; cbn [Z.eqb]; split; [reflexivity|]; split; [intros _; reflexivity|]; split; [intros b Hb; destruct Hb | intros b m Hb; destruct Hb]
  | exact HV
  | unfold I_regs_at, w64; rewrite Q23, Q24, D16, D8;
    rewrite Q2, Q3, Q4, Q8, Q18, Q19, Q25, Q22, Q9, Q20, Q27; enorm; agnorm; rewrite ?B19;
    rewrite E3, E4, E8, E18, E19, E25, E22, E27, <- Usp, Z_to_bv_bv_unsigned;
    repeat split; reflexivity
  | exact HFR2
  | unfold rfc_memI; split; [exact Vp|]; split; [exact Vn|]; split; [exact Vc|]; split; [exact Vl|]; split; [exact Vz|]; split; [exact Vfa|]; split; [exact Vfg|]; split; [exact Vde|]; split; [exact Vnl | exact Vti]
  | exact RAdstI
  | exact KEPT2
  | io_now ] end end.
- assert (Lb : Z.land fattr 1 = fattr mod 2) by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
  pose proof (Z.mod_pos_bound fattr 2 ltac:(lia)) as Hb2.
  assert (Hbit : Z.land fattr 1 <> 0).
  { rewrite branch_eq_U, (U_atom _ 10 (Z.land fattr 1) E10), U_SLit in Hc by (unfold M64; lia). change (zcanon 0) with 0 in Hc.
    destruct (Z.eqb_spec (Z.land fattr 1) 0); [discriminate Hc | assumption]. }
  clear Hc. norm_ss HS. reshok_bx HS 22%nat.
  aj_run_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan.
  all: try (oblD RAdst1 E8 E22).
  { awrI Usp E19 E8 Hown EFA1. }
  unrunRD HFr Zsm Usp B8 Usp UN1. clear HF HFr HG.
  pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT1 HSEP UN1 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT2. clear KEPT1.
  assert (SHK1 : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem ms) a = aview tfibsegs (w_H W1) mem1 a)
  by (intros a Ha; apply UN1; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]).
  pose proof (RA_kept_band _ _ dst 32 SHK1 ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst1) as RAdst1s. clear SHK1 RAdst1.
  vkeepUN2 UN1 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
  clear Wc. field_at HS 4%nat 19%nat st B19 16 8%N 34%nat curv E34 Wc.
  rename Wp into Vp. rename Wn into Vn. rename Wc into Vc.
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos (proj1 HJ1) HfinC) as (_ & _ & HFpres1 & _).
  rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  replace (Z_to_bv 64 338224) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; reflexivity).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  assert (CH : chain_pre lyc (aview tfibsegs (w_H W1) (ms_mem msX)) (ms_regs msX) []) end.
  { eapply (achain_chain_pre lyc _ (spZ regs - 96) dst []).
  - apply achain_low; clear - HDST0 HDSTC; lia.
  - unfold spZ; rewrite Rsp; enorm; agnorm; rewrite Usp; clear - HSPB C1 HTS Has; unfold spZ in *; lia.
  - unfold s0Z; rewrite Rs0; enorm; agnorm; rewrite E8; apply unsigned_lit_small; clear - HDST0 HDSTC C1; lia.
  - unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia. }
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (amalloc04_sub tfibsegs B LAWS tfib_segs_low MT AMALLOC4 W1 (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own
  lyc Sc _ k (3 * nlp) (spZ regs - 96 - sp0) (Z_to_bv 64 RFC_PM) [] HJ1);
  [ rewrite Ra0; enorm; agnorm; unfold w64; rewrite <- (denot_mul3 _ 51%nat nlp E51 Hnlp); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | unfold MALLOC_MAX; clear - Hnlp; lia
  | exact Hlive1
  | unfold spZ; rewrite Rsp; enorm; agnorm; rewrite Usp; unfold spZ; clear; lia
  | replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
  | lia
  | clear - Hwlo HTS Has; lia
  | rewrite Rgp; enorm; agnorm; rewrite E3; reflexivity
  | rewrite Rtp; enorm; agnorm; rewrite E4; reflexivity
  | exact Rra
  | vm_compute; reflexivity
  | rewrite HEV in Hev; clear - Hnev1 Hev; lia
  | exact CH
  | rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; rewrite HBcode, (tl_universe B TL);
  apply TRACES_read_frameconfig_U; apply memZL_In; vm_compute; reflexivity
  |
  apply (mok_station MT Sc Sc T 0 (mo_malloc MT (3 * nlp)) MTL HMOK HMLE); [apply (mo_malloc_nonneg MT MTL); clear - Hnlp; lia|];
  unfold RFC_COST in HCOST; pose proof (mo_malloc_mono MT MTL (3 * nlp) 196605 ltac:(clear - Hnlp; lia)) as Hmm;
  pose proof (mo_malloc_nonneg MT MTL N ltac:(clear - HN; lia)) as HmN; pose proof (mo_free_nonneg MT MTL) as Hf0; clear - HCOST Hmm HmN Hf0; lia ] end. }
  cbv beta. clear Ra0 Rra Rsp Rgp Rtp Rs0 CH.
  intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha02 & Hfrs2 & Hr4096 & Ebl & HK0 & HMLE2 & HJS2).
  assert (HIO2 : same_io mdc md2) by (io_after (ajournal_closed_same_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sink_closed_nil HJS2)). clear HJS2.
  pose proof (req_size_pos (3 * nlp) ltac:(clear - Hnlp; lia)) as [HrqN1 HrqN2].
  pose proof (proj1 HJ2) as HAR2.
  assert (HK : acall_kept tfibsegs B lyc Sc W1 (ms_mem ms) W2 mem2 (sp0 + (spZ regs - 96 - sp0) - ASTACK) (sp0 + (spZ regs - 96 - sp0)) (fun a => res <> 0 /\ res <= a < res + req_size (3 * nlp)))
  by (eapply acall_kept_mono_E; [exact HK0 | intros a Ha; cbn beta; split; [clear - Hr4096; lia | exact Ha]]).
  assert (HBin : forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly2 S2)) by (intros b Hb; rewrite Ebl; apply in_app_iff; left; exact Hb).
  assert (HrIn : In (res, 3 * nlp) (ablocks B ly2 S2)) by (rewrite Ebl; apply in_app_iff; right; left; reflexivity).
  assert (HresIn : res <> 0 -> In (res, 3 * nlp) (ablocks B ly2 S2)) by (intros _; exact HrIn).
  vkeep Vp (w_H W2) mem2 ltac:(apply (proj1 HK); [clear - Hi HSTB; lia | clear - Hi Hst1; lia]).
  vkeep Vn (w_H W2) mem2 ltac:(apply (proj1 HK); [clear - Hi HSTB; lia | clear - Hi Hst1; lia]).
  vkeep Vc (w_H W2) mem2 ltac:(apply (proj1 HK); [clear - Hi HSTB; lia | clear - Hi Hst1; lia]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ res (3 * nlp) HAR2 HrIn) as (Hr16 & _ & HrCeil & [_ HrHi2] & _).
  pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR2 HrIn) as HrHi1.
  assert (HrHi : (res + req_size (3 * nlp) <= 65536 \/ 6270976 <= res) /\ (res + req_size (3 * nlp) <= 2147446784 \/ 17594333495296 <= res))
  by (pose proof asan_consts as (C1' & C2' & C3' & C4' & C5'); clear - HrHi1 HrHi2 C1' C2' C3' C4' C5'; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
  assert (Hrng : res = 0 \/ (4096 <= res /\ ((res + req_size (3 * nlp) <= 65536 \/ 6270976 <= res) /\ (res + req_size (3 * nlp) <= 2147446784 \/ 17594333495296 <= res)) /\ res + req_size (3 * nlp) <= alloc_ceiling /\ res mod 16 = 0 /\ In (res, 3 * nlp) (ablocks B ly2 S2)))
  by (right; split; [exact Hr4096|]; split; [exact HrHi|]; split; [exact HrCeil|]; split; [exact Hr16 | exact HrIn]).
  assert (Hfin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; exact HfinC).
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 Hfin2) as (_ & _ & HFpres2 & _).
  destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ1)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
  destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
  pose proof HJ2 as (_ & Hly2 & _ & _ & _ & _ & Hnev2 & _).
  assert (EFA2 : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; destruct Hly2 as (_ & _ & _ & _ & _ & -> & _); rewrite HlyF; reflexivity).
  assert (HdstA2 : frame_addr ly2 cid pos <= dst) by (rewrite EFA2; exact Hdst1).
  assert (HdstB2 : dst + 32 <= frame_addr ly2 cid pos + fs_frame_bytes cid) by (rewrite EFA2; exact Hdst2).
  assert (HnewF : forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> ~ (res <> 0 /\ res <= a < res + req_size (3 * nlp))).
  { intros a Ha [Hnz Hin]. pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ res (3 * nlp) cid pos HAR2 (HresIn Hnz) Hfin2) as D.
  rewrite EFA2 in D. unfold zdisjoint in D. cbn [fst snd] in D. clear - D Ha Hin. lia. }
  assert (RAdst2 : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF dst 32).
  { eapply (RA_kept_call B lyc Sc); [exact HK | exact HfinC | intros a [Hnz Ha]; clear - Hnz Ha Hrng; unfold rboxed in *; lia | exact Hcid | exact Hfal
  | clear - HFhi1; lia | exact HFceil | exact Hdst1 | exact Hdst2 | exact RAdst1s]. }
  clear RAdst1s.
  reseatL HS HJ2 HP2 [0; 1; 2; 3; 4]%nat AG
  ltac:(first [ eapply (region_kept_stack_aj tfibsegs B); [exact HK | exact HJ2 | evalER AG | clear - HTS Has; lia | clear - Hwlo HTS Has; lia | clear - Hwhi; lia | cbn; lia | cbn; lia]
  | apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot1) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot2) | lia]
  | apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell1) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell2) | lia]
  | eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalER AG | exact HfinC | left; cbn [YP09.r_lo YP09.r_hi]; lia
  | intros a Ha; cbn beta; apply HnewF; lia | intros a Ha; apply (fun H => proj1 (HFpres2 a H)); rewrite EFA2; lia ]
  | eapply (region_kept_stack_aj tfibsegs B); [exact HK | exact HJ2 | evalER AG | clear - Hst1 HTS Has; lia | clear - Hst1 Hwlo HTS Has; lia | clear - Hst2; lia | cbn; lia | cbn; lia]
  | match goal with |- ?g => idtac "KEPTFAIL" g end ]).
  clear Kcell1 Kgot1 Kcell2 Kgot2.
  rreg HS (10%bv : bv 5) Rres. rewrite Ha02 in Rres. symmetry in Rres. unfold w64 in Rres.
  renvI HS AG E8 E19 E22 Usp st dst E8n E18n E25n Uspn B8n B18n.
  clear Hrng. rbox HrHi.
  pose proof (aftok_new_block tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (3 * nlp) HJ1 (proj1 HJ2) Ebl ltac:(clear - Hnlp; lia)) as Tpal.
  assert (Apal : forall blc i lyq, In (res, 3 * nlp) blc -> 0 <= i < req_size (3 * nlp) -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq own (res + i)).
  { intros blc i lyq Hin Hi. exact (awr_new_block tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (3 * nlp) blc i lyq HJ1 (proj1 HJ2) Ebl ltac:(clear - Hnlp; lia) Hin Hi). }
  assert (HPerm2 : Permutation (ablocks B ly2 S2) ((res, 3 * nlp) :: Bb)).
  { rewrite Ebl. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply Permutation_cons; [reflexivity | exact HPerm]. }
  assert (HsepB : forall b m, In (b, m) Bb -> res + req_size (3 * nlp) <= b \/ b + req_size m <= res).
  { intros b m Hb. destruct (in_split _ _ Hb) as (l1 & l2 & El).
  assert (HP' : Permutation (ablocks B ly2 S2) ((res, 3 * nlp) :: (b, m) :: l1 ++ l2)).
  { eapply Permutation_trans; [exact HPerm2|]. apply perm_skip. rewrite El. apply Permutation_sym. apply Permutation_middle. }
  pose proof (sep_blocks_perm tfibsegs B LAWS _ _ _ _ _ _ _ _ HAR2 HP') as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. clear - D. lia. }
  assert (HimgFS : forall c p a, In (c, p) (frames Sc) ->
  (in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) -> ~ (res <= a < res + req_size (3 * nlp))).
  { intros c p a Hcp Ha Hin. destruct Ha as [Ha | Ha].
  + pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ res (3 * nlp) c p HAR2 HrIn ltac:(rewrite Hfrs2; exact Hcp)) as D.
  rewrite EFA2 in D. unfold zdisjoint, frame_rng, in_zr in D, Ha. cbn [fst snd] in D, Ha. clear - D Ha Hin HrqN2. lia.
  + destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ c p HAR2 ltac:(rewrite Hfrs2; exact Hcp)) as (F0 & Fc & Fh). rewrite EFA2 in F0, Fc, Fh.
  pose proof (frame_shadow_low (frame_addr lyc c p) c a ltac:(clear - F0; lia) Fc Ha) as Hlow. clear - Hlow Hin HrHi HrqN2 C2 C3. unfold rboxed in HrHi. lia. }
  assert (KEPT3 : rfc_kept B W memc W2 mem2 (spZ regs) Bb lyc Sc st dst).
  { eapply (rfc_kept_call B _ _ _ _ _ _ _ _ _ _ lyc Sc _ _ _ _ _ KEPT2 HK ltac:(clear - HTS Has; lia) ltac:(clear; lia) HBb1 _ eq_refl ltac:(intros; reflexivity) _).
  Unshelve.
  - intros b m i Hb Hi [_ Hin]. pose proof (HsepB b m Hb) as Hd. clear - Hd Hi Hin. lia.
  - intros c p a Hcp Ha [_ Hin]. exact (HimgFS c p a Hcp Ha Hin). }
  clear KEPT2 Hlive1 HnewF.
  lazymatch type of Rres with ew ?Ex ?nx = _ =>
  pose proof (st_ok_add_fact tfibsegs Ex _ _ nx (mkAF 4096 140737479966720 4) HS
  ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Rres, unsigned_lit_small by lia;
  change (2 ^ 4) with 16; clear - Hr4096 HrCeil Hr16 HrqN1 HrqN2 C1; lia)) as HS3;
  clear HS; rename HS3 into HS end.
  norm_ss HS. reshok_bx HS 22%nat.
  pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo2 & Ehi2 & _).
  assert (RAst2 : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF st 24)
  by (apply (RA_stack B LAWS ly2 S2 W2 mem2 _ st 24 HAR2); [rewrite Elo2; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi2; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]).
  aj_run_tok tfibtbl_lib_ok HS HJ2 SHOK RBspan.
  all: try (oblD RAdst2 E8 E22).
  all: try (oblS RAst2 E19 E22).
  { awrI Uspn E18n E8n Hown EFA2. }
  unrunRD HFr Zsm Usp B8 Usp UN2. clear HF HFr HG.
  vkeepUN2 UN2 Vp Vn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
  clear Vc. field_at HS 4%nat 19%nat st B18n 16 8%N 34%nat curv E34 Vc.
  pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT3 HSEP UN2 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT4. clear KEPT3.
  assert (SHK2 : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W2) (ms_mem ms0) a = aview tfibsegs (w_H W2) mem2 a)
  by (intros a Ha; apply UN2; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]).
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
  lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem msX) _ _ |- _ =>
  assert (RAstC : range_addressable (aview tfibsegs (w_H W2) (ms_mem msX)) SHADOW_OFF st 24)
  by (apply (RA_stack B LAWS ly2 S2 W2 (ms_mem msX) _ st 24 (proj1 HJc)); [rewrite Elo2; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi2; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]);
  pose proof (proj1 HJc) as HARc end end.
  lazymatch type of HS with st_ok _ _ ?ss _ =>
  lazymatch type of AG with forall n, _ -> ew ?Eb n = _ =>
  let Kb := eval vm_compute in (run_K 0 (SOff 32 0) [] ss) in
  let ssJv := eval vm_compute in (mkSS RFC_PRD (sr_sets (ss_regs ss) (junk_upd 200 CLOB)) (ss_mem ss) None (mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss)))) in
  pose (ssJ := ssJv);
  assert (AGX : forall j, (j < Kb)%nat -> ew Eb j = ew Eb j) by (intros; reflexivity);
  lazymatch goal with |- SRr _ ?Wx {| cfg_ms := ?msX; cfg_model := ?mdX |} _ =>
  eapply SRr_bind with (R := rd_cut B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 Wx mdX (k + 1) ssJ Eb Kb (ms_mem msX) st res (3 * nlp) pdata nb curv (spZ regs - 96 - sp0) dst RFC_PRD) end end end.
  { srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
  - rewrite branch_geu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
    rewrite (U_atom _ 33 nb), (U_atom _ 34 curv), (U_mul3 _ 51 nlp), zcanon_id in Hc by first [unfold M64; lia | enorm; agnorm; first [exact E33 | exact E51 | exact E34] | lia].
    assert (HOK : curv + 3 * nlp <= nb) by (destruct (Z.ltb_spec nb (curv + 3 * nlp)); [discriminate Hc | lia]). clear Hc.
    norm_ss HS. reshok_bx HS 22%nat.
    aj_run_tok tfibtbl_lib_ok HS HJ2 SHOK RBspan.
    all: try (oblS RAstC E19 E22).
    { awrI Uspn E18n E8n Hown EFA2. }
    keStep HF HFr HG KE PR Zsm Usp B8 Usp.
    shkOf KE ZBsm SHKb.
    assert (Hpd2 : In (pdata, nb) (ablocks B ly2 S2)) by exact (HBin _ Hpdc).
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
    lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem msX) _ _ |- _ =>
    assert (HppresB : forall a, pdata + curv <= a < pdata + curv + (3 * nlp) -> apresent (w_H W2) (ms_mem msX) a)
    by (destruct (al_blocks _ _ LAWS _ _ _ _ _ pdata nb (proj1 HJc) Hpd2) as (_ & _ & _ & _ & HP & _); intros a Ha; apply (proj1 (HP a ltac:(clear - Ha HOK Hcurv Hcur Hrq2; lia))));
    assert (HsrcA : amem_range (pdata + curv) (3 * nlp)) by (apply (amem_range_of_block tfibsegs B LAWS ly2 S2 W2 _ _ pdata nb _ _ (proj1 HJc) Hpd2); clear - HOK Hcurv Hcur Hrq2; lia);
    assert (HsrcR : range_addressable (aview tfibsegs (w_H W2) (ms_mem msX)) SHADOW_OFF (pdata + curv) (3 * nlp)) by (apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 _ _ pdata nb _ _ (proj1 HJc) Hpd2); clear - HOK Hcurv Hcur Hrq2; lia);
    assert (HsrcH : 0 < (3 * nlp) -> shadow_hull_vis (aview tfibsegs (w_H W2) (ms_mem msX)) (pdata + curv) (3 * nlp)) by (intros Hn0; apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 _ _ pdata nb _ _ (proj1 HJc) Hpd2); clear - HOK Hcurv Hcur Hrq2 Hn0; lia);
    assert (HdA : amem_range res (3 * nlp)) by (apply (amem_range_of_block tfibsegs B LAWS ly2 S2 W2 _ _ res (3 * nlp) _ _ (proj1 HJc) HrIn); clear - HrqN2 Hnlp; lia);
    assert (HdR : range_addressable (aview tfibsegs (w_H W2) (ms_mem msX)) SHADOW_OFF res (3 * nlp)) by (apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 _ _ res (3 * nlp) _ _ (proj1 HJc) HrIn); clear - HrqN2 Hnlp; lia);
    assert (HdH : 0 < (3 * nlp) -> shadow_hull_vis (aview tfibsegs (w_H W2) (ms_mem msX)) res (3 * nlp)) by (intros Hn0; apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 _ _ res (3 * nlp) _ _ (proj1 HJc) HrIn); clear - HrqN2 Hn0; lia);
    destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJc)) as (KcellC & _ & KgotC & _) end end.
    rewrite HBgot, HBcell in KgotC. rewrite HBcell in KcellC.
    rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
    rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst _ (Z_to_bv 64 ?p) _ _; cfg_model := _ |} _ => change p with A_asan_memcpy_tfb end.
    eapply SRr_bind.
    { lazymatch goal with |- SRr _ _ {| cfg_ms := mkst (ms_regs ?msX) _ (ms_mem ?msX) _; cfg_model := _ |} _ =>
      lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem msX) _ _ |- _ =>
      eapply (aj_intrin_at_io B LAWS OCpy A_asan_memcpy_tfb AMEMCPY _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own
        ly2 S2 _ (k + 1) res (pdata + curv) (3 * nlp) (spZ regs - 96 - sp0) (Z_to_bv 64 (RFC_PM + 116)) HJc);
      [ rewrite Ra0; rewrite Rres; reflexivity
      | rewrite Ra1; agnorm; rewrite E32, E34, alu_add_small by (unfold M64; clear - HOK Hcurv Hcur Hnb Hpceil Hrq2 Hph Hnlp C1; lia); reflexivity
      | rewrite Ra2; agnorm; pose proof (denot_mul3 _ 51 nlp E51 Hnlp) as DM; cbn [sv_denot] in DM; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in DM; rewrite DM; reflexivity
      | clear - Hnlp; lia | clear - Hr4096; lia | clear - HrCeil HrqN2 C1 C3 C4 C5; lia
      | unfold spZ; rewrite Rsp; enorm; agnorm; rewrite Usp; unfold spZ; lia
      | replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
      | lia
      | clear - Hwlo HTS Has Hes; lia
      | rewrite Rgp; enorm; agnorm; rewrite E3; reflexivity
      | rewrite Rtp; enorm; agnorm; rewrite E4; reflexivity
      | rewrite Rra; reflexivity
      | vm_compute; reflexivity
      | intros a Ha; split; [replace a with (res + (a - res)) by lia; apply Apal; [exact HrIn | clear - Ha HrqN2; lia] | clear - Ha HrCeil HrqN2 HSPB C1 HTS Has Hes; lia]
      | exact HdA | exact HdR | exact HdH
      | split; [clear - Hpceil Hcurv Hcur Hrq2 Hph C1; lia|]; split; [clear - Hpceil HOK Hcurv Hcur Hrq2 Hph C1 C3 C4 C5; lia|]; split;
        [ intros a Ha; split; [apply (aview_some_of_apresent tfibsegs); exact (HppresB a Ha)
          | unfold spZ; rewrite Rsp; enorm; agnorm; rewrite Usp; clear - Ha Hpceil HOK Hcurv Hcur Hrq2 Hph HSPB C1 HTS Has Hes; unfold ESTACK in *; lia]
        | split; [pose proof (HsepB pdata nb Hpd) as Hd; clear - Hd HOK Hcurv Hcur Hrq2 HrqN2 Hph; lia|];
          split; [exact HsrcA|]; split; [exact HsrcR | exact HsrcH] ] ] end end. }
    cbv beta. clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp HppresB HsrcA HsrcR HsrcH HdA HdR HdH.
    intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3 & Hio3).
    replace (sp0 + (spZ regs - 96 - sp0)) with (spZ regs - 96) in Hfr3 by lia.
    destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ3)) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
    reseatX HS HJ3 HP3 [0; 1; 2; 3; 4]%nat AG AGX
    ltac:(first [ eapply region_kept_aview;
      [ evalER AG
      | intros a Ha; apply Hfr3;
        [ clear - Ha HSPB HDST0 HDSTC HSTB Hst2 HTS Has C1 Hwhi; lia
        | first [ clear - Ha HSPB HrCeil HrqN2 HSTB HTS Has C1; lia
                | intros X; apply (HimgFS cid pos a HfinC); [left; unfold in_zr, frame_rng; cbn [fst snd]; clear - Ha Hdst1 Hdst2; lia | clear - X HrqN2; lia] ]
        | clear - Ha HSPB HDST0 HDSTC HSTB HTS Has Hes C1; unfold ESTACK in *; lia ]
      | exact Hpres3 ]
    | apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword tfibsegs _ _ _ _ KgotC) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot3) | lia]
    | apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword tfibsegs _ _ _ _ KcellC) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell3) | lia]
    | match goal with |- ?g => idtac "KEPTFAIL" g end ]).
    clear KcellC KgotC Kcell3 Kgot3.
    renvI HS AG E8 E19 E22 Usp st dst E8n E18n E25n Uspn B8n B18n.
    set (ZsF := fun a : Z => Zsm a \/ res <= a < res + (3 * nlp) \/ spZ regs - 96 - ESTACK <= a < spZ regs - 96).
    lazymatch type of KE with forall a, _ -> _ -> aview ?sg ?Hh ?mc a = aview _ _ ?m0 a =>
    assert (KE3 : forall a, 0 <= a < 2 ^ 64 -> ~ ZsF a -> aview sg Hh mem3 a = aview sg Hh m0 a)
    by (intros a Ha Hn; rewrite (Hfr3 a Ha) by (intros X; apply Hn; subst ZsF; cbn beta; right; first [left; exact X | right; exact X]);
        apply KE; [exact Ha | intros X; apply Hn; subst ZsF; cbn beta; left; exact X]) end.
    rename KE into KEc. rename KE3 into KE.
    lazymatch type of PR with forall a, apresent ?Hh ?m0 a -> apresent _ ?mc a =>
    assert (PR3 : forall a, apresent Hh m0 a -> apresent Hh mem3 a) by (intros a' Ha'; exact (Hpres3 a' (PR a' Ha'))) end.
    clear PR. rename PR3 into PR.
    assert (ZBF : forall a, SB <= a < kHighShadowEnd -> ~ ZsF a).
    { intros a Ha. subst ZsF. cbn beta. intros [X|[X|X]]; [exact (ZBsm a Ha X) | clear - Ha X HrHi HrqN2 C1 C2 C3 C4 C5; unfold rboxed in HrHi; unfold SB in Ha; lia | clear - Ha X HSPB HTS Has Hes C1 C2 C3 C4 C5; unfold SB, ESTACK in *; lia]. }
    shkOf KE ZBF SHK3.
    pose proof (RA_kept_band _ _ st 24 SHK3 ltac:(lia) ltac:(clear - Hst2 Hshi H47 C4; lia) RAstC) as RAst3.
    norm_ss HS. reshok_bx HS 22%nat.
    aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RBspan RFC_PRD.
    all: try (oblS RAst3 E19 E22).
    { awrI Uspn E18n E8n Hown EFA2. }
    unrunRD HFr Zsm Usp B8 Usp UNf. clear HF HFr. prStep HG PR.
    pose proof (st_ok_cut 200 _ _ _ HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HSJ.
    lazymatch type of HSJ with st_ok _ _ ?ssx _ => replace ssx with ssJ in HSJ by (vm_compute; reflexivity) end.
    rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11.
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
    apply SRr_ret. unfold rd_cut. split; [reflexivity|].
    lazymatch type of HSJ with st_ok _ ?Ej _ _ =>
    lazymatch goal with |- exists E2 r2 m2 d2 r c2, {| cfg_ms := mkst ?rg _ ?mF _; cfg_model := ?dd |} = _ /\ _ =>
    exists Ej, rg, mF, dd, 0, (curv + (3 * nlp)) end end.
    split. { reflexivity. }
    split. { exact HSJ. }
    split. { intros j Hj. rewrite ew_havoc_old by lia. rewrite ?ew_ewset_other by lia.
             first [reflexivity | rewrite AGX by exact Hj; rewrite ?ew_ewset_other by lia; reflexivity]. }
    split. { exact HJ3. }
    split. { rewrite R10. reflexivity. }
    split. { rewrite R11. agnorm. pose proof (denot_mul3 _ 51 nlp E51 Hnlp) as DM; cbn [sv_denot] in DM; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in DM; rewrite DM, E34, alu_add_small by (unfold M64; clear - HOK Hcurv Hcur Hnb Hnlp HnbM C1; unfold MALLOC_MAX in *; lia). reflexivity. }
    split. { left. split; [reflexivity|]. split; [exact HOK|]. split; [reflexivity|].
             intros i Hi.
             rewrite (UNf (res + i)) by first [clear - Hi HrCeil HrqN2 Hr4096 C1; lia | subst Zsm; cbn beta; intros [X|[X|X]];
               [clear - X Hi HrCeil HrqN2 HSPB HTS Has C1; lia
               | apply (HimgFS cid pos (res + i) HfinC); [left; unfold in_zr, frame_rng; cbn [fst snd]; clear - X Hdst1 Hdst2; lia | clear - Hi HrqN2; lia]
               | clear - X Hi HrCeil HrqN2 HSTB; lia]].
             rewrite (Heff3 i Hi). cbn beta iota.
             apply KEc; [clear - Hi Hpceil HOK Hcurv Hcur Hrq2 Hph C1; lia | subst Zsm; cbn beta; unfold rboxed in Hpdst; intros [X|[X|X]];
               [clear - X Hi Hpceil HOK Hcurv Hcur Hrq2 HSPB HTS Has C1; lia
               | clear - X Hi Hpceil HOK Hcurv Hcur Hrq2 Hph Hpdst Hdst1 Hdst2; lia
               | clear - X Hi Hpceil HOK Hcurv Hcur Hrq2 HSTB; lia]]. }
    split. { intros a Ha N1 N2 N3 N4.
             rewrite (UNf a Ha) by (subst Zsm; cbn beta; clear - N2 N3 N4 HTS Has Hes; unfold ESTACK in *; lia).
             apply KE; [exact Ha | subst ZsF Zsm; cbn beta; clear - N1 N2 N3 N4 HTS Has Hes; unfold ESTACK in *; lia]. }
    split. { exact PR. }
    repeat (apply same_io_wvb). eapply same_io_trans; [|exact Hio3]. repeat split; reflexivity.
  - rewrite branch_geu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
    rewrite (U_atom _ 33 nb), (U_atom _ 34 curv), (U_mul3 _ 51 nlp), zcanon_id in Hc by first [unfold M64; lia | enorm; agnorm; first [exact E33 | exact E51 | exact E34] | lia].
    assert (HKO : nb < curv + 3 * nlp) by (destruct (Z.ltb_spec nb (curv + 3 * nlp)); [lia | discriminate Hc]). clear Hc.
    norm_ss HS. reshok_bx HS 22%nat.
    aj_run_to_tok tfibtbl_lib_ok HS HJ2 SHOK RBspan RFC_PRD.
    { awrI Uspn E18n E8n Hown EFA2. }
    keStep HF HFr HG KE PR Zsm Usp B8 Usp.
    pose proof (st_ok_cut 200 _ _ _ HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HSJ.
    lazymatch type of HSJ with st_ok _ _ ?ssx _ => replace ssx with ssJ in HSJ by (vm_compute; reflexivity) end.
    rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11.
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
    apply SRr_ret. unfold rd_cut. split; [reflexivity|].
    lazymatch type of HSJ with st_ok _ ?Ej _ _ =>
    lazymatch goal with |- exists E2 r2 m2 d2 r c2, {| cfg_ms := mkst ?rg _ ?mF _; cfg_model := ?dd |} = _ /\ _ =>
    exists Ej, rg, mF, dd, (2 ^ 64 - 1), nb end end.
    split. { reflexivity. }
    split. { exact HSJ. }
    split. { intros j Hj. rewrite ew_havoc_old by lia. rewrite ?ew_ewset_other by lia. reflexivity. }
    split. { exact HJ2. }
    split. { rewrite R10. unfold w64. f_equal. }
    split. { rewrite R11. enorm. rewrite E33. reflexivity. }
    split. { right. split; [reflexivity|]. split; [exact HKO|]. split; [reflexivity|].
             intros i Hi. apply KE; [clear - Hi HrCeil HrqN2 Hr4096 C1; lia | subst Zsm; cbn beta; intros [X|[X|X]];
             [clear - X Hi HrCeil HrqN2 HSPB HTS Has C1; lia
             | apply (HimgFS cid pos (res + i) HfinC); [left; unfold in_zr, frame_rng; cbn [fst snd]; clear - X Hdst1 Hdst2; lia | clear - Hi HrqN2; lia]
             | clear - X Hi HrCeil HrqN2 HSTB; lia]]. }
    split. { intros a Ha N1 N2 N3 N4. apply KE; [exact Ha | subst Zsm; cbn beta; clear - N2 N3 N4 HTS Has Hes; unfold ESTACK in *; lia]. }
    split. { exact PR. }
    repeat split; reflexivity. }
  cbv beta. intros W3 c3 _ (-> & Ej3 & regs3 & mem3 & md3 & r6 & cur6 & -> & HS3 & AGX3 & HJ3 & Ha03 & Ha13 & Hr6 & Hfr3 & Hpres3 & Hio3).
  assert (HIO3 : same_io mdc md3) by (io_after Hio3). clear Hio3.
  replace (sp0 + (spZ regs - 96 - sp0)) with (spZ regs - 96) in Hfr3 by lia.
  vkeep Vp (w_H W2) mem3 ltac:(apply Hfr3; unfold rboxed in Hsd; clear - Hi HSTB Hst1 Hsd HrCeil HrqN2 HSPB HTS Has C1 Hes; unfold ESTACK in *; lia).
  vkeep Vn (w_H W2) mem3 ltac:(apply Hfr3; unfold rboxed in Hsd; clear - Hi HSTB Hst1 Hsd HrCeil HrqN2 HSPB HTS Has C1 Hes; unfold ESTACK in *; lia).
  clear Vc RAstC HARc AGX.
  rebaseJ HS HS3 AGX3 AG.
  renvI HS AG E8 E19 E22 Usp st dst E8n E18n E25n Uspn B8n B18n.
  rreg HS (10%bv : bv 5) Rr6. rewrite Ha03 in Rr6. symmetry in Rr6. unfold w64 in Rr6.
  rreg HS (11%bv : bv 5) Rc6. rewrite Ha13 in Rc6. symmetry in Rc6. unfold w64 in Rc6.
  assert (Hr6rng : 0 <= r6 < 2 ^ 64) by (clear - Hr6; destruct Hr6 as [(-> & _)|(-> & _)]; lia).
  assert (Hcb6 : cur <= cur6 <= nb) by (clear - Hr6 Hcurv Hnb Hcur Hnlp; destruct Hr6 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia).
  lazymatch type of Hfr3 with forall a, _ -> _ -> _ -> _ -> _ -> aview _ _ _ a = aview _ _ ?mY a =>
  assert (UN3 : forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + (3 * nlp) \/ st + 16 <= a < st + 24 \/ spZ regs - 96 - 32 - ESTACK <= a < spZ regs \/ dst <= a < dst + 16) ->
  aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mY a) end.
  { intros a Ha Hn. apply (Hfr3 a Ha); clear - Hn; lia. }
  pose proof (rfc_kept_stepE B _ _ _ _ _ _ _ _ _ _ _ _ (fun a => res <= a < res + req_size (3 * nlp)) KEPT4 HSEP UN3
  ltac:(intros a Ha; cbn beta in Ha |- *; clear - Ha HrqN2 HTS Has Hes; lia) ltac:(clear - HSPB; lia) ltac:(intros a Ha; cbn beta in Ha |- *; clear - Ha HrCeil; lia)
  ltac:(intros b m i Hb Hi Hin; cbn beta in Hin; pose proof (HsepB b m Hb) as Hd; clear - Hd Hi Hin; lia)
  ltac:(intros c p a Hcp Ha Hin; cbn beta in Hin; exact (HimgFS c p a Hcp Ha Hin))
  ltac:(intros a Ha Him; cbn beta in Ha; pose proof (tfib_img_range a Him) as Hir; clear - Ha Hir HrHi HrqN2; unfold rboxed in HrHi; lia)) as KEPT5.
  assert (SHK3 : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a).
  { intros a Ha. rewrite (UN3 a); [apply SHK2; exact Ha | clear - Ha C2; unfold SB in Ha; lia |].
  clear - Ha HrHi HrqN2 HSTB HSPB HDSTH HTS Has Hes C1 C2 C3 C4 C5. unfold rboxed in HrHi, HDSTH. unfold SB in Ha. lia. }
  pose proof (RA_kept_band _ _ st 24 SHK3 ltac:(lia) ltac:(clear - Hst2 Hshi H47 C4; lia) RAst2) as RAst3. clear RAst2.
  assert (RDP : r6 = 0 -> forall i, 0 <= i < 3 * nlp -> aview tfibsegs (w_H W2) mem3 (res + i) = aview tfibsegs (w_H W) memc (pdata + (curv + i))).
  { intros Hz i Hi. destruct Hr6 as [(_ & Hle & _ & Hcp)|(Hne & _)]; [|exfalso; clear - Hne Hz; lia].
  rewrite (Hcp i Hi). replace (pdata + curv + i) with (pdata + (curv + i)) by (clear; lia).
  apply (proj1 (proj2 KEPT4) pdata nb (curv + i) Hpd). clear - Hi Hle Hcurv Hcur Hnb; unfold req_size; destruct (Z.eqb_spec nb 0); lia. }
  assert (Hrc6 : rboxed ((r6 = 0 /\ cur6 = curv + 3 * nlp /\ curv + 3 * nlp <= nb) \/ (r6 = 2 ^ 64 - 1 /\ cur6 = nb /\ nb < curv + 3 * nlp)))
  by (clear - Hr6; unfold rboxed; destruct Hr6 as [(A1 & X & A2 & _)|(A1 & X & A2 & _)]; [left | right]; lia).
  assert (DRF : res + req_size (3 * nlp) <= frame_addr lyc cid pos \/ frame_addr lyc cid pos + fs_frame_bytes cid <= res).
  { pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ res (3 * nlp) cid pos HAR2 HrIn Hfin2) as D. rewrite EFA2 in D. unfold zdisjoint, block_rng, frame_rng in D. cbn [fst snd] in D. clear - D. lia. }
  clear Hr6 Ha03 Ha13.
  norm_ss HS. reshok_bx HS 22%nat.
  aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RBspan RFC_I.
  all: try (oblS RAst3 E19 E22).
  { awrI Uspn E18n E8n Hown EFA2. }
  unrunRD HFr Zsm Usp B8 Usp UNf. clear HF HFr HG.
  vkeepUN2 UNf Vp Vn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
  lazymatch type of UNf with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
  rkeep RDP (w_H W2) m2 ltac:(apply UNf; [clear - Hi Hr4096 HrCeil HrqN2 C1; lia | subst Zsm; cbn beta; clear - Hi HrqN2 DRF Hdst1 Hdst2 Hr4096 HrCeil HSPB HSTB HTS Has C1; lia]) end.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
  assert (SHKI : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W2) (ms_mem msX) a = aview tfibsegs (w_H W2) mem2 a) end.
  { intros a Ha. rewrite (UNf a) by first [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]. apply SHK3; exact Ha. }
  pose proof (RA_kept_band _ _ dst 32 SHKI ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst2) as RAdstI. clear SHKI.
  pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT5 HSEP UNf ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT. clear KEPT5.
  pose proof (Z_lor_bound r6 racc 64 ltac:(clear; lia) Hr6rng HR) as Hl6.
  lazymatch type of Rc6 with ew _ ?nc = _ => field_at HS 4%nat 19%nat st B18n 16 8%N nc cur6 Rc6 Vc end.
  lazymatch type of Rres with ew _ ?nr = _ => field_at HS 3%nat 8%nat dst B8n 0 8%N nr res Rres Vl end.
  field_at HS 3%nat 8%nat dst B8n 16 4%N 48%nat fattr E48 Vfa.
  field_at HS 3%nat 8%nat dst B8n 20 4%N 49%nat fgen E49 Vfg.
  field_at HS 3%nat 8%nat dst B8n 24 2%N 50%nat delay E50 Vde.
  field_at HS 3%nat 8%nat dst B8n 26 2%N 51%nat nlp E51 Vnl.
  field_at HS 3%nat 8%nat dst B8n 28 1%N 52%nat tidx E52 Vti.
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 3%nat _ HS ltac:(vm_compute; reflexivity)) as HRd; cbn [ms_mem restrict] in HRd;
  pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRs; cbn [ms_mem restrict] in HRs end.
  pose proof (zero_of_region _ _ 8%nat dst _ _ _ _ _ 8 8 (dst + 8) 8 HRd B8n ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as Vz.
  pose proof (rfc_frame_of_stackI _ _ regs _ _ _ _ _ HRs Uspn
  ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn; tauto|]); exfalso; clear - Hj; lia)
  ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn [nth rfc_saved Nat.add]; first [exact E36 | exact E37 | exact E38 | exact E39 | exact E40 | exact E41 | exact E42 | exact E43 | exact E44 | exact E45 | exact E46 | exact E47]|]); exfalso; clear - Hj; lia)) as HFR2.
  clear HRd HRs.
  assert (HnotBb : ~ In (res, 3 * nlp) Bb) by (intros Hb; pose proof (HsepB _ _ Hb) as Hd; clear - Hd HrqN1; lia).
  rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4. rreg HS (8%bv : bv 5) Q8. rreg HS (9%bv : bv 5) Q9.
  rreg HS (18%bv : bv 5) Q18. rreg HS (19%bv : bv 5) Q19. rreg HS (20%bv : bv 5) Q20. rreg HS (22%bv : bv 5) Q22. rreg HS (23%bv : bv 5) Q23.
  rreg HS (24%bv : bv 5) Q24. rreg HS (25%bv : bv 5) Q25. rreg HS (27%bv : bv 5) Q27.
  pose proof (denot_shx _ 19 22 16 st SB E18n E25n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D16. cbn [sv_denot] in D16. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D16.
  pose proof (denot_shx _ 19 22 8 st SB E18n E25n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D8. cbn [sv_denot] in D8. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D8.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ => change p with RFC_I end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
  lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem msX) _ _ |- _ =>
  eapply (RI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
  W2 (ms_regs msX) (ms_mem msX) mdX ly2 S2 (k + 1) (Z.lor r6 racc) cur6 res nlp fattr fgen delay tidx [(res, 3 * nlp)] T (0 + mo_malloc MT (3 * nlp)) P);
  [ exact RC | exact HPL | exact (mle_station MT Sc Sc S2 0 (mo_malloc MT (3 * nlp)) MTL HMLE HMLE2)
    | pose proof (mo_malloc_mono MT MTL (3 * nlp) 196605 ltac:(clear - Hnlp; lia)) as Hmm; clear - Hmm; lia
  | exact Hhdrv
  | unfold rfc_progP, palsz; destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Hb0|Hb0']; [exfalso; exact (Hbit Hb0)|];
    unfold rboxed in Hrc6;
    destruct (Z.eq_dec (Z.lor r6 racc) 0) as [Hz|Hnz];
    [ pose proof (proj1 (Z.lor_eq_0_iff _ _) Hz) as [Hz2 Hz1]; left;
      destruct HprogH as [(_ & Hfit & Ecv) | (Hne & _)]; [| exfalso; exact (Hne Hz1)];
      split; [exact Hz|]; split; [clear - Hz2 Hrc6 Hfit Ecv; lia|]; split; [clear - Hz2 Hrc6 Ecv; lia|];
      intros _; apply garr8_of_aview; intros j Hj;
      rewrite firstn_length_le in Hj by (rewrite length_skipn; clear - Hz2 Hrc6 Ecv HlenP Hcur Hnlp; lia);
      rewrite slice_nth by (rewrite firstn_length_le by (rewrite length_skipn; clear - Hz2 Hrc6 Ecv HlenP Hcur Hnlp; lia); exact Hj);
      rewrite (RDP Hz2 (Z.of_nat j)) by (clear - Hj; lia);
      replace (pdata + (curv + Z.of_nat j)) with (pdata + Z.of_nat (Z.to_nat (cur + 9) + j)) by (clear - Ecv Hcur; lia);
      rewrite (garr8_aview _ _ _ _ HPL) by (clear - Hj Hz2 Hrc6 Ecv HlenP Hcur; lia); reflexivity
    | right; split; [exact Hnz|];
      assert (Hcase : racc <> 0 \/ r6 <> 0) by (destruct (Z.eq_dec racc 0) as [Z0|Z0]; [right; intros Zp; apply Hnz; rewrite Z0, Zp; reflexivity | left; exact Z0]);
      destruct HprogH as [(Hz1 & Hfit & Ecv) | (Hne & Hsh & Ecv)];
      [ destruct Hcase as [X|X]; [exfalso; exact (X Hz1) | clear - X Hrc6 Hfit Ecv Hnlp; lia]
      | clear - Hrc6 Hsh Ecv Hnlp Hcurv; lia ] ]
  | exact HJc | clear; lia | exact Hfrs2 | exact HPerm2
  |   unfold rfc_pal; destruct (Z.eqb_spec (Z.land fattr 1) 0) as [X|X]; [exfalso; exact (Hbit X)|];
      split; [reflexivity|]; split; [intros X2; exfalso; exact (Hbit X2)|]; split;
      [ intros b [<-|[]]; split; [exact Tpal | intros lyq blc i Hin Hi; cbn [fst snd] in Hin, Hi |- *; exact (Apal blc i lyq Hin Hi)]
      | intros b m [Hb|[]]; injection Hb as <- <-; split; [exact Hr4096 | exact HnotBb] ]
  | unfold rfc_vals; split; [exact Hl6|]; split; [exact Hcb6|]; split; [clear - Hr4096 HrCeil HrqN1 C1; lia|]; split; [exact Hnlp|]; split; [exact Hfattr|]; split; [exact Hfgen|]; split; [exact Hdelay | exact Htidx]
  | unfold I_regs_at, w64; rewrite Q23, Q24, D16, D8, Q25, Rr6, (AG 25%nat), E25, (rfcJ_alu_or_lits r6 racc Hr6rng HR) by lia;
    rewrite Q2, Q3, Q4, Q8, Q18, Q19, Q22, Q9, Q20, Q27; enorm; agnorm; rewrite ?B19;
    rewrite E3, E4, E8, E18, E19, E22, E27, <- Usp, Z_to_bv_bv_unsigned;
    repeat split; reflexivity
  | exact HFR2
  | unfold rfc_memI; split; [exact Vp|]; split; [exact Vn|]; split; [exact Vc|]; split; [exact Vl|]; split; [exact Vz|]; split; [exact Vfa|]; split; [exact Vfg|]; split; [exact Vde|]; split; [exact Vnl | exact Vti]
  | exact RAdstI
  | exact KEPT
  | io_now ] end end.
Qed.
End RJ.
End d.
