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
UI1e UI1i YI07 YP14 YI08 YI0c YI0g UI3h.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UIZ5.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac kw_next HF HU KWo KWn sp memc :=
lazymatch type of HF with frame_of _ _ _ ?m' =>
assert (KWn : forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 64 <= x < sp) -> mbyte ubs2segs m' x = mbyte ubs2segs memc x)
by (intros x Hx Hnx; mb_frame_g HF; [apply KWo; assumption | rewrite HU; lia]) end; clear HF KWo.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition CH_LOOP : Z := Eval vm_compute in (ubs2_A_col_hash + 0xcc).
Definition CH_BRET : Z := Eval vm_compute in (ubs2_A_col_hash + 0x104).
Definition CH_FRAME : Z := 64.
Definition LAY_CHF : layout_t := [(0, 8%N); (8, 8%N); (16, 8%N); (24, 8%N); (32, 8%N); (40, 8%N); (48, 8%N); (56, 8%N)].
Definition chf_vals (regs : bvmap 5 word) : list Z :=
[bv_unsigned (getr regs 22); bv_unsigned (getr regs 21); bv_unsigned (getr regs 20); bv_unsigned (getr regs 19);
bv_unsigned (getr regs 18); bv_unsigned (getr regs 9); bv_unsigned (getr regs 8); bv_unsigned (getr regs 1)].
Lemma u64_range' : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in H. lia. Qed.
Lemma obj_at_chf : forall (m : word -> option byte) a regs,
word_mem ubs2segs m (a + 56) (bv_unsigned (getr regs 1)) -> word_mem ubs2segs m (a + 48) (bv_unsigned (getr regs 8)) ->
word_mem ubs2segs m (a + 40) (bv_unsigned (getr regs 9)) -> word_mem ubs2segs m (a + 32) (bv_unsigned (getr regs 18)) ->
word_mem ubs2segs m (a + 24) (bv_unsigned (getr regs 19)) -> word_mem ubs2segs m (a + 16) (bv_unsigned (getr regs 20)) ->
word_mem ubs2segs m (a + 8) (bv_unsigned (getr regs 21)) -> word_mem ubs2segs m a (bv_unsigned (getr regs 22)) ->
obj_at ubs2segs m a LAY_CHF (chf_vals regs).
Proof.
intros m a regs W1 W8 W9 W18 W19 W20 W21 W22. cbn [obj_at LAY_CHF chf_vals]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add].
rewrite Z.add_0_r.
repeat split; try (apply val_mem_word_mem; assumption); apply u64_range'.
Qed.
Definition CH_KEPT : list reg := [3; 4; 23; 24; 25; 26; 27]%bv.
Definition BCMP_CLOB : list reg := [10; 11; 12; 13; 14]%bv.
Definition ss_loop : sstate :=
mkSS CH_LOOP (sr_set sr_atoms 22%bv (SLit 1))
[ YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (obj_chunks_from LAY_CHF 32) ;
YQ0b.mkRegion (Some 10%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 40%nat 0))] ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - 1) 0);
(8%nat, mkAF 1 (2^30) 0); (9%nat, mkAF 4096 CEIL_MAX 0); (18%nat, mkAF 4096 CEIL_MAX 0);
(19%nat, mkAF 4096 CEIL_MAX 0); (20%nat, mkAF 0 (2^30) 0);
(21%nat, mkAF (2^64 - 1 - CEIL_MAX) (2^64 - 1 - 4096) 0); (40%nat, mkAF 0 255 0) ] [] []).
Definition ch_facts : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + 64) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - 3) 0); (11%nat, mkAF 4096 (CEIL_MAX - 3) 0);
(12%nat, mkAF 4096 (CEIL_MAX - 1) 0); (13%nat, mkAF 1 (2^30) 0) ].
Definition ss_ch : sstate :=
mkSS ubs2_A_col_hash sr_atoms [ YQ0b.mkRegion (Some 2%nat) (-64) 0 (-64) 0 [] ] None (mkFacts ch_facts [] []).
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Section d.
Variables (regs : bvmap 5 word) (memc : word -> option byte) (STK sp0 : Z) (FP : list (Z * Z))
(L : layout) (A : astate) (mem : word -> option byte) (md : Model) (Lc : layout) (Ac : astate) (mdc : Model)
(rgb kp u T : Z) (used keys : list Z) (c : colour) (r js : Z).
Let sp : Z := spZ regs.
Let h0 : Z := hash0 T c.
Hypothesis Hra : YK0s.ret_ok (getr regs 1). Hypothesis Hal : sp mod 16 = 0.
Hypothesis Hsplo : alloc_ceiling + 64 <= sp. Hypothesis Hsphi : sp <= 2 ^ 63.
Hypothesis Hcol : col3 ubs2segs memc rgb c.
Hypothesis Hused : arr8 ubs2segs memc u used. Hypothesis Hkeys : arr8 ubs2segs memc kp keys.
Hypothesis LU : zlen used = T. Hypothesis LK : zlen keys = 3 * T. Hypothesis RT : 0 < T < 2 ^ 30.
Hypothesis Rrgb0 : 4096 <= rgb. Hypothesis Rrgb1 : rgb + 3 <= alloc_ceiling.
Hypothesis Ru0 : 4096 <= u. Hypothesis Ru1 : u + T <= alloc_ceiling.
Hypothesis Rk0 : 4096 <= kp. Hypothesis Rk1 : kp + 3 * T <= alloc_ceiling.
Hypothesis Hjs : 0 <= js < T. Hypothesis Hr : r = cyc T h0 js.
Hypothesis Hstop : forall i, 0 <= i <= js -> slot_stop (HT0 T used keys) c (cyc T h0 i) = (i =? js).
Definition ch_post (c' : config) : Prop :=
exists regs2 mem2,
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 r /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - COLHASH_STK <= a < sp) -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
Definition at_loop (j : Z) (regs1 : bvmap 5 word) (mem1 : word -> option byte) : Prop :=
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem1 mdc /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - CH_FRAME <= a < sp) -> mbyte ubs2segs mem1 a = mbyte ubs2segs memc a) /\
obj_at ubs2segs mem1 (sp - 64) LAY_CHF (chf_vals regs) /\
getr regs1 2 = Z_to_bv 64 (sp - 64) /\
getr regs1 20 = Z_to_bv 64 (cyc T h0 j) /\ getr regs1 10 = Z_to_bv 64 (u + cyc T h0 j) /\
getr regs1 8 = Z_to_bv 64 T /\ getr regs1 9 = Z_to_bv 64 u /\ getr regs1 18 = Z_to_bv 64 kp /\ getr regs1 19 = Z_to_bv 64 rgb /\
getr regs1 21 = Z_to_bv 64 (2 ^ 64 - 1 - u) /\ getr regs1 22 = Z_to_bv 64 1 /\
(forall rr, In rr CH_KEPT -> getr regs1 rr = getr regs rr).
Lemma ch_body : forall j regs1 mem1,
0 <= j <= js -> at_loop j regs1 mem1 ->
(forall regs' mem', j + 1 <= js -> at_loop (j + 1) regs' mem' ->
SR ubs2segs (mkCfg (mkst regs' (Z_to_bv 64 CH_LOOP) mem' (seg_rom ubs2segs)) mdc) ch_post) ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 CH_LOOP) mem1 (seg_rom ubs2segs)) mdc) ch_post.
Proof.
intros j regs1 mem1 Hj (HJ & Hfr & Hobj & G2 & G20 & G10 & G8 & G9 & G18 & G19 & G21 & G22 & GK) K.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (hj := cyc T h0 j) in *.
assert (Rhj : 0 <= hj < T) by (subst hj; apply cyc_range; lia).
destruct (arr8_getz ubs2segs memc u used hj Hused ltac:(lia)) as [Bu Ru'].
set (ub := getz used hj) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) (chf_vals regs ++ [ub]) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE40 : ew E 40 = Z_to_bv 64 ub) by (subst E; apply (Ereg_vals regs1 _ [] 8%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = u + hj) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 T) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE9 : ew E 9 = Z_to_bv 64 u) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE18 : ew E 18 = Z_to_bv 64 kp) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE19 : ew E 19 = Z_to_bv 64 rgb) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE20 : ew E 20 = Z_to_bv 64 hj) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HE21 : ew E 21 = Z_to_bv 64 (2 ^ 64 - 1 - u)) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (HE10 : ew E 10 = Z_to_bv 64 (u + hj)) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (Bu1 : mbyte ubs2segs mem1 (u + hj) = Some (Z_to_bv 8 ub)) by (rewrite Hfr by (unfold CH_FRAME; lia); exact Bu).
assert (HS : st_ok ubs2segs E ss_loop (mkst regs1 (Z_to_bv 64 CH_LOOP) mem1 (seg_rom ubs2segs))).
{ unfold ss_loop. subst E. apply entry_st_ok_gen.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite G22; reflexivity].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply (region_ok_obj ubs2segs _ mem1 2 (sp - 64)); [exact HU2 | lia | lia | exact Hobj | reflexivity | | intros i Hi; lia].
intros jj v Hjj. apply (Ereg_vals regs1 _ [] jj v). rewrite nth_error_app1; [exact Hjj | apply nth_error_Some; congruence].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ ub); [cbn [sv_denot]; rewrite Z.add_0_r, HE40, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. rewrite Z.add_0_r. apply val_mem_byte; [exact Bu1 | lia].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU10.
repeat split; try exact I. first [left; lia | right; lia].
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HE8, HE9, HE18, HE19, HE20, HE21, HE40, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
assert (Hal64 : (sp - 64) mod 16 = 0) by (replace (sp - 64) with (sp + (-4) * 16) by lia; rewrite Z.mod_add; [exact Hal | lia]).
repeat split; lia. }
assert (HV : forall jj v, nth_error (chf_vals regs ++ [ub]) jj = Some v -> ew E (32 + jj) = Z_to_bv 64 v) by (intros jj v Hjj; subst E; apply Ereg_vals; exact Hjj).
assert (HE32 : ew E 32 = getr regs 22) by (etransitivity; [exact (HV 0%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]).
assert (HE33 : ew E 33 = getr regs 21) by (etransitivity; [exact (HV 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]).
assert (HE34 : ew E 34 = getr regs 20) by (etransitivity; [exact (HV 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]).
assert (HE35 : ew E 35 = getr regs 19) by (etransitivity; [exact (HV 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]).
assert (HE36 : ew E 36 = getr regs 18) by (etransitivity; [exact (HV 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]).
assert (HE37 : ew E 37 = getr regs 9) by (etransitivity; [exact (HV 5%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]).
assert (HE38 : ew E 38 = getr regs 8) by (etransitivity; [exact (HV 6%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]).
assert (HE39 : ew E 39 = getr regs 1) by (etransitivity; [exact (HV 7%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]).
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 CH_LOOP) mem1 (seg_rom ubs2segs))) in HJ.
clearbody E. clear HV.
assert (EXIT : forall E' ss ms', st_ok ubs2segs E' ss ms' -> env_agree 41 E E' -> ss_resv ss = None ->
clookup ubs2tbl (ss_pc ss) = Some RET_WORD ->
sr_get (ss_regs ss) 1 = SOff 39 0 -> sr_get (ss_regs ss) 2 = SOff 2 64 ->
sr_get (ss_regs ss) 8 = SOff 38 0 -> sr_get (ss_regs ss) 9 = SOff 37 0 -> sr_get (ss_regs ss) 18 = SOff 36 0 ->
sr_get (ss_regs ss) 19 = SOff 35 0 -> sr_get (ss_regs ss) 20 = SOff 34 0 -> sr_get (ss_regs ss) 21 = SOff 33 0 ->
sr_get (ss_regs ss) 22 = SOff 32 0 -> sr_get (ss_regs ss) 10 = SOff 20 0 ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) CH_KEPT = true ->
hj = r ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall x, ms_mem ms' x = mem1 x) ->
SR ubs2segs (mkCfg ms' mdc) ch_post).
{ intros E' ss ms' HS' EA Hrv Hpc Q1 Q2 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q10 QK Hhr HJ' Hm'.
destruct EA as [EA ED].
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ')) as (Hh & Hl & _).
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | exact Hh | exact Hl | exact HS' | exact Hrv | exact Hpc |].
assert (RG : forall (rr : reg) e, sr_get (ss_regs ss) rr = e -> getr (ms_regs ms') rr = sv_denot E' e).
{ intros rr e He. rewrite <- He. apply (st_ok_reg _ _ _ _ rr HS'). }
assert (R1 : getr (ms_regs ms') 1 = getr regs 1).
{ rewrite (RG _ _ Q1). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE39 by lia. apply Z_to_bv_bv_unsigned. }
exists (ms_regs ms'), (ms_mem ms'). split; [rewrite R1, Hra; reflexivity|]. split; [exact HJ'|]. split; [|split].
-
assert (GK' : forall rr, In rr CH_KEPT -> getr (ms_regs ms') rr = getr regs rr).
{ intros rr Hrr. rewrite <- (GK rr Hrr).
apply (regs_kept_of_st_ok ubs2segs E' ss ms' regs1 [] CH_KEPT HS'); [|exact QK|exact Hrr].
eapply env_agree_trans; [exact EA0 | split; [intros n Hn; apply EA; lia | exact ED]]. }
apply regs_preserved_intro_g.
+ rewrite (RG _ _ Q2). cbn [sv_denot]. rewrite EA by lia. rewrite (HE 2%nat 2%bv eq_refl), G2, unsigned_lit_small by lia.
unfold sp. rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs 2)). f_equal. unfold spZ. lia.
+ apply GK'. cbv; auto 10.
+ apply GK'. cbv; auto 10.
+ rewrite (RG _ _ Q8). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE38 by lia. apply Z_to_bv_bv_unsigned.
+ rewrite (RG _ _ Q9). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE37 by lia. apply Z_to_bv_bv_unsigned.
+ rewrite (RG _ _ Q18). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE36 by lia. apply Z_to_bv_bv_unsigned.
+ rewrite (RG _ _ Q19). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE35 by lia. apply Z_to_bv_bv_unsigned.
+ rewrite (RG _ _ Q20). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE34 by lia. apply Z_to_bv_bv_unsigned.
+ rewrite (RG _ _ Q21). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE33 by lia. apply Z_to_bv_bv_unsigned.
+ rewrite (RG _ _ Q22). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE32 by lia. apply Z_to_bv_bv_unsigned.
+ apply GK'. cbv; auto 10.
+ apply GK'. cbv; auto 10.
+ apply GK'. cbv; auto 10.
+ apply GK'. cbv; auto 10.
+ apply GK'. cbv; auto 10.
- rewrite (RG _ _ Q10). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE20, <- Hhr by lia. rewrite unsigned_lit_small by lia. reflexivity.
- intros a Ha Hna. unfold mbyte. rewrite Hm'. fold (mbyte ubs2segs mem1 a). apply Hfr; [exact Ha|]. unfold CH_FRAME, COLHASH_STK in *. lia. }
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_bcmp. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms x = mem1 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
pose proof (Hstop j Hj) as Hsj. fold hj in Hsj. rewrite slot_stop_HT0 in Hsj. fold ub in Hsj.
jbranch ubs2tbl HS.
-
rewrite branch_eq_U, (U_atom E 40 ub HE40), U_lit in Hc by lia.
rewrite Hc in Hsj. cbn [orb] in Hsj. symmetry in Hsj. apply Z.eqb_eq in Hsj.
jrun LAWS ubs2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (EXIT _ _ _ HS); [apply env_agree_refl | reflexivity | vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| vm_compute; reflexivity | subst hj; rewrite Hsj; symmetry; exact Hr | exact HJ | ].
intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1.
-
rewrite branch_eq_U, (U_atom E 40 ub HE40), U_lit in Hc by lia.
rewrite Hc in Hsj. cbn [orb] in Hsj. clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_bcmp. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall x, ms_mem ms0 x = mem1 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG K1.
jbranch ubs2tbl HS.
{ exfalso. rewrite branch_ltu_U in Hc.
rewrite (U_add_mul3' E 20 18 hj kp HE20 ltac:(lia) HE18 ltac:(lia) ltac:(lia)) in Hc.
rewrite (U_atom E 18 kp HE18) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_bcmp. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HS with st_ok _ _ _ ?m => rename m into msB end.
assert (K3 : forall x, ms_mem msB x = mem1 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF HG K2.
jreg HS (10%bv:reg) as Hb0. rewrite HE19 in Hb0.
assert (Hb1 : getr (ms_regs msB) 11 = Z_to_bv 64 (kp + 3 * hj)).
{ eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get.
apply (U_add_mul3' E 20 18 hj kp HE20 ltac:(lia) HE18 ltac:(lia) ltac:(lia)). }
jreg HS (12%bv:reg) as Hb2. jreg HS (1%bv:reg) as Hbra.
destruct Hcol as (C0 & C1 & C2 & Cok).
assert (MB : forall a, 0 <= a < alloc_ceiling -> mbyte ubs2segs (ms_mem msB) a = mbyte ubs2segs memc a).
{ intros a Ha. unfold mbyte. rewrite K3. fold (mbyte ubs2segs mem1 a). apply Hfr; [lia|]. unfold CH_FRAME. lia. }
destruct (arr8_getz ubs2segs memc kp keys (3 * hj) Hkeys ltac:(lia)) as [Bk0 Rk0'].
destruct (arr8_getz ubs2segs memc kp keys (3 * hj + 1) Hkeys ltac:(lia)) as [Bk1 Rk1'].
destruct (arr8_getz ubs2segs memc kp keys (3 * hj + 2) Hkeys ltac:(lia)) as [Bk2 Rk2'].
set (lb := [Z_to_bv 8 (cR c); Z_to_bv 8 (cG c); Z_to_bv 8 (cB c)]).
set (rb := [Z_to_bv 8 (getz keys (3 * hj)); Z_to_bv 8 (getz keys (3 * hj + 1)); Z_to_bv 8 (getz keys (3 * hj + 2))]).
destruct (ubs2_bcmp lb rb _ _ _ (ms_mem msB) (seg_rom ubs2segs) (ms_regs msB) Hb0 Hb1 Hb2) as (regs2 & Hms & Hres & Hfr2).
{ rewrite unsigned_lit_small by lia. reflexivity. }
{ reflexivity. }
{ change (length lb) with 3%nat. apply rdn3_of_mbytes; rewrite MB by lia; assumption. }
{ change (length lb) with 3%nat. apply rdn3_of_mbytes; rewrite MB by lia;
[exact Bk0 | replace (kp + 3 * hj + 1) with (kp + (3 * hj + 1)) by lia; exact Bk1 | replace (kp + 3 * hj + 2) with (kp + (3 * hj + 2)) by lia; exact Bk2]. }
{ rewrite unsigned_lit_small by lia. change (length lb) with 3%nat. lia. }
{ rewrite unsigned_lit_small by lia. change (length lb) with 3%nat. lia. }
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
replace (v_jalr (getr (ms_regs msB) 1) 0) with (Z_to_bv 64 CH_BRET).
2:{ rewrite Hbra. symmetry. apply ret_ok_even. vm_compute. reflexivity. }
jafter_stretch_keep HS 41%nat regs2 (ms_mem msB) BCMP_CLOB CH_BRET [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2; intros ->; vm_compute in Hrr; discriminate Hrr. }
{ repeat (apply Forall_cons); try apply Forall_nil; apply (region_kept_same ubs2segs). }
clear HS. rename HS2 into HS.
change (ms_mem msB) with (ms_mem (mkst regs2 (Z_to_bv 64 CH_BRET) (ms_mem msB) (seg_rom ubs2segs))) in HJ.
assert (EA1 : env_agree 41 E (havoc E 41 (map (getr regs2) BCMP_CLOB))) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (H41 : ew (havoc E 41 (map (getr regs2) BCMP_CLOB)) 41 = Z_to_bv 64 (memcmp_spec lb rb)).
{ rewrite <- Hres. etransitivity; [apply (ew_havoc_new E 41 _ 0%nat (Z_to_bv 64 0)); cbn; lia | reflexivity]. }
assert (Hzero : Z_to_bv 64 (memcmp_spec lb rb) = Z_to_bv 64 0 <-> col_at keys hj = c).
{ rewrite (ubs2_memcmp_zero_iff lb rb eq_refl). subst lb rb. apply key_bytes_eq_iff; [exact Cok | lia | lia | lia]. }
jbranch ubs2tbl HS.
+
cbn [branch_taken sv_denot] in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, H41 in Hc. apply bv_eqb_eq in Hc.
apply Hzero in Hc. rewrite <- Hc, colour_eqb_refl in Hsj. symmetry in Hsj. apply Z.eqb_eq in Hsj.
jrun LAWS ubs2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (EXIT _ _ _ HS); [exact EA1 | reflexivity | vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| vm_compute; reflexivity | subst hj; rewrite Hsj; symmetry; exact Hr | exact HJ | ].
intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3.
+
cbn [branch_taken sv_denot] in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, H41 in Hc.
assert (Hjs' : j + 1 <= js).
{ destruct (Z.eqb_spec j js) as [Ej|]; [|lia]. exfalso. apply (proj1 (colour_eqb_spec _ _)) in Hsj.
apply Hzero in Hsj. rewrite Hsj, bv_eqb_refl in Hc. discriminate Hc. }
jrun_to LAWS ubs2tbl_ok HS HJ CH_LOOP. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HS with st_ok _ _ _ ?m => rename m into msL end.
assert (K4 : forall x, ms_mem msL x = mem1 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
assert (EA2 : env_agree 32 (Ereg regs1 []) Ef) by (eapply env_agree_trans; [exact EA0 | eapply env_agree_le; [| exact EA1]; lia]);
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs1 [] CH_KEPT HS EA2 ltac:(vm_compute; reflexivity)) as HKR;
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs1 [] [2; 8; 9; 18; 19; 21]%bv HS EA2 ltac:(vm_compute; reflexivity)) as HKR2 end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
apply K; [exact Hjs'|]. unfold at_loop. cbn [ms_regs ms_mem mkst].
split; [exact HJ|]. split. { intros a Ha Hna. rewrite <- (Hfr a Ha Hna). unfold mbyte. rewrite (K4 (Z_to_bv 64 a)). reflexivity. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ 64); [exact Hobj | reflexivity | intros i Hi; unfold mbyte; rewrite (K4 (Z_to_bv 64 (sp - 64 + i))); reflexivity]. }
split; [rewrite (HKR2 2%bv ltac:(cbv; auto 10)); exact G2|].
split. { eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get. rewrite cyc_succ by lia. fold hj.
apply (U_sv_next _ 20 8 hj T); [ew_havoc; exact HE20 | ew_havoc; exact HE8 | lia | lia]. }
split. { eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get. rewrite cyc_succ by lia. fold hj.
apply (U_u_next _ 9 20 8 u hj T); [ew_havoc; exact HE9 | ew_havoc; exact HE20 | ew_havoc; exact HE8 | lia | lia | lia | lia]. }
split; [rewrite (HKR2 8%bv ltac:(cbv; auto 10)); exact G8|].
split; [rewrite (HKR2 9%bv ltac:(cbv; auto 10)); exact G9|].
split; [rewrite (HKR2 18%bv ltac:(cbv; auto 10)); exact G18|].
split; [rewrite (HKR2 19%bv ltac:(cbv; auto 10)); exact G19|].
split; [rewrite (HKR2 21%bv ltac:(cbv; auto 10)); exact G21|].
split. { eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get. apply U_lit. lia. }
intros rr Hrr. rewrite (HKR rr Hrr). apply GK. exact Hrr.
Qed.
Lemma ch_loop : forall n j regs1 mem1, js - j <= Z.of_nat n -> 0 <= j <= js -> at_loop j regs1 mem1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 CH_LOOP) mem1 (seg_rom ubs2segs)) mdc) ch_post.
Proof.
induction n as [|n IH]; intros j regs1 mem1 Hn Hj HA.
- apply (ch_body j regs1 mem1 Hj HA). intros regs' mem' Hj' _. exfalso. cbn in Hn. lia.
- apply (ch_body j regs1 mem1 Hj HA). intros regs' mem' Hj' HA'.
apply (IH (j + 1)); [rewrite Nat2Z.inj_succ in Hn; lia | lia | exact HA'].
Qed.
End d.
Theorem ubs2_col_hash : col_hash_spec API.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs rgb kp u T fmt used keys c op r
HJ Hra Hal Hlo Hhi G10 G11 G12 G13 G14 Hpix Hused Hkeys LU LK RT Rrgb0 Rrgb1 Ru0 Ru1 Rk0 Rk1 Hprobe.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof HJ as (HH0 & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
set (sp := spZ regs) in *.
assert (Hsplo : alloc_ceiling + 64 <= sp) by (unfold COLHASH_STK in Hlo; lia).
pose proof Hpix as [Hcol Hfmt]. pose proof Hcol as (C0 & C1 & C2 & Cok). pose proof Cok as (Rr & Rg & Rb).
assert (Rf : fmt = 3 \/ fmt = 4) by (destruct Hfmt as [[-> _] | (-> & _)]; [left | right]; reflexivity).
set (E := Ereg regs []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = rgb) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs2segs E ss_ch (mkst regs (Z_to_bv 64 ubs2_A_col_hash) memc (seg_rom ubs2segs))).
{ unfold ss_ch. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
apply (region_ok_stack ubs2segs _ memc 2 sp); [exact HU2 | lia | lia | intros x Hx; apply Hstw; unfold COLHASH_STK in Hlo; lia].
- cbn [pairwise_disjoint all_disjoint]. repeat split; try exact I.
- cbn [atoms_ok ch_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, (HE 11%nat 11%bv eq_refl), G11, (HE 12%nat 12%bv eq_refl), G12, (HE 13%nat 13%bv eq_refl), G13, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
repeat split; lia. }
assert (EA0 : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_refl).
change memc with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_col_hash) memc (seg_rom ubs2segs))) in HJ.
clearbody E.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_getPixelVal.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; unfold COLHASH_STK in Hlo; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (KW0 : forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 64 <= x < sp) -> mbyte ubs2segs (ms_mem ms) x = mbyte ubs2segs memc x).
{ intros x Hx Hnx. mb_frame_g HF; [reflexivity | rewrite HU2; lia]. }
clear HF HG.
jreg HS (1%bv:reg) as Cra. jreg HS (10%bv:reg) as Ca0. jreg HS (11%bv:reg) as Ca1.
rewrite (HE 10%nat 10%bv eq_refl), G10 in Ca0. rewrite (HE 14%nat 14%bv eq_refl), G14 in Ca1.
assert (HpixC : pixel_at ubs2segs (ms_mem ms) rgb fmt c op).
{ apply (pixel_at_frame memc); [exact Hpix | intros a Ha; apply KW0; lia]. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ => change p with ubs2_A_getPixelVal end.
eapply SR_bind.
{ eapply (ubs2_getPixelVal API IMG STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc (ms_regs ms) rgb fmt c op HJ);
[ rewrite Cra; apply ret_ok_even; vm_compute; reflexivity | exact Ca0 | exact Ca1 | exact HpixC | lia | lia ]. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & HP2 & Ha02 & Hm2). clear HJ.
rewrite Cra.
jafter_call_keep HS 32%nat regs2 mem2 HP2 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ apply Forall_cons; [apply region_kept_ext; exact Hm2 | apply Forall_nil]. }
clear HS. rename HS2 into HS. rename HJ2 into HJ.
lazymatch type of HS with st_ok _ _ _ ?mX => change mem2 with (ms_mem mX) in HJ end.
set (E2 := havoc E 32 (map (getr regs2) CLOB)) in *.
assert (HE36 : ew E2 36 = Z_to_bv 64 (pixel_val c op)).
{ rewrite <- Ha02. subst E2. etransitivity; [apply (ew_havoc_new E 32 _ 4%nat (Z_to_bv 64 0)); cbn; lia | reflexivity]. }
assert (EA2 : env_agree 32 E E2) by (subst E2; apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (EAr : env_agree 32 (Ereg regs []) E2) by (subst E2; apply env_agree_havoc_ge; [lia | exact EA0]).
assert (HU2' : bv_unsigned (ew E2 2) = sp) by (rewrite (proj1 EA2) by lia; exact HU2).
assert (HE2 : forall n (rr : reg), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew E2 n = getr regs rr).
{ intros n rr Hn Hr. rewrite (proj1 EA2) by exact Hn. apply HE. exact Hr. }
clearbody E2.
set (A0 := if op then 255 else 0).
assert (RA : 0 <= A0 < 256) by (subst A0; destruct op; lia).
assert (HpU : U E2 (SOff 36 0) = A0 * 2 ^ 24 + cB c * 2 ^ 16 + cG c * 2 ^ 8 + cR c).
{ rewrite (U_atom E2 36 (pixel_val c op) HE36) by (unfold pixel_val; destruct op; lia). unfold pixel_val. subst A0. destruct op; lia. }
assert (KW1 : forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 64 <= x < sp) -> mbyte ubs2segs mem2 x = mbyte ubs2segs memc x).
{ intros x Hx Hnx. unfold mbyte. rewrite Hm2. fold (mbyte ubs2segs (ms_mem ms) x). apply KW0; assumption. }
clear KW0.
jrun_to LAWS ubs2tbl_ok HS HJ CH_LOOP.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2' | cbn [r_wlo r_whi]; intros _; unfold COLHASH_STK in Hlo; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
kw_next HF HU2' KW1 KW2 sp memc. clear HG.
jbranch ubs2tbl HS.
-
rewrite branch_ne_U, (U_pix_alpha E2 (SOff 36 0) A0 c Cok RA HpU), U_SLit in Hc.
assert (Hop : op = true) by (destruct op; [reflexivity | subst A0; vm_compute in Hc; discriminate Hc]).
clear Hc.
assert (E2_11 : ew E2 11 = Z_to_bv 64 kp) by (rewrite (HE2 11%nat 11%bv) by (lia || reflexivity); exact G11).
assert (E2_12 : ew E2 12 = Z_to_bv 64 u) by (rewrite (HE2 12%nat 12%bv) by (lia || reflexivity); exact G12).
assert (E2_13 : ew E2 13 = Z_to_bv 64 T) by (rewrite (HE2 13%nat 13%bv) by (lia || reflexivity); exact G13).
assert (E2_10 : ew E2 10 = Z_to_bv 64 rgb) by (rewrite (HE2 10%nat 10%bv) by (lia || reflexivity); exact G10).
assert (HhU : U E2 (sv_hashx (SOff 36 0) 13) = hash0 T c) by (exact (U_hashx E2 (SOff 36 0) 13 A0 c T Cok RA HpU E2_13 RT)).
pose proof (hash0_range T c ltac:(lia)) as Rh0.
jrun_to LAWS ubs2tbl_ok HS HJ CH_LOOP.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2' | cbn [r_wlo r_whi]; intros _; unfold COLHASH_STK in Hlo; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
kw_next HF HU2' KW2 KW3 sp memc. clear HG.
jbranch ubs2tbl HS.
{ exfalso. rewrite branch_ltu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc. change (SMdw M_REMU _ (SOff 13 0)) with (sv_hashx (SOff 36 0) 13) in Hc.
rewrite HhU, (U_atom E2 12 u E2_12) in Hc by lia.
rewrite zcanon_id in Hc by (unfold M64; lia).
apply Z.ltb_lt in Hc. lia. }
clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ CH_LOOP.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2' | cbn [r_wlo r_whi]; intros _; unfold COLHASH_STK in Hlo; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
kw_next HF HU2' KW3 KW4 sp memc. clear HG.
jbranch ubs2tbl HS.
{ exfalso. rewrite branch_eq_U, U_SAlu in Hc. cbn [zalu_raw] in Hc. rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc. rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc.
change (SMdw M_REMU _ (SOff 13 0)) with (sv_hashx (SOff 36 0) 13) in Hc.
rewrite HhU, (U_atom E2 12 u E2_12), !U_SLit in Hc by lia.
rewrite (zcanon_id (hash0 T c + u)) in Hc by (unfold M64; lia).
change (zcanon 1) with 1 in Hc. change (zcanon 0) with 0 in Hc.
replace (hash0 T c + u <? 1) with false in Hc by (symmetry; apply Z.ltb_ge; lia).
vm_compute in Hc. discriminate Hc. }
clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ CH_LOOP.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2' | cbn [r_wlo r_whi]; intros _; unfold COLHASH_STK in Hlo; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
kw_next HF HU2' KW4 KW5 sp memc. clear HG.
specialize (Hprobe Hop).
destruct (probe_facts T used keys c r ltac:(lia) Hprobe) as (js & Hjs & Hr & Hstop).
rewrite Hop.
lazymatch type of HS with st_ok _ _ ?ssA ?msA =>
assert (W : forall off n (rr : reg), Z.of_nat n = bv_unsigned rr -> (n < 32)%nat ->
(exists rg, nth_error (ss_mem ssA) 0 = Some rg /\ r_base rg = Some 2%nat /\ In (mkChunk off (CVal 8 (SOff n 0))) (r_chunks rg)) ->
forall a, a = sp + off -> word_mem ubs2segs (ms_mem msA) a (bv_unsigned (getr regs rr)))
end.
{ intros off n rr Hn Hn32 (rg & Hrg & Hrb & Hin) a ->.
eapply (st_chunk_word_g ubs2segs E2 _ _ 0%nat rg 2%nat off (SOff n 0)); [exact HS | exact Hrg | exact Hrb | exact Hin | exact HU2' | | apply u64_range].
cbn [sv_denot]. rewrite Z.add_0_r, (HE2 n rr Hn32 Hn), Z_to_bv_bv_unsigned. reflexivity. }
assert (E2_2 : ew E2 2 = Z_to_bv 64 sp) by (rewrite <- HU2'; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (hash0_range T c ltac:(lia)) as Rh0'.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ => change p with CH_LOOP end.
eapply SR_mono.
{ eapply (ch_loop regs memc STK sp0 FP L A mem md Lc Ac mdc rgb kp u T used keys c r js
Hra Hal Hsplo ltac:(lia) Hcol Hused Hkeys LU LK RT Rrgb0 ltac:(lia) Ru0 Ru1 Rk0 Rk1 Hr Hstop (Z.to_nat js) 0); [lia | lia |].
unfold at_loop. cbn [ms_regs ms_mem mkst]. split; [exact HJ|]. split; [unfold CH_FRAME; exact KW5|].
split. { apply obj_at_chf.
- apply (W (-8) 1%nat); [reflexivity | lia | eexists; split; [reflexivity | split; [reflexivity | cbv; auto 20]] | unfold sp; lia].
- apply (W (-16) 8%nat); [reflexivity | lia | eexists; split; [reflexivity | split; [reflexivity | cbv; auto 20]] | unfold sp; lia].
- apply (W (-24) 9%nat); [reflexivity | lia | eexists; split; [reflexivity | split; [reflexivity | cbv; auto 20]] | unfold sp; lia].
- apply (W (-32) 18%nat); [reflexivity | lia | eexists; split; [reflexivity | split; [reflexivity | cbv; auto 20]] | unfold sp; lia].
- apply (W (-40) 19%nat); [reflexivity | lia | eexists; split; [reflexivity | split; [reflexivity | cbv; auto 20]] | unfold sp; lia].
- apply (W (-48) 20%nat); [reflexivity | lia | eexists; split; [reflexivity | split; [reflexivity | cbv; auto 20]] | unfold sp; lia].
- apply (W (-56) 21%nat); [reflexivity | lia | eexists; split; [reflexivity | split; [reflexivity | cbv; auto 20]] | unfold sp; lia].
- apply (W (-64) 22%nat); [reflexivity | lia | eexists; split; [reflexivity | split; [reflexivity | cbv; auto 20]] | unfold sp; lia]. }
split. { eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get. rewrite (U_atom_off E2 2 sp (-64) E2_2) by lia. lia. }
split. { rewrite cyc_0 by lia. eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get.
rewrite U_SAlu. cbn [zalu_raw]. change (SMdw M_REMU _ (SOff 13 0)) with (sv_hashx (SOff 36 0) 13).
rewrite HhU, U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. unfold M64; lia. }
split. { rewrite cyc_0 by lia. eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get.
rewrite U_SAlu. cbn [zalu_raw]. change (SMdw M_REMU _ (SOff 13 0)) with (sv_hashx (SOff 36 0) 13).
rewrite HhU, (U_atom E2 12 u E2_12) by lia. apply zcanon_id. unfold M64; lia. }
split. { eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get. apply (U_atom E2 13 T E2_13). lia. }
split. { eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get. apply (U_atom E2 12 u E2_12). lia. }
split. { eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get. apply (U_atom E2 11 kp E2_11). lia. }
split. { eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get. apply (U_atom E2 10 rgb E2_10). lia. }
split. { eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get. apply (YI01.U_not E2 12 u E2_12). lia. }
split. { eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get. apply U_lit. lia. }
intros rr Hrr. apply (regs_kept_of_st_ok ubs2segs E2 _ _ regs [] CH_KEPT HS EAr); [vm_compute; reflexivity | exact Hrr]. }
cbv beta. intros c' Hc'. exact Hc'.
-
rewrite branch_ne_U, (U_pix_alpha E2 (SOff 36 0) A0 c Cok RA HpU), U_SLit in Hc.
assert (Hop : op = false) by (destruct op; [subst A0; vm_compute in Hc; discriminate Hc | reflexivity]).
clear Hc.
jrun LAWS ubs2tbl_ok HS HJ.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2' | cbn [r_wlo r_whi]; intros _; unfold COLHASH_STK in Hlo; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
kw_next HF HU2' KW2 KW3 sp memc. clear HG.
lazymatch type of HS with st_ok _ _ _ ?m => rename m into msF end.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | exact Hh | exact Hl | exact HS | reflexivity | vm_compute; reflexivity |].
assert (R1 : getr (ms_regs msF) 1 = getr regs 1).
{ jreg HS (1%bv:reg) as X. rewrite X. apply (HE2 1%nat 1%bv); [lia | reflexivity]. }
exists (ms_regs msF), (ms_mem msF). split; [rewrite R1, Hra; reflexivity|]. split; [exact HJ|]. split; [|split].
+ apply (regs_preserved_of_st_ok ubs2segs E2 _ msF regs [] HS EAr). vm_compute. reflexivity.
+ rewrite Hop. jreg HS (10%bv:reg) as X. rewrite X. reflexivity.
+ intros x Hx Hnx. apply KW3; [exact Hx | unfold COLHASH_STK in Hnx; lia].
Qed.
End S.
End b.
