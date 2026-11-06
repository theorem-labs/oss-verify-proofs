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
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YO3l YI00 YI02 YI01 YI03
YI1e YI1i YI07 YP14 YI08 YI0c YI0g YI3h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition CH_LOOP : Z := Eval vm_compute in (src2_A_col_hash + 0x90).
Definition CH_BRET : Z := Eval vm_compute in (src2_A_col_hash + 0xb8).
Definition CH_FRAME : Z := 48.
Definition LAY_CHF : layout_t := [(0, 8%N); (8, 8%N); (16, 8%N); (24, 8%N); (32, 8%N); (40, 8%N)].
Definition chf_vals (regs : bvmap 5 word) : list Z :=
[bv_unsigned (getr regs 20); bv_unsigned (getr regs 19); bv_unsigned (getr regs 18);
bv_unsigned (getr regs 9); bv_unsigned (getr regs 8); bv_unsigned (getr regs 1)].
Lemma u64_range' : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in H. lia. Qed.
Lemma obj_at_chf : forall (m : word -> option byte) a regs,
word_mem src2segs m (a + 40) (bv_unsigned (getr regs 1)) -> word_mem src2segs m (a + 32) (bv_unsigned (getr regs 8)) ->
word_mem src2segs m (a + 24) (bv_unsigned (getr regs 9)) -> word_mem src2segs m (a + 16) (bv_unsigned (getr regs 18)) ->
word_mem src2segs m (a + 8) (bv_unsigned (getr regs 19)) -> word_mem src2segs m a (bv_unsigned (getr regs 20)) ->
obj_at src2segs m a LAY_CHF (chf_vals regs).
Proof.
intros m a regs W1 W8 W9 W18 W19 W20. cbn [obj_at LAY_CHF chf_vals]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add].
rewrite Z.add_0_r.
repeat split; try (apply val_mem_word_mem; assumption); apply u64_range'.
Qed.
Definition CH_KEPT : list reg := [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition BCMP_CLOB : list reg := [10; 11; 12; 13; 14]%bv.
Definition ss_loop : sstate :=
mkSS CH_LOOP sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 48 0 0 (obj_chunks_from LAY_CHF 32) ;
YQ0b.mkRegion (Some 10%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 38%nat 0))] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + 16) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - 1) 0);
(8%nat, mkAF 1 (2^30) 0); (9%nat, mkAF 4096 CEIL_MAX 0); (18%nat, mkAF 4096 CEIL_MAX 0);
(19%nat, mkAF 4096 CEIL_MAX 0); (20%nat, mkAF 0 (2^30) 0); (38%nat, mkAF 0 255 0) ] [] []).
Definition ch_facts (fmt : Z) : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + 64) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - fmt) 0); (13%nat, mkAF 1 (2^30) 0);
(32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ].
Definition ss_ch3 : sstate :=
mkSS src2_A_col_hash (sr_set sr_atoms 14%bv (SLit 3))
[ YQ0b.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 3 0 0
[mkChunk 0 (CVal 1 (SOff 32%nat 0)); mkChunk 1 (CVal 1 (SOff 33%nat 0)); mkChunk 2 (CVal 1 (SOff 34%nat 0))] ]
None (mkFacts (ch_facts 3) [] []).
Definition ss_ch4 : sstate :=
mkSS src2_A_col_hash (sr_set sr_atoms 14%bv (SLit 4))
[ YQ0b.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 4 0 0
[mkChunk 0 (CVal 1 (SOff 32%nat 0)); mkChunk 1 (CVal 1 (SOff 33%nat 0)); mkChunk 2 (CVal 1 (SOff 34%nat 0)); mkChunk 3 (CVal 1 (SOff 35%nat 0))] ]
None (mkFacts (ch_facts 4) [] []).
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Section d.
Variables (regs : bvmap 5 word) (memc : word -> option byte) (STK sp0 : Z) (FP : list (Z * Z))
(L : layout) (A : astate) (mem : word -> option byte) (md : Model) (Lc : layout) (Ac : astate) (mdc : Model)
(rgb kp u T : Z) (used keys : list Z) (c : colour) (r js : Z).
Let sp : Z := spZ regs.
Let h0 : Z := hash0 T c.
Hypothesis Hra : YK0s.ret_ok (getr regs 1). Hypothesis Hal : sp mod 16 = 0.
Hypothesis Hsplo : alloc_ceiling + 64 <= sp. Hypothesis Hsphi : sp <= 2 ^ 63.
Hypothesis Hcol : col3 src2segs memc rgb c.
Hypothesis Hused : arr8 src2segs memc u used. Hypothesis Hkeys : arr8 src2segs memc kp keys.
Hypothesis LU : zlen used = T. Hypothesis LK : zlen keys = 3 * T. Hypothesis RT : 0 < T < 2 ^ 30.
Hypothesis Rrgb0 : 4096 <= rgb. Hypothesis Rrgb1 : rgb + 3 <= alloc_ceiling.
Hypothesis Ru0 : 4096 <= u. Hypothesis Ru1 : u + T <= alloc_ceiling.
Hypothesis Rk0 : 4096 <= kp. Hypothesis Rk1 : kp + 3 * T <= alloc_ceiling.
Hypothesis Hjs : 0 <= js < T. Hypothesis Hr : r = cyc T h0 js.
Hypothesis Hstop : forall i, 0 <= i <= js -> slot_stop (HT0 T used keys) c (cyc T h0 i) = (i =? js).
Definition ch_post (c' : config) : Prop :=
exists regs2 mem2,
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom src2segs)) mdc /\
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 r /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - COLHASH_STK <= a < sp) -> mbyte src2segs mem2 a = mbyte src2segs memc a).
Definition at_loop (j : Z) (regs1 : bvmap 5 word) (mem1 : word -> option byte) : Prop :=
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem1 mdc /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - CH_FRAME <= a < sp) -> mbyte src2segs mem1 a = mbyte src2segs memc a) /\
obj_at src2segs mem1 (sp - 48) LAY_CHF (chf_vals regs) /\
getr regs1 2 = Z_to_bv 64 (sp - 48) /\
getr regs1 20 = Z_to_bv 64 (cyc T h0 j) /\ getr regs1 10 = Z_to_bv 64 (u + cyc T h0 j) /\
getr regs1 8 = Z_to_bv 64 T /\ getr regs1 9 = Z_to_bv 64 u /\ getr regs1 18 = Z_to_bv 64 rgb /\ getr regs1 19 = Z_to_bv 64 kp /\
(forall rr, In rr CH_KEPT -> getr regs1 rr = getr regs rr).
Lemma ch_body : forall j regs1 mem1,
0 <= j <= js -> at_loop j regs1 mem1 ->
(forall regs' mem', j + 1 <= js -> at_loop (j + 1) regs' mem' ->
SR src2segs (mkCfg (mkst regs' (Z_to_bv 64 CH_LOOP) mem' (seg_rom src2segs)) mdc) ch_post) ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 CH_LOOP) mem1 (seg_rom src2segs)) mdc) ch_post.
Proof.
intros j regs1 mem1 Hj (HJ & Hfr & Hobj & G2 & G20 & G10 & G8 & G9 & G18 & G19 & GK) K.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (hj := cyc T h0 j) in *.
assert (Rhj : 0 <= hj < T) by (subst hj; apply cyc_range; lia).
destruct (arr8_getz src2segs memc u used hj Hused ltac:(lia)) as [Bu Ru'].
set (ub := getz used hj) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) (chf_vals regs ++ [ub]) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE38 : ew E 38 = Z_to_bv 64 ub) by (subst E; apply (Ereg_vals regs1 _ [] 6%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp - 48) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = u + hj) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 T) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE9 : ew E 9 = Z_to_bv 64 u) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE18 : ew E 18 = Z_to_bv 64 rgb) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE19 : ew E 19 = Z_to_bv 64 kp) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE20 : ew E 20 = Z_to_bv 64 hj) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HE10 : ew E 10 = Z_to_bv 64 (u + hj)) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (Bu1 : mbyte src2segs mem1 (u + hj) = Some (Z_to_bv 8 ub)) by (rewrite Hfr by (unfold CH_FRAME; lia); exact Bu).
assert (HS : st_ok src2segs E ss_loop (mkst regs1 (Z_to_bv 64 CH_LOOP) mem1 (seg_rom src2segs))).
{ unfold ss_loop. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply (region_ok_obj src2segs _ mem1 2 (sp - 48)); [exact HU2 | lia | lia | exact Hobj | reflexivity | | intros i Hi; lia].
intros jj v Hjj. apply (Ereg_vals regs1 _ [] jj v). rewrite nth_error_app1; [exact Hjj | apply nth_error_Some; congruence].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ ub); [cbn [sv_denot]; rewrite Z.add_0_r, HE38, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. rewrite Z.add_0_r. apply val_mem_byte; [exact Bu1 | lia].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU10.
repeat split; try exact I. first [left; lia | right; lia].
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HE8, HE9, HE18, HE19, HE20, HE38, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
assert (Hal48 : (sp - 48) mod 16 = 0) by (replace (sp - 48) with (sp + (-3) * 16) by lia; rewrite Z.mod_add; [exact Hal | lia]).
repeat split; lia. }
assert (HV : forall jj v, nth_error (chf_vals regs ++ [ub]) jj = Some v -> ew E (32 + jj) = Z_to_bv 64 v) by (intros jj v Hjj; subst E; apply Ereg_vals; exact Hjj).
assert (HE32 : ew E 32 = getr regs 20) by (etransitivity; [exact (HV 0%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]).
assert (HE33 : ew E 33 = getr regs 19) by (etransitivity; [exact (HV 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]).
assert (HE34 : ew E 34 = getr regs 18) by (etransitivity; [exact (HV 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]).
assert (HE35 : ew E 35 = getr regs 9) by (etransitivity; [exact (HV 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]).
assert (HE36 : ew E 36 = getr regs 8) by (etransitivity; [exact (HV 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]).
assert (HE37 : ew E 37 = getr regs 1) by (etransitivity; [exact (HV 5%nat _ eq_refl) | apply Z_to_bv_bv_unsigned]).
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 CH_LOOP) mem1 (seg_rom src2segs))) in HJ.
clearbody E. clear HV.
assert (EXIT : forall E' ss ms', st_ok src2segs E' ss ms' -> env_agree 39 E E' -> ss_resv ss = None ->
clookup src2tbl (ss_pc ss) = Some RET_WORD ->
sr_get (ss_regs ss) 1 = SOff 37 0 -> sr_get (ss_regs ss) 2 = SOff 2 48 ->
sr_get (ss_regs ss) 8 = SOff 36 0 -> sr_get (ss_regs ss) 9 = SOff 35 0 -> sr_get (ss_regs ss) 18 = SOff 34 0 ->
sr_get (ss_regs ss) 19 = SOff 33 0 -> sr_get (ss_regs ss) 20 = SOff 32 0 -> sr_get (ss_regs ss) 10 = SOff 20 0 ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) CH_KEPT = true ->
hj = r ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall x, ms_mem ms' x = mem1 x) ->
SR src2segs (mkCfg ms' mdc) ch_post).
{ intros E' ss ms' HS' EA Hrv Hpc Q1 Q2 Q8 Q9 Q18 Q19 Q20 Q10 QK Hhr HJ' Hm'.
destruct EA as [EA ED].
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ')) as (Hh & Hl & _).
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | exact Hh | exact Hl | exact HS' | exact Hrv | exact Hpc |].
assert (RG : forall (rr : reg) e, sr_get (ss_regs ss) rr = e -> getr (ms_regs ms') rr = sv_denot E' e).
{ intros rr e He. rewrite <- He. apply (st_ok_reg _ _ _ _ rr HS'). }
assert (R1 : getr (ms_regs ms') 1 = getr regs 1).
{ rewrite (RG _ _ Q1). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE37 by lia. apply Z_to_bv_bv_unsigned. }
exists (ms_regs ms'), (ms_mem ms'). split; [rewrite R1, Hra; reflexivity|]. split; [exact HJ'|]. split; [|split].
-
assert (GK' : forall rr, In rr CH_KEPT -> getr (ms_regs ms') rr = getr regs rr).
{ intros rr Hrr. rewrite <- (GK rr Hrr).
apply (regs_kept_of_st_ok src2segs E' ss ms' regs1 [] CH_KEPT HS'); [|exact QK|exact Hrr].
eapply env_agree_trans; [exact EA0 | split; [intros n Hn; apply EA; lia | exact ED]]. }
apply regs_preserved_intro_g.
+ rewrite (RG _ _ Q2). cbn [sv_denot]. rewrite EA by lia. rewrite (HE 2%nat 2%bv eq_refl), G2, unsigned_lit_small by lia.
unfold sp. rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs 2)). f_equal. unfold spZ. lia.
+ apply GK'. cbv; auto 10.
+ apply GK'. cbv; auto 10.
+ rewrite (RG _ _ Q8). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE36 by lia. apply Z_to_bv_bv_unsigned.
+ rewrite (RG _ _ Q9). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE35 by lia. apply Z_to_bv_bv_unsigned.
+ rewrite (RG _ _ Q18). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE34 by lia. apply Z_to_bv_bv_unsigned.
+ rewrite (RG _ _ Q19). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE33 by lia. apply Z_to_bv_bv_unsigned.
+ rewrite (RG _ _ Q20). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE32 by lia. apply Z_to_bv_bv_unsigned.
+ apply GK'. cbv; auto 10.
+ apply GK'. cbv; auto 10.
+ apply GK'. cbv; auto 10.
+ apply GK'. cbv; auto 10.
+ apply GK'. cbv; auto 10.
+ apply GK'. cbv; auto 10.
+ apply GK'. cbv; auto 10.
- rewrite (RG _ _ Q10). cbn [sv_denot]. rewrite Z.add_0_r, EA, HE20, <- Hhr by lia. rewrite unsigned_lit_small by lia. reflexivity.
- intros a Ha Hna. unfold mbyte. rewrite Hm'. fold (mbyte src2segs mem1 a). apply Hfr; [exact Ha|]. unfold CH_FRAME, COLHASH_STK in *. lia. }
jrun_to LAWS src2tbl_ok HS HJ src2_A_bcmp. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms x = mem1 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
pose proof (Hstop j Hj) as Hsj. fold hj in Hsj. rewrite slot_stop_HT0 in Hsj. fold ub in Hsj.
jbranch src2tbl HS.
-
rewrite branch_eq_U, (U_atom E 38 ub HE38), U_lit in Hc by lia.
rewrite Hc in Hsj. cbn [orb] in Hsj. symmetry in Hsj. apply Z.eqb_eq in Hsj.
jrun LAWS src2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (EXIT _ _ _ HS); [apply env_agree_refl | reflexivity | vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| vm_compute; reflexivity | subst hj; rewrite Hsj; symmetry; exact Hr | exact HJ | ].
intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1.
-
rewrite branch_eq_U, (U_atom E 38 ub HE38), U_lit in Hc by lia.
rewrite Hc in Hsj. cbn [orb] in Hsj. clear Hc.
jrun_to LAWS src2tbl_ok HS HJ src2_A_bcmp. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall x, ms_mem ms0 x = mem1 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG K1.
jreg HS (10%bv:reg) as Hb0. rewrite HE18 in Hb0.
assert (Hb1 : getr (ms_regs ms0) 11 = Z_to_bv 64 (kp + 3 * hj)).
{ eapply (getr_of_U src2segs); [exact HS|]. eval_sr_get. apply (U_add_mul3' E 20 19 hj kp HE20 ltac:(lia) HE19 ltac:(lia) ltac:(lia)). }
jreg HS (12%bv:reg) as Hb2. jreg HS (1%bv:reg) as Hbra.
destruct Hcol as (C0 & C1 & C2 & Cok).
assert (MB : forall a, 0 <= a < alloc_ceiling -> mbyte src2segs (ms_mem ms0) a = mbyte src2segs memc a).
{ intros a Ha. unfold mbyte. rewrite K2. fold (mbyte src2segs mem1 a). apply Hfr; [lia|]. unfold CH_FRAME. lia. }
destruct (arr8_getz src2segs memc kp keys (3 * hj) Hkeys ltac:(lia)) as [Bk0 Rk0'].
destruct (arr8_getz src2segs memc kp keys (3 * hj + 1) Hkeys ltac:(lia)) as [Bk1 Rk1'].
destruct (arr8_getz src2segs memc kp keys (3 * hj + 2) Hkeys ltac:(lia)) as [Bk2 Rk2'].
set (lb := [Z_to_bv 8 (cR c); Z_to_bv 8 (cG c); Z_to_bv 8 (cB c)]).
set (rb := [Z_to_bv 8 (getz keys (3 * hj)); Z_to_bv 8 (getz keys (3 * hj + 1)); Z_to_bv 8 (getz keys (3 * hj + 2))]).
destruct (src2_bcmp lb rb _ _ _ (ms_mem ms0) (seg_rom src2segs) (ms_regs ms0) Hb0 Hb1 Hb2) as (regs2 & Hms & Hres & Hfr2).
{ rewrite unsigned_lit_small by lia. reflexivity. }
{ reflexivity. }
{ change (length lb) with 3%nat. apply rdn3_of_mbytes; rewrite MB by lia; assumption. }
{ change (length lb) with 3%nat. apply rdn3_of_mbytes; rewrite MB by lia;
[exact Bk0 | replace (kp + 3 * hj + 1) with (kp + (3 * hj + 1)) by lia; exact Bk1 | replace (kp + 3 * hj + 2) with (kp + (3 * hj + 2)) by lia; exact Bk2]. }
{ rewrite unsigned_lit_small by lia. change (length lb) with 3%nat. lia. }
{ rewrite unsigned_lit_small by lia. change (length lb) with 3%nat. lia. }
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
replace (v_jalr (getr (ms_regs ms0) 1) 0) with (Z_to_bv 64 CH_BRET).
2:{ rewrite Hbra. symmetry. apply ret_ok_even. vm_compute. reflexivity. }
jafter_stretch_keep HS 39%nat regs2 (ms_mem ms0) BCMP_CLOB CH_BRET [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2; intros ->; vm_compute in Hrr; discriminate Hrr. }
{ repeat (apply Forall_cons); try apply Forall_nil; apply (region_kept_same src2segs). }
clear HS. rename HS2 into HS.
change (ms_mem ms0) with (ms_mem (mkst regs2 (Z_to_bv 64 CH_BRET) (ms_mem ms0) (seg_rom src2segs))) in HJ.
assert (EA1 : env_agree 39 E (havoc E 39 (map (getr regs2) BCMP_CLOB))) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (H39 : ew (havoc E 39 (map (getr regs2) BCMP_CLOB)) 39 = Z_to_bv 64 (memcmp_spec lb rb)).
{ rewrite <- Hres. etransitivity; [apply (ew_havoc_new E 39 _ 0%nat (Z_to_bv 64 0)); cbn; lia | reflexivity]. }
assert (Hzero : Z_to_bv 64 (memcmp_spec lb rb) = Z_to_bv 64 0 <-> col_at keys hj = c).
{ rewrite (src2_memcmp_zero_iff lb rb eq_refl). subst lb rb. apply key_bytes_eq_iff; [exact Cok | lia | lia | lia]. }
jbranch src2tbl HS.
+
cbn [branch_taken sv_denot] in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, H39 in Hc. apply bv_eqb_eq in Hc.
apply Hzero in Hc. rewrite <- Hc, colour_eqb_refl in Hsj. symmetry in Hsj. apply Z.eqb_eq in Hsj.
jrun LAWS src2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (EXIT _ _ _ HS); [exact EA1 | reflexivity | vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| vm_compute; reflexivity | subst hj; rewrite Hsj; symmetry; exact Hr | exact HJ | ].
intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2.
+
cbn [branch_taken sv_denot] in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, H39 in Hc.
assert (Hjs' : j + 1 <= js).
{ destruct (Z.eqb_spec j js) as [Ej|]; [|lia]. exfalso. apply (proj1 (colour_eqb_spec _ _)) in Hsj.
apply Hzero in Hsj. rewrite Hsj, bv_eqb_refl in Hc. discriminate Hc. }
jrun_to LAWS src2tbl_ok HS HJ CH_LOOP. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall x, ms_mem ms1 x = mem1 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
assert (EA2 : env_agree 32 (Ereg regs1 []) Ef) by (eapply env_agree_trans; [exact EA0 | eapply env_agree_le; [| exact EA1]; lia]);
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs1 [] CH_KEPT HS EA2 ltac:(vm_compute; reflexivity)) as HKR;
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs1 [] [2; 8; 9; 18; 19]%bv HS EA2 ltac:(vm_compute; reflexivity)) as HKR2 end.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
apply K; [exact Hjs'|]. unfold at_loop. cbn [ms_regs ms_mem mkst].
split; [exact HJ|]. split. { intros a Ha Hna. rewrite <- (Hfr a Ha Hna). unfold mbyte. rewrite (K3 (Z_to_bv 64 a)). reflexivity. }
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ 48); [exact Hobj | reflexivity | intros i Hi; unfold mbyte; rewrite (K3 (Z_to_bv 64 (sp - 48 + i))); reflexivity]. }
split; [rewrite (HKR2 2%bv ltac:(cbv; auto 10)); exact G2|].
split. { eapply (getr_of_U src2segs); [exact HS|]. eval_sr_get. rewrite cyc_succ by lia. fold hj.
apply (U_sv_next _ 20 8 hj T); [ew_havoc; exact HE20 | ew_havoc; exact HE8 | lia | lia]. }
split. { eapply (getr_of_U src2segs); [exact HS|]. eval_sr_get. rewrite cyc_succ by lia. fold hj.
apply (U_u_next _ 9 20 8 u hj T); [ew_havoc; exact HE9 | ew_havoc; exact HE20 | ew_havoc; exact HE8 | lia | lia | lia | lia]. }
split; [rewrite (HKR2 8%bv ltac:(cbv; auto 10)); exact G8|].
split; [rewrite (HKR2 9%bv ltac:(cbv; auto 10)); exact G9|].
split; [rewrite (HKR2 18%bv ltac:(cbv; auto 10)); exact G18|].
split; [rewrite (HKR2 19%bv ltac:(cbv; auto 10)); exact G19|].
intros rr Hrr. rewrite (HKR rr Hrr). apply GK. exact Hrr.
Qed.
Lemma ch_loop : forall n j regs1 mem1, js - j <= Z.of_nat n -> 0 <= j <= js -> at_loop j regs1 mem1 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 CH_LOOP) mem1 (seg_rom src2segs)) mdc) ch_post.
Proof.
induction n as [|n IH]; intros j regs1 mem1 Hn Hj HA.
- apply (ch_body j regs1 mem1 Hj HA). intros regs' mem' Hj' _. exfalso. cbn in Hn. lia.
- apply (ch_body j regs1 mem1 Hj HA). intros regs' mem' Hj' HA'.
apply (IH (j + 1)); [rewrite Nat2Z.inj_succ in Hn; lia | lia | exact HA'].
Qed.
End d.
Theorem src2_col_hash : col_hash_spec API.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs rgb kp u T fmt used keys c op r
HJ Hra Hal Hlo Hhi G10 G11 G12 G13 G14 Hpix Hused Hkeys LU LK RT Rrgb0 Rrgb1 Ru0 Ru1 Rk0 Rk1 Hprobe.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof HJ as (HH0 & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
set (sp := spZ regs) in *.
assert (Hsplo : alloc_ceiling + 64 <= sp) by (unfold COLHASH_STK in Hlo; lia).
destruct Hpix as [Hcol Hfmt]. pose proof Hcol as (C0 & C1 & C2 & Cok). pose proof Cok as (Rr & Rg & Rb).
assert (ARRIVE : forall E ss1 ms1 rg,
st_ok src2segs E ss1 ms1 -> op = true ->
(forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) -> ed E = ed (Ereg regs []) ->
ew E 32 = Z_to_bv 64 (cR c) -> ew E 33 = Z_to_bv 64 (cG c) -> ew E 34 = Z_to_bv 64 (cB c) ->
ss_pc ss1 = CH_LOOP -> ss_resv ss1 = None ->
sr_get (ss_regs ss1) 20 = sv_hash 32 33 34 13 -> sr_get (ss_regs ss1) 10 = SAlu ALU_ADD (SOff 12 0) (sv_hash 32 33 34 13) ->
sr_get (ss_regs ss1) 2 = SOff 2 (-48) -> sr_get (ss_regs ss1) 8 = SOff 13 0 -> sr_get (ss_regs ss1) 9 = SOff 12 0 ->
sr_get (ss_regs ss1) 18 = SOff 10 0 -> sr_get (ss_regs ss1) 19 = SOff 11 0 ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss1) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) CH_KEPT = true ->
nth_error (ss_mem ss1) 0 = Some rg -> r_base rg = Some 2%nat ->
In (mkChunk (-48) (CVal 8 (SOff 20 0))) (r_chunks rg) -> In (mkChunk (-40) (CVal 8 (SOff 19 0))) (r_chunks rg) ->
In (mkChunk (-32) (CVal 8 (SOff 18 0))) (r_chunks rg) -> In (mkChunk (-24) (CVal 8 (SOff 9 0))) (r_chunks rg) ->
In (mkChunk (-16) (CVal 8 (SOff 8 0))) (r_chunks rg) -> In (mkChunk (-8) (CVal 8 (SOff 1 0))) (r_chunks rg) ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms1) mdc ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp - CH_FRAME <= x < sp) -> mbyte src2segs (ms_mem ms1) x = mbyte src2segs memc x) ->
SR src2segs (mkCfg ms1 mdc)
(fun c' => exists regs2 mem2,
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom src2segs)) mdc /\
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\ regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 (if op then r else 2 ^ 64 - 1) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp - COLHASH_STK <= x < sp) -> mbyte src2segs mem2 x = mbyte src2segs memc x))).
{ intros E ss1 ms1 rg HS Hop HE HED HE32 HE33 HE34 Hpc Hrv Q20 Q10 Q2 Q8 Q9 Q18 Q19 QK Hrg Hrb I20 I19 I18 I9 I8 I1 HJ1 Hfr1.
rewrite Hop. specialize (Hprobe Hop).
destruct (probe_facts T used keys c r ltac:(lia) Hprobe) as (js & Hjs & Hr & Hstop).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HE13 : ew E 13 = Z_to_bv 64 T) by (rewrite (HE 13%nat 13%bv eq_refl); exact G13).
assert (HE12 : ew E 12 = Z_to_bv 64 u) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (RG : forall (rr : reg) e, sr_get (ss_regs ss1) rr = e -> getr (ms_regs ms1) rr = sv_denot E e).
{ intros rr e He. rewrite <- He. apply (st_ok_reg _ _ _ _ rr HS). }
assert (W : forall off n (rr : reg), Z.of_nat n = bv_unsigned rr -> In (mkChunk off (CVal 8 (SOff n 0))) (r_chunks rg) ->
forall a, a = sp + off -> word_mem src2segs (ms_mem ms1) a (bv_unsigned (getr regs rr))).
{ intros off n rr Hn Hin a ->. eapply (st_chunk_word_g src2segs E ss1 ms1 0%nat rg 2%nat off (SOff n 0)); [exact HS | exact Hrg | exact Hrb | exact Hin | exact HU2 | | apply u64_range].
cbn [sv_denot]. rewrite Z.add_0_r, (HE n rr Hn), Z_to_bv_bv_unsigned. reflexivity. }
rewrite (st_ok_mkst src2segs _ _ _ HS Hrv), Hpc.
eapply SR_mono.
{ eapply (ch_loop regs memc STK sp0 FP L A mem md Lc Ac mdc rgb kp u T used keys c r js
Hra Hal Hsplo ltac:(lia) Hcol Hused Hkeys LU LK RT Rrgb0 ltac:(lia) Ru0 Ru1 Rk0 Rk1 Hr Hstop (Z.to_nat js) 0); [lia | lia |].
unfold at_loop. cbn [ms_regs ms_mem mkst]. split; [exact HJ1|]. split; [exact Hfr1|].
split. { apply obj_at_chf.
- apply (W (-8) 1%nat); [reflexivity | exact I1 | unfold sp; lia].
- apply (W (-16) 8%nat); [reflexivity | exact I8 | unfold sp; lia].
- apply (W (-24) 9%nat); [reflexivity | exact I9 | unfold sp; lia].
- apply (W (-32) 18%nat); [reflexivity | exact I18 | unfold sp; lia].
- apply (W (-40) 19%nat); [reflexivity | exact I19 | unfold sp; lia].
- apply (W (-48) 20%nat); [reflexivity | exact I20 | unfold sp; lia]. }
split. { rewrite (RG _ _ Q2). cbn [sv_denot]. rewrite HU2. reflexivity. }
pose proof (hash0_range T c ltac:(lia)) as Rh0.
split. { rewrite cyc_0 by lia. eapply (getr_of_U src2segs); [exact HS|]. rewrite Q20. apply (U_hash0 E 32 33 34 13 c T HE32 HE33 HE34 Cok HE13 RT). }
split. { rewrite cyc_0 by lia. eapply (getr_of_U src2segs); [exact HS|]. rewrite Q10. apply (U_u_hash0 E 12 32 33 34 13 c T u HE32 HE33 HE34 Cok HE13 RT HE12); lia. }
split. { rewrite (RG _ _ Q8). cbn [sv_denot]. rewrite Z.add_0_r, HE13, unsigned_lit_small by lia. reflexivity. }
split. { rewrite (RG _ _ Q9). cbn [sv_denot]. rewrite Z.add_0_r, HE12, unsigned_lit_small by lia. reflexivity. }
split. { rewrite (RG _ _ Q18). cbn [sv_denot]. rewrite Z.add_0_r, (HE 10%nat 10%bv eq_refl), G10, unsigned_lit_small by lia. reflexivity. }
split. { rewrite (RG _ _ Q19). cbn [sv_denot]. rewrite Z.add_0_r, (HE 11%nat 11%bv eq_refl), G11, unsigned_lit_small by lia. reflexivity. }
intros rr Hrr. apply (regs_kept_of_st_ok src2segs E ss1 ms1 regs [] CH_KEPT HS); [|exact QK|exact Hrr].
split; [intros n Hn; rewrite (ew_Ereg_lt regs [] n Hn); apply HE; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5%N) with 32; rewrite Z.mod_small; lia | exact HED]. }
cbv beta. intros c' Hc'. exact Hc'. }
assert (TRANSP : forall E ss ms', st_ok src2segs E ss ms' -> op = false ->
(forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) -> ed E = ed (Ereg regs []) ->
ss_resv ss = None -> clookup src2tbl (ss_pc ss) = Some RET_WORD ->
sr_get (ss_regs ss) 1 = SOff 1 0 -> sr_get (ss_regs ss) 10 = SLit 18446744073709551615 ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) CALLEE_SAVED = true ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp - CH_FRAME <= x < sp) -> mbyte src2segs (ms_mem ms') x = mbyte src2segs memc x) ->
SR src2segs (mkCfg ms' mdc)
(fun c' => exists regs2 mem2,
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom src2segs)) mdc /\
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\ regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 (if op then r else 2 ^ 64 - 1) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp - COLHASH_STK <= x < sp) -> mbyte src2segs mem2 x = mbyte src2segs memc x))).
{ intros E ss ms' HS Hop HE HED Hrv Hpc Q1 Q10 QK HJ' Hfr'. rewrite Hop.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ')) as (Hh & Hl & _).
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | exact Hh | exact Hl | exact HS | exact Hrv | exact Hpc |].
assert (R1 : getr (ms_regs ms') 1 = getr regs 1).
{ rewrite (st_ok_reg _ _ _ _ 1%bv HS), Q1. cbn [sv_denot]. rewrite Z.add_0_r, (HE 1%nat 1%bv eq_refl). apply Z_to_bv_bv_unsigned. }
exists (ms_regs ms'), (ms_mem ms'). split; [rewrite R1, Hra; reflexivity|]. split; [exact HJ'|]. split; [|split].
- apply (regs_preserved_of_st_ok src2segs E ss ms' regs [] HS); [|exact QK].
split; [intros n Hn; rewrite (ew_Ereg_lt regs [] n Hn); apply HE; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5%N) with 32; rewrite Z.mod_small; lia | exact HED].
- rewrite (st_ok_reg _ _ _ _ 10%bv HS), Q10. reflexivity.
- intros x Hx Hnx. apply Hfr'; [exact Hx|]. unfold CH_FRAME, COLHASH_STK in *. lia. }
destruct Hfmt as [[Hf Hop] | (Hf & a & Ca & Ra & Hop)]; subst fmt.
-
set (E := Ereg regs (map (Z_to_bv 64) [cR c; cG c; cB c] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall jj v, nth_error [cR c; cG c; cB c] jj = Some v -> ew E (32 + jj) = Z_to_bv 64 v) by (intros jj v Hjj; subst E; apply Ereg_vals; exact Hjj).
assert (HE32 : ew E 32 = Z_to_bv 64 (cR c)) by exact (HV 0%nat _ eq_refl).
assert (HE33 : ew E 33 = Z_to_bv 64 (cG c)) by exact (HV 1%nat _ eq_refl).
assert (HE34 : ew E 34 = Z_to_bv 64 (cB c)) by exact (HV 2%nat _ eq_refl).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = rgb) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HS : st_ok src2segs E ss_ch3 (mkst regs (Z_to_bv 64 src2_A_col_hash) memc (seg_rom src2segs))).
{ unfold ss_ch3. subst E. apply entry_st_ok_gen.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite G14; reflexivity].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack src2segs _ memc 2 sp); [exact HU2 | lia | lia | intros x Hx; apply Hstw; unfold COLHASH_STK in Hlo; lia].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* eapply (chunk_ok_val _ _ _ _ _ _ _ (cR c)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. rewrite Z.add_0_r. apply val_mem_byte; [exact C0 | lia].
* eapply (chunk_ok_val _ _ _ _ _ _ _ (cG c)); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. apply val_mem_byte; [exact C1 | lia].
* eapply (chunk_ok_val _ _ _ _ _ _ _ (cB c)); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. apply val_mem_byte; [exact C2 | lia].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU10.
repeat split; try exact I. first [left; lia | right; lia].
- cbn [atoms_ok ch_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, (HE 13%nat 13%bv eq_refl), G13, HE32, HE33, HE34, !unsigned_lit_small by lia.
rewrite (ew_Ereg_extra regs _ 3). cbn [nth map app]. rewrite unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
repeat split; lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 src2_A_col_hash) memc (seg_rom src2segs))) in HJ.
assert (HED : ed E = ed (Ereg regs [])) by (subst E; reflexivity).
clearbody E.
jrun_to LAWS src2tbl_ok HS HJ CH_LOOP.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; unfold COLHASH_STK in Hlo; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
eapply (ARRIVE E _ _ _ HS Hop HE HED HE32 HE33 HE34); try reflexivity; [cbv; auto 10 | cbv; auto 10 | cbv; auto 10 | cbv; auto 10 | cbv; auto 10 | cbv; auto 10 | exact HJ |].
intros x Hx Hnx. mb_frame_g HF; [reflexivity | rewrite HU2; unfold CH_FRAME in Hnx; lia | rewrite HU10; lia].
-
set (E := Ereg regs (map (Z_to_bv 64) [cR c; cG c; cB c; a] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall jj v, nth_error [cR c; cG c; cB c; a] jj = Some v -> ew E (32 + jj) = Z_to_bv 64 v) by (intros jj v Hjj; subst E; apply Ereg_vals; exact Hjj).
assert (HE32 : ew E 32 = Z_to_bv 64 (cR c)) by exact (HV 0%nat _ eq_refl).
assert (HE33 : ew E 33 = Z_to_bv 64 (cG c)) by exact (HV 1%nat _ eq_refl).
assert (HE34 : ew E 34 = Z_to_bv 64 (cB c)) by exact (HV 2%nat _ eq_refl).
assert (HE35 : ew E 35 = Z_to_bv 64 a) by exact (HV 3%nat _ eq_refl).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = rgb) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HS : st_ok src2segs E ss_ch4 (mkst regs (Z_to_bv 64 src2_A_col_hash) memc (seg_rom src2segs))).
{ unfold ss_ch4. subst E. apply entry_st_ok_gen.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite G14; reflexivity].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack src2segs _ memc 2 sp); [exact HU2 | lia | lia | intros x Hx; apply Hstw; unfold COLHASH_STK in Hlo; lia].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* eapply (chunk_ok_val _ _ _ _ _ _ _ (cR c)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. rewrite Z.add_0_r. apply val_mem_byte; [exact C0 | lia].
* eapply (chunk_ok_val _ _ _ _ _ _ _ (cG c)); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. apply val_mem_byte; [exact C1 | lia].
* eapply (chunk_ok_val _ _ _ _ _ _ _ (cB c)); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. apply val_mem_byte; [exact C2 | lia].
* eapply (chunk_ok_val _ _ _ _ _ _ _ a); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. apply val_mem_byte; [exact Ca | lia].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU10.
repeat split; try exact I. first [left; lia | right; lia].
- cbn [atoms_ok ch_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, (HE 13%nat 13%bv eq_refl), G13, HE32, HE33, HE34, HE35, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
repeat split; lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 src2_A_col_hash) memc (seg_rom src2segs))) in HJ.
assert (HED : ed E = ed (Ereg regs [])) by (subst E; reflexivity).
clearbody E.
jrun_to LAWS src2tbl_ok HS HJ CH_LOOP.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; unfold COLHASH_STK in Hlo; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
jbranch src2tbl HS.
+
rewrite (branch_lt_sext8 _ 35 a HE35 Ra), <- Hop in Hc.
jrun_to LAWS src2tbl_ok HS HJ CH_LOOP.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; unfold COLHASH_STK in Hlo; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF0.
eapply (ARRIVE E _ _ _ HS Hc HE HED HE32 HE33 HE34); try reflexivity; [cbv; auto 10 | cbv; auto 10 | cbv; auto 10 | cbv; auto 10 | cbv; auto 10 | cbv; auto 10 | exact HJ |].
intros x Hx Hnx. mb_frame_g HF0; [| rewrite HU2; unfold CH_FRAME in Hnx; lia | rewrite HU10; lia].
mb_frame_g HF; [reflexivity | rewrite HU2; unfold CH_FRAME in Hnx; lia | rewrite HU10; lia].
+
rewrite (branch_lt_sext8 _ 35 a HE35 Ra), <- Hop in Hc.
jrun LAWS src2tbl_ok HS HJ.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; unfold COLHASH_STK in Hlo; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF0.
eapply (TRANSP E _ _ HS Hc HE HED); [reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HJ |].
intros x Hx Hnx. mb_frame_g HF0; [| rewrite HU2; unfold CH_FRAME in Hnx; lia | rewrite HU10; lia].
mb_frame_g HF; [reflexivity | rewrite HU2; unfold CH_FRAME in Hnx; lia | rewrite HU10; lia].
Qed.
End S.
End b.
