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
YI1e YI1d YI39 YI1i YI59 YI56 YI0x YI57
YI1h YI16.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition AF_CMPRET : Z := Eval vm_compute in (src2_A_cgif_addframe + 0x148).
Lemma rdn_ext : forall segs (m1 m2 : word -> option byte) n a,
(forall x, m1 x = m2 x) -> rdn segs m1 a n = rdn segs m2 a n.
Proof.
intros segs m1 m2 n. induction n as [|n IH]; intros a Heq; [reflexivity|].
cbn [rdn]. rewrite (Heq a), (IH (a + 1)%bv Heq). reflexivity.
Qed.
Lemma mem_grows_of_eq : forall (m1 m2 : word -> option byte), (forall x, m2 x = m1 x) -> mem_grows m1 m2.
Proof. intros m1 m2 Heq x Hx. rewrite Heq. exact Hx. Qed.
Lemma mbyte_of_eq : forall segs (m1 m2 : word -> option byte) a, (forall x, m2 x = m1 x) -> mbyte segs m2 a = mbyte segs m1 a.
Proof. intros segs m1 m2 a Heq. unfold mbyte. rewrite Heq. reflexivity. Qed.
Definition CMP_CLOB : list reg := [5; 6; 10; 11; 12; 13; 14; 15; 16; 17]%bv.
Lemma cmp_clob_out : forall r : reg, reg_in r CMP_CLOB = false ->
r <> 5%bv /\ r <> 6%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv.
Proof. intros r Hr. repeat split; intros ->; vm_compute in Hr; discriminate. Qed.
Definition ss_loop : sstate :=
mkSS AF_LOOP sr_atoms
[ YQ0b.mkRegion (Some 23%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 32 0))] ;
YQ0b.mkRegion (Some 24%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))] ]
None (mkFacts [ (23%nat, mkAF 4096 (CEIL_MAX - 1) 0); (24%nat, mkAF 4096 (CEIL_MAX - 1) 0);
(25%nat, mkAF 1 4294967296 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0) ] [] []).
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Section c.
Variables (mem0 : word -> option byte) (g cfp fhp img fimg N : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis Og : obj_at src2segs mem0 g LAY_CGIF gvals.
Hypothesis Ongp : nth_error gvals CG_ngp = Some ngp.
Hypothesis Ogpal : nth_error gvals CG_pal = Some gpal.
Hypothesis Oc : obj_at src2segs mem0 cfp LAY_FrameConfig cvals.
Hypothesis Ocattr : nth_error cvals FR_attr = Some cattr.
Hypothesis Octidx : nth_error cvals FR_ctidx = Some ctidx.
Hypothesis Ocnlp : nth_error cvals FR_nlp = Some cnlp.
Hypothesis Oclpal : nth_error cvals FR_lpal = Some clpal.
Hypothesis Ob : obj_at src2segs mem0 fhp LAY_FrameConfig bvals.
Hypothesis Obattr : nth_error bvals FR_attr = Some battr.
Hypothesis Obtidx : nth_error bvals FR_ctidx = Some btidx.
Hypothesis Obnlp : nth_error bvals FR_nlp = Some bnlp.
Hypothesis Oblpal : nth_error bvals FR_lpal = Some blpal.
Hypothesis G0 : 4096 <= g. Hypothesis G1 : g + CGIF_SIZE <= alloc_ceiling. Hypothesis G16 : g mod 16 = 0.
Hypothesis C0 : 4096 <= cfp. Hypothesis C1 : cfp + 32 <= 2 ^ 63. Hypothesis C8 : cfp mod 8 = 0.
Hypothesis B0 : 4096 <= fhp. Hypothesis B1 : fhp + 32 <= 2 ^ 63. Hypothesis B8 : fhp mod 8 = 0.
Hypothesis Dgc : g + CGIF_SIZE <= cfp \/ cfp + 29 <= g.
Hypothesis Dgb : g + CGIF_SIZE <= fhp \/ fhp + 29 <= g.
Hypothesis Dcb : cfp + 29 <= fhp \/ fhp + 29 <= cfp.
Hypothesis Rct : rdn src2segs mem0 (Z_to_bv 64 (ct_sel cattr clpal gpal)) (Z.to_nat (3 * ct_sel cattr cnlp ngp)) = Some ctcur.
Hypothesis Rbt : rdn src2segs mem0 (Z_to_bv 64 (ct_sel battr blpal gpal)) (Z.to_nat (3 * ct_sel battr bnlp ngp)) = Some ctbef.
Hypothesis Sc0 : 4096 <= ct_sel cattr clpal gpal. Hypothesis Sc1 : ct_sel cattr clpal gpal + 3 * ct_sel cattr cnlp ngp <= 2 ^ 63.
Hypothesis Sb0 : 4096 <= ct_sel battr blpal gpal. Hypothesis Sb1 : ct_sel battr blpal gpal + 3 * ct_sel battr bnlp ngp <= 2 ^ 63.
Hypothesis Pimg : forall i, 0 <= i < N -> present mem0 (img + i).
Hypothesis Pfimg : forall i, 0 <= i < N -> present mem0 (fimg + i).
Hypothesis Himg0 : 4096 <= img. Hypothesis Himg1 : img + N <= alloc_ceiling.
Hypothesis Hfimg0 : 4096 <= fimg. Hypothesis Hfimg1 : fimg + N <= alloc_ceiling.
Hypothesis HN : N < 2 ^ 32.
Hypothesis Dif : img + N <= fimg \/ fimg + N <= img.
Definition LOOP_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%bv.
Definition loop_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (c' : config) : Prop :=
exists regs' mem' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom src2segs)) mdc /\ (pc' = AF_C \/ pc' = AF_SAME) /\
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall x, mem' x = mem0 x) /\
(forall r : reg, In r LOOP_KEPT -> getr regs' r = getr regs r).
Lemma af_loop : forall (n : nat) (k : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc,
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
(forall x, memc x = mem0 x) ->
0 <= k -> k + Z.of_nat n = N -> (1 <= n)%nat ->
getr regs 8 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 cfp -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 23 = Z_to_bv 64 (img + k) -> getr regs 24 = Z_to_bv 64 (fimg + k) -> getr regs 25 = Z_to_bv 64 (Z.of_nat n) ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 AF_LOOP) memc (seg_rom src2segs)) mdc) (loop_post STK sp0 FP L A mem md Lc Ac mdc regs).
Proof.
intros n. induction n as [|n IH]; intros k STK sp0 FP L A mem md Lc Ac mdc regs memc HJ Hmem Hk HkN Hn G8 G9 G18 G21 G22 G25; [lia|].
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
set (bc := byte_at memc (img + k)). set (bb := byte_at memc (fimg + k)).
pose proof (byte_at_range memc (img + k)) as Rbc. pose proof (byte_at_range memc (fimg + k)) as Rbb. fold bc in Rbc. fold bb in Rbb.
set (E := Ereg regs (map (Z_to_bv 64) [bc; bb] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 bc) by (subst E; apply (Ereg_vals regs [bc; bb] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 bb) by (subst E; apply (Ereg_vals regs [bc; bb] [] 1%nat); reflexivity).
assert (HU21 : bv_unsigned (ew E 23) = img + k) by (rewrite (HE 23%nat 23%bv eq_refl), G21; apply unsigned_lit_small; lia).
assert (HU22 : bv_unsigned (ew E 24) = fimg + k) by (rewrite (HE 24%nat 24%bv eq_refl), G22; apply unsigned_lit_small; lia).
assert (HS : st_ok src2segs E ss_loop (mkst regs (Z_to_bv 64 AF_LOOP) memc (seg_rom src2segs))).
{ unfold ss_loop. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU21.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. rewrite <- (Hmem (Z_to_bv 64 (img + k))) || idtac. unfold present. rewrite Hmem. apply (Pimg k). lia.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU22.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. unfold present. rewrite Hmem. apply (Pfimg k). lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU21, HU22.
repeat split; try exact I. clear - Dif Hk HkN Hn. lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU21, HU22, HE32, HE33, (HE 25%nat 25%bv eq_refl), G25, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 AF_LOOP) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_cmpPixel. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ha0. rewrite (HE 8%nat 8%bv eq_refl), G8 in Ha0.
jreg HS (11%bv:reg) as Ha1. rewrite (HE 9%nat 9%bv eq_refl), G9 in Ha1.
jreg HS (12%bv:reg) as Ha2. rewrite (HE 18%nat 18%bv eq_refl), G18 in Ha2.
jreg HS (13%bv:reg) as Ha3. rewrite HE32 in Ha3. jreg HS (14%bv:reg) as Ha4. rewrite HE33 in Ha4.
jreg HS (1%bv:reg) as Hra.
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms x = mem0 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply Hmem. }
clear HF.
destruct (src2_cmpPixelG (ms_regs ms) (ms_mem ms) g gvals cfp cvals fhp bvals bc bb ctcur ctbef cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal
Ha0 Ha1 Ha2 Ha3 Ha4 Rbc Rbb) as (regs2 & mem2 & Hms & Hmem2 & Hres & Hfr2);
[ eapply obj_at_transport_range; [exact Og | exact (proj1 LAY_CGIF_ok) | intros i Hi; apply mbyte_of_eq; exact K1]
| exact Ongp | exact Ogpal
| eapply obj_at_transport_range; [exact Oc | exact lay_inside_FrameConfig | intros i Hi; apply mbyte_of_eq; exact K1]
| exact Ocattr | exact Octidx | exact Ocnlp | exact Oclpal
| eapply obj_at_transport_range; [exact Ob | exact lay_inside_FrameConfig | intros i Hi; apply mbyte_of_eq; exact K1]
| exact Obattr | exact Obtidx | exact Obnlp | exact Oblpal
| exact G0 | exact G1 | exact G16 | exact C0 | exact C1 | exact C8 | exact B0 | exact B1 | exact B8 | exact Dgc | exact Dgb | exact Dcb
| rewrite (rdn_ext src2segs (ms_mem ms) mem0) by exact K1; exact Rct
| rewrite (rdn_ext src2segs (ms_mem ms) mem0) by exact K1; exact Rbt
| exact Sc0 | exact Sc1 | exact Sb0 | exact Sb1 | ].
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc ss_loop].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
replace (v_jalr (getr (ms_regs ms) 1) 0) with (Z_to_bv 64 AF_CMPRET).
2:{ rewrite Hra. symmetry. apply ret_ok_even. vm_compute. reflexivity. }
assert (HJ2 : journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc).
{ eapply (journal_exec _ _ LAWS IMG) with (W := fun _ => False); [exact HJ | intros x _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2 | intros a []]. }
clear HJ.
jafter_stretch_keep HS 34%nat regs2 mem2 CMP_CLOB AF_CMPRET [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. destruct (cmp_clob_out rr Hrr) as (?&?&?&?&?&?&?&?&?&?). apply Hfr2; assumption. }
{ constructor; [|constructor; [|constructor]];
(eapply (region_kept_out src2segs _ _ _ _ 0 0); [intros x _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2
| cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HU21, ?HU22; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HU21, ?HU22; lia
| intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 AF_CMPRET) mem2 (seg_rom src2segs))) in HJ2.
assert (K2 : forall x, mem2 x = mem0 x) by (intros x; rewrite Hmem2; apply K1).
assert (EA : forall k' ws E', env_agree 32 E E' -> (32 <= k')%nat -> env_agree 32 E (havoc E' k' ws)).
{ intros k' ws E' HA Hk'. apply env_agree_havoc_ge; [exact Hk' | exact HA]. }
pose proof (EA 34%nat (map (getr regs2) CMP_CLOB) E (env_agree_refl _ _) ltac:(lia)) as EA1.
assert (EXIT : forall E' ss ms' pc', st_ok src2segs E' ss ms' -> env_agree 32 E E' -> ss_pc ss = pc' -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) LOOP_KEPT = true ->
(pc' = AF_C \/ pc' = AF_SAME) ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall x, ms_mem ms' x = mem0 x) ->
loop_post STK sp0 FP L A mem md Lc Ac mdc regs (mkCfg ms' mdc)).
{ intros E' ss ms' pc' HS' HA Hpc Hrv Hkl Hpc' HJ' K. exists (ms_regs ms'), (ms_mem ms'), pc'.
split; [rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact Hpc'|]. split; [exact HJ'|]. split; [exact K|].
intros rr Hrr. subst E. exact (regs_kept_of_st_ok src2segs E' ss ms' regs _ LOOP_KEPT HS' HA Hkl rr Hrr). }
jbranch src2tbl HS; clear Hc.
-
jrun_to LAWS src2tbl_ok HS HJ2 AF_C. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ _ AF_C HS EA1 eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(left; reflexivity) HJ2).
intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2.
-
jrun LAWS src2tbl_ok HS HJ2. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall x, ms_mem ms0 x = mem0 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF.
jbranch src2tbl HS.
+
clear Hc. jrun_to LAWS src2tbl_ok HS HJ2 AF_SAME. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ _ AF_SAME HS EA1 eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(right; reflexivity) HJ2).
intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3.
+
rewrite branch_eq_U, U_lit in Hc by lia.
rewrite (U_atom_off _ 25 (Z.of_nat (Datatypes.S n)) (-1)) in Hc by first [ew_havocA; rewrite (HE 25%nat 25%bv eq_refl); exact G25 | lia].
assert (Hn1 : (1 <= n)%nat) by (destruct (Z.eqb_spec (Z.of_nat (Datatypes.S n) + -1) 0); [discriminate Hc | lia]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ2 AF_LOOP. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K4 : forall x, ms_mem ms1 x = mem0 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3. }
clear HF.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs _ LOOP_KEPT HS ltac:(subst E; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (k + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ HJ2 K4 ltac:(lia) ltac:(lia) Hn1).
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- reg_nowF HS ltac:(ew_havocA; rewrite HU21; f_equal; lia).
- reg_nowF HS ltac:(ew_havocA; rewrite HU22; f_equal; lia).
- reg_nowF HS ltac:(ew_havocA; rewrite (HE 25%nat 25%bv eq_refl), G25, unsigned_lit_small by lia; f_equal; lia). }
cbv beta. intros c' (regs' & mem' & pc' & -> & Hpc' & HJ' & K' & HK'). exists regs', mem', pc'.
split; [reflexivity|]. split; [exact Hpc'|]. split; [exact HJ'|]. split; [exact K'|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
Qed.
End c.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
