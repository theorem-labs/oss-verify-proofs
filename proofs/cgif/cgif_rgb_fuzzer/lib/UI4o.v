(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI07
UI1e UI1i YI0x UI56 UI1h YP14 YI08 YI0c YI0g YI0f UI4v UIZm.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition PC_SL : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 2944).
Definition PC_A2 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 3012).
Definition PC_C  : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 3060).
Definition PC_SB : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 3144).
Definition PC_EX : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 3212).
Definition PC_X2 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 3228).
Definition PC_X3 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 3240).
Definition sm_cond (ha bef : Z) : Z := if (ha =? 0) && negb (bef =? 0) then 1 else 0.
Definition sm_notha (ha : Z) : Z := if ha =? 0 then 1 else 0.
Lemma in_bv5_sm : forall (r : reg) (L : list reg), existsb (bv_eqb r) L = true -> In r L.
Proof. intros r L H. apply existsb_exists in H as (r' & Hin & Heq). apply bv_eqb_eq in Heq. subst r'. exact Hin. Qed.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Notation segs := ubs2segs (only parsing).
Local Notation rom := (seg_rom ubs2segs) (only parsing).
Lemma getr_of_U_mk : forall E ss (regs : bvmap 5 word) pc mem (rr : reg) v,
st_ok segs E ss (mkst regs pc mem rom) -> U E (sr_get (ss_regs ss) rr) = v -> getr regs rr = Z_to_bv 64 v.
Proof. intros E ss regs pc mem rr v HS HU. exact (getr_of_U segs E ss (mkst regs pc mem rom) rr v HS HU). Qed.
Tactic Notation "jregm" constr(HS) constr(r) "as" ident(Hr) := jreg HS r as Hr; cbn [ms_regs mkst] in Hr.
Ltac wr_ok_eval :=
lazymatch goal with |- wr_ok ?Ee ?rs ?stk ?spp ?fp ?b0 ?bc => let rs' := eval vm_compute in rs in change (wr_ok Ee rs' stk spp fp b0 bc) end.
Lemma smj_U_add_atom : forall E n b a x, ew E n = Z_to_bv 64 b -> 0 <= b -> U E a = x -> 0 <= x -> b + x < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff n 0) a) = b + x.
Proof.
intros E n b a x Hn Hb Ha Hx Hbx. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n b Hn), Ha by lia. apply zcanon_id. unfold M64; lia.
Qed.
Definition SL_KEEP : list reg := [2; 3; 4; 8; 9; 19; 20; 21; 22; 24; 25; 26; 27]%bv.
Definition KEEP2 : list reg := [2; 3; 4; 8; 9; 19; 20; 21; 22; 24; 25; 26; 27]%bv.
Definition SB_KEEP : list reg := [2; 3; 4; 8; 9; 14; 15; 19; 20; 21; 26; 27]%bv.
Definition smj_A2Z_KEEP : list reg := [2; 3; 4; 8; 9; 19; 20; 21; 26; 27]%bv.
Definition X1_KEEP : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition X2_KEEP : list reg := [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition X3_KEEP : list reg := [2; 3; 4; 8; 9]%bv.
Definition P_KEEP : list reg := [2; 3; 4; 8; 20; 21]%bv.
Definition ss_SLA0 : sstate :=
mkSS PC_SL (sr_set (sr_set sr_atoms 9%bv (SLit 0)) 19%bv (SLit 1))
[ YQ0b.mkRegion (Some 20%nat) 8 48 0 0 [mkChunk 8 (CVal 8 (SOff 33 0)); mkChunk 16 (CVal 8 (SOff 34 0)); mkChunk 44 (CVal 4 (SOff 35 0))] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (20%nat, mkAF 4096 (2^48) 0); (22%nat, mkAF 0 (2^31) 0);
 (15%nat, mkAF 4096 (2^64 - 1) 0); (32%nat, mkAF 4096 (2^64 - 1) 0); (35%nat, mkAF 0 (2^31 - 1) 0) ]
 [mkAC BC_GEU (SOff 32 0) (SOff 15 0)]
 [(SAlu ALU_ADD (SOff 15 0) (SOff 22 0), SOff 32 0)]).
Lemma SLA0_stretch : forall (regs : bvmap 5 word) mem (sp fi img fmt c hv uv T : Z),
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5168 <= 2 ^ 63 -> sp mod 16 = 0 ->
getr regs 9 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 fi -> 0 <= fi < 2 ^ 31 ->
getr regs 15 = Z_to_bv 64 img -> 4096 <= img -> img + fi < 2 ^ 64 -> getr regs 14 = Z_to_bv 64 fmt ->
getr regs 20 = Z_to_bv 64 c -> 4096 <= c -> c + 48 <= alloc_ceiling ->
word_mem segs mem (c + 8) hv -> 0 <= hv < 2 ^ 64 -> word_mem segs mem (c + 16) uv -> 0 <= uv < 2 ^ 64 ->
val_mem segs mem (c + 44) 4 T -> 0 <= T < 2 ^ 31 ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_SL) mem rom) (mkst regs' (Z_to_bv 64 ubs2_A_col_hash) mem rom) /\
getr regs' 1 = Z_to_bv 64 PC_C /\ getr regs' 10 = Z_to_bv 64 (img + fi) /\ getr regs' 11 = Z_to_bv 64 hv /\
getr regs' 12 = Z_to_bv 64 uv /\ getr regs' 13 = Z_to_bv 64 T /\ getr regs' 14 = Z_to_bv 64 fmt /\
(forall r : reg, In r SL_KEEP -> getr regs' r = getr regs r).
Proof.
intros regs mem sp fi img fmt c hv uv T Hr2 Hsplo Hsphi Hal16 Hr9 Hr19 Hr22 Hfi Hr15 Himg0 Himg1 Hr14
Hr20 Hc0 Hc1 Vh Hhv Vu Huv VT HT.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [img + fi; hv; uv; T] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 (img + fi)) by (subst E; apply (Ereg_vals regs [img + fi; hv; uv; T] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 hv) by (subst E; apply (Ereg_vals regs [img + fi; hv; uv; T] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 uv) by (subst E; apply (Ereg_vals regs [img + fi; hv; uv; T] [] 2%nat); reflexivity).
assert (A35 : ew E 35 = Z_to_bv 64 T) by (subst E; apply (Ereg_vals regs [img + fi; hv; uv; T] [] 3%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU15 : bv_unsigned (ew E 15) = img) by (rewrite (HE 15%nat 15%bv eq_refl), Hr15; apply unsigned_lit_small; lia).
assert (HU20 : bv_unsigned (ew E 20) = c) by (rewrite (HE 20%nat 20%bv eq_refl), Hr20; apply unsigned_lit_small; lia).
assert (HU22 : bv_unsigned (ew E 22) = fi) by (rewrite (HE 22%nat 22%bv eq_refl), Hr22; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = img + fi) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = hv) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = uv) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HU35 : bv_unsigned (ew E 35) = T) by (rewrite A35; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_SLA0 (mkst regs (Z_to_bv 64 PC_SL) mem rom)).
{ unfold ss_SLA0. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite Hr9; reflexivity] | intros X; discriminate X | rewrite Hr19; reflexivity].
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Vh].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Vu].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU35; reflexivity | cbn; lia | cbn; lia | exact VT].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU20, HU22, HU15, HU32, HU35.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, !U_SOff, HU32, HU15, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; lia). apply Bool.negb_true_iff, Z.ltb_ge. lia.
+ cbn [f_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite (U_atom _ 32 (img + fi) A32) by lia.
apply (smj_U_add_atom _ 15 img _ fi); [rewrite (HE 15%nat 15%bv eq_refl); exact Hr15 | lia | apply (U_atom _ 22 fi); [rewrite (HE 22%nat 22%bv eq_refl); exact Hr22 | lia] | lia | lia]. }
pure_to ubs2tbl_ok HS ubs2_A_col_hash.
exists regs0. split; [exact Hms|].
split; [jregm HS (1%bv:reg) as Hq; exact Hq|].
split; [jregm HS (10%bv:reg) as Hq; rewrite Hq; exact A32|].
split; [jregm HS (11%bv:reg) as Hq; rewrite Hq; exact A33|].
split; [jregm HS (12%bv:reg) as Hq; rewrite Hq; exact A34|].
split; [jregm HS (13%bv:reg) as Hq; rewrite Hq; exact A35|].
split; [jregm HS (14%bv:reg) as Hq; rewrite Hq, (HE 14%nat 14%bv eq_refl); exact Hr14|].
assert (HK : forall r : reg, In r [2; 3; 4; 8; 20; 21; 22; 24; 25; 26; 27]%bv -> getr regs0 r = getr regs r)
by exact (regs_kept_of_st_ok _ _ _ _ regs _ [2; 3; 4; 8; 20; 21; 22; 24; 25; 26; 27]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
intros r Hr. destruct (bv_eqb r 9%bv) eqn:E9; [|destruct (bv_eqb r 19%bv) eqn:E19].
- apply bv_eqb_eq in E9. subst r. jregm HS (9%bv:reg) as Hq. rewrite Hq, Hr9. reflexivity.
- apply bv_eqb_eq in E19. subst r. jregm HS (19%bv:reg) as Hq. rewrite Hq, Hr19. reflexivity.
- apply HK. unfold SL_KEEP in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [first [vm_compute in E9; discriminate E9 | vm_compute in E19; discriminate E19 | cbv; tauto] |]). contradiction.
Qed.
Definition ss_SLA1 : sstate :=
mkSS PC_SL (sr_set sr_atoms 19%bv (SLit 1))
[ YQ0b.mkRegion (Some 2%nat) 72 96 0 0 [mkChunk 72 (CVal 8 (SOff 33 0)); mkChunk 88 (CVal 8 (SOff 34 0))] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (9%nat, mkAF 1 1 0); (22%nat, mkAF 0 (2^31) 0); (24%nat, mkAF 0 (2^31) 0);
 (15%nat, mkAF 4096 (2^64 - 1) 0); (32%nat, mkAF 4096 (2^64 - 1) 0) ]
 [mkAC BC_GEU (SOff 32 0) (SOff 15 0); mkAC BC_GEU (SOff 33 0) (SOff 24 0)]
 [(SAlu ALU_ADD (SOff 15 0) (SOff 22 0), SOff 32 0)]).
Lemma SLA1_stretch : forall (regs : bvmap 5 word) mem (sp fi bfi img bef : Z),
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5168 <= 2 ^ 63 -> sp mod 16 = 0 ->
getr regs 9 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 fi -> 0 <= fi < 2 ^ 31 ->
getr regs 24 = Z_to_bv 64 bfi -> 0 <= bfi < 2 ^ 31 ->
getr regs 15 = Z_to_bv 64 img -> 4096 <= img -> img + fi < 2 ^ 64 ->
word_mem segs mem (sp + 72) (2 ^ 64 - 1 - bef) -> word_mem segs mem (sp + 88) bef -> 0 <= bef -> bef + bfi < 2 ^ 64 ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_SL) mem rom) (mkst regs' (Z_to_bv 64 ubs2_A_bcmp) mem rom) /\
getr regs' 1 = Z_to_bv 64 PC_A2 /\ getr regs' 10 = Z_to_bv 64 (img + fi) /\ getr regs' 11 = Z_to_bv 64 (bef + bfi) /\
getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 23 = Z_to_bv 64 (img + fi) /\ getr regs' 18 = Z_to_bv 64 fi /\
(forall r : reg, In r SL_KEEP -> getr regs' r = getr regs r).
Proof.
intros regs mem sp fi bfi img bef Hr2 Hsplo Hsphi Hal16 Hr9 Hr19 Hr22 Hfi Hr24 Hbfi Hr15 Himg0 Himg1 V72 V88 Hbef0 Hbef1.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [img + fi; 2 ^ 64 - 1 - bef; bef] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 (img + fi)) by (subst E; apply (Ereg_vals regs [img + fi; 2 ^ 64 - 1 - bef; bef] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 (2 ^ 64 - 1 - bef)) by (subst E; apply (Ereg_vals regs [img + fi; 2 ^ 64 - 1 - bef; bef] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 bef) by (subst E; apply (Ereg_vals regs [img + fi; 2 ^ 64 - 1 - bef; bef] [] 2%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = 1) by (rewrite (HE 9%nat 9%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HU15 : bv_unsigned (ew E 15) = img) by (rewrite (HE 15%nat 15%bv eq_refl), Hr15; apply unsigned_lit_small; lia).
assert (HU22 : bv_unsigned (ew E 22) = fi) by (rewrite (HE 22%nat 22%bv eq_refl), Hr22; apply unsigned_lit_small; lia).
assert (HU24 : bv_unsigned (ew E 24) = bfi) by (rewrite (HE 24%nat 24%bv eq_refl), Hr24; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = img + fi) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = 2 ^ 64 - 1 - bef) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = bef) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_SLA1 (mkst regs (Z_to_bv 64 PC_SL) mem rom)).
{ unfold ss_SLA1. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite Hr19; reflexivity].
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V72].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V88].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU9, HU22, HU24, HU15, HU32.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_conds conds_ok]. split; [|split; [|exact I]].
* unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, !U_SOff, HU32, HU15, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; lia). apply Bool.negb_true_iff, Z.ltb_ge. lia.
* unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, !U_SOff, HU33, HU24, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; lia). apply Bool.negb_true_iff, Z.ltb_ge. lia.
+ cbn [f_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite (U_atom _ 32 (img + fi) A32) by lia.
apply (smj_U_add_atom _ 15 img _ fi); [rewrite (HE 15%nat 15%bv eq_refl); exact Hr15 | lia | apply (U_atom _ 22 fi); [rewrite (HE 22%nat 22%bv eq_refl); exact Hr22 | lia] | lia | lia]. }
pure_to ubs2tbl_ok HS ubs2_A_bcmp.
exists regs0. split; [exact Hms|].
split; [jregm HS (1%bv:reg) as Hq; exact Hq|].
split; [jregm HS (10%bv:reg) as Hq; rewrite Hq; exact A32|].
split. { eapply getr_of_U_mk; [exact HS|]. eval_sr_get.
first [ rewrite Z.add_comm; apply (smj_U_add_atom _ 24 bfi _ bef); [rewrite (HE 24%nat 24%bv eq_refl); exact Hr24 | lia | apply (U_atom _ 34 bef A34); lia | lia | lia]
      | apply (smj_U_add_atom _ 34 bef _ bfi); [exact A34 | lia | apply (U_atom _ 24 bfi); [rewrite (HE 24%nat 24%bv eq_refl); exact Hr24 | lia] | lia | lia] ]. }
split; [jregm HS (12%bv:reg) as Hq; exact Hq|].
split; [jregm HS (23%bv:reg) as Hq; rewrite Hq; exact A32|].
split; [jregm HS (18%bv:reg) as Hq; rewrite Hq, (HE 22%nat 22%bv eq_refl); exact Hr22|].
assert (HK : forall r : reg, In r [2; 3; 4; 8; 9; 20; 21; 22; 24; 25; 26; 27]%bv -> getr regs0 r = getr regs r)
by exact (regs_kept_of_st_ok _ _ _ _ regs _ [2; 3; 4; 8; 9; 20; 21; 22; 24; 25; 26; 27]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
intros r Hr. destruct (bv_eqb r 19%bv) eqn:E19.
- apply bv_eqb_eq in E19. subst r. jregm HS (19%bv:reg) as Hq. rewrite Hq, Hr19. reflexivity.
- apply HK. unfold SL_KEEP in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [first [vm_compute in E19; discriminate E19 | cbv; tauto] |]). contradiction.
Qed.
Definition ss_A2nz : sstate :=
mkSS PC_A2 (sr_set sr_atoms 19%bv (SLit 1))
[ YQ0b.mkRegion (Some 2%nat) 112 128 0 0 [mkChunk 112 (CVal 8 (SOff 32 0)); mkChunk 120 (CVal 8 (SOff 33 0))];
  YQ0b.mkRegion (Some 20%nat) 8 48 0 0 [mkChunk 8 (CVal 8 (SOff 34 0)); mkChunk 16 (CVal 8 (SOff 35 0)); mkChunk 44 (CVal 4 (SOff 36 0))] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (10%nat, mkAF 1 (2^64 - 1) 0); (20%nat, mkAF 4096 (2^48) 0);
 (32%nat, mkAF 4096 (2^64 - 1) 0); (23%nat, mkAF 4096 (2^64 - 1) 0); (18%nat, mkAF 0 (2^31) 0); (36%nat, mkAF 0 (2^31 - 1) 0) ]
 [mkAC BC_GEU (SOff 23 0) (SOff 32 0)]
 []).
Lemma A2nz_stretch : forall (regs : bvmap 5 word) mem (sp fi img fmt c hv uv T : Z),
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5168 <= 2 ^ 63 -> sp mod 16 = 0 ->
bv_unsigned (getr regs 10) <> 0 ->
word_mem segs mem (sp + 112) img -> word_mem segs mem (sp + 120) fmt -> 0 <= fmt < 2 ^ 64 ->
getr regs 19 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 fi -> getr regs 23 = Z_to_bv 64 (img + fi) ->
0 <= fi < 2 ^ 31 -> 4096 <= img -> img + fi < 2 ^ 64 ->
getr regs 20 = Z_to_bv 64 c -> 4096 <= c -> c + 48 <= alloc_ceiling ->
word_mem segs mem (c + 8) hv -> 0 <= hv < 2 ^ 64 -> word_mem segs mem (c + 16) uv -> 0 <= uv < 2 ^ 64 ->
val_mem segs mem (c + 44) 4 T -> 0 <= T < 2 ^ 31 ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_A2) mem rom) (mkst regs' (Z_to_bv 64 ubs2_A_col_hash) mem rom) /\
getr regs' 1 = Z_to_bv 64 PC_C /\ getr regs' 10 = Z_to_bv 64 (img + fi) /\ getr regs' 11 = Z_to_bv 64 hv /\
getr regs' 12 = Z_to_bv 64 uv /\ getr regs' 13 = Z_to_bv 64 T /\ getr regs' 14 = Z_to_bv 64 fmt /\
(forall r : reg, In r KEEP2 -> getr regs' r = getr regs r).
Proof.
intros regs mem sp fi img fmt c hv uv T Hr2 Hsplo Hsphi Hal16 Hnz V112 V120 Hfmt Hr19 Hr18 Hr23 Hfi Himg0 Himg1
Hr20 Hc0 Hc1 Vh Hhv Vu Huv VT HT.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (bv_unsigned_in_range _ (getr regs 10)) as R10. change (bv_modulus 64) with (2 ^ 64) in R10.
set (E := Ereg regs (map (Z_to_bv 64) [img; fmt; hv; uv; T] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 img) by (subst E; apply (Ereg_vals regs [img; fmt; hv; uv; T] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 fmt) by (subst E; apply (Ereg_vals regs [img; fmt; hv; uv; T] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 hv) by (subst E; apply (Ereg_vals regs [img; fmt; hv; uv; T] [] 2%nat); reflexivity).
assert (A35 : ew E 35 = Z_to_bv 64 uv) by (subst E; apply (Ereg_vals regs [img; fmt; hv; uv; T] [] 3%nat); reflexivity).
assert (A36 : ew E 36 = Z_to_bv 64 T) by (subst E; apply (Ereg_vals regs [img; fmt; hv; uv; T] [] 4%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 18) = fi) by (rewrite (HE 18%nat 18%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU20 : bv_unsigned (ew E 20) = c) by (rewrite (HE 20%nat 20%bv eq_refl), Hr20; apply unsigned_lit_small; lia).
assert (HU23 : bv_unsigned (ew E 23) = img + fi) by (rewrite (HE 23%nat 23%bv eq_refl), Hr23; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = bv_unsigned (getr regs 10)) by (rewrite (HE 10%nat 10%bv eq_refl); reflexivity).
assert (HU32 : bv_unsigned (ew E 32) = img) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = fmt) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = hv) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HU35 : bv_unsigned (ew E 35) = uv) by (rewrite A35; apply unsigned_lit_small; lia).
assert (HU36 : bv_unsigned (ew E 36) = T) by (rewrite A36; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_A2nz (mkst regs (Z_to_bv 64 PC_A2) mem rom)).
{ unfold ss_A2nz. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite Hr19; reflexivity].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V112].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V120].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Vh].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU35; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Vu].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU36; reflexivity | cbn; lia | cbn; lia | exact VT].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU20. repeat split; lia.
- split; [|split; [|exact I]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU10, HU20, HU32, HU23, HU18, HU36.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, !U_SOff, HU23, HU32, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; lia). apply Bool.negb_true_iff, Z.ltb_ge. lia. }
pure_to ubs2tbl_ok HS ubs2_A_col_hash.
exists regs0. split; [exact Hms|].
split; [jregm HS (1%bv:reg) as Hq; exact Hq|].
split. { eapply getr_of_U_mk; [exact HS|]. eval_sr_get. rewrite Z.add_comm.
apply (smj_U_add_atom _ 18 fi _ img); [rewrite (HE 18%nat 18%bv eq_refl); exact Hr18 | lia | apply (U_atom _ 32 img A32); lia | lia | lia]. }
split; [jregm HS (11%bv:reg) as Hq; rewrite Hq; exact A34|].
split; [jregm HS (12%bv:reg) as Hq; rewrite Hq; exact A35|].
split; [jregm HS (13%bv:reg) as Hq; rewrite Hq; exact A36|].
split; [jregm HS (14%bv:reg) as Hq; rewrite Hq; exact A33|].
assert (HK : forall r : reg, In r [2; 3; 4; 8; 9; 20; 21; 22; 24; 25; 26; 27]%bv -> getr regs0 r = getr regs r)
by exact (regs_kept_of_st_ok _ _ _ _ regs _ [2; 3; 4; 8; 9; 20; 21; 22; 24; 25; 26; 27]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
intros r Hr. destruct (bv_eqb r 19%bv) eqn:E19.
- apply bv_eqb_eq in E19. subst r. jregm HS (19%bv:reg) as Hq. rewrite Hq, Hr19. reflexivity.
- apply HK. unfold KEEP2 in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [first [vm_compute in E19; discriminate E19 | cbv; tauto] |]). contradiction.
Qed.
Definition ss_CT : sstate :=
mkSS PC_C (sr_set sr_atoms 10%bv (SLit (2 ^ 64 - 1)))
[ YQ0b.mkRegion (Some 2%nat) 80 128 0 0 [mkChunk 80 (CVal 8 (SOff 32 0)); mkChunk 112 (CVal 8 (SOff 33 0)); mkChunk 120 (CVal 8 (SOff 34 0))] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4) ] [] []).
Lemma CT_stretch : forall (regs : bvmap 5 word) mem (sp img fmt v80 : Z),
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5168 <= 2 ^ 63 -> sp mod 16 = 0 ->
getr regs 10 = Z_to_bv 64 (2 ^ 64 - 1) ->
word_mem segs mem (sp + 80) v80 -> word_mem segs mem (sp + 112) img -> word_mem segs mem (sp + 120) fmt ->
0 <= v80 < 2 ^ 64 -> 0 <= img < 2 ^ 64 -> 0 <= fmt < 2 ^ 64 ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_C) mem rom) (mkst regs' (Z_to_bv 64 PC_SB) mem rom) /\
getr regs' 15 = Z_to_bv 64 img /\ getr regs' 14 = Z_to_bv 64 fmt /\
(forall r : reg, In r KEEP2 -> getr regs' r = getr regs r).
Proof.
intros regs mem sp img fmt v80 Hr2 Hsplo Hsphi Hal16 Hr10 V80 V112 V120 Hv80 Himg Hfmt.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [v80; img; fmt] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 v80) by (subst E; apply (Ereg_vals regs [v80; img; fmt] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 img) by (subst E; apply (Ereg_vals regs [v80; img; fmt] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 fmt) by (subst E; apply (Ereg_vals regs [v80; img; fmt] [] 2%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = v80) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = img) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = fmt) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_CT (mkst regs (Z_to_bv 64 PC_C) mem rom)).
{ unfold ss_CT. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite Hr10; reflexivity].
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V80].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V112].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V120].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. repeat split; lia. }
pure_to ubs2tbl_ok HS PC_SB.
exists regs0. split; [exact Hms|].
split; [jregm HS (15%bv:reg) as Hq; rewrite Hq; exact A33|].
split; [jregm HS (14%bv:reg) as Hq; rewrite Hq; exact A34|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ KEEP2 HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_CI : sstate :=
mkSS PC_C sr_atoms
[ YQ0b.mkRegion (Some 20%nat) 32 40 0 0 [mkChunk 32 (CVal 8 (SOff 32 0))];
  YQ0b.mkRegion (Some 2%nat) 112 128 0 0 [mkChunk 112 (CVal 8 (SOff 33 0)); mkChunk 120 (CVal 8 (SOff 34 0))];
  YQ0b.mkRegion (Some 35%nat) 0 4 0 0 [mkChunk 0 (CVal 4 (SOff 36 0))] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (10%nat, mkAF 0 (2^30) 0); (20%nat, mkAF 4096 (2^48) 0);
 (32%nat, mkAF 4096 (2^48) 2); (35%nat, mkAF 4096 (2^48) 2) ]
 [mkAC BC_GEU (SOff 35 0) (SOff 32 0)]
 [(SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 2)) (SOff 32 0), SOff 35 0)]).
Lemma CI_stretch : forall (regs : bvmap 5 word) mem (sp img fmt h c x v : Z),
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5168 <= 2 ^ 63 -> sp mod 16 = 0 ->
word_mem segs mem (sp + 112) img -> word_mem segs mem (sp + 120) fmt -> 0 <= img < 2 ^ 64 -> 0 <= fmt < 2 ^ 64 ->
getr regs 10 = Z_to_bv 64 h -> 0 <= h < 2 ^ 30 ->
getr regs 20 = Z_to_bv 64 c -> 4096 <= c -> c + 48 <= alloc_ceiling ->
word_mem segs mem (c + 32) x -> 4096 <= x -> x + 4 * h + 4 <= alloc_ceiling -> x mod 4 = 0 ->
val_mem segs mem (x + 4 * h) 4 v -> 0 <= v < 2 ^ 32 -> (c + 48 <= x \/ x + 4 * h + 4 <= c) ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_C) mem rom) (mkst regs' (Z_to_bv 64 PC_SB) mem rom) /\
getr regs' 15 = Z_to_bv 64 img /\ getr regs' 14 = Z_to_bv 64 fmt /\
(forall r : reg, In r KEEP2 -> getr regs' r = getr regs r).
Proof.
intros regs mem sp img fmt h c x v Hr2 Hsplo Hsphi Hal16 V112 V120 Himg Hfmt Hr10 Hh Hr20 Hc0 Hc1 Vx Hx0 Hx1 Hx4 Vv Hv Hcx.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [x; img; fmt; x + 4 * h; v] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 x) by (subst E; apply (Ereg_vals regs [x; img; fmt; x + 4 * h; v] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 img) by (subst E; apply (Ereg_vals regs [x; img; fmt; x + 4 * h; v] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 fmt) by (subst E; apply (Ereg_vals regs [x; img; fmt; x + 4 * h; v] [] 2%nat); reflexivity).
assert (A35 : ew E 35 = Z_to_bv 64 (x + 4 * h)) by (subst E; apply (Ereg_vals regs [x; img; fmt; x + 4 * h; v] [] 3%nat); reflexivity).
assert (A36 : ew E 36 = Z_to_bv 64 v) by (subst E; apply (Ereg_vals regs [x; img; fmt; x + 4 * h; v] [] 4%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = h) by (rewrite (HE 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
assert (HU20 : bv_unsigned (ew E 20) = c) by (rewrite (HE 20%nat 20%bv eq_refl), Hr20; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = x) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = img) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = fmt) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HU35 : bv_unsigned (ew E 35) = x + 4 * h) by (rewrite A35; apply unsigned_lit_small; lia).
assert (HU36 : bv_unsigned (ew E 36) = v) by (rewrite A36; apply unsigned_lit_small; lia).
assert (H4 : (x + 4 * h) mod 4 = 0) by (replace (x + 4 * h) with (x + h * 4) by lia; rewrite Z.mod_add; [exact Hx4 | lia]).
assert (HS : st_ok segs E ss_CI (mkst regs (Z_to_bv 64 PC_C) mem rom)).
{ unfold ss_CI. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Vx].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V112].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V120].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU35.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU36; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vv].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU20, HU35. repeat split; lia.
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU10, HU20, HU32, HU35.
change (2 ^ 0) with 1. change (2 ^ 2) with 4. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, !U_SOff, HU35, HU32, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; lia). apply Bool.negb_true_iff, Z.ltb_ge. lia.
+ cbn [f_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, HU10, HU32, HU35, !Z.add_0_r.
rewrite (zcanon_id x), (zcanon_id h) by (unfold M64; lia). change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 2) with 4. rewrite (zcanon_id (h * 4)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia. }
pure_to ubs2tbl_ok HS PC_SB.
exists regs0. split; [exact Hms|].
split; [jregm HS (15%bv:reg) as Hq; rewrite Hq; exact A33|].
split; [jregm HS (14%bv:reg) as Hq; rewrite Hq; exact A34|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ KEEP2 HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_X1 : sstate :=
mkSS PC_EX sr_atoms [ YQ0b.mkRegion (Some 20%nat) 24 32 0 0 [mkChunk 24 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (20%nat, mkAF 4096 (2^48) 0) ] [] []).
Lemma X1_stretch : forall (regs : bvmap 5 word) mem (sp c p : Z),
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5168 <= 2 ^ 63 -> sp mod 16 = 0 ->
getr regs 20 = Z_to_bv 64 c -> 4096 <= c -> c + 48 <= alloc_ceiling ->
word_mem segs mem (c + 24) p -> 0 <= p < 2 ^ 64 ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_EX) mem rom) (mkst regs' (Z_to_bv 64 ubs2_A_memcpy) mem rom) /\
getr regs' 1 = Z_to_bv 64 PC_X2 /\ getr regs' 10 = Z_to_bv 64 (sp + 166) /\ getr regs' 11 = Z_to_bv 64 p /\
getr regs' 12 = Z_to_bv 64 768 /\
(forall r : reg, In r X1_KEEP -> getr regs' r = getr regs r).
Proof.
intros regs mem sp c p Hr2 Hsplo Hsphi Hal16 Hr20 Hc0 Hc1 Vp Hp.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [p] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 p) by (subst E; apply (Ereg_vals regs [p] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU20 : bv_unsigned (ew E 20) = c) by (rewrite (HE 20%nat 20%bv eq_refl), Hr20; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = p) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_X1 (mkst regs (Z_to_bv 64 PC_EX) mem rom)).
{ unfold ss_X1. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Vp].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU20.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
pure_to ubs2tbl_ok HS ubs2_A_memcpy.
exists regs0. split; [exact Hms|].
split; [jregm HS (1%bv:reg) as Hq; exact Hq|].
split; [jregm HS (10%bv:reg) as Hq; rewrite Hq, HU2; reflexivity|].
split; [jregm HS (11%bv:reg) as Hq; rewrite Hq; exact A32|].
split; [jregm HS (12%bv:reg) as Hq; exact Hq|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ X1_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_X2 : sstate :=
mkSS PC_X2 sr_atoms [ YQ0b.mkRegion (Some 20%nat) 40 44 0 0 [mkChunk 40 (CVal 4 (SOff 32 0))] ] None
(mkFacts [ (20%nat, mkAF 4096 (2^48) 0); (32%nat, mkAF 0 255 0) ] [] []).
Lemma X2_stretch : forall (regs : bvmap 5 word) mem (c cnt : Z),
getr regs 20 = Z_to_bv 64 c -> 4096 <= c -> c + 48 <= alloc_ceiling ->
val_mem segs mem (c + 40) 4 cnt -> 0 <= cnt <= 255 ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_X2) mem rom) (mkst regs' (Z_to_bv 64 ubs2_A_free_col_hash_table) mem rom) /\
getr regs' 1 = Z_to_bv 64 PC_X3 /\ getr regs' 10 = getr regs 20 /\ getr regs' 9 = Z_to_bv 64 cnt /\
(forall r : reg, In r X2_KEEP -> getr regs' r = getr regs r).
Proof.
intros regs mem c cnt Hr20 Hc0 Hc1 Vc Hcnt.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [cnt] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 cnt) by (subst E; apply (Ereg_vals regs [cnt] [] 0%nat); reflexivity).
assert (HU20 : bv_unsigned (ew E 20) = c) by (rewrite (HE 20%nat 20%bv eq_refl), Hr20; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = cnt) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_X2 (mkst regs (Z_to_bv 64 PC_X2) mem rom)).
{ unfold ss_X2. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | exact Vc].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU20, HU32.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
pure_to ubs2tbl_ok HS ubs2_A_free_col_hash_table.
exists regs0. split; [exact Hms|].
split; [jregm HS (1%bv:reg) as Hq; exact Hq|].
split; [jregm HS (10%bv:reg) as Hq; rewrite Hq; exact (HE 20%nat 20%bv eq_refl)|].
split; [jregm HS (9%bv:reg) as Hq; rewrite Hq; exact A32|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ X2_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_X3 : sstate :=
mkSS PC_X3 sr_atoms [ YQ0b.mkRegion (Some 2%nat) 24 32 0 0 [mkChunk 24 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (9%nat, mkAF 0 255 0) ] [] []).
Lemma X3_stretch : forall (regs : bvmap 5 word) mem (sp cnt pnew : Z),
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5168 <= 2 ^ 63 -> sp mod 16 = 0 ->
getr regs 9 = Z_to_bv 64 cnt -> 0 <= cnt <= 255 ->
word_mem segs mem (sp + 24) pnew -> 0 <= pnew < 2 ^ 64 ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_X3) mem rom) (mkst regs' (Z_to_bv 64 PC_FIN) mem rom) /\
getr regs' 18 = Z_to_bv 64 pnew /\
(forall r : reg, In r X3_KEEP -> getr regs' r = getr regs r).
Proof.
intros regs mem sp cnt pnew Hr2 Hsplo Hsphi Hal16 Hr9 Hcnt V24 Hpnew.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [pnew] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 pnew) by (subst E; apply (Ereg_vals regs [pnew] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = cnt) by (rewrite (HE 9%nat 9%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = pnew) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_X3 (mkst regs (Z_to_bv 64 PC_X3) mem rom)).
{ unfold ss_X3. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V24].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU9.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia. }
pure_to ubs2tbl_ok HS PC_FIN.
exists regs0. split; [exact Hms|].
split; [jregm HS (18%bv:reg) as Hq; rewrite Hq; exact A32|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ X3_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Lemma smj_lxor_ones : forall u, 0 <= u < 2 ^ 64 -> (Z.lxor u (Z.ones 64)) mod 2 ^ 64 = 2 ^ 64 - 1 - u.
Proof.
intros u Hu. transitivity (Z.lnot u mod 2 ^ 64).
- apply Z.bits_inj'. intros k Hk. destruct (Z.ltb_spec k 64) as [Hl|Hl].
+ rewrite !Z.mod_pow2_bits_low by exact Hl. rewrite Z.lxor_spec, Z.lnot_spec, Z.ones_spec_low by lia. destruct (Z.testbit u k); reflexivity.
+ rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
- unfold Z.lnot. replace (Z.pred (- u)) with ((2 ^ 64 - 1 - u) + (-1) * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma smj_U_cmpl_atom : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - x.
Proof.
intros E n x Hn Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn Hx), U_SLit.
change (zcanon (-1)) with (Z.ones 64). unfold zcanon, M64. apply smj_lxor_ones. exact Hx.
Qed.
Lemma smj_denot_cmpl_atom : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof. intros E n x Hn Hx. rewrite denot_lit_U. f_equal. exact (smj_U_cmpl_atom E n x Hn Hx). Qed.
Lemma smj_U_and255 : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 256 ->
U E (SAlu ALU_AND (SOff n 0) (SLit 255)) = x.
Proof.
intros E n x Hn Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn) by lia. rewrite U_SLit.
change (zcanon 255) with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small by (change (2 ^ 8) with 256; lia).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma smj_U_cond : forall E n m nv bef, bv_unsigned (ew E n) = nv -> 0 <= nv <= 1 -> bv_unsigned (ew E m) = bef -> 0 <= bef < 2 ^ 64 ->
U E (SAlu ALU_AND (SOff n 0) (SAlu ALU_SLTU (SLit 0) (SOff m 0))) = if (nv =? 1) && negb (bef =? 0) then 1 else 0.
Proof.
intros E n m nv bef Hn Hnv Hm Hbef. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, Hn, Hm, !Z.add_0_r. rewrite (zcanon_id bef), (zcanon_id nv) by (unfold M64; lia). change (zcanon 0) with 0.
assert (Hnv' : nv = 0 \/ nv = 1) by lia. destruct Hnv' as [-> | ->]; destruct (Z.ltb_spec 0 bef), (Z.eqb_spec bef 0); try lia; reflexivity.
Qed.
Section J.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition ss_P : sstate :=
mkSS PC_SM sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 48 96 72 88 [mkChunk 48 (CVal 8 (SOff 32 0)); mkChunk 64 (CVal 8 (SOff 33 0)); mkChunk 88 (CVal 8 (SOff 34 0))];
  YQ0b.mkRegion (Some 2%nat) 96 104 96 104 [] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (27%nat, mkAF 1 (2^31) 0); (14%nat, mkAF 3 4 0); (15%nat, mkAF 4096 (2^64 - 1) 0);
 (33%nat, mkAF 0 1 0); (11%nat, mkAF 0 255 0) ] [] []).
Lemma P_stretch : forall (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (sp ha bef fmt img fimg N cnt : Z) Q,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
sp0 - STK <= sp -> sp + 5168 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 11 = Z_to_bv 64 cnt -> getr regs 14 = Z_to_bv 64 fmt ->
getr regs 15 = Z_to_bv 64 img -> getr regs 27 = Z_to_bv 64 N ->
word_mem segs mem (sp + 48) fimg -> word_mem segs mem (sp + 64) (sm_notha ha) -> word_mem segs mem (sp + 88) bef ->
0 <= ha <= 1 -> 0 <= bef < 2 ^ 64 -> 3 <= fmt <= 4 -> 4096 <= img < 2 ^ 64 -> 0 <= fimg < 2 ^ 64 -> 1 <= N < 2 ^ 31 ->
0 <= cnt < 256 ->
(forall regs' mem',
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
word_mem segs mem' (sp + 72) (2 ^ 64 - 1 - bef) -> word_mem segs mem' (sp + 80) cnt -> word_mem segs mem' (sp + 96) fmt ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp + 72 <= x < sp + 88) -> ~ (sp + 96 <= x < sp + 104) -> mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 25 = Z_to_bv 64 0 -> getr regs' 22 = Z_to_bv 64 0 -> getr regs' 24 = Z_to_bv 64 0 ->
getr regs' 9 = Z_to_bv 64 (sm_cond ha bef) -> getr regs' 19 = Z_to_bv 64 1 -> getr regs' 26 = Z_to_bv 64 N ->
getr regs' 27 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) -> getr regs' 15 = Z_to_bv 64 img -> getr regs' 14 = Z_to_bv 64 fmt ->
(forall r : reg, In r P_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (mkst regs' (Z_to_bv 64 PC_SL) mem' rom) md) Q) ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 PC_SM) mem rom) md) Q.
Proof using API IMG.
intros regs mem STK sp0 FP L A mem0 md0 Lc Ac md sp ha bef fmt img fimg N cnt Q HJ Hwlo Hwhi Hal16 Hr2 Hr11 Hr14 Hr15 Hr27
V48 V64 V88 Hha Hbef Hfmt Himg Hfimg HN Hcnt HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (Hnv : 0 <= sm_notha ha <= 1) by (unfold sm_notha; destruct (ha =? 0); lia).
set (E := Ereg regs (map (Z_to_bv 64) [fimg; sm_notha ha; bef] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; apply (Ereg_vals regs [fimg; sm_notha ha; bef] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 (sm_notha ha)) by (subst E; apply (Ereg_vals regs [fimg; sm_notha ha; bef] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 bef) by (subst E; apply (Ereg_vals regs [fimg; sm_notha ha; bef] [] 2%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = cnt) by (rewrite (HE 11%nat 11%bv eq_refl), Hr11; apply unsigned_lit_small; lia).
assert (HU14 : bv_unsigned (ew E 14) = fmt) by (rewrite (HE 14%nat 14%bv eq_refl), Hr14; apply unsigned_lit_small; lia).
assert (HU15 : bv_unsigned (ew E 15) = img) by (rewrite (HE 15%nat 15%bv eq_refl), Hr15; apply unsigned_lit_small; lia).
assert (HU27 : bv_unsigned (ew E 27) = N) by (rewrite (HE 27%nat 27%bv eq_refl), Hr27; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = fimg) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = sm_notha ha) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = bef) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_P (mkst regs (Z_to_bv 64 PC_SM) mem rom)).
{ unfold ss_P. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V48].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V64].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V88].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia | apply Forall_nil].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU27, HU14, HU15, HU33, HU11. change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia. }
change mem with (ms_mem (mkst regs (Z_to_bv 64 PC_SM) mem rom)) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ PC_SL.
{ wr_ok_eval.
eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 2); [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia |].
eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 2); [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (st_chunk_val segs E ssf ms 0%nat _ 2%nat 72 8%N (SAlu ALU_XOR (SOff 34 0) (SLit (-1))) sp (2 ^ 64 - 1 - bef) HS eq_refl eq_refl ltac:(cbn; tauto) HU2
ltac:(exact (smj_denot_cmpl_atom E 34 bef A34 Hbef)) ltac:(cbn; lia) ltac:(cbn; lia)) as M72;
pose proof (st_chunk_val segs E ssf ms 0%nat _ 2%nat 80 8%N (SOff 11 0) sp cnt HS eq_refl eq_refl ltac:(cbn; tauto) HU2
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans (HE 11%nat 11%bv eq_refl) Hr11)) ltac:(cbn; lia) ltac:(cbn; lia)) as M80;
pose proof (st_chunk_val segs E ssf ms 1%nat _ 2%nat 96 8%N (SAlu ALU_AND (SOff 14 0) (SLit 255)) sp fmt HS eq_refl eq_refl ltac:(cbn; tauto) HU2
ltac:(rewrite denot_lit_U; f_equal; apply smj_U_and255; [exact (eq_trans (HE 14%nat 14%bv eq_refl) Hr14) | lia]) ltac:(cbn; lia) ltac:(cbn; lia)) as M96
end.
change (N.to_nat 8) with 8%nat in M72, M80, M96.
apply HK.
- exact HJ.
- apply val_mem_word_mem. exact M72.
- apply val_mem_word_mem. exact M80.
- apply val_mem_word_mem. exact M96.
- intros x Hx Hn1 Hn2. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2; lia). reflexivity.
- jreg HS (25%bv:reg) as Hq; exact Hq.
- jreg HS (22%bv:reg) as Hq; exact Hq.
- jreg HS (24%bv:reg) as Hq; exact Hq.
- eapply (getr_of_U segs); [exact HS|]. eval_sr_get. rewrite (smj_U_cond E 33 34 (sm_notha ha) bef HU33 Hnv HU34 Hbef).
unfold sm_notha, sm_cond. destruct (Z.eqb_spec ha 0); cbn [Z.eqb Pos.eqb andb]; reflexivity.
- jreg HS (19%bv:reg) as Hq; exact Hq.
- jreg HS (26%bv:reg) as Hq. rewrite Hq, (HE 27%nat 27%bv eq_refl). exact Hr27.
- eapply (getr_of_U segs); [exact HS|]. eval_sr_get. exact (smj_U_cmpl_atom E 32 fimg A32 Hfimg).
- jreg HS (15%bv:reg) as Hq. rewrite Hq, (HE 15%nat 15%bv eq_refl). exact Hr15.
- jreg HS (14%bv:reg) as Hq. rewrite Hq, (HE 14%nat 14%bv eq_refl). exact Hr14.
- exact (regs_kept_of_st_ok _ _ _ _ regs _ P_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_SB (c : acond) : sstate :=
mkSS PC_SB sr_atoms
[ YQ0b.mkRegion (Some 35%nat) 0 1 0 1 [];
  YQ0b.mkRegion (Some 2%nat) 48 112 0 0 [mkChunk 48 (CVal 8 (SOff 32 0)); mkChunk 96 (CVal 8 (SOff 33 0)); mkChunk 104 (CVal 8 (SOff 34 0))] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (35%nat, mkAF 4096 (2^48) 0) ]
 [mkAC BC_GEU (SOff 27 0) (SOff 25 0); c]
 [(SAlu ALU_ADD (SOff 32 0) (SOff 25 0), SOff 35 0)]).
Definition sb_cond (last : bool) : acond := mkAC (if last then BC_EQ else BC_NE) (SOff 26%nat 0) (SOff 25%nat 1).
Lemma SB_stretch : forall (last : bool) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (sp fimg i N a22 a24 fmtv bfv : Z) Q,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) (fimg + i) -> writable_at segs mem (fimg + i) ->
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5168 <= 2 ^ 63 -> sp mod 16 = 0 ->
word_mem segs mem (sp + 48) fimg -> 4096 <= fimg -> fimg + N <= alloc_ceiling ->
getr regs 25 = Z_to_bv 64 i -> 0 <= i < N -> getr regs 26 = Z_to_bv 64 N -> getr regs 27 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) ->
(if last then i + 1 = N else i + 1 <> N) ->
word_mem segs mem (sp + 96) fmtv -> word_mem segs mem (sp + 104) bfv -> 0 <= fmtv < 2 ^ 64 -> 0 <= bfv < 2 ^ 64 ->
getr regs 22 = Z_to_bv 64 a22 -> getr regs 24 = Z_to_bv 64 a24 ->
(forall regs' mem',
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
(forall x, 0 <= x < 2 ^ 64 -> x <> fimg + i -> mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 25 = Z_to_bv 64 (i + 1) -> getr regs' 22 = Z_to_bv 64 (a22 + fmtv) -> getr regs' 24 = Z_to_bv 64 (a24 + bfv) ->
(forall r : reg, In r SB_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (mkst regs' (Z_to_bv 64 (if last then PC_EX else PC_SL)) mem' rom) md) Q) ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 PC_SB) mem rom) md) Q.
Proof using API IMG.
intros last regs mem STK sp0 FP L A mem0 md0 Lc Ac md sp fimg i N a22 a24 fmtv bfv Q HJ Hwb Hwa Hr2 Hsplo Hsphi Hal16
V48 Hf0 Hf1 Hr25 Hi Hr26 Hr27 Hlast V96 V104 Hfv Hbv Hr22 Hr24 HK.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [fimg; fmtv; bfv; fimg + i] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; apply (Ereg_vals regs [fimg; fmtv; bfv; fimg + i] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 fmtv) by (subst E; apply (Ereg_vals regs [fimg; fmtv; bfv; fimg + i] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 bfv) by (subst E; apply (Ereg_vals regs [fimg; fmtv; bfv; fimg + i] [] 2%nat); reflexivity).
assert (A35 : ew E 35 = Z_to_bv 64 (fimg + i)) by (subst E; apply (Ereg_vals regs [fimg; fmtv; bfv; fimg + i] [] 3%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU25 : bv_unsigned (ew E 25) = i) by (rewrite (HE 25%nat 25%bv eq_refl), Hr25; apply unsigned_lit_small; lia).
assert (HU26 : bv_unsigned (ew E 26) = N) by (rewrite (HE 26%nat 26%bv eq_refl), Hr26; apply unsigned_lit_small; lia).
assert (HU27 : bv_unsigned (ew E 27) = 2 ^ 64 - 1 - fimg) by (rewrite (HE 27%nat 27%bv eq_refl), Hr27; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = fimg) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = fmtv) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = bfv) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HU35 : bv_unsigned (ew E 35) = fimg + i) by (rewrite A35; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E (ss_SB (sb_cond last)) (mkst regs (Z_to_bv 64 PC_SB) mem rom)).
{ unfold ss_SB. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- destruct last; vm_compute; reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU35.
split; [lia|]. split; [lia|]. split; [| apply Forall_nil]. intros o Ho. replace (fimg + i + o) with (fimg + i) by lia. exact Hwa.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V48].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V96].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V104].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU35. repeat split; lia.
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU35.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_conds conds_ok]. split; [|split; [|exact I]].
* unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, !U_SOff, HU27, HU25, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; lia). apply Bool.negb_true_iff, Z.ltb_ge. lia.
* unfold acond_ok, sb_cond. cbn [ac_c ac_a ac_b]. destruct last.
-- rewrite branch_eq_U, !U_SOff, HU26, HU25, Z.add_0_r. rewrite !zcanon_id by (unfold M64; lia). apply Z.eqb_eq. lia.
-- rewrite branch_ne_U, !U_SOff, HU26, HU25, Z.add_0_r. rewrite !zcanon_id by (unfold M64; lia). destruct (Z.eqb_spec N (i + 1)); [lia | reflexivity].
+ cbn [f_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite (U_atom _ 35 (fimg + i) A35) by lia.
apply (smj_U_add_atom _ 32 fimg _ i); [exact A32 | lia | apply (U_atom _ 25 i); [rewrite (HE 25%nat 25%bv eq_refl); exact Hr25 | lia] | lia | lia]. }
change mem with (ms_mem (mkst regs (Z_to_bv 64 PC_SB) mem rom)) in HJ.
destruct last.
- jrun_to LAWS ubs2tbl_ok HS HJ PC_EX.
{ wr_ok_eval. eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 35); [reflexivity | exact HU35 | cbn [r_wlo r_whi]; intros x Hx; replace x with (fimg + i) by lia; exact Hwb |].
apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
apply HK.
+ exact HJ.
+ intros x Hx Hne. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2, ?HU35; lia). reflexivity.
+ jreg HS (25%bv:reg) as Hq. rewrite Hq, HU25. reflexivity.
+ jreg HS (22%bv:reg) as Hq. rewrite Hq. cbn [alu64]. rewrite (HE 22%nat 22%bv eq_refl), Hr22, A33. apply lit_add.
+ jreg HS (24%bv:reg) as Hq. rewrite Hq. cbn [alu64]. rewrite (HE 24%nat 24%bv eq_refl), Hr24, A34. apply lit_add.
+ exact (regs_kept_of_st_ok _ _ _ _ regs _ SB_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
- jrun_to LAWS ubs2tbl_ok HS HJ PC_SL.
{ wr_ok_eval. eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 35); [reflexivity | exact HU35 | cbn [r_wlo r_whi]; intros x Hx; replace x with (fimg + i) by lia; exact Hwb |].
apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
apply HK.
+ exact HJ.
+ intros x Hx Hne. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2, ?HU35; lia). reflexivity.
+ jreg HS (25%bv:reg) as Hq. rewrite Hq, HU25. reflexivity.
+ jreg HS (22%bv:reg) as Hq. rewrite Hq. cbn [alu64]. rewrite (HE 22%nat 22%bv eq_refl), Hr22, A33. apply lit_add.
+ jreg HS (24%bv:reg) as Hq. rewrite Hq. cbn [alu64]. rewrite (HE 24%nat 24%bv eq_refl), Hr24, A34. apply lit_add.
+ exact (regs_kept_of_st_ok _ _ _ _ regs _ SB_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_A2z (c : acond) : sstate :=
mkSS PC_A2 (sr_set sr_atoms 10%bv (SLit 0))
[ YQ0b.mkRegion (Some 35%nat) 0 1 0 1 [];
  YQ0b.mkRegion (Some 2%nat) 48 128 0 0 [mkChunk 48 (CVal 8 (SOff 32 0)); mkChunk 80 (CVal 8 (SOff 36 0)); mkChunk 96 (CVal 8 (SOff 33 0));
  mkChunk 104 (CVal 8 (SOff 34 0)); mkChunk 112 (CVal 8 (SOff 37 0)); mkChunk 120 (CVal 8 (SOff 38 0))] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (35%nat, mkAF 4096 (2^48) 0) ]
 [mkAC BC_GEU (SOff 27 0) (SOff 25 0); c]
 [(SAlu ALU_ADD (SOff 32 0) (SOff 25 0), SOff 35 0)]).
Lemma A2z_stretch : forall (last : bool) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (sp fimg i N a22 a24 fmtv bfv img fmt v80 : Z) Q,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) (fimg + i) -> writable_at segs mem (fimg + i) ->
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5168 <= 2 ^ 63 -> sp mod 16 = 0 ->
getr regs 10 = Z_to_bv 64 0 ->
word_mem segs mem (sp + 48) fimg -> 4096 <= fimg -> fimg + N <= alloc_ceiling ->
getr regs 25 = Z_to_bv 64 i -> 0 <= i < N -> getr regs 26 = Z_to_bv 64 N -> getr regs 27 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) ->
(if last then i + 1 = N else i + 1 <> N) ->
word_mem segs mem (sp + 96) fmtv -> word_mem segs mem (sp + 104) bfv -> 0 <= fmtv < 2 ^ 64 -> 0 <= bfv < 2 ^ 64 ->
getr regs 22 = Z_to_bv 64 a22 -> getr regs 24 = Z_to_bv 64 a24 ->
word_mem segs mem (sp + 80) v80 -> word_mem segs mem (sp + 112) img -> word_mem segs mem (sp + 120) fmt ->
0 <= v80 < 2 ^ 64 -> 0 <= img < 2 ^ 64 -> 0 <= fmt < 2 ^ 64 ->
(forall regs' mem',
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
(forall x, 0 <= x < 2 ^ 64 -> x <> fimg + i -> mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 25 = Z_to_bv 64 (i + 1) -> getr regs' 22 = Z_to_bv 64 (a22 + fmtv) -> getr regs' 24 = Z_to_bv 64 (a24 + bfv) ->
getr regs' 15 = Z_to_bv 64 img -> getr regs' 14 = Z_to_bv 64 fmt ->
(forall r : reg, In r smj_A2Z_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (mkst regs' (Z_to_bv 64 (if last then PC_EX else PC_SL)) mem' rom) md) Q) ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 PC_A2) mem rom) md) Q.
Proof using API IMG.
intros last regs mem STK sp0 FP L A mem0 md0 Lc Ac md sp fimg i N a22 a24 fmtv bfv img fmt v80 Q HJ Hwb Hwa Hr2 Hsplo Hsphi Hal16 Hr10
V48 Hf0 Hf1 Hr25 Hi Hr26 Hr27 Hlast V96 V104 Hfv Hbv Hr22 Hr24 V80 V112 V120 Hv80 Himg Hfmt HK.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (vals := [fimg; fmtv; bfv; fimg + i; v80; img; fmt]).
set (E := Ereg regs (map (Z_to_bv 64) vals ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall jj v, nth_error vals jj = Some v -> ew E (32 + jj) = Z_to_bv 64 v) by (intros jj v Hjv; subst E; apply Ereg_vals; exact Hjv).
assert (A32 : ew E 32 = Z_to_bv 64 fimg) by exact (HV 0%nat _ eq_refl).
assert (A33 : ew E 33 = Z_to_bv 64 fmtv) by exact (HV 1%nat _ eq_refl).
assert (A34 : ew E 34 = Z_to_bv 64 bfv) by exact (HV 2%nat _ eq_refl).
assert (A35 : ew E 35 = Z_to_bv 64 (fimg + i)) by exact (HV 3%nat _ eq_refl).
assert (A36 : ew E 36 = Z_to_bv 64 v80) by exact (HV 4%nat _ eq_refl).
assert (A37 : ew E 37 = Z_to_bv 64 img) by exact (HV 5%nat _ eq_refl).
assert (A38 : ew E 38 = Z_to_bv 64 fmt) by exact (HV 6%nat _ eq_refl).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU25 : bv_unsigned (ew E 25) = i) by (rewrite (HE 25%nat 25%bv eq_refl), Hr25; apply unsigned_lit_small; lia).
assert (HU26 : bv_unsigned (ew E 26) = N) by (rewrite (HE 26%nat 26%bv eq_refl), Hr26; apply unsigned_lit_small; lia).
assert (HU27 : bv_unsigned (ew E 27) = 2 ^ 64 - 1 - fimg) by (rewrite (HE 27%nat 27%bv eq_refl), Hr27; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = fimg) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = fmtv) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = bfv) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HU35 : bv_unsigned (ew E 35) = fimg + i) by (rewrite A35; apply unsigned_lit_small; lia).
assert (HU36 : bv_unsigned (ew E 36) = v80) by (rewrite A36; apply unsigned_lit_small; lia).
assert (HU37 : bv_unsigned (ew E 37) = img) by (rewrite A37; apply unsigned_lit_small; lia).
assert (HU38 : bv_unsigned (ew E 38) = fmt) by (rewrite A38; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E (ss_A2z (sb_cond last)) (mkst regs (Z_to_bv 64 PC_A2) mem rom)).
{ unfold ss_A2z. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite Hr10; reflexivity].
- destruct last; vm_compute; reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU35.
split; [lia|]. split; [lia|]. split; [| apply Forall_nil]. intros o Ho. replace (fimg + i + o) with (fimg + i) by lia. exact Hwa.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V48].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU36; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V80].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V96].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V104].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU37; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V112].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU38; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V120].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU35. repeat split; lia.
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU35.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_conds conds_ok]. split; [|split; [|exact I]].
* unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, !U_SOff, HU27, HU25, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; lia). apply Bool.negb_true_iff, Z.ltb_ge. lia.
* unfold acond_ok, sb_cond. cbn [ac_c ac_a ac_b]. destruct last.
-- rewrite branch_eq_U, !U_SOff, HU26, HU25, Z.add_0_r. rewrite !zcanon_id by (unfold M64; lia). apply Z.eqb_eq. lia.
-- rewrite branch_ne_U, !U_SOff, HU26, HU25, Z.add_0_r. rewrite !zcanon_id by (unfold M64; lia). destruct (Z.eqb_spec N (i + 1)); [lia | reflexivity].
+ cbn [f_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite (U_atom _ 35 (fimg + i) A35) by lia.
apply (smj_U_add_atom _ 32 fimg _ i); [exact A32 | lia | apply (U_atom _ 25 i); [rewrite (HE 25%nat 25%bv eq_refl); exact Hr25 | lia] | lia | lia]. }
change mem with (ms_mem (mkst regs (Z_to_bv 64 PC_A2) mem rom)) in HJ.
clear HV.
destruct last.
- jrun_to LAWS ubs2tbl_ok HS HJ PC_EX.
{ wr_ok_eval. eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 35); [reflexivity | exact HU35 | cbn [r_wlo r_whi]; intros x Hx; replace x with (fimg + i) by lia; exact Hwb |].
apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
apply HK.
+ exact HJ.
+ intros x Hx Hne. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2, ?HU35; lia). reflexivity.
+ jreg HS (25%bv:reg) as Hq. rewrite Hq, HU25. reflexivity.
+ jreg HS (22%bv:reg) as Hq. rewrite Hq. cbn [alu64]. rewrite (HE 22%nat 22%bv eq_refl), Hr22, A33. apply lit_add.
+ jreg HS (24%bv:reg) as Hq. rewrite Hq. cbn [alu64]. rewrite (HE 24%nat 24%bv eq_refl), Hr24, A34. apply lit_add.
+ jreg HS (15%bv:reg) as Hq. rewrite Hq. exact A37.
+ jreg HS (14%bv:reg) as Hq. rewrite Hq. exact A38.
+ exact (regs_kept_of_st_ok _ _ _ _ regs _ smj_A2Z_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
- jrun_to LAWS ubs2tbl_ok HS HJ PC_SL.
{ wr_ok_eval. eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 35); [reflexivity | exact HU35 | cbn [r_wlo r_whi]; intros x Hx; replace x with (fimg + i) by lia; exact Hwb |].
apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
apply HK.
+ exact HJ.
+ intros x Hx Hne. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2, ?HU35; lia). reflexivity.
+ jreg HS (25%bv:reg) as Hq. rewrite Hq, HU25. reflexivity.
+ jreg HS (22%bv:reg) as Hq. rewrite Hq. cbn [alu64]. rewrite (HE 22%nat 22%bv eq_refl), Hr22, A33. apply lit_add.
+ jreg HS (24%bv:reg) as Hq. rewrite Hq. cbn [alu64]. rewrite (HE 24%nat 24%bv eq_refl), Hr24, A34. apply lit_add.
+ jreg HS (15%bv:reg) as Hq. rewrite Hq. exact A37.
+ jreg HS (14%bv:reg) as Hq. rewrite Hq. exact A38.
+ exact (regs_kept_of_st_ok _ _ _ _ regs _ smj_A2Z_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
End J.
End d.
