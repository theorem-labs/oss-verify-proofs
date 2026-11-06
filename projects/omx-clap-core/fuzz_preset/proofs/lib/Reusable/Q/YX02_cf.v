From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN1y_cf YN1p_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN03 YN02_cf YN2b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN0b_cf YN07_cf YN0a_cf YN1q_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.Q Require Import YW0e_cf YX00_cf YX01_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import AllocRealloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM06_cf YO0d_cf YN2b_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition t0r_env (k : Z) : list (nat * Z) :=
[(aKR, k); (aER, t0_e k); (aPR, 2 ^ t0_e k); (aTQ1R, DEBR + dbj_idx (2 ^ t0_e k)); (aT1R, t0_t1 k);
(aTQ2R, SCTR + 2 * (4 * t0_e k - 3)); (aT2R, znth (t0_i3 k) size_classes); (aTQ3R, SCTR + 2 * t0_i3 k)].
Definition t0r_chk (k : Z) : bool :=
let l := t0r_env k in let e := t0_e k in
(UZof l ANDXR =? 2 ^ e) && (UZof l TQ1XR =? DEBR + dbj_idx (2 ^ e)) && (UZof l TQ2XR =? SCTR + 2 * (4 * e - 3))
&& (UZof l (TQ3XR (t0_b1 k)) =? SCTR + 2 * t0_i3 k) && (UZof l (RESXR (t0_b1 k)) =? class_of_units k).
Lemma t0r_chk_all : forallb t0r_chk (zseq 10 8181) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma t0r_chk_sound k : t0r_chk k = true ->
UZof (t0r_env k) ANDXR = 2 ^ t0_e k /\ UZof (t0r_env k) TQ1XR = DEBR + dbj_idx (2 ^ t0_e k) /\
UZof (t0r_env k) TQ2XR = SCTR + 2 * (4 * t0_e k - 3) /\ UZof (t0r_env k) (TQ3XR (t0_b1 k)) = SCTR + 2 * t0_i3 k /\
UZof (t0r_env k) (RESXR (t0_b1 k)) = class_of_units k.
Proof.
unfold t0r_chk. cbv zeta. intros C.
apply andb_prop in C as [C C5]. apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
apply Z.eqb_eq in C1. apply Z.eqb_eq in C2. apply Z.eqb_eq in C3. apply Z.eqb_eq in C4. apply Z.eqb_eq in C5.
split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. exact C5.
Qed.
Lemma t0r_facts k : 10 <= k <= 8190 ->
UZof (t0r_env k) ANDXR = 2 ^ t0_e k /\ UZof (t0r_env k) TQ1XR = DEBR + dbj_idx (2 ^ t0_e k) /\
UZof (t0r_env k) TQ2XR = SCTR + 2 * (4 * t0_e k - 3) /\ UZof (t0r_env k) (TQ3XR (t0_b1 k)) = SCTR + 2 * t0_i3 k /\
UZof (t0r_env k) (RESXR (t0_b1 k)) = class_of_units k.
Proof. intros Hk. apply t0r_chk_sound. exact (proj1 (forallb_zseq_iff t0r_chk 10 8181) t0r_chk_all k ltac:(lia)). Qed.
Lemma stc_kk m : size_to_class m = class_of_units ((m + 3) / 16).
Proof. unfold size_to_class, IB. rewrite Z.shiftr_div_pow2 by lia. replace (m + 4 - 1) with (m + 3) by lia. reflexivity. Qed.
Lemma af0 E k lo hi : lo <= bv_unsigned (ew E k) <= hi -> afact_ok E k (mkAF lo hi 0).
Proof. intros H. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. Qed.
Lemma af1 E k lo hi : lo <= bv_unsigned (ew E k) <= hi -> bv_unsigned (ew E k) mod 2 = 0 -> afact_ok E k (mkAF lo hi 1).
Proof. intros H H2. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (2 ^ 1) with 2. lia. Qed.
Lemma alias_kR xv : (forall k, 0 <= xv k < 2 ^ 64) -> 0 <= xv 11%nat < MMAP_THRESHOLD -> xv aKR = (xv 11%nat + 3) / 16 ->
sv_denot (EV xv) (SAlu ALU_SRL (SOff 11 3) (SLit 4)) = sv_denot (EV xv) (SOff aKR 0).
Proof.
intros XR Hn Xk. rewrite !UZ_sound. f_equal. cbn [UZ]. rewrite Xk. unfold MMAP_THRESHOLD in Hn.
set (m := xv 11%nat) in *. set (q := (m + 3) / 16).
assert (K : 0 <= q < 8191) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold zalu64. cbn [zalu_raw].
rewrite !(zcanon_id m), !(zcanon_id 4), !(zcanon_id (m + 3)), !(zcanon_id q), Z.add_0_r, (zcanon_id q) by (unfold M64; lia).
change (Z.land 4 63) with 4. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. fold q. apply zcanon_id. unfold M64. lia.
Qed.
Lemma cGE_ok xv : (forall k, 0 <= xv k < 2 ^ 64) -> xv aN <= xv aEP -> acond_ok (EV xv) cGE.
Proof. intros XR H. unfold acond_ok, cGE. cbn [ac_c ac_a ac_b]. rewrite !(den_off0 xv XR), bt_geu by apply XR. apply negb_true_iff, Z.ltb_ge. exact H. Qed.
Lemma cLT_ok xv : (forall k, 0 <= xv k < 2 ^ 64) -> xv aEP < xv aN -> acond_ok (EV xv) cLT.
Proof. intros XR H. unfold acond_ok, cLT. cbn [ac_c ac_a ac_b]. rewrite !(den_off0 xv XR), bt_ltu by apply XR. apply Z.ltb_lt. exact H. Qed.
Lemma cb1_ok xv : (forall k, 0 <= xv k < 2 ^ 64) -> acond_ok (EV xv) (C_b1R (xv aKR <? xv aT1R)).
Proof.
intros XR. unfold acond_ok, C_b1R. destruct (xv aKR <? xv aT1R) eqn:Eb; cbn [ac_c ac_a ac_b]; rewrite !(den_off0 xv XR).
- rewrite bt_ltu by apply XR. exact Eb.
- rewrite bt_geu by apply XR. rewrite Eb. reflexivity.
Qed.
Lemma cCL_ok xv c ge cl sc : (forall k, 0 <= xv k < 2 ^ 64) -> xv c = cl -> xv aSC = sc -> 0 <= cl < 48 -> 0 <= sc < 48 ->
ge = (sc <=? cl + 1) -> acond_ok (EV xv) (cCL c ge).
Proof.
intros XR Xc Xs Hc Hs ->. unfold acond_ok, cCL. cbn [ac_c ac_a ac_b].
rewrite (den_off xv XR c 1) by lia. rewrite (den_off0 xv XR aSC), Xc, Xs.
destruct (sc <=? cl + 1) eqn:Eg.
- rewrite branch_ge, !lit64_small, !s64_small by lia. apply Z.leb_le in Eg. apply negb_true_iff, Z.ltb_ge. lia.
- rewrite branch_lt, !lit64_small, !s64_small by lia. apply Z.leb_gt in Eg. apply Z.ltb_lt. lia.
Qed.
Section b.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (idx : Z) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : small_ctx L A regs mem md g am idx fr n a ka rg.
Local Abbreviation XV := (xvS L regs g am idx fr a rg n).
Lemma XS_EP : XV aEP = avail_of am fr.
Proof using HC.
transitivity (ptr_addr L (slot_end am idx) - XV aP); [reflexivity|].
rewrite (XS_P L A regs mem md g am idx fr n a ka rg HC). unfold slot_end, frame_ptr, slot_start, avail_of. rewrite !ptr_addr_padd'. lia.
Qed.
Theorem nc_facts_ok nc : nc_ok am fr n nc -> facts_ok (ES L regs g am idx fr a rg n) (nc_facts nc).
Proof using fx HC.
intros H. pose proof (XS L A regs mem md g am idx fr n a ka rg HC) as XR.
pose proof (XS_N L A regs mem md g am idx fr n a ka rg HC) as XN.
pose proof XS_EP as XE.
pose proof (sx_n _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hn.
pose proof (sx_sc _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hsc.
assert (XSC : XV aSC = am_sc am) by reflexivity.
assert (Hsc0 : 0 <= am_sc am) by (rewrite <- XSC; apply XR).
assert (X11 : XV 11%nat = n) by exact XN.
unfold ES, facts_ok, nc_facts. cbn [f_atoms f_conds f_alias].
destruct nc as [| |ge|b1 ge]; cbn [nc_ok] in H; cbn [nc_atoms nc_conds nc_alias atoms_ok conds_ok alias_ok AL_kR].
- exact (conj I (conj I I)).
- destruct H as [H1 H2]. split; [exact I|]. split; [split; [apply cLT_ok; [exact XR | rewrite XN, XE; exact H2] | exact I] | exact I].
- destruct H as (Hs & Hav & Hge).
assert (Hm : n < MMAP_THRESHOLD) by (unfold MMAP_THRESHOLD; lia).
assert (Hk10 : (n + 3) / 16 < 10) by (apply Z.div_lt_upper_bound; lia).
assert (Hk0 : 0 <= (n + 3) / 16) by (apply Z.div_pos; lia).
assert (XK : XV aKR = (n + 3) / 16).
{ change (XV aKR) with ((nS n + 3) / 16). unfold nS. rewrite (proj2 (Z.ltb_lt _ _) Hm). reflexivity. }
assert (Hcl : size_to_class n = (n + 3) / 16).
{ rewrite stc_kk. unfold class_of_units. rewrite (proj2 (Z.ltb_lt _ _) Hk10). reflexivity. }
split; [split; [apply af0; rewrite (ew_EV _ XR), XK; lia | exact I]|].
split; [split; [apply cGE_ok; [exact XR | rewrite XN, XE; exact Hav] | split; [|exact I]] | split; [|exact I]].
+ apply (cCL_ok _ aKR ge ((n + 3) / 16) (am_sc am) XR XK XSC); [lia | lia | rewrite <- Hcl; exact Hge].
+ apply alias_kR; [exact XR | rewrite X11; lia | rewrite X11; exact XK].
- destruct H as ((Hlo & Hhi) & Hav & Hb1 & Hge).
assert (Hns : nS n = n) by (unfold nS; rewrite (proj2 (Z.ltb_lt _ _) Hhi); reflexivity).
set (k := kkS n) in *.
assert (Kq : k = (n + 3) / 16) by (unfold k, kkS; rewrite Hns; reflexivity).
assert (Kk : 10 <= k <= 8190).
{ rewrite Kq. unfold MMAP_THRESHOLD in Hhi. split; [apply Z.div_le_lower_bound; lia|].
assert ((n + 3) / 16 < 8191) by (apply Z.div_lt_upper_bound; lia). lia. }
pose proof (t0r_facts k Kk) as (F1 & F2 & F3 & F4 & F5).
pose proof (t0_facts k Kk) as (_ & _ & _ & _ & _ & He & _).
assert (Hcl : size_to_class n = class_of_units k) by (rewrite stc_kk, <- Kq; reflexivity).
pose proof (proj1 (size_to_class_range n ltac:(lia))) as Hcr. rewrite Hcl in Hcr.
assert (Henv : forall p, In p (t0r_env k) -> XV (fst p) = snd p).
{ intros p Hp. unfold t0r_env in Hp. cbn [In] in Hp. decompose [or] Hp; try contradiction; subst p; reflexivity. }
assert (XK : XV aKR = k) by reflexivity.
assert (XEr : XV aER = t0_e k) by reflexivity.
assert (XP : XV aPR = 2 ^ t0_e k) by reflexivity.
assert (XQ1 : XV aTQ1R = DEBR + dbj_idx (2 ^ t0_e k)) by reflexivity.
assert (XT1 : XV aT1R = t0_t1 k) by reflexivity.
assert (XQ2 : XV aTQ2R = SCTR + 2 * (4 * t0_e k - 3)) by reflexivity.
assert (XT2 : XV aT2R = znth (t0_i3 k) size_classes) by reflexivity.
assert (XQ3 : XV aTQ3R = SCTR + 2 * t0_i3 k) by reflexivity.
assert (XCL : XV aCL = class_of_units k).
{ change (XV aCL) with (size_to_class (nS n)). rewrite Hns. exact Hcl. }
assert (Pe : 8 <= 2 ^ t0_e k <= 4096).
{ split; [change 8 with (2 ^ 3); apply Z.pow_le_mono_r; lia | change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia]. }
pose proof (dbj_idx_range (2 ^ t0_e k)) as Kd.
pose proof (znth_sc_range (4 * t0_e k - 3)) as Kt1.
pose proof (znth_sc_range (t0_i3 k)) as Kt2.
assert (Ki3 : 8 <= t0_i3 k <= 46) by (unfold t0_i3; destruct (t0_b1 k); lia).
assert (Sev : forall x, (SCTR + 2 * x) mod 2 = 0).
{ intros x. rewrite (Z.mul_comm 2 x), Z_mod_plus_full. unfold SCTR, src0_D_size_classes. reflexivity. }
split.
{ split; [apply af0; rewrite (ew_EV _ XR), XK; lia|].
split; [apply af0; rewrite (ew_EV _ XR), XEr; lia|].
split; [apply af0; rewrite (ew_EV _ XR), XP; lia|].
split; [apply af0; rewrite (ew_EV _ XR), XQ1; lia|].
split; [apply af0; rewrite (ew_EV _ XR), XT1; unfold t0_t1; lia|].
split; [apply af1; rewrite (ew_EV _ XR), XQ2; [lia | apply Sev]|].
split; [apply af0; rewrite (ew_EV _ XR), XT2; lia|].
split; [apply af1; rewrite (ew_EV _ XR), XQ3; [lia | apply Sev]|].
split; [apply af0; rewrite (ew_EV _ XR), XCL; lia | exact I]. }
split.
{ split; [apply cGE_ok; [exact XR | rewrite XN, XE; exact Hav]|].
split; [subst b1; exact (cb1_ok _ XR)|].
split; [|exact I].
apply (cCL_ok _ aCL ge (class_of_units k) (am_sc am) XR XCL XSC); [lia | lia | rewrite <- Hcl; exact Hge]. }
split; [apply alias_kR; [exact XR | rewrite X11; lia | rewrite X11, XK; exact Kq]|].
split; [rewrite (UZ_by_atoms (t0r_env k) XV ANDXR eq_refl Henv), F1, (den_off0 _ XR), XP; reflexivity|].
split; [rewrite (UZ_by_atoms (t0r_env k) XV TQ1XR eq_refl Henv), F2, (den_off0 _ XR), XQ1; reflexivity|].
split; [rewrite (UZ_by_atoms (t0r_env k) XV TQ2XR eq_refl Henv), F3, (den_off0 _ XR), XQ2; reflexivity|].
subst b1.
split; [rewrite (UZ_by_atoms (t0r_env k) XV (TQ3XR (t0_b1 k))), F4, (den_off0 _ XR), XQ3; [reflexivity | destruct (t0_b1 k); reflexivity | exact Henv]|].
split; [rewrite (UZ_by_atoms (t0r_env k) XV (RESXR (t0_b1 k))), F5, (den_off0 _ XR), XCL; [reflexivity | destruct (t0_b1 k); reflexivity | exact Henv] | exact I].
Qed.
End b.
End a.
