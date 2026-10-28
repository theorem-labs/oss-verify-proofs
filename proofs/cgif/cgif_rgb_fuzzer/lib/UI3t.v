(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p YK1j.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI07
UI1e UI1i UI57 YI0x YP14 YI08 YI0c YI0g YI0f YI0d YI0e
UI3h UI4v UIZm UI4w UI3s YP12.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06 YM02 YI0a.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Lemma U_mul_lit : forall E n c i,
ew E n = Z_to_bv 64 i -> 0 <= i < 2 ^ 32 -> 0 <= c < 2 ^ 16 ->
sv_denot E (SMd M_MUL (SLit c) (SOff n 0)) = Z_to_bv 64 (c * i).
Proof.
intros E n c i Hn Hi Hc. rewrite denot_lit_U. f_equal.
rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit. rewrite (U_atom E n i Hn) by lia.
rewrite (zcanon_id c) by (unfold M64; lia). apply zcanon_id. unfold M64; nia.
Qed.
Lemma U_add_shl2 : forall E n m b x,
bv_unsigned (ew E m) = b -> bv_unsigned (ew E n) = x -> 0 <= b -> 0 <= x < 2 ^ 32 -> b + x * 4 < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 2)) (SOff m 0)) = Z_to_bv 64 (b + x * 4).
Proof.
intros E n m b x Hm Hn Hb Hx Hbx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, Hm, Hn, !Z.add_0_r.
rewrite (zcanon_id b), (zcanon_id x) by (unfold M64; lia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id (x * 4)) by (unfold M64; nia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma val_mem4_of_present : forall segs (m : word -> option byte) a,
(forall i, 0 <= i < 4 -> exists b, mbyte segs m (a + i) = Some b) ->
exists v, 0 <= v < 2 ^ 32 /\ val_mem segs m a 4 v.
Proof.
intros segs m a Hp.
destruct (Hp 0 ltac:(lia)) as [b0 M0]. destruct (Hp 1 ltac:(lia)) as [b1 M1].
destruct (Hp 2 ltac:(lia)) as [b2 M2]. destruct (Hp 3 ltac:(lia)) as [b3 M3].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
unfold bv_modulus in R0, R1, R2, R3. cbn [Z.of_N] in R0, R1, R2, R3. change (2 ^ 8) with 256 in R0, R1, R2, R3.
set (v := bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))).
exists v. split; [subst v; lia|].
assert (BY : forall (k : nat) (c : byte) (lo hi : Z),
v = lo + 2 ^ (8 * Z.of_nat k) * (bv_unsigned c + 256 * hi) -> 0 <= lo < 2 ^ (8 * Z.of_nat k) -> 0 <= hi ->
Z_to_bv 8 (YP0g.le_byte v 4 k) = c).
{ intros k c lo hi Hdec Hlo Hhi. unfold YP0g.le_byte. rewrite (Z.mod_small v) by (cbn; subst v; lia).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (bv_unsigned_in_range 8 c) as Hc. unfold bv_modulus in Hc. cbn [Z.of_N] in Hc. change (2 ^ 8) with 256 in Hc.
replace (v / 2 ^ (8 * Z.of_nat k)) with (bv_unsigned c + 256 * hi).
2:{ apply Z.div_unique with (r := lo); [left; lia | lia]. }
replace ((bv_unsigned c + 256 * hi) mod 256) with (bv_unsigned c).
2:{ apply Z.mod_unique with (q := hi); [left; lia | lia]. }
apply Z_to_bv_bv_unsigned. }
intros k Hk.
destruct k as [|[|[|[|k]]]]; [| | | |lia];
[ change (a + Z.of_nat 0) with (a + 0) | change (Z.of_nat 1) with 1 | change (Z.of_nat 2) with 2 | change (Z.of_nat 3) with 3 ].
- rewrite M0. f_equal. symmetry. apply (BY 0%nat b0 0 (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))); cbn; subst v; lia.
- rewrite M1. f_equal. symmetry. apply (BY 1%nat b1 (bv_unsigned b0) (bv_unsigned b2 + 256 * bv_unsigned b3)); cbn; subst v; lia.
- rewrite M2. f_equal. symmetry. apply (BY 2%nat b2 (bv_unsigned b0 + 256 * bv_unsigned b1) (bv_unsigned b3)); cbn; subst v; lia.
- rewrite M3. f_equal. symmetry. apply (BY 3%nat b3 (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)) 0); cbn; subst v; lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation BASEv := (BASE r g N img fmt rest s bef beffmt).
Local Notation FPv := (FPfoot r g bef beffmt s N).
Local Notation spv := (sp regs0).
Local Notation sp0v := (sp0 regs0).
Section l.
Variables (Lq : layout) (Aq : astate) (mdq : Model) (memD : word -> option byte).
Variables (flt fimg : Z) (t : tree).
Let M : Z := fmt * N.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN1 : 1 <= N. Hypothesis HNmax : N <= RGB_NMAX.
Hypothesis HW1 : 1 <= W. Hypothesis HWN : exists h, 1 <= h /\ N = W * h.
Hypothesis Hceil : alloc_ceiling + RGBA_STK <= sp0v. Hypothesis H63 : sp0v < 2 ^ 63. Hypothesis Hal0 : sp0v mod 16 = 0.
Hypothesis Hflt0 : 4096 <= flt. Hypothesis Hflt1 : flt + 4 * M <= alloc_ceiling. Hypothesis Hflt16 : flt mod 16 = 0.
Hypothesis Hfimg0 : 4096 <= fimg. Hypothesis Hfimg1 : fimg + N <= alloc_ceiling.
Hypothesis Hdisj : flt + 4 * M <= fimg \/ fimg + N <= flt.
Hypothesis Hfin : In (flt, 4 * M) (blocks Lq Aq). Hypothesis Hgin : In (fimg, N) (blocks Lq Aq).
Hypothesis Hwbf : forall i, 0 <= i < 4 * M -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) (flt + i).
Hypothesis Hwbg : forall i, 0 <= i < N -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) (fimg + i).
Hypothesis Hs48 : slot regs0 memD 48 fimg. Hypothesis Hs80 : slot regs0 memD 80 (troot t).
Hypothesis Hs112 : slot regs0 memD 112 (2 ^ 64 - 1 - fimg).
Hypothesis Htroot : 4096 <= troot t /\ troot t + NODE_SIZE <= alloc_ceiling /\ troot t mod 16 = 0.
Local Notation memIv := (memI N fmt memD flt fimg).
Lemma di_consts : RGBA_STK = 24576 /\ 934 <= RGBA_FRAME <= 8192 /\ RGBA_FRAME mod 16 = 0 /\ RGB_NMAX = 10000 /\ NODE_SIZE = 56 /\
  (CEIL_MIN <= alloc_ceiling <= CEIL_MAX).
Proof. repeat match goal with H : _ |- _ => clear H end. pose proof (proj1 alloc_ceiling_val). repeat split; first [reflexivity | unfold RGBA_FRAME; lia | lia]. Qed.
Lemma sp_facts : alloc_ceiling + 16384 <= spv /\ spv + 934 <= 2 ^ 63 /\ spv mod 16 = 0.
Proof.
pose proof di_consts as (HRv & HF1 & HF16 & _ & _ & Hac). unfold sp, sp0 in *.
split; [lia|]. split; [lia|]. rewrite Zminus_mod, Hal0, HF16. reflexivity.
Qed.
Lemma slot_now : forall m off v, memIv m -> 0 <= off -> off + 8 <= 160 -> slot regs0 memD off v -> slot regs0 m off v.
Proof.
intros m off v HMI Ho1 Ho2 Hs k Hk. pose proof sp_facts as (S1 & S2 & _). pose proof di_consts as (_ & _ & _ & _ & _ & Hac).
unfold slot, word_mem in Hs |- *. rewrite HMI; [apply Hs; exact Hk | lia | lia | lia].
Qed.
Lemma flt_present : forall m, journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall i, 0 <= i < 4 * M -> exists b, mbyte ubs2segs m (flt + i) = Some b.
Proof.
intros m HJ i Hi. apply mbyte_of_present.
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq flt (4 * M) i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfin Hi)).
Qed.
Lemma flt_writable : forall m, journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall a, flt <= a < flt + 4 * M -> writable_at ubs2segs m a.
Proof.
intros m HJ a Ha. replace a with (flt + (a - flt)) by lia. apply (present_writable ubs2_msyms).
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq flt (4 * M) (a - flt) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfin ltac:(lia))).
Qed.
Lemma fimg_writable : forall m, journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall a, fimg <= a < fimg + N -> writable_at ubs2segs m a.
Proof.
intros m HJ a Ha. replace a with (fimg + (a - fimg)) by lia. apply (present_writable ubs2_msyms).
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq fimg N (a - fimg) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hgin ltac:(lia))).
Qed.
Lemma Hf4 : flt mod 4 = 0.
Proof. pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd. rewrite Hflt16, Z.add_0_r in Hd. rewrite Hd.
replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia. apply Z_mod_mult. Qed.
Definition ss_H3 : sstate :=
mkSS PC_DIH (sr_set sr_atoms 7%bv (SLit 3)) [] None
(mkFacts [ (23%nat, mkAF 0 RGB_NMAX 0); (9%nat, mkAF 0 (2 ^ 20) 0) ] [] []).
Definition h4_frame : YQ0b.region :=
YQ0b.mkRegion (Some 2%nat) 0 160 0 0 [mkChunk 48 (CVal 8 (SOff 35 0)); mkChunk 112 (CVal 8 (SOff 34 0))].
Definition ss_H4x : sstate :=
mkSS PC_DIH (sr_set sr_atoms 7%bv (SLit 4))
[ h4_frame; YQ0b.mkRegion (Some 32%nat) 0 16 0 0 [mkChunk 0 (CData 0 0 16)]; YQ0b.mkRegion (Some 33%nat) 0 1 0 1 [] ] None
(mkFacts [ (23%nat, mkAF 0 RGB_NMAX 0); (9%nat, mkAF 0 (2 ^ 20) 0); (19%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0);
  (24%nat, mkAF 4096 CEIL_MAX 4); (2%nat, mkAF CEIL_MIN (2 ^ 63) 4); (32%nat, mkAF 4096 CEIL_MAX 4); (33%nat, mkAF 4096 CEIL_MAX 0);
  (34%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0); (35%nat, mkAF 4096 CEIL_MAX 0) ] []
[ (SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLL (SOff 23 0) (SLit 4)), SOff 32 0); (SAlu ALU_ADD (SOff 35 0) (SOff 23 0), SOff 33 0) ]).
Definition H_KEEP : list reg := [1; 2; 3; 4; 5; 6; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition H_FKEEP : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition H_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (i : Z) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem' (skip : bool),
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if skip then PC_IN else PC_CL)) mem' (seg_rom ubs2segs)) mdq /\
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\ frm_zero (@fp_csr fy') /\
(forall rr : reg, In rr H_KEEP -> getr regs' rr = getr regs rr) /\ getr regs' 7 = Z_to_bv 64 fmt /\
(forall rr : reg, In rr H_FKEEP -> reg_get (@fp_regs fy') rr = reg_get (@fp_regs fy) rr) /\
(forall a, 0 <= a < 2 ^ 64 -> a <> fimg + i -> mbyte ubs2segs mem' a = mbyte ubs2segs mem a) /\
(skip = false -> getr regs' 10 = Z_to_bv 64 (fmt * i) /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 (fmt * i)) /\
(skip = true -> getr regs' 11 = Z_to_bv 64 (i + 1)).
Lemma H_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> memIv mem ->
lregs regs0 W N fmt flt regs i -> getr regs 7 = Z_to_bv 64 fmt ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_DIH) mem (seg_rom ubs2segs)) mdq) (H_post fy regs mem i).
Proof.
intros fy regs mem i Hi HJ Hfrm HMI HL G7.
pose proof di_consts as (HRv & HF1 & HF16 & HNMv & HNSv & Hac). pose proof sp_facts as (S1 & S2 & S3).
destruct HL as (G2 & G23 & G9 & G19 & G21 & G22 & G25 & G26 & G27 & G24 & G18).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
destruct Hfmt as [F3 | F4].
- set (E := Ereg regs []).
  assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
  assert (U23 : bv_unsigned (ew E 23) = i) by (rewrite (HE 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = fmt * i) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; nia).
  assert (HS : @st_ok ubs2segs fy E ss_H3 (@mkst fy regs (Z_to_bv 64 PC_DIH) mem (seg_rom ubs2segs))).
  { unfold ss_H3. apply entry_st_ok_env.
    - apply regs_ok_pin; [subst E; apply regs_ok_Ereg | intros HH0; discriminate HH0 | cbn [sv_denot]; rewrite <- F3; exact G7].
    - vm_compute. reflexivity.
    - constructor.
    - cbn [pairwise_disjoint all_disjoint]. exact I.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23, U9.
      change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
  pure_to ubs2tbl_ok HS PC_CL.
  eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
  lazymatch goal with |- H_post _ _ _ _ (mkCfg (@mkst _ ?rg _ _ _) _) => rename rg into regs2 end.
  exists fy, regs2, mem, false. split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrm|].
  assert (RG : forall rr : reg, getr regs2 rr = sv_denot E (sr_get (ss_regs (fst (sym_run_toN ubs2segs ubs2tbl FUEL PC_CL ss_H3))) rr)) by (intros rr; exact (st_ok_reg ubs2segs E _ _ rr HS)).
  match type of RG with context [ss_regs (fst ?x)] => let v := eval vm_compute in (ss_regs (fst x)) in change (ss_regs (fst x)) with v in RG end.
  split; [exact (regs_kept_of_st_ok _ _ _ _ regs _ H_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity))|].
  split; [rewrite (RG 7%bv); eval_sr_get; cbn [sv_denot]; rewrite F3; reflexivity|].
  split; [intros; reflexivity|]. split; [intros; reflexivity|].
  split; [|intros HH0; discriminate HH0].
  intros _. split; [rewrite (RG 10%bv); eval_sr_get; rewrite (U_mul_lit E 23 3 i) by first [rewrite <- U23; symmetry; apply Z_to_bv_bv_unsigned | lia]; rewrite F3; reflexivity|].
  split; [rewrite (RG 11%bv); eval_sr_get; cbn [sv_denot]; reflexivity|].
  rewrite (RG 12%bv); eval_sr_get; cbn [sv_denot]; rewrite Z.add_0_r, (HE 9%nat 9%bv eq_refl), Z_to_bv_bv_unsigned; exact G9.
- assert (Hci : 0 <= 16 * i /\ 16 * i + 16 <= 4 * M) by (subst M; nia).
  destruct (bytes_of_present ubs2segs mem (flt + 16 * i) 16 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); lia)) as (b0 & Lb0 & Hb0).
  assert (Hs48' := slot_now mem 48 _ HMI ltac:(lia) ltac:(lia) Hs48).
  assert (Hs112' := slot_now mem 112 _ HMI ltac:(lia) ltac:(lia) Hs112).
  set (E0 := EregB regs (map (Z_to_bv 64) [flt + 16 * i; fimg + i; 2 ^ 64 - 1 - fimg; fimg]) [b0]).
  set (E := ew_fregs E0 64 (@fp_regs fy)).
  assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_EregB_nat; assumption).
  assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
  assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
  { intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
  assert (A32 : ew E0 32 = Z_to_bv 64 (flt + 16 * i)) by (subst E0; apply (EregB_vals regs _ _ 0%nat); reflexivity).
  assert (A33 : ew E0 33 = Z_to_bv 64 (fimg + i)) by (subst E0; apply (EregB_vals regs _ _ 1%nat); reflexivity).
  assert (A34 : ew E0 34 = Z_to_bv 64 (2 ^ 64 - 1 - fimg)) by (subst E0; apply (EregB_vals regs _ _ 2%nat); reflexivity).
  assert (A35 : ew E0 35 = Z_to_bv 64 fimg) by (subst E0; apply (EregB_vals regs _ _ 3%nat); reflexivity).
  assert (U23 : bv_unsigned (ew E0 23) = i) by (rewrite (HE0 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E0 9) = fmt * i) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; nia).
  assert (U19 : bv_unsigned (ew E0 19) = 2 ^ 64 - 1 - flt) by (rewrite (HE0 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E0 24) = flt) by (rewrite (HE0 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; lia).
  assert (U2 : bv_unsigned (ew E0 2) = spv) by (rewrite (HE0 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E0 32) = flt + 16 * i) by (rewrite A32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E0 33) = fimg + i) by (rewrite A33; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E0 34) = 2 ^ 64 - 1 - fimg) by (rewrite A34; apply unsigned_lit_small; lia).
  assert (U35 : bv_unsigned (ew E0 35) = fimg) by (rewrite A35; apply unsigned_lit_small; lia).
  assert (HS0 : @st_ok ubs2segs fy E0 ss_H4x (@mkst fy regs (Z_to_bv 64 PC_DIH) mem (seg_rom ubs2segs))).
  { unfold ss_H4x. apply entry_st_ok_env.
    - apply regs_ok_pin; [subst E0; apply regs_ok_EregB | intros HH0; discriminate HH0 | cbn [sv_denot]; rewrite <- F4; exact G7].
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor; [|constructor]]].
      + unfold h4_frame, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U2.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor]].
        * eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A35, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Hs48'].
        * eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A34, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Hs112'].
      + unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U32.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil]. set (bse := flt + 16 * i) in *. replace 16 with (Z.of_nat (length b0)) by (rewrite Lb0; reflexivity).
        apply (chunk_ok_data ubs2segs E0 mem bse 0 0 b0 ltac:(subst E0; reflexivity)). intros j Hj. rewrite Z.add_0_r. apply Hb0. rewrite <- Lb0. exact Hj.
      + unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U33.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply (fimg_writable mem HJ); lia | constructor].
    - cbn [pairwise_disjoint all_disjoint]. unfold h4_frame, extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U2, U32, U33.
      subst M. repeat split; lia.
    - split; [|split].
      + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23, U9, U19, U24, U2, U32, U33, U34, U35.
        change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
        assert ((flt + 16 * i) mod 16 = 0) by (replace (flt + 16 * i) with (flt + i * 16) by lia; rewrite Z.mod_add by lia; exact Hflt16).
        repeat split; lia.
      + cbn [f_conds conds_ok]. exact I.
      + cbn [f_alias alias_ok]. split; [|split; [|exact I]].
        * apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U24, U23, U32, !Z.add_0_r.
          rewrite (zcanon_id flt), (zcanon_id i) by (unfold M64; lia). change (Z.land (zcanon 4) 63) with 4. rewrite Z.shiftl_mul_pow2 by lia.
          change (2 ^ 4) with 16. rewrite (zcanon_id (i * 16)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia.
        * apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U35, U23, U33, !Z.add_0_r. rewrite (zcanon_id fimg), (zcanon_id i) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). reflexivity. }
  pose proof (st_ok_enterF ubs2segs fy 64 E0 ss_H4x _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
  change (ew_fregs E0 64 (@fp_regs fy)) with E in HS.
  clear HS0. rewrite <- !HEE in U23, U9, U19, U24, U2, U32, U33, U34, U35 by lia.
  change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_DIH) mem (seg_rom ubs2segs))) in HJ.
  assert (Hwr : wr_ok E (ss_mem ss_H4x) RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq)).
  { unfold ss_H4x. cbn [ss_mem]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|].
    eapply wr_ok_cons_gen; [reflexivity | exact U33 | cbn [r_wlo r_whi]; intros a Ha; replace a with (fimg + i) by lia; apply Hwbg; lia | apply wr_ok_nil]. }
  assert (POST : forall (ssx : sstate) (msx : machine_state) (skip : bool), st_okF ubs2segs E ssx msx -> ss_resv ssx = None ->
    ss_pc ssx = (if skip then PC_IN else PC_CL) ->
    forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ssx) rr) (SOff (ridx rr) 0)) H_KEEP = true -> sr_get (ss_regs ssx) 7%bv = SLit 4 ->
    (forall rr : reg, In rr H_FKEEP -> reg_get (ms_fregs msx) rr = reg_get (@fp_regs fy) rr) ->
    (skip = false -> sr_get (ss_regs ssx) 10%bv = SMd M_MUL (SLit 4) (SOff 23 0) /\ sr_get (ss_regs ssx) 11%bv = SLit 3 /\ sr_get (ss_regs ssx) 12%bv = SOff 9%nat 0) ->
    (skip = true -> sr_get (ss_regs ssx) 11%bv = SOff 23%nat 1) ->
    journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq (ms_mem msx) mdq ->
    (forall a, 0 <= a < 2 ^ 64 -> a <> fimg + i -> mbyte ubs2segs (ms_mem msx) a = mbyte ubs2segs mem a) ->
    H_post fy regs mem i (mkCfg msx mdq)).
  { intros ssx msx skip HSx Hrv Hpc Hkb Q7 HFK Qns Qsk HJx Hmb. exists (fp_of msx), (ms_regs msx), (ms_mem msx), skip.
    split; [rewrite (st_okF_mkst ubs2segs E ssx msx HSx Hrv), Hpc; reflexivity|]. split; [exact HJx|]. split; [exact (st_okF_frm ubs2segs E _ _ HSx)|].
    assert (RG : forall rr : reg, getr (ms_regs msx) rr = sv_denot E (sr_get (ss_regs ssx) rr)) by (intros rr; exact (st_okF_reg ubs2segs E ssx msx rr HSx)).
    split; [exact (st_okF_regs_kept ubs2segs E ssx msx _ H_KEEP HSx ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) Hkb)|].
    split; [rewrite (RG 7%bv), Q7; cbn [sv_denot]; rewrite F4; reflexivity|].
    split; [exact HFK|]. split; [exact Hmb|].
    split.
    { intros Hsk. destruct (Qns Hsk) as (Q10 & Q11 & Q12).
      split; [rewrite (RG 10%bv), Q10, (U_mul_lit E 23 4 i) by first [rewrite <- U23; symmetry; apply Z_to_bv_bv_unsigned | lia]; rewrite F4; reflexivity|].
      split; [rewrite (RG 11%bv), Q11; reflexivity|].
      rewrite (RG 12%bv), Q12; cbn [sv_denot]; rewrite U9, Z.add_0_r; reflexivity. }
    intros Hsk. rewrite (RG 11%bv), (Qsk Hsk); cbn [sv_denot]; rewrite U23; reflexivity. }
  jrunF_to LAWS ubs2tbl_ok HS HJ PC_CL. { wr_ok_eval. apply Hwr. }
  cbn [ms_mem mkst] in HF, HJ.
  jbranchF ubs2tbl HS.
  + jrunF_to LAWS ubs2tbl_ok HS HJ PC_CL. { wr_ok_eval. apply Hwr. }
    cbn [ms_mem mkst] in HF0, HJ. apply SR_ret.
    lazymatch type of HS with st_okF _ _ ?ssx ?msx =>
      assert (HFK : forall rr : reg, In rr H_FKEEP -> reg_get (ms_fregs msx) rr = reg_get (@fp_regs fy) rr)
        by (apply (st_okF_fregs_kept ubs2segs E ssx msx 64 (@fp_regs fy) H_FKEEP HS); [intros rr; subst E; apply ew_fregs_at | vm_compute; reflexivity]) end.
    eapply (POST _ _ false HS); [reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact HFK | intros _; repeat split; reflexivity | intros HH0; discriminate HH0 | exact HJ |].
    intros a Ha Hna. mb_frames ltac:(exact Ha) ltac:(rewrite ?U32, ?U33; lia). reflexivity.
  + jrunF_to LAWS ubs2tbl_ok HS HJ PC_IN. { wr_ok_eval. apply Hwr. }
    cbn [ms_mem mkst] in HF0, HJ. apply SR_ret.
    lazymatch type of HS with st_okF _ _ ?ssx ?msx =>
      assert (HFK : forall rr : reg, In rr H_FKEEP -> reg_get (ms_fregs msx) rr = reg_get (@fp_regs fy) rr)
        by (apply (st_okF_fregs_kept ubs2segs E ssx msx 64 (@fp_regs fy) H_FKEEP HS); [intros rr; subst E; apply ew_fregs_at | vm_compute; reflexivity]) end.
    eapply (POST _ _ true HS); [reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact HFK | intros HH0; discriminate HH0 | intros _; reflexivity | exact HJ |].
    intros a Ha Hna. mb_frames ltac:(exact Ha) ltac:(rewrite ?U32, ?U33; lia). reflexivity.
Qed.
Definition ss_CLx : sstate :=
mkSS PC_CL sr_atoms [ YQ0b.mkRegion (Some 32%nat) 0 4 0 4 [mkChunk 0 (CVal 4 (SOff 33 0))] ] None
(mkFacts [ (12%nat, mkAF 0 (2 ^ 20) 0); (11%nat, mkAF 1 3 0); (19%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0);
  (24%nat, mkAF 4096 CEIL_MAX 4); (32%nat, mkAF 4096 CEIL_MAX 2); (33%nat, mkAF 0 (2 ^ 32 - 1) 0) ] []
[ (SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLL (SOff 12 0) (SLit 2)), SOff 32%nat 0) ]).
Definition cl_le (n : nat) : sv := SF2 (FP2_cmp F_LE FMT_S) (SF1 FP1_nanbox (SOff 33 0)) (SOff n 0).
Definition cl_c1 : sv := SAlu ALU_AND (cl_le 72) (cl_le 73).
Definition cl_c2 : sv := SAlu ALU_OR (cl_le 72) (SAlu ALU_XOR (cl_le 73) (SLit 1)).
Definition CL_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition CL_FKEEP : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition CL_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (v cnt : Z) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if cnt =? 1 then PC_GA else PC_CL)) mem' (seg_rom ubs2segs)) mdq /\
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\ frm_zero (@fp_csr fy') /\
getr regs' 11 = Z_to_bv 64 (cnt - 1) /\ getr regs' 12 = Z_to_bv 64 (v + 1) /\
(forall rr : reg, In rr CL_KEEP -> getr regs' rr = getr regs rr) /\
(forall rr : reg, In rr CL_FKEEP -> reg_get (@fp_regs fy') rr = reg_get (@fp_regs fy) rr) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * v <= a < flt + 4 * v + 4) -> mbyte ubs2segs mem' a = mbyte ubs2segs mem a) /\
(exists cv, val_mem ubs2segs mem' (flt + 4 * v) 4 cv /\ 0 <= cv < 2 ^ 32 /\ s_in cv 0 255).
Lemma CL_step : forall (fy : FPState) (regs : bvmap 5 word) mem (v cnt : Z),
0 <= v < 2 ^ 20 -> 1 <= cnt <= 3 -> 4 * v + 4 <= 4 * M ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> fregs3 (@fp_regs fy) ->
getr regs 12 = Z_to_bv 64 v -> getr regs 11 = Z_to_bv 64 cnt -> getr regs 24 = Z_to_bv 64 flt -> getr regs 19 = Z_to_bv 64 (2 ^ 64 - 1 - flt) ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_CL) mem (seg_rom ubs2segs)) mdq) (CL_post fy regs mem v cnt).
Proof.
intros fy regs mem v cnt Hv Hcnt HvM HJ Hfrm HF3 G12 G11 G24 G19.
pose proof di_consts as (HRv & HF1 & HF16 & HNMv & HNSv & Hac). pose proof Hf4 as Hf4'.
destruct HF3 as (F8 & F9 & _).
destruct (val_mem4_of_present ubs2segs mem (flt + 4 * v) ltac:(intros j Hj; replace (flt + 4 * v + j) with (flt + (4 * v + j)) by lia; apply (flt_present mem HJ); lia)) as (cv0 & Rc & Vc).
set (E0 := EregB regs (map (Z_to_bv 64) [flt + 4 * v; cv0]) []).
set (E := ew_fregs E0 64 (@fp_regs fy)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_EregB_nat; assumption).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (A32 : ew E0 32 = Z_to_bv 64 (flt + 4 * v)) by (subst E0; apply (EregB_vals regs _ _ 0%nat); reflexivity).
assert (A33 : ew E0 33 = Z_to_bv 64 cv0) by (subst E0; apply (EregB_vals regs _ _ 1%nat); reflexivity).
assert (U12 : bv_unsigned (ew E0 12) = v) by (rewrite (HE0 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E0 11) = cnt) by (rewrite (HE0 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E0 24) = flt) by (rewrite (HE0 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E0 19) = 2 ^ 64 - 1 - flt) by (rewrite (HE0 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E0 32) = flt + 4 * v) by (rewrite A32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = cv0) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok ubs2segs fy E0 ss_CLx (@mkst fy regs (Z_to_bv 64 PC_CL) mem (seg_rom ubs2segs))).
{ unfold ss_CLx. apply entry_st_ok_env.
  - subst E0; apply regs_ok_EregB.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U32.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply (flt_writable mem HJ); lia|].
    apply Forall_cons; [|apply Forall_nil].
    eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A33, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vc].
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [|split].
    + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U12, U11, U24, U19, U32, U33.
      change (2 ^ 2) with 4. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      assert ((flt + 4 * v) mod 4 = 0) by (replace (flt + 4 * v) with (flt + v * 4) by lia; rewrite Z.mod_add by lia; exact Hf4').
      repeat split; lia.
    + cbn [f_conds conds_ok]. exact I.
    + cbn [f_alias alias_ok]. split; [|exact I].
      apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U24, U12, U32, !Z.add_0_r.
      rewrite (zcanon_id flt), (zcanon_id v) by (unfold M64; lia). change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
      change (2 ^ 2) with 4. rewrite (zcanon_id (v * 4)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia. }
pose proof (st_ok_enterF ubs2segs fy 64 E0 ss_CLx _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
change (ew_fregs E0 64 (@fp_regs fy)) with E in HS.
clear HS0.
assert (H72 : ew E 72 = nan_box (Z_to_bv 32 0)) by (subst E; exact (eq_trans (ew_fregs_at E0 64 (@fp_regs fy) 8%bv) F8)).
assert (H73 : ew E 73 = nan_box (Z_to_bv 32 S255)) by (subst E; exact (eq_trans (ew_fregs_at E0 64 (@fp_regs fy) 9%bv) F9)).
assert (W33 : ew E 33 = Z_to_bv 64 cv0) by (rewrite HEE by lia; exact A33).
pose proof (U_cl_and E 33 72 73 cv0 W33 Rc H72 H73) as VA. pose proof (U_cl_or E 33 72 73 cv0 W33 Rc H72 H73) as VO.
pose proof (cl_mid cv0) as VM. unfold LEV in VA, VO.
assert (P0 : fp_arg FMT_S (sv_denot E (SOff 72 0)) = 0) by (apply (fp_arg_f0 E 72 cv0 Rc); exact H72).
assert (P1 : fp_arg FMT_S (sv_denot E (SOff 73 0)) = S255) by (apply (fp_arg_f1 E 73 cv0 Rc); exact H73).
assert (Pv : fp_arg FMT_S (sv_denot E (SF1 FP1_nanbox (SOff 33 0))) = cv0) by (apply (fp_arg_v E 33 cv0 W33 Rc)).
rewrite <- !HEE in U12, U11, U24, U19, U32, U33 by lia.
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_CL) mem (seg_rom ubs2segs))) in HJ.
assert (Hwr : forall cs, wr_ok E [YQ0b.mkRegion (Some 32%nat) 0 4 0 4 cs] RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq)).
{ intros cs. eapply wr_ok_cons_gen; [reflexivity | exact U32 | cbn [r_wlo r_whi]; intros a Ha; replace a with (flt + (a - flt)) by lia; apply Hwbf; lia | apply wr_ok_nil]. }
assert (FIN : forall (ssx : sstate) (msx : machine_state) (X : sv) pc, st_okF ubs2segs E ssx msx -> ss_resv ssx = None -> ss_pc ssx = pc ->
  forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ssx) rr) (SOff (ridx rr) 0)) CL_KEEP = true ->
  sr_get (ss_regs ssx) 11%bv = SOff 11%nat (-1) -> sr_get (ss_regs ssx) 12%bv = SOff 12%nat 1 ->
  (forall rr : reg, In rr CL_FKEEP -> reg_get (ms_fregs msx) rr = reg_get (@fp_regs fy) rr) ->
  journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq (ms_mem msx) mdq ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * v <= a < flt + 4 * v + 4) -> mbyte ubs2segs (ms_mem msx) a = mbyte ubs2segs mem a) ->
  ss_mem ssx = [YQ0b.mkRegion (Some 32%nat) 0 4 0 4 [mkChunk 0 (CVal 4 (SF2 (FP2_sgnj F_SGNJ FMT_S) X X))]] ->
  0 <= fp_arg FMT_S (sv_denot E X) < 2 ^ 32 -> s_in (fp_arg FMT_S (sv_denot E X)) 0 255 ->
  (if cnt =? 1 then PC_GA else PC_CL) = pc ->
  CL_post fy regs mem v cnt (mkCfg msx mdq)).
{ intros ssx msx X pc HSx Hrv Hpc Hkb Q11 Q12 HFK HJx Hmb Hmm Rx Ix Hpce. exists (fp_of msx), (ms_regs msx), (ms_mem msx).
  split; [rewrite (st_okF_mkst ubs2segs E ssx msx HSx Hrv), Hpc, Hpce; reflexivity|]. split; [exact HJx|]. split; [exact (st_okF_frm ubs2segs E _ _ HSx)|].
  split; [rewrite (st_okF_reg ubs2segs E ssx msx 11%bv HSx), Q11; cbn [sv_denot]; rewrite U11; reflexivity|].
  split; [rewrite (st_okF_reg ubs2segs E ssx msx 12%bv HSx), Q12; cbn [sv_denot]; rewrite U12; reflexivity|].
  split; [exact (st_okF_regs_kept ubs2segs E ssx msx _ CL_KEEP HSx ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) Hkb)|].
  split; [exact HFK|]. split; [exact Hmb|].
  exists (fp_arg FMT_S (sv_denot E X)). split; [|split; [exact Rx | exact Ix]].
  pose proof HSx as (_ & _ & _ & _ & _ & _ & _ & HMx & _). rewrite Hmm in HMx.
  destruct HMx as (_ & HRx & _). apply Forall_cons_iff in HRx as (HRx & _).
  destruct HRx as (_ & _ & _ & Hcs). cbn [YQ0b.r_chunks YQ0b.r_base base_val] in Hcs. rewrite U32 in Hcs.
  pose proof (val_mem_of_cval4 ubs2segs E _ (flt + 4 * v) 0 _ (Forall_inv Hcs)) as Hvm.
  rewrite U_fmv_s_mod, Z.add_0_r in Hvm. exact Hvm. }
apply (st_okF_branch ubs2segs E _ _ _ BC_NE cl_c1 (SLit 0) HS); clear HS; intros Hc1 HS;
(apply (st_okF_branch ubs2segs E _ _ _ BC_NE cl_c2 (SLit 0) HS); clear HS; intros Hc2 HS).
all: rewrite branch_ne_U in Hc1, Hc2; unfold cl_c1, cl_c2, cl_le in Hc1, Hc2; rewrite VA in Hc1; rewrite VO in Hc2; rewrite U_SLit in Hc1, Hc2; change (zcanon 0) with 0 in Hc1, Hc2.
2: { exfalso. clear - Hc1 Hc2. destruct (cb0 cv0), (cb1 cv0); cbn in Hc1, Hc2; discriminate. }
all: unfold cl_c1, cl_c2, cl_le in HS; cbn [neg_bc] in HS.
all: jrunF_to LAWS ubs2tbl_ok HS HJ PC_GA; [wr_ok_eval; apply Hwr|].
all: cbn [ms_mem mkst] in HF, HJ.
all: jbranchF ubs2tbl HS.
all: lazymatch goal with Hb : branch_taken _ (sv_denot _ (SOff 11 (-1))) (sv_denot _ (SLit 0)) = ?bb |- _ =>
  rewrite branch_ne_U, U_SOff, U_SLit, U11 in Hb; change (zcanon 0) with 0 in Hb; rewrite zcanon_id in Hb by (unfold M64; lia);
  first [ constr_eq bb true; replace (cnt =? 1) with false in * by (symmetry; apply Z.eqb_neq; destruct (Z.eqb_spec (cnt + -1) 0); [discriminate Hb | lia]);
          jrunF_to LAWS ubs2tbl_ok HS HJ PC_CL; [wr_ok_eval; apply Hwr|]
        | constr_eq bb false; replace (cnt =? 1) with true in * by (symmetry; apply Z.eqb_eq; destruct (Z.eqb_spec (cnt + -1) 0); [lia | discriminate Hb]);
          jrunF_to LAWS ubs2tbl_ok HS HJ PC_GA; [wr_ok_eval; apply Hwr|] ] end.
all: cbn [ms_mem mkst] in HF0, HJ; apply SR_ret.
all: lazymatch type of HS with st_okF _ _ ?ssx ?msx =>
  assert (HFK : forall rr : reg, In rr CL_FKEEP -> reg_get (ms_fregs msx) rr = reg_get (@fp_regs fy) rr)
    by (apply (st_okF_fregs_kept ubs2segs E ssx msx 64 (@fp_regs fy) CL_FKEEP HS); [intros rr; subst E; apply ew_fregs_at | vm_compute; reflexivity]) end.
all: lazymatch type of HS with st_okF _ _ ?ssx _ =>
  let mm := eval vm_compute in (ss_mem ssx) in
  lazymatch mm with
  | [ YQ0b.mkRegion _ _ _ _ _ [mkChunk 0 (CVal 4 (SF2 (FP2_sgnj F_SGNJ FMT_S) ?X _))] ] =>
    eapply (FIN _ _ X _ HS ltac:(reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(reflexivity) HFK HJ);
    [ intros a Ha Hna; mb_frames ltac:(exact Ha) ltac:(rewrite ?U32; lia); reflexivity
    | vm_compute; reflexivity
    | first [rewrite P0; lia | rewrite P1; unfold S255; lia | rewrite Pv; exact Rc]
    | first [rewrite P0; apply (s_in_0 cv0 Rc) | rewrite P1; apply (s_in_255 cv0 Rc) | rewrite Pv; apply VM; clear - Hc1 Hc2; destruct (cb0 cv0), (cb1 cv0); cbn in Hc1, Hc2; first [reflexivity | discriminate]]
    | reflexivity ]
  end end.
Qed.
Lemma CL3_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> fregs3 (@fp_regs fy) ->
getr regs 12 = Z_to_bv 64 (fmt * i) -> getr regs 11 = Z_to_bv 64 3 -> getr regs 24 = Z_to_bv 64 flt -> getr regs 19 = Z_to_bv 64 (2 ^ 64 - 1 - flt) ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_CL) mem (seg_rom ubs2segs)) mdq)
(fun c' => exists (fy' : FPState) regs' mem' c0 c1 c2,
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 PC_GA) mem' (seg_rom ubs2segs)) mdq /\
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\ frm_zero (@fp_csr fy') /\
(forall rr : reg, In rr CL_KEEP -> getr regs' rr = getr regs rr) /\
(forall rr : reg, In rr CL_FKEEP -> reg_get (@fp_regs fy') rr = reg_get (@fp_regs fy) rr) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * (fmt * i) <= a < flt + 4 * (fmt * i) + 12) -> mbyte ubs2segs mem' a = mbyte ubs2segs mem a) /\
cells_at fmt flt mem' i c0 c1 c2).
Proof.
intros fy regs mem i Hi HJ Hfrm HF3 G12 G11 G24 G19.
pose proof di_consts as (HRv & HF1 & HF16 & HNMv & HNSv & Hac).
assert (HM : 4 * (fmt * i) + 12 <= 4 * M) by (subst M; nia). assert (Hfi : 0 <= fmt * i) by nia. assert (Hfi2 : fmt * i + 2 < 2 ^ 20) by nia.
assert (FK3 : forall f f' : bvmap 5 word, (forall rr : reg, In rr CL_FKEEP -> reg_get f' rr = reg_get f rr) -> fregs3 f -> fregs3 f').
{ intros f f' HK (X1 & X2 & X3). unfold fregs3. rewrite !HK by inK. repeat split; assumption. }
unfold cells_at. set (v := fmt * i) in *. clearbody v.
eapply SR_bind; [exact (CL_step fy regs mem v 3 ltac:(lia) ltac:(lia) ltac:(lia) HJ Hfrm HF3 G12 G11 G24 G19)|].
cbv beta. intros c1 (fy1 & regs1 & mem1 & -> & HJ1 & Hfrm1 & G11a & G12a & Hk1 & HF1' & Hm1 & (cv0 & Vc0 & Rc0 & Ic0)).
replace (3 =? 1) with false by reflexivity.
eapply SR_bind; [exact (CL_step fy1 regs1 mem1 (v + 1) 2 ltac:(lia) ltac:(lia) ltac:(lia) HJ1 Hfrm1 (FK3 _ _ HF1' HF3) G12a G11a
  ltac:(rewrite (Hk1 24%bv ltac:(inK)); exact G24) ltac:(rewrite (Hk1 19%bv ltac:(inK)); exact G19))|].
cbv beta. intros c2 (fy2 & regs2 & mem2 & -> & HJ2 & Hfrm2 & G11b & G12b & Hk2 & HF2' & Hm2 & (cv1 & Vc1 & Rc1 & Ic1)).
replace (2 =? 1) with false by reflexivity.
eapply SR_mono; [exact (CL_step fy2 regs2 mem2 (v + 1 + 1) (3 - 1 - 1) ltac:(lia) ltac:(lia) ltac:(lia) HJ2 Hfrm2 (FK3 _ _ HF2' (FK3 _ _ HF1' HF3)) G12b G11b
  ltac:(rewrite (Hk2 24%bv ltac:(inK)), (Hk1 24%bv ltac:(inK)); exact G24) ltac:(rewrite (Hk2 19%bv ltac:(inK)), (Hk1 19%bv ltac:(inK)); exact G19))|].
cbv beta. intros c3 (fy3 & regs3 & mem3 & -> & HJ3 & Hfrm3 & G11c & G12c & Hk3 & HF3' & Hm3 & (cv2 & Vc2 & Rc2 & Ic2)).
exists fy3, regs3, mem3, cv0, cv1, cv2. replace (3 - 1 - 1 =? 1) with true by reflexivity. split; [reflexivity|].
split; [exact HJ3|]. split; [exact Hfrm3|].
split; [intros rr Hrr; rewrite (Hk3 rr Hrr), (Hk2 rr Hrr), (Hk1 rr Hrr); reflexivity|].
split; [intros rr Hrr; rewrite (HF3' rr Hrr), (HF2' rr Hrr), (HF1' rr Hrr); reflexivity|].
split; [intros a Ha Hna; rewrite (Hm3 a Ha ltac:(lia)), (Hm2 a Ha ltac:(lia)), (Hm1 a Ha ltac:(lia)); reflexivity|].
assert (VK : forall (m m' : word -> option byte) a c, val_mem ubs2segs m a 4 c ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (a <= x < a + 4) -> False \/ mbyte ubs2segs m' x = mbyte ubs2segs m x) -> True) by (intros; exact I).
clear VK.
assert (KV : forall (m m' : word -> option byte) a c, val_mem ubs2segs m a 4 c -> 0 <= a -> a + 4 < 2 ^ 64 ->
  (forall x, a <= x < a + 4 -> mbyte ubs2segs m' x = mbyte ubs2segs m x) -> val_mem ubs2segs m' a 4 c).
{ intros m m' a c Hv Ha0 Ha1 Hk k Hk'. rewrite Hk by lia. apply Hv. exact Hk'. }
split; [|split; [|split; [|exact (conj Rc0 (conj Rc1 (conj Rc2 (conj Ic0 (conj Ic1 Ic2)))))]]].
- apply (KV mem1); [exact Vc0 | lia | lia |]. intros x Hx. rewrite (Hm3 x ltac:(lia) ltac:(lia)), (Hm2 x ltac:(lia) ltac:(lia)). reflexivity.
- replace (flt + 4 * v + 4) with (flt + 4 * (v + 1)) by lia. apply (KV mem2); [exact Vc1 | lia | lia |]. intros x Hx. rewrite (Hm3 x ltac:(lia) ltac:(lia)). reflexivity.
- replace (flt + 4 * v + 8) with (flt + 4 * (v + 1 + 1)) by lia. exact Vc2.
Qed.
Definition ss_GA : sstate :=
mkSS PC_GA sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 160 0 0 [mkChunk 80 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (10%nat, mkAF 0 (2 ^ 20) 0); (19%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0);
  (24%nat, mkAF 4096 CEIL_MAX 4); (32%nat, mkAF 4096 CEIL_MAX 4); (2%nat, mkAF CEIL_MIN (2 ^ 63) 4) ] [] []).
Definition GA_KEEP : list reg := [2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma GA_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> memIv mem ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 10 = Z_to_bv 64 (fmt * i) ->
getr regs 24 = Z_to_bv 64 flt -> getr regs 19 = Z_to_bv 64 (2 ^ 64 - 1 - flt) ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_GA) mem (seg_rom ubs2segs)) mdq)
(fun c' => exists regs',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 ubs2_A_get_leave_node_index) mem (seg_rom ubs2segs)) mdq /\
getr regs' 1 = Z_to_bv 64 PC_GR /\ getr regs' 10 = Z_to_bv 64 (troot t) /\ getr regs' 11 = Z_to_bv 64 (flt + 4 * (fmt * i)) /\
(forall rr : reg, In rr GA_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem i Hi HJ HMI G2 G10 G24 G19.
pose proof di_consts as (HRv & HF1 & HF16 & HNMv & HNSv & Hac). pose proof sp_facts as (S1 & S2 & S3).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
assert (Hs80' := slot_now mem 80 _ HMI ltac:(lia) ltac:(lia) Hs80).
destruct Htroot as (T0 & T1 & T16).
set (E := Ereg regs [Z_to_bv 64 (troot t)]).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 (troot t)) by (subst E; apply (Ereg_vals regs [troot t] [] 0%nat); reflexivity).
assert (U10 : bv_unsigned (ew E 10) = fmt * i) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; nia).
assert (U24 : bv_unsigned (ew E 24) = flt) by (rewrite (HE 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = 2 ^ 64 - 1 - flt) by (rewrite (HE 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = troot t) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : @st_ok ubs2segs fy E ss_GA (@mkst fy regs (Z_to_bv 64 PC_GA) mem (seg_rom ubs2segs))).
{ unfold ss_GA. subst E. apply entry_st_ok_gen.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U2.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Hs80'].
  - cbn [pairwise_disjoint all_disjoint]. repeat split.
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10, U24, U19, U32, U2.
    change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; try lia; nia. }
pure_to ubs2tbl_ok HS ubs2_A_get_leave_node_index.
eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms). apply SR_ret.
lazymatch goal with |- context [mkCfg (@mkst _ ?rg _ _ _) _] => rename rg into regs2 end.
exists regs2. split; [reflexivity|].
assert (RG : forall rr : reg, getr regs2 rr = sv_denot E (sr_get (ss_regs (fst (sym_run_toN ubs2segs ubs2tbl FUEL ubs2_A_get_leave_node_index ss_GA))) rr))
  by (intros rr; exact (st_ok_reg ubs2segs E _ _ rr HS)).
match type of RG with context [ss_regs (fst ?x)] => let v := eval vm_compute in (ss_regs (fst x)) in change (ss_regs (fst x)) with v in RG end.
split; [rewrite (RG 1%bv); eval_sr_get; reflexivity|].
split; [rewrite (RG 10%bv); eval_sr_get; cbn [sv_denot]; rewrite Z.add_0_r, A32, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (RG 11%bv); eval_sr_get; rewrite (U_add_shl2 E 10 24 flt (fmt * i) U24 U10) by nia; f_equal; lia|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ GA_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
End l.
End f.
End d.
