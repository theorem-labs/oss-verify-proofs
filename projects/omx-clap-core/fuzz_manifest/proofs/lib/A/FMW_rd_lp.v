(* lv2_locate_manifest_readings: the declaration scan's head L (0x81d18, lv2_locate.c:104-114) to R, L or P:
   SEG_L of FMW_rd_top.v. The byte at at = text + i: NUL ends the scan (0x820b0, R with res 0); '@' asks
   strncmp (at + 1, "prefix", 6) (0x81d48, "@prefix" head: P with s11 = 7); otherwise strncasecmp (at, "PREFIX", 6)
   (0x81d60): a "PREFIX" head at the text's start or after a space goes to P with s11 = 6, everything else to L at
   i + 1 (0x8202c). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_rd_cuts FMW_rd_ret ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- pure steps of fm's model (copies of lib/Prog/readings_scan.v:12-16, 230-235, 276-291, 318-350, kept here so
   this file does not load the plain engine) ---- *)
Lemma lp_bas : forall (t : list Z) p, (p < length t)%nat -> skipn p t = byte_at t p :: skipn (S p) t.
Proof.
  unfold byte_at. induction t as [|x t IH]; intros p Hp; cbn in Hp; [lia|].
  destruct p as [|p]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma lp_sc_end : forall t u i d f, (length t <= i)%nat -> scan t u i d (S f) = 0 /\ readings t u i d (S f) = O.
Proof. intros t u i d f H. cbn [scan readings]. rewrite (proj2 (Nat.leb_le _ _) H). split; reflexivity. Qed.

Lemma lp_sc_none : forall t u i d f, (i < length t)%nat -> head t i = None ->
  scan t u i d (S f) = scan t u (S i) d f /\ readings t u i d (S f) = readings t u (S i) d f.
Proof.
  intros t u i d f H D. cbn [scan readings]. rewrite (proj2 (Nat.leb_gt _ _) H). unfold decl. rewrite D.
  split; reflexivity.
Qed.

Lemma lp_head_at : forall t i, (i < length t)%nat -> byte_at t i = 64 ->
  head t i = if zl_eqb (firstn 6 (skipn (S i) t)) prefix_lc then Some (i + 7)%nat else None.
Proof.
  intros t i Hi Hb. unfold head. rewrite Hb, Z.eqb_refl. cbn [andb].
  destruct (zl_eqb (firstn 6 (skipn (S i) t)) prefix_lc); [reflexivity|].
  rewrite (lp_bas t i Hi), Hb. reflexivity.
Qed.

Lemma lp_ci_at64 : forall t i, (i < length t)%nat -> byte_at t i = 64 -> ci_eqb (firstn 6 (skipn i t)) prefix_lc = false.
Proof. intros t i Hi Hb. rewrite (lp_bas t i Hi), Hb. reflexivity. Qed.

Lemma lp_head_nat : forall t i, byte_at t i <> 64 ->
  head t i = if ci_eqb (firstn 6 (skipn i t)) prefix_lc &&
                match i with O => true | S i' => is_space (byte_at t i') end
             then Some (i + 6)%nat else None.
Proof. intros t i Hb. unfold head. rewrite (proj2 (Z.eqb_neq _ _) Hb). reflexivity. Qed.

Lemma lp_firstn_app0 : forall (l p : list Z), Forall (fun c => c <> 0) l -> Forall (fun c => c <> 0) p ->
  firstn (length p) (l ++ [0]) = p <-> firstn (length p) l = p.
Proof.
  intros l p Hl Hp. revert l Hl. induction p as [|y p IH]; intros l Hl; cbn [length firstn]; [tauto|].
  inversion Hp as [|y' p' Hy Hp']; subst.
  destruct l as [|x l]; cbn [app firstn].
  - split; intros H; [|discriminate]. injection H as H1 _. exfalso. apply Hy. symmetry. exact H1.
  - inversion Hl as [|x' l' Hx Hl']; subst.
    split; intros H; injection H as H1 H2; subst x; f_equal.
    + apply (proj1 (IH Hp' l Hl')). exact H2.
    + apply (proj2 (IH Hp' l Hl')). exact H2.
Qed.

Lemma lp_lc_app0 : forall (l p : list Z), Forall (fun c => 0 < c) l -> Forall (fun y => 97 <= y <= 122) p ->
  map lc (firstn (length p) (l ++ [0])) = p <-> ci_eqb (firstn (length p) l) p = true.
Proof.
  intros l p Hl Hp. revert l Hl. induction p as [|y p IH]; intros l Hl; cbn [length firstn map ci_eqb]; [tauto|].
  inversion Hp as [|y' p' Hy Hp']; subst.
  destruct l as [|x l]; cbn [app firstn map ci_eqb].
  - split; intros H; [|discriminate]. injection H as H1 _. unfold lc in H1. cbn in H1. lia.
  - inversion Hl as [|x' l' Hx Hl']; subst. split; intros H.
    + injection H as H1 H2. apply andb_true_iff. split.
      * unfold lc in H1.
        destruct ((65 <=? x) && (x <=? 90)) eqn:E; apply orb_true_iff; [right|left]; apply Z.eqb_eq; lia.
      * apply (proj1 (IH Hp' l Hl')). exact H2.
    + apply andb_true_iff in H as [H1 H2]. f_equal.
      * apply orb_true_iff in H1 as [H1|H1]; apply Z.eqb_eq in H1; unfold lc; subst x.
        -- destruct ((65 <=? y) && (y <=? 90)) eqn:E; [|reflexivity].
           apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
        -- destruct ((65 <=? y - 32) && (y - 32 <=? 90)) eqn:E; [lia|].
           apply andb_false_iff in E as [E|E]; apply Z.leb_gt in E; lia.
      * apply (proj2 (IH Hp' l Hl')). exact H2.
Qed.

(* the runtime answers in the model's terms: strncmp (s, "prefix", 6) and strncasecmp (s, "PREFIX", 6) *)
Definition LP_PRE : list Z := [112; 114; 101; 102; 105; 120].
Definition LP_PREU : list Z := [80; 82; 69; 70; 73; 88].

Lemma lp_strn6 : forall l, Forall (fun c => c <> 0) l ->
  strn_eq 6 l LP_PRE <-> zl_eqb (firstn 6 l) prefix_lc = true.
Proof.
  intros l Hl. unfold strn_eq. change (firstn 6 (LP_PRE ++ [0])) with prefix_lc.
  rewrite zl_eqb_eq. change 6%nat with (length prefix_lc).
  apply lp_firstn_app0; [exact Hl | unfold prefix_lc; repeat constructor; lia].
Qed.

Lemma lp_strncase6 : forall l, Forall (fun c => 0 < c) l ->
  strncase_eq 6 l LP_PREU <-> ci_eqb (firstn 6 l) prefix_lc = true.
Proof.
  intros l Hl. unfold strncase_eq. change (map lc (firstn 6 (LP_PREU ++ [0]))) with prefix_lc.
  change 6%nat with (length prefix_lc).
  apply lp_lc_app0; [exact Hl | unfold prefix_lc; repeat constructor; lia].
Qed.

(* the 64-bit unsigned compare of the isspace test (c - 9 <u 5) on a byte *)
Lemma lp_sp_ltu : forall c, 0 <= c < 256 -> (zcanon (c + -9) <? 5) = (9 <=? c) && (c <=? 13).
Proof.
  intros c Hc. unfold zcanon, M64.
  destruct (Z_lt_le_dec c 9) as [Hl|Hl].
  - replace (c + -9) with ((c + -9 + 2 ^ 64) + (-1) * 2 ^ 64) by ring. rewrite Z_mod_plus_full.
    rewrite Z.mod_small by lia. rewrite (proj2 (Z.leb_gt 9 c) Hl). cbn [andb]. apply Z.ltb_ge. lia.
  - rewrite Z.mod_small by lia. rewrite (proj2 (Z.leb_le 9 c) Hl). cbn [andb].
    destruct (Z.leb_spec c 13); [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma lp_byte_past : forall (t : list Z) p, (length t <= p)%nat -> byte_at t p = 0.
Proof. intros t p H. unfold byte_at. apply nth_overflow. lia. Qed.

Lemma lp_U_off : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff n c) = zcanon (v + c).
Proof. intros E n c v H Hv. rewrite U_SOff, H, unsigned_lit_small by lia. reflexivity. Qed.

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the bytes of a C string, and its suffixes *)
Lemma lp_cstr_pos : forall (W : world tfibsegs) mem p l, cstr_ok tfibsegs W mem p l -> Forall (fun c => 0 < c < 256) l.
Proof.
  intros W mem p l ((Hg & Hnz) & _). apply Forall_forall. intros x Hx.
  apply In_nth with (d := 0) in Hx. destruct Hx as (j & Hj & <-).
  destruct (Hg j ltac:(rewrite length_app; cbn [length]; lia)) as [_ R]. rewrite app_nth1 in R by lia.
  rewrite Forall_forall in Hnz. pose proof (Hnz (nth j l 0) (nth_In _ _ Hj)). lia.
Qed.

Lemma lp_byte_val : forall (W : world tfibsegs) mem p l j, cstr_ok tfibsegs W mem p l -> (j <= length l)%nat ->
  val_mem tfibsegs (rdW W mem) (p + Z.of_nat j) 1 (byte_at l j) /\ 0 <= byte_at l j < 256.
Proof.
  intros W mem p l j ((Hg & _) & _) Hj.
  assert (E : nth j (l ++ [0]) 0 = byte_at l j).
  { unfold byte_at. destruct (Nat.lt_ge_cases j (length l)) as [Hl|Hl].
    - apply app_nth1. exact Hl.
    - rewrite app_nth2 by lia. replace (j - length l)%nat with 0%nat by lia. rewrite (nth_overflow l) by lia.
      reflexivity. }
  rewrite <- E. apply Hg. rewrite length_app. cbn [length]. lia.
Qed.

Lemma lp_byte_end : forall (W : world tfibsegs) mem p l j, cstr_ok tfibsegs W mem p l -> (j <= length l)%nat ->
  byte_at l j = 0 -> j = length l.
Proof.
  intros W mem p l j HC Hj H0. destruct (Nat.lt_ge_cases j (length l)) as [Hl|Hl]; [|lia].
  pose proof (lp_cstr_pos W mem p l HC) as HP. rewrite Forall_forall in HP.
  pose proof (HP (byte_at l j) (nth_In l 0 Hl)) as R. lia.
Qed.

Lemma lp_nth_skipn : forall (l : list Z) m n d, nth n (skipn m l) d = nth (m + n) l d.
Proof.
  intros l m; revert l; induction m as [|m IH]; intros [|x l] n d; cbn; try reflexivity;
    [destruct n; reflexivity | apply IH].
Qed.

Lemma lp_div8_mono : forall a b, a <= b -> a / 8 * 8 <= b / 8 * 8.
Proof. intros a b H. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

Lemma lp_cstr_ok_suffix : forall (W : world tfibsegs) mem p l k, cstr_ok tfibsegs W mem p l -> (k <= length l)%nat ->
  cstr_ok tfibsegs W mem (p + Z.of_nat k) (skipn k l).
Proof.
  intros W mem p l k ((Hg & Hnz) & H4 & Hc & H32 & Ham & Hra & Hhv & Htl) Hk.
  assert (HL : Z.of_nat (length (skipn k l)) = Z.of_nat (length l) - Z.of_nat k) by (rewrite length_skipn; lia).
  unfold cstr_ok, cstr. rewrite HL.
  split; [split|].
  { intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. rewrite length_skipn in Hj.
    destruct (Hg (k + j)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [V R].
    assert (E : nth j (skipn k l ++ [0]) 0 = nth (k + j) (l ++ [0]) 0).
    { assert (S0 : skipn k (l ++ [0]) = skipn k l ++ [0])
        by (rewrite skipn_app; replace (k - length l)%nat with 0%nat by lia; reflexivity).
      rewrite <- S0, lp_nth_skipn. reflexivity. }
    rewrite E. split; [|exact R]. replace (p + Z.of_nat k + Z.of_nat j) with (p + Z.of_nat (k + j)) by lia. exact V. }
  { clear -Hnz. revert l Hnz. induction k as [|k IH]; intros l H; [exact H|].
    destruct l as [|x l]; [constructor|]. inversion H; subst. cbn [skipn]. apply IH. assumption. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split.
  { intros x Hx. apply Hra. lia. }
  split.
  { intros s Hs. apply Hhv.
    assert (Hsa : shadow_addr p <= shadow_addr (p + Z.of_nat k)).
    { unfold shadow_addr. pose proof (Z.div_le_mono p (p + Z.of_nat k) 8 ltac:(lia) ltac:(lia)). lia. }
    pose proof (lp_div8_mono _ _ Hsa) as M.
    replace (p + (Z.of_nat (length l) + 1) - 1) with (p + Z.of_nat k + (Z.of_nat (length l) - Z.of_nat k + 1) - 1)
      by lia.
    lia. }
  intros a Ha. apply Htl.
  replace (p + Z.of_nat (length l)) with (p + Z.of_nat k + (Z.of_nat (length l) - Z.of_nat k)) by lia. exact Ha.
Qed.

(* a frame helper: membership bounds of a literal list's first components *)
Lemma lp_fst_bound : forall (l : list (Z * Z)) lo hi,
  forallb (fun s => (lo <=? fst s) && (fst s <=? hi)) l = true -> forall s, In s l -> lo <= fst s <= hi.
Proof.
  intros l lo hi H s Hs. rewrite forallb_forall in H. specialize (H s Hs). apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1, H2. lia.
Qed.
End m.

(* ---- the symbolic states ---- *)
Definition LP_Bx : sv := SOff 8 0.
Definition LP_Bspan : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).
(* L, 0x81d18: the "prefix" slot (F + 0x58) and the byte at at = s8 (atom 32) *)
Definition lpL_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x58 0x60 0x58 0x58 [YP09.mkChunk 0x58 (CVal 8 (SLit RD_PREFIX))].
Definition lpL_byte : YP09.region := YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition ss_lpL : sstate :=
  mkSS RD_L sr_atoms [lpL_frame; lpL_byte] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
              (24%nat, mkAF 4096 (2 ^ 47 - 16) 0); (32%nat, mkAF 0 255 0)] [] []).
Definition LP_SHL : list shent := [mkSHE 24 0 1].
(* C7 (0x81d64, after strncasecmp): the text slot (F + 0x40, atom 32), the byte at at - 1 (atom 33) when i > 0 *)
Definition LP_C50 : Z := 0x81d50.
Definition LP_C7c : Z := 0x81d7c.
Definition lpC_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x40 0x48 0x40 0x40 [YP09.mkChunk 0x40 (CVal 8 (SOff 32 0))].
Definition lpC_bytem1 : YP09.region :=
  YP09.mkRegion (Some 24%nat) (-1) 0 (-1) (-1) [YP09.mkChunk (-1) (CVal 1 (SOff 33 0))].
Definition lpC_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (24%nat, mkAF 4096 (2 ^ 47 - 16) 0); (32%nat, mkAF 4096 (2 ^ 47 - 16) 0); (33%nat, mkAF 0 255 0)] [] [].
Definition ss_lpC64 : sstate := mkSS RD_C7 sr_atoms [lpC_frame] None lpC_facts.
Definition lpM_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (24%nat, mkAF 4096 (2 ^ 47 - 16) 0); (33%nat, mkAF 0 255 0)] [] [].
Definition ss_lpC7c : sstate := mkSS LP_C7c sr_atoms [lpC_bytem1] None lpM_facts.
Definition LP_SHM : list shent := [mkSHE 24 (-1) 0].
(* the states with no memory of their own (0x81d4c, 0x81d50) *)
Definition ss_bare (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).


Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma lp_L_entry : forall (W : world tfibsegs) mem regs3 Fz t i c,
  getr regs3 2 = w64 Fz -> getr regs3 8 = w64 SHADOW_OFF -> getr regs3 24 = w64 (t + i) ->
  2 ^ 46 <= Fz <= 2 ^ 47 - 16 -> Fz mod 16 = 0 -> alloc_ceiling <= Fz ->
  4096 <= t -> 0 <= i -> t + i + 1 <= alloc_ceiling -> 0 <= c < 256 ->
  val_mem tfibsegs (rdW W mem) (Fz + 0x58) 8 RD_PREFIX -> val_mem tfibsegs (rdW W mem) (t + i) 1 c ->
  st_ok tfibsegs (Ereg regs3 [Z_to_bv 64 c]) ss_lpL
    (restrict (w_H W) (mkst regs3 (Z_to_bv 64 RD_L) mem (seg_rom tfibsegs))).
Proof.
  intros W mem regs3 Fz t i c R2 R8 R24 HF1 HF2 HF3 Ht Hi Hti Hc V58 Vc.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 [Z_to_bv 64 c]).
  assert (U2 : bv_unsigned (ew E 2) = Fz)
    by (unfold E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U8 : bv_unsigned (ew E 8) = SHADOW_OFF)
    by (unfold E; rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl), R8; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U24 : bv_unsigned (ew E 24) = t + i)
    by (unfold E; rewrite (ew_Ereg_nat regs3 _ 24 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 c) by (unfold E; exact (ew_Ereg_extra regs3 _ 0)).
  unfold ss_lpL. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 [Z_to_bv 64 c]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold lpL_frame, lpL_byte.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ Fz 0x58 8 (SLit RD_PREFIX) RD_PREFIX);
        [reflexivity | unfold RD_PREFIX; cbn; lia | cbn; lia | exact V58].
    + rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ (t + i) 0 1 (SOff 32 0) c);
        [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vc.
  - apply pairwise_disjoint_of_extents. unfold lpL_frame, lpL_byte, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U24.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U8, U24, E32, unsigned_lit_small by lia.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; lia.
Qed.

Lemma lp_C64_entry : forall (W : world tfibsegs) mem regs3 Fz t i cm,
  getr regs3 2 = w64 Fz -> getr regs3 8 = w64 SHADOW_OFF -> getr regs3 24 = w64 (t + i) ->
  2 ^ 46 <= Fz <= 2 ^ 47 - 16 -> Fz mod 16 = 0 -> alloc_ceiling <= Fz ->
  4096 <= t -> 0 <= i -> t + i + 1 <= alloc_ceiling -> 0 <= cm < 256 ->
  val_mem tfibsegs (rdW W mem) (Fz + 0x40) 8 t ->
  st_ok tfibsegs (Ereg regs3 [Z_to_bv 64 t; Z_to_bv 64 cm]) ss_lpC64
    (restrict (w_H W) (mkst regs3 (Z_to_bv 64 RD_C7) mem (seg_rom tfibsegs))).
Proof.
  intros W mem regs3 Fz t i cm R2 R8 R24 HF1 HF2 HF3 Ht Hi Hti Hcm V40.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 [Z_to_bv 64 t; Z_to_bv 64 cm]).
  assert (U2 : bv_unsigned (ew E 2) = Fz)
    by (unfold E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U8 : bv_unsigned (ew E 8) = SHADOW_OFF)
    by (unfold E; rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl), R8; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U24 : bv_unsigned (ew E 24) = t + i)
    by (unfold E; rewrite (ew_Ereg_nat regs3 _ 24 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 t) by (unfold E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 cm) by (unfold E; exact (ew_Ereg_extra regs3 _ 1)).
  unfold ss_lpC64. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 [Z_to_bv 64 t; Z_to_bv 64 cm]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold lpC_frame. apply Forall_cons; [|apply Forall_nil]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs E _ Fz 0x40 8 (SOff 32 0) t);
      [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact V40].
  - apply pairwise_disjoint_of_extents. unfold lpC_frame, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok lpC_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U8, U24, E32, E33, !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; lia.
Qed.

Lemma lp_C7c_entry : forall (W : world tfibsegs) mem regs3 Fz t i cm,
  getr regs3 2 = w64 Fz -> getr regs3 8 = w64 SHADOW_OFF -> getr regs3 24 = w64 (t + i) ->
  2 ^ 46 <= Fz <= 2 ^ 47 - 16 -> Fz mod 16 = 0 -> alloc_ceiling <= Fz ->
  4096 <= t -> 1 <= i -> t + i + 1 <= alloc_ceiling -> 0 <= cm < 256 ->
  val_mem tfibsegs (rdW W mem) (t + i + -1) 1 cm ->
  st_ok tfibsegs (Ereg regs3 [Z_to_bv 64 0; Z_to_bv 64 cm]) ss_lpC7c
    (restrict (w_H W) (mkst regs3 (Z_to_bv 64 LP_C7c) mem (seg_rom tfibsegs))).
Proof.
  intros W mem regs3 Fz t i cm R2 R8 R24 HF1 HF2 HF3 Ht Hi Hti Hcm Vcm.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 [Z_to_bv 64 0; Z_to_bv 64 cm]).
  assert (U2 : bv_unsigned (ew E 2) = Fz)
    by (unfold E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U8 : bv_unsigned (ew E 8) = SHADOW_OFF)
    by (unfold E; rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl), R8; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U24 : bv_unsigned (ew E 24) = t + i)
    by (unfold E; rewrite (ew_Ereg_nat regs3 _ 24 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
  assert (E33 : ew E 33 = Z_to_bv 64 cm) by (unfold E; exact (ew_Ereg_extra regs3 _ 1)).
  unfold ss_lpC7c. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 [Z_to_bv 64 0; Z_to_bv 64 cm]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold lpC_bytem1. apply Forall_cons; [|apply Forall_nil]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs E _ (t + i) (-1) 1 (SOff 33 0) cm);
      [cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact Vcm].
  - apply pairwise_disjoint_of_extents. unfold lpC_bytem1, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok lpM_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U8, U24, E33, !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; lia.
Qed.

Lemma lp_bare_entry : forall (W : world tfibsegs) mem regs3 pc,
  st_ok tfibsegs (Ereg regs3 []) (ss_bare pc)
    (restrict (w_H W) (mkst regs3 (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
  intros W mem regs3 pc. rewrite restrict_mkst_fx. unfold ss_bare. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn; tauto.
  - split; [exact I | split; [exact I | exact I]].
Qed.
End e.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma lp_base_bounds : forall cx, rd_base B CTX cx ->
  cx_sp cx mod 16 = 0 /\ alloc_ceiling + STK_readings <= cx_sp cx /\ cx_sp cx + 16 <= 2 ^ 47 /\
  getr (cx_regs cx) 3 = w64 (as_gp B) /\ getr (cx_regs cx) 4 = w64 (as_tp B).
Proof.
  intros cx HB.
  destruct HB as (HAN & _ & _ & _ & _ & _ & _ & Htopr & _).
  pose proof HAN as (_ & _ & _ & Hgp & Htp & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & _ & Htop2).
  unfold cx_sp in *. split; [exact Hal16|]. split; [lia|]. split; [lia|]. split; [exact Hgp | exact Htp].
Qed.

(* the scan's invariant across a step that keeps the registers it names and changes memory only in a runtime callee's
   window below the frame *)
Lemma lp_loop_keep : forall cx d ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  rd_base B CTX cx -> rd_loop B cx d ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 mem4 md4 EV_names ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx - STK_RT_STR <= a < cx_F cx) ->
     aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  rd_loop B cx d ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx d ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HB HLP HJ4 HAV Q2 Q3 Q4 Q8 Q9 Q18.
  pose proof (lp_base_bounds cx HB) as (Hal & Hsplo & Hsphi & _ & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FFR : STK_readings = 16624) by reflexivity.
  assert (FRS : STK_RT_STR = 8192) by reflexivity.
  destruct HLP as (HC & R9 & R18 & HSL & Vrp & HPm & HG & Hcf & Hub & Hwh & Hd).
  destruct HC as (HJ & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
  assert (LOW : g3_low_kept W3 W3 mem3 mem4) by (intros a Ha; apply HAV; unfold cx_F; lia).
  assert (HI : forall a v, val_mem tfibsegs (rdW W3 mem3) a 8 v -> cx_F cx <= a -> a + 8 <= 2 ^ 64 ->
     val_mem tfibsegs (rdW W3 mem4) a 8 v).
  { intros a v Hv Ha Hn. apply (g3_val_mem_kept W3 W3 mem3 mem4 a 8 v Hv). intros j Hj.
    change (Z.of_nat 8) with 8 in Hj. apply HAV; unfold cx_F in *; lia. }
  split.
  { split; [change (unpoison [] mem4) with mem4; exact HJ4|].
    split; [unfold EV_names; lia|].
    split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. split; [rewrite Q4; exact R4|].
    split; [rewrite Q8; exact R8|].
    split.
    { unfold rd_saved_ok in *. rewrite Forall_forall in HSV |- *. intros s Hs.
      pose proof (lp_fst_bound RD_SAVED 104 200 ltac:(vm_compute; reflexivity) s Hs) as Hb.
      apply HI; [exact (HSV s Hs) | unfold cx_F in *; lia | unfold cx_F in *; lia]. }
    split.
    { intros a Ha. rewrite HAV by (unfold cx_F; lia). exact (K16 a Ha). }
    split; [exact (g3_arodata_kept B W3 W3 mem3 mem4 HRO LOW)|].
    split; [exact (g3_cstr_ok_kept W3 W3 mem3 mem4 _ _ Ct LOW)|].
    split; [exact (g3_cstr_ok_kept W3 W3 mem3 mem4 _ _ Cu LOW)|].
    split; [exact Kt | exact Ku]. }
  split; [rewrite Q9; exact R9|]. split; [rewrite Q18; exact R18|].
  split.
  { unfold rd_slots_ok in *. rewrite Forall_forall in HSL |- *. intros s Hs.
    pose proof (lp_fst_bound (rd_loc_list cx d) 0 0x60 ltac:(unfold rd_loc_list; vm_compute; reflexivity) s Hs)
      as Hb.
    destruct (HSL s Hs) as [Hv Hr]. split; [|exact Hr].
    apply HI; [exact Hv | unfold cx_F in *; lia | unfold cx_F in *; lia]. }
  split; [apply HI; [exact Vrp | unfold cx_F; lia | lia]|].
  split; [exact HPm|]. split; [exact (g3_fm_glob_kept W3 W3 mem3 mem4 _ _ _ _ HG LOW)|].
  exact (conj Hcf (conj Hub (conj Hwh Hd))).
Qed.

(* ---- the three exits: R (res 0 at the text's NUL), L at i + 1, P ---- *)
Lemma lp_R_exit : forall cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 md4,
  rd_base B CTX cx -> rd_loop B cx d ly3 S3 W3 regs3 mem3 md3 -> rd_acc cx i d (S f) ->
  byte_at (cx_tb cx) i = 0 ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 mem3 md4 EV_names ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  getr regs4 21 = w64 0 ->
  SRr tfibsegs W3 (cfg_at tfibsegs RD_R regs4 mem3 md4) (rd_post B cx).
Proof.
  intros cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 md4 HB HLP HACC Hb0 HJ4 Q2 Q3 Q4 Q8 Q9 Q18 Q21.
  pose proof (lp_loop_keep cx d ly3 S3 W3 regs3 mem3 md3 regs4 mem3 md4 HB HLP HJ4 (fun a _ _ => eq_refl)
    Q2 Q3 Q4 Q8 Q9 Q18) as HL4.
  destruct HL4 as (HC & _ & _ & _ & Vrp & HPm & HG & Hcf & Hub & _).
  destruct HACC as (Hi & _ & Hnm & Hnr).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ct & _).
  pose proof (lp_byte_end _ _ _ _ i Ct Hi Hb0) as Hend.
  destruct (lp_sc_end (cx_tb cx) (cx_ub cx) i d f ltac:(lia)) as [Es Er].
  apply (rd_ret_holds B CTX cx EV_names ly3 S3 W3 regs4 mem3 md4 0 HB HC Q21 ltac:(lia)).
  split; [exact HPm|]. split.
  { right; right. split; [exact Hub|]. split; [exact Hcf|]. split; [rewrite Hnm, Es; reflexivity|]. exact HG. }
  replace ((length (cx_ub cx) =? 0)%nat) with false
    by (symmetry; apply Nat.eqb_neq; intros H; apply Hub; apply length_zero_iff_nil; exact H).
  replace (cx_cnt cx =? cx_fail cx) with false by (symmetry; apply Z.eqb_neq; exact Hcf).
  cbn [orb]. rewrite Hnr, Er, Nat.add_0_r. exact Vrp.
Qed.

Lemma lp_L_exit : forall f, rd_seg_L B CTX f -> forall cx i d ly3 S3 W3 regs3 mem3 md3 regs4 md4,
  rd_base B CTX cx -> rd_loop B cx d ly3 S3 W3 regs3 mem3 md3 -> rd_acc cx i d (S f) ->
  (i < length (cx_tb cx))%nat -> head (cx_tb cx) i = None ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 mem3 md4 EV_names ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  getr regs4 20 = w64 64 -> getr regs4 24 = w64 (cx_t cx + Z.of_nat (S i)) ->
  SRr tfibsegs W3 (cfg_at tfibsegs RD_L regs4 mem3 md4) (rd_post B cx).
Proof.
  intros f HL cx i d ly3 S3 W3 regs3 mem3 md3 regs4 md4 HB HLP HACC Hi Hh HJ4 Q2 Q3 Q4 Q8 Q9 Q18 Q20 Q24.
  apply (HL cx (S i) d ly3 S3 W3 regs4 mem3 md4 HB).
  split; [exact (lp_loop_keep cx d ly3 S3 W3 regs3 mem3 md3 regs4 mem3 md4 HB HLP HJ4 (fun a _ _ => eq_refl)
    Q2 Q3 Q4 Q8 Q9 Q18)|].
  split; [|split; [exact Q20 | exact Q24]].
  destruct HACC as (Hle & Hf & Hnm & Hnr).
  destruct (lp_sc_none (cx_tb cx) (cx_ub cx) i d f Hi Hh) as [Es Er].
  split; [lia|]. split; [lia|]. split; [rewrite Hnm; exact Es|]. rewrite Hnr, Er. reflexivity.
Qed.

Lemma lp_P_exit : forall f, rd_seg_P B CTX (S f) -> forall cx i d s11 ly3 S3 W3 regs3 mem3 md3 regs4 md4,
  rd_base B CTX cx -> rd_loop B cx d ly3 S3 W3 regs3 mem3 md3 -> rd_acc cx i d (S f) ->
  (i < length (cx_tb cx))%nat -> head (cx_tb cx) i = Some (i + s11)%nat -> (s11 = 6 \/ s11 = 7)%nat ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 mem3 md4 EV_names ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  getr regs4 19 = w64 58 -> getr regs4 20 = w64 64 -> getr regs4 24 = w64 (cx_t cx + Z.of_nat i) ->
  getr regs4 27 = w64 (Z.of_nat s11) ->
  SRr tfibsegs W3 (cfg_at tfibsegs RD_P regs4 mem3 md4) (rd_post B cx).
Proof.
  intros f HP cx i d s11 ly3 S3 W3 regs3 mem3 md3 regs4 md4 HB HLP HACC Hi Hh H11 HJ4 Q2 Q3 Q4 Q8 Q9 Q18
    Q19 Q20 Q24 Q27.
  apply (HP cx i d s11 ly3 S3 W3 regs4 mem3 md4 HB).
  split; [exact (lp_loop_keep cx d ly3 S3 W3 regs3 mem3 md3 regs4 mem3 md4 HB HLP HJ4 (fun a _ _ => eq_refl)
    Q2 Q3 Q4 Q8 Q9 Q18)|].
  exact (conj HACC (conj Hi (conj Hh (conj H11 (conj Q19 (conj Q20 (conj Q24 Q27))))))).
Qed.
End k.

(* ---- the walk's tactics ---- *)
(* the value a register holds after a run, in terms of the cut's registers *)
Ltac lp_gr HS r0 :=
  let r := constr:(r0 : bv 5) in
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E ss ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end;
  cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
Ltac lp_g HS := lazymatch goal with |- getr _ ?r = _ => lp_gr HS r end.
Ltac lp_q HS EE n r := lp_g HS; exact (EE n (r : bv 5) eq_refl).
Ltac lp_qv HS EE n r Hr := lp_g HS; rewrite (EE n (r : bv 5) eq_refl); exact Hr.

(* every region of this walk is read only, so a run may write nothing *)
Ltac lp_awr :=
  lazymatch goal with |- awr_ok ?sg ?BB ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg BB E rs' stk sp0 fp b0 bc ly own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* a run of this walk writes nothing: its memory is the cut's *)
Ltac lp_mem m0 :=
  lazymatch goal with H : frame_of ?Ex ?rs ?mp (ms_mem ?m1) |- _ =>
    let Hm := fresh "Hmem" in
    assert (Hm : ms_mem m1 = m0) by
      (rewrite (frame_of_read_only Ex rs mp (ms_mem m1) ltac:(vm_compute; reflexivity) H);
       first [reflexivity | assumption]) end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the machine state of the goal, as mkst at a literal pc, over the cut's memory *)
Ltac lp_mk HS :=
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end;
  repeat match goal with Hm : ms_mem ?x = _ |- _ => rewrite Hm in * end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRNCMP : astrncmp_realizes tfibsegs B PC_strncmp.
Hypothesis STRNCASECMP : astrncasecmp_realizes tfibsegs B PC_strncasecmp.

(* 0x81d7c (lv2_locate.c:112): a "PREFIX" head at i > 0, so the byte before at decides *)
Lemma lp_C7c : forall f, rd_seg_L B CTX f -> rd_seg_P B CTX (S f) ->
  forall cx i d ly3 S3 W3 regs3 mem3 md3 regs4 md4,
  rd_base B CTX cx -> rd_loop B cx d ly3 S3 W3 regs3 mem3 md3 -> rd_acc cx i d (S f) ->
  (i < length (cx_tb cx))%nat -> (0 < i)%nat ->
  head (cx_tb cx) i = (if is_space (byte_at (cx_tb cx) (i - 1)) then Some (i + 6)%nat else None) ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 mem3 md4 EV_names ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  getr regs4 19 = w64 58 -> getr regs4 20 = w64 64 -> getr regs4 24 = w64 (cx_t cx + Z.of_nat i) ->
  getr regs4 27 = w64 6 ->
  SRr tfibsegs W3 (cfg_at tfibsegs LP_C7c regs4 mem3 md4) (rd_post B cx).
Proof.
intros f HL HP cx i d ly3 S3 W3 regs3 mem3 md3 regs4 md4 HB HLP HACC HiL Hi0 HH HJ4
  P2 P3 P4 P8 P9 P18 R19 R20 R24 R27.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFR : STK_readings = 16624) by reflexivity.
assert (FRS : STK_RT_STR = 8192) by reflexivity.
pose proof (lp_base_bounds B CTX cx HB) as (Hal & Hsplo & Hsphi & Hgp & Htp).
pose proof (lp_loop_keep B CTX cx d ly3 S3 W3 regs3 mem3 md3 regs4 mem3 md4 HB HLP HJ4
  (fun a _ _ => eq_refl) P2 P3 P4 P8 P9 P18) as HLP4.
pose proof HLP4 as (HC & R9 & R18 & HSL & Vrp & HPm & HG & Hcf & Hub & Hwh & Hd).
pose proof HC as (HJ & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HACC as (Hi & Hf & Hnm & Hnr).
pose proof Ct as (_ & Ht4 & Htc & _ & Ham & HRA & _).
assert (HFm : cx_F cx mod 16 = 0).
{ unfold cx_F. replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia. rewrite Z_mod_plus_full. exact Hal. }
pose proof (lp_byte_val W3 mem3 (cx_t cx) (cx_tb cx) (i - 1)%nat Ct ltac:(lia)) as (Vcm & Hcm).
set (cm := byte_at (cx_tb cx) (i - 1)%nat) in *.
pose proof (lp_C7c_entry W3 mem3 regs4 (cx_F cx) (cx_t cx) (Z.of_nat i) cm R2 R8 R24
  ltac:(unfold cx_F; lia) HFm ltac:(unfold cx_F; lia) Ht4 ltac:(lia) ltac:(lia) Hcm
  ltac:(replace (cx_t cx + Z.of_nat i + -1) with (cx_t cx + Z.of_nat (i - 1)) by lia; exact Vcm)) as HS.
remember (Ereg regs4 [Z_to_bv 64 0; Z_to_bv 64 cm]) as E eqn:HE.
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs4 q)
  by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
assert (E33 : ew E 33 = Z_to_bv 64 cm) by (rewrite HE; exact (ew_Ereg_extra regs4 _ 1)).
clear HE.
assert (SHOK : sh_ok tfibsegs LP_Bx LP_SHM E
  (mrestrict (w_H W3) (ms_mem (mkst regs4 (Z_to_bv 64 LP_C7c) mem3 (seg_rom tfibsegs))))).
{ constructor; [|constructor]. cbn [ms_mem].
  apply (shent_ok_of_range tfibsegs (w_H W3) mem3 E LP_Bx 24 (cx_t cx) (Z.of_nat (length (cx_tb cx)) + 1)
    (cx_t cx + Z.of_nat i) (-1) 0 HRA).
  - unfold LP_Bx. apply U_atom; [rewrite (EE 8%nat 8%bv eq_refl); exact R8 | unfold SHADOW_OFF; lia].
  - apply U_atom; [rewrite (EE 24%nat 24%bv eq_refl); exact R24 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Ham. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 LP_C7c) with (Z_to_bv 64 LP_C7c).
change (unpoison [] mem3) with mem3 in HJ.
change mem3 with (ms_mem (mkst regs4 (Z_to_bv 64 LP_C7c) mem3 (seg_rom tfibsegs))) in HJ.
aj_run_tok rd_tbl_ok HS HJ SHOK LP_Bspan.
{ lp_awr. }
lp_mem mem3.
srr_branch_tok rd_tbl_ok HS SHOK LP_Bspan.
{ (* 9 <= at[-1] <= 13: a space, so the head holds *)
  rewrite branch_ltu_U in Hc.
  rewrite (lp_U_off _ 33 (-9) cm) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E33 | lia]).
  rewrite (U_atom _ 18 5) in Hc
    by (first [cbn [ew ewset Nat.eqb]; rewrite (EE 18%nat 18%bv eq_refl); exact R18 | lia]).
  rewrite (lp_sp_ltu cm Hcm) in Hc.
  assert (HSP : is_space cm = true) by (unfold is_space; rewrite Hc; apply orb_true_r).
  aj_run_to_tok rd_tbl_ok HS HJ SHOK LP_Bspan RD_P.
  { lp_awr. }
  lp_mem mem3. lp_mk HS.
  eapply (lp_P_exit B CTX f HP cx i d 6%nat ly3 S3 W3 regs4 mem3 md4);
    [ exact HB | exact HLP4 | exact HACC | exact HiL | rewrite HH, HSP; reflexivity | left; reflexivity
    | exact HJ
    | lp_q HS EE 2%nat (2%bv : bv 5) | lp_q HS EE 3%nat (3%bv : bv 5) | lp_q HS EE 4%nat (4%bv : bv 5) | lp_q HS EE 8%nat (8%bv : bv 5)
    | lp_q HS EE 9%nat (9%bv : bv 5) | lp_q HS EE 18%nat (18%bv : bv 5)
    | lp_qv HS EE 19%nat (19%bv : bv 5) R19 | lp_qv HS EE 20%nat (20%bv : bv 5) R20 | lp_qv HS EE 24%nat (24%bv : bv 5) R24
    | lp_qv HS EE 27%nat (27%bv : bv 5) R27 ]. }
{ rewrite branch_ltu_U in Hc.
  rewrite (lp_U_off _ 33 (-9) cm) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E33 | lia]).
  rewrite (U_atom _ 18 5) in Hc
    by (first [cbn [ew ewset Nat.eqb]; rewrite (EE 18%nat 18%bv eq_refl); exact R18 | lia]).
  rewrite (lp_sp_ltu cm Hcm) in Hc.
  aj_run_tok rd_tbl_ok HS HJ SHOK LP_Bspan.
  { lp_awr. }
  lp_mem mem3.
  srr_branch_tok rd_tbl_ok HS SHOK LP_Bspan.
  { (* at[-1] <> ' ': no head here, the scan steps on *)
    rewrite branch_ne_U in Hc0.
    rewrite (U_atom _ 33 cm) in Hc0 by (first [cbn [ew ewset Nat.eqb]; exact E33 | lia]).
    rewrite (U_atom _ 9 32) in Hc0
      by (first [cbn [ew ewset Nat.eqb]; rewrite (EE 9%nat 9%bv eq_refl); exact R9 | lia]).
    apply Bool.negb_true_iff, Z.eqb_neq in Hc0.
    assert (HSP : is_space cm = false)
      by (unfold is_space; rewrite (proj2 (Z.eqb_neq cm 32) Hc0), Hc; reflexivity).
    aj_run_to_tok rd_tbl_ok HS HJ SHOK LP_Bspan RD_L.
    { lp_awr. }
    lp_mem mem3. lp_mk HS.
    eapply (lp_L_exit B CTX f HL cx i d ly3 S3 W3 regs4 mem3 md4);
      [ exact HB | exact HLP4 | exact HACC | exact HiL | rewrite HH, HSP; reflexivity | exact HJ
      | lp_q HS EE 2%nat (2%bv : bv 5) | lp_q HS EE 3%nat (3%bv : bv 5) | lp_q HS EE 4%nat (4%bv : bv 5) | lp_q HS EE 8%nat (8%bv : bv 5)
      | lp_q HS EE 9%nat (9%bv : bv 5) | lp_q HS EE 18%nat (18%bv : bv 5)
      | lp_qv HS EE 20%nat (20%bv : bv 5) R20
      | lp_g HS; rewrite (EE 24%nat 24%bv eq_refl), R24, unsigned_lit_small by lia;
        unfold w64; f_equal; lia ]. }
  { (* at[-1] = ' ' *)
    rewrite branch_ne_U in Hc0.
    rewrite (U_atom _ 33 cm) in Hc0 by (first [cbn [ew ewset Nat.eqb]; exact E33 | lia]).
    rewrite (U_atom _ 9 32) in Hc0
      by (first [cbn [ew ewset Nat.eqb]; rewrite (EE 9%nat 9%bv eq_refl); exact R9 | lia]).
    apply Bool.negb_false_iff, Z.eqb_eq in Hc0.
    assert (HSP : is_space cm = true) by (unfold is_space; rewrite Hc0; reflexivity).
    aj_run_to_tok rd_tbl_ok HS HJ SHOK LP_Bspan RD_P.
    { lp_awr. }
    lp_mem mem3. lp_mk HS.
    eapply (lp_P_exit B CTX f HP cx i d 6%nat ly3 S3 W3 regs4 mem3 md4);
      [ exact HB | exact HLP4 | exact HACC | exact HiL | rewrite HH, HSP; reflexivity | left; reflexivity
      | exact HJ
      | lp_q HS EE 2%nat (2%bv : bv 5) | lp_q HS EE 3%nat (3%bv : bv 5) | lp_q HS EE 4%nat (4%bv : bv 5) | lp_q HS EE 8%nat (8%bv : bv 5)
      | lp_q HS EE 9%nat (9%bv : bv 5) | lp_q HS EE 18%nat (18%bv : bv 5)
      | lp_qv HS EE 19%nat (19%bv : bv 5) R19 | lp_qv HS EE 20%nat (20%bv : bv 5) R20 | lp_qv HS EE 24%nat (24%bv : bv 5) R24
      | lp_qv HS EE 27%nat (27%bv : bv 5) R27 ]. } }
Qed.

(* 0x81d64: strncasecmp (at, "PREFIX", 6) answered v (lv2_locate.c:111) *)
Lemma lp_C64 : forall f, rd_seg_L B CTX f -> rd_seg_P B CTX (S f) ->
  forall cx i d v ly3 S3 W3 regs3 mem3 md3 regs4 md4,
  rd_base B CTX cx -> rd_loop B cx d ly3 S3 W3 regs3 mem3 md3 -> rd_acc cx i d (S f) ->
  (i < length (cx_tb cx))%nat ->
  head (cx_tb cx) i = (if ci_eqb (firstn 6 (skipn i (cx_tb cx))) prefix_lc &&
                          match i with O => true | S i' => is_space (byte_at (cx_tb cx) i') end
                       then Some (i + 6)%nat else None) ->
  (v = 0 <-> ci_eqb (firstn 6 (skipn i (cx_tb cx))) prefix_lc = true) ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 mem3 md4 EV_names ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  getr regs4 10 = w64 v -> 0 <= v < 2 ^ 64 ->
  getr regs4 19 = w64 58 -> getr regs4 20 = w64 64 -> getr regs4 24 = w64 (cx_t cx + Z.of_nat i) ->
  SRr tfibsegs W3 (cfg_at tfibsegs RD_C7 regs4 mem3 md4) (rd_post B cx).
Proof.
intros f HL HP cx i d v ly3 S3 W3 regs3 mem3 md3 regs4 md4 HB HLP HACC HiL HH Hv HJ4
  P2 P3 P4 P8 P9 P18 R10 Hv64 R19 R20 R24.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFR : STK_readings = 16624) by reflexivity.
assert (FRS : STK_RT_STR = 8192) by reflexivity.
pose proof (lp_base_bounds B CTX cx HB) as (Hal & Hsplo & Hsphi & Hgp & Htp).
pose proof (lp_loop_keep B CTX cx d ly3 S3 W3 regs3 mem3 md3 regs4 mem3 md4 HB HLP HJ4
  (fun a _ _ => eq_refl) P2 P3 P4 P8 P9 P18) as HLP4.
pose proof HLP4 as (HC & R9 & R18 & HSL & Vrp & HPm & HG & Hcf & Hub & Hwh & Hd).
pose proof HC as (HJ & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HACC as (Hi & Hf & Hnm & Hnr).
pose proof Ct as (_ & Ht4 & Htc & _ & Ham & HRA & _).
assert (HFm : cx_F cx mod 16 = 0).
{ unfold cx_F. replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia. rewrite Z_mod_plus_full. exact Hal. }
pose proof (proj1 (Forall_forall _ _) HSL (0x40, cx_t cx)
  ltac:(unfold rd_loc_list; cbn [In]; repeat (first [left; reflexivity | right]))) as (V40 & _).
cbn [fst snd] in V40.
set (cm := match i with O => 0 | S i' => byte_at (cx_tb cx) i' end).
assert (Hcm : 0 <= cm < 256).
{ unfold cm. destruct i as [|i']; [lia|].
  exact (proj2 (lp_byte_val W3 mem3 (cx_t cx) (cx_tb cx) i' Ct ltac:(lia))). }
pose proof (lp_C64_entry W3 mem3 regs4 (cx_F cx) (cx_t cx) (Z.of_nat i) cm R2 R8 R24
  ltac:(unfold cx_F; lia) HFm ltac:(unfold cx_F; lia) Ht4 ltac:(lia) ltac:(lia) Hcm V40) as HS.
remember (Ereg regs4 [Z_to_bv 64 (cx_t cx); Z_to_bv 64 cm]) as E eqn:HE.
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs4 q)
  by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (cx_t cx)) by (rewrite HE; exact (ew_Ereg_extra regs4 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cm) by (rewrite HE; exact (ew_Ereg_extra regs4 _ 1)).
clear HE.
assert (SHOK : sh_ok tfibsegs LP_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs4 (Z_to_bv 64 RD_C7) mem3 (seg_rom tfibsegs))))) by constructor.
unfold cfg_at. change (w64 RD_C7) with (Z_to_bv 64 RD_C7).
change (unpoison [] mem3) with mem3 in HJ.
change mem3 with (ms_mem (mkst regs4 (Z_to_bv 64 RD_C7) mem3 (seg_rom tfibsegs))) in HJ.
srr_branch_tok rd_tbl_ok HS SHOK LP_Bspan.
{ (* strncasecmp = 0: "PREFIX" at at *)
  rewrite branch_eq_U in Hc.
  rewrite (U_atom _ 10 v) in Hc by (first [cbn [ew ewset Nat.eqb]; rewrite (EE 10%nat 10%bv eq_refl); exact R10 | lia]).
  rewrite U_SLit, zcanon_id in Hc by (unfold M64; lia).
  apply Z.eqb_eq in Hc. rewrite (proj1 Hv Hc) in HH. cbn [andb] in HH.
  aj_run_tok rd_tbl_ok HS HJ SHOK LP_Bspan.
  { lp_awr. }
  lp_mem mem3.
  srr_branch_tok rd_tbl_ok HS SHOK LP_Bspan.
  { (* at = text: the head is at the text's start *)
    rewrite branch_eq_U in Hc0.
    rewrite (U_atom _ 24 (cx_t cx + Z.of_nat i)) in Hc0
      by (first [cbn [ew ewset Nat.eqb]; rewrite (EE 24%nat 24%bv eq_refl); exact R24 | lia]).
    rewrite (U_atom _ 32 (cx_t cx)) in Hc0 by (first [cbn [ew ewset Nat.eqb]; exact E32 | lia]).
    apply Z.eqb_eq in Hc0.
    assert (Hi0 : i = O) by lia. subst i. cbn [andb] in HH.
    aj_run_to_tok rd_tbl_ok HS HJ SHOK LP_Bspan RD_P.
    { lp_awr. }
    lp_mem mem3. lp_mk HS.
    eapply (lp_P_exit B CTX f HP cx O d 6%nat ly3 S3 W3 regs4 mem3 md4);
      [ exact HB | exact HLP4 | exact HACC | exact HiL | exact HH | left; reflexivity | exact HJ
      | lp_q HS EE 2%nat (2%bv : bv 5) | lp_q HS EE 3%nat (3%bv : bv 5) | lp_q HS EE 4%nat (4%bv : bv 5) | lp_q HS EE 8%nat (8%bv : bv 5)
      | lp_q HS EE 9%nat (9%bv : bv 5) | lp_q HS EE 18%nat (18%bv : bv 5)
      | lp_qv HS EE 19%nat (19%bv : bv 5) R19 | lp_qv HS EE 20%nat (20%bv : bv 5) R20
      | lp_g HS; rewrite (EE 24%nat (24%bv : bv 5) eq_refl), R24; unfold w64; f_equal; lia
      | lp_g HS; reflexivity ]. }
  { (* at <> text: the byte before at decides *)
    rewrite branch_eq_U in Hc0.
    rewrite (U_atom _ 24 (cx_t cx + Z.of_nat i)) in Hc0
      by (first [cbn [ew ewset Nat.eqb]; rewrite (EE 24%nat 24%bv eq_refl); exact R24 | lia]).
    rewrite (U_atom _ 32 (cx_t cx)) in Hc0 by (first [cbn [ew ewset Nat.eqb]; exact E32 | lia]).
    apply Z.eqb_neq in Hc0.
    assert (Hi0 : (0 < i)%nat) by lia.
    assert (HH7 : head (cx_tb cx) i = if is_space (byte_at (cx_tb cx) (i - 1)) then Some (i + 6)%nat else None).
    { rewrite HH. destruct i as [|i']; [lia|]. replace (S i' - 1)%nat with i' by lia. reflexivity. }
    aj_run_to_tok rd_tbl_ok HS HJ SHOK LP_Bspan LP_C7c.
    { lp_awr. }
    lp_mem mem3. lp_mk HS.
    eapply (lp_C7c f HL HP cx i d ly3 S3 W3 regs4 mem3 md4);
      [ exact HB | exact HLP4 | exact HACC | exact HiL | exact Hi0 | exact HH7 | exact HJ
      | lp_q HS EE 2%nat (2%bv : bv 5) | lp_q HS EE 3%nat (3%bv : bv 5) | lp_q HS EE 4%nat (4%bv : bv 5) | lp_q HS EE 8%nat (8%bv : bv 5)
      | lp_q HS EE 9%nat (9%bv : bv 5) | lp_q HS EE 18%nat (18%bv : bv 5)
      | lp_qv HS EE 19%nat (19%bv : bv 5) R19 | lp_qv HS EE 20%nat (20%bv : bv 5) R20 | lp_qv HS EE 24%nat (24%bv : bv 5) R24
      | lp_g HS; reflexivity ]. } }
{ (* strncasecmp <> 0: no head here *)
  rewrite branch_eq_U in Hc.
  rewrite (U_atom _ 10 v) in Hc by (first [cbn [ew ewset Nat.eqb]; rewrite (EE 10%nat 10%bv eq_refl); exact R10 | lia]).
  rewrite U_SLit, zcanon_id in Hc by (unfold M64; lia).
  apply Z.eqb_neq in Hc.
  assert (Hci : ci_eqb (firstn 6 (skipn i (cx_tb cx))) prefix_lc = false).
  { apply Bool.not_true_is_false. intros Eci. exact (Hc (proj2 Hv Eci)). }
  rewrite Hci in HH. cbn [andb] in HH.
  aj_run_to_tok rd_tbl_ok HS HJ SHOK LP_Bspan RD_L.
  { lp_awr. }
  lp_mem mem3. lp_mk HS.
  eapply (lp_L_exit B CTX f HL cx i d ly3 S3 W3 regs4 mem3 md4);
    [ exact HB | exact HLP4 | exact HACC | exact HiL | exact HH | exact HJ
    | lp_q HS EE 2%nat (2%bv : bv 5) | lp_q HS EE 3%nat (3%bv : bv 5) | lp_q HS EE 4%nat (4%bv : bv 5) | lp_q HS EE 8%nat (8%bv : bv 5)
    | lp_q HS EE 9%nat (9%bv : bv 5) | lp_q HS EE 18%nat (18%bv : bv 5)
    | lp_qv HS EE 20%nat (20%bv : bv 5) R20
    | lp_g HS; rewrite (EE 24%nat 24%bv eq_refl), R24, unsigned_lit_small by lia;
      unfold w64; f_equal; lia ]. }
Qed.

(* 0x81d50: the call strncasecmp (at, "PREFIX", 6) *)
Lemma lp_C50 : forall f, rd_seg_L B CTX f -> rd_seg_P B CTX (S f) ->
  forall cx i d ly3 S3 W3 regs3 mem3 md3 regs4 md4,
  rd_base B CTX cx -> rd_loop B cx d ly3 S3 W3 regs3 mem3 md3 -> rd_acc cx i d (S f) ->
  (i < length (cx_tb cx))%nat ->
  head (cx_tb cx) i = (if ci_eqb (firstn 6 (skipn i (cx_tb cx))) prefix_lc &&
                          match i with O => true | S i' => is_space (byte_at (cx_tb cx) i') end
                       then Some (i + 6)%nat else None) ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 mem3 md4 EV_names ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  getr regs4 19 = w64 58 -> getr regs4 20 = w64 64 -> getr regs4 24 = w64 (cx_t cx + Z.of_nat i) ->
  SRr tfibsegs W3 (cfg_at tfibsegs LP_C50 regs4 mem3 md4) (rd_post B cx).
Proof.
intros f HL HP cx i d ly3 S3 W3 regs3 mem3 md3 regs4 md4 HB HLP HACC HiL HH HJ4
  P2 P3 P4 P8 P9 P18 R19 R20 R24.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFR : STK_readings = 16624) by reflexivity.
assert (FRS : STK_RT_STR = 8192) by reflexivity.
pose proof (lp_base_bounds B CTX cx HB) as (Hal & Hsplo & Hsphi & Hgp & Htp).
pose proof (lp_loop_keep B CTX cx d ly3 S3 W3 regs3 mem3 md3 regs4 mem3 md4 HB HLP HJ4
  (fun a _ _ => eq_refl) P2 P3 P4 P8 P9 P18) as HLP4.
pose proof HLP4 as (HC & R9 & R18 & HSL & Vrp & HPm & HG & Hcf & Hub & Hwh & Hd).
pose proof HC as (HJ & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HACC as (Hi & Hf & Hnm & Hnr).
pose proof Ct as (_ & Ht4 & Htc & _ & Ham & HRA & _).
pose proof (lp_bare_entry W3 mem3 regs4 LP_C50) as HS.
remember (Ereg regs4 (@nil word)) as E eqn:HE.
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs4 q)
  by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
clear HE.
assert (SHOK : sh_ok tfibsegs LP_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs4 (Z_to_bv 64 LP_C50) mem3 (seg_rom tfibsegs))))) by constructor.
unfold cfg_at. change (w64 LP_C50) with (Z_to_bv 64 LP_C50).
change (unpoison [] mem3) with mem3 in HJ.
change mem3 with (ms_mem (mkst regs4 (Z_to_bv 64 LP_C50) mem3 (seg_rom tfibsegs))) in HJ.
aj_run_tok rd_tbl_ok HS HJ SHOK LP_Bspan.
{ lp_awr. }
lp_mem mem3. lp_mk HS.
(* the call's premises *)
pose proof (proj1 HJ) as HAR3.
destruct (IMG ly3 S3 W3 mem3 _ HAR3 HRO) as (HROM & HROO & Hcan & HFRS & Hfmt).
pose proof (proj1 (Forall_forall _ _) HFRS (RD_PREFIXU, LP_PREU)
  ltac:(unfold FM_RO_STRS, RD_PREFIXU, LP_PREU; cbn [In]; repeat (first [left; reflexivity | right])))
  as (Cpre & _).
cbn [fst snd] in Cpre.
pose proof (lp_cstr_ok_suffix W3 mem3 (cx_t cx) (cx_tb cx) i Ct ltac:(lia)) as Csuf.
eapply SRr_bind.
{ eapply (g3_aj_ro_at B LAWS PC_strncasecmp STK_RT_STR
    (fun r => r = 0 <-> strncase_eq (Z.to_nat 6) (skipn i (cx_tb cx)) LP_PREU)
    W3 _ _ (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 _ EV_names (-224) (Z_to_bv 64 RD_C7));
  [ exact HJ
  | unfold spZ; lp_gr HS (2%bv : bv 5); rewrite (EE 2%nat 2%bv eq_refl), R2, unsigned_lit_small by (unfold cx_F; lia);
    unfold cx_F; lia
  | reflexivity | lia | unfold ESTACK; lia | lia
  | lp_gr HS (3%bv : bv 5); rewrite (EE 3%nat 3%bv eq_refl), R3; exact Hgp
  | lp_gr HS (4%bv : bv 5); rewrite (EE 4%nat 4%bv eq_refl), R4; exact Htp
  | lp_gr HS (1%bv : bv 5); reflexivity
  | unfold YK0s.ret_ok; vm_compute; reflexivity
  | ].
  intros HPK.
  apply (STRNCASECMP ly3 S3 W3 _ _ _ (cx_t cx + Z.of_nat i) RD_PREFIXU 6 (skipn i (cx_tb cx)) LP_PREU HPK
    HROM HROO);
  [ lp_gr HS (10%bv : bv 5); rewrite (EE 24%nat 24%bv eq_refl); exact R24
  | lp_gr HS (11%bv : bv 5); reflexivity
  | lp_gr HS (12%bv : bv 5); reflexivity
  | lia | exact Csuf | exact Cpre ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & H10v & Hv64 & HR & Hfr2 & Hpres2).
assert (Hvz : v = 0 <-> ci_eqb (firstn 6 (skipn i (cx_tb cx))) prefix_lc = true).
{ rewrite HR. change (Z.to_nat 6) with 6%nat. apply lp_strncase6.
  pose proof (lp_cstr_pos W3 mem3 (cx_t cx + Z.of_nat i) (skipn i (cx_tb cx)) Csuf) as HPos.
  revert HPos. apply Forall_impl. intros a Ha. lia. }
assert (HAV : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx - STK_RT_STR <= a < cx_F cx) ->
  aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) mem3 a)
  by (intros a Ha Hn; apply Hfr2; [exact Ha | unfold cx_F in *; lia]).
assert (QQ : forall r : bv 5, In r [2; 3; 4; 8; 9; 18]%bv -> getr regs2 r = getr regs4 r).
{ intros r Hr. cbv [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
  - etransitivity; [exact (HP2 2 ltac:(unfold acallee_saved; lia))|]; lp_q HS EE 2%nat (2%bv : bv 5).
  - etransitivity; [exact (HP2 3 ltac:(unfold acallee_saved; lia))|]; lp_q HS EE 3%nat (3%bv : bv 5).
  - etransitivity; [exact (HP2 4 ltac:(unfold acallee_saved; lia))|]; lp_q HS EE 4%nat (4%bv : bv 5).
  - etransitivity; [exact (HP2 8 ltac:(unfold acallee_saved; lia))|]; lp_q HS EE 8%nat (8%bv : bv 5).
  - etransitivity; [exact (HP2 9 ltac:(unfold acallee_saved; lia))|]; lp_q HS EE 9%nat (9%bv : bv 5).
  - etransitivity; [exact (HP2 18 ltac:(unfold acallee_saved; lia))|]; lp_q HS EE 18%nat (18%bv : bv 5). }
pose proof (lp_loop_keep B CTX cx d ly3 S3 W3 regs4 mem3 md4 regs2 mem2 md2 HB HLP4 HJ2 HAV
  (QQ 2%bv ltac:(cbv; tauto)) (QQ 3%bv ltac:(cbv; tauto)) (QQ 4%bv ltac:(cbv; tauto))
  (QQ 8%bv ltac:(cbv; tauto)) (QQ 9%bv ltac:(cbv; tauto)) (QQ 18%bv ltac:(cbv; tauto))) as HLP2.
eapply (lp_C64 f HL HP cx i d v ly3 S3 W3 regs2 mem2 md2 regs2 md2);
  [ exact HB | exact HLP2 | exact HACC | exact HiL | exact HH | exact Hvz | exact HJ2
  | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
  | exact H10v | exact Hv64
  | etransitivity; [exact (HP2 19 ltac:(unfold acallee_saved; lia))|]; lp_qv HS EE 19%nat (19%bv : bv 5) R19
  | etransitivity; [exact (HP2 20 ltac:(unfold acallee_saved; lia))|]; lp_qv HS EE 20%nat (20%bv : bv 5) R20
  | etransitivity; [exact (HP2 24 ltac:(unfold acallee_saved; lia))|]; lp_qv HS EE 24%nat (24%bv : bv 5) R24 ].
Qed.

(* 0x81d4c: strncmp (at + 1, "prefix", 6) answered v, at holding '@' (lv2_locate.c:109) *)
Lemma lp_C4c : forall f, rd_seg_L B CTX f -> rd_seg_P B CTX (S f) ->
  forall cx i d v ly3 S3 W3 regs3 mem3 md3,
  rd_base B CTX cx -> rd_loop B cx d ly3 S3 W3 regs3 mem3 md3 -> rd_acc cx i d (S f) ->
  (i < length (cx_tb cx))%nat -> byte_at (cx_tb cx) i = 64 ->
  (v = 0 <-> zl_eqb (firstn 6 (skipn (S i) (cx_tb cx))) prefix_lc = true) ->
  getr regs3 10 = w64 v -> 0 <= v < 2 ^ 64 ->
  getr regs3 19 = w64 58 -> getr regs3 20 = w64 64 -> getr regs3 24 = w64 (cx_t cx + Z.of_nat i) ->
  SRr tfibsegs W3 (cfg_at tfibsegs RD_C6 regs3 mem3 md3) (rd_post B cx).
Proof.
intros f HL HP cx i d v ly3 S3 W3 regs3 mem3 md3 HB HLP HACC HiL H64 Hv R10 Hv64 R19 R20 R24.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFR : STK_readings = 16624) by reflexivity.
assert (FRS : STK_RT_STR = 8192) by reflexivity.
pose proof (lp_base_bounds B CTX cx HB) as (Hal & Hsplo & Hsphi & Hgp & Htp).
pose proof HLP as (HC & R9 & R18 & HSL & Vrp & HPm & HG & Hcf & Hub & Hwh & Hd).
pose proof HC as (HJ & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HACC as (Hi & Hf & Hnm & Hnr).
pose proof Ct as (_ & Ht4 & Htc & _ & Ham & HRA & _).
pose proof (lp_bare_entry W3 mem3 regs3 RD_C6) as HS.
remember (Ereg regs3 (@nil word)) as E eqn:HE.
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
  by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
clear HE.
assert (SHOK : sh_ok tfibsegs LP_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 RD_C6) mem3 (seg_rom tfibsegs))))) by constructor.
unfold cfg_at. change (w64 RD_C6) with (Z_to_bv 64 RD_C6).
change (unpoison [] mem3) with mem3 in HJ.
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 RD_C6) mem3 (seg_rom tfibsegs))) in HJ.
srr_branch_tok rd_tbl_ok HS SHOK LP_Bspan.
{ (* strncmp = 0: an "@prefix" head *)
  rewrite branch_eq_U in Hc.
  rewrite (U_atom _ 10 v) in Hc
    by (first [cbn [ew ewset Nat.eqb]; rewrite (EE 10%nat 10%bv eq_refl); exact R10 | lia]).
  rewrite U_SLit, zcanon_id in Hc by (unfold M64; lia).
  apply Z.eqb_eq in Hc.
  assert (Hh : head (cx_tb cx) i = Some (i + 7)%nat)
    by (rewrite (lp_head_at _ _ HiL H64), (proj1 Hv Hc); reflexivity).
  aj_run_to_tok rd_tbl_ok HS HJ SHOK LP_Bspan RD_P.
  { lp_awr. }
  lp_mem mem3. lp_mk HS.
  eapply (lp_P_exit B CTX f HP cx i d 7%nat ly3 S3 W3 regs3 mem3 md3);
    [ exact HB | exact HLP | exact HACC | exact HiL | exact Hh | right; reflexivity | exact HJ
    | lp_q HS EE 2%nat (2%bv : bv 5) | lp_q HS EE 3%nat (3%bv : bv 5) | lp_q HS EE 4%nat (4%bv : bv 5)
    | lp_q HS EE 8%nat (8%bv : bv 5) | lp_q HS EE 9%nat (9%bv : bv 5) | lp_q HS EE 18%nat (18%bv : bv 5)
    | lp_qv HS EE 19%nat (19%bv : bv 5) R19 | lp_qv HS EE 20%nat (20%bv : bv 5) R20
    | lp_qv HS EE 24%nat (24%bv : bv 5) R24 | lp_g HS; reflexivity ]. }
{ (* strncmp <> 0: no "@prefix" head; at's '@' is no "PREFIX" either *)
  rewrite branch_eq_U in Hc.
  rewrite (U_atom _ 10 v) in Hc
    by (first [cbn [ew ewset Nat.eqb]; rewrite (EE 10%nat 10%bv eq_refl); exact R10 | lia]).
  rewrite U_SLit, zcanon_id in Hc by (unfold M64; lia).
  apply Z.eqb_neq in Hc.
  assert (Hzl : zl_eqb (firstn 6 (skipn (S i) (cx_tb cx))) prefix_lc = false)
    by (apply Bool.not_true_is_false; intros Ez; exact (Hc (proj2 Hv Ez))).
  assert (HH : head (cx_tb cx) i = (if ci_eqb (firstn 6 (skipn i (cx_tb cx))) prefix_lc &&
                          match i with O => true | S i' => is_space (byte_at (cx_tb cx) i') end
                       then Some (i + 6)%nat else None)).
  { rewrite (lp_head_at _ _ HiL H64), Hzl, (lp_ci_at64 _ _ HiL H64). reflexivity. }
  aj_run_to_tok rd_tbl_ok HS HJ SHOK LP_Bspan LP_C50.
  { lp_awr. }
  lp_mem mem3. lp_mk HS.
  eapply (lp_C50 f HL HP cx i d ly3 S3 W3 regs3 mem3 md3);
    [ exact HB | exact HLP | exact HACC | exact HiL | exact HH | exact HJ
    | lp_q HS EE 2%nat (2%bv : bv 5) | lp_q HS EE 3%nat (3%bv : bv 5) | lp_q HS EE 4%nat (4%bv : bv 5)
    | lp_q HS EE 8%nat (8%bv : bv 5) | lp_q HS EE 9%nat (9%bv : bv 5) | lp_q HS EE 18%nat (18%bv : bv 5)
    | lp_qv HS EE 19%nat (19%bv : bv 5) R19 | lp_qv HS EE 20%nat (20%bv : bv 5) R20
    | lp_qv HS EE 24%nat (24%bv : bv 5) R24 ]. }
Qed.

(* L, 0x81d18: the scan's head (lv2_locate.c:104-108) *)
Lemma lp_L : forall f, rd_seg_L B CTX f -> rd_seg_P B CTX (S f) ->
  forall cx i d ly3 S3 W3 regs3 mem3 md3,
  rd_base B CTX cx -> rd_L B cx i d (S f) ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs RD_L regs3 mem3 md3) (rd_post B cx).
Proof.
intros f HL HP cx i d ly3 S3 W3 regs3 mem3 md3 HB (HLP & HACC & R20 & R24).
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFR : STK_readings = 16624) by reflexivity.
assert (FRS : STK_RT_STR = 8192) by reflexivity.
pose proof (lp_base_bounds B CTX cx HB) as (Hal & Hsplo & Hsphi & Hgp & Htp).
pose proof HLP as (HC & R9 & R18 & HSL & Vrp & HPm & HG & Hcf & Hub & Hwh & Hd).
pose proof HC as (HJ & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HACC as (Hi & Hf & Hnm & Hnr).
pose proof (lp_byte_val W3 mem3 (cx_t cx) (cx_tb cx) i Ct Hi) as (Vc & Hcr).
pose proof (proj1 (Forall_forall _ _) HSL (0x58, RD_PREFIX)
  ltac:(unfold rd_loc_list; cbn [In]; repeat (first [left; reflexivity | right]))) as (V58 & _).
cbn [fst snd] in V58.
pose proof Ct as (_ & Ht4 & Htc & _ & Ham & HRA & _).
assert (HFm : cx_F cx mod 16 = 0).
{ unfold cx_F. replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia. rewrite Z_mod_plus_full. exact Hal. }
pose proof (lp_L_entry W3 mem3 regs3 (cx_F cx) (cx_t cx) (Z.of_nat i) (byte_at (cx_tb cx) i) R2 R8 R24
  ltac:(unfold cx_F; lia) HFm ltac:(unfold cx_F; lia) Ht4 ltac:(lia) ltac:(lia) Hcr V58 Vc) as HS.
set (c := byte_at (cx_tb cx) i) in *.
remember (Ereg regs3 [Z_to_bv 64 c]) as E eqn:HE.
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
  by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 c) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 0)).
clear HE.
assert (SHOK : sh_ok tfibsegs LP_Bx LP_SHL E
  (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 RD_L) mem3 (seg_rom tfibsegs))))).
{ constructor; [|constructor]. cbn [ms_mem].
  apply (shent_ok_of_range tfibsegs (w_H W3) mem3 E LP_Bx 24 (cx_t cx) (Z.of_nat (length (cx_tb cx)) + 1)
    (cx_t cx + Z.of_nat i) 0 1 HRA).
  - unfold LP_Bx. apply U_atom; [rewrite (EE 8%nat 8%bv eq_refl); exact R8 | unfold SHADOW_OFF; lia].
  - apply U_atom; [rewrite (EE 24%nat 24%bv eq_refl); exact R24 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Ham. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 RD_L) with (Z_to_bv 64 RD_L).
change (unpoison [] mem3) with mem3 in HJ.
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 RD_L) mem3 (seg_rom tfibsegs))) in HJ.
aj_run_tok rd_tbl_ok HS HJ SHOK LP_Bspan.
{ lp_awr. }
lp_mem mem3.
srr_branch_tok rd_tbl_ok HS SHOK LP_Bspan.
{ (* at holds '@': strncmp (at + 1, "prefix", 6), 0x81d48 *)
  rewrite branch_eq_U in Hc.
  rewrite (U_atom _ 32 c) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E32 | lia]).
  rewrite (U_atom _ 20 64) in Hc
    by (first [cbn [ew ewset Nat.eqb]; rewrite (EE 20%nat 20%bv eq_refl); exact R20 | lia]).
  apply Z.eqb_eq in Hc.
  assert (HiL : (i < length (cx_tb cx))%nat).
  { destruct (Nat.lt_ge_cases i (length (cx_tb cx))) as [Hlt|Hge]; [exact Hlt|].
    exfalso. unfold c in Hc. rewrite (lp_byte_past _ _ Hge) in Hc. lia. }
  aj_run_tok rd_tbl_ok HS HJ SHOK LP_Bspan.
  { lp_awr. }
  lp_mem mem3. lp_mk HS.
  pose proof (proj1 HJ) as HAR3.
  destruct (IMG ly3 S3 W3 mem3 _ HAR3 HRO) as (HROM & HROO & Hcan & HFRS & Hfmt).
    pose proof (proj1 (Forall_forall _ _) HFRS (RD_PREFIX, LP_PRE)
    ltac:(unfold FM_RO_STRS, RD_PREFIX, LP_PRE; cbn [In]; repeat (first [left; reflexivity | right])))
    as (Cpre & _).
  cbn [fst snd] in Cpre.
  pose proof (lp_cstr_ok_suffix W3 mem3 (cx_t cx) (cx_tb cx) (S i) Ct ltac:(lia)) as Csuf.
  eapply SRr_bind.
  { eapply (g3_aj_ro_at B LAWS PC_strncmp STK_RT_STR
      (fun r => r = 0 <-> strn_eq (Z.to_nat 6) (skipn (S i) (cx_tb cx)) LP_PRE)
      W3 _ _ (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
      [] ly3 S3 _ EV_names (-224) (Z_to_bv 64 RD_C6));
    [ exact HJ
    | unfold spZ; lp_gr HS (2%bv : bv 5); rewrite (EE 2%nat 2%bv eq_refl), R2, unsigned_lit_small by (unfold cx_F; lia);
      unfold cx_F; lia
    | reflexivity | lia | unfold ESTACK; lia | lia
    | lp_gr HS (3%bv : bv 5); rewrite (EE 3%nat 3%bv eq_refl), R3; exact Hgp
    | lp_gr HS (4%bv : bv 5); rewrite (EE 4%nat 4%bv eq_refl), R4; exact Htp
    | lp_gr HS (1%bv : bv 5); reflexivity
    | unfold YK0s.ret_ok; vm_compute; reflexivity
    | ].
    intros HPK.
    apply (STRNCMP ly3 S3 W3 _ _ _ (cx_t cx + Z.of_nat (S i)) RD_PREFIX 6 (skipn (S i) (cx_tb cx)) LP_PRE HPK
      HROM HROO);
    [ lp_gr HS (10%bv : bv 5); rewrite (EE 24%nat 24%bv eq_refl), R24, unsigned_lit_small by lia;
      unfold w64; f_equal; lia
    | lp_gr HS (11%bv : bv 5); reflexivity
    | lp_gr HS (12%bv : bv 5); reflexivity
    | lia | exact Csuf | exact Cpre ]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & H10v & Hv64 & HR & Hfr2 & Hpres2).
  assert (Hvz : v = 0 <-> zl_eqb (firstn 6 (skipn (S i) (cx_tb cx))) prefix_lc = true).
  { rewrite HR. change (Z.to_nat 6) with 6%nat. apply lp_strn6. destruct Csuf as ((_ & Hnz) & _). exact Hnz. }
  assert (HAV : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx - STK_RT_STR <= a < cx_F cx) ->
    aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) mem3 a)
    by (intros a Ha Hn; apply Hfr2; [exact Ha | unfold cx_F in *; lia]).
  assert (QQ : forall r : bv 5, In r [2; 3; 4; 8; 9; 18]%bv -> getr regs2 r = getr regs3 r).
  { intros r Hr. cbv [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    - etransitivity; [exact (HP2 2 ltac:(unfold acallee_saved; lia))|]. lp_q HS EE 2%nat (2%bv : bv 5).
    - etransitivity; [exact (HP2 3 ltac:(unfold acallee_saved; lia))|]. lp_q HS EE 3%nat (3%bv : bv 5).
    - etransitivity; [exact (HP2 4 ltac:(unfold acallee_saved; lia))|]. lp_q HS EE 4%nat (4%bv : bv 5).
    - etransitivity; [exact (HP2 8 ltac:(unfold acallee_saved; lia))|]. lp_q HS EE 8%nat (8%bv : bv 5).
    - etransitivity; [exact (HP2 9 ltac:(unfold acallee_saved; lia))|]. lp_q HS EE 9%nat (9%bv : bv 5).
    - etransitivity; [exact (HP2 18 ltac:(unfold acallee_saved; lia))|]. lp_q HS EE 18%nat (18%bv : bv 5). }
  pose proof (lp_loop_keep B CTX cx d ly3 S3 W3 regs3 mem3 md3 regs2 mem2 md2 HB HLP HJ2 HAV
    (QQ 2%bv ltac:(cbv; tauto)) (QQ 3%bv ltac:(cbv; tauto)) (QQ 4%bv ltac:(cbv; tauto))
    (QQ 8%bv ltac:(cbv; tauto)) (QQ 9%bv ltac:(cbv; tauto)) (QQ 18%bv ltac:(cbv; tauto))) as HLP2.
  eapply (lp_C4c f HL HP cx i d v ly3 S3 W3 regs2 mem2 md2);
    [ exact HB | exact HLP2 | exact HACC | exact HiL | exact Hc | exact Hvz | exact H10v | exact Hv64
    | etransitivity; [exact (HP2 19 ltac:(unfold acallee_saved; lia))|]; lp_g HS; reflexivity
    | etransitivity; [exact (HP2 20 ltac:(unfold acallee_saved; lia))|]; lp_qv HS EE 20%nat (20%bv : bv 5) R20
    | etransitivity; [exact (HP2 24 ltac:(unfold acallee_saved; lia))|]; lp_qv HS EE 24%nat (24%bv : bv 5) R24 ]. }
{ (* at holds no '@' *)
  rewrite branch_eq_U in Hc.
  rewrite (U_atom _ 32 c) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E32 | lia]).
  rewrite (U_atom _ 20 64) in Hc
    by (first [cbn [ew ewset Nat.eqb]; rewrite (EE 20%nat 20%bv eq_refl); exact R20 | lia]).
  apply Z.eqb_neq in Hc.
  aj_run_tok rd_tbl_ok HS HJ SHOK LP_Bspan.
  { lp_awr. }
  lp_mem mem3.
  srr_branch_tok rd_tbl_ok HS SHOK LP_Bspan.
  { (* NUL: the scan ends, 0x820b0 *)
    rewrite branch_eq_U in Hc0.
    rewrite (U_atom _ 32 c) in Hc0 by (first [cbn [ew ewset Nat.eqb]; exact E32 | lia]).
    rewrite U_SLit, zcanon_id in Hc0 by (unfold M64; lia).
    apply Z.eqb_eq in Hc0.
    aj_run_to_tok rd_tbl_ok HS HJ SHOK LP_Bspan RD_R.
    { lp_awr. }
    lp_mem mem3. lp_mk HS.
    eapply (lp_R_exit B CTX cx i d f ly3 S3 W3 regs3 mem3 md3);
      [ exact HB | exact HLP | exact HACC | exact Hc0 | exact HJ
      | lp_q HS EE 2%nat (2%bv : bv 5) | lp_q HS EE 3%nat (3%bv : bv 5) | lp_q HS EE 4%nat (4%bv : bv 5)
      | lp_q HS EE 8%nat (8%bv : bv 5) | lp_q HS EE 9%nat (9%bv : bv 5) | lp_q HS EE 18%nat (18%bv : bv 5)
      | lp_g HS; reflexivity ]. }
  { (* neither: strncasecmp (at, "PREFIX", 6), 0x81d50 *)
    rewrite branch_eq_U in Hc0.
    rewrite (U_atom _ 32 c) in Hc0 by (first [cbn [ew ewset Nat.eqb]; exact E32 | lia]).
    rewrite U_SLit, zcanon_id in Hc0 by (unfold M64; lia).
    apply Z.eqb_neq in Hc0.
    assert (HiL : (i < length (cx_tb cx))%nat).
    { destruct (Nat.lt_ge_cases i (length (cx_tb cx))) as [Hlt|Hge]; [exact Hlt|].
      exfalso. apply Hc0. unfold c. exact (lp_byte_past _ _ Hge). }
    aj_run_to_tok rd_tbl_ok HS HJ SHOK LP_Bspan LP_C50.
    { lp_awr. }
    lp_mem mem3. lp_mk HS.
    eapply (lp_C50 f HL HP cx i d ly3 S3 W3 regs3 mem3 md3);
      [ exact HB | exact HLP | exact HACC | exact HiL | exact (lp_head_nat (cx_tb cx) i Hc) | exact HJ
      | lp_q HS EE 2%nat (2%bv : bv 5) | lp_q HS EE 3%nat (3%bv : bv 5) | lp_q HS EE 4%nat (4%bv : bv 5)
      | lp_q HS EE 8%nat (8%bv : bv 5) | lp_q HS EE 9%nat (9%bv : bv 5) | lp_q HS EE 18%nat (18%bv : bv 5)
      | lp_g HS; reflexivity
      | lp_qv HS EE 20%nat (20%bv : bv 5) R20 | lp_qv HS EE 24%nat (24%bv : bv 5) R24 ]. } }
Qed.

Theorem rd_L_holds : forall f, rd_seg_L B CTX f -> rd_seg_P B CTX (S f) -> rd_seg_L B CTX (S f).
Proof.
intros f HL HP cx i d ly3 S3 W3 regs3 mem3 md3 HB HLc.
exact (lp_L f HL HP cx i d ly3 S3 W3 regs3 mem3 md3 HB HLc).
Qed.
End c.
