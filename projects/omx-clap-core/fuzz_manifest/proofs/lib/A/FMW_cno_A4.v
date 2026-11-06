(* check_no_overread 0x80b20, segment R3 0x80c88 -> P4 0x80ca4: shadow check and NUL store at u2 + un + 17, malloc (tn + 18) -> t2. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YC20 YC85.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05 YCbp YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l AF0m ACej FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_cno0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis FB : FmB B.
Hypothesis HB : TfibSyms B.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis UNIV : fm_univ B.
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B ameter_triv.
Hypothesis AFREE4 : afree04_rule tfibsegs B ameter_triv.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy PC_memcpy.
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet PC_memset.
Hypothesis NAMES : names_spec tfibsegs B CTX_lv2_locate_manifest_names.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).

#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* ---- R3's symbolic state: s4 (atom 20) = u2 + un + 17, its one byte a writable region; s8 (atom 24) = the shadow
   base; the shadow entry says the byte at s4 is addressable ---- *)
Definition cnoA4_blk : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 1 [].
Definition ss_cnoA4 : sstate :=
  mkSS CNO_R3 sr_atoms [cnoA4_blk] None
    (mkFacts [(20%nat, mkAF 4096 (2 ^ 47 - 16) 0); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).
Definition cnoA4_Bx : sv := SOff 24 0.
Definition cnoA4_SH : list shent := [mkSHE 20 0 1].

(* ---- small kit ---- *)
Lemma cnoA4_entry : forall (W : world tfibsegs) mem regs x,
  getr regs 24 = w64 FMW_SB -> getr regs 20 = w64 x -> 4096 <= x <= 2 ^ 47 - 16 ->
  writable_at tfibsegs (rdW W mem) x ->
  st_ok tfibsegs (Ereg regs []) ss_cnoA4 (restrict (w_H W) (mkst regs (Z_to_bv 64 CNO_R3) mem (seg_rom tfibsegs))).
Proof.
intros W mem regs x R24 R20 Hx Hw.
rewrite restrict_mkst_fx.
set (E := Ereg regs []).
assert (U20 : bv_unsigned (ew E 20) = x)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl), R24; unfold w64, FMW_SB, SHADOW_OFF;
      apply unsigned_lit_small; lia).
unfold ss_cnoA4. apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold cnoA4_blk. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U20.
  split; [lia|]. split; [lia|]. split; [intros o Ho; replace (x + o) with x by lia; exact Hw|]. apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold cnoA4_blk, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U20, U24. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
Qed.
(* the run's one write is the byte x *)
Lemma cnoA4_keep : forall E (W : world tfibsegs) m m' x,
  frame_of E [cnoA4_blk] (rdW W m) (rdW W m') -> bv_unsigned (ew E 20) = x ->
  forall a, 0 <= a < 2 ^ 64 -> a <> x -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.
Proof.
intros E W m m' x HF Hx a Ha Hne. apply (aview_eq_of tfibsegs). apply HF.
rewrite unsigned_lit_small by lia. intros (r & [<-|[]] & Hr).
cbn [cnoA4_blk YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Hx in Hr. lia.
Qed.
(* a register the run left as an atom *)
Lemma cnoA4_reg_atom : forall (H : word -> bool) E ss ms (r : bv 5) n,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof. intros H E ss ms r n HS Hr. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. apply fmw_SOff0. Qed.
(* an image byte is no block byte *)
Lemma cnoA4_img_ne : forall ly S (W : world tfibsegs) mem md p m x a,
  AR tfibsegs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= x < p + req_size m -> in_img tfibsegs a -> a <> x.
Proof. intros ly S W mem md p m x a HAR Hin Hx Ha ->. exact (blk_img tfibsegs B LAWS ly S W mem md p m x HAR Hin Hx Ha). Qed.
(* a byte window whose view is unchanged keeps its bytes *)
Lemma cnoA4_garr8_keep : forall (W W' : world tfibsegs) m m' p l,
  (forall a, p <= a < p + Z.of_nat (length l) -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  garr8 tfibsegs (rdW W m) p l -> garr8 tfibsegs (rdW W' m') p l.
Proof.
intros W W' m m' p l HK Hg. apply (garr8_frame tfibsegs _ _ p l Hg). intros a Ha. apply (mbyte_of_aview tfibsegs).
exact (HK a Ha).
Qed.
(* fm's statics ride through any step that keeps their bytes *)
Lemma cnoA4_glob_img : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  (forall a, inFP FM_PSTAT_FP a -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  fm_glob tfibsegs W m live peak cnt fail -> fm_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail HK (G1 & G2 & G3 & G4 & R).
assert (VK : forall g v, In (g, g + 8) FM_PSTAT_FP ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv. eapply (val_mem_kept tfibsegs); [|exact Hv]. intros k Hk. apply HK.
  apply (inFP_FM_PSTAT_FP g Hg). cbn in Hk. lia. }
unfold fm_glob, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VK; [cbv [FM_PSTAT_FP In]; repeat (first [left; reflexivity | right]) | exact G1]|].
split; [apply VK; [cbv [FM_PSTAT_FP In]; repeat (first [left; reflexivity | right]) | exact G2]|].
split; [apply VK; [cbv [FM_PSTAT_FP In]; repeat (first [left; reflexivity | right]) | exact G3]|].
split; [apply VK; [cbv [FM_PSTAT_FP In]; repeat (first [left; reflexivity | right]) | exact G4]|].
exact R.
Qed.
(* a block made after the entry is not one of the entry's *)
Lemma cnoA4_new_notin : forall ly S (W : world tfibsegs) mem md bl0 nb x,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = bl0 ++ nb -> In x nb -> ~ In x bl0.
Proof.
intros ly S W mem md bl0 nb x HAR Hbl Hx Hx0.
apply in_split in Hx0 as (l1 & l2 & E1). apply in_split in Hx as (l3 & l4 & E2). subst bl0 nb.
pose proof (sep_blocks_pos tfibsegs B LAWS ly S W mem md x x l1 (l2 ++ l3) l4 HAR) as Hd.
assert (Eq : (l1 ++ x :: l2) ++ l3 ++ x :: l4 = l1 ++ x :: (l2 ++ l3) ++ x :: l4)
  by (rewrite <- app_assoc; cbn [app]; rewrite <- app_assoc; reflexivity).
assert (Hinx : In x (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
specialize (Hd (eq_trans Hbl Eq)). destruct x as [p n].
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinx) as (_ & _ & _ & _ & _ & _ & Hn).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (0 < req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia). lia.
Qed.
(* a source window homed in a block live at the entry keeps its bytes over a journal that keeps the block (block bytes
   are not image bytes, so not fm's statics) *)
Lemma cnoA4_bytes_kept : forall STK sp0 k ly S (W : world tfibsegs) mem md ly2 S2 W2 mem2 md2 p l,
  ajournal tfibsegs B STK sp0 FM_PSTAT_FP ly S W mem md [] ly2 S2 W2 mem2 md2 k ->
  AR tfibsegs B ly S W mem md ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)) ->
  cno_home B ly S p l -> bytes_at tfibsegs W mem p l -> bytes_at tfibsegs W2 mem2 p l.
Proof.
intros STK sp0 k ly S W mem md ly2 S2 W2 mem2 md2 p l HJ HAR Hinc Hh Hb.
destruct Hh as [-> | (b & m & Hin & Hlo & Hhi)]; [apply garr8_nil|].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
unfold bytes_at in *. apply (garr8_frame tfibsegs _ _ p l Hb). intros a Ha.
apply mbyte_of_aview.
assert (Hi : 0 <= a - b < req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
replace a with (b + (a - b)) by lia.
apply (F2 b m (a - b)); [exact Hin | exact (Hinc _ Hin) | exact Hi |].
intros Hfp. apply (blk_img tfibsegs B LAWS ly S W mem md b m (b + (a - b)) HAR Hin ltac:(lia)).
exact (pstat_img _ Hfp).
Qed.
(* a block's bytes ride over a runtime call's own journal (no footprint) that keeps the block *)
Lemma cnoA4_cpy_sub : forall STK sp0 k ly S (W : world tfibsegs) mem md ly2 S2 W2 mem2 md2 p m l,
  ajournal tfibsegs B STK sp0 [] ly S W mem md [] ly2 S2 W2 mem2 md2 k ->
  In (p, m) (ablocks B ly S) -> In (p, m) (ablocks B ly2 S2) -> Z.of_nat (length l) <= req_size m ->
  garr8 tfibsegs (rdW W mem) p l -> garr8 tfibsegs (rdW W2 mem2) p l.
Proof.
intros STK sp0 k ly S W mem md ly2 S2 W2 mem2 md2 p m l HJ Hin Hin2 Hl Hg.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (garr8_frame tfibsegs _ _ p l Hg). intros a Ha. apply (mbyte_of_aview tfibsegs).
replace a with (p + (a - p)) by lia.
apply (F2 p m (a - p) Hin Hin2); [lia | apply inFP_nil].
Qed.

(* ---- R3 0x80c88 -> P4 0x80ca4 ---- *)
Lemma cno_seg_R3 : forall cx ly S W regs mem md u1 t1 u2,
  cno_base B cx -> cno_R3 B cx ly S W regs mem md u1 t1 u2 ->
  (forall ly' S' W' regs' mem' md' t2, cno_P4 B cx ly' S' W' regs' mem' md' u1 t1 u2 t2 ->
     SRr tfibsegs W' (cfg_at tfibsegs CNO_P4 regs' mem' md') (cno_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs CNO_R3 regs mem md) (cno_post B cx).
Proof.
intros [ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt] ly S W regs mem md u1 t1 u2 HBX HR3 K.
pose proof HBX as (HPRE & Hra0 & G10 & G11 & G12 & G13 & Hsu & Hst & Hnzu & Hnzt & Hhu & Hht & Hlu & Htnm & HG0 & HQ
  & Hlive & Hev & Hbb).
destruct HPRE as [HAP HRO].
pose proof HAP as (HAR0 & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch & HQT).
destruct HR3 as (((HJ & HFR & Hsp & Hgp & Htp & H24 & HROc & H26 & H27) & Hbl & Hbu & Hbt & HG & H18 & H21 & H25) &
  Hu1 & Ht1 & Hu2 & R23 & R19 & R8 & R9 & R20 & R22 & Cu1 & Ct1 & Cu2).
unfold nx_un, nx_tn, nx_sp0, cno_J, cno_cpy, CNO_FRAME in *.
cbn [nx_ly nx_S nx_W nx_regs nx_mem nx_md nx_up nx_tp nx_ub nx_tb nx_live nx_peak nx_cnt] in *.
change (Z.of_nat (length _)) with 3 in HJ.
pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
assert (FS : STK_check_no_overread = 16736) by reflexivity.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnv & _).
(* the three copies made so far *)
assert (Hin_u1 : In (u1, Z.of_nat (length ub) + 18) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hin_t1 : In (t1, Z.of_nat (length tb) + 18) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; right; left; reflexivity).
assert (Hin_u2 : In (u2, Z.of_nat (length ub) + 18) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; right; right; left; reflexivity).
assert (Hrqu : req_size (Z.of_nat (length ub) + 18) = Z.of_nat (length ub) + 18)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length ub) + 18) 0); lia).
assert (Hrqt : req_size (Z.of_nat (length tb) + 18) = Z.of_nat (length tb) + 18)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length tb) + 18) 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u1) as (_ & _ & Hcu1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_t1) as (_ & _ & Hct1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u2) as (_ & _ & Hcu2 & Happ & Hpres & _).
rewrite Hrqu in Hcu1, Hcu2, Happ, Hpres. rewrite Hrqt in Hct1.
assert (Du1 : u1 + (Z.of_nat (length ub) + 18) <= u2 \/ u2 + (Z.of_nat (length ub) + 18) <= u1).
{ pose proof (sep_blocks_pos tfibsegs B LAWS ly S W mem md (u1, Z.of_nat (length ub) + 18) (u2, Z.of_nat (length ub) + 18)
    (ablocks B ly0 S0) [(t1, Z.of_nat (length tb) + 18)] [] HAR ltac:(rewrite Hbl; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hrqu in Hd. exact Hd. }
assert (Dt1 : t1 + (Z.of_nat (length tb) + 18) <= u2 \/ u2 + (Z.of_nat (length ub) + 18) <= t1).
{ pose proof (sep_blocks_pos tfibsegs B LAWS ly S W mem md (t1, Z.of_nat (length tb) + 18) (u2, Z.of_nat (length ub) + 18)
    (ablocks B ly0 S0 ++ [(u1, Z.of_nat (length ub) + 18)]) [] [] HAR
    ltac:(rewrite Hbl, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hrqu, Hrqt in Hd. exact Hd. }
(* the malloc call's budgets *)
assert (Hnev : st_nev S < EV_MAX) by (unfold EV_check_no_overread, EV_names in *; lia).
assert (Hbb3 : blocks_bytes S + (Z.of_nat (length tb) + 18) <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly S), Hbl, bsum_app, <- (blocks_bytes_bsum B ly0 S0).
  unfold bsum. cbn [fold_right snd]. unfold LIVE_check_no_overread, MANIFEST_MAX in *. lia. }
(* ---- 0x80c88: the shadow check of the byte at s4 = u2 + un + 17, sb zero, a0 := s6, call malloc ---- *)
assert (Hw : writable_at tfibsegs (rdW W mem) (u2 + Z.of_nat (length ub) + 17))
  by (apply (apresent_writable tfibsegs); exact (proj1 (Hpres (u2 + Z.of_nat (length ub) + 17) ltac:(lia)))).
pose proof (cnoA4_entry W mem regs (u2 + Z.of_nat (length ub) + 17) H24 R20 ltac:(lia) Hw) as HS.
set (E := Ereg regs []) in HS.
assert (U20 : bv_unsigned (ew E 20) = u2 + Z.of_nat (length ub) + 17)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok tfibsegs cnoA4_Bx cnoA4_SH E (rdW W (ms_mem (mkst regs (Z_to_bv 64 CNO_R3) mem (seg_rom tfibsegs))))).
{ constructor; [|constructor]. cbn [ms_mem].
  apply (shent_ok_of_range tfibsegs (w_H W) mem E cnoA4_Bx 20 u2 (Z.of_nat (length ub) + 18)
    (u2 + Z.of_nat (length ub) + 17) 0 1).
  - apply (range_addressable_of_block tfibsegs B LAWS ly S W mem md u2 _ u2 (Z.of_nat (length ub) + 18) HAR Hin_u2); lia.
  - unfold cnoA4_Bx. apply U_atom; [unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24 | unfold SHADOW_OFF; lia].
  - apply U_atom; [unfold E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact R20 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx.
    unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
assert (Hnew : ~ In (u2, Z.of_nat (length ub) + 18) (ablocks B ly0 S0)).
{ apply (cnoA4_new_notin ly S W mem md _ _ _ HAR Hbl). repeat (first [left; reflexivity | right]). }
unfold cfg_at. change (w64 CNO_R3) with (Z_to_bv 64 CNO_R3).
change mem with (ms_mem (mkst regs (Z_to_bv 64 CNO_R3) mem (seg_rom tfibsegs))) in HJ.
aj_run_to_tok fmw_tbl_cno_ok HS HJ SHOK fmw_Bspan 0x52dbc.
{ unfold ss_cnoA4. cbn [ss_mem].
  eapply awr_ok_cons_gen with (k := 20%nat) (b := u2 + Z.of_nat (length ub) + 17); [reflexivity | exact U20 | | apply awr_ok_nil].
  intros a Ha. cbn [cnoA4_blk YP09.r_wlo YP09.r_whi] in Ha. left; right; right; left.
  exists u2, (Z.of_nat (length ub) + 18). split; [exact Hin_u2|]. split; [exact Hnew|]. rewrite Hrqu. lia. }
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E1 := Ex) in HS end.
match goal with H : frame_of E _ (rdW W mem) (rdW W (ms_mem ms)) |- _ => rename H into HFm end.
change (ss_mem ss_cnoA4) with [cnoA4_blk] in HFm.
pose proof (cnoA4_keep E W mem (ms_mem ms) _ HFm U20) as KEEP.
assert (AG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs r)
  by (intros n r Hn Hr; unfold E1; rewrite !ew_ewset_other by lia; unfold E; apply ew_Ereg_nat; exact Hr).
pose proof (fmw_reg_lit _ E1 _ ms 1%bv CNO_P4 HS ltac:(vm_compute; reflexivity) ltac:(unfold CNO_P4; lia)) as Q1.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 2%bv 2 HS ltac:(vm_compute; reflexivity)) (AG 2%nat 2%bv ltac:(lia) eq_refl)) as Q2.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 3%bv 3 HS ltac:(vm_compute; reflexivity)) (AG 3%nat 3%bv ltac:(lia) eq_refl)) as Q3.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 4%bv 4 HS ltac:(vm_compute; reflexivity)) (AG 4%nat 4%bv ltac:(lia) eq_refl)) as Q4.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 8%bv 8 HS ltac:(vm_compute; reflexivity)) (AG 8%nat 8%bv ltac:(lia) eq_refl)) as Q8.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 9%bv 9 HS ltac:(vm_compute; reflexivity)) (AG 9%nat 9%bv ltac:(lia) eq_refl)) as Q9.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 10%bv 22 HS ltac:(vm_compute; reflexivity)) (AG 22%nat 22%bv ltac:(lia) eq_refl)) as Q10.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 18%bv 18 HS ltac:(vm_compute; reflexivity)) (AG 18%nat 18%bv ltac:(lia) eq_refl)) as Q18.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 19%bv 19 HS ltac:(vm_compute; reflexivity)) (AG 19%nat 19%bv ltac:(lia) eq_refl)) as Q19.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 21%bv 21 HS ltac:(vm_compute; reflexivity)) (AG 21%nat 21%bv ltac:(lia) eq_refl)) as Q21.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 22%bv 22 HS ltac:(vm_compute; reflexivity)) (AG 22%nat 22%bv ltac:(lia) eq_refl)) as Q22.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 23%bv 23 HS ltac:(vm_compute; reflexivity)) (AG 23%nat 23%bv ltac:(lia) eq_refl)) as Q23.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 24%bv 24 HS ltac:(vm_compute; reflexivity)) (AG 24%nat 24%bv ltac:(lia) eq_refl)) as Q24.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 25%bv 25 HS ltac:(vm_compute; reflexivity)) (AG 25%nat 25%bv ltac:(lia) eq_refl)) as Q25.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 26%bv 26 HS ltac:(vm_compute; reflexivity)) (AG 26%nat 26%bv ltac:(lia) eq_refl)) as Q26.
pose proof (eq_trans (cnoA4_reg_atom _ E1 _ ms 27%bv 27 HS ltac:(vm_compute; reflexivity)) (AG 27%nat 27%bv ltac:(lia) eq_refl)) as Q27.
assert (Hspc : spZ (ms_regs ms) = spZ regs0 + -96) by (unfold spZ in *; rewrite Q2; lia).
(* what the store kept *)
assert (HFRc : cno_frame (mkNX ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt) W (ms_mem ms)).
{ apply (cno_frame_kept _ W W mem (ms_mem ms)); [|exact HFR]. intros a Ha. unfold nx_sp0, CNO_FRAME in Ha.
  cbn [nx_regs] in Ha. apply KEEP; lia. }
assert (HGc : fm_glob tfibsegs W (ms_mem ms) live peak cnt SIZE_MAXZ).
{ apply (cnoA4_glob_img W W mem (ms_mem ms)); [|exact HG]. intros a Ha.
  pose proof (pstat_img a Ha) as Hi. pose proof (HSL a Hi) as Hl. unfold kLowMemEnd in Hl.
  exact (KEEP a ltac:(lia) (cnoA4_img_ne ly S W mem md u2 _ (u2 + Z.of_nat (length ub) + 17) a HAR Hin_u2
    ltac:(rewrite Hrqu; lia) Hi)). }
assert (Cu1c : garr8 tfibsegs (rdW W (ms_mem ms)) u1 (ub ++ [0])).
{ apply (cnoA4_garr8_keep W W mem (ms_mem ms) u1 (ub ++ [0])); [|exact Cu1].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KEEP; lia. }
assert (Ct1c : garr8 tfibsegs (rdW W (ms_mem ms)) t1 (tb ++ [0])).
{ apply (cnoA4_garr8_keep W W mem (ms_mem ms) t1 (tb ++ [0])); [|exact Ct1].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KEEP; lia. }
assert (Cu2c : garr8 tfibsegs (rdW W (ms_mem ms)) u2 (ub ++ [0])).
{ apply (cnoA4_garr8_keep W W mem (ms_mem ms) u2 (ub ++ [0])); [|exact Cu2].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KEEP; lia. }
(* the caller's frame chain: s0 = u1 is a heap address *)
assert (CH : chain_pre ly (aview tfibsegs (w_H W) (ms_mem ms)) (ms_regs ms) []).
{ apply (achain_chain_pre ly _ (spZ (ms_regs ms)) (s0Z (ms_regs ms)) [] (ms_regs ms)).
  - apply achain_low. unfold s0Z. rewrite Q8, R8. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite Hspc. lia.
  - reflexivity.
  - unfold raZ. rewrite Q1, unsigned_lit_small by (unfold CNO_P4; lia). unfold CNO_P4. lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E1 _ ms HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 0x52dbc) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite (fb_code B FB); reflexivity).
(* ---- malloc (tn + 18) ---- *)
eapply SRr_bind.
{ apply (amalloc04_sub tfibsegs B LAWS HSL ameter_triv AMALLOC4 W (ms_regs ms) (ms_mem ms) STK_check_no_overread
    (spZ regs0) FM_PSTAT_FP ly0 S0 W0 mem0 md0 [] ly S _ 3 (Z.of_nat (length tb) + 18) (-96) (Z_to_bv 64 CNO_P4) []).
  - exact HJ.
  - rewrite Q10. exact R22.
  - unfold MALLOC_MAX. unfold MANIFEST_MAX in Htnm. lia.
  - exact Hbb3.
  - exact Hspc.
  - reflexivity.
  - lia.
  - unfold ASTACK. lia.
  - rewrite Q3, Hgp. exact Hgp0.
  - rewrite Q4, Htp. exact Htp0.
  - exact Q1.
  - apply ret_ok_even. rewrite unsigned_lit_small by (unfold CNO_P4; lia). reflexivity.
  - exact Hnev.
  - exact CH.
  - apply UNIV. rewrite call_trace_nil, (fb_code B FB).
    assert (RA : raZ (ms_regs ms) = 0x80ca4) by (unfold raZ; rewrite Q1; apply unsigned_lit_small; unfold CNO_P4; lia).
    rewrite RA. apply memZL_In. vm_compute. reflexivity.
  - exact I. }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & H10r & _ & Hr4 & Hbl2 & HK & _ & HJs).
(* ---- back at 0x80ca4 ---- *)
destruct HK as (KK1 & _ & KK3 & _).
assert (Hbl4 : ablocks B ly2 S2 = ablocks B ly0 S0 ++ [(u1, Z.of_nat (length ub) + 18); (t1, Z.of_nat (length tb) + 18);
    (u2, Z.of_nat (length ub) + 18); (res, Z.of_nat (length tb) + 18)])
  by (rewrite Hbl2, Hbl, <- app_assoc; reflexivity).
assert (Hinc : forall x, In x (ablocks B ly0 S0) -> In x (ablocks B ly2 S2))
  by (intros x Hx; rewrite Hbl4; apply in_or_app; left; exact Hx).
assert (Hin2 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2))
  by (intros x Hx; rewrite Hbl2; apply in_or_app; left; exact Hx).
assert (HFR2 : cno_frame (mkNX ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt) W2 mem2).
{ apply (cno_frame_kept _ W W2 (ms_mem ms) mem2); [|exact HFRc]. intros a Ha.
  unfold nx_sp0, CNO_FRAME in Ha. cbn [nx_regs] in Ha. apply KK1; [lia | unfold ASTACK; lia]. }
assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W2) mem2))
  by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 pstat_closed pstat_not_roP HRO).
assert (HG2 : fm_glob tfibsegs W2 mem2 live peak cnt SIZE_MAXZ).
{ apply (cnoA4_glob_img W W2 (ms_mem ms) mem2); [|exact HGc].
  intros a Ha. destruct (fb_pstat B FB a Ha) as [N1 N2]. exact (KK3 a (pstat_img a Ha) N1 N2). }
assert (Hbu2 : bytes_at tfibsegs W2 mem2 up ub)
  by exact (cnoA4_bytes_kept _ _ _ ly0 S0 W0 mem0 md0 ly2 S2 W2 mem2 md2 up ub HJ2 HAR0 Hinc Hhu (proj1 Hsu)).
assert (Hbt2 : bytes_at tfibsegs W2 mem2 tp tb)
  by exact (cnoA4_bytes_kept _ _ _ ly0 S0 W0 mem0 md0 ly2 S2 W2 mem2 md2 tp tb HJ2 HAR0 Hinc Hht (proj1 Hst)).
assert (Cu12 : garr8 tfibsegs (rdW W2 mem2) u1 (ub ++ [0])).
{ apply (cnoA4_cpy_sub _ _ _ ly S W (ms_mem ms) _ ly2 S2 W2 mem2 md2 u1 (Z.of_nat (length ub) + 18) (ub ++ [0])
    HJs Hin_u1 (Hin2 _ Hin_u1)); [|exact Cu1c].
  rewrite length_app, Hrqu. cbn [length]. lia. }
assert (Ct12 : garr8 tfibsegs (rdW W2 mem2) t1 (tb ++ [0])).
{ apply (cnoA4_cpy_sub _ _ _ ly S W (ms_mem ms) _ ly2 S2 W2 mem2 md2 t1 (Z.of_nat (length tb) + 18) (tb ++ [0])
    HJs Hin_t1 (Hin2 _ Hin_t1)); [|exact Ct1c].
  rewrite length_app, Hrqt. cbn [length]. lia. }
assert (Cu22 : garr8 tfibsegs (rdW W2 mem2) u2 (ub ++ [0])).
{ apply (cnoA4_cpy_sub _ _ _ ly S W (ms_mem ms) _ ly2 S2 W2 mem2 md2 u2 (Z.of_nat (length ub) + 18) (ub ++ [0])
    HJs Hin_u2 (Hin2 _ Hin_u2)); [|exact Cu2c].
  rewrite length_app, Hrqu. cbn [length]. lia. }
(* the registers *)
assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (fmw_pres _ _ 2%bv HP2 ltac:(fmw_cs_side)).
assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (fmw_pres _ _ 3%bv HP2 ltac:(fmw_cs_side)).
assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (fmw_pres _ _ 4%bv HP2 ltac:(fmw_cs_side)).
assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (fmw_pres _ _ 8%bv HP2 ltac:(fmw_cs_side)).
assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (fmw_pres _ _ 9%bv HP2 ltac:(fmw_cs_side)).
assert (P18 : getr regs2 18 = getr (ms_regs ms) 18) by exact (fmw_pres _ _ 18%bv HP2 ltac:(fmw_cs_side)).
assert (P19 : getr regs2 19 = getr (ms_regs ms) 19) by exact (fmw_pres _ _ 19%bv HP2 ltac:(fmw_cs_side)).
assert (P21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (fmw_pres _ _ 21%bv HP2 ltac:(fmw_cs_side)).
assert (P22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (fmw_pres _ _ 22%bv HP2 ltac:(fmw_cs_side)).
assert (P23 : getr regs2 23 = getr (ms_regs ms) 23) by exact (fmw_pres _ _ 23%bv HP2 ltac:(fmw_cs_side)).
assert (P24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (fmw_pres _ _ 24%bv HP2 ltac:(fmw_cs_side)).
assert (P25 : getr regs2 25 = getr (ms_regs ms) 25) by exact (fmw_pres _ _ 25%bv HP2 ltac:(fmw_cs_side)).
assert (P26 : getr regs2 26 = getr (ms_regs ms) 26) by exact (fmw_pres _ _ 26%bv HP2 ltac:(fmw_cs_side)).
assert (P27 : getr regs2 27 = getr (ms_regs ms) 27) by exact (fmw_pres _ _ 27%bv HP2 ltac:(fmw_cs_side)).
change (mkCfg (mkst regs2 (Z_to_bv 64 CNO_P4) mem2 (seg_rom tfibsegs)) md2) with (cfg_at tfibsegs CNO_P4 regs2 mem2 md2).
apply (K ly2 S2 W2 regs2 mem2 md2 res).
unfold cno_P4, cno_cp, cno_core, cno_J, cno_cpy, nx_sp0, nx_un, nx_tn, CNO_FRAME.
cbn [nx_ly nx_S nx_W nx_regs nx_mem nx_md nx_up nx_tp nx_ub nx_tb nx_live nx_peak nx_cnt].
split; [split; [split; [exact HJ2|]|]|].
- split; [exact HFR2|]. split; [unfold spZ in *; rewrite P2, Q2; lia|].
  split; [rewrite P3, Q3; exact Hgp|]. split; [rewrite P4, Q4; exact Htp|].
  split; [rewrite P24, Q24; exact H24|]. split; [exact HRO2|].
  split; [rewrite P26, Q26; exact H26 | rewrite P27, Q27; exact H27].
- split; [exact Hbl4|]. split; [exact Hbu2|]. split; [exact Hbt2|]. split; [exact HG2|].
  split; [rewrite P18, Q18; exact H18|]. split; [rewrite P21, Q21; exact H21 | rewrite P25, Q25; exact H25].
- split; [exact Hu1|]. split; [exact Ht1|]. split; [exact Hu2|]. split; [exact Hr4|].
  split; [exact H10r|]. split; [rewrite P23, Q23; exact R23|]. split; [rewrite P19, Q19; exact R19|].
  split; [rewrite P8, Q8; exact R8|]. split; [rewrite P9, Q9; exact R9|]. split; [rewrite P22, Q22; exact R22|].
  split; [exact Cu12|]. split; [exact Ct12 | exact Cu22].
Qed.

End S.
