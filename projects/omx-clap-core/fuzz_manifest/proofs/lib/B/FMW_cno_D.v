(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_cno_D.v at a working branch 31d1eb57a40.
   check_no_overread 0x80bd4, the reader segments: R4 0x80e04 (the UBSan overflow check of t2 + tn + 17, the shadow
   check and NUL store at t2 + tn + 17, then names (t1, u1), back at N1 0x80e2c) and N1 (s1 := the answer,
   names (t2, u2), back at N2 0x80e3c).
   What differs from A:
   - R4 starts with `bltu s2, s10, 0x80ea0` (GUARD 0x80e04; s2 = ~t2, s10 = tn + 17; the target is `unimp`). It is dead:
     t2's block [t2, t2 + tn + 18) lies below 2^64, so ~t2 >= tn + 17 (cno_not_ge). Then `add a0, s4, s10` computes the
     byte's address (A carried it in s1 from the memset segment), so the walk runs to the check pc 0x80e0c first and
     re-bases there with a0 an atom (as A's cno_A2 does at 0x80bcc).
   - u2 is s5 (A: s7); the second call passes a1 := s5.
   - names_spec (lib/B/FMH_Fn.v) asks spZ < ly_top at each call: the journal gives sp0 <= ly_top (cnoD_sp_top, the
     lemma g5_sp_top of lib/B/FMW_as_ruled.v), and the call's sp is sp0 - 112. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0l YF0m YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_cno0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the state at the check pc 0x80e0c: a0 (atom 10) = t2 + tn + 17, its one byte a writable region; s8 (atom 24) =
   the shadow base; the shadow entry says the byte at a0 is addressable ---- *)
Definition cnoD_pc_chk : Z := 0x80e0c.
Definition cnoD_blk : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 1 [].
Definition ss_cnoD : sstate :=
  mkSS cnoD_pc_chk sr_atoms [cnoD_blk] None
    (mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 16) 0); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).
Definition cnoD_Bx : sv := SOff 24 0.
Definition cnoD_SH : list shent := [mkSHE 10 0 1].

Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis FB : FmB B.                                   (* FMW_seg.v:37: code addresses, GOT/cell values, statics not owned *)
Hypothesis HB : TfibSyms B.                              (* YF0m.v:658 *)
Hypothesis IMG : fm_img_facts tfibsegs B.                (* FMH_Fn.v:61 *)
Hypothesis UNIV : fm_univ B.                             (* FMH_Fn.v:71: incl Tfib_universe (as_universe B) *)
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B ameter_triv.   (* YC5d.v:57; ameter_triv YCbp.v:17, mo_ok = True *)
Hypothesis AFREE4 : afree04_rule tfibsegs B ameter_triv.       (* YC5d.v:76 *)
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy PC_memcpy.  (* YG0d.v:318 *)
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet PC_memset.
Hypothesis NAMES : names_spec tfibsegs B CTX_lv2_locate_manifest_names.   (* FMH_Fn.v:241 *)
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- small kit ---- *)
Lemma cnoD_entry : forall (W : world tfibsegs) mem regs x,
  getr regs 24 = w64 FMW_SB -> getr regs 10 = w64 x -> 4096 <= x <= 2 ^ 47 - 16 ->
  writable_at tfibsegs (rdW W mem) x ->
  st_ok tfibsegs (Ereg regs []) ss_cnoD (restrict (w_H W) (mkst regs (Z_to_bv 64 cnoD_pc_chk) mem (seg_rom tfibsegs))).
Proof.
intros W mem regs x R24 R10 Hx Hw.
rewrite restrict_mkst_fx.
set (E := Ereg regs []).
assert (U10 : bv_unsigned (ew E 10) = x)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl), R24; unfold w64, FMW_SB, SHADOW_OFF;
      apply unsigned_lit_small; lia).
unfold ss_cnoD. apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold cnoD_blk. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
  split; [lia|]. split; [lia|]. split; [intros o Ho; replace (x + o) with x by lia; exact Hw|]. apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold cnoD_blk, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10, U24. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
Qed.
(* the run's one write is the byte x *)
Lemma cnoD_keep : forall E (W : world tfibsegs) m m' x,
  frame_of E [cnoD_blk] (rdW W m) (rdW W m') -> bv_unsigned (ew E 10) = x ->
  forall a, 0 <= a < 2 ^ 64 -> a <> x -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.
Proof.
intros E W m m' x HF Hx a Ha Hne. apply (aview_eq_of tfibsegs). apply HF.
rewrite unsigned_lit_small by lia. intros (r & [<-|[]] & Hr).
cbn [cnoD_blk YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Hx in Hr. lia.
Qed.
(* a register the run left as an atom *)
Lemma cnoD_reg_atom : forall (H : word -> bool) E ss ms (r : bv 5) n,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof. intros H E ss ms r n HS Hr. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. apply fmw_SOff0. Qed.
(* a register the run left as a computed value v, U E v = z *)
Lemma cnoD_reg_U : forall H E ss ms (r : bv 5) v z,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = v -> U E v = z -> getr (ms_regs ms) r = w64 z.
Proof.
intros H E ss ms r v z HS Hr Hz. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. unfold w64. rewrite <- Hz.
unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* an image byte is no block byte *)
Lemma cnoD_img_ne : forall ly S (W : world tfibsegs) mem md p m x a,
  AR tfibsegs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= x < p + req_size m -> in_img tfibsegs a -> a <> x.
Proof. intros ly S W mem md p m x a HAR Hin Hx Ha ->. exact (blk_img tfibsegs B LAWS ly S W mem md p m x HAR Hin Hx Ha). Qed.
Lemma cnoD_garr8_keep : forall (W W' : world tfibsegs) m m' p l,
  (forall a, p <= a < p + Z.of_nat (length l) -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  garr8 tfibsegs (rdW W m) p l -> garr8 tfibsegs (rdW W' m') p l.
Proof.
intros W W' m m' p l HK Hg. apply (garr8_frame tfibsegs _ _ p l Hg). intros a Ha. apply (mbyte_of_aview tfibsegs).
exact (HK a Ha).
Qed.
(* fm's statics ride through any step that keeps their bytes *)
Lemma cnoD_glob_img : forall (W W' : world tfibsegs) m m' live peak cnt fail,
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
(* a C string copied into a live block (its bytes and NUL, then at least 7 more block bytes) *)
Lemma cnoD_cstr_blk : forall ly S (W : world tfibsegs) mem md p m l,
  AR tfibsegs B ly S W mem md -> In (p, m) (ablocks B ly S) -> Z.of_nat (length l) + 8 <= m ->
  Z.of_nat (length l) + 1 < 2 ^ 32 ->
  garr8 tfibsegs (rdW W mem) p (l ++ [0]) -> Forall (fun c => c <> 0) l ->
  cstr_ok tfibsegs W mem p l.
Proof.
intros ly S W mem md p m l HAR Hin Hm H32 Hg Hnz.
pose proof asan_consts as (C1 & _).
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _).
rewrite Hrq in Hceil, Happ.
split; [split; [exact Hg | exact Hnz]|].
split; [exact H4096|]. split; [lia|]. split; [exact H32|].
split.
{ unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  unfold kLowMemEnd, kHighMemEnd, kHighMemBeg. lia. }
split; [apply (range_addressable_of_block tfibsegs B LAWS ly S W mem md p m p _ HAR Hin); lia|].
split.
{ destruct (al_shadow _ _ LAWS ly S W mem md p m HAR Hin) as (_ & Hhv). rewrite Hrq in Hhv.
  apply (shadow_hull_vis_sub _ p m p _ Hhv); lia. }
intros a Ha. apply (block_word_tail_vis B LAWS ly S W mem md p m HAR Hin ltac:(lia)).
pose proof (word_end_mono (p + Z.of_nat (length l)) (p + m - 1) ltac:(lia)). lia.
Qed.
(* a block's bytes ride over a journal that keeps the block (its footprint, fm's statics, is image bytes) *)
Lemma cnoD_cpy_kept : forall STK sp0 k ly S (W : world tfibsegs) mem md ly2 S2 W2 mem2 md2 p m l,
  ajournal tfibsegs B STK sp0 FM_PSTAT_FP ly S W mem md [] ly2 S2 W2 mem2 md2 k ->
  AR tfibsegs B ly S W mem md -> In (p, m) (ablocks B ly S) -> In (p, m) (ablocks B ly2 S2) ->
  0 < m -> Z.of_nat (length l) <= m ->
  garr8 tfibsegs (rdW W mem) p l -> garr8 tfibsegs (rdW W2 mem2) p l.
Proof.
intros STK sp0 k ly S W mem md ly2 S2 W2 mem2 md2 p m l HJ HAR Hin Hin2 Hm Hl Hg.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
apply (garr8_frame tfibsegs _ _ p l Hg). intros a Ha. apply (mbyte_of_aview tfibsegs).
replace a with (p + (a - p)) by lia.
apply (F2 p m (a - p) Hin Hin2); [rewrite Hrq; lia|].
intros Hfp. apply (blk_img tfibsegs B LAWS ly S W mem md p m (p + (a - p)) HAR Hin); [rewrite Hrq; lia|].
exact (pstat_img _ Hfp).
Qed.
(* a block made after the entry is not one of the entry's *)
Lemma cnoD_new_notin : forall ly S (W : world tfibsegs) mem md bl0 nb x,
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
(* the reader's peak after a second call with the same URI is the first's *)
Lemma cnoD_rt_peak_idem : forall u live peak, rt_peak u live (rt_peak u live peak) = rt_peak u live peak.
Proof. intros [|c u] live peak; cbn [rt_peak]; [reflexivity | lia]. Qed.
(* B only: names_spec asks spZ < ly_top at the call (B4b 620968d59c7); the journal's stack facts give sp0 <= ly_top at
   any point (lib/B/FMW_as_ruled.v g5_sp_top), and the call's sp is sp0 - 112 *)
Lemma cnoD_sp_top : forall STK sp0 FP ly S0 W mem md own ly' S' W' mem' md' k,
  ajournal tfibsegs B STK sp0 FP ly S0 W mem md own ly' S' W' mem' md' k -> sp0 <= ly_top ly'.
Proof.
intros STK sp0 FP ly S0 W mem md own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & _ & _ & _ & _ & _ & Htop2 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). lia.
Qed.

Lemma cno_seg_R4 : forall cx ly S W regs mem md u1 t1 u2 t2,
  cno_base B cx -> cno_R4 B cx ly S W regs mem md u1 t1 u2 t2 ->
  (forall ly' S' W' regs' mem' md', cno_N1 B cx ly' S' W' regs' mem' md' u1 t1 u2 t2 ->
     SRr tfibsegs W' (cfg_at tfibsegs CNO_N1 regs' mem' md') (cno_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs CNO_R4 regs mem md) (cno_post B cx).
Proof.
intros [ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt] ly S W regs mem md u1 t1 u2 t2 HBX HR4 KN.
pose proof HBX as (HPRE & Hra0 & H10 & H11 & H12 & H13 & Hsu & Hst & Hnzu & Hnzt & Hhu & Hht & Hlu & Htn & HG0 & HQ
  & Hlive & Hev & Hbb).
destruct HR4 as (((HJ & HFR & Hsp & Hgp & Htp & H24 & HRO) & Hbl & Hbu & Hbt & HGl) &
  Hu1 & Ht1 & Hu2 & Ht2 & R20 & R21 & R19 & R8 & R26 & R18 & Cu1 & Ct1 & Cu2 & Ct2).
unfold nx_un, nx_tn, nx_sp0, cno_J, cno_cpy, CNO_FRAME in *.
cbn [nx_ly nx_S nx_W nx_regs nx_mem nx_md nx_up nx_tp nx_ub nx_tb nx_live nx_peak nx_cnt] in *.
change (Z.of_nat (length _)) with 4 in HJ.
pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & _).
assert (FS : STK_check_no_overread = ltac:(let v := eval vm_compute in STK_check_no_overread in exact v)) by reflexivity.
assert (FN : STK_names = ltac:(let v := eval vm_compute in STK_names in exact v)) by reflexivity.
destruct HPRE as [HAP HRO0].
pose proof (fmw_sp B _ ly0 S0 W0 regs0 mem0 md0 [] HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof HAP as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnv & _).
(* the four copies *)
assert (Hbl4 : forall p m, In (p, m) [(u1, Z.of_nat (length ub) + 18); (t1, Z.of_nat (length tb) + 18);
    (u2, Z.of_nat (length ub) + 18); (t2, Z.of_nat (length tb) + 18)] -> In (p, m) (ablocks B ly S))
  by (intros p m Hpm; rewrite Hbl; apply in_or_app; right; exact Hpm).
pose proof (Hbl4 _ _ (or_introl eq_refl)) as Hin_u1.
pose proof (Hbl4 _ _ (or_intror (or_introl eq_refl))) as Hin_t1.
pose proof (Hbl4 _ _ (or_intror (or_intror (or_introl eq_refl)))) as Hin_u2.
pose proof (Hbl4 _ _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as Hin_t2.
assert (Hrqu : req_size (Z.of_nat (length ub) + 18) = Z.of_nat (length ub) + 18)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length ub) + 18) 0); lia).
assert (Hrq : req_size (Z.of_nat (length tb) + 18) = Z.of_nat (length tb) + 18)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length tb) + 18) 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u1) as (_ & _ & Hcu1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_t1) as (_ & _ & Hct1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u2) as (_ & _ & Hcu2 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_t2) as (_ & _ & Hct2 & Happ & _).
rewrite Hrqu in Hcu1, Hcu2. rewrite Hrq in Hct1, Hct2, Happ.
assert (D1 : u1 + (Z.of_nat (length ub) + 18) <= t2 \/ t2 + (Z.of_nat (length tb) + 18) <= u1).
{ pose proof (sep_blocks_pos tfibsegs B LAWS ly S W mem md (u1, Z.of_nat (length ub) + 18) (t2, Z.of_nat (length tb) + 18)
    (ablocks B ly0 S0) [(t1, Z.of_nat (length tb) + 18); (u2, Z.of_nat (length ub) + 18)] [] HAR
    ltac:(rewrite Hbl; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hrqu, Hrq in Hd. exact Hd. }
assert (D2 : t1 + (Z.of_nat (length tb) + 18) <= t2 \/ t2 + (Z.of_nat (length tb) + 18) <= t1).
{ pose proof (sep_blocks_pos tfibsegs B LAWS ly S W mem md (t1, Z.of_nat (length tb) + 18) (t2, Z.of_nat (length tb) + 18)
    (ablocks B ly0 S0 ++ [(u1, Z.of_nat (length ub) + 18)]) [(u2, Z.of_nat (length ub) + 18)] [] HAR
    ltac:(rewrite Hbl, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. exact Hd. }
assert (D3 : u2 + (Z.of_nat (length ub) + 18) <= t2 \/ t2 + (Z.of_nat (length tb) + 18) <= u2).
{ pose proof (sep_blocks_pos tfibsegs B LAWS ly S W mem md (u2, Z.of_nat (length ub) + 18) (t2, Z.of_nat (length tb) + 18)
    (ablocks B ly0 S0 ++ [(u1, Z.of_nat (length ub) + 18); (t1, Z.of_nat (length tb) + 18)]) [] [] HAR
    ltac:(rewrite Hbl, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hrqu, Hrq in Hd. exact Hd. }
(* the reader call's budgets *)
assert (Hnev : st_nev S + EV_names <= EV_MAX) by (unfold EV_check_no_overread, EV_names in *; lia).
assert (Hbb4 : blocks_bytes S + LIVE_names <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly S), Hbl, bsum_app, <- (blocks_bytes_bsum B ly0 S0).
  unfold bsum. cbn [fold_right snd]. unfold LIVE_check_no_overread, LIVE_names, MANIFEST_MAX in *. lia. }
assert (Hx : 4096 <= t2 + Z.of_nat (length tb) + 17 <= 2 ^ 47 - 16) by lia.
(* ---- 0x80e04: GUARD `bltu s2, s10, 0x80ea0` (s2 = ~t2, s10 = tn + 17) is dead; 0x80e08: a0 := s4 + s10 ---- *)
pose proof (fmw_resume_nr W regs [] mem CNO_R4) as HSr.
set (E := Ereg regs []) in HSr.
assert (E18 : ew E 18 = Z_to_bv 64 (cno_not t2)) by (subst E; rewrite (ew_Ereg_nat regs [] 18 18%bv eq_refl); exact R18).
assert (E20 : ew E 20 = Z_to_bv 64 t2) by (subst E; rewrite (ew_Ereg_nat regs [] 20 20%bv eq_refl); exact R20).
assert (E26 : ew E 26 = Z_to_bv 64 (Z.of_nat (length tb) + 17))
  by (subst E; rewrite (ew_Ereg_nat regs [] 26 26%bv eq_refl); exact R26).
unfold cfg_at. change (w64 CNO_R4) with (Z_to_bv 64 CNO_R4).
eapply SRr_sym_branch with (c := BC_LTU) (a := SOff 18 0) (b := SOff 26 0); [exact HSr | |].
{ (* taken (-> 0x80ea0 unimp): ~t2 < tn + 17 would put t2 + tn + 18 above 2^64; t2's block lies below it *)
  intros Hb _. exfalso. rewrite branch_ltu_U in Hb.
  rewrite (U_atom E 18 (cno_not t2) E18 ltac:(unfold cno_not; lia)),
    (U_atom E 26 (Z.of_nat (length tb) + 17) E26 ltac:(lia)) in Hb.
  apply Z.ltb_lt in Hb.
  pose proof (cno_not_ge t2 (Z.of_nat (length tb)) ltac:(lia) ltac:(lia) ltac:(lia)) as Hge. lia. }
intros _ HS1. clear HSr.
aj_run_to fmw_tbl_cno_ok HS1 HJ cnoD_pc_chk.
{ apply awr_ok_nil. }
rename ms into msA.
(* the run touched no memory *)
assert (SB : same_below mem (ms_mem msA) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem (ms_mem msA) |- _ => exact (frame_nil_same _ mem (ms_mem msA) H) end).
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem msA) a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha; exact (aview_below (w_H W) mem (ms_mem msA) (2 ^ 64) a SB Ha)).
pose proof HJ as (HARr & _).
lazymatch type of HS1 with st_ok _ _ ?ss _ =>
  let v := eval vm_compute in (sr_get (ss_regs ss) 10%bv) in
  assert (U10 : U E v = t2 + Z.of_nat (length tb) + 17)
    by (rewrite U_SAlu, (U_atom E 20 t2 E20), (U_atom E 26 (Z.of_nat (length tb) + 17) E26) by lia;
        cbn [zalu_raw]; rewrite zcanon_id by (unfold M64; lia); lia);
  pose proof (cnoD_reg_U _ _ _ msA 10%bv v _ HS1 ltac:(vm_compute; reflexivity) U10) as A10
end.
pose proof (fmw_reg_atom _ regs _ _ msA 2%bv 2%bv 2 HS1 ltac:(vm_compute; reflexivity) eq_refl) as A2.
pose proof (fmw_reg_atom _ regs _ _ msA 3%bv 3%bv 3 HS1 ltac:(vm_compute; reflexivity) eq_refl) as A3.
pose proof (fmw_reg_atom _ regs _ _ msA 4%bv 4%bv 4 HS1 ltac:(vm_compute; reflexivity) eq_refl) as A4.
pose proof (fmw_reg_atom _ regs _ _ msA 8%bv 8%bv 8 HS1 ltac:(vm_compute; reflexivity) eq_refl) as A8.
pose proof (fmw_reg_atom _ regs _ _ msA 19%bv 19%bv 19 HS1 ltac:(vm_compute; reflexivity) eq_refl) as A19.
pose proof (fmw_reg_atom _ regs _ _ msA 20%bv 20%bv 20 HS1 ltac:(vm_compute; reflexivity) eq_refl) as A20.
pose proof (fmw_reg_atom _ regs _ _ msA 21%bv 21%bv 21 HS1 ltac:(vm_compute; reflexivity) eq_refl) as A21.
pose proof (fmw_reg_atom _ regs _ _ msA 24%bv 24%bv 24 HS1 ltac:(vm_compute; reflexivity) eq_refl) as A24.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ msA HS1 eq_refl). cbn [ss_pc].
clear HS1.
(* ---- re-based at 0x80e0c: the shadow check of the byte at a0 = t2 + tn + 17, sb zero, a0 := t1, a1 := u1, call
   names ---- *)
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARr Hin_t2) as (_ & _ & _ & _ & Hpres2 & _).
rewrite Hrq in Hpres2.
assert (Hw : writable_at tfibsegs (rdW W (ms_mem msA)) (t2 + Z.of_nat (length tb) + 17))
  by (apply (apresent_writable tfibsegs); exact (proj1 (Hpres2 (t2 + Z.of_nat (length tb) + 17) ltac:(lia)))).
assert (G24A : getr (ms_regs msA) 24 = w64 FMW_SB) by (rewrite A24; exact H24).
pose proof (cnoD_entry W (ms_mem msA) (ms_regs msA) (t2 + Z.of_nat (length tb) + 17) G24A A10 Hx Hw) as HS.
set (E2 := Ereg (ms_regs msA) []) in HS.
assert (U10' : bv_unsigned (ew E2 10) = t2 + Z.of_nat (length tb) + 17)
  by (unfold E2; rewrite (ew_Ereg_nat (ms_regs msA) _ 10 10%bv eq_refl), A10; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok tfibsegs cnoD_Bx cnoD_SH E2
  (rdW W (ms_mem (mkst (ms_regs msA) (Z_to_bv 64 cnoD_pc_chk) (ms_mem msA) (seg_rom tfibsegs))))).
{ constructor; [|constructor]. cbn [ms_mem].
  apply (shent_ok_of_range tfibsegs (w_H W) (ms_mem msA) E2 cnoD_Bx 10 t2 (Z.of_nat (length tb) + 18)
    (t2 + Z.of_nat (length tb) + 17) 0 1).
  - apply (range_addressable_of_block tfibsegs B LAWS ly S W (ms_mem msA) _ t2 _ t2 (Z.of_nat (length tb) + 18) HARr Hin_t2);
      lia.
  - unfold cnoD_Bx. apply U_atom;
      [unfold E2; rewrite (ew_Ereg_nat (ms_regs msA) _ 24 24%bv eq_refl); exact G24A | unfold SHADOW_OFF; lia].
  - apply U_atom; [unfold E2; rewrite (ew_Ereg_nat (ms_regs msA) _ 10 10%bv eq_refl); exact A10 | lia].
  - lia.
  - lia.
  - intros y Hy. cbn [Z.min Z.max] in Hy.
    unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
assert (Hnew : ~ In (t2, Z.of_nat (length tb) + 18) (ablocks B ly0 S0)).
{ apply (cnoD_new_notin ly S W mem md _ _ _ HAR Hbl). repeat (first [left; reflexivity | right]). }
change (ms_mem msA) with (ms_mem (mkst (ms_regs msA) (Z_to_bv 64 cnoD_pc_chk) (ms_mem msA) (seg_rom tfibsegs))) in HJ.
aj_run_to_tok fmw_tbl_cno_ok HS HJ SHOK fmw_Bspan A_names.
{ unfold ss_cnoD. cbn [ss_mem].
  eapply awr_ok_cons_gen with (k := 10%nat) (b := t2 + Z.of_nat (length tb) + 17); [reflexivity | exact U10' | | apply awr_ok_nil].
  intros a Ha. cbn [cnoD_blk YP09.r_wlo YP09.r_whi] in Ha. left; right; right; left.
  exists t2, (Z.of_nat (length tb) + 18). split; [exact Hin_t2|]. split; [exact Hnew|]. rewrite Hrq. lia. }
rewrite ?wvb_collapse in HJ.
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E1 := Ex) in HS end.
match goal with H : frame_of E2 _ (rdW W (ms_mem msA)) (rdW W (ms_mem ms)) |- _ => rename H into HFm end.
change (ss_mem ss_cnoD) with [cnoD_blk] in HFm.
pose proof (cnoD_keep E2 W (ms_mem msA) (ms_mem ms) _ HFm U10') as KEEP0.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> a <> t2 + Z.of_nat (length tb) + 17 ->
  aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha Hne; rewrite (KEEP0 a Ha Hne); exact (AVB a Ha)).
pose proof HJ as (HARc & _).
assert (AG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E1 n = getr (ms_regs msA) r)
  by (intros n r Hn Hr; unfold E1; rewrite !ew_ewset_other by lia; unfold E2; apply ew_Ereg_nat; exact Hr).
pose proof (fmw_reg_lit _ E1 _ ms 1%bv 0x80e2c HS ltac:(vm_compute; reflexivity) ltac:(lia)) as Q1.
pose proof (eq_trans (eq_trans (cnoD_reg_atom _ E1 _ ms 2%bv 2 HS ltac:(vm_compute; reflexivity))
  (AG 2%nat 2%bv ltac:(lia) eq_refl)) A2) as Q2.
pose proof (eq_trans (eq_trans (cnoD_reg_atom _ E1 _ ms 3%bv 3 HS ltac:(vm_compute; reflexivity))
  (AG 3%nat 3%bv ltac:(lia) eq_refl)) A3) as Q3.
pose proof (eq_trans (eq_trans (cnoD_reg_atom _ E1 _ ms 4%bv 4 HS ltac:(vm_compute; reflexivity))
  (AG 4%nat 4%bv ltac:(lia) eq_refl)) A4) as Q4.
pose proof (eq_trans (eq_trans (cnoD_reg_atom _ E1 _ ms 8%bv 8 HS ltac:(vm_compute; reflexivity))
  (AG 8%nat 8%bv ltac:(lia) eq_refl)) A8) as Q8.
pose proof (eq_trans (eq_trans (cnoD_reg_atom _ E1 _ ms 10%bv 19 HS ltac:(vm_compute; reflexivity))
  (AG 19%nat 19%bv ltac:(lia) eq_refl)) A19) as Q10.
pose proof (eq_trans (eq_trans (cnoD_reg_atom _ E1 _ ms 11%bv 8 HS ltac:(vm_compute; reflexivity))
  (AG 8%nat 8%bv ltac:(lia) eq_refl)) A8) as Q11.
pose proof (eq_trans (eq_trans (cnoD_reg_atom _ E1 _ ms 19%bv 19 HS ltac:(vm_compute; reflexivity))
  (AG 19%nat 19%bv ltac:(lia) eq_refl)) A19) as Q19.
pose proof (eq_trans (eq_trans (cnoD_reg_atom _ E1 _ ms 20%bv 20 HS ltac:(vm_compute; reflexivity))
  (AG 20%nat 20%bv ltac:(lia) eq_refl)) A20) as Q20.
pose proof (eq_trans (eq_trans (cnoD_reg_atom _ E1 _ ms 21%bv 21 HS ltac:(vm_compute; reflexivity))
  (AG 21%nat 21%bv ltac:(lia) eq_refl)) A21) as Q21.
pose proof (eq_trans (eq_trans (cnoD_reg_atom _ E1 _ ms 24%bv 24 HS ltac:(vm_compute; reflexivity))
  (AG 24%nat 24%bv ltac:(lia) eq_refl)) A24) as Q24.
assert (Hspc : spZ (ms_regs ms) = spZ regs0 + -112) by (unfold spZ in *; rewrite Q2; lia).
(* what the store kept *)
assert (HFRc : cno_frame (mkNX ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt) W (ms_mem ms)).
{ apply (cno_frame_kept _ W W mem (ms_mem ms)); [|exact HFR]. intros a Ha. unfold nx_sp0, CNO_FRAME in Ha.
  cbn [nx_regs] in Ha. apply KEEP; lia. }
assert (HROc : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) (ms_mem ms))).
{ intros a Ha Ho He. pose proof (roP_img a Ha) as Hi. pose proof (HSL a Hi) as Hl. unfold kLowMemEnd in Hl.
  rewrite (KEEP a ltac:(lia) (cnoD_img_ne ly S W mem md t2 _ (t2 + Z.of_nat (length tb) + 17) a HAR Hin_t2
    ltac:(rewrite Hrq; lia) Hi)).
  exact (HRO a Ha Ho He). }
assert (HGc : fm_glob tfibsegs W (ms_mem ms) live peak cnt SIZE_MAXZ).
{ apply (cnoD_glob_img W W mem (ms_mem ms)); [|exact HGl]. intros a Ha.
  pose proof (pstat_img a Ha) as Hi. pose proof (HSL a Hi) as Hl. unfold kLowMemEnd in Hl.
  exact (KEEP a ltac:(lia) (cnoD_img_ne ly S W mem md t2 _ (t2 + Z.of_nat (length tb) + 17) a HAR Hin_t2
    ltac:(rewrite Hrq; lia) Hi)). }
assert (Cu1c : garr8 tfibsegs (rdW W (ms_mem ms)) u1 (ub ++ [0])).
{ apply (cnoD_garr8_keep W W mem (ms_mem ms) u1 _); [|exact Cu1].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KEEP; lia. }
assert (Ct1c : garr8 tfibsegs (rdW W (ms_mem ms)) t1 (tb ++ [0])).
{ apply (cnoD_garr8_keep W W mem (ms_mem ms) t1 _); [|exact Ct1].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KEEP; lia. }
assert (Cu2c : garr8 tfibsegs (rdW W (ms_mem ms)) u2 (ub ++ [0])).
{ apply (cnoD_garr8_keep W W mem (ms_mem ms) u2 _); [|exact Cu2].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KEEP; lia. }
assert (Ct2c : garr8 tfibsegs (rdW W (ms_mem ms)) t2 (tb ++ [0])).
{ apply (cnoD_garr8_keep W W mem (ms_mem ms) t2 _); [|exact Ct2].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KEEP; lia. }
(* ---- the call of lv2_locate_manifest_names (t1, u1) at 0x80e28 ---- *)
assert (Htc : cstr_ok tfibsegs W (ms_mem ms) t1 tb)
  by (apply (cnoD_cstr_blk ly S W (ms_mem ms) _ t1 _ tb HARc Hin_t1); [lia | unfold MANIFEST_MAX in Htn; lia | exact Ct1c | exact Hnzt]).
assert (Huc : cstr_ok tfibsegs W (ms_mem ms) u1 ub)
  by (apply (cnoD_cstr_blk ly S W (ms_mem ms) _ u1 _ ub HARc Hin_u1); [lia | lia | exact Cu1c | exact Hnzu]).
assert (Hkt : cstr_kept B ly S t1 tb) by (left; exists t1, (Z.of_nat (length tb) + 18); split; [exact Hin_t1 | lia]).
assert (Hku : cstr_kept B ly S u1 ub) by (left; exists u1, (Z.of_nat (length ub) + 18); split; [exact Hin_u1 | lia]).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E1 _ ms HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (MD := m) in * end.
assert (HPREc : fpre tfibsegs B STK_names ly S W (ms_regs ms) (ms_mem ms) MD []).
{ split; [|exact HROc].
  apply (afn_pre_at tfibsegs B STK_check_no_overread (spZ regs0) FM_PSTAT_FP ly0 S0 W0 mem0 md0 [] ly S W (ms_mem ms) _ 4
    (ms_regs ms) STK_names (-112) [] HJ Hspc).
  all: first [ reflexivity | (rewrite ?FS, ?FN; lia)
             | (rewrite Q1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity)
             | (unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia)
             | (rewrite Q3, Hgp; exact Hgp0) | (rewrite Q4, Htp; exact Htp0)
             | (apply achain_low; unfold s0Z; rewrite Q8, R8; unfold w64; rewrite unsigned_lit_small by lia; lia) ]. }
assert (HCTX : In (raZ (ms_regs ms) :: spine []) CTX_lv2_locate_manifest_names).
{ unfold raZ. rewrite Q1, unsigned_lit_small by lia. cbn [spine map].
  unfold CTX_lv2_locate_manifest_names. repeat (first [left; reflexivity | right]). }
assert (Htop0 : spZ regs0 <= ly_top ly) by exact (cnoD_sp_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
assert (HTOP : spZ (ms_regs ms) < ly_top ly).
{ rewrite Hspc. apply (Z.lt_le_trans _ (spZ regs0 + 0)).
  - apply (proj1 (Z.add_lt_mono_l (-112) 0 (spZ regs0))). reflexivity.
  - rewrite Z.add_0_r. exact Htop0. }
eapply SRr_bind;
  [exact (NAMES ly S W (ms_regs ms) (ms_mem ms) _ [] t1 u1 tb ub live peak cnt SIZE_MAXZ HPREc HCTX HTOP
     ltac:(rewrite Q10; exact R19) ltac:(rewrite Q11; exact R8) Htc Huc Hkt Hku Hlu Htn HGc Hlive
     ltac:(destruct HQ as (_ & _ & Hc2); lia) Hnev Hbb4) |].
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & HP2 & (res & H10c & Hperm2 & HNR)).
destruct (names_res_quiet W2 mem2 tb ub live peak cnt SIZE_MAXZ res HNR
  ltac:(destruct HQ as (_ & Hc0 & Hc2); split; [reflexivity | lia])) as [Hres HG2].
(* ---- back at 0x80e2c ---- *)
pose proof (ajournal_sub_incl B STK_check_no_overread (spZ regs0) FM_PSTAT_FP ly0 S0 W0 mem0 md0 [] ly S W (ms_mem ms) _ 4
  STK_names (spZ (ms_regs ms)) FM_PSTAT_FP [] ly2 S2 W2 mem2 md2 EV_names HJ HJc ltac:(rewrite Hspc, FS, FN; lia)
  ltac:(rewrite Hspc; lia) (fun a Ha => Ha)) as HJ2.
cbn [app] in HJ2.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _).
assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (fmw_pres _ _ 2%bv HP2 ltac:(fmw_cs_side)).
assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (fmw_pres _ _ 3%bv HP2 ltac:(fmw_cs_side)).
assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (fmw_pres _ _ 4%bv HP2 ltac:(fmw_cs_side)).
assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (fmw_pres _ _ 8%bv HP2 ltac:(fmw_cs_side)).
assert (P19 : getr regs2 19 = getr (ms_regs ms) 19) by exact (fmw_pres _ _ 19%bv HP2 ltac:(fmw_cs_side)).
assert (P20 : getr regs2 20 = getr (ms_regs ms) 20) by exact (fmw_pres _ _ 20%bv HP2 ltac:(fmw_cs_side)).
assert (P21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (fmw_pres _ _ 21%bv HP2 ltac:(fmw_cs_side)).
assert (P24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (fmw_pres _ _ 24%bv HP2 ltac:(fmw_cs_side)).
assert (HFR2 : cno_frame (mkNX ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt) W2 mem2).
{ apply (cno_frame_kept _ W W2 (ms_mem ms) mem2); [|exact HFRc]. intros a Ha. unfold nx_sp0, CNO_FRAME in Ha.
  cbn [nx_regs] in Ha. apply F1c; [lia | rewrite Hspc, FN; lia]. }
assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W2) mem2))
  by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc pstat_closed pstat_not_roP HROc).
assert (Hu2' : In (u2, Z.of_nat (length ub) + 18) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm2) Hin_u2).
assert (Ht2' : In (t2, Z.of_nat (length tb) + 18) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm2) Hin_t2).
rewrite Q1.
change (mkCfg (mkst regs2 (Z_to_bv 64 0x80e2c) mem2 (seg_rom tfibsegs)) md2) with (cfg_at tfibsegs CNO_N1 regs2 mem2 md2).
apply (KN ly2 S2 W2 regs2 mem2 md2).
unfold cno_N1, cno_rd, cno_core, cno_J, cno_glob, cno_cpy, nx_sp0, nx_un, nx_tn, CNO_FRAME.
cbn [nx_ly nx_S nx_W nx_regs nx_mem nx_md nx_up nx_tp nx_ub nx_tb nx_live nx_peak nx_cnt].
split; [split; [split|] |].
- exact HJ2.
- split; [exact HFR2|]. split; [unfold spZ in *; rewrite P2, Q2; lia|].
  split; [rewrite P3, Q3; exact Hgp|]. split; [rewrite P4, Q4; exact Htp|].
  split; [rewrite P24, Q24; exact H24 | exact HRO2].
- split; [rewrite <- Hbl; exact Hperm2|].
  split; [exact Hu1|]. split; [exact Ht1|]. split; [exact Hu2|]. split; [exact Ht2|].
  split; [rewrite P20, Q20; exact R20|]. split; [rewrite P21, Q21; exact R21|].
  split; [rewrite P19, Q19; exact R19 | rewrite P8, Q8; exact R8].
- split; [rewrite H10c, Hres; reflexivity|].
  split.
  { apply (cnoD_cpy_kept _ _ _ ly S W (ms_mem ms) _ ly2 S2 W2 mem2 md2 u2 _ _ HJc HARc Hin_u2 Hu2'); [lia | | exact Cu2c].
    rewrite length_app. cbn [length]. lia. }
  split.
  { apply (cnoD_cpy_kept _ _ _ ly S W (ms_mem ms) _ ly2 S2 W2 mem2 md2 t2 _ _ HJc HARc Hin_t2 Ht2'); [lia | | exact Ct2c].
    rewrite length_app. cbn [length]. lia. }
  exact HG2.
Qed.

Lemma cno_seg_N1 : forall cx ly S W regs mem md u1 t1 u2 t2,
  cno_base B cx -> cno_N1 B cx ly S W regs mem md u1 t1 u2 t2 ->
  (forall ly' S' W' regs' mem' md', cno_N2 B cx ly' S' W' regs' mem' md' u1 t1 u2 t2 ->
     SRr tfibsegs W' (cfg_at tfibsegs CNO_N2 regs' mem' md') (cno_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs CNO_N1 regs mem md) (cno_post B cx).
Proof.
intros [ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt] ly S W regs mem md u1 t1 u2 t2 HBX HN1 KN.
pose proof HBX as (HPRE & Hra0 & H10 & H11 & H12 & H13 & Hsu & Hst & Hnzu & Hnzt & Hhu & Hht & Hlu & Htn & HG0 & HQ
  & Hlive & Hev & Hbb).
destruct HN1 as (((HJ & HFR & Hsp & Hgp & Htp & H24 & HRO) & Hperm & Hu1 & Ht1 & Hu2 & Ht2 & R20 & R21 & R19 & R8) &
  R10 & Cu2 & Ct2 & HGl).
unfold nx_un, nx_tn, nx_sp0, cno_J, cno_cpy, cno_glob, CNO_FRAME in *.
cbn [nx_ly nx_S nx_W nx_regs nx_mem nx_md nx_up nx_tp nx_ub nx_tb nx_live nx_peak nx_cnt] in *.
change (if 1 =? 0 then peak else rt_peak ub live peak) with (rt_peak ub live peak) in HGl.
pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & _).
assert (FS : STK_check_no_overread = ltac:(let v := eval vm_compute in STK_check_no_overread in exact v)) by reflexivity.
assert (FN : STK_names = ltac:(let v := eval vm_compute in STK_names in exact v)) by reflexivity.
destruct HPRE as [HAP HRO0].
pose proof (fmw_sp B _ ly0 S0 W0 regs0 mem0 md0 [] HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof HAP as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnv & _).
assert (Hbl4 : forall p m, In (p, m) [(u1, Z.of_nat (length ub) + 18); (t1, Z.of_nat (length tb) + 18);
    (u2, Z.of_nat (length ub) + 18); (t2, Z.of_nat (length tb) + 18)] -> In (p, m) (ablocks B ly S))
  by (intros p m Hpm; apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; exact Hpm).
pose proof (Hbl4 _ _ (or_introl eq_refl)) as Hin_u1.
pose proof (Hbl4 _ _ (or_intror (or_intror (or_introl eq_refl)))) as Hin_u2.
pose proof (Hbl4 _ _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as Hin_t2.
assert (Hrqu : req_size (Z.of_nat (length ub) + 18) = Z.of_nat (length ub) + 18)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length ub) + 18) 0); lia).
assert (Hrq : req_size (Z.of_nat (length tb) + 18) = Z.of_nat (length tb) + 18)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length tb) + 18) 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u1) as (_ & _ & Hcu1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u2) as (_ & _ & Hcu2 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_t2) as (_ & _ & Hct2 & _).
rewrite Hrqu in Hcu1, Hcu2. rewrite Hrq in Hct2.
assert (Hnev : st_nev S + EV_names <= EV_MAX) by (unfold EV_check_no_overread, EV_names in *; lia).
assert (Hbb4 : blocks_bytes S + LIVE_names <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ Hperm), bsum_app, <- (blocks_bytes_bsum B ly0 S0).
  unfold bsum. cbn [fold_right snd]. unfold LIVE_check_no_overread, LIVE_names, MANIFEST_MAX in *. lia. }
assert (Hc1 : 0 <= (if (length ub =? 0)%nat then cnt else cnt + 1) /\
  (if (length ub =? 0)%nat then cnt else cnt + 1) + 1 < 2 ^ 33)
  by (destruct HQ as (_ & Hc0 & Hc2); destruct (length ub =? 0)%nat; lia).
(* ---- 0x80e2c: s1 := the answer; a0 := t2 (s4), a1 := u2 (s5); call names ---- *)
pose proof (fmw_resume_nr W regs [] mem CNO_N1) as HS.
unfold cfg_at. change (w64 CNO_N1) with (Z_to_bv 64 CNO_N1).
aj_run_to fmw_tbl_cno_ok HS HJ A_names.
{ apply awr_ok_nil. }
assert (SB : same_below mem (ms_mem ms) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem (ms_mem ms) |- _ => exact (frame_nil_same _ mem (ms_mem ms) H) end).
assert (SBc : same_below mem (ms_mem ms) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB); lia).
pose proof HJ as (HARc & _).
pose proof (fmw_reg_lit _ (Ereg regs []) _ ms 1%bv 0x80e3c HS ltac:(vm_compute; reflexivity) ltac:(lia)) as Q1.
pose proof (fmw_reg_atom _ regs [] _ ms 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl) as Q2.
pose proof (fmw_reg_atom _ regs [] _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as Q3.
pose proof (fmw_reg_atom _ regs [] _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as Q4.
pose proof (fmw_reg_atom _ regs [] _ ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as Q8.
pose proof (fmw_reg_atom _ regs [] _ ms 9%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as Q9.
pose proof (fmw_reg_atom _ regs [] _ ms 10%bv 20%bv 20 HS ltac:(vm_compute; reflexivity) eq_refl) as Q10.
pose proof (fmw_reg_atom _ regs [] _ ms 11%bv 21%bv 21 HS ltac:(vm_compute; reflexivity) eq_refl) as Q11.
pose proof (fmw_reg_atom _ regs [] _ ms 19%bv 19%bv 19 HS ltac:(vm_compute; reflexivity) eq_refl) as Q19.
pose proof (fmw_reg_atom _ regs [] _ ms 20%bv 20%bv 20 HS ltac:(vm_compute; reflexivity) eq_refl) as Q20.
pose proof (fmw_reg_atom _ regs [] _ ms 21%bv 21%bv 21 HS ltac:(vm_compute; reflexivity) eq_refl) as Q21.
pose proof (fmw_reg_atom _ regs [] _ ms 24%bv 24%bv 24 HS ltac:(vm_compute; reflexivity) eq_refl) as Q24.
assert (Hspc : spZ (ms_regs ms) = spZ regs0 + -112) by (unfold spZ in *; rewrite Q2; lia).
assert (HFRc : cno_frame (mkNX ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt) W (ms_mem ms))
  by (apply (cno_frame_below _ W mem (ms_mem ms) SB); unfold nx_sp0, CNO_FRAME; cbn [nx_regs]; [lia | lia | exact HFR]).
pose proof (arodata_below B W mem (ms_mem ms) SBc HRO) as HROc.
pose proof (fm_glob_below W mem (ms_mem ms) _ _ _ _ SBc HGl) as HGc.
assert (Cu2c : garr8 tfibsegs (rdW W (ms_mem ms)) u2 (ub ++ [0])).
{ apply (cnoD_garr8_keep W W mem (ms_mem ms) u2 _); [|exact Cu2].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply (aview_below (w_H W) mem (ms_mem ms) (2 ^ 64) a SB). lia. }
assert (Ct2c : garr8 tfibsegs (rdW W (ms_mem ms)) t2 (tb ++ [0])).
{ apply (cnoD_garr8_keep W W mem (ms_mem ms) t2 _); [|exact Ct2].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply (aview_below (w_H W) mem (ms_mem ms) (2 ^ 64) a SB). lia. }
assert (Htc : cstr_ok tfibsegs W (ms_mem ms) t2 tb)
  by (apply (cnoD_cstr_blk ly S W (ms_mem ms) _ t2 _ tb HARc Hin_t2); [lia | unfold MANIFEST_MAX in Htn; lia | exact Ct2c | exact Hnzt]).
assert (Huc : cstr_ok tfibsegs W (ms_mem ms) u2 ub)
  by (apply (cnoD_cstr_blk ly S W (ms_mem ms) _ u2 _ ub HARc Hin_u2); [lia | lia | exact Cu2c | exact Hnzu]).
assert (Hkt : cstr_kept B ly S t2 tb) by (left; exists t2, (Z.of_nat (length tb) + 18); split; [exact Hin_t2 | lia]).
assert (Hku : cstr_kept B ly S u2 ub) by (left; exists u2, (Z.of_nat (length ub) + 18); split; [exact Hin_u2 | lia]).
assert (HPREc : fpre tfibsegs B STK_names ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) []).
{ split; [|exact HROc].
  apply (afn_pre_at tfibsegs B STK_check_no_overread (spZ regs0) FM_PSTAT_FP ly0 S0 W0 mem0 md0 [] ly S W (ms_mem ms) _ _
    (ms_regs ms) STK_names (-112) [] HJ Hspc).
  all: first [ reflexivity | (rewrite ?FS, ?FN; lia)
             | (rewrite Q1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity)
             | (unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia)
             | (rewrite Q3, Hgp; exact Hgp0) | (rewrite Q4, Htp; exact Htp0)
             | (apply achain_low; unfold s0Z; rewrite Q8, R8; unfold w64; rewrite unsigned_lit_small by lia; lia) ]. }
assert (HCTX : In (raZ (ms_regs ms) :: spine []) CTX_lv2_locate_manifest_names).
{ unfold raZ. rewrite Q1, unsigned_lit_small by lia. cbn [spine map].
  unfold CTX_lv2_locate_manifest_names. repeat (first [left; reflexivity | right]). }
assert (Htop0 : spZ regs0 <= ly_top ly) by exact (cnoD_sp_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
assert (HTOP : spZ (ms_regs ms) < ly_top ly).
{ rewrite Hspc. apply (Z.lt_le_trans _ (spZ regs0 + 0)).
  - apply (proj1 (Z.add_lt_mono_l (-112) 0 (spZ regs0))). reflexivity.
  - rewrite Z.add_0_r. exact Htop0. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) (Ereg regs []) _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind;
  [exact (NAMES ly S W (ms_regs ms) (ms_mem ms) _ [] t2 u2 tb ub live _ _ SIZE_MAXZ HPREc HCTX HTOP
     ltac:(rewrite Q10; exact R20) ltac:(rewrite Q11; exact R21) Htc Huc Hkt Hku Hlu Htn HGc Hlive
     ltac:(lia) Hnev Hbb4) |].
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & HP2 & (res & H10c & Hperm2 & HNR)).
destruct (names_res_quiet W2 mem2 tb ub live _ _ SIZE_MAXZ res HNR
  ltac:(split; [reflexivity | lia])) as [Hres HG2].
(* ---- back at 0x80e3c ---- *)
pose proof (ajournal_sub_incl B STK_check_no_overread (spZ regs0) FM_PSTAT_FP ly0 S0 W0 mem0 md0 [] ly S W (ms_mem ms) _ _
  STK_names (spZ (ms_regs ms)) FM_PSTAT_FP [] ly2 S2 W2 mem2 md2 EV_names HJ HJc ltac:(rewrite Hspc, FS, FN; lia)
  ltac:(rewrite Hspc; lia) (fun a Ha => Ha)) as HJ2.
cbn [app] in HJ2. replace (4 + EV_names + EV_names) with (4 + 2 * EV_names) in HJ2 by (unfold EV_names; lia).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _).
assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (fmw_pres _ _ 2%bv HP2 ltac:(fmw_cs_side)).
assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (fmw_pres _ _ 3%bv HP2 ltac:(fmw_cs_side)).
assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (fmw_pres _ _ 4%bv HP2 ltac:(fmw_cs_side)).
assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (fmw_pres _ _ 8%bv HP2 ltac:(fmw_cs_side)).
assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (fmw_pres _ _ 9%bv HP2 ltac:(fmw_cs_side)).
assert (P19 : getr regs2 19 = getr (ms_regs ms) 19) by exact (fmw_pres _ _ 19%bv HP2 ltac:(fmw_cs_side)).
assert (P20 : getr regs2 20 = getr (ms_regs ms) 20) by exact (fmw_pres _ _ 20%bv HP2 ltac:(fmw_cs_side)).
assert (P21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (fmw_pres _ _ 21%bv HP2 ltac:(fmw_cs_side)).
assert (P24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (fmw_pres _ _ 24%bv HP2 ltac:(fmw_cs_side)).
assert (HFR2 : cno_frame (mkNX ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt) W2 mem2).
{ apply (cno_frame_kept _ W W2 (ms_mem ms) mem2); [|exact HFRc]. intros a Ha. unfold nx_sp0, CNO_FRAME in Ha.
  cbn [nx_regs] in Ha. apply F1c; [lia | rewrite Hspc, FN; lia]. }
assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W2) mem2))
  by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc pstat_closed pstat_not_roP HROc).
rewrite Q1.
change (mkCfg (mkst regs2 (Z_to_bv 64 0x80e3c) mem2 (seg_rom tfibsegs)) md2) with (cfg_at tfibsegs CNO_N2 regs2 mem2 md2).
apply (KN ly2 S2 W2 regs2 mem2 md2).
unfold cno_N2, cno_rd, cno_core, cno_J, cno_glob, nx_sp0, nx_un, nx_tn, CNO_FRAME.
cbn [nx_ly nx_S nx_W nx_regs nx_mem nx_md nx_up nx_tp nx_ub nx_tb nx_live nx_peak nx_cnt].
split; [split; [split|] |].
- exact HJ2.
- split; [exact HFR2|]. split; [unfold spZ in *; rewrite P2, Q2; lia|].
  split; [rewrite P3, Q3; exact Hgp|]. split; [rewrite P4, Q4; exact Htp|].
  split; [rewrite P24, Q24; exact H24 | exact HRO2].
- split; [exact (perm_trans Hperm2 Hperm)|].
  split; [exact Hu1|]. split; [exact Ht1|]. split; [exact Hu2|]. split; [exact Ht2|].
  split; [rewrite P20, Q20; exact R20|]. split; [rewrite P21, Q21; exact R21|].
  split; [rewrite P19, Q19; exact R19 | rewrite P8, Q8; exact R8].
- split; [rewrite H10c, Hres; reflexivity|].
  split; [rewrite P9, Q9; exact R10|].
  change (if 2 =? 0 then peak else rt_peak ub live peak) with (rt_peak ub live peak).
  rewrite cnoD_rt_peak_idem in HG2.
  destruct (length ub =? 0)%nat; [exact HG2|].
  replace (cnt + 2) with (cnt + 1 + 1) by lia. exact HG2.
Qed.
End S.
