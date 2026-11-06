(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_cno_C1.v at a working branch 31d1eb57a40.
   check_no_overread 0x80bd4: segment Q1 0x80c58 -> R1 0x80c94. `s3 := ~u1`; the UBSan check `bltu s3, s4` (0x80c5c,
   u1 + un would wrap) is dead: u1's block [u1, u1 + un + 18) lies below 2^64, so ~u1 >= un + 17 (cno_not_ge);
   `a0 := u1 + un`; the inline shadow check of the byte at a0 (inside u1's block, so it passes); `sb zero, 0(a0)` stores
   the copy's NUL; the UBSan check `beq a0, -1` (0x80c7c) is dead: a0 = u1 + un <= 2^47 - 16 (the block's bound,
   carried as the symbolic state's fact on a0, which the run's branch test reads); `s9 := un + 17`;
   `memset (u1 + un + 1, 'a', 16)` fills the rest of the block past the NUL. The copy gains its NUL; every other fact of
   the copy phase rides through the store's one byte and the memset's 16 bytes. *)
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

(* ---- the state at 0x80c64 (after `add a0, s0, s4`): a0 (atom 10) = u1 + un, its one byte a writable region; s8
   (atom 24) = the shadow base; the shadow entry says the byte at a0 is addressable. a0's fact (<= 2^47 - 16) decides
   the UBSan check `beq a0, -1` at 0x80c7c. ---- *)
Definition cnoC1_blk : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 1 [].
Definition ss_cnoC1 : sstate :=
  mkSS 0x80c64 sr_atoms [cnoC1_blk] None
    (mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 16) 0); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).
Definition cnoC1_Bx : sv := SOff 24 0.
Definition cnoC1_SH : list shent := [mkSHE 10 0 1].

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
Lemma cnoC1_entry : forall (W : world tfibsegs) mem regs x,
  getr regs 24 = w64 FMW_SB -> getr regs 10 = w64 x -> 4096 <= x <= 2 ^ 47 - 16 ->
  writable_at tfibsegs (rdW W mem) x ->
  st_ok tfibsegs (Ereg regs []) ss_cnoC1 (restrict (w_H W) (mkst regs (Z_to_bv 64 0x80c64) mem (seg_rom tfibsegs))).
Proof.
intros W mem regs x R24 R10 Hx Hw.
rewrite restrict_mkst_fx.
set (E := Ereg regs []).
assert (U10 : bv_unsigned (ew E 10) = x)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl), R24; unfold w64, FMW_SB, SHADOW_OFF;
      apply unsigned_lit_small; lia).
unfold ss_cnoC1. apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold cnoC1_blk. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
  split; [lia|]. split; [lia|]. split; [intros o Ho; replace (x + o) with x by lia; exact Hw|]. apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold cnoC1_blk, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10, U24. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
Qed.
(* the store's one write is the byte x *)
Lemma cnoC1_keep : forall E (W : world tfibsegs) m m' x,
  frame_of E [cnoC1_blk] (rdW W m) (rdW W m') -> bv_unsigned (ew E 10) = x ->
  forall a, 0 <= a < 2 ^ 64 -> a <> x -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.
Proof.
intros E W m m' x HF Hx a Ha Hne. apply (aview_eq_of tfibsegs). apply HF.
rewrite unsigned_lit_small by lia. intros (r & [<-|[]] & Hr).
cbn [cnoC1_blk YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Hx in Hr. lia.
Qed.
(* a register the run left as an atom *)
Lemma cnoC1_reg_atom : forall (H : word -> bool) E ss ms (r : bv 5) n,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof. intros H E ss ms r n HS Hr. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. apply fmw_SOff0. Qed.
(* a register the run left as a computed value v, U E v = z *)
Lemma cnoC1_reg_U : forall H E ss ms (r : bv 5) v z,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = v -> U E v = z -> getr (ms_regs ms) r = w64 z.
Proof.
intros H E ss ms r v z HS Hr Hz. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. unfold w64. rewrite <- Hz.
unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* fm's statics ride through any step that keeps their bytes *)
Lemma cnoC1_glob_img : forall (W W' : world tfibsegs) m m' live peak cnt fail,
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
(* a byte window whose view is unchanged keeps its bytes *)
Lemma cnoC1_garr8_keep : forall (W : world tfibsegs) m m' p l,
  (forall a, p <= a < p + Z.of_nat (length l) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  garr8 tfibsegs (rdW W m) p l -> garr8 tfibsegs (rdW W m') p l.
Proof.
intros W m m' p l HK Hg. apply (garr8_frame tfibsegs _ _ p l Hg). intros a Ha. apply (mbyte_of_aview tfibsegs).
exact (HK a Ha).
Qed.
(* two blocks of one AR state, one from each side of a split of the block list, are disjoint *)
Lemma cnoC1_sep_in : forall ly S (W : world tfibsegs) mem md bl0 nb x y,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = bl0 ++ nb -> In x bl0 -> In y nb ->
  fst x + req_size (snd x) <= fst y \/ fst y + req_size (snd y) <= fst x.
Proof.
intros ly S W mem md bl0 nb x y HAR Hbl Hx Hy.
apply in_split in Hx as (a1 & a2 & ->). apply in_split in Hy as (b1 & b2 & ->).
pose proof (sep_blocks_pos tfibsegs B LAWS ly S W mem md x y a1 (a2 ++ b1) b2 HAR) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. apply Hd.
rewrite Hbl, <- app_assoc. cbn [app]. rewrite app_assoc. reflexivity.
Qed.
(* a block made after the entry is not one of the entry's *)
Lemma cnoC1_new_notin : forall ly S (W : world tfibsegs) mem md bl0 nb x,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = bl0 ++ nb -> In x nb -> 0 < req_size (snd x) -> ~ In x bl0.
Proof.
intros ly S W mem md bl0 nb x HAR Hbl Hx Hpos Hx0.
destruct (cnoC1_sep_in ly S W mem md bl0 nb x x HAR Hbl Hx0 Hx); lia.
Qed.
(* `not s3, s0` (xori s3, s0, -1): the 64-bit complement *)
Lemma cnoC1_not_U : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = cno_not x.
Proof.
intros E n x Hn Hx. rewrite U_SAlu, (U_atom E n x Hn Hx), U_SLit. cbn [zalu_raw].
replace (zcanon (-1)) with (2 ^ 64 - 1) by reflexivity.
rewrite lxor_allones by exact Hx. unfold cno_not. apply zcanon_id. unfold M64. lia.
Qed.

Lemma cno_seg_Q1 : forall cx ly S W regs mem md u1,
  cno_base B cx -> cno_Q1 B cx ly S W regs mem md u1 ->
  (forall ly' S' W' regs' mem' md', cno_R1 B cx ly' S' W' regs' mem' md' u1 ->
     SRr tfibsegs W' (cfg_at tfibsegs CNO_R1 regs' mem' md') (cno_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs CNO_Q1 regs mem md) (cno_post B cx).
Proof.
intros [ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt] ly S W regs mem md u1 HBX HQ1 KR.
pose proof HBX as (HPRE & Hra0 & G10 & G11 & G12 & G13 & Hsu & Hst & Hnzu & Hnzt & Hhu & Hht & Hlu & Htnm & HG0 & HQ
  & Hlive & Hev & Hbb).
destruct HPRE as [HAP HRO].
pose proof HAP as (HAR0 & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch & HQT).
destruct HQ1 as (((HJ & HFR & Hsp & Hgp & Htp & H24 & HROc) & Hbl & Hbu & Hbt & HGl) &
  Hu1 & R8 & R9 & R18 & R20 & R21 & R22 & Cu1).
unfold nx_un, nx_tn, nx_sp0, cno_J, cno_cpy in *.
cbn [nx_ly nx_S nx_W nx_regs nx_mem nx_md nx_up nx_tp nx_ub nx_tb nx_live nx_peak nx_cnt length Z.of_nat] in *.
pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
assert (FS : STK_check_no_overread = 16752) by reflexivity.
set (un := Z.of_nat (length ub)) in *.
assert (Hun0 : 0 <= un) by (unfold un; apply Zle_0_nat).
assert (Hun255 : un <= 255) by (unfold un; lia).
pose proof HJ as (HAR & _).
(* the copy's block *)
assert (Hin_u1 : In (u1, un + 18) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hrqu : req_size (un + 18) = un + 18) by (unfold req_size; destruct (Z.eqb_spec (un + 18) 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u1) as (_ & H4u1 & Hcu1 & Happ & _ & _ & _).
rewrite Hrqu in Hcu1, Happ.
assert (Hnew_u1 : ~ In (u1, un + 18) (ablocks B ly0 S0)).
{ apply (cnoC1_new_notin ly S W mem md _ _ _ HAR Hbl); [left; reflexivity | cbn [snd]; lia]. }
assert (Dsrc : forall b m, In (b, m) (ablocks B ly0 S0) -> b + req_size m <= u1 \/ u1 + (un + 18) <= b).
{ intros b m Hb. rewrite <- Hrqu.
  destruct (cnoC1_sep_in ly S W mem md _ _ (b, m) (u1, un + 18) HAR Hbl Hb (or_introl eq_refl)) as [Hd | Hd];
    cbn [fst snd] in Hd; [left | right]; lia. }
(* ---- 0x80c58: s3 := ~s0 ---- *)
pose proof (fmw_resume_nr W regs [] mem CNO_Q1) as HS.
set (E := Ereg regs []) in HS.
assert (E8 : ew E 8 = Z_to_bv 64 u1) by (subst E; rewrite (ew_Ereg_nat regs [] 8 8%bv eq_refl); exact R8).
assert (E20 : ew E 20 = Z_to_bv 64 un) by (subst E; rewrite (ew_Ereg_nat regs [] 20 20%bv eq_refl); exact R20).
unfold cfg_at. change (w64 CNO_Q1) with (Z_to_bv 64 CNO_Q1).
aj_run_to fmw_tbl_cno_ok HS HJ 0x80c5c.
{ apply awr_ok_nil. }
(* the `not` touched no memory *)
assert (SB0 : same_below mem (ms_mem ms) (2 ^ 64)) by exact (frame_nil_same E mem (ms_mem ms) HF).
clear HF HFr HG. rename ms into ms0.
(* ---- 0x80c5c: `bltu s3, s4, 0x80ea0` (UBSan: u1 + un wraps) is dead: s3 = ~u1 >= un + 17 (cno_not_ge) ---- *)
lazymatch type of HS with st_ok _ _ ?ssx _ =>
  let v := eval vm_compute in (sr_get (ss_regs ssx) 19%bv) in
  let w := eval vm_compute in (sr_get (ss_regs ssx) 20%bv) in
  assert (UA19 : U E v = cno_not u1) by (apply cnoC1_not_U; [exact E8 | lia]);
  assert (UA20 : U E w = un) by (apply (U_atom E 20 un E20); lia);
  eapply SRr_sym_branch with (c := BC_LTU) (a := v) (b := w); [exact HS | |] end.
{ intros Hb _. exfalso. rewrite branch_ltu_U, UA19, UA20 in Hb. apply Z.ltb_lt in Hb.
  pose proof (cno_not_ge u1 un ltac:(lia) Hun0 ltac:(lia)) as Hng. lia. }
intros _ HS2. clear HS.
(* ---- 0x80c60: a0 := s0 + s4 ---- *)
aj_run_to fmw_tbl_cno_ok HS2 HJ 0x80c64.
{ apply awr_ok_nil. }
rename HS2 into HS.
(* the add touched no memory *)
assert (SB1 : same_below mem (ms_mem ms) (2 ^ 64))
  by exact (same_below_trans _ _ _ _ SB0 (frame_nil_same E (ms_mem ms0) (ms_mem ms) HF)).
assert (AVB1 : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha; exact (aview_below (w_H W) mem (ms_mem ms) (2 ^ 64) a SB1 Ha)).
clear HF HFr HG SB0.
lazymatch type of HS with st_ok _ _ ?ssx _ =>
  let v := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in
  assert (UA10 : U E v = u1 + un) end.
{ rewrite U_SAlu. rewrite (U_atom E 8 u1 E8) by lia. rewrite (U_atom E 20 un E20) by lia.
  cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia. }
pose proof (cnoC1_reg_U _ _ _ ms 10%bv _ _ HS ltac:(vm_compute; reflexivity) UA10) as A10.
pose proof (cnoC1_reg_U _ _ _ ms 19%bv _ _ HS ltac:(vm_compute; reflexivity) UA19) as A19.
pose proof (fmw_reg_atom _ regs _ _ ms 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl) as A2.
pose proof (fmw_reg_atom _ regs _ _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as A3.
pose proof (fmw_reg_atom _ regs _ _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as A4.
pose proof (fmw_reg_atom _ regs _ _ ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as A8.
pose proof (fmw_reg_atom _ regs _ _ ms 9%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl) as A9.
pose proof (fmw_reg_atom _ regs _ _ ms 18%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl) as A18.
pose proof (fmw_reg_atom _ regs _ _ ms 20%bv 20%bv 20 HS ltac:(vm_compute; reflexivity) eq_refl) as A20.
pose proof (fmw_reg_atom _ regs _ _ ms 21%bv 21%bv 21 HS ltac:(vm_compute; reflexivity) eq_refl) as A21.
pose proof (fmw_reg_atom _ regs _ _ ms 22%bv 22%bv 22 HS ltac:(vm_compute; reflexivity) eq_refl) as A22.
pose proof (fmw_reg_atom _ regs _ _ ms 24%bv 24%bv 24 HS ltac:(vm_compute; reflexivity) eq_refl) as A24.
pose proof HJ as (HARa & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARa Hin_u1) as (_ & _ & _ & _ & Hpres & _).
rewrite Hrqu in Hpres.
(* ---- re-base at 0x80c64: the shadow check of the byte at a0 = u1 + un, a1 := -1, sb zero, the dead UBSan check
   `beq a0, a1` (0x80c7c), s9 := s4 + 17, a0 += 1, a1 := 'a', a2 := 16, jal memset ---- *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc].
clear HS. rename ms into msA.
assert (Hw : writable_at tfibsegs (rdW W (ms_mem msA)) (u1 + un))
  by (apply (apresent_writable tfibsegs); exact (proj1 (Hpres (u1 + un) ltac:(lia)))).
assert (A24' : getr (ms_regs msA) 24 = w64 FMW_SB) by (rewrite A24; exact H24).
(* a0 = u1 + un lies in [4096, 2^47 - 16] (u1's block is below alloc_ceiling): cnoC1_entry's fact on a0, from which
   the run decides `beq a0, a1` (a1 = 2^64 - 1) at 0x80c7c not taken *)
pose proof (cnoC1_entry W (ms_mem msA) (ms_regs msA) (u1 + un) A24' A10 ltac:(lia) Hw) as HS1.
set (E1 := Ereg (ms_regs msA) []) in HS1.
assert (U10 : bv_unsigned (ew E1 10) = u1 + un)
  by (unfold E1; rewrite (ew_Ereg_nat (ms_regs msA) _ 10 10%bv eq_refl), A10; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok tfibsegs cnoC1_Bx cnoC1_SH E1
  (rdW W (ms_mem (mkst (ms_regs msA) (Z_to_bv 64 0x80c64) (ms_mem msA) (seg_rom tfibsegs))))).
{ constructor; [|constructor]. cbn [ms_mem].
  apply (shent_ok_of_range tfibsegs (w_H W) (ms_mem msA) E1 cnoC1_Bx 10 u1 (un + 18) (u1 + un) 0 1).
  - apply (range_addressable_of_block tfibsegs B LAWS ly S W (ms_mem msA) _ u1 _ u1 (un + 18) HARa Hin_u1); lia.
  - unfold cnoC1_Bx. apply U_atom;
      [unfold E1; rewrite (ew_Ereg_nat (ms_regs msA) _ 24 24%bv eq_refl); exact A24' | unfold SHADOW_OFF; lia].
  - apply U_atom; [unfold E1; rewrite (ew_Ereg_nat (ms_regs msA) _ 10 10%bv eq_refl); exact A10 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx.
    unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
change (ms_mem msA) with (ms_mem (mkst (ms_regs msA) (Z_to_bv 64 0x80c64) (ms_mem msA) (seg_rom tfibsegs))) in HJ.
aj_run_to_tok fmw_tbl_cno_ok HS1 HJ SHOK fmw_Bspan PC_memset.
{ unfold ss_cnoC1. cbn [ss_mem].
  eapply awr_ok_cons_gen with (k := 10%nat) (b := u1 + un); [reflexivity | exact U10 | | apply awr_ok_nil].
  intros a Ha. cbn [cnoC1_blk YP09.r_wlo YP09.r_whi] in Ha. left; right; right; left.
  exists u1, (un + 18). split; [exact Hin_u1|]. split; [exact Hnew_u1|]. rewrite Hrqu. lia. }
lazymatch type of HS1 with st_ok _ ?Ex _ _ => set (E2 := Ex) in HS1 end.
match goal with H : frame_of E1 _ (rdW W (ms_mem msA)) (rdW W (ms_mem ms)) |- _ => rename H into HFm end.
change (ss_mem ss_cnoC1) with [cnoC1_blk] in HFm.
pose proof (cnoC1_keep E1 W (ms_mem msA) (ms_mem ms) _ HFm U10) as KEEP1.
assert (KEEPS : forall a, 0 <= a < 2 ^ 64 -> a <> u1 + un ->
  aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha Hne; rewrite (KEEP1 a Ha Hne); exact (AVB1 a Ha)).
pose proof HJ as (HARc & _).
assert (AG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E2 n = getr (ms_regs msA) r)
  by (intros n r Hn Hr; unfold E2; rewrite ?ew_ewset_other by lia; unfold E1; apply ew_Ereg_nat; exact Hr).
assert (E10b : ew E2 10 = Z_to_bv 64 (u1 + un)) by (rewrite (AG 10%nat 10%bv ltac:(lia) eq_refl); exact A10).
assert (E20b : ew E2 20 = Z_to_bv 64 un) by (rewrite (AG 20%nat 20%bv ltac:(lia) eq_refl), A20; exact R20).
pose proof (fmw_reg_lit _ E2 _ ms 1%bv CNO_R1 HS1 ltac:(vm_compute; reflexivity) ltac:(unfold CNO_R1; lia)) as Rra.
pose proof (fmw_reg_lit _ E2 _ ms 11%bv 0x61 HS1 ltac:(vm_compute; reflexivity) ltac:(lia)) as Ra1.
pose proof (fmw_reg_lit _ E2 _ ms 12%bv 16 HS1 ltac:(vm_compute; reflexivity) ltac:(lia)) as Ra2.
pose proof (cnoC1_reg_U _ _ _ ms 10%bv _ _ HS1 ltac:(vm_compute; reflexivity)
  (U_atom_off E2 10 (u1 + un) 1 E10b ltac:(lia) ltac:(lia))) as Ra0.
pose proof (cnoC1_reg_U _ _ _ ms 25%bv _ _ HS1 ltac:(vm_compute; reflexivity)
  (U_atom_off E2 20 un 17 E20b ltac:(lia) ltac:(lia))) as Ra25.
pose proof (eq_trans (cnoC1_reg_atom _ E2 _ ms 2%bv 2 HS1 ltac:(vm_compute; reflexivity)) (AG 2%nat 2%bv ltac:(lia) eq_refl)) as B2.
pose proof (eq_trans (cnoC1_reg_atom _ E2 _ ms 3%bv 3 HS1 ltac:(vm_compute; reflexivity)) (AG 3%nat 3%bv ltac:(lia) eq_refl)) as B3.
pose proof (eq_trans (cnoC1_reg_atom _ E2 _ ms 4%bv 4 HS1 ltac:(vm_compute; reflexivity)) (AG 4%nat 4%bv ltac:(lia) eq_refl)) as B4.
pose proof (eq_trans (cnoC1_reg_atom _ E2 _ ms 8%bv 8 HS1 ltac:(vm_compute; reflexivity)) (AG 8%nat 8%bv ltac:(lia) eq_refl)) as B8.
pose proof (eq_trans (cnoC1_reg_atom _ E2 _ ms 9%bv 9 HS1 ltac:(vm_compute; reflexivity)) (AG 9%nat 9%bv ltac:(lia) eq_refl)) as B9.
pose proof (eq_trans (cnoC1_reg_atom _ E2 _ ms 18%bv 18 HS1 ltac:(vm_compute; reflexivity)) (AG 18%nat 18%bv ltac:(lia) eq_refl)) as B18.
pose proof (eq_trans (cnoC1_reg_atom _ E2 _ ms 19%bv 19 HS1 ltac:(vm_compute; reflexivity)) (AG 19%nat 19%bv ltac:(lia) eq_refl)) as B19.
pose proof (eq_trans (cnoC1_reg_atom _ E2 _ ms 20%bv 20 HS1 ltac:(vm_compute; reflexivity)) (AG 20%nat 20%bv ltac:(lia) eq_refl)) as B20.
pose proof (eq_trans (cnoC1_reg_atom _ E2 _ ms 21%bv 21 HS1 ltac:(vm_compute; reflexivity)) (AG 21%nat 21%bv ltac:(lia) eq_refl)) as B21.
pose proof (eq_trans (cnoC1_reg_atom _ E2 _ ms 22%bv 22 HS1 ltac:(vm_compute; reflexivity)) (AG 22%nat 22%bv ltac:(lia) eq_refl)) as B22.
pose proof (eq_trans (cnoC1_reg_atom _ E2 _ ms 24%bv 24 HS1 ltac:(vm_compute; reflexivity)) (AG 24%nat 24%bv ltac:(lia) eq_refl)) as B24.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs0 + -112)
  by (unfold spZ at 1; rewrite B2, A2; unfold CNO_FRAME in Hsp; exact Hsp).
(* the stored byte: the region at a0's atom now carries the store's chunk *)
pose proof (fmw_region_nth E2 _ _ 0 _ HS1 eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
assert (U10b : bv_unsigned (ew E2 10) = u1 + un) by (rewrite E10b; apply unsigned_lit_small; lia).
pose proof (fmw_field E2 _ 10 (u1 + un) _ _ _ _ _ 0 1%N (SLit 0) 0 HR0 U10b ltac:(cbn; tauto) eq_refl
  ltac:(cbn; lia) ltac:(cbn; lia)) as V0.
rewrite Z.add_0_r in V0. change (N.to_nat 1) with 1%nat in V0.
(* the copy gains its NUL *)
assert (Cu1s : garr8 tfibsegs (rdW W (ms_mem ms)) u1 (ub ++ [0])).
{ apply (garr8_app1 tfibsegs (rdW W mem) (rdW W (ms_mem ms)) u1 ub 0); [exact Cu1 | exact V0 | lia |].
  intros a Ha. apply (mbyte_of_aview tfibsegs). apply KEEPS; lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E2 _ ms HS1 eq_refl). cbn [ss_pc].
(* ---- memset (u1 + un + 1, 'a', 16) ---- *)
eapply SRr_bind.
{ apply (aj_intrin_atS tfibsegs B LAWS HSL OSet PC_memset AMEMSET W (ms_regs ms) (ms_mem ms)
    STK_check_no_overread (spZ regs0) FM_PSTAT_FP ly0 S0 W0 mem0 md0 [] ly S _ 1 (u1 + un + 1) 0x61 16 (-112)
    (Z_to_bv 64 CNO_R1)).
  - exact HJ.
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - lia.
  - lia.
  - lia.
  - exact Hsp1.
  - reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite B3, A3, Hgp. exact Hgp0.
  - rewrite B4, A4, Htp. exact Htp0.
  - exact Rra.
  - apply ret_ok_even. rewrite unsigned_lit_small by (unfold CNO_R1; lia). reflexivity.
  - intros a Ha. split.
    + right. right. left. exists u1, (un + 18).
      split; [exact Hin_u1|]. split; [exact Hnew_u1|]. rewrite Hrqu. lia.
    + unfold ESTACK. lia.
  - apply (amem_range_of_block tfibsegs B LAWS ly S W (ms_mem ms) _ u1 (un + 18) (u1 + un + 1) 16 HARc Hin_u1);
      [lia | rewrite Hrqu; lia].
  - apply (range_addressable_of_block tfibsegs B LAWS ly S W (ms_mem ms) _ u1 (un + 18) (u1 + un + 1) 16 HARc Hin_u1);
      [lia | rewrite Hrqu; lia].
  - intros _.
    apply (shadow_hull_vis_of_block tfibsegs B LAWS ly S W (ms_mem ms) _ u1 (un + 18) (u1 + un + 1) 16 HARc Hin_u1);
      [lia | rewrite Hrqu; lia | lia].
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10r & Heff & Hfr2 & Hpres2 & Hmd).
(* ---- back at 0x80c94 (cno_R1) ---- *)
assert (KEEPM : forall a, 0 <= a < 2 ^ 64 -> ~ (u1 + un + 1 <= a < u1 + un + 1 + 16) ->
  ~ (spZ regs0 + -112 - ESTACK <= a < spZ regs0 + -112) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem ms) a)
  by (intros a Ha H1 H2; exact (Hfr2 a Ha H1 H2)).
assert (KEEPL : forall a, 0 <= a < alloc_ceiling -> ~ (u1 + un <= a < u1 + un + 17) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha H1. rewrite (KEEPM a ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia)). apply KEEPS; lia. }
(* the saved registers in the frame *)
assert (HFR2 : cno_frame (mkNX ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt) W mem2).
{ apply (cno_frame_kept _ W W mem mem2); [|exact HFR]. intros a Ha.
  unfold nx_sp0, CNO_FRAME in Ha. cbn [nx_regs] in Ha.
  rewrite (KEEPM a ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia)). apply KEEPS; lia. }
(* fm's statics and the source windows lie outside u1's block *)
assert (HG2 : fm_glob tfibsegs W mem2 live peak cnt SIZE_MAXZ).
{ apply (cnoC1_glob_img W W mem mem2); [|exact HGl]. intros a Ha.
  pose proof (fmw_img_range a (pstat_img a Ha)) as Hir. unfold FMW_IMG_LO, FMW_IMG_END in Hir.
  apply KEEPL; [lia|]. intros Hc.
  apply (blk_img tfibsegs B LAWS ly S W mem md u1 (un + 18) a HAR Hin_u1 ltac:(rewrite Hrqu; lia)).
  exact (pstat_img a Ha). }
assert (SRCK : forall p l, cno_home B ly0 S0 p l -> bytes_at tfibsegs W mem p l -> bytes_at tfibsegs W mem2 p l).
{ intros p l [-> | (b & m & Hb & Hlo & Hhi)]; [intros _; apply garr8_nil|].
  intros Hbp. unfold bytes_at in *.
  assert (Hbin : In (b, m) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; left; exact Hb).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hbin) as (_ & H4b & Hcb & _ & _ & _ & _).
  assert (Hrqb : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  destruct (Dsrc b m Hb) as [Hd | Hd].
  apply (cnoC1_garr8_keep W mem mem2 p l); [intros a Ha; apply KEEPL; lia | exact Hbp].
  apply (cnoC1_garr8_keep W mem mem2 p l); [intros a Ha; apply KEEPL; lia | exact Hbp]. }
assert (Hbu2 : bytes_at tfibsegs W mem2 up ub) by exact (SRCK up ub Hhu Hbu).
assert (Hbt2 : bytes_at tfibsegs W mem2 tp tb) by exact (SRCK tp tb Hht Hbt).
(* the copy and its NUL lie below the memset's window *)
assert (Cu12 : garr8 tfibsegs (rdW W mem2) u1 (ub ++ [0])).
{ apply (cnoC1_garr8_keep W (ms_mem ms) mem2 u1 (ub ++ [0])); [|exact Cu1s].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply KEEPM; [lia | lia | unfold ESTACK; lia]. }
(* the registers *)
assert (Q2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (fmw_pres _ _ 2%bv HP2 ltac:(fmw_cs_side)).
assert (Q3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (fmw_pres _ _ 3%bv HP2 ltac:(fmw_cs_side)).
assert (Q4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (fmw_pres _ _ 4%bv HP2 ltac:(fmw_cs_side)).
assert (Q8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (fmw_pres _ _ 8%bv HP2 ltac:(fmw_cs_side)).
assert (Q9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (fmw_pres _ _ 9%bv HP2 ltac:(fmw_cs_side)).
assert (Q18 : getr regs2 18 = getr (ms_regs ms) 18) by exact (fmw_pres _ _ 18%bv HP2 ltac:(fmw_cs_side)).
assert (Q19 : getr regs2 19 = getr (ms_regs ms) 19) by exact (fmw_pres _ _ 19%bv HP2 ltac:(fmw_cs_side)).
assert (Q20 : getr regs2 20 = getr (ms_regs ms) 20) by exact (fmw_pres _ _ 20%bv HP2 ltac:(fmw_cs_side)).
assert (Q21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (fmw_pres _ _ 21%bv HP2 ltac:(fmw_cs_side)).
assert (Q22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (fmw_pres _ _ 22%bv HP2 ltac:(fmw_cs_side)).
assert (Q24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (fmw_pres _ _ 24%bv HP2 ltac:(fmw_cs_side)).
assert (Q25 : getr regs2 25 = getr (ms_regs ms) 25) by exact (fmw_pres _ _ 25%bv HP2 ltac:(fmw_cs_side)).
assert (Hsp2 : spZ regs2 = spZ regs0 - CNO_FRAME)
  by (unfold spZ in Hsp1 |- *; rewrite Q2; unfold CNO_FRAME; lia).
assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) mem2))
  by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 pstat_closed pstat_not_roP HRO).
change (mkCfg (mkst regs2 (Z_to_bv 64 CNO_R1) mem2 (seg_rom tfibsegs)) md2)
  with (cfg_at tfibsegs CNO_R1 regs2 mem2 md2).
apply (KR ly S W regs2 mem2 md2).
unfold cno_R1, cno_cp, cno_core, cno_J, cno_cpy, nx_sp0, nx_un, nx_tn.
cbn [nx_ly nx_S nx_W nx_regs nx_mem nx_md nx_up nx_tp nx_ub nx_tb nx_live nx_peak nx_cnt length Z.of_nat].
split; [split; [split; [exact HJ2|]|]|].
- split; [exact HFR2|]. split; [exact Hsp2|].
  split; [rewrite Q3, B3, A3; exact Hgp|]. split; [rewrite Q4, B4, A4; exact Htp|].
  split; [rewrite Q24, B24, A24; exact H24 | exact HRO2].
- split; [exact Hbl|]. split; [exact Hbu2|]. split; [exact Hbt2 | exact HG2].
- split; [exact Hu1|].
  split; [rewrite Q8, B8, A8; exact R8|]. split; [rewrite Q9, B9, A9; exact R9|].
  split; [rewrite Q18, B18, A18; exact R18|]. split; [rewrite Q20, B20, A20; exact R20|].
  split; [rewrite Q21, B21, A21; exact R21|]. split; [rewrite Q22, B22, A22; exact R22|].
  split; [rewrite Q19, B19; exact A19|]. split; [rewrite Q25; exact Ra25|].
  exact Cu12.
Qed.

End S.
