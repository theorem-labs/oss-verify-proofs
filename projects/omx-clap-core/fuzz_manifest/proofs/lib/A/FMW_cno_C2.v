(* check_no_overread 0x80b20: segments Q3 -> R3 and Q4 -> R4. Each is `a0 := copy + n; sN := copy + n + 17;
   memset (a0, 0, 17)`: the 17 zero bytes land inside the copy's own block, so the copy gains its NUL and every other
   fact of the copy phase rides through the call's frame. *)
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
Hypothesis FB : FmB B.                                   (* FMW_seg.v:32: code addresses, GOT/cell values, statics not owned *)
Hypothesis HB : TfibSyms B.                              (* AF0m.v:564 *)
Hypothesis IMG : fm_img_facts tfibsegs B.                (* FMH_Fn.v:56 *)
Hypothesis UNIV : fm_univ B.                             (* FMH_Fn.v:70: incl Tfib_universe (as_universe B) *)
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B ameter_triv.   (* YC5d.v:57; ameter_triv YCbp.v:17, mo_ok = True *)
Hypothesis AFREE4 : afree04_rule tfibsegs B ameter_triv.       (* YC5d.v:76 *)
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy PC_memcpy.  (* YG0d.v:318 *)
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet PC_memset.
Hypothesis NAMES : names_spec tfibsegs B CTX_lv2_locate_manifest_names.   (* FMH_Fn.v:234 *)
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* ---- small kit ---- *)
(* a register the run left as a computed value v, U E v = z *)
Lemma cnoC2_reg_U : forall H E ss ms (r : bv 5) v z,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = v -> U E v = z -> getr (ms_regs ms) r = w64 z.
Proof.
intros H E ss ms r v z HS Hr Hz. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. unfold w64. rewrite <- Hz.
unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* fm's statics ride through any step that keeps their bytes *)
Lemma cnoC2_glob_img : forall (W W' : world tfibsegs) m m' live peak cnt fail,
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
Lemma cnoC2_garr8_keep : forall (W : world tfibsegs) m m' p l,
  (forall a, p <= a < p + Z.of_nat (length l) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  garr8 tfibsegs (rdW W m) p l -> garr8 tfibsegs (rdW W m') p l.
Proof.
intros W m m' p l HK Hg. apply (garr8_frame tfibsegs _ _ p l Hg). intros a Ha. apply (mbyte_of_aview tfibsegs).
exact (HK a Ha).
Qed.
(* a byte the memset left zero *)
Lemma cnoC2_val0 : forall (W : world tfibsegs) m a,
  aview tfibsegs (w_H W) m a = Some 0 -> val_mem tfibsegs (rdW W m) a 1 0.
Proof.
intros W m a Hv k Hk. assert (Ek : k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte tfibsegs (rdW W m) a) as [b|]; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as Hb. f_equal. apply bv_eq. rewrite Hb, Z_to_bv_unsigned. now vm_compute.
Qed.
(* two blocks of one AR state, one from each side of a split of the block list, are disjoint *)
Lemma cnoC2_sep_in : forall ly S (W : world tfibsegs) mem md bl0 nb x y,
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
Lemma cnoC2_new_notin : forall ly S (W : world tfibsegs) mem md bl0 nb x,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = bl0 ++ nb -> In x nb -> 0 < req_size (snd x) -> ~ In x bl0.
Proof.
intros ly S W mem md bl0 nb x HAR Hbl Hx Hpos Hx0.
destruct (cnoC2_sep_in ly S W mem md bl0 nb x x HAR Hbl Hx0 Hx); lia.
Qed.

Lemma cno_seg_Q3 : forall cx ly S W regs mem md u1 t1 u2,
  cno_base B cx -> cno_Q3 B cx ly S W regs mem md u1 t1 u2 ->
  (forall ly' S' W' regs' mem' md', cno_R3 B cx ly' S' W' regs' mem' md' u1 t1 u2 ->
     SRr tfibsegs W' (cfg_at tfibsegs CNO_R3 regs' mem' md') (cno_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs CNO_Q3 regs mem md) (cno_post B cx).
Proof.
intros [ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt] ly S W regs mem md u1 t1 u2 HBX HQ3 K.
pose proof HBX as (HPRE & Hra0 & G10 & G11 & G12 & G13 & Hsu & Hst & Hnzu & Hnzt & Hhu & Hht & Hlu & Htnm & HG0 & HQ
  & Hlive & Hev & Hbb).
destruct HPRE as [HAP HRO].
pose proof HAP as (HAR0 & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch & HQT).
destruct HQ3 as (((HJ & HFR & Hsp & Hgp & Htp & H24 & HROc & H26 & H27) & Hbl & Hbu & Hbt & HG & H18 & H21 & H25) &
  Hu1 & Ht1 & Hu2 & R23 & R19 & R8 & R9 & R20 & R22 & Cu1 & Ct1 & Cu2).
unfold nx_un, nx_tn, nx_sp0, cno_J, cno_cpy in *.
cbn [nx_ly nx_S nx_W nx_regs nx_mem nx_md nx_up nx_tp nx_ub nx_tb nx_live nx_peak nx_cnt length Z.of_nat] in *.
pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
assert (FS : STK_check_no_overread = 16736) by reflexivity.
set (un := Z.of_nat (length ub)) in *. set (tn := Z.of_nat (length tb)) in *.
assert (Hun0 : 0 <= un) by (unfold un; apply Zle_0_nat).
assert (Htn0 : 0 <= tn) by (unfold tn; apply Zle_0_nat).
pose proof HJ as (HAR & _).
(* the three copies made so far *)
assert (Hin_u1 : In (u1, un + 18) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hin_t1 : In (t1, tn + 18) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; right; left; reflexivity).
assert (Hin_u2 : In (u2, un + 18) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; right; right; left; reflexivity).
assert (Hrqu : req_size (un + 18) = un + 18) by (unfold req_size; destruct (Z.eqb_spec (un + 18) 0); lia).
assert (Hrqt : req_size (tn + 18) = tn + 18) by (unfold req_size; destruct (Z.eqb_spec (tn + 18) 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u1) as (_ & H4u1 & Hcu1 & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_t1) as (_ & H4t1 & Hct1 & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u2) as (_ & H4u2 & Hcu2 & _ & _ & _ & _).
rewrite Hrqu in Hcu1, Hcu2. rewrite Hrqt in Hct1.
(* u2's block is new, so it is disjoint from the entry's blocks and from the other copies *)
assert (Hnew_u2 : ~ In (u2, un + 18) (ablocks B ly0 S0)).
{ apply (cnoC2_new_notin ly S W mem md _ _ _ HAR Hbl); [repeat (first [left; reflexivity | right]) | cbn [snd]; lia]. }
assert (Dsrc : forall b m, In (b, m) (ablocks B ly0 S0) -> b + req_size m <= u2 \/ u2 + (un + 18) <= b).
{ intros b m Hb. rewrite <- Hrqu.
  destruct (cnoC2_sep_in ly S W mem md _ _ (b, m) (u2, un + 18) HAR Hbl Hb
    ltac:(repeat (first [left; reflexivity | right]))) as [Hd | Hd]; cbn [fst snd] in Hd; [left | right]; lia. }
assert (Du1 : u1 + (un + 18) <= u2 \/ u2 + (un + 18) <= u1).
{ rewrite <- Hrqu at 1. rewrite <- Hrqu at 2.
  destruct (sep_blocks_pos tfibsegs B LAWS ly S W mem md (u1, un + 18) (u2, un + 18)
    (ablocks B ly0 S0) [(t1, tn + 18)] [] HAR ltac:(rewrite Hbl; reflexivity)) as [Hd | Hd];
  unfold block_rng in *; cbn [fst snd] in Hd; [left | right]; lia. }
assert (Dt1 : t1 + (tn + 18) <= u2 \/ u2 + (un + 18) <= t1).
{ rewrite <- Hrqt at 1. rewrite <- Hrqu at 1.
  destruct (sep_blocks_pos tfibsegs B LAWS ly S W mem md (t1, tn + 18) (u2, un + 18)
    (ablocks B ly0 S0 ++ [(u1, un + 18)]) [] [] HAR ltac:(rewrite Hbl, <- app_assoc; reflexivity)) as [Hd | Hd];
  unfold block_rng in *; cbn [fst snd] in Hd; [left | right]; lia. }
(* ---- 0x80c70 .. 0x80c84: a0 := u2 + un, s4 := u2 + un + 17, a1 := 0, a2 := 17, jal memset ---- *)
pose proof (fmw_resume_nr W regs [] mem CNO_Q3) as HS.
set (E := Ereg regs []) in HS.
assert (E20 : ew E 20 = Z_to_bv 64 un) by (subst E; rewrite (ew_Ereg_nat regs [] 20 20%bv eq_refl); exact R20).
assert (E23 : ew E 23 = Z_to_bv 64 u2) by (subst E; rewrite (ew_Ereg_nat regs [] 23 23%bv eq_refl); exact R23).
assert (E25 : ew E 25 = Z_to_bv 64 (un + 18)) by (subst E; rewrite (ew_Ereg_nat regs [] 25 25%bv eq_refl); exact H25).
assert (U10 : U E (SAlu ALU_ADD (SOff 20 0) (SOff 23 0)) = u2 + un).
{ rewrite U_SAlu. rewrite (U_atom E 20 un E20) by lia. rewrite (U_atom E 23 u2 E23) by lia.
  cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia. }
assert (U20 : U E (SAlu ALU_ADD (SOff 23 (-1)) (SOff 25 0)) = u2 + un + 17).
{ rewrite U_SAlu. rewrite (U_atom_off E 23 u2 (-1) E23) by lia. rewrite (U_atom E 25 (un + 18) E25) by lia.
  cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia. }
unfold cfg_at. change (w64 CNO_Q3) with (Z_to_bv 64 CNO_Q3).
aj_run_to fmw_tbl_cno_ok HS HJ PC_memset.
{ apply awr_ok_nil. }
(* the run touched no memory *)
assert (SB : same_below mem (ms_mem ms) (2 ^ 64)) by exact (frame_nil_same E mem (ms_mem ms) HF).
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha; exact (aview_below (w_H W) mem (ms_mem ms) (2 ^ 64) a SB Ha)).
pose proof HJ as (HARr & _).
pose proof (fmw_reg_lit _ E _ ms 1%bv CNO_R3 HS ltac:(vm_compute; reflexivity) ltac:(unfold CNO_R3; lia)) as Rra.
pose proof (fmw_reg_lit _ E _ ms 11%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as Ra1.
pose proof (fmw_reg_lit _ E _ ms 12%bv 17 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as Ra2.
pose proof (cnoC2_reg_U _ _ _ ms 10%bv _ _ HS ltac:(vm_compute; reflexivity) U10) as Ra0.
pose proof (cnoC2_reg_U _ _ _ ms 20%bv _ _ HS ltac:(vm_compute; reflexivity) U20) as Rs4.
pose proof (fmw_reg_atom _ regs _ _ ms 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl) as P2.
pose proof (fmw_reg_atom _ regs _ _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as P3.
pose proof (fmw_reg_atom _ regs _ _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as P4.
pose proof (fmw_reg_atom _ regs _ _ ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as P8.
pose proof (fmw_reg_atom _ regs _ _ ms 9%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl) as P9.
pose proof (fmw_reg_atom _ regs _ _ ms 18%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl) as P18.
pose proof (fmw_reg_atom _ regs _ _ ms 19%bv 19%bv 19 HS ltac:(vm_compute; reflexivity) eq_refl) as P19.
pose proof (fmw_reg_atom _ regs _ _ ms 21%bv 21%bv 21 HS ltac:(vm_compute; reflexivity) eq_refl) as P21.
pose proof (fmw_reg_atom _ regs _ _ ms 22%bv 22%bv 22 HS ltac:(vm_compute; reflexivity) eq_refl) as P22.
pose proof (fmw_reg_atom _ regs _ _ ms 23%bv 23%bv 23 HS ltac:(vm_compute; reflexivity) eq_refl) as P23.
pose proof (fmw_reg_atom _ regs _ _ ms 24%bv 24%bv 24 HS ltac:(vm_compute; reflexivity) eq_refl) as P24.
pose proof (fmw_reg_atom _ regs _ _ ms 25%bv 25%bv 25 HS ltac:(vm_compute; reflexivity) eq_refl) as P25.
pose proof (fmw_reg_atom _ regs _ _ ms 26%bv 26%bv 26 HS ltac:(vm_compute; reflexivity) eq_refl) as P26.
pose proof (fmw_reg_atom _ regs _ _ ms 27%bv 27%bv 27 HS ltac:(vm_compute; reflexivity) eq_refl) as P27.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs0 + -96)
  by (unfold spZ at 1; rewrite P2; unfold CNO_FRAME in Hsp; exact Hsp).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc].
(* ---- memset (u2 + un, 0, 17) ---- *)
eapply SRr_bind.
{ apply (aj_intrin_atS tfibsegs B LAWS HSL OSet PC_memset AMEMSET W (ms_regs ms) (ms_mem ms)
    STK_check_no_overread (spZ regs0) FM_PSTAT_FP ly0 S0 W0 mem0 md0 [] ly S _ (Z.of_nat 3) (u2 + un) 0 17 (-96)
    (Z_to_bv 64 CNO_R3)).
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
  - rewrite P3, Hgp. exact Hgp0.
  - rewrite P4, Htp. exact Htp0.
  - exact Rra.
  - apply ret_ok_even. rewrite unsigned_lit_small by (unfold CNO_R3; lia). reflexivity.
  - intros a Ha. split.
    + right. right. left. exists u2, (un + 18).
      split; [exact Hin_u2|]. split; [exact Hnew_u2|]. rewrite Hrqu. lia.
    + unfold ESTACK. lia.
  - apply (amem_range_of_block tfibsegs B LAWS ly S W (ms_mem ms) _ u2 (un + 18) (u2 + un) 17 HARr Hin_u2);
      [lia | rewrite Hrqu; lia].
  - apply (range_addressable_of_block tfibsegs B LAWS ly S W (ms_mem ms) _ u2 (un + 18) (u2 + un) 17 HARr Hin_u2);
      [lia | rewrite Hrqu; lia].
  - intros _.
    apply (shadow_hull_vis_of_block tfibsegs B LAWS ly S W (ms_mem ms) _ u2 (un + 18) (u2 + un) 17 HARr Hin_u2);
      [lia | rewrite Hrqu; lia | lia].
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10r & Heff & Hfr2 & Hpres2 & Hmd).
(* ---- back at 0x80c88 (cno_R3) ---- *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (u2 + un <= a < u2 + un + 17) ->
  ~ (spZ regs0 + -96 - ESTACK <= a < spZ regs0 + -96) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha H1 H2. rewrite (Hfr2 a Ha H1 H2). exact (AVB a Ha). }
assert (KEEPL : forall a, 0 <= a < alloc_ceiling -> ~ (u2 + un <= a < u2 + un + 17) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha H1. apply KEEP; [lia | exact H1 | unfold ESTACK; lia]. }
(* the saved registers in the frame *)
assert (HFR2 : cno_frame (mkNX ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt) W mem2).
{ apply (cno_frame_kept _ W W mem mem2); [|exact HFR]. intros a Ha.
  unfold nx_sp0, CNO_FRAME in Ha. cbn [nx_regs] in Ha.
  apply KEEP; [lia | lia | unfold ESTACK; lia]. }
(* fm's statics, the source windows and the earlier copies all lie outside the memset's 17 bytes *)
assert (HG2 : fm_glob tfibsegs W mem2 live peak cnt SIZE_MAXZ).
{ apply (cnoC2_glob_img W W mem mem2); [|exact HG]. intros a Ha.
  pose proof (fmw_img_range a (pstat_img a Ha)) as Hir. unfold FMW_IMG_LO, FMW_IMG_END in Hir.
  apply KEEPL; [lia|]. intros Hc.
  apply (blk_img tfibsegs B LAWS ly S W (ms_mem ms) _ u2 (un + 18) a HARr Hin_u2 ltac:(rewrite Hrqu; lia)).
  exact (pstat_img a Ha). }
assert (SRCK : forall p l, cno_home B ly0 S0 p l -> bytes_at tfibsegs W mem p l -> bytes_at tfibsegs W mem2 p l).
{ intros p l [-> | (b & m & Hb & Hlo & Hhi)]; [intros _; apply garr8_nil|].
  intros Hbp. unfold bytes_at in *.
  assert (Hbin : In (b, m) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; left; exact Hb).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARr Hbin) as (_ & H4b & Hcb & _ & _ & _ & _).
  assert (Hrqb : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  destruct (Dsrc b m Hb) as [Hd | Hd].
  apply (cnoC2_garr8_keep W mem mem2 p l); [intros a Ha; apply KEEPL; lia | exact Hbp].
  apply (cnoC2_garr8_keep W mem mem2 p l); [intros a Ha; apply KEEPL; lia | exact Hbp]. }
assert (Hbu2 : bytes_at tfibsegs W mem2 up ub) by exact (SRCK up ub Hhu Hbu).
assert (Hbt2 : bytes_at tfibsegs W mem2 tp tb) by exact (SRCK tp tb Hht Hbt).
assert (Cu12 : garr8 tfibsegs (rdW W mem2) u1 (ub ++ [0])).
{ apply (cnoC2_garr8_keep W mem mem2 u1 (ub ++ [0])); [|exact Cu1].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KEEPL; lia. }
assert (Ct12 : garr8 tfibsegs (rdW W mem2) t1 (tb ++ [0])).
{ apply (cnoC2_garr8_keep W mem mem2 t1 (tb ++ [0])); [|exact Ct1].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KEEPL; lia. }
(* u2's copy gains its NUL: the memset's first byte *)
assert (Cu22 : garr8 tfibsegs (rdW W mem2) u2 (ub ++ [0])).
{ apply (garr8_app1 tfibsegs (rdW W mem) (rdW W mem2) u2 ub 0).
  - exact Cu2.
  - apply (cnoC2_val0 W mem2 (u2 + un)).
    pose proof (Heff 0 ltac:(lia)) as He. rewrite Z.add_0_r in He. change (0 mod 256) with 0 in He. exact He.
  - lia.
  - intros a Ha. apply (mbyte_of_aview tfibsegs). apply KEEPL; lia. }
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
assert (Q23 : getr regs2 23 = getr (ms_regs ms) 23) by exact (fmw_pres _ _ 23%bv HP2 ltac:(fmw_cs_side)).
assert (Q24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (fmw_pres _ _ 24%bv HP2 ltac:(fmw_cs_side)).
assert (Q25 : getr regs2 25 = getr (ms_regs ms) 25) by exact (fmw_pres _ _ 25%bv HP2 ltac:(fmw_cs_side)).
assert (Q26 : getr regs2 26 = getr (ms_regs ms) 26) by exact (fmw_pres _ _ 26%bv HP2 ltac:(fmw_cs_side)).
assert (Q27 : getr regs2 27 = getr (ms_regs ms) 27) by exact (fmw_pres _ _ 27%bv HP2 ltac:(fmw_cs_side)).
assert (Hsp2 : spZ regs2 = spZ regs0 - CNO_FRAME)
  by (unfold spZ in Hsp1 |- *; rewrite Q2; unfold CNO_FRAME; lia).
assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) mem2))
  by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 pstat_closed pstat_not_roP HRO).
change (mkCfg (mkst regs2 (Z_to_bv 64 CNO_R3) mem2 (seg_rom tfibsegs)) md2)
  with (cfg_at tfibsegs CNO_R3 regs2 mem2 md2).
apply (K ly S W regs2 mem2 md2).
unfold cno_R3, cno_cp, cno_core, cno_J, cno_cpy, nx_sp0, nx_un, nx_tn.
cbn [nx_ly nx_S nx_W nx_regs nx_mem nx_md nx_up nx_tp nx_ub nx_tb nx_live nx_peak nx_cnt length Z.of_nat].
split; [split; [split; [exact HJ2|]|]|].
- split; [exact HFR2|]. split; [exact Hsp2|].
  split; [rewrite Q3, P3; exact Hgp|]. split; [rewrite Q4, P4; exact Htp|].
  split; [rewrite Q24, P24; exact H24|]. split; [exact HRO2|].
  split; [rewrite Q26, P26; exact H26 | rewrite Q27, P27; exact H27].
- split; [exact Hbl|]. split; [exact Hbu2|]. split; [exact Hbt2|]. split; [exact HG2|].
  split; [rewrite Q18, P18; exact H18|]. split; [rewrite Q21, P21; exact H21 | rewrite Q25, P25; exact H25].
- split; [exact Hu1|]. split; [exact Ht1|]. split; [exact Hu2|].
  split; [rewrite Q23, P23; exact R23|]. split; [rewrite Q19, P19; exact R19|].
  split; [rewrite Q8, P8; exact R8|]. split; [rewrite Q9, P9; exact R9|].
  split; [rewrite Q20; exact Rs4|]. split; [rewrite Q22, P22; exact R22|].
  split; [exact Cu12|]. split; [exact Ct12 | exact Cu22].
Qed.

Lemma cno_seg_Q4 : forall cx ly S W regs mem md u1 t1 u2 t2,
  cno_base B cx -> cno_Q4 B cx ly S W regs mem md u1 t1 u2 t2 ->
  (forall ly' S' W' regs' mem' md', cno_R4 B cx ly' S' W' regs' mem' md' u1 t1 u2 t2 ->
     SRr tfibsegs W' (cfg_at tfibsegs CNO_R4 regs' mem' md') (cno_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs CNO_Q4 regs mem md) (cno_post B cx).
Proof.
intros [ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt] ly S W regs mem md u1 t1 u2 t2 HBX HQ4 K.
pose proof HBX as (HPRE & Hra0 & G10 & G11 & G12 & G13 & Hsu & Hst & Hnzu & Hnzt & Hhu & Hht & Hlu & Htnm & HG0 & HQ
  & Hlive & Hev & Hbb).
destruct HPRE as [HAP HRO].
pose proof HAP as (HAR0 & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch & HQT).
destruct HQ4 as (((HJ & HFR & Hsp & Hgp & Htp & H24 & HROc & H26 & H27) & Hbl & Hbu & Hbt & HG & H18 & H21 & H25) &
  Hu1 & Ht1 & Hu2 & Ht2 & R20 & R23 & R19 & R8 & R9 & R22 & Cu1 & Ct1 & Cu2 & Ct2).
unfold nx_un, nx_tn, nx_sp0, cno_J, cno_cpy in *.
cbn [nx_ly nx_S nx_W nx_regs nx_mem nx_md nx_up nx_tp nx_ub nx_tb nx_live nx_peak nx_cnt length Z.of_nat] in *.
pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
assert (FS : STK_check_no_overread = 16736) by reflexivity.
set (un := Z.of_nat (length ub)) in *. set (tn := Z.of_nat (length tb)) in *.
assert (Hun0 : 0 <= un) by (unfold un; apply Zle_0_nat).
assert (Htn0 : 0 <= tn) by (unfold tn; apply Zle_0_nat).
pose proof HJ as (HAR & _).
(* the four copies *)
assert (Hin_u1 : In (u1, un + 18) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hin_t1 : In (t1, tn + 18) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; right; left; reflexivity).
assert (Hin_u2 : In (u2, un + 18) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; right; right; left; reflexivity).
assert (Hin_t2 : In (t2, tn + 18) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; right; right; right; left; reflexivity).
assert (Hrqu : req_size (un + 18) = un + 18) by (unfold req_size; destruct (Z.eqb_spec (un + 18) 0); lia).
assert (Hrqt : req_size (tn + 18) = tn + 18) by (unfold req_size; destruct (Z.eqb_spec (tn + 18) 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u1) as (_ & H4u1 & Hcu1 & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_t1) as (_ & H4t1 & Hct1 & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u2) as (_ & H4u2 & Hcu2 & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_t2) as (_ & H4t2 & Hct2 & _ & _ & _ & _).
rewrite Hrqu in Hcu1, Hcu2. rewrite Hrqt in Hct1, Hct2.
assert (Hnew_t2 : ~ In (t2, tn + 18) (ablocks B ly0 S0)).
{ apply (cnoC2_new_notin ly S W mem md _ _ _ HAR Hbl); [repeat (first [left; reflexivity | right]) | cbn [snd]; lia]. }
assert (Dsrc : forall b m, In (b, m) (ablocks B ly0 S0) -> b + req_size m <= t2 \/ t2 + (tn + 18) <= b).
{ intros b m Hb. rewrite <- Hrqt.
  destruct (cnoC2_sep_in ly S W mem md _ _ (b, m) (t2, tn + 18) HAR Hbl Hb
    ltac:(repeat (first [left; reflexivity | right]))) as [Hd | Hd]; cbn [fst snd] in Hd; [left | right]; lia. }
assert (Du1 : u1 + (un + 18) <= t2 \/ t2 + (tn + 18) <= u1).
{ rewrite <- Hrqu at 1. rewrite <- Hrqt at 1.
  destruct (sep_blocks_pos tfibsegs B LAWS ly S W mem md (u1, un + 18) (t2, tn + 18)
    (ablocks B ly0 S0) [(t1, tn + 18); (u2, un + 18)] [] HAR ltac:(rewrite Hbl; reflexivity)) as [Hd | Hd];
  unfold block_rng in *; cbn [fst snd] in Hd; [left | right]; lia. }
assert (Dt1 : t1 + (tn + 18) <= t2 \/ t2 + (tn + 18) <= t1).
{ destruct (sep_blocks_pos tfibsegs B LAWS ly S W mem md (t1, tn + 18) (t2, tn + 18)
    (ablocks B ly0 S0 ++ [(u1, un + 18)]) [(u2, un + 18)] [] HAR
    ltac:(rewrite Hbl, <- app_assoc; reflexivity)) as [Hd | Hd];
  unfold block_rng in Hd; cbn [fst snd] in Hd; [left | right]; lia. }
assert (Du2 : u2 + (un + 18) <= t2 \/ t2 + (tn + 18) <= u2).
{ rewrite <- Hrqu at 1. rewrite <- Hrqt at 1.
  destruct (sep_blocks_pos tfibsegs B LAWS ly S W mem md (u2, un + 18) (t2, tn + 18)
    (ablocks B ly0 S0 ++ [(u1, un + 18); (t1, tn + 18)]) [] [] HAR
    ltac:(rewrite Hbl, <- app_assoc; reflexivity)) as [Hd | Hd];
  unfold block_rng in *; cbn [fst snd] in Hd; [left | right]; lia. }
(* ---- 0x80cc0 .. 0x80cd4: a0 := t2 + tn, s1 := t2 + tn + 17, a1 := 0, a2 := 17, jal memset ---- *)
pose proof (fmw_resume_nr W regs [] mem CNO_Q4) as HS.
set (E := Ereg regs []) in HS.
assert (E9 : ew E 9 = Z_to_bv 64 tn) by (subst E; rewrite (ew_Ereg_nat regs [] 9 9%bv eq_refl); exact R9).
assert (E20 : ew E 20 = Z_to_bv 64 t2) by (subst E; rewrite (ew_Ereg_nat regs [] 20 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = Z_to_bv 64 (tn + 18)) by (subst E; rewrite (ew_Ereg_nat regs [] 22 22%bv eq_refl); exact R22).
assert (U10 : U E (SAlu ALU_ADD (SOff 9 0) (SOff 20 0)) = t2 + tn).
{ rewrite U_SAlu. rewrite (U_atom E 9 tn E9) by lia. rewrite (U_atom E 20 t2 E20) by lia.
  cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia. }
assert (U9 : U E (SAlu ALU_ADD (SOff 20 (-1)) (SOff 22 0)) = t2 + tn + 17).
{ rewrite U_SAlu. rewrite (U_atom_off E 20 t2 (-1) E20) by lia. rewrite (U_atom E 22 (tn + 18) E22) by lia.
  cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia. }
unfold cfg_at. change (w64 CNO_Q4) with (Z_to_bv 64 CNO_Q4).
aj_run_to fmw_tbl_cno_ok HS HJ PC_memset.
{ apply awr_ok_nil. }
assert (SB : same_below mem (ms_mem ms) (2 ^ 64)) by exact (frame_nil_same E mem (ms_mem ms) HF).
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha; exact (aview_below (w_H W) mem (ms_mem ms) (2 ^ 64) a SB Ha)).
pose proof HJ as (HARr & _).
pose proof (fmw_reg_lit _ E _ ms 1%bv CNO_R4 HS ltac:(vm_compute; reflexivity) ltac:(unfold CNO_R4; lia)) as Rra.
pose proof (fmw_reg_lit _ E _ ms 11%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as Ra1.
pose proof (fmw_reg_lit _ E _ ms 12%bv 17 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as Ra2.
pose proof (cnoC2_reg_U _ _ _ ms 10%bv _ _ HS ltac:(vm_compute; reflexivity) U10) as Ra0.
pose proof (cnoC2_reg_U _ _ _ ms 9%bv _ _ HS ltac:(vm_compute; reflexivity) U9) as Rs1.
pose proof (fmw_reg_atom _ regs _ _ ms 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl) as P2.
pose proof (fmw_reg_atom _ regs _ _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as P3.
pose proof (fmw_reg_atom _ regs _ _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as P4.
pose proof (fmw_reg_atom _ regs _ _ ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as P8.
pose proof (fmw_reg_atom _ regs _ _ ms 18%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl) as P18.
pose proof (fmw_reg_atom _ regs _ _ ms 19%bv 19%bv 19 HS ltac:(vm_compute; reflexivity) eq_refl) as P19.
pose proof (fmw_reg_atom _ regs _ _ ms 20%bv 20%bv 20 HS ltac:(vm_compute; reflexivity) eq_refl) as P20.
pose proof (fmw_reg_atom _ regs _ _ ms 21%bv 21%bv 21 HS ltac:(vm_compute; reflexivity) eq_refl) as P21.
pose proof (fmw_reg_atom _ regs _ _ ms 22%bv 22%bv 22 HS ltac:(vm_compute; reflexivity) eq_refl) as P22.
pose proof (fmw_reg_atom _ regs _ _ ms 23%bv 23%bv 23 HS ltac:(vm_compute; reflexivity) eq_refl) as P23.
pose proof (fmw_reg_atom _ regs _ _ ms 24%bv 24%bv 24 HS ltac:(vm_compute; reflexivity) eq_refl) as P24.
pose proof (fmw_reg_atom _ regs _ _ ms 25%bv 25%bv 25 HS ltac:(vm_compute; reflexivity) eq_refl) as P25.
pose proof (fmw_reg_atom _ regs _ _ ms 26%bv 26%bv 26 HS ltac:(vm_compute; reflexivity) eq_refl) as P26.
pose proof (fmw_reg_atom _ regs _ _ ms 27%bv 27%bv 27 HS ltac:(vm_compute; reflexivity) eq_refl) as P27.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs0 + -96)
  by (unfold spZ at 1; rewrite P2; unfold CNO_FRAME in Hsp; exact Hsp).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc].
(* ---- memset (t2 + tn, 0, 17) ---- *)
eapply SRr_bind.
{ apply (aj_intrin_atS tfibsegs B LAWS HSL OSet PC_memset AMEMSET W (ms_regs ms) (ms_mem ms)
    STK_check_no_overread (spZ regs0) FM_PSTAT_FP ly0 S0 W0 mem0 md0 [] ly S _ (Z.of_nat 4) (t2 + tn) 0 17 (-96)
    (Z_to_bv 64 CNO_R4)).
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
  - rewrite P3, Hgp. exact Hgp0.
  - rewrite P4, Htp. exact Htp0.
  - exact Rra.
  - apply ret_ok_even. rewrite unsigned_lit_small by (unfold CNO_R4; lia). reflexivity.
  - intros a Ha. split.
    + right. right. left. exists t2, (tn + 18).
      split; [exact Hin_t2|]. split; [exact Hnew_t2|]. rewrite Hrqt. lia.
    + unfold ESTACK. lia.
  - apply (amem_range_of_block tfibsegs B LAWS ly S W (ms_mem ms) _ t2 (tn + 18) (t2 + tn) 17 HARr Hin_t2);
      [lia | rewrite Hrqt; lia].
  - apply (range_addressable_of_block tfibsegs B LAWS ly S W (ms_mem ms) _ t2 (tn + 18) (t2 + tn) 17 HARr Hin_t2);
      [lia | rewrite Hrqt; lia].
  - intros _.
    apply (shadow_hull_vis_of_block tfibsegs B LAWS ly S W (ms_mem ms) _ t2 (tn + 18) (t2 + tn) 17 HARr Hin_t2);
      [lia | rewrite Hrqt; lia | lia].
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10r & Heff & Hfr2 & Hpres2 & Hmd).
(* ---- back at 0x80cd8 (cno_R4) ---- *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (t2 + tn <= a < t2 + tn + 17) ->
  ~ (spZ regs0 + -96 - ESTACK <= a < spZ regs0 + -96) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha H1 H2. rewrite (Hfr2 a Ha H1 H2). exact (AVB a Ha). }
assert (KEEPL : forall a, 0 <= a < alloc_ceiling -> ~ (t2 + tn <= a < t2 + tn + 17) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha H1. apply KEEP; [lia | exact H1 | unfold ESTACK; lia]. }
assert (HFR2 : cno_frame (mkNX ly0 S0 W0 regs0 mem0 md0 up tp ub tb live peak cnt) W mem2).
{ apply (cno_frame_kept _ W W mem mem2); [|exact HFR]. intros a Ha.
  unfold nx_sp0, CNO_FRAME in Ha. cbn [nx_regs] in Ha.
  apply KEEP; [lia | lia | unfold ESTACK; lia]. }
assert (HG2 : fm_glob tfibsegs W mem2 live peak cnt SIZE_MAXZ).
{ apply (cnoC2_glob_img W W mem mem2); [|exact HG]. intros a Ha.
  pose proof (fmw_img_range a (pstat_img a Ha)) as Hir. unfold FMW_IMG_LO, FMW_IMG_END in Hir.
  apply KEEPL; [lia|]. intros Hc.
  apply (blk_img tfibsegs B LAWS ly S W (ms_mem ms) _ t2 (tn + 18) a HARr Hin_t2 ltac:(rewrite Hrqt; lia)).
  exact (pstat_img a Ha). }
assert (SRCK : forall p l, cno_home B ly0 S0 p l -> bytes_at tfibsegs W mem p l -> bytes_at tfibsegs W mem2 p l).
{ intros p l [-> | (b & m & Hb & Hlo & Hhi)]; [intros _; apply garr8_nil|].
  intros Hbp. unfold bytes_at in *.
  assert (Hbin : In (b, m) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; left; exact Hb).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARr Hbin) as (_ & H4b & Hcb & _ & _ & _ & _).
  assert (Hrqb : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  destruct (Dsrc b m Hb) as [Hd | Hd].
  apply (cnoC2_garr8_keep W mem mem2 p l); [intros a Ha; apply KEEPL; lia | exact Hbp].
  apply (cnoC2_garr8_keep W mem mem2 p l); [intros a Ha; apply KEEPL; lia | exact Hbp]. }
assert (Hbu2 : bytes_at tfibsegs W mem2 up ub) by exact (SRCK up ub Hhu Hbu).
assert (Hbt2 : bytes_at tfibsegs W mem2 tp tb) by exact (SRCK tp tb Hht Hbt).
assert (Cu12 : garr8 tfibsegs (rdW W mem2) u1 (ub ++ [0])).
{ apply (cnoC2_garr8_keep W mem mem2 u1 (ub ++ [0])); [|exact Cu1].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KEEPL; lia. }
assert (Ct12 : garr8 tfibsegs (rdW W mem2) t1 (tb ++ [0])).
{ apply (cnoC2_garr8_keep W mem mem2 t1 (tb ++ [0])); [|exact Ct1].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KEEPL; lia. }
assert (Cu22 : garr8 tfibsegs (rdW W mem2) u2 (ub ++ [0])).
{ apply (cnoC2_garr8_keep W mem mem2 u2 (ub ++ [0])); [|exact Cu2].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KEEPL; lia. }
assert (Ct22 : garr8 tfibsegs (rdW W mem2) t2 (tb ++ [0])).
{ apply (garr8_app1 tfibsegs (rdW W mem) (rdW W mem2) t2 tb 0).
  - exact Ct2.
  - apply (cnoC2_val0 W mem2 (t2 + tn)).
    pose proof (Heff 0 ltac:(lia)) as He. rewrite Z.add_0_r in He. change (0 mod 256) with 0 in He. exact He.
  - lia.
  - intros a Ha. apply (mbyte_of_aview tfibsegs). apply KEEPL; lia. }
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
assert (Q23 : getr regs2 23 = getr (ms_regs ms) 23) by exact (fmw_pres _ _ 23%bv HP2 ltac:(fmw_cs_side)).
assert (Q24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (fmw_pres _ _ 24%bv HP2 ltac:(fmw_cs_side)).
assert (Q25 : getr regs2 25 = getr (ms_regs ms) 25) by exact (fmw_pres _ _ 25%bv HP2 ltac:(fmw_cs_side)).
assert (Q26 : getr regs2 26 = getr (ms_regs ms) 26) by exact (fmw_pres _ _ 26%bv HP2 ltac:(fmw_cs_side)).
assert (Q27 : getr regs2 27 = getr (ms_regs ms) 27) by exact (fmw_pres _ _ 27%bv HP2 ltac:(fmw_cs_side)).
assert (Hsp2 : spZ regs2 = spZ regs0 - CNO_FRAME)
  by (unfold spZ in Hsp1 |- *; rewrite Q2; unfold CNO_FRAME; lia).
assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) mem2))
  by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 pstat_closed pstat_not_roP HRO).
change (mkCfg (mkst regs2 (Z_to_bv 64 CNO_R4) mem2 (seg_rom tfibsegs)) md2)
  with (cfg_at tfibsegs CNO_R4 regs2 mem2 md2).
apply (K ly S W regs2 mem2 md2).
unfold cno_R4, cno_cp, cno_core, cno_J, cno_cpy, nx_sp0, nx_un, nx_tn.
cbn [nx_ly nx_S nx_W nx_regs nx_mem nx_md nx_up nx_tp nx_ub nx_tb nx_live nx_peak nx_cnt length Z.of_nat].
split; [split; [split; [exact HJ2|]|]|].
- split; [exact HFR2|]. split; [exact Hsp2|].
  split; [rewrite Q3, P3; exact Hgp|]. split; [rewrite Q4, P4; exact Htp|].
  split; [rewrite Q24, P24; exact H24|]. split; [exact HRO2|].
  split; [rewrite Q26, P26; exact H26 | rewrite Q27, P27; exact H27].
- split; [exact Hbl|]. split; [exact Hbu2|]. split; [exact Hbt2|]. split; [exact HG2|].
  split; [rewrite Q18, P18; exact H18|]. split; [rewrite Q21, P21; exact H21 | rewrite Q25, P25; exact H25].
- split; [exact Hu1|]. split; [exact Ht1|]. split; [exact Hu2|]. split; [exact Ht2|].
  split; [rewrite Q20, P20; exact R20|]. split; [rewrite Q23, P23; exact R23|].
  split; [rewrite Q19, P19; exact R19|]. split; [rewrite Q8, P8; exact R8|].
  split; [rewrite Q9; exact Rs1|].
  split; [exact Cu12|]. split; [exact Ct12|]. split; [exact Cu22 | exact Ct22].
Qed.

End S.
