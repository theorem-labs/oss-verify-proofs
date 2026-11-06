(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_cno_B1.v at a working branch 31d1eb57a40.
   check_no_overread 0x80bd4, the first and second copies: from P1 0x80c3c (after malloc (un + 18) -> u1) to Q1 0x80c58
   (memcpy (u1, up, un) done or skipped), and from P2 0x80cbc (after malloc (tn + 18) -> t1) to Q2 0x80cd8 (memcpy
   (t1, tp, tn) done or skipped). Each segment: `beqz a0, 0x80e98` is dead (the fresh block is at or above 4096), the
   block pointer moves to a callee-saved register (u1 -> s0, t1 -> s3), `beqz` on the length (s4 = un, s1 = tn) splits,
   and the copy arm calls __asan_memcpy (0x51ac8) into the prefix of the new block (sources s6 = up, s2 = tp). The two
   ranges hold no UBSan overflow check. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* every frame of a run whose state carries no region, chained as same_below *)
Ltac cnoB1_sb_nil :=
  repeat match goal with
  | H : frame_of ?E0 ?rs ?m1 ?m2 |- _ =>
      lazymatch m1 with mrestrict _ _ => fail | _ => idtac end;
      let Hn := fresh "SBn" in
      assert (Hn : same_below m1 m2 (2 ^ 64)) by (apply (frame_nil_same E0); exact H); clear H
  end;
  repeat match goal with
  | H1 : same_below ?a ?b (2 ^ 64), H2 : same_below ?b ?c (2 ^ 64) |- _ =>
      let H := fresh "SBn" in pose proof (same_below_trans a b c (2 ^ 64) H1 H2) as H; clear H1 H2
  end.

Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis FB : FmB B.                                   (* B/FMW_seg.v:37: code addresses, GOT/cell values, statics not owned *)
Hypothesis HB : TfibSyms B.                              (* ReusableB/YF0m.v:658 *)
Hypothesis IMG : fm_img_facts tfibsegs B.                (* B/FMH_Fn.v:61 *)
Hypothesis UNIV : fm_univ B.                             (* B/FMH_Fn.v:71: incl Tfib_universe (as_universe B) *)
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B ameter_triv.   (* YC5d.v:57; ameter_triv YCbp.v:17, mo_ok = True *)
Hypothesis AFREE4 : afree04_rule tfibsegs B ameter_triv.       (* YC5d.v:76 *)
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy PC_memcpy.  (* YG0d.v:318 *)
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet PC_memset.
Hypothesis NAMES : names_spec tfibsegs B CTX_lv2_locate_manifest_names.   (* B/FMH_Fn.v:241 *)
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).

(* ---- memory a write of n bytes at d leaves as it was: all but that window and the callee's stack window below slo ---- *)
Definition cnoB1_keep (W : world tfibsegs) (m m' : word -> option byte) (d n slo : Z) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (slo - ESTACK <= a < slo) ->
    aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.
Lemma cnoB1_keep_same : forall W m m' d n slo, same_below m m' (2 ^ 64) -> cnoB1_keep W m m' d n slo.
Proof. intros W m m' d n slo Hs a Ha _ _. exact (aview_below (w_H W) m m' (2 ^ 64) a Hs Ha). Qed.
Lemma cnoB1_garr8_keep : forall W m m' d n slo p l,
  cnoB1_keep W m m' d n slo -> alloc_ceiling <= slo - ESTACK -> 0 <= p -> p + Z.of_nat (length l) <= alloc_ceiling ->
  (p + Z.of_nat (length l) <= d \/ d + n <= p) ->
  garr8 tfibsegs (mrestrict (w_H W) m) p l -> garr8 tfibsegs (mrestrict (w_H W) m') p l.
Proof.
intros W m m' d n slo p l HK Hs Hp Hl Hd Hg. pose proof asan_consts as (C1 & _).
apply (garr8_frame tfibsegs _ _ p l Hg). intros a Ha. apply (mbyte_of_aview tfibsegs). apply HK; lia.
Qed.
(* the bytes a copy reads at x, written at d *)
Lemma cnoB1_garr8_copy : forall H m m' d x l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview tfibsegs H m' (d + i) = aview tfibsegs H m (x + i)) ->
  garr8 tfibsegs (mrestrict H m) x l -> garr8 tfibsegs (mrestrict H m') d l.
Proof.
intros H m m' d x l Hc Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. assert (k = 0)%nat by lia. subst k.
pose proof (Hc (Z.of_nat j) ltac:(lia)) as E. specialize (Hv 0%nat Hk).
replace (x + Z.of_nat j + Z.of_nat 0) with (x + Z.of_nat j) in Hv by lia.
replace (d + Z.of_nat j + Z.of_nat 0) with (d + Z.of_nat j) by lia.
unfold aview in E. rewrite Hv in E.
destruct (mbyte tfibsegs (mrestrict H m') (d + Z.of_nat j)) as [b'|] eqn:Eb; cbn in E; [|discriminate].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma cnoB1_garr8_vis : forall H m p l a, garr8 tfibsegs (mrestrict H m) p l -> p <= a < p + Z.of_nat (length l) ->
  aview tfibsegs H m a <> None.
Proof.
intros H m p l a Hg Ha. destruct (Hg (Z.to_nat (a - p)) ltac:(lia)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)). replace (p + Z.of_nat (Z.to_nat (a - p)) + Z.of_nat 0) with a in Hv by lia.
unfold aview. rewrite Hv. cbn. discriminate.
Qed.
(* a block of the entry list and a block of the walk's own are disjoint *)
Lemma cnoB1_sep_app : forall ly S W m md L0 L1 x y, AR tfibsegs B ly S W m md -> ablocks B ly S = L0 ++ L1 ->
  In x L0 -> In y L1 -> zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W m md L0 L1 x y HAR E Hx Hy.
apply in_split in Hx as (a1 & a2 & ->). apply in_split in Hy as (b1 & b2 & ->).
apply (sep_blocks_pos tfibsegs B LAWS ly S W m md x y a1 (a2 ++ b1) b2 HAR).
rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.
(* the stack below the frame is above alloc_ceiling; gp and tp at the entry *)
Lemma cnoB1_slo : forall cx, cno_base B cx ->
  alloc_ceiling + ESTACK + CNO_FRAME <= nx_sp0 cx /\ nx_sp0 cx <= 2 ^ 47 /\
  getr (nx_regs cx) 3 = w64 (as_gp B) /\ getr (nx_regs cx) 4 = w64 (as_tp B).
Proof.
intros cx (HPRE & _). destruct HPRE as [HAP _].
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (_ & Hc & H47 & _).
pose proof HAP as (_ & _ & _ & Hgp & Htp & _).
assert (FS : STK_check_no_overread = 16752) by reflexivity. assert (ES : ESTACK = 4096) by reflexivity.
unfold nx_sp0, CNO_FRAME. rewrite FS in Hc. rewrite ES. split; [lia|]. split; [lia|]. split; [exact Hgp | exact Htp].
Qed.
(* a copy at p in a block other than the written one survives the write *)
Lemma cnoB1_cpy_kept : forall cx ly S W m0 md0 mem mem' d nd n p mp l,
  cno_base B cx -> AR tfibsegs B ly S W m0 md0 -> In (p, mp) (ablocks B ly S) ->
  zdisjoint (block_rng (p, mp)) (block_rng (d, nd)) -> Z.of_nat (length l) <= req_size mp -> 0 <= n <= req_size nd ->
  cnoB1_keep W mem mem' d n (nx_sp0 cx - CNO_FRAME) ->
  cno_cpy W mem p l -> cno_cpy W mem' p l.
Proof.
intros cx ly S W m0 md0 mem mem' d nd n p mp l HBX HAR Hin D Hl Hn HK Hc.
pose proof (cnoB1_slo cx HBX) as (Hslo & _). pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p mp HAR Hin) as (_ & H4096 & Hceil & _).
unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
apply (cnoB1_garr8_keep W mem mem' d n _ p l HK); [lia | lia | lia | lia | exact Hc].
Qed.
(* the copy phase's facts after a write into the prefix of one of the walk's own blocks (d, nd). On B the phase
   carries no register beyond cno_core's sp / gp / tp / s8 (each resume point states its own). *)
Lemma cnoB1_cp_kept : forall cx ly S W regs mem md regs' mem' md' nb d nd n,
  cno_base B cx -> cno_cp B cx ly S W regs mem md nb ->
  cno_J B cx ly S W mem' md' (Z.of_nat (length nb)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 24 = getr regs 24 ->
  In (d, nd) nb -> 0 <= n <= req_size nd ->
  cnoB1_keep W mem mem' d n (nx_sp0 cx - CNO_FRAME) ->
  cno_cp B cx ly S W regs' mem' md' nb.
Proof.
intros cx ly S W regs mem md regs' mem' md' nb d nd n HBX HCP HJ' R2 R3 R4 R24 Hdin Hn HK.
pose proof (cnoB1_slo cx HBX) as (Hslo & H47 & _ & _).
pose proof HBX as ((_ & HRO) & _ & _ & _ & _ & _ & Hsu & Hst & _ & _ & Hhu & Hht & _).
destruct HCP as ((HJ & HFR & Hsp & H3 & H4 & H24 & HROc) & Hbl & Hbu & Hbt & HG).
pose proof (proj1 HJ') as HAR'.
pose proof asan_consts as (C1 & _).
assert (ES : ESTACK = 4096) by reflexivity. assert (CF : CNO_FRAME = 112) by reflexivity.
assert (Hdb : In (d, nd) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; exact Hdin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ d nd HAR' Hdb) as (_ & Hd4096 & Hdceil & _ & _ & _ & Hnd).
pose proof (blk_off_img B ly S W mem' md' d nd HAR' Hdb) as Hdoff. unfold YCe5.off_img in Hdoff.
assert (HW : alloc_ceiling <= nx_sp0 cx - CNO_FRAME - ESTACK) by lia.
assert (WIN : forall p l, src_rd tfibsegs (nx_W cx) (nx_mem cx) p l -> cno_home B (nx_ly cx) (nx_S cx) p l ->
   bytes_at tfibsegs W mem p l -> bytes_at tfibsegs W mem' p l).
{ intros p l (_ & Hp4096 & Hpc & _) Hh Hb. destruct Hh as [-> | (b & mb & Hbin & Hb1 & Hb2)]; [apply garr8_nil|].
  assert (Hbb : In (b, mb) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; left; exact Hbin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b mb HAR' Hbb) as (_ & _ & _ & _ & _ & _ & Hmb).
  pose proof (cnoB1_sep_app ly S W mem' md' _ _ (b, mb) (d, nd) HAR' Hbl Hbin Hdin) as D.
  pose proof (req_size_pos mb ltac:(lia)) as [_ Q].
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
  apply (cnoB1_garr8_keep W mem mem' d n _ p l HK HW); [lia | lia | lia | exact Hb]. }
split; [|split; [exact Hbl|split; [exact (WIN _ _ Hsu Hhu Hbu)|split; [exact (WIN _ _ Hst Hht Hbt)|]]]].
- split; [exact HJ'|]. split.
  + eapply cno_frame_kept; [|exact HFR]. intros a Ha. apply HK; lia.
  + split; [unfold spZ in *; rewrite R2; exact Hsp|]. split; [rewrite R3; exact H3|]. split; [rewrite R4; exact H4|].
    split; [rewrite R24; exact H24|].
    exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' pstat_closed pstat_not_roP HRO).
- destruct HG as (G1 & G2 & G3 & G4 & GR).
  assert (GK : forall g, 0x9e260 <= g -> g + 8 <= 0x5d4748 -> forall k, 0 <= k < Z.of_nat 8 ->
    aview tfibsegs (w_H W) mem' (g + k) = aview tfibsegs (w_H W) mem (g + k)).
  { intros g Hg1 Hg2 k Hk. cbn in Hk. apply HK; lia. }
  split; [|split; [|split; [|split]]]; try exact GR;
    (eapply (val_mem_kept tfibsegs); [apply GK; unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia | eassumption]).
Qed.

(* ---- P1 0x80c3c -> Q1 0x80c58 ---- *)
Lemma cno_seg_P1 : forall cx ly S W regs mem md u1,
  cno_base B cx -> cno_P1 B cx ly S W regs mem md u1 ->
  (forall ly' S' W' regs' mem' md', cno_Q1 B cx ly' S' W' regs' mem' md' u1 ->
     SRr tfibsegs W' (cfg_at tfibsegs CNO_Q1 regs' mem' md') (cno_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs CNO_P1 regs mem md) (cno_post B cx).
Proof.
intros cx ly S W regs mem md u1 HBX HP K.
pose proof (cnoB1_slo cx HBX) as (Hslo & H47 & Hgp & Htp).
pose proof HBX as (_ & _ & _ & _ & _ & _ & Hsu & _ & _ & _ & Hhu & _ & Hlu & _).
pose proof Hsu as (_ & Hup4096 & Hupc & Hupam & _).
pose proof HP as (HCP & Hu1 & H10 & H9 & H18 & H20 & H21 & H22).
pose proof HCP as ((HJ & _ & Hsp & H3 & H4 & _) & Hbl & Hbu & _ & _).
unfold cno_J in HJ.
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & _).
assert (FS : STK_check_no_overread = 16752) by reflexivity. assert (ES : ESTACK = 4096) by reflexivity.
assert (CF : CNO_FRAME = 112) by reflexivity.
assert (EUn : nx_un cx = Z.of_nat (length (nx_ub cx))) by reflexivity.
assert (Hun255 : 0 <= nx_un cx <= 255) by lia.
assert (Erq : req_size (nx_un cx + 18) = nx_un cx + 18) by (unfold req_size; destruct (Z.eqb_spec (nx_un cx + 18) 0); lia).
set (nb := [(u1, nx_un cx + 18)]) in *.
assert (Hu1nb : In (u1, nx_un cx + 18) nb) by (subst nb; cbn; tauto).
assert (Hu1b : In (u1, nx_un cx + 18) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; exact Hu1nb).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hu1b) as (_ & _ & Hu1c & _).
assert (Hu1n : ~ In (u1, nx_un cx + 18) (ablocks B (nx_ly cx) (nx_S cx))).
{ intros Hin. pose proof (cnoB1_sep_app ly S W _ _ _ _ _ _ HAR Hbl Hin Hu1nb) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia. }
pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof (fmw_resume_nr W regs [] mem CNO_P1) as HS.
set (E := Ereg regs []) in HS.
assert (E10 : ew E 10 = Z_to_bv 64 u1) by (subst E; rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10).
assert (E20 : ew E 20 = Z_to_bv 64 (nx_un cx)) by (subst E; rewrite (ew_Ereg_nat regs [] 20 20%bv eq_refl); exact H20).
unfold cfg_at. change (w64 CNO_P1) with (Z_to_bv 64 CNO_P1).
(* 0x80c3c: beqz a0, 0x80e98 (u1 >= 4096) *)
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HS | intros Hb _ | intros _ HS1].
{ exfalso. rewrite branch_eq_U, (U_atom E 10 u1 E10 ltac:(lia)), U_lit in Hb by lia. apply Z.eqb_eq in Hb. lia. }
clear HS.
aj_run fmw_tbl_cno_ok HS1 HJ.
{ apply awr_ok_nil. }
cnoB1_sb_nil.
lazymatch type of HS1 with context [restrict _ ?m] => rename m into msA end.
(* 0x80c44: beqz s4 (un), 0x80c58 *)
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 20 0) (b := SLit 0); [exact HS1 | intros Hb2 HS2 | intros Hb2 HS2];
  rewrite branch_eq_U, (U_atom E 20 _ E20 ltac:(lia)), U_lit in Hb2 by lia; clear HS1.
- (* un = 0: no copy, straight to 0x80c58 *)
  apply Z.eqb_eq in Hb2.
  aj_run_to fmw_tbl_cno_ok HS2 HJ CNO_Q1.
  { apply awr_ok_nil. }
  cnoB1_sb_nil.
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into msB end.
  match goal with Hx : same_below mem _ (2 ^ 64) |- _ => rename Hx into SB end.
  rewrite ?wvb_collapse in HJ.
  pose proof (fmw_reg_atom _ regs [] _ msB 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R2.
  pose proof (fmw_reg_atom _ regs [] _ msB 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R3.
  pose proof (fmw_reg_atom _ regs [] _ msB 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R4.
  pose proof (fmw_reg_atom _ regs [] _ msB 24%bv 24%bv 24 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R24.
  pose proof (fmw_reg_atom _ regs [] _ msB 8%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R8.
  pose proof (fmw_reg_atom _ regs [] _ msB 9%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R9.
  pose proof (fmw_reg_atom _ regs [] _ msB 18%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R18.
  pose proof (fmw_reg_atom _ regs [] _ msB 20%bv 20%bv 20 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R20.
  pose proof (fmw_reg_atom _ regs [] _ msB 21%bv 21%bv 21 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R21.
  pose proof (fmw_reg_atom _ regs [] _ msB 22%bv 22%bv 22 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R22.
  pose proof (cnoB1_keep_same W mem (ms_mem msB) u1 0 (nx_sp0 cx - CNO_FRAME) SB) as KP.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ msB HS2 eq_refl). cbn [ss_pc].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdX |} _ =>
    refine (K ly S W (ms_regs msB) (ms_mem msB) mdX _) end.
  split; [exact (cnoB1_cp_kept cx ly S W regs mem md _ _ _ nb u1 (nx_un cx + 18) 0 HBX HCP HJ
    R2 R3 R4 R24 Hu1nb ltac:(lia) KP)|].
  split; [exact Hu1|]. split; [rewrite R8; exact H10|]. split; [rewrite R9; exact H9|].
  split; [rewrite R18; exact H18|]. split; [rewrite R20; exact H20|]. split; [rewrite R21; exact H21|].
  split; [rewrite R22; exact H22|].
  assert (Eub : nx_ub cx = []) by (apply length_zero_iff_nil; lia).
  unfold cno_cpy. rewrite Eub. apply garr8_nil.
- (* un <> 0: memcpy (u1, up, un) *)
  apply Z.eqb_neq in Hb2.
  aj_run_to fmw_tbl_cno_ok HS2 HJ PC_memcpy.
  { apply awr_ok_nil. }
  cnoB1_sb_nil.
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into msB end.
  match goal with Hx : same_below mem _ (2 ^ 64) |- _ => rename Hx into SB end.
  rewrite ?wvb_collapse in HJ.
  pose proof (proj1 HJ) as HARc.
  pose proof (fmw_reg_lit _ E _ msB 1%bv 0x80c58 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
  pose proof (fmw_reg_atom _ regs [] _ msB 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R2.
  pose proof (fmw_reg_atom _ regs [] _ msB 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R3.
  pose proof (fmw_reg_atom _ regs [] _ msB 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R4.
  pose proof (fmw_reg_atom _ regs [] _ msB 10%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R10.
  pose proof (fmw_reg_atom _ regs [] _ msB 11%bv 22%bv 22 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R11.
  pose proof (fmw_reg_atom _ regs [] _ msB 12%bv 20%bv 20 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R12.
  (* the source window's home block (an entry block, still live) *)
  destruct Hhu as [Hnil | (b & mb & Hbin & Hb1 & Hb3)]; [exfalso; apply Hb2; rewrite EUn, Hnil; reflexivity|].
  assert (Hbb : In (b, mb) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; left; exact Hbin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b mb HAR Hbb) as (_ & _ & _ & _ & _ & _ & Hmb).
  pose proof (req_size_pos mb ltac:(lia)) as [_ Qmb].
  pose proof (cnoB1_sep_app ly S W _ _ _ _ (b, mb) (u1, nx_un cx + 18) HAR Hbl Hbin Hu1nb) as Dbu.
  unfold zdisjoint, block_rng in Dbu. cbn [fst snd] in Dbu.
  assert (Hbuc : garr8 tfibsegs (mrestrict (w_H W) (ms_mem msB)) (nx_up cx) (nx_ub cx)).
  { apply (garr8_frame tfibsegs _ _ _ _ Hbu). intros a Ha. apply (mbyte_below (w_H W) mem (ms_mem msB) (2 ^ 64) a SB). lia. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ msB HS2 eq_refl). cbn [ss_pc].
  eapply SRr_bind.
  { eapply (aj_intrin_atS tfibsegs B LAWS HSL OCpy PC_memcpy AMEMCPY W (ms_regs msB) (ms_mem msB) _ _ _ _ _ _ _ _ _ _ _ _ _
      u1 (nx_up cx) (nx_un cx) (-112) (Z_to_bv 64 0x80c58) HJ).
    - rewrite R10; exact H10.
    - rewrite R11; exact H22.
    - rewrite R12; exact H20.
    - lia.
    - lia.
    - lia.
    - unfold spZ in *. rewrite R2. lia.
    - reflexivity.
    - lia.
    - rewrite ES, FS. lia.
    - rewrite R3, H3. exact Hgp.
    - rewrite R4, H4. exact Htp.
    - exact R1.
    - apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
    - intros a Ha. split; [|lia]. right. right. left. exists u1, (nx_un cx + 18).
      split; [exact Hu1b|]. split; [exact Hu1n | lia].
    - eapply amem_range_of_block; [exact LAWS | exact HARc | exact Hu1b | lia | lia].
    - eapply range_addressable_of_block; [exact LAWS | exact HARc | exact Hu1b | lia | lia].
    - intros Hn0. eapply shadow_hull_vis_of_block; [exact LAWS | exact HARc | exact Hu1b | lia | lia | exact Hn0].
    - split; [lia|]. split; [lia|]. split.
      + intros a Ha. split; [exact (cnoB1_garr8_vis _ _ _ _ a Hbuc ltac:(lia)) | unfold spZ; rewrite R2; unfold spZ in Hsp; lia].
      + split; [lia|]. split; [exact Hupam|]. split; [eapply range_addressable_of_block; [exact LAWS | exact HARc | exact Hbb | lia | lia]|].
        intros Hn0. eapply shadow_hull_vis_of_block; [exact LAWS | exact HARc | exact Hbb | lia | lia | exact Hn0]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Heff & Hfr & _ & _).
  assert (KP : cnoB1_keep W mem mem2 u1 (nx_un cx) (nx_sp0 cx - CNO_FRAME)).
  { intros a Ha Hd Hs. rewrite (Hfr a Ha Hd ltac:(lia)). exact (aview_below (w_H W) mem (ms_mem msB) (2 ^ 64) a SB Ha). }
  pose proof (fmw_carry _ regs [] _ msB regs2 2%bv 2 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 2 2%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K2.
  pose proof (fmw_carry _ regs [] _ msB regs2 3%bv 3 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 3 3%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K3.
  pose proof (fmw_carry _ regs [] _ msB regs2 4%bv 4 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 4 4%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K4.
  pose proof (fmw_carry _ regs [] _ msB regs2 24%bv 24 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 24 24%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K24.
  pose proof (fmw_carry _ regs [] _ msB regs2 8%bv 10 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 10 10%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K8.
  pose proof (fmw_carry _ regs [] _ msB regs2 9%bv 9 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 9 9%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K9.
  pose proof (fmw_carry _ regs [] _ msB regs2 18%bv 18 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 18 18%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K18.
  pose proof (fmw_carry _ regs [] _ msB regs2 20%bv 20 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 20 20%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K20.
  pose proof (fmw_carry _ regs [] _ msB regs2 21%bv 21 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 21 21%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K21.
  pose proof (fmw_carry _ regs [] _ msB regs2 22%bv 22 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 22 22%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K22.
  refine (K ly S W regs2 mem2 md2 _).
  split; [exact (cnoB1_cp_kept cx ly S W regs mem md regs2 mem2 md2 nb u1 (nx_un cx + 18) (nx_un cx) HBX HCP HJ2
    K2 K3 K4 K24 Hu1nb ltac:(lia) KP)|].
  split; [exact Hu1|]. split; [rewrite K8; exact H10|]. split; [rewrite K9; exact H9|].
  split; [rewrite K18; exact H18|]. split; [rewrite K20; exact H20|]. split; [rewrite K21; exact H21|].
  split; [rewrite K22; exact H22|].
  unfold cno_cpy. apply (cnoB1_garr8_copy (w_H W) (ms_mem msB) mem2 u1 (nx_up cx) (nx_ub cx)); [|exact Hbuc].
  intros i Hi. exact (Heff i ltac:(lia)).
Qed.

(* ---- P2 0x80cbc -> Q2 0x80cd8 ---- *)
Lemma cno_seg_P2 : forall cx ly S W regs mem md u1 t1,
  cno_base B cx -> cno_P2 B cx ly S W regs mem md u1 t1 ->
  (forall ly' S' W' regs' mem' md', cno_Q2 B cx ly' S' W' regs' mem' md' u1 t1 ->
     SRr tfibsegs W' (cfg_at tfibsegs CNO_Q2 regs' mem' md') (cno_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs CNO_P2 regs mem md) (cno_post B cx).
Proof.
intros cx ly S W regs mem md u1 t1 HBX HP K.
pose proof (cnoB1_slo cx HBX) as (Hslo & H47 & Hgp & Htp).
pose proof HBX as (_ & _ & _ & _ & _ & _ & _ & Hst & _ & _ & _ & Hht & Hlu & Htnm & _).
pose proof Hst as (_ & Htp4096 & Htpc & Htpam & _).
pose proof HP as (HCP & Hu1 & Ht1 & H10 & H8 & H9 & H18 & H20 & H21 & H22 & H23 & H25 & Hc1).
pose proof HCP as ((HJ & _ & Hsp & H3 & H4 & _) & Hbl & _ & Hbt & _).
unfold cno_J in HJ.
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & _).
assert (FS : STK_check_no_overread = 16752) by reflexivity. assert (ES : ESTACK = 4096) by reflexivity.
assert (CF : CNO_FRAME = 112) by reflexivity. assert (MM : MANIFEST_MAX = 4194304) by reflexivity.
assert (EUn : nx_un cx = Z.of_nat (length (nx_ub cx))) by reflexivity.
assert (ETn : nx_tn cx = Z.of_nat (length (nx_tb cx))) by reflexivity.
assert (Hun255 : 0 <= nx_un cx <= 255) by lia.
assert (Htn0 : 0 <= nx_tn cx <= 4194304) by lia.
assert (Erq : req_size (nx_un cx + 18) = nx_un cx + 18) by (unfold req_size; destruct (Z.eqb_spec (nx_un cx + 18) 0); lia).
assert (Erqt : req_size (nx_tn cx + 18) = nx_tn cx + 18) by (unfold req_size; destruct (Z.eqb_spec (nx_tn cx + 18) 0); lia).
set (nb := [(u1, nx_un cx + 18); (t1, nx_tn cx + 18)]) in *.
assert (Ht1nb : In (t1, nx_tn cx + 18) nb) by (subst nb; cbn; tauto).
assert (Hu1b : In (u1, nx_un cx + 18) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; subst nb; cbn; tauto).
assert (Ht1b : In (t1, nx_tn cx + 18) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; exact Ht1nb).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Ht1b) as (_ & _ & Ht1c & _).
assert (Ht1n : ~ In (t1, nx_tn cx + 18) (ablocks B (nx_ly cx) (nx_S cx))).
{ intros Hin. pose proof (cnoB1_sep_app ly S W _ _ _ _ _ _ HAR Hbl Hin Ht1nb) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia. }
assert (D12 : zdisjoint (block_rng (u1, nx_un cx + 18)) (block_rng (t1, nx_tn cx + 18))).
{ apply (sep_blocks_pos tfibsegs B LAWS ly S W _ _ _ _ (ablocks B (nx_ly cx) (nx_S cx)) [] [] HAR).
  rewrite Hbl. reflexivity. }
pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof (fmw_resume_nr W regs [] mem CNO_P2) as HS.
set (E := Ereg regs []) in HS.
assert (E10 : ew E 10 = Z_to_bv 64 t1) by (subst E; rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10).
assert (E9 : ew E 9 = Z_to_bv 64 (nx_tn cx)) by (subst E; rewrite (ew_Ereg_nat regs [] 9 9%bv eq_refl); exact H9).
unfold cfg_at. change (w64 CNO_P2) with (Z_to_bv 64 CNO_P2).
(* 0x80cbc: beqz a0, 0x80e98 (t1 >= 4096) *)
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HS | intros Hb _ | intros _ HS1].
{ exfalso. rewrite branch_eq_U, (U_atom E 10 t1 E10 ltac:(lia)), U_lit in Hb by lia. apply Z.eqb_eq in Hb. lia. }
clear HS.
aj_run fmw_tbl_cno_ok HS1 HJ.
{ apply awr_ok_nil. }
cnoB1_sb_nil.
lazymatch type of HS1 with context [restrict _ ?m] => rename m into msA end.
(* 0x80cc4: beqz s1 (tn), 0x80cd8 *)
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 9 0) (b := SLit 0); [exact HS1 | intros Hb2 HS2 | intros Hb2 HS2];
  rewrite branch_eq_U, (U_atom E 9 _ E9 ltac:(lia)), U_lit in Hb2 by lia; clear HS1.
- (* tn = 0: no copy, straight to 0x80cd8 *)
  apply Z.eqb_eq in Hb2.
  aj_run_to fmw_tbl_cno_ok HS2 HJ CNO_Q2.
  { apply awr_ok_nil. }
  cnoB1_sb_nil.
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into msB end.
  match goal with Hx : same_below mem _ (2 ^ 64) |- _ => rename Hx into SB end.
  rewrite ?wvb_collapse in HJ.
  pose proof (fmw_reg_atom _ regs [] _ msB 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R2.
  pose proof (fmw_reg_atom _ regs [] _ msB 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R3.
  pose proof (fmw_reg_atom _ regs [] _ msB 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R4.
  pose proof (fmw_reg_atom _ regs [] _ msB 24%bv 24%bv 24 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R24.
  pose proof (fmw_reg_atom _ regs [] _ msB 19%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R19.
  pose proof (fmw_reg_atom _ regs [] _ msB 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R8.
  pose proof (fmw_reg_atom _ regs [] _ msB 9%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R9.
  pose proof (fmw_reg_atom _ regs [] _ msB 18%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R18.
  pose proof (fmw_reg_atom _ regs [] _ msB 20%bv 20%bv 20 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R20.
  pose proof (fmw_reg_atom _ regs [] _ msB 21%bv 21%bv 21 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R21.
  pose proof (fmw_reg_atom _ regs [] _ msB 22%bv 22%bv 22 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R22.
  pose proof (fmw_reg_atom _ regs [] _ msB 23%bv 23%bv 23 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R23.
  pose proof (fmw_reg_atom _ regs [] _ msB 25%bv 25%bv 25 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R25.
  pose proof (cnoB1_keep_same W mem (ms_mem msB) t1 0 (nx_sp0 cx - CNO_FRAME) SB) as KP.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ msB HS2 eq_refl). cbn [ss_pc].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdX |} _ =>
    refine (K ly S W (ms_regs msB) (ms_mem msB) mdX _) end.
  split; [exact (cnoB1_cp_kept cx ly S W regs mem md _ _ _ nb t1 (nx_tn cx + 18) 0 HBX HCP HJ
    R2 R3 R4 R24 Ht1nb ltac:(lia) KP)|].
  split; [exact Hu1|]. split; [exact Ht1|]. split; [rewrite R19; exact H10|]. split; [rewrite R8; exact H8|].
  split; [rewrite R9; exact H9|]. split; [rewrite R18; exact H18|]. split; [rewrite R20; exact H20|].
  split; [rewrite R21; exact H21|]. split; [rewrite R22; exact H22|]. split; [rewrite R23; exact H23|].
  split; [rewrite R25; exact H25|].
  split; [exact (cnoB1_cpy_kept cx ly S W _ _ mem (ms_mem msB) t1 (nx_tn cx + 18) 0 u1 (nx_un cx + 18) (nx_ub cx ++ [0]) HBX HAR Hu1b D12
    ltac:(rewrite length_app; cbn [length]; lia) ltac:(lia) KP Hc1)|].
  assert (Etb : nx_tb cx = []) by (apply length_zero_iff_nil; lia).
  unfold cno_cpy. rewrite Etb. apply garr8_nil.
- (* tn <> 0: memcpy (t1, tp, tn) *)
  apply Z.eqb_neq in Hb2.
  aj_run_to fmw_tbl_cno_ok HS2 HJ PC_memcpy.
  { apply awr_ok_nil. }
  cnoB1_sb_nil.
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into msB end.
  match goal with Hx : same_below mem _ (2 ^ 64) |- _ => rename Hx into SB end.
  rewrite ?wvb_collapse in HJ.
  pose proof (proj1 HJ) as HARc.
  pose proof (fmw_reg_lit _ E _ msB 1%bv 0x80cd8 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
  pose proof (fmw_reg_atom _ regs [] _ msB 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R2.
  pose proof (fmw_reg_atom _ regs [] _ msB 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R3.
  pose proof (fmw_reg_atom _ regs [] _ msB 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R4.
  pose proof (fmw_reg_atom _ regs [] _ msB 10%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R10.
  pose proof (fmw_reg_atom _ regs [] _ msB 11%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R11.
  pose proof (fmw_reg_atom _ regs [] _ msB 12%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R12.
  (* the source window's home block (an entry block, still live) *)
  destruct Hht as [Hnil | (b & mb & Hbin & Hb1 & Hb3)]; [exfalso; apply Hb2; rewrite ETn, Hnil; reflexivity|].
  assert (Hbb : In (b, mb) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; left; exact Hbin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b mb HAR Hbb) as (_ & _ & _ & _ & _ & _ & Hmb).
  pose proof (req_size_pos mb ltac:(lia)) as [_ Qmb].
  pose proof (cnoB1_sep_app ly S W _ _ _ _ (b, mb) (t1, nx_tn cx + 18) HAR Hbl Hbin Ht1nb) as Dbt.
  unfold zdisjoint, block_rng in Dbt. cbn [fst snd] in Dbt.
  assert (Hbtc : garr8 tfibsegs (mrestrict (w_H W) (ms_mem msB)) (nx_tp cx) (nx_tb cx)).
  { apply (garr8_frame tfibsegs _ _ _ _ Hbt). intros a Ha. apply (mbyte_below (w_H W) mem (ms_mem msB) (2 ^ 64) a SB). lia. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ msB HS2 eq_refl). cbn [ss_pc].
  eapply SRr_bind.
  { eapply (aj_intrin_atS tfibsegs B LAWS HSL OCpy PC_memcpy AMEMCPY W (ms_regs msB) (ms_mem msB) _ _ _ _ _ _ _ _ _ _ _ _ _
      t1 (nx_tp cx) (nx_tn cx) (-112) (Z_to_bv 64 0x80cd8) HJ).
    - rewrite R10; exact H10.
    - rewrite R11; exact H18.
    - rewrite R12; exact H9.
    - lia.
    - lia.
    - lia.
    - unfold spZ in *. rewrite R2. lia.
    - reflexivity.
    - lia.
    - rewrite ES, FS. lia.
    - rewrite R3, H3. exact Hgp.
    - rewrite R4, H4. exact Htp.
    - exact R1.
    - apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
    - intros a Ha. split; [|lia]. right. right. left. exists t1, (nx_tn cx + 18).
      split; [exact Ht1b|]. split; [exact Ht1n | lia].
    - eapply amem_range_of_block; [exact LAWS | exact HARc | exact Ht1b | lia | lia].
    - eapply range_addressable_of_block; [exact LAWS | exact HARc | exact Ht1b | lia | lia].
    - intros Hn0. eapply shadow_hull_vis_of_block; [exact LAWS | exact HARc | exact Ht1b | lia | lia | exact Hn0].
    - split; [lia|]. split; [lia|]. split.
      + intros a Ha. split; [exact (cnoB1_garr8_vis _ _ _ _ a Hbtc ltac:(lia)) | unfold spZ; rewrite R2; unfold spZ in Hsp; lia].
      + split; [lia|]. split; [exact Htpam|]. split; [eapply range_addressable_of_block; [exact LAWS | exact HARc | exact Hbb | lia | lia]|].
        intros Hn0. eapply shadow_hull_vis_of_block; [exact LAWS | exact HARc | exact Hbb | lia | lia | exact Hn0]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Heff & Hfr & _ & _).
  assert (KP : cnoB1_keep W mem mem2 t1 (nx_tn cx) (nx_sp0 cx - CNO_FRAME)).
  { intros a Ha Hd Hs. rewrite (Hfr a Ha Hd ltac:(lia)). exact (aview_below (w_H W) mem (ms_mem msB) (2 ^ 64) a SB Ha). }
  pose proof (fmw_carry _ regs [] _ msB regs2 2%bv 2 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 2 2%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K2.
  pose proof (fmw_carry _ regs [] _ msB regs2 3%bv 3 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 3 3%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K3.
  pose proof (fmw_carry _ regs [] _ msB regs2 4%bv 4 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 4 4%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K4.
  pose proof (fmw_carry _ regs [] _ msB regs2 24%bv 24 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 24 24%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K24.
  pose proof (fmw_carry _ regs [] _ msB regs2 19%bv 10 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 10 10%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K19.
  pose proof (fmw_carry _ regs [] _ msB regs2 8%bv 8 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 8 8%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K8.
  pose proof (fmw_carry _ regs [] _ msB regs2 9%bv 9 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 9 9%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K9.
  pose proof (fmw_carry _ regs [] _ msB regs2 18%bv 18 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 18 18%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K18.
  pose proof (fmw_carry _ regs [] _ msB regs2 20%bv 20 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 20 20%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K20.
  pose proof (fmw_carry _ regs [] _ msB regs2 21%bv 21 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 21 21%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K21.
  pose proof (fmw_carry _ regs [] _ msB regs2 22%bv 22 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 22 22%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K22.
  pose proof (fmw_carry _ regs [] _ msB regs2 23%bv 23 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 23 23%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K23.
  pose proof (fmw_carry _ regs [] _ msB regs2 25%bv 25 _ HS2 ltac:(vm_compute; reflexivity) (ew_Ereg_nat regs [] 25 25%bv eq_refl) HP2 ltac:(fmw_cs_side)) as K25.
  refine (K ly S W regs2 mem2 md2 _).
  split; [exact (cnoB1_cp_kept cx ly S W regs mem md regs2 mem2 md2 nb t1 (nx_tn cx + 18) (nx_tn cx) HBX HCP HJ2
    K2 K3 K4 K24 Ht1nb ltac:(lia) KP)|].
  split; [exact Hu1|]. split; [exact Ht1|]. split; [rewrite K19; exact H10|]. split; [rewrite K8; exact H8|].
  split; [rewrite K9; exact H9|]. split; [rewrite K18; exact H18|]. split; [rewrite K20; exact H20|].
  split; [rewrite K21; exact H21|]. split; [rewrite K22; exact H22|]. split; [rewrite K23; exact H23|].
  split; [rewrite K25; exact H25|].
  split; [exact (cnoB1_cpy_kept cx ly S W _ _ mem mem2 t1 (nx_tn cx + 18) (nx_tn cx) u1 (nx_un cx + 18) (nx_ub cx ++ [0]) HBX HAR Hu1b D12
    ltac:(rewrite length_app; cbn [length]; lia) ltac:(lia) KP Hc1)|].
  unfold cno_cpy. apply (cnoB1_garr8_copy (w_H W) (ms_mem msB) mem2 t1 (nx_tp cx) (nx_tb cx)); [|exact Hbtc].
  intros i Hi. exact (Heff i ltac:(lia)).
Qed.
End S.
