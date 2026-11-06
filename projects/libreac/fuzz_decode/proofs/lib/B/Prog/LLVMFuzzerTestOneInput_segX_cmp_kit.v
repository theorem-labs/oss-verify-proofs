(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_cmp_kit: the facts the image-B cmp segment (lib/B/Prog/LLVMFuzzerTestOneInput_segF.v,
   llvm_b_cmp_stmt, +0x6f0 .. +0x83c) uses to carry the interface's frame invariant (dec_b_core of
   lib/B/Prog/LLVMFuzzerTestOneInput_segs.v) and the cut point's memory clauses across a symbolic run or a call.
   Nothing here is new; each lemma is a copy, with the prefix cm_, of the lemma of the same body named beside it:
     lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_defs.v (the exit group's kit, 44e7264cb0a and its working copy):
       ex_perm_twice, ex_garr8_kept, ex_core_kept, ex_ch, ex_achain, ex_acall_keep, ex_base, ex_ro_rd_covered,
       ex_in_rom, ex_rom_rd;
     lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_kit.v (the up group's kit, working copy):
       up_cell_view, up_cell_agree, up_val_mem_kept, up_ro_agree, up_tab_ro, up_mode_kept, up_chain_pre, up_trace_in.
   Those files are other lanes' and are not imported, so that a change there cannot break this segment.
   What is this segment's own: cm_mem (the memory clauses of llvm_b_st_6f0) and cm_mem_kept, the up group's
   up_mem_kept at those clauses. The mode tables' pointer words are constant cells of B (dec_crt_cells); their
   +4 / +8 words are DEC_RO_RD bytes, which the read-only view shows as the image's at every state the slot's
   journal reaches (cm_rom_rd). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
Import ListNotations.
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := decodesegsB0.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* The memory clauses of llvm_b_st_6f0 the segment reads or hands on: the fake frame's spill slots and shadow,
   the mode, the payload copy, and the spill slots of the realigned area at s1. *)
Definition cm_mem (cx : dctx) (out res mode nch ns : Z) (W : world segs) (mem : word -> option byte) : Prop :=
  dec_b_frs cx (aview segs (w_H W) mem) /\
  dec_b_fsh cx (aview segs (w_H W) mem) 0 4 /\
  dec_b_mode_ok cx W mem mode nch ns /\
  garr8 segs (mrestrict (w_H W) mem) res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
  dec_b_slot cx (aview segs (w_H W) mem) 24 (dec_b_len (d_n cx)) /\
  dec_b_slot cx (aview segs (w_H W) mem) 32 SHADOW_OFF /\
  dec_b_slot cx (aview segs (w_H W) mem) 40 res /\
  dec_b_slot cx (aview segs (w_H W) mem) 56 (ns mod 2 ^ 32) /\
  dec_b_slot cx (aview segs (w_H W) mem) 64 (nch mod 2 ^ 32) /\
  dec_b_slot cx (aview segs (w_H W) mem) 72 (ns mod 2 ^ 64) /\
  dec_b_slot cx (aview segs (w_H W) mem) 80 (res + 50) /\
  dec_b_slot cx (aview segs (w_H W) mem) 88 out /\
  dec_b_slot cx (aview segs (w_H W) mem) 112 (d_F cx).

Hypothesis LAWS : AR_laws segs B.

(* lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_defs.v ex_perm_twice (cgif lib/A/ACf6.v:84-103 ablocks_perm_twice). *)
Lemma cm_perm_twice : forall ly S W mem md l1 l2 x,
  AR segs B ly S W mem md -> Permutation (ablocks B ly S) (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros ly S W mem md l1 l2 x HAR HP H1 H2.
apply in_split in H1 as (a1 & a2 & E1). apply in_split in H2 as (c1 & c2 & E2). subst l1 l2.
assert (HP2 : Permutation (ablocks B ly S) (x :: x :: ((a1 ++ a2) ++ c1) ++ c2)).
{ eapply Permutation_trans; [exact HP|].
  eapply Permutation_trans. { apply Permutation_app; [apply Permutation_sym; apply (Permutation_middle a1 a2 x) | apply Permutation_refl]. }
  change ((x :: a1 ++ a2) ++ c1 ++ x :: c2) with (x :: ((a1 ++ a2) ++ (c1 ++ x :: c2))).
  apply perm_skip.
  replace ((a1 ++ a2) ++ (c1 ++ x :: c2)) with (((a1 ++ a2) ++ c1) ++ x :: c2) by (first [rewrite app_assoc; reflexivity | rewrite <- app_assoc; reflexivity]).
  change (x :: ((a1 ++ a2) ++ c1) ++ c2) with (x :: (((a1 ++ a2) ++ c1) ++ c2)).
  apply Permutation_sym. apply (Permutation_middle ((a1 ++ a2) ++ c1) c2 x). }
assert (Hx : In x (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP2 | left; reflexivity]).
destruct x as [b m].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hx) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (sep_blocks_perm segs B LAWS ly S W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
pose proof (req_size_pos m ltac:(lia)). lia.
Qed.

(* ex_garr8_kept (cgif lib/A/ACey.v:91-96 garr8_kept_aview). *)
Lemma cm_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) base l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview segs H' m' (base + i) = aview segs H m (base + i)) ->
  garr8 segs (mrestrict H m) base l -> garr8 segs (mrestrict H' m') base l.
Proof.
intros H H' m m' base l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk8. rewrite <- (Hv k Hk8). apply (mbyte_of_aview segs).
replace (base + Z.of_nat j + Z.of_nat k) with (base + (Z.of_nat j + Z.of_nat k)) by lia. apply Hk. lia.
Qed.

(* ex_core_kept: the frame invariant across a step that kept the bytes it reads. *)
Lemma cm_core_kept : forall cx ly S W regs mem md k ly2 S2 W2 regs2 mem2 md2 k2,
  dec_b_core B cx ly S W regs mem md k ->
  @ajournal rc dec_B_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly2 S2 W2 mem2 md2 k2 ->
  frames S2 = [(DEC_FCLASS, d_fpos cx)] ->
  YK11.getr regs2 8 = YK11.getr regs 8 -> YK11.getr regs2 9 = YK11.getr regs 9 -> spZ regs2 = spZ regs ->
  YK11.getr regs2 3 = YK11.getr regs 3 -> YK11.getr regs2 4 = YK11.getr regs 4 ->
  (forall a, d_sp0 cx - 104 <= a < d_sp0 cx -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_F cx <= a < d_F cx + 64 -> apresent (w_H W2) mem2 a) ->
  (0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B ly2 S2)) ->
  (forall i, 0 <= i < Z.of_nat (length (d_pl cx)) ->
     aview segs (w_H W2) mem2 (d_p cx + i) = aview segs (w_H W) mem (d_p cx + i)) ->
  dec_b_core B cx ly2 S2 W2 regs2 mem2 md2 k2.
Proof.
intros cx ly S W regs mem md k ly2 S2 W2 regs2 mem2 md2 k2 Hcore HJ2 Hfr2 E8 E9 Esp E3 E4 Ksv KF PF Hpay2 Kpay.
destruct Hcore as (HJ & Hfrs & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & Hsaved & HF4096 & HFal & HFpres &
  HFLw & Hpay & Hgarr).
unfold dec_b_core.
split; [exact HJ2|]. split; [exact Hfr2|].
split; [rewrite E8; exact Hs0|]. split; [rewrite E9; exact Hs1|]. split; [rewrite Esp; exact Hsp|].
split; [exact Hsp1r|]. split; [exact Hsp1al|]. split; [rewrite E3; exact Hgp|]. split; [rewrite E4; exact Htp|].
split.
{ unfold dec_b_saved in *. rewrite Forall_forall in Hsaved |- *. intros o Hin. specialize (Hsaved o Hin).
  assert (Hb : 8 <= fst o <= 104).
  { unfold dec_b_saved_at in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst]; lia|]). destruct Hin. }
  rewrite <- Hsaved. apply rdword_ext. intros j Hj. apply Ksv. lia. }
split; [exact HF4096|]. split; [exact HFal|]. split; [exact PF|].
split; [rewrite <- HFLw; apply rdword_ext; intros j Hj; apply KF; lia|].
split; [exact Hpay2|].
apply (cm_garr8_kept (w_H W) (w_H W2) mem mem2); [|exact Hgarr].
rewrite length_map. exact Kpay.
Qed.

(* ex_ch / ex_achain (cgif lib/A/ACf5.v:128 rt_ch, :172-186 rt_chain). *)
Definition cm_ch (cx : dctx) : list (Z * Z * Z) :=
  if d_sp0 cx + 16 <? ly_top (d_ly cx) then [(d_sp0 cx, raZ (d_regs cx), s0Z (d_regs cx))] else [].

Lemma cm_achain : forall cx ly S W regs mem md k,
  @achain rc (d_ly cx) (aview segs (w_H (d_W cx)) (d_mem cx)) (d_sp0 cx) (s0Z (d_regs cx)) [] ->
  astk_ok DEC_LLVMF_STK (d_ly cx) (d_sp0 cx) -> 4096 <= raZ (d_regs cx) ->
  dec_b_core B cx ly S W regs mem md k ->
  @achain rc ly (aview segs (w_H W) mem) (d_sp1 cx) (d_sp0 cx) (cm_ch cx).
Proof.
intros cx ly S W regs mem md k Hch Hstk Hra Hcore.
destruct Hcore as (HJ & _ & _ & _ & _ & Hsp1r & Hsp1al & _ & _ & Hsaved & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hstk as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Htop & _).
pose proof asan_consts as (C1 & _).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
unfold dec_b_saved, dec_b_saved_at in Hsaved.
apply Forall_cons_iff in Hsaved as [Hra8 Hsaved]. apply Forall_cons_iff in Hsaved as [Hs16 _].
cbn [fst snd] in Hra8, Hs16.
apply (achain_ly_top (d_ly cx) ly); [exact Htop|].
unfold cm_ch. destruct (Z.ltb_spec (d_sp0 cx + 16) (ly_top (d_ly cx))) as [Hlt | Hge].
- apply (achain_push (d_ly cx) (aview segs (w_H (d_W cx)) (d_mem cx))); [exact Hch | lia | | | | exact Hra | lia | | lia | unfold d_sp0 in *; lia].
  + intros a Ha. apply F1; lia.
  + unfold raZ. exact Hra8.
  + unfold s0Z. exact Hs16.
  + rewrite Z.mod_divide in Hsp0al |- * by lia. destruct Hsp0al as [q Hq]. exists (2 * q). lia.
- left. split; [right; left; lia | reflexivity].
Qed.

(* ex_acall_keep: what a call that keeps the caller's bytes outside its stack window and outside Er leaves of the
   bytes this function reads afterwards. *)
Lemma cm_acall_keep : forall cx ly S W regs mem md k W2 mem2 slo shi (Er : Z -> Prop),
  dec_b_core B cx ly S W regs mem md k ->
  @acall_kept rc segs B ly S W mem W2 mem2 slo shi Er -> shi <= d_sp1 cx ->
  (forall a, d_F cx <= a < d_F cx + 64 -> ~ Er a) -> (forall a, d_SH cx <= a < d_SH cx + 8 -> ~ Er a) ->
  (forall a, d_sp1 cx <= a < d_sp0 cx -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) /\
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a /\ apresent (w_H W2) mem2 a) /\
  (forall a, d_SH cx <= a < d_SH cx + 8 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
Proof.
intros cx ly S W regs mem md k W2 mem2 slo shi Er Hcore HK Hshi HnF HnS.
destruct Hcore as (HJ & Hfrs & _ & _ & _ & Hsp1r & _ & _ & _ & _ & HF4096 & _ & HFpres & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi' & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
pose proof asan_consts as (C1 & _).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite HlyF; reflexivity).
assert (FB : fs_frame_bytes DEC_FCLASS = 64) by reflexivity.
split; [|split].
- intros a Ha. apply K1; [lia | lia].
- intros a Ha.
  assert (Hv : aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
  { apply (K4 DEC_FCLASS (d_fpos cx) a Hin0); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA, FB; lia | exact (HnF a Ha)]. }
  split; [exact Hv|].
  destruct (frames_bounds segs B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hin0) as (Hb1 & Hb2 & _).
  rewrite EFA in Hb1. rewrite EFA, FB in Hb2.
  apply (apresent_transfer segs (w_H W) (w_H W2) mem mem2 a); [lia | | exact Hv | exact (HFpres a Ha)].
  apply (frm_img segs B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) a HAR Hin0). rewrite EFA, FB. lia.
- intros a Ha. apply (K4 DEC_FCLASS (d_fpos cx) a Hin0); [right; unfold in_zr; cbn [fst snd]; rewrite EFA, FB; unfold d_SH in Ha; change (64 / 8) with 8; lia | exact (HnS a Ha)].
Qed.

(* up_cell_view / up_cell_agree / up_val_mem_kept / up_mode_kept: the mode clause from AR's constant cells (the
   pointer words) and the read-only view (the tables' words). *)
Lemma cm_cell_view : forall ly S W mem md a w v k,
  AR segs B ly S W mem md -> In (ACell (ANum a) w (AV (ANum v))) (as_const B ly) -> (k < w)%nat ->
  aview segs (w_H W) mem (a + Z.of_nat k) = Some (le_byte v w k).
Proof.
intros ly S W mem md a w v k HAR Hin Hk.
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ Hin) as Hc.
unfold cell_holds in Hc. cbn [c_at YG0f.c_val c_w aeval] in Hc. exact (Hc k Hk).
Qed.

Lemma cm_cell_agree : forall ly S W mem md ly2 S2 W2 mem2 md2 a w v,
  AR segs B ly S W mem md -> AR segs B ly2 S2 W2 mem2 md2 ->
  (forall l, In (ACell (ANum a) w (AV (ANum v))) (as_const B l)) ->
  forall j, 0 <= j < Z.of_nat w -> aview segs (w_H W2) mem2 (a + j) = aview segs (w_H W) mem (a + j).
Proof.
intros ly S W mem md ly2 S2 W2 mem2 md2 a w v HAR HAR2 Hin j Hj.
replace j with (Z.of_nat (Z.to_nat j)) by lia.
rewrite (cm_cell_view ly2 S2 W2 mem2 md2 a w v (Z.to_nat j) HAR2 (Hin ly2) ltac:(lia)).
rewrite (cm_cell_view ly S W mem md a w v (Z.to_nat j) HAR (Hin ly) ltac:(lia)).
reflexivity.
Qed.

Lemma cm_val_mem_kept : forall (H H' : word -> bool) (m m' : word -> option byte) a n v,
  (forall j, 0 <= j < Z.of_nat n -> aview segs H' m' (a + j) = aview segs H m (a + j)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv k Hkn. rewrite <- (Hv k Hkn). apply (mbyte_of_aview segs). apply Hk. lia.
Qed.

(* ex_ro_rd_covered / ex_in_rom / ex_rom_rd: the scoped read-only view at any state the slot's journal reaches, from
   the entry's rom_view, the journal's image clause (YCbq.v:362) and dec_ro_rd_scoped. *)
Definition cm_rom_covers (a n : Z) : bool :=
  existsb (fun s : Segment => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) &&
    (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool segs.
Lemma cm_ro_rd_covered : forallb (fun r => cm_rom_covers (fst r) (snd r)) DEC_RO_RD = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cm_in_rom : forall a, dec_in_ro_rd a -> in_rom segs a /\ in_img segs a.
Proof.
intros a Ha. unfold dec_in_ro_rd in Ha. apply Exists_exists in Ha as ([lo n] & Hin & Hz).
pose proof cm_ro_rd_covered as Hc. rewrite forallb_forall in Hc. specialize (Hc _ Hin).
unfold cm_rom_covers in Hc. cbn [fst snd] in Hc. apply existsb_exists in Hc as (sg & Hsg & Hb).
apply andb_true_iff in Hb as [Hb Hhi]. apply andb_true_iff in Hb as [Hw Hlo].
apply negb_true_iff in Hw. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
unfold in_zr in Hz. cbn [fst snd] in Hz.
split; exists sg; (split; [exact Hsg|]); [split; [exact Hw|] |]; lia.
Qed.
Lemma cm_rom_rd : forall cx STK own ly' S' W' mem' md' k,
  dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  rom_view segs (d_W cx) (d_mem cx) ->
  @ajournal rc dec_B_sink_head segs B STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    own ly' S' W' mem' md' k ->
  dec_rom_view_rd W' mem'.
Proof.
intros cx STK own ly' S' W' mem' md' k HO HE HR HJ a Ha.
destruct (dec_ro_rd_scoped B HO HE a Ha) as [Hno Hne]. destruct (cm_in_rom a Ha) as [Hr Hi].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a Hi Hno Hne); [exact (HR a Hr)|].
apply fp_spares_closed. intros Ho. exact (sink_closed_nil Ho).
Qed.

(* up_ro_agree: two states whose read-only view shows the image at the DEC_RO_RD bytes agree there. *)
Lemma cm_ro_agree : forall (W W2 : world segs) mem mem2,
  dec_rom_view_rd W mem -> dec_rom_view_rd W2 mem2 ->
  forall a, dec_in_ro_rd a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a.
Proof. intros W W2 mem mem2 HR HR2 a Ha. rewrite (HR2 a Ha), (HR a Ha). reflexivity. Qed.

(* up_tab_ro: the +4 / +8 words of the three mode tables are DEC_RO_RD bytes. *)
Lemma cm_tab_ro : forall t a, t = 0x20d60 \/ t = 0x20d80 \/ t = 0x20da0 -> t + 4 <= a < t + 12 -> dec_in_ro_rd a.
Proof.
intros t a Ht Ha. unfold dec_in_ro_rd. apply Exists_exists.
exists (t + 4, 8). split; [|unfold in_zr; cbn [fst snd]; lia].
unfold DEC_RO_RD. destruct Ht as [-> | [-> | ->]]; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

Lemma cm_mode_kept : forall cx ly S W mem md ly2 S2 W2 mem2 md2 mode nch ns,
  dec_crt_cells B ->
  AR segs B ly S W mem md -> AR segs B ly2 S2 W2 mem2 md2 ->
  dec_rom_view_rd W mem -> dec_rom_view_rd W2 mem2 ->
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  dec_b_mode_ok cx W mem mode nch ns -> dec_b_mode_ok cx W2 mem2 mode nch ns.
Proof.
intros cx ly S W mem md ly2 S2 W2 mem2 md2 mode nch ns HC HAR HAR2 HRO HRO2 KF (Hsrc & Hb1 & Hb2 & V4 & V8).
assert (CELL : forall a w v, (forall l, In (ACell (ANum a) w (AV (ANum v))) (as_const B l)) ->
  forall j, 0 <= j < Z.of_nat w -> aview segs (w_H W2) mem2 (a + j) = aview segs (w_H W) mem (a + j))
  by (intros a w v Hin; exact (cm_cell_agree ly S W mem md ly2 S2 W2 mem2 md2 a w v HAR HAR2 Hin)).
assert (R4 : forall l, In (z8 (ANum (decodeb_obj 4%nat)) 0x20d60) (as_const B l))
  by (intros l; pose proof (HC l) as Hl; decompose [and] Hl; assumption).
assert (R5 : forall l, In (z8 (ANum (decodeb_obj 5%nat)) 0x20da0) (as_const B l))
  by (intros l; pose proof (HC l) as Hl; decompose [and] Hl; assumption).
assert (R6 : forall l, In (z8 (ANum (decodeb_obj 6%nat)) 0x20d80) (as_const B l))
  by (intros l; pose proof (HC l) as Hl; decompose [and] Hl; assumption).
assert (TAB : forall q t, t = 0x20d60 \/ t = 0x20d80 \/ t = 0x20da0 -> (forall l, In (z8 (ANum q) t) (as_const B l)) ->
  rdword (aview segs (w_H W) mem) q = Some mode ->
  rdword (aview segs (w_H W2) mem2) q = Some mode /\
  val_mem segs (mrestrict (w_H W2) mem2) (mode + 4) 4%nat (nch mod 2 ^ 32) /\
  val_mem segs (mrestrict (w_H W2) mem2) (mode + 8) 4%nat (ns mod 2 ^ 32)).
{ intros q t Ht Rq Hq.
  assert (Htr : 0 <= t < 18446744073709551616) by (destruct Ht as [-> | [-> | ->]]; lia).
  assert (Hw : rdword (aview segs (w_H W) mem) q = Some t).
  { eapply rdword_cell; [change (2 ^ 64) with 18446744073709551616; exact Htr|].
    exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ (Rq ly)). }
  rewrite Hw in Hq. injection Hq as Hq. subst mode.
  split; [rewrite <- Hw; apply rdword_ext; intros j Hj; apply (CELL q 8%nat t Rq); lia|].
  split; apply (cm_val_mem_kept (w_H W) (w_H W2) mem mem2); [| exact V4 | | exact V8];
    intros j Hj; apply (cm_ro_agree W W2 mem mem2 HRO HRO2); apply (cm_tab_ro t); first [exact Ht | lia]. }
destruct Hsrc as [H4 | [H5 | [H6 | Hloc]]].
- destruct (TAB (decodeb_obj 4%nat) 0x20d60 (or_introl eq_refl) R4 H4) as (Q1 & Q2 & Q3).
  split; [left; exact Q1|]. split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Q2 | exact Q3].
- destruct (TAB (decodeb_obj 5%nat) 0x20da0 (or_intror (or_intror eq_refl)) R5 H5) as (Q1 & Q2 & Q3).
  split; [right; left; exact Q1|]. split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Q2 | exact Q3].
- destruct (TAB (decodeb_obj 6%nat) 0x20d80 (or_intror (or_introl eq_refl)) R6 H6) as (Q1 & Q2 & Q3).
  split; [right; right; left; exact Q1|]. split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Q2 | exact Q3].
- subst mode. split; [right; right; right; reflexivity|]. split; [exact Hb1|]. split; [exact Hb2|].
  split; apply (cm_val_mem_kept (w_H W) (w_H W2) mem mem2); [| exact V4 | | exact V8];
    intros j Hj; apply KF; lia.
Qed.

(* up_mem_kept at cm_mem: the clauses survive a step after which AR still holds, the read-only view shows the image
   at both states, and the spill area (but its one written slot 48(s1)), the fake frame, its shadow and the copy read
   the same. *)
Lemma cm_mem_kept : forall cx ly S W mem md ly2 S2 W2 mem2 md2 out res mode nch ns,
  dec_crt_cells B ->
  AR segs B ly S W mem md -> AR segs B ly2 S2 W2 mem2 md2 ->
  dec_rom_view_rd W mem -> dec_rom_view_rd W2 mem2 ->
  (forall a, d_sp1 cx <= a < d_sp1 cx + 120 -> ~ (d_sp1 cx + 48 <= a < d_sp1 cx + 56) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_SH cx <= a < d_SH cx + 8 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall i, 0 <= i < Z.of_nat (length (d_body cx)) ->
     aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) mem (res + i)) ->
  cm_mem cx out res mode nch ns W mem -> cm_mem cx out res mode nch ns W2 mem2.
Proof.
intros cx ly S W mem md ly2 S2 W2 mem2 md2 out res mode nch ns HC HAR HAR2 HRO HRO2 KS KF KH KR
  ((F0 & F8 & F16) & (H0 & H4 & H5 & H6) & Hmode & Hg & S24 & S32 & S40 & S56 & S64 & S72 & S80 & S88 & S112).
assert (SLOT : forall off v, (0 <= off <= 40 \/ 56 <= off <= 112) ->
  dec_b_slot cx (aview segs (w_H W) mem) off v -> dec_b_slot cx (aview segs (w_H W2) mem2) off v).
{ intros off v Hoff Hs. unfold dec_b_slot in *. rewrite <- Hs. apply rdword_ext. intros j Hj. apply KS; lia. }
split; [split; [apply SLOT; [lia | exact F0] | split; [apply SLOT; [lia | exact F8] | apply SLOT; [lia | exact F16]]]|].
split.
{ split; [intros i Hi; rewrite KH by lia; exact (H0 i Hi)|].
  split; [rewrite KH by lia; exact H4|]. split; [rewrite KH by lia; exact H5|].
  intros i Hi; rewrite KH by lia; exact (H6 i Hi). }
split; [exact (cm_mode_kept cx ly S W mem md ly2 S2 W2 mem2 md2 mode nch ns HC HAR HAR2 HRO HRO2 KF Hmode)|].
split; [apply (cm_garr8_kept (w_H W) (w_H W2) mem mem2); [rewrite length_map; exact KR | exact Hg]|].
split; [apply SLOT; [lia | exact S24]|]. split; [apply SLOT; [lia | exact S32]|].
split; [apply SLOT; [lia | exact S40]|]. split; [apply SLOT; [lia | exact S56]|].
split; [apply SLOT; [lia | exact S64]|]. split; [apply SLOT; [lia | exact S72]|].
split; [apply SLOT; [lia | exact S80]|]. split; [apply SLOT; [lia | exact S88] | apply SLOT; [lia | exact S112]].
Qed.

(* up_chain_pre: the frame-pointer chain at a call of this function (s0 = the entry sp, the call's sp = d_sp1). *)
Lemma cm_chain_pre : forall cx ly S W regs mem md k regsT,
  @achain rc (d_ly cx) (aview segs (w_H (d_W cx)) (d_mem cx)) (d_sp0 cx) (s0Z (d_regs cx)) [] ->
  astk_ok DEC_LLVMF_STK (d_ly cx) (d_sp0 cx) -> 4096 <= raZ (d_regs cx) ->
  dec_b_core B cx ly S W regs mem md k ->
  spZ regsT = d_sp1 cx -> s0Z regsT = d_sp0 cx -> 4096 <= raZ regsT ->
  chain_pre ly (aview segs (w_H W) mem) regsT (cm_ch cx).
Proof.
intros cx ly S W regs mem md k regsT Hch Hstk Hra4 Hcore Hsp Hs0 Hraz.
pose proof (cm_achain cx ly S W regs mem md k Hch Hstk Hra4 Hcore) as Hach.
pose proof Hcore as (HJ & _ & _ & _ & _ & Hsp1r & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
apply (achain_chain_pre ly _ (d_sp1 cx) (d_sp0 cx) (cm_ch cx) regsT Hach); [rewrite Hsp; lia | exact Hs0 | exact Hraz].
Qed.

(* up_trace_in: the trace an allocator call of this function records is one dec_llvmf_utraces lists. *)
Lemma cm_trace_in : forall RA cx (regsT : bvmap 5 word) pc0 (U : list (list Z)) r,
  raZ (d_regs cx) = RA -> raZ regsT = r ->
  (forall sp, In sp [[]; [RA]] -> In (dec_utrace pc0 (r :: sp)) U) ->
  In (call_trace0 pc0 regsT (cm_ch cx)) U.
Proof.
intros RA cx regsT pc0 U r HRA Hr HU.
rewrite call_trace_of_spine, Hr. unfold cm_ch.
destruct (d_sp0 cx + 16 <? ly_top (d_ly cx)); cbn [spine map fst snd].
- rewrite HRA. exact (HU [RA] ltac:(right; left; reflexivity)).
- exact (HU [] ltac:(left; reflexivity)).
Qed.
End d.

(* ex_base: the facts of the slot pre (dec_b_base) the segment reads. *)
Section e. Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegsB0.
Lemma cm_base : forall cx,
  @dec_b_base rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  YK0s.ret_ok (YK11.getr (d_regs cx) 1) /\ raZ (d_regs cx) = RA_LLVMF /\
  YK11.getr (d_regs cx) 3 = w64 (as_gp B) /\ YK11.getr (d_regs cx) 4 = w64 (as_tp B) /\
  astk_ok DEC_LLVMF_STK (d_ly cx) (d_sp0 cx) /\
  @achain rc (d_ly cx) (aview segs (w_H (d_W cx)) (d_mem cx)) (d_sp0 cx) (s0Z (d_regs cx)) [] /\
  ((d_n cx = 0 /\ d_p cx = A_EMPTY) \/ (0 < d_n cx < 2 ^ 26 /\ In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx)))) /\
  d_n cx = Z.of_nat (length (d_pl cx)) /\ frames (d_S cx) = [] /\
  st_nev (d_S cx) + DEC_EV_LIB <= EV_MAX /\ blocks_bytes (d_S cx) + DEC_LIVE_LIB <= LIVE_MAX /\
  4096 <= raZ (d_regs cx).
Proof.
intros cx HB. unfold dec_b_base, dec_lib_pre_x in HB.
destruct HB as ((_ & Hret & Hra4 & Hgp & Htp & Hstk & _ & Hch & _) & Hra & _ & _ & Hpn & Hnlen & _ & Hfr & Hnev & Hlive &
  _).
exact (conj Hret (conj Hra (conj Hgp (conj Htp (conj Hstk (conj Hch (conj Hpn (conj Hnlen (conj Hfr (conj Hnev
  (conj Hlive Hra4))))))))))).
Qed.
End e.
