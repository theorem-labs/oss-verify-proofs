(* reac-pw/fuzz_link, image A: the stack-guard premises of the closed printf-family contracts (lib/A/Rt/LinkVfDefs.v
   afprintf_mf_realizes / avfprintf_mf_realizes at gc = LA_GOT_GUARD, gv = LA_GUARD), at a walk's state, for the walks of
   link's own functions that print on g_say (reac_code_emit, reac_served_mark).
   - `link_guard_got`: the .got word LA_GOT_GUARD 0xa2658 holds LA_GUARD 0x651c50 at every AR state: it is a row of
     AR's const table (lib/A/AF0m.v Tfib_const_abs; the word is runtime-owned, so arodata_okP does not reach it).
   - `link_guard_val`: the guard's 8 bytes at LA_GUARD read as some word (mbyte's image fallback, lib/A/AE36.v
     rdword_img_some).
   - `link_guard_apart`: both words miss a callee's two regions `vmf_out K sp f` (its window above alloc_ceiling, and a
     heap block f, which AR keeps off the image).
   - `blk_apart_img`: a heap block lies apart from any range of image bytes (a format, a .rodata literal).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP09 YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AF0x AE36.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkVfDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym LinkSyms LinkList LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem PcapRelro.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.

(* the .got word of the stack guard: a row of AR's const table (lib/A/AF0m.v Tfib_const_abs, `z8 (ANum 0xa2658)
   0x651c50`) *)
Lemma link_guard_got : forall ly S (W : world SEGS) (m : word -> option byte) md,
  AR SEGS B ly S W m md -> rdword (aview SEGS (w_H W) m) LA_GOT_GUARD = Some LA_GUARD.
Proof.
  rewrite HSEGS. intros ly S W m md (M & _).
  apply val_mem_rdword; [unfold LA_GUARD; lia|].
  apply (tfib_const_lookup B TB ly S (w_H W) m LA_GOT_GUARD 8 LA_GUARD M).
  vm_compute. reflexivity.
Qed.

(* the guard's word reads as some value *)
Lemma link_guard_val : forall (W : world SEGS) (m : word -> option byte),
  exists g, rdword (aview SEGS (w_H W) m) LA_GUARD = Some g.
Proof.
  rewrite HSEGS. intros W m.
  destruct (rdword_img_some (w_H W) m LA_GUARD ltac:(vm_compute; reflexivity)) as (v & Hv & _).
  exists v. exact Hv.
Qed.

(* image bytes, by the segment that holds them *)
Lemma link_img_range : forall lo n, (exists sg, find_segment tfibsegs lo n = Some sg) ->
  forall a, lo <= a < lo + n -> in_img SEGS a.
Proof.
  intros lo n (sg & Hf) a Ha. rewrite HSEGS.
  destruct (find_segment_hit _ _ _ _ Hf) as (Hin & H1 & H2). exists sg. split; [exact Hin | lia].
Qed.

(* a heap block of a state is apart from any range of image bytes *)
Lemma blk_apart_img : forall ly S (W : world SEGS) m md f n p q,
  AR SEGS B ly S W m md -> In (f, n) (ablocks B ly S) -> 0 <= n ->
  (forall a, p <= a < p + q -> in_img SEGS a) -> 0 < q ->
  apart p q f n.
Proof.
  intros ly S W m md f n p q HAR Hin Hn Himg Hq. unfold apart.
  destruct (Z_le_gt_dec (p + q) f) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (f + n) p) as [H'|H']; [right; exact H'|].
  exfalso.
  assert (Hreq : n <= req_size n /\ 0 < req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  assert (Ha : exists a, p <= a < p + q /\ f <= a < f + req_size n).
  { set (r := req_size n) in *. clearbody r. clear - H H' Hreq Hn Hq.
    destruct (Z_le_gt_dec p f) as [Hpf|Hpf]; [exists f | exists p]; split; lia. }
  destruct Ha as (a & Hap & Haf).
  assert (Hcl : (exists p0 n0, In (p0, n0) (ablocks B ly S) /\ p0 <= a < p0 + req_size n0) \/
    (exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) \/
    (exists cid pos, In (cid, pos) (frames S) /\ a = flag_addr ly cid pos)).
  { left. exists f, n. split; [exact Hin | exact Haf]. }
  destruct (al_client_img _ _ LAWS ly S W m md a HAR Hcl) as (_ & Hni).
  exact (Hni (Himg a Hap)).
Qed.

(* the two guard words miss a callee's window (above alloc_ceiling) and its heap block f *)
Lemma link_guard_apart : forall ly S (W : world SEGS) m md K sp f,
  AR SEGS B ly S W m md -> In (f, AMF_BLOCK) (ablocks B ly S) -> alloc_ceiling <= sp - K -> 0 <= K ->
  Forall (zdisjoint (LA_GOT_GUARD, 8)) (vmf_out K sp f) /\ Forall (zdisjoint (LA_GUARD, 8)) (vmf_out K sp f).
Proof.
  intros ly S W m md K sp f HAR Hin HK HK0.
  pose proof asan_consts as ((Hc1 & _) & _).
  assert (Ag : apart LA_GOT_GUARD 8 f AMF_BLOCK).
  { apply (blk_apart_img ly S W m md f AMF_BLOCK LA_GOT_GUARD 8 HAR Hin ltac:(unfold AMF_BLOCK; lia)); [|lia].
    apply link_img_range. vm_compute. eexists. reflexivity. }
  assert (Av : apart LA_GUARD 8 f AMF_BLOCK).
  { apply (blk_apart_img ly S W m md f AMF_BLOCK LA_GUARD 8 HAR Hin ltac:(unfold AMF_BLOCK; lia)); [|lia].
    apply link_img_range. vm_compute. eexists. reflexivity. }
  unfold vmf_out, apart, zdisjoint in *. cbn [fst snd].
  split; (constructor; [|constructor; [|constructor]]); cbn [fst snd];
    unfold LA_GOT_GUARD, LA_GUARD in *; lia.
Qed.

End a.

About link_guard_got. About link_guard_val. About link_img_range. About blk_apart_img. About link_guard_apart.
Print Assumptions link_guard_got. Print Assumptions link_guard_val. Print Assumptions link_guard_apart.
