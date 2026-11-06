(* reac_served_mark (fuzz_link.asan 0x895a8) on image A: the two buffers of its class-3 side frame F, kind[32] at
   F + 0x20 and alias[256] at F + 0x60, as a string wrapper reads them. Shared by the segments whose callee reads a
   buffer: reac_served_decide at +0x4a0 (kind and alias), wrapper_bcmp at +0x560 (alias), wrapper_fprintf at +0x5b4
   (alias as the second %s).

   `srm_bufs_rt`: at a cut whose base holds (lib/A/Prog/reac_served_markDefs.v `srm_base`) and whose buffers hold
   the read's strings (`srm_bufs`), each buffer's string meets `astr_rt_ok` at any callee window that lies above the
   allocator's ceiling: the string and its NUL are addressable (their shadow bytes SH + 4 .. SH + 7 and
   SH + 12 .. SH + 43 are 0, which the code stored at +0x1dc .. +0x268), the shadow hull is visible (F is a 64-aligned
   frame of the cut's allocator state: LinkWalkPi.v `shadow_hull_vis_of_frame`), the rest of the NUL's granule is in F
   and present, the 8-byte band is application memory (`in_app` of F), and F lies below the ceiling, so below every
   callee window. The frame facts are the Kit's `srm_F_facts` (lib/A/Prog/reac_served_markKit.v) and the string
   lengths are Xfer's `srm_R_lens` (lib/A/Prog/reac_served_markXfer.v); they are premises here so that this file
   needs only Defs.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalkSide PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_markDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* a present byte is seen *)
Lemma srm_aview_present : forall (H : word -> bool) (mem : word -> option byte) a,
  apresent H mem a -> aview SEGS H mem a <> None.
Proof. intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

(* ONE BUFFER: the bytes [F + off, F + off + cap) of F, whose shadow bytes SH + off / 8 .. are 0 *)
Lemma srm_buf_rt : forall cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 off cap s (regs' : bvmap 5 word) Kc,
  @srm_base fx rc SK PI B cx fpos X ly3 S3 W3 ms3 md3 ->
  srm_F cx fpos mod 64 = 0 -> srm_F cx fpos + SRM_FB <= alloc_ceiling -> in_app (srm_F cx fpos) SRM_FB ->
  In (SRM_CID, fpos) (frames S3) -> frame_addr ly3 SRM_CID fpos = srm_F cx fpos ->
  off mod 8 = 0 -> 0 <= off -> cap mod 8 = 0 -> off + cap + 8 <= SRM_FB ->
  (forall i, off / 8 <= i < (off + cap) / 8 ->
     aview SEGS (w_H W3) (ms_mem ms3) (srm_SH cx fpos + i) = Some 0) ->
  Z.of_nat (length s) < cap ->
  0 <= Kc -> alloc_ceiling <= spZ regs' - Kc ->
  astr_rt_ok SEGS regs' Kc (rdW W3 (ms_mem ms3)) (srm_F cx fpos + off) s.
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 off cap s regs' Kc HB Hal Hceil Happ Hin EF Hoff8 Hoff0 Hcap8 Hcap Hsh
    Hlen HK Hsp.
  unfold srm_base in HB. cbv zeta in HB.
  destruct HB as (_ & _ & _ & _ & _ & HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & HFp & _ & _ & _ & _ & _ & _).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof (proj1 HJi) as HAR. clear HJi memS.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  set (F := srm_F cx fpos) in *. set (n := Z.of_nat (length s)) in *.
  assert (Hn0 : 0 <= n) by (subst n; lia).
  assert (HF8 : F mod 8 = 0).
  { apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq]. apply Z.mod_divide; [lia|]. exists (8 * q). lia. }
  assert (HF4096 : 4096 <= F) by (unfold in_app in Happ; lia).
  unfold astr_rt_ok. fold n.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - lia.
  - unfold SRM_FB in Hcap. lia.
  - apply (amem_range_sub_app F SRM_FB); [exact Happ | exact Hceil | lia | unfold SRM_FB in *; lia | lia].
  - change (ard SEGS (rdW W3 (ms_mem ms3))) with (aview SEGS (w_H W3) (ms_mem ms3)).
    intros x Hx. exists 0. split; [|left; reflexivity].
    replace (shadow_of_addr SHADOW_OFF x) with (srm_SH cx fpos + (x - F) / 8).
    + apply Hsh. split.
      * apply Z.div_le_mono; lia.
      * assert (Hm : (off + cap) mod 8 = 0) by (rewrite Z.add_mod, Hoff8, Hcap8 by lia; reflexivity).
        lia.
    + replace x with (F + (x - F)) at 2 by lia. rewrite (shadow_of_addr_aligned_off SHADOW_OFF F (x - F) HF8).
      unfold srm_SH, shadow_addr, shadow_of_addr. fold F. lia.
  - change (ard SEGS (rdW W3 (ms_mem ms3))) with (aview SEGS (w_H W3) (ms_mem ms3)).
    apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 SRM_CID fpos _ _ HAR Hin);
      [rewrite EF; lia | rewrite EF, SRM_FB_val; unfold SRM_FB in *; lia | lia].
  - intros b Hb. change (ard SEGS (rdW W3 (ms_mem ms3))) with (aview SEGS (w_H W3) (ms_mem ms3)).
    apply srm_aview_present. apply HFp. fold F.
    assert (Hm : (F + off + cap) mod 8 = 0)
      by (rewrite Z.add_mod, (Z.add_mod F off), HF8, Hoff8, Hcap8 by lia; reflexivity).
    unfold SRM_FB in *. lia.
  - left. unfold SRM_FB in *. lia.
Qed.

(* THE TWO BUFFERS at a cut after the read *)
Lemma srm_bufs_rt : forall cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 R (regs' : bvmap 5 word) Kc,
  @srm_base fx rc SK PI B cx fpos X ly3 S3 W3 ms3 md3 ->
  srm_F cx fpos mod 64 = 0 -> srm_F cx fpos + SRM_FB <= alloc_ceiling -> in_app (srm_F cx fpos) SRM_FB ->
  In (SRM_CID, fpos) (frames S3) -> frame_addr ly3 SRM_CID fpos = srm_F cx fpos ->
  srm_bufs cx fpos W3 (ms_mem ms3) R ->
  Z.of_nat (length (r_kind R)) < KIND_CAP -> Z.of_nat (length (r_alias R)) < ALIAS_MAX ->
  0 <= Kc -> alloc_ceiling <= spZ regs' - Kc ->
  astr_rt_ok SEGS regs' Kc (rdW W3 (ms_mem ms3)) (srm_kind cx fpos) (r_kind R) /\
  astr_rt_ok SEGS regs' Kc (rdW W3 (ms_mem ms3)) (srm_alias cx fpos) (r_alias R).
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 R regs' Kc HB Hal Hceil Happ Hin EF Hbufs Hk Ha HK Hsp.
  destruct Hbufs as (_ & _ & _ & _ & Hsh).
  split.
  - unfold srm_kind, SRM_KIND.
    apply (srm_buf_rt cx fpos X ly3 S3 W3 ms3 md3 32 32 (r_kind R) regs' Kc HB Hal Hceil Happ Hin EF);
      [reflexivity | lia | reflexivity | unfold SRM_FB; lia | | unfold KIND_CAP in Hk; lia | exact HK | exact Hsp].
    intros i Hi. apply Hsh. unfold srm_bufsh_off. left. lia.
  - unfold srm_alias, SRM_ALIAS.
    apply (srm_buf_rt cx fpos X ly3 S3 W3 ms3 md3 96 256 (r_alias R) regs' Kc HB Hal Hceil Happ Hin EF);
      [reflexivity | lia | reflexivity | unfold SRM_FB; lia | | unfold ALIAS_MAX in Ha; lia | exact HK | exact Hsp].
    intros i Hi. apply Hsh. unfold srm_bufsh_off. right. lia.
Qed.

End b.
End a.
About srm_buf_rt. About srm_bufs_rt.
Print Assumptions srm_bufs_rt.
