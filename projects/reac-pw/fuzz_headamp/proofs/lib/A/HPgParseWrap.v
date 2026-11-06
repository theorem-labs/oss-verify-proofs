(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/Prog/reac_headamp_prop_parse.v at 499fa61524e
   (reac_headamp_prop_parse_of_result: the wrapper's two steps, then the result contract at R = 0), restated for the
   contracts of lib/A/HPgCSpec.v (hd_parse_result_specX, hd_parse_specX) and this engine: the two steps by SRr_step
   on the image's words, the journal carried over the materialized model (YCbq.v ajournal_materialize), the lemma
   generic in the segments and the entry address, with its instance at image A. *)
(* reac_headamp_prop_parse(props, out, max) (reac_headamp_prop.c:102-106) of reac-pw/fuzz_headamp's ASan images is
   two words: at a, `li a3,0` (`addi a3,zero,0`, 0x00000693); at a + 4, `j a + 8` (`jal zero,+4`, 0x0040006f), into
   reac_headamp_prop_parse_result at a + 8. No frame, ra kept: the parse returns to this function's caller.
   hp_parse_of_result: from the call at a the two steps reach a + 8 with a3 = 0 and every other register, the memory
   and the journal as at a (the model at most materialized); there hd_parse_result_specX at R = 0 applies. Its
   premises are hd_parse_specX's (hd_parse_args reads the registers only through sp), and its post is
   hd_parse_specX's: a3 is not callee-saved, ra and sp are as at a, and same_io passes the materialization.
   Image A (fuzz_headamp.asan, pinned sha256 f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47):
   a = 0x845ac, reac_headamp_prop_parse_result at 0x845b4 (hp_parse_of_result_A, the words read from Img0.rsegs).
   Proves function reac_headamp_prop_parse (image A 0x845ac) from the contract of reac_headamp_prop_parse_result
   (image A 0x845b4). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* a closed register number other than a3 (13) *)
Ltac hpw_ne := let E := fresh "E" in intro E; vm_compute in E; discriminate E.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---------------------------------- the two words ---------------------------------- *)
Lemma hpw_ecall0 : is_ecall (Z_to_bv 32 0x00000693) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma hpw_dec0 : decode_any (Z_to_bv 32 0x00000693) = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma hpw_ecall1 : is_ecall (Z_to_bv 32 0x0040006f) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma hpw_dec1 : decode_any (Z_to_bv 32 0x0040006f) = Some (Jal 0 4, 4%Z).
Proof. vm_refl_bv. Qed.

(* ---------------------------------- words and registers ---------------------------------- *)
Lemma hpw_v_addi_w : forall z k, v_addi (w64 z) k = w64 (z + k).
Proof.
intros z k. unfold w64, v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. apply bv_wrap_add_idemp_l.
Qed.
Lemma hpw_btgt : forall z, btgt (w64 (z + 4)) (bv_signed (4 : bv 21)) = w64 (z + 8).
Proof.
intros z. unfold btgt. rewrite hpw_v_addi_w.
assert (E : bv_signed (4 : bv 21) = 4) by (vm_compute; reflexivity).
rewrite E. replace (z + 4 + 4) with (z + 8) by ring. reflexivity.
Qed.
(* x0 reads 0: the addi's value *)
Lemma hpw_x0 : forall regs, v_addi (getr regs 0) (bv_signed (0 : bv 12)) = w64 0.
Proof. intros regs. vm_refl_bv. Qed.
Lemma hpw_getr_same : forall regs v, getr (regupd regs 13 v) 13 = v.
Proof.
intros regs v. unfold getr.
match goal with |- (if ?c then _ else _) = _ => replace c with false by (vm_compute; reflexivity) end.
cbv iota. apply regupd_same.
Qed.
Lemma hpw_getr_other : forall regs v r, bv_unsigned r <> 13 -> getr (regupd regs 13 v) r = getr regs r.
Proof.
intros regs v r Hr. unfold getr.
match goal with |- (if ?c then _ else _) = _ => destruct c end; [reflexivity|].
apply regupd_other. intros E. subst r. apply Hr. vm_compute. reflexivity.
Qed.
(* a3 is not callee-saved *)
Lemma hpw_cs_ne : forall r, acallee_saved r -> bv_unsigned (Z_to_bv 5 r) <> 13.
Proof.
intros r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat match type of Hc with _ \/ _ => destruct Hc as [Hc | Hc]; [subst r; hpw_ne |] end.
subst r. hpw_ne.
Qed.

(* ---------------------------------- the wrapper, any image ---------------------------------- *)
Theorem hp_parse_of_result : forall (segs : list Segment) (a : Z),
wx_segs_nowrap segs ->
(forall x, in_img segs x -> 0 <= x < kLowMemEnd) ->
fetch_word segs (w64 a) = Some (Z_to_bv 32 0x00000693) ->
fetch_word segs (w64 (a + 4)) = Some (Z_to_bv 32 0x0040006f) ->
forall RLO RHI akey aph apad asens gotw guard dcs,
hd_parse_result_specX segs B MT (a + 8) RLO RHI akey aph apad asens gotw guard dcs ->
hd_parse_specX segs B MT a RLO RHI akey aph apad asens gotw guard dcs.
Proof.
intros segs a Hwx Hlow Hf0 Hf1 RLO RHI akey aph apad asens gotw guard dcs HR
  STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs null P O cap ev bs HP Hn H10 H11 H12 HA.
unfold cfg_at.
(* a: `li a3,0` *)
eapply (YA0n.SRr_step segs Hwx W _
  (mkst (regupd regs 13 (w64 0)) (w64 (a + 4)) (mrestrict (w_H W) memc) (seg_rom segs))).
{ reflexivity. }
{ rewrite YA0o.restrict_mkst_fx. etransitivity.
  - exact (YK14.step_addi_at segs regs (w64 a) (mrestrict (w_H W) memc) (seg_rom segs) (Z_to_bv 32 0x00000693)
      13 0 0 (w64 0) Hf0 hpw_ecall0 hpw_dec0 ltac:(vm_compute; reflexivity) (hpw_x0 regs)).
  - rewrite hpw_v_addi_w. reflexivity. }
intros md1 Hs1. cbn [ms_mem mkst]. rewrite YA0o.unrestrict_mkst_mrestrict.
(* a + 4: `j a + 8` *)
eapply (YA0n.SRr_step segs Hwx W _
  (mkst (regupd regs 13 (w64 0)) (w64 (a + 8)) (mrestrict (w_H W) memc) (seg_rom segs))).
{ reflexivity. }
{ rewrite YA0o.restrict_mkst_fx. etransitivity.
  - exact (YK11.step_jal_x0 segs (regupd regs 13 (w64 0)) (w64 (a + 4)) (mrestrict (w_H W) memc) (seg_rom segs)
      (Z_to_bv 32 0x0040006f) 4 Hf1 hpw_ecall1 hpw_dec1).
  - rewrite hpw_btgt. reflexivity. }
intros md2 Hs2. cbn [ms_mem mkst]. rewrite YA0o.unrestrict_mkst_mrestrict.
pose proof (YK04.same_but_materialized_trans _ _ _ Hs1 Hs2) as Hs.
assert (Esp : spZ (regupd regs 13 (w64 0)) = spZ regs)
  by (unfold spZ; rewrite hpw_getr_other by hpw_ne; reflexivity).
assert (Era : raZ (regupd regs 13 (w64 0)) = raZ regs)
  by (unfold raZ; rewrite hpw_getr_other by hpw_ne; reflexivity).
(* a + 8: the result contract at R = 0 *)
eapply YA0n.SRr_mono.
{ apply (HR STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md2 k (regupd regs 13 (w64 0)) null P O 0 cap ev bs).
  - destruct HP as (HJ & Hret & Hra & Hgp & Htp & Hal & Hlo & Hhi & Hnev).
    unfold hd_pre. rewrite Era, Esp. rewrite !hpw_getr_other by hpw_ne.
    split; [|exact (conj Hret (conj Hra (conj Hgp (conj Htp (conj Hal (conj Hlo (conj Hhi Hnev)))))))].
    rewrite (YA0o.same_but_materialized_wvb mdc md2 Hs).
    eapply YCbq.ajournal_materialize; first [exact HJ | exact (YG0q.AR_laws_ok segs B) | exact Hlow].
  - exact Hn.
  - rewrite hpw_getr_other by hpw_ne. exact H10.
  - rewrite hpw_getr_other by hpw_ne. exact H11.
  - rewrite hpw_getr_other by hpw_ne. exact H12.
  - apply hpw_getr_same.
  - unfold hd_parse_args, hd_off_stack in HA |- *. rewrite Esp. exact HA. }
(* the post at a + 8 is the post at a *)
intros W2 c2 _ Hq.
unfold hd_parse_post, hd_post in Hq |- *. cbv beta in Hq |- *.
destruct Hq as (fx2 & ly2 & S2 & regs2 & mem2 & md3 & Hc & HFX & HJ2 & Hpres & Hra & Hfr & Hperm & Hio & Hmo &
  Hmem & HRq).
rewrite hpw_getr_other in Hc by hpw_ne. rewrite Esp in Hmem.
exists fx2, ly2, S2, regs2, mem2, md3.
split; [exact Hc|]. split; [exact HFX|]. split; [exact HJ2|].
split; [intros r Hr; rewrite (Hpres r Hr); apply hpw_getr_other; apply hpw_cs_ne; exact Hr|].
split; [rewrite Hra; apply hpw_getr_other; hpw_ne|].
split; [exact Hfr|]. split; [exact Hperm|].
split; [exact (YCbq.same_io_trans _ _ _ (YCbq.same_io_materialized _ _ Hs) Hio)|].
split; [exact Hmo|].
split; [exact Hmem | exact HRq].
Qed.

(* ---------------------------------- image A ---------------------------------- *)
(* the wrapper's two words, read from Img0.rsegs *)
Definition hpw_tbl : ctable := Eval vm_compute in (build_table rsegs PA_WRAP 2 TEmpty).
Lemma hpw_tbl_eq : hpw_tbl = build_table rsegs PA_WRAP 2 TEmpty.
Proof. vm_cast_no_check (eq_refl hpw_tbl). Qed.
Lemma hpw_tbl_ok : table_ok rsegs hpw_tbl.
Proof. rewrite hpw_tbl_eq. apply build_table_ok0. unfold PA_WRAP. lia. Qed.
Lemma hpw_fetch0_A : fetch_word rsegs (w64 0x845ac) = Some (Z_to_bv 32 0x00000693).
Proof. unfold w64. apply hpw_tbl_ok. vm_compute. reflexivity. Qed.
Lemma hpw_fetch1_A : fetch_word rsegs (w64 (0x845ac + 4)) = Some (Z_to_bv 32 0x0040006f).
Proof. unfold w64. apply hpw_tbl_ok. vm_compute. reflexivity. Qed.

Theorem hp_parse_of_result_A : forall RLO RHI akey aph apad asens gotw guard dcs,
hd_parse_result_specX rsegs B MT 0x845b4 RLO RHI akey aph apad asens gotw guard dcs ->
hd_parse_specX rsegs B MT 0x845ac RLO RHI akey aph apad asens gotw guard dcs.
Proof.
intros RLO RHI akey aph apad asens gotw guard dcs HR.
exact (hp_parse_of_result rsegs 0x845ac pa_wx pa_segs_low hpw_fetch0_A hpw_fetch1_A
  RLO RHI akey aph apad asens gotw guard dcs HR).
Qed.

End b.

Print Assumptions hp_parse_of_result.
Print Assumptions hp_parse_of_result_A.
