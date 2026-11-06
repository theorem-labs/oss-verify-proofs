(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v, with its module paths and module names changed; 1310 of its 1364 lines of code are new or changed and 437 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacMasterOnlyCadenceNs.v, with its module paths and module names changed; 222 of its 290 lines of code are new or changed and 1296 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacRateSnap.v; 114 of its 178 lines of code are new or changed and 226 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0s YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require FP.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma fp_rg_other : forall (m : bvmap 5 word) (k k' : bv 5) (v : word),
  bv_unsigned k <> bv_unsigned k' -> Sem.reg_get (bvmap_set k v m) k' = Sem.reg_get m k'.
Proof.
intros m k k' v H. unfold Sem.reg_get. rewrite bvmap_get_set_other; [reflexivity|].
intros X. apply H. rewrite X. reflexivity.
Qed.
Lemma fp_rg_same : forall (m : bvmap 5 word) (k : bv 5) (v : word), Sem.reg_get (bvmap_set k v m) k = v.
Proof. intros m k v. unfold Sem.reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.
Lemma fp_getr_upd : forall (regs : bvmap 5 word) (v : word) (r r' : bv 5),
  bv_unsigned r' <> bv_unsigned r -> getr (regupd regs r v) r' = getr regs r'.
Proof.
intros regs v r r' Hr. unfold getr, regupd. destruct (bv_eqb r' 0); [reflexivity|].
apply fp_rg_other. intros X. apply Hr. rewrite X. reflexivity.
Qed.
Lemma fp_spZ_upd : forall (regs : bvmap 5 word) (v : word) (r : bv 5),
  bv_unsigned r <> 2 -> spZ (regupd regs r v) = spZ regs.
Proof. intros regs v r Hr. unfold spZ. rewrite fp_getr_upd; [reflexivity | intros X; apply Hr; rewrite <- X; reflexivity]. Qed.
Lemma fp_step_fcvt_d_wu : forall (fx : FPState) segs regs pc mem rom w (rd rs : bv 5) (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt FC_D FC_WU rd rs rm, 4%Z) -> bv_unsigned rm = 0 ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 (bv_unsigned (getr regs rs))))) (@fp_regs fx))
      (Z_to_bv 32 (Z.lor (bv_unsigned (@fp_csr fx))
         (fflags_bits (snd (fp_of_int fmt_double RNE false 32 (bv_unsigned (getr regs rs))))))))
    regs (v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w rd rs rm Hf He Hd Hrm.
destruct fx as [fr cs]. cbn [fp_regs fp_csr] in *.
fp_pipeline Hf He Hd.
replace (rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned cs) 5) 7)) with (Some RNE)
  by (unfold rmode_of_field, rmode_of_Z; rewrite Hrm; reflexivity).
cbv beta iota. change (fp_format FMT_D) with fmt_double.
replace (if is_x0 rs then Z_to_bv 64 0 else Sem.reg_get regs rs) with (getr regs rs) by reflexivity.
destruct (fp_of_int fmt_double RNE false 32 (bv_unsigned (getr regs rs))) as [v fl].
cbn [fst snd]. rewrite b_npc4. reflexivity.
Qed.
Lemma fp_step_fmv_d : forall (fx : FPState) segs regs pc mem rom w (rd rs : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fsgnj F_SGNJ FMT_D rd rs rs, 4%Z) ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (Sem.reg_get (@fp_regs fx) rs) (@fp_regs fx)) (@fp_csr fx)) regs (v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w rd rs Hf He Hd.
destruct fx as [fr cs]. cbn [fp_regs fp_csr] in *.
fp_pipeline Hf He Hd. rewrite FP.sgnj_self, b_npc4. reflexivity.
Qed.
Lemma fp_step_flt_d : forall (F : bvmap 5 word) (fc : bv 32) segs regs pc mem rom w (rd rs1 rs2 : bv 5) (x y : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcmp F_LT FMT_D rd rs1 rs2, 4%Z) ->
  Sem.reg_get F rs1 = x -> Sem.reg_get F rs2 = y ->
  RiscvSemantics.step segs (@mkst (mkFP F fc) regs pc mem rom) =
  MachineOk (@mkst (mkFP F (Z_to_bv 32 (Z.lor (bv_unsigned fc)
      (fflags_bits (FP.fcmp_fl F_LT fmt_double (bv_unsigned x) (bv_unsigned y))))))
    (if bv_eqb rd 0 then regs else regupd regs rd (if FP.flt_d x y then Z_to_bv 64 1 else Z_to_bv 64 0))
    (v_addi pc 4) mem rom).
Proof.
intros F fc segs regs pc mem rom w rd rs1 rs2 x y Hf He Hd Hx Hy.
assert (E1 : FP.fcmp_fl F_LT fmt_double (bv_unsigned x) (bv_unsigned y) = snd (fp_lt fmt_double (bv_unsigned x) (bv_unsigned y))) by reflexivity.
assert (E2 : FP.flt_d x y = fst (fp_lt fmt_double (bv_unsigned x) (bv_unsigned y))) by reflexivity.
rewrite E1, E2.
fp_pipeline Hf He Hd.
cbv beta iota. change (fp_format FMT_D) with fmt_double. rewrite Hx, Hy.
destruct (fp_lt fmt_double (bv_unsigned x) (bv_unsigned y)) as [v fl]. cbn [fst snd].
rewrite b_npc4. unfold regupd. destruct (is_x0 rd); reflexivity.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Lemma fp_st_ok_fx : forall (fa fb : FPState) E ss regs pc mem rom,
  st_ok (fx := fa) segs E ss (@mkst fa regs pc mem rom) ->
  st_ok (fx := fb) segs E ss (@mkst fb regs pc mem rom).
Proof.
intros fa fb E ss regs pc mem rom (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
cbn [mkst ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem] in *.
unfold st_ok. cbn [mkst ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem].
split; [reflexivity|]. split; [exact H2|]. split; [reflexivity|]. split; [exact H4|].
split; [reflexivity|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9].
Qed.
Lemma fp_switch : forall (fa fb : FPState) E ss ms (H : word -> bool) sr' R' pcv,
  st_ok (fx := fa) segs E ss (restrict H ms) -> regs_ok E sr' R' ->
  st_ok (fx := fb) segs E (mkSST (bv_unsigned pcv) sr' (ss_fregs ss) (ss_mem ss) None (ss_facts ss))
    (restrict H (@mkst fb R' pcv (ms_mem ms) (seg_rom segs))).
Proof.
intros fa fb E ss ms H sr' R' pcv HS HR.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & Hm & Hf).
cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst] in Hm, Hf |- *.
unfold st_ok. cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
  ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
split; [reflexivity|]. split; [rewrite Z_to_bv_bv_unsigned; reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact HR|]. split; [exact Hm | exact Hf].
Qed.
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Lemma fp_keep_step : forall (W : world segs) (f f' : FPState) R R' pc pc' mem md Q
    STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k,
  RiscvSemantics.step segs (@mkst f R pc (mrestrict (w_H W) mem) (seg_rom segs)) =
    MachineOk (@mkst f' R' pc' (mrestrict (w_H W) mem) (seg_rom segs)) ->
  ajournal segs B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W mem md k ->
  (forall md', ajournal segs B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W mem md' k ->
     SRr segs W (mkCfg (@mkst f' R' pc' mem (seg_rom segs)) md') Q) ->
  SRr segs W (mkCfg (@mkst f R pc mem (seg_rom segs)) md) Q.
Proof.
intros W f f' R R' pc pc' mem md Q STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k Hst HJ Hk.
eapply (SRr_step segs Hwx W); [reflexivity | rewrite restrict_mkst_fx; exact Hst |].
intros md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
apply Hk. apply (ajournal_materialize segs B LAWS Hsegs). exact HJ.
Qed.
Lemma fp_write_step :
  forall (fb : FPState) (W : world segs) E ss' ms md Q
    (STK sp0 : Z) FPl ly S W0 mem0 md0 own lyc Sc k (Wr : Z -> Prop) mem' pcv,
  ms_svc_pending ms = None ->
  ajournal segs B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
  RiscvSemantics.step segs (restrict (w_H W) ms) =
    MachineOk (@mkst fb (ms_regs ms) pcv mem' (seg_rom segs)) ->
  st_ok (fx := fb) segs E ss' (@mkst fb (ms_regs ms) pcv mem' (seg_rom segs)) ->
  (forall x : word, w_H W x = true -> mem' x = None) ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mem' x = mrestrict (w_H W) (ms_mem ms) x) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) mem' ->
  (forall a, Wr a -> awr_byte STK sp0 FPl (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  (forall ms1 mat',
     ms_regs ms1 = ms_regs ms ->
     mrestrict (w_H W) (ms_mem ms1) = mem' ->
     (forall x : word, w_H W x = true -> ms_mem ms1 x = ms_mem ms x) ->
     st_ok (fx := fb) segs E ss' (restrict (w_H W) ms1) ->
     ajournal segs B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat' md) k ->
     SRr segs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr segs W (mkCfg ms md) Q.
Proof.
intros fb W E ss' ms md Q STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k Wr mem' pcv
  Hsvc HJ Hstep Hok' Hcl Hfr Hgr HW HK.
eapply (SRr_step segs Hwx W); [exact Hsvc | exact Hstep |].
intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
assert (Hclm : hclean (w_H W) (@mkst fb (ms_regs ms) pcv mem' (seg_rom segs)))
  by (intros a Ha; cbn [ms_mem mkst]; exact (Hcl a Ha)).
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) _ Hclm) as Hmm.
cbn [ms_mem mkst] in Hmm.
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hclm) as Hrr.
apply HK.
- cbn [unrestrict ms_regs]. reflexivity.
- exact Hmm.
- intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
- rewrite Hrr. exact Hok'.
- eapply (ajournal_exec segs B LAWS Hsegs) with (Wr := Wr); [exact HJ | | | | |].
  + intros x Hx. rewrite Hmm. exact (Hfr x Hx).
  + rewrite Hmm. exact Hgr.
  + intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
  + apply same_but_materialized_wvb_any.
  + exact HW.
Qed.
End f.
End e.
End d.
