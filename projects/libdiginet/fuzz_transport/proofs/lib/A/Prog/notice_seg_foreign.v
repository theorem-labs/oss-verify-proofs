(* notice_seg_foreign: the arm of notice for a notice of kind N_FOREIGN (0x8371c), which counts the notice and
   returns:
     +0x1a4 .. +0x1ac  a1 = (s32) GOT.foreign, a1 = a1 + 1, `sw a1, -872(a0)` with a0 the auipc value of the
                       field (pinned to the field's object so the store lands in its region);
     +0x1b0 .. +0x1b8  the epilogue (ra restored, sp + 16) and `ret`.
   The world's only change is GOT.foreign (notice_m's N_FOREIGN case, nt_m_foreign). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_data_cg check_state_desk_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import notice_seg_base notice_seg_lib notice_seg_disp.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The bytes a notice of kind N_FOREIGN writes: GOT.foreign's four. *)
Lemma nt_wr_foreign : forall Bw n a, TI.n_kind n = TC.N_FOREIGN -> notice_wr Bw n a ->
  TA_GOT + 212 <= a < TA_GOT + 216.
Proof.
  intros Bw n a Hk Hw.
  unfold notice_wr, TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in Hk, Hw.
  unfold twa_fld, TW.A_GOT_foreign, TW.OFF_GOT in Hw.
  destruct Hw as [(E & _) | [(E & _) | [(E & _) | [(E & _) | [(E & _) | (E & Ha)]]]]]; try lia.
Qed.

Lemma nt_le_byte_mod : forall v (m j : nat), YO0f.le_byte (v mod 2 ^ (8 * Z.of_nat m)) m j = YO0f.le_byte v m j.
Proof.
  intros v m j. unfold YO0f.le_byte.
  rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma nt_le_byte_small : forall v (m j : nat), 0 <= YO0f.le_byte v m j < 256.
Proof. intros v m j. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma nt_mod_64_32 : forall v, bv_unsigned (Z_to_bv 64 v) mod 2 ^ 32 = v mod 2 ^ 32.
Proof.
  intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity.
Qed.

Lemma nt_le_byte_mod32 : forall v (j : nat), YO0f.le_byte (v mod 2 ^ 32) 4 j = YO0f.le_byte v 4 j.
Proof.
  intros v j. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma nt_path_foreign : @nt_path fx rc B MT TC.N_FOREIGN NT_FOREIGN.
Proof.
unfold nt_path.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E ms md
  HC Ek HS HEI HElo HEd SHOK HJ KA.
destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
  as (HAR & Hwin & Hsp & Hce & Hm16 & Hp4096 & Hp47 & Hp8 & Hoffp & Hrd).
pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJ0 Hra Hra4 Hgp Htp H11 Hsp16
  Hlo Hhi HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : NOTICE_STK = 8240) by reflexivity.
destruct (nt_m_foreign timg_A Fr Bw n Bw' Ek Hm) as [Hmax HBw].
(* the valuation at the arm *)
pose proof (nt_E_atom regs NB Bw 9%nat ltac:(lia)) as E41q. cbn [Nat.add nth nt_vals] in E41q.
assert (E41 : ew E 41 = Z_to_bv 64 (TW.u_at Bw TW.A_GOT_foreign 4)) by (rewrite (HElo 41%nat ltac:(lia)); exact E41q).
assert (U39 : bv_unsigned (ew E (A_OBJ 39)) = TA_GOT + 212)
  by (rewrite (HEI (A_OBJ 39) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); vm_compute; reflexivity).
assert (U39n : bv_unsigned (ew E 280%nat) = TA_GOT + 212) by exact U39.
pose proof (nt_KA_mono W memc (ms_mem ms) (nt_Wn regs) (nt_Zs regs Bw n)
  (fun a Ha => nt_Wn_Zs regs Bw n a Ha) KA) as KA0.
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (HElo 2%nat ltac:(lia)); rewrite (nt_E_reg regs NB Bw 2%nat 2%bv eq_refl); reflexivity).
pose proof (nt_E_atom regs NB Bw 0%nat ltac:(lia)) as E32q. cbn [Nat.add nth nt_vals] in E32q.
assert (E32e : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (HElo 32%nat ltac:(lia)); exact E32q).
assert (U11e : bv_unsigned (ew E 11) = p).
{ rewrite (HElo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11%nat 11%bv eq_refl), H11.
  apply unsigned_lit_small. lia. }
assert (HtwM : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) Bw).
{ apply (nt_tw_keep W memc (ms_mem ms) Bw (nt_Wn regs) Htw KA).
  intros x Hx Hz. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia. }
(* GOT.foreign's region added *)
pose proof (nt_add E _ _ (nt_reg_fld 39 41) HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq.
specialize (HSq ltac:(cbn [ms_mem restrict]; apply (nt_fld_ok W _ E Bw 39%nat 41%nat 212);
  [exact U39 | lia | unfold TW.SZ_GOT; lia | exact E41 | exact HtwM])).
specialize (HSq ltac:(cbn [all_disjoint]; split; [|exact I];
  unfold extent_disjoint, nt_reg_fld, nt_reg_frame;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold TA_GOT in U39; lia)).
rename HSq into HS.
pose proof (nt_facts_set E _ _ (nt_facts_f 280%nat (TA_GOT + 212)) HS
  ltac:(apply (nt_facts_f_ok E (spZ regs) p 280%nat (TA_GOT + 212));
        first [exact Usp | exact U11e | exact E32e | exact U39n | lia])) as HSq.
clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport)) as RET.
(* run 1, +0x1a4 .. +0x1a8: the load of GOT.foreign and the increment; the store needs its auipc pinned *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ nt_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md1 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md1; clear mt end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
  assert (KA1 : nt_KA W memc (ms_mem mz) (nt_Zs regs Bw n)) by
    (apply (nt_KA_run _ _ W memc _ _ _ KA0 HFr HG);
     intros b wlo whi x Hin Hx; cbv beta;
     nt_win Hin Hx ltac:(rewrite ?Usp, ?U39n in Hx;
       first [ left; unfold nt_Wn; lia
             | right; unfold notice_wr, twa_fld, TW.A_GOT_foreign, TW.OFF_GOT;
               do 5 right; split; [exact Ek | unfold TA_GOT in *; lia] ])) end.
clear HF HFr HG.
nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (TA_GOT + 212 + 872)) Q10
  ltac:(cbn [sv_denot]; rewrite (HEI 477%nat ltac:(unfold A_TEXT, A_LIM; lia)); f_equal; vm_compute; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ =>
  assert (QD : sv_denot EF (SOff (A_OBJ 39) 872) = Z_to_bv 64 (TA_GOT + 212 + 872)) by
    (cbn [sv_denot]; rewrite (HEI (A_OBJ 39) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
     f_equal; vm_compute; reflexivity);
  pose proof (nt_pin EF _ _ (Z_to_bv 5 10) (SOff (A_OBJ 39) 872) HS (eq_trans Q10 (eq_sym QD))
    ltac:(vm_compute; reflexivity)) as HSq end.
clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
(* run 2, +0x1ac .. +0x1b8: the store of GOT.foreign + 1 and the epilogue *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ nt_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md2 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md2; clear mt end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
  assert (KA2 : nt_KA W memc (ms_mem mz) (nt_Zs regs Bw n)) by
    (apply (nt_KA_run _ _ W memc _ _ _ KA1 HFr HG);
     intros b wlo whi x Hin Hx; cbv beta;
     nt_win Hin Hx ltac:(rewrite ?Usp, ?U39n in Hx;
       first [ left; unfold nt_Wn; lia
             | right; unfold notice_wr, twa_fld, TW.A_GOT_foreign, TW.OFF_GOT;
               do 5 right; split; [exact Ek | unfold TA_GOT in *; lia] ])) end.
clear HF HFr HG KA1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into msF end.
(* the field's new value, read back from its region *)
assert (HVAL : val_mem segs (mrestrict (w_H W) (ms_mem msF)) (TA_GOT + 212 + 0) 4
  (bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 41 0)) (SLit 1))) mod 2 ^ (8 * Z.of_N 4))).
{ eapply (field_of_region_any E _ 280%nat (TA_GOT + 212) _ 0 4 0 4 0 4%N
    (SAlu ALU_ADD (SExt true 32 (SOff 41 0)) (SLit 1))).
  - exact (st_ok_pi_region_nth E _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)).
  - exact U39n.
  - cbn [In]. left. reflexivity.
  - lia. }
assert (HDEN : sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 41 0)) (SLit 1))
  = Z_to_bv 64 (TW.GOT_foreign Bw + 1)).
{ change (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 41 0)) (SLit 1)))
    with (alu64 ALU_ADD (sv_denot E (SExt true 32 (SOff 41 0))) (Z_to_bv 64 1)).
  pose proof (TWL.u_at_range Bw TW.A_GOT_foreign 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  rewrite (nt_sext32 E 41 _ E41 R).
  rewrite nt_add_lit. reflexivity. }
rewrite HDEN in HVAL. change (8 * Z.of_N 4) with 32 in HVAL. rewrite nt_mod_64_32 in HVAL.
(* the return *)
nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
  ltac:(cbn [sv_denot]; rewrite (HElo 1%nat ltac:(lia));
        rewrite (nt_E_reg regs NB Bw 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (HPF : aregs_preserved regs (ms_regs msF)).
{ apply (aregs_preserved_of_st_ok segs (w_H W) E _ msF regs (nt_vals NB Bw) HS).
  - apply nt_agree; [intros j Hj; apply HElo; lia | exact HEd].
  - vm_compute. reflexivity. }
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
refine (nt_close B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
  (ms_regs msF) (ms_mem msF) md2 HC HJ KA2 _ HPF RF1 mat').
(* the world after the store: GOT.foreign + 1 *)
rewrite HBw. unfold TW.set_GOT_foreign, TW.A_GOT_foreign.
apply (tw_write TMAP_A (aview segs (w_H W) memc) _ Bw TW.OFF_GOT TA_GOT TW.SZ_GOT 212 4
  (TW.GOT_foreign Bw + 1) TMAP_A_ok Htw TMAP_A_GOT ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)).
- intros j Hj. unfold aview.
  replace (TA_GOT + 212 + Z.of_nat j) with (TA_GOT + 212 + 0 + Z.of_nat j) by lia.
  rewrite (HVAL j Hj). cbn [option_map]. f_equal.
  rewrite AF0x.unsigned_lit_small8
    by (match goal with |- 0 <= YO0f.le_byte ?v ?m ?jj < _ => pose proof (nt_le_byte_small v m jj) end; lia).
  apply nt_le_byte_mod32.
- intros x Hx Hout. destruct KA2 as [KA2v _]. apply KA2v.
  + pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. lia.
  + intros [Hz | Hz].
    * pose proof (TMAP_A_hull x Hx) as Hh. unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia.
    * pose proof (nt_wr_foreign Bw n x Ek Hz) as Hr. lia.
Qed.
End f.
