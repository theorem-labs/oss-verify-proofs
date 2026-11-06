(* notice_seg_foreign: the N_FOREIGN arm of notice's walk on fuzz_transport.asan-ubsan (lib/B/Prog/notice_cgW.v),
   from the jump `jr a0` (0x83474) with a0 = 0x835f0:
     0x835f0 - 0x835f8  a0 = the auipc value 0x5e55f0; a2 = GOT.foreign (the 4-byte signed load at GOT + 212, read
                        from the region of that field, its value the world's u32), a1 = a2 + 1 (addiw);
     0x835fc            `blt a1, a2` to the UBSan trap 0x83610: taken exactly at INT_MAX (nt_ovf_br), which notice_m
                        rules out (its int_inc is None there);
     0x83600            the store of a1 at a0 - 1468 = GOT + 212 (a0 pinned to that field's object + 1468);
     0x83604 - 0x8360c  ra loaded back, sp = sp + 16, return.
   The post: the world is set_GOT_foreign Bw (GOT.foreign + 1) (nt_tw_set4), every other byte the walk keeps. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg check_state_desk_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import notice_seg_base notice_seg_lib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section foreign. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma nt_foreign : @nt_path fx rc B MT TC.N_FOREIGN NT_FOREIGN.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E ms md
  HC Ek HS HEI Elo Ed SHOK HJ KA0.
destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
  as (HAR & Hwin & Hsp & Hce & Hm16 & Hp4096 & Hp47 & Hp8 & Hoffp & Hrd).
pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJc Hra Hra4 Hgp Htp H11 Hsp16 Hlo Hhi
    HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : NOTICE_STK = 8240) by reflexivity.
destruct (nt_m_foreign timg_B Fr Bw n Bw' Ek Hm) as [Hmax HBw].
destruct nt_cvals as (V1 & V95 & VN & V36 & V13 & V37 & V38 & V39 & V40 & V73 & V72 & V74 & V75 & V77 & VB).
(* the atoms the arm reads *)
assert (E41 : ew E 41 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_GOT + 212) 4)).
{ rewrite (Elo 41%nat ltac:(lia)). exact (nt_E_atom regs NB Bw 9 ltac:(lia)). }
pose proof (TWL.u_at_range Bw (TW.OFF_GOT + 212) 4) as R41. change (8 * Z.of_nat 4) with 32 in R41.
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (Elo 2%nat ltac:(lia)), (nt_E_reg regs NB Bw 2 2%bv eq_refl); reflexivity).
assert (U40 : bv_unsigned (ew E (A_OBJ 40)) = TB_GOT + 212).
{ rewrite (HEI (A_OBJ 40) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V40. reflexivity. }
assert (U40n : bv_unsigned (ew E 281) = TB_GOT + 212) by exact U40.
assert (U77 : bv_unsigned (ew E (A_HI 77)) = VAL (A_HI 77))
  by (apply HEI; unfold A_HI, A_OBJ, A_TEXT, A_LIM; lia).
assert (U77n : bv_unsigned (ew E 477) = VAL (A_HI 77)) by exact U77.
(* the world at the arm's entry, and the field's region *)
pose proof (nt_tw_Wn W memc (ms_mem ms) regs Bw ltac:(unfold TG.G_HARNESS_B_HI; lia) Htw KA0) as Htw0.
pose proof (nt_add E _ _ (nt_reg_fld 40 41) HS ltac:(vm_compute; reflexivity)) as HS2. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts nt_ss_jr] in HS2.
specialize (HS2 ltac:(cbn [ms_mem restrict];
  exact (nt_fld_ok W (ms_mem ms) E Bw 40 41 212 U40 ltac:(lia) ltac:(unfold TW.SZ_GOT; lia) E41 Htw0))).
specialize (HS2 ltac:(cbn [all_disjoint]; split; [|exact I];
  unfold extent_disjoint, nt_reg_fld, nt_reg_frame;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Usp, U40; unfold TB_GOT; lia)).
rename HS2 into HS.
assert (U11 : bv_unsigned (ew E 11) = p).
{ rewrite (Elo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11 11%bv eq_refl), H11. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (Elo 32%nat ltac:(lia)); exact (nt_E_atom regs NB Bw 0 ltac:(lia))).
pose proof (nt_facts_set E _ _ (nt_facts_g 40 (TB_GOT + 212)) HS
  (nt_facts_g_ok E (spZ regs) p 40 (TB_GOT + 212) Usp U11 E32 U40 ltac:(lia) Hsp16 ltac:(lia) Hp8
    ltac:(unfold TB_GOT; reflexivity))) as HS2.
clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2. rename HS2 into HS.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
pose proof (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb)) as RET.
(* run 1: the jump, the load of GOT.foreign, the increment, to `blt` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U40, ?U40n in Ha.
    apply nt_inG_GOT. lia. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
  left. split; [unfold awr_byte; left; lia | lia]. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
assert (KA1 : nt_KA W memc (ms_mem ms1) (nt_Zs regs Bw n)).
{ apply (nt_KA_run _ _ W memc _ _ _ (nt_KA_mono W memc _ _ _ (nt_Wn_Zs regs Bw n) KA0) HFr HG).
  intros b wlo whi x Hin Hx. cbv beta.
  nt_win Hin Hx ltac:(rewrite ?Usp, ?U40, ?U40n in Hx; first
    [ left; unfold nt_Wn; lia
    | right; unfold notice_wr; right; right; right; right; right; split; [exact Ek|];
      unfold twb_fld, TW.A_GOT_foreign; lia ]). }
clear HF HFr HG.
(* the runs of this arm make no fresh atom (sh_j = 0): the valuation stays E *)
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* the trap: GOT.foreign = INT_MAX *)
  rewrite (nt_ovf_br E 41 _ E41 R41) in Hc. apply Z.eqb_eq in Hc. exfalso. apply Hmax. exact Hc.
- rewrite (nt_ovf_br E 41 _ E41 R41) in Hc. apply Z.eqb_neq in Hc.
  (* a0 pinned to the field's object + 1468 *)
  nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (VAL (A_HI 77))) Q10
    ltac:(cbn [sv_denot]; rewrite ?U77, ?U77n, Z.add_0_r; reflexivity).
  pose proof (nt_pin E _ _ (Z_to_bv 5 10) (SOff (A_OBJ 40) 1468) HS
    ltac:(cbn [ms_regs restrict]; rewrite Q10; cbn [sv_denot]; rewrite U40, V77; f_equal; lia)
    ltac:(vm_compute; reflexivity)) as HS3.
  clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond] in HS3. rename HS3 into HS.
  (* run 2: the store, the epilogue, to `ret` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_cons_g.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U40, ?U40n in Ha.
      apply nt_inG_GOT. lia. }
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
    left. split; [unfold awr_byte; left; lia | lia]. }
  set (mdF := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody mdF. clear mat.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  assert (KAF : nt_KA W memc (ms_mem msF) (nt_Zs regs Bw n)).
  { apply (nt_KA_run _ _ W memc _ _ _ KA1 HFr HG).
    intros b wlo whi x Hin Hx. cbv beta.
    nt_win Hin Hx ltac:(rewrite ?Usp, ?U40, ?U40n in Hx; first
      [ left; unfold nt_Wn; lia
      | right; unfold notice_wr; right; right; right; right; right; split; [exact Ek|];
        unfold twb_fld, TW.A_GOT_foreign; lia ]). }
  clear HF HFr HG.
  (* the field's 4 bytes at the return *)
  pose proof (st_ok_pi_region_nth E _ (restrict (w_H W) msF) 0 _ HS eq_refl) as RGF.
  cbn [ms_mem restrict] in RGF.
  destruct RGF as (_ & _ & _ & HCH). cbn [YP09.r_base YP09.r_chunks base_val] in HCH.
  apply Forall_cons_iff in HCH as [HCH _].
  rewrite ?U40, ?U40n in HCH.
  assert (HV4 : forall j, (j < 4)%nat ->
    aview segs (w_H W) (ms_mem msF) (TB_GOT + 212 + Z.of_nat j) =
    Some (YO0f.le_byte (TW.GOT_foreign Bw + 1) 4 j)).
  { intros j Hj. pose proof (nt_chunk_aview W (ms_mem msF) E (TB_GOT + 212) 0 4 _ (Z.of_nat j) HCH ltac:(lia)) as X.
    rewrite Z.add_0_r in X. rewrite X. f_equal.
    apply (nt_inc_bytes E 41 _ j); [exact E41 | exact R41 | exact Hc | exact Hj]. }
  nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite (Elo 1%nat ltac:(lia)), (nt_E_reg regs NB Bw 1 1%bv eq_refl), Z.add_0_r,
            Z_to_bv_bv_unsigned; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs msF)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E _ msF regs (nt_vals NB Bw) HS).
    - split; [intros j Hj; rewrite (Elo j ltac:(lia)); unfold nt_E; apply Eimg_low; unfold A_TEXT; lia
             | rewrite Ed; reflexivity].
    - vm_compute. reflexivity. }
  assert (HtwF : tw_at TMAP_B (aview segs (w_H W) (ms_mem msF)) Bw').
  { rewrite HBw. unfold TW.set_GOT_foreign, TW.A_GOT_foreign.
    apply (nt_tw_set4 W memc (ms_mem msF) Bw TW.OFF_GOT TB_GOT TW.SZ_GOT 212 (TW.GOT_foreign Bw + 1) Htw TMAP_B_GOT);
      [lia | unfold TW.SZ_GOT; lia | exact HV4 |].
    intros x Hx Hn. pose proof KAF as [KAx _]. apply KAx.
    + pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia.
    + unfold nt_Zs. intros [Hz | Hz].
      * pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_HI in Hh. lia.
      * apply Hn. unfold notice_wr in Hz.
        unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in Hz, Ek.
        destruct Hz as [(E' & _) | [(E' & _) | [(E' & _) | [(E' & _) | [(E' & _) | (_ & Hz)]]]]]; try lia.
        unfold twb_fld, TW.A_GOT_foreign in Hz. lia. }
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  exact (nt_close B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
    (ms_regs msF) (ms_mem msF) mdF HC HJ KAF HtwF HPF RF1 mat').
Qed.
End foreign.
