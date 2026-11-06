(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module paths, module names and numbers changed; 229 of its 304 lines of code are new or changed and 1135 lines of the source are left out. *)
(* TickBLost: Theorem tick_lost : tick_lost_stmt (lib/B/Prog/TickCutB.v), the lost piece of the walk of
   diginet_session_tick on fuzz_transport.asan-ubsan (0x8909c = transportb_sigma TB_diginet_session_tick,
   AF_diginet_session_tick = 0x7dfc of lib/B/Prog/DgnTransportBList.v): code +0x478 .. +0x484 (0x89514 .. 0x89520) and
   +0x604 (0x896a0), the call of set_state (s, S_IDLE, why) shared by the wake and online lost arms (:164, :422,
   :426), from the lost cut tick_lost_at to the epilogue cut tick_epi_at. The runs are the position-abstract runs of
   lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x over the caller's G journal, each from a symbolic state with
   no region (the block reads and writes no memory):
     run C  +0x478 .. +0x480  a0 = s4 (= s), a1 = 0 (S_IDLE), `jal set_state` (ra = 0x89520);
     run D  +0x484, +0x604    `j` +0x604, `li s10, 0`, to the epilogue cut.
   set_state is taken through its contract (lib/B/Prog/set_state_cg.v transport_set_state_cg, the fourth of
   tick_callees) in the same G journal. Its premises: the model's step and r = DIGINET_OK from the cut's model fact
   (TickCutB.v tick_lost_inv); the world relation at slost_w1 Bw (tick_lost_cur); g_fail_next (slost_w1 Bw) =
   g_fail_next Bw (lib/A/Prog/SlostHead.v slh_w1_facts, image-free: its slost_w1 is the B statement's text); TF's
   trans_tframe_at at set_state's window from the entry's (lib/B/Prog/TickBKit.v trans_tframe_at_top over the written
   range tick_wr Bw, with tick_wr_lo); set_state's written range inside tick_wr Bw (diginet_session_tick_cg.v
   tick_wr_sstate), so TF apart from it by tick_apart; the class-2 frame free (tick_fix, SSTATE_CID = TRANS_BC_CID).
   After the call the caller's kept memory is carried by TransportGCg.v dk_kept_trans_nf_g (set_state's acall_kept_g
   at the call state, written range inside tick_wr Bw), the saved words and the frame's last word by set_state's
   window and frame clauses, and run D writes nothing (lib/B/Prog/TickBTail.v tt_KA, tt_cur_move). The registers the
   epilogue reads are set_state's preserved ones and s10 = 0 = r. The structure is image A's keepalive tail
   (lib/A/Prog/TickKa_rest.v: a G-form callee in the same journal, folded into tick_epi_cur) and image A's wake piece
   (lib/A/Prog/TickWake.v: TF at the call by trans_tframe_at_top). TickBTail.v is loaded by Require only (its theorem
   tick_tail would hide the model function tick_tail). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBCg TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg set_state_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg TickCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TickBKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require TickBTail.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TickCut SlostHead.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module TCA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TickCut.
Module TT := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.TickBTail.
Module SLH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.SlostHead.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* set_state's return address: the `j` after the call (+0x484). *)
Definition TLO_R : Z := AF_diginet_session_tick + 0x484.

(* A symbolic state with no region and no fact, at pc. *)
Definition ss_lo (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

(* The value of an unchanged register of the run's valuation: its value at the run's entry. *)
Ltac tl_rv EE R :=
  cbn [sv_denot];
  lazymatch goal with |- context [ew _ ?n] => rewrite (EE n (Z_to_bv 5 (Z.of_nat n)) eq_refl) end;
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R.
(* The value of register r in the machine state of a symbolic state HS (after a run to a call, HS is a plain st_ok
   at the callee's pc): its symbolic value, computed, then tac (lib/A/Prog/TickKa_rest.v tka_reg). *)
Ltac tl_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "tl_reg: no match for" T; fail
  end.

Section tl. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The entry of a run from ss_lo pc: every register its atom. *)
Lemma tl_entry : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) (ss_lo pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx. unfold ss_lo.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I].
Qed.

Lemma tl_holds : @tick_lost_stmt fx rc B MT.
Proof.
unfold tick_lost_stmt. intros EPI. unfold tick_lost_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F why
  S2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGNE0 & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGE).
pose proof CALLEES as (_ & _ & _ & HSS & _).
pose proof HFIX as (HJe & Hret & Hra4 & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf0 & Hm0 & HTF &
  Hrom & Hap & Hinv & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HCU & Hbl & HGK & Htw1 & Hwhy & Hm).
pose proof HCU as (HJ & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFL).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R20 & R12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold TCA.TICK_FBYTES in HFc, HFapp, HFL.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJe) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite ?Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _ & _ & _ & ESLO & ESHI & _).
assert (HTS : TICK_STK = 8896) by reflexivity.
assert (HSST : SSTATE_STK = 8416) by reflexivity.
assert (HSTKLT : ly_stk_lo lyc < ly_stk_hi lyc) by (rewrite ESLO, ESHI; lia).
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold TICK_FRAME.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (r0 := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (Hce : alloc_ceiling <= spZ regs - TICK_STK) by lia.
assert (Hin : In (TICK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
(* the model: set_state's step at slost_w1 Bw, and r = DIGINET_OK *)
destruct (tick_lost_inv timg_B TF Bw Bw' why r Hm) as [HSM1 Er]. subst r.
assert (G1 : TW.g_fail_next (slost_w1 Bw) = TW.g_fail_next Bw) by exact (proj2 (SLH.slh_w1_facts Bw HLB)).
assert (Rwhy : 0 <= why < 2 ^ 31)
  by (destruct Hwhy as [Hw | Hw]; rewrite Hw; unfold TS0.DIGINET_R_WAKE_TIMEOUT, TS0.DIGINET_R_SILENCE; lia).
(* run C, +0x478 .. +0x480: a0 = s, a1 = 0, `jal set_state` *)
pose proof (tl_entry W regs2 mem2 TICK_LOST) as HS.
set (E0 := Eimg (PI := PI_transportb) (Ereg regs2 [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E0 n = YK11.getr regs2 q)
  by (intros n q Hn; unfold E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK : sh_ok segs TT.TT_Bx (@nil shent) E0 (mrestrict (w_H W) mem2)) by constructor.
assert (KA : TT.tt_KA W mem2 mem2) by apply TT.tt_KA_refl.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUNTO.
paj_run_tok RUN HS HJ SHOK TT.TT_B0.
{ TT.tt_awr. }
TT.tt_after KA HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdC := mdx) in * end.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARN.
(* the cut's facts at the call's memory (run C wrote nothing) *)
pose proof (TT.tt_cur_move B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCU HJ KA) as HCUN.
pose proof HCUN as (_ & _ & _ & _ & _ & _ & KC & _ & _).
assert (GKN : gx_kept_ex segs TG.G_HARNESS_B (tick_wr Bw) W memc W (ms_mem ms)).
{ intros a Ha Hn. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Ha) as Hl.
  unfold kLowMemEnd in Hl. destruct KA as [KA1 _]. rewrite (KA1 a ltac:(lia)). exact (HGK a Ha Hn). }
pose proof (TT.tt_tw_move W mem2 (ms_mem ms) (slost_w1 Bw) KA Htw1) as PTW.
(* the registers at the call *)
pmkst HS.
tl_reg HS (Z_to_bv 5 10) (w64 SSTATE_S) Q10 ltac:(tl_rv EE R20).
tl_reg HS (Z_to_bv 5 11) (w64 TS0.DIGINET_S_IDLE) Q11 ltac:(reflexivity).
tl_reg HS (Z_to_bv 5 12) (w64 why) Q12 ltac:(tl_rv EE R12).
tl_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + TLO_R)) Q1 ltac:(apply codeptr_val; exact HEI).
tl_reg HS (Z_to_bv 5 2) (w64 sp1) Q2 ltac:(tl_rv EE R2).
tl_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) Q3 ltac:(tl_rv EE (eq_trans R3 Hgp)).
tl_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) Q4 ltac:(tl_rv EE (eq_trans R4 Htp)).
tl_reg HS (Z_to_bv 5 8) (w64 (spZ regs)) Q8 ltac:(tl_rv EE R8).
tl_reg HS (Z_to_bv 5 9) (w64 sp1) Q9 ltac:(tl_rv EE R9).
tl_reg HS (Z_to_bv 5 18) (w64 F) Q18 ltac:(tl_rv EE R18).
tl_reg HS (Z_to_bv 5 27) (w64 F) Q27 ltac:(tl_rv EE R27).
assert (USPC : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
assert (EBR : BASE + TLO_R = 0x89520) by (vm_compute; reflexivity).
(* +0x480: set_state (s, S_IDLE, why), through its contract in the same G journal *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_set_state) rg mm mdx) Qx) end.
eapply SRr_bind.
{ exact (HSS fx STK sp0 FP ly S W0 mem0 md0 ((TICK_CID, pos) :: own) lyc S2 W (ms_mem ms) mdC (k + 0) (ms_regs ms)
    TS0.DIGINET_S_IDLE why TF (slost_w1 Bw) Bw' HJ
    ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold TLO_R, AF_diginet_session_tick; lia |
      reflexivity])
    ltac:(unfold raZ; rewrite Q1, EBR; rewrite unsigned_lit_small by lia; lia)
    Q3 Q4 Q10 Q11 Q12
    ltac:(rewrite USPC; destruct Hsp1 as (_ & M1); pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1;
          rewrite M1, Z.add_0_r in D1; rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring;
          apply Z.mod_mul; lia)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    PTW
    ltac:(rewrite G1; exact Hgf0)
    HSM1
    ltac:(unfold TS0.DIGINET_S_IDLE; lia) Rwhy
    (trans_tframe_at_top B LAWS HRU HRE lyc Sc W memc mdc S2 (ms_mem ms) mdC regs (ms_regs ms) TF (tick_wr Bw)
       TICK_STK SSTATE_STK TICK_CID pos HARc HARN Hfrs Hbl HSTKLT KC GKN Hap (tick_wr_lo Bw)
       ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) HTF)
    ltac:(intros a Ha; rewrite <- (Hrom a Ha); pose proof KC as (_ & _ & K3 & _);
          destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho Hen];
          apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact Hen];
          intro Ga; pose proof (inG_G_HARNESS_hull a Ga) as Gh; pose proof (trans_ro_rd_bounds a Ha) as Rb;
          unfold TG.G_HARNESS_B_LO in Gh; lia)
    ltac:(intros x Hx fr Hfr0; exact (Hap x (tick_wr_sstate Bw why x Hwhy Hx) fr Hfr0))
    ltac:(rewrite Hfrs; change (count_cid SSTATE_CID ((TICK_CID, pos) :: frames Sc)) with
            (0 + count_cid SSTATE_CID (frames Sc)); change SSTATE_CID with TRANS_BC_CID; lia)
    ltac:(unfold SSTATE_EV, NOTICE_EV; unfold TICK_EV in Hev; lia)). }
intros W3 c3 _ HPOST.
unfold transport_sstate_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Xtw &
  Xgf).
assert (He30 : e3 = 0) by (unfold SSTATE_EV, NOTICE_EV in He3; lia). subst e3.
replace (k + 0 + 0) with (k + 0) in HJ3 by lia.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite ?Z.add_0_r in HJi3.
pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
clear HJi3 memS3.
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
assert (Hfrs3 : frames S3 = (TICK_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
(* what the call kept, from its entry to set_state's return *)
assert (KC3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - TICK_STK) (spZ regs)
  (tick_wr Bw)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc lyc S2 W memc W (ms_mem ms) W3 mem3
    (spZ regs - TICK_STK) (spZ regs) (spZ (ms_regs ms) - SSTATE_STK) (spZ (ms_regs ms)) (tick_wr Bw)
    (sstate_wr (slost_w1 Bw) TS0.DIGINET_S_IDLE why) (fun _ => False)).
  - exact Hce.
  - lia.
  - intros c p. reflexivity.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - intros bm Hbm. rewrite Hbl. exact Hbm.
  - intros b m i _ _ Hf. exact Hf.
  - intros cid p a _ _ Hf. exact Hf.
  - exact KC.
  - exact HK3.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. left. exact (tick_wr_sstate Bw why a Hwhy Ha). }
(* the bytes the epilogue reads: the saved words above s1 and the frame's last word *)
pose proof HK3 as (K31 & _ & _ & K34 & _).
assert (KSTK : forall a, sp1 + 64 <= a < spZ regs -> aview segs (w_H W3) mem3 a = aview segs (w_H W) mem2 a).
{ intros a Ha. rewrite USPC in K31. rewrite K31 by lia. destruct KA as [KA1 _]. apply KA1. lia. }
assert (KFL : forall i, 0 <= i < 8 ->
  aview segs (w_H W3) mem3 (F + 2040 + i) = aview segs (w_H W) mem2 (F + 2040 + i)).
{ intros i Hi. transitivity (aview segs (w_H W) (ms_mem ms) (F + 2040 + i)).
  - apply (K34 TICK_CID pos (F + 2040 + i) Hin).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes TICK_CID) with 2048. lia.
    + intros Hw. apply (frm_img segs B LAWS lyc S2 W mem2 md2 TICK_CID pos (F + 2040 + i) HAR2 Hin);
        [rewrite <- EF; change (fs_frame_bytes TICK_CID) with 2048; lia|].
      exact (trans_g_img _ (tick_wr_G Bw _ (tick_wr_sstate Bw why _ Hwhy Hw))).
  - destruct KA as [KA1 _]. apply KA1. lia. }
assert (HSo : forall o, In o TCA.TICK_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold TCA.TICK_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
(* the cut's facts at set_state's return *)
assert (HCU3 : tick_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly3 S3 W3 mem3 md3 0).
{ split; [exact HJ3|].
  split; [unfold TICK_EV; lia|].
  split; [exact Hfrs3|].
  split; [exact (Permutation_trans Hperm3 Hperm)|].
  split; [exact ELF3c|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
  split; [exact KC3|].
  split.
  - rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
    pose proof (HSo o Ho) as Hob. apply YCbq.rdword_ext. intros i Hi. apply KSTK. lia.
  - unfold TCA.TICK_FBYTES. rewrite <- HFL. replace (F + 2048 - 8) with (F + 2040) by lia.
    apply YCbq.rdword_ext. intros i Hi. exact (KFL i Hi). }
assert (CH : forall n, acallee_saved n -> YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr (ms_regs ms) (Z_to_bv 5 n))
  by (intros n Hn; exact (HP3 n Hn)).
rename ms into msC.
(* run D, +0x484 and +0x604: `j`, s10 = 0, to the epilogue cut *)
rewrite Q1.
pose proof (tl_entry W3 regs3 mem3 TLO_R) as HS3.
set (E3 := Eimg (PI := PI_transportb) (Ereg regs3 [])) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E3 n = YK11.getr regs3 q)
  by (intros n q Hn; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK3 : sh_ok segs TT.TT_Bx (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
assert (KA3 : TT.tt_KA W3 mem3 mem3) by apply TT.tt_KA_refl.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 TT.TT_B0 TICK_EPI.
{ TT.tt_awr. }
TT.tt_after KA3 HS3.
pmkst HS3.
tl_reg HS3 (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) F2
  ltac:(tl_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 2)))).
tl_reg HS3 (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) F3
  ltac:(tl_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 3)))).
tl_reg HS3 (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) F4
  ltac:(tl_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 4)))).
tl_reg HS3 (Z_to_bv 5 8) (YK11.getr regs3 (Z_to_bv 5 8)) F8
  ltac:(tl_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 8)))).
tl_reg HS3 (Z_to_bv 5 9) (YK11.getr regs3 (Z_to_bv 5 9)) F9
  ltac:(tl_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 9)))).
tl_reg HS3 (Z_to_bv 5 18) (YK11.getr regs3 (Z_to_bv 5 18)) F18
  ltac:(tl_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 18)))).
tl_reg HS3 (Z_to_bv 5 27) (YK11.getr regs3 (Z_to_bv 5 27)) F27
  ltac:(tl_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 27)))).
tl_reg HS3 (Z_to_bv 5 26) (w64 DLib.DIGINET_OK) F26 ltac:(reflexivity).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_EPI)) mm rom) mdx) Q) end.
apply (EPI LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now DLib.DIGINET_OK TF Bw Bw'
  pos sp1 F ly3 S3 W3 (ms_mem ms) _ 0 (ms_regs ms) HFIX).
- refine (conj _ (conj (TT.tt_tw_move W3 mem3 (ms_mem ms) Bw' KA3 Xtw) Xgf)).
  exact (TT.tt_cur_move B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCU3 HJ3 KA3).
- refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))) F26).
  + exact (eq_trans F2 (eq_trans (CH 2 ltac:(hnf; lia)) Q2)).
  + exact (eq_trans F3 (eq_trans (CH 3 ltac:(hnf; lia)) (eq_trans Q3 (eq_sym Hgp)))).
  + exact (eq_trans F4 (eq_trans (CH 4 ltac:(hnf; lia)) (eq_trans Q4 (eq_sym Htp)))).
  + exact (eq_trans F8 (eq_trans (CH 8 ltac:(hnf; lia)) Q8)).
  + exact (eq_trans F9 (eq_trans (CH 9 ltac:(hnf; lia)) Q9)).
  + exact (eq_trans F18 (eq_trans (CH 18 ltac:(hnf; lia)) Q18)).
  + exact (eq_trans F27 (eq_trans (CH 27 ltac:(hnf; lia)) Q27)).
Qed.

End tl.

(* The lost piece of the walk of diginet_session_tick (TickCutB.v tick_lost_stmt), at every machine, run ceiling,
   record and meter. *)
Theorem tick_lost : forall fx rc B MT, @tick_lost_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@tl_holds fx rc B MT). Qed.
Print Assumptions tick_lost.
