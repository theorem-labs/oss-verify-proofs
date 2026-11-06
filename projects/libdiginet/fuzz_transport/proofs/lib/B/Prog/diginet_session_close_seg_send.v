(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 253 of its 319 lines of code are new or changed and 699 lines of the source are left out. *)
(* diginet_session_close_seg_send: Lemma close_send : close_send_stmt (lib/B/Prog/diginet_session_close_segs.v), the
   send piece of image B's walk of diginet_session_close, offsets +0xd8 .. +0xf4 of the listing
   lib/B/Prog/DgnTransportBList.v (fuzz_transport.asan-ubsan 0x87720 .. 0x8773c), reached from the head when
   close_go Bw holds.

   What the code does. +0xd8 `li a1, 0xe3` (DIGINET_CMD_DISCONNECT), +0xdc `mv a0, s0` (&g_s), +0xe0 `li a2, 0` (ack),
   +0xe4 `li a3, 0` (kp), +0xe8 `li a4, 0` (klp), +0xec `jal send_control` (return address +0xf0); +0xf0 `mv s1, a0`
   (the result r) and +0xf4 `j +0x8c`, the join cut.

   send_control is a G-form callee composed in the same G journal: its statement lib/B/Prog/send_control_cg.v
   transport_send_control_cg is a premise of this walk, taken with kp = klp = 0, so its out cells sendctl_outs 0 0 are
   [] and its post's acall_kept_g is read at the memory it returned (TransportGCg.v gover_nil_mem,
   acall_kept_g_mem_ext). The walk takes no side-stack frame, so the call state is the walk's own (lyc, Sc): what the
   call keeps folds into the walk's kept fact with TransportGCg.v dk_kept_trans_g, whose written range
   sendctl_wr 0 0 lies inside close_wr TF Bw on this path (close_go Bw = true) and whose window
   [sp - 32 - SENDCTL_STK, sp - 32) lies inside [sp - CLOSE_STK, sp). The four saved words lie in [sp - 32, sp),
   above the callee's window, so the callee's first clause keeps them. The two runs (to the call and from its return
   to the join) start from symbolic states with no region, so they write no byte. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg check_state_data_cg notice_cg io_send_cg send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  diginet_session_close_cg diginet_session_close_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The return address of the call of send_control, and the two symbolic states: at the cut (s0 = &g_s pinned, no
   region) and at the return (every register an atom, no region). *)
Definition CLOSE_SRET : Z := AF_diginet_session_close + 0xf0.
Definition cs_ss : sstate :=
  mkSS CLOSE_SEND (sr_set sr_atoms (Z_to_bv 5 8) (SLit CLOSE_S)) [] None (mkFacts [] [] []).
Definition cs_ss2 : sstate := mkSS CLOSE_SRET sr_atoms [] None (mkFacts [] [] []).
Definition CS_Bx : sv := SLit 0.

(* The nine registers s3 .. s11, one by one. *)
Lemma cs_q_cases : forall q, 19 <= q <= 27 ->
  q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27.
Proof. intros q Hq. lia. Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac cs_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "cs_reg: no match for" T; fail
  end.
(* The write right of a run from a state with no region. *)
Ltac cs_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.
(* A run from a state with no region writes no byte. *)
Ltac cs_kept HFr KR W mold msn :=
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem msn) a = aview tfibsegs (w_H W) mold a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []];
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin; destruct Hin
  | ].

Section send. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition cs_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

Lemma cs_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (cs_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold cs_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma cs_env_img : forall regs, img_env VAL A_LIM (cs_E regs).
Proof. intros regs. unfold cs_E. apply Eimg_env. Qed.

(* A symbolic state with no region holds of any machine state at its pc. *)
Lemma cs_entry0 : forall (W : world segs) regs mem (pc : Z),
  st_ok_pi segs VAL (cs_E regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* At the cut, with s0 = &g_s. *)
Lemma cs_entry : forall (W : world segs) regs mem, YK11.getr regs 8 = w64 CLOSE_S ->
  st_ok_pi segs VAL (cs_E regs) cs_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CLOSE_SEND)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem R8.
  exact (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 8) CLOSE_S (cs_entry0 W regs mem CLOSE_SEND) R8 eq_refl).
Qed.

(* Register q of 19 .. 27 (an atom of the state HS) is register q of regsx. *)
Ltac cs_q1 HS regsx :=
  lazymatch goal with |- YK11.getr _ (Z_to_bv 5 ?q) = _ =>
    let n := eval vm_compute in (Z.to_nat q) in
    let H := fresh "Hq" in
    cs_reg HS (Z_to_bv 5 q) (YK11.getr regsx (Z_to_bv 5 q)) H
      ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regsx n (Z_to_bv 5 q) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
            reflexivity);
    exact H
  end.

Lemma close_send : @close_send_stmt fx rc B MT.
Proof.
unfold close_send_stmt. intros JOIN. unfold close_send_at.
intros LAWS0 HSS HSC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' mem2 md2 regs2
  HFIX HCUR HREGS.
pose proof LAWS0 as (HCELLS & HZC & HRU & HRE & LAWS & MTL & HGX).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm & HTF &
  Hrom & Hapart & Htfg & Hinv1 & Hinv4 & Hcnt & Hev).
pose proof HCUR as ((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved) & Htw1 & Hgo).
pose proof HREGS as (R2 & R3 & R4 & R8 & R18 & Rq).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof close_stk_val as (SV1 & SV2 & _ & SV4).
pose proof close_ev_val as (EV1 & EV2 & _).
rewrite Z.add_0_r in HJ1.
(* the stack geometry *)
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _).
clear HJi memS.
assert (Hce : alloc_ceiling <= spZ regs - CLOSE_STK) by lia.
assert (H47r : spZ regs <= 2 ^ 47) by lia.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
(* the model: the send gives B1 and r *)
destruct (close_send_some timg_B TF Bw now Bw' r Hm Hgo) as (B1 & f & HSM1 & HS1).
(* ---- +0xd8 .. +0xec: the five argument moves and the call ---- *)
pose proof (cs_entry W regs2 mem2 R8) as HS.
assert (HEI : img_env VAL A_LIM (cs_E regs2)) by apply cs_env_img.
assert (SHOK : sh_ok segs CS_Bx (@nil shent) (cs_E regs2) (mrestrict (w_H W) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G_HARNESS_B HGX
  0 []) as RUNTO.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CLOSE_SEND)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
paj_run_tok RUN HS HJ1 SHOK YC4b.Bspan.
{ cs_awr. }
cs_kept HFr KR W mem2 ms.
assert (GR1 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the registers at the call *)
cs_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + CLOSE_SRET)) Q1 ltac:(apply codeptr_val; exact HEI).
cs_reg HS (2%bv : bv 5) (w64 (spZ regs - CLOSE_FRAME)) Q2
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs2 2 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
cs_reg HS (3%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 3)) Q3
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs2 3 (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cs_reg HS (4%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 4)) Q4
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs2 4 (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cs_reg HS (10%bv : bv 5) (w64 SENDCTL_S) Q10 ltac:(reflexivity).
cs_reg HS (11%bv : bv 5) (w64 TS0.DIGINET_CMD_DISCONNECT) Q11 ltac:(reflexivity).
cs_reg HS (12%bv : bv 5) (w64 (bv_swrap 32 0)) Q12 ltac:(reflexivity).
cs_reg HS (13%bv : bv 5) (w64 0) Q13 ltac:(reflexivity).
cs_reg HS (14%bv : bv 5) (w64 0) Q14 ltac:(reflexivity).
assert (QSP : spZ (ms_regs ms) = spZ regs - CLOSE_FRAME)
  by (unfold spZ at 1; rewrite Q2; unfold w64; apply unsigned_lit_small; rewrite SV4; lia).
(* the callee-saved registers the join reads, at the call *)
cs_reg HS (8%bv : bv 5) (w64 CLOSE_S) Q8 ltac:(reflexivity).
cs_reg HS (18%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 18)) Q18
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs2 18 (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
assert (Qq : forall q, 19 <= q <= 27 -> YK11.getr (ms_regs ms) (Z_to_bv 5 q) = YK11.getr regs2 (Z_to_bv 5 q)).
{ intros q Hq.
  destruct (cs_q_cases q Hq) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; cs_q1 HS regs2. }
(* the world relation at the call memory *)
assert (TWc : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms)) Bw).
{ apply (tw_kept TMAP_B (aview segs (w_H W) mem2)); [exact Htw1|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hh.
  apply KR. lia. }
(* the walk's kept fact at the call memory, and the read-only bytes there *)
assert (KCN : acall_kept_g segs B G_HARNESS_B lyc Sc W memc W (ms_mem ms) (spZ regs - CLOSE_STK) (spZ regs)
  (close_wr TF Bw)).
{ apply (dk_kept_step_g segs B LAWS transportb_segs_low G_HARNESS_B lyc Sc W memc mdc mem2 (ms_mem ms)
    (spZ regs - CLOSE_STK) (spZ regs) (close_wr TF Bw) (fun _ : Z => False) HARc HK
    ltac:(intros a Ha _; exact (KR a Ha)) GR1); intros; contradiction. }
assert (ROMc : trans_rom_view_rd W (ms_mem ms))
  by exact (close_rom B HRU HRE lyc Sc W memc W (ms_mem ms) _ _ _ KCN Hrom).
assert (EBR : BASE + CLOSE_SRET = 0x87738) by (vm_compute; reflexivity).
(* +0xec: the call of send_control *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB_send_control)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ exact (HSC fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) _ k (ms_regs ms)
    TS0.DIGINET_CMD_DISCONNECT 0 0 0 r [] [] f TF Bw B1
    ltac:(apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJ1)
    ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transportb));
          [unfold CLOSE_SRET, AF_diginet_session_close; lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, EBR; rewrite unsigned_lit_small by lia; lia)
    ltac:(exact (eq_trans Q3 (eq_trans R3 Hgp))) ltac:(exact (eq_trans Q4 (eq_trans R4 Htp)))
    Q10 Q11 Q12 Q13 Q14
    ltac:(rewrite QSP; unfold CLOSE_FRAME; rewrite <- (Z.mod_add (spZ regs - 32) 2 16) by lia;
          replace (spZ regs - 32 + 2 * 16) with (spZ regs) by ring; exact Hsp16)
    ltac:(rewrite QSP; lia) ltac:(rewrite QSP; lia)
    ltac:(unfold TS0.DIGINET_CMD_DISCONNECT; lia) ltac:(lia)
    (or_introl eq_refl)
    TWc Hgf HSM1 ROMc Hinv1 Hinv4 Hcnt ltac:(lia)). }
cbv beta.
intros W3 c3 _ HPOST.
unfold transport_sendctl_post, transport_cg_post_out in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & Ec3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HKg & Hmo3 &
  (HA0 & HTW3 & HGF3 & _)).
assert (Ee3 : e3 = 0) by lia. subst e3. rewrite Z.add_0_r in HJ3.
rewrite Q1 in Ec3. subst c3.
(* the callee's kept fact, at the memory it returned (no out cell) *)
assert (HK3 : acall_kept_g segs B G_HARNESS_B lyc Sc W (ms_mem ms) W3 mem3
  (spZ (ms_regs ms) - SENDCTL_STK) (spZ (ms_regs ms)) (sendctl_wr 0 0)).
{ apply (acall_kept_g_mem_ext segs B G_HARNESS_B lyc Sc W (ms_mem ms) W3
    (gover (sendctl_outs 0 0) mem3 (ms_mem ms)) mem3 _ _ (sendctl_wr 0 0)
    (fun x => eq_sym (gover_nil_mem mem3 (ms_mem ms) x)) HKg). }
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (_ & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
clear HJi3 memS3.
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
(* what the call kept, folded into the walk's own kept fact *)
assert (KC3 : acall_kept_g segs B G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - CLOSE_STK) (spZ regs)
  (close_wr TF Bw)).
{ eapply dk_kept_trans_g with (W1 := W) (memX := ms_mem ms) (slo' := spZ (ms_regs ms) - SENDCTL_STK)
    (shi' := spZ (ms_regs ms)) (Eo' := sendctl_wr 0 0).
  - exact Hce.
  - lia.
  - exact KCN.
  - exact HK3.
  - rewrite QSP. lia.
  - rewrite QSP. lia.
  - intros a Ha. left. split; [exact Hgo | exact Ha]. }
(* the saved words at the call's return: above the callee's window *)
pose proof HK3 as (K31 & _).
rewrite QSP in K31.
assert (KSTK : forall a, spZ regs - CLOSE_FRAME <= a < spZ regs ->
  aview segs (w_H W3) mem3 a = aview segs (w_H W) mem2 a).
{ intros a Ha. rewrite K31 by lia. apply KR. lia. }
assert (HSo : forall o, In o CLOSE_SAVED -> 8 <= fst o <= 32).
{ intros o Ho. unfold CLOSE_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
assert (HFW3 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem3) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) CLOSE_SAVED).
{ rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
  pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. lia. }
(* the callee-saved registers at the return, as the cut left them *)
assert (P2' : YK11.getr regs3 (Z_to_bv 5 2) = w64 (spZ regs - CLOSE_FRAME))
  by (rewrite (HP3 2 ltac:(hnf; lia)); exact Q2).
assert (P3' : YK11.getr regs3 (Z_to_bv 5 3) = YK11.getr regs 3)
  by exact (eq_trans (HP3 3 ltac:(hnf; lia)) (eq_trans Q3 R3)).
assert (P4' : YK11.getr regs3 (Z_to_bv 5 4) = YK11.getr regs 4)
  by exact (eq_trans (HP3 4 ltac:(hnf; lia)) (eq_trans Q4 R4)).
assert (P8' : YK11.getr regs3 (Z_to_bv 5 8) = w64 CLOSE_S)
  by (rewrite (HP3 8 ltac:(hnf; lia)); exact Q8).
assert (P18' : YK11.getr regs3 (Z_to_bv 5 18) = w64 SHADOW_OFF)
  by exact (eq_trans (HP3 18 ltac:(hnf; lia)) (eq_trans Q18 R18)).
assert (Pq' : forall q, 19 <= q <= 27 -> YK11.getr regs3 (Z_to_bv 5 q) = YK11.getr regs (Z_to_bv 5 q)).
{ intros q Hq. rewrite (HP3 q ltac:(hnf; lia)). rewrite (Qq q Hq). exact (Rq q Hq). }
clear dependent ms.
(* ---- +0xf0 .. +0xf4: s1 = a0, then the join cut ---- *)
pose proof (cs_entry0 W3 regs3 mem3 CLOSE_SRET) as HS3.
assert (HEI3 : img_env VAL A_LIM (cs_E regs3)) by apply cs_env_img.
assert (SHOK3 : sh_ok segs CS_Bx (@nil shent) (cs_E regs3) (mrestrict (w_H W3) mem3)) by constructor.
change (mkSS CLOSE_SRET sr_atoms [] None (mkFacts [] [] [])) with cs_ss2 in HS3.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_SRET)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 YC4b.Bspan CLOSE_JOIN.
{ cs_awr. }
cs_kept HFr KR2 W3 mem3 ms.
assert (GR2 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
rename HS3 into HS.
(* the registers at the join cut *)
cs_reg HS (2%bv : bv 5) (w64 (spZ regs - CLOSE_FRAME)) G2
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 2 (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P2').
cs_reg HS (3%bv : bv 5) (YK11.getr regs 3) G3
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 3 (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P3').
cs_reg HS (4%bv : bv 5) (YK11.getr regs 4) G4
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 4 (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P4').
cs_reg HS (8%bv : bv 5) (w64 CLOSE_S) G8
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 8 (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P8').
cs_reg HS (18%bv : bv 5) (w64 SHADOW_OFF) G18
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 18 (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P18').
cs_reg HS (9%bv : bv 5) (w64 r) G9
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 10 (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact HA0).
assert (Gq : forall q, 19 <= q <= 27 -> YK11.getr (ms_regs ms) (Z_to_bv 5 q) = YK11.getr regs (Z_to_bv 5 q)).
{ intros q Hq. transitivity (YK11.getr regs3 (Z_to_bv 5 q)); [|exact (Pq' q Hq)].
  destruct (cs_q_cases q Hq) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; cs_q1 HS regs3. }
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_JOIN)) mm rom) mdx) Q) end.
apply (JOIN LAWS0 HSS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' B1
  ly3 S3 W3 (ms_mem ms) _ 0 (ms_regs ms) HFIX).
- unfold close_join_cur. split; [|split; [exact HS1 | split]].
  + refine (conj _ (conj _ (conj Hfr3 (conj Hperm3 (conj ELF3c (conj Hmo3 (conj _ _))))))).
    * rewrite Z.add_0_r. exact HJ3.
    * lia.
    * apply (dk_kept_step_gw segs B LAWS transportb_segs_low G_HARNESS_B lyc Sc W memc mdc W3 mem3 (ms_mem ms)
        (spZ regs - CLOSE_STK) (spZ regs) (close_wr TF Bw) (fun _ : Z => False) HARc KC3
        ltac:(intros a Ha _; exact (KR2 a Ha)) GR2); intros; contradiction.
    * rewrite Forall_forall in HFW3 |- *. intros o Ho. rewrite <- (HFW3 o Ho).
      apply rdword_ext. intros i Hi. apply KR2. pose proof (HSo o Ho). lia.
  + apply (tw_kept TMAP_B (aview segs (w_H W3) mem3)); [exact HTW3|].
    intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hh.
    apply KR2. lia.
  + exact HGF3.
- exact (conj (conj G2 (conj G3 (conj G4 (conj G8 (conj G18 Gq))))) G9).
Qed.

End send.
