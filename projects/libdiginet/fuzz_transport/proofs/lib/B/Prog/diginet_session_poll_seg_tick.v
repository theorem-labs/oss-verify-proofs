(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 536 of its 589 lines of code are new or changed and 1871 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/diginet_session_poll_seg_rel.v; 206 of its 311 lines of code are new or changed and 484 lines of the source are left out. *)
(* diginet_session_poll_seg_tick (image B): Theorem pw_tick_piece : pw_tick_stmt
   (lib/B/Prog/diginet_session_poll_segs.v), the tick piece: from the cut tick (+0x288, 0x8ad20): `mv a0, s3`,
   `mv a1, a3`, `jal diginet_session_tick` (+0x290; diginet_session_poll_seg_grx.v pw_tick_call), then from its return
   (+0x294) the checks of s + 80 and s + 64 (the shadow bytes at s11 and s5 are 0: g_s's zero shadow,
   trans_poll_cells), to the cut loop (+0x2a4) with the fuel g_rx_times of tick's world. The code is image A's
   (lib/A/Prog/diginet_session_poll_seg_tick.v) at offsets + 8. Neither run stores a byte, so the facts of the cut are
   carried by diginet_session_poll_seg_kit.v pw_run_win at an unchanged view. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k YE2y AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit TransportGFrameB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require io_now_cg diginet_session_deadline_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TRunInv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_seg_rt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  diginet_session_poll_seg_leaf diginet_session_poll_seg_grecv diginet_session_poll_seg_grx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TPoll TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TPL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TPoll.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module TRI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TRunInv.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.
(* The return address of the call of diginet_session_tick (+0x294). *)
Definition PT_RET : Z := AF_diginet_session_poll + 0x294.
Lemma pt_ret_val : PT_RET = 39564.
Proof. reflexivity. Qed.
(* The state at +0x294: the shadow byte of s + 80 at s11 (atom 27) and that of s + 64 at s5 (atom 21), each 0. *)
Definition PT_R80 : YP09.region := YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SLit 0))].
Definition PT_R64 : YP09.region := YP09.mkRegion (Some 21%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SLit 0))].
Definition ss_pt2 : sstate := mkSS PT_RET sr_atoms [PT_R80; PT_R64] None (mkFacts [] [] []).
Definition PT_Bx : sv := SLit 0.
Definition PT_B0 : Z * Z := (0, 0).

(* The registers the cuts read from tick on, all callee-saved. *)
Definition PT_KREGS : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv.

(* The shadow addresses of s + 64 and s + 80. *)
Lemma pt_sh_vals : PW_SH64 = FCells.shadow_addr (POLL_S + 64) /\ PW_SH80 = FCells.shadow_addr (POLL_S + 80) /\
  PW_SH64 = 2148220624 /\ PW_SH80 = 2148220626.
Proof. repeat split; reflexivity. Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac pt_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* Register r holds the atom of register rs (number n) at the run's start, whose value Q states (EE: the valuation's
   registers). *)
Ltac pt_kreg HS EE r n rs Q H :=
  lazymatch type of Q with _ = ?v =>
    pt_reg HS r v H ltac:(cbn [sv_denot]; rewrite (EE n rs eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The awr obligation's regions, computed. *)
Ltac pt_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* After a run that stores no byte (HFr: its frame), every byte of the view in [0, 2 ^ 64) is the one at m0 (KD) and
   presence grows (GR); msF names the machine state the run ended in. *)
Ltac pt_after_run HS W KD GR m0 msF :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?mf) => rename mf into msF
  end;
  assert (KD : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) m0 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha;
    match goal with HFx : frame_of ?E ?rs (mrestrict (w_H W) m0) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      apply (YC4b.kept_of_frame E rs (w_H W) m0 (ms_mem msF) (fun _ => False) HFx); [ | exact Ha | tauto];
      let b := fresh "b" in let wl := fresh "wl" in let wh := fresh "wh" in let x := fresh "x" in
      let Hin := fresh "Hin" in let Hx := fresh "Hx" in
      intros b wl wh x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]); destruct Hin end
  | ];
  assert (GR : forall a, apresent (w_H W) m0 a -> apresent (w_H W) (ms_mem msF) a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    match goal with HGx : mem_grows (mrestrict (w_H W) m0) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (apresent_grows _ _ _ a HGx Ha) end
  | ].

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* A state with no region at offset pc, the registers as atoms. *)
Lemma pt_entry0 : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof using All.
  intros W regs mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* g_s's shadow bytes are 0 at every AR state (trans_poll_cells), at the granule of s + off. *)
Lemma pt_zsh : forall ly S (W : world segs) mem md off,
  trans_poll_cells B -> @AR rc segs B ly S W mem md -> off mod 8 = 0 -> 0 <= off -> off + 8 <= TW.SZ_g_s ->
  aview segs (w_H W) mem (FCells.shadow_addr (POLL_S + off)) = Some 0.
Proof using All.
  intros ly S W mem md off HPC HAR Hm Hlo Hhi.
  apply (decode_zshadow_rd B ly S W mem md POLL_S (POLL_S + TW.SZ_g_s) (POLL_S + off) HAR); [| lia | lia | exact HPC].
  unfold POLL_S, TB_g_s. rewrite Z.add_mod, Hm by lia. reflexivity.
Qed.

(* The state at +0x294: the two shadow bytes the checks read. *)
Lemma pt_entry2 : forall ly S (W : world segs) regs mem md,
  trans_poll_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 27 = w64 PW_SH80 -> YK11.getr regs 21 = w64 PW_SH64 ->
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) ss_pt2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + PT_RET)) mem (YK11.seg_rom segs))).
Proof using All.
  intros ly S W regs mem md HPC HAR R27 R21.
  destruct pt_sh_vals as (V64 & V80 & N64 & N80).
  rewrite restrict_mkst_fx. unfold ss_pt2.
  set (E := Eimg (PI := PI_transportb) (Ereg regs [])).
  assert (U27 : bv_unsigned (ew E 27) = PW_SH80)
    by (unfold E; rewrite (can_ew_Eimg_Ereg_nat regs [] 27 27%bv eq_refl), R27; unfold w64;
        apply unsigned_lit_small; rewrite N80; lia).
  assert (U21 : bv_unsigned (ew E 21) = PW_SH64)
    by (unfold E; rewrite (can_ew_Eimg_Ereg_nat regs [] 21 21%bv eq_refl), R21; unfold w64;
        apply unsigned_lit_small; rewrite N64; lia).
  assert (Z80 : aview segs (w_H W) mem PW_SH80 = Some 0)
    by (rewrite V80; apply (pt_zsh ly S W mem md 80 HPC HAR); [reflexivity | lia | unfold TW.SZ_g_s; lia]).
  assert (Z64 : aview segs (w_H W) mem PW_SH64 = Some 0)
    by (rewrite V64; apply (pt_zsh ly S W mem md 64 HPC HAR); [reflexivity | lia | unfold TW.SZ_g_s; lia]).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [PT_R80 PT_R64 YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite ?U27, ?U21.
    + split; [rewrite N80; lia|]. split; [rewrite N80; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ PW_SH80 0 1 (SLit 0) 0); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. apply YE2y.val_mem1_of_aview. exact Z80.
    + split; [rewrite N64; lia|]. split; [rewrite N64; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ PW_SH64 0 1 (SLit 0) 0); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. apply YE2y.val_mem1_of_aview. exact Z64.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, PT_R80, PT_R64. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U27, U21. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite N80, N64. repeat split; first [exact I | lia].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* pw_rg_buf at a register file that agrees with one of pw_rg_buf on the callee-saved registers it names. *)
Lemma pt_rg_buf_kept : forall c pos (regsA regsB : bvmap 5 word),
  pw_rg_buf B c pos regsA -> (forall r : bv 5, In r PT_KREGS -> YK11.getr regsB r = YK11.getr regsA r) ->
  pw_rg_buf B c pos regsB.
Proof using All.
  intros c pos regsA regsB (((R2 & R3 & R4 & R8 & R9 & R18) & R19 & R20 & R21 & R22 & R23 & R24 & R27) & R25) HK.
  unfold PT_KREGS in HK. unfold pw_rg_buf, pw_rg_run, pw_rg_base.
  refine (conj (conj (conj _ (conj _ (conj _ (conj _ (conj _ _))))) (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ _))))))) _);
  (rewrite HK; [| cbn [In]; repeat (first [left; reflexivity | right])]).
  - exact R2.
  - exact R3.
  - exact R4.
  - exact R8.
  - exact R9.
  - exact R18.
  - exact R19.
  - exact R20.
  - exact R21.
  - exact R22.
  - exact R23.
  - exact R24.
  - exact R27.
  - exact R25.
Qed.

(* aregs_preserved on the registers pw_rg_buf names. *)
Lemma pt_kregs_preserved : forall (regsA regsB : bvmap 5 word),
  aregs_preserved regsA regsB -> forall r : bv 5, In r PT_KREGS -> YK11.getr regsB r = YK11.getr regsA r.
Proof using All.
  intros regsA regsB HP r Hr. unfold PT_KREGS in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- YK11.getr _ ?rr = _ =>
        let n := eval vm_compute in (bv_unsigned rr) in
        change (YK11.getr regsB (Z_to_bv 5 n) = YK11.getr regsA (Z_to_bv 5 n));
        exact (HP n ltac:(unfold acallee_saved; lia)) end |]).
  destruct Hr.
Qed.

Lemma pw_tick_holds : @pw_tick_stmt fx rc B MT.
Proof using All.
unfold pw_tick_stmt. intros c LOOP. unfold pw_tick_at.
intros HRT HKP HOK pos ly2 S2 W2 mem2 md2 regs2 B2 now2 B3 r3 HRUN HRG R13 Hnow HTM HDR HDRX.
pose proof HRT as (_ & _ & HPC & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & HGX & _).
pose proof HRUN as ((HJ & _) & _).
pose proof HRG as (((R2 & R3 & R4 & R8 & R9 & R18) & R19 & R20 & R21 & R22 & R23 & R24 & R27) & R25).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
(* +0x288 .. +0x290: a0 = s, a1 = now2, `jal diginet_session_tick` *)
pose proof (pt_entry0 W2 regs2 mem2 PW_TICK) as HS.
set (E0 := Eimg (PI := PI_transportb) (Ereg regs2 [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK : sh_ok segs PT_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + PW_TICK)) mem2 (YK11.seg_rom segs)) md2) Q) end.
paj_run_tok RUN HS HJ SHOK PT_B0.
{ pt_awr_rs. apply awr_ok_x_nil. }
pt_after_run HS W2 KD1 GR1 mem2 ms1.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ _ _ _ _) ?mdx) _ => set (md1 := mdx) in * end.
pt_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 39564)) Q1 ltac:(apply codeptr_val; exact HEI).
pt_kreg HS EE (10%bv : bv 5) 19%nat (19%bv : bv 5) R19 Q10.
pt_kreg HS EE (11%bv : bv 5) 13%nat (13%bv : bv 5) R13 Q11.
pt_kreg HS EE (2%bv : bv 5) 2%nat (2%bv : bv 5) R2 Q2. pt_kreg HS EE (3%bv : bv 5) 3%nat (3%bv : bv 5) R3 Q3.
pt_kreg HS EE (4%bv : bv 5) 4%nat (4%bv : bv 5) R4 Q4.
assert (EBR : BASE + 39564 = 0x8ad2c) by (vm_compute; reflexivity).
assert (HK1 : forall r : bv 5, In r PT_KREGS -> YK11.getr (ms_regs ms1) r = YK11.getr regs2 r).
{ intros r Hr. unfold PT_KREGS in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- YK11.getr _ ?rr = _ =>
        let n := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in
        pt_reg HS rr (YK11.getr regs2 rr) Hq
          ltac:(cbn [sv_denot]; rewrite (EE n rr eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
        exact Hq end |]).
  destruct Hr. }
pose proof (pw_run_win B MT c pos ly2 S2 W2 mem2 md2 B2 (ms_mem ms1) md1 HRT HOK HRUN HJ
  ltac:(intros a Ha _; exact (KD1 a Ha)) GR1) as HRUN1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_diginet_session_tick) rg mm mdx) Q) end.
eapply SRr_bind.
{ exact (pw_tick_call B MT c pos ly2 S2 W2 (ms_mem ms1) md1 B2 (ms_regs ms1) now2 B3 r3 HRT HKP HOK HRUN1
    Q2 Q3 Q4 ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, EBR; rewrite unsigned_lit_small by lia; lia)
    Q10 Q11 Hnow HTM). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HP3 & HRUN3).
rewrite Q1.
(* +0x294 .. +0x2a0: the checks of s + 80 and s + 64 *)
pose proof (pt_kregs_preserved _ _ HP3) as HK3.
assert (HK3' : forall r : bv 5, In r PT_KREGS -> YK11.getr regs3 r = YK11.getr regs2 r)
  by (intros r Hr; rewrite (HK3 r Hr); exact (HK1 r Hr)).
pose proof (pt_rg_buf_kept c pos regs2 regs3 HRG HK3') as HRG3.
pose proof HRG3 as (((T2 & T3 & T4 & T8 & T9 & T18) & T19 & T20 & T21 & T22 & T23 & T24 & T27) & T25).
pose proof HRUN3 as ((HJ3 & _) & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
clear HS SHOK HJ.
pose proof (pt_entry2 ly3 S3 W3 regs3 mem3 md3 HPC HAR3 T27 T21) as HS.
set (E3 := Eimg (PI := PI_transportb) (Ereg regs3 [])) in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regs3 r)
  by (intros n r Hn; unfold E3; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK3 : sh_ok segs PT_Bx (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
change (Z_to_bv 64 (BASE + 39564)) with (Z_to_bv 64 (BASE + PT_RET)).
paj_run_to_tok RUNTO HS HJ3 SHOK3 PT_B0 PW_LOOP.
{ pt_awr_rs.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_nil. }
pt_after_run HS W3 KD4 GR4 mem3 ms4.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ _ _ _ _) ?mdx) _ => set (md4 := mdx) in * end.
assert (HK4 : forall r : bv 5, In r PT_KREGS -> YK11.getr (ms_regs ms4) r = YK11.getr regs3 r).
{ intros r Hr. unfold PT_KREGS in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- YK11.getr _ ?rr = _ =>
        let n := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in
        pt_reg HS rr (YK11.getr regs3 rr) Hq
          ltac:(cbn [sv_denot]; rewrite (EE3 n rr eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
        exact Hq end |]).
  destruct Hr. }
pose proof (pw_run_win B MT c pos ly3 S3 W3 mem3 md3 B3 (ms_mem ms4) md4 HRT HOK HRUN3 HJ3
  ltac:(intros a Ha _; exact (KD4 a Ha)) GR4) as HRUN4.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (BASE + PW_LOOP) rg mm mdx) Q) end.
exact (LOOP (Z.to_nat (TW.g_rx_times B3)) HRT HKP HOK pos ly3 S3 W3 (ms_mem ms4) md4 (ms_regs ms4) B3 HRUN4
  (pt_rg_buf_kept c pos regs3 (ms_regs ms4) HRG3 HK4) HDR HDRX).
Qed.

End s.

Theorem pw_tick_piece : forall fx rc B MT, @pw_tick_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@pw_tick_holds fx rc B MT). Qed.
