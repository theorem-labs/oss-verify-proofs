(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 433 of its 480 lines of code are new or changed and 512 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_pre: Lemma lc_pre_ok : lc_pre_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the
   segment PRE of the image-A walk of fuzz_transport.asan's LLVMFuzzerTestOneInput, from the cut INIT (+0x390, the
   return of diginet_session_init) to the loop head HEAD of operation 0 (+0x408) or the epilogue EXIT (+0x150c).

   The model. The cut INIT carries lc_pro_m timg_A Bw0 D = Some (B25, r) with a0 = r. The kit statement
   lc_pro_agree_stmt (K4, an argument of the lemma) gives lc_pro_m timg_A Bw0 D = Some (B25', SPEC_OK) with
   agree timg_A 0 B25', so B25' = B25 and r = SPEC_OK = 0. TSim/InitOk.v prologue_ok's third conjunct gives
   QueueFacts.fuzz_in_ok D (prologue_cursor D); the cut's s9 / s11 are that cursor.

   The code (listing slots 228 .. 258), three position-abstract runs of lib/A/Prog/TransportGRunA.v over the caller's
   G journal:
     +0x390  `beqz a0`: a0 = 0, taken; the fall-through `j` at +0x394 to the abort pair +0x18e0 / +0x18e4 is refuted;
     +0x398  `ld s4, 160(s1)`: g_fail_next's page, from the spill slot the prologue stored;
     +0x39c  `bnez s11`: s11 = 0 (no byte left) runs the `j` at +0x3a0 to the epilogue (EXIT); else
     +0x3a4 .. +0x404  s5 = 0, s6 = 7, a0 = F from 152(s1), and the nine stores of the loop's spill slots
             (lf_spill_loop: 96, 40, 8, 16, 168, 32, 104, 88, 136 from s1), up to the loop head (HEAD).
   The symbolic state holds five write regions on s1 (the bytes [8, 24), [32, 48), [88, 112), [136, 144) and
   [168, 176) above s1, exactly the nine stores) and one read region (the slots 152 and 160). Every other byte keeps
   its value, so the core, the frame shadow, the earlier spill slots and the world relation move to the end memory.
   The segment makes no call and writes no byte of G. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YO09 YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st LLVMFuzzerTestOneInput_sat.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts InitOk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module IOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.InitOk.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0x390                                      *)
(* ------------------------------------------------------------------ *)

(* s1 is atom 9; atom 32 is the shadow base, atom 33 the frame F. The read region holds the two slots the code loads
   (152: F, 160: g_fail_next's page); the five write regions are the bytes the nine stores write. *)
Definition lpe_rd : YP09.region :=
  YP09.mkRegion (Some 9%nat) 152 168 0 0
    [YP09.mkChunk 152 (YP09.CVal 8 (SOff 33 0)); YP09.mkChunk 160 (YP09.CVal 8 (SLit LF_S4))].
Definition lpe_w1 : YP09.region := YP09.mkRegion (Some 9%nat) 8 24 8 24 [].
Definition lpe_w2 : YP09.region := YP09.mkRegion (Some 9%nat) 32 48 32 48 [].
Definition lpe_w3 : YP09.region := YP09.mkRegion (Some 9%nat) 88 112 88 112 [].
Definition lpe_w4 : YP09.region := YP09.mkRegion (Some 9%nat) 136 144 136 144 [].
Definition lpe_w5 : YP09.region := YP09.mkRegion (Some 9%nat) 168 176 168 176 [].
Definition lpe_regions : smem := [lpe_w1; lpe_w2; lpe_w3; lpe_w4; lpe_w5; lpe_rd].
Definition lpe_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition ss_lpe : sstate := mkSS LO_INIT sr_atoms lpe_regions None lpe_facts.
Definition LPE_B0 : Z * Z := (0, 0).

(* The bytes the nine stores write, above s1. *)
Definition lpe_wr (sp1 a : Z) : Prop :=
  sp1 + 8 <= a < sp1 + 24 \/ sp1 + 32 <= a < sp1 + 48 \/ sp1 + 88 <= a < sp1 + 112 \/
  sp1 + 136 <= a < sp1 + 144 \/ sp1 + 168 <= a < sp1 + 176.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac lpe_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac lpe_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
(* The awr obligation's regions, computed. *)
Ltac lpe_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* Every window of the run's regions is a byte of the function's own stack window (or empty). *)
Ltac lpe_awr U :=
  lpe_awr_rs;
  repeat (apply awr_ok_x_cons;
          [let a := fresh "a" in let Ha := fresh "Ha" in
           intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U in Ha;
           first [lia | left; split; [unfold awr_byte; left; lia | lia]] |]);
  apply awr_ok_x_nil.
(* Name the machine state of HS. *)
Ltac lpe_name HS x :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into x
  end.
(* After a run: every byte outside the stores' bytes (lpe_wr sp1) is the one before (KD). U names s1's value. *)
Ltac lpe_kept HFr U sp1 KD :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?Hh ?mp) (mrestrict ?Hh2 ?mn) =>
  assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ lpe_wr sp1 a -> aview tfibsegs Hh mn a = aview tfibsegs Hh mp a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hna := fresh "Hna" in
    intros a Ha Hna; apply (YC4b.kept_of_frame _ _ _ _ _ (lpe_wr sp1) HFr); [| exact Ha | exact Hna];
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in
    let x := fresh "x" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [Hin | Hin];
            [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U in Hx; unfold lpe_wr; lia |]);
    destruct Hin
  | ] end.

Section pre. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Section env. Context {fx : YK11.FPState}.

(* The walk's valuation: the 32 registers, the shadow base (atom 32) and the frame (atom 33). *)
Definition lpe_E (regs : bvmap 5 word) (F : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF; w64 F]).

Lemma lpe_ew_reg : forall regs F n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (lpe_E regs F) n = YK11.getr regs r.
Proof. intros regs F n r Hn. unfold lpe_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma lpe_ew_32 : forall regs F, ew (lpe_E regs F) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs F. unfold lpe_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma lpe_ew_33 : forall regs F, ew (lpe_E regs F) 33 = Z_to_bv 64 F.
Proof. intros regs F. unfold lpe_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). Qed.
Lemma lpe_env_img : forall regs F, img_env VAL A_LIM (lpe_E regs F).
Proof. intros regs F. unfold lpe_E. apply Eimg_env. Qed.

(* The entry state at +0x390. *)
Lemma lpe_entry : forall (W : world segs) regs mem (F sp1 : Z),
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 - 192 -> sp1 mod 32 = 0 ->
  4096 <= F <= 2 ^ 47 -> F mod 64 = 0 ->
  (forall a, sp1 + 8 <= a < sp1 + 176 -> apresent (w_H W) mem a) ->
  rdword (aview segs (w_H W) mem) (sp1 + 152) = Some F ->
  rdword (aview segs (w_H W) mem) (sp1 + 160) = Some LF_S4 ->
  st_ok_pi segs VAL (lpe_E regs F) ss_lpe
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LO_INIT)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F sp1 R9 Hsp Hal HF HF64 Hpres H152 H160.
rewrite restrict_mkst_fx. unfold ss_lpe, lpe_regions.
assert (U9 : bv_unsigned (ew (lpe_E regs F) 9) = sp1)
  by (rewrite (lpe_ew_reg regs F 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew (lpe_E regs F) 32) = SHADOW_OFF)
  by (rewrite lpe_ew_32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew (lpe_E regs F) 33) = F) by (rewrite lpe_ew_33; apply unsigned_lit_small; lia).
assert (HS4 : 0 <= LF_S4 < 2 ^ 64) by (unfold LF_S4; rewrite (proj1 (proj2 (proj2 lf_spill_pages))); lia).
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [lpe_w1 lpe_w2 lpe_w3 lpe_w4 lpe_w5 lpe_rd
       YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  rewrite U9.
  1-5: split; [lia|]; split; [lia|]; split; [|constructor];
       intros o Ho; apply (apresent_writable segs); apply Hpres; lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  + apply (chunk_ok_val segs _ _ sp1 152 8 (SOff 33 0) F);
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword segs (w_H W) mem _ _ H152).
  + apply (chunk_ok_val segs _ _ sp1 160 8 (SLit LF_S4) LF_S4); [reflexivity | cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword segs (w_H W) mem _ _ H160).
- apply pairwise_disjoint_of_extents.
  unfold lpe_w1, lpe_w2, lpe_w3, lpe_w4, lpe_w5, lpe_rd, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold lpe_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U33.
  change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

End env.

(* Every conjunct of the core but its journal moves to a memory that differs from the cut's only in the bytes
   [sp1, sp1 + 192), with the five registers the core fixes unchanged. The journal at that memory is the run's own,
   so this lemma does not restate it. *)
Lemma lpe_core_own : forall cx ly' S' (W' : world segs) regs' mem' md' e regs2 mem2,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  YK11.getr regs2 2 = YK11.getr regs' 2 -> YK11.getr regs2 8 = YK11.getr regs' 8 ->
  YK11.getr regs2 9 = YK11.getr regs' 9 -> YK11.getr regs2 3 = YK11.getr regs' 3 ->
  YK11.getr regs2 4 = YK11.getr regs' 4 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lc_sp1 cx <= a < lc_sp1 cx + 192) ->
     aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a) ->
  (forall a, apresent (w_H W') mem' a -> apresent (w_H W') mem2 a) ->
  frames S' = [(LF_CID, l_fpos cx)] /\ ly_F ly' = ly_F (l_ly cx) /\
  Permutation (ablocks B ly' S') (ablocks B (l_ly cx) (l_S cx)) /\
  YK11.getr regs2 2 = w64 (lc_sp1 cx) /\ YK11.getr regs2 8 = w64 (lc_sp0 cx) /\ YK11.getr regs2 9 = w64 (lc_sp1 cx) /\
  YK11.getr regs2 3 = w64 (as_gp B) /\ YK11.getr regs2 4 = w64 (as_tp B) /\
  lc_sp0 cx - 336 <= lc_sp1 cx <= lc_sp0 cx - LF_FRAME /\ lc_sp1 cx mod 32 = 0 /\
  lc_saved cx (aview segs (w_H W') mem2) /\
  4096 <= lc_F cx /\ lc_F cx mod 64 = 0 /\ lc_F cx + LF_FBYTES <= alloc_ceiling /\
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> apresent (w_H W') mem2 a) /\
  rdword (aview segs (w_H W') mem2) (lc_F cx + LF_FBYTES - 8) = Some (lc_FL cx) /\
  lc_input cx W' mem2.
Proof.
intros cx ly' S' W' regs' mem' md' e regs2 mem2 LAWS HB HC E2 E8 E9 E3 E4 KA GR.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
destruct HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
pose proof asan_consts as ((CVlo & CVhi) & _).
change (2 ^ 47) with 140737488355328 in H47.
unfold LF_FRAME in *. unfold LF_FBYTES in *.
split; [exact Hfrs|]. split; [exact HlyF|]. split; [exact HPERM|].
split; [rewrite E2; exact Rsp|]. split; [rewrite E8; exact R8|]. split; [rewrite E9; exact R9|].
split; [rewrite E3; exact Rgp|]. split; [rewrite E4; exact Rtp|].
split; [exact Hsp1|]. split; [exact Hsp1al|].
split.
{ unfold lc_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros o Ho.
  assert (Hor : 8 <= fst o <= 104).
  { unfold LF_SAVED in Ho. repeat (destruct Ho as [<- | Ho]; [cbn; lia|]). destruct Ho. }
  rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W') mem2) (lc_sp0 cx - fst o))
    by (intros j Hj; apply KA; [change (2 ^ 64) with 18446744073709551616; lia | lia]).
  exact (HSAV o Ho). }
split; [exact HF4096|]. split; [exact HFal|]. split; [exact HFceil|].
split; [intros a Ha; exact (GR a (HFpres a Ha))|].
split.
{ rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W') mem2) (lc_F cx + 256 - 8))
    by (intros j Hj; apply KA; [change (2 ^ 64) with 18446744073709551616; lia | lia]).
  exact HFL. }
destruct HIN as (HPAYg & HPAYv).
destruct (Z_lt_le_dec 0 (l_n cx)) as [Hn0 | Hn0].
- pose proof (HINg Hn0) as InP.
  pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' (l_p cx) (l_n cx) HARg InP) as (_ & H4096 & Hbc & _).
  assert (KB : forall i, 0 <= i < l_n cx -> aview segs (w_H W') mem2 (l_p cx + i) = aview segs (w_H W') mem' (l_p cx + i))
    by (intros i Hi; apply KA; [change (2 ^ 64) with 18446744073709551616; lia | lia]).
  split.
  + apply (lc_garr8_kept (w_H W') (w_H W') mem' mem2 (l_p cx) _); [|exact HPAYg].
    intros j Hj. rewrite length_map in Hj. destruct Hn as (_ & Hnl). rewrite <- Hnl in Hj.
    exact (KB j Hj).
  + intros i Hi. rewrite (KB i Hi). exact (HPAYv i Hi).
- destruct Hn as (Hn1 & Hnl). split.
  + destruct (l_pl cx) as [|b0 pl0] eqn:Epl; [apply garr8_nil|]. exfalso. cbn [length] in Hnl. lia.
  + intros i Hi. lia.
Qed.

(* A list of spill slots moves to a memory whose bytes at those slots are unchanged. *)
Lemma lpe_spills_kept : forall cx (l : list (Z * Z)) (r r' : reader),
  (forall o j, In o l -> 0 <= j < 8 -> r' (lc_sp1 cx + fst o + j) = r (lc_sp1 cx + fst o + j)) ->
  lc_spills cx l r -> lc_spills cx l r'.
Proof.
intros cx l r r' Hk H. unfold lc_spills in *. rewrite Forall_forall in H |- *. intros o Ho.
rewrite (rdword_ext r r' (lc_sp1 cx + fst o)) by (intros j Hj; apply (Hk o j Ho Hj)).
exact (H o Ho).
Qed.

Lemma lc_pre_ok (lc_pro_agree_ok : lc_pro_agree_stmt) : lc_pre_stmt B MT XL RLO RHI.
Proof.
unfold lc_pre_stmt. intros HP cx W' c' HB HI.
destruct cx as [fx ly0 S0 W0 regs0 mem0 md0 p n pl M fpos].
set (cx := mkLCx fx ly0 S0 W0 regs0 mem0 md0 p n pl M fpos) in *.
destruct HI as (ly' & S' & regs' & mem' & md' & Bw0 & B25 & r & Hc & HC & HFR & HSP & HFSH & HMT & HCUR & R10 & HW0 &
  HPRO & HTW).
subst c'.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' 0 HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
destruct HFR as (R18 & R26).
destruct HCUR as (R25 & R27).
destruct HW0 as (HTW0 & HLEN).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
pose proof asan_consts as ((CVlo & CVhi) & _).
change (2 ^ 47) with 140737488355328 in H47.
unfold LF_FRAME in Hsp1. unfold LF_FBYTES in *.
assert (HSTK : LLVMF_STK = 32768) by reflexivity.
(* the model: r = SPEC_OK, the head's simulation facts *)
assert (HnD : Z.of_nat (length (l_pl cx)) < TOP.FUZZ_INPUT_MAX)
  by (destruct Hn as (Hn1 & Hn2); rewrite <- Hn2; unfold TOP.FUZZ_INPUT_MAX; lia).
destruct (lc_pro_agree_ok Bw0 (l_pl cx) HLEN HnD) as (B25' & HPRO' & HAG).
rewrite HPRO in HPRO'. injection HPRO' as EB Er. subst B25' r.
destruct (IOK.prologue_ok timg_A Bw0 (fun _ => 0) (l_pl cx) lc_timg_A_ok HLEN HnD) as (B0x & _ & _ & HFI).
set (c0 := IOK.prologue_cursor (l_pl cx)) in *.
(* the start state *)
assert (Hsp1r : 2 ^ 46 <= lc_sp1 cx <= 2 ^ 47 - 192) by lia.
assert (Hpres : forall a, lc_sp1 cx + 8 <= a < lc_sp1 cx + 176 -> apresent (w_H W') mem' a).
{ intros a Ha. pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). apply Hp. lia. }
assert (H152 : rdword (aview segs (w_H W') mem') (lc_sp1 cx + 152) = Some (lc_F cx)).
{ unfold lc_spills in HSP. rewrite Forall_forall in HSP. exact (HSP (152, lc_F cx) ltac:(cbn; tauto)). }
assert (H160 : rdword (aview segs (w_H W') mem') (lc_sp1 cx + 160) = Some LF_S4).
{ unfold lc_spills in HSP. rewrite Forall_forall in HSP. exact (HSP (160, transport_hi 10) ltac:(cbn; tauto)). }
pose proof (lpe_entry W' regs' mem' (lc_F cx) (lc_sp1 cx) R9 Hsp1r Hsp1al ltac:(lia) HFal Hpres H152 H160) as HS.
assert (HEI : img_env VAL A_LIM (lpe_E regs' (lc_F cx))) by apply lpe_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (lpe_E regs' (lc_F cx)) (mrestrict (w_H W') mem')) by constructor.
assert (U9 : bv_unsigned (ew (lpe_E regs' (lc_F cx)) 9) = lc_sp1 cx)
  by (rewrite (lpe_ew_reg regs' (lc_F cx) 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + LO_INIT)) mem' (YK11.seg_rom segs)) md') Q) end.
(* +0x390 `beqz a0`: a0 = SPEC_OK = 0, so the fall-through to the abort pair is refuted *)
psrr_branch_tok RUN BR HS SHOK LPE_B0.
2:{ exfalso. cbn [sv_denot] in Hc. rewrite (lpe_ew_reg regs' (lc_F cx) 10 10%bv eq_refl), R10 in Hc.
    vm_compute in Hc. discriminate Hc. }
clear Hc.
(* +0x390 .. +0x39c: the branch taken, `ld s4, 160(s1)`, up to `bnez s11` *)
paj_run_tok RUN HS HJ SHOK LPE_B0.
{ lpe_awr U9. }
lpe_name HS ms1.
lpe_kept HFr U9 (lc_sp1 cx) KD1.
pose proof (fun a Ha => apresent_grows _ _ _ a HG Ha) as GR1.
clear HF HFr HG.
(* the registers the cuts fix, at the run's end: s0, s1, sp, gp, tp, s2, s10, s9 and s11 are the cut's *)
assert (E27 : ew (lpe_E regs' (lc_F cx)) 27 = w64 (TOP.fi_n c0))
  by (rewrite (lpe_ew_reg regs' (lc_F cx) 27 27%bv eq_refl); exact R27).
assert (HRG : 0 <= lc_sp1 cx /\ lc_sp1 cx + 192 <= 2 ^ 64) by lia.
(* The kept bytes: those of the core, the frame shadow and G lie outside the stores. *)
assert (OUT192 : forall a, ~ (lc_sp1 cx <= a < lc_sp1 cx + 192) -> ~ lpe_wr (lc_sp1 cx) a)
  by (intros a Ha Hw; unfold lpe_wr in Hw; lia).
assert (OUTSH : forall a, lc_SH cx <= a < lc_SH cx + 32 -> ~ lpe_wr (lc_sp1 cx) a)
  by (intros a Ha Hw; unfold lpe_wr in Hw; unfold lc_SH, SHADOW_OFF in Ha; lia).
assert (OUTSHr : forall a, lc_SH cx <= a < lc_SH cx + 32 -> 0 <= a < 2 ^ 64)
  by (intros a Ha; unfold lc_SH, SHADOW_OFF in Ha; pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia)); lia).
assert (OUTG : forall b n0 i, In (b, n0) TG.G_HARNESS -> 0 <= i < n0 -> 0 <= b + i < 2 ^ 64 /\ ~ lpe_wr (lc_sp1 cx) (b + i)).
{ intros b n0 i Hin Hi.
  assert (Hg : inG TG.G_HARNESS (b + i))
    by (unfold inG; apply Exists_exists; exists (b, n0); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low segs B transport_segs_low TG.G_HARNESS _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  split; [lia|]. intros Hw. unfold lpe_wr in Hw. lia. }
assert (HSPI : forall mm : word -> option byte,
  (forall a, 0 <= a < 2 ^ 64 -> ~ lpe_wr (lc_sp1 cx) a -> aview segs (w_H W') mm a = aview segs (w_H W') mem' a) ->
  lc_spills cx (lf_spill_init (lc_F cx)) (aview segs (w_H W') mm)).
{ intros mm KD. apply (lpe_spills_kept cx _ (aview segs (w_H W') mem')); [|exact HSP].
  intros o j Ho Hj. unfold lf_spill_init, lf_spill_scal, lf_spill_sm in Ho. cbn [app In] in Ho.
  repeat (destruct Ho as [<- | Ho];
          [apply KD; [cbn [fst]; lia | unfold lpe_wr; cbn [fst]; lia] |]).
  destruct Ho. }
(* +0x39c `bnez s11` *)
psrr_branch_tok RUN BR HS SHOK LPE_B0.
- (* s11 <> 0: +0x3a4 .. +0x404, the loop's constants and spill slots, to the head of operation 0 *)
  assert (Hfi : TOP.fi_n c0 <> 0).
  { intros E0. cbn [sv_denot] in Hc. rewrite E27, E0 in Hc. vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK LPE_B0 LO_HEAD.
  { lpe_awr U9. }
  lpe_name HS msH.
  lpe_kept HFr U9 (lc_sp1 cx) KD2.
  pose proof (fun a Ha => apresent_grows _ _ _ a HG Ha) as GR2.
  clear HF HFr HG.
  assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ lpe_wr (lc_sp1 cx) a ->
    aview segs (w_H W') (ms_mem msH) a = aview segs (w_H W') mem' a)
    by (intros a Ha Hw; exact (eq_trans (KD2 a Ha Hw) (KD1 a Ha Hw))).
  assert (GR : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem msH) a)
    by (intros a Ha; exact (GR2 a (GR1 a Ha))).
  lpe_reg HS (2%bv : bv 5) (YK11.getr regs' 2) Y2 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 2 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  lpe_reg HS (8%bv : bv 5) (YK11.getr regs' 8) Y8 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 8 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  lpe_reg HS (9%bv : bv 5) (YK11.getr regs' 9) Y9 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 9 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  lpe_reg HS (3%bv : bv 5) (YK11.getr regs' 3) Y3 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  lpe_reg HS (4%bv : bv 5) (YK11.getr regs' 4) Y4 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  lpe_reg HS (18%bv : bv 5) (w64 (lc_SH cx)) Y18 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 18 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R18).
  lpe_reg HS (26%bv : bv 5) (w64 SHADOW_OFF) Y26 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 26 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R26).
  lpe_reg HS (25%bv : bv 5) (w64 (l_p cx + TOP.fi_off c0)) Y25 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 25 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R25).
  lpe_reg HS (27%bv : bv 5) (w64 (TOP.fi_n c0)) Y27 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 27 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R27).
  lpe_reg HS (20%bv : bv 5) (w64 LF_S4) Y20 ltac:(reflexivity).
  lpe_reg HS (21%bv : bv 5) (w64 0) Y21 ltac:(reflexivity).
  lpe_reg HS (22%bv : bv 5) (w64 7) Y22 ltac:(reflexivity).
  (* the nine slots the run stored, read back from the write regions *)
  assert (U33 : bv_unsigned (ew (lpe_E regs' (lc_F cx)) 33) = lc_F cx)
    by (rewrite lpe_ew_33; apply unsigned_lit_small; lia).
  lpe_region HS 0%nat HR0. lpe_region HS 1%nat HR1. lpe_region HS 2%nat HR2.
  lpe_region HS 3%nat HR3. lpe_region HS 4%nat HR4.
  assert (SLOT : forall lo hi cs od e v,
    region_ok segs (lpe_E regs' (lc_F cx)) (mrestrict (w_H W') (ms_mem msH)) (YP09.mkRegion (Some 9%nat) lo hi lo hi cs) ->
    In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot (lpe_E regs' (lc_F cx)) e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
    rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + od) = Some v).
  { intros lo hi cs od e0 v HR Hin He Hv.
    apply (AF0x.val_mem_rdword (w_H W') (ms_mem msH) _ _ Hv).
    exact (can_field_of_region (lpe_E regs' (lc_F cx)) _ 9 (lc_sp1 cx) cs lo hi lo hi od 8%N e0 v HR U9 Hin He
      ltac:(cbn; lia) ltac:(lia)). }
  assert (HFv : 0 <= lc_F cx /\ lc_F cx + 256 <= 2 ^ 63) by lia.
  assert (V8 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 8) = Some (lc_F cx + 86))
    by (apply (SLOT _ _ _ _ (SOff 33 86) _ HR0); [cbn [In]; repeat (first [left; reflexivity | right]) |
        cbn [sv_denot]; rewrite U33; reflexivity | lia]).
  assert (V16 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 16) = Some (lc_F cx + 33))
    by (apply (SLOT _ _ _ _ (SOff 33 33) _ HR0); [cbn [In]; repeat (first [left; reflexivity | right]) |
        cbn [sv_denot]; rewrite U33; reflexivity | lia]).
  assert (V32 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 32) = Some (lc_F cx + 35))
    by (apply (SLOT _ _ _ _ (SOff 33 35) _ HR1); [cbn [In]; repeat (first [left; reflexivity | right]) |
        cbn [sv_denot]; rewrite U33; reflexivity | lia]).
  assert (V40 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 40) = Some (2 ^ 32 - 3))
    by (apply (SLOT _ _ _ _ (SLit 4294967293) _ HR1); [cbn [In]; repeat (first [left; reflexivity | right]) |
        reflexivity | lia]).
  assert (V88 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 88) = Some (lc_F cx + 120))
    by (apply (SLOT _ _ _ _ (SOff 33 120) _ HR2); [cbn [In]; repeat (first [left; reflexivity | right]) |
        cbn [sv_denot]; rewrite U33; reflexivity | lia]).
  assert (V96 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 96) = Some 0x610f)
    by (apply (SLOT _ _ _ _ (SLit 24847) _ HR2); [cbn [In]; repeat (first [left; reflexivity | right]) |
        reflexivity | lia]).
  assert (V104 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 104) = Some (lc_F cx + 96))
    by (apply (SLOT _ _ _ _ (SOff 33 96) _ HR2); [cbn [In]; repeat (first [left; reflexivity | right]) |
        cbn [sv_denot]; rewrite U33; reflexivity | lia]).
  assert (V136 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 136) = Some 0xffff)
    by (apply (SLOT _ _ _ _ (SLit 65535) _ HR3); [cbn [In]; repeat (first [left; reflexivity | right]) |
        reflexivity | lia]).
  assert (V168 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 168) = Some (lc_F cx + 32))
    by (apply (SLOT _ _ _ _ (SOff 33 32) _ HR4); [cbn [In]; repeat (first [left; reflexivity | right]) |
        cbn [sv_denot]; rewrite U33; reflexivity | lia]).
  clear SLOT HR0 HR1 HR2 HR3 HR4.
  pmkst HS.
  apply SRr_ret. left. exists (mkLop 0 B25 c0 O). split; [reflexivity|].
  exists ly', S', (ms_regs msH), (ms_mem msH). eexists. exists 0.
  split; [unfold lc_cfg; reflexivity|].
  split.
  { split.
    { exact (conj HJ (lpe_core_own cx ly' S' W' regs' mem' md' 0 (ms_regs msH) (ms_mem msH) LAWS HB HC Y2 Y8 Y9 Y3 Y4
        (fun a Ha Hn => KD a Ha (OUT192 a Hn)) GR)). }
    split; [exact (conj Y18 Y26)|].
    split.
    { unfold lf_spill_loop, lc_spills. apply Forall_app. split; [exact (HSPI _ KD)|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - exact V96.
      - exact V40.
      - exact V8.
      - exact V16.
      - exact V168.
      - exact V32.
      - exact V104.
      - exact V88.
      - exact V136. }
    split.
    { apply (lc_fsh_kept cx (aview segs (w_H W') mem')); [|exact HFSH].
      intros a Ha. exact (KD a (OUTSHr a Ha) (OUTSH a Ha)). }
    split.
    { unfold lc_opok. cbn [lo_ops lo_B lo_c lo_k].
      split; [exact HAG|]. split; [unfold TC.OPS_MAX; lia|]. split; [exact HFI|]. split; [exact Hfi | lia]. }
    split; [cbn [lo_k Z.of_nat]; lia|].
    split; [exact HMT|].
    exact Y21. }
  split.
  { unfold lc_tw. apply (tw_kept_GA (aview segs (w_H W') mem')); [exact HTW|].
    intros b n0 i Hin Hi. destruct (OUTG b n0 i Hin Hi) as (Hr & Hw). exact (KD _ Hr Hw). }
  split; [exact (conj Y25 Y27)|].
  split; [exact Y20 | exact Y22].
- (* s11 = 0: the `j` at +0x3a0 to the epilogue *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK LPE_B0 LO_EXIT.
  { lpe_awr U9. }
  lpe_name HS msX.
  lpe_kept HFr U9 (lc_sp1 cx) KD2.
  pose proof (fun a Ha => apresent_grows _ _ _ a HG Ha) as GR2.
  clear HF HFr HG.
  assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ lpe_wr (lc_sp1 cx) a ->
    aview segs (w_H W') (ms_mem msX) a = aview segs (w_H W') mem' a)
    by (intros a Ha Hw; exact (eq_trans (KD2 a Ha Hw) (KD1 a Ha Hw))).
  assert (GR : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem msX) a)
    by (intros a Ha; exact (GR2 a (GR1 a Ha))).
  lpe_reg HS (2%bv : bv 5) (YK11.getr regs' 2) Y2 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 2 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  lpe_reg HS (8%bv : bv 5) (YK11.getr regs' 8) Y8 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 8 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  lpe_reg HS (9%bv : bv 5) (YK11.getr regs' 9) Y9 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 9 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  lpe_reg HS (3%bv : bv 5) (YK11.getr regs' 3) Y3 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  lpe_reg HS (4%bv : bv 5) (YK11.getr regs' 4) Y4 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  lpe_reg HS (18%bv : bv 5) (w64 (lc_SH cx)) Y18 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 18 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R18).
  lpe_reg HS (26%bv : bv 5) (w64 SHADOW_OFF) Y26 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 26 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R26).
  pmkst HS.
  apply SRr_ret. right.
  exists ly', S', (ms_regs msX), (ms_mem msX). eexists. exists 0, 0.
  split; [unfold lc_cfg; reflexivity|].
  split.
  { exact (conj HJ (lpe_core_own cx ly' S' W' regs' mem' md' 0 (ms_regs msX) (ms_mem msX) LAWS HB HC Y2 Y8 Y9 Y3 Y4
      (fun a Ha Hn => KD a Ha (OUT192 a Hn)) GR)). }
  split; [exact (conj Y18 Y26)|].
  split.
  { pose proof (HSPI _ KD) as HSPX. unfold lc_spills, lf_spill_init, lf_spill_scal in HSPX |- *.
    apply Forall_app in HSPX as [HSPX _]. apply Forall_app in HSPX as [HSPX _]. exact HSPX. }
  split.
  { apply (lc_fsh_kept cx (aview segs (w_H W') mem')); [|exact HFSH].
    intros a Ha. exact (KD a (OUTSHr a Ha) (OUTSH a Ha)). }
  split; [unfold TC.OPS_MAX; lia|].
  split; [lia|].
  exact HMT.
Qed.

End pre.
