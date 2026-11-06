(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 398 of its 445 lines of code are new or changed and 512 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_pre: Lemma lc_pre_ok : lc_pre_stmt (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), the
   segment PRE of the image-B walk of fuzz_transport.asan-ubsan's LLVMFuzzerTestOneInput, from the cut INIT (+0x528, the
   return of diginet_session_init) to the loop head HEAD of operation 0 (+0x58c) or the epilogue EXIT (+0x188).

   The model. The cut INIT carries lc_pro_m timg_B Bw0 D = Some (B25, r) with a0 = r. The kit statement
   lc_pro_agree_stmt (K4, an argument of the lemma) gives lc_pro_m timg_B Bw0 D = Some (B25', SPEC_OK) with
   agree timg_B 0 B25', so B25' = B25 and r = SPEC_OK = 0. TSim/InitOk.v prologue_ok's third conjunct gives
   QueueFacts.fuzz_in_ok D (prologue_cursor D); the cut's s9 / s7 are that cursor.

   The code (listing slots 330 .. 354), three position-abstract runs of lib/B/Prog/TransportGRunB.v over the caller's
   G journal:
     +0x528  `beqz a0`: a0 = 0, taken; the fall-through `j` at +0x52c to the abort pair +0x1b48 / +0x1b4c is refuted;
     +0x530 .. +0x584  s3 = 0, a0 = F from 136(s1), s4 = c = F + 32, a1 = body = F + 96, s6 = 1, and the nine stores
             of the loop's spill slots (lf_spill_loop: 88, 120, 48, 160, 72, 96, 80, 176, 144 from s1); the word at
             88(s1) is s11 + 0x10f, and s11 = 0x6000 at the cut, so the symbolic state starts with s11 pinned to it;
     +0x588  `beqz s7`: s7 = 0 (no byte left) is taken to the epilogue (EXIT); else the loop head (HEAD) follows.
   The symbolic state holds six write regions on s1 (the bytes [48, 56), [72, 104), [120, 128), [144, 152),
   [160, 168) and [176, 184) above s1, exactly the nine stores) and one read region (the slot 136). Every other byte
   keeps its value, so the core (LLVMFuzzerTestOneInput_st.v lc_core_kept_run), the frame shadow, the earlier spill
   slots and the world relation move to the end memory. The segment makes no call and writes no byte of G. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st LLVMFuzzerTestOneInput_sat.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts InitOk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
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
(* 1. The symbolic state at +0x528                                      *)
(* ------------------------------------------------------------------ *)

(* s1 is atom 9; atom 32 is the shadow base, atom 33 the frame F. The read region holds the slot the code loads
   (136: F); the six write regions are the bytes the nine stores write. *)
Definition lpe_rd : YP09.region :=
  YP09.mkRegion (Some 9%nat) 136 144 0 0 [YP09.mkChunk 136 (YP09.CVal 8 (SOff 33 0))].
Definition lpe_w1 : YP09.region := YP09.mkRegion (Some 9%nat) 48 56 48 56 [].
Definition lpe_w2 : YP09.region := YP09.mkRegion (Some 9%nat) 72 104 72 104 [].
Definition lpe_w3 : YP09.region := YP09.mkRegion (Some 9%nat) 120 128 120 128 [].
Definition lpe_w4 : YP09.region := YP09.mkRegion (Some 9%nat) 144 152 144 152 [].
Definition lpe_w5 : YP09.region := YP09.mkRegion (Some 9%nat) 160 168 160 168 [].
Definition lpe_w6 : YP09.region := YP09.mkRegion (Some 9%nat) 176 184 176 184 [].
Definition lpe_regions : smem := [lpe_w1; lpe_w2; lpe_w3; lpe_w4; lpe_w5; lpe_w6; lpe_rd].
Definition lpe_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition ss_lpe : sstate := mkSS LO_INIT sr_atoms lpe_regions None lpe_facts.
Definition LPE_B0 : Z * Z := (0, 0).

(* The bytes the nine stores write, above s1. *)
Definition lpe_wr (sp1 a : Z) : Prop :=
  sp1 + 48 <= a < sp1 + 56 \/ sp1 + 72 <= a < sp1 + 104 \/ sp1 + 120 <= a < sp1 + 128 \/
  sp1 + 144 <= a < sp1 + 152 \/ sp1 + 160 <= a < sp1 + 168 \/ sp1 + 176 <= a < sp1 + 184.

(* The symbolic complement (`not`: xori with -1) of an atom's offset, at its value. *)
Lemma lpe_not_val : forall E n x z v,
  bv_unsigned (ew E n) + x = v -> 0 <= v < 2 ^ 64 -> YP0m.zcanon z = 2 ^ 64 - 1 ->
  sv_denot E (SAlu ALU_XOR (SOff n x) (SLit z)) = Z_to_bv 64 (2 ^ 64 - 1 - v).
Proof.
intros E n x z v Hv Hr Hz. cbn [sv_denot]. rewrite YP0m.zalu64_sound. unfold YP0m.zalu64. cbn [YP0m.zalu_raw].
rewrite Hz, Hv, (YP0m.zcanon_small v Hr), (YI08.lxor_allones v Hr). f_equal. apply YP0m.zcanon_small. lia.
Qed.

(* The two parts of a model result. *)
Lemma lpe_some_inv : forall (X Y : Type) (a a' : X) (x x' : Y), Some (a, x) = Some (a', x') -> a = a' /\ x = x'.
Proof. intros X Y a a' x x' H. injection H as -> ->. split; reflexivity. Qed.

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
(* A chunk of a region's list, found by its offset. *)
Ltac lpe_in := cbn [In]; repeat (first [left; reflexivity | right]).

Section pre. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Section env. Context {fx : YK11.FPState}.

(* The walk's valuation: the 32 registers, the shadow base (atom 32) and the frame (atom 33). *)
Definition lpe_E (regs : bvmap 5 word) (F : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF; w64 F]).

Lemma lpe_ew_reg : forall regs F n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (lpe_E regs F) n = YK11.getr regs r.
Proof. intros regs F n r Hn. unfold lpe_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma lpe_ew_32 : forall regs F, ew (lpe_E regs F) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs F. unfold lpe_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma lpe_ew_33 : forall regs F, ew (lpe_E regs F) 33 = Z_to_bv 64 F.
Proof. intros regs F. unfold lpe_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). Qed.
Lemma lpe_env_img : forall regs F, img_env VAL A_LIM (lpe_E regs F).
Proof. intros regs F. unfold lpe_E. apply Eimg_env. Qed.

(* The entry state at +0x528. *)
Lemma lpe_entry : forall (W : world segs) regs mem (F sp1 : Z),
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 - 192 -> sp1 mod 32 = 0 ->
  4096 <= F <= 2 ^ 47 -> F mod 64 = 0 ->
  (forall a, sp1 + 48 <= a < sp1 + 184 -> apresent (w_H W) mem a) ->
  rdword (aview segs (w_H W) mem) (sp1 + 136) = Some F ->
  st_ok_pi segs VAL (lpe_E regs F) ss_lpe
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LO_INIT)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F sp1 R9 Hsp Hal HF HF64 Hpres H136.
rewrite restrict_mkst_fx. unfold ss_lpe, lpe_regions.
assert (U9 : bv_unsigned (ew (lpe_E regs F) 9) = sp1)
  by (rewrite (lpe_ew_reg regs F 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew (lpe_E regs F) 32) = SHADOW_OFF)
  by (rewrite lpe_ew_32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew (lpe_E regs F) 33) = F) by (rewrite lpe_ew_33; apply unsigned_lit_small; lia).
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [lpe_w1 lpe_w2 lpe_w3 lpe_w4 lpe_w5 lpe_w6 lpe_rd
       YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  rewrite U9.
  1-6: split; [lia|]; split; [lia|]; split; [|constructor];
       intros o Ho; apply (apresent_writable segs); apply Hpres; lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val segs _ _ sp1 136 8 (SOff 33 0) F);
    [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
  exact (val_mem_of_rdword segs (w_H W) mem _ _ H136).
- apply pairwise_disjoint_of_extents.
  unfold lpe_w1, lpe_w2, lpe_w3, lpe_w4, lpe_w5, lpe_w6, lpe_rd, extent_of_region.
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

(* The core moves to a memory that differs from the cut's only in the stores' bytes (lpe_wr), with the five registers
   it fixes unchanged and the run's journal: LLVMFuzzerTestOneInput_st.v lc_core_kept_run. *)
Lemma lpe_core : forall cx ly' S' (W' : world segs) regs' mem' md' regs2 mem2 md2,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W' regs' mem' md' 0 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W' mem2 md2 0 ->
  YK11.getr regs2 2 = YK11.getr regs' 2 -> YK11.getr regs2 3 = YK11.getr regs' 3 ->
  YK11.getr regs2 4 = YK11.getr regs' 4 -> YK11.getr regs2 8 = YK11.getr regs' 8 ->
  YK11.getr regs2 9 = YK11.getr regs' 9 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ lpe_wr (lc_sp1 cx) a -> aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a) ->
  (forall a, apresent (w_H W') mem' a -> apresent (w_H W') mem2 a) ->
  @lc_core rc B cx ly' S' W' regs2 mem2 md2 0.
Proof.
intros cx ly' S' W' regs' mem' md' regs2 mem2 md2 LAWS HB HC HJ2 E2 E3 E4 E8 E9 KA GR.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' 0 HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _ & _ & HF4096 & _ & HFceil & _).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
pose proof asan_consts as ((CVlo & CVhi) & _).
change (2 ^ 47) with 140737488355328 in H47.
unfold LF_FRAME in Hsp1. unfold LF_FBYTES in HFceil.
apply (lc_core_kept_run B MT XL RLO RHI cx ly' S' W' regs' mem' md' 0 ly' S' W' regs2 mem2 md2 0 HB HC HJ2 eq_refl
  (Permutation_refl _)).
- intros r Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; [exact E2 | exact E3 | exact E4 | exact E8 | exact E9].
- intros a Ha. apply KA; [change (2 ^ 64) with 18446744073709551616; lia | unfold lpe_wr; lia].
- intros i Hi.
  pose proof (HINg ltac:(lia)) as InP.
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' (l_p cx) (l_n cx) HARg InP) as (_ & H4096 & Hbc & _).
  pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
  apply KA; [change (2 ^ 64) with 18446744073709551616; lia | unfold lpe_wr; lia].
- intros a Ha. unfold LF_FBYTES in Ha.
  apply KA; [change (2 ^ 64) with 18446744073709551616; lia | unfold lpe_wr; lia].
- intros a _ Ha. exact (GR a Ha).
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

Lemma lc_pre_ok (K4 : lc_pro_agree_stmt) : lc_pre_stmt B MT XL RLO RHI.
Proof.
unfold lc_pre_stmt. intros HP cx W' c' HB HI.
destruct cx as [fx ly0 S0 W0 regs0 mem0 md0 p n pl M fpos].
set (cx := mkLCx fx ly0 S0 W0 regs0 mem0 md0 p n pl M fpos) in *.
destruct HI as (ly' & S' & regs' & mem' & md' & Bw0 & B25 & r & Hc & HC & HFR & HSP & HFSH & HMT & HCUR & R10 & R27 &
  HW0 & HPRO & HTW).
subst c'.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' 0 HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
destruct HFR as (R18 & R26).
destruct HCUR as (R25 & R23).
destruct HW0 as (HTW0 & HLEN).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
pose proof asan_consts as ((CVlo & CVhi) & _).
change (2 ^ 47) with 140737488355328 in H47.
unfold LF_FRAME in Hsp1. unfold LF_FBYTES in *.
assert (HSTK : LLVMF_STK = 32768) by reflexivity.
(* the model: r = SPEC_OK, the head's simulation facts *)
assert (HnD : Z.of_nat (length (l_pl cx)) < TOP.FUZZ_INPUT_MAX)
  by (destruct Hn as (Hn1 & Hn2); rewrite <- Hn2; unfold TOP.FUZZ_INPUT_MAX; lia).
destruct (K4 Bw0 (l_pl cx) HLEN HnD) as (B25' & HPRO' & HAG).
rewrite HPRO in HPRO'. destruct (lpe_some_inv _ _ _ _ _ _ HPRO') as (EB & Er). subst B25' r. clear HPRO'.
destruct (IOK.prologue_ok timg_B Bw0 (fun _ => 0) (l_pl cx) lc_timg_B_ok HLEN HnD) as (B0x & _ & _ & HFI).
set (c0 := IOK.prologue_cursor (l_pl cx)) in *.
(* the start state, s11 pinned to 0x6000 *)
assert (Hsp1r : 2 ^ 46 <= lc_sp1 cx <= 2 ^ 47 - 192) by lia.
assert (Hpres : forall a, lc_sp1 cx + 48 <= a < lc_sp1 cx + 184 -> apresent (w_H W') mem' a).
{ intros a Ha. pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). apply Hp. lia. }
assert (H136 : rdword (aview segs (w_H W') mem') (lc_sp1 cx + 136) = Some (lc_F cx)).
{ unfold lc_spills in HSP. rewrite Forall_forall in HSP. apply (HSP (136, lc_F cx)).
  cbn [lf_spill_init lf_spill_scal lf_spill_sm app In]. right. left. reflexivity. }
pose proof (lpe_entry W' regs' mem' (lc_F cx) (lc_sp1 cx) R9 Hsp1r Hsp1al ltac:(lia) HFal Hpres H136) as HS0.
pose proof (st_ok_pi_pin_reg' _ _ _ 27%bv 0x6000 HS0 R27 eq_refl) as HS.
clear HS0.
assert (HEI : img_env VAL A_LIM (lpe_E regs' (lc_F cx))) by apply lpe_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (lpe_E regs' (lc_F cx)) (mrestrict (w_H W') mem')) by constructor.
assert (U9 : bv_unsigned (ew (lpe_E regs' (lc_F cx)) 9) = lc_sp1 cx)
  by (rewrite (lpe_ew_reg regs' (lc_F cx) 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (lpe_E regs' (lc_F cx)) 33) = lc_F cx)
  by (rewrite lpe_ew_33; apply unsigned_lit_small; lia).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + LO_INIT)) mem' (YK11.seg_rom segs)) md') Q) end.
(* +0x528 `beqz a0`: a0 = SPEC_OK = 0, so the fall-through to the abort pair is refuted *)
psrr_branch_tok RUN BR HS SHOK LPE_B0.
2:{ exfalso. cbn [sv_denot] in Hc. rewrite (lpe_ew_reg regs' (lc_F cx) 10 10%bv eq_refl), R10 in Hc.
    vm_compute in Hc. discriminate Hc. }
clear Hc.
(* +0x528 .. +0x584: the branch taken, s3, s4, a1, s6, the nine stores, up to `beqz s7` *)
paj_run_tok RUN HS HJ SHOK LPE_B0.
{ lpe_awr U9. }
lpe_name HS ms1.
lpe_kept HFr U9 (lc_sp1 cx) KD1.
pose proof (fun a Ha => apresent_grows _ _ _ a HG Ha) as GR1.
clear HF HFr HG.
assert (E23 : ew (lpe_E regs' (lc_F cx)) 23 = w64 (TOP.fi_n c0))
  by (rewrite (lpe_ew_reg regs' (lc_F cx) 23 23%bv eq_refl); exact R23).
(* The kept bytes: those of the frame shadow and G lie outside the stores. *)
assert (OUTSH : forall a, lc_SH cx <= a < lc_SH cx + 32 -> ~ lpe_wr (lc_sp1 cx) a)
  by (intros a Ha Hw; unfold lpe_wr in Hw; unfold lc_SH, SHADOW_OFF in Ha; lia).
assert (OUTSHr : forall a, lc_SH cx <= a < lc_SH cx + 32 -> 0 <= a < 2 ^ 64)
  by (intros a Ha; unfold lc_SH, SHADOW_OFF in Ha; pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia)); lia).
assert (OUTG : forall b n0 i, In (b, n0) TG.G_HARNESS_B -> 0 <= i < n0 ->
  0 <= b + i < 2 ^ 64 /\ ~ lpe_wr (lc_sp1 cx) (b + i)).
{ intros b n0 i Hin Hi.
  assert (Hg : inG TG.G_HARNESS_B (b + i))
    by (unfold inG; apply Exists_exists; exists (b, n0); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  split; [lia|]. intros Hw. unfold lpe_wr in Hw. lia. }
assert (HSPI : forall mm : word -> option byte,
  (forall a, 0 <= a < 2 ^ 64 -> ~ lpe_wr (lc_sp1 cx) a -> aview segs (w_H W') mm a = aview segs (w_H W') mem' a) ->
  lc_spills cx (lf_spill_init (lc_F cx)) (aview segs (w_H W') mm)).
{ intros mm KD. apply (lpe_spills_kept cx _ (aview segs (w_H W') mem')); [|exact HSP].
  intros o j Ho Hj. unfold lf_spill_init, lf_spill_scal, lf_spill_sm in Ho. cbn [app In] in Ho.
  repeat (destruct Ho as [<- | Ho];
          [apply KD; [cbn [fst]; lia | unfold lpe_wr; cbn [fst]; lia] |]).
  destruct Ho. }
(* +0x588 `beqz s7` *)
psrr_branch_tok RUN BR HS SHOK LPE_B0.
- (* s7 = 0: the branch to the epilogue *)
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
  split; [exact (lpe_core cx ly' S' W' regs' mem' md' (ms_regs msX) (ms_mem msX) _ LAWS HB HC HJ Y2 Y3 Y4 Y8 Y9 KD GR)|].
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
- (* s7 <> 0: the loop head of operation 0 *)
  assert (Hfi : TOP.fi_n c0 <> 0).
  { intros E0. cbn [sv_denot] in Hc. rewrite E23, E0 in Hc. vm_compute in Hc. discriminate Hc. }
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
  lpe_reg HS (23%bv : bv 5) (w64 (TOP.fi_n c0)) Y23 ltac:(cbn [sv_denot];
    rewrite (lpe_ew_reg regs' (lc_F cx) 23 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R23).
  lpe_reg HS (19%bv : bv 5) (w64 0) Y19 ltac:(reflexivity).
  lpe_reg HS (20%bv : bv 5) (w64 (lc_F cx + 32)) Y20 ltac:(cbn [sv_denot]; rewrite U33; reflexivity).
  lpe_reg HS (22%bv : bv 5) (w64 1) Y22 ltac:(reflexivity).
  (* the nine slots the run stored, read back from the write regions *)
  lpe_region HS 0%nat HR0. lpe_region HS 1%nat HR1. lpe_region HS 2%nat HR2.
  lpe_region HS 3%nat HR3. lpe_region HS 4%nat HR4. lpe_region HS 5%nat HR5.
  assert (SLOT : forall lo hi cs od e v,
    region_ok segs (lpe_E regs' (lc_F cx)) (mrestrict (w_H W') (ms_mem msH)) (YP09.mkRegion (Some 9%nat) lo hi lo hi cs) ->
    In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot (lpe_E regs' (lc_F cx)) e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
    rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + od) = Some v).
  { intros lo hi cs od e0 v HR Hin He Hv.
    apply (YF0x.val_mem_rdword (w_H W') (ms_mem msH) _ _ Hv).
    exact (can_field_of_region (lpe_E regs' (lc_F cx)) _ 9 (lc_sp1 cx) cs lo hi lo hi od 8%N e0 v HR U9 Hin He
      ltac:(cbn; lia) ltac:(lia)). }
  assert (HFv : 0 <= lc_F cx /\ lc_F cx + 256 <= 2 ^ 63) by lia.
  assert (V48 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 48) = Some (lc_F cx + 35))
    by (eapply (SLOT _ _ _ _ _ _ HR0); [lpe_in | cbn [sv_denot]; rewrite U33; reflexivity | lia]).
  assert (V72 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 72) = Some (2 ^ 64 - 1 - (lc_F cx + 96)))
    by (eapply (SLOT _ _ _ _ _ _ HR1); [lpe_in | apply lpe_not_val; [rewrite U33; reflexivity | lia | reflexivity] | lia]).
  assert (V80 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 80) = Some (lc_F cx + 120))
    by (eapply (SLOT _ _ _ _ _ _ HR1); [lpe_in | cbn [sv_denot]; rewrite U33; reflexivity | lia]).
  assert (V88 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 88) = Some 0x610f)
    by (eapply (SLOT _ _ _ _ _ _ HR1); [lpe_in | reflexivity | lia]).
  assert (V96 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 96) = Some (lc_F cx + 96))
    by (eapply (SLOT _ _ _ _ _ _ HR1); [lpe_in | cbn [sv_denot]; rewrite U33; reflexivity | lia]).
  assert (V120 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 120) = Some 0xffff)
    by (eapply (SLOT _ _ _ _ _ _ HR2); [lpe_in | reflexivity | lia]).
  assert (V144 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 144) = Some (lc_F cx + 32))
    by (eapply (SLOT _ _ _ _ _ _ HR3); [lpe_in | cbn [sv_denot]; rewrite U33; reflexivity | lia]).
  assert (V160 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 160) = Some (2 ^ 64 - 1 - (lc_F cx + 32)))
    by (eapply (SLOT _ _ _ _ _ _ HR4); [lpe_in | apply lpe_not_val; [rewrite U33; reflexivity | lia | reflexivity] | lia]).
  assert (V176 : rdword (aview segs (w_H W') (ms_mem msH)) (lc_sp1 cx + 176) = Some (lc_F cx + 33))
    by (eapply (SLOT _ _ _ _ _ _ HR5); [lpe_in | cbn [sv_denot]; rewrite U33; reflexivity | lia]).
  clear SLOT HR0 HR1 HR2 HR3 HR4 HR5.
  pmkst HS.
  apply SRr_ret. left. exists (mkLop 0 B25 c0 O). split; [reflexivity|].
  exists ly', S', (ms_regs msH), (ms_mem msH). eexists. exists 0.
  split; [unfold lc_cfg; reflexivity|].
  split.
  { split; [exact (lpe_core cx ly' S' W' regs' mem' md' (ms_regs msH) (ms_mem msH) _ LAWS HB HC HJ Y2 Y3 Y4 Y8 Y9 KD GR)|].
    split; [exact (conj Y18 Y26)|].
    split.
    { unfold lf_spill_loop, lc_spills. apply Forall_app. split; [exact (HSPI _ KD)|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - exact V88.
      - exact V120.
      - exact V48.
      - exact V160.
      - exact V72.
      - exact V96.
      - exact V80.
      - exact V176.
      - exact V144. }
    split.
    { apply (lc_fsh_kept cx (aview segs (w_H W') mem')); [|exact HFSH].
      intros a Ha. exact (KD a (OUTSHr a Ha) (OUTSH a Ha)). }
    split.
    { unfold lc_opok. cbn [lo_ops lo_B lo_c lo_k].
      split; [exact HAG|]. split; [unfold TC.OPS_MAX; lia|]. split; [exact HFI|]. split; [exact Hfi | lia]. }
    split; [cbn [lo_k Z.of_nat]; lia|].
    split; [exact HMT|].
    exact Y19. }
  split.
  { unfold lc_tw. apply (tw_kept_GB (aview segs (w_H W') mem')); [exact HTW|].
    intros b n0 i Hin Hi. destruct (OUTG b n0 i Hin Hi) as (Hr & Hw). exact (KD _ Hr Hw). }
  split; [exact (conj Y25 Y23)|].
  exact (conj Y20 Y22).
Qed.

End pre.
