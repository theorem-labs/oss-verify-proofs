(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, addresses and numbers changed; 976 of its 1075 lines of code are new or changed and 647 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_reject_clean_starved.v, with its module names and numbers changed; 714 of its 791 lines of code are new or changed and 998 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_as_written.v; 290 of its 318 lines of code are new or changed and 763 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/SlotStepG.v, with its addresses changed; 76 of its 144 lines of code are new or changed and 250 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract Img0 FrameAPI AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec HState.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger GIInit SlotInv SlotDefs SlotStep SlotStepA SlotStepB SlotStepC SlotStepD SlotStepE HStateRoom preset_base64_decode_c check_round_trip_c SlotRunB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require HsKindB strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Cells Step Exec.
Import ListNotations.
Local Open Scope Z_scope.

(* From the check_4 call to the check_5 call: check_4 (its contract; it returns in a new FP state), then
   segment sF. *)

Section FX.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Lemma pd_fx : forall (f f' : FPState) regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd
    pt text,
  @pd f rc B API regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text ->
  frm_zero (@fp_csr f') ->
  @pd f' rc B API regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text.
Proof.
  intros f f' regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text
    ((SP & REL & R2 & RS & FR & LG & HC & RES & RA & _) & REST) FZ.
  exact (conj (conj SP (conj REL (conj R2 (conj RS (conj FR (conj LG (conj HC (conj RES (conj RA FZ))))))))) REST).
Qed.

End FX.

Section F.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Lemma step_c4 : slot_env B API -> check_round_trip_contract B API ->
  forall regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L A regs mem md (P : config -> Prop),
  slot_start B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j -> slot_bnd b ->
  at_pd B API 0x13464 4 (fun bd => bd <> 0) regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md ->
  (forall (fx' : FPState) L' A' regs' mem' md', frm_zero (@fp_csr fx') ->
     @at_pd fx' rc B API 0x13488 72 (fun _ => True) regs0 L0 A0 mem0 md0 pl cnt0 b L' A' regs' mem' md' ->
     SR (ms_segs B) (mkCfg (@mkst fx' regs' (Z_to_bv 64 0x13ef0) mem' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 0x139ac) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros ENV CRT regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L A regs mem md P HS HB
    (lenw & Lam & peak & cnt & bnd & bd & pt & text & PD & Hcn & R1 & R8 & R9 & R10 & R11 & R12 & R18 & R19 & Hb0) KC.
  pose proof ENV as (SEG & MAL & FRE & ERR & AX & BS & GF & SNK).
  pose proof HS as (SP & _ & _ & _ & _ & _ & _ & _ & _ & Hp & Hpe & _ & _ & _ & _ & _ & _ & _ & HCN & HJ).
  pose proof PD as (MID & Hpt & Ept & H16 & FA0 & BYT & ANS & Hnn).
  pose proof MID as (_ & REL & R2 & RS & FR & LG & HC & RES & RA & FZ).
  pose proof (mid_spZ B regs0 regs SP R2) as Hsp.
  pose proof SP as (Hs16 & Hlo & Hhi & Htp).
  pose proof alloc_ceiling_val as Hac. pose proof alloc_ceiling_lt as Hacl.
  pose proof (slot_nn_range pl) as Hnr. pose proof (slot_db_length pl) as Hdl.
  pose proof REL as (HM & _).
  pose proof HB as (HBl & HBb & HBc).
  assert (Hj : Z.of_nat j <= 3) by lia. assert (Hcnt : cnt0 <= 3 * 2 ^ 60) by nia.
  destruct (ans_bnd B L0 A0 mem pl text bd lenw Lam b bnd ANS Hnn) as (Bc & Bl & Bb).
  destruct ANS as [(_ & E & _)|(bs & Hs & _ & El & BYB & ELam & _ & _ & _)]; [exfalso; exact (Hb0 E)|].
  pose proof (dec_len _ _ Hs) as Hlen. unfold zs in Hlen. rewrite length_map, Hdl in Hlen.
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ pt _ HM Hpt) as [Ht1 Ht2]. rewrite Ept in Ht1, Ht2.
  assert (HinT : In (text, slot_nn pl + 1) (blocks L A)).
  { rewrite <- Ept. unfold blocks. apply in_map_iff. exists (pt, slot_nn pl + 1). split; [reflexivity | exact Hpt]. }
  destruct (slack_of B API BS L A mem md text (slot_nn pl + 1) HM HinT ltac:(lia)) as (slack & BS1 & Hsl).
  pose proof (Z.mod_pos_bound (- (text + (slot_nn pl + 1))) 8 ltac:(lia)) as Hsr.
  assert (BYS : lib.Lib.Mem.bytes_at (ms_segs B) mem text (slot_db pl ++ Z_to_bv 8 0 :: slack)).
  { replace (slot_db pl ++ Z_to_bv 8 0 :: slack) with ((slot_db pl ++ [Z_to_bv 8 0]) ++ slack)
      by (rewrite <- app_assoc; reflexivity).
    apply lib.Lib.Mem.bytes_at_app. split; [exact BYT|].
    replace (text + Z.of_nat (length (slot_db pl ++ [Z_to_bv 8 0]))) with (text + (slot_nn pl + 1))
      by (rewrite length_app, Nat2Z.inj_add, Hdl; cbn [length Z.of_nat]; lia).
    exact BS1. }
  unfold SLOT_STACK in *.
  eapply SR_bind.
  { apply (CRT L A regs mem md text (slot_db pl) slack bd bs bnd Lam peak cnt).
    - eapply mid_pre; [exact MID | unfold CRT_STK, ALLOC_STACK, SLOT_STACK; lia |]. rewrite R1. apply ret_lit; lia.
    - exact R10.
    - exact R11.
    - rewrite R12, El. reflexivity.
    - exact BYS.
    - apply slot_db_nozero.
    - rewrite Hdl, Hsl. replace (- (text + slot_nn pl + 1)) with (- (text + (slot_nn pl + 1))) by lia. lia.
    - rewrite Hdl. lia.
    - intros a Ha. unfold in_window, CRT_STK, ALLOC_STACK. rewrite Hsp. rewrite Hdl, Hsl in Ha. lia.
    - exists text, (slot_nn pl + 1). rewrite Hdl. split; [exact HinT | lia].
    - exact Hs.
    - exact Hb0.
    - exact BYB.
    - exists (dec_size (zs (slot_db pl))). split; [rewrite ELam; left; reflexivity|].
      unfold dec_size, zs. rewrite length_map, Hdl. lia.
    - exact LG.
    - unfold CRT_ALLOCS. lia.
    - destruct (ax_statics AX L A mem md HM) as (G1 & (g & _ & G2) & _).
      split; [exact RA | split; [exact G1 | exists g; exact G2]].
    - rewrite Hsp. lia.
    - unfold strtod_c.STRTOD_GLOBALS_TOP, CRT_STK, ALLOC_STACK. rewrite Hsp. lia.
    - exact FZ.
    - exact RES.
    - unfold CRT_OPS, CRT_SIZE. apply (hs_cap_le bnd 200 160 (2 ^ 25)); [lia | lia |].
      exact (cap_of b bnd HB Bc Bl Bb). }
  intros c' (fx' & L' & A' & regs' & mem' & md' & peak' & cnt' & -> & FK & FZ' & RA' & GK & CP & HI & KP & UK & HPK &
    HCN' & LG' & RES').
  rewrite R1.
  pose proof CP as (HM' & _ & _ & _ & PA & RP & _).
  assert (PD' : @pd fx rc B API regs0 L0 A0 mem0 md0 pl cnt0 b L' A' regs' mem' md' lenw Lam peak' cnt' bnd bd pt
                  text).
  { eapply pd_call; [exact ENV | exact PD | exact CP | unfold CRT_STK, ALLOC_STACK, SLOT_STACK; lia | | exact UK |
      exact KP | exact HI | exact LG' | unfold CRT_ALLOCS in HCN'; lia | exact RES' | exact RA'].
    intros a Ha. left. exact (statics_G a Ha). }
  pose proof (pd_fx B API fx fx' regs0 L0 A0 mem0 md0 pl cnt0 b L' A' regs' mem' md' lenw Lam peak' cnt' bnd bd pt
    text PD' FZ') as PD2.
  pose proof PD2 as (MID2 & _).
  pose proof MID2 as (_ & _ & _ & _ & FR2 & _).
  destruct (kb_md B API L' A' mem' md' HM') as [Hh Hl'].
  assert (Hsp' : bv_unsigned (getr regs' 2) = spZ regs0 - 48)
    by exact (eq_trans (f_equal bv_unsigned (RP 2 ltac:(unfold callee_saved; lia))) Hsp).
  destruct FR2 as ((_ & BY0) & _).
  cbn [slot_cells lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in BY0.
  apply lib.Lib.Mem.bytes_at_app in BY0 as (BYL & _).
  eapply (kb_seg B regs' (Z_to_bv 64 0x13464) mem' md' _ P Hh Hl' SEG).
  - eapply sF_run with (lenw := lenw). rewrite Hsp'. exact BYL.
  - intros ms' (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
    do 3 eexists. reflexivity.
  - intros R pc' m2 regs2 HQ HG.
    destruct HQ as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & EQ).
    injection EQ as ER Epc Em. subst R pc' m2.
    apply (KC fx' L' A' regs2 mem' md' FZ'). exists lenw, Lam, peak', cnt', bnd, bd, pt, text.
    split.
    { destruct PD2 as (MID3 & REST). split; [|exact REST].
      apply (mid_regs B API regs0 L0 A0 mem0 md0 cnt0 L' A' regs' mem' md' _ _ _ _ _ regs2 MID3).
      - rewrite HG. reflexivity.
      - slot_kept HG. }
    split; [unfold CRT_ALLOCS in HCN'; lia|].
    split; [rewrite HG; reflexivity|].
    split; [rewrite HG; exact (eq_trans (RP 8 ltac:(unfold callee_saved; lia)) R8)|].
    split; [rewrite HG; exact (eq_trans (RP 9 ltac:(unfold callee_saved; lia)) R9)|].
    split; [rewrite HG; exact (eq_trans (RP 8 ltac:(unfold callee_saved; lia)) R8)|].
    split; [rewrite HG; exact (eq_trans (RP 18 ltac:(unfold callee_saved; lia)) R18)|].
    split; [rewrite HG; reflexivity|].
    split; [rewrite HG; exact (eq_trans (RP 18 ltac:(unfold callee_saved; lia)) R18)|].
    split; [rewrite HG; exact (eq_trans (RP 19 ltac:(unfold callee_saved; lia)) R19)|].
    exact I.
Qed.

End F.
