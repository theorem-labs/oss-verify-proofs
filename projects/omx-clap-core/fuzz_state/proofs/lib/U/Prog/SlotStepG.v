(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, addresses and numbers changed; 976 of its 1075 lines of code are new or changed and 647 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_reject_clean_starved.v, with its module names and numbers changed; 714 of its 791 lines of code are new or changed and 998 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_as_written.v; 290 of its 318 lines of code are new or changed and 763 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YO10.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract Img0 FrameAPI AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec HState.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger GIInit SlotInv SlotDefs SlotStep SlotStepA SlotStepB SlotStepC SlotStepD SlotStepE HStateRoom preset_base64_decode_c check_as_written_c check_reject_clean_starved_c fuzz_free_c SlotRunB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require HsKindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Cells Step Exec.
Import ListNotations.
Local Open Scope Z_scope.

(* From the check_5 call to the return: check_5 (its contract) and segment sG, fuzz_free (its contract) and segment
   sH, free (its contract) and segment sI, which restores the saved registers and returns 0. *)

Lemma sb_free_malloc : forall x n, sb_free (sb_malloc x n) n = x.
Proof. intros [l y c] n. unfold sb_free, sb_malloc. cbn [sb_live sb_bytes sb_cap]. f_equal; lia. Qed.

Lemma fst_unique : forall {X Y : Type} (l : list (X * Y)) x a c,
  List.NoDup (map fst l) -> In (x, a) l -> In (x, c) l -> a = c.
Proof.
  intros X Y l. induction l as [|[y d] l IH]; intros x a c ND Ha Hc; [destruct Ha|].
  cbn [map fst] in ND. inversion ND as [|? ? Hn ND']; subst.
  destruct Ha as [Ea|Ha]; destruct Hc as [Ec|Hc].
  - inversion Ea; inversion Ec; subst; reflexivity.
  - inversion Ea; subst. exfalso. apply Hn. apply (in_map fst) in Hc. exact Hc.
  - inversion Ec; subst. exfalso. apply Hn. apply (in_map fst) in Ha. exact Ha.
  - exact (IH x a c ND' Ha Hc).
Qed.

Lemma single_split : forall {X : Type} (x y : X) l1 l2, [x] = l1 ++ y :: l2 -> l1 = [] /\ l2 = [].
Proof.
  intros X x y l1 l2 E. destruct l1 as [|z l1]; cbn in E.
  - injection E as _ E2. split; [reflexivity | symmetry; exact E2].
  - injection E as _ E2. destruct l1; discriminate.
Qed.

Section G.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Definition at_ff (regs0 : bvmap 5 word) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model)
    (pl : list byte) (cnt0 : Z) (b : sbound)
    (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  exists lenw Lam peak cnt bnd bd pt text,
  pd B API regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text /\ cnt <= cnt0 + 74 /\
  getr regs 1 = Z_to_bv 64 0x13490 /\ getr regs 8 = Z_to_bv 64 text /\ getr regs 10 = Z_to_bv 64 bd.

Definition at_fr (regs0 : bvmap 5 word) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model)
    (pl : list byte) (cnt0 : Z) (b : sbound)
    (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  exists lenw peak cnt pt text,
  slot_mid B API regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw [] peak cnt (sb_malloc b (slot_nn pl + 1)) /\
  cnt <= cnt0 + 74 /\ In (pt, slot_nn pl + 1) (user_blocks A) /\ ptr_addr L pt = text /\
  (forall q k, In (q, k) (user_blocks A0) -> 0 < k -> ptr_addr L0 q <> text) /\
  getr regs 1 = Z_to_bv 64 0x13498 /\ getr regs 10 = Z_to_bv 64 text.

Lemma step_c5 : slot_env B API -> check_reject_clean_starved_contract B API ->
  forall regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L A regs mem md K (P : config -> Prop),
  slot_start B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j -> slot_bnd b -> K <= 72 ->
  at_pd B API 0x13488 K (fun _ => True) regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md ->
  (forall L' A' regs' mem' md', at_ff regs0 L0 A0 mem0 md0 pl cnt0 b L' A' regs' mem' md' ->
     SR (ms_segs B) (mkCfg (mkst regs' (Z_to_bv 64 0x14378) mem' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 0x13ef0) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros ENV CRS regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L A regs mem md K P HS HB HK
    (lenw & Lam & peak & cnt & bnd & bd & pt & text & PD & Hcn & R1 & R8 & R9 & R10 & R11 & R12 & R18 & R19 & _) KC.
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
  destruct (ans_caw B L0 A0 mem pl text bd lenw Lam b bnd ANS) as (l & El & CAWA & HLam & Hl).
  destruct (ans_bnd B L0 A0 mem pl text bd lenw Lam b bnd ANS Hnn) as (Bc & Bl & Bb).
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
  { apply (CRS L A regs mem md text (slot_db pl) slack bd l bnd Lam peak cnt).
    - eapply mid_pre; [exact MID | unfold CRCS_STK, ALLOC_STACK, SLOT_STACK; lia |]. rewrite R1. apply ret_lit; lia.
    - exact R10.
    - exact R11.
    - rewrite R12, El. reflexivity.
    - exact BYS.
    - apply slot_db_nozero.
    - rewrite Hdl, Hsl. replace (- (text + slot_nn pl + 1)) with (- (text + (slot_nn pl + 1))) by lia. lia.
    - rewrite Hdl. lia.
    - intros a Ha. unfold in_window, CRCS_STK, ALLOC_STACK. rewrite Hsp. rewrite Hdl, Hsl in Ha. lia.
    - exists text, (slot_nn pl + 1). rewrite Hdl. split; [exact HinT | lia].
    - exact CAWA.
    - exact HLam.
    - exact LG.
    - lia.
    - exact RA.
    - exact RES.
    - rewrite Hdl. apply (hs_room_of_bound 2 (2 ^ 25)).
      + lia.
      + unfold starved_ops. destruct (bd =? 0); cbn [length]; lia.
      + unfold hs_small, starved_ops. destruct (Z.eqb_spec bd 0) as [Hb|Hb].
        * apply Forall_cons; [cbv beta iota; lia | apply Forall_nil].
        * specialize (Hl Hb). apply Forall_cons; [cbv beta iota; lia|].
          apply Forall_cons; [cbv beta iota; lia | apply Forall_nil].
      + rewrite Bc, HBc. unfold CAPMAX. change (Z.of_nat 2) with 2. lia.
      + change (Z.of_nat 2) with 2. lia. }
  intros c' (L' & A' & regs' & mem' & md' & -> & RA' & GK & CP & HI & BLK & KP & UK & LG' & RES').
  rewrite R1.
  pose proof CP as (HM' & _ & _ & _ & PA & RP & _).
  assert (Hcc : (if bd =? 0 then cnt + 1 else cnt + 2) <= cnt + 2) by (destruct (bd =? 0); lia).
  assert (Hcc' : cnt <= (if bd =? 0 then cnt + 1 else cnt + 2)) by (destruct (bd =? 0); lia).
  assert (PD' : pd B API regs0 L0 A0 mem0 md0 pl cnt0 b L' A' regs' mem' md' lenw Lam peak
                  (if bd =? 0 then cnt + 1 else cnt + 2) bnd bd pt text).
  { eapply pd_call; [exact ENV | exact PD | exact CP | unfold CRCS_STK, ALLOC_STACK, SLOT_STACK; lia | | exact UK |
      exact KP | exact HI | exact LG' | lia | | exact RA'].
    - intros a Ha. left. exact (statics_G a Ha).
    - eapply res_same_blocks; [exact RES | exact RES' | reflexivity | exact BLK]. }
  destruct (kb_md B API L' A' mem' md' HM') as [Hh Hl'].
  eapply (kb_seg B regs' (Z_to_bv 64 0x13488) mem' md' _ P Hh Hl' SEG).
  - apply sG_run.
  - intros ms' ->. do 3 eexists. reflexivity.
  - intros R pc' m2 regs2 HQ HG. injection HQ as ER Epc Em. subst R pc' m2.
    apply (KC L' A'). exists lenw, Lam, peak, (if bd =? 0 then cnt + 1 else cnt + 2), bnd, bd, pt, text.
    split.
    { destruct PD' as (MID2 & REST). split; [|exact REST].
      apply (mid_regs B API regs0 L0 A0 mem0 md0 cnt0 L' A' regs' mem' md' _ _ _ _ _ regs2 MID2).
      - rewrite HG. reflexivity.
      - slot_kept HG. }
    split; [lia|].
    split; [rewrite HG; reflexivity|].
    split; [rewrite HG; exact (eq_trans (RP 8 ltac:(unfold callee_saved; lia)) R8)|].
    rewrite HG. exact (eq_trans (RP 18 ltac:(unfold callee_saved; lia)) R18).
Qed.

Lemma step_ff : slot_env B API -> fuzz_free_contract B API sb_form ->
  forall regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L A regs mem md (P : config -> Prop),
  slot_start B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ->
  at_ff regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md ->
  (forall L' A' regs' mem' md', at_fr regs0 L0 A0 mem0 md0 pl cnt0 b L' A' regs' mem' md' ->
     SR (ms_segs B) (mkCfg (mkst regs' (Z_to_bv 64 (ms_free B)) mem' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 0x14378) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros ENV FF regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L A regs mem md P HS
    (lenw & Lam & peak & cnt & bnd & bd & pt & text & PD & Hcn & R1 & R8 & R10) KC.
  pose proof ENV as (SEG & MAL & FRE & ERR & AX & BS & GF & SNK).
  pose proof HS as (SP & _ & _ & _ & _ & _ & _ & _ & _ & Hp & Hpe & _ & _ & _ & _ & _ & _ & _ & HCN & HJ).
  pose proof PD as (MID & Hpt & Ept & H16 & FA0 & BYT & ANS & Hnn).
  pose proof MID as (_ & REL & R2 & RS & FR & LG & HC & RES & RA & FZ).
  pose proof (mid_spZ B regs0 regs SP R2) as Hsp.
  pose proof SP as (Hs16 & Hlo & Hhi & Htp).
  pose proof alloc_ceiling_val as Hac. pose proof alloc_ceiling_lt as Hacl.
  pose proof REL as (HM & _ & _ & _ & _ & U0 & _).
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ pt _ HM Hpt) as [Ht1 Ht2]. rewrite Ept in Ht1, Ht2.
  set (m := dec_size (zs (slot_db pl))).
  set (k := if bd =? 0 then 0 else m).
  unfold SLOT_STACK in *.
  eapply SR_bind.
  { apply (FF L A regs mem md bd k bnd Lam peak cnt (2 ^ 64 - 1)).
    - eapply mid_pre; [exact MID | unfold ALLOC_STACK, SLOT_STACK; lia |]. rewrite R1. apply ret_lit; lia.
    - exact R10.
    - exact LG.
    - exact RA.
    - destruct ANS as [(_ & -> & _ & -> & _)|(bs & _ & Hb & _ & _ & -> & _)].
      + left. split; [reflexivity|]. unfold k. reflexivity.
      + right. unfold k. rewrite (proj2 (Z.eqb_neq bd 0) Hb). left. reflexivity.
    - exact RES. }
  intros c' (L' & A' & regs' & mem' & md' & -> & RA' & GK & HI & _ & CP & _ & KP & UK & CASES).
  cbn [rf_ok rf_free sb_form] in CASES.
  rewrite R1.
  pose proof CP as (HM' & _ & _ & _ & PA & RP & _).
  assert (POST : ledger B L' A' mem' [] peak cnt (2 ^ 64 - 1) /\ res_ok_slots A' (sb_malloc b (slot_nn pl + 1)) /\
    (forall q k', In (q, k') (user_blocks A0) -> (ptr_addr L q, k') <> (bd - 16, k + 16)) /\
    (text, slot_nn pl + 1) <> (bd - 16, k + 16) /\
    (forall a, free_writes bd k a -> in_globals omx_G a \/ (0 <= a < alloc_ceiling /\ ~ in_img B a))).
  { assert (Hgl : forall a, G_LIVE <= a < G_LIVE + 8 -> in_globals omx_G a).
    { intros a Ha. apply statics_G. left. exact Ha. }
    destruct ANS as [(_ & Hb & _ & HL & Hbn)|(bs & _ & Hb & _ & _ & HL & Hbn & NT & NA)].
    - assert (Hk : k = 0) by (unfold k; rewrite Hb; reflexivity).
      destruct CASES as [(_ & _ & _ & _ & _ & _ & _ & LG2 & RES2)|(Hp0 & _)]; [|exfalso; exact (Hp0 Hb)].
      rewrite HL in LG2. rewrite Hbn in RES2.
      split; [exact LG2|]. split; [exact RES2|].
      split.
      { intros q k' Hq E. injection E as E1 _. destruct (U0 q k' Hq) as [Hq1 _].
        pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q _ HM Hq1). lia. }
      split; [intros E; injection E as E1 _; lia|].
      intros a [Ha|(Hbz & _)]; [left; exact (Hgl a Ha) | exfalso; exact (Hbz Hb)].
    - assert (Hk : k = m) by (unfold k; rewrite (proj2 (Z.eqb_neq bd 0) Hb); reflexivity).
      destruct CASES as [(Hp0 & _)|(_ & _ & (l1 & l2 & EL & LG2) & RES2)]; [exfalso; exact (Hb Hp0)|].
      rewrite HL in EL. destruct (single_split _ _ _ _ EL) as [-> ->]. cbn [app] in LG2.
      rewrite Hbn, Hk in RES2. unfold m in RES2. rewrite sb_free_malloc in RES2.
      split; [exact LG2|]. split; [exact RES2|].
      split.
      { intros q k' Hq. destruct (U0 q k' Hq) as [_ Ep]. rewrite Ep, Hk. exact (NA q k' Hq). }
      split; [rewrite Hk; exact NT|].
      rewrite HL in LG. destruct LG as (_ & _ & _ & _ & _ & LF). inversion LF as [|x l Hx _]; subst.
      destruct Hx as (_ & Hin & _ & Hni). cbn [fst snd] in Hin, Hni.
      intros a [Ha|(_ & Ha)]; [left; exact (Hgl a Ha)|]. right.
      rewrite Hk in Ha. unfold m in Ha.
      destruct (lib.U.Prog.HsKindB.block_low B API L A mem md _ _ (a - (bd - 16)) HM Hin ltac:(lia)) as [Hge Hlt].
      split; [lia|]. replace a with (bd - 16 + (a - (bd - 16))) by lia. apply Hni. lia. }
  destruct POST as (LG2 & RES2 & NA & NT & HE).
  assert (Hpt' : In (pt, slot_nn pl + 1) (user_blocks A')).
  { apply (UK pt _ Hpt). rewrite Ept. exact NT. }
  assert (MID' : slot_mid B API regs0 L0 A0 mem0 md0 cnt0 L' A' regs' mem' md' lenw [] peak cnt
                   (sb_malloc b (slot_nn pl + 1))).
  { eapply mid_call; [exact ENV | exact MID | exact CP | unfold ALLOC_STACK, SLOT_STACK; lia | exact HE | | exact HI |
      exact LG2 | lia | exact RES2 | exact RA'].
    intros q k' Hq0 Hq. exact (UK q k' Hq (NA q k' Hq0)). }
  destruct (kb_md B API L' A' mem' md' HM') as [Hh Hl'].
  eapply (kb_seg B regs' (Z_to_bv 64 0x13490) mem' md' _ P Hh Hl' SEG).
  - apply sH_run.
  - intros ms' ->. do 3 eexists. reflexivity.
  - intros R pc' m2 regs2 HQ HG. injection HQ as ER Epc Em. subst R pc' m2.
    rewrite FRE in KC. apply (KC L' A'). exists lenw, peak, cnt, pt, text.
    split.
    { apply (mid_regs B API regs0 L0 A0 mem0 md0 cnt0 L' A' regs' mem' md' _ _ _ _ _ regs2 MID').
      - rewrite HG. reflexivity.
      - slot_kept HG. }
    split; [exact Hcn|]. split; [exact Hpt'|]. split; [rewrite (PA _ _ Hpt Hpt'); exact Ept|].
    split; [exact FA0|].
    split; [rewrite HG; reflexivity|].
    rewrite HG. exact (eq_trans (RP 8 ltac:(unfold callee_saved; lia)) R8).
Qed.

Lemma step_fr : slot_env B API -> free_contract B API ->
  forall regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b L A regs mem md,
  slot_start B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j -> getr regs0 1 = Z_to_bv 64 ra ->
  lib_delta (Z.of_nat (length pl)) b = b ->
  at_fr regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom (ms_segs B))) md)
    (slot_fin B API regs0 L0 A0 mem0 md0 ra p0 (Z.of_nat (length pl)) b j).
Proof.
  intros ENV FRC regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b L A regs mem md HS HRA LD
    (lenw & peak & cnt & pt & text & MID & Hcn & Hpt & Ept & FA0 & R1 & R10).
  pose proof ENV as (SEG & MAL & FRE & ERR & AX & BS & GF & SNK).
  pose proof HS as (SP & _ & _ & _ & _ & _ & HRT & _ & _ & Hp & Hpe & _ & _ & _ & _ & _ & _ & _ & HCN & HJ).
  pose proof MID as (_ & REL & R2 & RS & FR & LG & HC & RES & RA & FZ).
  pose proof (mid_spZ B regs0 regs SP R2) as Hsp.
  pose proof SP as (Hs16 & Hlo & Hhi & Htp).
  pose proof alloc_ceiling_val as Hac. pose proof alloc_ceiling_lt as Hacl.
  pose proof REL as (HM & HWF & _ & _ & _ & U0 & _).
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ pt _ HM Hpt) as [Ht1 Ht2]. rewrite Ept in Ht1, Ht2.
  unfold SLOT_STACK in *.
  eapply SR_bind.
  { apply (FRC L A regs mem md pt (slot_nn pl + 1) (sb_malloc b (slot_nn pl + 1))).
    - apply (proj2 (call_pre_k_alloc B MR L A regs mem md)).
      eapply mid_pre; [exact MID | unfold ALLOC_STACK, SLOT_STACK; lia |]. rewrite R1. apply ret_lit; lia.
    - exact RA.
    - exact Hpt.
    - rewrite Ept. exact R10.
    - exact RES. }
  intros c' (L' & A' & regs' & mem' & md' & -> & CP0 & _ & _ & RA' & GK & UB & HI & _ & RES').
  rewrite R1.
  pose proof (proj1 (call_post_k_alloc B MR L A regs mem md _ L' A' regs' mem' md') CP0) as CP.
  pose proof CP as (HM' & _ & _ & _ & PA & RP & _).
  rewrite sb_free_malloc in RES'.
  assert (Hblk : forall a, ptr_addr L pt <= a < ptr_addr L pt + (slot_nn pl + 1) ->
            0 <= a < alloc_ceiling /\ ~ in_img B a).
  { intros a Ha. split; [lia|]. replace a with (ptr_addr L pt + (a - ptr_addr L pt)) by lia.
    apply (ax_blocks_img AX L A mem md pt _ (a - ptr_addr L pt) HM Hpt). lia. }
  assert (LG2 : ledger B L' A' mem' [] peak cnt (2 ^ 64 - 1)).
  { eapply ledger_frame; [exact LG | intros a k [] |].
    intros x [Hx|(a & k & [] & _)].
    apply (kb_post_globals B API omx_G ALLOC_STACK L A regs mem md _ L' A' regs' mem' md' x GF HM CP).
    - rewrite Hsp. unfold ALLOC_STACK. lia.
    - exact (statics_G x Hx).
    - intros Hx'. apply (proj2 (Hblk x Hx')). apply (glob_img B API ENV). exact (statics_G x Hx). }
  assert (MID' : slot_mid B API regs0 L0 A0 mem0 md0 cnt0 L' A' regs' mem' md' lenw [] peak cnt b).
  { eapply mid_call; [exact ENV | exact MID | exact CP | unfold ALLOC_STACK, SLOT_STACK; lia | | | exact HI |
      exact LG2 | lia | exact RES' | exact RA'].
    - intros a Ha. right. exact (Hblk a Ha).
    - intros q k Hq0 Hq. apply (UB q k Hq). intros ->.
      pose proof (fst_unique _ pt k (slot_nn pl + 1) (lib.Reusable.YO10.user_block_ptrs_NoDup A HWF) Hq Hpt) as ->.
      destruct (U0 pt _ Hq0) as [_ Ep]. apply (FA0 pt _ Hq0 ltac:(pose proof (slot_nn_range pl); lia)).
      rewrite <- Ep. exact Ept. }
  pose proof MID' as (_ & REL' & R2' & RS' & FR' & _).
  destruct (kb_md B API L' A' mem' md' HM') as [Hh Hl'].
  assert (Hsp' : bv_unsigned (getr regs' 2) = spZ regs0 - 48)
    by exact (eq_trans (f_equal bv_unsigned (RP 2 ltac:(unfold callee_saved; lia))) Hsp).
  eapply (kb_seg B regs' (Z_to_bv 64 0x13498) mem' md' _ _ Hh Hl' SEG).
  - eapply sI_run. rewrite Hsp'. exact FR'.
  - intros ms' ->. do 3 eexists. reflexivity.
  - intros R pc' m2 regs2 HQ HG. injection HQ as ER Epc Em. subst R pc' m2.
    rewrite (kb_ret_pc _ HRT), HRA. apply SR_ret.
    apply (fin_of B API ENV regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b L' A' regs2 mem' md' peak cnt HS HRA REL').
    + intros r Hr. rewrite HG. unfold callee_saved in Hr.
      assert (HC2 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ 20 <= r <= 27) by lia.
      destruct HC2 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | HC2]]]]]]].
      * change (Z_to_bv 64 (bv_unsigned (getr regs' 2) + 48) = getr regs0 2). rewrite Hsp'.
        replace (spZ regs0 - 48 + 48) with (spZ regs0) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
      * exact (RS' 3 ltac:(lia)).
      * exact (RS' 4 ltac:(lia)).
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * assert (HC3 : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct HC3 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
          first [exact (RS' 20 ltac:(lia)) | exact (RS' 21 ltac:(lia)) | exact (RS' 22 ltac:(lia)) |
                 exact (RS' 23 ltac:(lia)) | exact (RS' 24 ltac:(lia)) | exact (RS' 25 ltac:(lia)) |
                 exact (RS' 26 ltac:(lia)) | exact (RS' 27 ltac:(lia))].
    + rewrite HG. reflexivity.
    + exact LG2.
    + lia.
    + exact RA'.
    + rewrite LD. exact RES'.
    + exact FZ.
Qed.

End G.
