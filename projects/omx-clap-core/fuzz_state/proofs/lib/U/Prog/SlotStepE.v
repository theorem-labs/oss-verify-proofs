(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, addresses and numbers changed; 976 of its 1075 lines of code are new or changed and 647 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_reject_clean_starved.v, with its module names and numbers changed; 714 of its 791 lines of code are new or changed and 998 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_as_written.v; 290 of its 318 lines of code are new or changed and 763 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/SlotStepG.v, with its module names and addresses changed; 262 of its 331 lines of code are new or changed and 249 lines of the source are left out. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger GIInit SlotInv SlotDefs SlotStep SlotStepA SlotStepB SlotStepC SlotStepD HStateRoom preset_base64_decode_c SlotRunA check_as_written_c check_reject_clean_c check_round_trip_c SlotRunB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require HsKindB strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Cells Step Exec.
Import ListNotations.
Local Open Scope Z_scope.

(* From the check_2 call to the check_5 call: check_2 (its contract), then on a null decoder result segment sE0
   (check_3 inside), else segment sE1, check_4 (its contract; a new FP state) and segment sF. *)

Lemma room_of8 : forall b b' n, slot_bnd b -> sb_cap b' = sb_cap b -> sb_live b' <= sb_live b + 8 ->
  sb_bytes b' <= sb_bytes b + 2 ^ 27 -> 0 <= n <= 2 ^ 25 -> room_slots b' n.
Proof.
  intros b b' n (Hl & Hb & Hc) E1 E2 E3 Hn. apply (hs_cap_room b' 199 (2 ^ 25) n); [lia | exact Hn |].
  unfold hs_cap. rewrite E1, Hc. unfold CAPMAX. change (Z.of_nat (Datatypes.S 199)) with 200. lia.
Qed.

Section E.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Definition at_pd (ra K : Z) (Q : Z -> Prop) (regs0 : bvmap 5 word) (L0 : layout) (A0 : astate)
    (mem0 : word -> option byte) (md0 : Model) (pl : list byte) (cnt0 : Z) (b : sbound)
    (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  exists lenw Lam peak cnt bnd bd pt text,
  pd B API regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text /\ cnt <= cnt0 + K /\
  getr regs 1 = Z_to_bv 64 ra /\ getr regs 8 = Z_to_bv 64 text /\ getr regs 9 = Z_to_bv 64 (slot_nn pl) /\
  getr regs 10 = Z_to_bv 64 text /\ getr regs 11 = Z_to_bv 64 bd /\ getr regs 12 = lenw /\
  getr regs 18 = Z_to_bv 64 bd /\ getr regs 19 = Z_to_bv 64 0 /\ Q bd.

Lemma at_c2_pd : forall regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md,
  at_c2 B API regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md ->
  at_pd 0x13450 4 (fun _ => True) regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md.
Proof.
  intros regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md
    (lenw & Lam & peak & cnt & bnd & bd & pt & text & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  exists lenw, Lam, peak, cnt, bnd, bd, pt, text. repeat (split; [assumption|]). exact I.
Qed.

Lemma ans_caw : forall L0 A0 mem pl text bd lenw Lam b bnd,
  dec_ans B L0 A0 mem pl text bd lenw Lam b bnd ->
  exists l, lenw = Z_to_bv 64 l /\ caw_answer B mem (slot_db pl) bd l /\
    (bd <> 0 -> exists k, In (bd, k) Lam /\ l <= k) /\ (bd <> 0 -> 0 <= l <= slot_nn pl / 4 * 3 + 2).
Proof.
  intros L0 A0 mem pl text bd lenw Lam b bnd [(Hn & -> & -> & -> & ->)|(bs & Hs & Hb & -> & BY & -> & -> & _ & _)].
  - exists (2 ^ 64 - 1). split; [reflexivity|]. split; [left; split; [exact Hn | split; reflexivity]|].
    split; intros H; exfalso; apply H; reflexivity.
  - pose proof (dec_len _ _ Hs) as Hl. unfold zs in Hl. rewrite length_map, slot_db_length in Hl.
    exists (Z.of_nat (length bs)). split; [reflexivity|].
    split; [right; exists bs; split; [exact Hs|]; split; [exact Hb|]; split; [reflexivity | exact BY]|].
    split.
    + intros _. exists (dec_size (zs (slot_db pl))). split; [left; reflexivity|].
      unfold dec_size, zs. rewrite length_map, slot_db_length. lia.
    + intros _. lia.
Qed.

Lemma ans_bnd : forall L0 A0 mem pl text bd lenw Lam b bnd,
  dec_ans B L0 A0 mem pl text bd lenw Lam b bnd -> slot_nn pl <= 0x300000 ->
  sb_cap bnd = sb_cap b /\ sb_live bnd <= sb_live b + 2 /\ sb_bytes bnd <= sb_bytes b + 2 ^ 25.
Proof.
  intros L0 A0 mem pl text bd lenw Lam b bnd ANS Hn. pose proof (slot_nn_range pl).
  destruct ANS as [(_ & _ & _ & _ & ->)|(bs & _ & _ & _ & _ & _ & -> & _ & _)];
    cbn [sb_cap sb_live sb_bytes sb_malloc]; [lia|].
  unfold dec_size, zs. rewrite length_map, slot_db_length. lia.
Qed.

Lemma ans_bd : forall L0 A0 L A mem md pl text bd lenw Lam b bnd peak cnt fail,
  MR L A mem md -> ledger B L A mem Lam peak cnt fail ->
  dec_ans B L0 A0 mem pl text bd lenw Lam b bnd -> bd <> 0 -> 4112 <= bd /\ bd < alloc_ceiling.
Proof.
  intros L0 A0 L A mem md pl text bd lenw Lam b bnd peak cnt fail HM LG ANS Hb.
  destruct ANS as [(_ & E & _)|(bs & _ & _ & _ & _ & -> & _ & _ & _)]; [exfalso; exact (Hb E)|].
  destruct (ledger_block_range B API L A mem md _ peak cnt fail bd _ HM LG ltac:(left; reflexivity)) as (H1 & H2 & _).
  unfold dec_size in H2. lia.
Qed.

Lemma ans_keep : forall L0 A0 L A mem mem' md pl text bd lenw Lam b bnd peak cnt fail,
  MR L A mem md -> ledger B L A mem Lam peak cnt fail -> keeps B L A mem mem' 0 ->
  dec_ans B L0 A0 mem pl text bd lenw Lam b bnd -> dec_ans B L0 A0 mem' pl text bd lenw Lam b bnd.
Proof.
  intros L0 A0 L A mem mem' md pl text bd lenw Lam b bnd peak cnt fail HM LG KP
    [H|(bs & Hs & Hb & Hl & BY & HL & Hbn & N1 & N2)]; [left; exact H|].
  right. exists bs. split; [exact Hs|]. split; [exact Hb|]. split; [exact Hl|].
  split; [|split; [exact HL | split; [exact Hbn | split; [exact N1 | exact N2]]]].
  subst Lam. destruct LG as (_ & _ & _ & _ & _ & LF). inversion LF as [|x l Hx _]; subst.
  destruct Hx as (Hk & Hin & _). cbn [fst snd] in Hin, Hk.
  pose proof (dec_len _ _ Hs) as Hlen.
  apply (bytes_keep _ mem mem' _ _ BY). intros i Hi. unfold bz in Hi. rewrite length_map in Hi.
  replace (bd + i) with (bd - 16 + (16 + i)) by lia.
  apply (KP (bd - 16) (dec_size (zs (slot_db pl)) + 16) (16 + i) Hin).
  - destruct (lib.U.Prog.HsKindB.in_blocks L A _ _ Hin) as (q & Hq & Eq).
    pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q _ HM Hq). lia.
  - unfold dec_size. lia.
Qed.

Lemma pd_keep : forall regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text
    L' A' regs' mem' md' peak' cnt',
  pd B API regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text ->
  slot_mid B API regs0 L0 A0 mem0 md0 cnt0 L' A' regs' mem' md' lenw Lam peak' cnt' bnd ->
  In (pt, slot_nn pl + 1) (user_blocks A') -> ptr_addr L' pt = text -> keeps B L A mem mem' 0 ->
  pd B API regs0 L0 A0 mem0 md0 pl cnt0 b L' A' regs' mem' md' lenw Lam peak' cnt' bnd bd pt text.
Proof.
  intros regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text L' A' regs' mem' md' peak' cnt'
    (MID & Hpt & Ept & H16 & FA0 & BYT & ANS & Hnn) MID' Hpt' Ept' KP.
  pose proof MID as (_ & (HM & _) & _ & _ & _ & LG & _).
  split; [exact MID'|]. split; [exact Hpt'|]. split; [exact Ept'|]. split; [exact H16|]. split; [exact FA0|].
  split.
  { apply (bytes_keep _ mem mem' _ _ BYT). intros i Hi. rewrite length_app, Nat2Z.inj_add, slot_db_length in Hi.
    cbn in Hi. pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ pt _ HM Hpt) as [Hr _]. rewrite Ept in Hr.
    apply (KP text (slot_nn pl + 1) i); [|lia | lia].
    rewrite <- Ept. unfold blocks. apply in_map_iff. exists (pt, slot_nn pl + 1). split; [reflexivity | exact Hpt]. }
  split; [exact (ans_keep L0 A0 L A mem mem' md pl text bd lenw Lam b bnd peak cnt _ HM LG KP ANS) | exact Hnn].
Qed.

Lemma pd_call : slot_env B API ->
  forall regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text Kc E L' A' regs' mem' md'
    peak' cnt',
  pd B API regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text ->
  call_post_k B MR Kc L A regs mem md E L' A' regs' mem' md' ->
  0 <= Kc <= SLOT_STACK - 48 ->
  (forall a, E a -> in_globals omx_G a \/ (0 <= a < alloc_ceiling /\ ~ in_img B a)) ->
  ublocks_kept L A A' (0, 0) -> keeps B L A mem mem' 0 ->
  (st_init_done A = true -> st_init_done A' = true) ->
  ledger B L' A' mem' Lam peak' cnt' (2 ^ 64 - 1) -> cnt0 <= cnt' <= cnt0 + 100 ->
  res_ok_slots A' bnd -> ro_agree (ms_segs B) mem' ->
  pd B API regs0 L0 A0 mem0 md0 pl cnt0 b L' A' regs' mem' md' lenw Lam peak' cnt' bnd bd pt text.
Proof.
  intros ENV regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text Kc E L' A' regs' mem' md'
    peak' cnt' PD CP HK HE UK KP HI LG' HC' RES' RA'.
  pose proof PD as (MID & Hpt & Ept & _).
  pose proof MID as (_ & (HM & _) & _).
  pose proof CP as (_ & _ & _ & _ & PA & _).
  assert (Hpt' : In (pt, slot_nn pl + 1) (user_blocks A')) by exact (ub_keep B API L A mem md A' HM UK _ _ Hpt).
  apply (pd_keep regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text L' A' regs' mem' md'
    peak' cnt' PD); [| exact Hpt' | rewrite (PA _ _ Hpt Hpt'); exact Ept | exact KP].
  eapply mid_call; [exact ENV | exact MID | exact CP | exact HK | exact HE | | exact HI | exact LG' | exact HC' |
    exact RES' | exact RA'].
  intros q k _ Hq. exact (ub_keep B API L A mem md A' HM UK q k Hq).
Qed.

Lemma ro_munch : forall W m m', ro_agree (ms_segs B) m -> lib.Lib.Frame.munch W m m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside W a -> lib.Lib.Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) ->
  ro_agree (ms_segs B) m'.
Proof.
  intros W m m' H HM HW a Ha. destruct (kb_outside_dec W (bv_unsigned a)) as [Ho|Ho].
  - pose proof (H a Ha) as E. unfold lib.Lib.Mem.mrd in *. rewrite (HM a Ho). exact E.
  - exfalso. pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    pose proof (HW (bv_unsigned a) Hr Ho) as E. rewrite lib.Lib.Step.Z_to_bv_lit_self in E. congruence.
Qed.

(* A segment that writes only the stack below the frame. *)
Lemma pd_A : slot_env B API ->
  forall regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text regs' mem' W,
  pd B API regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text ->
  lib.Lib.Frame.munch W mem mem' -> lib.Lib.Frame.wmono rsegs mem mem' ->
  (forall x, ~ (spZ regs0 - SLOT_STACK <= x < spZ regs0 - 48) -> lib.Lib.Frame.outside W x) ->
  getr regs' 2 = Z_to_bv 64 (spZ regs0 - 48) ->
  (forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs' (Z_to_bv 5 k) = getr regs0 (Z_to_bv 5 k)) ->
  ro_agree (ms_segs B) mem' ->
  pd B API regs0 L0 A0 mem0 md0 pl cnt0 b L A regs' mem' md lenw Lam peak cnt bnd bd pt text.
Proof.
  intros ENV regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text regs' mem' W
    PD MU WM HW R2' RS' RA'.
  pose proof PD as (MID & Hpt & Ept & _).
  pose proof MID as (SP & (HM & _) & _ & _ & _ & LG & HC & _).
  pose proof SP as (_ & Hlo & Hhi & _). pose proof alloc_ceiling_val. pose proof alloc_ceiling_lt.
  pose proof (slot_img_low B API ENV) as [ILi _]. pose proof ENV as (SEG & _).
  unfold SLOT_STACK in *.
  assert (LOW : forall x, 0 <= x < alloc_ceiling -> lib.Lib.Frame.outside W x) by (intros x Hx; apply HW; lia).
  assert (KP : keeps B L A mem mem' 0).
  { intros a k i Hin _ Hi. destruct (lib.U.Prog.HsKindB.block_low B API L A mem md a k i HM Hin Hi).
    apply (lib.U.Prog.HsKindB.mbyte_munch _ W mem mem'); [exact MU | lia | apply LOW; lia]. }
  apply (pd_keep regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text L A regs' mem' md
    peak cnt PD); [| exact Hpt | exact Ept | exact KP].
  eapply mid_A; [exact ENV | exact MID | exact MU | exact WM | | | | | exact R2' | exact RS' | | exact HC | exact RA'].
  - intros x Hx Hs. apply HW. unfold SLOT_STACK. exact Hs.
  - intros x Hx _. apply LOW. exact (ILi x Hx).
  - intros x Hx _. apply LOW. exact Hx.
  - intros q k i Hq Hi. apply LOW. pose proof MID as (_ & (_ & _ & _ & _ & _ & U & _) & _).
    destruct (U q k Hq) as [Hq1 Ep]. rewrite <- Ep.
    pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k HM Hq1). lia.
  - exact (lib.U.Prog.HsKindB.ledger_munch B API L A mem md mem' W Lam peak cnt _ HM LG MU LOW).
Qed.

Lemma step_c2 : slot_env B API -> check_as_written_contract B API -> check_reject_clean_contract ->
  forall regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L A regs mem md (P : config -> Prop),
  slot_start B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j -> slot_bnd b ->
  at_pd 0x13450 4 (fun _ => True) regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md ->
  (forall L' A' regs' mem' md', at_pd 0x13488 4 (fun _ => True) regs0 L0 A0 mem0 md0 pl cnt0 b L' A' regs' mem' md' ->
     SR (ms_segs B) (mkCfg (mkst regs' (Z_to_bv 64 0x13ef0) mem' (seg_rom (ms_segs B))) md') P) ->
  (forall L' A' regs' mem' md', at_pd 0x13464 4 (fun bd => bd <> 0) regs0 L0 A0 mem0 md0 pl cnt0 b L' A' regs' mem' md' ->
     SR (ms_segs B) (mkCfg (mkst regs' (Z_to_bv 64 0x139ac) mem' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 0x13690) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros ENV CAW CRC regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L A regs mem md P HS HB
    (lenw & Lam & peak & cnt & bnd & bd & pt & text & PD & Hcn & R1 & R8 & R9 & R10 & R11 & R12 & R18 & R19 & _) KC5 KC4.
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
  destruct (ans_caw L0 A0 mem pl text bd lenw Lam b bnd ANS) as (l & El & CAWA & HLam & Hl).
  destruct (ans_bnd L0 A0 mem pl text bd lenw Lam b bnd ANS Hnn) as (Bc & Bl & Bb).
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
  { apply (CAW L A regs mem md text (slot_db pl) slack bd l bnd Lam peak cnt (2 ^ 64 - 1)).
    - eapply mid_pre; [exact MID | unfold CAW_FRAME, ALLOC_STACK, SLOT_STACK; lia |]. rewrite R1. apply ret_lit; lia.
    - exact R10.
    - exact R11.
    - rewrite R12, El. reflexivity.
    - exact BYS.
    - apply slot_db_nozero.
    - rewrite Hdl, Hsl. replace (- (text + slot_nn pl + 1)) with (- (text + (slot_nn pl + 1))) by lia. lia.
    - rewrite Hdl. lia.
    - intros a Ha. unfold in_window, CAW_FRAME, ALLOC_STACK. rewrite Hsp. rewrite Hdl, Hsl in Ha. lia.
    - exists text, (slot_nn pl + 1). rewrite Hdl. split; [exact HinT | lia].
    - exact CAWA.
    - exact HLam.
    - exact LG.
    - exact RA.
    - exact RES.
    - apply (room_of8 b); [exact HB | exact Bc | lia | lia |]. rewrite Hdl. unfold b64_alloc_bound. lia.
    - apply (room_of8 b); [exact HB | exact Bc | cbn [sb_live sb_malloc]; lia | cbn [sb_bytes sb_malloc];
        rewrite Hdl; unfold b64_alloc_bound; lia |]. rewrite Hdl. lia. }
  intros c' (L' & A' & regs' & mem' & md' & w & s & -> & RA' & GK & INIT & FBw & FBs & DJw & DJs & CP & BLK & KP &
    UK & LG' & RES').
  rewrite R1.
  pose proof CP as (HM' & _ & _ & _ & PA & RP & _).
  assert (PD' : pd B API regs0 L0 A0 mem0 md0 pl cnt0 b L' A' regs' mem' md' lenw Lam peak cnt bnd bd pt text).
  { eapply pd_call; [exact ENV | exact PD | exact CP | unfold CAW_FRAME, ALLOC_STACK, SLOT_STACK; lia | | exact UK |
      exact KP | intros _; exact INIT | exact LG' | lia | | exact RA'].
    - intros a [Ha|Ha]; right.
      + destruct FBw as (H1 & H2 & H3). split; [lia|]. replace a with (w + (a - w)) by lia. apply H3. lia.
      + destruct FBs as (H1 & H2 & H3). split; [lia|]. replace a with (s + (a - s)) by lia. apply H3. lia.
    - eapply res_same_blocks; [exact RES | exact RES' | reflexivity | exact BLK]. }
  pose proof PD' as (MID' & _).
  pose proof MID' as (_ & REL' & R2' & RS' & FR' & LG2 & _ & _ & RA2 & _).
  destruct (kb_md B API L' A' mem' md' HM') as [Hh Hl'].
  assert (Hsp' : bv_unsigned (getr regs' 2) = spZ regs0 - 48)
    by exact (eq_trans (f_equal bv_unsigned (RP 2 ltac:(unfold callee_saved; lia))) Hsp).
  destruct FR' as ((_ & BY0) & _).
  cbn [slot_cells lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in BY0.
  apply lib.Lib.Mem.bytes_at_app in BY0 as (BYL & _).
  destruct (Z.eq_dec bd 0) as [Hb0|Hb0].
  - (* null result: sE0, check_3 inside *)
    assert (Ln : lenw = Z_to_bv 64 (2 ^ 64 - 1) /\ Lam = []).
    { destruct ANS as [(_ & _ & E1 & E2 & _)|(bs & _ & Hb & _)]; [split; assumption | exfalso; exact (Hb Hb0)]. }
    destruct Ln as [-> ->].
    pose proof LG2 as ((W1 & _) & _).
    assert (E19 : getr regs' 19 = Z_to_bv 64 0) by exact (eq_trans (RP 19 ltac:(unfold callee_saved; lia)) R19).
    eapply (kb_seg B regs' (Z_to_bv 64 0x13450) mem' md' _ P Hh Hl' SEG).
    + eapply sE0_run with (lo := spZ regs0 - 65536).
      * exact CRC.
      * exact (eq_trans (eq_trans (RP 18 ltac:(unfold callee_saved; lia)) R18) (f_equal (Z_to_bv 64) Hb0)).
      * rewrite Hsp'. exact BYL.
      * rewrite E19.
        apply word_mem_le8; [rewrite <- SEG; exact W1 | lia | lia | lia].
      * rewrite Hsp'. apply lib.U.Prog.HsKindB.stk_of_writable; [lia | lia |]. intros a Ha. rewrite <- SEG.
        pose proof REL' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SW). apply SW. left. unfold SLOT_STACK. lia.
      * rewrite Hsp'. lia.
      * rewrite Hsp'. lia.
    + intros ms' (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _).
      do 3 eexists. reflexivity.
    + intros R pc' m2 regs2 HQ HG.
      destruct HQ as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & EQ & MU & WM).
      injection EQ as ER Epc Em. subst R pc' m2.
      assert (KK : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs2 (Z_to_bv 5 k) = getr regs' (Z_to_bv 5 k))
        by (slot_kept HG).
      apply (KC5 L' A'). exists (Z_to_bv 64 (2 ^ 64 - 1)), [], peak, cnt, bnd, bd, pt, text.
      split.
      { apply (pd_A ENV regs0 L0 A0 mem0 md0 pl cnt0 b L' A' regs' mem' md' _ [] peak cnt bnd bd pt text regs2 m3
          [(bv_unsigned (getr regs' 2) - 16, bv_unsigned (getr regs' 2))] PD' MU WM).
        - intros x Hx. rewrite Hsp'. cbn [lib.Lib.Frame.outside]. split; [unfold SLOT_STACK in Hx; lia | exact I].
        - rewrite HG. exact R2'.
        - intros k Hk. rewrite (KK k Hk). exact (RS' k Hk).
        - apply (ro_munch _ mem' m3 RA2 MU). intros a Ha Ho. rewrite SEG. apply sa_ro_hi.
          destruct (Z_le_gt_dec (bv_unsigned (getr regs' 2) - 16) a); [|exfalso; apply Ho; cbn; split; [lia | exact I]].
          destruct (Z_lt_ge_dec a (bv_unsigned (getr regs' 2))); [|exfalso; apply Ho; cbn; split; [lia | exact I]].
          rewrite Hsp' in *. lia. }
      split; [lia|].
      split; [rewrite HG; reflexivity|].
      split; [rewrite HG; exact (eq_trans (RP 8 ltac:(unfold callee_saved; lia)) R8)|].
      split; [rewrite HG; exact (eq_trans (RP 9 ltac:(unfold callee_saved; lia)) R9)|].
      split; [rewrite HG; exact (eq_trans (RP 8 ltac:(unfold callee_saved; lia)) R8)|].
      split; [rewrite HG; exact (eq_trans (RP 18 ltac:(unfold callee_saved; lia)) R18)|].
      split; [rewrite HG; reflexivity|].
      split; [rewrite HG; exact (eq_trans (RP 18 ltac:(unfold callee_saved; lia)) R18)|].
      split; [rewrite HG; exact (eq_trans (RP 19 ltac:(unfold callee_saved; lia)) R19)|].
      exact I.
  - (* sE1, to the check_4 call *)
    destruct (ans_bd L0 A0 L' A' mem' md' pl text bd lenw Lam b bnd peak cnt _ HM' LG2
      (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PD'))))))) Hb0) as [Hbd1 Hbd2].
    eapply (kb_seg B regs' (Z_to_bv 64 0x13450) mem' md' _ P Hh Hl' SEG).
    + eapply sE1_run with (bd := bd) (lenw := lenw).
      * exact (eq_trans (RP 18 ltac:(unfold callee_saved; lia)) R18).
      * lia.
      * rewrite Hsp'. exact BYL.
    + intros ms' (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
      do 3 eexists. reflexivity.
    + intros R pc' m2 regs2 HQ HG.
      destruct HQ as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & EQ).
      injection EQ as ER Epc Em. subst R pc' m2.
      apply (KC4 L' A'). exists lenw, Lam, peak, cnt, bnd, bd, pt, text.
      split.
      { destruct PD' as (MID2 & REST). split; [|exact REST].
        apply (mid_regs B API regs0 L0 A0 mem0 md0 cnt0 L' A' regs' mem' md' _ _ _ _ _ regs2 MID2).
        - rewrite HG. reflexivity.
        - slot_kept HG. }
      split; [lia|].
      split; [rewrite HG; reflexivity|].
      split; [rewrite HG; exact (eq_trans (RP 8 ltac:(unfold callee_saved; lia)) R8)|].
      split; [rewrite HG; exact (eq_trans (RP 9 ltac:(unfold callee_saved; lia)) R9)|].
      split; [rewrite HG; exact (eq_trans (RP 8 ltac:(unfold callee_saved; lia)) R8)|].
      split; [rewrite HG; exact (eq_trans (RP 18 ltac:(unfold callee_saved; lia)) R18)|].
      split; [rewrite HG; reflexivity|].
      split; [rewrite HG; exact (eq_trans (RP 18 ltac:(unfold callee_saved; lia)) R18)|].
      split; [rewrite HG; exact (eq_trans (RP 19 ltac:(unfold callee_saved; lia)) R19)|].
      exact Hb0.
Qed.

End E.
