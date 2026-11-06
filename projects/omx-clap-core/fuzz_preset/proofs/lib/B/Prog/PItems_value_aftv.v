(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_head.v, with its module paths and module names changed; 1109 of its 1220 lines of code are new or changed and 1195 lines of the source are left out. *)
(* Theorem Labs, 2026-10: segment VALUE of parse_items' image-B walk, block AFTV.
   Proves no function (kind: segment lemma).
   THE BLOCK (the neutral listing, the internal file parse_items.fuzz_preset.asan-ubsan.s lines
   218-226; C preset_file.c:244-250), PI_O_AFTV up to the call of skip_ws, whose return site is PV_O_SEP:
     0x87d98 lbu a1,0(s8) ; 0x87d9c bnez a1    the ASan shadow test of v + 40 (s8 = shadow (v + 40))
     0x87da0 ld a1,0(s6) ; addi ; sd a1,0(s6)  v->n := n + 1 (s6 = v + 40), on BOTH arms, as the C does (the failed kid
                                                is freed with the rest)
     0x87dac li s5,-1                           the result register
     0x87db0 bnez a0 -> PI_O_EPI                a0 = -1: parse_value refused; the epilogue returns -1
     0x87db4 mv a0,s1 ; 0x87db8 jal skip_ws      a0 = q; the return site 0x87dbc is PV_O_SEP (PItems_value_sep.v's block)
   THEOREM pv_aftv_holds (section 5): PItems_value_pres.v pv_aftv_spec B ARx SK d CTX0 CW N from pv_sep_spec d CTX0 CW N
   (PItems_value_sep.v) and pi_epi_spec d (PItems_entry.v), at image B's listing (B_prog_listing / PL_prog_B / PI_prog_B) and PrhImg
   prh_img_B, all passed explicitly.
   THE CURSOR SET AND THE JOURNAL: the cursor set CW and the BUDGETED journal (pi_ajR ..
   WS0 at wbudget CW 0; the runs and skip_ws's call, YCbqGcallW.v aj_call_xW_spR, on the rebased empty-budget journal,
   YCbqGwild.ajournal_xw_rebaseR / ajournal_xw_unbase0R; pv_sep_spec and pi_epi_spec at WS0, the latter at
   P := wbudget CW 0). Read arm: pv_sep_pre's pi_led from the pre's ledger over the granted trace
   (PItems_ledk1.pik1_move_regt under pi_grant) and its batch-kit tail (the new member's capacity words, PItems_value_model.v
   pvm_ncaps_snoc; the completed slots' free order at S n, PItems_forder.v pis_fo_snoc, framed across the store and
   the call by PRH_PjOrder.pf_oitemsR_frame). Refused arm: the batch-kit post's OUTCOME clause is the pre's, its ledger the
   pre's move, and its partial free order PItems_forder.v pi_forder_at / pis_fo_item / pis_fo_slots_hb_nat against the
   pre's model.
   THE RUN: one symbolic state ss_av at PI_O_AFTV (the node's n field a writable region of atom 19 = v; a0 a literal per
   arm), run with the CALLER-FRAME runners PI_RUNFR / PI_RUNTOFR (the node may lie in a caller's fake frame; the write
   permission is av_awr). Refused arm: the run reaches PI_O_EPI, where pi_epi_spec gives the kit's post; its None arm is built
   here (the container with n + 1 members, the last the failed kid: PItems_shape.v pis_frame / pis_fd_next). Read arm: the
   run stops at the call; YCbqGcallW.v aj_call_xW_spR at e1 = PI_FRAME + e with skip_ws's text; at PV_O_SEP the new
   member is in the container (pis_snoc, pis_frame across the store and across the call), pi_cur and the node's bytes
   come from the call-keep statement and lemma (PItems_kept.v), and pv_sep_spec continues.
   CHECKS SHOWN NOT TAKEN:
     0x87d9c `bnez a1` (ASan report path, 0x88050) on the shadow byte of v + 40: decided inside the symbolic run by the SH
       entry (v, 0, 56) (av_sh_ok), from pv_aftv_pre's range_addressable v 56, v 8-aligned (pi_cont's pj_hdrR) and v off
       the shadow range (av_v_place).
     0x87db0 `bnez a0`: the result test, not a check; each arm's run decides it from pv_aftv_pre's a0 (0 read, -1 refused).
     No UBSan check branch lies in 0x87d98 .. 0x87db8 (the internal file B-U-TRAPS.md lists none between 0x87d8c and 0x87dd8).
   SECTION HYPOTHESES (section 5): LAWS (the engine's allocator laws, AR_laws_x at head length HL); SKW (skip_ws's text,
   lib/A/PRH_FnReader.v tskip_ws_specX, verbatim); HCURK (lib/B/Prog/PItems_kept.v pi_cur_kept_callR_stmt, the cursor
   call-keep statement over a world relation R, by name). The node's bytes across skip_ws are PItems_kept.v's lemma
   pi_node_kept_callR.
   THE RE-HIDING MOVE: the walk runs at the world relation wle' segs RZ_cf (YA0nH): the journal pi_ajR and the goal
   pi_goalR at wle', the runners PI_RUNFR / PI_RUNTOFR, the journal steps YCbqGwild.ajournal_xw_rebaseR /
   ajournal_xw_unbase0R, skip_ws's call by YCbqGcallW.aj_call_xW_spR at wle'. skip_ws's text concludes plain SRr at
   wle; av_callee_R lifts it (YA0nH.SRr_SRr', its journal by YCbqG.ajournal_xwR_mono). pi_epi_spec concludes SRr' at
   wle', which is the goal at PI_O_EPI.
   THE TRAVELLING FACTS (form (b), PItems_pres.v): memnorm of the overlay rides through each runner phase and the
   v->n store by YGcallMxmn.v memnorm_frame_of on the runner post's full frame_of (av_mn_run), and across skip_ws by its
   m-form keep (PRH_Base.v fQmn). pv_aftv_pre's position implication over tr0, its hull use and pi_live over tr0: the
   runs keep the allocator state, and skip_ws's text gives S' = S, so (read arm, where the hull use is over tr0 and the
   two make PItems_posb.pi_posb S Sc tr0) pi_posb_eq / pi_live_eq carry them to pv_sep_pre; the refused arm's post
   (the text's tpiP_Q, built through tpiP_Q_of_R) takes its live-request permutation, its position implication and its hull
   use (over the whole call's all-granted list) off them as they are, and its injected-reading conjunct is pv_aftv_pre's
   clause. skip_ws's text takes no memnorm and no count at entry (it allocates nothing); its fpre's frm_zero comes from
   pi_fpok.
   Numerals: PI_O_AFTV, PI_O_EPI, PV_O_SEP and PI_FRAME are LENGTHs (byte offsets inside the body, the frame); 8, 16, 24,
   32, 40, 48, 56, 104, 144 are LENGTHs (node field and frame offsets); 2 ^ 64 - 1 is the WORD -1; 2 ^ 44, 2 ^ 47, 2 ^ 54,
   4096 and 16560 are DERIVED / LENGTH bounds (shadow span, address space, capacity, page, STK_parse_items' leaf part);
   register and atom indices are DERIVED (the engine's numbering). No ADDRESS: every pc is VAL A_TEXT + PIAT PI_O_*. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YC80xf YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YK06 YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
PItems_defs PItems_pres PItems_agr PItems_value_pres PItems_value_model PItems_kept PItems_shape S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_posb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_forder PItems_ledk1 PvB_Frees.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================================================================================== *)
(* 1. THE SYMBOLIC STATE AT PI_O_AFTV *)
Definition av_Bx : sv := SOff 26 0.
Definition av_sregs (a0 : Z) : list sv :=
  sr_set (sr_set (sr_set sr_atoms 22%bv (SOff 19 40)) 24%bv (pi_shx (SOff 19 40))) 10%bv (SLit a0).
Definition av_region (c : Z) : YP09.region :=
  YP09.mkRegion (Some 19%nat) 40 48 40 48 [YP09.mkChunk 40 (CVal 8 (SOff 32 c))].
Definition av_smem : smem := [av_region 0].
Definition av_facts : list (nat * afact) :=
 [ (19%nat, mkAF 4096 (2 ^ 47 - 56) 3); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 (2 ^ 54) 0) ].
Definition ss_av (a0 pc : Z) : sstate := mkSS pc (av_sregs a0) av_smem None (mkFacts av_facts [] []).
Definition av_SH : list shent := [mkSHE 19 0 56].

Section st. Context {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation VAL := (@pa_val rc B_prog_listing (@PI_prog_B rc)).

Lemma av_st_ok : forall (fy : YK11.FPState) (W : world SEGS) memc (regs : bvmap 5 word) v n a0 off,
  getr regs 19 = w64 v -> getr regs 22 = w64 (v + 40) -> getr regs 24 = w64 (pi_sh (v + 40)) ->
  getr regs 26 = w64 SHADOW_OFF -> getr regs 10 = w64 a0 ->
  4096 <= v <= 2 ^ 47 - 56 -> v mod 8 = 0 -> 0 <= n <= 2 ^ 54 ->
  val_mem SEGS (mrestrict (w_H W) memc) (v + 40) 8 n ->
  (forall x, v + 40 <= x < v + 48 -> writable_at SEGS (mrestrict (w_H W) memc) x) ->
  st_ok_pi (fx := fy) SEGS VAL (Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) (Ereg regs [Z_to_bv 64 n]))
    (ss_av a0 off) (restrict (w_H W) (@YK11.mkst fy regs (Z_to_bv 64 (VAL A_TEXT + off)) memc (seg_rom SEGS))).
Proof.
intros fy W memc regs v n a0 off H19 H22 H24 H26 H10 Hv Hv8 Hn Vn Hwr.
set (E := Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) (Ereg regs [Z_to_bv 64 n])).
assert (E19 : ew E 19 = Z_to_bv 64 v) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 n) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U19 : bv_unsigned (ew E 19) = v) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = n) by (rewrite E32; apply unsigned_lit_small; lia).
assert (D19 : forall c, 0 <= v + c < 2 ^ 64 -> sv_denot E (SOff 19 c) = Z_to_bv 64 (v + c)).
{ intros c Hc. rewrite denot_lit_U, U_SOff, U19, zcanon_id by (unfold M64; lia). reflexivity. }
rewrite (restrict_mkst_fx (fx := fy)). unfold ss_av.
apply (pa_entry_st_ok_full (fx := fy) (L := B_prog_listing) (PI := PI_prog_B)).
- unfold av_sregs.
  apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg| |]| |]| |];
  try (intros X; discriminate X).
  + rewrite H22, D19 by lia. reflexivity.
  + rewrite H24, (pi_denot_shx E (SOff 19 40) SHADOW_OFF (v + 40) (D19 40 ltac:(lia)) E26) by (unfold SHADOW_OFF; lia).
    reflexivity.
  + rewrite H10. reflexivity.
- vm_compute. reflexivity.
- unfold av_smem, av_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite U19.
  split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ v 40 8 (SOff 32 0) n);
  [rewrite denot_lit_U, U_SOff, U32, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | exact Vn].
- apply pairwise_disjoint_of_extents. unfold av_smem, av_region. cbn [map]. unfold extent_of_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19.
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok av_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U19, U26, U32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

Lemma av_sh_ok : forall (W : world SEGS) memc (regs : bvmap 5 word) v n,
  getr regs 19 = w64 v -> getr regs 26 = w64 SHADOW_OFF ->
  4096 <= v <= 2 ^ 47 - 56 -> (v + 56 <= SHADOW_OFF \/ kHighMemBeg <= v) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v 56 ->
  sh_ok SEGS av_Bx av_SH (Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) (Ereg regs [Z_to_bv 64 n]))
    (mrestrict (w_H W) memc).
Proof.
intros W memc regs v n H19 H26 Hv Hsh Hra.
set (E := Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) (Ereg regs [Z_to_bv 64 n])).
assert (E19 : ew E 19 = Z_to_bv 64 v) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
unfold av_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) memc E av_Bx 19 v 56 v 0 56 Hra);
[unfold av_Bx; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
| rewrite (U_atom E 19 v E19) by lia; reflexivity | lia | lia
| intros x Hx; unfold kHighMemBeg, SHADOW_OFF in *; lia].
Qed.

(* the store the run makes: v + 40 now holds n + 1, every other byte of the reader is kept *)
Definition av_F (v x : Z) : Prop := 0 <= x < 2 ^ 64 /\ ~ (v + 40 <= x < v + 48).

Lemma av_store_post : forall {fy : YK11.FPState} E (Wc : world SEGS) memc memr v n,
  bv_unsigned (ew E 19) = v -> ew E 32 = Z_to_bv 64 n -> 0 <= n <= 2 ^ 54 ->
  frame_of E av_smem (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memr) ->
  Forall (region_ok SEGS E (mrestrict (w_H Wc) memr)) [av_region 1] ->
  pi_agr (av_F v) (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memr) /\
  val_mem SEGS (mrestrict (w_H Wc) memr) (v + 40) 8 (n + 1) /\
  (forall x, v + 40 <= x < v + 48 -> writable_at SEGS (mrestrict (w_H Wc) memr) x).
Proof.
intros fy E Wc memc memr v n U19 E32 Hn HFr HR.
assert (U32 : bv_unsigned (ew E 32) = n) by (rewrite E32; apply unsigned_lit_small; lia).
apply Forall_inv in HR.
split; [|split].
- intros a [Ha Hn']. apply HFr. rewrite unsigned_lit_small by lia. intros (r & Hin & Hr).
  unfold av_smem in Hin. destruct Hin as [<- | []]. unfold av_region in Hr.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U19 in Hr. apply Hn'. lia.
- pose proof (pi_field SEGS E _ 19%nat v _ _ _ _ _ 40 8 (SOff 32 1) (n + 1) HR U19 ltac:(left; reflexivity)
    ltac:(rewrite denot_lit_U, U_SOff, U32, zcanon_id by (unfold M64; lia); reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
  exact VQ.
- intros x Hx. destruct HR as (_ & _ & Hw & _). unfold av_region in Hw.
  cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi] in Hw. rewrite U19 in Hw.
  replace x with (v + (x - v)) by lia. apply Hw. lia.
Qed.

End st.

(* ================================================================================================== *)
(* 2. PURE AND SHAPE LEMMAS *)

(* the cursor after skip_ws: its rest is skip of the rest before *)
Lemma av_skip_rest : forall tb text len pc, Z.of_nat (length tb) = len ->
  rest_atR tb text (text + len - Z.of_nat (length (skip (rest_atR tb text pc)))) = skip (rest_atR tb text pc).
Proof.
intros tb text len pc Hl.
set (r := rest_atR tb text pc).
destruct (pvm_suf_skip r) as (u & Hu).
assert (Hr : tb = (firstn (Z.to_nat (pc - text)) tb ++ u) ++ skip r).
{ rewrite <- app_assoc, <- Hu. unfold r, rest_atR. symmetry. apply firstn_skipn. }
set (P := firstn (Z.to_nat (pc - text)) tb ++ u) in Hr.
assert (HL : length tb = (length P + length (skip r))%nat) by (rewrite Hr at 1; apply length_app).
unfold rest_atR. replace (Z.to_nat (text + len - Z.of_nat (length (skip r)) - text)) with (length P) by lia.
rewrite Hr at 1. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

(* the refused value: d < MAXD, else the whole call refuses at once with no event, so D0 = [], and the kid slot's
   array block (n < cap) is in D0 (the ledger move at any granted trace gt) *)
Lemma av_d_lt : forall d o x0 ok0 tr0 f n cap acc nm Lam peak cnt fail ran most gt D0 Lamc peakc cntc failc ranc
    kids keys D,
  pv_run_after d o x0 ok0 tr0 f n cap acc nm None ->
  rd_ledger_move Lam peak cnt fail ran most ok0 gt tr0 D0 Lamc peakc cntc failc ranc ->
  Permutation D0 (pi_sblk o kids keys cap ++ D) -> (n < cap)%nat -> (d < PjGrammar.MAXD)%nat.
Proof.
intros d o x0 ok0 tr0 f n cap acc nm Lam peak cnt fail ran most gt D0 Lamc peakc cntc failc ranc kids keys D HR HL HP
  Hn.
destruct (Nat.lt_ge_cases d PjGrammar.MAXD) as [H|H]; [exact H|exfalso].
specialize (HR []). rewrite app_nil_r in HR.
unfold jr_items, jr_cont in HR.
replace (Nat.ltb PjGrammar.MAXD (S d)) with true in HR by (symmetry; apply Nat.ltb_lt; lia).
unfold jrefuse in HR. injection HR as E1 E2. subst tr0.
unfold rd_ledger_move in HL. destruct HL as (_ & _ & _ & _ & _ & Hlen & _). cbn [nliveR] in Hlen.
destruct D0 as [|b D0']; [|cbn [length] in Hlen; lia].
apply Permutation_nil in HP. apply app_eq_nil in HP as [HP _].
unfold pi_sblk, kids_blkR in HP. destruct (Z.of_nat cap =? 0) eqn:E; [apply Z.eqb_eq in E; lia | discriminate HP].
Qed.

Lemma av_ty : forall o : bool, (if o then 6 else 5) = 5 + pis_oz o.
Proof. intros [|]; reflexivity. Qed.

Section shp. Context {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).

(* PItems_shape.v's open container back as the half-built container (PItems_value_model.v pvm_cont_open's converse) *)
Lemma av_cont_of_open : forall m lblk (o : bool) v kids keys n cap acc Di,
  pis_open SEGS m lblk v o 0 kids keys (Z.of_nat cap) (Z.of_nat n) (map snd acc) (map fst acc) Di ->
  n = length acc ->
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) m lblk o v kids keys n cap acc Di.
Proof.
intros m lblk o v kids keys n cap acc Di (HN & HA & Hh & Hs & Hk & Hi) Hn.
destruct Hs as (Hty & (Hnc & Hc54) & Hc0 & Hcp).
split; [rewrite av_ty; exact Hh|]. split; [exact Hn|]. split; [lia|]. split; [lia|].
split.
{ destruct cap as [|c].
  - left. split; [reflexivity|]. destruct (Hc0 eq_refl) as (Hk0 & Hy0). split; [exact Hk0|].
    destruct o; [apply Hy0; reflexivity | apply Hk; reflexivity].
  - right. split; [lia|]. destruct (Hcp ltac:(lia)) as (Hl1 & Hl2). split; [exact Hl1|].
    intros Ho. subst o. apply Hl2. reflexivity. }
split; [exact Hk|]. split; [exact (pis_nodup_r _ _ _ HN)|].
split; [intros b x Hb; apply (HA b x); apply in_or_app; right; exact Hb|].
destruct o; unfold pis_items in Hi; [destruct Hi as (_ & Hm); rewrite pis_combine_map in Hm; exact Hm | exact Hi].
Qed.

(* a byte the reader sees writable and that is no image byte is in memory *)
Lemma av_wr_some : forall (m : word -> option byte) x, 0 <= x < 2 ^ 64 -> ~ in_img SEGS x ->
  writable_at SEGS m x -> exists b, m (Z_to_bv 64 x) = Some b.
Proof.
intros m x Hx Hn Hw. unfold writable_at, wview in Hw. destruct (m (Z_to_bv 64 x)) as [b|]; [exists b; reflexivity|].
exfalso. apply Hw. cbn [Z.of_N]. rewrite unsigned_lit_small by lia. rewrite (find_segment_none SEGS x Hn). reflexivity.
Qed.

(* two readers that agree on a byte that is no image byte: the same byte, and writable stays writable *)
Lemma av_same_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) x, 0 <= x < 2 ^ 64 ->
  ~ in_img SEGS x -> aview SEGS H' m' x = aview SEGS H m x -> pis_same SEGS (mrestrict H m) (mrestrict H' m') x.
Proof.
intros H H' m m' x Hx Hn Ha.
assert (Hm : mbyte SEGS (mrestrict H' m') x = mbyte SEGS (mrestrict H m) x) by exact (mbyte_of_aview SEGS H H' m m' x Ha).
split; [exact Hm|]. intros Hw. destruct (av_wr_some _ x Hx Hn Hw) as (b & Hb).
assert (Hm0 : mbyte SEGS (mrestrict H m) x = Some b) by (unfold mbyte; rewrite Hb; reflexivity).
rewrite Hm0 in Hm. unfold mbyte in Hm. destruct (mrestrict H' m' (Z_to_bv 64 x)) as [b'|] eqn:E.
- unfold writable_at, wview. rewrite E. discriminate.
- rewrite (seg_rom_none SEGS x Hx Hn) in Hm. discriminate.
Qed.

End shp.

(* ================================================================================================== *)
(* 3. WHERE THE NODE IS, AND WHAT THE STORE INTO v->n KEEPS *)
Section stl. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_B.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.

Lemma av_rs : forall n, 0 <= n -> 1 <= req_size n /\ n <= req_size n.
Proof. exact req_size_pos. Qed.
(* the request size of a nonnegative size, as two facts (the instance of cf_head is fixed before lia runs) *)
Ltac av_rq n := let RQ := fresh "RQ" in pose proof (av_rs n) as RQ; specialize (RQ ltac:(lia)); destruct RQ.

(* PRH_FnReader.v prhReader_at's four places of the node, read off at one state: bounds, off the shadow, no image byte *)
Lemma av_v_place : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own (regs0 : bvmap 5 word) e v,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs0 e v 56 -> YM05.alloc_ceiling <= spZ regs0 -> spZ regs0 + e <= 2 ^ 47 ->
  4096 <= v /\ v + 56 <= 2 ^ 47 /\ (v + 56 <= SHADOW_OFF \/ kHighMemBeg <= v) /\
  (forall x, v <= x < v + 56 -> ~ in_img SEGS x).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs0 e v HAR HLED Hat Hsp He.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@cf_head_nonneg cp) as Hh0.
assert (HB : forall b m, In (b, m) (ablocks B ly S) -> b <= v -> v + 56 <= b + req_size m ->
  4096 <= v /\ v + 56 <= 2 ^ 47 /\ (v + 56 <= SHADOW_OFF \/ kHighMemBeg <= v) /\
  (forall x, v <= x < v + 56 -> ~ in_img SEGS x)).
{ intros b m Hin H1 H2. destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m HAR Hin) as (_ & H4096 & Hc & Happ & _).
  split; [|split; [|split]].
  - lia.
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
  - intros x Hx. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b m x HAR Hin). lia. }
destruct Hat as [(a & k & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
- destruct HLED as (_ & _ & HF & _). pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk & Hblk & _).
  cbn [fst snd] in Hk, Hblk. apply (HB _ _ Hblk); [lia|]. av_rq (k + cf_head). lia.
- apply (HB _ _ Hin); [lia|]. destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m HAR Hin) as (_ & _ & _ & Happ & _).
  unfold req_size. destruct (Z.eqb_spec m 0); lia.
- destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfa).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  split; [|split; [|split]].
  + lia.
  + unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
  + unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
  + intros x Hx. apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos x HAR Hin). lia.
- split; [|split; [|split]].
  + lia.
  + lia.
  + right. unfold kHighMemBeg. lia.
  + intros x Hx Him. pose proof (pa_segs_low (PAImg := PI_prog_B) x Him). unfold kLowMemEnd in *. lia.
Qed.

(* a block a reader call allocated (rd_blocks_move: not a block of the entry state) is apart from the node, which
   the caller placed at the entry state (rd_pre's prhPv_node), outside the caller's window *)
Lemma av_new_apart : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own (regs0 : bvmap 5 word) e v
    lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc mostc ownc D0 tr0 x d,
  ARx lyc Sc Hpc Wc memc mdc -> layout_le (length (st_secs S)) ly lyc ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> prhReader_at B ly S Lam regs0 e v 56 ->
  (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> incl D0 Lamc ->
  rd_blocks_move B ly S lyc Sc D0 tr0 x d ->
  pj_apartR D0 v.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own regs0 e v lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc
  ownc D0 tr0 x d HAR HLY HL0 Hat Hwin HLc HI HBM [a k] y Hin Hy Hyv.
unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct HLc as (_ & _ & HFc & _). pose proof (proj1 (Forall_forall _ _) HFc (a, k) (HI _ Hin)) as (Hk0 & Hab & _).
cbn [fst snd] in Hk0, Hab.
destruct HBM as (Hnew & Hperm & Hfr & _). pose proof (Hnew a k Hin) as Hnot.
av_rq (k + cf_head).
assert (Hold : forall b m, In (b, m) (ablocks B ly S) -> b <= v -> v + 56 <= b + req_size m -> False).
{ intros b m Hb H1 H2.
  assert (Hbc : In (b, m) (ablocks B lyc Sc))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; exact Hb).
  assert (Hne : (a - cf_head, k + cf_head) <> (b, m)) by (intros E; rewrite E in Hnot; exact (Hnot Hb)).
  pose proof (sep_blocks_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HAR Hab Hbc Hne) as HD.
  unfold zdisjoint in HD. cbn [fst snd] in HD. lia. }
destruct Hat as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hin' & _ & H1 & H2) | [(cid & pos & Hin' & H1 & H2) | (H1 & H2)]]].
- destruct HL0 as (_ & _ & HF0 & _). pose proof (proj1 (Forall_forall _ _) HF0 (a', k') Hin') as (Hk' & Hab' & _).
  cbn [fst snd] in Hk', Hab'. apply (Hold _ _ Hab'); [lia|]. av_rq (k' + cf_head). lia.
- apply (Hold _ _ Hin'); [lia|]. unfold req_size. destruct (Z.eqb_spec m 0); lia.
- assert (Hfc : In (cid, pos) (frames Sc)) by exact (Permutation_in _ (Permutation_sym Hfr) Hin').
  pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ cid pos HAR Hab Hfc) as HD.
  unfold zdisjoint in HD. cbn [fst snd] in HD.
  assert (EF : frame_addr lyc cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct HLY as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  rewrite EF in HD. lia.
- lia.
Qed.

(* the head word of a harness block of the ledger is apart from the node's n field, wherever the node is *)
Lemma av_head_apart : forall lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc mostc ownc
    (regs0 : bvmap 5 word) e v,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  prhReader_at B lyc Sc Lamc regs0 e v 56 -> YM05.alloc_ceiling <= spZ regs0 ->
  forall a k y, In (a, k) Lamc -> a - cf_head <= y < a - cf_head + 8 -> ~ (v + 40 <= y < v + 48).
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc regs0 e v HAR HLc Hat Hsp a k y Hin Hy Hyv.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct HLc as (_ & HND & HF & _). pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk0 & Hab & _).
cbn [fst snd] in Hk0, Hab.
av_rq (k + cf_head).
destruct Hat as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hin' & Hnl & H1 & H2) | [(cid & pos & Hin' & H1 & H2) | (H1 & H2)]]].
- destruct (Z.eq_dec a a') as [<- | Hne]; [lia|].
  pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hab' & _). cbn [fst snd] in Hk', Hab'.
  assert (Hd : (a - cf_head, k + cf_head) <> (a' - cf_head, k' + cf_head)) by (intros E; injection E; lia).
  pose proof (sep_blocks_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HAR Hab Hab' Hd) as HD.
  unfold zdisjoint in HD. cbn [fst snd] in HD. av_rq (k' + cf_head). lia.
- assert (Hd : (a - cf_head, k + cf_head) <> (b, m)).
  { intros E. injection E as E1 E2. apply Hnl. replace (b + cf_head) with a by lia. replace (m - cf_head) with k by lia.
    exact Hin. }
  pose proof (sep_blocks_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HAR Hab Hin' Hd) as HD.
  unfold zdisjoint in HD. cbn [fst snd] in HD. av_rq m. lia.
- pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ cid pos HAR Hab Hin') as HD.
  unfold zdisjoint in HD. cbn [fst snd] in HD. lia.
- destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hab) as (_ & _ & Hc & _). lia.
Qed.

(* the ledger reads the statics (image bytes) and the head words: none is a byte of the n field *)
Lemma av_ledger_store : forall lyc Sc Hpc (Wc : world SEGS) memc memr mdc Lamc peakc cntc failc ranc mostc ownc
    (regs0 : bvmap 5 word) e v,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  prhReader_at B lyc Sc Lamc regs0 e v 56 -> YM05.alloc_ceiling <= spZ regs0 ->
  (forall x, v <= x < v + 56 -> ~ in_img SEGS x) ->
  pi_agr (av_F v) (rdW Wc memc) (rdW Wc memr) ->
  prh_ledger B lyc Sc Hpc Wc memr Lamc peakc cntc failc ranc mostc ownc.
Proof.
intros lyc Sc Hpc Wc memc memr mdc Lamc peakc cntc failc ranc mostc ownc regs0 e v HAR HLc Hat Hsp Hni HA.
pose proof (av_head_apart lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc regs0 e v HAR HLc Hat Hsp)
  as HHA.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct HLc as (HG & HND & HB & HP).
assert (FS : forall a, Exists (in_zr a) prh_pst -> av_F v a).
{ intros a Ha. pose proof (pst_in_img_B a Ha) as Hi. pose proof (pa_segs_low (PAImg := PI_prog_B) a Hi) as Hl.
  split; [unfold kLowMemEnd in Hl; lia|]. intros Hv. exact (Hni a ltac:(lia) Hi). }
split; [|split; [exact HND|split; [|exact HP]]].
- destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & M6) & (G7 & M7) & GR).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ M6) (conj (conj _ M7) GR))))))).
  + apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ HA); [|exact G1]. intros kk Hk. apply FS.
    unfold prh_pst. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  + apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ HA); [|exact G2]. intros kk Hk. apply FS.
    unfold prh_pst. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  + apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ HA); [|exact G3]. intros kk Hk. apply FS.
    unfold prh_pst. do 2 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  + apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ HA); [|exact G4]. intros kk Hk. apply FS.
    unfold prh_pst. do 3 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  + apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ HA); [|exact G5]. intros kk Hk. apply FS.
    unfold prh_pst. do 4 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  + apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ HA); [|exact G6]. intros kk Hk. apply FS.
    unfold prh_pst. do 5 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  + apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ HA); [|exact G7]. intros kk Hk. apply FS.
    unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Forall_forall. intros [a k] Hin. pose proof (proj1 (Forall_forall _ _) HB (a, k) Hin) as (K0 & Kin & Khp & Kal & Kv).
  cbn [fst snd] in *.
  refine (conj K0 (conj Kin (conj Khp (conj Kal _)))).
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Kin) as (_ & B2 & B3 & _).
  pose proof asan_consts as (AC1 & _). av_rq (k + cf_head).
  apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ HA); [|exact Kv]. intros kk Hk. split; [lia|].
  apply (HHA a k); [exact Hin | lia].
Qed.

(* the ledger is a reader predicate: it survives a memory whose reader agrees pointwise *)
Lemma av_ledger_pw : forall ly S Hp (W : world SEGS) m m' Lam peak cnt fail ran most own,
  (forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
  prh_ledger B ly S Hp W m Lam peak cnt fail ran most own -> prh_ledger B ly S Hp W m' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W m m' Lam peak cnt fail ran most own Heq (HG & HND & HB & HP).
assert (HA : pi_agr (fun _ => True) (rdW W m) (rdW W m')) by (intros a _; apply Heq).
split; [|split; [exact HND|split; [|exact HP]]].
- destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & M6) & (G7 & M7) & GR).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ M6) (conj (conj _ M7) GR)))))));
    apply (pi_val_agr SEGS (fun _ => True) _ _ _ _ _ HA); first [intros; exact I | assumption].
- apply Forall_forall. intros [a k] Hin. pose proof (proj1 (Forall_forall _ _) HB (a, k) Hin) as (K0 & Kin & Khp & Kal & Kv).
  refine (conj K0 (conj Kin (conj Khp (conj Kal _)))).
  apply (pi_val_agr SEGS (fun _ => True) _ _ _ _ _ HA); [intros; exact I | exact Kv].
Qed.

(* The kit's post reads memory only through the reader (PItems_head.v cl_post_stable's statement; proved pointwise, through
   PItems_agr.v's agreement lemmas and the batch-kit frames PRH_PjOrder.pj_foR_frame / PvB_Frees.pvf_ncap_frame, with no
   extensionality). The post is read through tpiP_R_of and built through tpiP_Q_of_R; only the ledger and the arm read
   memory *)
Lemma av_post_stable : forall ly0 S0 dd (o : bool) tb text len p q v Lam peak cnt fail ran most own kr,
  pi_Qstable (rc := rc) (L := B_prog_listing) (PA := PI_prog_B)
    (pi_post (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
       B ly0 S0 dd o tb text len p q v Lam peak cnt fail ran most own kr).
Proof.
intros ly0 S0 dd o tb text len p q v Lam peak cnt fail ran most own kr ly S Hp W regs m m' md md' Heq HQ.
assert (HA : pi_agr (fun _ => True) (rdW W m) (rdW W m')) by (intros a _; apply Heq).
assert (SAME : forall x, pis_same SEGS (rdW W m) (rdW W m') x).
{ intros x. split; [unfold mbyte; rewrite (HA x I); reflexivity|]. intros Hw. exact (pi_wr_agr SEGS _ _ _ x HA I Hw). }
unfold pi_post in HQ |- *.
eapply tpiP_R_of in HQ.
destruct HQ as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & HR).
(* the free order of the node at the reader: pj_foR reads the node's header and its blocks *)
assert (FOk : forall nn F, PRH_PjOrder.pj_foR SEGS (rdW W m) (prh_lin Lam') nn v D F ->
  PRH_PjOrder.pj_foR SEGS (rdW W m') (prh_lin Lam') nn v D F).
{ intros nn F HF. apply (PRH_PjOrder.pj_foR_frame SEGS nn _ _ _ _ v D F HF);
    [exact (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HF) | intros x _; exact (SAME x)]. }
pose proof (tpiP_arm HR) as Hm.
eapply tpiP_Q_of_R.
refine {| tpiP_run := tpiP_run HR; tpiP_ledger := av_ledger_pw _ _ _ _ _ _ _ _ _ _ _ _ _ Heq (tpiP_ledger HR);
  tpiP_room := tpiP_room HR; tpiP_hull := tpiP_hull HR; tpiP_live := tpiP_live HR; tpiP_pos := tpiP_pos HR;
  tpiP_outcome := tpiP_outcome HR; tpiP_injected := tpiP_injected HR; tpiP_ledger_move := tpiP_ledger_move HR;
  tpiP_blocks_move := tpiP_blocks_move HR; tpiP_bytes := tpiP_bytes HR; tpiP_lsum := tpiP_lsum HR;
  tpiP_arm := _ |}.
destruct res as [[t r] |].
- destruct Hm as (H10 & HFO & HIN & HND & HNC & HLS). split; [exact H10|].
  split; [intros Hh nn Hnn; destruct (HFO Hh nn Hnn) as (F & HF & HFm); exists F; exact (conj (FOk nn F HF) HFm)|].
  destruct HIN as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG & Hdqt & Hd032).
  split; [|split; [exact (pi_nodeR_agr SEGS t (fun _ => True) _ _ _ _ _ HA (fun _ _ => I) HND)|]].
  2: { split; [|exact HLS].
       exact (PvB_Frees.pvf_ncap_frame SEGS t (w_H W) m (rdW W m') (prh_lin Lam') v D HND (fun x _ => SAME x) HNC). }
  refine (conj _ (conj _ (conj _ (conj _ (conj Hq8 (conj Ht0 (conj Htl (conj Hple (conj Hlen (conj _ (conj Hdqt Hd032))))))))))).
  + exact (pi_val_agr SEGS _ _ _ _ _ _ HA (fun _ _ => I) Vp).
  + exact (pi_val_agr SEGS _ _ _ _ _ _ HA (fun _ _ => I) Ve).
  + exact (pi_val_agr SEGS _ _ _ _ _ _ HA (fun _ _ => I) Vd).
  + exact (pi_rw_agr SEGS _ _ _ _ _ HA (fun _ _ => I) Hrw).
  + exact (pi_garr8_agr SEGS _ _ _ _ _ HA (fun _ _ => I) HG).
- destruct Hm as (H10 & HFO & HAF & HFD). split; [exact H10|].
  split; [intros Hh nn Hnn; destruct (HFO Hh nn Hnn) as (F & HF & HFm); exists F; exact (conj (FOk nn F HF) HFm)|].
  split; [|exact (pis_fd_frame SEGS _ _ _ _ _ _ _ HFD (fun a k _ H => H) (fun x _ => SAME x))].
  destruct HAF as (p' & d' & Hp' & Hd' & Vp & Ve & Vd & Hrw). exists p', d'.
  refine (conj Hp' (conj Hd' (conj _ (conj _ (conj _ _))))).
  + exact (pi_val_agr SEGS _ _ _ _ _ _ HA (fun _ _ => I) Vp).
  + exact (pi_val_agr SEGS _ _ _ _ _ _ HA (fun _ _ => I) Ve).
  + exact (pi_val_agr SEGS _ _ _ _ _ _ HA (fun _ _ => I) Vd).
  + exact (pi_rw_agr SEGS _ _ _ _ _ HA (fun _ _ => I) Hrw).
Qed.

End stl.



(* ================================================================================================== *)
(* 4. THE CALL'S SMALL FACTS *)
Section cs. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_B.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* two readers that agree on a set F agree, on F, as pis_same *)
Lemma av_same_agr : forall F (m m' : word -> option byte) x, pi_agr F m m' -> F x -> pis_same SEGS m m' x.
Proof.
intros F m m' x HA Hx. split; [unfold mbyte; rewrite (HA x Hx); reflexivity|].
intros Hw. exact (pi_wr_agr SEGS F m m' x HA Hx Hw).
Qed.

(* the slot regions and the members' blocks of an open container lie in the call's blocks *)
Lemma av_ifoot_in : forall (o : bool) kids keys (cap L : nat) Di' x (D : list (Z * Z)),
  (0 < cap)%nat -> (L <= cap)%nat ->
  (forall b, In b (pi_sblk o kids keys cap) -> In b D) -> (forall b, In b Di' -> In b D) ->
  pis_ifoot o kids keys (Z.of_nat L) Di' x -> exists b, In b D /\ pj_holdsR b x.
Proof.
intros o kids keys cap L Di' x D Hc HL HS HD [Hx | [(Ho & Hx) | (b & Hb & Hx)]].
- exists (kids, 56 * Z.of_nat cap). split; [apply HS; unfold pi_sblk, kids_blkR|unfold pj_holdsR; cbn [fst snd]; lia].
  apply in_or_app. left. replace (Z.of_nat cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity.
- subst o. exists (keys, 8 * Z.of_nat cap). split; [apply HS; unfold pi_sblk, kids_blkR, keys_blkR|unfold pj_holdsR; cbn [fst snd]; lia].
  apply in_or_app. right. replace (Z.of_nat cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. left. reflexivity.
- exists b. split; [exact (HD b Hb) | exact Hx].
Qed.

(* the store into v + 40 is a write the caller-frame runner admits: the node is in FP, and lies in a live block, a
   live fake frame of the entry state, or the caller's window (prhReader_at at the current state) *)
Lemma av_awr : forall E a0 off (STK sp0 : Z) (regs0 : bvmap 5 word) e q v ly S lyc Sc Hpc (Wc : world SEGS) memc
    Lamc peakc cntc failc ranc mostc ownc,
  bv_unsigned (ew E 19) = v ->
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> prhReader_at B lyc Sc Lamc regs0 e v 56 ->
  frames Sc = frames S -> sp0 = spZ regs0 + e -> sp0 - STK <= spZ regs0 ->
  awr_ok_fr E (ss_mem (ss_av a0 off)) STK sp0 (rd_fp q v) (ablocks B ly S) (ablocks B lyc Sc) S lyc [].
Proof.
intros E a0 off STK sp0 regs0 e q v ly S lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc U19 HLc Hat Hfr Hsp0
  Hstk a (r & Hr & Ha).
unfold ss_av, av_smem in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<- | []].
unfold av_region in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19 in Ha.
pose proof (@cf_head_nonneg cp) as Hh0.
assert (HinFP : inFP (rd_fp q v) a) by (exists (v, v + 56); split; [right; right; left; reflexivity | cbn [fst snd]; lia]).
destruct Hat as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hin' & _ & H1 & H2) | [(cid & pos & Hin' & H1 & H2) | (H1 & H2)]]].
- destruct HLc as (_ & _ & HF & _). pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hab' & _).
  cbn [fst snd] in Hk', Hab'. left. right. left. split; [exact HinFP|]. exists (a' - cf_head), (k' + cf_head).
  split; [exact Hab'|]. pose proof (req_size_pos (k' + cf_head)) as RQ. specialize (RQ ltac:(lia)). lia.
- left. right. left. split; [exact HinFP|]. exists b, m. split; [exact Hin'|].
  pose proof (req_size_pos m) as RQ. specialize (RQ ltac:(lia)). lia.
- right. split; [exact HinFP|]. exists cid, pos. split; [rewrite <- Hfr; exact Hin'|].
  unfold in_zr, frame_rng. cbn [fst snd]. lia.
- left. left. lia.
Qed.

(* fpre's read-only view rides through a journal whose footprint does not open the sink (PItems_body_key.v
   pik_rod_kept, with S1ImgB.v pst_not_ro_B for its preamble hypothesis PIK_PSTRO), over any world relation R (the
   image conjunct does not read R) *)
Lemma av_rod_kept : forall (R : world SEGS -> world SEGS -> Prop) STK sp0 FP ly S Hp (W : world SEGS) mem md own lyc
    Sc Hpc (W' : world SEGS) mem' md' k,
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS (pa_relro_lo (PAImg := PI_prog_B)) (pa_relro_hi (PAImg := PI_prog_B)) B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS (pa_relro_lo (PAImg := PI_prog_B)) (pa_relro_hi (PAImg := PI_prog_B)) B (aview SEGS (w_H W') mem').
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k HJ Hsk Hrod a Hro Hos Her.
pose proof (ajxR_img HJ) as F3.
rewrite (F3 a); [exact (Hrod a Hro Hos Her) | | exact Hos | exact Her | | apply fp_spares_closed; exact Hsk].
- destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img (PAImg := PI_prog_B) a Hr)].
- intros Hp'. exact (pst_not_ro_B a Hp' Hro).
Qed.

(* PItems_body_key.v pik_rdword_of_val, same proof *)
Lemma av_rdword_of_val : forall (H : word -> bool) (mem : word -> option byte) a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bb : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bb 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bb 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bb 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bb 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bb 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bb 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bb 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bb 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* a value two readers of two worlds agree on *)
Lemma av_val_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a n w,
  (forall kk, (kk < n)%nat -> aview SEGS H' m' (a + Z.of_nat kk) = aview SEGS H m (a + Z.of_nat kk)) ->
  val_mem SEGS (mrestrict H m) a n w -> val_mem SEGS (mrestrict H' m') a n w.
Proof.
intros H H' m m' a n w HE Hv kk Hk. rewrite (mbyte_of_aview SEGS H H' m m' (a + Z.of_nat kk) (HE kk Hk)). exact (Hv kk Hk).
Qed.

(* the frame across a call whose window clause covers parse_items' own frame and the caller's window *)
Lemma av_frame_call : forall (regs0 regs regs' : bvmap 5 word) (W : world SEGS) mem (Wc W2 : world SEGS) memc mem2 e q v,
  pi_frame (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs0 regs W mem Wc memc e q v ->
  spZ regs' = spZ regs -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  (forall a, spZ regs0 - 104 <= a < spZ regs0 -> ~ inFP (rd_fp q v) a) ->
  (forall a, spZ regs0 - 104 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
  pi_frame (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs0 regs' W mem W2 mem2 e q v.
Proof.
intros regs0 regs regs' W mem Wc W2 memc mem2 e q v
  (Fsp & F3 & F4 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & Fw & Fra & Fe0 & Fe16)
  Hsp H3 H4 Hfp HX.
unfold PI_FRAME in Fsp.
assert (VK : forall o w, 40 <= o -> o + 8 <= 144 ->
  val_mem SEGS (rdW Wc memc) (spZ regs + o) 8 w -> val_mem SEGS (rdW W2 mem2) (spZ regs' + o) 8 w).
{ intros o w Ho1 Ho2 Hv. rewrite Hsp. apply (av_val_aview (w_H Wc) (w_H W2) memc mem2); [|exact Hv].
  intros kk Hk. apply HX; [lia | apply Hfp; lia]. }
split; [unfold PI_FRAME; lia|]. split; [rewrite H3; exact F3|]. split; [rewrite H4; exact F4|].
split; [apply VK; [lia | lia | exact V1]|]. split; [apply VK; [lia | lia | exact V2]|].
split; [apply VK; [lia | lia | exact V3]|]. split; [apply VK; [lia | lia | exact V4]|].
split; [apply VK; [lia | lia | exact V5]|]. split; [apply VK; [lia | lia | exact V6]|].
split; [apply VK; [lia | lia | exact V7]|]. split; [apply VK; [lia | lia | exact V8]|].
split; [apply VK; [lia | lia | exact V9]|]. split; [apply VK; [lia | lia | exact V10]|].
split; [apply VK; [lia | lia | exact V11]|]. split; [apply VK; [lia | lia | exact V12]|].
split; [apply VK; [lia | lia | exact V13]|].
split; [|exact (conj Fra (conj Fe0 Fe16))].
intros a Ha Hn. rewrite (HX a ltac:(lia) Hn). exact (Fw a Ha Hn).
Qed.

(* a callee whose text concludes plain SRr (skip_ws: no free) at a call by an R call rule at wle' segs RZ_cf: the
   lift of its conclusion (YA0nH.SRr_SRr') and of its post's journal (YCbqG.ajournal_xwR_mono at wle <= wle') *)
Lemma av_callee_R : forall (fy : YK11.FPState) (W : world SEGS) c STK d FP (regs : bvmap 5 word) ly S Hp mem md K,
  SRr SEGS W c (fpostW_x (fx := fy) (SK := SK) SEGS B prh_pst ARx STK d FP regs ly S Hp W mem md K) ->
  SRrG SEGS (wle' SEGS YGcfRehidePost.RZ_cf) W c
    (fpostW_xR (fx := fy) (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK d FP regs ly S Hp W mem
       md K).
Proof.
intros fy W c STK d FP regs ly S Hp mem md K H.
apply (SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
eapply (SRr_mono SEGS); [exact H|].
intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HX & HP & HK).
exists ly', S', Hp', regs', mem', md', k.
refine (conj Hc (conj _ (conj HX (conj HP HK)))).
apply (ajournal_xwR_mono (SK := SK) SEGS B prh_pst ARx (@wle SEGS) _ (wle_wle' SEGS YGcfRehidePost.RZ_cf)).
exact HJ.
Qed.

End cs.
(* memnorm across one caller-frame runner phase: YGcallMxmn.v memnorm_frame_of, at the run's start state (the walk's
   st_ok_pi is st_ok at abs_ss) and the runner post's FULL frame_of *)
Section mn. Context {fy : YK11.FPState}.
Lemma av_mn_run : forall {rc : YM05.RunCeil} (W : world (@pa_segs rc B_prog_listing (@PI_prog_B rc)))
    E ss (ms0 ms : machine_state),
  YAkMemnorm.memnorm (@pa_segs rc B_prog_listing (@PI_prog_B rc)) (ms_mem ms0) ->
  st_ok_pi (@pa_segs rc B_prog_listing (@PI_prog_B rc)) (@pa_val rc B_prog_listing (@PI_prog_B rc)) E ss
    (restrict (w_H W) ms0) ->
  frame_of E (ss_mem ss) (ms_mem ms0) (ms_mem ms) ->
  YAkMemnorm.memnorm (@pa_segs rc B_prog_listing (@PI_prog_B rc)) (ms_mem ms).
Proof.
intros rc W E ss ms0 ms HM HS HF.
exact (YGcallMxmn.memnorm_frame_of _ (w_H W) E _ ms0 (ms_mem ms) HM HS HF).
Qed.
End mn.

(* ================================================================================================== *)
(* 5. THE BLOCK *)
Section main. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_B.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation VAL := (@pa_val rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation PIAT := (@PI_AT rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
(* the walk's world relation (the re-hiding move) *)
#[local] Notation WR := (wle' SEGS YGcfRehidePost.RZ_cf).
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable d : nat.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Hypothesis SKW : forall (fy : YK11.FPState), tskip_ws_specX (fx := fy) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK.
(* the cursor's call-keep statement over a world relation R, by name (lib/B/Prog/PItems_kept.v pi_cur_kept_callR_stmt);
   PItems_kept.v proves it as pi_cur_kept_callR inside its Section laws (LAWS, HSH, HZS, HAL, HIMG, HPSTRO), so a client
   instantiates HCURK with that lemma and those laws (HPSTRO at image B is S1ImgB.v pst_not_ro_B). Here it is taken at
   R := wle' segs RZ_cf, skip_ws's call journal. The node's bytes come from PItems_kept.v's lemma pi_node_kept_callR.
   The runners PI_RUNFR / PI_RUNTOFR bring functional_extensionality_dep (toolchain/allowed-axioms.txt:94). *)
Hypothesis HCURK : pi_cur_kept_callR_stmt (L := B_prog_listing) (PA := PI_prog_B) (SKq := SK) B ARx.

(* the callee-saved registers the block reads back after skip_ws (YG0d.v acallee_saved) *)
Lemma av_cs : forall z, In z [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> acallee_saved z.
Proof. intros z Hz. cbn [In] in Hz. unfold acallee_saved. lia. Qed.

Lemma av_stk : 16560 + 144 <= STK_parse_items d.
Proof.
unfold STK_parse_items. pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - d)).
assert (EL : LEAF_pv_pi (PI := prh_img_B) = 16560) by (vm_compute; reflexivity). rewrite EL.
change (PRH_Base.pi_frame F_parse_items) with 144. change (PRH_Base.pi_frame F_parse_value) with 176. lia.
Qed.

(* split a right-nested conjunction into its conjuncts, syntactically (no definition is unfolded) *)
Ltac av_split H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "TLa" in let H2 := fresh "TLb" in destruct H as [H1 H2]; av_split H2
  | _ => idtac
  end.

Theorem pv_aftv_holds : forall CTX0 CW N,
  pv_sep_spec (L := B_prog_listing) (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d CTX0 CW N ->
  pi_epi_spec (L := B_prog_listing) (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d ->
  pv_aftv_spec (L := B_prog_listing) (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d CTX0 CW N.
Proof.
intros CTX0 CW N HSEP HEPI fxc fx0 ly S0 Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own
  kr lyc Sc Hpc Wc memc mdc k regs WS0 HJw HWS HPRE.
destruct HPRE as (HFP & HENT & HMN & HFRM & HREGS & HRB & H21 & f & n & cap & acc & kids & keys & Di & nm & Dk
  & res & Dv & ok0 & tr0 & D0 & Lamc & peakc & cntc & failc & ranc & H10 & Hncap & HCONT & HDEP & HAPS & HKEY & HPERM
  & HRUN & HLED & HBLK & HPOS & HHU & HLIVE & HBB & HOK & HLS & HRLC & HRAq & HSRC & HHOME & HAT & HRAv & HLG & HRES
  & Hcapn & HNCAPS & af & lk & fv & HFORD & HLK & HTAIL).
(* pi_ent and its rd_pre: the fixed prefix by position, every conjunct after it BY TYPE (robust to a conjunct the kit owner adds
   there, e.g. the strict text ceiling of fix (a)) *)
pose proof HENT as (_ & _ & _ & Ein & Eclo & Ecent & Echn & Ecur & E10 & E11 & E12 & Egp & Etp & RDP & Eplt & Enth & Eroom
  & Efch & Efrm & Erod & EENT).
av_split EENT.
pose proof RDP as (_ & _ & _ & _ & HIN0 & Hfwin & Hspq & Hqe & HRA0 & HSRC0 & HHOME0 & RDT).
av_split RDT.
match goal with H : prhPv_node _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HPV end.
match goal with H : q + 24 <= v \/ v + 56 <= q |- _ => rename H into Hqv end.
match goal with H : 0 < len -> text + len <= v \/ v + 56 <= text |- _ => rename H into Htv end.
match goal with H : v + 56 <= spZ regs0 \/ spZ regs0 + e <= v |- _ => rename H into Hvw end.
match goal with H : prh_ledger B ly S0 Hp W mem Lam peak cnt fail ran most own |- _ => rename H into HLG0 end.
match goal with H : (d <= PjGrammar.MAXD)%nat |- _ => rename H into HdM end.
match goal with H : cnt + 2 * Z.of_nat (length (rest_atR tb text p)) + 2 < 2 ^ 64 - 1 |- _ => rename H into HCNT0 end.
pose proof HPV as (Hv4096 & Hv8 & _ & _ & HAT0 & _ & Hvown & _).
pose proof HFRM as (Fsp & F3 & F4 & FW1 & FW2 & FW3 & FW4 & FW5 & FW6 & FW7 & FW8 & FW9 & FW10 & FW11 & FW12 & FW13
  & Fwin & Fret & He0 & He16).
pose proof HREGS as (R9 & R19 & R18 & R8 & R20 & R26 & R27 & R25 & R23).
pose proof HRB as (R22 & R24 & B0 & B32 & B24 & B16 & B8).
unfold pi_ajR in HJw.
pose proof (ajxR_ar HJw) as HARc. pose proof (ajxR_ly HJw) as HLY. pose proof (ajxR_frs HJw) as Hfrs.
pose proof (ajxR_stk HJw) as Hastk.
(* THE BUDGETED JOURNAL, at the walk's relation: the runs and skip_ws's call take the empty-budget
   journal, rebased at the block's depot (YCbqGwild.ajournal_xw_rebaseR); HWD is the wild part's cover the step back to
   WS0 needs (YCbqGwild.ajournal_xw_unbase0R): the block and skip_ws make no allocator call *)
pose proof (ajxR_wild HJw) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw)
  as HJ.
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof av_stk as HSTK.
pose proof (@cf_head_nonneg cp) as Hh0.
unfold PI_FRAME in Fsp.
assert (Hsp0 : YM05.alloc_ceiling <= spZ regs0 - STK_parse_items d) by lia.
destruct (av_v_place B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc most own regs0 e v HARc HLG HAT
  ltac:(lia) ltac:(lia)) as (Hv0 & Hv1 & Hvsh & Hvni).
pose proof HCONT as (Hh & Hnl & Hle & Hcap & Hsl & Hk & HNDi & HAPDi & Hit).
pose proof Hh as ((Hal & Hrw) & _ & _ & _ & _ & _ & (Hn0 & Vn) & _).
assert (Hnb : 0 <= Z.of_nat n <= 2 ^ 54) by lia.
(* the blocks the prefix allocated: no duplicates, in the ledger, apart from the node (they are new) *)
pose proof HLED as HLED'. unfold rd_ledger_move in HLED'. destruct HLED' as (_ & _ & _ & HPL & _ & _ & _).
assert (HI0 : incl D0 Lamc)
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hb).
assert (HND0 : List.NoDup D0).
{ destruct HLG as (_ & HNDm & _). apply (proj1 (NoDup_ListNoDup _)) in HNDm. apply NoDup_map_inv in HNDm.
  pose proof (Permutation_NoDup HPL HNDm) as H. apply (proj2 (NoDup_ListNoDup _)) in H.
  apply (proj1 (NoDup_ListNoDup _)). exact (pis_nodup_l _ _ _ H). }
assert (HAP0 : pj_apartR D0 v)
  by exact (av_new_apart B ARx LAWS ly S0 Hp W mem Lam peak cnt fail ran most own regs0 e v lyc Sc Hpc Wc memc mdc Lamc
    peakc cntc failc ranc most own D0 tr0 (rest_atR tb text p) d HARc HLY HLG0 HAT0 Hvw HLG HI0 HBLK).
assert (FOOT : forall x, (exists b, In b D0 /\ pj_holdsR b x) -> 4096 <= x < YM05.alloc_ceiling /\ ~ (v <= x < v + 56)).
{ intros x ([b m] & Hb & Hx). unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
  destruct (cl_D_bounds B ARx HL LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc most own b m HARc HLG
    (HI0 _ Hb)) as (Hb1 & Hb2).
  split; [lia|]. exact (HAP0 (b, m) x Hb Hx). }
assert (HINs : forall b, In b (pi_sblk o kids keys cap ++ Di ++ Dk ++ Dv) -> In b D0)
  by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPERM) Hb)).
assert (HNDs : NoDup (pi_sblk o kids keys cap ++ Di ++ Dk ++ Dv))
  by (apply (proj2 (NoDup_ListNoDup _)); exact (Permutation_NoDup HPERM HND0)).
assert (HNDsd : NoDup (pi_sblk o kids keys cap ++ Di)).
{ apply (pis_nodup_l _ _ (Dk ++ Dv)). rewrite <- app_assoc. exact HNDs. }
assert (HSB : forall b, In b (pi_sblk o kids keys cap) -> In b D0) by (intros b Hb; apply HINs; apply in_or_app; left; exact Hb).
assert (HDI : forall b, In b Di -> In b D0)
  by (intros b Hb; apply HINs; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HDK : forall b, In b Dk -> In b D0)
  by (intros b Hb; apply HINs; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HDV : forall b, In b Dv -> In b D0)
  by (intros b Hb; apply HINs; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
assert (HAPkv : pj_apartR (Dk ++ Dv) v).
{ intros b x Hb Hx. apply in_app_or in Hb as [Hb|Hb]; [exact (HAP0 b x (HDK b Hb) Hx) | exact (HAP0 b x (HDV b Hb) Hx)]. }
pose proof (pvm_cont_open (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) _ (prh_lin Lamc) o v kids keys n cap acc Di
  HCONT HAPS HNDsd) as HOPEN.
assert (Hlts : length (map snd acc) = n) by (rewrite length_map; symmetry; exact Hnl).
assert (HFts : Forall (fun t => (PjTree.depth t <= PjGrammar.MAXD - Nat.succ d)%nat) (map snd acc))
  by (apply Forall_map; exact HDEP).
(* the kid slot lies in the kids block *)
assert (FSLOT : forall x, kids + 56 * Z.of_nat n <= x < kids + 56 * Z.of_nat n + 56 -> exists b, In b D0 /\ pj_holdsR b x).
{ intros x Hx. exists (kids, 56 * Z.of_nat cap). split; [apply HSB; unfold pi_sblk, kids_blkR|unfold pj_holdsR; cbn [fst snd]; lia].
  apply in_or_app. left. replace (Z.of_nat cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
(* the symbolic state at PI_O_AFTV *)
assert (Hwr40 : forall x, v + 40 <= x < v + 48 -> writable_at SEGS (rdW Wc memc) x) by (intros x Hx; apply Hrw; lia).
assert (Hvb : 4096 <= v <= 2 ^ 47 - 56) by lia.
assert (Hfr0 : frames Sc = frames S0) by (rewrite Hfrs; reflexivity).
destruct res as [[t r] |].
- (* ---- THE VALUE WAS READ: v->n := n + 1, a0 = 0, the call of skip_ws ---- *)
  destruct HRES as (HNDk & Hdept & pc & HINc & Hrest & Hcnt2 & HN1 & Hf1 & HROOM).
  destruct HTAIL as (HGR & HNCt & HFOt & HMOD).
  (* the value was read: the hull use is over tr0, so with the position implication it is pi_posb S Sc tr0 *)
  assert (HPOSB : PItems_posb.pi_posb S0 Sc tr0) by exact (conj HPOS HHU).
  pose proof (av_st_ok fxc Wc memc regs v (Z.of_nat n) 0 (PIAT PI_O_AFTV) R19 R22 R24 R26 H10 Hvb Hal Hnb Vn Hwr40) as HS.
  pose proof (av_sh_ok Wc memc regs v (Z.of_nat n) R19 R26 Hvb Hvsh HRAv) as SHOK.
  remember (Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) (Ereg regs [Z_to_bv 64 (Z.of_nat n)])) as E eqn:HE in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (Z.of_nat n)]) E)
    by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E9 : ew E 9 = getr regs 9) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E19 : ew E 19 = Z_to_bv 64 v).
  { rewrite HE, Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl). exact R19. }
  assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF).
  { rewrite HE, Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl). exact R26. }
  assert (U19 : bv_unsigned (ew E 19) = v) by (rewrite E19; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat n)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  clear HE.
  unfold pi_goalR, cfg_at. change (w64 (VAL A_TEXT + PIAT PI_O_AFTV)) with (Z_to_bv 64 (VAL A_TEXT + PIAT PI_O_AFTV)).
  pose (RUNF := @PI_RUNFR fxc rc SK B_prog_listing PL_prog_B PI_prog_B B prh_pst ARx HL LAWS).
  pose proof HS as HS0.
  pi_run RUNF HS HJ SHOK.
  { (* the store into v + 40 (the shadow test 0x87d9c on s8 = shadow (v + 40) is decided by the SH entry (v, 0, 56),
       from pv_aftv_pre's range_addressable v 56; the run then stops at the call of skip_ws, 0x87db8) *)
    refine (av_awr B E 0 (PIAT PI_O_AFTV) (STK_parse_items d + e) (spZ regs0 + e) regs0 e q v ly _ lyc Sc Hpc Wc
      memc Lamc peakc cntc failc ranc most own U19 HLG HAT _ eq_refl _); [exact Hfr0 | lia]. }
  (* the memory after the store *)
  pose proof (st_ok_mem_ok SEGS E _ _ HS) as (_ & HRG & _). cbn [ms_mem restrict] in HRG.
  destruct (av_store_post (fy := fxc) E Wc memc (ms_mem ms) v (Z.of_nat n) U19 E32 Hnb HFr HRG) as (AGR & VN1 & WR1).
  (* the overlay stays normal across the run and the store (YGcallMxmn.v memnorm_frame_of, on the full frame) *)
  lazymatch type of HS0 with context [restrict _ ?m0] =>
    pose proof (av_mn_run (fy := fxc) Wc E _ m0 ms HMN HS0 HF) as HMN1 end.
  pose proof HJ as (HARr & _).
  (* the registers at the call *)
  assert (KMS : forall rr, In rr [2; 3; 4; 8; 9; 18; 19; 20; 23; 25; 26; 27]%bv -> getr (ms_regs ms) rr = getr regs rr)
    by (intros rr Hr; exact (regs_kept_of_st_ok SEGS E _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 23; 25; 26; 27]%bv HS HAE
      ltac:(vm_compute; reflexivity) rr Hr)).
  prreg HS (1%bv : bv 5) R1'. prreg HS (10%bv : bv 5) R10'. prreg HS (21%bv : bv 5) R21'.
  pose proof (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 22%bv HS) as R22'.
  pose proof (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 24%bv HS) as R24'.
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let e22 := eval vm_compute in (sr_get (ss_regs ss) 22%bv) in change (sr_get (ss_regs ss) 22%bv) with e22 in R22';
    let e24 := eval vm_compute in (sr_get (ss_regs ss) 24%bv) in change (sr_get (ss_regs ss) 24%bv) with e24 in R24' end.
  assert (D19 : sv_denot E (SOff 19 40) = Z_to_bv 64 (v + 40)).
  { rewrite denot_lit_U, U_SOff, U19, zcanon_id by (unfold M64; lia). reflexivity. }
  rewrite D19 in R22'.
  rewrite (pi_denot_shx' E 19 40 SHADOW_OFF (v + 40) D19 E26 ltac:(lia) ltac:(unfold SHADOW_OFF; lia)) in R24'.
  assert (Usp : spZ (ms_regs ms) = spZ regs) by (unfold spZ; rewrite (KMS 2%bv ltac:(cbn; tauto)); reflexivity).
  (* everything the call reads, at the store's memory: the cursor, the text, the shadows, the ledger (all apart from
     the n field) *)
  pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & Hhull).
  pose proof HINc as (Vp & Ve & Vd & Hrwq & Hq8 & Ht0 & Htl & Hple & Hlen & HGx & Hdqt & Hd032).
  rewrite Hlen in Htc, Htam, Htra, Hhull.
  assert (FQ : forall x, q <= x < q + 24 -> av_F v x) by (intros x Hx; split; lia).
  assert (FT : forall x, text <= x < text + len -> av_F v x) by (intros x Hx; split; lia).
  assert (FSH : forall x, 0 <= x < 2 ^ 47 -> av_F v (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. unfold shadow_of_addr. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). unfold kHighMemBeg, SHADOW_OFF in *. split; lia. }
  assert (HIN1 : pj_in_okR SEGS (rdW Wc (ms_mem ms)) q text len pc (Z.of_nat d + 1) tb).
  { split; [apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ AGR); [intros kk Hkk; apply FQ; lia | exact Vp]|].
    split; [apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ AGR); [intros kk Hkk; apply FQ; lia | exact Ve]|].
    split; [apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ AGR); [intros kk Hkk; apply FQ; lia | exact Vd]|].
    split; [apply (pi_rw_agr SEGS (av_F v) _ _ _ _ AGR); [intros x Hx; apply FQ; lia | exact Hrwq]|].
    split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [exact Hple|]. split; [exact Hlen|].
    split; [apply (pi_garr8_agr SEGS (av_F v) _ _ _ _ AGR); [intros x Hx; apply FT; lia | exact HGx]|].
    split; [exact Hdqt | exact Hd032]. }
  pose proof HIN1 as (Vp1 & Ve1 & _).
  assert (HRAq1 : range_addressable (aview SEGS (w_H Wc) (ms_mem ms)) SHADOW_OFF q 24)
    by (apply (pi_ra_agr SEGS (av_F v) (w_H Wc) memc (ms_mem ms) q 24 AGR); [intros x Hx; apply FSH; lia | exact HRAq]).
  assert (HRAv1 : range_addressable (aview SEGS (w_H Wc) (ms_mem ms)) SHADOW_OFF v 56)
    by (apply (pi_ra_agr SEGS (av_F v) (w_H Wc) memc (ms_mem ms) v 56 AGR); [intros x Hx; apply FSH; lia | exact HRAv]).
  assert (HLG1 : prh_ledger B lyc Sc Hpc Wc (ms_mem ms) Lamc peakc cntc failc ranc most own)
    by exact (av_ledger_store B ARx LAWS lyc Sc Hpc Wc memc (ms_mem ms) mdc Lamc peakc cntc failc ranc most own regs0 e v
      HARc HLG HAT ltac:(lia) Hvni AGR).
  assert (Hcntr : cntc + 2 * Z.of_nat (length (rest_atR tb text pc)) + 2 < 2 ^ 64 - 1) by (rewrite Hrest; exact Hcnt2).
  assert (HCUR1 : pi_cur (rc := rc) (cp := cp) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B regs0 e q v
    text len tb d lyc Sc Hpc Wc (ms_mem ms) pc Lamc peakc cntc failc ranc most own).
  { refine (conj HIN1 (conj HRAq1 (conj _ (conj HHOME (conj HAT (conj HRAv1 (conj HLG1 Hcntr))))))).
    split; [apply (pi_garr8_agr SEGS (av_F v) _ _ _ _ AGR); [intros x Hx; apply FT; lia | exact HGt]|].
    split; [exact Ht4|]. rewrite Hlen. split; [exact Htc|]. split; [exact Htam|].
    split; [apply (pi_ra_agr SEGS (av_F v) (w_H Wc) memc (ms_mem ms) text len AGR); [intros x Hx; apply FSH; lia | exact Htra]|].
    intros Hl s0 Hs0. rewrite (pi_aview_agr SEGS (av_F v) (w_H Wc) memc (ms_mem ms) s0 AGR); [exact (Hhull Hl s0 Hs0)|].
    unfold shadow_addr in Hs0.
    pose proof (Z.div_pos text 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound (text + len - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (SHADOW_OFF + text / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)).
    unfold kHighMemBeg, SHADOW_OFF in *. split; lia. }
  (* the container with its new member, at the store's memory (PItems_shape.v pis_snoc, then the n field) *)
  assert (SAME1 : forall x, 4096 <= x < YM05.alloc_ceiling -> ~ (v <= x < v + 56) ->
    pis_same SEGS (rdW Wc memc) (rdW Wc (ms_mem ms)) x)
    by (intros x Hx Hxv; apply (av_same_agr (av_F v) _ _ x AGR); split; lia).
  assert (Hh1 : pj_hdrR SEGS (rdW Wc (ms_mem ms)) v (5 + pis_oz o) 0 0 kids keys (Z.of_nat n + 1) (Z.of_nat cap)).
  { rewrite <- av_ty. apply (pis_hdr_n SEGS (rdW Wc memc) (rdW Wc (ms_mem ms)) v _ 0 0 kids keys (Z.of_nat n) (Z.of_nat cap)
      (Z.of_nat n + 1) Hh); [lia | exact VN1 | |].
    - intros x Hx Hx'. unfold mbyte. rewrite (AGR x); [reflexivity | split; lia].
    - intros x Hx Hw. destruct (Z_lt_dec x (v + 40)) as [Hl|Hl]; [|destruct (Z_lt_dec x (v + 48)) as [Hl2|Hl2]].
      + apply (pi_wr_agr SEGS (av_F v) _ _ x AGR); [split; lia | exact Hw].
      + apply WR1. lia.
      + apply (pi_wr_agr SEGS (av_F v) _ _ x AGR); [split; lia | exact Hw]. }
  assert (Hlts' : length (map snd acc ++ [t]) = Nat.succ n) by (rewrite length_app, Hlts; cbn [List.length]; rewrite Nat.add_1_r; reflexivity).
  assert (HDIKV : forall b, In b (Di ++ Dk ++ Dv) -> In b D0)
    by (intros b Hb; apply HINs; apply in_or_app; right; exact Hb).
  assert (HOPENs : pis_open SEGS (rdW Wc memc) (prh_lin Lamc) v o 0 kids keys (Z.of_nat cap) (Z.of_nat n)
    (map snd acc ++ [t]) (map fst acc ++ [nm]) (Di ++ Dk ++ Dv)).
  { apply (pis_snoc SEGS _ _ v o 0 kids keys (Z.of_nat cap) (Z.of_nat n) (map snd acc) (map fst acc) Di t nm Dk Dv HOPEN).
    - rewrite Hlts. exact HNDk.
    - rewrite Hlts. destruct o; [exact HKEY | exact (proj2 HKEY)].
    - rewrite <- pvm_sblk_slots. exact HNDs.
    - exact HAPkv. }
  assert (HOPEN1 : pis_open SEGS (rdW Wc (ms_mem ms)) (prh_lin Lamc) v o 0 kids keys (Z.of_nat cap) (Z.of_nat n + 1)
    (map snd acc ++ [t]) (map fst acc ++ [nm]) (Di ++ Dk ++ Dv)).
  { apply (pis_frame SEGS (rdW Wc memc) (prh_lin Lamc) (rdW Wc (ms_mem ms)) (prh_lin Lamc) v o 0 kids keys (Z.of_nat cap)
      (Z.of_nat n) (map snd acc ++ [t]) (map fst acc ++ [nm]) (Di ++ Dk ++ Dv) 0 (Z.of_nat n + 1) HOPENs Hh1); [lia | |].
    - exact (pis_open_lblk SEGS _ _ _ _ _ _ _ _ _ _ _ _ HOPENs).
    - intros x Hx. rewrite Hlts' in Hx.
      assert (Hc0 : (0 < cap)%nat) by exact (Nat.le_lt_trans 0 n cap (Nat.le_0_l n) Hncap). assert (Hc1 : (Nat.succ n <= cap)%nat) by exact Hncap.
      destruct (FOOT x (av_ifoot_in o kids keys cap (Nat.succ n) (Di ++ Dk ++ Dv) x D0 Hc0 Hc1 HSB HDIKV Hx))
        as (Hx1 & Hx2).
      exact (SAME1 x Hx1 Hx2). }
  (* THE CALL OF skip_ws (0x87db8): a0 = q, ra = PV_O_SEP; the window rule at e1 = PI_FRAME + e *)
  assert (HCH : exists ch1, achain lyc (aview SEGS (w_H Wc) (ms_mem ms)) (spZ regs) (q + 16) ch1).
  { destruct (Z_lt_le_dec (q + 16) (ly_top lyc - 16)) as [Hlt | Hge].
    - exists [(q + 16, text + len, pc)]. right.
      split; [lia|]. split; [exact Hlt|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
      split.
      + cbn [fpchain]. split; [reflexivity|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
        split; [replace (q + 16 - 8) with (q + 8) by lia;
                apply (av_rdword_of_val (w_H Wc) (ms_mem ms) (q + 8) (text + len)); [exact Ve1 | lia]|].
        split; [replace (q + 16 - 16) with q by lia;
                apply (av_rdword_of_val (w_H Wc) (ms_mem ms) q pc); [exact Vp1 | lia]|].
        split; [lia|].
        unfold bad_next. replace (pc <=? q + 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      + constructor; [cbn [fst]; lia | constructor].
    - exists []. left. split; [right; left; lia | reflexivity]. }
  destruct HCH as (ch1 & HCH).
  let x := eval vm_compute in (STK_skip_ws (PI := prh_img_B)) in assert (Hskw : STK_skip_ws (PI := prh_img_B) = x) by reflexivity.
  assert (Us0 : s0Z (ms_regs ms) = q + 16).
  { unfold s0Z. rewrite (KMS 8%bv ltac:(cbn; tauto)), R8. apply unsigned_lit_small. lia. }
  assert (HLYc : ly_stk_hi lyc = ly_stk_hi ly) by (destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh & _); exact Eh).
  eapply (SRrG_bind SEGS WR (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  { eapply (aj_call_xW_spR (fx := fxc) (SK := SK) SEGS B prh_pst ARx LAWS (pa_segs_low (PAImg := PI_prog_B)) WR
      (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc E _ ms
      (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v) ly _ Hp W mem md [] lyc Sc Hpc _ k
      STK_skip_ws (PI_FRAME + e) [(q, q + 8)] (- (PI_FRAME + e)) (Z_to_bv 64 (VAL A_TEXT + PIAT PV_O_SEP)) ch1
      (* skip_ws's post, the m-form (PRH_Base.v fQmn): its Q, and the memnorm keep from the call memory *)
      (fun ly' S' Hp' W' regs' mem' md' =>
         ((room_live_cf Sc -> room_live_cf S') /\ Hp' = Hpc /\ S' = Sc /\ ablocks B ly' S' = ablocks B lyc Sc /\
          prh_ledger B ly' S' Hp' W' mem' Lamc peakc cntc failc ranc most own /\
          pj_in_okR SEGS (mrestrict (w_H W') mem') q text len
            (text + len - Z.of_nat (length (PjGrammar.skip (rest_atR tb text pc)))) (Z.of_nat d + 1) tb) /\
         (YAkMemnorm.memnorm SEGS (ms_mem ms) -> YAkMemnorm.memnorm SEGS mem'))
      HS eq_refl HJ).
    - rewrite Usp, Fsp. unfold PI_FRAME. lia.
    - unfold PI_FRAME. rewrite Z.mod_opp_l_z; [reflexivity | lia | rewrite Z.add_mod, He16 by lia; reflexivity].
    - unfold PI_FRAME. lia.
    - rewrite Hskw. lia.
    - rewrite Hskw. unfold PI_FRAME. lia.
    - unfold PI_FRAME. lia.
    - unfold PI_FRAME. rewrite Z.add_mod, He16 by lia; reflexivity.
    - lia.
    - rewrite (KMS 3%bv ltac:(cbn; tauto)), F3. exact Egp.
    - rewrite (KMS 4%bv ltac:(cbn; tauto)), F4. exact Etp.
    - rewrite R1'; f_equal; vm_compute; reflexivity.
    - apply ret_ok_codeptr_v; [vm_compute; split; [discriminate | reflexivity] | vm_compute; reflexivity].
    - assert (Hpc0 : 0 <= VAL A_TEXT + PIAT PV_O_SEP < 2 ^ 64) by (vm_compute; split; [discriminate | reflexivity]).
      rewrite unsigned_lit_small by exact Hpc0. vm_compute. discriminate.
    - replace (spZ regs0 + e + - (PI_FRAME + e)) with (spZ regs) by (unfold PI_FRAME; lia). rewrite Us0. exact HCH.
    - intros HAF HWIN. cbn [ss_pc setpc].
      (* skip_ws's text concludes plain SRr: lifted to the walk's relation *)
      apply (av_callee_R SK B ARx fxc).
      refine (SKW fxc lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ ch1 (PI_FRAME + e) q text len pc (Z.of_nat d + 1) tb
        Lamc peakc cntc failc ranc most own _ _ _ _ _ _ _ _ _ _).
      + split; [exact HAF|]. split.
        * apply (av_rod_kept SK B ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [|exact Erod].
          intros (rr & Hrr & H0). cbn [rd_fp In] in Hrr.
          destruct Hrr as [<- | [<- | [<- | []]]]; cbn [fst snd] in H0; lia.
        * split; [rewrite Usp, Fsp, HLYc; unfold PI_FRAME; lia|].
          (* fpre's frm_zero at the call (FRM0-ENTRY): the block's own float state, pi_fpok *)
          split; [|exact (proj1 HFP)].
          (* fpre's return address below the ceiling: ra is the listing's return site PV_O_SEP (the jal's own pc + 4) *)
          assert (ER1 : getr (ms_regs ms) 1 = Z_to_bv 64 (VAL A_TEXT + PIAT PV_O_SEP))
            by (rewrite R1'; f_equal; vm_compute; reflexivity).
          assert (Hpc1 : 0 <= VAL A_TEXT + PIAT PV_O_SEP < 2 ^ 64) by (vm_compute; split; [discriminate | reflexivity]).
          assert (Hpc2 : VAL A_TEXT + PIAT PV_O_SEP < YM05.CEIL_MIN) by (vm_compute; reflexivity).
          pose proof (YM05.alloc_ceiling_value (rc := rc)) as (CM & _).
          unfold raZ. rewrite ER1, unsigned_lit_small by exact Hpc1. lia.
      + rewrite R10', E9. exact R9.
      + exact HIN1.
      + exact HWIN.
      + rewrite Usp. lia.
      + rewrite Usp, Fsp. unfold PI_FRAME. lia.
      + exact HRAq1.
      + exact (proj1 (proj2 (proj2 HCUR1))).
      + exact HHOME.
      + exact HLG1.
    - intros a (rr & Hrr & Ha). left. exists rr. split; [|exact Ha].
      destruct Hrr as [<- | []]. left. reflexivity. }
  (* back at PV_O_SEP: skip_ws's post, its journal from the call state, its window clause *)
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HX & HP
    & (Hrl & HHp & HS2e & Hab & Hled2 & Hin2) & HMNk).
  (* the travelling facts at the return state: skip_ws keeps the overlay normal (its m-form keep) and leaves the
     allocator state as it was (S2 = Sc), so pi_posb / pi_live over tr0 carry over unchanged (PItems_posb.pi_posb_eq /
     pi_live_eq) *)
  pose proof (HMNk HMN1) as HMN2.
  (* back to the budgeted journal from S0 at WS0: skip_ws stored no wild trace *)
  pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HJ2 HWD) as HJ2w.
  pose proof (PItems_posb.pi_posb_eq S0 Sc S2 tr0 HS2e HPOSB) as HPOSB2.
  assert (HLIVE2 : PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S0))
    (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) tr0)
    by (apply (PItems_posb.pi_live_eq _ (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)));
        [rewrite HS2e; apply Permutation_refl | exact HLIVE]).
  unfold PI_FRAME in HX, HJ1.
  assert (KR : forall (rr : bv 5) (z : Z), acallee_saved z -> rr = Z_to_bv 5 z -> getr regs2 rr = getr (ms_regs ms) rr)
    by (intros rr z Hz ->; exact (HP z Hz)).
  assert (G : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 23; 25; 26; 27]%bv -> getr regs2 rr = getr regs rr).
  { intros rr Hr. rewrite <- (KMS rr Hr). cbn [In] in Hr.
    let tac z := (apply (KR _ z); [apply av_cs; cbn [In]; tauto | apply bv_eq; reflexivity]) in
    repeat (destruct Hr as [<- | Hr];
      [first [ tac 2 | tac 3 | tac 4 | tac 8 | tac 9 | tac 18 | tac 19 | tac 20 | tac 23 | tac 25 | tac 26 | tac 27 ] |]);
    destruct Hr. }
  assert (G2 : spZ regs2 = spZ regs) by (unfold spZ; rewrite (G 2%bv ltac:(cbn; tauto)); reflexivity).
  assert (G21 : getr regs2 21 = w64 (-1)).
  { rewrite (KR 21%bv 21 ltac:(apply av_cs; cbn [In]; tauto) ltac:(apply bv_eq; reflexivity)), R21'. apply bv_eq. vm_compute. reflexivity. }
  assert (G22 : getr regs2 22 = w64 (v + 40))
    by (rewrite (KR 22%bv 22 ltac:(apply av_cs; cbn [In]; tauto) ltac:(apply bv_eq; reflexivity)), R22'; reflexivity).
  assert (G24 : getr regs2 24 = w64 (pi_sh (v + 40)))
    by (rewrite (KR 24%bv 24 ltac:(apply av_cs; cbn [In]; tauto) ltac:(apply bv_eq; reflexivity)), R24'; reflexivity).
  (* the window clause covers parse_items' frame (cache words and saved registers) and the caller's window *)
  assert (HXw : forall a, spZ regs0 - 144 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
  { intros a Ha Hn. apply HX; [lia|]. intros (rr & Hrr & Hra). apply Hn. exists rr. split; [|exact Hra].
    destruct Hrr as [<- | []]. left. reflexivity. }
  assert (FRF : forall a, spZ regs0 - 144 <= a < spZ regs0 -> ~ inFP (rd_fp q v) a /\ av_F v a).
  { intros a Ha. split.
    - intros (rr & Hrr & Hra). cbn [rd_fp In] in Hrr.
      destruct Hrr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra; [lia | lia|].
      apply (proj2 (Hvown a ltac:(lia))). lia.
    - split; [lia|]. intros Hav. apply (proj2 (Hvown a ltac:(lia))). lia. }
  assert (FRK : forall o' w, 0 <= o' -> o' + 8 <= 40 ->
    val_mem SEGS (rdW Wc memc) (spZ regs + o') 8 w -> val_mem SEGS (rdW W2 mem2) (spZ regs2 + o') 8 w).
  { intros o' w Ho1 Ho2 Hv. rewrite G2.
    apply (av_val_aview (w_H Wc) (w_H W2) (ms_mem ms) mem2); [intros kk Hkk; apply HXw; [lia | apply FRF; lia]|].
    apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ AGR); [intros kk Hkk; apply FRF; lia | exact Hv]. }
  assert (HFRM1 : pi_frame (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs0 (ms_regs ms) W mem Wc (ms_mem ms) e q v).
  { apply (pi_frame_kept (av_F v) regs0 regs (ms_regs ms) W mem Wc memc (ms_mem ms) e q v HFRM).
    - exact Usp.
    - exact (KMS 3%bv ltac:(cbn; tauto)).
    - exact (KMS 4%bv ltac:(cbn; tauto)).
    - exact AGR.
    - intros a Ha. apply FRF. lia.
    - intros a Ha Hn. split; [lia|]. intros Hav. apply Hn. exists (v, v + 56).
      split; [right; right; left; reflexivity | cbn [fst snd]; lia]. }
  (* the node's bytes and the prefix's blocks are kept by skip_ws *)
  pose proof HJ2 as (_ & HLY2 & _).
  assert (Eslo : ly_stk_lo ly2 = ly_stk_lo ly) by (destruct HLY2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & El & _); exact El).
  assert (Eshi : ly_stk_hi ly2 = ly_stk_hi ly) by (destruct HLY2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh & _); exact Eh).
  assert (NODE2 : forall a, v <= a < v + 56 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
  { apply (pi_node_kept_callR (L := B_prog_listing) (PA := PI_prog_B) (SKq := SK) B ARx WR regs0 e v lyc Sc Hpc Wc
      (ms_mem ms) _ STK_skip_ws (spZ regs0 + e + - (144 + e)) (144 + e) [(q, q + 8)] [] ly2 S2 Hp2 W2 mem2 md2 k1 Lamc []
      HAT HJ1 HX).
    - lia.
    - lia.
    - lia.
    - rewrite Eshi. lia.
    - intros a Ha (rr & Hrr & Hra). destruct Hrr as [<- | []]. cbn [fst snd] in Hra. lia.
    - intros b m Hb _ _. rewrite Hab. exact Hb.
    - intros a kk Hak. pose proof HLG as (_ & _ & HFc & _).
      exact (proj1 (proj2 (proj1 (Forall_forall _ _) HFc (a, kk) Hak))).
    - exact Hvw. }
  assert (KEEP2 : forall x, (exists b, In b D0 /\ pj_holdsR b x) -> pis_same SEGS (rdW Wc (ms_mem ms)) (rdW W2 mem2) x).
  { intros x Hx. pose proof (FOOT x Hx) as (Hx1 & Hx2). destruct Hx as ([b m] & Hb & Hx). unfold pj_holdsR in Hx.
    cbn [fst snd] in Hx.
    pose proof HLG as (_ & _ & HFc & _). pose proof (proj1 (Forall_forall _ _) HFc (b, m) (HI0 _ Hb)) as (Hm0 & Hab0 & _).
    cbn [fst snd] in Hm0, Hab0.
    pose proof (req_size_pos (m + cf_head)) as RQ. specialize (RQ ltac:(lia)).
    apply av_same_of_aview; [lia | apply (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc (b - cf_head) (m + cf_head) x HARc Hab0); lia |].
    pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    replace x with ((b - cf_head) + (x - (b - cf_head))) by lia.
    apply (F2 (b - cf_head) (m + cf_head)); [exact Hab0 | rewrite Hab; exact Hab0 | lia |].
    intros (rr & Hrr & Hra). destruct Hrr as [<- | []]. cbn [fst snd] in Hra. lia. }
  assert (Hh2 : pj_hdrR SEGS (rdW W2 mem2) v (5 + pis_oz o) 0 0 kids keys (Z.of_nat n + 1) (Z.of_nat cap)).
  { apply (pis_hdr_frame SEGS (rdW Wc (ms_mem ms)) (rdW W2 mem2) v _ _ _ _ _ _ _ Hh1).
    intros x Hx. apply av_same_of_aview; [lia | apply Hvni; lia | apply NODE2; lia]. }
  assert (HOPEN2 : pis_open SEGS (rdW W2 mem2) (prh_lin Lamc) v o 0 kids keys (Z.of_nat cap) (Z.of_nat n + 1)
    (map snd acc ++ [t]) (map fst acc ++ [nm]) (Di ++ Dk ++ Dv)).
  { apply (pis_frame SEGS (rdW Wc (ms_mem ms)) (prh_lin Lamc) (rdW W2 mem2) (prh_lin Lamc) v o 0 kids keys (Z.of_nat cap)
      (Z.of_nat n + 1) (map snd acc ++ [t]) (map fst acc ++ [nm]) (Di ++ Dk ++ Dv) 0 (Z.of_nat n + 1) HOPEN1 Hh2); [lia | |].
    - exact (pis_open_lblk SEGS _ _ _ _ _ _ _ _ _ _ _ _ HOPEN1).
    - intros x Hx. rewrite Hlts' in Hx.
      assert (Hc0 : (0 < cap)%nat) by exact (Nat.le_lt_trans 0 n cap (Nat.le_0_l n) Hncap).
      assert (Hc1 : (Nat.succ n <= cap)%nat) by exact Hncap.
      exact (KEEP2 x (av_ifoot_in o kids keys cap (Nat.succ n) (Di ++ Dk ++ Dv) x D0 Hc0 Hc1 HSB HDIKV Hx)). }
  (* the cursor, the text, the node's place and the ledger at the return state (the cursor call-keep statement at the
     walk's relation) *)
  set (pc2 := text + len - Z.of_nat (length (PjGrammar.skip (rest_atR tb text pc)))).
  assert (Hrest2 : rest_atR tb text pc2 = PjGrammar.skip r) by (unfold pc2; rewrite av_skip_rest by exact Hlen; rewrite Hrest; reflexivity).
  pose proof (skip_len r) as Hskl.
  assert (HCUR2 : pi_cur (rc := rc) (cp := cp) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B regs0 e q v
    text len tb d ly2 S2 Hp2 W2 mem2 pc2 Lamc peakc cntc failc ranc most own).
  { apply (HCURK WR regs0 e q v text len tb d lyc Sc Hpc Wc (ms_mem ms) _ pc Lamc peakc cntc failc ranc most own
      STK_skip_ws (spZ regs0 + e + - (144 + e)) (144 + e) [(q, q + 8)] [] ly2 S2 Hp2 W2 mem2 md2 k1
      pc2 Lamc peakc cntc failc ranc most own [] HCUR1 HJ1 HX).
    - lia.
    - lia.
    - lia.
    - rewrite Eslo. lia.
    - rewrite Eshi. lia.
    - destruct HHOME as [[(b & m & Hb & H1 & H2) | [Hro | Hki]] | (b & m & Hb & _ & H1 & H2)].
      + right; right. pose proof HLG as (_ & _ & HFc & _).
        pose proof (proj1 (Forall_forall _ _) HFc (b, m) Hb) as (Hm0 & Hab0 & _). cbn [fst snd] in Hm0, Hab0.
        exists (b - cf_head), (m + cf_head). split; [exact Hab0 | lia].
      + left. exact Hro.
      + right; left. exact Hki.
      + right; right. exists b, m. split; [exact Hb | lia].
    - intros b m Hb _. split; [rewrite Hab; exact Hb | rewrite HHp; tauto].
    - intros a Ha (rr & Hrr & Hra). destruct Hrr as [<- | []]. cbn [fst snd] in Hra. lia.
    - intros a Ha (rr & Hrr & Hra). destruct Hrr as [<- | []]. cbn [fst snd] in Hra. unfold shadow_of_addr in Hra.
      pose proof (Z.div_lt_upper_bound a 8 (2 ^ 44) ltac:(lia) ltac:(lia)). unfold SHADOW_OFF in Hra. lia.
    - intros a Ha (rr & Hrr & Hra). destruct Hrr as [<- | []]. cbn [fst snd] in Hra. unfold shadow_of_addr in Hra.
      pose proof (Z.div_lt_upper_bound a 8 (2 ^ 44) ltac:(lia) ltac:(lia)). unfold SHADOW_OFF in Hra. lia.
    - intros (rr & Hrr & Hra). destruct Hrr as [<- | []]. cbn [fst snd] in Hra. lia.
    - left. exact Hin2.
    - exact Hled2.
    - rewrite Hrest2. lia.
    - left. reflexivity.
    - intros a kk Hak _. exact Hak.
    - exact Hspq.
    - exact Hqe.
    - intros a kk Hak. left. exact Hak.
    - exact HARr. }
  (* THE BATCH KIT'S INVARIANTS at PV_O_SEP. The value was read, so every call so far was granted (the pre's pi_grant): the
     prefix's move is priced the same over its own trace (PItems_ledk1.pik1_move_regt) *)
  pose proof HGR as HGR'. unfold pi_grant in HGR'.
  assert (HGG : prh_granted ok0 cnt fail (PjGrammar.calls tr0))
    by (rewrite HGR'; apply PItems_ledk1.pik1_grant_granted).
  assert (Hc0 : (0 < cap)%nat) by exact (Nat.le_lt_trans 0 n cap (Nat.le_0_l n) Hncap).
  assert (Hc1 : (Nat.succ n <= cap)%nat) by exact Hncap.
  (* the prefix's blocks from the pre's memory to the return state: kept by the store (SAME1) and by skip_ws (KEEP2) *)
  assert (AGR02 : forall x, (exists b, In b D0 /\ pj_holdsR b x) -> pis_same SEGS (rdW Wc memc) (rdW W2 mem2) x).
  { intros x Hx. destruct (FOOT x Hx) as (Hx1 & Hx2). destruct (SAME1 x Hx1 Hx2) as (S1m & S1w).
    destruct (KEEP2 x Hx) as (S2m & S2w). split; [rewrite S2m; exact S1m | intros Hw; exact (S2w (S1w Hw))]. }
  assert (HKIDS : forall x, kids <= x < kids + 56 * Z.of_nat (length acc) -> exists b, In b D0 /\ pj_holdsR b x).
  { intros x Hx. exists (kids, 56 * Z.of_nat cap).
    split; [apply HSB; unfold pi_sblk, kids_blkR|unfold pj_holdsR; cbn [fst snd]; clear - Hx Hnl Hncap; lia].
    apply in_or_app. left. replace (Z.of_nat cap =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hc0; lia).
    left. reflexivity. }
  (* the members' capacity words at the return state, the new member's from the kid's (pvm_ncaps_snoc) *)
  assert (HNC2 : pi_ncaps (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) (rdW W2 mem2) kids (acc ++ [(nm, t)])).
  { apply (proj2 (pvm_ncaps_snoc (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) (rdW W2 mem2) kids acc nm t)).
    split.
    - assert (HXD : forall b x, In b Di -> pj_holdsR b x -> exists b', In b' D0 /\ pj_holdsR b' x)
        by (intros b x Hb Hx; exists b; split; [exact (HDI b Hb) | exact Hx]).
      destruct o.
      + exact (pvm_ncaps_mems (w_H Wc) memc (rdW W2 mem2) (prh_lin Lamc)
          (fun x => exists b, In b D0 /\ pj_holdsR b x) acc kids keys Di Hit HNCAPS AGR02 HKIDS HXD).
      + exact (pvm_ncaps_items (w_H Wc) memc (rdW W2 mem2) (prh_lin Lamc)
          (fun x => exists b, In b D0 /\ pj_holdsR b x) acc kids Di Hit HNCAPS AGR02 HKIDS HXD).
    - rewrite <- Hnl. change (kids + 56 * Z.of_nat n) with (pv_slot kids n).
      apply (PvB_Frees.pvf_ncap_frame SEGS t (w_H Wc) memc (rdW W2 mem2) (prh_lin Lamc) (pv_slot kids n) Dv HNDk);
        [|exact HNCt].
      intros x [Hx | (b & Hb & Hx)].
      + exact (AGR02 x (FSLOT x Hx)).
      + exact (AGR02 x (ex_intro _ b (conj (HDV b Hb) Hx))). }
  (* the completed slots' free order at S n: slot n's value subtree (the kid's tie, fv) and key (lk) appended
     (PItems_forder.v pis_fo_snoc at the pre's memory), framed to the return state on its read bytes *)
  assert (HFO2 : pi_forder (rc := rc) (cp := cp) (L := B_prog_listing) (PA := PI_prog_B) (rdW W2 mem2) (prh_lin Lamc) o
    kids keys (Nat.succ n) (Di ++ Dk ++ Dv) (acc ++ [(nm, t)]) (af ++ fv ++ lk)).
  { intros Hhd nn Hnn. apply Forall_app in Hnn as (HnnA & HnnT).
    apply Forall_inv in HnnT. cbn [snd] in HnnT.
    destruct (HFORD Hhd nn HnnA) as (Facc & HI & HM).
    destruct (HFOt Hhd nn HnnT) as (Ft & HFt & HFm).
    assert (HKm : pj_keyR SEGS (rdW Wc memc) (prh_lin Lamc) o (keys + 8 * Z.of_nat n) Dk).
    { pose proof HKEY as HK'. unfold pi_key in HK'. destruct o.
      - destruct HK' as (x & kx & -> & Hx & Hc). cbn [pj_keyR]. exists x.
        split; [exact Hx | right; exists kx; split; [exact (proj1 Hc) | reflexivity]].
      - destruct HK' as (_ & ->). reflexivity. }
    pose proof (PItems_forder.pis_fo_snoc SEGS _ _ nn o kids keys n Di Facc Dk Dv Ft HI HKm HFt) as HS1.
    exists (Facc ++ Ft ++ Dk). split.
    - apply (PRH_PjOrder.pf_oitemsR_frame SEGS nn _ _ _ _ o kids keys (Nat.succ n) (Di ++ Dk ++ Dv) _ HS1).
      + exact (PRH_PjOrder.pf_oitemsR_lblk SEGS _ _ nn o kids keys (Nat.succ n) _ _ HS1).
      + intros x Hx.
        exact (AGR02 x (av_ifoot_in o kids keys cap (Nat.succ n) (Di ++ Dk ++ Dv) x D0 Hc0 Hc1 HSB HDIKV Hx)).
    - rewrite !map_app, HM, HFm, (HLK Hhd). reflexivity. }
  (* SEGMENT SEP's pre at PV_O_SEP, from the journal at WS0 *)
  change (Z_to_bv 64 (VAL A_TEXT + PIAT PV_O_SEP)) with (w64 (VAL A_TEXT + PIAT PV_O_SEP)).
  apply (HSEP fxc fx0 ly S0 Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr ly2 S2 Hp2
    W2 mem2 md2 (k + k1) regs2 WS0 HJ2w HWS).
  unfold pv_sep_pre.
  split; [exact HFP|]. split; [exact HENT|]. split; [exact HMN2|].
  split.
  { apply (av_frame_call regs0 (ms_regs ms) regs2 W mem Wc W2 (ms_mem ms) mem2 e q v HFRM1).
    - rewrite G2. exact (eq_sym Usp).
    - rewrite (G 3%bv ltac:(cbn; tauto)). exact (eq_sym (KMS 3%bv ltac:(cbn; tauto))).
    - rewrite (G 4%bv ltac:(cbn; tauto)). exact (eq_sym (KMS 4%bv ltac:(cbn; tauto))).
    - intros a Ha. apply FRF. lia.
    - intros a Ha Hn. apply HXw; [lia | exact Hn]. }
  split.
  { unfold pi_regs.
    rewrite (G 9%bv ltac:(cbn; tauto)), (G 19%bv ltac:(cbn; tauto)), (G 18%bv ltac:(cbn; tauto)), (G 8%bv ltac:(cbn; tauto)),
      (G 20%bv ltac:(cbn; tauto)), (G 26%bv ltac:(cbn; tauto)), (G 27%bv ltac:(cbn; tauto)), (G 25%bv ltac:(cbn; tauto)),
      (G 23%bv ltac:(cbn; tauto)).
    exact HREGS. }
  split.
  { split; [exact G22|]. split; [exact G24|].
    split; [rewrite <- (Z.add_0_r (spZ regs2)); apply FRK; [lia | lia | rewrite Z.add_0_r; exact B0]|].
    split; [apply FRK; [lia | lia | exact B32]|]. split; [apply FRK; [lia | lia | exact B24]|].
    split; [apply FRK; [lia | lia | exact B16]|]. apply FRK; [lia | lia | exact B8]. }
  split; [exact G21|].
  exists f, n, cap, acc, kids, keys, (Di ++ Dk ++ Dv), nm, t, r, pc2, ok0, tr0, D0, Lamc, peakc, cntc, failc, ranc.
  split; [exact Hncap|].
  split.
  { apply av_cont_of_open; [|rewrite length_app, <- Hnl; cbn [List.length]; rewrite Nat.add_1_r; reflexivity].
    rewrite !map_app. cbn [map fst snd]. rewrite Nat2Z.inj_succ. exact HOPEN2. }
  split; [apply Forall_app; split; [exact HDEP | constructor; [exact Hdept | constructor]]|].
  split; [exact HAPS|]. split; [exact HPERM|]. split; [exact HRUN|].
  split; [unfold pi_led; exact (PItems_ledk1.pik1_move_regt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGG HLED)|].
  split.
  { destruct HBLK as (HB1 & HB2 & HB3 & HB4). pose proof HJ1 as (_ & _ & _ & _ & _ & Hfr2 & _). cbn [app] in Hfr2.
    refine (conj HB1 (conj _ (conj _ HB4))); [rewrite Hab; exact HB2 | rewrite Hfr2; exact HB3]. }
  split; [exact HPOSB2|]. split; [exact HLIVE2|].
  assert (HBB2 : blocks_bytes S2 = blocks_bytes Sc)
    by (rewrite (blocks_bytes_bsum B ly2 S2), Hab, <- (blocks_bytes_bsum B lyc Sc); reflexivity).
  split; [rewrite HBB2; exact HBB|]. split; [exact HOK|]. split; [exact HLS|].
  split; [exact (Hrl HRLC)|]. split; [exact HCUR2|]. split; [exact Hrest2|].
  split; [exact HN1|]. split; [exact Hf1|].
  split.
  { (* rd_room (the batch kit's tip): its live-bytes conjunct reads the state's live requests, and skip_ws keeps the state *)
    destruct HROOM as (RM1 & RM2 & RM3). split; [exact (Hrl HRLC)|]. split; [exact RM2|]. rewrite HS2e. exact RM3. }
  split; [exact HGR|]. split; [exact Hcapn|]. split; [exact HNC2|].
  exists (af ++ fv ++ lk). split; [exact HFO2 | exact HMOD].
- (* ---- THE VALUE WAS REFUSED: v->n := n + 1 (the failed kid is freed with the rest), s5 := -1, to PI_O_EPI ---- *)
  assert (H10' : getr regs 10 = w64 (2 ^ 64 - 1)) by (rewrite H10; apply bv_eq; vm_compute; reflexivity).
  pose proof (av_st_ok fxc Wc memc regs v (Z.of_nat n) (2 ^ 64 - 1) (PIAT PI_O_AFTV) R19 R22 R24 R26 H10' Hvb Hal Hnb Vn
    Hwr40) as HS.
  pose proof (av_sh_ok Wc memc regs v (Z.of_nat n) R19 R26 Hvb Hvsh HRAv) as SHOK.
  remember (Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) (Ereg regs [Z_to_bv 64 (Z.of_nat n)])) as E eqn:HE in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E3 : ew E 3 = getr regs 3) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
  assert (E4 : ew E 4 = getr regs 4) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
  assert (U19 : bv_unsigned (ew E 19) = v).
  { rewrite HE, Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl), R19. apply unsigned_lit_small. lia. }
  assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat n)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  clear HE.
  unfold pi_goalR, cfg_at. change (w64 (VAL A_TEXT + PIAT PI_O_AFTV)) with (Z_to_bv 64 (VAL A_TEXT + PIAT PI_O_AFTV)).
  pose (RUNTOF := @PI_RUNTOFR fxc rc SK B_prog_listing PL_prog_B PI_prog_B B prh_pst ARx HL LAWS).
  pose proof HS as HS0.
  pi_run_to RUNTOF HS HJ SHOK (PIAT PI_O_EPI).
  { (* the store into v + 40 (checks: the shadow test 0x87d9c on s8 = shadow (v + 40) is decided by the SH entry
       (v, 0, 56), from pv_aftv_pre's range_addressable v 56) *)
    refine (av_awr B E (2 ^ 64 - 1) (PIAT PI_O_AFTV) (STK_parse_items d + e) (spZ regs0 + e) regs0 e q v ly _ lyc Sc
      Hpc Wc memc Lamc peakc cntc failc ranc most own U19 HLG HAT _ eq_refl _); [exact Hfr0 | lia]. }
  (* the memory after the store *)
  pose proof (st_ok_mem_ok SEGS E _ _ HS) as (_ & HRG & _). cbn [ms_mem restrict] in HRG.
  destruct (av_store_post (fy := fxc) E Wc memc (ms_mem ms) v (Z.of_nat n) U19 E32 Hnb HFr HRG) as (AGR & VN1 & WR1).
  (* the overlay stays normal across the run and the store (YGcallMxmn.v memnorm_frame_of, on the full frame) *)
  lazymatch type of HS0 with context [restrict _ ?m0] =>
    pose proof (av_mn_run (fy := fxc) Wc E _ m0 ms HMN HS0 HF) as HMN1 end.
  prreg HS (21%bv : bv 5) R21'. prreg HS (2%bv : bv 5) R2'. prreg HS (3%bv : bv 5) R3'. prreg HS (4%bv : bv 5) R4'.
  pmkst HS.
  lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
    replace pcw with (w64 (VAL A_TEXT + PIAT PI_O_EPI)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
  (* the epilogue at the journal back at WS0 (the run stored nothing), its budget predicate wbudget CW 0; pi_epi_spec
     concludes SRr' at wle' with the text's fpostWFbm, which is the goal's fpostWFbmR at wle' *)
  pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HJ HWD) as HJe.
  apply (HEPI (YCbqGwild.wbudget CW 0) fxc fx0 ly S0 Hp W mem md regs0 e q v _ lyc Sc Hpc Wc _ _ k _ (-1) WS0 HJe HWS).
  unfold pi_epi_pre.
  split; [exact HFP|]. split; [exact HMN1|].
  split.
  { apply (pi_frame_kept (av_F v) regs0 regs (ms_regs ms) W mem Wc memc (ms_mem ms) e q v HFRM).
    - unfold spZ. rewrite R2', E2. reflexivity.
    - rewrite R3', E3. reflexivity.
    - rewrite R4', E4. reflexivity.
    - exact AGR.
    - intros a Ha. split; [lia|]. intros Hav. apply (proj2 (Hvown a ltac:(lia))). lia.
    - intros a Ha Hn. split; [lia|]. intros Hav. apply Hn. exists (v, v + 56).
      split; [right; right; left; reflexivity | cbn [fst snd]; lia]. }
  split; [rewrite R21'; apply bv_eq; vm_compute; reflexivity|].
  split; [apply av_post_stable|].
  intros regs'' H10''.
  destruct HRES as (HFD & HAFT).
  destruct HTAIL as (HOUT & HINJ & HFT & HMOD).
  assert (Hd : (d < PjGrammar.MAXD)%nat)
    by exact (av_d_lt d o _ ok0 tr0 f n cap acc nm Lam peak cnt fail ran most _ D0 Lamc peakc cntc failc ranc kids keys
      (Di ++ Dk ++ Dv) HRUN HLED HPERM Hncap).
  (* the refused container's header and its members at the store's memory *)
  assert (SAME1 : forall x, 4096 <= x < YM05.alloc_ceiling -> ~ (v <= x < v + 56) ->
    pis_same SEGS (rdW Wc memc) (rdW Wc (ms_mem ms)) x)
    by (intros x Hx Hxv; apply (av_same_agr (av_F v) _ _ x AGR); split; lia).
  assert (Hh1 : pj_hdrR SEGS (rdW Wc (ms_mem ms)) v (5 + pis_oz o) 0 0 kids keys (Z.of_nat n + 1) (Z.of_nat cap)).
  { rewrite <- av_ty. apply (pis_hdr_n SEGS (rdW Wc memc) (rdW Wc (ms_mem ms)) v _ 0 0 kids keys (Z.of_nat n) (Z.of_nat cap)
      (Z.of_nat n + 1) Hh); [lia | exact VN1 | |].
    - intros x Hx Hx'. unfold mbyte. rewrite (AGR x); [reflexivity | split; lia].
    - intros x Hx Hw. destruct (Z_lt_dec x (v + 40)) as [Hl|Hl]; [|destruct (Z_lt_dec x (v + 48)) as [Hl2|Hl2]].
      + apply (pi_wr_agr SEGS (av_F v) _ _ x AGR); [split; lia | exact Hw].
      + apply WR1. lia.
      + apply (pi_wr_agr SEGS (av_F v) _ _ x AGR); [split; lia | exact Hw]. }
  (* THE PARTIAL FREE ORDER (the batch-kit post's None arm): at every n' >= MAXD - d, n' = S nn with the completed slots' list
     at nn (pi_forder_at), the partial kid's tie at nn (the pre's, fv), the key, and the arrays (pis_fo_item over the
     v->n++ store), against the pre's model at ok1 = [] *)
  assert (HFOP : cf_head = PresetReqAt.HEAD -> forall nq, (PjGrammar.MAXD - d <= nq)%nat ->
    exists F, PRH_PjOrder.pj_foR SEGS (rdW Wc (ms_mem ms)) (prh_lin Lamc) nq v D0 F /\
      map (fun b => snd b + cf_head) F = prhPi_frees d o (rest_atR tb text p) ok0).
  { intros Hhd nq Hnq.
    destruct (PItems_forder.pi_forder_at _ _ o kids keys n Di acc af d HFORD Hhd Hd HDEP nq Hnq)
      as (nn & Facc & -> & Hnn & HI & HM).
    destruct (HFT Hhd nn Hnn) as (Ft & HFt & HFm).
    assert (HKm : if o then pj_keyR SEGS (rdW Wc memc) (prh_lin Lamc) true (keys + 8 * Z.of_nat n) Dk else Dk = []).
    { pose proof HKEY as HK'. unfold pi_key in HK'. destruct o.
      - destruct HK' as (x & kx & -> & Hx & Hc). cbn [pj_keyR]. exists x.
        split; [exact Hx | right; exists kx; split; [exact (proj1 Hc) | reflexivity]].
      - destruct HK' as (_ & ->). reflexivity. }
    assert (HDIV : forall b, In b (Di ++ Dv) -> In b D0)
      by (intros b Hb; apply in_app_or in Hb as [Hb|Hb]; [exact (HDI b Hb) | exact (HDV b Hb)]).
    assert (FS1 : forall x, pis_ifoot o kids keys (Z.of_nat n + 1) (Di ++ Dv) x ->
      pis_same SEGS (rdW Wc memc) (rdW Wc (ms_mem ms)) x).
    { intros x Hx. assert (EN1 : Z.of_nat n + 1 = Z.of_nat (S n)) by (rewrite Nat2Z.inj_succ; reflexivity).
      rewrite EN1 in Hx.
      assert (Hc0 : (0 < cap)%nat) by exact (Nat.le_lt_trans 0 n cap (Nat.le_0_l n) Hncap).
      destruct (FOOT x (av_ifoot_in o kids keys cap (Nat.succ n) (Di ++ Dv) x D0 Hc0 Hncap HSB HDIV Hx))
        as (Hx1 & Hx2).
      exact (SAME1 x Hx1 Hx2). }
    pose proof (PItems_forder.pis_fo_item SEGS (rdW Wc memc) (rdW Wc (ms_mem ms)) (prh_lin Lamc) v o 0 kids keys
      (Z.of_nat cap) (map snd acc) (map fst acc) Di nn Facc Dk Dv Ft) as HFI.
    rewrite Hlts in HFI.
    specialize (HFI HOPEN ltac:(apply Nat2Z.inj_lt; exact Hncap) HI HFt HKm
      ltac:(rewrite <- pvm_sblk_slots; exact HNDs) HAPkv Hh1 FS1).
    pose proof (HMOD []) as HM0. rewrite app_nil_r in HM0.
    exists ((Facc ++ Ft ++ Dk) ++ pis_slots o kids keys (Z.of_nat cap)). split.
    - apply (pvm_foR_perm SEGS _ (prh_lin Lamc) _ v (pis_slots o kids keys (Z.of_nat cap) ++ Di ++ Dk ++ Dv) D0);
        [rewrite <- pvm_sblk_slots; apply Permutation_sym; exact HPERM | exact HFI].
    - rewrite !map_app, HM, HFm, (HLK Hhd), (PItems_forder.pis_fo_slots_hb_nat cf_head o kids keys cap Hhd), HM0.
      reflexivity. }
  (* the text's post, built through its named record: the run leaves the allocator state Sc as it is, so the pre's pi_live,
     position implication and hull use (the latter over the whole call's all-granted list on this arm) are the post's;
     the OUTCOME and the injected-reading conjunct are the pre's clauses at this state *)
  assert (HR0 : jr_items ReaderRes.jr_strtod d o (rest_atR tb text p) ok0 = (None, tr0, []))
    by (pose proof (HRUN []) as HR; rewrite app_nil_r in HR; exact HR).
  pose proof (av_ledger_store B ARx LAWS lyc Sc Hpc Wc memc (ms_mem ms) mdc Lamc peakc cntc failc ranc most own regs0
    e v HARc HLG HAT ltac:(lia) Hvni AGR) as HLG1.
  unfold pi_post.
  eapply tpiP_Q_of_R.
  refine {| tpiP_run := HR0; tpiP_ledger := HLG1; tpiP_room := HRLC; tpiP_hull := HHU; tpiP_live := HLIVE;
    tpiP_pos := HPOS; tpiP_outcome := HOUT; tpiP_injected := HINJ; tpiP_ledger_move := HLED; tpiP_blocks_move := HBLK;
    tpiP_bytes := HBB; tpiP_lsum := HLS; tpiP_arm := _ |}.
  split; [exact H10''|].
  split; [exact HFOP|].
  split.
  { (* the cursor's three cells are apart from the node *)
    destruct HAFT as (p' & d' & Hp' & Hd' & Vp' & Ve' & Vd' & Hrw').
    assert (FQ : forall x, q <= x < q + 24 -> av_F v x) by (intros x Hx; split; lia).
    exists p', d'. split; [exact Hp'|]. split; [exact Hd'|].
    split; [apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ AGR); [intros kk Hkk; apply FQ; lia | exact Vp']|].
    split; [apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ AGR); [intros kk Hkk; apply FQ; lia | exact Ve']|].
    split; [apply (pi_val_agr SEGS (av_F v) _ _ _ _ _ AGR); [intros kk Hkk; apply FQ; lia | exact Vd']|].
    apply (pi_rw_agr SEGS (av_F v) _ _ _ _ AGR); [intros x Hx; apply FQ; lia | exact Hrw']. }
  assert (HOPEN1 : pis_open SEGS (rdW Wc (ms_mem ms)) (prh_lin Lamc) v o 0 kids keys (Z.of_nat cap) (Z.of_nat n + 1)
    (map snd acc) (map fst acc) Di).
  { apply (pis_frame SEGS (rdW Wc memc) (prh_lin Lamc) (rdW Wc (ms_mem ms)) (prh_lin Lamc) v o 0 kids keys (Z.of_nat cap)
      (Z.of_nat n) (map snd acc) (map fst acc) Di 0 (Z.of_nat n + 1) HOPEN Hh1); [lia | |].
    - exact (pis_open_lblk SEGS _ _ _ _ _ _ _ _ _ _ _ _ HOPEN).
    - intros x Hx. rewrite Hlts in Hx.
      destruct (FOOT x (av_ifoot_in o kids keys cap n Di x D0 ltac:(lia) ltac:(lia) HSB HDI Hx)) as (Hx1 & Hx2).
      exact (SAME1 x Hx1 Hx2). }
  assert (Ht1 : pj_fdR SEGS (rdW Wc (ms_mem ms)) (prh_lin Lamc) (PjGrammar.MAXD - Nat.succ d)
    (kids + 56 * Z.of_nat (length (map snd acc))) Dv).
  { rewrite Hlts. apply (pis_fd_frame SEGS _ (rdW Wc memc) (prh_lin Lamc) (rdW Wc (ms_mem ms)) (prh_lin Lamc) _ Dv HFD);
      [intros a kk _ Hl; exact Hl|].
    intros x [Hx | (b & Hb & Hx)].
    - destruct (FOOT x (FSLOT x Hx)) as (Hx1 & Hx2). exact (SAME1 x Hx1 Hx2).
    - destruct (FOOT x (ex_intro _ b (conj (HDV b Hb) Hx))) as (Hx1 & Hx2). exact (SAME1 x Hx1 Hx2). }
  assert (Hk1 : if o then pj_keyR SEGS (rdW Wc (ms_mem ms)) (prh_lin Lamc) true (keys + 8 * Z.of_nat (length (map snd acc))) Dk
    else Dk = []).
  { rewrite Hlts. destruct o.
    - destruct HKEY as (x & kx & -> & Hx & Hc). cbn [pj_keyR]. exists x.
      split; [|right; exists kx; split; [exact (proj1 Hc) | reflexivity]].
      apply (pi_u64_agr SEGS (av_F v) _ _ _ _ AGR); [|exact Hx]. intros y Hy.
      assert (Hyin : exists b, In b D0 /\ pj_holdsR b y).
      { exists (keys, 8 * Z.of_nat cap). split; [apply HSB; unfold pi_sblk, kids_blkR, keys_blkR|unfold pj_holdsR; cbn [fst snd]; lia].
        apply in_or_app. right. replace (Z.of_nat cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. left. reflexivity. }
      destruct (FOOT y Hyin) as (Hy1 & Hy2). split; lia.
    - destruct HKEY as (_ & ->). reflexivity. }
  rewrite (pis_maxd d Hd).
  apply (pvm_fd_perm SEGS _ (prh_lin Lamc) _ v (pis_slots o kids keys (Z.of_nat cap) ++ Di ++ Dk ++ Dv) D0).
  { rewrite <- pvm_sblk_slots. apply Permutation_sym. exact HPERM. }
  apply (pis_fd_next SEGS (rdW Wc (ms_mem ms)) (prh_lin Lamc) v o 0 kids keys (Z.of_nat cap) (Z.of_nat n + 1) (map snd acc)
    (map fst acc) Di (PjGrammar.MAXD - Nat.succ d) Dk Dv HOPEN1); [rewrite Hlts; reflexivity | exact HFts | exact Ht1 | exact Hk1
    | rewrite <- pvm_sblk_slots; exact HNDs | exact HAPkv].
Qed.

End main.
