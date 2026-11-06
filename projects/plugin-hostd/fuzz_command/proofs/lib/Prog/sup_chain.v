(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module names changed; 605 of its 653 lines of code are new or changed and 500 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0 AllocSlots.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel printf_facts_c arg_i RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM06 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import arg_i_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import xstrdup_c rec_calls_free_c answer_c rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecInv RecInvP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecSeq RecStep RecGlue RecAnsB RecTail RecStub.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecCore sprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import SupChainA SupChainB SupChainC.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import sup_chain_c.
Import ListNotations.
Open Scope Z_scope.

Lemma schh_no0 : forall ids, no0 (dec_list ids).
Proof.
  intros [|i r]; cbn [dec_list]; [intros H; destruct H|].
  apply no0_app; [apply dec_no0|].
  induction r as [|v r IH]; cbn [map concat]; [intros H; destruct H|].
  apply no0_app; [|exact IH].
  change (SPACE :: dec v) with ([SPACE] ++ dec v).
  apply no0_app; [apply no0_nz; vm_compute; reflexivity | apply dec_no0].
Qed.

Lemma schh_pw : forall {X} (Rl : X -> X -> Prop) l x y,
  pairwise Rl l -> In x l -> In y l -> x <> y -> Rl x y \/ Rl y x.
Proof.
  intros X Rl l. induction l as [|w l IH]; intros x y HP Hx Hy Hne; cbn in *; [destruct Hx|].
  destruct HP as [H1 H2]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - congruence.
  - left. exact (H1 y Hy).
  - right. exact (H1 x Hx).
  - exact (IH x y H2 Hx Hy Hne).
Qed.

Section H.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis MALLOC_PC : ms_malloc B = 0x18a0c.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis MALLOC : malloc_contract B API.
Hypothesis FREE_PC : ms_free B = 0x188cc.
Hypothesis FREE : forall fx0 : YK11.FPState, free_contract (fx := fx0) B API.
Hypothesis ARGI : forall fx0 : YK11.FPState, arg_i_contract (fx := fx0) B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis XSD : forall fx0 : YK11.FPState, xstrdup_contract (fx := fx0) B API.
Hypothesis CTX : ctx_owned B API.
Hypothesis RCF : rec_calls_free_contract B API.
Hypothesis ANSF : forall fx0 : YK11.FPState, answer_contract (fx := fx0) B API.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis SPRINTF : sprintf_c.sprintf_contract.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.

Definition sch_ret (fx0 : YK11.FPState) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (id : Z) (ids : list Z) (R : rstate) (O : list (Z * Z)) (b : sbound) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' R' O' t q,
    sup_chain_m R id ids = (R', t) /\
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    fp_kept fx0 fx' /\
    call_post_rec B (aa_MR API) SUP_CHAIN_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 q /\
    g_rec_rep (ms_segs B) L' A' mem' R' O' /\ owns_new L A O O' /\
    In (q, Z.of_nat (length t) + 1) (blocks L' A') /\ fresh_block B q (Z.of_nat (length t) + 1) /\
    ~ In q (map fst O') /\
    Mem.bytes_at (ms_segs B) mem' q (t ++ [Z_to_bv 8 0]) /\
    others_kept (ms_segs B) L A mem L' A' mem' O /\
    (forall pn, In pn (blocks L' A') ->
       (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
    (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
       ptr_addr L p + k <= q \/ q + Z.of_nat (length t) + 1 <= ptr_addr L p) /\
    Mem.bytes_at (ms_segs B) mem' rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes /\
    ro_agree (ms_segs B) mem' /\ f18_words (ms_segs B) mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_mallocs b (sup_chain_sizes id ids t)) /\
    res_ok_slots A' (sb_shift b A A').

Lemma sch_back : forall L A regs mem md id ids R O b b1 Lc Ac regs_c mc mdc Oc lp j,
  call_pre_t B API 12384 L A regs mem md ->
  (1 <= length ids <= 62)%nat -> Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes -> frm_zero fp_csr ->
  room_slots (sb_malloc (sb_malloc (sb_mallocs b [12 * Z.of_nat (length ids) + 1; Z.of_nat (length (dec id)) + 1;
                                                  Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1;
                                                  Z.of_nat (length (dec_list ids)) + 1])
      (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1)) (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1)) 745 ->
  -2 ^ 31 <= r_code R < 2 ^ 31 -> (length (r_calls R) <= 16)%nat ->
  sinvx B API 12384 (spZ regs) L A mem md O Lc Ac mc mdc
    (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids))]) Oc b (lp, 12 * Z.of_nat (length ids) + 1) ->
  sb_le b1 b ->
  sb_shift b A Ac = sb_malloc (sb_malloc (sb_malloc b1 (12 * Z.of_nat (length ids) + 1))
                      (Z.of_nat (length (dec id)) + 1)) (Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1) ->
  bytes_at rsegs mc lp (dec_list ids ++ [Z_to_bv 8 0]) ->
  getr regs_c 2 = Z_to_bv 64 (spZ regs - 80) -> getr regs_c 3 = getr regs 3 -> getr regs_c 4 = getr regs 4 ->
  getr regs_c 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr regs_c 19 = Z_to_bv 64 lp ->
  getr regs_c 24 = getr regs 24 -> getr regs_c 25 = getr regs 25 -> getr regs_c 26 = getr regs 26 ->
  getr regs_c 27 = getr regs 27 ->
  rw_cells rsegs mc (spZ regs - 80)
    [CB 8 j; C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
     C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  SR rsegs (mkCfg (@mkst fx regs_c (Z_to_bv 64 0x16c3c) mc (seg_rom rsegs)) mdc)
    (sch_ret fx L A regs mem md id ids R O b).
Proof using SEGS ERRNO_LOW GFACT GOWN AX GOTG GRD FREE_PC FREE SLACK XSD CTX ANSF RSO RIMG RFREE.
  intros L A regs mem md id ids R O b b1 Lc Ac regs_c mc mdc Oc lp j PRE HN HF GS FRM ROOM HCODE HRN SI BLE1
    EQB BX E2 E3 E4 E8 E19 E24 E25 E26 E27 FR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (SPc : spZ regs_c = bv_unsigned sp - 80) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  pose proof SI as (RJ & GR & _).
  pose proof RJ as (HM & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  assert (NE : ids <> []) by (intros E; rewrite E in HN; cbn in HN; lia).
  pose proof (sc_dec_list_len ids NE HF) as DLL.
  change (snd (sup_chain_m R id ids)) with
    (snd (rec_answer (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids])
      (REC_CHAIN, [dec id; dec (Z.of_nat (length ids)); dec_list ids]) (daemon_shape "chain") true)) in ROOM.
  assert (LT : (length (snd (rec_answer (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids])
                  (REC_CHAIN, [dec id; dec (Z.of_nat (length ids)); dec_list ids]) (daemon_shape "chain") true)) <= 16)%nat).
  { pose proof (stub_len R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids] (daemon_shape "chain") true HCODE)
      as H.
    assert (LX : (length (daemon_shape "chain") <= 16)%nat) by (apply Nat.leb_le; vm_compute; reflexivity).
    lia. }
  destruct (RecCore.rec_rep_entry rsegs G_REC REC_SC Lc Ac mc R Oc REC_CHAIN [dec id; dec (Z.of_nat (length ids))] GR HRN)
    as (P0 & (_ & _ & _ & _ & NAc & _)).
  assert (ROOMc : room_slots (sb_malloc (sb_shift b A Ac) (Z.of_nat (length (dec_list ids)) + 1))
                    (Z.of_nat (length (dec_list ids)) + 1)).
  { eapply room_slots_mono; [| | exact ROOM].
    - rewrite EQB. eapply sb_le_trans; [|apply sb_le_malloc; lia]. eapply sb_le_trans; [|apply sb_le_malloc; lia].
      unfold sb_mallocs. cbn [fold_left]. repeat apply sb_malloc_mono. exact BLE1.
    - lia. }
  assert (HALc : spZ regs_c mod 16 = 0).
  { rewrite SPc. replace (bv_unsigned sp - 80) with (bv_unsigned sp + (-5) * 16) by ring.
    rewrite Z.mod_add by lia. exact HAL. }
  apply (sch_copy B API SEGS GOWN AX ERRNO_LOW GOTG GRD GFACT SLACK (XSD fx) 12384 (bv_unsigned sp) L A mem md O
           Lc Ac mc mdc R REC_CHAIN [dec id; dec (Z.of_nat (length ids))] Oc b lp (12 * Z.of_nat (length ids) + 1)
           (dec_list ids) regs_c _ SI Hh Hl eq_refl NAc BX (schh_no0 ids) ltac:(unfold LMAX; lia) ltac:(lia) ROOMc HALc
           ltac:(rewrite SPc; unfold XSTRDUP_K, ALLOC_STACK in *; lia) ltac:(rewrite SPc; lia)
           ltac:(rewrite E4; exact HTP) E8 E19).
  intros L2 A2 R2 m2 md2 p SI2 INI2 EQ2 RP2 E21 E210 KEEP2.
  cbn [app] in SI2.
  pose proof SI2 as (RJ2 & _ & _ & _ & _ & _ & _ & _ & LIN2 & _).
  pose proof RJ2 as (HM2 & _).
  pose proof LIN2 as LIN'. unfold blocks in LIN'. apply in_map_iff in LIN' as ([q z'] & Eq & HQ).
  cbn in Eq. injection Eq as HLP HZ'. subst z'.
  pose proof (block_facts B _ LAWS L2 A2 m2 md2 lp (12 * Z.of_nat (length ids) + 1) 0 HM2 LIN2 ltac:(lia))
    as (_ & _ & LPC & _).
  assert (R2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 80))
    by exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E2).
  assert (SP2 : spZ R2 = bv_unsigned sp - 80) by (unfold spZ; rewrite R2_2; apply unsigned_lit; lia).
  assert (CP2 : call_pre B (aa_MR API) L2 A2 R2 m2 md2).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L2 A2 R2 m2 md2)).
    apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md L2 A2 m2 md2 ALLOC_STACK R2 RJ2).
    - rewrite E21. apply bv_eq. vm_compute. reflexivity.
    - rewrite SP2. replace (bv_unsigned sp - 80) with (bv_unsigned sp + (-5) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    - unfold ALLOC_STACK. lia.
    - rewrite SP2. unfold ALLOC_STACK. lia.
    - rewrite SP2. lia.
    - exact (eq_trans (RP2 4 ltac:(unfold callee_saved; lia)) (eq_trans E4 HTP)). }
  apply (sch_free B API SEGS ERRNO_LOW GFACT GOWN AX GOTG GRD FREE_PC (FREE fx) 12384 (bv_unsigned sp) L A mem md O
           L2 A2 m2 md2 _ _ b q lp (12 * Z.of_nat (length ids) + 1) R2 _ SI2 CP2
           ltac:(rewrite SP2; unfold ALLOC_STACK; lia) ltac:(rewrite SP2; lia) ltac:(lia) HQ HLP E210 INI2).
  intros L3 A3 R3 m3 md3 SI3 POST3 EQ3.
  rewrite E21.
  pose proof POST3 as (PM3 & _ & _ & _ & _ & RP3 & _).
  assert (R3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 80))
    by exact (eq_trans (RP3 2 ltac:(unfold callee_saved; lia)) R2_2).
  assert (R3_3 : getr R3 3 = getr regs 3)
    by exact (eq_trans (RP3 3 ltac:(unfold callee_saved; lia)) (eq_trans (RP2 3 ltac:(unfold callee_saved; lia)) E3)).
  assert (R3_4 : getr R3 4 = getr regs 4)
    by exact (eq_trans (RP3 4 ltac:(unfold callee_saved; lia)) (eq_trans (RP2 4 ltac:(unfold callee_saved; lia)) E4)).
  assert (R3_8 : getr R3 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by exact (eq_trans (RP3 8 ltac:(unfold callee_saved; lia)) (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E8)).
  assert (R3_24 : getr R3 24 = getr regs 24)
    by exact (eq_trans (RP3 24 ltac:(unfold callee_saved; lia)) (eq_trans (RP2 24 ltac:(unfold callee_saved; lia)) E24)).
  assert (R3_25 : getr R3 25 = getr regs 25)
    by exact (eq_trans (RP3 25 ltac:(unfold callee_saved; lia)) (eq_trans (RP2 25 ltac:(unfold callee_saved; lia)) E25)).
  assert (R3_26 : getr R3 26 = getr regs 26)
    by exact (eq_trans (RP3 26 ltac:(unfold callee_saved; lia)) (eq_trans (RP2 26 ltac:(unfold callee_saved; lia)) E26)).
  assert (R3_27 : getr R3 27 = getr regs 27)
    by exact (eq_trans (RP3 27 ltac:(unfold callee_saved; lia)) (eq_trans (RP2 27 ltac:(unfold callee_saved; lia)) E27)).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 80)
                  [CB 8 j; C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
                   C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs mc); [exact FR|]. intros i Hi. cbn in Hi.
    apply KEEP2. rewrite SPc. lia. }
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 80)
                  [CB 8 j; C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
                   C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m2); [exact FR2|]. intros i Hi. cbn in Hi.
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW ALLOC_STACK L2 A2 R2 m2 md2 _ L3 A3 R3 m3 md3 (bv_unsigned sp - 80 + i)
                HM2 POST3 ltac:(lia) ltac:(rewrite SP2; unfold ALLOC_STACK; lia)) as [K1 K2].
    - intros H. cbv beta in H. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  destruct (mr_model B _ LAWS L3 A3 m3 md3 PM3) as (Hh3 & Hl3 & _).
  pose proof SI3 as (RJ3 & _ & _ & _ & _ & RA3 & _).
  pose proof RJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC3 & _).
  assert (FRn : rw_cells rsegs (normalize rsegs m3) (bv_unsigned sp - 80)
                  [CB 8 j; C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
                   C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply rw_cells_normalize; [exact RA3 | exact FR3 |]. intros i Hi. cbn in Hi. unfold wa. apply ro_addr_hi. lia. }
  assert (STn : stk rsegs (normalize rsegs m3) (bv_unsigned sp - 12384) (bv_unsigned sp - 80)).
  { apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC3. left. lia. }
  pose proof (bytes_at_normalize rsegs m3 _ _ RA3
                (rjr_shapes B API SEGS RIMG 12384 (bv_unsigned sp) O L A mem md L3 A3 m3 md3 RJ3 GS)) as GSn.
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q3 : reg_get R3 2 = Z_to_bv 64 (bv_unsigned sp - 80)) by exact R3_2.
    rewrite Q3.
    eapply (evt_normalize rsegs); [exact WX | exact RA3 |].
    eapply (sch_after RSO); [exact FRn | exact STn | lia | lia | exact GSn | apply mem_inv_normalize]. }
  intros ms5 (can5 & (s5n & Q5 & REL5 & RO5) & EQ5).
  destruct Q5 as (m5n & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU5n & WM5n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL5) as [EC5 MR5r].
  revert EC5 MR5r RO5 EQ5. generalize (ms_mem can5) as m5. intros m5 EC5 MR5r RO5 EQ5. subst can5.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR5r RO5 MU5n) as MU5.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR5r RO5 WM5n) as WM5.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L3 A3 m3 md3 _ _ b m5 _ SI3 MU5 WM5
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI5.
  pose proof SI5 as (_ & _ & _ & _ & _ & RA5 & _).
  assert (E5_1 : getr R5 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_2 : getr R5 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_10 : getr R5 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs; exact R3_8).
  assert (E5_11 : getr R5 11 = Z_to_bv 64 0x10417)
    by (rewrite (getr_of_eqv _ _ 11 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_12 : getr R5 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X5 eq_refl); simp_regs; reflexivity).
  assert (RP5 : regs_preserved regs R5).
  { apply (schb_pres_step regs R5 _ X5). intros rr Hrr. unfold callee_saved in Hrr.
    assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
                 rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    clear Hrr.
    repeat (destruct CC as [CC|CC];
            [subst rr; simp_regs; first [reflexivity | exact R3_3 | exact R3_4 | exact R3_24 | exact R3_25
                                        | exact R3_26 | exact R3_27]|]).
    subst rr; simp_regs; exact R3_27. }
  assert (BLE5 : sb_le (sb_shift b A A3)
                   (sb_mallocs b [12 * Z.of_nat (length ids) + 1; Z.of_nat (length (dec id)) + 1;
                                  Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1;
                                  Z.of_nat (length (dec_list ids)) + 1])).
  { rewrite EQ3, EQ2, EQB. apply sch_bpre; [exact BLE1 | lia]. }
  assert (AK : ANSWER_K <= 12384) by (apply Z.leb_le; vm_compute; reflexivity).
  eapply SR_mono.
  { apply (sinv_answer B API SEGS ERRNO_LOW AX CTX (ANSF fx) SLACK 12384 L A regs mem md O L3 A3 R5 m5 md3
             (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids]) _ b
             (sb_mallocs b [12 * Z.of_nat (length ids) + 1; Z.of_nat (length (dec id)) + 1;
                            Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1;
                            Z.of_nat (length (dec_list ids)) + 1])
             (rec_entry G_REC REC_SC R) 0x10417
             (REC_CHAIN, [dec id; dec (Z.of_nat (length ids)); dec_list ids])
             (daemon_shape "chain") true PRE AK SI5 E5_1 ltac:(unfold spZ; rewrite E5_2; reflexivity) RP5 E5_10
             E5_11 ltac:(rewrite E5_12; reflexivity)).
    - intros _. replace (daemon_shape "chain") with REC_MOD_HOST_SHAPE by (vm_compute; reflexivity).
      apply mod_host_shape. exact RA5.
    - intros _ _. exact (ans_entry_record R REC_CHAIN _ HRN).
    - exact FRM.
    - exact BLE5.
    - eapply room_slots_mono; [| | exact ROOM].
      + apply sb_malloc_mono, sb_malloc_mono. exact BLE5.
      + lia. }
  intros c' TR.
  destruct TR as (fx'' & L' & A' & regs' & mem' & md' & O' & q' & -> & FK' & POST' & A10' & GR' & ON' & BL' & IN' & FB'
    & NQ' & BY' & OK' & AP' & RA' & F18' & INI' & REG' & BLE' & RES').
  exists fx'', L', A', regs', mem', md', (fst (sup_chain_m R id ids)), O', (snd (sup_chain_m R id ids)), q'.
  split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact FK'|].
  split; [exact POST'|].
  do 10 (split; [assumption|]).
  split.
  { rewrite SEGS. apply (shapes_kept B API SEGS RIMG RFREE _ L A regs mem md _ _ L' A' regs' mem' md' PRK POST');
      [|exact GS]. intros a Ha Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES in *. lia. }
  repeat (split; [assumption|]).
  first [exact RES' | split; [rewrite sch_mallocs_split; exact BLE' | exact RES']].
Qed.

End H.

Section H2.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis MALLOC_PC : ms_malloc B = 0x18a0c.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis MALLOC : malloc_contract B API.
Hypothesis FREE_PC : ms_free B = 0x188cc.
Hypothesis FREE : forall fx0 : YK11.FPState, free_contract (fx := fx0) B API.
Hypothesis ARGI : forall fx0 : YK11.FPState, arg_i_contract (fx := fx0) B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis XSD : forall fx0 : YK11.FPState, xstrdup_contract (fx := fx0) B API.
Hypothesis CTX : ctx_owned B API.
Hypothesis RCF : rec_calls_free_contract B API.
Hypothesis ANSF : forall fx0 : YK11.FPState, answer_contract (fx := fx0) B API.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis SPRINTF : sprintf_c.sprintf_contract.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.

Lemma sch_rest : forall L A regs mem md id ids pids R O b b1 Lc Ac regs_c mc mdc Oc lp j,
  call_pre_t B API 12384 L A regs mem md -> spZ regs <= TASK_SIZE ->
  (1 <= length ids <= 62)%nat -> Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes -> frm_zero fp_csr ->
  room_slots (sb_malloc (sb_malloc (sb_mallocs b [12 * Z.of_nat (length ids) + 1; Z.of_nat (length (dec id)) + 1;
                                                  Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1;
                                                  Z.of_nat (length (dec_list ids)) + 1])
      (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1)) (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1)) 745 ->
  -2 ^ 31 <= r_code R < 2 ^ 31 -> (length (r_calls R) <= 16)%nat ->
  sinvx B API 12384 (spZ regs) L A mem md O Lc Ac mc mdc
    (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids))]) Oc b (lp, 12 * Z.of_nat (length ids) + 1) ->
  sb_le b1 b ->
  sb_shift b A Ac = sb_malloc (sb_malloc (sb_malloc b1 (12 * Z.of_nat (length ids) + 1))
                      (Z.of_nat (length (dec id)) + 1)) (Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1) ->
  0 <= pids -> pids + 4 * Z.of_nat (length ids) <= TASK_SIZE ->
  (pids + 4 * Z.of_nat (length ids) <= spZ regs - 12384 \/ spZ regs - 80 <= pids) ->
  (pids + 4 * Z.of_nat (length ids) <= lp \/ lp + 12 * Z.of_nat (length ids) + 1 <= pids) ->
  bytes_at rsegs mc pids (concat (map le32 ids)) ->
  getr regs_c 2 = Z_to_bv 64 (spZ regs - 80) -> getr regs_c 3 = getr regs 3 -> getr regs_c 4 = getr regs 4 ->
  getr regs_c 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr regs_c 9 = Z_to_bv 64 (Z.of_nat (length ids)) ->
  getr regs_c 18 = Z_to_bv 64 pids -> getr regs_c 19 = Z_to_bv 64 lp ->
  getr regs_c 24 = getr regs 24 -> getr regs_c 25 = getr regs 25 -> getr regs_c 26 = getr regs 26 ->
  getr regs_c 27 = getr regs 27 ->
  rw_cells rsegs mc (spZ regs - 80)
    [CB 8 j; C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
     C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  SR rsegs (mkCfg (@mkst fx regs_c (Z_to_bv 64 0x16bf4) mc (seg_rom rsegs)) mdc)
    (sch_ret B API fx L A regs mem md id ids R O b).
Proof using SEGS ERRNO_LOW GFACT GOWN AX GOTG GRD FREE_PC FREE SLACK XSD CTX ANSF RSO SPRINTF RIMG RFREE.
  intros L A regs mem md id ids pids R O b b1 Lc Ac regs_c mc mdc Oc lp j PRE HTS HN HF GS FRM ROOM HCODE HRN SI BLE1
    EQB HP0 HP1 HPS HPL BYP E2 E3 E4 E8 E9 E18 E19 E24 E25 E26 E27 FR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (SPc : spZ regs_c = bv_unsigned sp - 80) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  pose proof SI as (RJ & _ & _ & _ & _ & _ & _ & _ & LIN & _).
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  pose proof (block_facts B _ LAWS Lc Ac mc mdc lp (12 * Z.of_nat (length ids) + 1) 0 HM LIN ltac:(lia))
    as (_ & _ & LPC & _).
  apply (sch_list B API SEGS GOWN AX SPRINTF 12384 (bv_unsigned sp) L A mem md O Lc Ac mc mdc _ Oc b lp ids pids regs_c _
           SI Hh Hl HN HF HP0 HP1 ltac:(rewrite SPc; lia) HPL
           ltac:(rewrite SPc; unfold sprintf_c.SPRINTF_K in *; lia) ltac:(rewrite SPc; lia) ltac:(rewrite SPc; lia)
           ltac:(intros a Ha; rewrite <- SEGS; apply HSC; left; lia) FRM BYP E9 E18 E19).
  intros fx' R' m' FK SI' BX' BYP' MU' WM' RA' R'2 R'3 R'4 R'8 R'19 R'24 R'25 R'26 R'27.
  assert (FR' : rw_cells rsegs m' (bv_unsigned sp - 80)
                  [CB 8 j; C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
                   C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transport rsegs _ mc m' _ _ FR MU' WM'). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply SR_mono.
  { apply (sch_back (fx := fx') B API SEGS ERRNO_LOW GFACT GOWN AX GOTG GRD FREE_PC FREE SLACK XSD CTX ANSF RSO RIMG RFREE
             L A regs mem md id ids R O b b1 Lc Ac R' m' mdc Oc lp j PRE HN HF GS (proj1 FK) ROOM HCODE HRN
             SI' BLE1 EQB BX' (eq_trans R'2 E2) (eq_trans R'3 E3) (eq_trans R'4 E4) (eq_trans R'8 E8) R'19
             (eq_trans R'24 E24) (eq_trans R'25 E25) (eq_trans R'26 E26) (eq_trans R'27 E27) FR'). }
  intros c' (fx'' & L' & A' & regs' & mem' & md' & R'' & O' & t & q & Q1 & Q2 & FK2 & Q3).
  exists fx'', L', A', regs', mem', md', R'', O', t, q.
  split; [exact Q1|]. split; [exact Q2|]. split; [exact (fpk_trans _ _ _ FK FK2) | exact Q3].
Qed.

End H2.

Section H3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis MALLOC_PC : ms_malloc B = 0x18a0c.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis MALLOC : malloc_contract B API.
Hypothesis FREE_PC : ms_free B = 0x188cc.
Hypothesis FREE : forall fx0 : YK11.FPState, free_contract (fx := fx0) B API.
Hypothesis ARGI : forall fx0 : YK11.FPState, arg_i_contract (fx := fx0) B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis XSD : forall fx0 : YK11.FPState, xstrdup_contract (fx := fx0) B API.
Hypothesis CTX : ctx_owned B API.
Hypothesis RCF : rec_calls_free_contract B API.
Hypothesis ANSF : forall fx0 : YK11.FPState, answer_contract (fx := fx0) B API.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis SPRINTF : sprintf_c.sprintf_contract.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.

Lemma sch_task : forall L A mem md (O : list (Z * Z)) sp pids n, aa_MR API L A mem md -> 0 < n ->
  ((sp <= pids /\ pids + n <= TASK_SIZE) \/
   (exists q k, In (q, k) (blocks L A) /\ ~ In q (map fst O) /\ q <= pids /\ pids + n <= q + k) \/
   (0 <= pids /\ pids + n <= 2 ^ 64 /\ forall i, 0 <= i < n -> Mem.ro_addr rsegs (Z_to_bv 64 (pids + i)) = true)) ->
  pids + n <= TASK_SIZE.
Proof.
  intros L A mem md O sp pids n HM Hn [(H1 & H2) | [(q & k & Hq & _ & H1 & H2) | (H1 & H2 & H3)]].
  - exact H2.
  - pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_value as (ACr & _). pose proof alloc_ceiling_lt as ACl.
    destruct (block_facts B _ LAWS L A mem md q k 0 HM Hq ltac:(lia)) as (_ & _ & QC & _). unfold TASK_SIZE in *. lia.
  - pose proof (H3 (n - 1) ltac:(lia)) as E. apply (proj1 (rs_ro_rsegs (pids + (n - 1)) ltac:(lia))) in E.
    unfold TASK_SIZE. lia.
Qed.

Lemma sch_pids : forall L A regs mem md O L' A' m' md' Rc Oc' bc lp z pids bs n,
  call_pre_t B API 12384 L A regs mem md -> ro_agree rsegs mem ->
  sinvx B API 12384 (spZ regs) L A mem md O L' A' m' md' Rc Oc' bc (lp, z) -> 0 < z ->
  bytes_at rsegs mem pids bs -> Z.of_nat (length bs) = n -> 0 < n ->
  ((spZ regs <= pids /\ pids + n <= TASK_SIZE) \/
   (exists q k, In (q, k) (blocks L A) /\ ~ In q (map fst O) /\ q <= pids /\ pids + n <= q + k) \/
   (0 <= pids /\ pids + n <= 2 ^ 64 /\ forall i, 0 <= i < n -> Mem.ro_addr rsegs (Z_to_bv 64 (pids + i)) = true)) ->
  (forall a, pids <= a < pids + n -> ~ rec_area a) ->
  bytes_at rsegs m' pids bs /\ (pids + n <= lp \/ lp + z <= pids).
Proof using SEGS ERRNO_LOW AX.
  intros L A regs mem md O L' A' m' md' Rc Oc' bc lp z pids bs n PRE RA SI Hz BX HL Hn HOME NRA.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _ & _ & _ & _ & RA' & _ & _ & LIN & LOC & _).
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & K1 & K2 & K3 & HF & HRM & HKP & _).
  pose proof (block_facts B _ LAWS L' A' m' md' lp z 0 HM LIN ltac:(lia)) as (_ & _ & LPC & _).
  split.
  - apply (bytes_at_transfer rsegs mem); [exact BX|]. intros i Hi. rewrite HL in Hi.
    destruct HOME as [(H1 & H2) | [(qb & kb & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
    + rewrite <- SEGS. refine (proj1 (HF (pids + i) _ _ _ _));
        [unfold free_a; left; unfold TASK_SIZE in *; lia | lia | lia | apply NRA; lia].
    + unfold blocks in Hq. apply in_map_iff in Hq as ([pb kb'] & E & Hpb). cbn [fst snd] in E.
      injection E as E1 E2. subst qb kb.
      rewrite <- SEGS. replace (pids + i) with (ptr_addr L pb + (pids + i - ptr_addr L pb)) by ring.
      apply (HKP pb kb' (pids + i - ptr_addr L pb) Hpb); [|lia].
      intros G. apply Hnq. exact (in_map fst O _ G).
    + rewrite (mbyte_ro_agree _ _ _ RA' (H3 i Hi)), (mbyte_ro_agree _ _ _ RA (H3 i Hi)). reflexivity.
  - destruct HOME as [(H1 & H2) | [(qb & kb & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
    + right. lia.
    + pose proof Hq as Hq0. unfold blocks in Hq. apply in_map_iff in Hq as ([pb kb'] & E & Hpb). cbn [fst snd] in E.
      injection E as E1 E2. subst qb kb.
      pose proof (rjr_others_kept B (aa_MR API) _ _ _ _ _ _ _ _ _ _ _ _ O RJ (fun pn G => G)) as OK.
      destruct (OK pb kb' Hpb ltac:(intros G; apply Hnq; exact (in_map fst O _ G))) as (Hp' & EA & _).
      assert (QIN : In (ptr_addr L pb, kb') (blocks L' A')).
      { rewrite <- EA. unfold blocks. apply in_map_iff. exists (pb, kb'). split; [reflexivity | exact Hp']. }
      assert (NEQ : (lp, z) <> (ptr_addr L pb, kb')).
      { intros Eq. pose proof Eq as Eq'. injection Eq' as Ea Eb. apply Hnq. rewrite <- Ea. rewrite <- Eq in Hq0.
        exact (in_map fst O _ (LOC Hq0)). }
      pose proof (mr_blocks_disjoint B (aa_MR API) LAWS L' A' m' md' HM) as PW.
      destruct (schh_pw _ _ _ _ PW LIN QIN NEQ) as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
    + pose proof LIN as LIN'. unfold blocks in LIN'. apply in_map_iff in LIN' as ([q z'] & Eq & HQ).
      cbn in Eq. injection Eq as HLP HZ'. subst z'.
      assert (NI : forall i, 0 <= i < z -> ~ in_img B (lp + i)).
      { intros i Hi. rewrite <- HLP. exact (ax_blocks_img AX L' A' m' md' q z i HM HQ Hi). }
      destruct (Z_le_gt_dec (pids + n) lp) as [D|D]; [left; exact D|].
      destruct (Z_le_gt_dec (lp + z) pids) as [D'|D']; [right; exact D'|]. exfalso.
      apply (NI (Z.max pids lp - lp)); [lia|].
      replace (lp + (Z.max pids lp - lp)) with (pids + (Z.max pids lp - pids)) by lia.
      apply (ro_in_img B SEGS); [lia | apply H3; lia].
Qed.

Lemma sch_mal : forall L A regs mem md id ids pids R O b Lc Ac regs_c mc mdc Oc j,
  call_pre_t B API 12384 L A regs mem md -> spZ regs <= TASK_SIZE ->
  (1 <= length ids <= 62)%nat -> Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids -> -2 ^ 31 <= id < 2 ^ 31 ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes -> frm_zero fp_csr ->
  room_slots (sb_malloc (sb_malloc (sb_mallocs b [12 * Z.of_nat (length ids) + 1; Z.of_nat (length (dec id)) + 1;
                                                  Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1;
                                                  Z.of_nat (length (dec_list ids)) + 1])
      (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1)) (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1)) 745 ->
  -2 ^ 31 <= r_code R < 2 ^ 31 -> (length (r_calls R) <= 16)%nat ->
  sinv B API 12384 (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_CHAIN []) Oc b ->
  sb_le (sb_shift b A Ac) b ->
  0 <= pids -> pids + 4 * Z.of_nat (length ids) <= TASK_SIZE ->
  (pids + 4 * Z.of_nat (length ids) <= spZ regs - 12384 \/ spZ regs - 80 <= pids) ->
  (forall L' A' m' md' Oc' lp,
     sinvx B API 12384 (spZ regs) L A mem md O L' A' m' md'
       (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids))]) Oc' b (lp, 12 * Z.of_nat (length ids) + 1) ->
     bytes_at rsegs m' pids (concat (map le32 ids)) /\
     (pids + 4 * Z.of_nat (length ids) <= lp \/ lp + 12 * Z.of_nat (length ids) + 1 <= pids)) ->
  getr regs_c 1 = Z_to_bv 64 0x16bd4 ->
  getr regs_c 2 = Z_to_bv 64 (spZ regs - 80) -> getr regs_c 3 = getr regs 3 -> getr regs_c 4 = getr regs 4 ->
  getr regs_c 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr regs_c 9 = Z_to_bv 64 (Z.of_nat (length ids)) ->
  getr regs_c 10 = Z_to_bv 64 (12 * Z.of_nat (length ids) + 1) ->
  getr regs_c 18 = Z_to_bv 64 pids -> getr regs_c 20 = Z_to_bv 64 id ->
  getr regs_c 24 = getr regs 24 -> getr regs_c 25 = getr regs 25 -> getr regs_c 26 = getr regs 26 ->
  getr regs_c 27 = getr regs 27 ->
  rw_cells rsegs mc (spZ regs - 80)
    [CB 8 j; C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
     C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  SR rsegs (mkCfg (@mkst fx regs_c (Z_to_bv 64 0x18a0c) mc (seg_rom rsegs)) mdc)
    (sch_ret B API fx L A regs mem md id ids R O b).
Proof using SEGS ERRNO_LOW GFACT GOWN AX MALLOC_PC GOTG GRD MALLOC FREE_PC FREE ARGI SLACK XSD CTX ANSF RSO SPRINTF
  RIMG RFREE.
  intros L A regs mem md id ids pids R O b Lc Ac regs_c mc mdc Oc j PRE HTS HN HF HID GS FRM ROOM HCODE HRN SI BLE
    HP0 HP1 HPS PIDS E1 E2 E3 E4 E8 E9 E10 E18 E20 E24 E25 E26 E27 FR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (SPc : spZ regs_c = bv_unsigned sp - 80) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  pose proof (dec_length id HID) as DL1.
  pose proof (dec_length (Z.of_nat (length ids)) ltac:(lia)) as DL2.
  assert (NE : ids <> []) by (intros E; rewrite E in HN; cbn in HN; lia).
  pose proof (sc_dec_list_len ids NE HF) as DLL.
  assert (BIG : forall s, sb_le s (sb_mallocs b [12 * Z.of_nat (length ids) + 1; Z.of_nat (length (dec id)) + 1;
                                               Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1;
                                               Z.of_nat (length (dec_list ids)) + 1]) ->
                  sb_le s (sb_malloc (sb_malloc (sb_mallocs b [12 * Z.of_nat (length ids) + 1;
                                                               Z.of_nat (length (dec id)) + 1;
                                                               Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1;
                                                               Z.of_nat (length (dec_list ids)) + 1])
                    (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1))
                    (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1))).
  { intros s H. eapply sb_le_trans; [|apply sb_le_malloc; lia]. eapply sb_le_trans; [|apply sb_le_malloc; lia].
    exact H. }
  apply (sch_mid B API SEGS ERRNO_LOW GFACT GOWN AX MALLOC_PC GOTG GRD MALLOC ARGI 12384 (bv_unsigned sp) L A mem md O
           Lc Ac mc mdc R REC_CHAIN Oc b regs_c (Z.of_nat (length ids)) id _ SI HRN E1
           ltac:(rewrite SPc; replace (bv_unsigned sp - 80) with (bv_unsigned sp + (-5) * 16) by ring;
                 rewrite Z.mod_add by lia; exact HAL)
           ltac:(rewrite E4; exact HTP) E8 E9 E10 E20 ltac:(lia) HID
           ltac:(rewrite SPc; unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK in *; lia) ltac:(rewrite SPc; lia)
           ltac:(rewrite SPc; lia) FRM).
  - eapply room_slots_mono; [| | exact ROOM]; [|lia].
    apply BIG. eapply sb_le_trans; [exact BLE|]. unfold sb_mallocs. cbn [fold_left].
    eapply sb_le_trans; [|apply sb_le_malloc; lia]. eapply sb_le_trans; [|apply sb_le_malloc; lia].
    eapply sb_le_trans; [|apply sb_le_malloc; lia]. apply sb_le_malloc; lia.
  - eapply room_slots_mono; [| | exact ROOM]; [|lia].
    apply BIG. unfold sb_mallocs. cbn [fold_left].
    eapply sb_le_trans; [|apply sb_le_malloc; lia]. eapply sb_le_trans; [|apply sb_le_malloc; lia].
    apply sb_malloc_mono, sb_malloc_mono. exact BLE.
  - eapply room_slots_mono; [| | exact ROOM]; [|lia].
    apply BIG. unfold sb_mallocs. cbn [fold_left].
    eapply sb_le_trans; [|apply sb_le_malloc; lia].
    apply sb_malloc_mono, sb_malloc_mono, sb_malloc_mono. exact BLE.
  - intros fx' L' A' R' m' md' lp p1 p2 FK SI' Hh' Hl' EQ' KEEP' R'2 R'3 R'4 R'8 R'9 R'18 R'19 R'24 R'25 R'26 R'27.
    destruct (PIDS L' A' m' md' _ lp SI') as [BYP' HPL].
    assert (FR' : rw_cells rsegs m' (bv_unsigned sp - 80)
                    [CB 8 j; C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
                     C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                     C8 (reg_get regs 1)]).
    { apply (rw_cells_transfer rsegs mc); [exact FR|]. intros i Hi. cbn in Hi.
      apply KEEP'. rewrite SPc. lia. }
    eapply SR_mono.
    { apply (sch_rest (fx := fx') B API SEGS ERRNO_LOW GFACT GOWN AX GOTG GRD FREE_PC FREE SLACK XSD CTX ANSF RSO SPRINTF
               RIMG RFREE L A regs mem md id ids pids R O b (sb_shift b A Ac) L' A' R' m' md' _ lp j PRE HTS HN HF GS
               (proj1 FK) ROOM HCODE HRN SI' BLE EQ' HP0 HP1 HPS HPL BYP' (eq_trans R'2 E2) (eq_trans R'3 E3)
               (eq_trans R'4 E4) (eq_trans R'8 E8) (eq_trans R'9 E9) (eq_trans R'18 E18) R'19
               (eq_trans R'24 E24) (eq_trans R'25 E25) (eq_trans R'26 E26) (eq_trans R'27 E27) FR'). }
    intros c' (fx'' & L'' & A'' & regs' & mem' & md'' & R'' & O' & t & q & Q1 & Q2 & FK2 & Q3).
    exists fx'', L'', A'', regs', mem', md'', R'', O', t, q.
    split; [exact Q1|]. split; [exact Q2|]. split; [exact (fpk_trans _ _ _ FK FK2) | exact Q3].
Qed.


Theorem sup_chain_holds : sup_chain_contract B API.
Proof using SEGS ERRNO_LOW GFACT GOWN AX MALLOC_PC GOTG GRD MALLOC FREE_PC FREE ARGI SLACK XSD CTX RCF ANSF RSO SPRINTF
  RIMG RFREE.
  unfold sup_chain_contract.
  intros L A regs mem md id pids ids R O b PRE A10 HID A11 A12 HN HF HPZ HP4 BY HPS HOME NRA GS GR RA FRM F18 RES ROOM.
  change (SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 SUP_CHAIN) mem (seg_rom (ms_segs B))) md)
            (sch_ret B API fx L A regs mem md id ids R O b)).
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SUP_CHAIN_K in PRE, PRK, HCEIL, HWS, HPS. unfold SUP_CHAIN.
  rewrite SEGS in GS, GR, RA, F18, HWS, BY, HOME |- *.
  rewrite sch_mallocs_split in ROOM.
  pose proof (sinv_init B API 12384 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & (G1 & G2 & G3 & G4 & G5 & G6) & _ & _ & HX & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & HCODE & _).
  assert (HP0 : 0 <= pids) by (destruct BY as (BY0 & _); exact BY0).
  assert (HT : pids + 4 * Z.of_nat (length ids) <= TASK_SIZE)
    by exact (sch_task L A mem md O (spZ regs) pids (4 * Z.of_nat (length ids)) HMR ltac:(lia) HOME).
  assert (PIDS : forall L' A' m' md' Oc' lp,
     sinvx B API 12384 (spZ regs) L A mem md O L' A' m' md'
       (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids))]) Oc' b (lp, 12 * Z.of_nat (length ids) + 1) ->
     bytes_at rsegs m' pids (concat (map le32 ids)) /\
     (pids + 4 * Z.of_nat (length ids) <= lp \/ lp + 12 * Z.of_nat (length ids) + 1 <= pids)).
  { intros L' A' m' md' Oc' lp SI'.
    destruct (sch_pids L A regs mem md O L' A' m' md' _ Oc' b lp _ pids (concat (map le32 ids)) (4 * Z.of_nat (length ids))
                PRE RA SI' ltac:(lia) BY ltac:(rewrite sc_ids_len; lia) ltac:(lia) HOME NRA) as (BX' & D).
    split; [exact BX' | lia]. }
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (HPS' : pids + 4 * Z.of_nat (length ids) <= bv_unsigned sp - 12384 \/ bv_unsigned sp - 80 <= pids)
    by (destruct HPS as [H|H]; [left|right]; lia).
  assert (ST : stk rsegs mem (bv_unsigned sp - 12384) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  set (n := length (r_calls R)) in *.
  assert (NC : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))])
    by (apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact G3]).
  destruct (Nat.lt_ge_cases n 16) as [Hn|Hn].
  - destruct (glob_rw_cells mem (0x33d58 + 56 * Z.of_nat n) 8 ltac:(unfold GLOB_LO; lia)
                ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
    apply (sch_front_lt B API SEGS GOWN AX L A regs mem md R O b (Z.of_nat (length ids)) junk _ SI0 Hh Hl ST
             ltac:(change (spZ regs) with (bv_unsigned sp); lia) NC EW A12 ltac:(lia) Hn).
    intros R1 m1 b1 j SI1 X1 FR1 ST1.
    apply (sch_mal L A regs mem md id ids pids R O b L A R1 m1 md O j PRE TS HN HF HID GS FRM ROOM HCODE ltac:(lia) SI1
             ltac:(rewrite sb_shift_refl; apply sb_le_refl) HP0 HT HPS' PIDS).
    + rewrite (getr_of_eqv _ _ 1 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 2 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 3 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 4 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn). rewrite (getr_of_eqv _ _ 8 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 9 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 10 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 18 X1 eq_refl). simp_regs. exact A11.
    + rewrite (getr_of_eqv _ _ 20 X1 eq_refl). simp_regs. exact A10.
    + rewrite (getr_of_eqv _ _ 24 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 25 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 26 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 27 X1 eq_refl). simp_regs. reflexivity.
    + exact FR1.
  - assert (H16 : n = 16%nat) by lia.
    assert (NC16 : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 16)]) by (rewrite H16 in NC; exact NC).
    apply (sch_front_eq B API SEGS GOWN AX ERRNO_LOW GOTG GRD RCF L A regs mem md R O b (Z.of_nat (length ids)) _ SI0
             Hh Hl ST ltac:(change (spZ regs) with (bv_unsigned sp); lia) HAL HTP NC16 A12 ltac:(lia) H16).
    intros L' A' R2 m2 md' Oc' j SI2 BLE2 E1 E2 E4 E8 E9 E10 E18 E20 E3 E24 E25 E26 E27 FR2.
    apply (sch_mal L A regs mem md id ids pids R O b L' A' R2 m2 md' Oc' j PRE TS HN HF HID GS FRM ROOM HCODE ltac:(lia)
             SI2 BLE2 HP0 HT HPS' PIDS E1 E2 E3 E4 ltac:(rewrite (rec_entry_full G_REC REC_SC R H16); exact E8) E9 E10
             (eq_trans E18 A11) (eq_trans E20 A10) E24 E25 E26 E27 FR2).
Qed.
End H3.
