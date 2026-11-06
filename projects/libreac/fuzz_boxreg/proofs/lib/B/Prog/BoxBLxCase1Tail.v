(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 962 of its 1056 lines of code are new or changed and 837 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase1Want.v, with its module names changed; 3911 of its 4040 lines of code are new or changed and 927 lines of the source are left out. *)
(* The tail of case 1 of the switch of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput (op & 3 = 1,
   fuzz/fuzz_boxreg.c:312-373): the segment C1_SEG_tail of BoxBLxCase1Defs.v, from the cut C1_I7 at 0x809a8
   (C1_P7 0x9fc) to the cut LI_K at 0x80b08 (LP_K 0xb5c).

   0x809a8 .. 0x809b4  reac_boxreg_find (r, mac) (HY's lh_find): known, find_result bs M known.
   0x809b8 .. 0x809c8  reac_boxreg_add (r, mac, nch) (HY's lh_add): idx and the new table bs', add_out.
   0x809cc .. 0x80a3c  the checks: a zero MAC gives idx = -1 (c1_add_zero), a legal width with known >= 0 gives
                       idx = known (c1_known), idx < 0 skips to 0x80a94; for idx >= 0 the shadow check of
                       r + 280, idx < r->n (add_held of bs'), idx <= 4, the pointer-overflow guard against ~r, and
                       bcmp (&r->box[idx], mac, 6) (HY's lh_bcmp), whose 0 follows from add_held bs' M idx.
   0x80a40 .. 0x80a4c  bnez on bcmp's 0; reac_boxreg_find again: idx (c1_find_held).
   0x80a50 .. 0x80a60  bne on it; reac_boxreg_add again: idx and bs' unchanged (c1_add_again).
   0x80a64 .. 0x80b04  bne on it; s11 = fab, s10 = n_before; for known < 0 the row's nch is nch (c1_add_pos);
                       idx = want (c1_add_want); s8 = 2^32 - 1; when want = n_before the new row's base is lf and
                       its pinned word 0 (c1_add_want).
   Every abort (__asan_handle_no_return; abort at 0x80fa4) and every shadow report is refuted: the engine decides
   each such branch from the seat's literals, atoms and atom facts, or a psrr_branch_tok case is refuted from the
   model; the shadow checks are covered by the registry block's shadow entry (mkSHE 20 0 288).

   The walk is cut at each call (TK1 at 0x809b8, TK2 at 0x809cc, TKP at 0x80a40 / 0x80a50 / 0x80a64): a phase seats
   its cut with BoxBLxSeat.v's lx_seat, closes the spill and frame regions' write windows (the code stores
   nothing), runs to the call, applies the callee's contract with YC85.v cl_callS (find, add) or YCbq.v aj_bcmp_at,
   and lands the next cut on the callee's post (lx_keep_call_fp keeps the frame, the slots, the saved words and the
   input). Values that depend on a variable are atoms of the seat's environment, never SLit of an open term; the
   index idx, which the code turns into row offsets, is split into its six values first. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import
BoxBReacBoxregInit BoxBReacBoxregFind BoxBReacBoxregAdd.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase1Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require
Boxreg reac_boxreg_add_c reac_boxreg_find_c reac_boxreg_add_inv LLVMFuzzerTestOneInput_case1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition TL_SB : Z := 0x7fff8000.
Definition TL_CB : sv := SOff LA_SB 0.
Definition TL_BSPAN : Z * Z := (TL_SB, TL_SB + 2 ^ 44 - 1).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).

Lemma tl_unwin : forall E ss ms i r,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
  regions_wf (list_upd (ss_mem ss) i (set_window r 0 0)) = true ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (list_upd (ss_mem ss) i (set_window r 0 0)) (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms i r HS Hn Hw. apply (ast_ok_pi_set_region E ss ms i r); [exact HS | exact Hn | | exact Hw |].
  - destruct r. reflexivity.
  - apply region_ok_rewindow; [exact (st_ok_pi_region_nth E ss ms i r HS Hn) | intros o Ho; lia].
Qed.

Lemma tl_awr_ro : forall E rs STK sp0 FP bl0 blc ly own,
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
  intros E rs. induction rs as [|r rs IH]; intros STK sp0 FP bl0 blc ly own H; [apply awr_ok_nil|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  apply awr_ok_cons_ro; [exact H1 | exact (IH _ _ _ _ _ _ _ H2)].
Qed.

Ltac tl_unwin_tac HS i :=
  let H := fresh "HSu" in
  pose proof (tl_unwin _ _ _ i _ HS ltac:(reflexivity) ltac:(vm_compute; reflexivity)) as H;
  clear HS; rename H into HS;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.


Definition tmem (i : nat) (cx : lxcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (q : nat) (r fab : Z)
  (bs M : list byte) (nch nz lf : Z) : Prop :=
  lprev cx fp W3 ms3 bs /\ lcur cx W3 ms3 q /\ lslots_loop cx fp W3 ms3 r fab /\
  lslot cx W3 ms3 0x58 (Z.of_nat i) /\ lslot cx W3 ms3 0x48 (Boxreg.bx_n bs) /\
  c1_read cx fp W3 ms3 M nch /\ c1_nz cx W3 ms3 M nz /\ lslot cx W3 ms3 0x20 (lf mod 2 ^ 64).

Definition tcore (i : nat) (cx : lxcx) (fp pc k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (q : nat) (r fab : Z) (bs M : list byte) (nch nz lf want w7 : Z) : Prop :=
  lx_body cx fp pc W3 ms3 LSH_iter /\ (i < 64)%nat /\
  k <= 1 + 2 * Z.of_nat i /\ acc <= LX_A1 MT + Z.of_nat i * LX_AI MT /\
  lblk B cx ly3 S3 r /\ Boxreg.boxreg_inv bs /\ Boxreg.bx_fabric bs = fab /\
  tmem i cx fp W3 ms3 q r fab bs M nch nz lf /\
  -1 <= lf <= 38 /\ LC1.c1_wantP bs M nch lf want /\ -1 <= want <= 4 /\
  0 <= w7 < 2 ^ 64 /\ (Z.land w7 1 = 0 <-> reac_boxreg_add_c.add_width_ok nch fab) /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) /\
  getr (ms_regs ms3) 25 = w64 want /\ getr (ms_regs ms3) 26 = w64 (Boxreg.bx_n bs) /\
  getr (ms_regs ms3) 27 = w64 fab.

Definition TK1 (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (q : nat) (r fab : Z) (bs M : list byte) (nch nz lf want w7 known : Z),
  tcore i cx fp 0xa0c k acc ly3 S3 W3 ms3 q r fab bs M nch nz lf want w7 /\
  lreg W3 ms3 r bs /\ reac_boxreg_find_c.find_result bs M known /\
  getr (ms_regs ms3) 10 = w64 known /\ getr (ms_regs ms3) 19 = w64 (lF cx fp + 32) /\
  getr (ms_regs ms3) 23 = w64 w7.

Definition TK2 (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (q : nat) (r fab : Z) (bs M : list byte) (nch nz lf want w7 known idx : Z) (bs' : list byte),
  tcore i cx fp 0xa20 k acc ly3 S3 W3 ms3 q r fab bs M nch nz lf want w7 /\
  lreg W3 ms3 r bs' /\ reac_boxreg_find_c.find_result bs M known /\
  reac_boxreg_add_c.add_out bs M nch idx bs' /\
  getr (ms_regs ms3) 10 = w64 idx /\ getr (ms_regs ms3) 23 = w64 w7 /\ getr (ms_regs ms3) 24 = w64 known.

Definition TKP (pc : Z) (ba : bool) (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (q : nat) (r fab : Z) (bs M : list byte) (nch nz lf want w7 known idx : Z) (bs' : list byte),
  tcore i cx fp pc k acc ly3 S3 W3 ms3 q r fab bs M nch nz lf want w7 /\
  lreg W3 ms3 r bs' /\ reac_boxreg_find_c.find_result bs M known /\
  reac_boxreg_add_c.add_out bs M nch idx bs' /\ 0 <= idx /\
  getr (ms_regs ms3) 10 = w64 (if ba then idx else 0) /\ getr (ms_regs ms3) 19 = w64 idx /\
  getr (ms_regs ms3) 23 = w64 (r + 56 * idx) /\ getr (ms_regs ms3) 24 = w64 known.

Lemma tl_keep_eq : forall cx fp (W3 : world SEGS) rs m m',
  mrestrict (w_H W3) m' = mrestrict (w_H W3) m -> lx_keep cx fp W3 rs m m'.
Proof. intros cx fp W3 rs m m' H a _. unfold aview. rewrite H. reflexivity. Qed.

Lemma tl_reg_kept : forall (regs regs' : bvmap 5 word) (rr : bv 5),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned rr) -> getr regs' rr = getr regs rr.
Proof.
  intros regs regs' rr HP Hc. rewrite <- (Z_to_bv_bv_unsigned 5 rr). apply HP. exact Hc.
Qed.

Lemma tl_byte_keep : forall cx fp (W3 : world SEGS) rs (ms ms' : machine_state) a v,
  lx_keep cx fp W3 rs (ms_mem ms) (ms_mem ms') -> lx_keep_at cx fp rs a ->
  lview W3 ms a = v -> lview W3 ms' a = v.
Proof. intros cx fp W3 rs ms ms' a v Hk Ha H. unfold lview in *. rewrite (Hk a Ha). exact H. Qed.

Lemma tl_tmem_keep : forall i cx fp (W3 : world SEGS) rs (ms ms' : machine_state) q r fab bs M nch nz lf,
  lx_base B MT cx -> lx_keep cx fp W3 rs (ms_mem ms) (ms_mem ms') ->
  tmem i cx fp W3 ms q r fab bs M nch nz lf -> tmem i cx fp W3 ms' q r fab bs M nch nz lf.
Proof.
  intros i cx fp W3 rs ms ms' q r fab bs M nch nz lf HB Hk
    (HP & HC & HL & S58 & S48 & ((HML & HMB) & S50 & Hn) & (S60 & Hz & Hzi) & S20).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  split; [exact (lx_prev_keep cx fp W3 rs ms ms' bs Hk HP)|].
  split; [exact (lx_cur_keep B MT cx fp W3 HB rs ms ms' q Hk HC)|].
  split; [exact (lx_slots_loop_keep B MT cx fp W3 HB rs ms ms' r fab Hk HL)|].
  split; [exact (lx_slot_keep B MT cx fp W3 HB rs ms ms' 0x58 _ Hk ltac:(lia) ltac:(lia) S58)|].
  split; [exact (lx_slot_keep B MT cx fp W3 HB rs ms ms' 0x48 _ Hk ltac:(lia) ltac:(lia) S48)|].
  split.
  { split; [split; [exact HML|] | split; [exact (lx_slot_keep B MT cx fp W3 HB rs ms ms' 0x50 _ Hk ltac:(lia) ltac:(lia) S50) | exact Hn]].
    intros j Hj. apply (tl_byte_keep cx fp W3 rs ms ms' _ _ Hk); [|exact (HMB j Hj)].
    right; right; left. rewrite Hfb. lia. }
  split; [split; [exact (lx_slot_keep B MT cx fp W3 HB rs ms ms' 0x60 _ Hk ltac:(lia) ltac:(lia) S60) | split; [exact Hz | exact Hzi]]|].
  exact (lx_slot_keep B MT cx fp W3 HB rs ms ms' 0x20 _ Hk ltac:(lia) ltac:(lia) S20).
Qed.

Lemma tl_body_mk : forall cx fp pc pc' (W3 : world SEGS) rs (ms : machine_state) regs' mem',
  lx_base B MT cx -> lx_keep cx fp W3 rs (ms_mem ms) mem' -> lx_body cx fp pc W3 ms LSH_iter ->
  lregs cx fp (mkst regs' (Z_to_bv 64 (BASE + pc')) mem' (seg_rom SEGS)) ->
  lx_body cx fp pc' W3 (mkst regs' (Z_to_bv 64 (BASE + pc')) mem' (seg_rom SEGS)) LSH_iter.
Proof.
  intros cx fp pc pc' W3 rs ms regs' mem' HB Hk HBD HR.
  set (ms' := mkst regs' (Z_to_bv 64 (BASE + pc')) mem' (seg_rom SEGS)).
  assert (Hk' : lx_keep cx fp W3 rs (ms_mem ms) (ms_mem ms')) by exact Hk.
  pose proof HBD as (_ & _ & _ & _ & _ & _ & _ & HSV & HSH & HFL & S10 & S18 & S80 & HIN).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HR|].
  split; [exact (lx_saved_keep B MT cx fp W3 HB rs ms ms' Hk' HSV)|].
  split; [apply (lx_shadow_keep cx fp W3 rs ms ms' LSH_iter Hk'); [vm_compute; congruence | exact HSH]|].
  split; [exact (lx_flag_keep cx fp W3 rs ms ms' Hk' HFL)|].
  split; [exact (lx_slot_keep B MT cx fp W3 HB rs ms ms' 0x10 _ Hk' ltac:(lia) ltac:(lia) S10)|].
  split; [exact (lx_slot_keep B MT cx fp W3 HB rs ms ms' 0x18 _ Hk' ltac:(lia) ltac:(lia) S18)|].
  split; [exact (lx_slot_keep B MT cx fp W3 HB rs ms ms' 0x80 _ Hk' ltac:(lia) ltac:(lia) S80)|].
  exact (lx_input_keep cx fp W3 rs ms ms' Hk' HIN).
Qed.

Section d.
Hypothesis HY : lx_hyps B MT.

Lemma tl_mod8_of_64 : forall a, a mod 64 = 0 -> a mod 8 = 0.
Proof.
  intros a Ha. apply Z.mod_divide in Ha; [|lia]. destruct Ha as [x ->].
  apply Z.mod_divide; [lia|]. exists (8 * x). lia.
Qed.

Lemma tl_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
  intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia].
  destruct Ha as [x ->]. destruct Hb as [y ->]. apply Z.mod_divide; [lia|]. exists (2 * x - y). lia.
Qed.

(* mac[6] at F + 32 is an object of the function's side-stack frame, addressable while the turn has it in
   scope (LSH_iter). *)
Lemma tl_mac_afobj : forall cx fp k ly3 S3 W3 (ms : machine_state) mdc,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) mdc k ->
  frames S3 = [(LX_CID, fp)] -> lshadow cx fp W3 ms LSH_iter ->
  afobj SEGS B ly3 S3 W3 (ms_mem ms) (lF cx fp + 32) 6.
Proof.
  intros cx fp k ly3 S3 W3 ms mdc HB HJ HFR HSH.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms ly3 S3 mdc k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms ly3 S3 mdc k HB HJ) as EFA.
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  pose proof asan_consts as (C1a & _).
  set (E := lx_env cx fp (ms_regs ms) ([] : list word)).
  assert (U32 : U E (SOff LA_SB 0) = SHADOW_OFF).
  { apply U_atom; [exact (lx_env_x cx fp (ms_regs ms) [] 0 ltac:(lia)) | unfold SHADOW_OFF; lia]. }
  assert (U46 : U E (SOff LA_F 0) = lF cx fp).
  { apply U_atom; [exact (lx_env_x cx fp (ms_regs ms) [] 14 ltac:(lia)) | lia]. }
  pose proof (lx_shent_frame B MT LAWS cx fp W3 ms ly3 S3 mdc k HB HJ HFR E 32 38 U32 U46 HSH
    ltac:(left; lia)) as (HRA & _).
  cbn [she_m she_lo she_hi] in HRA. rewrite U32, U46 in HRA. rewrite <- (aview_rd_of SEGS) in HRA.
  split.
  - exists LX_CID, fp. rewrite HFR. split; [left; reflexivity|]. rewrite EFA, Hfb.
    split; [unfold LX_CID; lia|]. split; [exact (tl_mod8_of_64 _ HF64)|]. lia.
  - split; [|exact HRA].
    rewrite Zplus_mod, (tl_mod8_of_64 _ HF64). reflexivity.
Qed.

(* The chain a callee sees from the realigned stack pointer, in the current layout. *)
Lemma tl_achain : forall cx fp k ly3 S3 W3 (ms : machine_state) mdc,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) mdc k ->
  lsaved cx W3 ms ->
  achain ly3 (aview SEGS (w_H W3) (ms_mem ms)) (lsp1 cx) (lsp0 cx) (lch cx).
Proof.
  intros cx fp k ly3 S3 W3 ms mdc HB HJ (Hra8 & Hsj).
  pose proof HB as (HPRE & _).
  pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT0).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
  pose proof HJ as (_ & Hly3 & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  apply (achain_ly_top (lc_ly cx)); [exact Etop|].
  apply (lx_achain cx _ (lsp1 cx)).
  - exact Hch.
  - lia.
  - unfold lsp0. lia.
  - unfold lsp0. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [x Hx]. rewrite Hx.
    apply Z.mod_divide; [lia|]. exists (2 * x). lia.
  - exact Hra4.
  - intros a Ha. eapply aview_above_of_journal; [exact HJ | exact Ha].
  - exact Hra8.
  - pose proof (Hsj 0 ltac:(lia)) as H0. replace (lsp0 cx - 16 - 8 * 0) with (lsp0 cx - 16) in H0 by lia.
    exact H0.
  - lia.
Qed.

(* What a caller-side call of reac_boxreg_find / reac_boxreg_add from this function needs: sp = sp1, s0 = sp0,
   gp, tp, ra the return slot. *)
Definition tl_callregs (cx : lxcx) (regs : bvmap 5 word) (retk : Z) : Prop :=
  getr regs 2 = w64 (lsp1 cx) /\ getr regs 8 = w64 (lsp0 cx) /\
  getr regs 3 = getr (lc_regs cx) 3 /\ getr regs 4 = getr (lc_regs cx) 4 /\
  getr regs 1 = Z_to_bv 64 (BASE + retk) /\ 0 <= retk < 2 ^ 40 /\ retk mod 2 = 0.

Lemma tl_callregs_facts : forall cx regs retk, lx_base B MT cx -> tl_callregs cx regs retk ->
  spZ regs = lsp0 cx + (lsp1 cx - lsp0 cx) /\ (lsp1 cx - lsp0 cx) mod 16 = 0 /\ lsp1 cx - lsp0 cx <= 0 /\
  -287 <= lsp1 cx - lsp0 cx /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ YK0s.ret_ok (getr regs 1) /\
  4096 <= bv_unsigned (getr regs 1) /\ s0Z regs = lsp0 cx /\ alloc_ceiling <= lsp1 cx.
Proof.
  intros cx regs retk HB (R2 & R8 & R3 & R4 & R1 & Hk & Hk2).
  pose proof HB as (HPRE & _).
  pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT0).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
  pose proof asan_consts as (C1a & _).
  pose proof (pa_B_ok (L := boxb_listing)) as (HB0 & HB1 & HB4).
  pose proof (pa_base_lo (L := boxb_listing)) as HBlo.
  split; [unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia|].
  split; [exact (tl_mod16 _ _ Hsp1al Hsp0al)|]. split; [lia|]. split; [lia|].
  split; [rewrite R3; exact Hgp|]. split; [rewrite R4; exact Htp|].
  split; [rewrite R1; exact (ret_ok_codeptr_v retk Hk Hk2)|].
  split; [rewrite R1, unsigned_lit_small by lia; lia|].
  split; [unfold s0Z; rewrite R8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  lia.
Qed.

Lemma tl_find_call : forall cx fp k ly3 S3 W3 (ms : machine_state) mdc r bs M retk,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) mdc k ->
  frames S3 = [(LX_CID, fp)] -> lblk B cx ly3 S3 r ->
  lsaved cx W3 ms -> lshadow cx fp W3 ms LSH_iter -> lreg W3 ms r bs -> c1_mac cx fp W3 ms M ->
  Boxreg.boxreg_inv bs -> tl_callregs cx (ms_regs ms) retk ->
  getr (ms_regs ms) 10 = w64 r -> getr (ms_regs ms) 11 = w64 (lF cx fp + 32) ->
  SRr SEGS W3 (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (SIGMA BB_reac_boxreg_find)) (ms_mem ms) (seg_rom SEGS)) mdc)
    (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2 z,
       c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
         [(LX_CID, fp)] ly3 S3 W3 mem2 md2 k /\
       aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 z /\
       reac_boxreg_find_c.find_result bs M z /\
       lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms) mem2).
Proof.
  intros cx fp k ly3 S3 W3 ms mdc r bs M retk HB HJ HFR HBLK HSV HSH HREG (HML & HMB) HINV HCR H10 H11.
  pose proof (lh_laws B MT HY) as LAWS.
  destruct (tl_callregs_facts cx (ms_regs ms) retk HB HCR) as (Hsp & Ho16 & Ho0 & Ho1 & Hgp & Htp & Hret & Hra4 & Hs0 & Hceil).
  pose proof HCR as (_ & _ & _ & _ & R1 & _).
  assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
  pose proof HINV as ((HL288 & HB1 & _) & _).
  assert (WSF : REAC_BOXREG_FIND_STKB = 8272) by reflexivity.
  eapply SRr_mono.
  { eapply (cl_callS B LAWS W3 (ms_regs ms) (ms_mem ms) _ LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx)
      (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 mdc k REAC_BOXREG_FIND_STKB [] 0 (lsp1 cx - lsp0 cx)
      (getr (ms_regs ms) 1) (lch cx)
      (fun ly' S' W' (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) => ly' = ly3 /\ S' = S3 /\ W' = W3 /\
         Permutation (ablocks B ly' S') (ablocks B ly3 S3) /\
         (forall i, 0 <= i < REG_SIZEB ->
            aview SEGS (w_H W') mem' (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) /\
         (forall i, 0 <= i < 6 ->
            aview SEGS (w_H W') mem' ((lF cx fp + 32) + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) /\
         exists z, getr regs' 10 = w64 z /\ reac_boxreg_find_c.find_result bs M z)).
    - exact HJ.
    - exact Hsp.
    - exact Ho16.
    - exact Ho0.
    - rewrite WSF. lia.
    - rewrite WSF. unfold LX_STK. lia.
    - exact Hgp.
    - exact Htp.
    - reflexivity.
    - exact Hret.
    - exact Hra4.
    - replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) by lia. rewrite Hs0.
      exact (tl_achain cx fp k ly3 S3 W3 ms mdc HB HJ HSV).
    - intros HPREc. rewrite pa_sigma_reac_boxreg_find.
      exact (lh_find B MT HY ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdc (lch cx) r (lF cx fp + 32) bs M HPREc H10 H11
        Hrin HL288 (fun i Hi => HREG i ltac:(unfold LX_REG, REG_SIZEB in *; lia)) HB1
        (tl_mac_afobj cx fp k ly3 S3 W3 ms mdc HB HJ HFR HSH) HML HMB).
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & (-> & -> & -> & _ & _ & _ & z & Hz & Hres)).
  split; [reflexivity|]. exists regs2, mem2, md2, z.
  split; [rewrite R1; reflexivity|].
  split; [rewrite Z.add_0_r in HJ2; exact HJ2|].
  split; [exact HP|]. split; [exact Hz|]. split; [exact Hres|].
  replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) in HJc by lia.
  apply (lx_keep_call_fp B MT LAWS cx fp W3 ms ly3 S3 mdc k HB HJ HFR [(r, LX_REG)] [] REAC_BOXREG_FIND_STKB
           (ms_mem ms) mdc mem2 md2 0 Hceil).
  - intros p n Hin. rewrite HBLK. apply in_or_app. left. exact Hin.
  - apply Forall_cons; [|apply Forall_nil]. exists LX_REG. cbn [fst snd]. split; [exact Hrin|].
    pose proof (req_size_pos LX_REG ltac:(unfold LX_REG; lia)) as [_ Hq]. unfold LX_REG in *. lia.
  - intros a _ Ha. exact (inFP_nil a Ha).
  - exact HJc.
Qed.

Ltac tl_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.


(* ---- W1: 0x809a8 .. the call of reac_boxreg_find at 0x809b4, back at 0x809b8 ---- *)
Lemma tl_w1 : forall POST i, lx_from B MT POST (TK1 i) -> lx_from B MT POST (C1_I7 B MT i).
Proof.
intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
pose proof (lh_laws B MT HY) as LAWS.
destruct HGI as (q & r & fab & bs & M & nch & nz & lf & want & w7 & HBD & HRD & HNZ & S20 & Hlf & HW & Hwant
  & Hw7 & Hw7b & R23 & R25 & R26 & R27).
destruct HBD as (HBODY & Hi64 & Hk & Hacc & HBLK & HREG & HINV & HFAB & HPREV & HCUR & HSLL & S58 & S48 & R20 & R21).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG
  & HS10 & HS18 & HS80 & HINP).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
set (E := lx_env cx fp (ms_regs ms3) ([] : list word)).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 []); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss C1_P7 (lx_sr LX_OV) LSH_iter (lx_slot_chunks [(0x68, SOff LA_F 32)]) [] 0 0 0 0 []
     (mkFacts LX_AF [] [])) (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms | apply (lx_ov_ok cx fp ms3 []); exact HREGS].
  - unfold lx_slots. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    apply (lx_slot_atom cx W3 ms3 E _ LA_F (lF cx fp) 32); [exact L68 | exact E46 | lia | lia].
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat apply Forall_cons; try apply Forall_nil; exact I.
  - split; [exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE) | split; exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
pose (RUN := paj_run B LAWS).
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch goal with HFx : frame_of _ ?rs ?m ?m' |- _ =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HFx) as HM end.
pmkst HS. clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (19%bv : bv 5) Q19.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.

unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F in E2, E8, E22, E32, E46.
assert (E20 : ew E 20 = w64 r) by (unfold E; rewrite (lx_env_reg cx fp (ms_regs ms3) [] 20 (20%bv : bv 5) eq_refl); exact R20).
assert (EF32 : Z_to_bv 64 (bv_unsigned (ew E 46) + 32) = w64 (lF cx fp + 32))
  by (rewrite E46; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
rewrite EF32 in Q11, Q19.
assert (Hk0 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms)) by (apply tl_keep_eq; exact HM).
assert (HCR : tl_callregs cx (ms_regs ms) 2572).
{ split; [rewrite Q2; exact E2|]. split; [rewrite Q8; exact E8|]. split; [rewrite Q3; exact E3|].
  split; [rewrite Q4; exact E4|]. split; [exact Q1|]. split; [lia | reflexivity]. }
pose proof HRD as (HMAC & S50 & Hnch).
eapply SRr_bind.
{ eapply (tl_find_call cx fp k ly3 S3 W3 ms _ r bs M 2572 HB HJ HFR HBLK).
  - exact (lx_saved_keep B MT cx fp W3 HB _ ms3 ms Hk0 HSAVED).
  - apply (lx_shadow_keep cx fp W3 _ ms3 ms LSH_iter Hk0); [vm_compute; congruence | exact HSH].
  - exact (lx_reg_keep cx fp W3 _ ms3 ms r bs Hk0 ltac:(left; reflexivity) HREG).
  - destruct (tl_tmem_keep i cx fp W3 _ ms3 ms q r fab bs M nch nz lf HB Hk0
      (conj HPREV (conj HCUR (conj HSLL (conj S58 (conj S48 (conj HRD (conj HNZ S20))))))))
      as (_ & _ & _ & _ & _ & (HM' & _) & _). exact HM'.
  - exact HINV.
  - exact HCR.
  - rewrite Q10. exact E20.
  - exact Q11. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & z & -> & HJ2 & HP2 & Hz & Hres & HK2).
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0xa0c)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
assert (Hk2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2) by exact (lx_keep_trans cx fp W3 _ _ _ _ Hk0 HK2).
set (ms1 := mkst regs2 (Z_to_bv 64 (BASE + 0xa0c)) mem2 (seg_rom SEGS)).
assert (Hk1 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms1)) by exact Hk2.
assert (G : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr (ms_regs ms1) rr = getr (ms_regs ms) rr)
  by (intros rr Hrr; exact (tl_reg_kept _ _ rr HP2 Hrr)).
exists q, r, fab, bs, M, nch, nz, lf, want, w7, z.
split.
{ split.
  { apply (tl_body_mk cx fp C1_P7 0xa0c W3 [(r, LX_REG)] ms3 regs2 mem2 HB Hk2 HBODY).
    split; [rewrite (G 2%bv) by tl_cs; rewrite Q2; exact E2|].
    split; [rewrite (G 8%bv) by tl_cs; rewrite Q8; exact E8|].
    split; [rewrite (G 9%bv) by tl_cs; rewrite Q9; exact E2|].
    split; [rewrite (G 3%bv) by tl_cs; rewrite Q3; exact E3|].
    split; [rewrite (G 4%bv) by tl_cs; rewrite Q4; exact E4|].
    split; [rewrite (G 18%bv) by tl_cs; rewrite Q18; exact E32|].
    rewrite (G 22%bv) by tl_cs; rewrite Q22; exact E22. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (tl_tmem_keep i cx fp W3 _ ms3 ms1 q r fab bs M nch nz lf HB Hk1
      (conj HPREV (conj HCUR (conj HSLL (conj S58 (conj S48 (conj HRD (conj HNZ S20))))))))|].
  split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7b|].
  split; [rewrite (G 20%bv) by tl_cs; rewrite Q20; exact E20|].
  split; [rewrite (G 21%bv) by tl_cs; rewrite Q21; unfold E; rewrite (lx_env_reg cx fp (ms_regs ms3) [] 21 (21%bv : bv 5) eq_refl); exact R21|].
  split; [rewrite (G 25%bv) by tl_cs; rewrite Q25; unfold E; rewrite (lx_env_reg cx fp (ms_regs ms3) [] 25 (25%bv : bv 5) eq_refl); exact R25|].
  split; [rewrite (G 26%bv) by tl_cs; rewrite Q26; unfold E; rewrite (lx_env_reg cx fp (ms_regs ms3) [] 26 (26%bv : bv 5) eq_refl); exact R26|].
  rewrite (G 27%bv) by tl_cs; rewrite Q27; unfold E; rewrite (lx_env_reg cx fp (ms_regs ms3) [] 27 (27%bv : bv 5) eq_refl); exact R27. }
split; [exact (lx_reg_keep cx fp W3 _ ms3 ms1 r bs Hk1 ltac:(left; reflexivity) HREG)|].
split; [exact Hres|]. split; [exact Hz|].
split; [rewrite (G 19%bv) by tl_cs; exact Q19|].
rewrite (G 23%bv) by tl_cs; rewrite Q23; unfold E; rewrite (lx_env_reg cx fp (ms_regs ms3) [] 23 (23%bv : bv 5) eq_refl); exact R23.
Qed.


(* The registry block is not one of the caller's blocks (lx_blk adds it once to them). *)
Lemma tl_r_fresh : forall (cx : lxcx) ly3 S3 (W3 : world SEGS) mem3 md3 r,
  AR SEGS B ly3 S3 W3 mem3 md3 -> lblk B cx ly3 S3 r -> ~ In (r, LX_REG) (ablocks B (lc_ly cx) (lc_S cx)).
Proof.
  intros cx ly3 S3 W3 mem3 md3 r HAR Hb Hin. pose proof (lh_laws B MT HY) as LAWS.
  apply in_split in Hin as (l1 & l2 & E1).
  pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (r, LX_REG) (r, LX_REG) l1 l2 [] HAR) as Hd.
  unfold lblk in Hb. rewrite Hb, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size LX_REG) with 288 in Hd. lia.
Qed.

(* No byte a phase keeps (lx_keep_at with no block of its own) lies in the registry block. *)
Lemma tl_keep_at_not_reg : forall cx fp k ly3 S3 W3 (ms : machine_state) mdc r a,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) mdc k ->
  frames S3 = [(LX_CID, fp)] -> lblk B cx ly3 S3 r ->
  lx_keep_at cx fp [] a -> ~ (r <= a < r + REG_SIZEB).
Proof.
  intros cx fp k ly3 S3 W3 ms mdc r a HB HJ HFR HBLK Ha Hr.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof HJ as (HAR3 & _).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms ly3 S3 mdc k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms ly3 S3 mdc k HB HJ) as EFA.
  assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in Hrceil, Hria. unfold REG_SIZEB in Hr.
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  assert (Hfb8 : fs_frame_bytes LX_CID / 8 = 64) by (vm_compute; reflexivity).
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - lia.
  - destruct HB as (_ & _ & _ & Hpn & _). destruct Hpn as [Hn0 | [Hn Hin]]; [lia|].
    apply in_split in Hin as (l1 & l2 & E1).
    pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms) mdc (lc_p cx, lc_n cx) (r, LX_REG) l1 l2 [] HAR3) as Hd.
    unfold lblk in HBLK. rewrite HBLK, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size LX_REG) with 288 in Hd.
    pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hq]. lia.
  - pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) mdc r LX_REG LX_CID fp HAR3 Hrin
      ltac:(rewrite HFR; left; reflexivity)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size LX_REG) with 288 in Hd.
    rewrite EFA, Hfb in Hd. rewrite Hfb in Ha. lia.
  - rewrite Hfb8 in Ha. unfold lSH, shadow_addr, SHADOW_OFF in Ha.
    exact (fshadow_not_app (lF cx fp) 64 r 288 a HF0 ltac:(lia) Hria ltac:(lia) ltac:(lia)).
  - apply Exists_exists in Ha as (x & Hx & _). destruct Hx.
Qed.

Lemma tl_add_call : forall cx fp k ly3 S3 W3 (ms : machine_state) mdc r bs M nch retk,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) mdc k ->
  frames S3 = [(LX_CID, fp)] -> lblk B cx ly3 S3 r ->
  lsaved cx W3 ms -> lshadow cx fp W3 ms LSH_iter -> lreg W3 ms r bs -> c1_mac cx fp W3 ms M ->
  Boxreg.boxreg_inv bs -> 0 <= nch < 256 -> tl_callregs cx (ms_regs ms) retk ->
  getr (ms_regs ms) 10 = w64 r -> getr (ms_regs ms) 11 = w64 (lF cx fp + 32) -> getr (ms_regs ms) 12 = w64 nch ->
  SRr SEGS W3 (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (SIGMA BB_reac_boxreg_add)) (ms_mem ms) (seg_rom SEGS)) mdc)
    (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2 z bs',
       c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
         [(LX_CID, fp)] ly3 S3 W3 mem2 md2 k /\
       aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 z /\
       reac_boxreg_add_c.add_out bs M nch z bs' /\
       (forall i, 0 <= i < LX_REG -> aview SEGS (w_H W3) mem2 (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs' (Z_to_bv 8 0)))) /\
       lx_keep cx fp W3 [] (ms_mem ms) mem2).
Proof.
  intros cx fp k ly3 S3 W3 ms mdc r bs M nch retk HB HJ HFR HBLK HSV HSH HREG (HML & HMB) HINV Hnch HCR H10 H11 H12.
  pose proof (lh_laws B MT HY) as LAWS.
  destruct (tl_callregs_facts cx (ms_regs ms) retk HB HCR) as (Hsp & Ho16 & Ho0 & Ho1 & Hgp & Htp & Hret & Hra4 & Hs0 & Hceil).
  pose proof HCR as (_ & _ & _ & _ & R1 & _).
  pose proof HJ as (HAR3 & _).
  assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
  pose proof (tl_r_fresh cx ly3 S3 W3 (ms_mem ms) mdc r HAR3 HBLK) as Hfresh.
  assert (WSA : REAC_BOXREG_ADD_STKB = 8352) by reflexivity.
  eapply SRr_mono.
  { eapply (cl_callS B LAWS W3 (ms_regs ms) (ms_mem ms) _ LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx)
      (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 mdc k REAC_BOXREG_ADD_STKB [(r, r + REG_SIZEB)] 0 (lsp1 cx - lsp0 cx)
      (getr (ms_regs ms) 1) (lch cx)
      (fun ly' S' W' (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) => ly' = ly3 /\ S' = S3 /\ W' = W3 /\
         Permutation (ablocks B ly' S') (ablocks B ly3 S3) /\
         exists z bs', getr regs' 10 = w64 z /\ reac_boxreg_add_c.add_out bs M nch z bs' /\
         (forall i, 0 <= i < REG_SIZEB ->
            aview SEGS (w_H W') mem' (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs' (Z_to_bv 8 0)))))).
    - exact HJ.
    - exact Hsp.
    - exact Ho16.
    - exact Ho0.
    - rewrite WSA. lia.
    - rewrite WSA. unfold LX_STK. lia.
    - exact Hgp.
    - exact Htp.
    - reflexivity.
    - exact Hret.
    - exact Hra4.
    - replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) by lia. rewrite Hs0.
      exact (tl_achain cx fp k ly3 S3 W3 ms mdc HB HJ HSV).
    - intros HPREc. rewrite pa_sigma_reac_boxreg_add.
      exact (lh_add B MT HY ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdc (lch cx) r (lF cx fp + 32) nch bs M HPREc H10 H11 H12
        ltac:(lia) Hrin (fun i Hi => HREG i ltac:(unfold LX_REG, REG_SIZEB in *; lia)) HINV
        (tl_mac_afobj cx fp k ly3 S3 W3 ms mdc HB HJ HFR HSH) HML HMB).
    - intros a Ha. right. apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
      exists r, LX_REG. split; [exact Hrin|]. split; [exact Hfresh|].
      change (req_size LX_REG) with 288. unfold REG_SIZEB in Ha. lia. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & (-> & -> & -> & _ & z & bs' & Hz & Hres & HBS)).
  split; [reflexivity|]. exists regs2, mem2, md2, z, bs'.
  split; [rewrite R1; reflexivity|].
  split; [rewrite Z.add_0_r in HJ2; exact HJ2|].
  split; [exact HP|]. split; [exact Hz|]. split; [exact Hres|].
  split; [intros i Hi; apply HBS; unfold LX_REG, REG_SIZEB in *; lia|].
  replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) in HJc by lia.
  apply (lx_keep_call_fp B MT LAWS cx fp W3 ms ly3 S3 mdc k HB HJ HFR [] [(r, r + REG_SIZEB)] REAC_BOXREG_ADD_STKB
           (ms_mem ms) mdc mem2 md2 0 Hceil).
  - intros p n Hin. rewrite HBLK. apply in_or_app. left. exact Hin.
  - apply Forall_nil.
  - intros a Ha Hin. apply inFP_cons in Hin as [Hin | Hin]; [|exact (inFP_nil a Hin)].
    exact (tl_keep_at_not_reg cx fp k ly3 S3 W3 ms mdc r a HB HJ HFR HBLK Ha Hin).
  - exact HJc.
Qed.


(* The registers every cut keeps, read back after a call from their values at the call. *)
Ltac tl_lregs G Q2 Q8 Q9 Q3 Q4 Q18 Q22 E2 E8 E3 E4 E32 E22 :=
  split; [rewrite (G 2%bv) by tl_cs; rewrite Q2; exact E2|];
  split; [rewrite (G 8%bv) by tl_cs; rewrite Q8; exact E8|];
  split; [rewrite (G 9%bv) by tl_cs; rewrite Q9; exact E2|];
  split; [rewrite (G 3%bv) by tl_cs; rewrite Q3; exact E3|];
  split; [rewrite (G 4%bv) by tl_cs; rewrite Q4; exact E4|];
  split; [rewrite (G 18%bv) by tl_cs; rewrite Q18; exact E32|];
  rewrite (G 22%bv) by tl_cs; rewrite Q22; exact E22.

(* A register the walk did not touch, kept by the call: its value at the seat. *)
Ltac tl_rk G Q E R :=
  rewrite G by tl_cs; rewrite Q; unfold E; erewrite lx_env_reg; [exact R | reflexivity].

(* ---- W2: 0x809b8 `mv s8, a0` .. the call of reac_boxreg_add at 0x809c8, back at 0x809cc ---- *)
Lemma tl_w2 : forall POST i, lx_from B MT POST (TK2 i) -> lx_from B MT POST (TK1 i).
Proof.
intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
pose proof (lh_laws B MT HY) as LAWS.
destruct HGI as (q & r & fab & bs & M & nch & nz & lf & want & w7 & known & HCO & HREG & HFRES & R10 & R19 & R23).
destruct HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & Hlf & HW & Hwant & Hw7 & Hw7b & R20 & R21 & R25 & R26 & R27).
pose proof HTM as (HPREV & HCUR & HSLL & S58 & S48 & HRD & HNZ & S20).
pose proof HRD as (HMAC & S50 & Hnch).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG
  & HS10 & HS18 & HS80 & HINP).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
set (ex := [w64 nch]).
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (E48 : ew E 48 = w64 nch) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa0c (lx_sr LX_OV) LSH_iter (lx_slot_chunks [(0x50, SOff 48 0)]) [] 0 0 0 0 []
     (mkFacts LX_AF [] [])) (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms | apply (lx_ov_ok cx fp ms3 ex); exact HREGS].
  - unfold lx_slots. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    apply (lx_slot_atom cx W3 ms3 E _ 48 nch 0); [rewrite Z.add_0_r; exact S50 | exact E48 | lia | lia].
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat apply Forall_cons; try apply Forall_nil; exact I.
  - split; [exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE) | split; exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
pose (RUN := paj_run B LAWS).
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch goal with HFx : frame_of _ ?rs ?m ?m' |- _ =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HFx) as HM end.
pmkst HS. clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F in E2, E8, E22, E32, E46.
assert (E20 : ew E 20 = w64 r) by (unfold E; rewrite (lx_env_reg cx fp (ms_regs ms3) ex 20 (20%bv : bv 5) eq_refl); exact R20).
assert (E19 : ew E 19 = w64 (lF cx fp + 32)) by (unfold E; rewrite (lx_env_reg cx fp (ms_regs ms3) ex 19 (19%bv : bv 5) eq_refl); exact R19).
assert (Hk0 : lx_keep cx fp W3 [] (ms_mem ms3) (ms_mem ms)) by (apply tl_keep_eq; exact HM).
assert (HCR : tl_callregs cx (ms_regs ms) 0xa20).
{ split; [rewrite Q2; exact E2|]. split; [rewrite Q8; exact E8|]. split; [rewrite Q3; exact E3|].
  split; [rewrite Q4; exact E4|]. split; [exact Q1|]. split; [lia | reflexivity]. }
pose proof (tl_tmem_keep i cx fp W3 _ ms3 ms q r fab bs M nch nz lf HB Hk0 HTM) as (_ & _ & _ & _ & _ & (HMACc & _) & _).
eapply SRr_bind.
{ eapply (tl_add_call cx fp k ly3 S3 W3 ms _ r bs M nch 0xa20 HB HJ HFR HBLK).
  - exact (lx_saved_keep B MT cx fp W3 HB _ ms3 ms Hk0 HSAVED).
  - apply (lx_shadow_keep cx fp W3 _ ms3 ms LSH_iter Hk0); [vm_compute; congruence | exact HSH].
  - exact (lx_reg_keep cx fp W3 [(r, LX_REG)] ms3 ms r bs (tl_keep_eq cx fp W3 _ _ _ HM) ltac:(left; reflexivity) HREG).
  - exact HMACc.
  - exact HINV.
  - exact Hnch.
  - exact HCR.
  - rewrite Q10. exact E20.
  - rewrite Q11. exact E19.
  - rewrite Q12. exact E48. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & z & bs' & -> & HJ2 & HP2 & Hz & Hres & HBS & HK2).
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0xa20)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
assert (Hk2 : lx_keep cx fp W3 [] (ms_mem ms3) mem2) by exact (lx_keep_trans cx fp W3 _ _ _ _ Hk0 HK2).
set (ms1 := mkst regs2 (Z_to_bv 64 (BASE + 0xa20)) mem2 (seg_rom SEGS)).
assert (Hk1 : lx_keep cx fp W3 [] (ms_mem ms3) (ms_mem ms1)) by exact Hk2.
assert (G : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr (ms_regs ms1) rr = getr (ms_regs ms) rr)
  by (intros rr Hrr; exact (tl_reg_kept _ _ rr HP2 Hrr)).
exists q, r, fab, bs, M, nch, nz, lf, want, w7, known, z, bs'.
split.
{ split.
  { apply (tl_body_mk cx fp 0xa0c 0xa20 W3 [] ms3 regs2 mem2 HB Hk2 HBODY).
    tl_lregs G Q2 Q8 Q9 Q3 Q4 Q18 Q22 E2 E8 E3 E4 E32 E22. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (tl_tmem_keep i cx fp W3 _ ms3 ms1 q r fab bs M nch nz lf HB Hk1 HTM)|].
  split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7b|].
  split; [tl_rk G Q20 E R20|].
  split; [tl_rk G Q21 E R21|].
  split; [tl_rk G Q25 E R25|].
  split; [tl_rk G Q26 E R26|].
  tl_rk G Q27 E R27. }
split; [intros j Hj; exact (HBS j Hj)|].
split; [exact HFRES|]. split; [exact Hres|]. split; [exact Hz|].
split; [tl_rk G Q23 E R23|].
tl_rk G Q24 E R10.
Qed.


(* Every byte a phase keeps lies at or above sp1 or below the allocator's ceiling, far from the bcmp wrapper's
   stack window under sp1. *)
Lemma tl_keep_at_split : forall cx fp k ly3 S3 W3 (ms : machine_state) mdc r a,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) mdc k ->
  frames S3 = [(LX_CID, fp)] -> lblk B cx ly3 S3 r ->
  lx_keep_at cx fp [(r, LX_REG)] a -> (lsp1 cx <= a < 2 ^ 64) \/ (0 <= a < alloc_ceiling).
Proof.
  intros cx fp k ly3 S3 W3 ms mdc r a HB HJ HFR HBLK Ha.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof HJ as (HAR3 & _).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms ly3 S3 mdc k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
  pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
  assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in Hrceil.
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  assert (Hfb8 : fs_frame_bytes LX_CID / 8 = 64) by (vm_compute; reflexivity).
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - left. exact Ha.
  - right. destruct HB as (_ & _ & _ & Hpn & _). destruct Hpn as [Hn0 | [Hn Hin]]; [lia|].
    assert (Hin3 : In (lc_p cx, lc_n cx) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; left; exact Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hq]. lia.
  - right. rewrite Hfb in Ha. lia.
  - right. rewrite Hfb8 in Ha. unfold lSH, shadow_addr, SHADOW_OFF in Ha.
    assert (lF cx fp / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
    assert (0 <= lF cx fp / 8) by (apply Z.div_pos; lia). lia.
  - right. apply Exists_exists in Ha as (x & [<- | []] & Hx). cbn [fst snd] in Hx. unfold LX_REG in Hx. lia.
Qed.

Lemma tl_bcmp_call : forall cx fp k ly3 S3 W3 (ms : machine_state) mdc r bs' M idx retk,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) mdc k ->
  frames S3 = [(LX_CID, fp)] -> lblk B cx ly3 S3 r ->
  lshadow cx fp W3 ms LSH_iter -> lreg W3 ms r bs' -> c1_mac cx fp W3 ms M ->
  length bs' = 288%nat -> 0 <= idx < 5 -> Boxreg.bx_mac bs' idx = M -> tl_callregs cx (ms_regs ms) retk ->
  getr (ms_regs ms) 10 = w64 (r + 56 * idx) -> getr (ms_regs ms) 11 = w64 (lF cx fp + 32) ->
  getr (ms_regs ms) 12 = w64 6 ->
  SRr SEGS W3 (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (SIGMA BB___interceptor_trampoline_bcmp)) (ms_mem ms) (seg_rom SEGS)) mdc)
    (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
         [(LX_CID, fp)] ly3 S3 W3 mem2 md2 k /\
       aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 0 /\
       lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms) mem2).
Proof.
  intros cx fp k ly3 S3 W3 ms mdc r bs' M idx retk HB HJ HFR HBLK HSH HREG (HML & HMB) HL Hidx HMAC HCR H10 H11 H12.
  pose proof (lh_laws B MT HY) as LAWS. pose proof (lh_bcmp B MT HY) as ABCMP.
  unfold lreg, lview in HREG. unfold lview in HMB.
  destruct (tl_callregs_facts cx (ms_regs ms) retk HB HCR) as (Hsp & Ho16 & Ho0 & Ho1 & Hgp & Htp & Hret & Hra4 & Hs0 & Hceil).
  pose proof HCR as (_ & _ & _ & _ & R1 & _).
  pose proof HJ as (HAR3 & _).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms ly3 S3 mdc k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms ly3 S3 mdc k HB HJ) as EFA.
  pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (Hfin : In (LX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in Hrceil, Hria.
  pose proof (tl_mac_afobj cx fp k ly3 S3 W3 ms mdc HB HJ HFR HSH) as (_ & _ & HRAm).
  assert (Hsp1' : spZ (ms_regs ms) = lsp1 cx) by lia.
  eapply SRr_mono.
  { eapply (aj_bcmp_at SEGS B LAWS pa_segs_low _ ABCMP W3 (ms_regs ms) (ms_mem ms) LX_STK (lsp0 cx) []
      (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 mdc k
      (r + 56 * idx) (lF cx fp + 32) 6 (lsp1 cx - lsp0 cx) (getr (ms_regs ms) 1) HJ H10 H11 H12).
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hsp.
    - exact Ho16.
    - exact Ho0.
    - rewrite Hes. unfold LX_STK. lia.
    - exact Hgp.
    - exact Htp.
    - reflexivity.
    - exact Hret.
    - intros a Ha. split; [|rewrite Hsp1', Hes; lia].
      replace a with (r + (a - r)) by lia. rewrite (HREG (a - r)) by (unfold LX_REG; lia). discriminate.
    - intros a Ha. split; [|rewrite Hsp1', Hes; lia].
      replace a with (lF cx fp + 32 + (a - (lF cx fp + 32))) by lia. rewrite (HMB (a - (lF cx fp + 32))) by lia. discriminate.
    - intros a Ha. rewrite Hes. lia.
    - intros a Ha. rewrite Hes. lia.
    - eapply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) mdc r LX_REG); [exact HAR3 | exact Hrin | lia | change (req_size LX_REG) with 288; lia].
    - exact (amem_range_sub_app _ _ (lF cx fp + 32) 6 HFapp HFc ltac:(lia) ltac:(lia) ltac:(lia)).
    - eapply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) mdc r LX_REG); [exact HAR3 | exact Hrin | lia | change (req_size LX_REG) with 288; lia].
    - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) mdc r LX_REG); [exact HAR3 | exact Hrin | lia | change (req_size LX_REG) with 288; lia | lia].
    - exact HRAm.
    - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) mdc LX_CID fp (lF cx fp + 32) 6 HAR3 Hfin);
        [rewrite EFA; lia | rewrite EFA, Hfb; lia | lia]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & _).
  split; [reflexivity|]. exists regs2, mem2, md2.
  split; [rewrite R1; reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
  split.
  { rewrite Hv. apply Hcmp. intros j Hj.
    rewrite (HMB j Hj).
    replace (r + 56 * idx + j) with (r + (56 * idx + j)) by lia.
    rewrite (HREG (56 * idx + j)) by (unfold LX_REG; lia).
    pose proof (proj1 (fnd_mac_eq bs' M idx HL HML Hidx) HMAC j Hj) as E. rewrite E. reflexivity. }
  intros a Ha. destruct (tl_keep_at_split cx fp k ly3 S3 W3 ms mdc r a HB HJ HFR HBLK Ha) as [Hlo | Hlo];
    apply Hfr; rewrite ?Hes; lia.
Qed.


Lemma tl_rd4_bytes : forall bs (o : nat), length bs = 288%nat -> (o + 4 <= 288)%nat -> 0 <= Boxreg.rd4 bs (Z.of_nat o) ->
  forall k, (k < 4)%nat -> nth (o + k) bs (Z_to_bv 8 0) = Z_to_bv 8 (le_byte (Boxreg.rd4 bs (Z.of_nat o)) 4 k).
Proof.
  intros bs o HL Ho Hn k Hk.
  assert (L : length (Boxreg.bsub bs (Z.of_nat o) 4) = 4%nat) by (apply Boxreg.bsub_length; lia).
  assert (Hv : bytes_le_to_Z (Boxreg.bsub bs (Z.of_nat o) 4) = Boxreg.rd4 bs (Z.of_nat o)).
  { pose proof (Boxreg.le4_range _ L) as R. unfold Boxreg.rd4 in *.
    revert Hn R. generalize (bytes_le_to_Z (Boxreg.bsub bs (Z.of_nat o) 4)). intros v Hn R.
    unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 32) with (2 ^ 32) in *.
    change (2 ^ 32 / 2) with (2 ^ 31) in *. Z.div_mod_to_equations. lia. }
  assert (E2 : nth (o + k) bs (Z_to_bv 8 0) = nth k (Boxreg.bsub bs (Z.of_nat o) 4) (Z_to_bv 8 0)).
  { unfold Boxreg.bsub. rewrite nth_firstn. change (Z.to_nat 4) with 4%nat. rewrite Nat2Z.id.
    destruct (Nat.ltb_spec k 4); [|lia]. rewrite nth_skipn. reflexivity. }
  rewrite E2. rewrite <- (BoxregRd.le_bytes_roundtrip (Boxreg.bsub bs (Z.of_nat o) 4)). rewrite L, Hv.
  rewrite fnd_nth_le_bytes by exact Hk.
  pose proof (Boxreg.rd4_range bs (Z.of_nat o)) as Hr.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, le_byte. change (bv_modulus 8) with 256.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small (Boxreg.rd4 bs (Z.of_nat o)) (2 ^ 32)) by lia.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma tl_word_val : forall (W3 : world SEGS) (ms : machine_state) r bs (o : nat),
  lreg W3 ms r bs -> length bs = 288%nat -> (o + 4 <= 288)%nat -> 0 <= Boxreg.rd4 bs (Z.of_nat o) ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (r + Z.of_nat o) 4 (Boxreg.rd4 bs (Z.of_nat o)).
Proof.
  intros W3 ms r bs o HREG HL Ho Hn kk Hkk.
  assert (HA : aview SEGS (w_H W3) (ms_mem ms) (r + (Z.of_nat o + Z.of_nat kk)) =
               Some (bv_unsigned (nth (o + kk) bs (Z_to_bv 8 0)))).
  { unfold lreg, lview in HREG. rewrite (HREG (Z.of_nat o + Z.of_nat kk)) by (unfold LX_REG; lia).
    replace (Z.to_nat (Z.of_nat o + Z.of_nat kk)) with (o + kk)%nat by lia. reflexivity. }
  destruct (aview_byte SEGS _ _ _ _ HA) as (b & Hb & Hbv & _).
  replace (r + Z.of_nat o + Z.of_nat kk) with (r + (Z.of_nat o + Z.of_nat kk)) by lia. rewrite Hb. f_equal.
  replace b with (nth (o + kk) bs (Z_to_bv 8 0)) by (apply bv_eq; lia). exact (tl_rd4_bytes bs o HL Ho Hn kk Hkk).
Qed.


Lemma tl_AI_nonneg : 0 <= LX_AI MT.
Proof.
  pose proof (lh_mtl B MT HY) as MTL. unfold LX_AI.
  pose proof (mo_malloc_nonneg MT MTL 48 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia.
Qed.

(* The landing at LP_K (0x80b08) of a walk that wrote no memory since its seat at ms3. *)
Lemma tl_land_K : forall POST i cx fp pc0 k acc ly3 S3 W3 (ms3 ms : machine_state) md E ss q r fab bs M nch nz lf want w7 bs',
  lx_from B MT POST (LI_K B MT i) -> lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) md k ->
  frames S3 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S3 acc ->
  tcore i cx fp pc0 k acc ly3 S3 W3 ms3 q r fab bs M nch nz lf want w7 -> lreg W3 ms3 r bs' ->
  Boxreg.boxreg_inv bs' -> Boxreg.bx_fabric bs' = fab -> lkept bs bs' (-1) ->
  mrestrict (w_H W3) (ms_mem ms) = mrestrict (w_H W3) (ms_mem ms3) ->
  lx_E cx fp E -> st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms) -> ss_pc ss = LP_K -> ss_resv ss = None ->
  sr_get (ss_regs ss) 2 = SOff LA_SP 0 -> sr_get (ss_regs ss) 8 = SOff LA_SP0 0 ->
  sr_get (ss_regs ss) 9 = SOff LA_SP 0 ->
  sr_get (ss_regs ss) 3 = SOff 3%nat 0 -> sr_get (ss_regs ss) 4 = SOff 4%nat 0 ->
  sr_get (ss_regs ss) 18 = SOff LA_SB 0 -> sr_get (ss_regs ss) 22 = SOff LA_FSH 0 ->
  getr (ms_regs ms) 20 = w64 r -> getr (ms_regs ms) 21 = w64 (lF cx fp + 64) ->
  getr (ms_regs ms) 24 = w64 ((-1) mod 2 ^ 32) -> getr (ms_regs ms) 27 = w64 fab ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST i cx fp pc0 k acc ly3 S3 W3 ms3 ms md E ss q r fab bs M nch nz lf want w7 bs'
    HNEXT HB HJ HFR HMO HCO HREG HINV' HFAB' HKEPT HM HE HS Hpc Hrv Hr2 Hr8 Hr9 Hr3 Hr4 Hr18 Hr22 R20 R21 R24 R27.
  destruct HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & _).
  pose proof HBODY as (_ & _ & _ & _ & _ & _ & _ & HSV & HSH & HFL & S10 & S18 & S80 & HIN).
  assert (Hk0 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms)) by (apply tl_keep_eq; exact HM).
  pose proof (tl_tmem_keep i cx fp W3 _ ms3 ms q r fab bs M nch nz lf HB Hk0 HTM)
    as (HPV & HCUR & HSLL & S58 & _).
  pose proof tl_AI_nonneg as HAI.
  apply (HNEXT cx fp k acc ly3 S3 W3 ms md HB HJ HFR HMO).
  exists q, r, fab, (-1), bs, bs'.
  split.
  { apply (lx_land cx fp W3 ms E LP_K ss LSH_iter HE HS Hpc Hrv Hr2 Hr8 Hr9 Hr3 Hr4 Hr18 Hr22).
    - exact (lx_saved_keep B MT cx fp W3 HB _ ms3 ms Hk0 HSV).
    - apply (lx_shadow_keep cx fp W3 _ ms3 ms LSH_iter Hk0); [vm_compute; congruence | exact HSH].
    - exact (lx_flag_keep cx fp W3 _ ms3 ms Hk0 HFL).
    - exact (lx_slot_keep B MT cx fp W3 HB _ ms3 ms 0x10 _ Hk0 ltac:(lia) ltac:(lia) S10).
    - exact (lx_slot_keep B MT cx fp W3 HB _ ms3 ms 0x18 _ Hk0 ltac:(lia) ltac:(lia) S18).
    - exact (lx_slot_keep B MT cx fp W3 HB _ ms3 ms 0x80 _ Hk0 ltac:(lia) ltac:(lia) S80).
    - exact (lx_input_keep cx fp W3 _ ms3 ms Hk0 HIN). }
  split; [exact Hi64|]. split; [lia|]. split; [nia|]. split; [exact HBLK|].
  split; [exact HPV|]. split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (lx_reg_keep cx fp W3 _ ms3 ms r bs' Hk0 ltac:(left; reflexivity) HREG)|].
  split; [exact HINV'|]. split; [exact HFAB'|]. split; [exact HKEPT|].
  split; [pose proof (LC1.c1_inv_n bs HINV); lia|].
  split; [exact HCUR|]. split; [exact HSLL|]. split; [exact S58|].
  split; [exact R20|]. split; [exact R21|]. split; [exact R24 | exact R27].
Qed.


Lemma tl_atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
  intros E l1. induction l1 as [|[n f] l1 IH]; intros l2 H1 H2; cbn [app atoms_ok] in *; [exact H2|].
  destruct H1 as [H1 H1']. split; [exact H1 | exact (IH l2 H1' H2)].
Qed.

Lemma tl_afact : forall E n v lo hi, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  afact_ok E n (mkAF lo hi 0).
Proof.
  intros E n v lo hi Hn Hv Hlh. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hn. unfold w64.
  rewrite unsigned_lit_small by exact Hv. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

(* The shadow address of r + 280 (spill slot 0x40), in the form the token engine matches. *)
Definition TL_SH280 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 280) (SLit 3)) (SOff LA_SB 0).

Lemma tl_slot_sh280 : forall cx (W3 : world SEGS) ms3 E r,
  lslot cx W3 ms3 0x40 (shadow_addr (r + 280)) -> ew E 20 = w64 r -> ew E LA_SB = w64 SHADOW_OFF ->
  0 <= r -> r + 288 <= 2 ^ 47 ->
  rdword (lview W3 ms3) (lsp1 cx + 0x40) = Some (bv_unsigned (sv_denot E TL_SH280)).
Proof.
  intros cx W3 ms3 E r Hs H20 H32 Hr0 Hr1. rewrite Hs. f_equal.
  change (bv_unsigned (sv_denot E TL_SH280)) with (U E TL_SH280). unfold TL_SH280.
  rewrite U_SAlu, U_SAlu, U_SOff, U_SOff, U_lit by lia. rewrite H20, H32. unfold w64.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia). cbn [zalu_raw].
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (Hd : 0 <= (r + 280) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  rewrite Z.add_0_r. rewrite (zcanon_id (r + 280)) by (unfold M64; lia).
  rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
  rewrite (zcanon_id ((r + 280) / 8)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). unfold shadow_addr. lia.
Qed.

(* The registry block as a read-only region over atom 20 (s4 = r). *)
Definition tl_regn (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 20%nat) 0 288 0 0 cs.

Lemma tl_regn_ok : forall E m r cs, ew E 20 = w64 r -> 0 <= r -> r + 288 <= 2 ^ 64 ->
  Forall (YP09.chunk_ok SEGS E m r) cs -> YP09.region_ok SEGS E m (tl_regn cs).
Proof.
  intros E m r cs H20 Hr0 Hr1 Hcs. unfold YP09.region_ok, tl_regn.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite H20. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact Hcs].
Qed.

(* A 4-byte word of the registry at offset o, as a chunk with value atom n. *)
Lemma tl_word_chunk : forall E (W3 : world SEGS) (ms : machine_state) r bs (o : nat) (n : nat) v,
  lreg W3 ms r bs -> length bs = 288%nat -> (o + 4 <= 288)%nat -> Boxreg.rd4 bs (Z.of_nat o) = v -> 0 <= v ->
  sv_denot E (SOff n 0) = Z_to_bv 64 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) r (YP09.mkChunk (Z.of_nat o) (CVal 4 (SOff n 0))).
Proof.
  intros E W3 ms r bs o n v HREG HL Ho Hv Hv0 Hn. subst v.
  pose proof (Boxreg.rd4_range bs (Z.of_nat o)) as Hr.
  apply (chunk_ok_val SEGS E _ r (Z.of_nat o) 4 (SOff n 0) (Boxreg.rd4 bs (Z.of_nat o)) Hn); [cbn; lia | cbn; lia|].
  exact (tl_word_val W3 ms r bs o HREG HL Ho Hv0).
Qed.

Lemma tl_word_chunk_lit : forall E (W3 : world SEGS) (ms : machine_state) r bs (o : nat) v,
  lreg W3 ms r bs -> length bs = 288%nat -> (o + 4 <= 288)%nat -> Boxreg.rd4 bs (Z.of_nat o) = v -> 0 <= v < 2 ^ 31 ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) r (YP09.mkChunk (Z.of_nat o) (CVal 4 (SLit v))).
Proof.
  intros E W3 ms r bs o v HREG HL Ho Hv Hv0. subst v.
  apply (chunk_ok_val SEGS E _ r (Z.of_nat o) 4 (SLit (Boxreg.rd4 bs (Z.of_nat o))) (Boxreg.rd4 bs (Z.of_nat o)));
    [reflexivity | cbn; lia | cbn; lia|].
  exact (tl_word_val W3 ms r bs o HREG HL Ho ltac:(lia)).
Qed.

(* The registry region lies apart from the seat's four regions. *)
Lemma tl_regn_disj : forall cx fp k ly3 S3 W3 (ms : machine_state) mdc r E sh scs fcs fwlo fwhi wlo whi cs,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) mdc k ->
  frames S3 = [(LX_CID, fp)] -> lblk B cx ly3 S3 r -> lx_E cx fp E -> ew E 20 = w64 r ->
  Forall (fun rg => YP09.all_disjoint E rg [tl_regn cs]) (lx_regions0 sh scs fcs fwlo fwhi wlo whi).
Proof.
  intros cx fp k ly3 S3 W3 ms mdc r E sh scs fcs fwlo fwhi wlo whi cs HB HJ HFR HBLK HE H20.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof HJ as (HAR3 & _).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms ly3 S3 mdc k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms ly3 S3 mdc k HB HJ) as EFA.
  pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
  assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in Hrceil, Hria.
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) mdc r LX_REG LX_CID fp HAR3 Hrin
    ltac:(rewrite HFR; left; reflexivity)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size LX_REG) with 288 in Hd.
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  rewrite EFA, Hfb in Hd.
  pose proof (lx_extents B MT LAWS cx fp W3 ms ly3 S3 mdc k HB HJ HFR E HE) as (U8 & U2 & U46 & U22).
  assert (UR : YP09.base_val E (Some 20%nat) = r) by (cbn [YP09.base_val]; rewrite H20; unfold w64; apply unsigned_lit_small; lia).
  assert (Hd0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : lF cx fp / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
  unfold lx_regions0, lx_saved_region, lx_spill_region, LX_SPILL, lx_frame_region,
    lx_shadow_region, fshadow_region, tl_regn.
  repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.all_disjoint]; (split; [|exact I]);
    unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi];
    rewrite ?U8, ?U2, ?U46, ?U22, ?UR; rewrite ?Hfb.
  - lia.
  - lia.
  - lia.
  - replace (512 / 8) with 64 by reflexivity. rewrite HSHe.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.


Lemma tl_bne : forall E a b, branch_taken BC_NE (sv_denot E a) (sv_denot E b) = negb (U E a =? U E b).
Proof. intros. rewrite <- branch_eq_U. reflexivity. Qed.

Lemma tl_land_or1 : forall w, Z.land (Z.lor w 1) 1 = 1.
Proof.
  intros w. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.lor_spec.
  destruct (Z.eq_dec n 0) as [->|Hne].
  - assert (T1 : Z.testbit 1 0 = true) by reflexivity. rewrite T1, orb_true_r, andb_true_r. reflexivity.
  - assert (Hb : Z.testbit 1 n = false) by (apply Z.bits_above_log2; [lia | change (Z.log2 1) with 0; lia]).
    rewrite Hb, andb_false_r. reflexivity.
Qed.

Lemma tl_lor1_lt : forall w, 0 <= w < 2 ^ 64 -> 0 <= Z.lor w 1 < 2 ^ 64.
Proof.
  intros w Hw. assert (H0 : 0 <= Z.lor w 1) by (apply Z.lor_nonneg; lia).
  split; [exact H0|].
  assert (Hpos : 0 < Z.lor w 1).
  { destruct (Z.eq_dec (Z.lor w 1) 0) as [E0|]; [|lia].
    exfalso. pose proof (tl_land_or1 w) as Hb. rewrite E0 in Hb. cbn in Hb. discriminate. }
  apply (Z.log2_lt_pow2 _ 64 Hpos). rewrite Z.log2_lor by lia.
  change (Z.log2 1) with 0.
  destruct (Z.eq_dec w 0) as [->|Hw0]; [cbn; lia|].
  assert (Z.log2 w < 64) by (apply Z.log2_lt_pow2; lia).
  pose proof (Z.log2_nonneg w). lia.
Qed.

Lemma tl_width_u0 : forall E w, ew E 23 = w64 w -> 0 <= w < 2 ^ 64 -> Z.land w 1 = 0 ->
  U E (SAlu ALU_AND (SAlu ALU_OR (SOff 23 0) (SLit 0)) (SLit 1)) = 0.
Proof.
  intros E w H23 Hw Hb.
  assert (U23 : U E (SOff 23 0) = w) by (apply (U_atom E 23 w); [rewrite H23; reflexivity | lia]).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite U23, !U_lit by lia. rewrite Z.lor_0_r, (zcanon_id w) by (unfold M64; lia).
  rewrite Hb. reflexivity.
Qed.

Lemma tl_width_u1 : forall E w, ew E 23 = w64 w -> 0 <= w < 2 ^ 64 ->
  U E (SAlu ALU_AND (SAlu ALU_OR (SOff 23 0) (SLit 1)) (SLit 1)) = 1.
Proof.
  intros E w H23 Hw.
  assert (U23 : U E (SOff 23 0) = w) by (apply (U_atom E 23 w); [rewrite H23; reflexivity | lia]).
  pose proof (tl_lor1_lt w Hw) as Hlt.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite U23, !U_lit by lia. rewrite (zcanon_id (Z.lor w 1)) by (unfold M64; lia).
  rewrite tl_land_or1. apply zcanon_id. unfold M64. lia.
Qed.


(* ---- W3: 0x809cc .. the checks after the first add; for idx >= 0 the bcmp at 0x80a3c, back at 0x80a40 ---- *)
(* The seat's spill slots (r + 280, its shadow address, nch, nonzero, mac, ~r), its extra atoms (48 nch, 49 nonzero,
   50 ~r, 51 the n of the new table) and their facts, and the registry word r->n. *)
Definition TL_SL : list (Z * sv) :=
  [(0x28, SOff 20 280); (0x40, TL_SH280); (0x50, SOff 48 0); (0x60, SOff 49 0); (0x68, SOff LA_F 32); (0x70, SOff 50 0)].
Definition TL_EX (r nch nz : Z) (bs' : list byte) : list word :=
  [w64 nch; w64 nz; w64 (2 ^ 64 - 1 - r); w64 (Boxreg.bx_n bs')].
Definition TL_AFP (z : Z) : list (nat * afact) :=
  LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (49%nat, mkAF 1 (2 ^ 64 - 1) 0);
            (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0); (51%nat, mkAF (z + 1) 5 0)].
Definition TL_RCH : list YP09.chunk := [YP09.mkChunk 280 (CVal 4 (SOff 51 0))].

Definition TW3P (z : Z) : Prop :=
  forall POST i, lx_from B MT POST (TKP 0xa94 false i) ->
  forall cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3 q r fab bs M nch nz lf want w7 known bs',
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S3 acc ->
  tcore i cx fp 0xa20 k acc ly3 S3 W3 ms3 q r fab bs M nch nz lf want w7 ->
  lreg W3 ms3 r bs' -> reac_boxreg_find_c.find_result bs M known ->
  reac_boxreg_add_c.add_out bs M nch z bs' ->
  getr (ms_regs ms3) 10 = w64 z -> getr (ms_regs ms3) 23 = w64 w7 -> getr (ms_regs ms3) 24 = w64 known ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

Lemma tl_w3_p0 : TW3P 0.
Proof.

intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs'
  HB HJ HFR HMO HCO HREG HFRES HADD R10 R23 R24.
pose proof (lh_laws B MT HY) as LAWS.
pose proof HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & Hlf & HW & Hwant & Hw7 & Hw7b & R20 & R21 & R25 & R26 & R27).
pose proof HTM as (HPREV & HCUR & HSLL & S58 & S48 & HRD & HNZ & S20).
pose proof HRD as (HMAC & S50 & Hnch). pose proof HMAC as (HML & HMB).
pose proof HNZ as (S60 & Hnzr & Hnzi).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof HJ as (HAR3 & _).
assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size LX_REG) with 288 in Hrceil, Hria.
pose proof (LC1.c1_inv_len bs HINV) as HL288. pose proof (LC1.c1_inv_n bs HINV) as HnB.
pose proof (lxc1_add_keeps bs M nch _ bs' HINV HML HADD) as (HINV' & HFAB' & HKEPT).
pose proof (LC1.c1_inv_len bs' HINV') as HL288'. pose proof (LC1.c1_inv_n bs' HINV') as HnB'.
set (ex := TL_EX r nch nz bs').
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (E48 : ew E 48 = w64 nch) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
assert (E49 : ew E 49 = w64 nz) by exact (lx_env_ex cx fp (ms_regs ms3) ex 1 ltac:(lia)).
assert (E50 : ew E 50 = w64 (2 ^ 64 - 1 - r)) by exact (lx_env_ex cx fp (ms_regs ms3) ex 2 ltac:(lia)).
assert (E51 : ew E 51 = w64 (Boxreg.bx_n bs')) by exact (lx_env_ex cx fp (ms_regs ms3) ex 3 ltac:(lia)).
assert (E20 : ew E 20 = w64 r) by (unfold E; erewrite lx_env_reg; [exact R20 | reflexivity]).
assert (E23 : ew E 23 = w64 w7) by (unfold E; erewrite lx_env_reg; [exact R23 | reflexivity]).
unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F in E2, E8, E22, E32, E46.
assert (HSL : lx_slots cx W3 ms3 E TL_SL).
{ unfold lx_slots, TL_SL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - apply (lx_slot_atom cx W3 ms3 E _ 20 r 280); [exact L28 | exact E20 | lia | lia].
  - apply (tl_slot_sh280 cx W3 ms3 E r L40 E20 E32); lia.
  - apply (lx_slot_atom cx W3 ms3 E _ 48 nch 0); [rewrite Z.add_0_r; exact S50 | exact E48 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ 49 nz 0); [rewrite Z.add_0_r; exact S60 | exact E49 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ LA_F (lF cx fp) 32); [exact L68 | exact E46 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ 50 (2 ^ 64 - 1 - r) 0); [rewrite Z.add_0_r; exact L70 | exact E50 | lia | lia]. }
assert (HRG : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (tl_regn TL_RCH)).
{ apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
  apply Forall_cons; [|apply Forall_nil].
  change 280 with (Z.of_nat 280). apply (tl_word_chunk E W3 ms3 r bs' 280 51 (Boxreg.bx_n bs') HREG HL288' ltac:(lia));
    [reflexivity | lia | rewrite lx_sv_SOff0, E51; reflexivity]. }

destruct (LC1.c1_add_pos bs M nch 0 bs' HINV HML HADD ltac:(lia)) as (HMZ & Ao & Hfab' & Hn5 & Hh' & Hcase).
destruct (LC1.c1_add_want bs M nch lf want 0 bs' HINV HML HW HADD) as (Ewant & _).
assert (Hw7z : Z.land w7 1 = 0) by (apply Hw7b; rewrite <- HFAB; exact Ao).
assert (Hnz0 : nz <> 0) by (intros E0; apply HMZ; apply Hnzi; exact E0).
pose proof (LC1.c1_find_range bs M known HFRES HnB) as Hkr.
assert (Hkn : known = -1 \/ known = 0).
{ destruct (Z_lt_ge_dec known 0) as [Hk0|Hk0]; [left; lia|].
  right. symmetry. exact (LC1.c1_known bs M nch known 0 bs' HFRES ltac:(lia) Ao HADD). }
pose proof Hh' as (Hzn & HMACz & _).
assert (HFACT : atoms_ok E (TL_AFP 0)).
{ unfold TL_AFP. apply tl_atoms_ok_app; [exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE)|].
  cbn [atoms_ok]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E20. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [change (2 ^ 4) with 16; exact Hr16 | lia].
  - exact (tl_afact E 48 nch 0 255 E48 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 49 nz 1 (2 ^ 64 - 1) E49 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 50 (2 ^ 64 - 1 - r) (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) E50 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 51 (Boxreg.bx_n bs') (0 + 1) 5 E51 ltac:(lia) ltac:(lia)). }
destruct Hkn as [-> | ->].
{ (* known = -1 *)

assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa20 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 0); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 0)]))
     LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 [tl_regn TL_RCH] (mkFacts (TL_AFP 0) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - exact HSL.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact HRG | apply Forall_nil].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 TL_RCH HB HJ HFR HBLK HE E20).
  - split; [exact HFACT | split; exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.

psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, (tl_width_u1 E w7 E23 Hw7), U_lit in Hc by lia; discriminate ].

paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.

assert (HMM : ms_mem ms0 = ms_mem ms3) by (rewrite HM2; exact HM1).
assert (Hk0 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms0)) by (apply tl_keep_eq; rewrite HMM; reflexivity).
assert (HCR : tl_callregs cx (ms_regs ms0) 0xa94).
{ split; [rewrite Q2; exact E2|]. split; [rewrite Q8; exact E8|]. split; [rewrite Q3; exact E3|].
  split; [rewrite Q4; exact E4|]. split; [exact Q1|]. split; [lia | reflexivity]. }
pose proof (tl_tmem_keep i cx fp W3 _ ms3 ms0 q r fab bs M nch nz lf HB Hk0 HTM) as (_ & _ & _ & _ & _ & (HMAC0 & _) & _).
eapply SRr_bind.
{ eapply (tl_bcmp_call cx fp k ly3 S3 W3 ms0 _ r bs' M 0 0xa94 HB HJ HFR HBLK).
  - apply (lx_shadow_keep cx fp W3 _ ms3 ms0 LSH_iter Hk0); [vm_compute; congruence | exact HSH].
  - exact (lx_reg_keep cx fp W3 _ ms3 ms0 r bs' Hk0 ltac:(left; reflexivity) HREG).
  - exact HMAC0.
  - exact HL288'.
  - lia.
  - exact HMACz.
  - exact HCR.
  - rewrite Q10. rewrite ?E20. unfold w64. rewrite ?unsigned_lit_small by lia. first [reflexivity | f_equal; lia].
  - rewrite Q11, E46. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - exact Q12. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H0 & HK2).
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
assert (Hk2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2) by exact (lx_keep_trans cx fp W3 _ _ _ _ Hk0 HK2).
set (ms1 := mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)).
assert (Hk1 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms1)) by exact Hk2.
assert (G : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr (ms_regs ms1) rr = getr (ms_regs ms0) rr)
  by (intros rr Hrr; exact (tl_reg_kept _ _ rr HP2 Hrr)).
eexists q, r, fab, bs, M, nch, nz, lf, want, w7, _, 0, bs'.
split.
{ split.
  { apply (tl_body_mk cx fp 0xa20 0xa94 W3 [(r, LX_REG)] ms3 regs2 mem2 HB Hk2 HBODY).
    tl_lregs G Q2 Q8 Q9 Q3 Q4 Q18 Q22 E2 E8 E3 E4 E32 E22. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (tl_tmem_keep i cx fp W3 _ ms3 ms1 q r fab bs M nch nz lf HB Hk1 HTM)|].
  split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7b|].
  split; [tl_rk G Q20 E R20|].
  split; [tl_rk G Q21 E R21|].
  split; [rewrite G by tl_cs; rewrite Q25, <- Ewant; reflexivity|].
  split; [tl_rk G Q26 E R26|].
  tl_rk G Q27 E R27. }
split; [exact (lx_reg_keep cx fp W3 _ ms3 ms1 r bs' Hk1 ltac:(left; reflexivity) HREG)|].
split; [exact HFRES|]. split; [exact HADD|]. split; [lia|].
split; [cbn; exact H0|].
split; [rewrite G by tl_cs; rewrite Q19; reflexivity|].
split; [rewrite G by tl_cs; rewrite Q23; rewrite ?E20; unfold w64; rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]|].
rewrite G by tl_cs; rewrite Q24; first [reflexivity | apply bv_eq; vm_compute; reflexivity].
}

{ (* known = idx *)

assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa20 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 0); ((24%bv : bv 5), SLit 0); ((25%bv : bv 5), SLit 0)]))
     LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 [tl_regn TL_RCH] (mkFacts (TL_AFP 0) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - exact HSL.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact HRG | apply Forall_nil].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 TL_RCH HB HJ HFR HBLK HE E20).
  - split; [exact HFACT | split; exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.

psrr_branch_tok RUN BR HS SHOK TL_BSPAN.
{ exfalso. rewrite tl_bne, (tl_width_u0 E w7 E23 Hw7 Hw7z), U_lit in Hc by lia. discriminate. }
clear Hc.

paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.

assert (HMM : ms_mem ms0 = ms_mem ms3) by (rewrite HM2; exact HM1).
assert (Hk0 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms0)) by (apply tl_keep_eq; rewrite HMM; reflexivity).
assert (HCR : tl_callregs cx (ms_regs ms0) 0xa94).
{ split; [rewrite Q2; exact E2|]. split; [rewrite Q8; exact E8|]. split; [rewrite Q3; exact E3|].
  split; [rewrite Q4; exact E4|]. split; [exact Q1|]. split; [lia | reflexivity]. }
pose proof (tl_tmem_keep i cx fp W3 _ ms3 ms0 q r fab bs M nch nz lf HB Hk0 HTM) as (_ & _ & _ & _ & _ & (HMAC0 & _) & _).
eapply SRr_bind.
{ eapply (tl_bcmp_call cx fp k ly3 S3 W3 ms0 _ r bs' M 0 0xa94 HB HJ HFR HBLK).
  - apply (lx_shadow_keep cx fp W3 _ ms3 ms0 LSH_iter Hk0); [vm_compute; congruence | exact HSH].
  - exact (lx_reg_keep cx fp W3 _ ms3 ms0 r bs' Hk0 ltac:(left; reflexivity) HREG).
  - exact HMAC0.
  - exact HL288'.
  - lia.
  - exact HMACz.
  - exact HCR.
  - rewrite Q10. rewrite ?E20. unfold w64. rewrite ?unsigned_lit_small by lia. first [reflexivity | f_equal; lia].
  - rewrite Q11, E46. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - exact Q12. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H0 & HK2).
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
assert (Hk2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2) by exact (lx_keep_trans cx fp W3 _ _ _ _ Hk0 HK2).
set (ms1 := mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)).
assert (Hk1 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms1)) by exact Hk2.
assert (G : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr (ms_regs ms1) rr = getr (ms_regs ms0) rr)
  by (intros rr Hrr; exact (tl_reg_kept _ _ rr HP2 Hrr)).
eexists q, r, fab, bs, M, nch, nz, lf, want, w7, _, 0, bs'.
split.
{ split.
  { apply (tl_body_mk cx fp 0xa20 0xa94 W3 [(r, LX_REG)] ms3 regs2 mem2 HB Hk2 HBODY).
    tl_lregs G Q2 Q8 Q9 Q3 Q4 Q18 Q22 E2 E8 E3 E4 E32 E22. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (tl_tmem_keep i cx fp W3 _ ms3 ms1 q r fab bs M nch nz lf HB Hk1 HTM)|].
  split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7b|].
  split; [tl_rk G Q20 E R20|].
  split; [tl_rk G Q21 E R21|].
  split; [rewrite G by tl_cs; rewrite Q25, <- Ewant; reflexivity|].
  split; [tl_rk G Q26 E R26|].
  tl_rk G Q27 E R27. }
split; [exact (lx_reg_keep cx fp W3 _ ms3 ms1 r bs' Hk1 ltac:(left; reflexivity) HREG)|].
split; [exact HFRES|]. split; [exact HADD|]. split; [lia|].
split; [cbn; exact H0|].
split; [rewrite G by tl_cs; rewrite Q19; reflexivity|].
split; [rewrite G by tl_cs; rewrite Q23; rewrite ?E20; unfold w64; rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]|].
rewrite G by tl_cs; rewrite Q24; first [reflexivity | apply bv_eq; vm_compute; reflexivity].
}

Qed.

Lemma tl_w3_p1 : TW3P 1.
Proof.

intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs'
  HB HJ HFR HMO HCO HREG HFRES HADD R10 R23 R24.
pose proof (lh_laws B MT HY) as LAWS.
pose proof HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & Hlf & HW & Hwant & Hw7 & Hw7b & R20 & R21 & R25 & R26 & R27).
pose proof HTM as (HPREV & HCUR & HSLL & S58 & S48 & HRD & HNZ & S20).
pose proof HRD as (HMAC & S50 & Hnch). pose proof HMAC as (HML & HMB).
pose proof HNZ as (S60 & Hnzr & Hnzi).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof HJ as (HAR3 & _).
assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size LX_REG) with 288 in Hrceil, Hria.
pose proof (LC1.c1_inv_len bs HINV) as HL288. pose proof (LC1.c1_inv_n bs HINV) as HnB.
pose proof (lxc1_add_keeps bs M nch _ bs' HINV HML HADD) as (HINV' & HFAB' & HKEPT).
pose proof (LC1.c1_inv_len bs' HINV') as HL288'. pose proof (LC1.c1_inv_n bs' HINV') as HnB'.
set (ex := TL_EX r nch nz bs').
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (E48 : ew E 48 = w64 nch) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
assert (E49 : ew E 49 = w64 nz) by exact (lx_env_ex cx fp (ms_regs ms3) ex 1 ltac:(lia)).
assert (E50 : ew E 50 = w64 (2 ^ 64 - 1 - r)) by exact (lx_env_ex cx fp (ms_regs ms3) ex 2 ltac:(lia)).
assert (E51 : ew E 51 = w64 (Boxreg.bx_n bs')) by exact (lx_env_ex cx fp (ms_regs ms3) ex 3 ltac:(lia)).
assert (E20 : ew E 20 = w64 r) by (unfold E; erewrite lx_env_reg; [exact R20 | reflexivity]).
assert (E23 : ew E 23 = w64 w7) by (unfold E; erewrite lx_env_reg; [exact R23 | reflexivity]).
unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F in E2, E8, E22, E32, E46.
assert (HSL : lx_slots cx W3 ms3 E TL_SL).
{ unfold lx_slots, TL_SL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - apply (lx_slot_atom cx W3 ms3 E _ 20 r 280); [exact L28 | exact E20 | lia | lia].
  - apply (tl_slot_sh280 cx W3 ms3 E r L40 E20 E32); lia.
  - apply (lx_slot_atom cx W3 ms3 E _ 48 nch 0); [rewrite Z.add_0_r; exact S50 | exact E48 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ 49 nz 0); [rewrite Z.add_0_r; exact S60 | exact E49 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ LA_F (lF cx fp) 32); [exact L68 | exact E46 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ 50 (2 ^ 64 - 1 - r) 0); [rewrite Z.add_0_r; exact L70 | exact E50 | lia | lia]. }
assert (HRG : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (tl_regn TL_RCH)).
{ apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
  apply Forall_cons; [|apply Forall_nil].
  change 280 with (Z.of_nat 280). apply (tl_word_chunk E W3 ms3 r bs' 280 51 (Boxreg.bx_n bs') HREG HL288' ltac:(lia));
    [reflexivity | lia | rewrite lx_sv_SOff0, E51; reflexivity]. }

destruct (LC1.c1_add_pos bs M nch 1 bs' HINV HML HADD ltac:(lia)) as (HMZ & Ao & Hfab' & Hn5 & Hh' & Hcase).
destruct (LC1.c1_add_want bs M nch lf want 1 bs' HINV HML HW HADD) as (Ewant & _).
assert (Hw7z : Z.land w7 1 = 0) by (apply Hw7b; rewrite <- HFAB; exact Ao).
assert (Hnz0 : nz <> 0) by (intros E0; apply HMZ; apply Hnzi; exact E0).
pose proof (LC1.c1_find_range bs M known HFRES HnB) as Hkr.
assert (Hkn : known = -1 \/ known = 1).
{ destruct (Z_lt_ge_dec known 0) as [Hk0|Hk0]; [left; lia|].
  right. symmetry. exact (LC1.c1_known bs M nch known 1 bs' HFRES ltac:(lia) Ao HADD). }
pose proof Hh' as (Hzn & HMACz & _).
assert (HFACT : atoms_ok E (TL_AFP 1)).
{ unfold TL_AFP. apply tl_atoms_ok_app; [exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE)|].
  cbn [atoms_ok]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E20. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [change (2 ^ 4) with 16; exact Hr16 | lia].
  - exact (tl_afact E 48 nch 0 255 E48 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 49 nz 1 (2 ^ 64 - 1) E49 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 50 (2 ^ 64 - 1 - r) (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) E50 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 51 (Boxreg.bx_n bs') (1 + 1) 5 E51 ltac:(lia) ltac:(lia)). }
destruct Hkn as [-> | ->].
{ (* known = -1 *)

assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa20 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 1); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 1)]))
     LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 [tl_regn TL_RCH] (mkFacts (TL_AFP 1) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - exact HSL.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact HRG | apply Forall_nil].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 TL_RCH HB HJ HFR HBLK HE E20).
  - split; [exact HFACT | split; exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.

psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, (tl_width_u1 E w7 E23 Hw7), U_lit in Hc by lia; discriminate ].

paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.

assert (HMM : ms_mem ms0 = ms_mem ms3) by (rewrite HM2; exact HM1).
assert (Hk0 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms0)) by (apply tl_keep_eq; rewrite HMM; reflexivity).
assert (HCR : tl_callregs cx (ms_regs ms0) 0xa94).
{ split; [rewrite Q2; exact E2|]. split; [rewrite Q8; exact E8|]. split; [rewrite Q3; exact E3|].
  split; [rewrite Q4; exact E4|]. split; [exact Q1|]. split; [lia | reflexivity]. }
pose proof (tl_tmem_keep i cx fp W3 _ ms3 ms0 q r fab bs M nch nz lf HB Hk0 HTM) as (_ & _ & _ & _ & _ & (HMAC0 & _) & _).
eapply SRr_bind.
{ eapply (tl_bcmp_call cx fp k ly3 S3 W3 ms0 _ r bs' M 1 0xa94 HB HJ HFR HBLK).
  - apply (lx_shadow_keep cx fp W3 _ ms3 ms0 LSH_iter Hk0); [vm_compute; congruence | exact HSH].
  - exact (lx_reg_keep cx fp W3 _ ms3 ms0 r bs' Hk0 ltac:(left; reflexivity) HREG).
  - exact HMAC0.
  - exact HL288'.
  - lia.
  - exact HMACz.
  - exact HCR.
  - rewrite Q10. rewrite ?E20. unfold w64. rewrite ?unsigned_lit_small by lia. first [reflexivity | f_equal; lia].
  - rewrite Q11, E46. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - exact Q12. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H0 & HK2).
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
assert (Hk2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2) by exact (lx_keep_trans cx fp W3 _ _ _ _ Hk0 HK2).
set (ms1 := mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)).
assert (Hk1 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms1)) by exact Hk2.
assert (G : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr (ms_regs ms1) rr = getr (ms_regs ms0) rr)
  by (intros rr Hrr; exact (tl_reg_kept _ _ rr HP2 Hrr)).
eexists q, r, fab, bs, M, nch, nz, lf, want, w7, _, 1, bs'.
split.
{ split.
  { apply (tl_body_mk cx fp 0xa20 0xa94 W3 [(r, LX_REG)] ms3 regs2 mem2 HB Hk2 HBODY).
    tl_lregs G Q2 Q8 Q9 Q3 Q4 Q18 Q22 E2 E8 E3 E4 E32 E22. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (tl_tmem_keep i cx fp W3 _ ms3 ms1 q r fab bs M nch nz lf HB Hk1 HTM)|].
  split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7b|].
  split; [tl_rk G Q20 E R20|].
  split; [tl_rk G Q21 E R21|].
  split; [rewrite G by tl_cs; rewrite Q25, <- Ewant; reflexivity|].
  split; [tl_rk G Q26 E R26|].
  tl_rk G Q27 E R27. }
split; [exact (lx_reg_keep cx fp W3 _ ms3 ms1 r bs' Hk1 ltac:(left; reflexivity) HREG)|].
split; [exact HFRES|]. split; [exact HADD|]. split; [lia|].
split; [cbn; exact H0|].
split; [rewrite G by tl_cs; rewrite Q19; reflexivity|].
split; [rewrite G by tl_cs; rewrite Q23; rewrite ?E20; unfold w64; rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]|].
rewrite G by tl_cs; rewrite Q24; first [reflexivity | apply bv_eq; vm_compute; reflexivity].
}

{ (* known = idx *)

assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa20 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 1); ((24%bv : bv 5), SLit 1); ((25%bv : bv 5), SLit 1)]))
     LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 [tl_regn TL_RCH] (mkFacts (TL_AFP 1) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - exact HSL.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact HRG | apply Forall_nil].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 TL_RCH HB HJ HFR HBLK HE E20).
  - split; [exact HFACT | split; exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.

psrr_branch_tok RUN BR HS SHOK TL_BSPAN.
{ exfalso. rewrite tl_bne, (tl_width_u0 E w7 E23 Hw7 Hw7z), U_lit in Hc by lia. discriminate. }
clear Hc.

paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.

assert (HMM : ms_mem ms0 = ms_mem ms3) by (rewrite HM2; exact HM1).
assert (Hk0 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms0)) by (apply tl_keep_eq; rewrite HMM; reflexivity).
assert (HCR : tl_callregs cx (ms_regs ms0) 0xa94).
{ split; [rewrite Q2; exact E2|]. split; [rewrite Q8; exact E8|]. split; [rewrite Q3; exact E3|].
  split; [rewrite Q4; exact E4|]. split; [exact Q1|]. split; [lia | reflexivity]. }
pose proof (tl_tmem_keep i cx fp W3 _ ms3 ms0 q r fab bs M nch nz lf HB Hk0 HTM) as (_ & _ & _ & _ & _ & (HMAC0 & _) & _).
eapply SRr_bind.
{ eapply (tl_bcmp_call cx fp k ly3 S3 W3 ms0 _ r bs' M 1 0xa94 HB HJ HFR HBLK).
  - apply (lx_shadow_keep cx fp W3 _ ms3 ms0 LSH_iter Hk0); [vm_compute; congruence | exact HSH].
  - exact (lx_reg_keep cx fp W3 _ ms3 ms0 r bs' Hk0 ltac:(left; reflexivity) HREG).
  - exact HMAC0.
  - exact HL288'.
  - lia.
  - exact HMACz.
  - exact HCR.
  - rewrite Q10. rewrite ?E20. unfold w64. rewrite ?unsigned_lit_small by lia. first [reflexivity | f_equal; lia].
  - rewrite Q11, E46. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - exact Q12. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H0 & HK2).
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
assert (Hk2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2) by exact (lx_keep_trans cx fp W3 _ _ _ _ Hk0 HK2).
set (ms1 := mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)).
assert (Hk1 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms1)) by exact Hk2.
assert (G : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr (ms_regs ms1) rr = getr (ms_regs ms0) rr)
  by (intros rr Hrr; exact (tl_reg_kept _ _ rr HP2 Hrr)).
eexists q, r, fab, bs, M, nch, nz, lf, want, w7, _, 1, bs'.
split.
{ split.
  { apply (tl_body_mk cx fp 0xa20 0xa94 W3 [(r, LX_REG)] ms3 regs2 mem2 HB Hk2 HBODY).
    tl_lregs G Q2 Q8 Q9 Q3 Q4 Q18 Q22 E2 E8 E3 E4 E32 E22. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (tl_tmem_keep i cx fp W3 _ ms3 ms1 q r fab bs M nch nz lf HB Hk1 HTM)|].
  split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7b|].
  split; [tl_rk G Q20 E R20|].
  split; [tl_rk G Q21 E R21|].
  split; [rewrite G by tl_cs; rewrite Q25, <- Ewant; reflexivity|].
  split; [tl_rk G Q26 E R26|].
  tl_rk G Q27 E R27. }
split; [exact (lx_reg_keep cx fp W3 _ ms3 ms1 r bs' Hk1 ltac:(left; reflexivity) HREG)|].
split; [exact HFRES|]. split; [exact HADD|]. split; [lia|].
split; [cbn; exact H0|].
split; [rewrite G by tl_cs; rewrite Q19; reflexivity|].
split; [rewrite G by tl_cs; rewrite Q23; rewrite ?E20; unfold w64; rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]|].
rewrite G by tl_cs; rewrite Q24; first [reflexivity | apply bv_eq; vm_compute; reflexivity].
}

Qed.

Lemma tl_w3_p2 : TW3P 2.
Proof.

intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs'
  HB HJ HFR HMO HCO HREG HFRES HADD R10 R23 R24.
pose proof (lh_laws B MT HY) as LAWS.
pose proof HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & Hlf & HW & Hwant & Hw7 & Hw7b & R20 & R21 & R25 & R26 & R27).
pose proof HTM as (HPREV & HCUR & HSLL & S58 & S48 & HRD & HNZ & S20).
pose proof HRD as (HMAC & S50 & Hnch). pose proof HMAC as (HML & HMB).
pose proof HNZ as (S60 & Hnzr & Hnzi).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof HJ as (HAR3 & _).
assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size LX_REG) with 288 in Hrceil, Hria.
pose proof (LC1.c1_inv_len bs HINV) as HL288. pose proof (LC1.c1_inv_n bs HINV) as HnB.
pose proof (lxc1_add_keeps bs M nch _ bs' HINV HML HADD) as (HINV' & HFAB' & HKEPT).
pose proof (LC1.c1_inv_len bs' HINV') as HL288'. pose proof (LC1.c1_inv_n bs' HINV') as HnB'.
set (ex := TL_EX r nch nz bs').
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (E48 : ew E 48 = w64 nch) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
assert (E49 : ew E 49 = w64 nz) by exact (lx_env_ex cx fp (ms_regs ms3) ex 1 ltac:(lia)).
assert (E50 : ew E 50 = w64 (2 ^ 64 - 1 - r)) by exact (lx_env_ex cx fp (ms_regs ms3) ex 2 ltac:(lia)).
assert (E51 : ew E 51 = w64 (Boxreg.bx_n bs')) by exact (lx_env_ex cx fp (ms_regs ms3) ex 3 ltac:(lia)).
assert (E20 : ew E 20 = w64 r) by (unfold E; erewrite lx_env_reg; [exact R20 | reflexivity]).
assert (E23 : ew E 23 = w64 w7) by (unfold E; erewrite lx_env_reg; [exact R23 | reflexivity]).
unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F in E2, E8, E22, E32, E46.
assert (HSL : lx_slots cx W3 ms3 E TL_SL).
{ unfold lx_slots, TL_SL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - apply (lx_slot_atom cx W3 ms3 E _ 20 r 280); [exact L28 | exact E20 | lia | lia].
  - apply (tl_slot_sh280 cx W3 ms3 E r L40 E20 E32); lia.
  - apply (lx_slot_atom cx W3 ms3 E _ 48 nch 0); [rewrite Z.add_0_r; exact S50 | exact E48 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ 49 nz 0); [rewrite Z.add_0_r; exact S60 | exact E49 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ LA_F (lF cx fp) 32); [exact L68 | exact E46 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ 50 (2 ^ 64 - 1 - r) 0); [rewrite Z.add_0_r; exact L70 | exact E50 | lia | lia]. }
assert (HRG : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (tl_regn TL_RCH)).
{ apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
  apply Forall_cons; [|apply Forall_nil].
  change 280 with (Z.of_nat 280). apply (tl_word_chunk E W3 ms3 r bs' 280 51 (Boxreg.bx_n bs') HREG HL288' ltac:(lia));
    [reflexivity | lia | rewrite lx_sv_SOff0, E51; reflexivity]. }

destruct (LC1.c1_add_pos bs M nch 2 bs' HINV HML HADD ltac:(lia)) as (HMZ & Ao & Hfab' & Hn5 & Hh' & Hcase).
destruct (LC1.c1_add_want bs M nch lf want 2 bs' HINV HML HW HADD) as (Ewant & _).
assert (Hw7z : Z.land w7 1 = 0) by (apply Hw7b; rewrite <- HFAB; exact Ao).
assert (Hnz0 : nz <> 0) by (intros E0; apply HMZ; apply Hnzi; exact E0).
pose proof (LC1.c1_find_range bs M known HFRES HnB) as Hkr.
assert (Hkn : known = -1 \/ known = 2).
{ destruct (Z_lt_ge_dec known 0) as [Hk0|Hk0]; [left; lia|].
  right. symmetry. exact (LC1.c1_known bs M nch known 2 bs' HFRES ltac:(lia) Ao HADD). }
pose proof Hh' as (Hzn & HMACz & _).
assert (HFACT : atoms_ok E (TL_AFP 2)).
{ unfold TL_AFP. apply tl_atoms_ok_app; [exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE)|].
  cbn [atoms_ok]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E20. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [change (2 ^ 4) with 16; exact Hr16 | lia].
  - exact (tl_afact E 48 nch 0 255 E48 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 49 nz 1 (2 ^ 64 - 1) E49 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 50 (2 ^ 64 - 1 - r) (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) E50 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 51 (Boxreg.bx_n bs') (2 + 1) 5 E51 ltac:(lia) ltac:(lia)). }
destruct Hkn as [-> | ->].
{ (* known = -1 *)

assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa20 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 2); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 2)]))
     LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 [tl_regn TL_RCH] (mkFacts (TL_AFP 2) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - exact HSL.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact HRG | apply Forall_nil].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 TL_RCH HB HJ HFR HBLK HE E20).
  - split; [exact HFACT | split; exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.

psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, (tl_width_u1 E w7 E23 Hw7), U_lit in Hc by lia; discriminate ].

paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.

assert (HMM : ms_mem ms0 = ms_mem ms3) by (rewrite HM2; exact HM1).
assert (Hk0 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms0)) by (apply tl_keep_eq; rewrite HMM; reflexivity).
assert (HCR : tl_callregs cx (ms_regs ms0) 0xa94).
{ split; [rewrite Q2; exact E2|]. split; [rewrite Q8; exact E8|]. split; [rewrite Q3; exact E3|].
  split; [rewrite Q4; exact E4|]. split; [exact Q1|]. split; [lia | reflexivity]. }
pose proof (tl_tmem_keep i cx fp W3 _ ms3 ms0 q r fab bs M nch nz lf HB Hk0 HTM) as (_ & _ & _ & _ & _ & (HMAC0 & _) & _).
eapply SRr_bind.
{ eapply (tl_bcmp_call cx fp k ly3 S3 W3 ms0 _ r bs' M 2 0xa94 HB HJ HFR HBLK).
  - apply (lx_shadow_keep cx fp W3 _ ms3 ms0 LSH_iter Hk0); [vm_compute; congruence | exact HSH].
  - exact (lx_reg_keep cx fp W3 _ ms3 ms0 r bs' Hk0 ltac:(left; reflexivity) HREG).
  - exact HMAC0.
  - exact HL288'.
  - lia.
  - exact HMACz.
  - exact HCR.
  - rewrite Q10. rewrite ?E20. unfold w64. rewrite ?unsigned_lit_small by lia. first [reflexivity | f_equal; lia].
  - rewrite Q11, E46. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - exact Q12. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H0 & HK2).
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
assert (Hk2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2) by exact (lx_keep_trans cx fp W3 _ _ _ _ Hk0 HK2).
set (ms1 := mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)).
assert (Hk1 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms1)) by exact Hk2.
assert (G : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr (ms_regs ms1) rr = getr (ms_regs ms0) rr)
  by (intros rr Hrr; exact (tl_reg_kept _ _ rr HP2 Hrr)).
eexists q, r, fab, bs, M, nch, nz, lf, want, w7, _, 2, bs'.
split.
{ split.
  { apply (tl_body_mk cx fp 0xa20 0xa94 W3 [(r, LX_REG)] ms3 regs2 mem2 HB Hk2 HBODY).
    tl_lregs G Q2 Q8 Q9 Q3 Q4 Q18 Q22 E2 E8 E3 E4 E32 E22. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (tl_tmem_keep i cx fp W3 _ ms3 ms1 q r fab bs M nch nz lf HB Hk1 HTM)|].
  split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7b|].
  split; [tl_rk G Q20 E R20|].
  split; [tl_rk G Q21 E R21|].
  split; [rewrite G by tl_cs; rewrite Q25, <- Ewant; reflexivity|].
  split; [tl_rk G Q26 E R26|].
  tl_rk G Q27 E R27. }
split; [exact (lx_reg_keep cx fp W3 _ ms3 ms1 r bs' Hk1 ltac:(left; reflexivity) HREG)|].
split; [exact HFRES|]. split; [exact HADD|]. split; [lia|].
split; [cbn; exact H0|].
split; [rewrite G by tl_cs; rewrite Q19; reflexivity|].
split; [rewrite G by tl_cs; rewrite Q23; rewrite ?E20; unfold w64; rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]|].
rewrite G by tl_cs; rewrite Q24; first [reflexivity | apply bv_eq; vm_compute; reflexivity].
}

{ (* known = idx *)

assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa20 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 2); ((24%bv : bv 5), SLit 2); ((25%bv : bv 5), SLit 2)]))
     LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 [tl_regn TL_RCH] (mkFacts (TL_AFP 2) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - exact HSL.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact HRG | apply Forall_nil].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 TL_RCH HB HJ HFR HBLK HE E20).
  - split; [exact HFACT | split; exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.

psrr_branch_tok RUN BR HS SHOK TL_BSPAN.
{ exfalso. rewrite tl_bne, (tl_width_u0 E w7 E23 Hw7 Hw7z), U_lit in Hc by lia. discriminate. }
clear Hc.

paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.

assert (HMM : ms_mem ms0 = ms_mem ms3) by (rewrite HM2; exact HM1).
assert (Hk0 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms0)) by (apply tl_keep_eq; rewrite HMM; reflexivity).
assert (HCR : tl_callregs cx (ms_regs ms0) 0xa94).
{ split; [rewrite Q2; exact E2|]. split; [rewrite Q8; exact E8|]. split; [rewrite Q3; exact E3|].
  split; [rewrite Q4; exact E4|]. split; [exact Q1|]. split; [lia | reflexivity]. }
pose proof (tl_tmem_keep i cx fp W3 _ ms3 ms0 q r fab bs M nch nz lf HB Hk0 HTM) as (_ & _ & _ & _ & _ & (HMAC0 & _) & _).
eapply SRr_bind.
{ eapply (tl_bcmp_call cx fp k ly3 S3 W3 ms0 _ r bs' M 2 0xa94 HB HJ HFR HBLK).
  - apply (lx_shadow_keep cx fp W3 _ ms3 ms0 LSH_iter Hk0); [vm_compute; congruence | exact HSH].
  - exact (lx_reg_keep cx fp W3 _ ms3 ms0 r bs' Hk0 ltac:(left; reflexivity) HREG).
  - exact HMAC0.
  - exact HL288'.
  - lia.
  - exact HMACz.
  - exact HCR.
  - rewrite Q10. rewrite ?E20. unfold w64. rewrite ?unsigned_lit_small by lia. first [reflexivity | f_equal; lia].
  - rewrite Q11, E46. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - exact Q12. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H0 & HK2).
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
assert (Hk2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2) by exact (lx_keep_trans cx fp W3 _ _ _ _ Hk0 HK2).
set (ms1 := mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)).
assert (Hk1 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms1)) by exact Hk2.
assert (G : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr (ms_regs ms1) rr = getr (ms_regs ms0) rr)
  by (intros rr Hrr; exact (tl_reg_kept _ _ rr HP2 Hrr)).
eexists q, r, fab, bs, M, nch, nz, lf, want, w7, _, 2, bs'.
split.
{ split.
  { apply (tl_body_mk cx fp 0xa20 0xa94 W3 [(r, LX_REG)] ms3 regs2 mem2 HB Hk2 HBODY).
    tl_lregs G Q2 Q8 Q9 Q3 Q4 Q18 Q22 E2 E8 E3 E4 E32 E22. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (tl_tmem_keep i cx fp W3 _ ms3 ms1 q r fab bs M nch nz lf HB Hk1 HTM)|].
  split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7b|].
  split; [tl_rk G Q20 E R20|].
  split; [tl_rk G Q21 E R21|].
  split; [rewrite G by tl_cs; rewrite Q25, <- Ewant; reflexivity|].
  split; [tl_rk G Q26 E R26|].
  tl_rk G Q27 E R27. }
split; [exact (lx_reg_keep cx fp W3 _ ms3 ms1 r bs' Hk1 ltac:(left; reflexivity) HREG)|].
split; [exact HFRES|]. split; [exact HADD|]. split; [lia|].
split; [cbn; exact H0|].
split; [rewrite G by tl_cs; rewrite Q19; reflexivity|].
split; [rewrite G by tl_cs; rewrite Q23; rewrite ?E20; unfold w64; rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]|].
rewrite G by tl_cs; rewrite Q24; first [reflexivity | apply bv_eq; vm_compute; reflexivity].
}

Qed.

Lemma tl_w3_p3 : TW3P 3.
Proof.

intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs'
  HB HJ HFR HMO HCO HREG HFRES HADD R10 R23 R24.
pose proof (lh_laws B MT HY) as LAWS.
pose proof HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & Hlf & HW & Hwant & Hw7 & Hw7b & R20 & R21 & R25 & R26 & R27).
pose proof HTM as (HPREV & HCUR & HSLL & S58 & S48 & HRD & HNZ & S20).
pose proof HRD as (HMAC & S50 & Hnch). pose proof HMAC as (HML & HMB).
pose proof HNZ as (S60 & Hnzr & Hnzi).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof HJ as (HAR3 & _).
assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size LX_REG) with 288 in Hrceil, Hria.
pose proof (LC1.c1_inv_len bs HINV) as HL288. pose proof (LC1.c1_inv_n bs HINV) as HnB.
pose proof (lxc1_add_keeps bs M nch _ bs' HINV HML HADD) as (HINV' & HFAB' & HKEPT).
pose proof (LC1.c1_inv_len bs' HINV') as HL288'. pose proof (LC1.c1_inv_n bs' HINV') as HnB'.
set (ex := TL_EX r nch nz bs').
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (E48 : ew E 48 = w64 nch) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
assert (E49 : ew E 49 = w64 nz) by exact (lx_env_ex cx fp (ms_regs ms3) ex 1 ltac:(lia)).
assert (E50 : ew E 50 = w64 (2 ^ 64 - 1 - r)) by exact (lx_env_ex cx fp (ms_regs ms3) ex 2 ltac:(lia)).
assert (E51 : ew E 51 = w64 (Boxreg.bx_n bs')) by exact (lx_env_ex cx fp (ms_regs ms3) ex 3 ltac:(lia)).
assert (E20 : ew E 20 = w64 r) by (unfold E; erewrite lx_env_reg; [exact R20 | reflexivity]).
assert (E23 : ew E 23 = w64 w7) by (unfold E; erewrite lx_env_reg; [exact R23 | reflexivity]).
unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F in E2, E8, E22, E32, E46.
assert (HSL : lx_slots cx W3 ms3 E TL_SL).
{ unfold lx_slots, TL_SL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - apply (lx_slot_atom cx W3 ms3 E _ 20 r 280); [exact L28 | exact E20 | lia | lia].
  - apply (tl_slot_sh280 cx W3 ms3 E r L40 E20 E32); lia.
  - apply (lx_slot_atom cx W3 ms3 E _ 48 nch 0); [rewrite Z.add_0_r; exact S50 | exact E48 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ 49 nz 0); [rewrite Z.add_0_r; exact S60 | exact E49 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ LA_F (lF cx fp) 32); [exact L68 | exact E46 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ 50 (2 ^ 64 - 1 - r) 0); [rewrite Z.add_0_r; exact L70 | exact E50 | lia | lia]. }
assert (HRG : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (tl_regn TL_RCH)).
{ apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
  apply Forall_cons; [|apply Forall_nil].
  change 280 with (Z.of_nat 280). apply (tl_word_chunk E W3 ms3 r bs' 280 51 (Boxreg.bx_n bs') HREG HL288' ltac:(lia));
    [reflexivity | lia | rewrite lx_sv_SOff0, E51; reflexivity]. }

destruct (LC1.c1_add_pos bs M nch 3 bs' HINV HML HADD ltac:(lia)) as (HMZ & Ao & Hfab' & Hn5 & Hh' & Hcase).
destruct (LC1.c1_add_want bs M nch lf want 3 bs' HINV HML HW HADD) as (Ewant & _).
assert (Hw7z : Z.land w7 1 = 0) by (apply Hw7b; rewrite <- HFAB; exact Ao).
assert (Hnz0 : nz <> 0) by (intros E0; apply HMZ; apply Hnzi; exact E0).
pose proof (LC1.c1_find_range bs M known HFRES HnB) as Hkr.
assert (Hkn : known = -1 \/ known = 3).
{ destruct (Z_lt_ge_dec known 0) as [Hk0|Hk0]; [left; lia|].
  right. symmetry. exact (LC1.c1_known bs M nch known 3 bs' HFRES ltac:(lia) Ao HADD). }
pose proof Hh' as (Hzn & HMACz & _).
assert (HFACT : atoms_ok E (TL_AFP 3)).
{ unfold TL_AFP. apply tl_atoms_ok_app; [exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE)|].
  cbn [atoms_ok]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E20. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [change (2 ^ 4) with 16; exact Hr16 | lia].
  - exact (tl_afact E 48 nch 0 255 E48 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 49 nz 1 (2 ^ 64 - 1) E49 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 50 (2 ^ 64 - 1 - r) (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) E50 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 51 (Boxreg.bx_n bs') (3 + 1) 5 E51 ltac:(lia) ltac:(lia)). }
destruct Hkn as [-> | ->].
{ (* known = -1 *)

assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa20 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 3); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 3)]))
     LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 [tl_regn TL_RCH] (mkFacts (TL_AFP 3) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - exact HSL.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact HRG | apply Forall_nil].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 TL_RCH HB HJ HFR HBLK HE E20).
  - split; [exact HFACT | split; exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.

psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, (tl_width_u1 E w7 E23 Hw7), U_lit in Hc by lia; discriminate ].

paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.

assert (HMM : ms_mem ms0 = ms_mem ms3) by (rewrite HM2; exact HM1).
assert (Hk0 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms0)) by (apply tl_keep_eq; rewrite HMM; reflexivity).
assert (HCR : tl_callregs cx (ms_regs ms0) 0xa94).
{ split; [rewrite Q2; exact E2|]. split; [rewrite Q8; exact E8|]. split; [rewrite Q3; exact E3|].
  split; [rewrite Q4; exact E4|]. split; [exact Q1|]. split; [lia | reflexivity]. }
pose proof (tl_tmem_keep i cx fp W3 _ ms3 ms0 q r fab bs M nch nz lf HB Hk0 HTM) as (_ & _ & _ & _ & _ & (HMAC0 & _) & _).
eapply SRr_bind.
{ eapply (tl_bcmp_call cx fp k ly3 S3 W3 ms0 _ r bs' M 3 0xa94 HB HJ HFR HBLK).
  - apply (lx_shadow_keep cx fp W3 _ ms3 ms0 LSH_iter Hk0); [vm_compute; congruence | exact HSH].
  - exact (lx_reg_keep cx fp W3 _ ms3 ms0 r bs' Hk0 ltac:(left; reflexivity) HREG).
  - exact HMAC0.
  - exact HL288'.
  - lia.
  - exact HMACz.
  - exact HCR.
  - rewrite Q10. rewrite ?E20. unfold w64. rewrite ?unsigned_lit_small by lia. first [reflexivity | f_equal; lia].
  - rewrite Q11, E46. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - exact Q12. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H0 & HK2).
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
assert (Hk2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2) by exact (lx_keep_trans cx fp W3 _ _ _ _ Hk0 HK2).
set (ms1 := mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)).
assert (Hk1 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms1)) by exact Hk2.
assert (G : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr (ms_regs ms1) rr = getr (ms_regs ms0) rr)
  by (intros rr Hrr; exact (tl_reg_kept _ _ rr HP2 Hrr)).
eexists q, r, fab, bs, M, nch, nz, lf, want, w7, _, 3, bs'.
split.
{ split.
  { apply (tl_body_mk cx fp 0xa20 0xa94 W3 [(r, LX_REG)] ms3 regs2 mem2 HB Hk2 HBODY).
    tl_lregs G Q2 Q8 Q9 Q3 Q4 Q18 Q22 E2 E8 E3 E4 E32 E22. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (tl_tmem_keep i cx fp W3 _ ms3 ms1 q r fab bs M nch nz lf HB Hk1 HTM)|].
  split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7b|].
  split; [tl_rk G Q20 E R20|].
  split; [tl_rk G Q21 E R21|].
  split; [rewrite G by tl_cs; rewrite Q25, <- Ewant; reflexivity|].
  split; [tl_rk G Q26 E R26|].
  tl_rk G Q27 E R27. }
split; [exact (lx_reg_keep cx fp W3 _ ms3 ms1 r bs' Hk1 ltac:(left; reflexivity) HREG)|].
split; [exact HFRES|]. split; [exact HADD|]. split; [lia|].
split; [cbn; exact H0|].
split; [rewrite G by tl_cs; rewrite Q19; reflexivity|].
split; [rewrite G by tl_cs; rewrite Q23; rewrite ?E20; unfold w64; rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]|].
rewrite G by tl_cs; rewrite Q24; first [reflexivity | apply bv_eq; vm_compute; reflexivity].
}

{ (* known = idx *)

assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa20 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 3); ((24%bv : bv 5), SLit 3); ((25%bv : bv 5), SLit 3)]))
     LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 [tl_regn TL_RCH] (mkFacts (TL_AFP 3) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - exact HSL.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact HRG | apply Forall_nil].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 TL_RCH HB HJ HFR HBLK HE E20).
  - split; [exact HFACT | split; exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.

psrr_branch_tok RUN BR HS SHOK TL_BSPAN.
{ exfalso. rewrite tl_bne, (tl_width_u0 E w7 E23 Hw7 Hw7z), U_lit in Hc by lia. discriminate. }
clear Hc.

paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.

assert (HMM : ms_mem ms0 = ms_mem ms3) by (rewrite HM2; exact HM1).
assert (Hk0 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms0)) by (apply tl_keep_eq; rewrite HMM; reflexivity).
assert (HCR : tl_callregs cx (ms_regs ms0) 0xa94).
{ split; [rewrite Q2; exact E2|]. split; [rewrite Q8; exact E8|]. split; [rewrite Q3; exact E3|].
  split; [rewrite Q4; exact E4|]. split; [exact Q1|]. split; [lia | reflexivity]. }
pose proof (tl_tmem_keep i cx fp W3 _ ms3 ms0 q r fab bs M nch nz lf HB Hk0 HTM) as (_ & _ & _ & _ & _ & (HMAC0 & _) & _).
eapply SRr_bind.
{ eapply (tl_bcmp_call cx fp k ly3 S3 W3 ms0 _ r bs' M 3 0xa94 HB HJ HFR HBLK).
  - apply (lx_shadow_keep cx fp W3 _ ms3 ms0 LSH_iter Hk0); [vm_compute; congruence | exact HSH].
  - exact (lx_reg_keep cx fp W3 _ ms3 ms0 r bs' Hk0 ltac:(left; reflexivity) HREG).
  - exact HMAC0.
  - exact HL288'.
  - lia.
  - exact HMACz.
  - exact HCR.
  - rewrite Q10. rewrite ?E20. unfold w64. rewrite ?unsigned_lit_small by lia. first [reflexivity | f_equal; lia].
  - rewrite Q11, E46. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - exact Q12. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H0 & HK2).
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
assert (Hk2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2) by exact (lx_keep_trans cx fp W3 _ _ _ _ Hk0 HK2).
set (ms1 := mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)).
assert (Hk1 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms1)) by exact Hk2.
assert (G : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr (ms_regs ms1) rr = getr (ms_regs ms0) rr)
  by (intros rr Hrr; exact (tl_reg_kept _ _ rr HP2 Hrr)).
eexists q, r, fab, bs, M, nch, nz, lf, want, w7, _, 3, bs'.
split.
{ split.
  { apply (tl_body_mk cx fp 0xa20 0xa94 W3 [(r, LX_REG)] ms3 regs2 mem2 HB Hk2 HBODY).
    tl_lregs G Q2 Q8 Q9 Q3 Q4 Q18 Q22 E2 E8 E3 E4 E32 E22. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (tl_tmem_keep i cx fp W3 _ ms3 ms1 q r fab bs M nch nz lf HB Hk1 HTM)|].
  split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7b|].
  split; [tl_rk G Q20 E R20|].
  split; [tl_rk G Q21 E R21|].
  split; [rewrite G by tl_cs; rewrite Q25, <- Ewant; reflexivity|].
  split; [tl_rk G Q26 E R26|].
  tl_rk G Q27 E R27. }
split; [exact (lx_reg_keep cx fp W3 _ ms3 ms1 r bs' Hk1 ltac:(left; reflexivity) HREG)|].
split; [exact HFRES|]. split; [exact HADD|]. split; [lia|].
split; [cbn; exact H0|].
split; [rewrite G by tl_cs; rewrite Q19; reflexivity|].
split; [rewrite G by tl_cs; rewrite Q23; rewrite ?E20; unfold w64; rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]|].
rewrite G by tl_cs; rewrite Q24; first [reflexivity | apply bv_eq; vm_compute; reflexivity].
}

Qed.

Lemma tl_w3_p4 : TW3P 4.
Proof.

intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs'
  HB HJ HFR HMO HCO HREG HFRES HADD R10 R23 R24.
pose proof (lh_laws B MT HY) as LAWS.
pose proof HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & Hlf & HW & Hwant & Hw7 & Hw7b & R20 & R21 & R25 & R26 & R27).
pose proof HTM as (HPREV & HCUR & HSLL & S58 & S48 & HRD & HNZ & S20).
pose proof HRD as (HMAC & S50 & Hnch). pose proof HMAC as (HML & HMB).
pose proof HNZ as (S60 & Hnzr & Hnzi).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof HJ as (HAR3 & _).
assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size LX_REG) with 288 in Hrceil, Hria.
pose proof (LC1.c1_inv_len bs HINV) as HL288. pose proof (LC1.c1_inv_n bs HINV) as HnB.
pose proof (lxc1_add_keeps bs M nch _ bs' HINV HML HADD) as (HINV' & HFAB' & HKEPT).
pose proof (LC1.c1_inv_len bs' HINV') as HL288'. pose proof (LC1.c1_inv_n bs' HINV') as HnB'.
set (ex := TL_EX r nch nz bs').
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (E48 : ew E 48 = w64 nch) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
assert (E49 : ew E 49 = w64 nz) by exact (lx_env_ex cx fp (ms_regs ms3) ex 1 ltac:(lia)).
assert (E50 : ew E 50 = w64 (2 ^ 64 - 1 - r)) by exact (lx_env_ex cx fp (ms_regs ms3) ex 2 ltac:(lia)).
assert (E51 : ew E 51 = w64 (Boxreg.bx_n bs')) by exact (lx_env_ex cx fp (ms_regs ms3) ex 3 ltac:(lia)).
assert (E20 : ew E 20 = w64 r) by (unfold E; erewrite lx_env_reg; [exact R20 | reflexivity]).
assert (E23 : ew E 23 = w64 w7) by (unfold E; erewrite lx_env_reg; [exact R23 | reflexivity]).
unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F in E2, E8, E22, E32, E46.
assert (HSL : lx_slots cx W3 ms3 E TL_SL).
{ unfold lx_slots, TL_SL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - apply (lx_slot_atom cx W3 ms3 E _ 20 r 280); [exact L28 | exact E20 | lia | lia].
  - apply (tl_slot_sh280 cx W3 ms3 E r L40 E20 E32); lia.
  - apply (lx_slot_atom cx W3 ms3 E _ 48 nch 0); [rewrite Z.add_0_r; exact S50 | exact E48 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ 49 nz 0); [rewrite Z.add_0_r; exact S60 | exact E49 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ LA_F (lF cx fp) 32); [exact L68 | exact E46 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E _ 50 (2 ^ 64 - 1 - r) 0); [rewrite Z.add_0_r; exact L70 | exact E50 | lia | lia]. }
assert (HRG : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (tl_regn TL_RCH)).
{ apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
  apply Forall_cons; [|apply Forall_nil].
  change 280 with (Z.of_nat 280). apply (tl_word_chunk E W3 ms3 r bs' 280 51 (Boxreg.bx_n bs') HREG HL288' ltac:(lia));
    [reflexivity | lia | rewrite lx_sv_SOff0, E51; reflexivity]. }

destruct (LC1.c1_add_pos bs M nch 4 bs' HINV HML HADD ltac:(lia)) as (HMZ & Ao & Hfab' & Hn5 & Hh' & Hcase).
destruct (LC1.c1_add_want bs M nch lf want 4 bs' HINV HML HW HADD) as (Ewant & _).
assert (Hw7z : Z.land w7 1 = 0) by (apply Hw7b; rewrite <- HFAB; exact Ao).
assert (Hnz0 : nz <> 0) by (intros E0; apply HMZ; apply Hnzi; exact E0).
pose proof (LC1.c1_find_range bs M known HFRES HnB) as Hkr.
assert (Hkn : known = -1 \/ known = 4).
{ destruct (Z_lt_ge_dec known 0) as [Hk0|Hk0]; [left; lia|].
  right. symmetry. exact (LC1.c1_known bs M nch known 4 bs' HFRES ltac:(lia) Ao HADD). }
pose proof Hh' as (Hzn & HMACz & _).
assert (HFACT : atoms_ok E (TL_AFP 4)).
{ unfold TL_AFP. apply tl_atoms_ok_app; [exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE)|].
  cbn [atoms_ok]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E20. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [change (2 ^ 4) with 16; exact Hr16 | lia].
  - exact (tl_afact E 48 nch 0 255 E48 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 49 nz 1 (2 ^ 64 - 1) E49 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 50 (2 ^ 64 - 1 - r) (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) E50 ltac:(lia) ltac:(lia)).
  - exact (tl_afact E 51 (Boxreg.bx_n bs') (4 + 1) 5 E51 ltac:(lia) ltac:(lia)). }
destruct Hkn as [-> | ->].
{ (* known = -1 *)

assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa20 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 4); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 4)]))
     LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 [tl_regn TL_RCH] (mkFacts (TL_AFP 4) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - exact HSL.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact HRG | apply Forall_nil].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 TL_RCH HB HJ HFR HBLK HE E20).
  - split; [exact HFACT | split; exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.

psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, (tl_width_u1 E w7 E23 Hw7), U_lit in Hc by lia; discriminate ].

paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.

assert (HMM : ms_mem ms0 = ms_mem ms3) by (rewrite HM2; exact HM1).
assert (Hk0 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms0)) by (apply tl_keep_eq; rewrite HMM; reflexivity).
assert (HCR : tl_callregs cx (ms_regs ms0) 0xa94).
{ split; [rewrite Q2; exact E2|]. split; [rewrite Q8; exact E8|]. split; [rewrite Q3; exact E3|].
  split; [rewrite Q4; exact E4|]. split; [exact Q1|]. split; [lia | reflexivity]. }
pose proof (tl_tmem_keep i cx fp W3 _ ms3 ms0 q r fab bs M nch nz lf HB Hk0 HTM) as (_ & _ & _ & _ & _ & (HMAC0 & _) & _).
eapply SRr_bind.
{ eapply (tl_bcmp_call cx fp k ly3 S3 W3 ms0 _ r bs' M 4 0xa94 HB HJ HFR HBLK).
  - apply (lx_shadow_keep cx fp W3 _ ms3 ms0 LSH_iter Hk0); [vm_compute; congruence | exact HSH].
  - exact (lx_reg_keep cx fp W3 _ ms3 ms0 r bs' Hk0 ltac:(left; reflexivity) HREG).
  - exact HMAC0.
  - exact HL288'.
  - lia.
  - exact HMACz.
  - exact HCR.
  - rewrite Q10. rewrite ?E20. unfold w64. rewrite ?unsigned_lit_small by lia. first [reflexivity | f_equal; lia].
  - rewrite Q11, E46. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - exact Q12. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H0 & HK2).
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
assert (Hk2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2) by exact (lx_keep_trans cx fp W3 _ _ _ _ Hk0 HK2).
set (ms1 := mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)).
assert (Hk1 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms1)) by exact Hk2.
assert (G : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr (ms_regs ms1) rr = getr (ms_regs ms0) rr)
  by (intros rr Hrr; exact (tl_reg_kept _ _ rr HP2 Hrr)).
eexists q, r, fab, bs, M, nch, nz, lf, want, w7, _, 4, bs'.
split.
{ split.
  { apply (tl_body_mk cx fp 0xa20 0xa94 W3 [(r, LX_REG)] ms3 regs2 mem2 HB Hk2 HBODY).
    tl_lregs G Q2 Q8 Q9 Q3 Q4 Q18 Q22 E2 E8 E3 E4 E32 E22. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (tl_tmem_keep i cx fp W3 _ ms3 ms1 q r fab bs M nch nz lf HB Hk1 HTM)|].
  split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7b|].
  split; [tl_rk G Q20 E R20|].
  split; [tl_rk G Q21 E R21|].
  split; [rewrite G by tl_cs; rewrite Q25, <- Ewant; reflexivity|].
  split; [tl_rk G Q26 E R26|].
  tl_rk G Q27 E R27. }
split; [exact (lx_reg_keep cx fp W3 _ ms3 ms1 r bs' Hk1 ltac:(left; reflexivity) HREG)|].
split; [exact HFRES|]. split; [exact HADD|]. split; [lia|].
split; [cbn; exact H0|].
split; [rewrite G by tl_cs; rewrite Q19; reflexivity|].
split; [rewrite G by tl_cs; rewrite Q23; rewrite ?E20; unfold w64; rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]|].
rewrite G by tl_cs; rewrite Q24; first [reflexivity | apply bv_eq; vm_compute; reflexivity].
}

{ (* known = idx *)

assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa20 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 4); ((24%bv : bv 5), SLit 4); ((25%bv : bv 5), SLit 4)]))
     LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 [tl_regn TL_RCH] (mkFacts (TL_AFP 4) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - exact HSL.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact HRG | apply Forall_nil].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks TL_SL) [] 0 0 0 0 TL_RCH HB HJ HFR HBLK HE E20).
  - split; [exact HFACT | split; exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.

psrr_branch_tok RUN BR HS SHOK TL_BSPAN.
{ exfalso. rewrite tl_bne, (tl_width_u0 E w7 E23 Hw7 Hw7z), U_lit in Hc by lia. discriminate. }
clear Hc.

paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.

assert (HMM : ms_mem ms0 = ms_mem ms3) by (rewrite HM2; exact HM1).
assert (Hk0 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms0)) by (apply tl_keep_eq; rewrite HMM; reflexivity).
assert (HCR : tl_callregs cx (ms_regs ms0) 0xa94).
{ split; [rewrite Q2; exact E2|]. split; [rewrite Q8; exact E8|]. split; [rewrite Q3; exact E3|].
  split; [rewrite Q4; exact E4|]. split; [exact Q1|]. split; [lia | reflexivity]. }
pose proof (tl_tmem_keep i cx fp W3 _ ms3 ms0 q r fab bs M nch nz lf HB Hk0 HTM) as (_ & _ & _ & _ & _ & (HMAC0 & _) & _).
eapply SRr_bind.
{ eapply (tl_bcmp_call cx fp k ly3 S3 W3 ms0 _ r bs' M 4 0xa94 HB HJ HFR HBLK).
  - apply (lx_shadow_keep cx fp W3 _ ms3 ms0 LSH_iter Hk0); [vm_compute; congruence | exact HSH].
  - exact (lx_reg_keep cx fp W3 _ ms3 ms0 r bs' Hk0 ltac:(left; reflexivity) HREG).
  - exact HMAC0.
  - exact HL288'.
  - lia.
  - exact HMACz.
  - exact HCR.
  - rewrite Q10. rewrite ?E20. unfold w64. rewrite ?unsigned_lit_small by lia. first [reflexivity | f_equal; lia].
  - rewrite Q11, E46. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - exact Q12. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H0 & HK2).
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
assert (Hk2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2) by exact (lx_keep_trans cx fp W3 _ _ _ _ Hk0 HK2).
set (ms1 := mkst regs2 (Z_to_bv 64 (BASE + 0xa94)) mem2 (seg_rom SEGS)).
assert (Hk1 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms1)) by exact Hk2.
assert (G : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr (ms_regs ms1) rr = getr (ms_regs ms0) rr)
  by (intros rr Hrr; exact (tl_reg_kept _ _ rr HP2 Hrr)).
eexists q, r, fab, bs, M, nch, nz, lf, want, w7, _, 4, bs'.
split.
{ split.
  { apply (tl_body_mk cx fp 0xa20 0xa94 W3 [(r, LX_REG)] ms3 regs2 mem2 HB Hk2 HBODY).
    tl_lregs G Q2 Q8 Q9 Q3 Q4 Q18 Q22 E2 E8 E3 E4 E32 E22. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (tl_tmem_keep i cx fp W3 _ ms3 ms1 q r fab bs M nch nz lf HB Hk1 HTM)|].
  split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7b|].
  split; [tl_rk G Q20 E R20|].
  split; [tl_rk G Q21 E R21|].
  split; [rewrite G by tl_cs; rewrite Q25, <- Ewant; reflexivity|].
  split; [tl_rk G Q26 E R26|].
  tl_rk G Q27 E R27. }
split; [exact (lx_reg_keep cx fp W3 _ ms3 ms1 r bs' Hk1 ltac:(left; reflexivity) HREG)|].
split; [exact HFRES|]. split; [exact HADD|]. split; [lia|].
split; [cbn; exact H0|].
split; [rewrite G by tl_cs; rewrite Q19; reflexivity|].
split; [rewrite G by tl_cs; rewrite Q23; rewrite ?E20; unfold w64; rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]|].
rewrite G by tl_cs; rewrite Q24; first [reflexivity | apply bv_eq; vm_compute; reflexivity].
}

Qed.


Lemma tl_width_ux : forall E w, ew E 23 = w64 w -> 0 <= w < 2 ^ 64 ->
  U E (SAlu ALU_AND (SAlu ALU_OR (SOff 23 0) (SLit 0)) (SLit 1)) = Z.land w 1.
Proof.
  intros E w H23 Hw.
  assert (U23 : U E (SOff 23 0) = w) by (apply (U_atom E 23 w); [rewrite H23; reflexivity | lia]).
  pose proof (Z.land_ones w 1 ltac:(lia)) as H1. change (Z.ones 1) with 1 in H1. change (2 ^ 1) with 2 in H1.
  pose proof (Z.mod_pos_bound w 2 ltac:(lia)) as H2.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite U23, !U_lit by lia. rewrite Z.lor_0_r, (zcanon_id w) by (unfold M64; lia).
  apply zcanon_id. unfold M64. lia.
Qed.

Definition TW3N : Prop :=
  forall POST i, lx_from B MT POST (LI_K B MT i) ->
  forall cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3 q r fab bs M nch nz lf want w7 known bs',
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S3 acc ->
  tcore i cx fp 0xa20 k acc ly3 S3 W3 ms3 q r fab bs M nch nz lf want w7 ->
  lreg W3 ms3 r bs' -> reac_boxreg_find_c.find_result bs M known ->
  reac_boxreg_add_c.add_out bs M nch (-1) bs' ->
  getr (ms_regs ms3) 10 = w64 (-1) -> getr (ms_regs ms3) 23 = w64 w7 -> getr (ms_regs ms3) 24 = w64 known ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

Lemma tl_w3_n : TW3N.
Proof.

intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs'
  HB HJ HFR HMO HCO HREG HFRES HADD R10 R23 R24.
pose proof (lh_laws B MT HY) as LAWS.
pose proof HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & Hlf & HW & Hwant & Hw7 & Hw7b & R20 & R21 & R25 & R26 & R27).
pose proof HTM as (HPREV & HCUR & HSLL & S58 & S48 & HRD & HNZ & S20).
pose proof HRD as (HMAC & S50 & Hnch). pose proof HMAC as (HML & HMB).
pose proof HNZ as (S60 & Hnzr & Hnzi).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
pose proof (LC1.c1_inv_n bs HINV) as HnB.
pose proof (lxc1_add_keeps bs M nch _ bs' HINV HML HADD) as (HINV' & HFAB' & HKEPT).
destruct (LC1.c1_add_want bs M nch lf want (-1) bs' HINV HML HW HADD) as (Ewant & _).
pose proof (LC1.c1_find_range bs M known HFRES HnB) as Hkr.
set (ex := [w64 nz]).
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (E48 : ew E 48 = w64 nz) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
assert (E20 : ew E 20 = w64 r) by (unfold E; erewrite lx_env_reg; [exact R20 | reflexivity]).
assert (E23 : ew E 23 = w64 w7) by (unfold E; erewrite lx_env_reg; [exact R23 | reflexivity]).
assert (E24 : ew E 24 = w64 known) by (unfold E; erewrite lx_env_reg; [exact R24 | reflexivity]).
assert (E26 : ew E 26 = w64 (Boxreg.bx_n bs)) by (unfold E; erewrite lx_env_reg; [exact R26 | reflexivity]).
assert (E21 : ew E 21 = w64 (lF cx fp + 64)) by (unfold E; erewrite lx_env_reg; [exact R21 | reflexivity]).
assert (E27 : ew E 27 = w64 fab) by (unfold E; erewrite lx_env_reg; [exact R27 | reflexivity]).
assert (HAF0 : atoms_ok E LX_AF) by exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE).
assert (AF26 : afact_ok E 26 (mkAF 0 5 0)) by exact (tl_afact E 26 (Boxreg.bx_n bs) 0 5 E26 ltac:(lia) ltac:(lia)).
pose (RUN := paj_run B LAWS). pose (RUNTO := paj_run_to B LAWS). pose (BR := paj_branch (PI := PI)).
destruct (Z.eq_dec nz 0) as [Hnz0 | Hnz0]; (destruct (Z_lt_ge_dec known 0) as [Hkn | Hkn]; [assert (known = -1) as -> by lia|]).
- { 
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa20 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 18446744073709551615); ((24%bv : bv 5), SLit 18446744073709551615)])) LSH_iter (lx_slot_chunks [(0x60, SLit 0)]) [] 0 0 0 0 [] (mkFacts (LX_AF ++ [(26%nat, mkAF 0 5 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. apply bv_eq. vm_compute. reflexivity.
    + rewrite R25, <- Ewant. apply bv_eq. vm_compute. reflexivity.
    + rewrite R24. apply bv_eq. vm_compute. reflexivity.
  - unfold lx_slots. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. apply (lx_slot_lit cx W3 ms3 E _ 0); [rewrite <- Hnz0; exact S60 | lia].
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat apply Forall_cons; try apply Forall_nil; exact I.
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF26 | exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, (tl_width_u1 E w7 E23 Hw7), U_lit in Hc by lia; discriminate ].

paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xa20 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT
  ltac:(rewrite HM2, HM1; reflexivity) HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].
 }
- { 
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa20 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 18446744073709551615)])) LSH_iter (lx_slot_chunks [(0x60, SLit 0)]) [] 0 0 0 0 [] (mkFacts (LX_AF ++ (24%nat, mkAF 0 4 0) :: [(26%nat, mkAF 0 5 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. apply bv_eq. vm_compute. reflexivity.
    + rewrite R25, <- Ewant. apply bv_eq. vm_compute. reflexivity.
  - unfold lx_slots. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. apply (lx_slot_lit cx W3 ms3 E _ 0); [rewrite <- Hnz0; exact S60 | lia].
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat apply Forall_cons; try apply Forall_nil; exact I.
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact (tl_afact E 24 known 0 4 E24 ltac:(lia) ltac:(lia)) | split; [exact AF26 | exact I]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, (tl_width_ux E w7 E23 Hw7), U_lit in Hc by lia;
  apply negb_false_iff, Z.eqb_eq in Hc;
  pose proof (LC1.c1_known bs M nch known (-1) bs' HFRES ltac:(lia) ltac:(rewrite HFAB; apply Hw7b; exact Hc) HADD); lia ].

paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xa20 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT
  ltac:(rewrite HM2, HM1; reflexivity) HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].
 }
- { 
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa20 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 18446744073709551615); ((24%bv : bv 5), SLit 18446744073709551615)])) LSH_iter (lx_slot_chunks [(0x60, SOff 48 0)]) [] 0 0 0 0 [] (mkFacts (LX_AF ++ (48%nat, mkAF 1 (2 ^ 64 - 1) 0) :: [(26%nat, mkAF 0 5 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. apply bv_eq. vm_compute. reflexivity.
    + rewrite R25, <- Ewant. apply bv_eq. vm_compute. reflexivity.
    + rewrite R24. apply bv_eq. vm_compute. reflexivity.
  - unfold lx_slots. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. apply (lx_slot_atom cx W3 ms3 E _ 48 nz 0); [rewrite Z.add_0_r; exact S60 | exact E48 | lia | lia].
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat apply Forall_cons; try apply Forall_nil; exact I.
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact (tl_afact E 48 nz 1 (2 ^ 64 - 1) E48 ltac:(lia) ltac:(lia)) | split; [exact AF26 | exact I]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, (tl_width_u1 E w7 E23 Hw7), U_lit in Hc by lia; discriminate ].

paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xa20 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT
  ltac:(rewrite HM2, HM1; reflexivity) HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].
 }
- { 
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa20 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 18446744073709551615)])) LSH_iter (lx_slot_chunks [(0x60, SOff 48 0)]) [] 0 0 0 0 [] (mkFacts (LX_AF ++ (24%nat, mkAF 0 4 0) :: (48%nat, mkAF 1 (2 ^ 64 - 1) 0) :: [(26%nat, mkAF 0 5 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. apply bv_eq. vm_compute. reflexivity.
    + rewrite R25, <- Ewant. apply bv_eq. vm_compute. reflexivity.
  - unfold lx_slots. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. apply (lx_slot_atom cx W3 ms3 E _ 48 nz 0); [rewrite Z.add_0_r; exact S60 | exact E48 | lia | lia].
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat apply Forall_cons; try apply Forall_nil; exact I.
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact (tl_afact E 24 known 0 4 E24 ltac:(lia) ltac:(lia)) | split; [exact (tl_afact E 48 nz 1 (2 ^ 64 - 1) E48 ltac:(lia) ltac:(lia)) | split; [exact AF26 | exact I]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, (tl_width_ux E w7 E23 Hw7), U_lit in Hc by lia;
  apply negb_false_iff, Z.eqb_eq in Hc;
  pose proof (LC1.c1_known bs M nch known (-1) bs' HFRES ltac:(lia) ltac:(rewrite HFAB; apply Hw7b; exact Hc) HADD); lia ].

paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xa20 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT
  ltac:(rewrite HM2, HM1; reflexivity) HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].
 }
Qed.


Lemma tl_w3 : forall POST i, lx_from B MT POST (LI_K B MT i) -> lx_from B MT POST (TKP 0xa94 false i) ->
  lx_from B MT POST (TK2 i).
Proof.
  intros POST i HK HP cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
  destruct HGI as (q & r & fab & bs & M & nch & nz & lf & want & w7 & known & idx & bs' & HCO & HREG & HFRES & HADD & R10 & R23 & R24).
  pose proof HCO as (_ & _ & _ & _ & _ & HINV & _).
  pose proof (LC1.c1_add_range bs M nch idx bs' HINV HADD) as Hr.
  assert (Hc : idx = -1 \/ idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3 \/ idx = 4) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]].
  - exact (tl_w3_n POST i HK cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs' HB HJ HFR HMO HCO HREG HFRES HADD R10 R23 R24).
  - exact (tl_w3_p0 POST i HP cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs' HB HJ HFR HMO HCO HREG HFRES HADD R10 R23 R24).
  - exact (tl_w3_p1 POST i HP cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs' HB HJ HFR HMO HCO HREG HFRES HADD R10 R23 R24).
  - exact (tl_w3_p2 POST i HP cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs' HB HJ HFR HMO HCO HREG HFRES HADD R10 R23 R24).
  - exact (tl_w3_p3 POST i HP cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs' HB HJ HFR HMO HCO HREG HFRES HADD R10 R23 R24).
  - exact (tl_w3_p4 POST i HP cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs' HB HJ HFR HMO HCO HREG HFRES HADD R10 R23 R24).
Qed.


(* ---- W4: 0x80a40 `bnez a0` (bcmp's 0) .. the second reac_boxreg_find at 0x80a4c, back at 0x80a50 ---- *)
Lemma tl_w4 : forall POST i, lx_from B MT POST (TKP 0xaa4 true i) -> lx_from B MT POST (TKP 0xa94 false i).
Proof.
intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
pose proof (lh_laws B MT HY) as LAWS.
destruct HGI as (q & r & fab & bs & M & nch & nz & lf & want & w7 & known & idx & bs' & HCO & HREG & HFRES & HADD & Hidx & R10 & R19 & R23 & R24).
pose proof HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & Hlf & HW & Hwant & Hw7 & Hw7b & R20 & R21 & R25 & R26 & R27).
pose proof HTM as (HPREV & HCUR & HSLL & S58 & S48 & HRD & HNZ & S20).
pose proof HRD as (HMAC & S50 & Hnch). pose proof HMAC as (HML & HMB).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof (lxc1_add_keeps bs M nch idx bs' HINV HML HADD) as (HINV' & HFAB' & HKEPT).
destruct (LC1.c1_add_pos bs M nch idx bs' HINV HML HADD Hidx) as (HMZ & Ao & Hfab' & Hn5 & Hh' & Hcase).
cbn in R10.
set (ex := ([] : list word)).
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xa94 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 0)])) LSH_iter (lx_slot_chunks [(0x68, SOff LA_F 32)]) [] 0 0 0 0 []
     (mkFacts LX_AF [] [])) (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    apply Forall_cons; [|apply Forall_nil]. cbn [fst snd sv_denot]. rewrite R10. reflexivity.
  - unfold lx_slots. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    apply (lx_slot_atom cx W3 ms3 E _ LA_F (lF cx fp) 32); [exact L68 | exact E46 | lia | lia].
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat apply Forall_cons; try apply Forall_nil; exact I.
  - split; [exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE) | split; exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
pose (RUN := paj_run B LAWS).
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F in E2, E8, E22, E32, E46.
assert (E20 : ew E 20 = w64 r) by (unfold E; erewrite lx_env_reg; [exact R20 | reflexivity]).
assert (EF32 : Z_to_bv 64 (bv_unsigned (ew E 46) + 32) = w64 (lF cx fp + 32))
  by (rewrite E46; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hk0 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms)) by (apply tl_keep_eq; rewrite HM; reflexivity).
assert (HCR : tl_callregs cx (ms_regs ms) 0xaa4).
{ split; [rewrite Q2; exact E2|]. split; [rewrite Q8; exact E8|]. split; [rewrite Q3; exact E3|].
  split; [rewrite Q4; exact E4|]. split; [exact Q1|]. split; [lia | reflexivity]. }
pose proof (tl_tmem_keep i cx fp W3 _ ms3 ms q r fab bs M nch nz lf HB Hk0 HTM) as (_ & _ & _ & _ & _ & (HMACc & _) & _).
eapply SRr_bind.
{ eapply (tl_find_call cx fp k ly3 S3 W3 ms _ r bs' M 0xaa4 HB HJ HFR HBLK).
  - exact (lx_saved_keep B MT cx fp W3 HB _ ms3 ms Hk0 HSAVED).
  - apply (lx_shadow_keep cx fp W3 _ ms3 ms LSH_iter Hk0); [vm_compute; congruence | exact HSH].
  - exact (lx_reg_keep cx fp W3 _ ms3 ms r bs' Hk0 ltac:(left; reflexivity) HREG).
  - exact HMACc.
  - exact HINV'.
  - exact HCR.
  - rewrite Q10. exact E20.
  - rewrite Q11. exact EF32. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & z & -> & HJ2 & HP2 & Hz & Hres & HK2).
pose proof (LC1.c1_find_held bs' M idx z HMZ Hh' Hres) as ->.
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0xaa4)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
assert (Hk2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2) by exact (lx_keep_trans cx fp W3 _ _ _ _ Hk0 HK2).
set (ms1 := mkst regs2 (Z_to_bv 64 (BASE + 0xaa4)) mem2 (seg_rom SEGS)).
assert (Hk1 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms1)) by exact Hk2.
assert (G : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr (ms_regs ms1) rr = getr (ms_regs ms) rr)
  by (intros rr Hrr; exact (tl_reg_kept _ _ rr HP2 Hrr)).
exists q, r, fab, bs, M, nch, nz, lf, want, w7, known, idx, bs'.
split.
{ split.
  { apply (tl_body_mk cx fp 0xa94 0xaa4 W3 [(r, LX_REG)] ms3 regs2 mem2 HB Hk2 HBODY).
    tl_lregs G Q2 Q8 Q9 Q3 Q4 Q18 Q22 E2 E8 E3 E4 E32 E22. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (tl_tmem_keep i cx fp W3 _ ms3 ms1 q r fab bs M nch nz lf HB Hk1 HTM)|].
  split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7b|].
  split; [tl_rk G Q20 E R20|]. split; [tl_rk G Q21 E R21|]. split; [tl_rk G Q25 E R25|].
  split; [tl_rk G Q26 E R26|]. tl_rk G Q27 E R27. }
split; [exact (lx_reg_keep cx fp W3 _ ms3 ms1 r bs' Hk1 ltac:(left; reflexivity) HREG)|].
split; [exact HFRES|]. split; [exact HADD|]. split; [exact Hidx|].
split; [cbn; exact Hz|].
split; [tl_rk G Q19 E R19|]. split; [tl_rk G Q23 E R23|]. tl_rk G Q24 E R24.
Qed.


(* ---- W5: 0x80a50 `bne a0, s3` (find gave idx again) .. the second reac_boxreg_add at 0x80a60, back at 0x80a64 ---- *)
Lemma tl_w5 : forall POST i, lx_from B MT POST (TKP 0xab8 true i) -> lx_from B MT POST (TKP 0xaa4 true i).
Proof.
intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
pose proof (lh_laws B MT HY) as LAWS.
destruct HGI as (q & r & fab & bs & M & nch & nz & lf & want & w7 & known & idx & bs' & HCO & HREG & HFRES & HADD & Hidx & R10 & R19 & R23 & R24).
pose proof HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & Hlf & HW & Hwant & Hw7 & Hw7b & R20 & R21 & R25 & R26 & R27).
pose proof HTM as (HPREV & HCUR & HSLL & S58 & S48 & HRD & HNZ & S20).
pose proof HRD as (HMAC & S50 & Hnch). pose proof HMAC as (HML & HMB).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof (lxc1_add_keeps bs M nch idx bs' HINV HML HADD) as (HINV' & HFAB' & HKEPT).
destruct (LC1.c1_add_pos bs M nch idx bs' HINV HML HADD Hidx) as (HMZ & Ao & Hfab' & Hn5 & Hh' & Hcase).
cbn in R10.
set (ex := [w64 nch]).
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (E48 : ew E 48 = w64 nch) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
assert (E19 : ew E 19 = w64 idx) by (unfold E; erewrite lx_env_reg; [exact R19 | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xaa4 (lx_sr (LX_OV ++ [((10%bv : bv 5), SOff 19 0)]))
     LSH_iter (lx_slot_chunks [(0x50, SOff 48 0); (0x68, SOff LA_F 32)]) [] 0 0 0 0 []
     (mkFacts LX_AF [] [])) (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. rewrite lx_sv_SOff0, E19, R10. reflexivity.
  - unfold lx_slots. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + apply (lx_slot_atom cx W3 ms3 E _ 48 nch 0); [rewrite Z.add_0_r; exact S50 | exact E48 | lia | lia].
    + apply (lx_slot_atom cx W3 ms3 E _ LA_F (lF cx fp) 32); [exact L68 | exact E46 | lia | lia].
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat apply Forall_cons; try apply Forall_nil; exact I.
  - split; [exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE) | split; exact I]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
pose (RUN := paj_run B LAWS).
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F in E2, E8, E22, E32, E46.
assert (E20 : ew E 20 = w64 r) by (unfold E; erewrite lx_env_reg; [exact R20 | reflexivity]).
assert (EF32 : Z_to_bv 64 (bv_unsigned (ew E 46) + 32) = w64 (lF cx fp + 32))
  by (rewrite E46; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hk0 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms)) by (apply tl_keep_eq; rewrite HM; reflexivity).
assert (Hk0' : lx_keep cx fp W3 [] (ms_mem ms3) (ms_mem ms)) by (apply tl_keep_eq; rewrite HM; reflexivity).
assert (HCR : tl_callregs cx (ms_regs ms) 0xab8).
{ split; [rewrite Q2; exact E2|]. split; [rewrite Q8; exact E8|]. split; [rewrite Q3; exact E3|].
  split; [rewrite Q4; exact E4|]. split; [exact Q1|]. split; [lia | reflexivity]. }
pose proof (tl_tmem_keep i cx fp W3 _ ms3 ms q r fab bs M nch nz lf HB Hk0 HTM) as (_ & _ & _ & _ & _ & (HMACc & _) & _).
eapply SRr_bind.
{ eapply (tl_add_call cx fp k ly3 S3 W3 ms _ r bs' M nch 0xab8 HB HJ HFR HBLK).
  - exact (lx_saved_keep B MT cx fp W3 HB _ ms3 ms Hk0 HSAVED).
  - apply (lx_shadow_keep cx fp W3 _ ms3 ms LSH_iter Hk0); [vm_compute; congruence | exact HSH].
  - exact (lx_reg_keep cx fp W3 _ ms3 ms r bs' Hk0 ltac:(left; reflexivity) HREG).
  - exact HMACc.
  - exact HINV'.
  - exact Hnch.
  - exact HCR.
  - rewrite Q10. exact E20.
  - rewrite Q11. exact EF32.
  - rewrite Q12. exact E48. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & z & bs3 & -> & HJ2 & HP2 & Hz & Hres & HBS & HK2).
destruct (LC1.c1_add_again bs' M nch idx z bs3 HMZ ltac:(rewrite Hfab'; exact Ao) Hh' Hres) as [-> ->].
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0xab8)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
assert (Hk2 : lx_keep cx fp W3 [] (ms_mem ms3) mem2) by exact (lx_keep_trans cx fp W3 _ _ _ _ Hk0' HK2).
set (ms1 := mkst regs2 (Z_to_bv 64 (BASE + 0xab8)) mem2 (seg_rom SEGS)).
assert (Hk1 : lx_keep cx fp W3 [] (ms_mem ms3) (ms_mem ms1)) by exact Hk2.
assert (G : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr (ms_regs ms1) rr = getr (ms_regs ms) rr)
  by (intros rr Hrr; exact (tl_reg_kept _ _ rr HP2 Hrr)).
exists q, r, fab, bs, M, nch, nz, lf, want, w7, known, idx, bs'.
split.
{ split.
  { apply (tl_body_mk cx fp 0xaa4 0xab8 W3 [] ms3 regs2 mem2 HB Hk2 HBODY).
    tl_lregs G Q2 Q8 Q9 Q3 Q4 Q18 Q22 E2 E8 E3 E4 E32 E22. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split; [exact HINV|]. split; [exact HFAB|].
  split; [exact (tl_tmem_keep i cx fp W3 _ ms3 ms1 q r fab bs M nch nz lf HB Hk1 HTM)|].
  split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7b|].
  split; [tl_rk G Q20 E R20|]. split; [tl_rk G Q21 E R21|]. split; [tl_rk G Q25 E R25|].
  split; [tl_rk G Q26 E R26|]. tl_rk G Q27 E R27. }
split; [intros j Hj; exact (HBS j Hj)|].
split; [exact HFRES|]. split; [exact HADD|]. split; [exact Hidx|].
split; [cbn; exact Hz|].
split; [tl_rk G Q19 E R19|]. split; [tl_rk G Q23 E R23|]. tl_rk G Q24 E R24.
Qed.


(* ---- W6: 0x80a64 `bne a0, s3` (add gave idx again) .. the width and the new row's base and pinned checks ..
   0x80b08 ---- *)
Definition TW6 (z : Z) : Prop :=
  forall POST i, lx_from B MT POST (LI_K B MT i) ->
  forall cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3 q r fab bs M nch nz lf want w7 known bs',
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S3 acc ->
  tcore i cx fp 0xab8 k acc ly3 S3 W3 ms3 q r fab bs M nch nz lf want w7 ->
  lreg W3 ms3 r bs' -> reac_boxreg_find_c.find_result bs M known ->
  reac_boxreg_add_c.add_out bs M nch z bs' ->
  getr (ms_regs ms3) 10 = w64 z -> getr (ms_regs ms3) 19 = w64 z ->
  getr (ms_regs ms3) 23 = w64 (r + 56 * z) -> getr (ms_regs ms3) 24 = w64 known ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

Lemma tl_w6_0 : TW6 0.
Proof.

intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs'
  HB HJ HFR HMO HCO HREG HFRES HADD R10 R19 R23 R24.
pose proof (lh_laws B MT HY) as LAWS.
pose proof HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & Hlf & HW & Hwant & Hw7 & Hw7b & R20 & R21 & R25 & R26 & R27).
pose proof HTM as (HPREV & HCUR & HSLL & S58 & S48 & HRD & HNZ & S20).
pose proof HRD as (HMAC & S50 & Hnch). pose proof HMAC as (HML & HMB).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof HJ as (HAR3 & _).
assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size LX_REG) with 288 in Hrceil, Hria.
pose proof (LC1.c1_inv_n bs HINV) as HnB. pose proof (LC1.c1_inv_fab bs HINV) as HfB.
pose proof (lxc1_add_keeps bs M nch _ bs' HINV HML HADD) as (HINV' & HFAB' & HKEPT).
pose proof (LC1.c1_inv_len bs' HINV') as HL288'.
destruct (LC1.c1_add_pos bs M nch 0 bs' HINV HML HADD ltac:(lia)) as (HMZ & Ao & Hfab' & Hn5 & Hh' & Hcase).
destruct (LC1.c1_add_want bs M nch lf want 0 bs' HINV HML HW HADD) as (Ewant & Hnew).
pose proof (LC1.c1_find_range bs M known HFRES HnB) as Hkr.
assert (Hkn : known = -1 \/ known = 0).
{ destruct (Z_lt_ge_dec known 0) as [Hk0|Hk0]; [left; lia|].
  right. symmetry. exact (LC1.c1_known bs M nch known 0 bs' HFRES ltac:(lia) Ao HADD). }
cbn in R10.
set (ex := [w64 nch; w64 lf; w64 (2 ^ 64 - 1 - r)]).
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (E48 : ew E 48 = w64 nch) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
assert (E49 : ew E 49 = w64 lf) by exact (lx_env_ex cx fp (ms_regs ms3) ex 1 ltac:(lia)).
assert (E50 : ew E 50 = w64 (2 ^ 64 - 1 - r)) by exact (lx_env_ex cx fp (ms_regs ms3) ex 2 ltac:(lia)).
assert (E20 : ew E 20 = w64 r) by (unfold E; erewrite lx_env_reg; [exact R20 | reflexivity]).
assert (E21 : ew E 21 = w64 (lF cx fp + 64)) by (unfold E; erewrite lx_env_reg; [exact R21 | reflexivity]).
assert (E26 : ew E 26 = w64 (Boxreg.bx_n bs)) by (unfold E; erewrite lx_env_reg; [exact R26 | reflexivity]).
assert (E27 : ew E 27 = w64 fab) by (unfold E; erewrite lx_env_reg; [exact R27 | reflexivity]).
unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F in E2, E8, E22, E32, E46.
assert (HAF0 : atoms_ok E LX_AF) by exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE).
assert (AF20 : afact_ok E 20 (mkAF 4096 140737479966720 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E20. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [change (2 ^ 4) with 16; exact Hr16 | lia]. }
assert (AF48 : afact_ok E 48 (mkAF 0 255 0)) by exact (tl_afact E 48 nch 0 255 E48 ltac:(lia) ltac:(lia)).
assert (AF50 : afact_ok E 50 (mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0))
  by exact (tl_afact E 50 (2 ^ 64 - 1 - r) (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) E50 ltac:(lia) ltac:(lia)).
assert (SL30 : rdword (lview W3 ms3) (lsp1 cx + 0x30) = Some (bv_unsigned (sv_denot E (SOff 27 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 27 fab 0); [rewrite Z.add_0_r; exact L30 | exact E27 | lia | lia]).
assert (SL50 : rdword (lview W3 ms3) (lsp1 cx + 0x50) = Some (bv_unsigned (sv_denot E (SOff 48 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 48 nch 0); [rewrite Z.add_0_r; exact S50 | exact E48 | lia | lia]).
assert (SL70 : rdword (lview W3 ms3) (lsp1 cx + 0x70) = Some (bv_unsigned (sv_denot E (SOff 50 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 50 (2 ^ 64 - 1 - r) 0); [rewrite Z.add_0_r; exact L70 | exact E50 | lia | lia]).
assert (SH0 : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
assert (OV23 : sv_denot E (SOff 20 (56 * 0)) = getr (ms_regs ms3) 23).
{ cbn [sv_denot]. rewrite E20, R23. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
pose (RUN := paj_run B LAWS). pose (RUNTO := paj_run_to B LAWS). pose (BR := paj_branch (PI := PI)).
destruct Hkn as [-> | ->].
- (* known = -1: the row is new or an unbound one bound now; it has the asked width *)
  assert (HN : reac_boxreg_add_c.add_none_held bs M) by exact (LC1.c1_find_none bs M (-1) HFRES ltac:(lia) HMZ).
  assert (Hnch12 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 0 + 12))) = nch).
  { change (Z.of_nat (Z.to_nat (56 * 0 + 12))) with (56 * 0 + 12). change (Boxreg.rd4 bs' (56 * 0 + 12)) with (Boxreg.bx_nch bs' 0).
    destruct Hcase as [(Hh & _) | (_ & Hk')]; [exfalso; destruct Hh as (Hi & Mi & _); exact (HN 0 Hi Mi) | exact Hk']. }
  destruct (Z.eq_dec 0 (Boxreg.bx_n bs)) as [Hznb | Hznb].
  + (* a new row: its base is lf, its pinned word 0 *)
    destruct (Hnew ltac:(lia)) as (Hb' & Hp'). rewrite <- Ewant in Hb', Hp'.
    assert (Hlf0 : 0 <= lf).
    { destruct HW as [(_ & W1) | [(_ & _ & (W2 & _)) | [(_ & _ & _ & (W3' & _)) | [(_ & _ & _ & _ & _ & W4) | (_ & _ & _ & _ & _ & _ & W5 & _)]]]]; lia. }
    assert (Hbase8 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 0 + 8))) = lf).
    { change (Z.of_nat (Z.to_nat (56 * 0 + 8))) with (56 * 0 + 8). change (Boxreg.rd4 bs' (56 * 0 + 8)) with (Boxreg.bx_base bs' 0).
      exact Hb'. }
    assert (Hpin20 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 0 + 20))) = 0).
    { change (Z.of_nat (Z.to_nat (56 * 0 + 20))) with (56 * 0 + 20). change (Boxreg.rd4 bs' (56 * 0 + 20)) with (Boxreg.bx_pinned bs' 0).
      exact Hp'. }
    
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 0); ((19%bv : bv 5), SLit 0); ((23%bv : bv 5), SOff 20 (56 * 0)); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 0); ((26%bv : bv 5), SLit 0)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SLit 0); (0x50, SOff 48 0); (0x70, SOff 50 0); (0x20, SOff 49 0)]) [] 0 0 0 0 [tl_regn [YP09.mkChunk (56 * 0 + 8) (CVal 4 (SOff 49 0)); YP09.mkChunk (56 * 0 + 12) (CVal 4 (SOff 48 0)); YP09.mkChunk (56 * 0 + 20) (CVal 4 (SLit 0))]] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0); (49%nat, mkAF 0 38 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
    + rewrite R26, <- Hznb. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_lit cx W3 ms3 E _ 0); [rewrite Hznb; exact S48 | lia].
    + exact SL50.
    + exact SL70.
    + apply (lx_slot_atom cx W3 ms3 E _ 49 lf 0); [rewrite Z.add_0_r, <- (Z.mod_small lf (2 ^ 64)) by lia; exact S20 | exact E49 | lia | lia].
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + change (56 * 0 + 8) with (Z.of_nat (Z.to_nat (56 * 0 + 8))).
      apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 0 + 8)) 49 lf HREG HL288' ltac:(cbn; lia)); [exact Hbase8 | lia | rewrite lx_sv_SOff0, E49; reflexivity].
    + change (56 * 0 + 12) with (Z.of_nat (Z.to_nat (56 * 0 + 12))).
      apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 0 + 12)) 48 nch HREG HL288' ltac:(cbn; lia)); [exact Hnch12 | lia | rewrite lx_sv_SOff0, E48; reflexivity].
    + change (56 * 0 + 20) with (Z.of_nat (Z.to_nat (56 * 0 + 20))).
      apply (tl_word_chunk_lit E W3 ms3 r bs' (Z.to_nat (56 * 0 + 20)) 0 HREG HL288' ltac:(cbn; lia)); [exact Hpin20 | lia].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SLit 0); (0x50, SOff 48 0); (0x70, SOff 50 0); (0x20, SOff 49 0)]) [] 0 0 0 0 _ HB HJ HFR HBLK HE E20).
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | split; [exact (tl_afact E 49 lf 0 38 E49 ltac:(lia) ltac:(lia)) | exact I]]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))) by exact SH0.
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

  + 
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 0); ((19%bv : bv 5), SLit 0); ((23%bv : bv 5), SOff 20 (56 * 0)); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 0)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 [tl_regn [YP09.mkChunk (56 * 0 + 12) (CVal 4 (SOff 48 0))]] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_atom cx W3 ms3 E _ 26 (Boxreg.bx_n bs) 0); [rewrite Z.add_0_r; exact S48 | exact E26 | lia | lia].
    + exact SL50.
    + exact SL70.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
    apply Forall_cons; [|apply Forall_nil].
    change (56 * 0 + 12) with (Z.of_nat (Z.to_nat (56 * 0 + 12))).
    apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 0 + 12)) 48 nch HREG HL288' ltac:(cbn; lia)); [exact Hnch12 | lia | rewrite lx_sv_SOff0, E48; reflexivity].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 _ HB HJ HFR HBLK HE E20).
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | exact I]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))) by exact SH0.
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, U_lit, (U_atom E 26 (Boxreg.bx_n bs) E26) in Hc by lia;
  apply negb_false_iff, Z.eqb_eq in Hc; lia ].
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms0) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM2, HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

- (* known = idx: the row was held, so idx < n_before *)
  assert (Hzn : 0 < Boxreg.bx_n bs).
  { unfold reac_boxreg_find_c.find_result, reac_boxreg_find_c.first_mac in HFRES.
    destruct HFRES as [(_ & E1) | [(_ & (H1 & _)) | (_ & E1 & _)]]; lia. }
  assert (Hznb : 0 <> Boxreg.bx_n bs) by lia.
  
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 0); ((19%bv : bv 5), SLit 0); ((23%bv : bv 5), SOff 20 (56 * 0)); ((24%bv : bv 5), SLit 0); ((25%bv : bv 5), SLit 0)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 [] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_atom cx W3 ms3 E _ 26 (Boxreg.bx_n bs) 0); [rewrite Z.add_0_r; exact S48 | exact E26 | lia | lia].
    + exact SL50.
    + exact SL70.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat apply Forall_cons; try apply Forall_nil; exact I.
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | exact I]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, U_lit, (U_atom E 26 (Boxreg.bx_n bs) E26) in Hc by lia;
  apply negb_false_iff, Z.eqb_eq in Hc; lia ].
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms0) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM2, HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

Qed.

Lemma tl_w6_1 : TW6 1.
Proof.

intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs'
  HB HJ HFR HMO HCO HREG HFRES HADD R10 R19 R23 R24.
pose proof (lh_laws B MT HY) as LAWS.
pose proof HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & Hlf & HW & Hwant & Hw7 & Hw7b & R20 & R21 & R25 & R26 & R27).
pose proof HTM as (HPREV & HCUR & HSLL & S58 & S48 & HRD & HNZ & S20).
pose proof HRD as (HMAC & S50 & Hnch). pose proof HMAC as (HML & HMB).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof HJ as (HAR3 & _).
assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size LX_REG) with 288 in Hrceil, Hria.
pose proof (LC1.c1_inv_n bs HINV) as HnB. pose proof (LC1.c1_inv_fab bs HINV) as HfB.
pose proof (lxc1_add_keeps bs M nch _ bs' HINV HML HADD) as (HINV' & HFAB' & HKEPT).
pose proof (LC1.c1_inv_len bs' HINV') as HL288'.
destruct (LC1.c1_add_pos bs M nch 1 bs' HINV HML HADD ltac:(lia)) as (HMZ & Ao & Hfab' & Hn5 & Hh' & Hcase).
destruct (LC1.c1_add_want bs M nch lf want 1 bs' HINV HML HW HADD) as (Ewant & Hnew).
pose proof (LC1.c1_find_range bs M known HFRES HnB) as Hkr.
assert (Hkn : known = -1 \/ known = 1).
{ destruct (Z_lt_ge_dec known 0) as [Hk0|Hk0]; [left; lia|].
  right. symmetry. exact (LC1.c1_known bs M nch known 1 bs' HFRES ltac:(lia) Ao HADD). }
cbn in R10.
set (ex := [w64 nch; w64 lf; w64 (2 ^ 64 - 1 - r)]).
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (E48 : ew E 48 = w64 nch) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
assert (E49 : ew E 49 = w64 lf) by exact (lx_env_ex cx fp (ms_regs ms3) ex 1 ltac:(lia)).
assert (E50 : ew E 50 = w64 (2 ^ 64 - 1 - r)) by exact (lx_env_ex cx fp (ms_regs ms3) ex 2 ltac:(lia)).
assert (E20 : ew E 20 = w64 r) by (unfold E; erewrite lx_env_reg; [exact R20 | reflexivity]).
assert (E21 : ew E 21 = w64 (lF cx fp + 64)) by (unfold E; erewrite lx_env_reg; [exact R21 | reflexivity]).
assert (E26 : ew E 26 = w64 (Boxreg.bx_n bs)) by (unfold E; erewrite lx_env_reg; [exact R26 | reflexivity]).
assert (E27 : ew E 27 = w64 fab) by (unfold E; erewrite lx_env_reg; [exact R27 | reflexivity]).
unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F in E2, E8, E22, E32, E46.
assert (HAF0 : atoms_ok E LX_AF) by exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE).
assert (AF20 : afact_ok E 20 (mkAF 4096 140737479966720 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E20. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [change (2 ^ 4) with 16; exact Hr16 | lia]. }
assert (AF48 : afact_ok E 48 (mkAF 0 255 0)) by exact (tl_afact E 48 nch 0 255 E48 ltac:(lia) ltac:(lia)).
assert (AF50 : afact_ok E 50 (mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0))
  by exact (tl_afact E 50 (2 ^ 64 - 1 - r) (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) E50 ltac:(lia) ltac:(lia)).
assert (SL30 : rdword (lview W3 ms3) (lsp1 cx + 0x30) = Some (bv_unsigned (sv_denot E (SOff 27 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 27 fab 0); [rewrite Z.add_0_r; exact L30 | exact E27 | lia | lia]).
assert (SL50 : rdword (lview W3 ms3) (lsp1 cx + 0x50) = Some (bv_unsigned (sv_denot E (SOff 48 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 48 nch 0); [rewrite Z.add_0_r; exact S50 | exact E48 | lia | lia]).
assert (SL70 : rdword (lview W3 ms3) (lsp1 cx + 0x70) = Some (bv_unsigned (sv_denot E (SOff 50 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 50 (2 ^ 64 - 1 - r) 0); [rewrite Z.add_0_r; exact L70 | exact E50 | lia | lia]).
assert (SH0 : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
assert (OV23 : sv_denot E (SOff 20 (56 * 1)) = getr (ms_regs ms3) 23).
{ cbn [sv_denot]. rewrite E20, R23. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
pose (RUN := paj_run B LAWS). pose (RUNTO := paj_run_to B LAWS). pose (BR := paj_branch (PI := PI)).
destruct Hkn as [-> | ->].
- (* known = -1: the row is new or an unbound one bound now; it has the asked width *)
  assert (HN : reac_boxreg_add_c.add_none_held bs M) by exact (LC1.c1_find_none bs M (-1) HFRES ltac:(lia) HMZ).
  assert (Hnch12 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 1 + 12))) = nch).
  { change (Z.of_nat (Z.to_nat (56 * 1 + 12))) with (56 * 1 + 12). change (Boxreg.rd4 bs' (56 * 1 + 12)) with (Boxreg.bx_nch bs' 1).
    destruct Hcase as [(Hh & _) | (_ & Hk')]; [exfalso; destruct Hh as (Hi & Mi & _); exact (HN 1 Hi Mi) | exact Hk']. }
  destruct (Z.eq_dec 1 (Boxreg.bx_n bs)) as [Hznb | Hznb].
  + (* a new row: its base is lf, its pinned word 0 *)
    destruct (Hnew ltac:(lia)) as (Hb' & Hp'). rewrite <- Ewant in Hb', Hp'.
    assert (Hlf0 : 0 <= lf).
    { destruct HW as [(_ & W1) | [(_ & _ & (W2 & _)) | [(_ & _ & _ & (W3' & _)) | [(_ & _ & _ & _ & _ & W4) | (_ & _ & _ & _ & _ & _ & W5 & _)]]]]; lia. }
    assert (Hbase8 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 1 + 8))) = lf).
    { change (Z.of_nat (Z.to_nat (56 * 1 + 8))) with (56 * 1 + 8). change (Boxreg.rd4 bs' (56 * 1 + 8)) with (Boxreg.bx_base bs' 1).
      exact Hb'. }
    assert (Hpin20 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 1 + 20))) = 0).
    { change (Z.of_nat (Z.to_nat (56 * 1 + 20))) with (56 * 1 + 20). change (Boxreg.rd4 bs' (56 * 1 + 20)) with (Boxreg.bx_pinned bs' 1).
      exact Hp'. }
    
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 1); ((19%bv : bv 5), SLit 1); ((23%bv : bv 5), SOff 20 (56 * 1)); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 1); ((26%bv : bv 5), SLit 1)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SLit 1); (0x50, SOff 48 0); (0x70, SOff 50 0); (0x20, SOff 49 0)]) [] 0 0 0 0 [tl_regn [YP09.mkChunk (56 * 1 + 8) (CVal 4 (SOff 49 0)); YP09.mkChunk (56 * 1 + 12) (CVal 4 (SOff 48 0)); YP09.mkChunk (56 * 1 + 20) (CVal 4 (SLit 0))]] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0); (49%nat, mkAF 0 38 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
    + rewrite R26, <- Hznb. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_lit cx W3 ms3 E _ 1); [rewrite Hznb; exact S48 | lia].
    + exact SL50.
    + exact SL70.
    + apply (lx_slot_atom cx W3 ms3 E _ 49 lf 0); [rewrite Z.add_0_r, <- (Z.mod_small lf (2 ^ 64)) by lia; exact S20 | exact E49 | lia | lia].
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + change (56 * 1 + 8) with (Z.of_nat (Z.to_nat (56 * 1 + 8))).
      apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 1 + 8)) 49 lf HREG HL288' ltac:(cbn; lia)); [exact Hbase8 | lia | rewrite lx_sv_SOff0, E49; reflexivity].
    + change (56 * 1 + 12) with (Z.of_nat (Z.to_nat (56 * 1 + 12))).
      apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 1 + 12)) 48 nch HREG HL288' ltac:(cbn; lia)); [exact Hnch12 | lia | rewrite lx_sv_SOff0, E48; reflexivity].
    + change (56 * 1 + 20) with (Z.of_nat (Z.to_nat (56 * 1 + 20))).
      apply (tl_word_chunk_lit E W3 ms3 r bs' (Z.to_nat (56 * 1 + 20)) 0 HREG HL288' ltac:(cbn; lia)); [exact Hpin20 | lia].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SLit 1); (0x50, SOff 48 0); (0x70, SOff 50 0); (0x20, SOff 49 0)]) [] 0 0 0 0 _ HB HJ HFR HBLK HE E20).
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | split; [exact (tl_afact E 49 lf 0 38 E49 ltac:(lia) ltac:(lia)) | exact I]]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))) by exact SH0.
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

  + 
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 1); ((19%bv : bv 5), SLit 1); ((23%bv : bv 5), SOff 20 (56 * 1)); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 1)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 [tl_regn [YP09.mkChunk (56 * 1 + 12) (CVal 4 (SOff 48 0))]] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_atom cx W3 ms3 E _ 26 (Boxreg.bx_n bs) 0); [rewrite Z.add_0_r; exact S48 | exact E26 | lia | lia].
    + exact SL50.
    + exact SL70.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
    apply Forall_cons; [|apply Forall_nil].
    change (56 * 1 + 12) with (Z.of_nat (Z.to_nat (56 * 1 + 12))).
    apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 1 + 12)) 48 nch HREG HL288' ltac:(cbn; lia)); [exact Hnch12 | lia | rewrite lx_sv_SOff0, E48; reflexivity].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 _ HB HJ HFR HBLK HE E20).
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | exact I]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))) by exact SH0.
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, U_lit, (U_atom E 26 (Boxreg.bx_n bs) E26) in Hc by lia;
  apply negb_false_iff, Z.eqb_eq in Hc; lia ].
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms0) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM2, HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

- (* known = idx: the row was held, so idx < n_before *)
  assert (Hzn : 1 < Boxreg.bx_n bs).
  { unfold reac_boxreg_find_c.find_result, reac_boxreg_find_c.first_mac in HFRES.
    destruct HFRES as [(_ & E1) | [(_ & (H1 & _)) | (_ & E1 & _)]]; lia. }
  assert (Hznb : 1 <> Boxreg.bx_n bs) by lia.
  
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 1); ((19%bv : bv 5), SLit 1); ((23%bv : bv 5), SOff 20 (56 * 1)); ((24%bv : bv 5), SLit 1); ((25%bv : bv 5), SLit 1)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 [] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_atom cx W3 ms3 E _ 26 (Boxreg.bx_n bs) 0); [rewrite Z.add_0_r; exact S48 | exact E26 | lia | lia].
    + exact SL50.
    + exact SL70.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat apply Forall_cons; try apply Forall_nil; exact I.
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | exact I]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, U_lit, (U_atom E 26 (Boxreg.bx_n bs) E26) in Hc by lia;
  apply negb_false_iff, Z.eqb_eq in Hc; lia ].
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms0) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM2, HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

Qed.

Lemma tl_w6_2 : TW6 2.
Proof.

intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs'
  HB HJ HFR HMO HCO HREG HFRES HADD R10 R19 R23 R24.
pose proof (lh_laws B MT HY) as LAWS.
pose proof HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & Hlf & HW & Hwant & Hw7 & Hw7b & R20 & R21 & R25 & R26 & R27).
pose proof HTM as (HPREV & HCUR & HSLL & S58 & S48 & HRD & HNZ & S20).
pose proof HRD as (HMAC & S50 & Hnch). pose proof HMAC as (HML & HMB).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof HJ as (HAR3 & _).
assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size LX_REG) with 288 in Hrceil, Hria.
pose proof (LC1.c1_inv_n bs HINV) as HnB. pose proof (LC1.c1_inv_fab bs HINV) as HfB.
pose proof (lxc1_add_keeps bs M nch _ bs' HINV HML HADD) as (HINV' & HFAB' & HKEPT).
pose proof (LC1.c1_inv_len bs' HINV') as HL288'.
destruct (LC1.c1_add_pos bs M nch 2 bs' HINV HML HADD ltac:(lia)) as (HMZ & Ao & Hfab' & Hn5 & Hh' & Hcase).
destruct (LC1.c1_add_want bs M nch lf want 2 bs' HINV HML HW HADD) as (Ewant & Hnew).
pose proof (LC1.c1_find_range bs M known HFRES HnB) as Hkr.
assert (Hkn : known = -1 \/ known = 2).
{ destruct (Z_lt_ge_dec known 0) as [Hk0|Hk0]; [left; lia|].
  right. symmetry. exact (LC1.c1_known bs M nch known 2 bs' HFRES ltac:(lia) Ao HADD). }
cbn in R10.
set (ex := [w64 nch; w64 lf; w64 (2 ^ 64 - 1 - r)]).
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (E48 : ew E 48 = w64 nch) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
assert (E49 : ew E 49 = w64 lf) by exact (lx_env_ex cx fp (ms_regs ms3) ex 1 ltac:(lia)).
assert (E50 : ew E 50 = w64 (2 ^ 64 - 1 - r)) by exact (lx_env_ex cx fp (ms_regs ms3) ex 2 ltac:(lia)).
assert (E20 : ew E 20 = w64 r) by (unfold E; erewrite lx_env_reg; [exact R20 | reflexivity]).
assert (E21 : ew E 21 = w64 (lF cx fp + 64)) by (unfold E; erewrite lx_env_reg; [exact R21 | reflexivity]).
assert (E26 : ew E 26 = w64 (Boxreg.bx_n bs)) by (unfold E; erewrite lx_env_reg; [exact R26 | reflexivity]).
assert (E27 : ew E 27 = w64 fab) by (unfold E; erewrite lx_env_reg; [exact R27 | reflexivity]).
unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F in E2, E8, E22, E32, E46.
assert (HAF0 : atoms_ok E LX_AF) by exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE).
assert (AF20 : afact_ok E 20 (mkAF 4096 140737479966720 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E20. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [change (2 ^ 4) with 16; exact Hr16 | lia]. }
assert (AF48 : afact_ok E 48 (mkAF 0 255 0)) by exact (tl_afact E 48 nch 0 255 E48 ltac:(lia) ltac:(lia)).
assert (AF50 : afact_ok E 50 (mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0))
  by exact (tl_afact E 50 (2 ^ 64 - 1 - r) (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) E50 ltac:(lia) ltac:(lia)).
assert (SL30 : rdword (lview W3 ms3) (lsp1 cx + 0x30) = Some (bv_unsigned (sv_denot E (SOff 27 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 27 fab 0); [rewrite Z.add_0_r; exact L30 | exact E27 | lia | lia]).
assert (SL50 : rdword (lview W3 ms3) (lsp1 cx + 0x50) = Some (bv_unsigned (sv_denot E (SOff 48 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 48 nch 0); [rewrite Z.add_0_r; exact S50 | exact E48 | lia | lia]).
assert (SL70 : rdword (lview W3 ms3) (lsp1 cx + 0x70) = Some (bv_unsigned (sv_denot E (SOff 50 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 50 (2 ^ 64 - 1 - r) 0); [rewrite Z.add_0_r; exact L70 | exact E50 | lia | lia]).
assert (SH0 : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
assert (OV23 : sv_denot E (SOff 20 (56 * 2)) = getr (ms_regs ms3) 23).
{ cbn [sv_denot]. rewrite E20, R23. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
pose (RUN := paj_run B LAWS). pose (RUNTO := paj_run_to B LAWS). pose (BR := paj_branch (PI := PI)).
destruct Hkn as [-> | ->].
- (* known = -1: the row is new or an unbound one bound now; it has the asked width *)
  assert (HN : reac_boxreg_add_c.add_none_held bs M) by exact (LC1.c1_find_none bs M (-1) HFRES ltac:(lia) HMZ).
  assert (Hnch12 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 2 + 12))) = nch).
  { change (Z.of_nat (Z.to_nat (56 * 2 + 12))) with (56 * 2 + 12). change (Boxreg.rd4 bs' (56 * 2 + 12)) with (Boxreg.bx_nch bs' 2).
    destruct Hcase as [(Hh & _) | (_ & Hk')]; [exfalso; destruct Hh as (Hi & Mi & _); exact (HN 2 Hi Mi) | exact Hk']. }
  destruct (Z.eq_dec 2 (Boxreg.bx_n bs)) as [Hznb | Hznb].
  + (* a new row: its base is lf, its pinned word 0 *)
    destruct (Hnew ltac:(lia)) as (Hb' & Hp'). rewrite <- Ewant in Hb', Hp'.
    assert (Hlf0 : 0 <= lf).
    { destruct HW as [(_ & W1) | [(_ & _ & (W2 & _)) | [(_ & _ & _ & (W3' & _)) | [(_ & _ & _ & _ & _ & W4) | (_ & _ & _ & _ & _ & _ & W5 & _)]]]]; lia. }
    assert (Hbase8 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 2 + 8))) = lf).
    { change (Z.of_nat (Z.to_nat (56 * 2 + 8))) with (56 * 2 + 8). change (Boxreg.rd4 bs' (56 * 2 + 8)) with (Boxreg.bx_base bs' 2).
      exact Hb'. }
    assert (Hpin20 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 2 + 20))) = 0).
    { change (Z.of_nat (Z.to_nat (56 * 2 + 20))) with (56 * 2 + 20). change (Boxreg.rd4 bs' (56 * 2 + 20)) with (Boxreg.bx_pinned bs' 2).
      exact Hp'. }
    
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 2); ((19%bv : bv 5), SLit 2); ((23%bv : bv 5), SOff 20 (56 * 2)); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 2); ((26%bv : bv 5), SLit 2)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SLit 2); (0x50, SOff 48 0); (0x70, SOff 50 0); (0x20, SOff 49 0)]) [] 0 0 0 0 [tl_regn [YP09.mkChunk (56 * 2 + 8) (CVal 4 (SOff 49 0)); YP09.mkChunk (56 * 2 + 12) (CVal 4 (SOff 48 0)); YP09.mkChunk (56 * 2 + 20) (CVal 4 (SLit 0))]] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0); (49%nat, mkAF 0 38 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
    + rewrite R26, <- Hznb. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_lit cx W3 ms3 E _ 2); [rewrite Hznb; exact S48 | lia].
    + exact SL50.
    + exact SL70.
    + apply (lx_slot_atom cx W3 ms3 E _ 49 lf 0); [rewrite Z.add_0_r, <- (Z.mod_small lf (2 ^ 64)) by lia; exact S20 | exact E49 | lia | lia].
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + change (56 * 2 + 8) with (Z.of_nat (Z.to_nat (56 * 2 + 8))).
      apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 2 + 8)) 49 lf HREG HL288' ltac:(cbn; lia)); [exact Hbase8 | lia | rewrite lx_sv_SOff0, E49; reflexivity].
    + change (56 * 2 + 12) with (Z.of_nat (Z.to_nat (56 * 2 + 12))).
      apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 2 + 12)) 48 nch HREG HL288' ltac:(cbn; lia)); [exact Hnch12 | lia | rewrite lx_sv_SOff0, E48; reflexivity].
    + change (56 * 2 + 20) with (Z.of_nat (Z.to_nat (56 * 2 + 20))).
      apply (tl_word_chunk_lit E W3 ms3 r bs' (Z.to_nat (56 * 2 + 20)) 0 HREG HL288' ltac:(cbn; lia)); [exact Hpin20 | lia].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SLit 2); (0x50, SOff 48 0); (0x70, SOff 50 0); (0x20, SOff 49 0)]) [] 0 0 0 0 _ HB HJ HFR HBLK HE E20).
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | split; [exact (tl_afact E 49 lf 0 38 E49 ltac:(lia) ltac:(lia)) | exact I]]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))) by exact SH0.
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

  + 
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 2); ((19%bv : bv 5), SLit 2); ((23%bv : bv 5), SOff 20 (56 * 2)); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 2)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 [tl_regn [YP09.mkChunk (56 * 2 + 12) (CVal 4 (SOff 48 0))]] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_atom cx W3 ms3 E _ 26 (Boxreg.bx_n bs) 0); [rewrite Z.add_0_r; exact S48 | exact E26 | lia | lia].
    + exact SL50.
    + exact SL70.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
    apply Forall_cons; [|apply Forall_nil].
    change (56 * 2 + 12) with (Z.of_nat (Z.to_nat (56 * 2 + 12))).
    apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 2 + 12)) 48 nch HREG HL288' ltac:(cbn; lia)); [exact Hnch12 | lia | rewrite lx_sv_SOff0, E48; reflexivity].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 _ HB HJ HFR HBLK HE E20).
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | exact I]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))) by exact SH0.
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, U_lit, (U_atom E 26 (Boxreg.bx_n bs) E26) in Hc by lia;
  apply negb_false_iff, Z.eqb_eq in Hc; lia ].
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms0) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM2, HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

- (* known = idx: the row was held, so idx < n_before *)
  assert (Hzn : 2 < Boxreg.bx_n bs).
  { unfold reac_boxreg_find_c.find_result, reac_boxreg_find_c.first_mac in HFRES.
    destruct HFRES as [(_ & E1) | [(_ & (H1 & _)) | (_ & E1 & _)]]; lia. }
  assert (Hznb : 2 <> Boxreg.bx_n bs) by lia.
  
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 2); ((19%bv : bv 5), SLit 2); ((23%bv : bv 5), SOff 20 (56 * 2)); ((24%bv : bv 5), SLit 2); ((25%bv : bv 5), SLit 2)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 [] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_atom cx W3 ms3 E _ 26 (Boxreg.bx_n bs) 0); [rewrite Z.add_0_r; exact S48 | exact E26 | lia | lia].
    + exact SL50.
    + exact SL70.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat apply Forall_cons; try apply Forall_nil; exact I.
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | exact I]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, U_lit, (U_atom E 26 (Boxreg.bx_n bs) E26) in Hc by lia;
  apply negb_false_iff, Z.eqb_eq in Hc; lia ].
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms0) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM2, HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

Qed.

Lemma tl_w6_3 : TW6 3.
Proof.

intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs'
  HB HJ HFR HMO HCO HREG HFRES HADD R10 R19 R23 R24.
pose proof (lh_laws B MT HY) as LAWS.
pose proof HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & Hlf & HW & Hwant & Hw7 & Hw7b & R20 & R21 & R25 & R26 & R27).
pose proof HTM as (HPREV & HCUR & HSLL & S58 & S48 & HRD & HNZ & S20).
pose proof HRD as (HMAC & S50 & Hnch). pose proof HMAC as (HML & HMB).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof HJ as (HAR3 & _).
assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size LX_REG) with 288 in Hrceil, Hria.
pose proof (LC1.c1_inv_n bs HINV) as HnB. pose proof (LC1.c1_inv_fab bs HINV) as HfB.
pose proof (lxc1_add_keeps bs M nch _ bs' HINV HML HADD) as (HINV' & HFAB' & HKEPT).
pose proof (LC1.c1_inv_len bs' HINV') as HL288'.
destruct (LC1.c1_add_pos bs M nch 3 bs' HINV HML HADD ltac:(lia)) as (HMZ & Ao & Hfab' & Hn5 & Hh' & Hcase).
destruct (LC1.c1_add_want bs M nch lf want 3 bs' HINV HML HW HADD) as (Ewant & Hnew).
pose proof (LC1.c1_find_range bs M known HFRES HnB) as Hkr.
assert (Hkn : known = -1 \/ known = 3).
{ destruct (Z_lt_ge_dec known 0) as [Hk0|Hk0]; [left; lia|].
  right. symmetry. exact (LC1.c1_known bs M nch known 3 bs' HFRES ltac:(lia) Ao HADD). }
cbn in R10.
set (ex := [w64 nch; w64 lf; w64 (2 ^ 64 - 1 - r)]).
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (E48 : ew E 48 = w64 nch) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
assert (E49 : ew E 49 = w64 lf) by exact (lx_env_ex cx fp (ms_regs ms3) ex 1 ltac:(lia)).
assert (E50 : ew E 50 = w64 (2 ^ 64 - 1 - r)) by exact (lx_env_ex cx fp (ms_regs ms3) ex 2 ltac:(lia)).
assert (E20 : ew E 20 = w64 r) by (unfold E; erewrite lx_env_reg; [exact R20 | reflexivity]).
assert (E21 : ew E 21 = w64 (lF cx fp + 64)) by (unfold E; erewrite lx_env_reg; [exact R21 | reflexivity]).
assert (E26 : ew E 26 = w64 (Boxreg.bx_n bs)) by (unfold E; erewrite lx_env_reg; [exact R26 | reflexivity]).
assert (E27 : ew E 27 = w64 fab) by (unfold E; erewrite lx_env_reg; [exact R27 | reflexivity]).
unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F in E2, E8, E22, E32, E46.
assert (HAF0 : atoms_ok E LX_AF) by exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE).
assert (AF20 : afact_ok E 20 (mkAF 4096 140737479966720 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E20. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [change (2 ^ 4) with 16; exact Hr16 | lia]. }
assert (AF48 : afact_ok E 48 (mkAF 0 255 0)) by exact (tl_afact E 48 nch 0 255 E48 ltac:(lia) ltac:(lia)).
assert (AF50 : afact_ok E 50 (mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0))
  by exact (tl_afact E 50 (2 ^ 64 - 1 - r) (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) E50 ltac:(lia) ltac:(lia)).
assert (SL30 : rdword (lview W3 ms3) (lsp1 cx + 0x30) = Some (bv_unsigned (sv_denot E (SOff 27 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 27 fab 0); [rewrite Z.add_0_r; exact L30 | exact E27 | lia | lia]).
assert (SL50 : rdword (lview W3 ms3) (lsp1 cx + 0x50) = Some (bv_unsigned (sv_denot E (SOff 48 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 48 nch 0); [rewrite Z.add_0_r; exact S50 | exact E48 | lia | lia]).
assert (SL70 : rdword (lview W3 ms3) (lsp1 cx + 0x70) = Some (bv_unsigned (sv_denot E (SOff 50 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 50 (2 ^ 64 - 1 - r) 0); [rewrite Z.add_0_r; exact L70 | exact E50 | lia | lia]).
assert (SH0 : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
assert (OV23 : sv_denot E (SOff 20 (56 * 3)) = getr (ms_regs ms3) 23).
{ cbn [sv_denot]. rewrite E20, R23. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
pose (RUN := paj_run B LAWS). pose (RUNTO := paj_run_to B LAWS). pose (BR := paj_branch (PI := PI)).
destruct Hkn as [-> | ->].
- (* known = -1: the row is new or an unbound one bound now; it has the asked width *)
  assert (HN : reac_boxreg_add_c.add_none_held bs M) by exact (LC1.c1_find_none bs M (-1) HFRES ltac:(lia) HMZ).
  assert (Hnch12 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 3 + 12))) = nch).
  { change (Z.of_nat (Z.to_nat (56 * 3 + 12))) with (56 * 3 + 12). change (Boxreg.rd4 bs' (56 * 3 + 12)) with (Boxreg.bx_nch bs' 3).
    destruct Hcase as [(Hh & _) | (_ & Hk')]; [exfalso; destruct Hh as (Hi & Mi & _); exact (HN 3 Hi Mi) | exact Hk']. }
  destruct (Z.eq_dec 3 (Boxreg.bx_n bs)) as [Hznb | Hznb].
  + (* a new row: its base is lf, its pinned word 0 *)
    destruct (Hnew ltac:(lia)) as (Hb' & Hp'). rewrite <- Ewant in Hb', Hp'.
    assert (Hlf0 : 0 <= lf).
    { destruct HW as [(_ & W1) | [(_ & _ & (W2 & _)) | [(_ & _ & _ & (W3' & _)) | [(_ & _ & _ & _ & _ & W4) | (_ & _ & _ & _ & _ & _ & W5 & _)]]]]; lia. }
    assert (Hbase8 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 3 + 8))) = lf).
    { change (Z.of_nat (Z.to_nat (56 * 3 + 8))) with (56 * 3 + 8). change (Boxreg.rd4 bs' (56 * 3 + 8)) with (Boxreg.bx_base bs' 3).
      exact Hb'. }
    assert (Hpin20 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 3 + 20))) = 0).
    { change (Z.of_nat (Z.to_nat (56 * 3 + 20))) with (56 * 3 + 20). change (Boxreg.rd4 bs' (56 * 3 + 20)) with (Boxreg.bx_pinned bs' 3).
      exact Hp'. }
    
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 3); ((19%bv : bv 5), SLit 3); ((23%bv : bv 5), SOff 20 (56 * 3)); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 3); ((26%bv : bv 5), SLit 3)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SLit 3); (0x50, SOff 48 0); (0x70, SOff 50 0); (0x20, SOff 49 0)]) [] 0 0 0 0 [tl_regn [YP09.mkChunk (56 * 3 + 8) (CVal 4 (SOff 49 0)); YP09.mkChunk (56 * 3 + 12) (CVal 4 (SOff 48 0)); YP09.mkChunk (56 * 3 + 20) (CVal 4 (SLit 0))]] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0); (49%nat, mkAF 0 38 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
    + rewrite R26, <- Hznb. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_lit cx W3 ms3 E _ 3); [rewrite Hznb; exact S48 | lia].
    + exact SL50.
    + exact SL70.
    + apply (lx_slot_atom cx W3 ms3 E _ 49 lf 0); [rewrite Z.add_0_r, <- (Z.mod_small lf (2 ^ 64)) by lia; exact S20 | exact E49 | lia | lia].
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + change (56 * 3 + 8) with (Z.of_nat (Z.to_nat (56 * 3 + 8))).
      apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 3 + 8)) 49 lf HREG HL288' ltac:(cbn; lia)); [exact Hbase8 | lia | rewrite lx_sv_SOff0, E49; reflexivity].
    + change (56 * 3 + 12) with (Z.of_nat (Z.to_nat (56 * 3 + 12))).
      apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 3 + 12)) 48 nch HREG HL288' ltac:(cbn; lia)); [exact Hnch12 | lia | rewrite lx_sv_SOff0, E48; reflexivity].
    + change (56 * 3 + 20) with (Z.of_nat (Z.to_nat (56 * 3 + 20))).
      apply (tl_word_chunk_lit E W3 ms3 r bs' (Z.to_nat (56 * 3 + 20)) 0 HREG HL288' ltac:(cbn; lia)); [exact Hpin20 | lia].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SLit 3); (0x50, SOff 48 0); (0x70, SOff 50 0); (0x20, SOff 49 0)]) [] 0 0 0 0 _ HB HJ HFR HBLK HE E20).
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | split; [exact (tl_afact E 49 lf 0 38 E49 ltac:(lia) ltac:(lia)) | exact I]]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))) by exact SH0.
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

  + 
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 3); ((19%bv : bv 5), SLit 3); ((23%bv : bv 5), SOff 20 (56 * 3)); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 3)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 [tl_regn [YP09.mkChunk (56 * 3 + 12) (CVal 4 (SOff 48 0))]] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_atom cx W3 ms3 E _ 26 (Boxreg.bx_n bs) 0); [rewrite Z.add_0_r; exact S48 | exact E26 | lia | lia].
    + exact SL50.
    + exact SL70.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
    apply Forall_cons; [|apply Forall_nil].
    change (56 * 3 + 12) with (Z.of_nat (Z.to_nat (56 * 3 + 12))).
    apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 3 + 12)) 48 nch HREG HL288' ltac:(cbn; lia)); [exact Hnch12 | lia | rewrite lx_sv_SOff0, E48; reflexivity].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 _ HB HJ HFR HBLK HE E20).
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | exact I]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))) by exact SH0.
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, U_lit, (U_atom E 26 (Boxreg.bx_n bs) E26) in Hc by lia;
  apply negb_false_iff, Z.eqb_eq in Hc; lia ].
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms0) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM2, HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

- (* known = idx: the row was held, so idx < n_before *)
  assert (Hzn : 3 < Boxreg.bx_n bs).
  { unfold reac_boxreg_find_c.find_result, reac_boxreg_find_c.first_mac in HFRES.
    destruct HFRES as [(_ & E1) | [(_ & (H1 & _)) | (_ & E1 & _)]]; lia. }
  assert (Hznb : 3 <> Boxreg.bx_n bs) by lia.
  
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 3); ((19%bv : bv 5), SLit 3); ((23%bv : bv 5), SOff 20 (56 * 3)); ((24%bv : bv 5), SLit 3); ((25%bv : bv 5), SLit 3)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 [] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_atom cx W3 ms3 E _ 26 (Boxreg.bx_n bs) 0); [rewrite Z.add_0_r; exact S48 | exact E26 | lia | lia].
    + exact SL50.
    + exact SL70.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat apply Forall_cons; try apply Forall_nil; exact I.
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | exact I]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, U_lit, (U_atom E 26 (Boxreg.bx_n bs) E26) in Hc by lia;
  apply negb_false_iff, Z.eqb_eq in Hc; lia ].
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms0) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM2, HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

Qed.

Lemma tl_w6_4 : TW6 4.
Proof.

intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs'
  HB HJ HFR HMO HCO HREG HFRES HADD R10 R19 R23 R24.
pose proof (lh_laws B MT HY) as LAWS.
pose proof HCO as (HBODY & Hi64 & Hk & Hacc & HBLK & HINV & HFAB & HTM & Hlf & HW & Hwant & Hw7 & Hw7b & R20 & R21 & R25 & R26 & R27).
pose proof HTM as (HPREV & HCUR & HSLL & S58 & S48 & HRD & HNZ & S20).
pose proof HRD as (HMAC & S50 & Hnch). pose proof HMAC as (HML & HMB).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof HJ as (HAR3 & _).
assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size LX_REG) with 288 in Hrceil, Hria.
pose proof (LC1.c1_inv_n bs HINV) as HnB. pose proof (LC1.c1_inv_fab bs HINV) as HfB.
pose proof (lxc1_add_keeps bs M nch _ bs' HINV HML HADD) as (HINV' & HFAB' & HKEPT).
pose proof (LC1.c1_inv_len bs' HINV') as HL288'.
destruct (LC1.c1_add_pos bs M nch 4 bs' HINV HML HADD ltac:(lia)) as (HMZ & Ao & Hfab' & Hn5 & Hh' & Hcase).
destruct (LC1.c1_add_want bs M nch lf want 4 bs' HINV HML HW HADD) as (Ewant & Hnew).
pose proof (LC1.c1_find_range bs M known HFRES HnB) as Hkr.
assert (Hkn : known = -1 \/ known = 4).
{ destruct (Z_lt_ge_dec known 0) as [Hk0|Hk0]; [left; lia|].
  right. symmetry. exact (LC1.c1_known bs M nch known 4 bs' HFRES ltac:(lia) Ao HADD). }
cbn in R10.
set (ex := [w64 nch; w64 lf; w64 (2 ^ 64 - 1 - r)]).
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
assert (E48 : ew E 48 = w64 nch) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
assert (E49 : ew E 49 = w64 lf) by exact (lx_env_ex cx fp (ms_regs ms3) ex 1 ltac:(lia)).
assert (E50 : ew E 50 = w64 (2 ^ 64 - 1 - r)) by exact (lx_env_ex cx fp (ms_regs ms3) ex 2 ltac:(lia)).
assert (E20 : ew E 20 = w64 r) by (unfold E; erewrite lx_env_reg; [exact R20 | reflexivity]).
assert (E21 : ew E 21 = w64 (lF cx fp + 64)) by (unfold E; erewrite lx_env_reg; [exact R21 | reflexivity]).
assert (E26 : ew E 26 = w64 (Boxreg.bx_n bs)) by (unfold E; erewrite lx_env_reg; [exact R26 | reflexivity]).
assert (E27 : ew E 27 = w64 fab) by (unfold E; erewrite lx_env_reg; [exact R27 | reflexivity]).
unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F in E2, E8, E22, E32, E46.
assert (HAF0 : atoms_ok E LX_AF) by exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE).
assert (AF20 : afact_ok E 20 (mkAF 4096 140737479966720 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E20. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [change (2 ^ 4) with 16; exact Hr16 | lia]. }
assert (AF48 : afact_ok E 48 (mkAF 0 255 0)) by exact (tl_afact E 48 nch 0 255 E48 ltac:(lia) ltac:(lia)).
assert (AF50 : afact_ok E 50 (mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0))
  by exact (tl_afact E 50 (2 ^ 64 - 1 - r) (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) E50 ltac:(lia) ltac:(lia)).
assert (SL30 : rdword (lview W3 ms3) (lsp1 cx + 0x30) = Some (bv_unsigned (sv_denot E (SOff 27 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 27 fab 0); [rewrite Z.add_0_r; exact L30 | exact E27 | lia | lia]).
assert (SL50 : rdword (lview W3 ms3) (lsp1 cx + 0x50) = Some (bv_unsigned (sv_denot E (SOff 48 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 48 nch 0); [rewrite Z.add_0_r; exact S50 | exact E48 | lia | lia]).
assert (SL70 : rdword (lview W3 ms3) (lsp1 cx + 0x70) = Some (bv_unsigned (sv_denot E (SOff 50 0))))
  by (apply (lx_slot_atom cx W3 ms3 E _ 50 (2 ^ 64 - 1 - r) 0); [rewrite Z.add_0_r; exact L70 | exact E50 | lia | lia]).
assert (SH0 : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))).
{ apply Forall_cons; [|apply Forall_nil].
  apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR3 Hrin).
  - apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 20 r E20). lia.
  - lia.
  - lia.
  - change (req_size LX_REG) with 288. lia. }
assert (OV23 : sv_denot E (SOff 20 (56 * 4)) = getr (ms_regs ms3) 23).
{ cbn [sv_denot]. rewrite E20, R23. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
pose (RUN := paj_run B LAWS). pose (RUNTO := paj_run_to B LAWS). pose (BR := paj_branch (PI := PI)).
destruct Hkn as [-> | ->].
- (* known = -1: the row is new or an unbound one bound now; it has the asked width *)
  assert (HN : reac_boxreg_add_c.add_none_held bs M) by exact (LC1.c1_find_none bs M (-1) HFRES ltac:(lia) HMZ).
  assert (Hnch12 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 4 + 12))) = nch).
  { change (Z.of_nat (Z.to_nat (56 * 4 + 12))) with (56 * 4 + 12). change (Boxreg.rd4 bs' (56 * 4 + 12)) with (Boxreg.bx_nch bs' 4).
    destruct Hcase as [(Hh & _) | (_ & Hk')]; [exfalso; destruct Hh as (Hi & Mi & _); exact (HN 4 Hi Mi) | exact Hk']. }
  destruct (Z.eq_dec 4 (Boxreg.bx_n bs)) as [Hznb | Hznb].
  + (* a new row: its base is lf, its pinned word 0 *)
    destruct (Hnew ltac:(lia)) as (Hb' & Hp'). rewrite <- Ewant in Hb', Hp'.
    assert (Hlf0 : 0 <= lf).
    { destruct HW as [(_ & W1) | [(_ & _ & (W2 & _)) | [(_ & _ & _ & (W3' & _)) | [(_ & _ & _ & _ & _ & W4) | (_ & _ & _ & _ & _ & _ & W5 & _)]]]]; lia. }
    assert (Hbase8 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 4 + 8))) = lf).
    { change (Z.of_nat (Z.to_nat (56 * 4 + 8))) with (56 * 4 + 8). change (Boxreg.rd4 bs' (56 * 4 + 8)) with (Boxreg.bx_base bs' 4).
      exact Hb'. }
    assert (Hpin20 : Boxreg.rd4 bs' (Z.of_nat (Z.to_nat (56 * 4 + 20))) = 0).
    { change (Z.of_nat (Z.to_nat (56 * 4 + 20))) with (56 * 4 + 20). change (Boxreg.rd4 bs' (56 * 4 + 20)) with (Boxreg.bx_pinned bs' 4).
      exact Hp'. }
    
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 4); ((19%bv : bv 5), SLit 4); ((23%bv : bv 5), SOff 20 (56 * 4)); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 4); ((26%bv : bv 5), SLit 4)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SLit 4); (0x50, SOff 48 0); (0x70, SOff 50 0); (0x20, SOff 49 0)]) [] 0 0 0 0 [tl_regn [YP09.mkChunk (56 * 4 + 8) (CVal 4 (SOff 49 0)); YP09.mkChunk (56 * 4 + 12) (CVal 4 (SOff 48 0)); YP09.mkChunk (56 * 4 + 20) (CVal 4 (SLit 0))]] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0); (49%nat, mkAF 0 38 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
    + rewrite R26, <- Hznb. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_lit cx W3 ms3 E _ 4); [rewrite Hznb; exact S48 | lia].
    + exact SL50.
    + exact SL70.
    + apply (lx_slot_atom cx W3 ms3 E _ 49 lf 0); [rewrite Z.add_0_r, <- (Z.mod_small lf (2 ^ 64)) by lia; exact S20 | exact E49 | lia | lia].
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + change (56 * 4 + 8) with (Z.of_nat (Z.to_nat (56 * 4 + 8))).
      apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 4 + 8)) 49 lf HREG HL288' ltac:(cbn; lia)); [exact Hbase8 | lia | rewrite lx_sv_SOff0, E49; reflexivity].
    + change (56 * 4 + 12) with (Z.of_nat (Z.to_nat (56 * 4 + 12))).
      apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 4 + 12)) 48 nch HREG HL288' ltac:(cbn; lia)); [exact Hnch12 | lia | rewrite lx_sv_SOff0, E48; reflexivity].
    + change (56 * 4 + 20) with (Z.of_nat (Z.to_nat (56 * 4 + 20))).
      apply (tl_word_chunk_lit E W3 ms3 r bs' (Z.to_nat (56 * 4 + 20)) 0 HREG HL288' ltac:(cbn; lia)); [exact Hpin20 | lia].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SLit 4); (0x50, SOff 48 0); (0x70, SOff 50 0); (0x20, SOff 49 0)]) [] 0 0 0 0 _ HB HJ HFR HBLK HE E20).
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | split; [exact (tl_afact E 49 lf 0 38 E49 ltac:(lia) ltac:(lia)) | exact I]]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))) by exact SH0.
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

  + 
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 4); ((19%bv : bv 5), SLit 4); ((23%bv : bv 5), SOff 20 (56 * 4)); ((24%bv : bv 5), SLit 18446744073709551615); ((25%bv : bv 5), SLit 4)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 [tl_regn [YP09.mkChunk (56 * 4 + 12) (CVal 4 (SOff 48 0))]] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_atom cx W3 ms3 E _ 26 (Boxreg.bx_n bs) 0); [rewrite Z.add_0_r; exact S48 | exact E26 | lia | lia].
    + exact SL50.
    + exact SL70.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (tl_regn_ok E _ r); [exact E20 | lia | lia|].
    apply Forall_cons; [|apply Forall_nil].
    change (56 * 4 + 12) with (Z.of_nat (Z.to_nat (56 * 4 + 12))).
    apply (tl_word_chunk E W3 ms3 r bs' (Z.to_nat (56 * 4 + 12)) 48 nch HREG HL288' ltac:(cbn; lia)); [exact Hnch12 | lia | rewrite lx_sv_SOff0, E48; reflexivity].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - exact (tl_regn_disj cx fp k ly3 S3 W3 ms3 md3 r E LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 _ HB HJ HFR HBLK HE E20).
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | exact I]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [mkSHE 20 0 288] E (mrestrict (w_H W3) (ms_mem ms3))) by exact SH0.
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, U_lit, (U_atom E 26 (Boxreg.bx_n bs) E26) in Hc by lia;
  apply negb_false_iff, Z.eqb_eq in Hc; lia ].
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms0) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM2, HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

- (* known = idx: the row was held, so idx < n_before *)
  assert (Hzn : 4 < Boxreg.bx_n bs).
  { unfold reac_boxreg_find_c.find_result, reac_boxreg_find_c.first_mac in HFRES.
    destruct HFRES as [(_ & E1) | [(_ & (H1 & _)) | (_ & E1 & _)]]; lia. }
  assert (Hznb : 4 <> Boxreg.bx_n bs) by lia.
  
assert (HS : st_ok_pi SEGS VAL E
  (lx_ss 0xab8 (lx_sr (LX_OV ++ [((10%bv : bv 5), SLit 4); ((19%bv : bv 5), SLit 4); ((23%bv : bv 5), SOff 20 (56 * 4)); ((24%bv : bv 5), SLit 4); ((25%bv : bv 5), SLit 4)])) LSH_iter (lx_slot_chunks [(0x30, SOff 27 0); (0x48, SOff 26 0); (0x50, SOff 48 0); (0x70, SOff 50 0)]) [] 0 0 0 0 [] (mkFacts (LX_AF ++ [(20%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 255 0); (50%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0)]) [] []))
  (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms|].
    apply Forall_app. split; [apply (lx_ov_ok cx fp ms3 ex); exact HREGS|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot].
    + rewrite R10. reflexivity.
    + rewrite R19. reflexivity.
    + exact OV23.
    + rewrite R24. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + rewrite R25, <- Ewant. reflexivity.
  - unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact SL30.
    + apply (lx_slot_atom cx W3 ms3 E _ 26 (Boxreg.bx_n bs) 0); [rewrite Z.add_0_r; exact S48 | exact E26 | lia | lia].
    + exact SL50.
    + exact SL70.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat apply Forall_cons; try apply Forall_nil; exact I.
  - split; [|split; exact I]. apply tl_atoms_ok_app; [exact HAF0|]. cbn [atoms_ok]. split; [exact AF20 | split; [exact AF48 | split; [exact AF50 | exact I]]]. }
tl_unwin_tac HS 1%nat. tl_unwin_tac HS 2%nat.
assert (SHOK : sh_ok SEGS TL_CB [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK TL_BSPAN; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TL_BSPAN;
[ clear Hc
| exfalso; rewrite tl_bne, U_lit, (U_atom E 26 (Boxreg.bx_n bs) E26) in Hc by lia;
  apply negb_false_iff, Z.eqb_eq in Hc; lia ].
paj_run_to_tok RUNTO HS HJ SHOK TL_BSPAN LP_K; [apply tl_awr_ro; vm_compute; reflexivity |].
lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
  pose proof (frame_of_read_only _ rs m m' ltac:(vm_compute; reflexivity) HF) as HM2 end.
clear HF HFr HG.
assert (HMM : mrestrict (w_H W3) (ms_mem ms0) = mrestrict (w_H W3) (ms_mem ms3)) by (rewrite HM2, HM1; reflexivity).
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
eapply (tl_land_K POST i cx fp 0xab8 k acc ly3 S3 W3 ms3 _ _ E _ q r fab bs M nch nz lf want w7 bs'
  HNEXT HB HJ HFR HMO HCO HREG HINV' ltac:(rewrite HFAB', HFAB; reflexivity) HKEPT HMM HE HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite Q20; exact E20 | rewrite Q21; exact E21
  | rewrite Q24; apply bv_eq; vm_compute; reflexivity | rewrite Q27; exact E27 ].

Qed.


Lemma tl_w6 : forall POST i, lx_from B MT POST (LI_K B MT i) -> lx_from B MT POST (TKP 0xab8 true i).
Proof.
  intros POST i HK cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
  destruct HGI as (q & r & fab & bs & M & nch & nz & lf & want & w7 & known & idx & bs' & HCO & HREG & HFRES & HADD & Hidx & R10 & R19 & R23 & R24).
  pose proof HCO as (_ & _ & _ & _ & _ & HINV & _).
  pose proof (LC1.c1_add_range bs M nch idx bs' HINV HADD) as Hr.
  cbn in R10.
  assert (Hc : idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3 \/ idx = 4) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | ->]]]].
  - exact (tl_w6_0 POST i HK cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs' HB HJ HFR HMO HCO HREG HFRES HADD R10 R19 R23 R24).
  - exact (tl_w6_1 POST i HK cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs' HB HJ HFR HMO HCO HREG HFRES HADD R10 R19 R23 R24).
  - exact (tl_w6_2 POST i HK cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs' HB HJ HFR HMO HCO HREG HFRES HADD R10 R19 R23 R24).
  - exact (tl_w6_3 POST i HK cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs' HB HJ HFR HMO HCO HREG HFRES HADD R10 R19 R23 R24).
  - exact (tl_w6_4 POST i HK cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz lf want w7 known bs' HB HJ HFR HMO HCO HREG HFRES HADD R10 R19 R23 R24).
Qed.


End d.

(* ---- the segment: C1_I7 at 0x809a8 .. LI_K at 0x80b08 ---- *)
Theorem c1_seg_tail : C1_SEG_tail B MT.
Proof.
  intros HY POST i HK.
  apply (tl_w1 HY POST i). apply (tl_w2 HY POST i). apply (tl_w3 HY POST i HK).
  apply (tl_w4 HY POST i). apply (tl_w5 HY POST i). exact (tl_w6 HY POST i HK).
Qed.

End c.
End b.
End a.
