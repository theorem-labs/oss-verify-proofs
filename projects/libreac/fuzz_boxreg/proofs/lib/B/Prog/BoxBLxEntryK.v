(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 909 of its 980 lines of code are new or changed and 860 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase0TN.v, with its module names changed; 184 of its 232 lines of code are new or changed and 932 lines of the source are left out. *)
(* Cut K of the entry phase of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput (fuzz_boxreg.asan-ubsan 0x7ffac):
   from check's return (0x80214, ss_K of BoxBLxEntryDefs.v) to the loop head 0x80258 (BoxBLxDefs.v LP_J = 0x2ac) of
   turn 0, where LI_J B MT 0 holds; the lx_from of le_cut closes it (le_K : le_K_stmt B MT).

   The code 0x80214 .. 0x80254 is straight-line (no branch, no call, no shadow check):
     0x80214 mv s8, zero            0x80218 andi a0, s4, 3        0x8021c sd a0, 0x38(s1)
     0x80220 addi a1, s4, 0x118     0x80224 not a0, s4            0x80228 sd a0, 0x70(s1)
     0x8022c not a0, s5             0x80230 sd a0, 0x78(s1)       0x80234 addi s3, zero, 1
     0x80238 srli a0, a1, 3         0x8023c sd a1, 0x28(s1)       0x80240 andi a1, a1, 7
     0x80244 add a0, a0, s2         0x80248 sd a0, 0x40(s1)       0x8024c addi a1, a1, 3
     0x80250 sd a1, 8(s1)           0x80254 sd s11, 0x30(s1)
   0x80258 (LP_J) is `ld a1, 0x90(s1)`, then `beqz a1` at 0x8025c, so the run stops at LP_J by paj_run_to_tok. The
   engine folds r & 3 and ((r + 280) & 7) + 3 to 0 and 3 by atom 84's alignment fact (16) in ss_K's facts. The
   landing reads the registers and the slots from the final symbolic state (BoxBLxSeat.v lx_land, lx_slot_of_ss and
   friends), the registry block through the run's frame_of (the run writes only spill slots), and the input bytes
   from lx_base through the journal. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase YC4b BoxRo PaStep.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBCheck.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxEntryDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregInit reac_boxreg_init_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


Ltac lk_norm HS :=
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
Ltac lk_in := cbn [In]; repeat first [left; reflexivity | right].

(* ---- values of the symbolic expressions the run leaves in the slots ---- *)
Lemma lk_denot_U : forall E e v, U E e = v -> sv_denot E e = w64 v.
Proof. intros E e v H. unfold w64. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma lk_U_off : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> U E (SOff n c) = v + c.
Proof.
  intros E n v c H Hv Hc. rewrite U_SOff, H. unfold w64. rewrite unsigned_lit_small by lia.
  apply zcanon_id. unfold M64. lia.
Qed.

Lemma lk_hi : forall x i, 0 <= x < 2 ^ 64 -> 64 <= i -> Z.testbit x i = false.
Proof. intros x i Hx Hi. rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. Qed.

Lemma lk_lxor : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
  intros x Hx. change (2 ^ 64 - 1) with (Z.ones 64).
  assert (L : Z.ldiff x (Z.ones 64) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 64).
    - rewrite Z.ones_spec_low by lia. cbn [negb]. apply andb_false_r.
    - rewrite (lk_hi x i Hx) by lia. reflexivity. }
  rewrite (Z.sub_nocarry_ldiff (Z.ones 64) x L).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.ldiff_spec.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x i); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite (lk_hi x i Hx) by lia. reflexivity.
Qed.

Lemma lk_U_not : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SOff n c) (SLit (-1))) = 2 ^ 64 - 1 - (v + c).
Proof.
  intros E n v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw]. rewrite (lk_U_off E n v c Hn Hv Hc), U_SLit.
  change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lk_lxor by exact Hc. apply zcanon_id. unfold M64. lia.
Qed.

(* Slot 0x40: the shadow address of r + 280 (r->n). *)
Lemma lk_U_sh : forall E r, ew E 84 = w64 r -> ew E 32 = w64 SHADOW_OFF -> 0 <= r -> r + 288 <= 2 ^ 47 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 84 280) (SLit 3)) (SOff 32 0)) = shadow_addr (r + 280).
Proof.
  intros E r H84 H32 Hr0 Hr1.
  rewrite U_SAlu, U_SAlu, U_SOff, U_SOff, U_lit by lia. rewrite H84, H32. unfold w64.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia). cbn [zalu_raw].
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (Hd : 0 <= (r + 280) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  rewrite Z.add_0_r. rewrite (zcanon_id (r + 280)) by (unfold M64; lia).
  rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
  rewrite (zcanon_id ((r + 280) / 8)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). unfold shadow_addr. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.

(* ---- the memory the run keeps ---- *)
Lemma lk_frame_byte : forall E rs H (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof. intros E rs H m m' a HF Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hn. Qed.

(* ss_K writes only the spill slots (region 1) and the frame (region 2). *)
Lemma lk_nowr : forall cx fp E a,
  YP09.base_val E (Some LA_SP) = lsp1 cx -> YP09.base_val E (Some LA_F) = lF cx fp ->
  (a < lsp1 cx \/ lsp1 cx + 152 <= a) -> (a < lF cx fp \/ lF cx fp + 512 <= a) ->
  ~ in_wrange E (ss_mem ss_K) a.
Proof.
  intros cx fp E a U2 U46 Hs Hf (rg & Hin & Ha). unfold LA_SP, LA_F in U2, U46.
  change (ss_mem ss_K) with [lx_saved_region; le_spill_D; le_frame_C; le_shadow_C] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi lx_saved_region le_spill_D le_frame_C le_shadow_C] in Ha; [lia | | | lia].
  - rewrite U2 in Ha. lia.
  - rewrite U46 in Ha. lia.
Qed.

(* A byte of a block of the entry state, at a later state of the journal (BoxBLxEntry.v le_val_mem_kept). *)
Lemma lk_val_mem_kept : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k p n i v,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
  val_mem SEGS (mrestrict (w_H W) mem) (p + i) 1 v -> val_mem SEGS (mrestrict (w_H W') mem') (p + i) 1 v.
Proof.
  intros STK sp0 ly S W mem md own ly' S' W' mem' md' k p n i v HJ H1 H2 Hi Hv.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  apply (val_mem_moved SEGS (w_H W) (w_H W') mem mem' (p + i) (p + i) 1 v); [|exact Hv].
  intros q Hq. replace (p + i + q) with (p + (i + q)) by lia.
  apply (F2 p n (i + q) H1 H2); [lia | apply inFP_nil].
Qed.

(* The caller's input bytes at any state of the call's journal that keeps the caller's blocks. *)
Lemma lk_input : forall cx fp ly S (W : world SEGS) mem md k,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)]
    ly S W mem md k ->
  (forall p n, In (p, n) (ablocks B (lc_ly cx) (lc_S cx)) -> In (p, n) (ablocks B ly S)) ->
  garr8 SEGS (mrestrict (w_H W) mem) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)).
Proof.
  intros cx fp ly S W mem md k HB HJ Hbl j Hj.
  pose proof HB as (_ & _ & _ & Hn & Hgarr & _).
  destruct (Hgarr j Hj) as [Hv Hr]. split; [|exact Hr].
  rewrite length_map in Hj.
  destruct Hn as [[Hn0 _] | ((Hnpos & Hn26) & Hin)]; [exfalso; unfold lc_n in *; lia|].
  assert (Hrqn : req_size (lc_n cx) = lc_n cx) by (unfold req_size; destruct (Z.eqb_spec (lc_n cx) 0); lia).
  eapply lk_val_mem_kept; [exact HJ | exact Hin | exact (Hbl _ _ Hin) | | exact Hv].
  rewrite Hrqn. unfold lc_n. lia.
Qed.

(* The input cursor's two words are in range (lx_base: the input block, or the bound of the empty input's pointer). *)
Lemma lk_cur_range : forall cx ly S (W : world SEGS) mem md (pos : nat),
  lx_base B MT cx -> AR SEGS B ly S W mem md ->
  (forall p n, In (p, n) (ablocks B (lc_ly cx) (lc_S cx)) -> In (p, n) (ablocks B ly S)) ->
  (pos <= length (lc_pl cx))%nat ->
  0 <= lc_p cx + Z.of_nat pos < 2 ^ 64 /\ 0 <= lc_n cx - Z.of_nat pos < 2 ^ 64.
Proof.
  intros cx ly S W mem md pos HB HAR Hbl Hpos.
  pose proof (lh_laws B MT HY) as LAWS. pose proof asan_consts as (C1 & _).
  pose proof HB as (_ & _ & _ & Hn & _).
  destruct Hn as [[Hn0 Hp0] | ((Hnpos & Hn26) & Hin)]; [unfold lc_n in *; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (Hbl _ _ Hin)) as (_ & Hp4096 & Hpceil & _).
  assert (Hrqn : req_size (lc_n cx) = lc_n cx) by (unfold req_size; destruct (Z.eqb_spec (lc_n cx) 0); lia).
  rewrite Hrqn in Hpceil. unfold lc_n in *. lia.
Qed.

(* K: from check's return (0x80214) to the loop head of turn 0. *)
Theorem le_K : le_K_stmt B MT.
Proof.
  intros POST cx fp E W ms md ly S r b fab pos HC HS.
  destruct HC as (HFROM & HB & HEI & HE & E84 & E96 & Hb & E99 & Hfab & E97 & E98 & Hpos & HJ & HFR & Hmle & Hbl & Hreg).
  pose proof (le_sp_facts B MT cx HB) as (Hal16 & Hsp0lo & Hsp0hi & Hsp1 & Hal32).
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  pose proof (lx_F_facts B MT LAWS cx fp W ms ly S md 1 HB HJ HFR) as (HF0 & HFc & HFia & HFo & HF64 & HSHeq).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W ms ly S md 1 HB HJ) as Hfa.
  pose proof (lx_extents B MT LAWS cx fp W ms ly S md 1 HB HJ HFR E HE) as (U8 & U2 & U46 & U22).
  pose proof HE as (EW2 & EW8 & EW3 & EW4 & EW22 & EW32 & EWSV & EW46 & EW47).
  unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F, LA_FL in EW2, EW8, EW22, EW32, EW46, EW47.
  pose proof HJ as (HAR & _).
  assert (Hrin : In (r, LX_REG) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR Hrin) as (Hr16 & Hr4096 & Hrceil & _).
  change (req_size LX_REG) with 288 in Hrceil.
  assert (HdrF : r + 288 <= lF cx fp \/ lF cx fp + 512 <= r).
  { pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ r LX_REG LX_CID fp HAR Hrin ltac:(rewrite HFR; left; reflexivity))
      as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hfa in Hd. change (req_size LX_REG) with 288 in Hd.
    change (fs_frame_bytes LX_CID) with 512 in Hd. lia. }
  assert (Hbl0 : forall p n, In (p, n) (ablocks B (lc_ly cx) (lc_S cx)) -> In (p, n) (ablocks B ly S))
    by (intros p n Hq; rewrite Hbl; apply in_or_app; left; exact Hq).
  destruct (lk_cur_range cx ly S W (ms_mem ms) md pos HB HAR Hbl0 Hpos) as (Hp64 & Hn64).
  pose proof (BoxregInit.clamp40_range (le_sx b)) as Hfab40. rewrite <- Hfab in Hfab40.
  assert (UB32 : U E (SOff LA_SB 0) = SHADOW_OFF) by (apply U_atom; [exact EW32 | unfold SHADOW_OFF; lia]).
  assert (UB46 : U E (SOff LA_F 0) = lF cx fp) by (apply U_atom; [exact EW46 | lia]).
  assert (SHOK : sh_ok SEGS CBR [mkSHE LA_F 512 0] E (mrestrict (w_H W) (ms_mem ms))).
  { unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
    exact (lx_shent_rev E _ (lF cx fp) 512 LA_F UB32 UB46 HFia ltac:(lia)). }
  pose proof (paj_run_to B LAWS) as RUNTO.
  lk_norm HS.
  (* 0x80214 .. 0x80254: the loop's set-up; the run stops at 0x80258 *)
  paj_run_to_tok RUNTO HS HJ SHOK BspanR LP_J.
  { cbn [ss_mem].
    apply (le_awr B MT cx fp E); [exact HB | exact U2 | exact U46 | exact U22 | exact Hfa | lia | lia | apply awr_ok_nil]. }
  prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21.
  prreg HS (24%bv : bv 5) R24. prreg HS (27%bv : bv 5) R27.
  (* 0x80258: LI_J of turn 0 *)
  apply (HFROM cx fp 1 (LX_A1 MT) ly S W ms0 _ HB HJ HFR Hmle).
  exists pos, r, fab, (reac_boxreg_init_c.init_bytes fab).
  split.
  { eapply (lx_land cx fp W ms0 E LP_J); [exact HE | exact HS | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | | | | | | ].
    - exact (lx_saved_of_ss B MT cx fp W ms0 HB E _ HE HS eq_refl).
    - eapply (lx_shadow_of_ss B MT LAWS cx fp W ms0 ly S _ 1 HB HJ HFR E);
        [exact HE | exact HS | reflexivity | vm_compute; reflexivity].
    - eapply (lx_flag_of_ss B MT LAWS cx fp W ms0 ly S _ 1 HB HJ HFR E); [exact HE | exact HS | reflexivity | lk_in].
    - eapply (lx_slot_of_ss B MT cx fp W ms0 HB E); [exact HE | exact HS | reflexivity | lk_in
        | apply lk_denot_U; rewrite (lk_U_off E 46 (lF cx fp) 0 EW46) by lia; lia | lia].
    - eapply (lx_slot_of_ss B MT cx fp W ms0 HB E); [exact HE | exact HS | reflexivity | lk_in
        | apply lk_denot_U; rewrite (lk_U_off E 46 (lF cx fp) 0 EW46) by lia; lia | lia].
    - eapply (lx_slot_of_ss B MT cx fp W ms0 HB E); [exact HE | exact HS | reflexivity | lk_in
        | apply lk_denot_U; rewrite (lk_U_off E 46 (lF cx fp) 0 EW46) by lia; lia | lia].
    - exact (lk_input cx fp ly S W (ms_mem ms0) _ 1 HB HJ Hbl0). }
  split; [lia|]. split; [cbn [Z.of_nat]; lia|]. split; [cbn [Z.of_nat]; lia|].
  split; [exact Hbl|].
  split.
  { intros i Hi. unfold LX_REG in Hi. unfold lview.
    rewrite (lk_frame_byte E _ (w_H W) (ms_mem ms) (ms_mem ms0) (r + i) HFr);
      [exact (Hreg i ltac:(unfold LX_REG; lia)) | lia | apply (lk_nowr cx fp E); [exact U2 | exact U46 | lia | lia]]. }
  split; [rewrite Hfab; exact (proj1 (BoxregInit.init_bytes_inv (le_sx b)))|].
  split; [rewrite Hfab; exact (proj2 (proj2 (BoxregInit.init_bytes_inv (le_sx b))))|].
  split.
  { split; [exact Hpos|]. split.
    - eapply (lx_slot_of_ss B MT cx fp W ms0 HB E); [exact HE | exact HS | reflexivity | lk_in
        | apply lk_denot_U; rewrite (lk_U_off E 97 _ 0 E97) by lia; lia | lia].
    - eapply (lx_slot_of_ss B MT cx fp W ms0 HB E); [exact HE | exact HS | reflexivity | lk_in
        | apply lk_denot_U; rewrite (lk_U_off E 98 _ 0 E98) by lia; lia | lia]. }
  split.
  { assert (Hsh0 : 0 <= (r + 280) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    unfold lslots_loop.
    split; [eapply (lx_slot_of_ss B MT cx fp W ms0 HB E); [exact HE | exact HS | reflexivity | lk_in
        | apply lk_denot_U; rewrite U_lit by lia; reflexivity | lia]|].
    split; [eapply (lx_slot_of_ss B MT cx fp W ms0 HB E); [exact HE | exact HS | reflexivity | lk_in
        | apply lk_denot_U; rewrite (lk_U_off E 84 r 280 E84) by lia; reflexivity | lia]|].
    split; [eapply (lx_slot_of_ss B MT cx fp W ms0 HB E); [exact HE | exact HS | reflexivity | lk_in
        | apply lk_denot_U; rewrite (lk_U_off E 99 fab 0 E99) by lia; lia | lia]|].
    split; [eapply (lx_slot_of_ss B MT cx fp W ms0 HB E); [exact HE | exact HS | reflexivity | lk_in
        | apply lk_denot_U; rewrite U_lit by lia; reflexivity | lia]|].
    split; [eapply (lx_slot_of_ss B MT cx fp W ms0 HB E); [exact HE | exact HS | reflexivity | lk_in
        | apply lk_denot_U; exact (lk_U_sh E r E84 EW32 ltac:(lia) ltac:(lia)) | unfold shadow_addr, SHADOW_OFF; lia]|].
    split; [eapply (lx_slot_of_ss B MT cx fp W ms0 HB E); [exact HE | exact HS | reflexivity | lk_in
        | apply lk_denot_U; rewrite (lk_U_off E 46 (lF cx fp) 32 EW46) by lia; reflexivity | lia]|].
    split; [eapply (lx_slot_of_ss B MT cx fp W ms0 HB E); [exact HE | exact HS | reflexivity | lk_in
        | apply lk_denot_U; rewrite (lk_U_not E 84 r 0 E84) by lia; lia | lia]|].
    eapply (lx_slot_of_ss B MT cx fp W ms0 HB E); [exact HE | exact HS | reflexivity | lk_in
      | apply lk_denot_U; rewrite (lk_U_not E 46 (lF cx fp) 64 EW46) by lia; reflexivity | lia]. }
  split; [exact R19|].
  split; [rewrite R20; exact E84|].
  split; [rewrite R21, EW46; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split; [rewrite R24; reflexivity|].
  rewrite R27. exact E99.
Qed.

End a.
