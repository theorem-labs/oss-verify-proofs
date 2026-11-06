(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS4), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySweepS4.v. *)
(* Segment 4 of the sweep phase of fuzz_grant's entry function on IMAGE B:
   0x8173c .. 0x81804 (listing 0xd00 .. 0xdc8), the group-B loop, six turns, proved by
   induction on the turns left, 6 - i. One turn: the five shadow stores 0x8173c .. 0x81750
   mark `poll` (34 bytes at frame offset 464) usable, the last granule partially (2);
   reac_ctrl_identity_poll_block(i, poll) at 0x8175c fills it with GBz i; three bcmp calls
   compare it with row 5 + i of the sweep (0x81780, 34 bytes), bytes 16..19 of the row with
   the literal 12 11 05 00 the turn writes at frame offset 544 (0x817b8, 4 bytes) and bytes
   20..22 with POLL[i] (object 6; 0x817d4, 3 bytes); the five shadow bytes go back to 0xf8
   (0x817dc .. 0x817ec) and s2, s8, s9 step. Refuted here: the four branches into the abort
   block 0x81d98 (0x81760, 0x81784, 0x817bc, 0x817d8) and the three UBSan guards into the
   trap 0x81f48 (0x8176c, 0x8178c, 0x817c4). The ground this walk stands on is
   LLVMFEntrySweepS1c.v and LLVMFEntrySeat.v.

   Adapted from lib/A/Prog/GrantEntrySweepS4.v (a working branch afd75724b5b, blob e60961568,
   1767 lines), which carries no licence header of its own.
   Image B counts the turns up with s8 = 34 i against 204
   where image A counts s5 down to 0, holds the shadow base in s3 and the row bases in s4,
   s6 and s7, reads the addresses of `poll` and of the literal from spill slots 80 and 56,
   guards the row address with three UBSan overflow checks against the one's complement of
   the sweep in slot 88, and takes the callee in the caller-journal form of
   GrantBContracts.tb_reac_ctrl_identity_poll_block_spec, whose premises are discharged
   here. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib GrantRo GrantBContracts
LLVMFEntryDefs LLVMFEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC1i YC45 YC85 GrantFrame GrantACja GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* Image A's text was written with this flag false; `Local` keeps the setting here. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySweepS1c.

(* The atoms of the turn's three regions are below every atom a call havocs. *)
Ltac gb_ewold := repeat (rewrite ew_havoc_old by (cbv; lia)); reflexivity.
(* An atom of the turn's environment, read through the havocs of the calls before it. *)
Ltac gb_atom F := repeat (rewrite ew_havoc_old by (cbv; lia)); exact F.

(* ---- why the three comparisons of a turn find equal bytes ---- *)
(* The compound literal 12 11 05 00 of fuzz_grant.c:355, which the turn writes into the
   frame at F + 544 (0x8179c .. 0x817b0) before it compares. *)
Definition gb_LITz : list Z := [18; 17; 5; 0].

Lemma gb_gbz_len : forall i, length (GBz i) = 34%nat.
Proof. intros i. unfold GBz, gb_tail. destruct (i =? 0), (i =? 1), (i =? 2), (i =? 3), (i =? 4); reflexivity. Qed.

Lemma gb_gbz_range : forall i, 0 <= i <= 5 -> forall j, (j < 34)%nat -> 0 <= nth j (GBz i) 0 < 256.
Proof.
  intros i Hi j Hj.
  assert (Hb : forallb (fun z => (0 <=? z) && (z <? 256))%bool (GBz i) = true).
  { assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
    destruct C as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity. }
  rewrite forallb_forall in Hb.
  assert (Hin : In (nth j (GBz i) 0) (GBz i)) by (apply nth_In; rewrite gb_gbz_len; exact Hj).
  specialize (Hb _ Hin). apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma gb_poll_bytes : forall i j, (i <= 5)%nat -> (j < 3)%nat ->
  nth (3 * i + j) POLLz 0 = nth (20 + j) (GBz (Z.of_nat i)) 0.
Proof.
  intros i j Hi Hj.
  do 6 (destruct i as [|i]; [do 3 (destruct j as [|j]; [vm_compute; reflexivity|]); lia|]). lia.
Qed.

Lemma gb_lit_bytes : forall i j, (i <= 5)%nat -> (j < 4)%nat ->
  nth (16 + j) (GBz (Z.of_nat i)) 0 = nth j gb_LITz 0.
Proof.
  intros i j Hi Hj.
  do 6 (destruct i as [|i]; [do 4 (destruct j as [|j]; [vm_compute; reflexivity|]); lia|]). lia.
Qed.

Lemma gb_nth_concat34 : forall (L : list (list byte)) k j d,
  Forall (fun r => length r = 34%nat) L -> (k < length L)%nat -> (j < 34)%nat ->
  nth (34 * k + j) (concat L) d = nth j (nth k L []) d.
Proof.
  induction L as [|r L IH]; intros k j d HL Hk Hj; cbn [length] in Hk; [lia|].
  inversion HL as [|r0 L0 Hr HL']; subst r0 L0. cbn [concat].
  destruct k as [|k].
  - cbn [nth]. rewrite app_nth1 by lia. f_equal; lia.
  - rewrite app_nth2 by lia. rewrite Hr. replace (34 * S k + j - 34)%nat with (34 * k + j)%nat by lia.
    cbn [nth]. apply IH; [exact HL' | lia | exact Hj].
Qed.

Lemma gb_nth_unsigned : forall (l : list byte) n,
  nth n (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
  induction l as [|b l IH]; intros n; destruct n as [|n]; cbn [map nth]; try reflexivity. apply IH.
Qed.

(* Row 5 + i of the sweep is the i-th identity poll row (SweepRowCheck.nth_row_B). *)
Lemma gb_row_bytes : forall pl t i j, ok pl = true -> (i <= 5)%nat -> (j < 34)%nat ->
  nth (34 * (5 + i) + j) (map (fun b : byte => bv_unsigned b) (sw_bytes pl t)) 0 = nth j (GBz (Z.of_nat i)) 0.
Proof.
  intros pl t i j Hok Hi Hj.
  assert (Hw : (1 <= Z.to_nat (sw_in pl))%nat).
  { unfold ok, fits in Hok. unfold sw_in.
    apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hok _].
    apply Z.leb_le in Hok. lia. }
  unfold sw_bytes. rewrite SWEEP_rows, gb_nth_unsigned.
  pose proof (length_sweep_rows (sw_base pl) (Z.to_nat (sw_in pl)) (sw_vals pl t) Hw) as Hlen.
  rewrite gb_nth_concat34;
    [| apply Forall_rowok_len, sweep_rows_ok | lia | exact Hj].
  rewrite nth_row_B by lia. unfold GB, bl.
  rewrite (map_nth (Z_to_bv 8) (GBz (Z.of_nat i)) 0 j).
  apply bv8_small. apply gb_gbz_range; [lia | exact Hj].
Qed.

(* ---- the symbolic state at the head of the loop ---- *)
(* Atoms 0..31 are the registers at 0x8173c; 32 is the address of `poll` (spill slot 80),
   33 the address of the compound literal (slot 56) and 34 the one's complement of the
   sweep buffer (slot 88). The regions: the five shadow bytes of `poll` (s3 = the frame's
   shadow base, offsets 58..62), the three spill slots above s1, and the literal's four
   bytes. No region carries a chunk the stores write, and every chunk value is an atom. *)
Definition gb_rs0 : YP09.smem :=
  [ YP09.mkRegion (Some 19%nat) 58 63 58 63 [];
    YP09.mkRegion (Some 9%nat) 0 192 0 0
      [YP09.mkChunk 80 (CVal 8 (SOff 32 0)); YP09.mkChunk 56 (CVal 8 (SOff 33 0));
       YP09.mkChunk 88 (CVal 8 (SOff 34 0))];
    YP09.mkRegion (Some 33%nat) 0 4 0 4 [] ].
Definition ss_gb0 : sstate := mkSS GPS_gbhd sr_atoms gb_rs0 None (mkFacts [] [] []).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* A one-byte chunk of a literal gives that byte of the state's memory. *)
Lemma gb_cv1 : forall (E' : env) (H : word -> bool) (mem : word -> option byte) base off v,
  YP09.chunk_ok SEGS E' (mrestrict H mem) base (YP09.mkChunk off (CVal 1 (SLit v))) -> 0 <= v < 256 ->
  aview SEGS H mem (base + off) = Some v.
Proof.
  intros E' H mem base off v Hc Hv.
  destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (b & Hb & Hm).
  cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb, Hm. rewrite Z.add_0_r in Hm.
  unfold aview. rewrite Hm. injection Hb as <-. cbn [option_map].
  f_equal. unfold YP09.byte_of_word. cbn [sv_denot].
  rewrite Z.mul_0_r, Z.shiftr_0_r, unsigned_lit_small by lia. apply bv8_small. exact Hv.
Qed.

(* The same for a one-byte chunk whose value is any expression, read mod 256. *)
Lemma gb_cv1m : forall (E' : env) (H : word -> bool) (mem : word -> option byte) base off (e : sv) v,
  YP09.chunk_ok SEGS E' (mrestrict H mem) base (YP09.mkChunk off (CVal 1 e)) ->
  U E' e mod 256 = v -> 0 <= v < 256 -> aview SEGS H mem (base + off) = Some v.
Proof.
  intros E' H mem base off e v Hc Hu Hv.
  destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (b & Hb & Hm).
  cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb, Hm. rewrite Z.add_0_r in Hm.
  unfold aview. rewrite Hm. injection Hb as <-. cbn [option_map].
  f_equal. unfold YP09.byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
  change (bv_unsigned (sv_denot E' e)) with (U E' e).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact Hu.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
(* The runtime the turn uses, as GSW_RT gives it, and the callee's contract. *)
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA GS___interceptor_trampoline_bcmp).
Hypothesis HIMGSH : img_shadow_vis SEGS B.
Hypothesis HGM : globs_marked SEGS B GRANT_GLOBS_B.
Hypothesis TIPB : tb_reac_ctrl_identity_poll_block_spec B.
(* Image B's read-only tables, as GSW_IMG gives them: POLL (object 6), which the third
   comparison reads, and GRANT_GROUPB (object 19), which the callee copies. *)
Hypothesis HIMG : IMG_LLVMF_SWEEP B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

Section t.
Variables (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) (t s : Z) (i : nat).
Hypothesis HB : ge_base B MT cx.
Hypothesis HJ : ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k.
Hypothesis HFR : YG01.frames S3 = [(GE_CID, fp)].
Hypothesis HBODY : ge_body cx fp GPS_gbhd W3 ms3 GSH_a.
Hypothesis HBLK : gsw_blk B cx fp ly3 S3 W3 ms3 t s.
Hypothesis HROWS : gsw_rows cx W3 ms3 t s.
Hypothesis HS88 : gslot cx W3 ms3 88 (2 ^ 64 - 1 - s).
Hypothesis Hi : (i <= 5)%nat.
Hypothesis R18 : getr (ms_regs ms3) 18 = w64 (Z.of_nat i).
Hypothesis R24 : getr (ms_regs ms3) 24 = w64 (34 * Z.of_nat i).
Hypothesis R20 : getr (ms_regs ms3) 20 = w64 (s + 170).
Hypothesis R22 : getr (ms_regs ms3) 22 = w64 (s + 190).
Hypothesis R23 : getr (ms_regs ms3) 23 = w64 (s + 186).
Hypothesis R21 : getr (ms_regs ms3) 21 = w64 (-8).
Hypothesis R25 : getr (ms_regs ms3) 25 = w64 (VAL (A_OBJ 6) + 3 * Z.of_nat i).
Hypothesis R27 : getr (ms_regs ms3) 27 = w64 s.
Hypothesis R19 : getr (ms_regs ms3) 19 = w64 (gSH cx fp).
(* The two ways out of a turn: round again at i + 1, or leave for the free of the sweep. *)
Hypothesis HLOOP : forall (ms' : machine_state) (md' : Model),
  (S i <= 5)%nat ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms') md' k ->
  ge_body cx fp GPS_gbhd W3 ms' GSH_a ->
  gsw_blk B cx fp ly3 S3 W3 ms' t s -> gsw_rows cx W3 ms' t s ->
  gslot cx W3 ms' 88 (2 ^ 64 - 1 - s) ->
  getr (ms_regs ms') 18 = w64 (Z.of_nat (S i)) ->
  getr (ms_regs ms') 24 = w64 (34 * Z.of_nat (S i)) ->
  getr (ms_regs ms') 20 = w64 (s + 170) ->
  getr (ms_regs ms') 22 = w64 (s + 190) ->
  getr (ms_regs ms') 23 = w64 (s + 186) ->
  getr (ms_regs ms') 21 = w64 (-8) ->
  getr (ms_regs ms') 25 = w64 (VAL (A_OBJ 6) + 3 * Z.of_nat (S i)) ->
  getr (ms_regs ms') 27 = w64 s -> getr (ms_regs ms') 19 = w64 (gSH cx fp) ->
  SRr SEGS W3 (mkCfg ms' md') (ge_post B MT cx).
Hypothesis HEXIT : forall (ms' : machine_state) (md' : Model),
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms') md' k ->
  ge_body cx fp GPS_free1 W3 ms' GSH_a ->
  gsw_blk B cx fp ly3 S3 W3 ms' t s ->
  getr (ms_regs ms') 27 = w64 s -> getr (ms_regs ms') 19 = w64 (gSH cx fp) ->
  SRr SEGS W3 (mkCfg ms' md') (ge_post B MT cx).

Lemma gb_frame_eq : forall c p, frame_addr ly3 c p = frame_addr (c_ly cx) c p.
Proof.
  intros c p. pose proof HJ as (_ & HLY & _). destruct HLY as (_ & _ & _ & _ & _ & HF & _).
  unfold frame_addr. rewrite HF. reflexivity.
Qed.

(* The frame, its shadow, the machine stack and the realigned stack pointer, as numbers.
   The frame's place against image B's own range is LLVMFEntrySeat.ge_F_facts (through
   YC1h.v frm_off_imgB). *)
Lemma gb_nums :
  gF cx fp mod 32 = 0 /\ 4096 <= gF cx fp /\ gF cx fp + 1024 <= alloc_ceiling /\ in_app (gF cx fp) 1024 /\
  gSH cx fp = SHADOW_OFF + gF cx fp / 8 /\ 8 * (gF cx fp / 8) = gF cx fp /\
  alloc_ceiling + GE_STK <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\ spZ (c_regs cx) mod 16 = 0 /\
  c_sp1 cx mod 32 = 0 /\ spZ (c_regs cx) - 304 <= c_sp1 cx <= spZ (c_regs cx) - 288 /\
  c_sp1 cx mod 16 = 0.
Proof.
  pose proof HJ as (HAR & _).
  pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1d & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  assert (Hfin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR Hfin) as (HFal & _ & _ & _).
  pose proof (ge_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF4096 & HFceil & HFia & _ & ESH).
  rewrite gb_frame_eq in HFal. fold (gF cx fp) in HFal.
  pose proof (Z.div_mod (gF cx fp) 32 ltac:(lia)) as D32.
  pose proof (Z.div_mod (gF cx fp) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (gF cx fp) 8 ltac:(lia)) as M8.
  destruct (sp1_facts (spZ (c_regs cx) + -288) ltac:(unfold GE_STK, STK_LLVMFuzzerTestOneInput in *; lia)
             ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity))
    as (Hsp1r & Hsp1al & Hsp1al16).
  rewrite <- Hsp1d in Hsp1r, Hsp1al, Hsp1al16.
  split; [exact HFal|]. split; [exact HF4096|]. split; [exact HFceil|]. split; [exact HFia|].
  split; [exact ESH|]. split; [lia|].
  split; [unfold GE_STK, STK_LLVMFuzzerTestOneInput in *; lia|]. split; [lia|]. split; [exact Hal16|].
  split; [exact Hsp1al|]. split; [lia | exact Hsp1al16].
Qed.

(* ---- the environment of the turn: the registers at the head, the three slot values ---- *)
Definition gb_extra : list word :=
  [w64 (gF cx fp + GO_POLL); w64 (gF cx fp + GO_LIT); w64 (2 ^ 64 - 1 - s)].
Definition gb_E : env := Eimg (Ereg (ms_regs ms3) gb_extra).

Lemma gb_EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew gb_E n = getr (ms_regs ms3) r.
Proof. intros nn r Hnn. apply ew_Eimg_Ereg_nat. exact Hnn. Qed.

Lemma gb_X : forall j, (j < 3)%nat -> ew gb_E (32 + j) = nth j gb_extra (Z_to_bv 64 0).
Proof. intros j Hj. unfold gb_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

Lemma gb_E32 : ew gb_E 32 = w64 (gF cx fp + GO_POLL).
Proof. exact (gb_X 0 ltac:(lia)). Qed.
Lemma gb_E33 : ew gb_E 33 = w64 (gF cx fp + GO_LIT).
Proof. exact (gb_X 1 ltac:(lia)). Qed.
Lemma gb_E34 : ew gb_E 34 = w64 (2 ^ 64 - 1 - s).
Proof. exact (gb_X 2 ltac:(lia)). Qed.

Lemma gb_B19 : base_val gb_E (Some 19%nat) = gSH cx fp.
Proof.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & _).
  pose proof asan_consts as (C1 & _).
  cbn [base_val]. rewrite (gb_EE 19%nat 19%bv eq_refl), R19. apply unsigned_lit_small.
  pose proof (Z.div_mod (gF cx fp) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (gF cx fp) 8 ltac:(lia)).
  rewrite ESH. unfold SHADOW_OFF. lia.
Qed.

Lemma gb_B9 : base_val gb_E (Some 9%nat) = c_sp1 cx.
Proof.
  pose proof gb_nums as (_ & _ & _ & _ & _ & _ & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof HBODY as (_ & _ & _ & _ & _ & _ & (_ & _ & Q9 & _) & _).
  pose proof asan_consts as (C1 & _). unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0lo.
  cbn [base_val]. rewrite (gb_EE 9%nat 9%bv eq_refl), Q9. apply unsigned_lit_small. lia.
Qed.

Lemma gb_B33 : base_val gb_E (Some 33%nat) = gF cx fp + GO_LIT.
Proof.
  pose proof gb_nums as (_ & HF4096 & HFceil & _). pose proof asan_consts as (C1 & _).
  cbn [base_val]. rewrite gb_E33. apply unsigned_lit_small. unfold GO_LIT. lia.
Qed.

(* The head registers, as atoms of the turn's environment. *)
Lemma gb_A18 : ew gb_E 18 = w64 (Z.of_nat i).
Proof. rewrite (gb_EE 18%nat 18%bv eq_refl). exact R18. Qed.
Lemma gb_A19 : ew gb_E 19 = w64 (gSH cx fp).
Proof. rewrite (gb_EE 19%nat 19%bv eq_refl). exact R19. Qed.
Lemma gb_A20 : ew gb_E 20 = w64 (s + 170).
Proof. rewrite (gb_EE 20%nat 20%bv eq_refl). exact R20. Qed.
Lemma gb_A21 : ew gb_E 21 = w64 (-8).
Proof. rewrite (gb_EE 21%nat 21%bv eq_refl). exact R21. Qed.
Lemma gb_A22 : ew gb_E 22 = w64 (s + 190).
Proof. rewrite (gb_EE 22%nat 22%bv eq_refl). exact R22. Qed.
Lemma gb_A23 : ew gb_E 23 = w64 (s + 186).
Proof. rewrite (gb_EE 23%nat 23%bv eq_refl). exact R23. Qed.
Lemma gb_A24 : ew gb_E 24 = w64 (34 * Z.of_nat i).
Proof. rewrite (gb_EE 24%nat 24%bv eq_refl). exact R24. Qed.
Lemma gb_A25 : ew gb_E 25 = w64 (VAL (A_OBJ 6) + 3 * Z.of_nat i).
Proof. rewrite (gb_EE 25%nat 25%bv eq_refl). exact R25. Qed.
Lemma gb_A27 : ew gb_E 27 = w64 s.
Proof. rewrite (gb_EE 27%nat 27%bv eq_refl). exact R27. Qed.

(* The image's read-only bytes are the same in every state this walk reaches. *)
Lemma gb_rod : forall (mem' : word -> option byte) md' k',
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem' md' k' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem').
Proof.
  intros mem' md' k' HJ' a Hro Ho He.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HROD & _).
  pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a).
  - exact (HROD a Hro Ho He).
  - destruct Hro as [(sg & Hs & _ & Hr) | Hgot]; [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hgot)].
  - exact Ho.
  - exact He.
  - apply fp_spares_closed. intros (r & [] & _).
Qed.

(* The frame, its shadow bytes and the machine-stack window lie apart. *)
Lemma gb_sep :
  (gF cx fp + 1024 <= gSH cx fp \/ gSH cx fp + 128 <= gF cx fp) /\
  gSH cx fp + 128 <= c_sp1 cx - 8192 /\ gF cx fp + 1024 <= c_sp1 cx - 8192 /\ 0 <= gSH cx fp.
Proof.
  pose proof gb_nums as (HFal & HF4096 & HFceil & HFia & ESH & E8 & Hsp0lo & Hsp0hi & Hsp0al & Hsp1al & Hsp1 & _).
  pose proof asan_consts as (C1 & _). unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0lo.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFia.
  destruct HFia as (_ & [HA | (HB1 & HB2)]).
  - split; [left; rewrite ESH; unfold SHADOW_OFF; lia|].
    split; [rewrite ESH; unfold SHADOW_OFF; lia|]. split; [lia|]. rewrite ESH; unfold SHADOW_OFF; lia.
  - split; [right; rewrite ESH; unfold SHADOW_OFF; lia|].
    split; [rewrite ESH; unfold SHADOW_OFF; lia|]. split; [lia|]. rewrite ESH; unfold SHADOW_OFF; lia.
Qed.

Lemma gb_sh_nf : forall a, gSH cx fp + 58 <= a < gSH cx fp + 63 -> ~ (gF cx fp <= a < gF cx fp + 1024).
Proof. intros a Ha. pose proof gb_sep as (HSEP & _). destruct HSEP; lia. Qed.

Lemma gb_sh_nf2 : forall a, gSH cx fp <= a < gSH cx fp + 128 -> ~ (gF cx fp <= a < gF cx fp + 1024).
Proof. intros a Ha. pose proof gb_sep as (HSEP & _). destruct HSEP; lia. Qed.

(* Every byte the turn writes is the walk's own: the frame's shadow window of `poll`
   and the four bytes of the compound literal, both inside the frame it owns. *)
Lemma gb_awr : forall (E' : env) (rs : YP09.smem),
  ew E' 9 = ew gb_E 9 -> ew E' 19 = ew gb_E 19 -> ew E' 33 = ew gb_E 33 ->
  YP09.skeleton rs = YP09.skeleton gb_rs0 ->
  awr_ok E' rs GE_STK (spZ (c_regs cx)) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(GE_CID, fp)].
Proof.
  intros E' rs H9 H19 H33 Hsk a Hin.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & _).
  pose proof gb_B19 as B19. pose proof gb_B33 as B33.
  apply (in_wrange_skeleton E' rs gb_rs0 a Hsk) in Hin.
  unfold gb_rs0 in Hin. destruct Hin as (r & Hr & Ha).
  cbn [In] in Hr. cbn [base_val] in B19, B33.
  right; right; right. exists GE_CID, fp. split; [left; reflexivity|].
  rewrite gb_frame_eq. fold (gF cx fp). change (fs_frame_bytes GE_CID) with 1024.
  destruct Hr as [<- | [<- | [<- | []]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - right. rewrite H19, B19, ESH in Ha. unfold in_zr, shadow_addr. cbn [fst snd].
    change (1024 / 8) with 128. lia.
  - exfalso. lia.
  - left. rewrite H33, B33 in Ha. unfold in_zr. cbn [fst snd]. unfold GO_LIT in Ha. lia.
Qed.

(* The three regions of the turn's state survive a call that keeps their bytes. *)
Lemma gb_kept : forall (E' : env) (m m' : word -> option byte) cs1 cs2 cs3,
  ew E' 9 = ew gb_E 9 -> ew E' 19 = ew gb_E 19 -> ew E' 33 = ew gb_E 33 ->
  (forall a, gSH cx fp + 58 <= a < gSH cx fp + 63 -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  (forall a, c_sp1 cx <= a < c_sp1 cx + 192 -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  (forall a, gF cx fp + GO_LIT <= a < gF cx fp + GO_LIT + 4 -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  (forall a, gSH cx fp + 58 <= a < gSH cx fp + 63 -> apresent (w_H W3) m' a) ->
  (forall a, gF cx fp + GO_LIT <= a < gF cx fp + GO_LIT + 4 -> apresent (w_H W3) m' a) ->
  Forall (region_kept SEGS E' (mrestrict (w_H W3) m) (mrestrict (w_H W3) m'))
    [YP09.mkRegion (Some 19%nat) 58 63 58 63 cs1;
     YP09.mkRegion (Some 9%nat) 0 192 0 0 cs2;
     YP09.mkRegion (Some 33%nat) 0 4 0 4 cs3].
Proof.
  intros E' m m' cs1 cs2 cs3 H9 H19 H33 K19 K9 K33 P19 P33.
  pose proof gb_B19 as B19. pose proof gb_B9 as B9. pose proof gb_B33 as B33.
  cbn [base_val] in B19, B9, B33.
  repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    rewrite ?H9, ?H19, ?H33, ?B19, ?B9, ?B33; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply K19. lia.
  - intros _. apply (apresent_writable SEGS). apply P19. lia.
  - apply (mbyte_of_aview SEGS). apply K9. lia.
  - lia.
  - apply (mbyte_of_aview SEGS). apply K33. lia.
  - intros _. apply (apresent_writable SEGS). apply P33. lia.
Qed.

(* The five shadow bytes the turn writes before the call (0x8173c .. 0x81750): the 34
   bytes of `poll` at frame offset 464 are usable, the last granule partially (2). *)
Definition gb_sh5 (m : word -> option byte) : Prop :=
  aview SEGS (w_H W3) m (gSH cx fp + 58) = Some 0 /\
  aview SEGS (w_H W3) m (gSH cx fp + 59) = Some 0 /\
  aview SEGS (w_H W3) m (gSH cx fp + 60) = Some 0 /\
  aview SEGS (w_H W3) m (gSH cx fp + 61) = Some 0 /\
  aview SEGS (w_H W3) m (gSH cx fp + 62) = Some 2.

Lemma gb_sh5_tr : forall (m m' : word -> option byte),
  gb_sh5 m -> (forall a, gSH cx fp + 58 <= a < gSH cx fp + 63 -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  gb_sh5 m'.
Proof.
  intros m m' (H58 & H59 & H60 & H61 & H62) HK. unfold gb_sh5.
  split; [rewrite HK by lia; exact H58|]. split; [rewrite HK by lia; exact H59|].
  split; [rewrite HK by lia; exact H60|]. split; [rewrite HK by lia; exact H61|].
  rewrite HK by lia. exact H62.
Qed.

(* Those five bytes say the 34 bytes of `poll` are usable. *)
Lemma gb_ra_of_sh5 : forall (m : word -> option byte),
  gb_sh5 m -> range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (gF cx fp + GO_POLL) 34.
Proof.
  intros m (C58 & C59 & C60 & C61 & C62).
  pose proof gb_nums as (HFal & HF4096 & HFceil & HFia & ESH & E8 & _).
  assert (HD1 : (gF cx fp + 464) / 8 = gF cx fp / 8 + 58).
  { rewrite <- E8 at 1. replace (8 * (gF cx fp / 8) + 464) with ((gF cx fp / 8) * 8 + 464) by lia.
    rewrite Z.div_add_l by lia. reflexivity. }
  assert (HD2 : (gF cx fp + 464 + 32) / 8 = gF cx fp / 8 + 62).
  { rewrite <- E8 at 1. replace (8 * (gF cx fp / 8) + 464 + 32) with ((gF cx fp / 8) * 8 + 496) by lia.
    rewrite Z.div_add_l by lia. reflexivity. }
  assert (HM1 : (gF cx fp + 464) mod 8 = 0).
  { rewrite <- E8. replace (8 * (gF cx fp / 8) + 464) with ((gF cx fp / 8 + 58) * 8) by lia. apply Z_mod_mult. }
  assert (HM2 : (gF cx fp + 464 + 32) mod 8 = 0).
  { rewrite <- E8. replace (8 * (gF cx fp / 8) + 464 + 32) with ((gF cx fp / 8 + 62) * 8) by lia. apply Z_mod_mult. }
  unfold GO_POLL. replace 34 with (32 + 2) by lia. apply range_addressable_app; [lia| |].
  - apply zero_shadow_range; [exact HM1 | reflexivity |].
    intros j Hj. change (32 / 8) with 4 in Hj. unfold shadow_of_addr. rewrite HD1.
    assert (Hj4 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
    destruct Hj4 as [-> | [-> | [-> | ->]]].
    + replace (SHADOW_OFF + (gF cx fp / 8 + 58) + 0) with (gSH cx fp + 58) by (rewrite ESH; lia). exact C58.
    + replace (SHADOW_OFF + (gF cx fp / 8 + 58) + 1) with (gSH cx fp + 59) by (rewrite ESH; lia). exact C59.
    + replace (SHADOW_OFF + (gF cx fp / 8 + 58) + 2) with (gSH cx fp + 60) by (rewrite ESH; lia). exact C60.
    + replace (SHADOW_OFF + (gF cx fp / 8 + 58) + 3) with (gSH cx fp + 61) by (rewrite ESH; lia). exact C61.
  - apply (range_addressable_partial _ SHADOW_OFF (gF cx fp + 464 + 32) 2); [|exact HM2 | lia].
    unfold shadow_of_addr. rewrite HD2.
    replace (SHADOW_OFF + (gF cx fp / 8 + 62)) with (gSH cx fp + 62) by (rewrite ESH; lia). exact C62.
Qed.

Lemma gb_garr8_tr : forall (m m' : word -> option byte) b l,
  garr8 SEGS (mrestrict (w_H W3) m) b l ->
  (forall a, b <= a < b + Z.of_nat (length l) -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  garr8 SEGS (mrestrict (w_H W3) m') b l.
Proof.
  intros m m' b l Hg HK. apply (garr8_frame SEGS (mrestrict (w_H W3) m)); [exact Hg|].
  intros a Ha. apply (mbyte_of_aview SEGS). apply HK. exact Ha.
Qed.

(* The sweep the box built: its block, its length, and its row 5 + i. *)
Lemma gb_rows_ok : ok (c_pl cx) = true /\ 1 <= sw_in (c_pl cx) <= 40 /\ 11 <= sw_rows (c_pl cx).
Proof.
  pose proof HBLK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hok & _).
  pose proof HROWS as (Hwant & _).
  pose proof (gs_ok_range (c_pl cx) Hok) as (_ & Hin & _).
  unfold sw_want in Hwant. split; [exact Hok|]. split; [exact Hin | lia].
Qed.

Lemma gb_len_concat34 : forall (L : list (list byte)),
  Forall (fun r => length r = 34%nat) L -> length (concat L) = (34 * length L)%nat.
Proof.
  induction L as [|r L IH]; intros HL; [reflexivity|].
  inversion HL as [|r0 L0 Hr HL']; subst r0 L0.
  cbn [concat length]. rewrite length_app, Hr, (IH HL'). lia.
Qed.

Lemma gb_sweep_len : Z.of_nat (length (sw_bytes (c_pl cx) t)) = 34 * (8 + 3 * sw_in (c_pl cx)).
Proof.
  pose proof gb_rows_ok as (_ & Hin & _).
  unfold sw_bytes. rewrite SWEEP_rows, gb_len_concat34 by (apply Forall_rowok_len, sweep_rows_ok).
  rewrite Nat2Z.inj_mul,
    (length_sweep_rows (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t) ltac:(lia)).
  lia.
Qed.

Lemma gb_rowlen : Z.of_nat (length (sw_bytes (c_pl cx) t)) <= sw_mbytes (c_pl cx).
Proof.
  pose proof gb_sweep_len as HL. pose proof HROWS as (Hwant & _).
  unfold sw_mbytes. unfold sw_want in Hwant. destruct (Z.ltb_spec 0 (sw_rows (c_pl cx))); lia.
Qed.

Lemma gb_blk : In (s, sw_mbytes (c_pl cx)) (ablocks B ly3 S3) /\ 0 < s /\ 374 <= sw_mbytes (c_pl cx).
Proof.
  pose proof HBLK as (_ & Hsin & _ & _ & _ & _ & _ & _ & _ & Ht0 & Hs0 & _).
  pose proof gb_rows_ok as (_ & _ & Hr11).
  split; [exact Hsin|]. split; [exact Hs0|]. unfold sw_mbytes.
  destruct (Z.ltb_spec 0 (sw_rows (c_pl cx))); lia.
Qed.

(* The call left `poll` holding GBz i; row 5 + i of the sweep holds the same bytes. *)
Lemma gb_row_eq : forall (m : word -> option byte) j,
  garr8 SEGS (mrestrict (w_H W3) m) (gF cx fp + GO_POLL) (GBz (Z.of_nat i)) ->
  garr8 SEGS (mrestrict (w_H W3) m) s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) ->
  0 <= j < 34 ->
  aview SEGS (w_H W3) m (gF cx fp + GO_POLL + j) = aview SEGS (w_H W3) m (s + 170 + 34 * Z.of_nat i + j).
Proof.
  intros m j HP HR Hj.
  pose proof gb_rows_ok as (Hok & Hin1 & _). pose proof gb_sweep_len as HL.
  destruct (garr8_nthZ SEGS _ _ _ j HP ltac:(lia) ltac:(rewrite gb_gbz_len; lia)) as (Hv1 & Hr1).
  destruct (garr8_nthZ SEGS _ _ _ (34 * (5 + Z.of_nat i) + j) HR ltac:(lia)
              ltac:(rewrite length_map; lia)) as (Hv2 & Hr2).
  assert (HE : nth (Z.to_nat (34 * (5 + Z.of_nat i) + j))
                 (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) 0
               = nth (Z.to_nat j) (GBz (Z.of_nat i)) 0).
  { replace (Z.to_nat (34 * (5 + Z.of_nat i) + j)) with (34 * (5 + i) + Z.to_nat j)%nat by lia.
    apply gb_row_bytes; [exact Hok | exact Hi | lia]. }
  rewrite HE in Hv2, Hr2.
  rewrite (aview_of_val_mem1 SEGS (w_H W3) m _ _ Hv1 Hr1).
  replace (s + 170 + 34 * Z.of_nat i + j) with (s + (34 * (5 + Z.of_nat i) + j)) by lia.
  rewrite (aview_of_val_mem1 SEGS (w_H W3) m _ _ Hv2 Hr2). reflexivity.
Qed.

(* Row 5 + i at offset 16 holds the four bytes of the compound literal. *)
Lemma gb_lit_eq : forall (m : word -> option byte) j,
  garr8 SEGS (mrestrict (w_H W3) m) s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) ->
  (forall j', 0 <= j' < 4 -> aview SEGS (w_H W3) m (gF cx fp + GO_LIT + j') = Some (nth (Z.to_nat j') gb_LITz 0)) ->
  0 <= j < 4 ->
  aview SEGS (w_H W3) m (s + 170 + 34 * Z.of_nat i + 16 + j) = aview SEGS (w_H W3) m (gF cx fp + GO_LIT + j).
Proof.
  intros m j HR HL4 Hj.
  pose proof gb_rows_ok as (Hok & Hin1 & _). pose proof gb_sweep_len as HL.
  destruct (garr8_nthZ SEGS _ _ _ (34 * (5 + Z.of_nat i) + 16 + j) HR ltac:(lia)
              ltac:(rewrite length_map; lia)) as (Hv2 & Hr2).
  assert (HE : nth (Z.to_nat (34 * (5 + Z.of_nat i) + 16 + j))
                 (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) 0
               = nth (Z.to_nat j) gb_LITz 0).
  { replace (Z.to_nat (34 * (5 + Z.of_nat i) + 16 + j)) with (34 * (5 + i) + (16 + Z.to_nat j))%nat by lia.
    rewrite gb_row_bytes by (first [exact Hok | exact Hi | lia]).
    apply gb_lit_bytes; [exact Hi | lia]. }
  rewrite HE in Hv2, Hr2.
  replace (s + 170 + 34 * Z.of_nat i + 16 + j) with (s + (34 * (5 + Z.of_nat i) + 16 + j)) by lia.
  rewrite (aview_of_val_mem1 SEGS (w_H W3) m _ _ Hv2 Hr2), (HL4 j Hj). reflexivity.
Qed.

(* Row 5 + i at offset 20 holds the three bytes POLL[i] of the image. *)
Lemma gb_pollt_eq : forall (m : word -> option byte) j,
  garr8 SEGS (mrestrict (w_H W3) m) s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) ->
  garr8 SEGS (mrestrict (w_H W3) m) (VAL (A_OBJ 6)) POLLz ->
  0 <= j < 3 ->
  aview SEGS (w_H W3) m (s + 170 + 34 * Z.of_nat i + 20 + j)
  = aview SEGS (w_H W3) m (VAL (A_OBJ 6) + 3 * Z.of_nat i + j).
Proof.
  intros m j HR HP Hj.
  pose proof gb_rows_ok as (Hok & Hin1 & _). pose proof gb_sweep_len as HL.
  destruct (garr8_nthZ SEGS _ _ _ (34 * (5 + Z.of_nat i) + 20 + j) HR ltac:(lia)
              ltac:(rewrite length_map; lia)) as (Hv2 & Hr2).
  destruct (garr8_nthZ SEGS _ _ _ (3 * Z.of_nat i + j) HP ltac:(lia) ltac:(cbn [length POLLz]; lia))
    as (Hv3 & Hr3).
  assert (HE : nth (Z.to_nat (34 * (5 + Z.of_nat i) + 20 + j))
                 (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) 0
               = nth (Z.to_nat (3 * Z.of_nat i + j)) POLLz 0).
  { replace (Z.to_nat (34 * (5 + Z.of_nat i) + 20 + j)) with (34 * (5 + i) + (20 + Z.to_nat j))%nat by lia.
    rewrite gb_row_bytes by (first [exact Hok | exact Hi | lia]).
    replace (Z.to_nat (3 * Z.of_nat i + j)) with (3 * i + Z.to_nat j)%nat by lia.
    symmetry. apply gb_poll_bytes; [exact Hi | lia]. }
  rewrite HE in Hv2, Hr2.
  replace (s + 170 + 34 * Z.of_nat i + 20 + j) with (s + (34 * (5 + Z.of_nat i) + 20 + j)) by lia.
  replace (VAL (A_OBJ 6) + 3 * Z.of_nat i + j) with (VAL (A_OBJ 6) + (3 * Z.of_nat i + j)) by lia.
  rewrite (aview_of_val_mem1 SEGS (w_H W3) m _ _ Hv2 Hr2),
          (aview_of_val_mem1 SEGS (w_H W3) m _ _ Hv3 Hr3). reflexivity.
Qed.

(* ---- what a turn keeps ----
   The callee's contract keeps the machine stack above alloc_ceiling, the blocks, the
   frames and their shadow, each outside the callee's own window and `poll`
   (GrantBContracts.tcj_kept); every fact the turn carries lies at one of those. *)
Definition gb_kat (a : Z) : Prop :=
  (alloc_ceiling <= a < 2 ^ 64) \/ (gF cx fp <= a < gF cx fp + 1024) \/
  (gSH cx fp <= a < gSH cx fp + 128) \/
  (exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= a < p + n).

Lemma gb_kat_rng : forall a, gb_kat a -> 0 <= a < 2 ^ 64.
Proof.
  intros a Ha.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & _ & _ & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0).
  pose proof asan_consts as (C1 & _). unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0lo.
  destruct Ha as [Ha | [Ha | [Ha | (p & n & Hin & Ha)]]]; try lia.
  pose proof (proj1 HJ) as HAR.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hn0).
  pose proof (req_size_pos' n ltac:(lia)) as (_ & Hreq). lia.
Qed.

(* What the whole turn leaves alone: all but its stack windows, `poll`, the five shadow
   bytes of `poll` and the four bytes of the compound literal. *)
Definition gb_tkeep (m m' : word -> option byte) : Prop :=
  forall a, gb_kat a ->
    ~ (c_sp1 cx - 8192 <= a < c_sp1 cx) ->
    ~ (gF cx fp + GO_POLL <= a < gF cx fp + GO_POLL + 34) ->
    ~ (gSH cx fp + 58 <= a < gSH cx fp + 63) ->
    ~ (gF cx fp + GO_LIT <= a < gF cx fp + GO_LIT + 4) ->
    aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.

Lemma gb_tkeep_refl : forall m, gb_tkeep m m.
Proof. intros m a _ _ _ _ _. reflexivity. Qed.

Lemma gb_tkeep_trans : forall m1 m2 m3, gb_tkeep m1 m2 -> gb_tkeep m2 m3 -> gb_tkeep m1 m3.
Proof. intros m1 m2 m3 H1 H2 a Ha Aa Bb Cc Dd. rewrite (H2 a Ha Aa Bb Cc Dd). exact (H1 a Ha Aa Bb Cc Dd). Qed.

(* What a call of this turn leaves alone: everything but its own stack window and `poll`. *)
Definition gb_keep (m m' : word -> option byte) : Prop :=
  forall a, gb_kat a -> ~ (c_sp1 cx - 8192 <= a < c_sp1 cx) ->
    ~ (gF cx fp + GO_POLL <= a < gF cx fp + GO_POLL + 34) ->
    aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.

Lemma gb_tkeep_of_keep : forall m m', gb_keep m m' -> gb_tkeep m m'.
Proof. intros m m' HK a Ha Aa Bb _ _. exact (HK a Ha Aa Bb). Qed.

(* reac_ctrl_identity_poll_block's kept clause, read on the turn's addresses. *)
Lemma gb_keep_of_tcj : forall (m m' : word -> option byte),
  tcj_kept B STK_reac_ctrl_identity_poll_block ly3 S3 W3 m W3 m' (c_sp1 cx)
    (fun a => gF cx fp + GO_POLL <= a < gF cx fp + GO_POLL + 34) ->
  gb_keep m m'.
Proof.
  intros m m' (K1 & K2 & _ & K4 & _) a Ha Hw Hp.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & _).
  assert (Hfin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
  destruct Ha as [Ha | [Ha | [Ha | (p & n & Hin & Ha)]]].
  - apply K1; [exact Ha | unfold STK_reac_ctrl_identity_poll_block, ESTACK; lia | exact Hp].
  - apply (K4 GE_CID fp a Hfin); [|exact Hp].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite gb_frame_eq. fold (gF cx fp).
    change (fs_frame_bytes GE_CID) with 1024. lia.
  - apply (K4 GE_CID fp a Hfin); [|exact Hp].
    right. unfold in_zr. cbn [fst snd]. rewrite gb_frame_eq. fold (gF cx fp).
    unfold shadow_addr. rewrite <- ESH. change (fs_frame_bytes GE_CID / 8) with 128. lia.
  - pose proof (proj1 HJ) as HAR.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos' n ltac:(lia)) as (_ & Hreq).
    replace a with (p + (a - p)) by lia.
    apply (K2 p n (a - p) Hin); [lia | cbv beta; replace (p + (a - p)) with a by lia; exact Hp].
Qed.

(* The frame's shadow byte of the compound literal: in scope from the first slot. *)
Lemma gb_sh68 : forall m, gb_tkeep (ms_mem ms3) m -> aview SEGS (w_H W3) m (gSH cx fp + 68) = Some 4.
Proof.
  intros m HTK.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0). pose proof asan_consts as (C1 & _).
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0lo.
  pose proof HBODY as (_ & _ & _ & _ & _ & _ & _ & _ & Hgsh & _).
  assert (H68 : aview SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + 68) = Some 4).
  { pose proof (Hgsh 68%nat ltac:(vm_compute; lia)) as H. cbn [Z.of_nat] in H.
    replace (nth 68 GSH_a 0) with 4 in H by (vm_compute; reflexivity). exact H. }
  rewrite HTK.
  - exact H68.
  - right; right; left. lia.
  - lia.
  - intros HC. apply (gb_sh_nf2 (gSH cx fp + 68) ltac:(lia)). unfold GO_POLL in HC. lia.
  - lia.
  - intros HC. apply (gb_sh_nf2 (gSH cx fp + 68) ltac:(lia)). unfold GO_LIT in HC. lia.
Qed.

Lemma gb_ra_lit : forall (m : word -> option byte),
  aview SEGS (w_H W3) m (gSH cx fp + 68) = Some 4 ->
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (gF cx fp + GO_LIT) 4.
Proof.
  intros m H68. pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & _).
  assert (HD : (gF cx fp + 544) / 8 = gF cx fp / 8 + 68).
  { rewrite <- E8 at 1. replace (8 * (gF cx fp / 8) + 544) with ((gF cx fp / 8) * 8 + 544) by lia.
    rewrite Z.div_add_l by lia. reflexivity. }
  assert (HM : (gF cx fp + 544) mod 8 = 0).
  { rewrite <- E8. replace (8 * (gF cx fp / 8) + 544) with ((gF cx fp / 8 + 68) * 8) by lia. apply Z_mod_mult. }
  unfold GO_LIT. apply (range_addressable_partial _ SHADOW_OFF (gF cx fp + 544) 4); [|exact HM | lia].
  unfold shadow_of_addr. rewrite HD.
  replace (SHADOW_OFF + (gF cx fp / 8 + 68)) with (gSH cx fp + 68) by (rewrite ESH; lia). exact H68.
Qed.

(* The sweep block: where it lies, and that it lies apart from the frame. *)
Lemma gb_sbnd : 4096 <= s /\ s + req_size (sw_mbytes (c_pl cx)) <= alloc_ceiling /\
  in_app s (req_size (sw_mbytes (c_pl cx))) /\ sw_mbytes (c_pl cx) <= req_size (sw_mbytes (c_pl cx)) /\
  (s + req_size (sw_mbytes (c_pl cx)) <= gF cx fp \/ gF cx fp + 1024 <= s) /\
  (s + req_size (sw_mbytes (c_pl cx)) <= gSH cx fp \/ gSH cx fp + 128 <= s) /\
  s + req_size (sw_mbytes (c_pl cx)) <= c_sp1 cx - 8192.
Proof.
  pose proof (proj1 HJ) as HAR. pose proof gb_blk as (Hsin & Hs0 & Hsm).
  assert (Hfin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ s (sw_mbytes (c_pl cx)) HAR Hsin)
    as (_ & Hs4096 & Hsceil & Hsapp & _ & _).
  pose proof (req_size_pos' (sw_mbytes (c_pl cx)) ltac:(lia)) as (_ & Hreq).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 s (sw_mbytes (c_pl cx)) GE_CID fp
                HAR Hsin Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite gb_frame_eq in Hd. fold (gF cx fp) in Hd.
  change (fs_frame_bytes GE_CID) with 1024 in Hd.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof asan_consts as (C1 & _). unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0lo.
  split; [exact Hs4096|]. split; [exact Hsceil|]. split; [exact Hsapp|]. split; [exact Hreq|].
  split; [exact Hd|]. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hsapp.
  split; [rewrite ESH; unfold SHADOW_OFF; destruct Hsapp as (_ & [HA | (HB1 & HB2)]); lia | lia].
Qed.

(* The two facts of the turn that must cross every call. *)
Definition gb_mem (m : word -> option byte) : Prop :=
  gb_sh5 m /\
  garr8 SEGS (mrestrict (w_H W3) m) s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)).

Lemma gb_mem_tr : forall m m', gb_mem m -> gb_keep m m' -> gb_mem m'.
Proof.
  intros m m' (H5 & Hg) HK.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0).
  pose proof gb_sbnd as (Hs4096 & Hsceil & _ & Hreq & Hsep & Hsepsh & Hsstk).
  pose proof gb_rowlen as HRL.
  pose proof asan_consts as (C1 & _). unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0lo.
  pose proof gb_blk as (Hsin & Hs0 & Hsm).
  split.
  - apply (gb_sh5_tr m); [exact H5|]. intros a Ha. apply HK; [right; right; left; lia | lia |].
    intros HC. apply (gb_sh_nf a Ha). unfold GO_POLL in HC. lia.
  - apply (gb_garr8_tr m); [exact Hg|]. intros a Ha. rewrite length_map in Ha.
    apply HK; [right; right; right; exists s, (sw_mbytes (c_pl cx)); split; [exact Hsin | lia] | lia |].
    unfold GO_POLL. lia.
Qed.

(* The only bytes a run of this turn writes are those five and the four of the literal. *)
Lemma gb_wrange : forall (E' : env) (rs : YP09.smem),
  ew E' 9 = ew gb_E 9 -> ew E' 19 = ew gb_E 19 -> ew E' 33 = ew gb_E 33 ->
  YP09.skeleton rs = YP09.skeleton gb_rs0 ->
  forall a, in_wrange E' rs a ->
    (gSH cx fp + 58 <= a < gSH cx fp + 63) \/ (gF cx fp + GO_LIT <= a < gF cx fp + GO_LIT + 4).
Proof.
  intros E' rs H9 H19 H33 Hsk a Hin.
  pose proof gb_B19 as B19. pose proof gb_B33 as B33. cbn [base_val] in B19, B33.
  apply (in_wrange_skeleton E' rs gb_rs0 a Hsk) in Hin.
  unfold gb_rs0 in Hin. destruct Hin as (r & Hr & Ha). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - left. rewrite H19, B19 in Ha. lia.
  - exfalso. lia.
  - right. rewrite H33, B33 in Ha. lia.
Qed.

Lemma gb_tkeep_run : forall (E' : env) (rs : YP09.smem) (m m' : word -> option byte),
  ew E' 9 = ew gb_E 9 -> ew E' 19 = ew gb_E 19 -> ew E' 33 = ew gb_E 33 ->
  YP09.skeleton rs = YP09.skeleton gb_rs0 ->
  frame_of E' rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  gb_tkeep m m'.
Proof.
  intros E' rs m m' H9 H19 H33 Hsk HFr a Ha Aa Bb Cc Dd.
  pose proof (gb_kat_rng a Ha) as Hr.
  unfold aview. f_equal. unfold mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros Hw. rewrite unsigned_lit_small in Hw by lia.
  destruct (gb_wrange E' rs H9 H19 H33 Hsk a Hw) as [Hsh | Hlit]; [exact (Cc Hsh) | exact (Dd Hlit)].
Qed.

(* What the turn keeps, read on a block, on the frame and on the machine stack. *)
Lemma gb_blk_tkeep : forall (p n : Z) (m m' : word -> option byte),
  In (p, n) (ablocks B ly3 S3) -> gb_tkeep m m' ->
  forall a, p <= a < p + n -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Proof.
  intros p n m m' Hin HTK a Ha.
  pose proof (proj1 HJ) as HAR.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0). pose proof asan_consts as (C1 & _).
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0lo.
  assert (Hfin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hp4096 & Hpceil & Hpapp & _ & _ & Hn0).
  pose proof (req_size_pos' n ltac:(lia)) as (_ & Hreq).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 p n GE_CID fp HAR Hin Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite gb_frame_eq in Hd. fold (gF cx fp) in Hd.
  change (fs_frame_bytes GE_CID) with 1024 in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
  apply HTK.
  - right; right; right. exists p, n. split; [exact Hin | lia].
  - lia.
  - unfold GO_POLL. lia.
  - rewrite ESH. unfold SHADOW_OFF. destruct Hpapp as (_ & [HA | (HB1 & HB2)]); lia.
  - unfold GO_LIT. lia.
Qed.

Lemma gb_frm_tkeep : forall (o : Z) (m m' : word -> option byte),
  gb_tkeep m m' -> 0 <= o < 1024 ->
  ~ (GO_POLL <= o < GO_POLL + 34) -> ~ (GO_LIT <= o < GO_LIT + 4) ->
  aview SEGS (w_H W3) m' (gF cx fp + o) = aview SEGS (w_H W3) m (gF cx fp + o).
Proof.
  intros o m m' HTK Ho Hp Hl.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0). pose proof asan_consts as (C1 & _).
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0lo.
  apply HTK.
  - right; left. lia.
  - lia.
  - unfold GO_POLL in *. lia.
  - intros HC. apply (gb_sh_nf (gF cx fp + o) HC). lia.
  - unfold GO_LIT in *. lia.
Qed.

Lemma gb_stk_tkeep : forall (a : Z) (m m' : word -> option byte),
  gb_tkeep m m' -> c_sp1 cx <= a < spZ (c_regs cx) ->
  aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Proof.
  intros a m m' HTK Ha.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0). pose proof asan_consts as (C1 & _).
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0lo.
  apply HTK.
  - left. lia.
  - lia.
  - unfold GO_POLL. lia.
  - lia.
  - unfold GO_LIT. lia.
Qed.

Lemma gb_rdword_tr : forall (m m' : word -> option byte) a v,
  rdword (aview SEGS (w_H W3) m) a = Some v ->
  (forall x, a <= x < a + 8 -> aview SEGS (w_H W3) m' x = aview SEGS (w_H W3) m x) ->
  rdword (aview SEGS (w_H W3) m') a = Some v.
Proof.
  intros m m' a v Hr HK. unfold rdword in *.
  rewrite (HK a ltac:(lia)), (HK (a+1) ltac:(lia)), (HK (a+2) ltac:(lia)), (HK (a+3) ltac:(lia)),
          (HK (a+4) ltac:(lia)), (HK (a+5) ltac:(lia)), (HK (a+6) ltac:(lia)), (HK (a+7) ltac:(lia)).
  exact Hr.
Qed.

(* `addiw` of 1 on a counter below six. *)
Lemma gb_addiw1 : forall z, 0 <= z <= 5 ->
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 z)) (low32 (Z_to_bv 64 1))) = Z_to_bv 64 (z + 1).
Proof.
  intros z Hz.
  assert (C : z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5) by lia.
  destruct C as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
Qed.

Lemma gb_rows_run : forall (E' : env) (rs : YP09.smem) (m m' : word -> option byte),
  ew E' 9 = ew gb_E 9 -> ew E' 19 = ew gb_E 19 -> ew E' 33 = ew gb_E 33 ->
  YP09.skeleton rs = YP09.skeleton gb_rs0 ->
  frame_of E' rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  garr8 SEGS (mrestrict (w_H W3) m) s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) ->
  garr8 SEGS (mrestrict (w_H W3) m') s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)).
Proof.
  intros E' rs m m' H9 H19 H33 Hsk HFr Hg.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0).
  pose proof gb_sbnd as (Hs4096 & Hsceil & _ & Hreq & Hsep & Hsepsh & Hsstk).
  pose proof gb_rowlen as HRL.
  pose proof asan_consts as (C1 & _). pose proof gb_blk as (_ & Hs0 & Hsm).
  apply (garr8_frame SEGS (mrestrict (w_H W3) m)); [exact Hg|].
  intros a Ha. rewrite length_map in Ha. unfold mbyte. rewrite (HFr (Z_to_bv 64 a)).
  - reflexivity.
  - intros Hw. rewrite unsigned_lit_small in Hw by lia.
    destruct (gb_wrange E' rs H9 H19 H33 Hsk a Hw) as [Hsh | Hlit]; unfold GO_LIT in *; lia.
Qed.

Lemma gb_poll_run : forall (E' : env) (rs : YP09.smem) (m m' : word -> option byte),
  ew E' 9 = ew gb_E 9 -> ew E' 19 = ew gb_E 19 -> ew E' 33 = ew gb_E 33 ->
  YP09.skeleton rs = YP09.skeleton gb_rs0 ->
  frame_of E' rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  garr8 SEGS (mrestrict (w_H W3) m) (gF cx fp + GO_POLL) (GBz (Z.of_nat i)) ->
  garr8 SEGS (mrestrict (w_H W3) m') (gF cx fp + GO_POLL) (GBz (Z.of_nat i)).
Proof.
  intros E' rs m m' H9 H19 H33 Hsk HFr Hg.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & _).
  pose proof asan_consts as (C1 & _).
  apply (garr8_frame SEGS (mrestrict (w_H W3) m)); [exact Hg|].
  intros a Ha. rewrite gb_gbz_len in Ha. unfold mbyte. rewrite (HFr (Z_to_bv 64 a)).
  - reflexivity.
  - intros Hw. rewrite unsigned_lit_small in Hw by (unfold GO_POLL in Ha; lia).
    destruct (gb_wrange E' rs H9 H19 H33 Hsk a Hw) as [Hsh | Hlit].
    + apply (gb_sh_nf a Hsh). unfold GO_POLL in Ha. lia.
    + unfold GO_LIT, GO_POLL in *. lia.
Qed.

(* The five shadow bytes of `poll`, read back from the walk's own symbolic state at a
   call: the stores 0x8173c .. 0x81750 left them as chunks of region 0. *)
Lemma gb_sh5_of_state : forall (E' : env) (ss : sstate) (msx : machine_state),
  st_ok SEGS E' ss (restrict (w_H W3) msx) -> ew E' 19 = ew gb_E 19 ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 19%nat) 58 63 58 63
     [YP09.mkChunk 62 (CVal 1 (SLit 2)); YP09.mkChunk 61 (CVal 1 (SLit 0));
      YP09.mkChunk 60 (CVal 1 (SLit 0)); YP09.mkChunk 59 (CVal 1 (SLit 0));
      YP09.mkChunk 58 (CVal 1 (SLit 0))]) ->
  gb_sh5 (ms_mem msx).
Proof.
  intros E' ss msx HS H19 Hnth.
  pose proof gb_B19 as B19. cbn [base_val] in B19.
  destruct (st_ok_region_nth E' ss _ 0%nat _ HS Hnth) as (_ & _ & _ & HC).
  cbn [YP09.r_base YP09.r_chunks base_val] in HC. rewrite H19, B19 in HC.
  inversion HC as [|?? C62 HC1]; subst. inversion HC1 as [|?? C61 HC2]; subst.
  inversion HC2 as [|?? C60 HC3]; subst. inversion HC3 as [|?? C59 HC4]; subst.
  inversion HC4 as [|?? C58 HC5]; subst.
  cbn [ms_mem restrict] in C58, C59, C60, C61, C62.
  apply (gb_cv1 E' (w_H W3) (ms_mem msx) (gSH cx fp) 62 2) in C62; [|lia].
  apply (gb_cv1 E' (w_H W3) (ms_mem msx) (gSH cx fp) 61 0) in C61; [|lia].
  apply (gb_cv1 E' (w_H W3) (ms_mem msx) (gSH cx fp) 60 0) in C60; [|lia].
  apply (gb_cv1 E' (w_H W3) (ms_mem msx) (gSH cx fp) 59 0) in C59; [|lia].
  apply (gb_cv1 E' (w_H W3) (ms_mem msx) (gSH cx fp) 58 0) in C58; [|lia].
  repeat split; assumption.
Qed.

(* The four bytes of the compound literal, read back from the walk's own state: the
   stores 0x8179c .. 0x817b0 through the address in slot 56 left them in region 2. *)
Lemma gb_lit4_of_state : forall (E' : env) (ss : sstate) (msx : machine_state),
  st_ok SEGS E' ss (restrict (w_H W3) msx) -> ew E' 33 = ew gb_E 33 ->
  nth_error (ss_mem ss) 2 = Some (YP09.mkRegion (Some 33%nat) 0 4 0 4
    [YP09.mkChunk 3 (CVal 1 (SLit 0)); YP09.mkChunk 2 (CVal 1 (SLit 5));
     YP09.mkChunk 1 (CVal 1 (SLit 17)); YP09.mkChunk 0 (CVal 1 (SLit 18))]) ->
  forall j, 0 <= j < 4 ->
  aview SEGS (w_H W3) (ms_mem msx) (gF cx fp + GO_LIT + j) = Some (nth (Z.to_nat j) gb_LITz 0).
Proof.
  intros E' ss msx HS H33 Hnth j Hj.
  pose proof gb_B33 as B33. cbn [base_val] in B33.
  destruct (st_ok_region_nth E' ss _ 2%nat _ HS Hnth) as (_ & _ & _ & HC).
  cbn [YP09.r_base YP09.r_chunks base_val] in HC. rewrite H33, B33 in HC.
  inversion HC as [|?? C3 HC1]; subst. inversion HC1 as [|?? C2 HC2]; subst.
  inversion HC2 as [|?? C1 HC3]; subst. inversion HC3 as [|?? C0 HC4]; subst.
  cbn [ms_mem restrict] in C0, C1, C2, C3.
  apply (gb_cv1 E' (w_H W3) (ms_mem msx) _ 3 0) in C3; [|lia].
  apply (gb_cv1 E' (w_H W3) (ms_mem msx) _ 2 5) in C2; [|lia].
  apply (gb_cv1 E' (w_H W3) (ms_mem msx) _ 1 17) in C1; [|lia].
  apply (gb_cv1 E' (w_H W3) (ms_mem msx) _ 0 18) in C0; [|lia].
  assert (Hj4 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
  destruct Hj4 as [-> | [-> | [-> | ->]]]; cbn [gb_LITz nth Z.to_nat Pos.to_nat];
    first [exact C0 | exact C1 | exact C2 | exact C3].
Qed.

(* The five shadow bytes of `poll`, back at 0xf8 (0x817dc .. 0x817ec, s5 = -8), read
   from the walk's own state at the landing. *)
Lemma gb_sh5f_of_state : forall (E' : env) (ss : sstate) (msx : machine_state),
  st_ok_pi SEGS VAL E' ss (restrict (w_H W3) msx) ->
  ew E' 19 = ew gb_E 19 -> ew E' 21 = ew gb_E 21 ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 19%nat) 58 63 58 63
     [YP09.mkChunk 62 (CVal 1 (SOff 21 0)); YP09.mkChunk 61 (CVal 1 (SOff 21 0));
      YP09.mkChunk 60 (CVal 1 (SOff 21 0)); YP09.mkChunk 59 (CVal 1 (SOff 21 0));
      YP09.mkChunk 58 (CVal 1 (SOff 21 0))]) ->
  forall j, (58 <= j < 63)%nat ->
  aview SEGS (w_H W3) (ms_mem msx) (gSH cx fp + Z.of_nat j) = Some 248.
Proof.
  intros E' ss msx HS H19 H21 Hnth j Hj.
  pose proof gb_B19 as B19. cbn [base_val] in B19.
  assert (HU21 : U E' (SOff 21 0) mod 256 = 248).
  { rewrite U_SOff, H21, gb_A21, Z.add_0_r.
    unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    reflexivity. }
  destruct (st_ok_pi_region_nth E' ss _ 0%nat _ HS Hnth) as (_ & _ & _ & HC).
  cbn [YP09.r_base YP09.r_chunks base_val] in HC. rewrite H19, B19 in HC.
  inversion HC as [|?? C62 HC1]; subst. inversion HC1 as [|?? C61 HC2]; subst.
  inversion HC2 as [|?? C60 HC3]; subst. inversion HC3 as [|?? C59 HC4]; subst.
  inversion HC4 as [|?? C58 HC5]; subst.
  cbn [ms_mem restrict] in C58, C59, C60, C61, C62.
  apply (gb_cv1m E' (w_H W3) (ms_mem msx) _ 62 (SOff 21 0) 248) in C62; [|exact HU21 | lia].
  apply (gb_cv1m E' (w_H W3) (ms_mem msx) _ 61 (SOff 21 0) 248) in C61; [|exact HU21 | lia].
  apply (gb_cv1m E' (w_H W3) (ms_mem msx) _ 60 (SOff 21 0) 248) in C60; [|exact HU21 | lia].
  apply (gb_cv1m E' (w_H W3) (ms_mem msx) _ 59 (SOff 21 0) 248) in C59; [|exact HU21 | lia].
  apply (gb_cv1m E' (w_H W3) (ms_mem msx) _ 58 (SOff 21 0) 248) in C58; [|exact HU21 | lia].
  assert (C : (j = 58 \/ j = 59 \/ j = 60 \/ j = 61 \/ j = 62)%nat) by lia.
  destruct C as [-> | [-> | [-> | [-> | ->]]]]; cbn [Z.of_nat Pos.of_succ_nat]; assumption.
Qed.

(* ---- the landing: the machine state at the next cut ---- *)
Lemma gb_land_body : forall (ms' : machine_state) (pc : Z),
  ms_pc_val ms' = Z_to_bv 64 (BASE + pc) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  getr (ms_regs ms') 2 = w64 (c_sp1 cx) -> getr (ms_regs ms') 8 = w64 (spZ (c_regs cx)) ->
  getr (ms_regs ms') 9 = w64 (c_sp1 cx) ->
  getr (ms_regs ms') 3 = getr (c_regs cx) 3 -> getr (ms_regs ms') 4 = getr (c_regs cx) 4 ->
  gb_tkeep (ms_mem ms3) (ms_mem ms') ->
  (forall j, (58 <= j < 63)%nat ->
     aview SEGS (w_H W3) (ms_mem ms') (gSH cx fp + Z.of_nat j) = Some 248) ->
  ge_body cx fp pc W3 ms' GSH_a.
Proof.
  intros ms' pc Hpc Hrv Hsvc Hrom Hfr Hfc G2 G8 G9 G3 G4 HTK H248.
  pose proof HBODY as (_ & _ & _ & _ & _ & _ & _ & HSAVED0 & HSHAD0 & HFLAG0 & HLEN0 & HIN0).
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0). pose proof asan_consts as (C1 & _).
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0lo.
  pose proof HB as (_ & _ & _ & Hpn & _).
  pose proof HBLK as (Ebl & _).
  split; [exact Hpc|]. split; [exact Hrv|]. split; [exact Hsvc|]. split; [exact Hrom|].
  split; [exact Hfr|]. split; [exact Hfc|].
  split; [repeat split; assumption|].
  split.
  { destruct HSAVED0 as (Hra0 & Hsv0). split.
    - apply (gb_rdword_tr (ms_mem ms3)); [exact Hra0|].
      intros x Hx. apply gb_stk_tkeep; [exact HTK | lia].
    - intros j Hj. apply (gb_rdword_tr (ms_mem ms3)); [exact (Hsv0 j Hj)|].
      intros x Hx. apply gb_stk_tkeep; [exact HTK | lia]. }
  split.
  { intros j Hj. rewrite HLEN0 in Hj. unfold GE_NSH in Hj.
    destruct (Nat.lt_ge_cases j 58%nat) as [Hlo | Hge].
    - rewrite (HTK (gSH cx fp + Z.of_nat j));
        [ exact (HSHAD0 j ltac:(rewrite HLEN0; unfold GE_NSH; lia))
        | right; right; left; lia | lia
        | intros HC; apply (gb_sh_nf2 (gSH cx fp + Z.of_nat j) ltac:(lia)); unfold GO_POLL in HC; lia
        | lia
        | intros HC; apply (gb_sh_nf2 (gSH cx fp + Z.of_nat j) ltac:(lia)); unfold GO_LIT in HC; lia ].
    - destruct (Nat.lt_ge_cases j 63%nat) as [Hhi | Hge2].
      + rewrite (H248 j ltac:(lia)).
        assert (C : (j = 58 \/ j = 59 \/ j = 60 \/ j = 61 \/ j = 62)%nat) by lia.
        destruct C as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; reflexivity.
      + rewrite (HTK (gSH cx fp + Z.of_nat j));
        [ exact (HSHAD0 j ltac:(rewrite HLEN0; unfold GE_NSH; lia))
        | right; right; left; lia | lia
        | intros HC; apply (gb_sh_nf2 (gSH cx fp + Z.of_nat j) ltac:(lia)); unfold GO_POLL in HC; lia
        | lia
        | intros HC; apply (gb_sh_nf2 (gSH cx fp + Z.of_nat j) ltac:(lia)); unfold GO_LIT in HC; lia ]. }
  split.
  { apply (gb_rdword_tr (ms_mem ms3)); [exact HFLAG0|].
    intros x Hx. replace x with (gF cx fp + (x - gF cx fp)) by lia.
    apply gb_frm_tkeep; [exact HTK | lia | unfold GO_POLL; lia | unfold GO_LIT; lia]. }
  split; [exact HLEN0|].
  apply (gb_garr8_tr (ms_mem ms3)); [exact HIN0|].
  intros a Ha. rewrite length_map in Ha.
  destruct Hpn as [(Hn0 & _) | (Hn0 & Hin)].
  - exfalso. unfold c_n in Hn0. lia.
  - apply (gb_blk_tkeep (c_p cx) (c_n cx)); [rewrite Ebl; apply in_or_app; left; exact Hin | exact HTK |].
    unfold c_n in *. lia.
Qed.

Lemma gb_land_slot : forall (ms' : machine_state) off v,
  gb_tkeep (ms_mem ms3) (ms_mem ms') -> gslot cx W3 ms3 off v -> 0 <= off <= 184 -> gslot cx W3 ms' off v.
Proof.
  intros ms' off v HTK Hs' Hoff.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof asan_consts as (C1 & _). unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0lo.
  unfold gslot in *. apply (gb_rdword_tr (ms_mem ms3)); [exact Hs'|].
  intros x Hx. apply gb_stk_tkeep; [exact HTK | lia].
Qed.

Lemma gb_land_blk : forall (ms' : machine_state),
  gb_tkeep (ms_mem ms3) (ms_mem ms') -> gsw_blk B cx fp ly3 S3 W3 ms' t s.
Proof.
  intros ms' HTK.
  pose proof HBLK as (Ebl & Hsin & HTAB & HWAS & HSET & HREL & HI1 & SLOTS & Hn26 & Ht0 & Hs0 & Hok & HA0 & HA1).
  destruct (SegSetModel.tables_end_inv (c_pl cx)) as (_ & Hwsl & Hstl & _).
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof asan_consts as (C1 & _). unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0lo.
  assert (FB : forall o v, gfb cx fp W3 ms3 o v -> 0 <= o < 1024 ->
                 ~ (GO_POLL <= o < GO_POLL + 34) -> ~ (GO_LIT <= o < GO_LIT + 4) -> gfb cx fp W3 ms' o v).
  { intros o v Hb Ho Hp Hl. unfold gfb in *. rewrite (gb_frm_tkeep o _ _ HTK Ho Hp Hl). exact Hb. }
  split; [exact Ebl|]. split; [exact Hsin|].
  split.
  { destruct HTAB as (Htin & Ht0' & HTlen & HTb). split; [exact Htin|]. split; [exact Ht0'|].
    split; [exact HTlen|]. intros ii H1 H2 H3 H4.
    rewrite (gb_blk_tkeep t 460 (ms_mem ms3) (ms_mem ms') Htin HTK (t + ii) ltac:(lia)).
    exact (HTb ii H1 H2 H3 H4). }
  split.
  { unfold gfarr in *. apply (gb_garr8_tr (ms_mem ms3)); [exact HWAS|].
    intros a Ha. rewrite length_map, Hwsl in Ha. replace a with (gF cx fp + (a - gF cx fp)) by lia.
    apply gb_frm_tkeep;
      [exact HTK | unfold GO_WAS in *; lia | unfold GO_WAS, GO_POLL in *; lia
       | unfold GO_WAS, GO_LIT in *; lia]. }
  split.
  { unfold gfarr in *. apply (gb_garr8_tr (ms_mem ms3)); [exact HSET|].
    intros a Ha. rewrite length_map, Hstl in Ha. replace a with (gF cx fp + (a - gF cx fp)) by lia.
    apply gb_frm_tkeep;
      [exact HTK | unfold GO_SET in *; lia | unfold GO_SET, GO_POLL in *; lia
       | unfold GO_SET, GO_LIT in *; lia]. }
  split; [exact HREL|]. split; [exact HI1|].
  split.
  { destruct SLOTS as (S8 & S16 & S40 & S48 & S56 & S64 & S72 & S80 & S96 & S104 & S112 & S120 & S128
                       & S136 & S144 & S152).
    unfold gsw_slots.
    repeat (split; [apply (gb_land_slot ms' _ _ HTK); [assumption | lia]|]).
    apply (gb_land_slot ms' _ _ HTK); [assumption | lia]. }
  split; [exact Hn26|]. split; [exact Ht0|]. split; [exact Hs0|]. split; [exact Hok|].
  split; apply FB; try assumption; unfold GO_A, GO_POLL, GO_LIT; lia.
Qed.

Lemma gb_land_rows : forall (ms' : machine_state),
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms')) s
    (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) ->
  gsw_rows cx W3 ms' t s.
Proof. intros ms' Hg. pose proof HROWS as (Hwant & _). split; [exact Hwant | exact Hg]. Qed.

(* The seat: no chunk of the turn's three regions mentions cx, fp or s. *)
Lemma gb_seat : st_ok_pi SEGS VAL gb_E ss_gb0 (restrict (w_H W3) ms3).
Proof.
  pose proof gb_nums as (HFal & HF4096 & HFceil & HFia & ESH & E8 & Hsp0lo & Hsp0hi & Hsp0al & Hsp1al & Hsp1 & Hsp1al16).
  pose proof gb_sep as (HSEP & HSHstk & HFstk & HSH0).
  pose proof gb_B19 as B19. pose proof gb_B9 as B9. pose proof gb_B33 as B33.
  assert (U9 : bv_unsigned (ew gb_E 9%nat) = c_sp1 cx) by (cbn [base_val] in B9; exact B9).
  pose proof HJ as (HAR & _).
  pose proof HBODY as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc & HREGS & _).
  pose proof HBLK as (_ & _ & _ & _ & _ & _ & _ & SLOTS & _).
  pose proof SLOTS as (_ & _ & _ & _ & SL56 & _ & _ & SL80 & _).
  assert (Hfin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR Hfin) as (_ & _ & HFpres & HFSpres).
  rewrite gb_frame_eq in HFpres, HFSpres. fold (gF cx fp) in HFpres, HFSpres.
  change (fs_frame_bytes GE_CID) with 1024 in HFpres. change (fs_frame_bytes GE_CID / 8) with 128 in HFSpres.
  pose proof asan_consts as (C1 & _).
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0lo.
  assert (Ems3 : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GPS_gbhd)) (ms_mem ms3) (seg_rom SEGS)).
  { clear - Hpc Hrv Hsvc Hrom Hfr Hfc. destruct ms3; cbn in *; subst; reflexivity. }
  assert (Hrs : Forall (YP09.region_ok SEGS gb_E (mrestrict (w_H W3) (ms_mem ms3))) gb_rs0).
  { unfold gb_rs0. repeat apply Forall_cons; try apply Forall_nil.
    - unfold YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite B19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      replace (gSH cx fp + o) with (shadow_addr (gF cx fp) + o) by (rewrite ESH; unfold shadow_addr; reflexivity).
      apply (proj1 (HFSpres o ltac:(lia))).
    - apply (gs_slotreg_ok W3 gb_E (ms_mem ms3) _ (c_sp1 cx) 0 0 U9 ltac:(lia) ltac:(lia) ltac:(intros o Ho; lia)).
      repeat apply Forall_cons; try apply Forall_nil.
      + exact (gs_slot_chunk W3 gb_E (ms_mem ms3) 80 32%nat (gF cx fp + GO_POLL) (c_sp1 cx) gb_E32 U9 SL80).
      + exact (gs_slot_chunk W3 gb_E (ms_mem ms3) 56 33%nat (gF cx fp + GO_LIT) (c_sp1 cx) gb_E33 U9 SL56).
      + exact (gs_slot_chunk W3 gb_E (ms_mem ms3) 88 34%nat (2 ^ 64 - 1 - s) (c_sp1 cx) gb_E34 U9 HS88).
    - unfold YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite B33. unfold GO_LIT. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (HFpres (gF cx fp + 544 + o) ltac:(lia))). }
  assert (Hpd : YP09.pairwise_disjoint gb_E gb_rs0).
  { unfold gb_rs0. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B19, B9, B33. unfold GO_LIT.
    repeat split; lia. }
  pose proof (gs_seat W3 (ms_regs ms3) (ms_mem ms3) gb_extra GPS_gbhd gb_rs0 []
     ltac:(vm_compute; reflexivity) Hrs Hpd ltac:(cbn; tauto)) as HS.
  rewrite <- Ems3 in HS. exact HS.
Qed.

(* One turn of the loop, 0x8173c back to 0x8173c (or on to 0x81804 after the sixth). *)
Lemma gb_turn : SRr SEGS W3 (mkCfg ms3 md3) (ge_post B MT cx).
Proof.
  pose proof gb_nums as (HFal & HF4096 & HFceil & HFia & ESH & E8 & Hsp0lo & Hsp0hi & Hsp0al & Hsp1al & Hsp1 & Hsp1al16).
  pose proof gb_sep as (HSEP & HSHstk & HFstk & HSH0).
  pose proof gb_B19 as B19. pose proof gb_B9 as B9. pose proof gb_B33 as B33.
  pose proof asan_consts as (C1 & _). unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0lo.
  pose proof HBODY as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc & HREGS & _).
  pose proof HREGS as (Q2 & Q8 & Q9 & Q3 & Q4).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
  pose proof HIMG as (HTBL & _ & _ & HPin & HGBin & _ & _ & _ & _ & HPlo & HPhi & HGBlo & HGBhi).
  unfold IMG_LO, IMG_HI in HPlo, HPhi, HGBlo, HGBhi.
  assert (Hfin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
  pose proof gb_sbnd as (Hs4096 & Hsceil & Hsapp & Hreq & Hsep & Hsepsh & Hsstk).
  pose proof gb_blk as (Hsin & Hs0 & Hsm).
  pose proof gb_seat as HS.
  assert (HEI : img_env VAL A_LIM gb_E) by apply Eimg_env.
  pose proof HJ as HJ0.
  paj_run_shc RUNP RUNC HS HJ0.
  - apply gb_awr; [reflexivity | reflexivity | reflexivity | vm_compute; reflexivity].
  - (* 0x8175c: reac_ctrl_identity_poll_block(i, poll) *)
    prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
    prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
    rewrite (gb_EE 2%nat 2%bv eq_refl), Q2 in P2.
    rewrite (gb_EE 3%nat 3%bv eq_refl), Q3, Hgp in P3.
    rewrite (gb_EE 4%nat 4%bv eq_refl), Q4, Htp in P4.
    rewrite (gb_EE 18%nat 18%bv eq_refl), R18 in P10.
    rewrite gb_E32 in P11.
    (* the five shadow bytes of `poll` the turn has just written (0x8173c .. 0x81750) *)
    assert (HSH5 : gb_sh5 (ms_mem ms)) by (apply (gb_sh5_of_state _ _ _ HS); [reflexivity | vm_compute; reflexivity]).
    (* the frame at this state *)
    pose proof (proj1 HJ0) as HAR1.
    destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR1 Hfin) as (_ & _ & HFpres1 & _).
    rewrite gb_frame_eq in HFpres1. fold (gF cx fp) in HFpres1.
    change (fs_frame_bytes GE_CID) with 1024 in HFpres1.
    pose proof (ge_F_facts B MT LAWS cx fp W3 ms ly3 S3 _ k HB HJ0 HFR) as (_ & _ & _ & HFimg & _).
    pose proof (gb_ra_of_sh5 _ HSH5) as HRA.
    assert (Hsp : spZ (ms_regs ms) = c_sp1 cx)
      by (unfold spZ; rewrite P2; apply unsigned_lit_small; lia).
    pmkst HS. rewrite pa_sigma_reac_ctrl_identity_poll_block.
    eapply SRr_bind.
    { eapply (TIPB GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
                [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms) _ k (ms_regs ms) (Z.of_nat i) (gF cx fp + GO_POLL) HJ0).
      - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
      - unfold raZ. rewrite P1, unsigned_lit_small by (pose proof pa_B_ok as (HB1 & HB2 & _); lia).
        pose proof pa_base_lo as HBLO. rewrite IMG_LO_B_val in HBLO. lia.
      - exact P3.
      - exact P4.
      - exact P10.
      - lia.
      - exact P11.
      - rewrite Hsp. exact Hsp1al16.
      - rewrite Hsp. unfold STK_reac_ctrl_identity_poll_block, ESTACK, GE_STK, STK_LLVMFuzzerTestOneInput. lia.
      - rewrite Hsp. lia.
      - right. rewrite Hsp. unfold STK_reac_ctrl_identity_poll_block, ESTACK, GO_POLL. lia.
      - (* the destination is the frame's own `poll` *)
        intros a Ha. split; [|split; [|split]].
        + right; right; right. exists GE_CID, fp. split; [left; reflexivity|]. left.
          unfold in_zr. cbn [fst snd]. rewrite gb_frame_eq. fold (gF cx fp).
          change (fs_frame_bytes GE_CID) with 1024. unfold GO_POLL in Ha. lia.
        + exact (proj1 (HFpres1 a ltac:(unfold GO_POLL in Ha; lia))).
        + exact (proj2 (HFpres1 a ltac:(unfold GO_POLL in Ha; lia))).
        + rewrite Hsp. unfold ESTACK, GO_POLL in *. lia.
      - apply (amem_range_sub_app (gF cx fp) 1024); unfold GO_POLL; [exact HFia | lia | lia | lia | lia].
      - exact HRA.
      - apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ GE_CID fp (gF cx fp + GO_POLL) 34 HAR1 Hfin);
          [ rewrite gb_frame_eq; fold (gF cx fp); unfold GO_POLL; lia
          | rewrite gb_frame_eq; fold (gF cx fp); change (fs_frame_bytes GE_CID) with 1024; unfold GO_POLL; lia
          | lia ].
      - unfold GO_POLL. lia.
      - exact (proj2 (proj2 (proj2 (HTBL _ _ (gb_rod _ _ _ HJ0))))).
      - exact HGBin.
      - exact HGBlo.
      - exact HGBhi. }
    cbv beta. intros W' c' Hwle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HKEEP2 & HPOST2).
    assert (Hib : ((0 <=? Z.of_nat i) && (Z.of_nat i <=? 5))%bool = true)
      by (apply andb_true_intro; split; apply Z.leb_le; lia).
    rewrite Hib in HPOST2. destruct HPOST2 as (HA0 & HPOLLB).
    rewrite P1.
    rewrite Hsp in HKEEP2. pose proof (gb_keep_of_tcj _ _ HKEEP2) as HK2. clear HKEEP2.
    pose proof (proj1 HJ2) as HAR2.
    destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR2 Hfin) as (_ & _ & HFpres2 & HFSpres2).
    rewrite gb_frame_eq in HFpres2, HFSpres2. fold (gF cx fp) in HFpres2, HFSpres2.
    change (fs_frame_bytes GE_CID) with 1024 in HFpres2.
    change (fs_frame_bytes GE_CID / 8) with 128 in HFSpres2.
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      let K := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss) in
      jafter_call_keep_hi HS K regs2 (mrestrict (w_H W3) mem2) HP2 [0;1;2]%nat HS2
    end.
    lazymatch type of HS2 with ?Q -> _ => assert (HQ : Q) end.
    { apply gb_kept; try reflexivity.
      - intros a Ha. apply HK2;
          [ right; right; left; lia | lia | intros HC; apply (gb_sh_nf a Ha); unfold GO_POLL in HC; lia ].
      - intros a Ha. apply HK2; [left; lia | lia | unfold GO_POLL; lia].
      - intros a Ha. unfold GO_LIT in Ha. apply HK2; [right; left; lia | lia | unfold GO_POLL; lia].
      - intros a Ha.
        replace a with (shadow_addr (gF cx fp) + (a - gSH cx fp)) by (rewrite ESH; unfold shadow_addr; lia).
        apply (proj1 (HFSpres2 (a - gSH cx fp) ltac:(lia))).
      - intros a Ha. unfold GO_LIT in Ha. apply (proj1 (HFpres2 a ltac:(lia))). }
    specialize (HS2 HQ). clear HQ HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    (* the sweep rows and the five shadow bytes cross the call *)
    assert (HRW : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) s
                    (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
      by (apply (gb_rows_run gb_E (ss_mem ss_gb0) (ms_mem ms3));
          [reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HFr
           | exact (proj2 HROWS)]).
    assert (HTK : gb_tkeep (ms_mem ms3) (ms_mem ms))
      by (refine (gb_tkeep_run gb_E (ss_mem ss_gb0) (ms_mem ms3) (ms_mem ms) _ _ _ _ HFr);
          [reflexivity | reflexivity | reflexivity | vm_compute; reflexivity]).
    assert (HMEM2 : gb_mem mem2).
    { apply (gb_mem_tr (ms_mem ms)); [split; [exact HSH5 | exact HRW]|]. exact HK2. }
    assert (HTK2 : gb_tkeep (ms_mem ms3) mem2)
      by (eapply gb_tkeep_trans; [exact HTK | apply gb_tkeep_of_keep; exact HK2]).
    clear HTK HRW HF HFr HG. rename HTK2 into HTK.
    destruct HMEM2 as (_ & HRW).
    pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS HA0 eq_refl) as HS3.
    clear HS. rename HS3 into HS. norm_ss HS.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HEI2 : img_env VAL A_LIM Ev)
        by (repeat (apply img_env_havoc_hi; [|cbv; lia]); exact HEI)
    end.
    paj_run_shc RUNP RUNC HS HJ2.
    { apply gb_awr; first [gb_ewold | vm_compute; reflexivity]. }
    lazymatch type of HS with context [restrict _ ?msN] => rename msN into msR1 end.
    (* 0x8176c `bltu a1,a0` with a1 = ~s (slot 88), a0 = 34 i + 170: the trap is not taken *)
    psrr_branch_pi RUNP BR HS.
    { exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
      rewrite (U_atom _ 34 (2 ^ 64 - 1 - s)) in Hc by (first [gb_atom gb_E34 | lia]).
      rewrite (U_atom_off _ 24 (34 * Z.of_nat i) 170) in Hc by (first [gb_atom gb_A24 | lia]).
      lia. }
    clear Hc.
    assert (HTKn : gb_tkeep (ms_mem ms3) (ms_mem msR1))
      by (eapply gb_tkeep_trans; [exact HTK | refine (gb_tkeep_run _ _ mem2 _ _ _ _ _ HFr);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]]).
    assert (HRWn : garr8 SEGS (mrestrict (w_H W3) (ms_mem msR1)) s
                     (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
      by (refine (gb_rows_run _ _ mem2 _ _ _ _ _ HFr HRW);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]).
    assert (HPOLLn : garr8 SEGS (mrestrict (w_H W3) (ms_mem msR1)) (gF cx fp + GO_POLL) (GBz (Z.of_nat i)))
      by (refine (gb_poll_run _ _ mem2 _ _ _ _ _ HFr HPOLLB);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]).
    clear HTK HRW HPOLLB HF HFr HG. rename HTKn into HTK. rename HRWn into HRW. rename HPOLLn into HPOLLB.
    paj_run_shc RUNP RUNC HS HJ2.
    { apply gb_awr; first [gb_ewold | vm_compute; reflexivity]. }
    lazymatch type of HS with context [restrict _ ?msN] => rename msN into msB1 end.
    (* 0x81780: bcmp(poll, row 5 + i, 34) *)
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2b. prreg HS (3%bv : bv 5) Q3b.
    prreg HS (4%bv : bv 5) Q4b. prreg HS (10%bv : bv 5) Q10.
    prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    rewrite gb_E32 in Q10.
    rewrite gb_A20, gb_A24 in Q11. unfold w64 in Q11. rewrite alu64_add_lit in Q11.
    rewrite (gb_EE 2%nat 2%bv eq_refl), Q2 in Q2b.
    rewrite (gb_EE 3%nat 3%bv eq_refl), Q3, Hgp in Q3b.
    rewrite (gb_EE 4%nat 4%bv eq_refl), Q4, Htp in Q4b.
    assert (Hsp2 : spZ (ms_regs msB1) = c_sp1 cx)
      by (unfold spZ; rewrite Q2b; apply unsigned_lit_small; lia).
    pose proof (proj1 HJ2) as HAR3.
    destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR3 Hfin) as (_ & _ & HFpres3 & HFSpres3).
    rewrite gb_frame_eq in HFpres3, HFSpres3. fold (gF cx fp) in HFpres3, HFSpres3.
    change (fs_frame_bytes GE_CID) with 1024 in HFpres3.
    change (fs_frame_bytes GE_CID / 8) with 128 in HFSpres3.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ s (sw_mbytes (c_pl cx)) HAR3 Hsin) as (_ & _ & _ & _ & Hspres3 & _).
    assert (HSH5b : gb_sh5 (ms_mem msB1))
      by (apply (gb_sh5_of_state _ _ _ HS); [gb_ewold | vm_compute; reflexivity]).
    assert (HTKn : gb_tkeep (ms_mem ms3) (ms_mem msB1))
      by (eapply gb_tkeep_trans; [exact HTK | refine (gb_tkeep_run _ _ (ms_mem msR1) _ _ _ _ _ HFr);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]]).
    assert (HRWn : garr8 SEGS (mrestrict (w_H W3) (ms_mem msB1)) s
                     (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
      by (refine (gb_rows_run _ _ (ms_mem msR1) _ _ _ _ _ HFr HRW);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]).
    assert (HPOLLn : garr8 SEGS (mrestrict (w_H W3) (ms_mem msB1)) (gF cx fp + GO_POLL) (GBz (Z.of_nat i)))
      by (refine (gb_poll_run _ _ (ms_mem msR1) _ _ _ _ _ HFr HPOLLB);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]).
    clear HTK HRW HPOLLB HF HFr HG. rename HTKn into HTK. rename HRWn into HRW. rename HPOLLn into HPOLLB.
    pmkst HS.
    eapply SRr_bind.
    { eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA GS___interceptor_trampoline_bcmp) ABCMP
                W3 (ms_regs msB1) (ms_mem msB1) GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx)
                (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 _ k
                (gF cx fp + GO_POLL) (s + 170 + 34 * Z.of_nat i) 34
                (c_sp1 cx - spZ (c_regs cx)) _ HJ2).
      - exact Q10.
      - exact Q11.
      - exact Q12.
      - lia.
      - unfold GO_POLL. lia.
      - unfold GO_POLL. lia.
      - lia.
      - lia.
      - rewrite Hsp2. lia.
      - rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
      - lia.
      - unfold ESTACK, GE_STK, STK_LLVMFuzzerTestOneInput. lia.
      - exact Q3b.
      - exact Q4b.
      - exact Q1.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. split.
        + apply (aview_some_of_apresent SEGS).
          apply (proj1 (HFpres3 a ltac:(unfold GO_POLL in Ha; lia))).
        + rewrite Hsp2. unfold ESTACK, GO_POLL in *. lia.
      - intros a Ha. split.
        + apply (aview_some_of_apresent SEGS). apply (proj1 (Hspres3 a ltac:(lia))).
        + rewrite Hsp2. unfold ESTACK. lia.
      - intros a Ha. unfold ESTACK, GO_POLL in *. lia.
      - intros a Ha. unfold ESTACK in *. lia.
      - apply (amem_range_sub_app (gF cx fp) 1024); unfold GO_POLL; [exact HFia | lia | lia | lia | lia].
      - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem msB1) _ s (sw_mbytes (c_pl cx)) _ 34
                 HAR3 Hsin); lia.
      - exact (gb_ra_of_sh5 _ HSH5b).
      - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem msB1) _ GE_CID fp
                           (gF cx fp + GO_POLL) 34 HAR3 Hfin);
          [ rewrite gb_frame_eq; fold (gF cx fp); unfold GO_POLL; lia
          | rewrite gb_frame_eq; fold (gF cx fp); change (fs_frame_bytes GE_CID) with 1024;
            unfold GO_POLL; lia
          | lia ].
      - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem msB1) _ s (sw_mbytes (c_pl cx))
                 _ 34 HAR3 Hsin); lia.
      - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem msB1) _ s
                           (sw_mbytes (c_pl cx)) _ 34 HAR3 Hsin); lia. }
    cbv beta. intros W4 c4 Hwle4 (-> & regs4 & mem4 & md4 & v4 & -> & HJ4 & HP4 & Hv4 & Hcmp4 & Hkp4 & Hpr4).
    (* `poll` and row 5 + i agree, so 0x81784 does not branch to the abort block *)
    assert (Hv40 : v4 = w64 0)
      by (apply Hcmp4; intros j Hj; apply gb_row_eq; [exact HPOLLB | exact HRW | lia]).
    rewrite Hv40 in Hv4.
    assert (HTKn : gb_tkeep (ms_mem ms3) mem4)
      by (eapply gb_tkeep_trans; [exact HTK |
          intros a Ha Aa Bb Cc Dd; apply Hkp4; [apply gb_kat_rng; exact Ha | unfold ESTACK; lia]]).
    assert (HRWn : garr8 SEGS (mrestrict (w_H W3) mem4) s
                     (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
      by (apply (gb_garr8_tr (ms_mem msB1)); [exact HRW|];
          intros a Ha; rewrite length_map in Ha; pose proof gb_rowlen as HRL;
          apply Hkp4; unfold ESTACK; lia).
    clear HTK HRW HPOLLB. rename HTKn into HTK. rename HRWn into HRW.
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      let K := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss) in
      jafter_call_keep_hi HS K regs4 (mrestrict (w_H W3) mem4) HP4 [0;1;2]%nat HS4
    end.
    lazymatch type of HS4 with ?Q -> _ => assert (HQ4 : Q) end.
    { apply gb_kept; try gb_ewold.
      - intros a Ha. apply Hkp4; unfold ESTACK; lia.
      - intros a Ha. apply Hkp4; unfold ESTACK; lia.
      - intros a Ha. apply Hkp4; unfold GO_LIT in Ha; unfold ESTACK; lia.
      - intros a Ha. apply Hpr4.
        replace a with (shadow_addr (gF cx fp) + (a - gSH cx fp)) by (rewrite ESH; unfold shadow_addr; lia).
        apply (proj1 (HFSpres3 (a - gSH cx fp) ltac:(lia))).
      - intros a Ha. apply Hpr4. apply (proj1 (HFpres3 a ltac:(unfold GO_LIT in Ha; lia))). }
    specialize (HS4 HQ4). clear HQ4 HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
    pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS Hv4 eq_refl) as HS5.
    clear HS. rename HS5 into HS. norm_ss HS.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HEI3 : img_env VAL A_LIM Ev)
        by (repeat (apply img_env_havoc_hi; [|cbv; lia]); exact HEI)
    end.
    paj_run_shc RUNP RUNC HS HJ4.
    { apply gb_awr; first [gb_ewold | vm_compute; reflexivity]. }
    lazymatch type of HS with context [restrict _ ?msN] => rename msN into msR2 end.
    (* 0x8178c `bltu a0,s10` with a0 = -17, s10 = s + 170 + 34 i: the trap is not taken *)
    psrr_branch_pi RUNP BR HS.
    { exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
      rewrite U_lit in Hc by lia. rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc.
      rewrite (U_atom _ 20 (s + 170)) in Hc by (first [gb_atom gb_A20 | lia]).
      rewrite (U_atom _ 24 (34 * Z.of_nat i)) in Hc by (first [gb_atom gb_A24 | lia]).
      rewrite zcanon_id in Hc by (unfold M64; lia).
      lia. }
    clear Hc.
    assert (HTKn : gb_tkeep (ms_mem ms3) (ms_mem msR2))
      by (eapply gb_tkeep_trans; [exact HTK | refine (gb_tkeep_run _ _ mem4 _ _ _ _ _ HFr);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]]).
    assert (HRWn : garr8 SEGS (mrestrict (w_H W3) (ms_mem msR2)) s
                     (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
      by (refine (gb_rows_run _ _ mem4 _ _ _ _ _ HFr HRW);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]).
    clear HTK HRW HF HFr HG. rename HTKn into HTK. rename HRWn into HRW.
    paj_run_shc RUNP RUNC HS HJ4.
    { apply gb_awr; first [gb_ewold | vm_compute; reflexivity]. }
    lazymatch type of HS with context [restrict _ ?msN] => rename msN into msB2 end.
    (* 0x817b8: bcmp(row 5 + i + 16, the compound literal 12 11 05 00, 4) *)
    prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3.
    prreg HS (4%bv : bv 5) U4. prreg HS (10%bv : bv 5) U10.
    prreg HS (11%bv : bv 5) U11. prreg HS (12%bv : bv 5) U12.
    rewrite (gb_EE 2%nat 2%bv eq_refl), Q2 in U2.
    rewrite (gb_EE 3%nat 3%bv eq_refl), Q3, Hgp in U3.
    rewrite (gb_EE 4%nat 4%bv eq_refl), Q4, Htp in U4.
    rewrite gb_A23, gb_A24 in U10. unfold w64 in U10. rewrite alu64_add_lit in U10.
    replace (s + 186 + 34 * Z.of_nat i) with (s + 170 + 34 * Z.of_nat i + 16) in U10 by lia.
    rewrite gb_E33 in U11.
    assert (Hsp3 : spZ (ms_regs msB2) = c_sp1 cx)
      by (unfold spZ; rewrite U2; apply unsigned_lit_small; lia).
    pose proof (proj1 HJ4) as HAR5.
    destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR5 Hfin) as (_ & _ & HFpres5 & HFSpres5).
    rewrite gb_frame_eq in HFpres5, HFSpres5. fold (gF cx fp) in HFpres5, HFSpres5.
    change (fs_frame_bytes GE_CID) with 1024 in HFpres5.
    change (fs_frame_bytes GE_CID / 8) with 128 in HFSpres5.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ s (sw_mbytes (c_pl cx)) HAR5 Hsin)
      as (_ & _ & _ & _ & Hspres5 & _).
    assert (HTKn : gb_tkeep (ms_mem ms3) (ms_mem msB2))
      by (eapply gb_tkeep_trans; [exact HTK | refine (gb_tkeep_run _ _ (ms_mem msR2) _ _ _ _ _ HFr);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]]).
    assert (HRWn : garr8 SEGS (mrestrict (w_H W3) (ms_mem msB2)) s
                     (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
      by (refine (gb_rows_run _ _ (ms_mem msR2) _ _ _ _ _ HFr HRW);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]).
    clear HTK HRW HF HFr HG. rename HTKn into HTK. rename HRWn into HRW.
    assert (HL4 : forall j, 0 <= j < 4 ->
              aview SEGS (w_H W3) (ms_mem msB2) (gF cx fp + GO_LIT + j) = Some (nth (Z.to_nat j) gb_LITz 0))
      by (apply (gb_lit4_of_state _ _ _ HS); [gb_ewold | vm_compute; reflexivity]).
    pmkst HS.
    eapply SRr_bind.
    { eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA GS___interceptor_trampoline_bcmp) ABCMP
                W3 (ms_regs msB2) (ms_mem msB2) GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx)
                (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 _ k
                (s + 170 + 34 * Z.of_nat i + 16) (gF cx fp + GO_LIT) 4
                (c_sp1 cx - spZ (c_regs cx)) _ HJ4).
      - exact U10.
      - exact U11.
      - exact U12.
      - lia.
      - lia.
      - lia.
      - unfold GO_LIT. lia.
      - unfold GO_LIT. lia.
      - rewrite Hsp3. lia.
      - rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
      - lia.
      - unfold ESTACK, GE_STK, STK_LLVMFuzzerTestOneInput. lia.
      - exact U3.
      - exact U4.
      - exact U1.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. split.
        + apply (aview_some_of_apresent SEGS). apply (proj1 (Hspres5 a ltac:(lia))).
        + rewrite Hsp3. unfold ESTACK. lia.
      - intros a Ha. split.
        + apply (aview_some_of_apresent SEGS).
          apply (proj1 (HFpres5 a ltac:(unfold GO_LIT in Ha; lia))).
        + rewrite Hsp3. unfold ESTACK, GO_LIT in *. lia.
      - intros a Ha. unfold ESTACK in *. lia.
      - intros a Ha. unfold ESTACK, GO_LIT in *. lia.
      - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem msB2) _ s (sw_mbytes (c_pl cx))
                 _ 4 HAR5 Hsin); lia.
      - apply (amem_range_sub_app (gF cx fp) 1024); unfold GO_LIT; [exact HFia | lia | lia | lia | lia].
      - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem msB2) _ s
                 (sw_mbytes (c_pl cx)) _ 4 HAR5 Hsin); lia.
      - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem msB2) _ s
                           (sw_mbytes (c_pl cx)) _ 4 HAR5 Hsin); lia.
      - apply gb_ra_lit. apply gb_sh68. exact HTK.
      - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem msB2) _ GE_CID fp
                           (gF cx fp + GO_LIT) 4 HAR5 Hfin);
          [ rewrite gb_frame_eq; fold (gF cx fp); unfold GO_LIT; lia
          | rewrite gb_frame_eq; fold (gF cx fp); change (fs_frame_bytes GE_CID) with 1024;
            unfold GO_LIT; lia
          | lia ]. }
    cbv beta.
    intros W6 c6 Hwle6 (-> & regs6 & mem6 & md6 & v6 & -> & HJ6 & HP6 & Hv6 & Hcmp6 & Hkp6 & Hpr6).
    (* bytes 16..19 of the row are the literal, so 0x817bc does not branch to the abort block *)
    assert (Hv60 : v6 = w64 0)
      by (apply Hcmp6; intros j Hj; apply gb_lit_eq; [exact HRW | exact HL4 | lia]).
    rewrite Hv60 in Hv6.
    assert (HTKn : gb_tkeep (ms_mem ms3) mem6)
      by (eapply gb_tkeep_trans; [exact HTK |
          intros a Ha Aa Bb Cc Dd; apply Hkp6; [apply gb_kat_rng; exact Ha | unfold ESTACK; lia]]).
    assert (HRWn : garr8 SEGS (mrestrict (w_H W3) mem6) s
                     (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
      by (apply (gb_garr8_tr (ms_mem msB2)); [exact HRW|];
          intros a Ha; rewrite length_map in Ha; pose proof gb_rowlen as HRL;
          apply Hkp6; unfold ESTACK; lia).
    clear HTK HRW HL4. rename HTKn into HTK. rename HRWn into HRW.
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      let K := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss) in
      jafter_call_keep_hi HS K regs6 (mrestrict (w_H W3) mem6) HP6 [0;1;2]%nat HS6
    end.
    lazymatch type of HS6 with ?Q -> _ => assert (HQ6 : Q) end.
    { apply gb_kept; try gb_ewold.
      - intros a Ha. apply Hkp6; unfold ESTACK; lia.
      - intros a Ha. apply Hkp6; unfold ESTACK; lia.
      - intros a Ha. apply Hkp6; unfold GO_LIT in Ha; unfold ESTACK; lia.
      - intros a Ha. apply Hpr6.
        replace a with (shadow_addr (gF cx fp) + (a - gSH cx fp)) by (rewrite ESH; unfold shadow_addr; lia).
        apply (proj1 (HFSpres5 (a - gSH cx fp) ltac:(lia))).
      - intros a Ha. apply Hpr6. apply (proj1 (HFpres5 a ltac:(unfold GO_LIT in Ha; lia))). }
    specialize (HS6 HQ6). clear HQ6 HS. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
    pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS Hv6 eq_refl) as HS7.
    clear HS. rename HS7 into HS. norm_ss HS.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HEI4 : img_env VAL A_LIM Ev)
        by (repeat (apply img_env_havoc_hi; [|cbv; lia]); exact HEI)
    end.
    paj_run_shc RUNP RUNC HS HJ6.
    { apply gb_awr; first [gb_ewold | vm_compute; reflexivity]. }
    lazymatch type of HS with context [restrict _ ?msN] => rename msN into msR3 end.
    (* 0x817c4 `bltu a0,s10` with a0 = -21, s10 = s + 170 + 34 i: the trap is not taken *)
    psrr_branch_pi RUNP BR HS.
    { exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
      rewrite U_lit in Hc by lia. rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc.
      rewrite (U_atom _ 20 (s + 170)) in Hc by (first [gb_atom gb_A20 | lia]).
      rewrite (U_atom _ 24 (34 * Z.of_nat i)) in Hc by (first [gb_atom gb_A24 | lia]).
      rewrite zcanon_id in Hc by (unfold M64; lia).
      lia. }
    clear Hc.
    assert (HTKn : gb_tkeep (ms_mem ms3) (ms_mem msR3))
      by (eapply gb_tkeep_trans; [exact HTK | refine (gb_tkeep_run _ _ mem6 _ _ _ _ _ HFr);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]]).
    assert (HRWn : garr8 SEGS (mrestrict (w_H W3) (ms_mem msR3)) s
                     (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
      by (refine (gb_rows_run _ _ mem6 _ _ _ _ _ HFr HRW);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]).
    clear HTK HRW HF HFr HG. rename HTKn into HTK. rename HRWn into HRW.
    paj_run_shc RUNP RUNC HS HJ6.
    { apply gb_awr; first [gb_ewold | vm_compute; reflexivity]. }
    lazymatch type of HS with context [restrict _ ?msN] => rename msN into msB3 end.
    (* 0x817d4: bcmp(row 5 + i + 20, POLL + 3 i, 3) *)
    prreg HS (1%bv : bv 5) V1. prreg HS (2%bv : bv 5) V2. prreg HS (3%bv : bv 5) V3.
    prreg HS (4%bv : bv 5) V4. prreg HS (10%bv : bv 5) V10.
    prreg HS (11%bv : bv 5) V11. prreg HS (12%bv : bv 5) V12.
    rewrite (gb_EE 2%nat 2%bv eq_refl), Q2 in V2.
    rewrite (gb_EE 3%nat 3%bv eq_refl), Q3, Hgp in V3.
    rewrite (gb_EE 4%nat 4%bv eq_refl), Q4, Htp in V4.
    rewrite gb_A22, gb_A24 in V10. unfold w64 in V10. rewrite alu64_add_lit in V10.
    replace (s + 190 + 34 * Z.of_nat i) with (s + 170 + 34 * Z.of_nat i + 20) in V10 by lia.
    rewrite gb_A25 in V11.
    assert (Hsp4 : spZ (ms_regs msB3) = c_sp1 cx)
      by (unfold spZ; rewrite V2; apply unsigned_lit_small; lia).
    pose proof (proj1 HJ6) as HAR7.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ s (sw_mbytes (c_pl cx)) HAR7 Hsin)
      as (_ & _ & _ & _ & Hspres7 & _).
    assert (HTKn : gb_tkeep (ms_mem ms3) (ms_mem msB3))
      by (eapply gb_tkeep_trans; [exact HTK | refine (gb_tkeep_run _ _ (ms_mem msR3) _ _ _ _ _ HFr);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]]).
    assert (HRWn : garr8 SEGS (mrestrict (w_H W3) (ms_mem msB3)) s
                     (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
      by (refine (gb_rows_run _ _ (ms_mem msR3) _ _ _ _ _ HFr HRW);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]).
    clear HTK HRW HF HFr HG. rename HTKn into HTK. rename HRWn into HRW.
    (* POLL (object 6) through GSW_IMG, and its shadow through the registered globals *)
    pose proof (proj1 (proj2 (proj2 (HTBL _ _ (gb_rod _ _ _ HJ6))))) as HPT.
    pose proof IMG_LO_B_val as ELO. pose proof IMG_TOP_B_val as ETOP.
    assert (HROP : range_addressable (aview SEGS (w_H W3) (ms_mem msB3)) SHADOW_OFF
                     (VAL (A_OBJ 6) + 3 * Z.of_nat i) 3 /\
                   shadow_hull_vis (aview SEGS (w_H W3) (ms_mem msB3)) (VAL (A_OBJ 6) + 3 * Z.of_nat i) 3).
    { eapply ro_read_ok_glob; [exact HGM | exact HPin | exact HIMGSH | exact HAR7 | lia | lia | lia
        | unfold IMG_LO; lia | unfold IMG_HI; lia]. }
    destruct HROP as (HRAP & HHUP).
    pmkst HS.
    eapply SRr_bind.
    { eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA GS___interceptor_trampoline_bcmp) ABCMP
                W3 (ms_regs msB3) (ms_mem msB3) GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx)
                (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 _ k
                (s + 170 + 34 * Z.of_nat i + 20) (VAL (A_OBJ 6) + 3 * Z.of_nat i) 3
                (c_sp1 cx - spZ (c_regs cx)) _ HJ6).
      - exact V10.
      - exact V11.
      - exact V12.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - rewrite Hsp4. lia.
      - rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
      - lia.
      - unfold ESTACK, GE_STK, STK_LLVMFuzzerTestOneInput. lia.
      - exact V3.
      - exact V4.
      - exact V1.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. split.
        + apply (aview_some_of_apresent SEGS). apply (proj1 (Hspres7 a ltac:(lia))).
        + rewrite Hsp4. unfold ESTACK. lia.
      - intros a Ha. split.
        + destruct (garr8_nthZ SEGS _ _ _ (a - VAL (A_OBJ 6)) HPT ltac:(lia)
                      ltac:(cbn [length POLLz]; lia)) as (Hva & Hra).
          replace (VAL (A_OBJ 6) + (a - VAL (A_OBJ 6))) with a in Hva by lia.
          rewrite (aview_of_val_mem1 SEGS (w_H W3) (ms_mem msB3) _ _ Hva Hra). discriminate.
        + rewrite Hsp4. unfold ESTACK. lia.
      - intros a Ha. unfold ESTACK in *. lia.
      - intros a Ha. unfold ESTACK in *. lia.
      - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem msB3) _ s (sw_mbytes (c_pl cx))
                 _ 3 HAR7 Hsin); lia.
      - unfold amem_range, kLowMemEnd. left. lia.
      - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem msB3) _ s
                 (sw_mbytes (c_pl cx)) _ 3 HAR7 Hsin); lia.
      - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem msB3) _ s
                           (sw_mbytes (c_pl cx)) _ 3 HAR7 Hsin); lia.
      - exact HRAP.
      - intros _. exact HHUP. }
    cbv beta.
    intros W8 c8 Hwle8 (-> & regs8 & mem8 & md8 & v8 & -> & HJ8 & HP8 & Hv8 & Hcmp8 & Hkp8 & Hpr8).
    (* bytes 20..22 of the row are POLL[i], so 0x817d8 does not branch to the abort block *)
    assert (Hv80 : v8 = w64 0)
      by (apply Hcmp8; intros j Hj; apply gb_pollt_eq; [exact HRW | exact HPT | lia]).
    rewrite Hv80 in Hv8.
    assert (HTKn : gb_tkeep (ms_mem ms3) mem8)
      by (eapply gb_tkeep_trans; [exact HTK |
          intros a Ha Aa Bb Cc Dd; apply Hkp8; [apply gb_kat_rng; exact Ha | unfold ESTACK; lia]]).
    assert (HRWn : garr8 SEGS (mrestrict (w_H W3) mem8) s
                     (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
      by (apply (gb_garr8_tr (ms_mem msB3)); [exact HRW|];
          intros a Ha; rewrite length_map in Ha; pose proof gb_rowlen as HRL;
          apply Hkp8; unfold ESTACK; lia).
    clear HTK HRW HPT. rename HTKn into HTK. rename HRWn into HRW.
    destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR7 Hfin) as (_ & _ & HFpres7 & HFSpres7).
    rewrite gb_frame_eq in HFpres7, HFSpres7. fold (gF cx fp) in HFpres7, HFSpres7.
    change (fs_frame_bytes GE_CID) with 1024 in HFpres7.
    change (fs_frame_bytes GE_CID / 8) with 128 in HFSpres7.
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      let K := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss) in
      jafter_call_keep_hi HS K regs8 (mrestrict (w_H W3) mem8) HP8 [0;1;2]%nat HS8
    end.
    lazymatch type of HS8 with ?Q -> _ => assert (HQ8 : Q) end.
    { apply gb_kept; try gb_ewold.
      - intros a Ha. apply Hkp8; unfold ESTACK; lia.
      - intros a Ha. apply Hkp8; unfold ESTACK; lia.
      - intros a Ha. apply Hkp8; unfold GO_LIT in Ha; unfold ESTACK; lia.
      - intros a Ha. apply Hpr8.
        replace a with (shadow_addr (gF cx fp) + (a - gSH cx fp)) by (rewrite ESH; unfold shadow_addr; lia).
        apply (proj1 (HFSpres7 (a - gSH cx fp) ltac:(lia))).
      - intros a Ha. apply Hpr8. apply (proj1 (HFpres7 a ltac:(unfold GO_LIT in Ha; lia))). }
    specialize (HS8 HQ8). clear HQ8 HS. rewrite <- restrict_mkst_fx in HS8. rename HS8 into HS.
    pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS Hv8 eq_refl) as HS9.
    clear HS. rename HS9 into HS. norm_ss HS.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HEI5 : img_env VAL A_LIM Ev)
        by (repeat (apply img_env_havoc_hi; [|cbv; lia]); exact HEI)
    end.
    (* 0x817dc .. 0x81800: `poll` out of scope again, s2 + 1, s8 + 34, s9 + 3, and the test *)
    paj_run_shc RUNP RUNC HS HJ8.
    { apply gb_awr; first [gb_ewold | vm_compute; reflexivity]. }
    lazymatch type of HS with context [restrict _ ?msN] => rename msN into msR4 end.
    assert (HTKn : gb_tkeep (ms_mem ms3) (ms_mem msR4))
      by (eapply gb_tkeep_trans; [exact HTK | refine (gb_tkeep_run _ _ mem8 _ _ _ _ _ HFr);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]]).
    assert (HRWn : garr8 SEGS (mrestrict (w_H W3) (ms_mem msR4)) s
                     (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
      by (refine (gb_rows_run _ _ mem8 _ _ _ _ _ HFr HRW);
          [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]).
    clear HTK HRW HF HFr HG. rename HTKn into HTK. rename HRWn into HRW.
    (* 0x81800 `bne s8,a0` with s8 = 34 (i + 1), a0 = 204 *)
    psrr_branch_pi RUNP BR HS.
    + (* taken: i + 1 < 6, back to the head of the loop *)
      rewrite branch_ne_U in Hc.
      rewrite (U_atom_off _ 24 (34 * Z.of_nat i) 34) in Hc by (first [gb_atom gb_A24 | lia]).
      rewrite U_lit in Hc by lia.
      apply (proj1 (negb_true_iff _)) in Hc. apply (proj1 (Z.eqb_neq _ _)) in Hc.
      assert (Hi5 : (i < 5)%nat) by lia.
      paj_run_to_sh RUNTOP HS HJ8 GPS_gbhd.
      { apply gb_awr; first [gb_ewold | vm_compute; reflexivity]. }
      lazymatch type of HS with context [restrict _ ?msN] => rename msN into msL end.
      assert (HTKn : gb_tkeep (ms_mem ms3) (ms_mem msL))
        by (eapply gb_tkeep_trans; [exact HTK | refine (gb_tkeep_run _ _ (ms_mem msR4) _ _ _ _ _ HFr);
            [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]]).
      assert (HRWn : garr8 SEGS (mrestrict (w_H W3) (ms_mem msL)) s
                       (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
        by (refine (gb_rows_run _ _ (ms_mem msR4) _ _ _ _ _ HFr HRW);
            [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]).
      clear HTK HRW HF HFr HG. rename HTKn into HTK. rename HRWn into HRW.
      pose proof HS as (HfrL & HpcL & HsvcL & HrvL & HfcL & HromL & _).
      cbn [ss_pc abs_ss ss_resv resv_denot] in HpcL, HrvL.
      assert (H248 : forall j, (58 <= j < 63)%nat ->
                aview SEGS (w_H W3) (ms_mem msL) (gSH cx fp + Z.of_nat j) = Some 248)
        by (apply (gb_sh5f_of_state _ _ _ HS); [gb_ewold | gb_ewold | vm_compute; reflexivity]).
      prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4.
      prreg HS (8%bv : bv 5) Z8. prreg HS (9%bv : bv 5) Z9.
      prreg HS (18%bv : bv 5) Y18. prreg HS (19%bv : bv 5) Y19.
      prreg HS (20%bv : bv 5) Y20. prreg HS (21%bv : bv 5) Y21.
      prreg HS (22%bv : bv 5) Y22. prreg HS (23%bv : bv 5) Y23.
      prreg HS (24%bv : bv 5) Y24. prreg HS (25%bv : bv 5) Y25. prreg HS (27%bv : bv 5) Y27.
      rewrite (gb_EE 2%nat 2%bv eq_refl), Q2 in Z2.
      rewrite (gb_EE 3%nat 3%bv eq_refl), Q3 in Z3.
      rewrite (gb_EE 4%nat 4%bv eq_refl), Q4 in Z4.
      rewrite (gb_EE 8%nat 8%bv eq_refl), Q8 in Z8.
      rewrite (gb_EE 9%nat 9%bv eq_refl), Q9 in Z9.
      rewrite gb_A19 in Y19. rewrite gb_A20 in Y20. rewrite gb_A21 in Y21.
      rewrite gb_A22 in Y22. rewrite gb_A23 in Y23. rewrite gb_A27 in Y27.
      rewrite gb_A18 in Y18. unfold w64 in Y18. rewrite (gb_addiw1 (Z.of_nat i) ltac:(lia)) in Y18.
      rewrite gb_A24, unsigned_lit_small in Y24 by lia.
      rewrite gb_A25, unsigned_lit_small in Y25 by lia.
      apply (HLOOP msL _ ltac:(lia) HJ8).
      * apply (gb_land_body msL GPS_gbhd);
          [ exact HpcL | exact HrvL | exact HsvcL | exact HromL | exact HfrL | exact HfcL
          | exact Z2 | exact Z8 | exact Z9 | exact Z3 | exact Z4 | exact HTK | exact H248 ].
      * apply (gb_land_blk msL HTK).
      * apply gb_land_rows. exact HRW.
      * apply (gb_land_slot msL 88 _ HTK HS88). lia.
      * rewrite Y18. unfold w64. f_equal. lia.
      * rewrite Y24. unfold w64. f_equal. lia.
      * exact Y20.
      * exact Y22.
      * exact Y23.
      * exact Y21.
      * rewrite Y25. unfold w64. f_equal. lia.
      * exact Y27.
      * exact Y19.
    + (* not taken: i + 1 = 6, the sixth turn is done; on to the free at 0x81804 *)
      rewrite branch_ne_U in Hc.
      rewrite (U_atom_off _ 24 (34 * Z.of_nat i) 34) in Hc by (first [gb_atom gb_A24 | lia]).
      rewrite U_lit in Hc by lia.
      apply (proj1 (negb_false_iff _)) in Hc. apply (proj1 (Z.eqb_eq _ _)) in Hc.
      paj_run_to_sh RUNTOP HS HJ8 GPS_free1.
      { apply gb_awr; first [gb_ewold | vm_compute; reflexivity]. }
      lazymatch type of HS with context [restrict _ ?msN] => rename msN into msL end.
      assert (HTKn : gb_tkeep (ms_mem ms3) (ms_mem msL))
        by (eapply gb_tkeep_trans; [exact HTK | refine (gb_tkeep_run _ _ (ms_mem msR4) _ _ _ _ _ HFr);
            [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]]).
      clear HTK HF HFr HG. rename HTKn into HTK.
      pose proof HS as (HfrL & HpcL & HsvcL & HrvL & HfcL & HromL & _).
      cbn [ss_pc abs_ss ss_resv resv_denot] in HpcL, HrvL.
      assert (H248 : forall j, (58 <= j < 63)%nat ->
                aview SEGS (w_H W3) (ms_mem msL) (gSH cx fp + Z.of_nat j) = Some 248)
        by (apply (gb_sh5f_of_state _ _ _ HS); [gb_ewold | gb_ewold | vm_compute; reflexivity]).
      prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4.
      prreg HS (8%bv : bv 5) Z8. prreg HS (9%bv : bv 5) Z9.
      prreg HS (19%bv : bv 5) Y19. prreg HS (27%bv : bv 5) Y27.
      rewrite (gb_EE 2%nat 2%bv eq_refl), Q2 in Z2.
      rewrite (gb_EE 3%nat 3%bv eq_refl), Q3 in Z3.
      rewrite (gb_EE 4%nat 4%bv eq_refl), Q4 in Z4.
      rewrite (gb_EE 8%nat 8%bv eq_refl), Q8 in Z8.
      rewrite (gb_EE 9%nat 9%bv eq_refl), Q9 in Z9.
      rewrite gb_A19 in Y19. rewrite gb_A27 in Y27.
      apply (HEXIT msL _ HJ8).
      * apply (gb_land_body msL GPS_free1);
          [ exact HpcL | exact HrvL | exact HsvcL | exact HromL | exact HfrL | exact HfcL
          | exact Z2 | exact Z8 | exact Z9 | exact Z3 | exact Z4 | exact HTK | exact H248 ].
      * apply (gb_land_blk msL HTK).
      * exact Y27.
      * exact Y19.
Qed.

End t.

(* ---- the loop: induction on the turns that remain, 6 - i ---- *)
Lemma gb_loop :
  ge_from B MT (ge_post B MT) (GIS_free1 B MT) ->
  forall (n : nat) (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) (t s : Z) (i : nat),
  (6 - i <= n)%nat ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  ge_body cx fp GPS_gbhd W3 ms3 GSH_a -> k <= 2 -> acc <= GE_A2 MT - mo_free MT ->
  gsw_blk B cx fp ly3 S3 W3 ms3 t s -> gsw_rows cx W3 ms3 t s ->
  gslot cx W3 ms3 88 (2 ^ 64 - 1 - s) ->
  (i <= 5)%nat ->
  getr (ms_regs ms3) 18 = w64 (Z.of_nat i) ->
  getr (ms_regs ms3) 24 = w64 (34 * Z.of_nat i) ->
  getr (ms_regs ms3) 20 = w64 (s + 170) ->
  getr (ms_regs ms3) 22 = w64 (s + 190) ->
  getr (ms_regs ms3) 23 = w64 (s + 186) ->
  getr (ms_regs ms3) 21 = w64 (-8) ->
  getr (ms_regs ms3) 25 = w64 (VAL (A_OBJ 6) + 3 * Z.of_nat i) ->
  getr (ms_regs ms3) 27 = w64 s -> getr (ms_regs ms3) 19 = w64 (gSH cx fp) ->
  SRr SEGS W3 (mkCfg ms3 md3) (ge_post B MT cx).
Proof.
  intros HF n. induction n as [|n IH];
    intros cx fp k acc ly3 S3 W3 ms3 md3 t s i Hn HB HJ HFR HMO HBODY Hk2 Hacc HBLK HROWS HS88 Hi
      R18 R24 R20 R22 R23 R21 R25 R27 R19.
  - lia.
  - eapply gb_turn with (t := t) (s := s) (i := i); try eassumption.
    + intros ms' md' Hi' HJ' HBODY' HBLK' HROWS' HS88' R18' R24' R20' R22' R23' R21' R25' R27' R19'.
      exact (IH cx fp k acc ly3 S3 W3 ms' md' t s (S i) ltac:(lia) HB HJ' HFR HMO HBODY' Hk2 Hacc
               HBLK' HROWS' HS88' Hi' R18' R24' R20' R22' R23' R21' R25' R27' R19').
    + intros ms' md' HJ' HBODY' HBLK' R27' R19'.
      exact (HF cx fp k acc ly3 S3 W3 ms' md' HB HJ' HFR HMO
               (ex_intro _ t (ex_intro _ s (conj HBODY' (conj Hk2 (conj Hacc (conj HBLK' (conj R27' R19')))))))).
Qed.

End c.
End b.
End a.

Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section zb.
Context {PI : PAImg grant_listing}.

(* The segment. Beyond SEG_gb's own premises it takes the callee's contract; every premise
   of that contract at 0x8175c is discharged inside gb_turn from the side-stack frame's
   own facts, the five shadow stores and GSW_IMG. *)
Lemma gsw_seg_gb : forall (B : asyms) (MT : ameter_ops),
  GrantBContracts.tb_reac_ctrl_identity_poll_block_spec B -> @SEG_gb fx rc SK PI B MT.
Proof.
  intros B MT TIPB RT HIMG HF.
  destruct RT as (LAWS & TL & TLF & ML & MTL & MTF & AMALLOC4 & AFREE4 & ABCMP & HIMGSH & HGL & RO).
  intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGIS.
  destruct HGIS as (t & s & i & HBODY & Hk2 & Hacc & HBLK & HROWS & HS88 & Hi
                    & R18 & R24 & R20 & R22 & R23 & R21 & R25 & R27 & R19).
  eapply gb_loop with (n := (6 - i)%nat) (t := t) (s := s) (i := i); first [eassumption | lia].
Qed.

End zb.
End z.
