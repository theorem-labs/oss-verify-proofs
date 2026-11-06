(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedTurnCr), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AF0s.v. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedTurnD), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACa1.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySchedTurnCr.v and lib/A/Prog/GrantEntrySchedTurnD.v. *)
(* The image-B (UBSan) walk of segment Cr of the frame-loop turn of
   LLVMFuzzerTestOneInput, over image B's own addresses, registers, spill slots and UBSan guards; the shape is
   image A's.
   Ported from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySchedTurnCr.v and
   proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySchedTurnD.v at e6bd82f51c9. *)
(* The frame-loop turn of LLVMFuzzerTestOneInput (image B, entry 0x80a3c), segment Cr: 0x81c1c (GP_effr, the
   return of reac_headamp_tx_effective) .. 0x81c48 (GP_scn), eleven slots (LLVMFEntrySchedTurnDefs.v):

     81c1c  bne  s4,a0,0x81d98   v <> eff T' t c p -> abort
     81c20  ld   a0,0x70(s1)     slot 112 = &param
     81c24  lbu  a3,0(a0)        a3 := param (a byte, 0..255 on its face)
     81c28  bltu s11,a3,0x81c48  2 < a3 -> past the call
     81c2c  ld   a0,0x60(s1)     slot 96 = &value
     81c30  lbu  s4,0(a0)        s4 := value
     81c34  lbu  a2,0(s6)        a2 := ch
     81c38  ld   a0,0x88(s1)     slot 136 = &was_set
     81c3c  ld   a1,0x80(s1)     slot 128 = &set_to
     81c40  jal  want_of         want_of(was_set, set_to, ch, param)
     81c44  bne  s4,a0,0x81d98   v <> want_of's answer -> abort

   It proves `segCr : seg_Cr_ok B MT POST`: from any state the cut TCr describes, the run reaches the cut TE at
   0x81c48 with the whole record body (trec) intact, given want_of's contract (GrantBContracts.tb_want_of_spec).
   The two aborts are refuted by HeadampSched.frame_ok's clauses for the record next_model emitted; the guard at
   0x81c28 is refuted by frame_ok's 0 <= p < 3 for the byte at &param, which trec carries (gfb .. GO_PAR p), so
   the walk reaches the call on the fall-through only, where the byte is at most 2.

   WHAT IMAGE B DOES AND IMAGE A DOES NOT: image A reads was_set / set_to in line, each read behind its own
   shadow check (its segment Cr, 0x8162c .. 0x816ac), and calls reac_headamp_default for an unset cell (its
   segment D, 0x816a4 .. 0x816ac). Image B calls want_of, which does both inside itself, so this one segment
   is the twin of image A's Cr and D together: the two inline shadow checks of image A's Cr (its SHCr entries)
   become want_of's two shadow premises (cr_arr_usable), and image A's D's call of reac_headamp_default
   becomes the call of want_of (wo_call, the twin of image A's hd_call). Both images have the guard on the
   re-read param byte (image A: `bltu s11,a0` at 0x81634, image B: `bltu s11,a3` at 0x81c28). Image A lets
   the engine decide it from an atom fact 0 <= p <= 2; here the state carries only the byte range 0..255 and
   the walk splits the guard and refutes its taken side by hand, so that the bound want_of needs comes from
   the fall-through. Image B keeps &param in slot 112 and &value in slot 96 (image A: s5 and slot 128), the
   value in s4 (A: s3), &ch in s6 (A: slot 104), &was_set in slot 136 and &set_to in slot 128 (A: 144 and
   136), and the parameter bound 2 in s11 (A: s11). *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
(* val_mem1_of_aview; image-independent (its closure is Stdlib, LPS and lib/Reusable), as LLVMFEntrySeat.v says. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC85 GrantFrame YC1h YC1g ACj1 GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantBContracts LLVMFEntryDefs LLVMFEntrySeat LLVMFEntrySchedTurnDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel NextModel GrantModel SlotNeeds_c GrantSlotPlan HeadampSched SegSetModel Seg_sched_turn HeadampLayout.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- the symbolic state at 0x81c1c ----
   Atoms past the registers: 32 = ch, 33 = param. s4 (atom 20) holds the value. The run reads the spill slots
   96, 112, 128 and 136 through s1 (atom 9) and the three one-byte cells through s6 (atom 22, = F + 784):
   ch at s6 + 0, param at s6 + 16, value at s6 + 32. Every region is read-only: the segment writes no memory.
   Each atom carries only the byte range its load gives (0..255); the bound 0 <= param < 3 is NOT a fact of the
   state, so the engine cannot decide the guard at 0x81c28 and the walk refutes it by hand. *)
Definition cellc (n : nat) (o : Z) (a : nat) : YP09.region :=
  YP09.mkRegion (Some n) o (o + 1) 0 0 [YP09.mkChunk o (CVal 1 (SOff a 0))].
(* The spill slots the run reads: &value (96), &param (112), &set_to (128) and &was_set (136), each as an
   offset from &ch in s6. *)
Definition stkCr : YP09.region := YP09.mkRegion (Some 9%nat) 96 144 0 0
  [YP09.mkChunk 96 (CVal 8 (SOff 22 32)); YP09.mkChunk 112 (CVal 8 (SOff 22 16));
   YP09.mkChunk 128 (CVal 8 (SOff 22 (-544))); YP09.mkChunk 136 (CVal 8 (SOff 22 (-752)))].
Definition rsCr : YP09.smem := [stkCr; cellc 22 16 33; cellc 22 32 20; cellc 22 0 32].
Definition GCr : facts := mkFacts [(20%nat, mkAF 0 255 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)] [] [].

(* The shadow bytes of was_set (frame shadow bytes 4..21) and set_to (30..47) while a turn runs. *)
Lemma GSH_turn_tables : forallb (fun j => Z.eqb (nth j GSH_turn 0) 0) (seq 4 18 ++ seq 30 18) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma GSH_turn_zero : forall j, 4 <= j < 22 \/ 30 <= j < 48 -> nth (Z.to_nat j) GSH_turn 0 = 0.
Proof.
  intros j Hj. pose proof GSH_turn_tables as Hb. rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat j) ltac:(apply in_app_iff; destruct Hj; [left | right]; apply in_seq; lia)).
  apply Z.eqb_eq in Hb. exact Hb.
Qed.

Ltac cr_pow := repeat match goal with |- context [2 ^ (8 * Z.of_N ?n)] =>
  let r := eval vm_compute in (2 ^ (8 * Z.of_N n)) in change (2 ^ (8 * Z.of_N n)) with r end.

(* A branch condition as an arithmetic fact on the atoms' values. *)
Ltac cr_hc Hc :=
  rewrite ?branch_ne_U, ?branch_eq_U, ?branch_ltu_U, ?branch_geu_U in Hc; unfold U in Hc;
  rewrite ?ge_sv_SOff0 in Hc;
  repeat (rewrite ew_ewset_other in Hc by lia);
  repeat match goal with H : ew ?Ex ?n = w64 _ |- _ => match type of Hc with context [ew Ex n] => rewrite H in Hc end end;
  cbn [sv_denot] in Hc; unfold w64 in Hc; rewrite ?unsigned_lit_small in Hc by lia;
  first [ apply negb_true_iff, Z.eqb_neq in Hc | apply negb_false_iff, Z.eqb_eq in Hc
        | apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc
        | apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc ].

Ltac cr_awr_ro := lazymatch goal with |- awr_ok ?E0 ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' a1 a2 a3 a4 a5 a6 a7) end;
  repeat (first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

(* A run whose regions are read-only keeps every byte. *)
Lemma cr_kept_ro : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forallb (fun r => Z.leb (YP09.r_whi r) (YP09.r_wlo r)) rs = true ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' HF Hro a. rewrite (aview_wrap H m' a), (aview_wrap H m a).
  apply (aview_kept_out E rs H m m' HF); [apply Z.mod_pos_bound; lia|].
  intros (r & Hin & Ha). rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

Lemma cellc_ok : forall E m n o a b x, bv_unsigned (ew E n) = b -> bv_unsigned (ew E a) = x -> 0 <= x < 256 ->
  0 <= b + o -> b + o + 1 <= 2 ^ 64 -> val_mem SEGS m (b + o) 1 x -> region_ok SEGS E m (cellc n o a).
Proof.
  intros E m n o a b x Hb Ha Hx H0 H1 Hv. unfold region_ok, cellc.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
  split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E m b o 1 (SOff a 0) x).
  - rewrite ge_sv_SOff0, <- Ha. symmetry. apply Z_to_bv_bv_unsigned.
  - cbn. lia.
  - cbn. lia.
  - exact Hv.
Qed.

(* The byte j of was_set or set_to is marked usable in the frame's shadow while a turn runs: the shadow
   premises of want_of (GrantBContracts.v tb_want_of_spec), from the zero shadow bytes 4..21 and 30..47 of
   GSH_turn. This replaces image A's two inline shadow entries (34, 0, 1) and (34, 208, 209). *)
Lemma cr_arr_usable : forall cx fp W3 ms3 off j,
  gshadow cx fp W3 ms3 GSH_turn -> gF cx fp mod 64 = 0 -> gSH cx fp = SHADOW_OFF + gF cx fp / 8 ->
  (off = GO_WAS \/ off = GO_SET) -> 0 <= j < 144 ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (gF cx fp + off + j) 1.
Proof.
  intros cx fp W3 ms3 off j Hsh H64 HSH Hoff Hj x Hx.
  assert (Ex : x = gF cx fp + off + j) by lia. subst x.
  assert (Hg8 : gF cx fp mod 8 = 0).
  { rewrite (Z.div_mod (gF cx fp) 64) by lia. rewrite H64, Z.add_0_r.
    replace (64 * (gF cx fp / 64)) with ((8 * (gF cx fp / 64)) * 8) by lia. apply Z_mod_mult. }
  assert (Ejj : (gF cx fp + off + j) / 8 = gF cx fp / 8 + (off + j) / 8).
  { rewrite (Z.div_mod (gF cx fp) 8) at 1 by lia. rewrite Hg8, Z.add_0_r.
    replace (8 * (gF cx fp / 8) + off + j) with ((off + j) + (gF cx fp / 8) * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  assert (Hjr : 4 <= (off + j) / 8 < 22 \/ 30 <= (off + j) / 8 < 48).
  { destruct Hoff as [-> | ->]; unfold GO_WAS, GO_SET; [left | right]; split;
      first [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
  exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. rewrite Ejj.
  pose proof (Hsh (Z.to_nat ((off + j) / 8))) as Hs.
  rewrite Z2Nat.id in Hs by lia.
  replace (SHADOW_OFF + (gF cx fp / 8 + (off + j) / 8)) with (gSH cx fp + (off + j) / 8) by lia.
  rewrite Hs by (rewrite GSH_turn_len; unfold GE_NSH; lia).
  rewrite GSH_turn_zero by exact Hjr. reflexivity.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis WOF : GrantBContracts.tb_want_of_spec B.
Variable POST : ecx -> world SEGS -> config -> Prop.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* The names of LLVMFEntrySchedTurnDefs.v at this section's asyms, meter and laws. *)
#[local] Notation tbody := (tbody B MT).
#[local] Notation tcom := (tcom B MT).
#[local] Notation GSn := (GSn B MT).
#[local] Notation TB := (TB B MT).
#[local] Notation trec := (trec B MT).
#[local] Notation TC := (TC B MT).
#[local] Notation TCr := (TCr B MT).
#[local] Notation TE := (TE B MT).
#[local] Notation TF := (TF B MT).
#[local] Notation gtracked := (gtracked B).
#[local] Notation gctx := (gctx B MT LAWS).
#[local] Notation gaddr_ok := (gaddr_ok B).
#[local] Notation ginput_ok := (ginput_ok B MT LAWS).
#[local] Notation tbody_keep := (tbody_keep B MT).
#[local] Notation tcom_keep := (tcom_keep B MT).
#[local] Notation gpres := (gpres B MT LAWS).
#[local] Notation gtracked_rng := (gtracked_rng B MT LAWS).
#[local] Notation table_out := (table_out B MT LAWS).
#[local] Notation gtab_keep := (gtab_keep B).
#[local] Notation GI_sched_of := (GI_sched_of B MT).
#[local] Notation tcom_of_GI_sched := (tcom_of_GI_sched B MT).
#[local] Notation GI_freeT_of := (GI_freeT_of B MT).
#[local] Notation table_sep := (table_sep B LAWS).
#[local] Notation table_new := (table_new B LAWS).
#[local] Notation garo := (garo B MT).
#[local] Notation gtab_obj := (gtab_obj B).
#[local] Notation obj_gtab := (obj_gtab B).

(* The call of want_of(was_set, set_to, c, p) at 0x81c40, made from the realigned stack pointer with the return
   address 0x81c44 (listing offset 0x1208): a0 comes back as want_of's answer, the layout, the blocks and the
   world are as they were, and both journals go on (the entry function's and the callee's own, whose frame
   clauses say what the callee kept). The twin of image A's hd_call (GrantEntrySchedTurnD.v), for the contract
   GrantBContracts.tb_want_of_spec. Every premise of the contract but its two bounds on c and p is discharged
   here from the frame's geometry; the two bounds are this lemma's premises because the CALLER derives them:
   segCr below proves 0 <= c < 48 from HeadampSched.frame_ok and 0 <= p < 3 from its own branch at 0x81c28. *)
Lemma wo_call : forall cx fp k ly3 S3 W3 (regsT : bvmap 5 word) memT mdT c p,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 memT mdT k ->
  frames S3 = [(GE_CID, fp)] ->
  getr regsT 2 = w64 (c_sp1 cx) -> getr regsT 3 = getr (c_regs cx) 3 -> getr regsT 4 = getr (c_regs cx) 4 ->
  getr regsT 8 = w64 (spZ (c_regs cx)) ->
  getr regsT 1 = w64 (BASE + 0x1208) ->
  rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  getr regsT 10 = w64 (gF cx fp + GO_WAS) -> getr regsT 11 = w64 (gF cx fp + GO_SET) ->
  getr regsT 12 = w64 c -> getr regsT 13 = w64 p ->
  0 <= c < 48 -> 0 <= p < 3 ->
  garr8 SEGS (mrestrict (w_H W3) memT) (gF cx fp + GO_WAS)
    (map (fun b : byte => bv_unsigned b) (GrantSlotPlan.ws_end (c_pl cx))) ->
  garr8 SEGS (mrestrict (w_H W3) memT) (gF cx fp + GO_SET)
    (map (fun b : byte => bv_unsigned b) (GrantSlotPlan.st_end (c_pl cx))) ->
  range_addressable (aview SEGS (w_H W3) memT) SHADOW_OFF (gF cx fp + GO_WAS + (3 * c + p)) 1 ->
  range_addressable (aview SEGS (w_H W3) memT) SHADOW_OFF (gF cx fp + GO_SET + (3 * c + p)) 1 ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_want_of)) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (getr regsT 1) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
         [(GE_CID, fp)] ly3 S3 W3 mem2 md2 k /\
       ajournal SEGS B STK_want_of (c_sp1 cx) [] ly3 S3 W3 memT mdT [] ly3 S3 W3 mem2 md2 0 /\
       aregs_preserved regsT regs2 /\
       getr regs2 10 = w64 (if HeadampModel.tb (GrantSlotPlan.ws_end (c_pl cx)) (3 * c + p) =? 0
                            then HeadampModel.dflt p
                            else HeadampModel.tb (GrantSlotPlan.st_end (c_pl cx)) (3 * c + p))).
Proof.
  intros cx fp k ly3 S3 W3 regsT memT mdT c p HB HJ Hfr R2 R3 R4 R8 R1 H8 H16 R10 R11 R12 R13 Hc Hp
    HWS HST HWsh HVsh.
  destruct (gctx cx fp k ly3 S3 W3 memT mdT HB HJ Hfr)
    as (EFA & HF4096 & HFceil & HFapp & HF64 & HSH & Hceil & H47 & Hal16 & Hsp1 & Hsp32).
  pose proof HB as ((_ & _ & _ & Hgp & Htp & _) & _).
  pose proof HJ as (HAR3 & HLY & _ & _ & _ & _ & _ & _ & J9 & _).
  pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (L := grant_listing)) as HBLO.
  rewrite IMG_LO_B_val in HBLO.
  assert (GS : GE_STK = 32768) by reflexivity.
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (USP : spZ regsT = c_sp1 cx) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
  assert (US0 : s0Z regsT = spZ (c_regs cx)) by (unfold s0Z; rewrite R8; apply unsigned_lit_small; lia).
  assert (Ho : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
  { dm (c_sp1 cx) 32. dm (spZ (c_regs cx)) 16. dm (c_sp1 cx - spZ (c_regs cx)) 16. lia. }
  (* the two tables of the frame: lengths, and their place against the image, the stack and each other *)
  pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (_ & Lws & Lst & _).
  (* Image B's own image range, through YC1h.v:131 frm_off_imgB (image A's frm_off_imgP carries image A's
     top 0x5fa000; on the integration tree off_img is lib/B/YCbq.v's, over image B's top 0x5fb000; the walk does
     not depend on which). *)
  pose proof (frm_off_imgB B ly3 S3 W3 memT mdT GE_CID fp HAR3 Hfin) as HFo. rewrite EFA, fsb4 in HFo.
  rewrite IMG_LO_B_val, IMG_TOP_B_val in HFo.
  assert (HW0 : 0 <= gF cx fp + GO_WAS) by (unfold GO_WAS; lia).
  assert (HV0 : 0 <= gF cx fp + GO_SET) by (unfold GO_SET; lia).
  assert (HWam : amem_range (gF cx fp + GO_WAS) 144)
    by (apply (amem_range_sub_app (gF cx fp) 1024); first [exact HFapp | exact HFceil | unfold GO_WAS; lia]).
  assert (HVam : amem_range (gF cx fp + GO_SET) 144)
    by (apply (amem_range_sub_app (gF cx fp) 1024); first [exact HFapp | exact HFceil | unfold GO_SET; lia]).
  assert (HWimg : gF cx fp + GO_WAS + 144 <= IMG_LO_B \/ IMG_TOP_B <= gF cx fp + GO_WAS)
    by (rewrite IMG_LO_B_val, IMG_TOP_B_val; unfold GO_WAS; lia).
  assert (HVimg : gF cx fp + GO_SET + 144 <= IMG_LO_B \/ IMG_TOP_B <= gF cx fp + GO_SET)
    by (rewrite IMG_LO_B_val, IMG_TOP_B_val; unfold GO_SET; lia).
  (* GO_WAS + 144 = 176 <= 240 = GO_SET *)
  assert (HWV : gF cx fp + GO_WAS + 144 <= gF cx fp + GO_SET \/ gF cx fp + GO_SET + 144 <= gF cx fp + GO_WAS)
    by (left; unfold GO_WAS, GO_SET; lia).
  (* the frame lies below the callee's stack window: F + 1024 <= alloc_ceiling <= s1 - ESTACK *)
  assert (HWsp : spZ regsT <= gF cx fp + GO_WAS \/ gF cx fp + GO_WAS + 144 <= spZ regsT - STK_want_of)
    by (right; rewrite USP; unfold STK_want_of, ESTACK, GO_WAS; lia).
  assert (HVsp : spZ regsT <= gF cx fp + GO_SET \/ gF cx fp + GO_SET + 144 <= spZ regsT - STK_want_of)
    by (right; rewrite USP; unfold STK_want_of, ESTACK, GO_SET; lia).
  eapply SRr_mono.
  { apply (cl_callS B LAWS W3 regsT memT _ GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
      (c_md cx) [(GE_CID, fp)] ly3 S3 mdT k STK_want_of [] 0 (c_sp1 cx - spZ (c_regs cx)) (getr regsT 1) (gch cx)
      (fun ly' S' W' regs' mem' md' => ly' = ly3 /\ S' = S3 /\ W' = W3 /\
         getr regs' 10 = w64 (if HeadampModel.tb (GrantSlotPlan.ws_end (c_pl cx)) (3 * c + p) =? 0
                              then HeadampModel.dflt p
                              else HeadampModel.tb (GrantSlotPlan.st_end (c_pl cx)) (3 * c + p))) HJ).
    - rewrite USP. lia.
    - exact Ho.
    - lia.
    - unfold STK_want_of, ESTACK. lia.
    - unfold STK_want_of, ESTACK. lia.
    - rewrite R3. exact Hgp.
    - rewrite R4. exact Htp.
    - reflexivity.
    - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
      rewrite US0. apply (achain_ly_top (c_ly cx)); [destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|].
      apply (ge_achain B MT cx HB); [intros a Ha; apply J9; lia | exact H8 | exact H16 | lia].
    - intros HPRE'.
      exact (WOF ly3 S3 W3 regsT memT mdT (gch cx) (gF cx fp + GO_WAS) (gF cx fp + GO_SET) c p
        (GrantSlotPlan.ws_end (c_pl cx)) (GrantSlotPlan.st_end (c_pl cx)) HPRE' R10 R11 R12 R13 Hc Hp
        Lws HWS Lst HST HW0 HWam HWimg HV0 HVam HVimg HWV HWsp HVsp HWsh HVsh).
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & (-> & -> & -> & H10)).
  split; [reflexivity|]. exists regs2, mem2, md2.
  split; [reflexivity|]. split; [rewrite Z.add_0_r in HJ2; exact HJ2|].
  split; [replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJc by lia; exact HJc|].
  split; [exact HP | exact H10].
Qed.

(* 0x81c1c .. 0x81c48: the value against reac_headamp_tx_effective, the guard on param, the call of want_of
   and the value against its answer. *)
Lemma segCr : seg_Cr_ok B MT POST.
Proof.
  intros m HTE cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr HMLE
    (i & t & T & us & c & p & v & T' & (HT & Hm & Hsch & Hnx & Htab & Hlus & Hus & Cc & Cp & Cv) & R10 & R20).
  destruct (gctx cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr)
    as (EFA & HF4096 & HFceil & HFapp & HF64 & HSH & Hceil & H47 & Hal16 & Hsp1 & Hsp32).
  pose proof HT as (HTB0 & Hi & R21).
  pose proof HTB0 as (HBD & Hk & Hacc & Hbl & Hn & R18 & R19 & R22 & R23 & R24 & R25 & R26 & R27 & HSC & HSL & HWS & HST & HH).
  pose proof (ginput_ok cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfr Hbl) as HIN.
  pose proof HBD as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfc & HG & HSV & HSHW & HFL & Hlen & HINP).
  pose proof HG as (G2 & G8 & G9 & G3 & G4).
  pose proof HSL as (L8 & L40 & L64 & L72 & L80 & L88 & L96 & L112 & L128 & L136 & L144 & L152).
  pose proof Htab as (Hint & Ht0 & HTl & HTb).
  pose proof asan_consts as (C1 & _).
  assert (GS : GE_STK = 32768) by reflexivity.
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  (* the five checks of the frame (HeadampSched.v:162-173) for the record next_model emitted at this turn *)
  pose proof (HeadampSched.frame_ok (c_pl cx) t i Ht0) as FO.
  revert FO. destruct (GrantSlotPlan.sched_rd (c_pl cx)) as [[[[sb sw] per] fr] pe]. intros FO.
  rewrite Hsch in FO. cbv beta iota zeta in FO. rewrite Hnx in FO. cbv beta iota zeta in FO.
  destruct FO as (_ & _ & _ & _ & _ & _ & _ & FR1).
  destruct (FR1 eq_refl) as (Hc48 & Hp3 & Hleg & Hveff & Hset & Hunset). clear FR1.
  (* want_of's answer for (c, p) is the value the record carries: frame_ok's two clauses on was_set *)
  assert (Hwant : (if HeadampModel.tb (GrantSlotPlan.ws_end (c_pl cx)) (3 * c + p) =? 0
                   then HeadampModel.dflt p
                   else HeadampModel.tb (GrantSlotPlan.st_end (c_pl cx)) (3 * c + p)) = v).
  { destruct (Z.eqb_spec (HeadampModel.tb (GrantSlotPlan.ws_end (c_pl cx)) (3 * c + p)) 0) as [Hw0 | Hw0].
    - symmetry. exact (proj1 (Hunset Hw0)).
    - symmetry. exact (Hset Hw0). }
  destruct (val_mem1_of_aview SEGS _ _ _ _ Cc) as (VCc & Rc).
  destruct (val_mem1_of_aview SEGS _ _ _ _ Cp) as (VCp & Rp).
  destruct (val_mem1_of_aview SEGS _ _ _ _ Cv) as (VCv & Rv).
  (* the trace and the cut the run reaches carry over from TCr: the run and the call keep every byte the
     cuts track and the table's bytes, and the registers the turn names *)
  assert (KEEP : forall (msF : machine_state),
     (forall a, gtracked cx fp a -> aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
     (forall j, 0 <= j < 460 -> aview SEGS (w_H W3) (ms_mem msF) (t + j) = aview SEGS (w_H W3) (ms_mem ms3) (t + j)) ->
     ms_pc_val msF = w64 (BASE + GP_scn) -> ms_resv msF = None -> ms_svc_pending msF = None ->
     ms_rom msF = seg_rom SEGS -> ms_fregs msF = fp_regs -> ms_fcsr msF = fp_csr ->
     gtregs (ms_regs ms3) (ms_regs msF) -> getr (ms_regs msF) 21 = getr (ms_regs ms3) 21 ->
     trec cx fp GP_scn m k acc ly3 S3 W3 msF i t T us c p v T').
  { intros msF FK FKt Fpc Frv Fsvc From Ffr Ffc FR F21.
    split.
    { eapply tcom_keep; [exact HF4096 | exact HFceil | exact HFapp | lia | lia | exact HIN | exact HT
        | exact Fpc | exact Frv | exact Fsvc | exact From | exact Ffr | exact Ffc | exact FR | exact Hi
        | rewrite F21; exact R21 | intros a Ha _; exact (FK a Ha) | | exact GSH_turn_len].
      intros j Hj. rewrite FK; [exact (HSHW j Hj)|].
      pose proof GSH_turn_len as GL. unfold GE_NSH in GL. rewrite GL in Hj.
      right; right; right. lia. }
    split; [exact Hm|]. split; [exact Hsch|]. split; [exact Hnx|].
    split; [eapply gtab_keep; [exact Htab | exact FKt]|].
    split; [exact Hlus|].
    split.
    { eapply gfarr_keep; [exact Hus|]. intros a Ha. rewrite Hlus in Ha. apply FK.
      right; right; left. unfold GO_UNSET in Ha. lia. }
    unfold gfb in *.
    split; [rewrite FK; [exact Cc | right; right; left; unfold GO_CH; lia]|].
    split; [rewrite FK; [exact Cp | right; right; left; unfold GO_PAR; lia]|].
    rewrite FK; [exact Cv | right; right; left; unfold GO_VAL; lia]. }
  (* the environment: the registers at 0x81c1c and the two atoms ch, param *)
  remember (Eimg (Ereg (ms_regs ms3) [w64 c; w64 p])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) [w64 c; w64 p]) E) by (subst E; apply gagree0).
  assert (EE : forall (n : nat) (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr (ms_regs ms3) r0)
    by (intros n0 r0 Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (E32 : ew E 32 = w64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (E33 : ew E 33 = w64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
  assert (E20 : ew E 20 = w64 v) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  (* a0 = eff T' t c p = v: frame_ok's r = 1 -> v = eff T' t c p (HeadampSched.v:169) *)
  assert (E10 : ew E 10 = w64 v) by (rewrite (EE 10%nat 10%bv eq_refl), R10, <- Hveff; reflexivity).
  assert (E27 : ew E 27 = w64 2) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
  assert (U22 : bv_unsigned (ew E 22) = gF cx fp + 784)
    by (rewrite (EE 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; unfold GO_CH; lia).
  assert (U20 : bv_unsigned (ew E 20) = v) by (rewrite E20; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = p) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi SEGS VAL E (mkSS GP_effr sr_atoms rsCr None GCr) (restrict (w_H W3) ms3)).
  { rewrite (gms_eq (w_H W3) GP_effr ms3 Hpc Hrv Hsvc Hrom Hfrg Hfc). apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold rsCr. apply Forall_cons.
      { unfold region_ok, stkCr.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
        - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 96 8 (SOff 22 32) (gF cx fp + 816)).
          + cbn [sv_denot]. rewrite U22. f_equal. lia.
          + cr_pow. lia.
          + cbn. lia.
          + apply val_mem_of_rdword. exact L96.
        - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 112 8 (SOff 22 16) (gF cx fp + 800)).
          + cbn [sv_denot]. rewrite U22. f_equal. lia.
          + cr_pow. lia.
          + cbn. lia.
          + apply val_mem_of_rdword. exact L112.
        - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 128 8 (SOff 22 (-544)) (gF cx fp + 240)).
          + cbn [sv_denot]. rewrite U22. f_equal. lia.
          + cr_pow. lia.
          + cbn. lia.
          + apply val_mem_of_rdword. exact L128.
        - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 136 8 (SOff 22 (-752)) (gF cx fp + 32)).
          + cbn [sv_denot]. rewrite U22. f_equal. lia.
          + cr_pow. lia.
          + cbn. lia.
          + apply val_mem_of_rdword. exact L136. }
      apply Forall_cons; [eapply cellc_ok; [exact U22 | exact U33 | lia | lia | lia |
        replace (gF cx fp + 784 + 16) with (gF cx fp + GO_PAR) by (unfold GO_PAR; lia); exact VCp]|].
      apply Forall_cons; [eapply cellc_ok; [exact U22 | exact U20 | lia | lia | lia |
        replace (gF cx fp + 784 + 32) with (gF cx fp + GO_VAL) by (unfold GO_VAL; lia); exact VCv]|].
      apply Forall_cons; [eapply cellc_ok; [exact U22 | exact U32 | lia | lia | lia |
        replace (gF cx fp + 784 + 0) with (gF cx fp + GO_CH) by (unfold GO_CH; lia); exact VCc]|].
      apply Forall_nil.
    - apply pairwise_disjoint_of_extents. unfold extent_of_region, rsCr, stkCr, cellc.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U22.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; exact I].
      cbn [f_atoms atoms_ok GCr]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U20, U32, U33. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
  clear HE.
  assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  (* 0x81c1c  bne s4,a0,0x81d98 *)
  psrr_branch_tok RUN BR HS SHOK Bsp0.
  - (* taken, to abort: s4 = v and a0 = eff T' t c p differ. REFUTED by HeadampSched.frame_ok's
       r = 1 -> v = eff T' t c p (Hveff, HeadampSched.v:169), which E10 carries. *)
    exfalso. cr_hc Hc. exact (Hc eq_refl).
  - clear Hc.
    (* 0x81c1c .. 0x81c28: &param from slot 112, the param byte a3 (atom 33, the byte at F + GO_PAR) *)
    paj_run_tok RUN HS HJ SHOK Bsp0.
    { cr_awr_ro. }
    (* 0x81c28  bltu s11,a3,0x81c48: s11 = 2 (tbody's reg 27; `li s11,2` at 0x81b78) *)
    psrr_branch_tok RUN BR HS SHOK Bsp0.
    + (* taken: 2 <u a3, and the call of want_of would be skipped. REFUTED by HeadampSched.frame_ok's
         r = 1 -> 0 <= p < 3 (Hp3, HeadampSched.v:169): a3 is the byte re-read at 0x81c24 from &param, which
         is p because trec carries `gfb cx fp W3 ms3 GO_PAR p` (atom 33 = p, region cellc 22 16 33, VCp). *)
      exfalso. cr_hc Hc. clear - Hc Hp3. lia.
    + (* not taken: a3 <= 2. This fall-through fact is what bounds want_of's p at the call. *)
      cr_hc Hc. rename Hc into Hp_le2.
      assert (Hpcall : 0 <= p < 3) by (clear - Hp_le2 Rp; lia).
      (* 0x81c2c .. 0x81c40: the value (s4), ch (a2), &was_set (a0), &set_to (a1), then the jal *)
      paj_run_tok RUN HS HJ SHOK Bsp0.
      { cr_awr_ro. }
      lazymatch goal with
      | HSx : st_ok _ _ _ (restrict _ ?msX) |- SRr _ _ (mkCfg ?msX _) _ => rename HSx into HSc; rename msX into msc
      | HSx : st_ok_pi _ _ _ _ (restrict _ ?msX) |- SRr _ _ (mkCfg ?msX _) _ => rename HSx into HSc; rename msX into msc
      end.
      (* the run wrote no memory: every region was read-only *)
      assert (FK1 : forall a, aview SEGS (w_H W3) (ms_mem msc) a = aview SEGS (w_H W3) (ms_mem ms3) a).
      { intros a. repeat match goal with HFx : frame_of _ _ (mrestrict _ (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)) |-
            aview _ _ (ms_mem ?m1) a = _ => rewrite (cr_kept_ro _ _ _ _ _ HFx ltac:(vm_compute; reflexivity) a); clear HFx end.
        reflexivity. }
      first
        [ pose proof (regs_kept_of_st_ok SEGS E _ _ (ms_regs ms3) [w64 c; w64 p]
            [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HSc HAE ltac:(vm_compute; reflexivity)) as QR
        | pose proof (regs_kept_of_st_ok_pi E _ _ (ms_regs ms3) [w64 c; w64 p]
            [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HSc HAE ltac:(vm_compute; reflexivity)) as QR ].
      cbn [ms_regs restrict] in QR.
      prreg HSc (1%bv : bv 5) Q1. prreg HSc (10%bv : bv 5) Q10. prreg HSc (11%bv : bv 5) Q11.
      prreg HSc (12%bv : bv 5) Q12. prreg HSc (13%bv : bv 5) Q13.
      assert (Hra : getr (ms_regs msc) 1 = w64 (BASE + 0x1208)) by (rewrite Q1; reflexivity).
      (* a0 = &was_set = F + GO_WAS (slot 136), a1 = &set_to = F + GO_SET (slot 128) *)
      assert (A10 : getr (ms_regs msc) 10 = w64 (gF cx fp + GO_WAS)).
      { rewrite Q10. try rewrite ge_sv_SOff0. cbn [sv_denot]. rewrite ?U22. unfold w64, GO_WAS. f_equal. lia. }
      assert (A11 : getr (ms_regs msc) 11 = w64 (gF cx fp + GO_SET)).
      { rewrite Q11. try rewrite ge_sv_SOff0. cbn [sv_denot]. rewrite ?U22. unfold w64, GO_SET. f_equal. lia. }
      (* a2 = c (atom 32, the byte at F + GO_CH), a3 = p (atom 33, the byte at F + GO_PAR) *)
      assert (A12 : getr (ms_regs msc) 12 = w64 c) by (rewrite Q12; try rewrite ge_sv_SOff0; exact E32).
      assert (A13 : getr (ms_regs msc) 13 = w64 p) by (rewrite Q13; try rewrite ge_sv_SOff0; exact E33).
      assert (HSVc : gsaved cx W3 msc).
      { destruct HSV as (S8 & S16). split.
        - rewrite <- S8. apply rdword_ext. intros kk Hkk. apply FK1.
        - intros j Hj. rewrite <- (S16 j Hj). apply rdword_ext. intros kk Hkk. apply FK1. }
      assert (HSHc : gshadow cx fp W3 msc GSH_turn) by (intros j Hj; rewrite FK1; exact (HSHW j Hj)).
      assert (HWSc : gfarr cx fp W3 msc GO_WAS (GrantSlotPlan.ws_end (c_pl cx)))
        by (eapply gfarr_keep; [exact HWS | intros a _; apply FK1]).
      assert (HSTc : gfarr cx fp W3 msc GO_SET (GrantSlotPlan.st_end (c_pl cx)))
        by (eapply gfarr_keep; [exact HST | intros a _; apply FK1]).
      pmkst HSc. rewrite ?pa_sigma_want_of.
      (* 0x81c40: the call of want_of. Its two bounds: 0 <= c < 48 is frame_ok's (Hc48, HeadampSched.v:169);
         0 <= p < 3 is the fall-through of 0x81c28 (Hpcall, from Hp_le2 and the byte's range Rp). *)
      eapply SRr_bind.
      { apply (wo_call cx fp k ly3 S3 W3 (ms_regs msc) (ms_mem msc) _ c p HB HJ Hfr).
        - rewrite (QR 2%bv ltac:(cbv; tauto)). exact G2.
        - rewrite (QR 3%bv ltac:(cbv; tauto)). exact G3.
        - rewrite (QR 4%bv ltac:(cbv; tauto)). exact G4.
        - rewrite (QR 8%bv ltac:(cbv; tauto)). exact G8.
        - exact Hra.
        - exact (proj1 HSVc).
        - pose proof (proj2 HSVc 0 ltac:(lia)) as S0.
          replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in S0 by lia.
          rewrite S0. reflexivity.
        - exact A10.
        - exact A11.
        - exact A12.
        - exact A13.
        - exact Hc48.
        - exact Hpcall.
        - exact HWSc.
        - exact HSTc.
        - exact (cr_arr_usable cx fp W3 msc GO_WAS (3 * c + p) HSHc HF64 HSH (or_introl eq_refl) ltac:(lia)).
        - exact (cr_arr_usable cx fp W3 msc GO_SET (3 * c + p) HSHc HF64 HSH (or_intror eq_refl) ltac:(lia)). }
      intros W4 c4 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & R10').
      (* the callee-saved registers, back from the call *)
      assert (QP : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
                   getr regs2 r0 = getr (ms_regs ms3) r0).
      { intros r0 Hr0. rewrite <- (QR r0 Hr0).
        assert (Hcs : acallee_saved (bv_unsigned r0)).
        { cbv [In] in Hr0. unfold acallee_saved.
          repeat (destruct Hr0 as [<- | Hr0];
            [ lazymatch goal with |- context [bv_unsigned ?r] =>
                let z := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with z end; lia |]);
          destruct Hr0. }
        pose proof (HP2 _ Hcs) as X. rewrite !Z_to_bv_bv_unsigned in X. exact X. }
      (* the bytes the turn tracks and the table's bytes are kept: the callee writes only its stack window
         below s1 (the callee journal's frame clauses) *)
      assert (HKall : forall a, gtracked cx fp a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
      { intros a Htr. assert (Ha : 0 <= a < 2 ^ 64) by (eapply gtracked_rng; eauto; lia).
        rewrite <- (FK1 a).
        pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & K10 & _ & K12 & _).
        destruct Htr as [Hs | [(b & n & Hin & Hb) | [Hf | Hsh]]].
        - apply K9; [lia | unfold STK_want_of, ESTACK; lia].
        - assert (Hin3 : In (b, n) (ablocks B ly3 S3)) by (rewrite Hbl; apply in_app_iff; left; exact Hin).
          replace a with (b + (a - b)) by lia. apply (K10 b n (a - b)); [exact Hin3 | exact Hin3 | lia | apply inFP_nil].
        - apply (K12 GE_CID fp a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA, fsb4; lia | apply inFP_nil].
        - apply (K12 GE_CID fp a Hfin); [|apply inFP_nil].
          right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EFA, fsb4. change (1024 / 8) with 128.
          rewrite <- HSH. lia. }
      assert (HKt : forall j, 0 <= j < 460 ->
                 aview SEGS (w_H W3) mem2 (t + j) = aview SEGS (w_H W3) (ms_mem ms3) (t + j)).
      { intros j Hj. rewrite <- (FK1 (t + j)).
        pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & _).
        apply (K10 t 460 j Hint Hint); [change (req_size 460) with 460; lia | apply inFP_nil]. }
      (* a0 = want_of's answer = v (Hwant) *)
      assert (R10v : getr regs2 10 = w64 v) by (rewrite R10'; f_equal; exact Hwant).
      assert (R20v : getr regs2 20 = w64 v) by (rewrite (QP 20%bv ltac:(cbv; tauto)); exact R20).
      rewrite Hra.
      (* 0x81c44  bne s4,a0,0x81d98 *)
      remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
      assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
      assert (HAE2 : env_agree 32 (Ereg regs2 []) E2) by (subst E2; apply gagree0).
      assert (EE2 : forall (n : nat) (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E2 n = getr regs2 r0)
        by (intros n0 r0 Hr; subst E2; apply ew_Eimg_Ereg_nat; exact Hr).
      assert (HS2 : st_ok_pi SEGS VAL E2 (mkSS 0x1208 sr_atoms [] None (mkFacts [] [] []))
         (restrict (w_H W3) (mkst regs2 (w64 (BASE + 0x1208)) mem2 (seg_rom SEGS)))).
      { rewrite (gms_eq (w_H W3) 0x1208 (mkst regs2 (w64 (BASE + 0x1208)) mem2 (seg_rom SEGS))
          eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl).
        apply pa_entry_st_ok_full.
        - rewrite HE2. apply regs_ok_Eimg_Ereg.
        - vm_compute. reflexivity.
        - constructor.
        - exact I.
        - split; [exact I | split; exact I]. }
      clear HE2.
      assert (SHOK2 : sh_ok SEGS BxL [] E2 (mrestrict (w_H W3) (ms_mem (mkst regs2 (w64 (BASE + 0x1208)) mem2 (seg_rom SEGS)))))
        by constructor.
      psrr_branch_tok RUN BR HS2 SHOK2 Bsp0.
      * (* taken, to abort: s4 = v and a0 = want_of's answer differ. REFUTED by HeadampSched.frame_ok's two
           clauses (HeadampSched.v:170-171): tb ws_end (3c+p) <> 0 -> v = tb st_end (3c+p) and
           tb ws_end (3c+p) = 0 -> v = dflt p, against want_of's post (Hwant). *)
        exfalso.
        rewrite branch_ne_U in Hc. unfold U in Hc. rewrite !ge_sv_SOff0 in Hc.
        rewrite (EE2 20%nat 20%bv eq_refl), (EE2 10%nat 10%bv eq_refl) in Hc.
        rewrite R20v, R10v, Z.eqb_refl in Hc. cbn in Hc. discriminate Hc.
      * (* not taken: on to 0x81c48 *)
        paj_run_to_tok RUNTO HS2 HJ2 SHOK2 Bsp0 GP_scn.
        { cr_awr_ro. }
        lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msF) |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
          destruct (stf _ _ _ _ HSx eq_refl) as (Fpc & Frv & Fsvc & From & Ffr & Ffc);
          assert (FK2 : forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) mem2 a)
            by (intros a;
                repeat match goal with HFx : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?m1)) |-
                  aview _ _ (ms_mem ?m1) a = _ => rewrite (cr_kept_ro _ _ _ _ _ HFx ltac:(vm_compute; reflexivity) a); clear HFx end;
                reflexivity);
          pose proof (regs_kept_of_st_ok_pi E2 ssx (restrict (w_H W3) msF) regs2 []
            [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HSx HAE2 ltac:(vm_compute; reflexivity)) as FR;
          cbn [ms_regs restrict] in FR;
          apply (HTE cx fp k acc ly3 S3 W3 msF mdF HB HJ2 Hfr HMLE)
        end.
        exists i, t, T, us, c, p, v, T'.
        apply KEEP.
        -- intros a Ha. rewrite FK2. exact (HKall a Ha).
        -- intros j Hj. rewrite FK2. exact (HKt j Hj).
        -- exact Fpc.
        -- exact Frv.
        -- exact Fsvc.
        -- exact From.
        -- exact Ffr.
        -- exact Ffc.
        -- repeat split; (rewrite FR by (cbv; tauto)); apply QP; cbv; tauto.
        -- rewrite FR by (cbv; tauto). apply QP. cbv; tauto.
Qed.

End c.
End b.
End a.
