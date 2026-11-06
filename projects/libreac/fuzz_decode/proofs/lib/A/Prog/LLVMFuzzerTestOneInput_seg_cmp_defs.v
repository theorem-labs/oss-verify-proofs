(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* LLVMFuzzerTestOneInput_seg_cmp_defs: proves no function (kind: segment lemma).
   The shared part of the cmp segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput
   (+0x5fc .. +0x744, the premise llvm_a_cmp_stmt of lib/A/Prog/LLVMFuzzerTestOneInput_segs.v, proved as
   llvm_a_cmp_ok in LLVMFuzzerTestOneInput_seg_cmp.v): the inner cut points, the seats, the helpers, and the
   first half of one turn of the bcmp double loop.

   What the code does (offsets from DEC_A_LLVMF, decoded from the audited listing lib/A/Prog/DecodeList.v in
   map-code.md section 2):
     +0x5fc..+0x604  the plain-result check `bne a0, (s8 - 1) | s10` -> +0xa4c; refuted, both ways:
                     plain_ok gives a0 = ns and s8 = 1, else a0 = -1 and s8 = 0.
     +0x608..+0x614  a7 := out, a6 := [80(s1)], s3 := s7 (the frame), `bgez a0` -> +0x66c.
     +0x618..+0x668  scan loop L2 (taken only when the plain check refused, a0 = -1): the decode buffer still
                     holds the 0xa5 fill, so the accumulator a2 stays 0 and the `bnez a2` at +0x668 is refuted.
                     The shadow check at +0x624..+0x630 is the token form (lib/Reusable/YCbn.v tok_load /
                     tok_branch): the out-of-line slow path at +0x658 and its __asan_report_load1 at +0x664 are
                     never stepped.
     +0x66c..+0x67c  64(s1) := res + 50, then two `blez` that skip the comparison when the plain check refused.
     +0x680..+0x6bc  the four spills and the register setup of the double loop.
     +0x6c0..+0x714  the bcmp double loop L3/L4: for each channel c and sample k it compares the three bytes at
                     out + 3*(ns*c + k) with the three at res + 50 + 3*(c + nch*k) through
                     __interceptor_trampoline_bcmp.  They agree: out holds plain_out (the plain leaf's post)
                     and res holds the body, and plain_byte's index is exactly the braid one (cmp_bytes_eq).  So
                     every call returns 0, s10 stays 0 and the `bnez s10` at +0x730 is refuted.
                     The measure is nch*ns - (c*ns + k), the one the old bespoke walk used
                     (a working branch 3ee4cb94cb5 lib/A/Prog/afd_down.v:5465).
     +0x718..+0x738  the reloads of the spilled registers and of s2, and free #1 of the decode buffer
                     through afree04_rule (the block is live: it is the second appended block of st_5fc).
     +0x73c..+0x744  s10 := [56(s1)] = len, a0 := s10, and the call of reac_upstream_channels.

   The cut points: cmp_q624 (+0x624), cmp_q66c (+0x66c), cmp_q734 (+0x734); inside the double loop cmp_inv
   (+0x6e0, the loop invariant), cmp_q6f0 (+0x6f0, the return of bcmp) and cmp_x734 (the loop's exit, before its
   memory facts are carried to cmp_q734).  cmp_l34_call (+0x6e0 -> +0x6f0, the bcmp call) is proved here.

   The engine is the Pa walk of lib/A/Prog/{PaTable,PaSym,PaStep,PaRun,PaShadow,PaJournal}.v with the unit layer
   DecodePa / DecodePaLib / DecodeImg; the idiom is libreac/fuzz_boxreg's lib/A/Prog/ReadName.v at
   a working branch 1d92330b7ad (sstate, paj_run / paj_run_to / paj_branch, awr_ok, the
   shadow side conditions, the journal close). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0s YI00 YO09 YM05 YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require DecodeShape Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
PaRun PaShadow PaJournal PaStep DecodeSyms DecodeList DecodeAddr DecodePa DecodeImg DecodePaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import YC1g YC1h YC1i YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeCJ.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require
reac_upstream_channels_cg reac_decode_plain_le_c reac_upstream_channels_c reac_frame_inspect_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* YC4b / YC1i switch lia's division handling off for their importers; the walk's alignment facts need it
   (ReadName.v:149's line). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module CPlain := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_plain_le_c.
Module CChan := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_c.
Module CInsp := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_inspect_c.
Module LUpChannels := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_cg.

Section cmp.
Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

(* ------------------------------------------------------------------ *)
(* 1. Small facts with no engine in them                                *)
(* ------------------------------------------------------------------ *)

(* plain_ok asks inspect_wf, whose first conjunct is len = 1492 (lib/A/Prog/reac_frame_inspect_c.v:13-15). *)
Lemma cmp_plain_len : forall len bs nch ns, CPlain.plain_ok len bs nch ns = true -> len = 1492.
Proof.
intros len bs nch ns H. unfold CPlain.plain_ok in H.
repeat (apply andb_prop in H as [H ?]). unfold CInsp.inspect_wf in H.
repeat (apply andb_prop in H as [H ?]). apply Z.eqb_eq in H. exact H.
Qed.
Lemma cmp_plain_pos : forall len bs nch ns, CPlain.plain_ok len bs nch ns = true ->
  0 < nch /\ 0 < ns /\ nch * ns <= 480.
Proof.
intros len bs nch ns H. unfold CPlain.plain_ok in H.
apply andb_prop in H as [H H480]. apply andb_prop in H as [H Hns]. apply andb_prop in H as [_ Hnch].
apply Z.ltb_lt in Hnch. apply Z.ltb_lt in Hns. apply Z.leb_le in H480. auto.
Qed.

(* all ones ORed with any 64-bit value is all ones: the shape the refused plain check leaves at +0x604 *)
Lemma cmp_lor_ones : forall y, 0 <= y < 2 ^ 64 -> Z.lor (2 ^ 64 - 1) y = 2 ^ 64 - 1.
Proof.
intros y Hy. apply Z.bits_inj'. intros i Hi.
change (2 ^ 64 - 1) with (Z.ones 64).
rewrite Z.lor_spec, Z.testbit_ones by lia.
destruct (Z.ltb_spec i 64) as [Hlt | Hge].
- replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
  replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [andb]. apply orb_true_l.
- replace (Z.testbit y i) with false.
  + replace (i <? 64) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite andb_false_r. reflexivity.
  + symmetry. destruct (Z.eq_dec y 0) as [-> | Hne]; [apply Z.testbit_0_l|].
    assert (Hl : Z.log2 y < 64) by (apply (proj1 (Z.log2_lt_pow2 y 64 ltac:(lia))); lia).
    apply Z.bits_above_log2; lia.
Qed.

(* the signed branches of the segment, read off bv_signed (YO0c.v:235 branch_ge's statement) *)
Lemma cmp_bge : forall x y : word, branch_taken BC_GE x y = negb (bv_signed x <? bv_signed y).
Proof. intros x y. cbn [branch_taken]. unfold bv_lts. reflexivity. Qed.
Lemma cmp_signed_lit : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small.
change (bv_half_modulus 64) with (2 ^ 63). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The walk                                                          *)
(* ------------------------------------------------------------------ *)

(* The atoms the walk names besides the 32 registers: 32 is the shadow base (the Bx of every run), the rest are
   the values llvm_a_st_5fc fixes.  The whole segment uses one numbering, so one spill picture serves every
   seat. *)
Definition cmp_extra (res out F SH len nch32 ns32 md olen nch64 ns64 : Z) : list word :=
  [w64 SHADOW_OFF; w64 res; w64 out; w64 F; w64 SH; w64 len; w64 nch32; w64 ns32; w64 md;
   w64 olen; w64 nch64; w64 ns64].
(*   32 SB    33 res   34 out   35 F   36 SH   37 len   38 nch32   39 ns32   40 mode   41 olen
     42 nch64  43 ns64 *)

(* The 120 bytes of the realigned spill area at s1 = sp that llvm_a_st_5fc pins.  It is the only writable
   region of the first runs; the journal's own window gives the right to write it (awr_byte's stack case). *)
Definition cmp_spill0 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 120 0 120
   [YP09.mkChunk 32 (CVal 8 (SOff 39%nat 0));
    YP09.mkChunk 40 (CVal 8 (SOff 32%nat 0));
    YP09.mkChunk 48 (CVal 8 (SOff 42%nat 0));
    YP09.mkChunk 56 (CVal 8 (SOff 37%nat 0));
    YP09.mkChunk 64 (CVal 8 (SOff 40%nat 0));
    YP09.mkChunk 72 (CVal 8 (SOff 34%nat 0));
    YP09.mkChunk 80 (CVal 8 (SOff 38%nat 0));
    YP09.mkChunk 88 (CVal 8 (SOff 43%nat 0));
    YP09.mkChunk 112 (CVal 8 (SOff 35%nat 0))].

(* sp is the realigned stack pointer: inside the stack window, 32-aligned.  The bounds are the layout's
   (lib/Reusable/YK06.v alloc_ceiling <= ly_stk_lo and ly_stk_hi <= 2 ^ 47), which is what makes the spill area
   disjoint from the shadow span Bspan. *)
Definition cmp_facts0 : facts :=
  mkFacts [(9%nat, mkAF 140735332483072 140737488355328 5); (32%nat, mkAF 2147450880 2147450880 0)] [] [].

(* every word the cut points name is read with rdword off the walk's own view, so it is a 64-bit value *)
Lemma cmp_rdw_range : forall (W : world decodesegs0) mem a v,
  rdword (aview decodesegs0 (w_H W) mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros W mem a v Hw. unfold rdword in Hw.
destruct (aview decodesegs0 (w_H W) mem a) as [b0|] eqn:D0; [|discriminate].
destruct (aview decodesegs0 (w_H W) mem (a + 1)) as [b1|] eqn:D1; [|discriminate].
destruct (aview decodesegs0 (w_H W) mem (a + 2)) as [b2|] eqn:D2; [|discriminate].
destruct (aview decodesegs0 (w_H W) mem (a + 3)) as [b3|] eqn:D3; [|discriminate].
destruct (aview decodesegs0 (w_H W) mem (a + 4)) as [b4|] eqn:D4; [|discriminate].
destruct (aview decodesegs0 (w_H W) mem (a + 5)) as [b5|] eqn:D5; [|discriminate].
destruct (aview decodesegs0 (w_H W) mem (a + 6)) as [b6|] eqn:D6; [|discriminate].
destruct (aview decodesegs0 (w_H W) mem (a + 7)) as [b7|] eqn:D7; [|discriminate].
injection Hw as <-.
apply aview_byte in D0 as (c0 & _ & _ & R0). apply aview_byte in D1 as (c1 & _ & _ & R1).
apply aview_byte in D2 as (c2 & _ & _ & R2). apply aview_byte in D3 as (c3 & _ & _ & R3).
apply aview_byte in D4 as (c4 & _ & _ & R4). apply aview_byte in D5 as (c5 & _ & _ & R5).
apply aview_byte in D6 as (c6 & _ & _ & R6). apply aview_byte in D7 as (c7 & _ & _ & R7).
lia.
Qed.

(* one 8-byte slot of a region, from the walk's rdword fact *)
Lemma cmp_chunk : forall (E : env) (W : world decodesegs0) mem (n : nat) (base off v : Z),
  ew E n = w64 v ->
  rdword (aview decodesegs0 (w_H W) mem) (base + off) = Some v ->
  YP09.chunk_ok decodesegs0 E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E W mem n base off v Hew Hrd.
pose proof (cmp_rdw_range W mem (base + off) v Hrd) as Hv.
apply (chunk_ok_val decodesegs0 E (mrestrict (w_H W) mem) base off 8%N (SOff n 0) v).
- cbn [sv_denot]. rewrite Hew. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- cbn [Z.of_N Z.mul]. exact Hv.
- cbn [Z.of_N]. lia.
- cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_of_rdword. exact Hrd.
Qed.

(* the twelve atoms of cmp_extra *)
Lemma cmp_ew : forall (regs : bvmap 5 word) res out F SH len nch32 ns32 md olen nch64 ns64,
  let EE := Ereg regs (cmp_extra res out F SH len nch32 ns32 md olen nch64 ns64) in
  ew EE 32%nat = w64 SHADOW_OFF /\ ew EE 33%nat = w64 res /\ ew EE 34%nat = w64 out /\
  ew EE 35%nat = w64 F /\ ew EE 36%nat = w64 SH /\ ew EE 37%nat = w64 len /\
  ew EE 38%nat = w64 nch32 /\ ew EE 39%nat = w64 ns32 /\ ew EE 40%nat = w64 md /\
  ew EE 41%nat = w64 olen /\ ew EE 42%nat = w64 nch64 /\ ew EE 43%nat = w64 ns64.
Proof.
intros regs res out F SH len nch32 ns32 md olen nch64 ns64 EE.
split; [exact (ew_Ereg_extra regs _ 0%nat)|]. split; [exact (ew_Ereg_extra regs _ 1%nat)|].
split; [exact (ew_Ereg_extra regs _ 2%nat)|]. split; [exact (ew_Ereg_extra regs _ 3%nat)|].
split; [exact (ew_Ereg_extra regs _ 4%nat)|]. split; [exact (ew_Ereg_extra regs _ 5%nat)|].
split; [exact (ew_Ereg_extra regs _ 6%nat)|]. split; [exact (ew_Ereg_extra regs _ 7%nat)|].
split; [exact (ew_Ereg_extra regs _ 8%nat)|]. split; [exact (ew_Ereg_extra regs _ 9%nat)|].
split; [exact (ew_Ereg_extra regs _ 10%nat)|]. exact (ew_Ereg_extra regs _ 11%nat).
Qed.

(* ------------------------------------------------------------------ *)
(* The two inner cut points of this segment                            *)
(* ------------------------------------------------------------------ *)

(* +0x624, the head of the scan loop L2, entered only when the plain check refused (a0 = -1).  Nothing has been
   stored since +0x5fc; a7 = a3 = a1 = out, a2 = 0, s3 = the frame (+0x610), s9 = olen; the buffer still holds the
   0xa5 fill. *)
Definition cmp_q624 (cx : dctx) : world decodesegs0 -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res out mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x624)) mem' (YK11.seg_rom decodesegs0)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core B cx ly' S' W' regs' mem' md' dec_ev_5fc /\
    Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++
                                    [(out, dec_a_olen nch ns)]) /\
    4096 <= res /\ 4096 <= out /\
    mo_le MT (d_S cx) S' (dec_spent_5fc MT (d_n cx)) /\ mo_ok MT S' (dec_rest_5fc MT) /\
    CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = false /\
    dec_a_fr cx regs' /\
    YK11.getr regs' 10 = w64 (-1) /\
    YK11.getr regs' 11 = w64 out /\ YK11.getr regs' 13 = w64 out /\ YK11.getr regs' 17 = w64 out /\
    YK11.getr regs' 12 = w64 0 /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 20 = w64 res /\
    YK11.getr regs' 25 = w64 (dec_a_olen nch ns) /\
    dec_a_mode_ok cx W' mem' mode nch ns /\
    dec_a_fsh cx (aview decodesegs0 (w_H W') mem') 0 4 /\
    garr8 decodesegs0 (mrestrict (w_H W') mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    dec_a_filled W' mem' out (dec_a_olen nch ns) /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 40 SHADOW_OFF /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 56 (dec_a_len (d_n cx)) /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 72 out /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 112 (d_F cx).

(* +0x734, the `mv a0, a7` before free #1, reached from both paths: by the `blez a0` at +0x674 when the plain
   check refused, and after the reloads +0x718..+0x72c and the refuted `bnez s10` at +0x730 when it passed.
   Everything of llvm_a_st_748 but the free and the channel call is already true here: s3 / s5 / s11 hold the frame
   again, s2 the shadow base, s4 the copy, a7 the decode buffer, and 64(s1) = res + 50. *)
Definition cmp_q734 (cx : dctx) : world decodesegs0 -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res out mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x734)) mem' (YK11.seg_rom decodesegs0)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core B cx ly' S' W' regs' mem' md' dec_ev_5fc /\
    Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++
                                    [(out, dec_a_olen nch ns)]) /\
    4096 <= res /\ 4096 <= out /\
    mo_le MT (d_S cx) S' (dec_spent_5fc MT (d_n cx)) /\ mo_ok MT S' (dec_rest_5fc MT) /\
    dec_a_fr cx regs' /\
    YK11.getr regs' 17 = w64 out /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 20 = w64 res /\
    dec_a_mode_ok cx W' mem' mode nch ns /\
    dec_a_fsh cx (aview decodesegs0 (w_H W') mem') 0 4 /\
    garr8 decodesegs0 (mrestrict (w_H W') mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    (CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
       dec_a_slot cx (aview decodesegs0 (w_H W') mem') 8 res /\
       dec_a_slot cx (aview decodesegs0 (w_H W') mem') 16 (d_SH cx) /\
       dec_a_slot cx (aview decodesegs0 (w_H W') mem') 24 (d_F cx) /\
       dec_a_slot cx (aview decodesegs0 (w_H W') mem') 48 (d_F cx)) /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 40 SHADOW_OFF /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 56 (dec_a_len (d_n cx)) /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 64 (res + 50) /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 72 out /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 112 (d_F cx).

(* +0x66c, the `addi a1, s4, 50` after the `bgez a0` at +0x614 was taken: the plain check passed, a0 = ns,
   a7 = out (+0x608), a6 = nch (+0x60c), s3 = the frame (+0x610); nothing has been stored since +0x5fc, so the
   memory is llvm_a_st_5fc's, and the buffer holds plain_out. *)
Definition cmp_q66c (cx : dctx) : world decodesegs0 -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res out mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x66c)) mem' (YK11.seg_rom decodesegs0)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core B cx ly' S' W' regs' mem' md' dec_ev_5fc /\
    Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++
                                    [(out, dec_a_olen nch ns)]) /\
    4096 <= res /\ 4096 <= out /\
    mo_le MT (d_S cx) S' (dec_spent_5fc MT (d_n cx)) /\ mo_ok MT S' (dec_rest_5fc MT) /\
    CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true /\
    dec_a_fr cx regs' /\
    YK11.getr regs' 10 = w64 ns /\
    YK11.getr regs' 16 = w64 (nch mod 2 ^ 32) /\
    YK11.getr regs' 17 = w64 out /\
    YK11.getr regs' 20 = w64 res /\
    YK11.getr regs' 26 = w64 (ns mod 2 ^ 64) /\
    dec_a_mode_ok cx W' mem' mode nch ns /\
    dec_a_fsh cx (aview decodesegs0 (w_H W') mem') 0 4 /\
    garr8 decodesegs0 (mrestrict (w_H W') mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    garr8 decodesegs0 (mrestrict (w_H W') mem') out
      (map (fun b : byte => bv_unsigned b) (CPlain.plain_out (d_body cx) nch ns)) /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 32 (ns mod 2 ^ 32) /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 40 SHADOW_OFF /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 48 (nch mod 2 ^ 64) /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 56 (dec_a_len (d_n cx)) /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 64 mode /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 72 out /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 80 (nch mod 2 ^ 32) /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 88 (ns mod 2 ^ 64) /\
    dec_a_slot cx (aview decodesegs0 (w_H W') mem') 112 (d_F cx).

(* the premises of llvm_a_cmp_stmt, as one Prop, so the phase lemmas below state them once *)
Definition cmp_prem : Prop :=
  pc_wrap_free (as_code B) = decode_sigma DS___interceptor_trampoline_free /\
  dec_llvmf_utraces RA_LLVMF B /\
  dec_crt_cells B /\
  dec_ro_rd_unowned B /\ dec_rom_no_errno B /\
  AR_laws decodesegs0 B /\ model_laws (as_universe B) /\ ameter_laws MT /\
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc decodesegs0 B (decode_sigma DS___interceptor_trampoline_bcmp)) /\
  (forall fx' : YK11.FPState, @afree04_rule fx' rc dec_A_sink_head decodesegs0 B MT) /\
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LUpChannels.dec_reac_upstream_channels_cg) fx').

(* The spill area inside the double loop: the four words stored at +0x680..+0x68c, 64(s1) = res + 50 stored at
   +0x670, and the slots of llvm_a_st_5fc. *)
Definition cmp_spill1 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 120 0 120
   [YP09.mkChunk 8 (CVal 8 (SOff 33%nat 0));
    YP09.mkChunk 16 (CVal 8 (SOff 36%nat 0));
    YP09.mkChunk 24 (CVal 8 (SOff 35%nat 0));
    YP09.mkChunk 32 (CVal 8 (SOff 39%nat 0));
    YP09.mkChunk 40 (CVal 8 (SOff 32%nat 0));
    YP09.mkChunk 48 (CVal 8 (SOff 35%nat 0));
    YP09.mkChunk 56 (CVal 8 (SOff 37%nat 0));
    YP09.mkChunk 64 (CVal 8 (SOff 33%nat 50));
    YP09.mkChunk 72 (CVal 8 (SOff 34%nat 0));
    YP09.mkChunk 80 (CVal 8 (SOff 38%nat 0));
    YP09.mkChunk 88 (CVal 8 (SOff 43%nat 0));
    YP09.mkChunk 112 (CVal 8 (SOff 35%nat 0))].

Ltac cmp_awr1 sp1 sp0 Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
  [ reflexivity
  | rewrite Usp; lia
  | unfold DEC_LLVMF_STK; cbn [r_wlo]; lia
  | cbn [r_whi]; lia
  | apply awr_ok_nil ].

(* an 8-byte chunk whose value is an atom plus a constant *)
Lemma cmp_chunk_off : forall (E : env) (W : world decodesegs0) mem (n : nat) (base off v z : Z),
  ew E n = w64 v -> 0 <= v -> 0 <= z -> v + z < 2 ^ 64 ->
  rdword (aview decodesegs0 (w_H W) mem) (base + off) = Some (v + z) ->
  YP09.chunk_ok decodesegs0 E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff n z))).
Proof.
intros E W mem n base off v z Hew Hv Hz Hvz Hrd.
apply (chunk_ok_val decodesegs0 E (mrestrict (w_H W) mem) base off 8%N (SOff n z) (v + z)).
- cbn [sv_denot]. rewrite Hew. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- cbn [Z.of_N Z.mul]. lia.
- cbn [Z.of_N]. lia.
- cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_of_rdword. exact Hrd.
Qed.

(* A word read from its bytes, copied from LLVMFuzzerTestOneInput_seg_entry.v:108-123 (there from a Theorem Labs lane's
   GrantFrame.v). *)
Lemma cmp_rdword_of_val_mem : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (BB : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (BB 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (BB 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (BB 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (BB 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (BB 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (BB 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (BB 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (BB 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
(* a register the seat named by its own atom still reads as the seat's register *)
Lemma cmp_den_atom : forall (E : env) n w, ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

(* a one-byte val_mem fact is the walk's view of that byte *)
Lemma cmp_aview_of_val1 : forall segs H (m : word -> option byte) a v,
  val_mem segs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview segs H m a = Some v.
Proof.
intros segs H m a v Hv Hr. unfold aview. specialize (Hv 0%nat ltac:(lia)).
cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YO0f.le_byte.
replace (v mod 2 ^ (8 * Z.of_nat 1)) with v by (symmetry; apply Z.mod_small; cbn; lia).
replace (8 * Z.of_nat 0) with 0 by reflexivity.
rewrite Z.shiftr_0_r. rewrite !(Z.mod_small v 256) by lia. reflexivity.
Qed.

(* the braid index of the double loop (plain_byte's index at 3*(ns*c + k) + i) *)
Lemma cmp_braid_index : forall nch ns c k i, 0 < ns -> 0 <= c -> 0 <= k < ns -> 0 <= i < 3 ->
  50 + 3 * (((3 * (ns * c + k) + i) / 3) mod ns * nch + (3 * (ns * c + k) + i) / 3 / ns)
     + (3 * (ns * c + k) + i) mod 3
  = 50 + 3 * (c + nch * k) + i.
Proof.
intros nch ns c k i Hns Hc Hk Hi.
assert (D3 : (3 * (ns * c + k) + i) / 3 = ns * c + k).
{ rewrite Z.mul_comm, Z.div_add_l by lia. rewrite (Z.div_small i 3) by lia. lia. }
assert (M3 : (3 * (ns * c + k) + i) mod 3 = i).
{ rewrite Z.mul_comm, Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia. }
assert (Mn : (ns * c + k) mod ns = k).
{ rewrite Z.mul_comm, Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia. }
assert (Dn : (ns * c + k) / ns = c).
{ rewrite Z.mul_comm, Z.div_add_l by lia. rewrite (Z.div_small k ns) by lia. lia. }
rewrite D3, M3, Mn, Dn. ring.
Qed.

(* the body fuzz_dup copies has dec_a_len n bytes *)
Lemma cmp_body_len : forall (pl : list byte) n, n = Z.of_nat (length pl) ->
  Z.of_nat (length (skipn (Z.to_nat (dec_a_u n)) pl)) = dec_a_len n.
Proof.
intros pl n Hn. rewrite length_skipn. unfold dec_a_u, dec_a_len. lia.
Qed.

(* a register of a state stopped at a call, without unfolding its denotation (ReadName.v:408 rn_reg) *)
Ltac cmp_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

(* the j-th byte value of a list built over seq *)
Lemma cmp_nth_map_seq : forall (f : Z -> byte) N j, (j < N)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) (map f (map Z.of_nat (seq 0 N)))) 0 = bv_unsigned (f (Z.of_nat j)).
Proof.
intros f N j Hj. rewrite !map_map.
set (F := fun x : nat => bv_unsigned (f (Z.of_nat x))).
rewrite (nth_indep _ 0 (F 0%nat)) by (rewrite length_map, length_seq; exact Hj).
rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.
Lemma cmp_nth_map_byte : forall (l : list byte) j, (j < length l)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
intros l j Hj.
rewrite (nth_indep _ 0 ((fun b : byte => bv_unsigned b) (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
rewrite map_nth. reflexivity.
Qed.

(* the three bytes bcmp compares agree: plain_out at 3*(ns*c + k) + i is the body byte at
   50 + 3*(c + nch*k) + i *)
Lemma cmp_bytes_eq : forall segs H (m : word -> option byte) (body : list byte) res out nch ns c k i,
  garr8 segs (mrestrict H m) res (map (fun b : byte => bv_unsigned b) body) ->
  garr8 segs (mrestrict H m) out (map (fun b : byte => bv_unsigned b) (CPlain.plain_out body nch ns)) ->
  Z.of_nat (length body) = 1492 -> 0 < nch -> 0 < ns -> nch * ns <= 480 ->
  0 <= c < nch -> 0 <= k < ns -> 0 <= i < 3 ->
  aview segs H m (out + 3 * ns * c + 3 * k + i) = aview segs H m (res + 50 + 3 * c + 3 * nch * k + i).
Proof.
intros segs H m body res out nch ns c k i HR HO Hlen Hnch Hns Hprod Hc Hk Hi.
set (j := 3 * (ns * c + k) + i).
set (j' := 50 + 3 * (c + nch * k) + i).
assert (Hj : 0 <= j < 3 * nch * ns) by (subst j; nia).
assert (Hj' : 0 <= j' < 1492) by (subst j'; nia).
assert (LO : length (map (fun b : byte => bv_unsigned b) (CPlain.plain_out body nch ns)) = Z.to_nat (3 * nch * ns))
  by (unfold CPlain.plain_out; rewrite !length_map, length_seq; reflexivity).
destruct (HO (Z.to_nat j) ltac:(rewrite LO; lia)) as [VO RO].
destruct (HR (Z.to_nat j') ltac:(rewrite length_map; lia)) as [VR RR].
rewrite Z2Nat.id in VO, VR by lia.
replace (out + 3 * ns * c + 3 * k + i) with (out + j) by (subst j; ring).
replace (res + 50 + 3 * c + 3 * nch * k + i) with (res + j') by (subst j'; ring).
rewrite (cmp_aview_of_val1 _ _ _ _ _ VO RO), (cmp_aview_of_val1 _ _ _ _ _ VR RR).
f_equal. unfold CPlain.plain_out.
rewrite cmp_nth_map_seq by lia. rewrite cmp_nth_map_byte by lia.
unfold CPlain.plain_byte. rewrite Z2Nat.id by lia. subst j.
rewrite cmp_braid_index by lia. reflexivity.
Qed.

(* a callee-saved register is kept by a call, read at a bv literal *)
Lemma cmp_pres_lit : forall (regs regs' : bvmap 5 word) (rr : bv 5),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned rr) -> YK11.getr regs' rr = YK11.getr regs rr.
Proof.
intros regs regs' rr HP Hr. specialize (HP _ Hr). rewrite Z_to_bv_bv_unsigned in HP. exact HP.
Qed.

(* a slot of a region chunk, back out as the walk's rdword fact *)
Lemma cmp_slot_of_chunk : forall (E : env) (W : world decodesegs0) mem (n : nat) (base off v z : Z),
  YP09.chunk_ok decodesegs0 E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff n z))) ->
  bv_unsigned (ew E n) + z = v -> 0 <= v < 2 ^ 64 ->
  rdword (aview decodesegs0 (w_H W) mem) (base + off) = Some v.
Proof.
intros E W mem n base off v z HC Hv Hr.
apply cmp_rdword_of_val_mem; [|exact Hr].
apply (val_of_chunk_ok decodesegs0 E (mrestrict (w_H W) mem) base off 8%N (SOff n z) v HC).
- cbn [sv_denot]. rewrite Hv. reflexivity.
- cbn [Z.of_N Z.mul]. exact Hr.
- cbn [Z.of_N]. lia.
Qed.

(* the twelve slots of the loop's spill picture, from the region of a state whose run stored nothing *)
Lemma cmp_unseat1 : forall (E : env) (W : world decodesegs0) mem (cx : dctx) res out nch ns,
  region_ok decodesegs0 E (mrestrict (w_H W) mem) cmp_spill1 ->
  bv_unsigned (ew E 9%nat) = d_sp1 cx ->
  bv_unsigned (ew E 33%nat) = res -> bv_unsigned (ew E 36%nat) = d_SH cx ->
  bv_unsigned (ew E 35%nat) = d_F cx -> bv_unsigned (ew E 39%nat) = ns mod 2 ^ 32 ->
  bv_unsigned (ew E 32%nat) = SHADOW_OFF -> bv_unsigned (ew E 37%nat) = dec_a_len (d_n cx) ->
  bv_unsigned (ew E 34%nat) = out -> bv_unsigned (ew E 38%nat) = nch mod 2 ^ 32 ->
  bv_unsigned (ew E 43%nat) = ns mod 2 ^ 64 ->
  res + 50 < 2 ^ 64 ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 8 res /\
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 16 (d_SH cx) /\
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 24 (d_F cx) /\
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 32 (ns mod 2 ^ 32) /\
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 40 SHADOW_OFF /\
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 48 (d_F cx) /\
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 56 (dec_a_len (d_n cx)) /\
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 64 (res + 50) /\
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 72 out /\
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 80 (nch mod 2 ^ 32) /\
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 88 (ns mod 2 ^ 64) /\
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 112 (d_F cx).
Proof.
intros E W mem cx res out nch ns HR Hb A33 A36 A35 A39 A32 A37 A34 A38 A43 Hr50.
destruct HR as (_ & _ & _ & HC).
cbn [YP09.r_base YP09.r_chunks base_val cmp_spill1] in HC. rewrite Hb in HC.
assert (G : forall off n z, In (YP09.mkChunk off (CVal 8 (SOff n z))) (YP09.r_chunks cmp_spill1) ->
  YP09.chunk_ok decodesegs0 E (mrestrict (w_H W) mem) (d_sp1 cx) (YP09.mkChunk off (CVal 8 (SOff n z))))
  by (intros off n z Hin; exact (proj1 (Forall_forall _ _) HC _ Hin)).
pose proof (bv_unsigned_in_range 64 (ew E 33%nat)) as R33.
pose proof (bv_unsigned_in_range 64 (ew E 36%nat)) as R36.
pose proof (bv_unsigned_in_range 64 (ew E 35%nat)) as R35.
pose proof (bv_unsigned_in_range 64 (ew E 39%nat)) as R39.
pose proof (bv_unsigned_in_range 64 (ew E 32%nat)) as R32.
pose proof (bv_unsigned_in_range 64 (ew E 37%nat)) as R37.
pose proof (bv_unsigned_in_range 64 (ew E 34%nat)) as R34.
pose proof (bv_unsigned_in_range 64 (ew E 38%nat)) as R38.
pose proof (bv_unsigned_in_range 64 (ew E 43%nat)) as R43.
change (bv_modulus 64) with (2 ^ 64) in R33, R36, R35, R39, R32, R37, R34, R38, R43.
unfold dec_a_slot.
split; [apply (cmp_slot_of_chunk E W mem 33%nat _ _ _ 0 (G 8 33%nat 0 ltac:(cbn; tauto))); lia|].
split; [apply (cmp_slot_of_chunk E W mem 36%nat _ _ _ 0 (G 16 36%nat 0 ltac:(cbn; tauto))); lia|].
split; [apply (cmp_slot_of_chunk E W mem 35%nat _ _ _ 0 (G 24 35%nat 0 ltac:(cbn; tauto))); lia|].
split; [apply (cmp_slot_of_chunk E W mem 39%nat _ _ _ 0 (G 32 39%nat 0 ltac:(cbn; tauto))); lia|].
split; [apply (cmp_slot_of_chunk E W mem 32%nat _ _ _ 0 (G 40 32%nat 0 ltac:(cbn; tauto))); lia|].
split; [apply (cmp_slot_of_chunk E W mem 35%nat _ _ _ 0 (G 48 35%nat 0 ltac:(cbn; tauto))); lia|].
split; [apply (cmp_slot_of_chunk E W mem 37%nat _ _ _ 0 (G 56 37%nat 0 ltac:(cbn; tauto))); lia|].
split; [apply (cmp_slot_of_chunk E W mem 33%nat _ _ _ 50 (G 64 33%nat 50 ltac:(cbn; tauto))); lia|].
split; [apply (cmp_slot_of_chunk E W mem 34%nat _ _ _ 0 (G 72 34%nat 0 ltac:(cbn; tauto))); lia|].
split; [apply (cmp_slot_of_chunk E W mem 38%nat _ _ _ 0 (G 80 38%nat 0 ltac:(cbn; tauto))); lia|].
split; [apply (cmp_slot_of_chunk E W mem 43%nat _ _ _ 0 (G 88 43%nat 0 ltac:(cbn; tauto))); lia|].
apply (cmp_slot_of_chunk E W mem 35%nat _ _ _ 0 (G 112 35%nat 0 ltac:(cbn; tauto))); lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The mode's geometry at another state of the walk                    *)
(* ------------------------------------------------------------------ *)

(* The table words +4 / +8 of each REAC_MODE table are DEC_RO_RD bytes (check_round_trip_cg.v DEC_RO_RD). *)
Lemma cmp_tab_ro_rd : forall t k, (t = 0x20d40 \/ t = 0x20d60 \/ t = 0x20d80) -> 0 <= k < 8 ->
  dec_in_ro_rd (t + 4 + k).
Proof.
intros t k Ht Hk. unfold dec_in_ro_rd, DEC_RO_RD.
destruct Ht as [-> | [-> | ->]].
- apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- do 4 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- do 5 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* Every DEC_RO_RD byte lies in the low read-only image, below 0x30000. *)
Lemma cmp_ro_rd_low : forall a, dec_in_ro_rd a -> 0 <= a < 0x30000.
Proof.
intros a Ha. unfold dec_in_ro_rd, DEC_RO_RD in Ha. rewrite Exists_exists in Ha.
destruct Ha as (r & Hin & Hz). unfold in_zr in Hz. cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]; [cbn [fst snd] in Hz; lia|]). destruct Hin.
Qed.

(* dec_a_mode_ok at another state of the same walk (after LLVMFuzzerTestOneInput_seg_crt1.v c1_mode_re). The
   pointer cells decode_obj 4 / 5 / 6 are constant cells of dec_crt_cells, picked by their statement and read again
   at the new state. The table words +4 / +8 are read-only image bytes (DEC_RO_RD), and the two states see the same
   bytes there; the caller gets that from dec_rom_view_rd at both states or from a kept-memory fact. The frame's
   local is kept by the caller. *)
Lemma cmp_mode_re : forall cx (W W' : world decodesegs0) mem mem' ly S md ly' S' md' mode nch ns,
  dec_crt_cells B ->
  @AR rc decodesegs0 B ly S W mem md -> @AR rc decodesegs0 B ly' S' W' mem' md' ->
  dec_a_mode_ok cx W mem mode nch ns ->
  (forall a, dec_in_ro_rd a -> aview decodesegs0 (w_H W') mem' a = aview decodesegs0 (w_H W) mem a) ->
  (forall k, 0 <= k < 8 ->
     aview decodesegs0 (w_H W') mem' (d_F cx + 36 + k) = aview decodesegs0 (w_H W) mem (d_F cx + 36 + k)) ->
  dec_a_mode_ok cx W' mem' mode nch ns.
Proof.
intros cx W W' mem mem' ly S md ly' S' md' mode nch ns HCELLS HAR HAR' (Hmc & Hnch & Hns & Hv4 & Hv8) HRO HF.
assert (VK : forall a (n : nat) v, (forall k, 0 <= k < Z.of_nat n ->
   aview decodesegs0 (w_H W') mem' (a + k) = aview decodesegs0 (w_H W) mem (a + k)) ->
   val_mem decodesegs0 (mrestrict (w_H W) mem) a n v -> val_mem decodesegs0 (mrestrict (w_H W') mem') a n v).
{ intros a n v Hk Hv j Hj. rewrite (mbyte_of_aview decodesegs0 (w_H W) (w_H W') mem mem' (a + Z.of_nat j)).
  - exact (Hv j Hj).
  - apply Hk. lia. }
assert (CL : forall ly0 S0 (W0 : world decodesegs0) mem0 md0 c t,
  @AR rc decodesegs0 B ly0 S0 W0 mem0 md0 -> In (z8 (ANum c) t) (as_const B ly0) -> 0 <= t < 2 ^ 64 ->
  rdword (aview decodesegs0 (w_H W0) mem0) c = Some t).
{ intros ly0 S0 W0 mem0 md0 c t HA Hin Ht. destruct HA as [HAm _].
  pose proof (am_const _ _ _ _ HAm) as HC. rewrite Forall_forall in HC.
  exact (rdword_cell B ly0 _ c t Ht (HC _ Hin)). }
assert (TB : forall c, rdword (aview decodesegs0 (w_H W) mem) c = Some mode ->
   (exists t, In (z8 (ANum c) t) (as_const B ly) /\ In (z8 (ANum c) t) (as_const B ly') /\
              (t = 0x20d40 \/ t = 0x20d60 \/ t = 0x20d80)) ->
   rdword (aview decodesegs0 (w_H W') mem') c = Some mode /\
   val_mem decodesegs0 (mrestrict (w_H W') mem') (mode + 4) 4 (nch mod 2 ^ 32) /\
   val_mem decodesegs0 (mrestrict (w_H W') mem') (mode + 8) 4 (ns mod 2 ^ 32)).
{ intros c Hc (t & P0 & P0' & Ht).
  assert (Ht64 : 0 <= t < 2 ^ 64) by lia.
  rewrite (CL _ _ _ _ _ _ _ HAR P0 Ht64) in Hc. injection Hc as <-.
  split; [exact (CL _ _ _ _ _ _ _ HAR' P0' Ht64)|].
  split; (apply (VK _ 4%nat); [|assumption]); intros k Hk; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk.
  - apply HRO, cmp_tab_ro_rd; [exact Ht | lia].
  - replace (t + 8 + k) with (t + 4 + (4 + k)) by lia. apply HRO, cmp_tab_ro_rd; [exact Ht | lia]. }
pose proof (HCELLS ly) as HCL. pose proof (HCELLS ly') as HCL'.
repeat match type of HCL with _ /\ _ => let H1 := fresh "Row" in destruct HCL as [H1 HCL] end.
repeat match type of HCL' with _ /\ _ => let H1 := fresh "Row" in destruct HCL' as [H1 HCL'] end.
destruct Hmc as [Hc | [Hc | [Hc | Hc]]].
- destruct (TB _ Hc ltac:(eexists; repeat split; first [eassumption | lia])) as (R0 & R4 & R8).
  split; [left; exact R0 | split; [exact Hnch | split; [exact Hns | split; [exact R4 | exact R8]]]].
- destruct (TB _ Hc ltac:(eexists; repeat split; first [eassumption | lia])) as (R0 & R4 & R8).
  split; [right; left; exact R0 | split; [exact Hnch | split; [exact Hns | split; [exact R4 | exact R8]]]].
- destruct (TB _ Hc ltac:(eexists; repeat split; first [eassumption | lia])) as (R0 & R4 & R8).
  split; [right; right; left; exact R0 | split; [exact Hnch | split; [exact Hns | split; [exact R4 | exact R8]]]].
- subst mode. split; [right; right; right; reflexivity|]. split; [exact Hnch|]. split; [exact Hns|].
  split; (apply (VK _ 4%nat); [|assumption]); intros k Hk;
    [replace (d_F cx + 32 + 4 + k) with (d_F cx + 36 + k) by lia
    | replace (d_F cx + 32 + 8 + k) with (d_F cx + 36 + (4 + k)) by lia];
    apply HF; cbn in Hk; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Tactics and value lemmas of the loop's runs                         *)
(* ------------------------------------------------------------------ *)

(* the value of an atom plus a constant *)
Lemma cmp_off : forall (E : env) n v z, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 ->
  sv_denot E (SOff n z) = w64 (v + z).
Proof. intros E n v z Hn Hv Hz. rewrite denot_lit_U. unfold w64. f_equal. apply U_atom_off; [exact Hn | lia | lia]. Qed.

(* a signed read of an atom holding a small value; the literal 0 *)
Lemma cmp_sgn_atom : forall (E : env) n v, ew E n = w64 v -> 0 <= v < 2 ^ 63 -> bv_signed (sv_denot E (SOff n 0)) = v.
Proof. intros E n v Hn Hv. rewrite (cmp_den_atom E n _ Hn). unfold w64. apply cmp_signed_lit. lia. Qed.
Lemma cmp_sgn0 : forall (E : env), bv_signed (sv_denot E (SLit 0)) = 0.
Proof. intros E. reflexivity. Qed.

(* a spill slot, read off a chunk of a region at s1 = atom 9 *)
Lemma cmp_slot : forall (E : env) (W : world decodesegs0) mem cx lo hi wlo whi cs off e v,
  region_ok decodesegs0 E (mrestrict (w_H W) mem) (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 9%nat) = d_sp1 cx -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) off v.
Proof.
intros E W mem cx lo hi wlo whi cs off e v HR Hb Hin He Hv. unfold dec_a_slot.
apply cmp_rdword_of_val_mem; [|exact Hv].
exact (field_of_region E _ 9 (d_sp1 cx) cs lo hi wlo whi off 8%N e v HR Hb Hin He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* a slot is kept when its eight bytes are *)
Lemma cmp_slot_kept : forall (W : world decodesegs0) (m m' : word -> option byte) cx off v,
  (forall a, d_sp1 cx + off <= a < d_sp1 cx + off + 8 -> aview decodesegs0 (w_H W) m' a = aview decodesegs0 (w_H W) m a) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) m) off v -> dec_a_slot cx (aview decodesegs0 (w_H W) m') off v.
Proof.
intros W m m' cx off v HK Hs. unfold dec_a_slot, rdword in *.
rewrite !HK by lia. exact Hs.
Qed.

Ltac cmp_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* After a run over the loop's spill picture: the bytes outside [sp1 - 8192, sp1 + 120) are still the base
   memory's (KR), and every byte present in the base memory is still present (GR) (ReadName.v rn_kupd). *)
Ltac cmp_kupd sp1 Usp KR GR :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rsx (mrestrict ?H ?m0) (mrestrict ?H ?m1),
    HG : mem_grows (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- _ =>
    lazymatch type of KR with forall a, _ -> _ -> aview _ ?Hk _ a = aview _ _ ?mbase a =>
      let KR2 := fresh "KR" in let GR2 := fresh "GR" in
      assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 8192 <= a < sp1 + 120) ->
                aview decodesegs0 Hk m1 a = aview decodesegs0 Hk mbase a);
      [ intros a Ha Hn; etransitivity;
        [ refine (kept_of_frame Ex rsx H m0 m1 (fun x => sp1 - 8192 <= x < sp1 + 120) HFr _ a Ha Hn);
          intros bb wlo whi xx Hin Hr;
          let wsv := eval vm_compute in (windows rsx) in change (In (bb, wlo, whi) wsv) in Hin;
          cbn [In] in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr|]); try contradiction;
          cbv beta; first [lia | rewrite Usp in Hr; lia]
        | exact (KR a Ha Hn) ]
      | ];
      assert (GR2 : forall a, apresent Hk mbase a -> apresent Hk m1 a)
        by (intros a Ha; exact (apresent_grows H m0 m1 a HG (GR a Ha)));
      clear KR GR; rename KR2 into KR; rename GR2 into GR
    end
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Section body.
Context {fx : YK11.FPState}.

(* The loop invariant at the head of the inner loop L4 (+0x6e0), channel c and sample k: the outer counter
   s3 = c, the mismatch accumulator s10 = 0, the strides s5 = 3*nch and s6 = s4 = 3*ns, the outer cursors
   s7 = out + 3*ns*c and s2 = res + 50 + 3*c, the inner bound s11 = out + 3*ns*(c+1), the inner cursors
   s8 = out + 3*(ns*c + k) and s9 = res + 50 + 3*(c + nch*k).  The world, the layout and the allocator state do not
   move inside the loop (bcmp writes only below sp); the memory agrees with +0x5fc's outside the spill area and
   bcmp's stack window, and the spill area holds its twelve words. *)
Definition cmp_inv (cx : dctx) (ly5 : alayout) (S5 : astate) (W5 : world decodesegs0)
    (mem5 : word -> option byte) (res out nch ns c k : Z) : world decodesegs0 -> config -> Prop :=
  fun W' c' => W' = W5 /\ 0 <= c < nch /\ 0 <= k < ns /\
    exists regs mem md,
      c' = mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x6e0)) mem (YK11.seg_rom decodesegs0)) md /\
      @ajournal rc dec_A_sink_head decodesegs0 B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx)
        (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly5 S5 W5 mem md dec_ev_5fc /\
      YK11.getr regs 2 = w64 (d_sp1 cx) /\ YK11.getr regs 9 = w64 (d_sp1 cx) /\
      YK11.getr regs 8 = w64 (d_sp0 cx) /\
      YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
      YK11.getr regs 19 = w64 c /\ YK11.getr regs 26 = w64 0 /\
      YK11.getr regs 21 = w64 (3 * nch) /\ YK11.getr regs 22 = w64 (3 * ns) /\
      YK11.getr regs 20 = w64 (3 * ns) /\
      YK11.getr regs 23 = w64 (out + 3 * ns * c) /\ YK11.getr regs 18 = w64 (res + 50 + 3 * c) /\
      YK11.getr regs 27 = w64 (out + 3 * ns * (c + 1)) /\
      YK11.getr regs 24 = w64 (out + 3 * ns * c + 3 * k) /\
      YK11.getr regs 25 = w64 (res + 50 + 3 * c + 3 * nch * k) /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - 8192 <= a < d_sp1 cx + 120) ->
         aview decodesegs0 (w_H W5) mem a = aview decodesegs0 (w_H W5) mem5 a) /\
      (forall a, apresent (w_H W5) mem5 a -> apresent (w_H W5) mem a) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 8 res /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 16 (d_SH cx) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 24 (d_F cx) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 32 (ns mod 2 ^ 32) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 40 SHADOW_OFF /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 48 (d_F cx) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 56 (dec_a_len (d_n cx)) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 64 (res + 50) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 72 out /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 80 (nch mod 2 ^ 32) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 88 (ns mod 2 ^ 64) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 112 (d_F cx).

(* The exit of the double loop at +0x734, before the memory facts are carried over: the reloads +0x718..+0x72c
   have put the frame back in s3 / s5 / s11, the shadow base in s2, res in s4 and out in a7; the journal is the
   loop's; the memory agrees with the +0x66c memory mem5 outside the spill area and bcmp's stack window, and the
   spill area holds the slots cmp_q734 names.  cmp_x734_q734 (LLVMFuzzerTestOneInput_seg_cmp_x734.v) turns it into
   cmp_q734. *)
Definition cmp_x734 (cx : dctx) (ly5 : alayout) (S5 : astate) (W5 : world decodesegs0)
    (mem5 : word -> option byte) (res out : Z) : world decodesegs0 -> config -> Prop :=
  fun W' c' => W' = W5 /\
    exists regs mem md,
      c' = mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x734)) mem (YK11.seg_rom decodesegs0)) md /\
      @ajournal rc dec_A_sink_head decodesegs0 B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx)
        (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly5 S5 W5 mem md dec_ev_5fc /\
      YK11.getr regs 2 = w64 (d_sp1 cx) /\ YK11.getr regs 9 = w64 (d_sp1 cx) /\
      YK11.getr regs 8 = w64 (d_sp0 cx) /\
      YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
      dec_a_fr cx regs /\
      YK11.getr regs 17 = w64 out /\ YK11.getr regs 18 = w64 SHADOW_OFF /\ YK11.getr regs 20 = w64 res /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - 8192 <= a < d_sp1 cx + 120) ->
         aview decodesegs0 (w_H W5) mem a = aview decodesegs0 (w_H W5) mem5 a) /\
      (forall a, apresent (w_H W5) mem5 a -> apresent (w_H W5) mem a) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 8 res /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 16 (d_SH cx) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 24 (d_F cx) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 40 SHADOW_OFF /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 48 (d_F cx) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 56 (dec_a_len (d_n cx)) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 64 (res + 50) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 72 out /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 112 (d_F cx).

(* +0x6f0, the return of __interceptor_trampoline_bcmp in turn (c, k): cmp_inv's state with a0 = 0 (the three
   bytes agreed, the braid relation), the inner cursors s8 / s9 not yet stepped. *)
Definition cmp_q6f0 (cx : dctx) (ly5 : alayout) (S5 : astate) (W5 : world decodesegs0)
    (mem5 : word -> option byte) (res out nch ns c k : Z) : world decodesegs0 -> config -> Prop :=
  fun W' c' => W' = W5 /\ 0 <= c < nch /\ 0 <= k < ns /\
    exists regs mem md,
      c' = mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x6f0)) mem (YK11.seg_rom decodesegs0)) md /\
      @ajournal rc dec_A_sink_head decodesegs0 B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx)
        (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly5 S5 W5 mem md dec_ev_5fc /\
      YK11.getr regs 2 = w64 (d_sp1 cx) /\ YK11.getr regs 9 = w64 (d_sp1 cx) /\
      YK11.getr regs 8 = w64 (d_sp0 cx) /\
      YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
      YK11.getr regs 10 = w64 0 /\
      YK11.getr regs 19 = w64 c /\ YK11.getr regs 26 = w64 0 /\
      YK11.getr regs 21 = w64 (3 * nch) /\ YK11.getr regs 22 = w64 (3 * ns) /\
      YK11.getr regs 20 = w64 (3 * ns) /\
      YK11.getr regs 23 = w64 (out + 3 * ns * c) /\ YK11.getr regs 18 = w64 (res + 50 + 3 * c) /\
      YK11.getr regs 27 = w64 (out + 3 * ns * (c + 1)) /\
      YK11.getr regs 24 = w64 (out + 3 * ns * c + 3 * k) /\
      YK11.getr regs 25 = w64 (res + 50 + 3 * c + 3 * nch * k) /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - 8192 <= a < d_sp1 cx + 120) ->
         aview decodesegs0 (w_H W5) mem a = aview decodesegs0 (w_H W5) mem5 a) /\
      (forall a, apresent (w_H W5) mem5 a -> apresent (w_H W5) mem a) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 8 res /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 16 (d_SH cx) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 24 (d_F cx) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 32 (ns mod 2 ^ 32) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 40 SHADOW_OFF /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 48 (d_F cx) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 56 (dec_a_len (d_n cx)) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 64 (res + 50) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 72 out /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 80 (nch mod 2 ^ 32) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 88 (ns mod 2 ^ 64) /\
      dec_a_slot cx (aview decodesegs0 (w_H W5) mem) 112 (d_F cx).

(* the seat of a state of the double loop: registers as atoms, the spill area as cmp_spill1 *)
Lemma cmp_seat1 : forall (cx : dctx) (W : world decodesegs0) regs mem (pc : Z) res out mode nch ns,
  YK11.getr regs 9 = w64 (d_sp1 cx) ->
  140735332483072 <= d_sp1 cx <= 140737488355328 -> d_sp1 cx mod 32 = 0 ->
  d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 ->
  (forall a, d_sp0 cx - 32768 <= a < d_sp0 cx -> apresent (w_H W) mem a) ->
  0 <= res -> res + 50 < 2 ^ 64 ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 8 res ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 16 (d_SH cx) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 24 (d_F cx) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 32 (ns mod 2 ^ 32) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 40 SHADOW_OFF ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 48 (d_F cx) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 56 (dec_a_len (d_n cx)) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 64 (res + 50) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 72 out ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 80 (nch mod 2 ^ 32) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 88 (ns mod 2 ^ 64) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 112 (d_F cx) ->
  st_ok_pi pa_segs pa_val
    (Eimg (Ereg regs (cmp_extra res out (d_F cx) (d_SH cx) (dec_a_len (d_n cx)) (nch mod 2 ^ 32)
       (ns mod 2 ^ 32) mode (dec_a_olen nch ns) (nch mod 2 ^ 64) (ns mod 2 ^ 64))))
    (mkSS pc sr_atoms [cmp_spill1] None cmp_facts0)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (pa_val A_TEXT + pc)) mem (YK11.seg_rom pa_segs))).
Proof.
intros cx W regs mem pc res out mode nch ns R9 Hsp Hsp32 Hsp240 Hpres Hres0 Hres50
  S8 S16 S24 S32 S40 S48 S56 S64 S72 S80 S88 S112.
unfold dec_a_slot in *.
pose proof (cmp_ew regs res out (d_F cx) (d_SH cx) (dec_a_len (d_n cx)) (nch mod 2 ^ 32)
  (ns mod 2 ^ 32) mode (dec_a_olen nch ns) (nch mod 2 ^ 64) (ns mod 2 ^ 64)) as
  (A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43).
cbn zeta in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43.
set (EX := cmp_extra res out (d_F cx) (d_SH cx) (dec_a_len (d_n cx)) (nch mod 2 ^ 32)
  (ns mod 2 ^ 32) mode (dec_a_olen nch ns) (nch mod 2 ^ 64) (ns mod 2 ^ 64)) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (Eimg (Ereg regs EX)) n = ew (Ereg regs EX) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs EX)) 9%nat) = d_sp1 cx).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs EX 9%nat 9%bv eq_refl), R9.
  unfold w64. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx.
apply (pa_entry_st_ok_full (PI := PI_decode)).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold cmp_spill1, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp.
  split; [lia|]. split; [lia|].
  split.
  { intros o Ho. apply (apresent_writable decodesegs0). apply Hpres. lia. }
  pose proof (cmp_rdw_range W mem _ _ S8) as R8b.
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (cmp_chunk _ W mem 33%nat (d_sp1 cx) 8 res); [rewrite EL by (unfold A_TEXT; lia); exact A33 | exact S8].
  + apply (cmp_chunk _ W mem 36%nat (d_sp1 cx) 16 (d_SH cx)); [rewrite EL by (unfold A_TEXT; lia); exact A36 | exact S16].
  + apply (cmp_chunk _ W mem 35%nat (d_sp1 cx) 24 (d_F cx)); [rewrite EL by (unfold A_TEXT; lia); exact A35 | exact S24].
  + apply (cmp_chunk _ W mem 39%nat (d_sp1 cx) 32 (ns mod 2 ^ 32)); [rewrite EL by (unfold A_TEXT; lia); exact A39 | exact S32].
  + apply (cmp_chunk _ W mem 32%nat (d_sp1 cx) 40 SHADOW_OFF); [rewrite EL by (unfold A_TEXT; lia); exact A32 | exact S40].
  + apply (cmp_chunk _ W mem 35%nat (d_sp1 cx) 48 (d_F cx)); [rewrite EL by (unfold A_TEXT; lia); exact A35 | exact S48].
  + apply (cmp_chunk _ W mem 37%nat (d_sp1 cx) 56 (dec_a_len (d_n cx))); [rewrite EL by (unfold A_TEXT; lia); exact A37 | exact S56].
  + apply (cmp_chunk_off _ W mem 33%nat (d_sp1 cx) 64 res 50); [rewrite EL by (unfold A_TEXT; lia); exact A33 | lia | lia | lia | exact S64].
  + apply (cmp_chunk _ W mem 34%nat (d_sp1 cx) 72 out); [rewrite EL by (unfold A_TEXT; lia); exact A34 | exact S72].
  + apply (cmp_chunk _ W mem 38%nat (d_sp1 cx) 80 (nch mod 2 ^ 32)); [rewrite EL by (unfold A_TEXT; lia); exact A38 | exact S80].
  + apply (cmp_chunk _ W mem 43%nat (d_sp1 cx) 88 (ns mod 2 ^ 64)); [rewrite EL by (unfold A_TEXT; lia); exact A43 | exact S88].
  + apply (cmp_chunk _ W mem 35%nat (d_sp1 cx) 112 (d_F cx)); [rewrite EL by (unfold A_TEXT; lia); exact A35 | exact S112].
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- unfold facts_ok, cmp_facts0.
  cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  split; [|split; [|exact I]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
    split; [lia|]. split; [change (2 ^ 5) with 32; exact Hsp32 | lia].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite EL by (unfold A_TEXT; lia). rewrite A32.
    unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    split; [unfold SHADOW_OFF; lia|]. split; [reflexivity | lia].
Qed.

(* The first half of one turn of the bcmp double loop, from the inner head +0x6e0 (cmp_inv) through the call of
   __interceptor_trampoline_bcmp at +0x6ec to its return at +0x6f0 (cmp_q6f0): the three bytes compared agree,
   so a0 = 0.  The second half, cmp_l34_after, and the turn cmp_l34_body are in
   LLVMFuzzerTestOneInput_seg_cmp_after.v. *)
Lemma cmp_l34_call : forall (cx : dctx) ly5 S5 (W5 : world decodesegs0) regs5 mem5 md5 res out nch ns,
  AR_laws decodesegs0 B ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc decodesegs0 B (decode_sigma DS___interceptor_trampoline_bcmp)) ->
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_a_core B cx ly5 S5 W5 regs5 mem5 md5 dec_ev_5fc ->
  Permutation (ablocks B ly5 S5) (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++
                                  [(out, dec_a_olen nch ns)]) ->
  CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
  garr8 decodesegs0 (mrestrict (w_H W5) mem5) res (map (fun b : byte => bv_unsigned b) (d_body cx)) ->
  garr8 decodesegs0 (mrestrict (w_H W5) mem5) out
    (map (fun b : byte => bv_unsigned b) (CPlain.plain_out (d_body cx) nch ns)) ->
  forall (c k : Z) (W : world decodesegs0) (c' : config),
    cmp_inv cx ly5 S5 W5 mem5 res out nch ns c k W c' ->
    SRr decodesegs0 W c' (cmp_q6f0 cx ly5 S5 W5 mem5 res out nch ns c k).
Proof.
intros cx ly5 S5 W5 regs5 mem5 md5 res out nch ns LAWS ABCMP HB Hcore5 Hperm5 HP Hres5 Hout5
  c k W c' Hinv.
destruct Hinv as (-> & Hc & Hk & regs & mem & md & -> & HJ & Rsp & Rs1 & Rs0 & Rgp & Rtp & Rs3 & Rs10 &
  Rs5 & Rs6 & Rs4 & Rs7 & Rs2 & Rs11 & Rs8 & Rs9 & KR & GR &
  S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S112).
pose proof Hcore5 as (HJ5 & Hfrs5 & R8 & R9 & Hsp5 & Hsp240 & Hsp32 & Rgp5 & Rtp5 & Hsaved5 &
  HF4096 & HF32 & HFpres5 & HFL5 & Hblk5 & Hgarr5).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrsj & Hnev & Hkj & J1 & J2 & J3 & J4 & Hgone & Hpres &
  Hstk & J5 & HQT).
pose proof Hstk as (Hsp0al & HstkP & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
unfold DEC_LLVMF_STK in Hslo, Hpres.
destruct (cmp_plain_pos _ _ _ _ HP) as (Hnch0 & Hns0 & Hprod).
assert (Hin_res : In (res, dec_a_len (d_n cx)) (ablocks B ly5 S5))
  by (apply (Permutation_in _ (Permutation_sym Hperm5)); apply in_or_app; right; cbn; auto).
assert (Hin_out : In (out, dec_a_olen nch ns) (ablocks B ly5 S5))
  by (apply (Permutation_in _ (Permutation_sym Hperm5)); apply in_or_app; right; cbn; auto).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_res) as (_ & Hres4096 & Hresc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_out) as (_ & Hout4096 & Houtc & _).
pose proof (cmp_plain_len _ _ _ _ HP) as Hlen.
assert (Hreq_len : req_size (dec_a_len (d_n cx)) = 1492) by (rewrite Hlen; reflexivity).
assert (Holen : dec_a_olen nch ns = 3 * nch * ns)
  by (unfold dec_a_olen; replace ((0 <? nch) && (0 <? ns))%bool with true; [reflexivity|];
      symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
assert (Hreq_olen : req_size (dec_a_olen nch ns) = 3 * nch * ns)
  by (rewrite Holen; unfold req_size; destruct (Z.eqb_spec (3 * nch * ns) 0); [nia | reflexivity]).
rewrite Hreq_len in Hresc. rewrite Hreq_olen in Houtc.
pose proof (cmp_seat1 cx W5 regs mem 0x6e0 res out 0 nch ns Rs1 ltac:(lia) Hsp32 Hsp240 Hpres
  ltac:(lia) ltac:(lia) S8 S16 S24 S32 S40 S48 S56 S64 S72 S80 S88 S112) as HS.
set (EX := cmp_extra res out (d_F cx) (d_SH cx) (dec_a_len (d_n cx)) (nch mod 2 ^ 32)
  (ns mod 2 ^ 32) 0 (dec_a_olen nch ns) (nch mod 2 ^ 64) (ns mod 2 ^ 64)) in *.
pose proof (Eimg_env (Ereg regs EX)) as HEI.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (Eimg (Ereg regs EX)) n = ew (Ereg regs EX) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs EX)) 9%nat) = d_sp1 cx).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs EX 9%nat 9%bv eq_refl), Rs1.
  unfold w64. apply unsigned_lit_small. lia. }
assert (SHOK : sh_ok pa_segs (SOff 32%nat 0) (@nil shent) (Eimg (Ereg regs EX))
                 (mrestrict (w_H W5) mem)) by apply Forall_nil.
change (w64 (DEC_A_LLVMF + 0x6e0)) with (Z_to_bv 64 (pa_val A_TEXT + 0x6e0)).
change decodesegs0 with pa_segs.
(* +0x6e0 .. +0x6ec: a2 := 3, a0 := s8, a1 := s9, the call *)
paj_run_tok (paj_run (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) HS HJ SHOK Bspan;
  [ cmp_awr1 (d_sp1 cx) (d_sp0 cx) Usp |].
(* the call of __interceptor_trampoline_bcmp (x, y, 3) with x = out + 3*(ns*c + k), y = res + 50 + 3*(c + nch*k) *)
set (X := out + 3 * ns * c + 3 * k) in *.
set (Y := res + 50 + 3 * c + 3 * nch * k) in *.
assert (HXb : X + 3 <= out + 3 * nch * ns) by (subst X; nia).
assert (HYb : Y + 3 <= res + 50 + 3 * nch * ns) by (subst Y; nia).
assert (HX0 : out <= X) by (subst X; nia).
assert (HY0 : res + 50 <= Y) by (subst Y; nia).
assert (B24 : ew (Eimg (Ereg regs EX)) 24%nat = w64 X)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs EX 24%nat 24%bv eq_refl); exact Rs8).
assert (B25 : ew (Eimg (Ereg regs EX)) 25%nat = w64 Y)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs EX 25%nat 25%bv eq_refl); exact Rs9).
assert (B2 : ew (Eimg (Ereg regs EX)) 2%nat = w64 (d_sp1 cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs EX 2%nat 2%bv eq_refl); exact Rsp).
assert (B3 : ew (Eimg (Ereg regs EX)) 3%nat = w64 (as_gp B))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs EX 3%nat 3%bv eq_refl); exact Rgp).
assert (B4 : ew (Eimg (Ereg regs EX)) 4%nat = w64 (as_tp B))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs EX 4%nat 4%bv eq_refl); exact Rtp).
cmp_reg HS (10%bv : bv 5) Pa0. cmp_reg HS (11%bv : bv 5) Pa1. cmp_reg HS (12%bv : bv 5) Pa2.
cmp_reg HS (1%bv : bv 5) Pra. cmp_reg HS (2%bv : bv 5) Psp. cmp_reg HS (3%bv : bv 5) Pgp.
cmp_reg HS (4%bv : bv 5) Ptp.
assert (Q10 : YK11.getr (ms_regs ms) 10 = w64 X) by (rewrite Pa0; apply cmp_den_atom; exact B24).
assert (Q11 : YK11.getr (ms_regs ms) 11 = w64 Y) by (rewrite Pa1; apply cmp_den_atom; exact B25).
assert (Q12 : YK11.getr (ms_regs ms) 12 = w64 3) by (rewrite Pa2; reflexivity).
assert (Q1 : YK11.getr (ms_regs ms) 1 = Z_to_bv 64 (pa_val A_TEXT + 1776))
  by (rewrite Pra; apply codeptr_val; exact HEI).
assert (Q3 : YK11.getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Pgp; apply cmp_den_atom; exact B3).
assert (Q4 : YK11.getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Ptp; apply cmp_den_atom; exact B4).
assert (Q2 : spZ (ms_regs ms) = d_sp0 cx + (d_sp1 cx - d_sp0 cx)).
{ unfold spZ. rewrite Psp, (cmp_den_atom _ 2 _ B2). unfold w64. rewrite unsigned_lit_small by lia. lia. }
clear Pa0 Pa1 Pa2 Pra Psp Pgp Ptp.
(* what the run +0x6e0..+0x6ec kept: the registers it does not write, the spill area, the memory outside it *)
lazymatch type of HS with st_ok ?sg ?Ex ?ssx (restrict (w_H W5) ?msx) =>
  assert (HAE : env_agree 32 (Ereg regs EX) Ex)
    by (split; [intros nn Hnn; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
               | reflexivity]);
  pose proof (regs_kept_of_st_ok sg Ex ssx (restrict (w_H W5) msx) regs EX
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv]
    HS HAE ltac:(vm_compute; reflexivity)) as KRg;
  let rr0 := eval vm_compute in (nth_error (ss_mem ssx) 0) in
  lazymatch rr0 with Some ?r0 =>
    assert (HRf : region_ok decodesegs0 Ex (mrestrict (w_H W5) (ms_mem msx)) r0)
      by exact (st_ok_region_nth (segs := sg) Ex ssx _ 0 r0 HS eq_refl) end
end.
cmp_kupd (d_sp1 cx) Usp KR GR.
pose proof (cmp_ew regs res out (d_F cx) (d_SH cx) (dec_a_len (d_n cx)) (nch mod 2 ^ 32)
  (ns mod 2 ^ 32) 0 (dec_a_olen nch ns) (nch mod 2 ^ 64) (ns mod 2 ^ 64)) as
  (A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43).
cbn zeta in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43. fold EX in A32, A33, A34, A35, A36,
  A37, A38, A39, A40, A41, A42, A43.
rewrite <- EL in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43 by (unfold A_TEXT; lia).
pose proof (cmp_rdw_range _ _ _ _ S112) as HFr64.
assert (HSH64 : 0 <= d_SH cx < 2 ^ 64) by (pose proof (cmp_rdw_range _ _ _ _ S16); lia).
assert (Hlen64 : 0 <= dec_a_len (d_n cx) < 2 ^ 64) by (pose proof (cmp_rdw_range _ _ _ _ S56); lia).
assert (Hb32 : forall z, 0 <= z mod 2 ^ 32 < 2 ^ 64) by (intros z; pose proof (Z.mod_pos_bound z (2 ^ 32)); lia).
assert (Hb64 : forall z, 0 <= z mod 2 ^ 64 < 2 ^ 64) by (intros z; apply Z.mod_pos_bound; lia).
pose proof (cmp_unseat1 _ W5 (ms_mem ms) cx res out nch ns HRf Usp
  ltac:(rewrite A33; unfold w64; apply unsigned_lit_small; lia)
  ltac:(rewrite A36; unfold w64; apply unsigned_lit_small; lia)
  ltac:(rewrite A35; unfold w64; apply unsigned_lit_small; lia)
  ltac:(rewrite A39; unfold w64; apply unsigned_lit_small; apply Hb32)
  ltac:(rewrite A32; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
  ltac:(rewrite A37; unfold w64; apply unsigned_lit_small; lia)
  ltac:(rewrite A34; unfold w64; apply unsigned_lit_small; lia)
  ltac:(rewrite A38; unfold w64; apply unsigned_lit_small; apply Hb32)
  ltac:(rewrite A43; unfold w64; apply unsigned_lit_small; apply Hb64)
  ltac:(lia)) as (U8 & U16 & U24 & U32 & U40 & U48 & U56 & U64 & U72 & U80 & U88 & U112).
pmkst HS.
lazymatch goal with |- context [with_vm_backing ?a ?b ?c] => set (mdv := with_vm_backing a b c) in * end.
clearbody mdv.
pose proof (proj1 HJ) as HARc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin_out) as (_ & _ & _ & _ & Hopres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin_res) as (_ & _ & _ & _ & Hrpres & _).
rewrite Hreq_olen in Hopres. rewrite Hreq_len in Hrpres.
eapply SRr_bind.
{ eapply (aj_bcmp_at (@pa_segs rc decode_listing (@PI_decode rc)) B
    (LAWS : AR_laws (@pa_segs rc decode_listing (@PI_decode rc)) B) (@pa_segs_low rc decode_listing (@PI_decode rc))
    (decode_sigma DS___interceptor_trampoline_bcmp)
    (ABCMP fx : @abcmp_realizes fx rc (@pa_segs rc decode_listing (@PI_decode rc)) B
                  (decode_sigma DS___interceptor_trampoline_bcmp))
    W5 (ms_regs ms) (ms_mem ms) DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly5 S5 mdv dec_ev_5fc X Y 3 (d_sp1 cx - d_sp0 cx)
    (Z_to_bv 64 (pa_val A_TEXT + 1776)) HJ Q10 Q11 Q12);
  [ lia | lia | lia | lia | lia | exact Q2 | lia | lia | unfold ESTACK, DEC_LLVMF_STK; lia
  | exact Q3 | exact Q4 | exact Q1 | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros a Ha; split;
    [ apply aview_some_of_apresent; apply (proj1 (Hopres a ltac:(lia))) | rewrite Q2; unfold ESTACK; lia ]
  | intros a Ha; split;
    [ apply aview_some_of_apresent; apply (proj1 (Hrpres a ltac:(lia))) | rewrite Q2; unfold ESTACK; lia ]
  | intros a Ha; unfold ESTACK; lia
  | intros a Ha; unfold ESTACK; lia
  | eapply (amem_range_of_block _ B LAWS _ _ _ _ _ _ _ _ _ HARc Hin_out); rewrite ?Hreq_olen; lia
  | eapply (amem_range_of_block _ B LAWS _ _ _ _ _ _ _ _ _ HARc Hin_res); rewrite ?Hreq_len; lia
  | eapply (range_addressable_of_block _ B LAWS _ _ _ _ _ _ _ _ _ HARc Hin_out); rewrite ?Hreq_olen; lia
  | intros _; eapply (shadow_hull_vis_of_block _ B LAWS _ _ _ _ _ _ _ _ _ HARc Hin_out);
    rewrite ?Hreq_olen; lia
  | eapply (range_addressable_of_block _ B LAWS _ _ _ _ _ _ _ _ _ HARc Hin_res); rewrite ?Hreq_len; lia
  | intros _; eapply (shadow_hull_vis_of_block _ B LAWS _ _ _ _ _ _ _ _ _ HARc Hin_res);
    rewrite ?Hreq_len; lia ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hveq & Hkeep2 & Hpres2).
(* the three bytes compared agree (the braid relation), so bcmp returned 0 *)
assert (HLEN : d_n cx = Z.of_nat (length (d_pl cx))).
{ pose proof HB as HB'. unfold dec_a_base, dec_lib_pre_x in HB'.
  destruct HB' as (_Hafn & _Hra & _Ha0 & _Ha1 & _Hblk & Hl & _). exact Hl. }
assert (Hbl : Z.of_nat (length (d_body cx)) = 1492)
  by (unfold d_body; rewrite (cmp_body_len (d_pl cx) (d_n cx) HLEN); exact Hlen).
assert (Hwin : forall a, 4096 <= a < alloc_ceiling -> 0 <= a < 2 ^ 64 /\ ~ (d_sp1 cx - 8192 <= a < d_sp1 cx + 120))
  by (intros a Ha; split; lia).
assert (Hv0 : v = w64 0).
{ apply (proj2 Hveq). intros i Hi.
  destruct (Hwin (X + i) ltac:(subst X; nia)) as [HXa HXn].
  destruct (Hwin (Y + i) ltac:(subst Y; nia)) as [HYa HYn].
  transitivity (aview decodesegs0 (w_H W5) mem5 (X + i)); [exact (KR (X + i) HXa HXn)|].
  transitivity (aview decodesegs0 (w_H W5) mem5 (Y + i)); [|symmetry; exact (KR (Y + i) HYa HYn)].
  subst X Y.
  exact (cmp_bytes_eq _ _ _ (d_body cx) res out nch ns c k i Hres5 Hout5 Hbl Hnch0 Hns0 Hprod Hc Hk Hi). }
(* the registers the call keeps (callee-saved) and the run kept *)
assert (Hcs : forall rr : bv 5,
  In rr [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  YK11.getr regs2 rr = YK11.getr regs rr).
{ intros rr Hrr. rewrite (cmp_pres_lit (ms_regs ms) regs2 rr HP2); [exact (KRg rr Hrr)|].
  cbn [In] in Hrr.
  repeat (destruct Hrr as [<- | Hrr];
          [unfold acallee_saved; vm_compute; repeat (first [left; reflexivity | right]); split; discriminate|]).
  destruct Hrr. }
(* the memory: bcmp wrote only below sp, the run only the spill area *)
assert (Hk2 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - 8192 <= a < d_sp1 cx) ->
  aview decodesegs0 (w_H W5) mem2 a = aview decodesegs0 (w_H W5) (ms_mem ms) a)
  by (intros a Ha Hn; apply Hkeep2; [exact Ha | unfold ESTACK; lia]).
apply SRr_ret. unfold cmp_q6f0.
split; [reflexivity|]. split; [exact Hc|]. split; [exact Hk|].
exists regs2, mem2, md2.
split; [reflexivity|].
split; [exact HJ2|].
split; [rewrite (Hcs 2%bv) by cmp_in; exact Rsp|].
split; [rewrite (Hcs 9%bv) by cmp_in; exact Rs1|].
split; [rewrite (Hcs 8%bv) by cmp_in; exact Rs0|].
split; [rewrite (Hcs 3%bv) by cmp_in; exact Rgp|].
split; [rewrite (Hcs 4%bv) by cmp_in; exact Rtp|].
split; [rewrite Hv; exact Hv0|].
split; [rewrite (Hcs 19%bv) by cmp_in; exact Rs3|].
split; [rewrite (Hcs 26%bv) by cmp_in; exact Rs10|].
split; [rewrite (Hcs 21%bv) by cmp_in; exact Rs5|].
split; [rewrite (Hcs 22%bv) by cmp_in; exact Rs6|].
split; [rewrite (Hcs 20%bv) by cmp_in; exact Rs4|].
split; [rewrite (Hcs 23%bv) by cmp_in; exact Rs7|].
split; [rewrite (Hcs 18%bv) by cmp_in; exact Rs2|].
split; [rewrite (Hcs 27%bv) by cmp_in; exact Rs11|].
split; [rewrite (Hcs 24%bv) by cmp_in; exact Rs8|].
split; [rewrite (Hcs 25%bv) by cmp_in; exact Rs9|].
split; [intros a Ha Hn; rewrite (Hk2 a Ha ltac:(lia)); exact (KR a Ha Hn)|].
split; [intros a Ha; exact (Hpres2 a (GR a Ha))|].
assert (SK : forall off v0, 8 <= off <= 112 ->
  dec_a_slot cx (aview decodesegs0 (w_H W5) (ms_mem ms)) off v0 ->
  dec_a_slot cx (aview decodesegs0 (w_H W5) mem2) off v0).
{ intros off v0 Hoff Hs. apply (cmp_slot_kept W5 (ms_mem ms) mem2 cx off v0); [|exact Hs].
  intros a Ha. apply Hk2; lia. }
split; [apply SK; [lia | exact U8]|]. split; [apply SK; [lia | exact U16]|].
split; [apply SK; [lia | exact U24]|]. split; [apply SK; [lia | exact U32]|].
split; [apply SK; [lia | exact U40]|]. split; [apply SK; [lia | exact U48]|].
split; [apply SK; [lia | exact U56]|]. split; [apply SK; [lia | exact U64]|].
split; [apply SK; [lia | exact U72]|]. split; [apply SK; [lia | exact U80]|].
split; [apply SK; [lia | exact U88]|]. apply SK; [lia | exact U112].
Qed.

End body.
End cmp.
