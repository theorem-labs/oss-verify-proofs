(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* LLVMFuzzerTestOneInput_seg_up: the `up` segment of the image-A walk of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput: offsets +0x748 .. +0x868 of the audited listing lib/A/Prog/DecodeList.v, i.e. the
   premise `llvm_a_up_stmt` of lib/A/Prog/LLVMFuzzerTestOneInput_segs.v's dec_llvmf_holds_of_segs.

   What the code does (map-code.md section 2, rows 0x748-0x868): it checks the channel count
   reac_upstream_channels returned against the geometry the harness recomputes from the body length
   (+0x74c..+0x79c, a division by 36 by the multiply-high constant of decode_obj 9 with the parity and range
   tests); it asks malloc for 36 * count bytes, or 1 byte when the count is not positive (+0x7a0..+0x7c0);
   it fills the buffer with 0xa5 (__asan_memset at +0x7d4); it calls reac_upstream_decode twice with a NULL
   argument (+0x7e4 with raw = NULL, +0x7f8 with out = NULL), each of which refuses and returns -1; it scans
   the buffer byte by byte with the instrumented 1-byte loads of loop L5 (+0x818..+0x854) and checks every byte
   is still 0xa5; and it calls reac_upstream_decode a third time, for real (+0x868).

   Every abort edge of the segment is refuted, never stepped (the statement asks the trap block +0xa4c..+0xb60 to
   be unreachable): +0x79c (the count disagrees), +0x7c4 (malloc returned NULL: the rule gives 4096 <= res),
   +0x800 / +0x804 (a refusing call did not return -1), +0x858 (a byte of the buffer changed), and the inline
   report call at +0x854 (the shadow slow path of L5, whose guard the engine's token discharge refutes). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0s YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow DecodeSyms DecodeList DecodePa.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaJournal DecodeImg DecodeCJ.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaStep DecodePaLib YC1g YC1h YC81 YC4b YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require DecodeShape Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require reac_upstream_channels_cg reac_upstream_decode_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require reac_decode_c reac_decode_plain_le_c
  reac_upstream_channels_c reac_upstream_decode_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require LLVMFuzzerTestOneInput_leafb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The offsets of this segment's cut points, from the function's entry (DecodeList.v line = offset / 4 + 28). *)
Definition UP_CHK : Z := 0x748.          (* the segment's entry: the return of reac_upstream_channels *)
Definition UP_CMP : Z := 0x79c.         (* the channel-count check *)
Definition UP_MALLOC_RA : Z := 0x7c4.    (* the return of malloc #3 *)
Definition UP_MEMSET_RA : Z := 0x7d8.    (* the return of __asan_memset *)
Definition UP_DEC1_RA : Z := 0x7e8.      (* the return of reac_upstream_decode #1 (raw = NULL) *)
Definition UP_DEC2_RA : Z := 0x7fc.      (* the return of reac_upstream_decode #2 (out = NULL) *)
Definition UP_LOOP : Z := 0x818.         (* the head of the scan loop L5 *)
Definition UP_TAIL : Z := 0x858.         (* the loop's exit, the `bnez a1` abort edge *)
Definition UP_DEC3_RA : Z := 0x86c.      (* the segment's exit: the return of reac_upstream_decode #3 *)

Module UCh := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_c.
Module UDe := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_decode_c.
Module LB := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.LLVMFuzzerTestOneInput_leafb.

(* A register's symbolic value, without unfolding its denotation (ReadName.v:408 rn_reg). *)
Ltac up_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.

(* This segment stores nothing, so every region of its symbolic states is read only and the engine's write
   obligation is the empty one. *)
Ltac up_awr :=
  lazymatch goal with
  | |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in
      change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx)
  end;
  repeat first [ apply awr_ok_nil
               | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|] ].

(* Stage B: a callee-saved register literal (acallee_saved of its number), and membership in a literal list. *)
Ltac upB_cs :=
  unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  lia.
Ltac upB_in := repeat first [ apply in_eq | apply in_cons ].

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac
   (LLVMFuzzerTestOneInput_seg_entry.v:430 reg_at, with the st_ok_pi case added). Stage D's form; the lane's
   own three-argument up_reg above is ReadName.v:408 rn_reg. *)
Ltac upD_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _);
         change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?valx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _);
         change (sv_denot Ex e = v); tac)
  end.

(* ------------------------------------------------------------------ *)
(* The segment's pure arithmetic: the division by 36, the channel count *)
(* reac_upstream_channels returns, the output length, and up_nch.       *)
(* ------------------------------------------------------------------ *)

(* The division by 36 the listing does at +0x758..+0x768: `ld a1,%lo(obj9)(a1)` loads the multiply-high
   constant, `mulhu a1,a2,a1` keeps the high 64 bits of the unsigned product, `srli a1,a1,5` shifts. *)
Definition up_div36 (x : Z) : Z := (x * UCh.UPSTREAM_DIV36) / 2 ^ 64 / 2 ^ 5.

Lemma up_div36_ok : forall x, 0 <= x < 2 ^ 32 -> up_div36 x = x / 36.
Proof.
  intros x Hx. unfold up_div36. rewrite Z.div_div by lia.
  pose proof (Z.div_mod x 36 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 36 ltac:(lia)) as B.
  symmetry. apply (Z.div_unique _ _ _ (28 * (x / 36) + (x mod 36) * UCh.UPSTREAM_DIV36));
    unfold UCh.UPSTREAM_DIV36.
  - left. split; [lia|]. cbn. lia.
  - cbn. lia.
Qed.

Lemma up_chan_cases : forall len, 0 <= len < 2 ^ 26 ->
  (len < 52 -> UCh.upstream_result len = -1) /\
  (52 <= len -> (len - 52) mod 36 <> 0 -> UCh.upstream_result len = -1) /\
  (52 <= len -> (len - 52) mod 36 = 0 -> ((len - 52) / 36 < 2 \/ 40 < (len - 52) / 36) ->
     UCh.upstream_result len = -1) /\
  (52 <= len -> (len - 52) mod 36 = 0 -> 2 <= (len - 52) / 36 <= 40 -> Z.odd ((len - 52) / 36) = true ->
     UCh.upstream_result len = -1) /\
  (52 <= len -> (len - 52) mod 36 = 0 -> 2 <= (len - 52) / 36 <= 40 -> Z.even ((len - 52) / 36) = true ->
     UCh.upstream_result len = (len - 52) / 36).
Proof.
  intros len Hlen.
  assert (HR : UCh.upstream_result len =
    if (52 <=? len) && ((len - 52) mod 36 =? 0) && Z.even ((len - 52) / 36) &&
       (2 <=? (len - 52) / 36) && ((len - 52) / 36 <=? 40) then (len - 52) / 36 else -1).
  { unfold UCh.upstream_result, UCh.upstream_ok, UCh.upstream_width.
    destruct (Z.leb_spec 52 len) as [H52|H52]; [|reflexivity].
    rewrite (Z.mod_small ((len - 52) / 36) (2 ^ 32)); [reflexivity|].
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite HR. clear HR. rewrite <- Z.negb_even.
  pose proof (Z.div_mod (len - 52) 36 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (len - 52) 36 ltac:(lia)) as Hm.
  set (w := (len - 52) / 36) in *. set (r := (len - 52) mod 36) in *. clearbody w r.
  destruct (Z.leb_spec 52 len); destruct (Z.eqb_spec r 0); destruct (Z.even w);
    destruct (Z.leb_spec 2 w); destruct (Z.leb_spec w 40); cbn [andb negb];
    repeat split; intros; solve [reflexivity | lia | congruence].
Qed.

Lemma up_cnt_range : forall len, 0 <= len < 2 ^ 26 ->
  UCh.upstream_result len = -1 \/
  (2 <= UCh.upstream_result len <= 40 /\ Z.even (UCh.upstream_result len) = true /\
   len = 52 + 36 * UCh.upstream_result len).
Proof.
  intros len Hlen. destruct (up_chan_cases len Hlen) as (H1 & H2 & H3 & H4 & H5).
  destruct (Z_lt_le_dec len 52) as [Hl|Hl]; [left; exact (H1 Hl)|].
  destruct (Z.eq_dec ((len - 52) mod 36) 0) as [Hm|Hm]; [|left; exact (H2 Hl Hm)].
  destruct (Z_lt_le_dec ((len - 52) / 36) 2) as [Hw|Hw]; [left; exact (H3 Hl Hm (or_introl Hw))|].
  destruct (Z_lt_le_dec 40 ((len - 52) / 36)) as [Hw'|Hw']; [left; exact (H3 Hl Hm (or_intror Hw'))|].
  destruct (Bool.bool_dec (Z.even ((len - 52) / 36)) true) as [He|He].
  - right. rewrite (H5 Hl Hm (conj Hw Hw') He). split; [lia|]. split; [exact He|].
    pose proof (Z.div_mod (len - 52) 36 ltac:(lia)) as Hd. lia.
  - left. apply Bool.not_true_is_false in He. apply (H4 Hl Hm (conj Hw Hw')).
    rewrite <- Z.negb_even, He. reflexivity.
Qed.

Lemma up_olen_val : forall len, 0 <= len < 2 ^ 26 ->
  (UCh.upstream_result len <= 0 -> dec_a_uolen (UCh.upstream_result len) = 1) /\
  (0 < UCh.upstream_result len -> dec_a_uolen (UCh.upstream_result len) = 36 * UCh.upstream_result len) /\
  1 <= dec_a_uolen (UCh.upstream_result len) <= 1440.
Proof.
  intros len Hlen. unfold dec_a_uolen.
  destruct (up_cnt_range len Hlen) as [H | (H1 & _ & _)];
    destruct (Z.ltb_spec 0 (UCh.upstream_result len)); cbv beta iota;
    repeat split; intros; lia.
Qed.

Lemma up_nch_result : forall len, 0 <= len < 2 ^ 26 ->
  (0 <= UCh.upstream_result len -> UDe.up_nch len = UCh.upstream_result len) /\
  (UCh.upstream_result len < 0 -> UDe.up_nch len = -1).
Proof.
  intros len Hlen.
  assert (HR : UCh.upstream_result len =
    if (52 <=? len) && ((len - 52) mod 36 =? 0) && Z.even ((len - 52) / 36) &&
       (2 <=? (len - 52) / 36) && ((len - 52) / 36 <=? 40) then (len - 52) / 36 else -1).
  { unfold UCh.upstream_result, UCh.upstream_ok, UCh.upstream_width.
    destruct (Z.leb_spec 52 len) as [H52|H52]; [|reflexivity].
    rewrite (Z.mod_small ((len - 52) / 36) (2 ^ 32)); [reflexivity|].
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite HR. clear HR. unfold UDe.up_nch. rewrite Zmod_even.
  pose proof (Z.div_mod (len - 52) 36 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (len - 52) 36 ltac:(lia)) as Hm.
  set (w := (len - 52) / 36) in *. set (r := (len - 52) mod 36) in *. clearbody w r.
  destruct (Z.leb_spec 124 len); destruct (Z.leb_spec 52 len); destruct (Z.eqb_spec r 0);
    destruct (Z.even w); destruct (Z.leb_spec 2 w); destruct (Z.leb_spec w 40);
    cbn [andb Z.eqb]; split; intros; solve [reflexivity | lia].
Qed.

Section up.
Context {rc : YM05.RunCeil}.
(* The Section of lib/A/Prog/LLVMFuzzerTestOneInput_segs.v:168-183, variable for variable, so that
   llvm_a_up_stmt can be stated here at the same arguments. *)
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
Local Notation segs := decodesegs0.
(* The slot pre of lib/A/Prog/LLVMFuzzerTestOneInput_segs.v:246 at this Section's arguments. *)
Local Notation up_base cx :=
  (dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx).

(* The three values the segment's own arithmetic names: the body length the harness decoded (s10), the channel
   count reac_upstream_channels returned (s6, checked at +0x79c against the harness's own geometry) and the
   number of bytes the harness asks malloc for (s8). *)
Definition up_len (cx : dctx) : Z := dec_a_len (d_n cx).
Definition up_cnt (cx : dctx) : Z := CChan.upstream_result (up_len cx).
Definition up_sz (cx : dctx) : Z := dec_a_uolen (up_cnt cx).

(* The bytes of the caller's memory this segment reads and must carry to its post: the 13 saved words, the
   realigned spill slots, the fake frame and its eight shadow bytes, the caller's payload, and the body copy.
   The mode geometry is NOT here: a table mode lies in the image, where a call keeps a byte only under the
   allocator's own ownership side conditions, and is carried by up_mode_kept instead. *)
Definition up_touch (cx : dctx) (res : Z) (a : Z) : Prop :=
  (d_sp0 cx - 104 <= a < d_sp0 cx) \/
  (d_sp1 cx + 8 <= a < d_sp1 cx + 120) \/
  (d_F cx <= a < d_F cx + 64) \/
  (d_SH cx <= a < d_SH cx + 8) \/
  (d_p cx <= a < d_p cx + d_n cx) \/
  (res <= a < res + up_len cx).

(* Everything llvm_a_st_748 and llvm_a_st_86c say about memory, at one world and memory. *)
Definition up_mem (cx : dctx) (res mode nch ns : Z) (W' : world segs) (mem' : word -> option byte) : Prop :=
  dec_a_saved cx (aview segs (w_H W') mem') /\
  (forall a, d_F cx <= a < d_F cx + 64 -> apresent (w_H W') mem' a) /\
  rdword (aview segs (w_H W') mem') (d_F cx + 56) = Some (d_FL cx) /\
  garr8 segs (mrestrict (w_H W') mem') (d_p cx) (map (fun b : byte => bv_unsigned b) (d_pl cx)) /\
  dec_a_mode_ok cx W' mem' mode nch ns /\
  dec_a_fsh cx (aview segs (w_H W') mem') 0 4 /\
  garr8 segs (mrestrict (w_H W') mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
  (CPlain.plain_ok (up_len cx) (d_body cx) nch ns = true ->
     dec_a_slot cx (aview segs (w_H W') mem') 8 res /\
     dec_a_slot cx (aview segs (w_H W') mem') 16 (d_SH cx) /\
     dec_a_slot cx (aview segs (w_H W') mem') 24 (d_F cx) /\
     dec_a_slot cx (aview segs (w_H W') mem') 48 (d_F cx)) /\
  dec_a_slot cx (aview segs (w_H W') mem') 40 SHADOW_OFF /\
  dec_a_slot cx (aview segs (w_H W') mem') 56 (up_len cx) /\
  dec_a_slot cx (aview segs (w_H W') mem') 64 (res + 50) /\
  dec_a_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* The part of dec_a_core that is a fact about the entry context alone. *)
Definition up_geom (cx : dctx) : Prop :=
  d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 /\ d_sp1 cx mod 32 = 0 /\
  4096 <= d_F cx /\ d_F cx mod 32 = 0.

(* The state at every point of the segment: dec_a_core's state clauses, the blocks (up to order), the frame
   registers, the three callee-saved registers the segment reads, and up_mem. *)
Definition up_run (cx : dctx) (res mode nch ns : Z) (bl : list (Z * Z)) (k : Z)
    (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) : Prop :=
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' W' mem' md' k /\
  frames S' = [(DEC_FCLASS, d_fpos cx)] /\
  YK11.getr regs' 8 = w64 (d_sp0 cx) /\ YK11.getr regs' 9 = w64 (d_sp1 cx) /\ spZ regs' = d_sp1 cx /\
  YK11.getr regs' 3 = w64 (as_gp B) /\ YK11.getr regs' 4 = w64 (as_tp B) /\
  (0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B ly' S')) /\
  Permutation (ablocks B ly' S') bl /\
  dec_a_fr cx regs' /\
  YK11.getr regs' 18 = w64 SHADOW_OFF /\
  YK11.getr regs' 20 = w64 res /\
  YK11.getr regs' 26 = w64 (up_len cx) /\
  up_mem cx res mode nch ns W' mem'.

(* The blocks at the segment's entry and after malloc #3. *)
Definition up_bl0 (cx : dctx) (res : Z) : list (Z * Z) :=
  ablocks B (d_ly cx) (d_S cx) ++ [(res, up_len cx)].
Definition up_bl1 (cx : dctx) (res upb : Z) : list (Z * Z) :=
  up_bl0 cx res ++ [(upb, up_sz cx)].

(* ---------------------------------------------------------------- *)
(* The engine's picture of this segment                              *)
(* ---------------------------------------------------------------- *)

(* The listing's base is the function's entry (AF_LLVMFuzzerTestOneInput = 0). *)
Lemma up_base_eq : pa_val A_TEXT = DEC_A_LLVMF.
Proof. vm_compute. reflexivity. Qed.

(* A decidable witness for "a is one of the read-only bytes the walks read" (check_round_trip_cg.v DEC_RO_RD). *)
Definition up_rd_b (a : Z) : bool :=
  existsb (fun r : Z * Z => ((fst r <=? a) && (a <? fst r + snd r))%bool) DEC_RO_RD.
Lemma up_rd_of_b : forall a, up_rd_b a = true -> dec_in_ro_rd a.
Proof.
  intros a H. unfold up_rd_b in H. apply existsb_exists in H as (r & Hin & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  unfold dec_in_ro_rd. apply Exists_exists. exists r. split; [exact Hin|]. unfold in_zr. lia.
Qed.

(* One row of dec_crt_cells, found by its statement (LLVMFuzzerTestOneInput_leafb.v dec_leafb_row with
   eassumption, so a row's value may be left for the row to give): rows may be added or removed. *)
Ltac up_md_row HC ly := let H := fresh "Hrow" in pose proof (HC ly) as H;
  repeat match type of H with _ /\ _ => let A := fresh "Hrow" in destruct H as [A H] end; eassumption.

(* An 8-byte constant cell of B reads its value at any state AR holds of (am_const, YG0n.v:211):
   lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_rom.v up_const_val (a Theorem Labs lane 569efeb43b0), copied. *)
Lemma up_const_val : forall ly S (W : world segs) mem md a e,
  AR segs B ly S W mem md -> In (c8 (ANum a) e) (as_const B ly) ->
  val_mem segs (mrestrict (w_H W) mem) a 8 (aeval B ly e).
Proof.
intros ly S W mem md a e HAR Hin.
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ Hin) as Hc.
unfold cell_holds, c8 in Hc. cbn [c_at YG0f.c_val c_w] in Hc. change (aeval B ly (ANum a)) with a in Hc.
intros k Hk. specialize (Hc k Hk). unfold aview in Hc.
destruct (mbyte segs (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|]; [|discriminate].
injection Hc as Hc. unfold YO0f.le_byte, YG0f.le_byte in *. rewrite <- Hc. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* The multiply-high constant the listing loads at +0x75c (PLdHi .. (A_OBJ 9) .. SZ8 true), at decode_obj 9 =
   UPSTREAM_DIV36_AT: an owned constant cell of B (dec_crt_cells' row for decode_obj 9), so AR reads it at every
   state (after lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_rom.v up_div36_val). *)
Lemma up_obj9_val : forall ly S (W : world segs) mem md,
  dec_crt_cells B -> AR segs B ly S W mem md ->
  val_mem segs (mrestrict (w_H W) mem) (decode_obj 9) 8 UCh.UPSTREAM_DIV36.
Proof.
  intros ly S W mem md HC HAR.
  assert (Hrow : In (c8 (ANum (decode_obj 9%nat)) (ANum UCh.UPSTREAM_DIV36)) (as_const B ly))
    by (up_md_row HC ly).
  exact (up_const_val ly S W mem md (decode_obj 9) (ANum UCh.UPSTREAM_DIV36) HAR Hrow).
Qed.

(* The symbolic state the walk enters the segment with: every register is its own atom, the only region is the
   read-only constant at decode_obj 9, and the only fact is that the shadow base in s2 is SHADOW_OFF. *)
Definition up_facts : facts := mkFacts [(18%nat, mkAF SB SB 0)] [] [].
Definition up_obj9 : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 9)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit UCh.UPSTREAM_DIV36))].
Definition ss_up_at (k : Z) : sstate := mkSS k sr_atoms [up_obj9] None up_facts.


(* ---------------------------------------------------------------- *)
(* Keeping up_mem across a call.                                     *)
(* ---------------------------------------------------------------- *)

(* The 13 saved words lie at d_sp0 - 104 .. d_sp0 - 8 (each 8 bytes). *)
Lemma up_saved_at_rng : forall o, In o dec_a_saved_at -> 8 <= fst o <= 104.
Proof.
intros o Ho. unfold dec_a_saved_at in Ho. cbn [In] in Ho.
repeat (destruct Ho as [Ho | Ho]; [subst o; cbn [fst]; lia |]). destruct Ho.
Qed.

(* A word whose eight bytes the call kept reads the same. *)
Lemma up_rdword_kept : forall (cx : dctx) (res : Z) (W1 W2 : world segs) m1 m2 a,
  (forall a, up_touch cx res a -> aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  (forall k, 0 <= k < 8 -> up_touch cx res (a + k)) ->
  rdword (aview segs (w_H W2) m2) a = rdword (aview segs (w_H W1) m1) a.
Proof.
intros cx res W1 W2 m1 m2 a HT Hin. apply rdword_ext. intros k Hk. apply HT, Hin, Hk.
Qed.

(* A spill slot inside s1 + 8 .. s1 + 120 is kept. *)
Lemma up_slot_kept : forall (cx : dctx) (res : Z) (W1 W2 : world segs) m1 m2 off v,
  (forall a, up_touch cx res a -> aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  8 <= off <= 112 ->
  dec_a_slot cx (aview segs (w_H W1) m1) off v -> dec_a_slot cx (aview segs (w_H W2) m2) off v.
Proof.
intros cx res W1 W2 m1 m2 off v HT Ho HS. unfold dec_a_slot in *.
rewrite (up_rdword_kept cx res W1 W2 m1 m2 _ HT); [exact HS|].
intros k Hk. unfold up_touch. right; left. lia.
Qed.

(* A byte array whose bytes the call kept is kept. *)
Lemma up_garr8_kept : forall (H1 H2 : word -> bool) (m1 m2 : word -> option byte) base l,
  (forall a, base <= a < base + Z.of_nat (length l) -> aview segs H2 m2 a = aview segs H1 m1 a) ->
  garr8 segs (mrestrict H1 m1) base l -> garr8 segs (mrestrict H2 m2) base l.
Proof.
intros H1 H2 m1 m2 base l HK HG. eapply garr8_frame; [exact HG|].
intros a Ha. apply mbyte_of_aview. apply HK, Ha.
Qed.

(* The fake frame's eight shadow bytes are kept when the reader agrees on them. *)
Lemma up_fsh_kept : forall (cx : dctx) (r r' : reader) (b4 b5 : Z),
  (forall i, 0 <= i < 8 -> r' (d_SH cx + i) = r (d_SH cx + i)) ->
  dec_a_fsh cx r b4 b5 -> dec_a_fsh cx r' b4 b5.
Proof.
intros cx r r' b4 b5 HK (F1 & F4 & F5 & F6). unfold dec_a_fsh.
split; [intros i Hi; rewrite HK by lia; apply F1, Hi|].
split; [rewrite HK by lia; exact F4|].
split; [rewrite HK by lia; exact F5|].
intros i Hi; rewrite HK by lia; apply F6, Hi.
Qed.

(* Every byte of the caller the segment carries lies in up_touch, so a call that keeps up_touch, keeps
   presence and keeps the mode geometry keeps up_mem. The payload length (dec_a_base's
   n = Z.of_nat (length pl)) makes the two byte arrays span exactly up_touch's payload and body ranges. *)
Lemma up_mem_kept : forall (cx : dctx) (res mode nch ns : Z) (W1 W2 : world segs) m1 m2,
  d_n cx = Z.of_nat (length (d_pl cx)) ->
  (forall a, up_touch cx res a -> aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) ->
  (dec_a_mode_ok cx W1 m1 mode nch ns -> dec_a_mode_ok cx W2 m2 mode nch ns) ->
  up_mem cx res mode nch ns W1 m1 -> up_mem cx res mode nch ns W2 m2.
Proof.
intros cx res mode nch ns W1 W2 m1 m2 HLEN HT HP HM
  (SV & FP & FL & GP & MO & FSH & GB & PL & S40 & S56 & S64 & S112).
assert (SL : forall off v, 8 <= off <= 112 ->
  dec_a_slot cx (aview segs (w_H W1) m1) off v -> dec_a_slot cx (aview segs (w_H W2) m2) off v)
  by (intros off v Ho; exact (up_slot_kept cx res W1 W2 m1 m2 off v HT Ho)).
assert (LB : Z.of_nat (length (d_body cx)) = up_len cx).
{ unfold d_body, up_len, dec_a_len, dec_a_u. rewrite length_skipn. lia. }
unfold up_mem.
split.
{ unfold dec_a_saved in SV |- *. rewrite Forall_forall in SV |- *. intros o Ho.
  rewrite (up_rdword_kept cx res W1 W2 m1 m2 _ HT); [apply SV, Ho|].
  pose proof (up_saved_at_rng o Ho). intros k Hk. unfold up_touch. left. lia. }
split.
{ intros a Ha. apply HP, FP, Ha. }
split.
{ rewrite (up_rdword_kept cx res W1 W2 m1 m2 _ HT); [exact FL|].
  intros k Hk. unfold up_touch. right; right; left. lia. }
split.
{ apply (up_garr8_kept (w_H W1) (w_H W2) m1 m2); [|exact GP].
  intros a Ha. apply HT. rewrite length_map in Ha. unfold up_touch. do 4 right. left. lia. }
split.
{ apply HM, MO. }
split.
{ apply (up_fsh_kept cx (aview segs (w_H W1) m1)); [|exact FSH].
  intros i Hi. apply HT. unfold up_touch. do 3 right. left. lia. }
split.
{ apply (up_garr8_kept (w_H W1) (w_H W2) m1 m2); [|exact GB].
  intros a Ha. apply HT. rewrite length_map, LB in Ha. unfold up_touch. do 5 right. lia. }
split.
{ intros HOK. destruct (PL HOK) as (P8 & P16 & P24 & P48).
  split; [apply SL; [lia | exact P8]|]. split; [apply SL; [lia | exact P16]|].
  split; [apply SL; [lia | exact P24]|]. apply SL; [lia | exact P48]. }
split; [apply SL; [lia | exact S40]|].
split; [apply SL; [lia | exact S56]|].
split; [apply SL; [lia | exact S64]|].
apply SL; [lia | exact S112].
Qed.

(* up_mem_kept with presence asked only over the fake frame, which is all up_mem reads of it: a call whose
   kept clauses give presence only above the allocator ceiling (acall_kept) still keeps up_mem. *)
Lemma up_mem_kept_fr : forall (cx : dctx) (res mode nch ns : Z) (W1 W2 : world segs) m1 m2,
  d_n cx = Z.of_nat (length (d_pl cx)) ->
  (forall a, up_touch cx res a -> aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  (forall a, d_F cx <= a < d_F cx + 64 -> apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) ->
  (dec_a_mode_ok cx W1 m1 mode nch ns -> dec_a_mode_ok cx W2 m2 mode nch ns) ->
  up_mem cx res mode nch ns W1 m1 -> up_mem cx res mode nch ns W2 m2.
Proof.
intros cx res mode nch ns W1 W2 m1 m2 HLEN HT HP HM
  (SV & FP & FL & GP & MO & FSH & GB & PL & S40 & S56 & S64 & S112).
assert (SL : forall off v, 8 <= off <= 112 ->
  dec_a_slot cx (aview segs (w_H W1) m1) off v -> dec_a_slot cx (aview segs (w_H W2) m2) off v)
  by (intros off v Ho; exact (up_slot_kept cx res W1 W2 m1 m2 off v HT Ho)).
assert (LB : Z.of_nat (length (d_body cx)) = up_len cx).
{ unfold d_body, up_len, dec_a_len, dec_a_u. rewrite length_skipn. lia. }
unfold up_mem.
split.
{ unfold dec_a_saved in SV |- *. rewrite Forall_forall in SV |- *. intros o Ho.
  rewrite (up_rdword_kept cx res W1 W2 m1 m2 _ HT); [apply SV, Ho|].
  pose proof (up_saved_at_rng o Ho). intros k Hk. unfold up_touch. left. lia. }
split.
{ intros a Ha. apply HP; [exact Ha | apply FP, Ha]. }
split.
{ rewrite (up_rdword_kept cx res W1 W2 m1 m2 _ HT); [exact FL|].
  intros k Hk. unfold up_touch. right; right; left. lia. }
split.
{ apply (up_garr8_kept (w_H W1) (w_H W2) m1 m2); [|exact GP].
  intros a Ha. apply HT. rewrite length_map in Ha. unfold up_touch. do 4 right. left. lia. }
split.
{ apply HM, MO. }
split.
{ apply (up_fsh_kept cx (aview segs (w_H W1) m1)); [|exact FSH].
  intros i Hi. apply HT. unfold up_touch. do 3 right. left. lia. }
split.
{ apply (up_garr8_kept (w_H W1) (w_H W2) m1 m2); [|exact GB].
  intros a Ha. apply HT. rewrite length_map, LB in Ha. unfold up_touch. do 5 right. lia. }
split.
{ intros HOK. destruct (PL HOK) as (P8 & P16 & P24 & P48).
  split; [apply SL; [lia | exact P8]|]. split; [apply SL; [lia | exact P16]|].
  split; [apply SL; [lia | exact P24]|]. apply SL; [lia | exact P48]. }
split; [apply SL; [lia | exact S40]|].
split; [apply SL; [lia | exact S56]|].
split; [apply SL; [lia | exact S64]|].
apply SL; [lia | exact S112].
Qed.

(* dec_a_mode_ok reads only aview, so a memory equal to the old one at every address keeps it. *)
Lemma up_mode_ext : forall (cx : dctx) (W1 W2 : world segs) m1 m2 (mode nch ns : Z),
  (forall a, aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  dec_a_mode_ok cx W1 m1 mode nch ns -> dec_a_mode_ok cx W2 m2 mode nch ns.
Proof.
  intros cx W1 W2 m1 m2 mode nch ns HA (Hwhere & Hnch & Hns & Hv4 & Hv8).
  assert (HR : forall a, rdword (aview segs (w_H W2) m2) a = rdword (aview segs (w_H W1) m1) a)
    by (intros a; apply rdword_ext; intros k _; apply HA).
  split; [rewrite !HR; exact Hwhere|]. split; [exact Hnch|]. split; [exact Hns|].
  split; (eapply val_mem_kept; [| eassumption]); intros k _; apply HA.
Qed.


(* ---------------------------------------------------------------- *)
(* The room and meter premises of malloc #3 (amalloc04_sub).         *)
(* ---------------------------------------------------------------- *)

(* The released up_olen_bounds (lib/U/Prog/fd_up.v:38): upstream_ok bounds the count by 40. *)
Lemma up_sz_bounds : forall cx : dctx, 1 <= up_sz cx <= 1440.
Proof.
intros cx. unfold up_sz, up_cnt, dec_a_uolen, CChan.upstream_result.
destruct (CChan.upstream_ok (up_len cx)) eqn:E.
- unfold CChan.upstream_ok in E. rewrite !andb_true_iff in E.
  destruct E as ((((_ & _) & _) & E2) & E40). rewrite Z.leb_le in E2, E40.
  destruct (Z.ltb_spec 0 (CChan.upstream_width (up_len cx))); lia.
- destruct (Z.ltb_spec 0 (-1)); lia.
Qed.

(* (a) the request size. *)
Lemma up_room_sz : forall cx : dctx, 0 <= up_sz cx < MALLOC_MAX.
Proof. intros cx. pose proof (up_sz_bounds cx). unfold MALLOC_MAX. lia. Qed.

(* (b) the live-bytes room: the blocks at the call are the entry's plus the body copy. *)
Lemma up_room_live : forall (cx : dctx) (res : Z) (ly' : alayout) (S' : astate),
  Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx) ++ [(res, up_len cx)]) ->
  blocks_bytes (d_S cx) + DEC_LIVE_LIB <= LIVE_MAX -> 0 <= d_n cx < 2 ^ 26 ->
  blocks_bytes S' + up_sz cx <= LIVE_MAX.
Proof.
intros cx res ly' S' HPm HL HN. pose proof (up_sz_bounds cx) as HSZ.
rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HPm), bsum_app, bsum_cons.
rewrite <- (blocks_bytes_bsum B (d_ly cx) (d_S cx)). cbn [snd]. change (bsum []) with 0.
unfold up_len, dec_a_len, DEC_LIVE_LIB, LIVE_MAX in *. lia.
Qed.

(* (c) the event room. *)
Lemma up_room_ev : forall (cx : dctx) (S' : astate),
  st_nev S' <= st_nev (d_S cx) + dec_ev_748 -> st_nev (d_S cx) + DEC_EV_LIB <= EV_MAX ->
  st_nev S' < EV_MAX.
Proof. intros cx S' H1 H2. unfold dec_ev_748, DEC_EV_LIB, EV_MAX in *. lia. Qed.

Lemma up_rest_86c_nonneg : ameter_laws MT -> 0 <= dec_rest_86c MT.
Proof.
intros ML. unfold dec_rest_86c, dec_crt_cost_max.
pose proof (mo_malloc_nonneg MT ML 1920 ltac:(lia)). pose proof (mo_malloc_nonneg MT ML 1016 ltac:(lia)).
pose proof (mo_malloc_nonneg MT ML 1440 ltac:(lia)). pose proof (mo_free_nonneg MT ML). lia.
Qed.

(* (d) the meter covers malloc #3. *)
Lemma up_meter_malloc : forall (cx : dctx) (S' : astate),
  ameter_laws MT -> mo_ok MT S' (dec_rest_748 MT) -> mo_ok MT S' (mo_malloc MT (up_sz cx)).
Proof.
intros cx S' ML HOK. pose proof (up_sz_bounds cx) as HSZ.
apply (mo_ok_le MT ML S' _ (dec_rest_748 MT) HOK).
pose proof (mo_malloc_mono MT ML (up_sz cx) 1440 ltac:(lia)).
pose proof (up_rest_86c_nonneg ML). unfold dec_rest_748. lia.
Qed.

(* (e) what the walk has spent after malloc #3. *)
Lemma up_meter_le : forall (cx : dctx) (S' S2 : astate),
  ameter_laws MT ->
  mo_le MT (d_S cx) S' (dec_spent_748 MT (d_n cx)) -> mo_le MT S' S2 (mo_malloc MT (up_sz cx)) ->
  mo_le MT (d_S cx) S2 (dec_spent_86c MT (d_n cx)).
Proof.
intros cx S' S2 ML H1 H2. pose proof (up_sz_bounds cx) as HSZ.
apply (mo_le_mono MT ML _ _ _ _ (mo_le_trans MT ML _ _ _ _ _ H1 H2)).
pose proof (mo_malloc_mono MT ML (up_sz cx) 1440 ltac:(lia)). unfold dec_spent_86c. lia.
Qed.

(* (f) what the walk still has after malloc #3. *)
Lemma up_meter_rest : forall (cx : dctx) (S' S2 : astate),
  ameter_laws MT ->
  mo_ok MT S' (dec_rest_748 MT) -> mo_le MT S' S2 (mo_malloc MT (up_sz cx)) ->
  mo_ok MT S2 (dec_rest_86c MT).
Proof.
intros cx S' S2 ML HOK HLE. pose proof (up_sz_bounds cx) as HSZ.
apply (mo_ok_step MT ML S' S2 (mo_malloc MT (up_sz cx)) (dec_rest_86c MT)); [|exact HLE].
apply (mo_ok_le MT ML S' _ (dec_rest_748 MT) HOK).
pose proof (mo_malloc_mono MT ML (up_sz cx) 1440 ltac:(lia)). unfold dec_rest_748. lia.
Qed.

(* ---------------------------------------------------------------- *)
(* The leaf bridge: the premises reac_upstream_decode_cg.v's leaf     *)
(* reads at the raw call memory, from the walk's cgif-level facts.    *)
(* ---------------------------------------------------------------- *)

(* A byte aview reads is the byte decode's mrd reads: aview hides the world's set H, which covers no loaded
   segment (w_Hoff), so a visible byte is the overlay's byte or the image's. Img0.rsegs is decodesegs0. *)
Lemma up_lb_view_mrd : forall (W : world segs) mem a (c : byte),
  aview segs (w_H W) mem a = Some (bv_unsigned c) ->
  DMem.mrd Img0.rsegs mem (DMem.wa a) = Some c.
Proof.
  intros W mem a c V. unfold aview in V.
  match type of V with context [mbyte ?sg ?m ?x] => destruct (mbyte sg m x) as [t|] eqn:E end;
    cbn [option_map] in V; [|discriminate].
  injection V as V. apply bv_eq in V. subst t.
  exact (proj1 (mbyte_mrestrict_some segs (w_H W) mem a c (w_Hoff W) E)).
Qed.

Lemma up_lb_nth_seq : forall w i s, (i < w)%nat -> nth_error (List.seq s w) i = Some (s + i)%nat.
Proof.
  induction w as [|w IH]; intros i s Hi; [lia|].
  destruct i as [|i]; cbn; [f_equal; lia|].
  rewrite IH by lia. f_equal. lia.
Qed.

Lemma up_lb_bytes : forall (W : world segs) mem a (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i c, nth_error bs i = Some c -> aview segs (w_H W) mem (a + Z.of_nat i) = Some (bv_unsigned c)) ->
  DMem.bytes_at Img0.rsegs mem a bs.
Proof.
  intros W mem a bs H0 H1 HV. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (nth_error bs i) as [c|] eqn:E.
  - exact (up_lb_view_mrd W mem _ c (HV i c E)).
  - apply nth_error_None in E. lia.
Qed.

(* The runtime cells the leaf reads: the shared bridge's dec_leafb_asan_cells, which looks each row of
   dec_crt_cells up by statement (LLVMFuzzerTestOneInput_leafb.v:220). *)
Lemma dec_leafb_cells : forall ly S (W : world segs) mem md,
  AR_laws segs B -> dec_crt_cells B -> AR segs B ly S W mem md -> AsanCells.asan_cells mem.
Proof.
  intros ly S W mem md _ HC HAR. exact (LB.dec_leafb_asan_cells B HC ly S W mem md HAR).
Qed.

(* The leaf reads the multiply-high constant at DIV36_MAGIC_AT = decode_obj 9: the owned constant cell of
   dec_crt_cells, read at the raw call memory by the shared bridge's dec_leafb_z8. *)
Lemma dec_leafb_magic : forall ly S (W : world segs) mem md,
  dec_crt_cells B -> AR segs B ly S W mem md ->
  DMem.bytes_at Img0.rsegs mem reac_upstream_decode_c.DIV36_MAGIC_AT
    (DMem.le8 (DMem.wa reac_upstream_decode_c.DIV36_MAGIC)).
Proof.
  intros ly S W mem md HC HAR.
  assert (HK : Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly))
    by (destruct HAR as [HM _]; eapply am_const; exact HM).
  assert (Hrow : In (z8 (ANum reac_upstream_decode_c.DIV36_MAGIC_AT) reac_upstream_decode_c.DIV36_MAGIC)
                    (as_const B ly)) by (up_md_row HC ly).
  exact (LB.dec_leafb_z8 B ly (w_H W) mem reac_upstream_decode_c.DIV36_MAGIC_AT reac_upstream_decode_c.DIV36_MAGIC
           (w_Hoff W) HK Hrow ltac:(clear; vm_compute; reflexivity)
           ltac:(clear; unfold reac_upstream_decode_c.DIV36_MAGIC_AT; lia)).
Qed.

(* The leaf's stack premises, from the journal's presence of the window below sp. *)
Lemma dec_leafb_stack : forall (W : world segs) (regs : bvmap 5 word) mem,
  (forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
  alloc_ceiling <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  Frame.stk Img0.rsegs mem (spZ regs - ESTACK) (spZ regs) /\
  AsanCells.app_mem (spZ regs - reac_upstream_decode_c.REAC_UPSTREAM_DECODE_D) /\
  AsanCells.app_mem (spZ regs - 1) /\
  AsanKA.off_stk (YK11.getr regs (Z_to_bv 5 2)) reac_upstream_decode_c.REAC_UPSTREAM_DECODE_D
    AsanCells.GOT_CELL_K (AsanCells.MIDEND + 8 - AsanCells.GOT_CELL_K) /\
  AsanKA.off_stk (YK11.getr regs (Z_to_bv 5 2)) reac_upstream_decode_c.REAC_UPSTREAM_DECODE_D
    reac_upstream_decode_c.DIV36_MAGIC_AT 8.
Proof.
  intros W regs mem HP HC H47 _.
  pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _].
  assert (SP : bv_unsigned (YK11.getr regs (Z_to_bv 5 2)) = spZ regs).
  { unfold spZ. first [reflexivity | f_equal; f_equal; apply bv_eq; reflexivity]. }
  unfold AsanKA.off_stk. rewrite SP.
  unfold AsanCells.app_mem, AsanCells.LOWMEM_END, AsanCells.HIGHMEM_BEG, AsanCells.APPMEM_END,
    AsanCells.GOT_CELL_K, AsanCells.MIDEND, reac_upstream_decode_c.REAC_UPSTREAM_DECODE_D,
    reac_upstream_decode_c.DIV36_MAGIC_AT.
  split; [|split; [lia|split; [lia|split; lia]]].
  split; [unfold ESTACK; lia|]. split; [lia|].
  intros a Ha. destruct (HP a Ha) as [_ (b & Hb)].
  unfold wview, DMem.mrd, DMem.wa. rewrite Hb. split; [discriminate|eauto].
Qed.

(* What the segment reads of the slot pre, in ONE place: dec_lib_pre_x (LLVMFuzzerTestOneInput_cg.v:102-116)
   is destructed here and nowhere else, so a change of its conjuncts touches only this proof. Its conjuncts, in
   the order of that text: afn_pre (whose first conjunct is AR), raZ, a0, a1, the payload's block, its length,
   its bytes, frames S = [], the event room, the live room, then the sink / fd / fs / meta / meter / rounding
   clauses this segment does not read. *)
Lemma up_base_facts : forall (cx : dctx), up_base cx ->
  AR segs B (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) /\
  d_n cx = Z.of_nat (length (d_pl cx)) /\ 0 <= d_n cx < 2 ^ 26 /\
  st_nev (d_S cx) + DEC_EV_LIB <= EV_MAX /\ blocks_bytes (d_S cx) + DEC_LIVE_LIB <= LIVE_MAX.
Proof.
  intros cx HB. unfold dec_a_base, dec_lib_pre_x in HB.
  destruct HB as (Hafn & _Hra & _Ha0 & _Ha1 & Hblk & Hlen & _Hgarr & _Hfrs & Hnev & Hlive & _).
  destruct Hafn as (HAR & _).
  split; [exact HAR|]. split; [exact Hlen|].
  split; [destruct Hblk as [(Hn0 & _) | (Hn & _)]; lia|].
  split; [exact Hnev | exact Hlive].
Qed.

(* dec_a_mode_ok's table modes: the mode cells decode_obj 4 / 5 / 6 are pointer rows of dec_crt_cells, which AR
   reads the same at every state; the +4 / +8 words of each table are DEC_RO_RD bytes (the c-alpha amendment,
   check_round_trip_cg.v DEC_RO_RD), which the read-only view gives as the image's at any state that has it. *)
(* AR's constant cells at one state, read through the state's view (YG0n.v am_const); leafb's route. *)
Lemma up_md_const : forall ly S (W : world decodesegs0) mem md,
  AR decodesegs0 B ly S W mem md ->
  Forall (cell_holds B ly (aview decodesegs0 (w_H W) mem)) (as_const B ly).
Proof. intros ly S W mem md HAR. destruct HAR as [HM _]. eapply am_const; exact HM. Qed.

(* The 8 bytes after a table's base word are DEC_RO_RD bytes, decided at the concrete table address. *)
Lemma up_md_ro_of : forall T,
  forallb (fun j : nat => up_rd_b (T + 4 + Z.of_nat j)) (seq 0 8) = true ->
  forall j, 0 <= j < 8 -> dec_in_ro_rd (T + 4 + j).
Proof.
  intros T Hb j Hj. rewrite forallb_forall in Hb.
  pose proof (Hb (Z.to_nat j) ltac:(apply in_seq; lia)) as H. rewrite Z2Nat.id in H by lia.
  exact (up_rd_of_b _ H).
Qed.

(* One mode table: the pointer row of dec_crt_cells at decode_obj k, holding the table address T, whose +4 and +8
   words are DEC_RO_RD bytes. Found by statement, so T is the row's own value. *)
Lemma up_md_rows_of : dec_crt_cells B -> forall k : nat, (k = 4 \/ k = 5 \/ k = 6)%nat ->
  exists T, (forall ly, In (z8 (ANum (decode_obj k)) T) (as_const B ly)) /\ 0 <= T < 2 ^ 64 /\
    (forall j, 0 <= j < 8 -> dec_in_ro_rd (T + 4 + j)).
Proof.
  intros HC k Hk. destruct Hk as [-> | [-> | ->]]; eexists;
    (split; [intros ly; up_md_row HC ly | split; [lia | apply up_md_ro_of; vm_compute; reflexivity]]).
Qed.

(* The pointer row, and the read-only view at both states, carry one state's mode facts to the other. *)
Lemma up_md_table : forall p T ly1 S1 (W1 : world decodesegs0) m1 md1 ly2 S2 (W2 : world decodesegs0) m2 md2
    mode x y,
  (forall ly, In (z8 (ANum p) T) (as_const B ly)) -> 0 <= T < 2 ^ 64 ->
  (forall j, 0 <= j < 8 -> dec_in_ro_rd (T + 4 + j)) ->
  AR decodesegs0 B ly1 S1 W1 m1 md1 -> AR decodesegs0 B ly2 S2 W2 m2 md2 ->
  dec_rom_view_rd W1 m1 -> dec_rom_view_rd W2 m2 ->
  rdword (aview decodesegs0 (w_H W1) m1) p = Some mode ->
  val_mem decodesegs0 (mrestrict (w_H W1) m1) (mode + 4) 4%nat x ->
  val_mem decodesegs0 (mrestrict (w_H W1) m1) (mode + 8) 4%nat y ->
  rdword (aview decodesegs0 (w_H W2) m2) p = Some mode /\
  val_mem decodesegs0 (mrestrict (w_H W2) m2) (mode + 4) 4%nat x /\
  val_mem decodesegs0 (mrestrict (w_H W2) m2) (mode + 8) 4%nat y.
Proof.
  intros p T ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 mode x y HP HT HRO HAR1 HAR2 RV1 RV2 Hp V4 V8.
  pose proof (proj1 (Forall_forall _ _) (up_md_const ly1 S1 W1 m1 md1 HAR1)) as K1.
  pose proof (proj1 (Forall_forall _ _) (up_md_const ly2 S2 W2 m2 md2 HAR2)) as K2.
  rewrite (YG0s.rdword_cell B ly1 _ p T HT (K1 _ (HP ly1))) in Hp. injection Hp as <-.
  assert (SAME : forall j, 0 <= j < 8 ->
                   aview decodesegs0 (w_H W2) m2 (T + 4 + j) = aview decodesegs0 (w_H W1) m1 (T + 4 + j))
    by (intros j Hj; rewrite (RV2 _ (HRO j Hj)), (RV1 _ (HRO j Hj)); reflexivity).
  split; [exact (YG0s.rdword_cell B ly2 _ p T HT (K2 _ (HP ly2)))|].
  split.
  - eapply val_mem_kept; [| exact V4]. intros k Hk. exact (SAME k ltac:(lia)).
  - eapply val_mem_kept; [| exact V8]. intros k Hk.
    replace (T + 8 + k) with (T + 4 + (4 + k)) by lia. exact (SAME (4 + k) ltac:(lia)).
Qed.

Lemma up_mode_rows : dec_crt_cells B ->
  forall (cx : dctx) ly1 S1 (W1 : world decodesegs0) m1 md1 ly2 S2 (W2 : world decodesegs0) m2 md2
         (mode nch ns : Z),
  AR decodesegs0 B ly1 S1 W1 m1 md1 -> AR decodesegs0 B ly2 S2 W2 m2 md2 ->
  dec_rom_view_rd W1 m1 -> dec_rom_view_rd W2 m2 ->
  mode <> d_F cx + 32 ->
  dec_a_mode_ok cx W1 m1 mode nch ns -> dec_a_mode_ok cx W2 m2 mode nch ns.
Proof.
  intros HC cx ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 mode nch ns HAR1 HAR2 RV1 RV2 Hne HM1.
  unfold dec_a_mode_ok in HM1 |- *. destruct HM1 as (Hsel & Hnch & Hns & V4 & V8).
  assert (Hk : exists k : nat, (k = 4 \/ k = 5 \/ k = 6)%nat /\
                 rdword (aview decodesegs0 (w_H W1) m1) (decode_obj k) = Some mode).
  { destruct Hsel as [Hp | [Hp | [Hp | Hp]]];
      [ exists 4%nat; split; [left; reflexivity | exact Hp]
      | exists 5%nat; split; [right; left; reflexivity | exact Hp]
      | exists 6%nat; split; [right; right; reflexivity | exact Hp]
      | exfalso; exact (Hne Hp) ]. }
  destruct Hk as (k & Hk & Hp).
  destruct (up_md_rows_of HC k Hk) as (T & HP & HT & HRO).
  destruct (up_md_table (decode_obj k) T ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 mode _ _ HP HT HRO HAR1 HAR2 RV1 RV2
              Hp V4 V8) as (R & A4 & A8).
  split; [|split; [exact Hnch|split; [exact Hns|split; [exact A4|exact A8]]]].
  destruct Hk as [-> | [-> | ->]]; [left | right; left | right; right; left]; exact R.
Qed.

Section f.
Context {fx : YK11.FPState}.

Lemma up_seat : forall (k : Z) (W : world segs) (regs : bvmap 5 word) mem,
  val_mem segs (mrestrict (w_H W) mem) (decode_obj 9) 8 UCh.UPSTREAM_DIV36 ->
  YK11.getr regs 18 = w64 SHADOW_OFF ->
  st_ok_pi segs pa_val (Eimg (Ereg regs [])) (ss_up_at k)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (DEC_A_LLVMF + k)) mem (seg_rom segs))).
Proof.
  intros k W regs mem HR H18.
  set (E := Eimg (Ereg regs (@nil word))).
  assert (E18 : ew E 18 = w64 SHADOW_OFF)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E9o : ew E (A_OBJ 9) = Z_to_bv 64 (pa_val (A_OBJ 9)))
    by (unfold E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Hval9 : pa_val (A_OBJ 9) = decode_obj 9) by (vm_compute; reflexivity).
  assert (H9lo : 0 <= decode_obj 9) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (H9hi : decode_obj 9 + 8 <= 2 ^ 64) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (Hmagic : 0 <= UCh.UPSTREAM_DIV36 < 2 ^ 64)
    by (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
  rewrite restrict_mkst_fx.
  rewrite <- up_base_eq.
  unfold ss_up_at.
  apply (pa_entry_st_ok_full (PI := PI_decode) E k sr_atoms regs [up_obj9] up_facts
           (mrestrict (w_H W) mem)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute; reflexivity.
  - apply Forall_cons; [| apply Forall_nil].
    unfold up_obj9, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9o, unsigned_lit_small by apply pa_val_range. rewrite Hval9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [| apply Forall_nil].
    apply (chunk_ok_val segs E _ (decode_obj 9) 0 8 (SLit UCh.UPSTREAM_DIV36) UCh.UPSTREAM_DIV36).
    + cbn [sv_denot]. reflexivity.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hmagic.
    + cbn [Z.of_N]; lia.
    + rewrite Z.add_0_r. exact HR.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [| split; [exact I | exact I]].
    cbn [up_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E18, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. unfold SB, SHADOW_OFF. repeat split; try exact I; lia.
Qed.

(* The segment's entry configuration, i.e. llvm_a_st_748 read as up_run. *)
Definition up_pre_748 (cx : dctx) (res mode nch ns : Z)
    (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) : Prop :=
  up_run cx res mode nch ns (up_bl0 cx res) dec_ev_748 ly' S' W' regs' mem' md' /\
  4096 <= res /\
  mo_le MT (d_S cx) S' (dec_spent_748 MT (d_n cx)) /\ mo_ok MT S' (dec_rest_748 MT) /\
  YK11.getr regs' 10 = w64 (up_cnt cx).

(* What every point after malloc #3 carries: the state, the new block, the meter, and the two callee-saved
   registers the harness keeps the count and the buffer size in (s6 at +0x748, s8 at +0x7a4 / +0x7b8). *)
Definition up_mid (cx : dctx) (res mode nch ns upb : Z)
    (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) : Prop :=
  up_run cx res mode nch ns (up_bl1 cx res upb) dec_ev_86c ly' S' W' regs' mem' md' /\
  4096 <= upb /\
  In (upb, up_sz cx) (ablocks B ly' S') /\ ~ In (upb, up_sz cx) (ablocks B (d_ly cx) (d_S cx)) /\
  mo_le MT (d_S cx) S' (dec_spent_86c MT (d_n cx)) /\ mo_ok MT S' (dec_rest_86c MT) /\
  YK11.getr regs' 22 = w64 (up_cnt cx) /\
  YK11.getr regs' 24 = w64 (up_sz cx).

(* +0x7c4, the return of malloc #3: a0 is the buffer. *)
Definition up_post_7c4 (cx : dctx) (res mode nch ns : Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (upb : Z),
    c' = @cfg_at fx segs (DEC_A_LLVMF + UP_MALLOC_RA) regs' mem' md' /\
    up_mid cx res mode nch ns upb ly' S' W' regs' mem' md' /\
    YK11.getr regs' 10 = w64 upb.

(* +0x7fc, the return of reac_upstream_decode #2: both refusing calls returned -1 (s9 and a0), and neither
   wrote a byte, so the buffer is still 0xa5. *)
Definition up_post_7fc (cx : dctx) (res mode nch ns : Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (upb : Z),
    c' = @cfg_at fx segs (DEC_A_LLVMF + UP_DEC2_RA) regs' mem' md' /\
    up_mid cx res mode nch ns upb ly' S' W' regs' mem' md' /\
    YK11.getr regs' 23 = w64 upb /\
    dec_a_filled W' mem' upb (up_sz cx) /\
    YK11.getr regs' 25 = w64 (-1) /\ YK11.getr regs' 10 = w64 (-1).

(* The head of the scan loop L5 at its i-th pass: a0 and a2 are the current byte, a3 what is left, and a1 the
   accumulated difference, still zero because every byte read so far was 0xa5. *)
Definition up_loop (cx : dctx) (res mode nch ns : Z) (i : Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (upb : Z),
    c' = @cfg_at fx segs (DEC_A_LLVMF + UP_LOOP) regs' mem' md' /\
    up_mid cx res mode nch ns upb ly' S' W' regs' mem' md' /\
    YK11.getr regs' 23 = w64 upb /\
    dec_a_filled W' mem' upb (up_sz cx) /\
    0 <= i < up_sz cx /\
    YK11.getr regs' 10 = w64 (upb + i) /\ YK11.getr regs' 11 = w64 0 /\
    YK11.getr regs' 12 = w64 (upb + i) /\ YK11.getr regs' 13 = w64 (up_sz cx - i).

(* +0x858, the loop's exit: a1 is zero, so the abort edge is refuted. *)
Definition up_post_858 (cx : dctx) (res mode nch ns : Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (upb : Z),
    c' = @cfg_at fx segs (DEC_A_LLVMF + UP_TAIL) regs' mem' md' /\
    up_mid cx res mode nch ns upb ly' S' W' regs' mem' md' /\
    YK11.getr regs' 23 = w64 upb /\
    dec_a_filled W' mem' upb (up_sz cx) /\
    YK11.getr regs' 11 = w64 0.

(* ---------------------------------------------------------------- *)
(* The four stages, as Props, so that each is proved on its own.     *)
(* ---------------------------------------------------------------- *)

(* +0x79c, the channel-count check: the harness's own geometry is in a0 and the leaf's answer in s6, and the
   two agree, so the `bne` to the trap block is refuted. *)
Definition up_post_79c (cx : dctx) (res mode nch ns : Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md',
    c' = @cfg_at fx segs (DEC_A_LLVMF + UP_CMP) regs' mem' md' /\
    up_run cx res mode nch ns (up_bl0 cx res) dec_ev_748 ly' S' W' regs' mem' md' /\
    4096 <= res /\
    mo_le MT (d_S cx) S' (dec_spent_748 MT (d_n cx)) /\ mo_ok MT S' (dec_rest_748 MT) /\
    YK11.getr regs' 10 = w64 (up_cnt cx) /\ YK11.getr regs' 22 = w64 (up_cnt cx).

Definition up_A1_stmt : Prop :=
  forall (cx : dctx) (res mode nch ns : Z) ly' S' (W' : world segs) regs' mem' md',
    up_base cx -> dec_a_rom cx -> up_geom cx ->
    up_pre_748 cx res mode nch ns ly' S' W' regs' mem' md' ->
    SRr segs W' (@cfg_at fx segs (DEC_A_LLVMF + UP_CHK) regs' mem' md')
      (up_post_79c cx res mode nch ns).

Definition up_A2_stmt : Prop :=
  forall (cx : dctx) (res mode nch ns : Z) (W' : world segs) (c' : config),
    up_base cx -> dec_a_rom cx -> up_geom cx ->
    up_post_79c cx res mode nch ns W' c' ->
    SRr segs W' c' (up_post_7c4 cx res mode nch ns).

Definition up_B_stmt : Prop :=
  forall (cx : dctx) (res mode nch ns : Z) (W' : world segs) (c' : config),
    up_base cx -> dec_a_rom cx -> up_geom cx ->
    up_post_7c4 cx res mode nch ns W' c' ->
    SRr segs W' c' (up_post_7fc cx res mode nch ns).

Definition up_C_stmt : Prop :=
  forall (cx : dctx) (res mode nch ns : Z) (W' : world segs) (c' : config),
    up_base cx -> dec_a_rom cx -> up_geom cx ->
    up_post_7fc cx res mode nch ns W' c' ->
    SRr segs W' c' (up_post_858 cx res mode nch ns).

Definition up_D_stmt : Prop :=
  forall (cx : dctx) (res mode nch ns : Z) (W' : world segs) (c' : config),
    frm_zero (@fp_csr fx) ->
    up_base cx -> dec_a_rom cx -> up_geom cx ->
    up_post_858 cx res mode nch ns W' c' ->
    SRr segs W' c' (llvm_a_st_86c B MT cx).


(* ---------------------------------------------------------------- *)
(* The stepping                                                      *)
(* ---------------------------------------------------------------- *)

Section g.
Hypothesis LAWS : AR_laws segs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis CELLS : dec_crt_cells B.
Hypothesis UTR : dec_llvmf_utraces RA_LLVMF B.
Hypothesis HPCM : pc_wrap_malloc (as_code B) = decode_sigma DS___interceptor_trampoline_malloc.
Hypothesis AMS : forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (decode_sigma DS___asan_memset).
Hypothesis AM : forall fx' : YK11.FPState, @amalloc04_rule fx' rc dec_A_sink_head segs B MT.
Hypothesis LUP : forall fx' : YK11.FPState, @dec_leaf_wr_at rc B (@LUpDecode.dec_reac_upstream_decode_cg) fx'.
(* The two instance facts of the statement that let the journal's image clause (YCbq.v:362) carry a read-only
   byte to a later memory (check_round_trip_cg.v dec_ro_rd_scoped). *)
Hypothesis HOWN : dec_ro_rd_unowned B.
Hypothesis HNERR : dec_rom_no_errno B.
(* The read-only bytes the walk reads (DEC_RO_RD: here the +4 / +8 words of the three REAC_MODE tables, which
   dec_a_mode_ok's table modes point at) are the image's at every point of the segment: the journal's image clause
   keeps them, because dec_ro_rd_scoped puts them outside the owned statics and errno, and the sink's head is far
   from them. *)
Lemma HROM_KEPT : forall STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs) mem' md' k,
  @ajournal rc dec_A_sink_head segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  rom_view segs W mem -> dec_rom_view_rd W' mem'.
Proof.
  intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR a Ha.
  destruct (dec_ro_rd_scoped B HOWN HNERR a Ha) as [Hno Hne].
  destruct (dec_ro_rd_rom_clean a Ha) as [Hrom _].
  (* ajournal's conjuncts, YCbq.v:354-372: the image clause is the eleventh *)
  destruct HJ as (_HAR & _Hly & _Hsecs & _Hwle & _Hio & _Hfrs & _Hnev & _Hk & _F1 & _F2 & F3 & _).
  assert (Himg : in_img segs a) by (destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
  assert (Hsp : fp_spares (SK := dec_A_sink_head) FP a).
  { apply fp_spares_off.
    assert (Hfar : forallb (fun r : Z * Z => ((fst r + snd r <=? @AOFL_HEAD dec_A_sink_head) ||
                                              (@AOFL_HEAD dec_A_sink_head + 8 <=? fst r))%bool) DEC_RO_RD = true)
      by (vm_compute; reflexivity).
    unfold dec_in_ro_rd in Ha. apply Exists_exists in Ha as (r & Hin & Hr).
    rewrite forallb_forall in Hfar. pose proof (Hfar r Hin) as Hf.
    apply orb_prop in Hf as [Hf | Hf]; apply Z.leb_le in Hf; unfold in_zr in Hr; lia. }
  rewrite (F3 a Himg Hno Hne Hsp). exact (HR a Hrom).
Qed.


(* The call trace of malloc #3 (+0x7c0): s0 is the frame pointer the prologue set to the entry sp (+0x3c), the
   frame record below it holds RA_LLVMF and the caller's s0 (the saved words at d_sp0 - 8 / - 16), and the
   caller's own chain is empty (afn_pre .. [] in dec_lib_pre_x), so the chain is [] or one record whose return
   address is RA_LLVMF, which is what dec_llvmf_utraces lists. *)
Definition up_trace_stmt : Prop :=
  forall (cx : dctx) ly' S' (W' : world segs) mem' md' (k : Z) (regsT : bvmap 5 word),
    up_base cx -> up_geom cx ->
    @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
      (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' W' mem' md' k ->
    dec_a_saved cx (aview segs (w_H W') mem') ->
    YK11.getr regsT 8 = w64 (d_sp0 cx) -> spZ regsT = d_sp1 cx ->
    YK11.getr regsT 1 = w64 (DEC_A_LLVMF + UP_MALLOC_RA) ->
    exists ch, chain_pre ly' (aview segs (w_H W') mem') regsT ch /\
               In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B).

(* From a working branch 1a9fb3f284b, proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v lines 890-992,
   inside Section g right after Definition up_trace_stmt. *)
(* The two fields of dec_lib_pre_x (LLVMFuzzerTestOneInput_cg.v:102-116) the call trace reads: the caller's afn_pre
   with the empty chain (its first conjunct, :104) and the return address RA_LLVMF (its second conjunct, :105). *)
Lemma up_tr_base : forall cx : dctx, up_base cx ->
  @afn_pre rc segs B DEC_LLVMF_STK (d_ly cx) (d_S cx) (d_W cx) (d_regs cx) (d_mem cx) (d_md cx) [] /\
  raZ (d_regs cx) = RA_LLVMF.
Proof.
  intros cx H. unfold dec_a_base, dec_lib_pre_x in H.
  destruct H as (HAFN (* :104  afn_pre STK ly S W regs mem md [] *) &
                 HRA (* :105  raZ regs = RA_LLVMF *) &
                 _ (* :106-116  a0 / a1, the payload, frames, rooms, sinks, meter, rounding mode *)).
  exact (conj HAFN HRA).
Qed.

(* The call trace of malloc #3. The caller's chain is [] (afn_pre .. []), so when the frame record at d_sp0 lies
   below ly_top - 16 the chain is that record pushed on [] (achain_push, YCbq.v:296), else it is [] by achain's
   first disjunct (YCbq.v:218-221); chain_pre follows by achain_chain_pre (YCbq.v:281) and the trace is
   dec_utrace's form by call_trace_of_spine (YCbq.v:2802), with spine [RA_LLVMF] or []. *)
Lemma up_trace : up_trace_stmt.
Proof.
  unfold up_trace_stmt.
  intros cx ly' S' W' mem' md' k regsT HB HG HJ HSV R8 HSP R1.
  destruct (up_tr_base cx HB) as [HAFN HRA].
  (* afn_pre (YCbq.v:336-343) of the entry registers d_regs cx. *)
  destruct HAFN as (_ (* AR segs B ly S W mem md *) & _ (* YK0s.ret_ok (getr regs 1) *) &
                    HRA4 (* 4096 <= raZ regs *) & _ (* getr regs 3 = w64 (as_gp B) *) &
                    _ (* getr regs 4 = w64 (as_tp B) *) & HSTK (* astk_ok STK ly (spZ regs) *) &
                    _ (* the stack window below spZ regs is present *) &
                    HCH (* achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) [] *) & _ (* qtight S *)).
  (* astk_ok (YCbq.v:333-335) at sp0 = spZ (d_regs cx), which is d_sp0 cx. *)
  destruct HSTK as (HAL (* sp0 mod 16 = 0 *) & _ (* 0 <= STK *) & HCEIL (* alloc_ceiling <= ly_stk_lo ly *) &
                    HSLO (* ly_stk_lo ly + STK <= sp0 *) & HSHI (* sp0 <= ly_stk_hi ly *) &
                    H47 (* ly_stk_hi ly <= 2 ^ 47 *) & _ (* ly_bot ly + STK < sp0 + ASTACK *) &
                    _ (* sp0 <= ly_top ly *) & HTOP (* ly_top ly <= ly_stk_hi ly *)).
  (* ajournal (YCbq.v:350-372) from the entry to the call. *)
  destruct HJ as (_ (* AR segs B ly' S' W' mem' md' *) & HLY (* layout_le (length (st_secs S)) ly ly' *) &
                  _ (* (length (st_secs S) <= length (st_secs S'))%nat *) & _ (* wle W W' *) &
                  _ (* aos_step FP md md' *) & _ (* frames S' = own ++ frames S *) &
                  _ (* st_nev S' <= st_nev S + k *) & _ (* 0 <= k *) &
                  HKEEP (* forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
                           aview segs (w_H W') mem' a = aview segs (w_H W) mem a *) &
                  _ (* blocks, image, frames, freed blocks, stack presence, astk_ok, extras, qtight S' *)).
  (* layout_le (YG0f.v:65-68): its ninth conjunct keeps ly_top. *)
  assert (ETOP : ly_top ly' = ly_top (d_ly cx)).
  { destruct HLY as (_ (* ly_prim *) & _ (* ly_space *) & _ (* ly_Q *) & _ (* ly_T *) & _ (* ly_C *) &
                     _ (* ly_F *) & _ (* ly_NB *) & _ (* ly_SB *) & E (* ly_top *) & _).
    exact E. }
  (* up_geom: d_sp0 - 240 <= d_sp1 <= d_sp0 - 224. *)
  destruct HG as ([HG1 HG2] & _ (* d_sp1 mod 32 = 0 *) & _ (* 4096 <= d_F *) & _ (* d_F mod 32 = 0 *)).
  (* The frame record below d_sp0 at the call: the first two entries (8, 1) and (16, 8) of dec_a_saved_at
     (LLVMFuzzerTestOneInput_segs.v:95-97), i.e. the entry's ra and s0. *)
  unfold dec_a_saved, dec_a_saved_at in HSV.
  apply Forall_cons_iff in HSV as [S1 HSV]. apply Forall_cons_iff in HSV as [S8 _]. cbn [fst snd] in S1, S8.
  assert (E1 : bv_unsigned (YK11.getr (d_regs cx) (Z_to_bv 5 1)) = raZ (d_regs cx)).
  { unfold raZ. first [reflexivity | f_equal; f_equal; apply bv_eq; reflexivity]. }
  assert (E8 : bv_unsigned (YK11.getr (d_regs cx) (Z_to_bv 5 8)) = s0Z (d_regs cx)).
  { unfold s0Z. first [reflexivity | f_equal; f_equal; apply bv_eq; reflexivity]. }
  rewrite E1, HRA in S1. rewrite E8 in S8.
  change (spZ (d_regs cx)) with (d_sp0 cx) in HAL, HSLO, HSHI, HCH.
  pose proof (@YM05.alloc_ceiling_value rc) as [[CL CU] _].
  unfold DEC_LLVMF_STK in HSLO, HKEEP.
  assert (HRAT : raZ regsT = DEC_A_LLVMF + UP_MALLOC_RA).
  { unfold raZ. rewrite R1. apply (unsigned_lit_small (DEC_A_LLVMF + UP_MALLOC_RA)).
    unfold DEC_A_LLVMF, decode_text, AF_LLVMFuzzerTestOneInput, UP_MALLOC_RA. lia. }
  assert (HS0T : s0Z regsT = d_sp0 cx).
  { unfold s0Z. rewrite R8. apply (unsigned_lit_small (d_sp0 cx)). lia. }
  assert (HRAT4 : 4096 <= raZ regsT).
  { rewrite HRAT. unfold DEC_A_LLVMF, decode_text, AF_LLVMFuzzerTestOneInput, UP_MALLOC_RA. lia. }
  assert (HSPT : alloc_ceiling <= spZ regsT <= d_sp1 cx) by (rewrite HSP; lia).
  (* The two spines dec_llvmf_utraces lists, at r = DEC_A_LLVMF + 0x7c4 (the third of DEC_LLVMF_RA_MALLOC). *)
  assert (HU : forall sp, In sp [[]; [RA_LLVMF]] ->
                 In (dec_utrace (pc_malloc_ra0 (as_code B)) (raZ regsT :: sp)) (as_universe B)).
  { intros sp Hsp. rewrite HRAT. apply (proj1 (UTR sp Hsp)).
    unfold DEC_LLVMF_RA_MALLOC, UP_MALLOC_RA. cbn [map In]. right. right. left. reflexivity. }
  destruct (Z_lt_ge_dec (d_sp0 cx) (ly_top (d_ly cx) - 16)) as [Hlt | Hge].
  - (* The record (d_sp0, RA_LLVMF, entry s0) pushed on the caller's []. *)
    exists [(d_sp0 cx, RA_LLVMF, s0Z (d_regs cx))]. split.
    + apply (achain_chain_pre ly' (aview segs (w_H W') mem') (d_sp1 cx) (d_sp0 cx)).
      * apply (achain_ly_top (d_ly cx)); [exact ETOP|].
        apply (achain_push (d_ly cx) (aview segs (w_H (d_W cx)) (d_mem cx))).
        -- exact HCH.
        -- lia.
        -- intros a Ha. apply HKEEP; lia.
        -- exact S1.
        -- exact S8.
        -- rewrite <- HRA. exact HRA4.
        -- lia.
        -- destruct (Z.mod_divide (d_sp0 cx) 16 ltac:(lia)) as [Hd _]. destruct (Hd HAL) as [q Hq].
           rewrite Hq. replace (q * 16) with (q * 2 * 8) by ring. apply Z.mod_mul. discriminate.
        -- exact Hlt.
        -- lia.
      * exact HSPT.
      * exact HS0T.
      * exact HRAT4.
    + rewrite call_trace_of_spine. exact (HU [RA_LLVMF] ltac:(cbn [In]; right; left; reflexivity)).
  - (* d_sp0 lies within 16 bytes of ly_top: the chain is [] by achain's first disjunct. *)
    exists []. split.
    + apply (achain_chain_pre ly' (aview segs (w_H W') mem') (d_sp1 cx) (d_sp0 cx)).
      * unfold achain. left. split; [right; left; rewrite ETOP; lia | reflexivity].
      * exact HSPT.
      * exact HS0T.
      * exact HRAT4.
    + rewrite call_trace_of_spine. exact (HU [] ltac:(cbn [In]; left; reflexivity)).
Qed.

Let RUN := paj_run (SK := dec_A_sink_head) B LAWS.
Let RUNTO := paj_run_to (SK := dec_A_sink_head) B LAWS.
Let BR := paj_branch (PI := PI_decode).

(* dec_a_mode_ok across a call: a table mode by up_mode_rows, the frame-local mode by the fake frame's bytes,
   which every call keeps (acall_kept's frames clause, and the leaf posts keep everything outside their own
   stack window and written range). *)
Lemma up_mode_kept : forall (cx : dctx) ly1 S1 (W1 : world segs) m1 md1 ly2 S2 (W2 : world segs) m2 md2
    (mode nch ns : Z),
  AR segs B ly1 S1 W1 m1 md1 -> AR segs B ly2 S2 W2 m2 md2 ->
  dec_rom_view_rd W1 m1 -> dec_rom_view_rd W2 m2 ->
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  dec_a_mode_ok cx W1 m1 mode nch ns -> dec_a_mode_ok cx W2 m2 mode nch ns.
Proof.
  intros cx ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 mode nch ns HAR1 HAR2 RV1 RV2 HF HM.
  destruct (Z.eq_dec mode (d_F cx + 32)) as [Hloc | Hne];
    [| exact (up_mode_rows CELLS cx ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 mode nch ns HAR1 HAR2 RV1 RV2 Hne HM)].
  pose proof HM as (Hwhere & Hnch & Hns & Hv4 & Hv8).
  split; [right; right; right; exact Hloc|]. split; [exact Hnch|]. split; [exact Hns|].
  split; (eapply val_mem_kept; [| eassumption]); intros k Hk; apply HF; subst mode; cbn [Z.of_nat] in Hk; lia.
Qed.

(* The `bgtz s6` of +0x7a0 as the engine states it (blt zero, s6), read as arithmetic. *)
Lemma up_bgtz : forall E c, ew E 22 = w64 c -> - 2 ^ 63 <= c < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SLit 0)) (sv_denot E (SOff 22 0)) = (0 <? c).
Proof.
  intros E c H22 Hc.
  change (branch_taken BC_LT (sv_denot E (SLit 0)) (sv_denot E (SOff 22 0)))
    with (Sg E (SLit 0) <? Sg E (SOff 22 0)).
  rewrite S_SLit, S_SOff, H22. unfold w64. rewrite Z_to_bv_unsigned, Z.add_0_r, bv_swrap_wrap.
  rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.

(* s8 as +0x7ac..+0x7b8 compute it for a positive count c: 36 * c, or 1 when that is 0 (never, here). *)
Lemma up_s8_val : forall E c, ew E 22 = w64 c -> 2 <= c <= 40 ->
  U E (SAlu ALU_OR (SMd M_MUL (SOff 22 0) (SLit 36))
                   (SAlu ALU_SLTU (SMd M_MUL (SOff 22 0) (SLit 36)) (SLit 1))) = 36 * c.
Proof.
  intros E c H22 Hc.
  assert (U22 : U E (SOff 22 0) = c) by (apply U_atom; [exact H22 | lia]).
  assert (UM : U E (SMd M_MUL (SOff 22 0) (SLit 36)) = 36 * c).
  { rewrite U_SMd. cbn [zmd_raw]. rewrite U22, U_SLit.
    unfold zcanon, M64. rewrite (Z.mod_small 36) by lia. rewrite Z.mod_small by lia. lia. }
  rewrite U_SAlu. cbn [zalu_raw]. rewrite UM, U_SAlu. cbn [zalu_raw]. rewrite UM, U_SLit.
  replace (zcanon 1) with 1 by reflexivity.
  replace (36 * c <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (zcanon 0) with 0 by reflexivity. rewrite Z.lor_0_r.
  unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

(* A run that writes no byte and leaves the callee-saved registers keeps up_run. *)
Lemma up_run_after : forall (cx : dctx) (res mode nch ns : Z) bl k ly S (W : world segs) regs mem md regs' mem' md',
  up_run cx res mode nch ns bl k ly S W regs mem md ->
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S W mem' md' k ->
  (forall x, mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  (forall n, In n [2; 3; 4; 8; 9; 18; 19; 20; 21; 26; 27] ->
     YK11.getr regs' (Z_to_bv 5 n) = YK11.getr regs (Z_to_bv 5 n)) ->
  d_n cx = Z.of_nat (length (d_pl cx)) ->
  up_run cx res mode nch ns bl k ly S W regs' mem' md'.
Proof.
  intros cx res mode nch ns bl k ly S W regs mem md regs' mem' md' HRUN HJ' MEQ KEEP HLEN.
  destruct HRUN as (HJ & Hfrms & Hr8 & Hr9 & Hsp & Hgp & Htp & Hinp & HPERM & HFR & Hr18 & Hr20 & Hr26 & HMEM).
  assert (AV : forall a, aview segs (w_H W) mem' a = aview segs (w_H W) mem a)
    by (intros a; unfold aview, mbyte; rewrite MEQ; reflexivity).
  assert (K : forall n, In n [2; 3; 4; 8; 9; 18; 19; 20; 21; 26; 27] ->
     YK11.getr regs' (Z_to_bv 5 n) = YK11.getr regs (Z_to_bv 5 n)) by exact KEEP.
  split; [exact HJ'|]. split; [exact Hfrms|].
  split; [exact (eq_trans (K 8 ltac:(cbn; tauto)) Hr8)|].
  split; [exact (eq_trans (K 9 ltac:(cbn; tauto)) Hr9)|].
  split; [unfold spZ in *; rewrite <- Hsp; f_equal; exact (K 2 ltac:(cbn; tauto))|].
  split; [exact (eq_trans (K 3 ltac:(cbn; tauto)) Hgp)|].
  split; [exact (eq_trans (K 4 ltac:(cbn; tauto)) Htp)|].
  split; [exact Hinp|]. split; [exact HPERM|].
  split.
  { destruct HFR as (F19 & F21 & F27).
    split; [exact (eq_trans (K 19 ltac:(cbn; tauto)) F19)|].
    split; [exact (eq_trans (K 21 ltac:(cbn; tauto)) F21)|].
    exact (eq_trans (K 27 ltac:(cbn; tauto)) F27). }
  split; [exact (eq_trans (K 18 ltac:(cbn; tauto)) Hr18)|].
  split; [exact (eq_trans (K 20 ltac:(cbn; tauto)) Hr20)|].
  split; [exact (eq_trans (K 26 ltac:(cbn; tauto)) Hr26)|].
  apply (up_mem_kept_fr cx res mode nch ns W W mem mem' HLEN (fun a _ => AV a)).
  - intros a _ (Hh & b & Hb). split; [exact Hh|]. exists b.
    pose proof (MEQ (Z_to_bv 64 a)) as Ma. unfold mrestrict in Ma. rewrite Hh in Ma. rewrite Ma. exact Hb.
  - exact (up_mode_ext cx W W mem mem' mode nch ns AV).
  - exact HMEM.
Qed.

(* Two materialisations in a row are the last one (YK04.v:550 with_vm_backing reads only the record's fields). *)
Lemma up_wvb2 : forall (md : Model) a b,
  with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) a md)) b (with_vm_backing (m_vm_lazy md) a md) =
  with_vm_backing (m_vm_lazy md) b md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a b. reflexivity. Qed.

(* A run whose regions are all read only writes no byte. *)
Lemma up_frame_ro : forall E rs (m m' : word -> option byte),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
  intros E rs m m' Hro HF x. apply HF. intros (r & Hin & Hr).
  rewrite forallb_forall in Hro. pose proof (Hro r Hin) as Hw. apply Z.leb_le in Hw. lia.
Qed.

(* A block a call has just added is not one the state had before (the blocks of a state are disjoint and a
   block is never empty, req_size >= 1). *)
Lemma up_new_not_old : forall ly S (W : world segs) mem md lyc Sc (b n : Z),
  AR segs B ly S W mem md -> ablocks B ly S = ablocks B lyc Sc ++ [(b, n)] -> 0 <= n ->
  ~ In (b, n) (ablocks B lyc Sc).
Proof.
  intros ly S W mem md lyc Sc b n HAR Hbl Hn Hin. apply in_split in Hin as (l1 & l2 & Eq).
  pose proof (sep_blocks_pos segs B LAWS ly S W mem md (b, n) (b, n) l1 l2 [] HAR) as D.
  rewrite Hbl, Eq, <- app_assoc in D. cbn [app] in D. specialize (D eq_refl).
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. pose proof (req_size_pos n Hn). lia.
Qed.

(* malloc #3 at +0x7c0 (a0 = s8 = up_sz cx), by amalloc04_rule through YC85.v:191 amalloc04_sub, after
   ReadName.v:841-896; the post is up_post_7c4. The call keeps every byte up_mem reads: the saved words and the
   spill slots lie above sp (acall_kept's first clause), the payload and the body copy are blocks of the state
   (its second), and the fake frame and its shadow are the state's own frame (its fourth). *)
Lemma up_malloc_call : up_trace_stmt ->
  forall (cx : dctx) (res mode nch ns : Z) ly0 S0 (W0 : world segs) (regsT : bvmap 5 word) memT mdT,
  up_base cx -> dec_a_rom cx -> up_geom cx ->
  up_run cx res mode nch ns (up_bl0 cx res) dec_ev_748 ly0 S0 W0 regsT memT mdT ->
  4096 <= res ->
  mo_le MT (d_S cx) S0 (dec_spent_748 MT (d_n cx)) -> mo_ok MT S0 (dec_rest_748 MT) ->
  YK11.getr regsT 1 = w64 (DEC_A_LLVMF + UP_MALLOC_RA) ->
  YK11.getr regsT 10 = w64 (up_sz cx) ->
  YK11.getr regsT 22 = w64 (up_cnt cx) -> YK11.getr regsT 24 = w64 (up_sz cx) ->
  SRr segs W0 (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom segs)) mdT)
    (up_post_7c4 cx res mode nch ns).
Proof.
intros UPTR cx res mode nch ns ly0 S0 W0 regsT memT mdT HBASE HROMcx HGEOM HRUN Hres HMLE HMOK Hra Ha0 Hs6 Hs8.
pose proof HRUN as (HJ & Hfrms & Hr8 & Hr9 & Hsp & Hgp & Htp & Hinp & HPERM & HFR & Hr18 & Hr20 & Hr26 & HMEM).
pose proof HMEM as (Hsaved & _).
destruct (up_base_facts cx HBASE) as (HAR0 & HLEN & Hn & Hev & Hbb).
destruct (UPTR cx ly0 S0 W0 memT mdT dec_ev_748 regsT HBASE HGEOM HJ Hsaved Hr8 Hsp Hra) as (ch & Hch & Htr).
pose proof HJ as (HARc & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstk & F5 & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HGEOM as (Hsp1r & Hsp1al & HF4096 & HFal).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAS : ASTACK = 16384) by reflexivity.
assert (HSTK : DEC_LLVMF_STK = 32768) by reflexivity.
assert (Hsp1_16 : d_sp1 cx mod 16 = 0).
{ pose proof (Z.div_mod (d_sp1 cx) 32 ltac:(lia)) as D. rewrite Hsp1al, Z.add_0_r in D. rewrite D.
  replace (32 * (d_sp1 cx / 32)) with ((2 * (d_sp1 cx / 32)) * 16) by lia. apply Z.mod_mul. lia. }
assert (Ho16 : (d_sp1 cx - d_sp0 cx) mod 16 = 0).
{ rewrite Zminus_mod, Hsp1_16, Hsp0al. reflexivity. }
eapply SRr_bind.
{ eapply (amalloc04_sub segs B LAWS decode_segs_low MT (AM fx) W0 regsT memT DEC_LLVMF_STK (d_sp0 cx) []
    (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly0 S0 mdT dec_ev_748
    (up_sz cx) (d_sp1 cx - d_sp0 cx) (w64 (DEC_A_LLVMF + UP_MALLOC_RA)) ch HJ Ha0).
  - exact (up_room_sz cx).
  - exact (up_room_live cx res ly0 S0 HPERM Hbb Hn).
  - rewrite Hsp. lia.
  - exact Ho16.
  - lia.
  - rewrite HAS, HSTK. lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - unfold w64. rewrite <- up_base_eq. apply ret_ok_codeptr_v; [unfold UP_MALLOC_RA; lia | reflexivity].
  - exact (up_room_ev cx S0 ltac:(exact Hnev) Hev).
  - exact Hch.
  - exact Htr.
  - exact (up_meter_malloc cx S0 MTL HMOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & upb & -> & HJ2 & HP2 & Hupb & Hfr2 & H4096 & Hbl & HK & MLE & _).
assert (P : forall r, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regsT (Z_to_bv 5 r))
  by exact HP2.
pose proof HJ2 as (HAR2 & Hly2 & _).
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (up_sz_bounds cx) as Hszb.
assert (Hreq : req_size (up_sz cx) = up_sz cx)
  by (unfold req_size; destruct (Z.eqb_spec (up_sz cx) 0); lia).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly0 HAR0 Hly) as (_ & HFA0 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR0 Hly2) as (_ & HFA2 & _).
assert (Hfb : fs_frame_bytes DEC_FCLASS = 64) by reflexivity.
assert (HinF0 : In (DEC_FCLASS, d_fpos cx) (frames S0)) by (rewrite Hfrms; left; reflexivity).
assert (HinF2 : In (DEC_FCLASS, d_fpos cx) (frames S2)) by (rewrite Hfr2; exact HinF0).
assert (HinU : In (upb, up_sz cx) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (HnotU : ~ In (upb, up_sz cx) (ablocks B ly0 S0)) by (exact (up_new_not_old _ _ _ _ _ _ _ _ _ HAR2 Hbl ltac:(lia))).
destruct (frames_bounds segs B LAWS _ _ _ _ _ _ _ HAR2 HinF2) as (HfbA & HfbB & HfbC).
rewrite HFA2 in HfbA, HfbB. rewrite Hfb in HfbB.
assert (HFhi : d_F cx + 64 <= alloc_ceiling) by (unfold d_F; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ upb (up_sz cx) HAR2 HinU) as (_ & HU4096 & HUceil & HUapp & _).
rewrite Hreq in HUceil, HUapp.
(* the new block shares no byte with the fake frame, nor with the state's other blocks *)
assert (HdF : upb + up_sz cx <= d_F cx \/ d_F cx + 64 <= upb).
{ pose proof (sep_block_frame segs B LAWS _ _ _ _ _ upb (up_sz cx) DEC_FCLASS (d_fpos cx) HAR2 HinU HinF2) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite Hreq, HFA2, Hfb in D. unfold d_F. lia. }
assert (HdB : forall b m, In (b, m) (ablocks B ly0 S0) -> upb + up_sz cx <= b \/ b + req_size m <= upb).
{ intros b m Hin.
  assert (Hin2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; left; exact Hin).
  assert (Hne : (b, m) <> (upb, up_sz cx)) by (intros Heq; rewrite Heq in Hin; exact (HnotU Hin)).
  pose proof (sep_blocks segs B LAWS _ _ _ _ _ b m upb (up_sz cx) HAR2 Hin2 HinU Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite Hreq in D. lia. }
assert (KT : forall a, up_touch cx res a -> aview segs (w_H W2) mem2 a = aview segs (w_H W0) memT a).
{ intros a Ha. unfold up_touch in Ha.
  destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]].
  - apply K1; [rewrite HSTK in Hslo; lia | rewrite HAS; lia].
  - apply K1; [rewrite HSTK in Hslo; lia | rewrite HAS; lia].
  - apply (K4 DEC_FCLASS (d_fpos cx) a HinF0).
    + left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite HFA0, Hfb. unfold d_F in Ha. lia.
    + intros Hu; cbv beta in Hu; rewrite Hreq in Hu. clear - Hu Ha HdF. lia.
  - apply (K4 DEC_FCLASS (d_fpos cx) a HinF0).
    + right. unfold in_zr. cbn [fst snd]. rewrite HFA0, Hfb. change (64 / 8) with 8. unfold d_SH, d_F in Ha. lia.
    + intros Hu; cbv beta in Hu; rewrite Hreq in Hu.
      apply (fshadow_not_app (d_F cx) 8 upb (up_sz cx) a HF4096); [ | exact HUapp | | exact Hu ].
      * unfold d_F. lia.
      * unfold d_SH, shadow_addr, SHADOW_OFF in Ha. lia.
  - assert (Hn0 : 0 < d_n cx) by lia.
    replace a with (d_p cx + (a - d_p cx)) by lia.
    pose proof (Hinp Hn0) as Hin. pose proof (req_size_pos (d_n cx) ltac:(lia)) as Hrq.
    apply (K2 (d_p cx) (d_n cx) (a - d_p cx) Hin); [lia|].
    intros Hu; cbv beta in Hu; rewrite Hreq in Hu. pose proof (HdB _ _ Hin). lia.
  - assert (Hin : In (res, up_len cx) (ablocks B ly0 S0))
      by (eapply Permutation_in; [apply Permutation_sym, HPERM | unfold up_bl0; apply in_or_app; right; left; reflexivity]).
    replace a with (res + (a - res)) by lia.
    pose proof (req_size_pos (up_len cx) ltac:(unfold up_len, dec_a_len; lia)) as Hrq.
    apply (K2 res (up_len cx) (a - res) Hin); [lia|].
    intros Hu; cbv beta in Hu; rewrite Hreq in Hu. pose proof (HdB _ _ Hin). lia. }
assert (KF : forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W0) memT a)
  by (intros a Ha; apply KT; unfold up_touch; right; right; left; exact Ha).
apply SRr_ret. unfold up_post_7c4; cbv beta. exists ly2, S2, regs2, mem2, md2, upb.
split; [reflexivity|].
split; [|exact Hupb].
unfold up_mid.
split.
{ unfold up_run.
  split; [replace dec_ev_86c with (dec_ev_748 + 1) by reflexivity; exact HJ2|].
  split; [rewrite Hfr2; exact Hfrms|].
  split; [exact (eq_trans (P 8 ltac:(unfold acallee_saved; lia)) Hr8)|].
  split; [exact (eq_trans (P 9 ltac:(unfold acallee_saved; lia)) Hr9)|].
  split; [unfold spZ in *; rewrite <- Hsp; f_equal; exact (P 2 ltac:(unfold acallee_saved; lia))|].
  split; [exact (eq_trans (P 3 ltac:(unfold acallee_saved; lia)) Hgp)|].
  split; [exact (eq_trans (P 4 ltac:(unfold acallee_saved; lia)) Htp)|].
  split; [intros Hn0; rewrite Hbl; apply in_or_app; left; exact (Hinp Hn0)|].
  split; [rewrite Hbl; unfold up_bl1; apply Permutation_app_tail; exact HPERM|].
  split.
  { destruct HFR as (F19 & F21 & F27).
    split; [exact (eq_trans (P 19 ltac:(unfold acallee_saved; lia)) F19)|].
    split; [exact (eq_trans (P 21 ltac:(unfold acallee_saved; lia)) F21)|].
    exact (eq_trans (P 27 ltac:(unfold acallee_saved; lia)) F27). }
  split; [exact (eq_trans (P 18 ltac:(unfold acallee_saved; lia)) Hr18)|].
  split; [exact (eq_trans (P 20 ltac:(unfold acallee_saved; lia)) Hr20)|].
  split; [exact (eq_trans (P 26 ltac:(unfold acallee_saved; lia)) Hr26)|].
  apply (up_mem_kept_fr cx res mode nch ns W0 W2 memT mem2 HLEN KT).
  - intros a Ha Hp. apply (apresent_transfer segs (w_H W0) (w_H W2) memT mem2 a); [lia | | exact (KF a Ha) | exact Hp].
    apply (frm_img segs B LAWS _ _ _ _ _ DEC_FCLASS (d_fpos cx) a HARc HinF0). rewrite HFA0, Hfb. unfold d_F in Ha. lia.
  - exact (up_mode_kept cx _ _ _ _ _ _ _ _ _ _ mode nch ns HARc HAR2
             (HROM_KEPT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROMcx) (HROM_KEPT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROMcx)
             KF).
  - exact HMEM. }
split; [exact H4096|].
split; [exact HinU|].
split.
{ intros Hin. apply HnotU. eapply Permutation_in; [apply Permutation_sym, HPERM|].
  unfold up_bl0. apply in_or_app. left. exact Hin. }
split; [exact (up_meter_le cx S0 S2 MTL HMLE MLE)|].
split; [exact (up_meter_rest cx S0 S2 MTL HMOK MLE)|].
split; [exact (eq_trans (P 22 ltac:(unfold acallee_saved; lia)) Hs6)|].
exact (eq_trans (P 24 ltac:(unfold acallee_saved; lia)) Hs8).
Qed.

Lemma up_A2_of_trace : up_trace_stmt -> up_A2_stmt.
Proof.
intros UPTR. unfold up_A2_stmt.
intros cx res mode nch ns W0 c0 HBASE HROMcx HGEOM H79c.
destruct H79c as (ly0 & S0 & regs0 & mem0 & md0 & -> & HRUN & Hres & HMLE & HMOK & Ha0 & Hs6).
pose proof HRUN as (HJ & Hfrms & Hr8 & Hr9 & Hsp & Hgp & Htp & Hinp & HPERM & HFR & Hr18 & Hr20 & Hr26 & HMEM).
pose proof (up_seat UP_CMP W0 regs0 mem0 (up_obj9_val _ _ _ _ _ CELLS (proj1 HJ)) Hr18) as HS.
set (E := Eimg (Ereg regs0 (@nil word))) in *.
assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
assert (SHOK : sh_ok pa_segs (SOff 18 0) (@nil shent) E (mrestrict (w_H W0) mem0)) by apply Forall_nil.
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs0 r)
  by (intros n r Hn; unfold E; apply ew_Eimg_Ereg_nat; exact Hn).
unfold cfg_at.
psrr_branch_tok RUN BR HS SHOK Bspan.
1: { exfalso. rewrite branch_ne_U, !U_SOff in Hc.
     rewrite (ER 22%nat 22%bv eq_refl), (ER 10%nat 10%bv eq_refl), Hs6, Ha0, Z.eqb_refl in Hc.
     discriminate Hc. }
destruct (up_base_facts cx HBASE) as (_ & HLEN & Hn & _ & _).
assert (Hlen : 0 <= up_len cx < 2 ^ 26) by (unfold up_len, dec_a_len; lia).
assert (E22 : ew E 22 = w64 (up_cnt cx)) by exact (eq_trans (ER 22%nat 22%bv eq_refl) Hs6).
assert (HAE : env_agree 32 (Ereg regs0 (@nil word)) E)
  by (split; [intros n Hnn; unfold E; apply Eimg_low; unfold A_TEXT; lia | unfold E; reflexivity]).
pose proof (up_cnt_range (up_len cx) Hlen) as Hcr. fold (up_cnt cx) in Hcr.
pose proof (up_olen_val (up_len cx) Hlen) as Hov. fold (up_cnt cx) in Hov. fold (up_sz cx) in Hov.
(* +0x79c .. +0x7a0 *)
paj_run_tok RUN HS HJ SHOK Bspan; [ up_awr | ].
lazymatch type of HF with frame_of _ ?rs ?m0 ?m1 =>
  pose proof (up_frame_ro _ rs m0 m1 ltac:(vm_compute; reflexivity) HF) as MEQ1 end. clear HF HFr HG.
(* +0x7a0: bgtz s6 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
all: rewrite (up_bgtz E (up_cnt cx) E22 ltac:(destruct Hcr as [Hm | (Hc2 & _)]; lia)) in Hc0.
(* +0x7a4 / +0x7ac .. +0x7c0: s8, a0, and the call *)
all: paj_run_tok RUN HS HJ SHOK Bspan; [ up_awr | ].
all: lazymatch goal with HF : frame_of _ ?rs ?m0 ?m1 |- _ =>
       pose proof (up_frame_ro _ rs m0 m1 ltac:(vm_compute; reflexivity) HF) as MEQ2 end; clear HF HFr HG.
all: match goal with
     | HR : up_run _ _ _ _ _ _ _ _ _ _ _ ?mm _,
       M2 : forall x : word, mrestrict ?H (ms_mem ?b) x = mrestrict ?H (ms_mem ?a) x,
       M1 : forall x : word, ms_mem ?a x = ?mm x |- _ =>
         assert (MEQ : forall x, mrestrict H (ms_mem b) x = mrestrict H mm x)
           by (intros x; rewrite M2; unfold mrestrict; rewrite M1; reflexivity)
     end.
all: rewrite up_wvb2 in HJ.
all: pose proof (regs_kept_of_st_ok segs _ _ _ regs0 (@nil word)
        (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]) HS HAE ltac:(vm_compute; reflexivity)) as KEEP.
all: cbn [ms_regs restrict] in KEEP.
all: up_reg HS (1%bv : bv 5) Rra.
all: up_reg HS (10%bv : bv 5) Ra0'.
all: up_reg HS (24%bv : bv 5) Rs8.
all: pmkst HS.
all: change (pa_sigma DS___interceptor_trampoline_malloc) with (decode_sigma DS___interceptor_trampoline_malloc).
all: rewrite <- HPCM.
all: apply (up_malloc_call UPTR cx res mode nch ns ly0 S0 W0 _ _ _ HBASE HROMcx HGEOM).
all: try (apply (up_run_after cx res mode nch ns _ _ ly0 S0 W0 regs0 mem0 md0 _ _ _ HRUN HJ MEQ); [
            intros nn Hnn; apply KEEP; apply in_map; cbn in Hnn |- *; tauto | exact HLEN ]).
all: try exact Hres.
all: try exact HMLE.
all: try exact HMOK.
all: try (rewrite Rra, codeptr_val, up_base_eq by assumption; reflexivity).
all: try exact (eq_trans (KEEP (Z_to_bv 5 22)
        (in_map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27] 22 ltac:(cbn; tauto))) Hs6).
(* the taken arm: 0 < up_cnt, a0 = s8 = 36 * up_cnt *)
1: { apply Z.ltb_lt in Hc0. destruct Hcr as [Hm | (Hc2 & Hev & Hleq)]; [lia|].
     destruct Hov as (_ & Hpos & _). rewrite (Hpos ltac:(lia)).
     rewrite Ra0', denot_lit_U, U_SAlu. cbn [zalu_raw].
     rewrite (up_s8_val E (up_cnt cx) E22 Hc2), U_SLit.
     unfold w64. f_equal. rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r.
     apply zcanon_id. unfold M64. lia. }
1: { apply Z.ltb_lt in Hc0. destruct Hcr as [Hm | (Hc2 & Hev & Hleq)]; [lia|].
     destruct Hov as (_ & Hpos & _). rewrite (Hpos ltac:(lia)).
     rewrite Rs8, denot_lit_U, (up_s8_val E (up_cnt cx) E22 Hc2). reflexivity. }
(* the arm not taken: up_cnt = -1, a0 = s8 = 1 *)
1: { apply Z.ltb_ge in Hc0. destruct Hcr as [Hm | (Hc2 & _)]; [|lia].
     destruct Hov as (Hneg & _). rewrite (Hneg ltac:(lia)).
     rewrite Ra0'; reflexivity. }
1: { apply Z.ltb_ge in Hc0. destruct Hcr as [Hm | (Hc2 & _)]; [|lia].
     destruct Hov as (Hneg & _). rewrite (Hneg ltac:(lia)).
     rewrite Rs8; reflexivity. }
Qed.

Lemma up_A2 : up_A2_stmt.
Proof. exact (up_A2_of_trace up_trace). Qed.

(* ---------------------------------------------------------------- *)
(* Stage C: +0x7fc .. +0x858, the two refused-call checks and loop L5 *)
(* ---------------------------------------------------------------- *)

(* The states the engine is seated with. At +0x7fc: every register its own atom, no region, the shadow base
   fact. At the loop head +0x818: the same, plus the one byte a2 points at (read only, 0xa5) and the pointer
   fact on a0's atom that the token discharge of the shadow check needs (ob_in_span). *)
Definition up_C_byte : YP09.region :=
  YP09.mkRegion (Some 12%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit DEC_FILL))].
Definition up_C_facts : facts := mkFacts [(10%nat, YC4b.PTR 0); (18%nat, mkAF SB SB 0)] [] [].

Lemma up_C_seat : forall (pc : Z) (rs : smem) (G : facts) (W : world segs) (regs : bvmap 5 word) mem,
  regions_wf rs = true ->
  Forall (region_ok segs (Eimg (Ereg regs [])) (mrestrict (w_H W) mem)) rs ->
  pairwise_disjoint (Eimg (Ereg regs [])) rs ->
  facts_ok (Eimg (Ereg regs [])) G ->
  st_ok_pi segs pa_val (Eimg (Ereg regs [])) (mkSS pc sr_atoms rs None G)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (DEC_A_LLVMF + pc)) mem (seg_rom segs))).
Proof.
  intros pc rs G W regs mem Hwf Hok Hdj HG.
  rewrite restrict_mkst_fx. rewrite <- up_base_eq.
  exact (pa_entry_st_ok_full (PI := PI_decode) _ pc sr_atoms regs rs G (mrestrict (w_H W) mem)
           (regs_ok_Eimg_Ereg regs []) Hwf Hok Hdj HG).
Qed.

(* An atom below A_TEXT of the entry environment is the register of the same number. *)
Lemma up_C_ew_reg : forall (regs : bvmap 5 word) (n : nat) (r : Prelude.reg),
  Z.of_nat n = bv_unsigned r -> (n < A_TEXT)%nat -> ew (Eimg (Ereg regs [])) n = YK11.getr regs r.
Proof. intros regs n r Hr Hn. rewrite Eimg_low by exact Hn. exact (ew_Ereg_nat regs [] n r Hr). Qed.

Lemma up_C_den_atom : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
  intros E n. apply bv_eq. change (bv_unsigned (sv_denot E (SOff n 0))) with (U E (SOff n 0)).
  rewrite U_SOff, Z.add_0_r. apply zcanon_id. pose proof (u64_range (ew E n)). unfold M64. lia.
Qed.

Lemma up_C_den_off : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n c v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. reflexivity. Qed.

Lemma up_C_den_or0 : forall E n, ew E n = Z_to_bv 64 0 ->
  sv_denot E (SAlu ALU_OR (SOff n 0) (SLit 0)) = w64 0.
Proof. intros E n H. cbn [sv_denot]. rewrite H. apply bv_eq. vm_compute. reflexivity. Qed.

(* The refused-call checks +0x800 / +0x804: the register holds -1, so `bne r, a1(= -1)` is not taken. *)
Lemma up_C_ne_m1 : forall E n, ew E n = w64 (-1) ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 18446744073709551615)) = false.
Proof. intros E n H. rewrite branch_ne_U. unfold U. cbn [sv_denot]. rewrite H. vm_compute. reflexivity. Qed.

(* The back edge +0x844: a3 - 1 is the counter after the pass. *)
Lemma up_C_ne_cnt : forall E v, ew E 13 = Z_to_bv 64 v -> 1 <= v < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff 13 (-1))) (sv_denot E (SLit 0)) = negb (v - 1 =? 0).
Proof.
  intros E v H Hv. rewrite branch_ne_U, (U_atom_off E 13 v (-1) H) by lia. rewrite U_lit by lia.
  replace (v + -1) with (v - 1) by lia. reflexivity.
Qed.

(* The loop's byte, 0xa5, as the region's one-byte chunk. *)
Lemma up_C_val_mem1 : forall H (m : word -> option byte) a,
  aview segs H m a = Some DEC_FILL -> val_mem segs (mrestrict H m) a 1 DEC_FILL.
Proof.
  intros H m a Hv kk Hk. assert (kk = 0%nat) as -> by lia.
  destruct (aview_byte segs H m a DEC_FILL Hv) as (b & Hb & Hbv & _).
  change (a + Z.of_nat 0) with (a + 0). rewrite Z.add_0_r, Hb.
  f_equal. apply bv_eq. rewrite <- Hbv. vm_compute. reflexivity.
Qed.

(* The registers stage C does not write (it writes a0..a5 only), as far as up_mid and the cut points read them. *)
Definition up_C_keep (regs regs2 : bvmap 5 word) : Prop :=
  YK11.getr regs2 2 = YK11.getr regs 2 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\
  YK11.getr regs2 4 = YK11.getr regs 4 /\ YK11.getr regs2 8 = YK11.getr regs 8 /\
  YK11.getr regs2 9 = YK11.getr regs 9 /\ YK11.getr regs2 18 = YK11.getr regs 18 /\
  YK11.getr regs2 19 = YK11.getr regs 19 /\ YK11.getr regs2 20 = YK11.getr regs 20 /\
  YK11.getr regs2 21 = YK11.getr regs 21 /\ YK11.getr regs2 22 = YK11.getr regs 22 /\
  YK11.getr regs2 23 = YK11.getr regs 23 /\ YK11.getr regs2 24 = YK11.getr regs 24 /\
  YK11.getr regs2 26 = YK11.getr regs 26 /\ YK11.getr regs2 27 = YK11.getr regs 27.

Lemma up_C_mid_keep : forall (cx : dctx) (res mode nch ns upb : Z) ly S (W : world segs) regs regs2 mem md md2,
  up_mid cx res mode nch ns upb ly S W regs mem md ->
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S W mem md2 dec_ev_86c ->
  up_C_keep regs regs2 ->
  up_mid cx res mode nch ns upb ly S W regs2 mem md2.
Proof.
  intros cx res mode nch ns upb ly S W regs regs2 mem md md2
    ((_ & FR & R8 & R9 & SP & R3 & R4 & PB & PM & (D19 & D21 & D27) & R18 & R20 & R26 & UM)
       & M2 & M3 & M4 & M5 & M6 & R22 & R24)
    HJ (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K26 & K27).
  assert (SP2 : spZ regs2 = spZ regs) by (unfold spZ; f_equal; exact K2).
  split; [|exact (conj M2 (conj M3 (conj M4 (conj M5 (conj M6 (conj (eq_trans K22 R22) (eq_trans K24 R24)))))))].
  exact (conj HJ (conj FR (conj (eq_trans K8 R8) (conj (eq_trans K9 R9) (conj (eq_trans SP2 SP)
    (conj (eq_trans K3 R3) (conj (eq_trans K4 R4) (conj PB (conj PM
    (conj (conj (eq_trans K19 D19) (conj (eq_trans K21 D21) (eq_trans K27 D27)))
    (conj (eq_trans K18 R18) (conj (eq_trans K20 R20) (conj (eq_trans K26 R26) UM))))))))))))).
Qed.

(* The run's frame: every region is read only, so memory is unchanged. HMEM: the current machine memory is the
   cut point's (HJ and SHOK stay at the machine memory, which the next run asks). *)
Ltac up_C_mem HMEM :=
  lazymatch goal with
  | HF : frame_of _ ?rs ?m0 (ms_mem ?msn) |- _ =>
      let Hm := fresh "Hm" in
      pose proof (frame_of_read_only _ rs m0 (ms_mem msn) ltac:(vm_compute; reflexivity) HF) as Hm;
      clear HF;
      try (rewrite HMEM in Hm; clear HMEM);
      rename Hm into HMEM;
      repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
(* The model after a run, abstracted (the term would double at each run). *)
Ltac up_C_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    lazymatch mdx with
    | with_vm_backing _ _ _ => let mdv := fresh "md" in set (mdv := mdx) in *; clearbody mdv
    | _ => idtac
    end
  end.
(* A register of the current machine state as the engine's symbolic value. *)
Ltac up_C_rd HS :=
  lazymatch goal with |- YK11.getr (ms_regs ?msx) ?r = _ =>
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hx msx) =>
      rewrite (st_ok_pi_restrict_reg Hx Ex ssx msx r HS);
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      change (sr_get (ss_regs ssx) r) with e
    end
  end.
(* An atom below A_TEXT of the current environment (the entry one under the tokens' ewset layers). *)
Ltac up_C_low r :=
  repeat (rewrite ew_ewset_other by lia);
  rewrite (up_C_ew_reg _ _ r) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]).
Ltac up_C_kreg HS :=
  lazymatch goal with |- YK11.getr (ms_regs _) ?r = YK11.getr _ ?r =>
    up_C_rd HS; rewrite up_C_den_atom; up_C_low r; try reflexivity
  end.

(* +0x7fc .. +0x818: both refused calls returned -1 (the two `bne` to the trap block are refuted), then the loop
   is set up: a1 := 0, a0 = a2 := s7 (the buffer), a3 := s8 (its size). *)
Lemma up_C_head : forall (cx : dctx) (res mode nch ns : Z) (W : world segs) (c : config),
  up_post_7fc cx res mode nch ns W c -> SRr segs W c (up_loop cx res mode nch ns 0).
Proof.
  intros cx res mode nch ns W c (ly & S & regs & mem & md & upb & -> & HM & H23 & HFILL & H25 & H10).
  pose proof HM as HM0.
  destruct HM as ((HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H18 & _ & _ & _) & _ & _ & _ & _ & _ & _ & H24).
  pose proof (up_sz_bounds cx) as HSZ.
  assert (E18 : ew (Eimg (Ereg regs [])) 18 = w64 SHADOW_OFF) by (up_C_low (18%bv : bv 5); exact H18).
  assert (E25 : ew (Eimg (Ereg regs [])) 25 = w64 (-1)) by (up_C_low (25%bv : bv 5); exact H25).
  assert (E10 : ew (Eimg (Ereg regs [])) 10 = w64 (-1)) by (up_C_low (10%bv : bv 5); exact H10).
  assert (HG : facts_ok (Eimg (Ereg regs [])) up_facts).
  { split; [| split; [exact I | exact I]].
    cbn [up_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E18, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. unfold SB, SHADOW_OFF. repeat split; try exact I; lia. }
  pose proof (up_C_seat UP_DEC2_RA [] up_facts W regs mem eq_refl (Forall_nil _) I HG) as HS.
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
  assert (SHOK : sh_ok pa_segs (SOff 18 0) (@nil shent) (Eimg (Ereg regs [])) (mrestrict (w_H W) mem))
    by apply Forall_nil.
  unfold cfg_at.
  (* +0x7fc .. +0x800 *)
  paj_run_tok RUN HS HJ SHOK Bspan; [ up_awr | ].
  up_C_mem HMEM. up_C_md.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  1: { exfalso. lazymatch goal with Hx : branch_taken _ _ _ = true |- _ =>
         rewrite (up_C_ne_m1 _ 25 E25) in Hx; discriminate Hx end. }
  (* +0x800 .. +0x804 *)
  paj_run_tok RUN HS HJ SHOK Bspan; [ up_awr | ].
  up_C_mem HMEM. up_C_md.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  1: { exfalso. lazymatch goal with Hx : branch_taken _ _ _ = true |- _ =>
         rewrite (up_C_ne_m1 _ 10 E10) in Hx; discriminate Hx end. }
  (* +0x804 .. +0x818 *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan UP_LOOP; [ up_awr | ].
  up_C_mem HMEM. up_C_md. rewrite HMEM in HJ.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (HK : up_C_keep regs (ms_regs msx)) by (unfold up_C_keep; repeat split; up_C_kreg HS) end.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K23 & _).
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) ?mdx) _ =>
    apply SRr_ret; exists ly, S, rg, mem, mdx, upb end.
  split; [rewrite HMEM, up_base_eq; reflexivity |].
  split; [exact (up_C_mid_keep cx res mode nch ns upb ly S W regs _ mem md _ HM0 HJ HK) |].
  split; [exact (eq_trans K23 H23) |].
  split; [exact HFILL |].
  split; [lia |].
  split; [up_C_rd HS; rewrite up_C_den_atom; up_C_low (23%bv : bv 5); rewrite H23, Z.add_0_r; reflexivity |].
  split; [up_C_rd HS; reflexivity |].
  split; [up_C_rd HS; rewrite up_C_den_atom; up_C_low (23%bv : bv 5); rewrite H23, Z.add_0_r; reflexivity |].
  up_C_rd HS; rewrite up_C_den_atom; up_C_low (24%bv : bv 5); rewrite H24, Z.sub_0_r; reflexivity.
Qed.

(* One pass of L5 from its head: the shadow check of the byte at a0 is the engine's token discharge (its
   obligation is the byte's addressability, from the block (upb, up_sz)), the byte is 0xa5 so a1 stays 0, and the
   back edge either returns to the head at i + 1 or falls through to +0x858. *)
Lemma up_C_body : forall (cx : dctx) (res mode nch ns i : Z) (W : world segs) (c : config),
  up_loop cx res mode nch ns i W c ->
  SRr segs W c (fun W' c' => up_post_858 cx res mode nch ns W' c' \/
    exists i', 0 <= up_sz cx - i' < up_sz cx - i /\ up_loop cx res mode nch ns i' W' c').
Proof.
  intros cx res mode nch ns i W c
    (ly & S & regs & mem & md & upb & -> & HM & H23 & HFILL & Hi & H10 & H11 & H12 & H13).
  pose proof HM as HM0.
  destruct HM as ((HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H18 & _ & _ & _) & _ & HIN & _ & _ & _ & _ & _).
  pose proof (up_sz_bounds cx) as HSZ.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ upb (up_sz cx) (proj1 HJ) HIN) as (_ & Hb4096 & Hbceil & _).
  pose proof (req_size_pos (up_sz cx) ltac:(lia)) as [_ HRQ].
  pose proof (@YM05.alloc_ceiling_value rc) as [[_ HCH] _].
  assert (E18 : ew (Eimg (Ereg regs [])) 18 = w64 SHADOW_OFF) by (up_C_low (18%bv : bv 5); exact H18).
  assert (E10 : ew (Eimg (Ereg regs [])) 10 = w64 (upb + i)) by (up_C_low (10%bv : bv 5); exact H10).
  assert (E12 : ew (Eimg (Ereg regs [])) 12 = w64 (upb + i)) by (up_C_low (12%bv : bv 5); exact H12).
  assert (HR : region_ok segs (Eimg (Ereg regs [])) (mrestrict (w_H W) mem) up_C_byte).
  { unfold up_C_byte, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E12, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs _ _ (upb + i) 0 1%N (SLit DEC_FILL) DEC_FILL).
    - reflexivity.
    - unfold DEC_FILL. cbn. lia.
    - cbn. lia.
    - rewrite Z.add_0_r. apply up_C_val_mem1. apply HFILL. lia. }
  assert (HG : facts_ok (Eimg (Ereg regs [])) up_C_facts).
  { split; [| split; [exact I | exact I]].
    cbn [up_C_facts f_atoms atoms_ok]. unfold afact_ok, YC4b.PTR. cbn [af_lo af_hi af_al2].
    rewrite E10, E18, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF. repeat split; try exact I; lia. }
  pose proof (up_C_seat UP_LOOP [up_C_byte] up_C_facts W regs mem ltac:(vm_compute; reflexivity)
    ltac:(apply Forall_cons; [exact HR | apply Forall_nil]) ltac:(cbn [pairwise_disjoint all_disjoint]; split; exact I) HG) as HS.
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
  assert (SHOK : sh_ok pa_segs (SOff 18 0) (@nil shent) (Eimg (Ereg regs [])) (mrestrict (w_H W) mem))
    by apply Forall_nil.
  unfold cfg_at.
  (* +0x818 .. +0x844: the obligation is range_addressable .. (upb + i) 1. *)
  paj_run_tok RUN HS HJ SHOK Bspan;
    [ rewrite (U_atom _ 18 SHADOW_OFF E18) by (unfold SHADOW_OFF; lia);
      rewrite (U_atom _ 10 (upb + i) E10) by lia;
      exact (range_addressable_of_block segs B LAWS ly S W mem md upb (up_sz cx) (upb + i) 1 (proj1 HJ) HIN
               ltac:(lia) ltac:(lia))
    | up_awr | ].
  up_C_mem HMEM. up_C_md.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (X10 : ew Ex 10 = Z_to_bv 64 (upb + i)) by (up_C_low (10%bv : bv 5); exact H10);
    assert (X11 : ew Ex 11 = Z_to_bv 64 0) by (up_C_low (11%bv : bv 5); exact H11);
    assert (X12 : ew Ex 12 = Z_to_bv 64 (upb + i)) by (up_C_low (12%bv : bv 5); exact H12);
    assert (X13 : ew Ex 13 = Z_to_bv 64 (up_sz cx - i)) by (up_C_low (13%bv : bv 5); exact H13)
  end.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  - (* the back edge is taken: one more pass *)
    lazymatch goal with Hx : branch_taken _ _ _ = true |- _ =>
      rewrite (up_C_ne_cnt _ _ X13) in Hx by lia; apply negb_true_iff, Z.eqb_neq in Hx end.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan UP_LOOP; [ up_awr | ].
    up_C_mem HMEM. up_C_md. rewrite HMEM in HJ.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      assert (HK : up_C_keep regs (ms_regs msx)) by (unfold up_C_keep; repeat split; up_C_kreg HS) end.
    pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K23 & _).
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) ?mdx) _ =>
      apply SRr_ret; right; exists (i + 1); split; [lia|]; exists ly, S, rg, mem, mdx, upb end.
    split; [rewrite HMEM, up_base_eq; reflexivity |].
    split; [exact (up_C_mid_keep cx res mode nch ns upb ly S W regs _ mem md _ HM0 HJ HK) |].
    split; [exact (eq_trans K23 H23) |].
    split; [exact HFILL |].
    split; [lia |].
    split; [up_C_rd HS; rewrite (up_C_den_off _ _ _ _ X10) by lia; unfold w64; f_equal; lia |].
    split; [up_C_rd HS; exact (up_C_den_or0 _ _ X11) |].
    split; [up_C_rd HS; rewrite (up_C_den_off _ _ _ _ X12) by lia; unfold w64; f_equal; lia |].
    up_C_rd HS; rewrite (up_C_den_off _ _ _ _ X13) by lia; unfold w64; f_equal; lia.
  - (* the counter reached zero: +0x848 j +0x858 *)
    lazymatch goal with Hx : branch_taken _ _ _ = false |- _ =>
      rewrite (up_C_ne_cnt _ _ X13) in Hx by lia; apply negb_false_iff, Z.eqb_eq in Hx end.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan UP_TAIL; [ up_awr | ].
    up_C_mem HMEM. up_C_md. rewrite HMEM in HJ.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      assert (HK : up_C_keep regs (ms_regs msx)) by (unfold up_C_keep; repeat split; up_C_kreg HS) end.
    pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K23 & _).
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) ?mdx) _ =>
      apply SRr_ret; left; exists ly, S, rg, mem, mdx, upb end.
    split; [rewrite HMEM, up_base_eq; reflexivity |].
    split; [exact (up_C_mid_keep cx res mode nch ns upb ly S W regs _ mem md _ HM0 HJ HK) |].
    split; [exact (eq_trans K23 H23) |].
    split; [exact HFILL |].
    up_C_rd HS; exact (up_C_den_or0 _ _ X11).
Qed.

(* Stage C: the set-up, then L5 by induction on what is left (SRr_loopZ with m i := up_sz - i). *)
Lemma up_C : up_C_stmt.
Proof.
  intros cx res mode nch ns W c _ _ _ Hpost.
  eapply SRr_bind; [exact (up_C_head cx res mode nch ns W c Hpost) |].
  intros W2 c2 _ HL.
  exact (SRr_loopZ segs Z (fun i => up_sz cx - i) (up_loop cx res mode nch ns) (up_post_858 cx res mode nch ns)
           (up_C_body cx res mode nch ns) 0 W2 c2 HL).
Qed.
(* ---------------------------------------------------------------- *)
(* Stage A1: +0x748 .. +0x79c, the harness's own channel count.     *)
(* ---------------------------------------------------------------- *)

(* q = (len - 52) / 36 as the code computes it at +0x758..+0x768 (s10 is atom 26). *)
Definition up_q : sv :=
  SAlu ALU_SRL (SMd M_MULHU (SOff 26 (-52)) (SLit 16397105843297379215)) (SLit 5).

(* a0 at +0x79c on the in-range path (+0x788..+0x798): q when q is even, -1 when it is odd, sign-extended. *)
Definition up_a0 (q : sv) : sv :=
  SAluw ALU_ADD
    (SAlu ALU_OR (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_AND q (SLit 1)) (SLit 1)) (SLit (-1))) q) (SLit 0).

(* The registers up_run names that the stage does not write. *)
Definition up_keep : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 26%bv; 27%bv].
Ltac up_in := unfold up_keep; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma up_q_U : forall E L, ew E 26 = Z_to_bv 64 L -> 52 <= L < 2 ^ 26 -> U E up_q = (L - 52) / 36.
Proof.
intros E L H26 HL. unfold up_q.
rewrite U_SAlu, U_SMd, U_SOff, H26, unsigned_lit_small by lia.
rewrite !U_lit by lia.
cbn [zalu_raw zmd_raw].
change (Z.land 5 63) with 5. change (Z.of_N 64) with 64.
rewrite (zcanon_id (L + -52)) by (unfold M64; lia).
assert (Hm : 0 <= (L + -52) * 16397105843297379215 < 2 ^ 26 * 2 ^ 64).
{ split; [lia|]. apply Z.mul_lt_mono_nonneg; lia. }
rewrite !Z.shiftr_div_pow2 by lia.
rewrite (zcanon_id ((L + -52) * 16397105843297379215 / 2 ^ 64)).
2: { unfold M64. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
change ((L + -52) * 16397105843297379215 / 2 ^ 64 / 2 ^ 5) with (up_div36 (L + -52)).
rewrite up_div36_ok by lia.
replace (L + -52) with (L - 52) by lia.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma up_r_U : forall E L, ew E 26 = Z_to_bv 64 L -> 52 <= L < 2 ^ 26 ->
  U E (SAlu ALU_SUB (SOff 26 (-52)) (SMd M_MUL up_q (SLit 36))) = (L - 52) mod 36.
Proof.
intros E L H26 HL.
rewrite U_SAlu, U_SMd, (up_q_U E L H26 HL), U_SOff, H26, unsigned_lit_small, U_lit by lia.
cbn [zalu_raw zmd_raw].
rewrite (zcanon_id (L + -52)) by (unfold M64; lia).
pose proof (Z.div_mod (L - 52) 36 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (L - 52) 36 ltac:(lia)) as Bm.
rewrite (zcanon_id ((L - 52) / 36 * 36)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma up_addiw_U : forall E a, 0 <= U E a < 2 ^ 31 ->
  U E (SAluw ALU_ADD a (SLit (-2))) = (U E a - 2) mod 2 ^ 64.
Proof.
intros E a Ha. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite U_SLit.
change (zcanon (-2) mod 2 ^ 32) with 4294967294.
rewrite (Z.mod_small (U E a) (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
change (bv_modulus 64) with (2 ^ 64).
replace (U E a + 4294967294 + 2 ^ 31) with ((U E a - 2 + 2 ^ 31) + 1 * 2 ^ 32) by lia.
rewrite Z.mod_add by lia. rewrite (Z.mod_small (U E a - 2 + 2 ^ 31)) by lia.
replace (U E a - 2 + 2 ^ 31 - 2 ^ 31) with (U E a - 2) by lia. reflexivity.
Qed.

Lemma up_rng_cases : forall w, 0 <= w < 2 ^ 31 ->
  ((38 <? (w - 2) mod 2 ^ 64) = true -> w < 2 \/ 40 < w) /\
  ((38 <? (w - 2) mod 2 ^ 64) = false -> 2 <= w <= 40).
Proof.
intros w Hw. destruct (Z_lt_le_dec w 2) as [Hl|Hl].
- rewrite <- (Z.mod_add (w - 2) 1) by lia. rewrite Z.mod_small by lia.
  split; intros H; [left; lia|]. apply Z.ltb_ge in H. lia.
- rewrite Z.mod_small by lia.
  split; intros H; [apply Z.ltb_lt in H; lia | apply Z.ltb_ge in H; lia].
Qed.

Lemma up_a0_val : forall E q, 2 <= U E q <= 40 ->
  sv_denot E (up_a0 q) = Z_to_bv 64 (if Z.even (U E q) then U E q else -1).
Proof.
intros E q Hq.
assert (HC : forall E1 E2 q1 q2, sv_denot E1 q1 = sv_denot E2 q2 -> sv_denot E1 (up_a0 q1) = sv_denot E2 (up_a0 q2))
  by (intros E1 E2 q1 q2 H; unfold up_a0; cbn [sv_denot]; rewrite H; reflexivity).
set (w := U E q) in *.
set (Ew := mkEnv (fun _ => Z_to_bv 64 w) (fun _ => [])).
assert (HQ : sv_denot E q = sv_denot Ew (SOff 0 0)).
{ cbn [sv_denot Ew ew]. rewrite Z.add_0_r, unsigned_lit_small by lia. unfold w, U. symmetry. apply Z_to_bv_bv_unsigned. }
rewrite (HC E Ew q (SOff 0 0) HQ). unfold Ew. clearbody w. clear HC HQ Ew.
apply bv_eq.
assert (Hb : forallb (fun n => Z.eqb (bv_unsigned (sv_denot (mkEnv (fun _ => Z_to_bv 64 (Z.of_nat n)) (fun _ => []))
  (up_a0 (SOff 0 0)))) (bv_unsigned (Z_to_bv 64 (if Z.even (Z.of_nat n) then Z.of_nat n else -1)))) (seq 2 39) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb (Z.to_nat w)). rewrite Z2Nat.id in Hb by lia.
apply Z.eqb_eq. apply Hb. apply in_seq. lia.
Qed.

Lemma up_m1 : Z_to_bv 64 18446744073709551615 = w64 (-1).
Proof. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity. Qed.


(* up_mem at a memory that agrees byte for byte. *)
Lemma up_mem_same : forall (cx : dctx) (res mode nch ns : Z) (W : world segs) m1 m2,
  d_n cx = Z.of_nat (length (d_pl cx)) -> (forall x, m2 x = m1 x) ->
  up_mem cx res mode nch ns W m1 -> up_mem cx res mode nch ns W m2.
Proof.
intros cx res mode nch ns W m1 m2 HLEN HQ.
assert (HMB : forall H a, mbyte segs (mrestrict H m2) a = mbyte segs (mrestrict H m1) a)
  by (intros H a; unfold mbyte, mrestrict; cbv beta; rewrite HQ; reflexivity).
assert (HAV : forall a, aview segs (w_H W) m2 a = aview segs (w_H W) m1 a)
  by (intros a; unfold aview; rewrite HMB; reflexivity).
apply (up_mem_kept cx res mode nch ns W W m1 m2 HLEN).
- intros a _. apply HAV.
- intros a (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite HQ. exact Hb.
- intros (HM1 & HM2 & HM3 & HM4 & HM5). unfold dec_a_mode_ok.
  assert (RW : forall a, rdword (aview segs (w_H W) m2) a = rdword (aview segs (w_H W) m1) a)
    by (intros a; unfold rdword; rewrite !HAV; reflexivity).
  rewrite !RW. split; [exact HM1|]. split; [exact HM2|]. split; [exact HM3|].
  split; intros k Hk; rewrite HMB; [apply HM4 | apply HM5]; exact Hk.
Qed.

(* up_run at a state whose memory agrees byte for byte and whose kept registers are the same. *)
Lemma up_run_same : forall (cx : dctx) (res mode nch ns : Z) bl k ly S (W : world segs) regs regs2 m1 m2 md md2,
  d_n cx = Z.of_nat (length (d_pl cx)) ->
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S W m2 md2 k ->
  (forall x, m2 x = m1 x) ->
  (forall r, In r up_keep -> YK11.getr regs2 r = YK11.getr regs r) ->
  up_run cx res mode nch ns bl k ly S W regs m1 md -> up_run cx res mode nch ns bl k ly S W regs2 m2 md2.
Proof.
intros cx res mode nch ns bl k ly S W regs regs2 m1 m2 md md2 HLEN HJ HQ HK
  (_ & Hfrs & H8 & H9 & Hsp & H3 & H4 & Hpin & Hperm & (F19 & F21 & F27) & H18 & H20 & H26 & HM).
assert (K : forall r, In r up_keep -> forall v, YK11.getr regs r = v -> YK11.getr regs2 r = v)
  by (intros r Hr v Hv; rewrite (HK r Hr); exact Hv).
unfold up_run, dec_a_fr. unfold spZ in Hsp |- *.
split; [exact HJ|]. split; [exact Hfrs|].
split; [apply K; [up_in | exact H8]|].
split; [apply K; [up_in | exact H9]|].
split; [lazymatch goal with |- bv_unsigned (YK11.getr regs2 ?r) = _ => rewrite (HK r ltac:(up_in)); exact Hsp end|].
split; [apply K; [up_in | exact H3]|].
split; [apply K; [up_in | exact H4]|].
split; [exact Hpin|]. split; [exact Hperm|].
split; [split; [|split]; apply K; first [assumption | up_in]|].
split; [apply K; [up_in | exact H18]|].
split; [apply K; [up_in | exact H20]|].
split; [apply K; [up_in | exact H26]|].
exact (up_mem_same cx res mode nch ns W m1 m2 HLEN HQ HM).
Qed.

Lemma up_A1 : up_A1_stmt.
Proof.
unfold up_A1_stmt.
intros cx res mode nch ns ly' S' W' regs' mem' md' HB HROMcx _ HPRE.
destruct HPRE as (HRUN & Hres & HMLE & HMOK & H10).
pose proof HRUN as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H18 & _ & H26 & _).
pose proof HB as HB'. unfold dec_a_base, dec_lib_pre_x in HB'.
destruct HB' as (_ & _ & _ & _ & Hor & HLEN & _).
assert (Hn : 0 <= d_n cx < 2 ^ 26) by (destruct Hor as [[Hn0 _] | [Hn0 _]]; lia).
assert (HL : 0 <= up_len cx < 2 ^ 26) by (unfold up_len, dec_a_len; lia).
destruct (up_chan_cases (up_len cx) HL) as (C1 & C2 & C3 & C4 & C5).
pose proof (up_seat UP_CHK W' regs' mem' (up_obj9_val _ _ _ _ _ CELLS (proj1 HJ)) H18) as HS.
set (E := Eimg (Ereg regs' (@nil word))) in *.
assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
assert (SHOK : sh_ok pa_segs (SOff 18 0) (@nil shent) E (mrestrict (w_H W') mem')) by apply Forall_nil.
assert (E26 : ew E 26 = Z_to_bv 64 (up_len cx))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 26 26%bv eq_refl); exact H26).
assert (E10 : ew E 10 = w64 (up_cnt cx))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact H10).
assert (HAE : env_agree 32 (Ereg regs' []) E)
  by (split; [intros n Hn'; unfold E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
(* +0x748 .. +0x754: s6 := a0, a1 := 52, a0 := -1, up to `bltu s10, a1`. *)
paj_run_tok RUN HS HJ SHOK Bspan; [ up_awr | ].
psrr_branch_tok RUN BR HS SHOK Bspan.
(* Taken: len < 52, on to +0x79c. Not taken: q and r = len - 52 - 36 q, up to `bnez a2` at +0x778. *)
all: paj_run_tok RUN HS HJ SHOK Bspan; [ up_awr | ].
2: psrr_branch_tok RUN BR HS SHOK Bspan.
(* Taken: r <> 0, on to +0x79c. Not taken: a2 := q - 2 (addiw), a3 := 38, up to `bltu a3, a2` at +0x784. *)
2-3: paj_run_tok RUN HS HJ SHOK Bspan; [ up_awr | ].
3: psrr_branch_tok RUN BR HS SHOK Bspan.
(* Taken: q out of 2 .. 40, on to +0x79c. Not taken: the parity select, on to +0x79c. *)
3-4: paj_run_tok RUN HS HJ SHOK Bspan; [ up_awr | ].
(* Every run wrote nothing: the memory at +0x79c is mem' byte for byte. *)
all: repeat match goal with HFx : frame_of _ _ (mrestrict _ _) _ |- _ => clear HFx end.
all: repeat match goal with HFx : frame_of _ ?rs ?m0 ?m1 |- _ =>
  let Hq := fresh "HQ" in pose proof (up_frame_ro _ rs m0 m1 ltac:(vm_compute; reflexivity) HFx) as Hq; clear HFx end.
all: lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msf) |- _ =>
  assert (HMQ : forall x, ms_mem msf x = mem' x);
  [ intros x; repeat match goal with Hq : forall y : word, ms_mem ?a y = _ |- ms_mem ?a x = _ => rewrite (Hq x) end;
    reflexivity | ] end.
(* a0 and s6 at +0x79c, and the kept registers. *)
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssf (restrict ?Hh ?msf) |- _ =>
  pose proof (st_ok_pi_restrict_reg Hh Ex ssf msf (10%bv : bv 5) HS) as Ra0;
  pose proof (st_ok_pi_restrict_reg Hh Ex ssf msf (22%bv : bv 5) HS) as Rs6;
  let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10 in Ra0;
  let e22 := eval vm_compute in (sr_get (ss_regs ssf) (22%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (22%bv : bv 5)) with e22 in Rs6;
  pose proof (regs_kept_of_st_ok_pi Ex ssf (restrict Hh msf) regs' [] up_keep HS HAE ltac:(vm_compute; reflexivity)) as HK
end.
all: lazymatch type of Rs6 with ?lhs = _ =>
  assert (HS6 : lhs = w64 (up_cnt cx))
    by (rewrite Rs6; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E10) end.
all: clear Rs6.
(* The four engine arms, in order: len < 52; r <> 0; q out of 2 .. 40; q in 2 .. 40. In each, up_chan_cases
   gives up_cnt cx, which is the value a0 holds at +0x79c. *)
all: rewrite branch_ltu_U, (U_atom E 26 (up_len cx) E26), U_lit in Hc by lia.
1: apply Z.ltb_lt in Hc.
1: assert (Hcnt : up_cnt cx = -1) by (unfold up_cnt; exact (C1 Hc)).
2-4: apply Z.ltb_ge in Hc.
2-4: fold up_q in Hc0.
2-4: rewrite branch_ne_U, (up_r_U E (up_len cx) E26), U_lit in Hc0 by lia.
2: apply negb_true_iff, Z.eqb_neq in Hc0.
2: assert (Hcnt : up_cnt cx = -1) by (unfold up_cnt; exact (C2 Hc Hc0)).
3-4: apply negb_false_iff, Z.eqb_eq in Hc0.
3-4: assert (HqU : U E up_q = (up_len cx - 52) / 36) by (apply up_q_U; [exact E26 | lia]).
3-4: assert (Hw : 0 <= (up_len cx - 52) / 36 < 2 ^ 31)
       by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
3-4: fold up_q in Hc1.
3-4: rewrite branch_ltu_U, U_lit in Hc1 by lia.
3-4: rewrite (up_addiw_U E up_q ltac:(rewrite HqU; exact Hw)), HqU in Hc1.
3: apply (proj1 (up_rng_cases ((up_len cx - 52) / 36) Hw)) in Hc1.
3: assert (Hcnt : up_cnt cx = -1) by (unfold up_cnt; exact (C3 Hc Hc0 Hc1)).
4: apply (proj2 (up_rng_cases ((up_len cx - 52) / 36) Hw)) in Hc1.
4: fold up_q in Ra0.
4: fold (up_a0 up_q) in Ra0.
4: rewrite (up_a0_val E up_q ltac:(rewrite HqU; exact Hc1)) in Ra0.
4: rewrite HqU in Ra0.
4: destruct (Z.even ((up_len cx - 52) / 36)) eqn:Hev.
4: assert (Hcnt : up_cnt cx = (up_len cx - 52) / 36) by (unfold up_cnt; exact (C5 Hc Hc0 Hc1 eq_refl)).
5: assert (Hcnt : up_cnt cx = -1)
     by (unfold up_cnt; apply (C4 Hc Hc0 Hc1); rewrite <- Z.negb_even, Hev; reflexivity).
1-3: lazymatch type of Ra0 with ?lhs = _ =>
  assert (HA0 : lhs = w64 (up_cnt cx)) by (rewrite Ra0, Hcnt; cbn [sv_denot]; exact up_m1) end.
4-5: lazymatch type of Ra0 with ?lhs = _ =>
  assert (HA0 : lhs = w64 (up_cnt cx)) by (rewrite Ra0, Hcnt; reflexivity) end.
all: clear Ra0.
(* Close each arm at +0x79c with up_post_79c: the state is the entry's (no byte written, the kept registers
   unchanged), a0 and s6 both hold up_cnt cx. *)
all: lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msf) |- _ =>
  pmkst HS; apply SRr_ret; unfold up_post_79c; cbv beta;
  exists ly', S', (ms_regs msf), (ms_mem msf); eexists end.
all: split; [unfold cfg_at, w64; rewrite up_base_eq; reflexivity|].
all: split; [eapply up_run_same; [exact HLEN | exact HJ | exact HMQ | exact HK | exact HRUN]|].
all: split; [exact Hres|].
all: split; [exact HMLE|].
all: split; [exact HMOK|].
all: split; [exact HA0 | exact HS6].
Qed.
(* ---------------------------------------------------------------- *)
(* Stage B: +0x7c4 .. +0x7fc                                        *)
(* ---------------------------------------------------------------- *)

(* d_n's range, the payload's length and its block, from dec_a_base. The clauses are found by their types
   (LLVMFuzzerTestOneInput_cg.v:102-116: `(n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))`
   and `n = Z.of_nat (length pl)`), never by their position. *)
Lemma upB_base : forall cx : dctx, up_base cx ->
  0 <= d_n cx < 2 ^ 26 /\ d_n cx = Z.of_nat (length (d_pl cx)) /\
  (0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))).
Proof.
intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. clear H.
lazymatch goal with
| Hd : (d_n cx = 0 /\ _) \/ (0 < d_n cx < 2 ^ 26 /\ In (d_p cx, d_n cx) _),
  Hl : d_n cx = Z.of_nat (length (d_pl cx)) |- _ =>
    split; [destruct Hd as [[Hd _] | [Hd _]]; lia|];
    split; [exact Hl|];
    intros Hpos; destruct Hd as [[Hd _] | [_ Hd]]; [lia | exact Hd]
end.
Qed.

Lemma upB_zdisj_sym : forall a b : Z * Z, zdisjoint a b -> zdisjoint b a.
Proof. unfold zdisjoint. intros a b H. lia. Qed.

Lemma upB_pairwise_perm : forall {X : Type} (R : X -> X -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros X R Hsym l l' HP. induction HP as [| x l l' HP IH | x y l | l l' l'' H1 IH1 H2 IH2]; intros H.
- exact I.
- cbn [pairwise] in H |- *. destruct H as [HF H]. split; [|exact (IH H)].
  rewrite Forall_forall in HF |- *. intros z Hz. apply HF. exact (Permutation_in z (Permutation_sym HP) Hz).
- cbn [pairwise] in H |- *. destruct H as [HFy [HFx H]]. rewrite Forall_cons_iff in HFy.
  destruct HFy as [Hyx HFy].
  split; [apply Forall_cons; [apply Hsym; exact Hyx | exact HFx]|]. split; [exact HFy | exact H].
- exact (IH2 (IH1 H)).
Qed.

Lemma upB_pairwise_last : forall {X : Type} (R : X -> X -> Prop) (l : list X) z w,
  pairwise R (l ++ [z]) -> In w l -> R w z.
Proof.
intros X R l z w. induction l as [|h t IH]; intros H Hw; [destruct Hw|].
cbn [app pairwise] in H. destruct H as [HF H]. destruct Hw as [<- | Hw].
- rewrite Forall_forall in HF. apply HF. apply in_or_app. right. left. reflexivity.
- exact (IH H Hw).
Qed.

(* A block listed before the last one of a block list the state's blocks are a permutation of is disjoint
   from the last one (AR's pairwise disjointness, al_blocks). *)
Lemma upB_disj : forall ly S (W : world segs) mem md (l : list (Z * Z)) x y,
  AR segs B ly S W mem md -> Permutation (ablocks B ly S) (l ++ [x]) -> In y l ->
  zdisjoint (fst y, req_size (snd y)) (fst x, req_size (snd x)).
Proof.
intros ly S W mem md l [b n] y HAR HP Hy.
assert (Hx : In (b, n) (ablocks B ly S)).
{ apply (Permutation_in (b, n) (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hx) as (_ & _ & _ & _ & _ & Hpw & _).
pose proof (upB_pairwise_perm zdisjoint upB_zdisj_sym _ _
  (Permutation_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) HP) Hpw) as H2.
rewrite map_app in H2. cbn [map] in H2.
exact (upB_pairwise_last zdisjoint _ _ _ H2 (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l y Hy)).
Qed.

(* Every byte up_mem reads lies in range, outside the stack window of a call made at sp = d_sp1, and outside
   the buffer of malloc #3. *)
Lemma upB_touch : forall (cx : dctx) (res upb : Z) ly' S' (W : world segs) mem' md' k,
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' W mem' md' k ->
  up_geom cx -> frames S' = [(DEC_FCLASS, d_fpos cx)] -> up_base cx ->
  (0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B ly' S')) ->
  Permutation (ablocks B ly' S') (up_bl1 cx res upb) ->
  forall a, up_touch cx res a ->
    0 <= a < 2 ^ 64 /\ ~ (d_sp1 cx - ESTACK <= a < d_sp1 cx) /\ ~ (upb <= a < upb + up_sz cx).
Proof.
intros cx res upb ly' S' W mem' md' k HJ HGEOM Hfrms HBASE Hinp HPERM a Ha.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
unfold DEC_LLVMF_STK in Hslo.
pose proof HGEOM as (Hg1 & Hg2 & Hg3 & Hg4).
destruct (upB_base cx HBASE) as (Hn & Hnlen & Hpin).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _].
pose proof (up_sz_bounds cx) as HSZ.
assert (Hreq : req_size (up_sz cx) = up_sz cx) by (unfold req_size; destruct (Z.eqb_spec (up_sz cx) 0); lia).
assert (Hinupb : In (upb, up_sz cx) (ablocks B ly' S')).
{ apply (Permutation_in _ (Permutation_sym HPERM)). unfold up_bl1. apply in_or_app; right; left; reflexivity. }
assert (Hinres : In (res, up_len cx) (ablocks B ly' S')).
{ apply (Permutation_in _ (Permutation_sym HPERM)). unfold up_bl1, up_bl0.
  apply in_or_app; left; apply in_or_app; right; left; reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinupb) as (_ & _ & Hbceil & Hbapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinres) as (_ & Hr4096 & Hrceil & _).
rewrite Hreq in Hbceil, Hbapp.
assert (Hreql : up_len cx <= req_size (up_len cx)) by (unfold req_size; destruct (Z.eqb_spec (up_len cx) 0); lia).
pose proof (upB_disj ly' S' W mem' md' (up_bl0 cx res) (upb, up_sz cx) (res, up_len cx) HAR HPERM
  ltac:(unfold up_bl0; apply in_or_app; right; left; reflexivity)) as HRd.
unfold zdisjoint in HRd. cbn [fst snd] in HRd. rewrite Hreq in HRd.
assert (HFin : In (DEC_FCLASS, d_fpos cx) (frames S')) by (rewrite Hfrms; left; reflexivity).
pose proof (frames_bounds segs B LAWS _ _ _ _ _ _ _ HAR HFin) as (_ & HF2 & _).
pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR Hinupb HFin) as HFd.
assert (HdF : frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _). rewrite HlyF. reflexivity. }
assert (H64 : fs_frame_bytes DEC_FCLASS = 64) by reflexivity.
rewrite HdF, H64 in HF2. rewrite HdF, H64, Hreq in HFd.
unfold zdisjoint in HFd. cbn [fst snd] in HFd.
unfold ESTACK. unfold up_touch in Ha.
destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]].
- lia.
- lia.
- lia.
- unfold d_SH, shadow_addr in Ha.
  assert (Hq1 : 0 <= d_F cx / 8) by (apply Z.div_pos; lia).
  assert (Hq2 : 8 * (d_F cx / 8) <= d_F cx) by (apply Z.mul_div_le; lia).
  set (q := d_F cx / 8) in *.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. unfold SHADOW_OFF in Ha.
  destruct Hbapp as [Hb1 [Hb2 | [Hb2 Hb3]]]; lia.
- assert (Hn0 : 0 < d_n cx) by lia.
  pose proof (Hinp Hn0) as Hpin0.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin0) as (_ & Hp4096 & Hpceil & _).
  pose proof (upB_disj ly' S' W mem' md' (up_bl0 cx res) (upb, up_sz cx) (d_p cx, d_n cx) HAR HPERM
    ltac:(unfold up_bl0; apply in_or_app; left; exact (Hpin Hn0))) as HPd.
  unfold zdisjoint in HPd. cbn [fst snd] in HPd. rewrite Hreq in HPd.
  assert (Hreqn : req_size (d_n cx) = d_n cx) by (unfold req_size; destruct (Z.eqb_spec (d_n cx) 0); lia).
  rewrite Hreqn in Hpceil, HPd. lia.
- lia.
Qed.

Lemma upB_upok0 : forall raw out (bs : list byte), (raw = 0 \/ out = 0) ->
  forall len, UDe.up_ok raw out len bs = false.
Proof.
intros raw out bs [-> | ->] len; unfold UDe.up_ok; [reflexivity|].
destruct (negb (raw =? 0)); reflexivity.
Qed.

Lemma upB_gz : forall (R : bvmap 5 word) (n : Z) (r : bv 5), bv_unsigned r = n ->
  YK11.getr R (Z_to_bv 5 n) = YK11.getr R r.
Proof. intros R n r H. subst n. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma upB_ap : forall (R1 R2 : bvmap 5 word) (r : bv 5), aregs_preserved R1 R2 -> acallee_saved (bv_unsigned r) ->
  YK11.getr R2 r = YK11.getr R1 r.
Proof. intros R1 R2 r HP Hc. pose proof (HP _ Hc) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.

(* The callee-saved registers the segment carries, all but s9 (which the segment sets at +0x7e8). *)
Lemma upB_ap_cs : forall (R1 R2 : bvmap 5 word), aregs_preserved R1 R2 ->
  forall r : bv 5, In r ([2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv : list (bv 5)) ->
  YK11.getr R2 r = YK11.getr R1 r.
Proof.
intros R1 R2 HP r Hr. apply (upB_ap R1 R2 r HP). cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [upB_cs |]). destruct Hr.
Qed.

Lemma upB_agree : forall regs : bvmap 5 word, env_agree 32 (Ereg regs []) (Eimg (Ereg regs [])).
Proof. intros regs. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* Reading a register of a symbolic state re-seated by up_seat. *)
Lemma upB_reg_off : forall (H : word -> bool) (regs : bvmap 5 word) ss ms (r r' : bv 5) (n : nat),
  st_ok segs (Eimg (Ereg regs [])) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 ->
  (n < A_TEXT)%nat -> Z.of_nat n = bv_unsigned r' -> YK11.getr (ms_regs ms) r = YK11.getr regs r'.
Proof.
intros H regs ss ms r r' n HS Hs Hn Hr.
transitivity (sv_denot (Eimg (Ereg regs [])) (sr_get (ss_regs ss) r)); [exact (st_ok_restrict_reg segs H _ ss ms r HS)|].
rewrite Hs. cbn [sv_denot].
rewrite (Eimg_low _ n Hn), (ew_Ereg_nat regs [] n r' Hr), Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma upB_reg_lit : forall (H : word -> bool) E ss ms (r : bv 5) (z : Z),
  st_ok segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> YK11.getr (ms_regs ms) r = Z_to_bv 64 z.
Proof.
intros H E ss ms r z HS Hs.
transitivity (sv_denot E (sr_get (ss_regs ss) r)); [exact (st_ok_restrict_reg segs H E ss ms r HS)|].
rewrite Hs. reflexivity.
Qed.

Lemma upB_reg_ra : forall (H : word -> bool) (regs : bvmap 5 word) ss ms (k : Z),
  st_ok segs (Eimg (Ereg regs [])) ss (restrict H ms) -> sr_get (ss_regs ss) 1%bv = SOff A_TEXT k ->
  YK11.getr (ms_regs ms) 1 = Z_to_bv 64 (DEC_A_LLVMF + k).
Proof.
intros H regs ss ms k HS Hs.
transitivity (sv_denot (Eimg (Ereg regs [])) (sr_get (ss_regs ss) 1%bv));
  [exact (st_ok_restrict_reg segs H _ ss ms 1%bv HS)|].
rewrite Hs. rewrite (codeptr_val _ k (Eimg_env _)).
first [rewrite up_base_eq; reflexivity | f_equal; f_equal; exact up_base_eq].
Qed.

Lemma upB_ret : forall k, 0 <= k < 2 ^ 40 -> k mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 (DEC_A_LLVMF + k)).
Proof. intros k H1 H2. rewrite <- up_base_eq. exact (ret_ok_codeptr_v k H1 H2). Qed.

Lemma upB_kept : forall (H : word -> bool) (regs : bvmap 5 word) ss ms (l : list (bv 5)),
  st_ok segs (Eimg (Ereg regs [])) ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) l = true ->
  forall r, In r l -> YK11.getr (ms_regs ms) r = YK11.getr regs r.
Proof. intros H regs ss ms l HS Hf r Hr. exact (regs_kept_of_st_ok segs _ _ _ regs [] l HS (upB_agree regs) Hf r Hr). Qed.

Local Ltac upB_off HS r r' n X :=
  pose proof (upB_reg_off _ _ _ _ r r' n HS) as X;
  specialize (X ltac:(vm_compute; reflexivity) ltac:(unfold A_TEXT; lia) eq_refl).
Local Ltac upB_lit HS r z X :=
  pose proof (upB_reg_lit _ _ _ _ r z HS) as X; specialize (X ltac:(vm_compute; reflexivity)).
Local Ltac upB_ra HS k X :=
  pose proof (upB_reg_ra _ _ _ _ k HS) as X; specialize (X ltac:(vm_compute; reflexivity)).
Local Ltac upB_keep HS l X :=
  pose proof (upB_kept _ _ _ _ l HS) as X; specialize (X ltac:(vm_compute; reflexivity)).

(* A run that stores nothing leaves the memory as it was (its only region is the read-only constant). *)
Lemma upB_frame : forall E rs (m m' : word -> option byte), rs = [up_obj9] -> frame_of E rs m m' ->
  forall x, m' x = m x.
Proof.
intros E rs m m' -> HF x. apply HF. intros (r & Hin & Hr). destruct Hin as [<- | []].
cbn [up_obj9 YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

Lemma upB_aview_ext : forall (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, aview segs H m' a = aview segs H m a.
Proof. intros H m m' E a. unfold aview, mbyte, mrestrict. cbv beta. rewrite E. reflexivity. Qed.

Lemma upB_pres_ext : forall (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, apresent H m a -> apresent H m' a.
Proof. intros H m m' E a (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite E. exact Hb. Qed.

(* sp = d_sp1 is 16-aligned, and so is its offset from the entry sp (lia does not see through mod). *)
Lemma upB_mod16 : forall cx : dctx, up_geom cx -> d_sp0 cx mod 16 = 0 ->
  d_sp1 cx mod 16 = 0 /\ (d_sp1 cx - d_sp0 cx) mod 16 = 0.
Proof.
intros cx (Hg1 & Hg2 & _) H0.
assert (A : d_sp1 cx mod 16 = 0).
{ pose proof (Z.div_mod (d_sp1 cx) 32 ltac:(lia)) as D. rewrite Hg2, Z.add_0_r in D. rewrite D.
  replace (32 * (d_sp1 cx / 32)) with ((2 * (d_sp1 cx / 32)) * 16) by ring. apply Z.mod_mul. lia. }
split; [exact A|]. rewrite Zminus_mod, A, H0. reflexivity.
Qed.

(* __asan_memset (buffer, 0xa5, size) at +0x7d4, by the intrinsic rule (YCbq.v aj_intrin_at): the buffer is a
   block of the current state that the entry state does not have (in_tmp_block), below the stack. *)
Lemma upB_memset : forall (cx : dctx) ly' S' (W : world segs) (regsT : bvmap 5 word) memT mdc (k upb : Z),
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' W memT mdc k ->
  up_geom cx ->
  In (upb, up_sz cx) (ablocks B ly' S') -> ~ In (upb, up_sz cx) (ablocks B (d_ly cx) (d_S cx)) ->
  YK11.getr regsT 10 = w64 upb -> YK11.getr regsT 11 = w64 165 -> YK11.getr regsT 12 = w64 (up_sz cx) ->
  spZ regsT = d_sp1 cx -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK0s.ret_ok (YK11.getr regsT 1) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (decode_sigma DS___asan_memset)) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (YK11.getr regsT 1) mem2 (seg_rom segs)) md2 /\
       @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
         (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       dec_a_filled W mem2 upb (up_sz cx) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (upb <= a < upb + up_sz cx) -> ~ (d_sp1 cx - ESTACK <= a < d_sp1 cx) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros cx ly' S' W regsT memT mdc k upb HJ HGEOM Hin Hnin H10 H11 H12 Hsp Hgp Htp Hra.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
unfold DEC_LLVMF_STK in Hslo.
pose proof HGEOM as (Hg1 & Hg2 & Hg3 & Hg4).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _].
pose proof (up_sz_bounds cx) as HSZ.
destruct (al_blocks _ _ LAWS _ _ _ _ _ upb (up_sz cx) HAR Hin) as (_ & Hb4096 & Hbceil & _).
assert (Hreq : req_size (up_sz cx) = up_sz cx) by (unfold req_size; destruct (Z.eqb_spec (up_sz cx) 0); lia).
rewrite Hreq in Hbceil.
eapply SRr_mono.
{ eapply (aj_intrin_at segs B LAWS DecodeImg.decode_segs_low OSet (decode_sigma DS___asan_memset) (AMS fx)
    W regsT memT DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly' S' mdc k upb 165 (up_sz cx) (d_sp1 cx - d_sp0 cx) (YK11.getr regsT 1)
    HJ H10 H11 H12).
  - lia.
  - lia.
  - lia.
  - rewrite Hsp. lia.
  - exact (proj2 (upB_mod16 cx HGEOM Hsp0al)).
  - lia.
  - unfold ESTACK, DEC_LLVMF_STK. lia.
  - exact Hgp.
  - exact Htp.
  - reflexivity.
  - exact Hra.
  - intros a Ha. split.
    + right; right; left. exists upb, (up_sz cx). split; [exact Hin|]. split; [exact Hnin|]. rewrite Hreq. lia.
    + unfold ESTACK. lia.
  - eapply (amem_range_of_block segs B LAWS _ _ _ _ _ _ _ _ _ HAR Hin); rewrite ?Hreq; lia.
  - eapply (range_addressable_of_block segs B LAWS _ _ _ _ _ _ _ _ _ HAR Hin); rewrite ?Hreq; lia.
  - intros Hn0. eapply (shadow_hull_vis_of_block segs B LAWS _ _ _ _ _ _ _ _ _ HAR Hin); rewrite ?Hreq; lia.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & _ & Hfill & Hkeep & Hgr).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
split; [intros i Hi; rewrite (Hfill i Hi); reflexivity|].
split; [| exact Hgr].
intros a Ha Hb Hw. apply Hkeep; [exact Ha | exact Hb |]. intros Hw'. apply Hw. lia.
Qed.

(* reac_upstream_decode with raw = NULL or out = NULL (+0x7e4, +0x7f8), by the leaf contract LUP through the
   shared bridge (LLVMFuzzerTestOneInput_leafb.v dec_leafb_journal): up_ok is false by its first two conjuncts,
   so the leaf returns -1, writes nothing (WR = []), and every premise guarded by `raw <> 0 -> out <> 0 -> ..`
   or `up_ok .. = true -> ..` is vacuous. *)
Lemma upB_refuse : forall (cx : dctx) ly' S' (W : world segs) (regsT : bvmap 5 word) memT mdc (k raw out len : Z),
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' W memT mdc k ->
  up_geom cx -> (raw = 0 \/ out = 0) ->
  0 <= raw < 2 ^ 64 -> 0 <= out < 2 ^ 64 -> 0 <= len < 2 ^ 32 ->
  YK11.getr regsT 10 = w64 raw -> YK11.getr regsT 11 = w64 len -> YK11.getr regsT 12 = w64 out ->
  spZ regsT = d_sp1 cx -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK0s.ret_ok (YK11.getr regsT 1) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (decode_sigma DS_reac_upstream_decode)) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (YK11.getr regsT 1) mem2 (seg_rom segs)) md2 /\
       @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
         (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ YK11.getr regs2 10 = w64 (-1) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - ESTACK <= a < d_sp1 cx) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros cx ly' S' W regsT memT mdc k raw out len HJ HGEOM Hz Hraw Hout Hlen H10 H11 H12 Hsp Hgp Htp Hra.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
unfold DEC_LLVMF_STK in Hslo.
pose proof HGEOM as (Hg1 & Hg2 & Hg3 & Hg4).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _].
assert (Hpc : decode_sigma DS_reac_upstream_decode = UDe.REAC_UPSTREAM_DECODE) by (vm_compute; reflexivity).
rewrite Hpc.
assert (SPZ : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = spZ regsT)
  by (rewrite (upB_gz regsT 2 2%bv eq_refl); reflexivity).
assert (G10 : YK11.getr regsT (Z_to_bv 5 10) = Z_to_bv 64 raw)
  by (rewrite (upB_gz regsT 10 10%bv eq_refl); exact H10).
assert (G12 : YK11.getr regsT (Z_to_bv 5 12) = Z_to_bv 64 out)
  by (rewrite (upB_gz regsT 12 12%bv eq_refl); exact H12).
assert (U11 : bv_unsigned (YK11.getr regsT (Z_to_bv 5 11)) = len)
  by (rewrite (upB_gz regsT 11 11%bv eq_refl), H11; unfold w64; apply unsigned_lit_small; lia).
assert (HPW : forall a, spZ regsT - ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply Hpres; rewrite Hsp in Ha; unfold ESTACK in Ha; unfold DEC_LLVMF_STK; lia).
destruct (dec_leafb_stack W regsT memT HPW ltac:(rewrite Hsp; lia) ltac:(rewrite Hsp; lia)
  ltac:(rewrite Hsp; exact (proj1 (upB_mod16 cx HGEOM Hsp0al))))
  as (S1 & S2 & S3 & S4 & S5).
eapply SRr_mono.
{ eapply (LLVMFuzzerTestOneInput_leafb.dec_leafb_journal (fx := fx) (SK := dec_A_sink_head) B LAWS W regsT memT
    DEC_LLVMF_STK (d_sp0 cx) []
    (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' mdc k
    (d_sp1 cx - d_sp0 cx) UDe.REAC_UPSTREAM_DECODE (Some (-1)) [] _ HJ).
  - rewrite Hsp. lia.
  - exact (proj2 (upB_mod16 cx HGEOM Hsp0al)).
  - lia.
  - unfold ESTACK, DEC_LLVMF_STK. lia.
  - exact Hra.
  - exact Hgp.
  - exact Htp.
  - intros a Ha. first [inversion Ha | (apply Exists_nil in Ha; destruct Ha)].
  - intros HPRE.
    pose proof (LUP fx) as HL. unfold dec_leaf_wr_at, LUpDecode.dec_reac_upstream_decode_cg in HL.
    cbv beta zeta in HL.
    specialize (HL ly' S' W regsT memT mdc [] raw out (spZ regsT - ESTACK) HPRE).
    rewrite (upB_upok0 raw out [] Hz) in HL. cbv beta iota in HL.
    apply HL; clear HL.
    + exact G10.
    + exact G12.
    + exact Hraw.
    + exact Hout.
    + rewrite U11. lia.
    + exact (dec_leafb_magic ly' S' W memT mdc CELLS HAR).
    + intros Hr Ho. destruct Hz as [Hz | Hz]; contradiction.
    + intros Hf. discriminate Hf.
    + rewrite SPZ. exact S1.
    + rewrite SPZ. unfold ESTACK, UDe.REAC_UPSTREAM_DECODE_D. lia.
    + intros Hr Ho. destruct Hz as [Hz | Hz]; contradiction.
    + intros Hf. discriminate Hf.
    + exact S5.
    + rewrite SPZ. exact S2.
    + rewrite SPZ. exact S3.
    + exact (dec_leafb_cells ly' S' W memT mdc LAWS CELLS HAR).
    + exact S4.
    + intros Hr Ho. destruct Hz as [Hz | Hz]; contradiction.
    + intros Hf. discriminate Hf.
    + rewrite SPZ. apply (LLVMFuzzerTestOneInput_leafb.dec_leafb_rng_vis W memT);
        [rewrite Hsp; unfold UDe.REAC_UPSTREAM_DECODE_D; lia | rewrite Hsp; unfold UDe.REAC_UPSTREAM_DECODE_D; lia |].
      intros a Ha. apply HPW. unfold ESTACK, UDe.REAC_UPSTREAM_DECODE_D in *. lia.
    + apply (LLVMFuzzerTestOneInput_leafb.dec_leafb_rng W);
        [unfold UDe.DIV36_MAGIC_AT; lia | unfold UDe.DIV36_MAGIC_AT; lia |].
      intros a Ha. replace a with (UDe.DIV36_MAGIC_AT + (a - UDe.DIV36_MAGIC_AT)) by lia.
      apply (LLVMFuzzerTestOneInput_leafb.dec_leafb_covers_visible (w_H W) UDe.DIV36_MAGIC_AT 8);
        [exact (w_Hoff W) | vm_compute; reflexivity | lia | unfold UDe.DIV36_MAGIC_AT; lia].
    + exact (proj1 (LLVMFuzzerTestOneInput_leafb.dec_leafb_rng_cells W)).
    + exact (proj2 (LLVMFuzzerTestOneInput_leafb.dec_leafb_rng_cells W)).
    + intros Hr Ho. destruct Hz as [Hz | Hz]; contradiction.
    + intros Hr Ho. destruct Hz as [Hz | Hz]; contradiction.
    + intros Hf. discriminate Hf.
    + intros Hf. discriminate Hf.
    + intros x Hx. first [inversion Hx | (apply Exists_nil in Hx; destruct Hx)]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hres & Heff & Hgr & _).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact (Hres (-1) eq_refl)|].
split; [| exact Hgr].
intros a Ha Hw. apply Heff; [exact Ha | rewrite Hsp; exact Hw |].
intros Hx. first [inversion Hx | (apply Exists_nil in Hx; destruct Hx)].
Qed.

(* The stage: the NULL check refuted, run to the memset, the memset, run to the first refusing decode, the
   call, run to the second, the call. Each run is entered from a fresh state (up_seat). *)
Lemma up_B : up_B_stmt.
Proof.
unfold up_B_stmt.
intros cx res mode nch ns W0 c0 HBASE HROMcx HGEOM HPOST.
destruct HPOST as (ly0 & S0 & regs0 & mem0 & md0 & upb & -> & HMID & Ha0).
destruct HMID as (HRUN & Hupb4096 & Hinupb & Hnotupb & HMLE & HMOK & Hr22 & Hr24).
destruct HRUN as (HJ & Hfrms & Hr8 & Hr9 & Hsp & Hgp & Htp & Hinp & HPERM & HFR & Hr18 & Hr20 & Hr26 & HMEM).
destruct (upB_base cx HBASE) as (Hn & Hnlen & Hpin).
pose proof (up_sz_bounds cx) as HSZ.
pose proof HJ as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
unfold DEC_LLVMF_STK in Hslo.
pose proof HGEOM as (Hg1 & Hg2 & Hg3 & Hg4).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _].
destruct (al_blocks _ _ LAWS _ _ _ _ _ upb (up_sz cx) HAR0 Hinupb) as (_ & _ & Hbceil & _).
assert (Hreq : req_size (up_sz cx) = up_sz cx) by (unfold req_size; destruct (Z.eqb_spec (up_sz cx) 0); lia).
rewrite Hreq in Hbceil.
assert (Hinres : In (res, up_len cx) (ablocks B ly0 S0)).
{ apply (Permutation_in _ (Permutation_sym HPERM)). unfold up_bl1, up_bl0.
  apply in_or_app; left; apply in_or_app; right; left; reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (up_len cx) HAR0 Hinres) as (_ & Hres4096 & Hrceil & _).
assert (Hreql : up_len cx <= req_size (up_len cx)) by (unfold req_size; destruct (Z.eqb_spec (up_len cx) 0); lia).
assert (Hlen : 0 <= up_len cx < 2 ^ 32) by (unfold up_len, dec_a_len; lia).
pose proof (upB_touch cx res upb ly0 S0 W0 mem0 md0 dec_ev_86c HJ HGEOM Hfrms HBASE Hinp HPERM) as HT.
(* +0x7c4: the NULL check; then +0x7c8 .. +0x7d4 up to the call of __asan_memset. *)
pose proof (HROM_KEPT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROMcx) as HROM0.
pose proof (up_seat UP_MALLOC_RA W0 regs0 mem0 (up_obj9_val _ _ _ _ _ CELLS (proj1 HJ)) Hr18) as HS.
assert (HEI : img_env pa_val A_LIM (Eimg (Ereg regs0 (@nil word)))) by apply Eimg_env.
assert (SHOK : sh_ok pa_segs (SOff 18 0) (@nil shent) (Eimg (Ereg regs0 (@nil word))) (mrestrict (w_H W0) mem0))
  by apply Forall_nil.
unfold cfg_at.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_eq_U, U_lit in Hc by lia.
  assert (E10 : ew (Eimg (Ereg regs0 [])) 10 = Z_to_bv 64 upb).
  { rewrite (Eimg_low _ 10 ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs0 [] 10 10%bv eq_refl). exact Ha0. }
  rewrite (U_atom _ 10 upb E10) in Hc by lia. apply Z.eqb_eq in Hc. lia. }
paj_run_tok RUN HS HJ SHOK Bspan; [ up_awr | ].
rename ms into ms1, HJ into HJ1.
pose proof (fun Hr => upB_frame _ _ _ _ Hr HF) as E1. specialize (E1 ltac:(vm_compute; reflexivity)). clear HF.
pmkst HS.
upB_off HS (10%bv : bv 5) (10%bv : bv 5) 10%nat Q10. rewrite Ha0 in Q10.
upB_lit HS (11%bv : bv 5) 165 Q11.
upB_off HS (12%bv : bv 5) (24%bv : bv 5) 24%nat Q12. rewrite Hr24 in Q12.
upB_off HS (2%bv : bv 5) (2%bv : bv 5) 2%nat Q2.
upB_off HS (3%bv : bv 5) (3%bv : bv 5) 3%nat Q3. rewrite Hgp in Q3.
upB_off HS (4%bv : bv 5) (4%bv : bv 5) 4%nat Q4. rewrite Htp in Q4.
upB_off HS (23%bv : bv 5) (10%bv : bv 5) 10%nat Q23. rewrite Ha0 in Q23.
upB_ra HS 2008 Q1.
upB_keep HS ([2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 26; 27]%bv : list (bv 5)) K1.
assert (Qsp : spZ (ms_regs ms1) = d_sp1 cx) by (unfold spZ; rewrite Q2; exact Hsp).
(* +0x7d4: __asan_memset (upb, 0xa5, up_sz). *)
eapply SRr_bind.
{ apply (upB_memset cx ly0 S0 W0 (ms_regs ms1) (ms_mem ms1) _ dec_ev_86c upb HJ1 HGEOM Hinupb Hnotupb
    Q10 Q11 Q12 Qsp Q3 Q4 ltac:(rewrite Q1; apply upB_ret; [lia | reflexivity])). }
cbv beta. intros W2 c2 _ (-> & R2 & M2 & MD2 & -> & HJ2 & HP2 & F2 & KM2 & P2).
rewrite Q1.
pose proof (upB_ap_cs _ _ HP2) as K2.
clear HS SHOK HFr HG. try clear HEI0. clear HEI.
(* +0x7d8 .. +0x7e4: up to the first refusing call (raw = NULL). *)
assert (R2_18 : YK11.getr R2 18 = w64 SHADOW_OFF) by (rewrite K2, K1 by upB_in; exact Hr18).
pose proof (up_seat UP_MEMSET_RA W0 R2 M2 (up_obj9_val _ _ _ _ _ CELLS (proj1 HJ2)) R2_18) as HS.
assert (HEI : img_env pa_val A_LIM (Eimg (Ereg R2 (@nil word)))) by apply Eimg_env.
assert (SHOK : sh_ok pa_segs (SOff 18 0) (@nil shent) (Eimg (Ereg R2 (@nil word))) (mrestrict (w_H W0) M2))
  by apply Forall_nil.
paj_run_tok RUN HS HJ2 SHOK Bspan; [ up_awr | ].
rename ms into ms2, HJ2 into HJ3.
pose proof (fun Hr => upB_frame _ _ _ _ Hr HF) as E3. specialize (E3 ltac:(vm_compute; reflexivity)). clear HF.
pmkst HS.
upB_lit HS (10%bv : bv 5) 0 T10.
upB_off HS (11%bv : bv 5) (26%bv : bv 5) 26%nat T11. rewrite K2, K1, Hr26 in T11 by upB_in.
upB_off HS (12%bv : bv 5) (23%bv : bv 5) 23%nat T12. rewrite K2, Q23 in T12 by upB_in.
upB_off HS (2%bv : bv 5) (2%bv : bv 5) 2%nat T2.
upB_off HS (3%bv : bv 5) (3%bv : bv 5) 3%nat T3. rewrite K2, Q3 in T3 by upB_in.
upB_off HS (4%bv : bv 5) (4%bv : bv 5) 4%nat T4. rewrite K2, Q4 in T4 by upB_in.
upB_ra HS 2024 T1.
upB_keep HS ([2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv : list (bv 5)) K3.
assert (Tsp : spZ (ms_regs ms2) = d_sp1 cx) by (unfold spZ; rewrite T2, K2, Q2 by upB_in; exact Hsp).
(* +0x7e4: reac_upstream_decode (NULL, len, upb). *)
eapply SRr_bind.
{ apply (upB_refuse cx ly0 S0 W0 (ms_regs ms2) (ms_mem ms2) _ dec_ev_86c 0 upb (up_len cx) HJ3 HGEOM
    (or_introl eq_refl) ltac:(lia) ltac:(lia) Hlen T10 T11 T12 Tsp T3 T4
    ltac:(rewrite T1; apply upB_ret; [lia | reflexivity])). }
cbv beta. intros W4 c4 _ (-> & R4 & M4 & MD4 & -> & HJ4 & HP4 & Hd4 & KM4 & P4).
rewrite T1.
pose proof (upB_ap_cs _ _ HP4) as K4.
clear HS SHOK HFr HG. try clear HEI0. clear HEI.
(* +0x7e8 .. +0x7f8: up to the second refusing call (out = NULL). *)
assert (R4_18 : YK11.getr R4 18 = w64 SHADOW_OFF) by (rewrite K4, K3, K2, K1 by upB_in; exact Hr18).
pose proof (up_seat UP_DEC1_RA W0 R4 M4 (up_obj9_val _ _ _ _ _ CELLS (proj1 HJ4)) R4_18) as HS.
assert (HEI : img_env pa_val A_LIM (Eimg (Ereg R4 (@nil word)))) by apply Eimg_env.
assert (SHOK : sh_ok pa_segs (SOff 18 0) (@nil shent) (Eimg (Ereg R4 (@nil word))) (mrestrict (w_H W0) M4))
  by apply Forall_nil.
paj_run_tok RUN HS HJ4 SHOK Bspan; [ up_awr | ].
rename ms into ms3, HJ4 into HJ5.
pose proof (fun Hr => upB_frame _ _ _ _ Hr HF) as E5. specialize (E5 ltac:(vm_compute; reflexivity)). clear HF.
pmkst HS.
upB_off HS (10%bv : bv 5) (20%bv : bv 5) 20%nat V10. rewrite K4, K3, K2, K1, Hr20 in V10 by upB_in.
upB_off HS (11%bv : bv 5) (26%bv : bv 5) 26%nat V11. rewrite K4, K3, K2, K1, Hr26 in V11 by upB_in.
upB_lit HS (12%bv : bv 5) 0 V12.
upB_off HS (2%bv : bv 5) (2%bv : bv 5) 2%nat V2.
upB_off HS (3%bv : bv 5) (3%bv : bv 5) 3%nat V3. rewrite K4, K3, K2, Q3 in V3 by upB_in.
upB_off HS (4%bv : bv 5) (4%bv : bv 5) 4%nat V4. rewrite K4, K3, K2, Q4 in V4 by upB_in.
upB_off HS (25%bv : bv 5) (10%bv : bv 5) 10%nat V25. rewrite Hd4 in V25.
upB_ra HS 2044 V1.
upB_keep HS ([2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv : list (bv 5)) K5.
assert (Vsp : spZ (ms_regs ms3) = d_sp1 cx) by (unfold spZ; rewrite V2, K4, K3, K2, Q2 by upB_in; exact Hsp).
(* +0x7f8: reac_upstream_decode (res, len, NULL). *)
eapply SRr_bind.
{ apply (upB_refuse cx ly0 S0 W0 (ms_regs ms3) (ms_mem ms3) _ dec_ev_86c res 0 (up_len cx) HJ5 HGEOM
    (or_intror eq_refl) ltac:(lia) ltac:(lia) Hlen V10 V11 V12 Vsp V3 V4
    ltac:(rewrite V1; apply upB_ret; [lia | reflexivity])). }
cbv beta. intros W6 c6 _ (-> & R6 & M6 & MD6 & -> & HJ6 & HP6 & Hd6 & KM6 & P6).
rewrite V1.
pose proof (upB_ap_cs _ _ HP6) as K6.
(* +0x7fc. *)
apply SRr_ret.
assert (KT : forall r : bv 5, In r ([2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv : list (bv 5)) ->
  YK11.getr R6 r = YK11.getr (ms_regs ms1) r)
  by (intros r Hr; rewrite (K6 r Hr), (K5 r Hr), (K4 r Hr), (K3 r Hr), (K2 r Hr); reflexivity).
assert (HV : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - ESTACK <= a < d_sp1 cx) ->
  aview segs (w_H W0) M6 a = aview segs (w_H W0) M2 a).
{ intros a Ha Hw. rewrite (KM6 a Ha Hw), (upB_aview_ext _ _ _ E5 a), (KM4 a Ha Hw), (upB_aview_ext _ _ _ E3 a).
  reflexivity. }
assert (HTK : forall a, up_touch cx res a -> aview segs (w_H W0) M6 a = aview segs (w_H W0) mem0 a).
{ intros a Ha. destruct (HT a Ha) as (Hr & Hw & Hb). rewrite (HV a Hr Hw), (KM2 a Hr Hb Hw).
  exact (upB_aview_ext _ _ _ E1 a). }
assert (HPK : forall a, apresent (w_H W0) mem0 a -> apresent (w_H W0) M6 a).
{ intros a H. apply P6. apply (upB_pres_ext _ _ _ E5). apply P4. apply (upB_pres_ext _ _ _ E3). apply P2.
  exact (upB_pres_ext _ _ _ E1 a H). }
unfold up_post_7fc. exists ly0, S0, R6, M6, MD6, upb.
split; [unfold cfg_at; reflexivity|].
split.
{ unfold up_mid. split.
  { unfold up_run.
    split; [exact HJ6|]. split; [exact Hfrms|].
    split; [rewrite KT, K1 by upB_in; exact Hr8|].
    split; [rewrite KT, K1 by upB_in; exact Hr9|].
    split; [unfold spZ; rewrite KT, K1 by upB_in; exact Hsp|].
    split; [rewrite KT, K1 by upB_in; exact Hgp|].
    split; [rewrite KT, K1 by upB_in; exact Htp|].
    split; [exact Hinp|]. split; [exact HPERM|].
    split; [unfold dec_a_fr in HFR |- *; rewrite !KT, !K1 by upB_in; exact HFR|].
    split; [rewrite KT, K1 by upB_in; exact Hr18|].
    split; [rewrite KT, K1 by upB_in; exact Hr20|].
    split; [rewrite KT, K1 by upB_in; exact Hr26|].
    apply (up_mem_kept cx res mode nch ns W0 W0 mem0 M6 Hnlen HTK HPK); [|exact HMEM].
    intros HMo. apply (up_mode_kept cx ly0 S0 W0 mem0 md0 ly0 S0 W0 M6 MD6 mode nch ns HAR0 (proj1 HJ6)
                         HROM0 (HROM_KEPT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6 HROMcx)); [|exact HMo].
    intros a Ha. apply HTK. unfold up_touch. right; right; left. exact Ha. }
  split; [exact Hupb4096|]. split; [exact Hinupb|]. split; [exact Hnotupb|].
  split; [exact HMLE|]. split; [exact HMOK|].
  split; [rewrite KT, K1 by upB_in; exact Hr22|].
  rewrite KT, K1 by upB_in; exact Hr24. }
split; [rewrite KT by upB_in; exact Q23|].
split.
{ intros i Hi. rewrite (HV (upb + i)) by (unfold ESTACK; lia). exact (F2 i Hi). }
split; [rewrite (upB_ap _ _ 25%bv HP6) by upB_cs; exact V25|].
exact Hd6.
Qed.

(* ---------------------------------------------------------------- *)
(* Stage D: +0x858 .. +0x868, the last abort edge and the real call. *)
(* ---------------------------------------------------------------- *)

(* A symmetric pairwise relation survives a permutation of its list. *)
Lemma upD_perm_pairwise : forall {X : Type} (R : X -> X -> Prop) (l1 l2 : list X),
  (forall x y, R x y -> R y x) -> Permutation l1 l2 -> pairwise R l1 -> pairwise R l2.
Proof.
  intros X R l1 l2 Hsym HP. induction HP as [|x la lb HP IH|x y l|la lb lc HP1 IH1 HP2 IH2].
  - intros H; exact H.
  - cbn. intros [HF HPw]. split; [| exact (IH HPw)].
    apply Forall_forall. intros z Hz. rewrite Forall_forall in HF. apply HF.
    eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hz].
  - cbn. intros [HF [HF2 HPw]].
    pose proof (Forall_inv HF) as Hyx. pose proof (Forall_inv_tail HF) as HFl.
    split; [apply Forall_cons; [apply Hsym; exact Hyx | exact HF2] | split; [exact HFl | exact HPw]].
  - intros H. exact (IH2 (IH1 H)).
Qed.

(* Two blocks the walk names in two different parts of a permutation of ablocks are disjoint. *)
Lemma upD_blk_disj : forall ly S (W : world segs) mem md (l1 l2 : list (Z * Z)) (a b : Z * Z),
  AR segs B ly S W mem md ->
  Permutation (ablocks B ly S) (l1 ++ l2) -> In a l1 -> In b l2 ->
  zdisjoint (fst a, req_size (snd a)) (fst b, req_size (snd b)).
Proof.
  intros ly S W mem md l1 l2 a b HAR HPerm Ha Hb.
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hpw _].
  apply pairwise_app_l in Hpw as [Hpw _].
  pose proof (upD_perm_pairwise zdisjoint _ _ zdisjoint_sym
                (Permutation_map (fun x : Z * Z => (fst x, req_size (snd x))) HPerm) Hpw) as Hpw2.
  rewrite map_app in Hpw2.
  exact (pairwise_In zdisjoint _ _ _ _ _ eq_refl Hpw2
           (in_map (fun x : Z * Z => (fst x, req_size (snd x))) l1 a Ha)
           (in_map (fun x : Z * Z => (fst x, req_size (snd x))) l2 b Hb)).
Qed.

(* The leaf's post is a raw bytes_at; the walk's clauses are garr8 of the view. The bytes of a range whose
   every byte is present (a live block) read the same at mrd and at the view. *)
Lemma upD_garr8_of_bytes : forall (W : world segs) (m : word -> option byte) (p : Z) (bs : list byte),
  (forall i, 0 <= i < Z.of_nat (length bs) -> apresent (w_H W) m (p + i)) ->
  DMem.bytes_at segs m p bs ->
  garr8 segs (mrestrict (w_H W) m) p (map (fun b : byte => bv_unsigned b) bs).
Proof.
  intros W m p bs HP HB j Hj. rewrite length_map in Hj.
  assert (Hv : w_H W (Z_to_bv 64 (p + Z.of_nat j)) = false)
    by (exact (proj1 (HP (Z.of_nat j) ltac:(lia)))).
  assert (Hnth : nth j (map (fun b : byte => bv_unsigned b) bs) 0 = bv_unsigned (nth j bs (Z_to_bv 8 0))).
  { rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
    apply (map_nth (fun b : byte => bv_unsigned b)). }
  pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as HR.
  change (bv_modulus 8) with 256 in HR.
  split; [| rewrite Hnth; lia].
  intros kk Hk. assert (kk = 0%nat) as -> by lia. rewrite Nat2Z.inj_0, Z.add_0_r.
  rewrite <- (LLVMFuzzerTestOneInput_leafb.dec_leafb_mrd W m (p + Z.of_nat j) Hv).
  destruct HB as (_ & _ & HB). rewrite (HB j Hj).
  rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hj). rewrite Hnth. f_equal.
  symmetry. apply LLVMFuzzerTestOneInput_leafb.dec_leafb_le_byte1.
Qed.

(* What up_ok says about its own arguments. *)
Lemma upD_ok_facts : forall (raw out len : Z) (bs : list byte),
  CUp.up_ok raw out len bs = true -> raw <> 0 /\ out <> 0 /\ 0 <= CUp.up_nch len.
Proof.
  intros raw out len bs H. unfold CUp.up_ok in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H Hc]. apply andb_prop in H as [Ha Hb].
  apply negb_true_iff in Ha. apply Z.eqb_neq in Ha.
  apply negb_true_iff in Hb. apply Z.eqb_neq in Hb.
  apply Z.leb_le in Hc. split; [exact Ha | split; [exact Hb | exact Hc]].
Qed.

(* lia here runs with the euclidean division equations off (lib/A/Prog/YC4b.v:24), so a mod fact is proved
   by divisibility, never by lia. *)
Lemma upD_mod16_of_mod32 : forall x : Z, x mod 32 = 0 -> x mod 16 = 0.
Proof.
  intros x H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia].
  destruct H as [k Hk]. exists (2 * k). lia.
Qed.

(* The two fields of dec_lib_pre_x this stage reads, taken by their shape, never by position
   (LLVMFuzzerTestOneInput_cg.v:102-116: the payload disjunct and n = length pl). *)
Lemma upD_base_facts : forall cx : dctx,
  up_base cx ->
  ((d_n cx = 0 /\ d_p cx = A_EMPTY) \/
   (0 < d_n cx < 2 ^ 26 /\ In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx)))) /\
  d_n cx = Z.of_nat (length (d_pl cx)).
Proof.
  intros cx HB. unfold dec_a_base, dec_lib_pre_x in HB.
  repeat match goal with H : _ /\ _ |- _ => let h := fresh "HBf" in destruct H as [h H] end.
  split.
  - match goal with
    | H : (d_n cx = 0 /\ d_p cx = A_EMPTY) \/ _ |- _ => exact H
    end.
  - match goal with
    | H : d_n cx = Z.of_nat (length (d_pl cx)) |- _ => exact H
    end.
Qed.

Lemma up_D : up_D_stmt.
Proof.
unfold up_D_stmt.
intros cx res mode nch ns W' c' HFZ HBASE HROMcx HGEO HPOST.
destruct HPOST as (ly' & S' & regs' & mem' & md' & upb & -> & HMID & H23 & HFILL & H11).
(* up_mid (line 731) over up_run (line 239), conjunct by conjunct against those definitions. *)
destruct HMID as ((HJ & HFRS & H8 & H9 & HSP & H3 & H4 & HPAY & HPERM & HDFR & H18 & H20 & H26 & HMEM)
  & H4096u & HINu & HNINu & HMOLE & HMOOK & H22 & H24).
pose proof (upD_base_facts cx HBASE) as [HPN HLEN].
pose proof HGEO as (HG1 & HG2 & HG3 & HG4).
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (HSTKV : DEC_LLVMF_STK = 32768) by reflexivity.
assert (HN26 : 0 <= d_n cx < 2 ^ 26) by (destruct HPN as [[Hq _] | [Hq _]]; lia).
assert (HLENR : 0 <= up_len cx < 2 ^ 26) by (unfold up_len, dec_a_len; lia).
assert (LB : Z.of_nat (length (d_body cx)) = up_len cx)
  by (unfold d_body, up_len, dec_a_len, dec_a_u; rewrite length_skipn; lia).
pose proof (up_sz_bounds cx) as HSZB.
(* ajournal (lib/Reusable/YCbq.v:350-372), conjunct by conjunct against that definition. *)
pose proof HJ as (_ & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRESJ & HSTK & _).
pose proof HSTK as (HSP0al & HSTK0 & HCEIL & HSLO & HSHI & H47 & _).
assert (HWIN : alloc_ceiling + 28000 <= d_sp1 cx - ESTACK) by (unfold ESTACK in *; lia).
(* the fake frame, and so its shadow row, lies below the allocator ceiling *)
assert (HFIN : In (DEC_FCLASS, d_fpos cx) (frames S')) by (rewrite HFRS; left; reflexivity).
assert (HFEQ : frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr.
  destruct HLY as (_ & _ & _ & _ & _ & HLF & _). rewrite HLF. reflexivity. }
destruct (frames_bounds segs B LAWS ly' S' W' mem' md' DEC_FCLASS (d_fpos cx) HAR HFIN)
  as (HF0 & HFC & HFA).
rewrite HFEQ in HFC, HFA.
change (fs_frame_bytes DEC_FCLASS) with 64 in HFC, HFA.
assert (HSHlo : SHADOW_OFF <= d_SH cx)
  by (unfold d_SH; exact (proj1 (YG0s.shadow_addr_bounds (d_F cx) ltac:(lia)))).
assert (HSHhi : d_SH cx + 8 <= kHighMemBeg).
{ pose proof (proj2 (YG0s.shadow_addr_bounds (d_F cx + 56) ltac:(lia))
                ltac:(unfold kHighMemEnd in *; lia)) as Hq.
  unfold d_SH, shadow_addr in *.
  replace (d_F cx + 56) with (d_F cx + 7 * 8) in Hq by lia. rewrite Z.div_add in Hq by lia. lia. }
assert (HSH0 : 0 <= d_SH cx) by (unfold SHADOW_OFF in HSHlo; lia).
(* the three live blocks of this cut point *)
assert (HPERM1 : Permutation (ablocks B ly' S') (up_bl0 cx res ++ [(upb, up_sz cx)]))
  by (unfold up_bl1 in HPERM; exact HPERM).
assert (HINres : In (res, up_len cx) (ablocks B ly' S')).
{ eapply Permutation_in; [apply Permutation_sym; exact HPERM1|].
  apply in_or_app. left. unfold up_bl0. apply in_or_app. right. left. reflexivity. }
destruct (al_blocks segs B LAWS ly' S' W' mem' md' res (up_len cx) HAR HINres)
  as (_ & HR4096 & HRceil & HRapp & HRpres & _ & HRmax).
destruct (al_blocks segs B LAWS ly' S' W' mem' md' upb (up_sz cx) HAR HINu)
  as (_ & HU4096 & HUceil & HUapp & HUpres & _ & HUmax).
pose proof (req_size_pos0 (up_len cx) ltac:(lia)) as [HRq1 HRq2].
pose proof (req_size_pos0 (up_sz cx) ltac:(lia)) as [HUq1 HUq2].
assert (HDbody : zdisjoint (res, req_size (up_len cx)) (upb, req_size (up_sz cx))).
{ exact (upD_blk_disj ly' S' W' mem' md' (up_bl0 cx res) [(upb, up_sz cx)]
           (res, up_len cx) (upb, up_sz cx) HAR HPERM1
           ltac:(unfold up_bl0; apply in_or_app; right; left; reflexivity)
           ltac:(left; reflexivity)). }
unfold zdisjoint in HDbody. cbn [fst snd] in HDbody.
assert (HDpay : 0 < d_n cx -> zdisjoint (d_p cx, req_size (d_n cx)) (upb, req_size (up_sz cx))).
{ intros Hn0. destruct HPN as [[Hq _] | [_ Hin0]]; [lia|].
  exact (upD_blk_disj ly' S' W' mem' md' (up_bl0 cx res) [(upb, up_sz cx)]
           (d_p cx, d_n cx) (upb, up_sz cx) HAR HPERM1
           ltac:(unfold up_bl0; apply in_or_app; left; exact Hin0)
           ltac:(left; reflexivity)). }
assert (HDfr : zdisjoint (upb, req_size (up_sz cx)) (d_F cx, 64)).
{ pose proof (sep_block_frame segs B LAWS ly' S' W' mem' md' upb (up_sz cx) DEC_FCLASS (d_fpos cx)
                HAR HINu HFIN) as Hq.
  rewrite HFEQ in Hq. change (fs_frame_bytes DEC_FCLASS) with 64 in Hq. exact Hq. }
unfold zdisjoint in HDfr. cbn [fst snd] in HDfr.
(* no byte this segment carries lies in the upstream buffer *)
assert (HTOUCHU : forall a, up_touch cx res a -> ~ (upb <= a < upb + req_size (up_sz cx))).
{ intros a Ha. unfold up_touch in Ha.
  unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in HUapp, HSHlo, HSHhi.
  destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]].
  - lia.
  - lia.
  - lia.
  - destruct HUapp as [_ [Hq | [Hq1 Hq2]]]; lia.
  - destruct (Z.eq_dec (d_n cx) 0) as [Hz | Hz]; [lia|].
    pose proof (HDpay ltac:(lia)) as Hq. unfold zdisjoint in Hq. cbn [fst snd] in Hq.
    pose proof (req_size_pos0 (d_n cx) ltac:(lia)) as [Hq1 Hq2]. lia.
  - lia. }
(* and none of it lies in the leaf's own stack window *)
assert (HTOUCHS : forall a, up_touch cx res a -> ~ (d_sp1 cx - ESTACK <= a < d_sp1 cx)).
{ intros a Ha. unfold up_touch in Ha.
  unfold kHighMemBeg in HSHhi.
  destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]].
  - lia.
  - lia.
  - lia.
  - lia.
  - destruct (Z.eq_dec (d_n cx) 0) as [Hz | Hz]; [lia|].
    destruct (al_blocks segs B LAWS ly' S' W' mem' md' (d_p cx) (d_n cx) HAR (HPAY ltac:(lia)))
      as (_ & _ & Hq & _).
    pose proof (req_size_pos0 (d_n cx) ltac:(lia)) as [Hq1 Hq2]. lia.
  - lia. }
(* 36 * up_nch is the buffer the harness allocated, once the leaf accepts *)
assert (HNCH : CUp.up_ok res upb (up_len cx) (d_body cx) = true ->
               36 * CUp.up_nch (up_len cx) = up_sz cx).
{ intros HOK. destruct (upD_ok_facts _ _ _ _ HOK) as (_ & _ & Hn0).
  pose proof (up_nch_result (up_len cx) HLENR) as [HN1 HN2].
  pose proof (up_olen_val (up_len cx) HLENR) as (_ & HO2 & _).
  pose proof (up_cnt_range (up_len cx) HLENR) as [Hm1 | (Hr1 & _ & _)].
  - exfalso. rewrite (HN2 ltac:(lia)) in Hn0. lia.
  - unfold up_sz, up_cnt in *. rewrite (HO2 ltac:(lia)), (HN1 ltac:(lia)). reflexivity. }
(* ---- the engine, from +0x858 ---- *)
pose proof (HROM_KEPT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROMcx) as HROM0.
pose proof (up_seat UP_TAIL W' regs' mem' (up_obj9_val _ _ _ _ _ CELLS (proj1 HJ)) H18) as HS.
set (E := Eimg (Ereg regs' (@nil word))) in *.
assert (E11 : ew E 11 = Z_to_bv 64 0).
{ unfold E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs' _ 11 11%bv eq_refl). exact H11. }
assert (HAE : env_agree 32 (Ereg regs' (@nil word)) E)
  by (split; [intros n Hn; unfold E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
assert (SHOK : sh_ok pa_segs (SOff 18 0) (@nil shent) E (mrestrict (w_H W') mem')) by apply Forall_nil.
unfold cfg_at.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* +0x858 bnez a1: REFUTED, a1 = 0 (up_post_858) *)
  exfalso. rewrite branch_ne_U, (U_atom E 11 0 E11 ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hc.
  cbn in Hc. discriminate. }
(* +0x85c..+0x868: mv a0,s4 / mv a1,s10 / mv a2,s7 / jal reac_upstream_decode *)
paj_run_tok RUN HS HJ SHOK Bspan; [ up_awr | ].
(* the environment above A_TEXT grew; below it, it is still the entry's *)
lazymatch type of HS with
| st_ok _ ?Ex _ _ =>
    assert (AG : forall n, (n < 240)%nat -> ew Ex n = ew E n)
      by (intros nn Hnn; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia];
          reflexivity);
    assert (EE : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
                 ew Ex n = YK11.getr regs' r)
      by (intros nn r Hnn Hr; try rewrite (AG nn ltac:(lia)); unfold E;
          rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs' _ nn r Hr))
end.
(* the bytes the four instructions did not touch: this segment's symbolic state has no writable region *)
assert (KEEP0 : forall a, aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a. apply aview_eq_of. apply HFr. intros (r & Hr & Hq).
  lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end.
  cbn [In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hq. lia. }
assert (APRES0 : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows (w_H W') mem' (ms_mem ms) a HG Ha)).
assert (HMEMT : up_mem cx res mode nch ns W' (ms_mem ms)).
{ apply (up_mem_kept cx res mode nch ns W' W' mem' (ms_mem ms) HLEN
           ltac:(intros a _; apply KEEP0) APRES0); [| exact HMEM].
  intros HM. apply (up_mode_kept cx ly' S' W' mem' md' ly' S' W' (ms_mem ms)
                      (with_vm_backing (m_vm_lazy md') mat md') mode nch ns
                      HAR ltac:(exact (proj1 HJ)) HROM0 (HROM_KEPT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROMcx)
                      ltac:(intros a _; apply KEEP0) HM). }
pose proof HMEMT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12).
(* the registers at the call *)
pose proof HS as HScall.
upD_reg HS (1%bv : bv 5) (Z_to_bv 64 (DEC_A_LLVMF + UP_DEC3_RA)) UR1
  ltac:(rewrite <- up_base_eq; apply codeptr_val; assumption).
upD_reg HS (10%bv : bv 5) (w64 res) UR10
  ltac:(cbn [sv_denot]; rewrite (EE 20%nat 20%bv ltac:(lia) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact H20).
upD_reg HS (11%bv : bv 5) (w64 (up_len cx)) UR11
  ltac:(cbn [sv_denot]; rewrite (EE 26%nat 26%bv ltac:(lia) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact H26).
upD_reg HS (12%bv : bv 5) (w64 upb) UR12
  ltac:(cbn [sv_denot]; rewrite (EE 23%nat 23%bv ltac:(lia) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact H23).
assert (HPRES1 : aregs_preserved regs' (ms_regs ms)).
{ lazymatch type of HS with
  | st_ok _ ?Ex _ _ =>
      eapply (aregs_preserved_of_st_ok segs _ Ex _ _ regs' (@nil word) HS);
      [ split; [intros n Hn; try rewrite (AG n ltac:(lia)); exact (proj1 HAE n Hn)
               | cbn [ed ewset havoc]; exact (proj2 HAE)]
      | vm_compute; reflexivity ]
  end. }
assert (HSPT : spZ (ms_regs ms) = d_sp1 cx)
  by exact (eq_trans (f_equal bv_unsigned (HPRES1 2 ltac:(unfold acallee_saved; lia))) HSP).
assert (HGPT : YK11.getr (ms_regs ms) 3 = w64 (as_gp B))
  by exact (eq_trans (HPRES1 3 ltac:(unfold acallee_saved; lia)) H3).
assert (HTPT : YK11.getr (ms_regs ms) 4 = w64 (as_tp B))
  by exact (eq_trans (HPRES1 4 ltac:(unfold acallee_saved; lia)) H4).
assert (HRAT : YK0s.ret_ok (YK11.getr (ms_regs ms) 1)).
{ rewrite UR1. rewrite <- up_base_eq.
  apply (ret_ok_codeptr_v (PI := PI_decode)); [unfold UP_DEC3_RA; lia | reflexivity]. }
assert (HSPT2 : bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = d_sp1 cx) by exact HSPT.
assert (HA1 : bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 11)) = up_len cx)
  by exact (eq_trans (f_equal bv_unsigned UR11) (unsigned_lit_small (up_len cx) ltac:(lia))).
(* the leaf's environment at the call *)
assert (HPRESW : forall a, d_sp1 cx - ESTACK <= a < d_sp1 cx -> apresent (w_H W') (ms_mem ms) a).
{ intros a Ha. apply APRES0. apply HPRESJ. unfold ESTACK in *. lia. }
destruct (dec_leafb_stack W' (ms_regs ms) (ms_mem ms)
            ltac:(rewrite HSPT; exact HPRESW) ltac:(rewrite HSPT; lia) ltac:(rewrite HSPT; lia)
            ltac:(rewrite HSPT; exact (upD_mod16_of_mod32 _ HG2)))
  as (LSTK & LAPP1 & LAPP2 & LOFF1 & LOFF2).
rewrite HSPT in LSTK, LAPP1, LAPP2.
pose proof (dec_leafb_cells ly' S' W' (ms_mem ms) (with_vm_backing (m_vm_lazy md') mat md')
              LAWS CELLS ltac:(exact (proj1 HJ))) as LCELLS.
pose proof (dec_leafb_magic ly' S' W' (ms_mem ms) (with_vm_backing (m_vm_lazy md') mat md') CELLS
              ltac:(exact (proj1 HJ))) as LMAGIC.
(* the call *)
pmkst HS.
lazymatch goal with
| |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (YK11.mkst rg (Z_to_bv 64 reac_upstream_decode_c.REAC_UPSTREAM_DECODE) mm rom) mdx) Q)
end.
pose proof (LUP fx) as HL0. unfold dec_leaf_wr_at, LUpDecode.dec_reac_upstream_decode_cg in HL0.
eapply SRr_mono;
[ eapply (LLVMFuzzerTestOneInput_leafb.dec_leafb_journal (SK := dec_A_sink_head) B LAWS
            W' (ms_regs ms) (ms_mem ms) _ _ _ _ _ _ _ _ _ _ _ _ _
            (d_sp1 cx - d_sp0 cx) reac_upstream_decode_c.REAC_UPSTREAM_DECODE
            (Some (if CUp.up_ok res upb (up_len cx) (d_body cx) then 12 else -1))
            (if CUp.up_ok res upb (up_len cx) (d_body cx)
             then [(upb, upb + 36 * CUp.up_nch (up_len cx))] else @nil (Z * Z))
            (fun m2 => CUp.up_ok res upb (up_len cx) (d_body cx) = true ->
               DMem.bytes_at Img0.rsegs m2 upb
                 (CDec.braid_out (d_body cx) (CUp.up_nch (up_len cx)) 12))
            HJ)
| ].
- (* spZ regsT = sp0 + o *) rewrite HSPT. lia.
- (* o mod 16 = 0 *)
  rewrite Zminus_mod, (upD_mod16_of_mod32 _ HG2), HSP0al. reflexivity.
- (* o <= 0 *) lia.
- (* ESTACK - o <= STK *) unfold ESTACK in *; lia.
- exact HRAT.
- exact HGPT.
- exact HTPT.
- (* the written range is a temporary block of this call *)
  intros a Hin. destruct (CUp.up_ok res upb (up_len cx) (d_body cx)) eqn:EOK.
  + hnf in Hin. inversion Hin as [q l Hq | q l Hq]; subst; [| inversion Hq].
    cbn [fst snd] in Hq. rewrite (HNCH eq_refl) in Hq.
    right. right. left. exists upb, (up_sz cx).
    split; [exact HINu | split; [exact HNINu | lia]].
  + hnf in Hin. inversion Hin.
- (* the leaf *)
  intros HPRE.
  specialize (HL0 ly' S' W' (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md') mat md')
                (d_body cx) res upb (d_sp1 cx - ESTACK) HPRE).
  cbv zeta in HL0. rewrite HA1, HSPT2 in HL0.
  apply HL0; clear HL0.
  + exact UR10.
  + exact UR12.
  + lia.
  + lia.
  + lia.
  + exact LMAGIC.
  + intros _ _ Hn0. split; [rewrite <- LB, Nat2Z.id; reflexivity|].
    apply (LLVMFuzzerTestOneInput_leafb.dec_leafb_bytes_garr8 W');
      [ exact T7 | lia | rewrite LB; lia ].
  + intros HOK. pose proof (HNCH HOK) as HE36.
    split;
      [ apply (LLVMFuzzerTestOneInput_leafb.dec_leafb_wr_at_block B LAWS ly' S' W' (ms_mem ms)
                 (with_vm_backing (m_vm_lazy md') mat md') upb (up_sz cx) upb
                 (36 * CUp.up_nch (up_len cx)) (proj1 HJ) HINu ltac:(lia) ltac:(lia))
      | split; [lia | lia] ].
  + exact LSTK.
  + unfold reac_upstream_decode_c.REAC_UPSTREAM_DECODE_D, ESTACK in *. lia.
  + intros _ _ _. unfold AsanKA.off_stk. rewrite HSPT2.
    unfold reac_upstream_decode_c.REAC_UPSTREAM_DECODE_D in *. lia.
  + intros HOK. pose proof (HNCH HOK) as HE36. unfold AsanKA.off_stk. rewrite HSPT2.
    unfold reac_upstream_decode_c.REAC_UPSTREAM_DECODE_D in *. lia.
  + exact LOFF2.
  + exact LAPP1.
  + exact LAPP2.
  + exact LCELLS.
  + exact LOFF1.
  + intros _ _ Hn0.
    apply (LLVMFuzzerTestOneInput_leafb.dec_leafb_addressable_block B LAWS ly' S' W' (ms_mem ms)
             (with_vm_backing (m_vm_lazy md') mat md') res (up_len cx) res (up_len cx)
             (proj1 HJ) HINres ltac:(lia) ltac:(lia) ltac:(lia)).
  + intros HOK. pose proof (HNCH HOK) as HE36.
    apply (LLVMFuzzerTestOneInput_leafb.dec_leafb_addressable_block B LAWS ly' S' W' (ms_mem ms)
             (with_vm_backing (m_vm_lazy md') mat md') upb (up_sz cx) upb
             (36 * CUp.up_nch (up_len cx)) (proj1 HJ) HINu ltac:(lia) ltac:(lia) ltac:(lia)).
  + apply (LLVMFuzzerTestOneInput_leafb.dec_leafb_rng_journal (SK := dec_A_sink_head) B
             DEC_LLVMF_STK (d_sp0 cx) (@nil (Z * Z)) (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
             [(DEC_FCLASS, d_fpos cx)] ly' S' W' (ms_mem ms)
             (with_vm_backing (m_vm_lazy md') mat md') dec_ev_86c
             (d_sp1 cx - reac_upstream_decode_c.REAC_UPSTREAM_DECODE_D)
             reac_upstream_decode_c.REAC_UPSTREAM_DECODE_D HJ);
      unfold reac_upstream_decode_c.REAC_UPSTREAM_DECODE_D in *; lia.
  + apply (LLVMFuzzerTestOneInput_leafb.dec_leafb_rng W');
      [ unfold reac_upstream_decode_c.DIV36_MAGIC_AT; lia
      | unfold reac_upstream_decode_c.DIV36_MAGIC_AT; lia |].
    intros a Ha. replace a with (reac_upstream_decode_c.DIV36_MAGIC_AT +
                                 (a - reac_upstream_decode_c.DIV36_MAGIC_AT)) by lia.
    apply (LLVMFuzzerTestOneInput_leafb.dec_leafb_covers_visible (w_H W')
             reac_upstream_decode_c.DIV36_MAGIC_AT 8);
      [ exact (w_Hoff W') | vm_compute; reflexivity | lia
      | unfold reac_upstream_decode_c.DIV36_MAGIC_AT; lia ].
  + exact (proj1 (LLVMFuzzerTestOneInput_leafb.dec_leafb_rng_cells W')).
  + exact (proj2 (LLVMFuzzerTestOneInput_leafb.dec_leafb_rng_cells W')).
  + intros _ _ Hn0.
    apply (LLVMFuzzerTestOneInput_leafb.dec_leafb_rng_block B LAWS ly' S' W' (ms_mem ms)
             (with_vm_backing (m_vm_lazy md') mat md') res (up_len cx) res (up_len cx)
             (proj1 HJ) HINres ltac:(lia) ltac:(lia)).
  + intros _ _ Hn0.
    assert (Hpos : 0 < up_len cx).
    { pose proof (up_nch_result (up_len cx) HLENR) as [HN1 HN2].
      unfold CUp.up_nch in Hn0.
      destruct ((124 <=? up_len cx) && ((up_len cx - 52) mod 36 =? 0) &&
                (((up_len cx - 52) / 36) mod 2 =? 0) && ((up_len cx - 52) / 36 <=? 40))%bool eqn:Eb;
        [| lia].
      apply andb_prop in Eb as [Eb _]. apply andb_prop in Eb as [Eb _].
      apply andb_prop in Eb as [Eb _]. apply Z.leb_le in Eb. lia. }
    pose proof (LLVMFuzzerTestOneInput_leafb.dec_leafb_rng_shadow_block B LAWS ly' S' W' (ms_mem ms)
                  (with_vm_backing (m_vm_lazy md') mat md') res (up_len cx) res (up_len cx)
                  (proj1 HJ) HINres ltac:(lia) ltac:(lia) ltac:(lia)) as HSH.
    unfold AsanCells.shadow_addr in HSH.
    replace ((res + up_len cx - 1) / 8 + AsanCells.ASAN_K - (res / 8 + AsanCells.ASAN_K) + 1)
      with ((res + up_len cx - 1) / 8 - res / 8 + 1) in HSH by lia.
    exact HSH.
  + intros HOK. pose proof (HNCH HOK) as HE36.
    apply (LLVMFuzzerTestOneInput_leafb.dec_leafb_rng_block B LAWS ly' S' W' (ms_mem ms)
             (with_vm_backing (m_vm_lazy md') mat md') upb (up_sz cx) upb
             (36 * CUp.up_nch (up_len cx)) (proj1 HJ) HINu ltac:(lia) ltac:(lia)).
  + intros HOK. pose proof (HNCH HOK) as HE36.
    pose proof (LLVMFuzzerTestOneInput_leafb.dec_leafb_rng_shadow_block B LAWS ly' S' W' (ms_mem ms)
                  (with_vm_backing (m_vm_lazy md') mat md') upb (up_sz cx) upb
                  (36 * CUp.up_nch (up_len cx)) (proj1 HJ) HINu ltac:(lia) ltac:(lia) ltac:(lia)) as HSH.
    unfold AsanCells.shadow_addr in HSH.
    replace ((upb + 36 * CUp.up_nch (up_len cx) - 1) / 8 + AsanCells.ASAN_K
             - (upb / 8 + AsanCells.ASAN_K) + 1)
      with ((upb + 36 * CUp.up_nch (up_len cx) - 1) / 8 - upb / 8 + 1) in HSH by lia.
    exact HSH.
  + intros x Hin. destruct (CUp.up_ok res upb (up_len cx) (d_body cx)) eqn:EOK.
    * hnf in Hin. inversion Hin as [q l Hq | q l Hq]; subst; [| inversion Hq].
      cbn [fst snd] in Hq. rewrite (HNCH eq_refl) in Hq.
      exact (LLVMFuzzerTestOneInput_leafb.dec_leafb_wr_block B LAWS ly' S' W' (ms_mem ms)
               (with_vm_backing (m_vm_lazy md') mat md') upb (up_sz cx) (proj1 HJ) HINu x
               ltac:(lia)).
    * hnf in Hin. inversion Hin.
- (* back at +0x86c *)
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres2 & Heff2 & Hgr2 & HX2).
  assert (CH : forall r, acallee_saved r ->
                 YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r))
    by (intros r Hr; exact (eq_trans (HP2 r Hr) (HPRES1 r Hr))).
  assert (KEEP : forall a, up_touch cx res a ->
                   aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a).
  { intros a Ha. rewrite <- (KEEP0 a). apply Heff2.
    - unfold up_touch in Ha. unfold kHighMemBeg in HSHhi.
      destruct (Z.eq_dec (d_n cx) 0) as [Hz | Hz].
      + destruct Ha as [Hq | [Hq | [Hq | [Hq | [Hq | Hq]]]]]; lia.
      + destruct (al_blocks segs B LAWS ly' S' W' mem' md' (d_p cx) (d_n cx) HAR (HPAY ltac:(lia)))
          as (_ & Hp1 & Hp2 & _).
        pose proof (req_size_pos0 (d_n cx) ltac:(lia)) as [Hq1 Hq2].
        destruct Ha as [Hq | [Hq | [Hq | [Hq | [Hq | Hq]]]]]; lia.
    - rewrite HSPT. exact (HTOUCHS a Ha).
    - destruct (CUp.up_ok res upb (up_len cx) (d_body cx)) eqn:EOK.
      + intros Hin. hnf in Hin. inversion Hin as [q l Hq | q l Hq]; subst; [| inversion Hq].
        cbn [fst snd] in Hq. rewrite (HNCH eq_refl) in Hq.
        exact (HTOUCHU a Ha ltac:(lia)).
      + intros Hin. hnf in Hin. inversion Hin. }
  assert (HMEM2 : up_mem cx res mode nch ns W' mem2).
  { apply (up_mem_kept cx res mode nch ns W' W' mem' mem2 HLEN KEEP
             ltac:(intros a Ha; apply Hgr2; apply APRES0; exact Ha)); [| exact HMEM].
    intros HM. apply (up_mode_kept cx ly' S' W' mem' md' ly' S' W' mem2 md2 mode nch ns
                        HAR ltac:(exact (proj1 HJ2)) HROM0 (HROM_KEPT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROMcx)
                        ltac:(intros a Ha; apply KEEP; unfold up_touch; right; right; left; lia) HM). }
  pose proof HMEM2 as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12).
  unfold llvm_a_st_86c.
  (* read the post in this file's names: up_len / up_cnt / up_sz are those of llvm_a_st_86c by definition *)
  assert (HULEN : dec_a_len (d_n cx) = up_len cx) by reflexivity.
  assert (HUCNT : CChan.upstream_result (up_len cx) = up_cnt cx) by reflexivity.
  assert (HUSZ : dec_a_uolen (up_cnt cx) = up_sz cx) by reflexivity.
  rewrite ?HULEN, ?HUCNT, ?HUSZ.
  exists fx, ly', S', regs2, mem2, md2, res, upb, mode, nch, ns.
  split; [rewrite UR1; reflexivity|].
  split; [exact HFZ|].
  split.
  { unfold dec_a_core.
    split; [exact HJ2|].
    split; [exact HFRS|].
    split; [exact (eq_trans (CH 8 ltac:(unfold acallee_saved; lia)) H8)|].
    split; [exact (eq_trans (CH 9 ltac:(unfold acallee_saved; lia)) H9)|].
    split; [exact (eq_trans (f_equal bv_unsigned (CH 2 ltac:(unfold acallee_saved; lia))) HSP)|].
    split; [lia|]. split; [exact HG2|].
    split; [exact (eq_trans (CH 3 ltac:(unfold acallee_saved; lia)) H3)|].
    split; [exact (eq_trans (CH 4 ltac:(unfold acallee_saved; lia)) H4)|].
    split; [exact M1|].
    split; [lia|]. split; [exact HG4|].
    split; [exact M2|].
    split; [exact M3|].
    split; [exact HPAY|].
    exact M4. }
  split.
  { unfold up_bl1, up_bl0 in HPERM. rewrite <- app_assoc in HPERM. exact HPERM. }
  split; [lia|]. split; [lia|].
  split; [exact HMOLE|]. split; [exact HMOOK|].
  split.
  { destruct HDFR as (D1 & D2 & D3).
    split; [exact (eq_trans (CH 19 ltac:(unfold acallee_saved; lia)) D1)|].
    split; [exact (eq_trans (CH 21 ltac:(unfold acallee_saved; lia)) D2)|].
    exact (eq_trans (CH 27 ltac:(unfold acallee_saved; lia)) D3). }
  split; [exact (Hres2 _ eq_refl)|].
  split; [exact (eq_trans (CH 18 ltac:(unfold acallee_saved; lia)) H18)|].
  split; [exact (eq_trans (CH 20 ltac:(unfold acallee_saved; lia)) H20)|].
  split; [exact (eq_trans (CH 22 ltac:(unfold acallee_saved; lia)) H22)|].
  split; [exact (eq_trans (CH 23 ltac:(unfold acallee_saved; lia)) H23)|].
  split; [exact (eq_trans (CH 24 ltac:(unfold acallee_saved; lia)) H24)|].
  split; [exact (eq_trans (CH 26 ltac:(unfold acallee_saved; lia)) H26)|].
  split; [exact M5|].
  split; [exact M6|].
  split; [exact M7|].
  split.
  { intros HOK. pose proof (HNCH HOK) as HE36.
    destruct (upD_ok_facts _ _ _ _ HOK) as (_ & _ & Hn0).
    assert (HBL : Z.of_nat (length (CDec.braid_out (d_body cx) (CUp.up_nch (up_len cx)) 12))
                  = 36 * CUp.up_nch (up_len cx)).
    { unfold CDec.braid_out. rewrite !length_map, length_seq, Z2Nat.id by lia. lia. }
    apply (upD_garr8_of_bytes W' mem2 upb).
    - intros i Hi. rewrite HBL in Hi.
      apply Hgr2. apply APRES0. exact (proj1 (HUpres (upb + i) ltac:(lia))).
    - exact (HX2 HOK). }
  split.
  { intros HOK i Hi.
    rewrite (Heff2 (upb + i) ltac:(lia)
               ltac:(rewrite HSPT; intros [Hq _]; lia)
               ltac:(rewrite HOK; intros Hin; hnf in Hin; inversion Hin)).
    rewrite (KEEP0 (upb + i)). exact (HFILL i Hi). }
  split; [exact M8|].
  split; [exact M9|].
  split; [exact M10|].
  split; [exact M11|].
  exact M12.
Qed.

End g.

(* ---------------------------------------------------------------- *)
(* The segment: llvm_a_st_748 -> A1 -> A2 -> B -> C -> D              *)
(* ---------------------------------------------------------------- *)

(* llvm_a_st_748 read as up_geom and up_pre_748: the same facts, regrouped (dec_a_core's state clauses and the
   byte clauses of up_mem are interleaved in the interface's text). *)
Lemma up_pre_of_748 : forall (cx : dctx) (W' : world segs) (c' : config),
  up_base cx -> llvm_a_st_748 B MT cx W' c' ->
  up_geom cx /\
  exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res mode nch ns : Z),
    c' = @cfg_at fx' segs (DEC_A_LLVMF + UP_CHK) regs' mem' md' /\
    frm_zero (@fp_csr fx') /\
    up_pre_748 cx res mode nch ns ly' S' W' regs' mem' md'.
Proof.
intros cx W' c' HBASE H748.
destruct H748 as (fx' & ly' & S' & regs' & mem' & md' & res & mode & nch & ns & Hcfg & Hfrm & HCORE &
                  HPERM & Hres & HMLE & HMOK & HFR & Ha0 & Hr18 & Hr20 & Hr26 & HMODE & HFSH & HGARR &
                  HSLOTS & S40 & S56 & S64 & S112).
destruct HCORE as (HJ & Hfrms & Hr8 & Hr9 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & Hsaved & HF4096 & HFal &
                   HFpres & HFL & Hinp & HGP).
split; [exact (conj Hsp1r (conj Hsp1al (conj HF4096 HFal)))|].
exists fx', ly', S', regs', mem', md', res, mode, nch, ns.
split; [exact Hcfg|]. split; [exact Hfrm|].
split.
{ unfold up_run.
  split; [exact HJ|]. split; [exact Hfrms|]. split; [exact Hr8|]. split; [exact Hr9|]. split; [exact Hsp|].
  split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hinp|].
  split; [exact HPERM|]. split; [exact HFR|]. split; [exact Hr18|]. split; [exact Hr20|]. split; [exact Hr26|].
  unfold up_mem.
  split; [exact Hsaved|]. split; [exact HFpres|]. split; [exact HFL|]. split; [exact HGP|].
  split; [exact HMODE|]. split; [exact HFSH|]. split; [exact HGARR|].
  split; [exact HSLOTS|]. split; [exact S40|]. split; [exact S56|]. split; [exact S64 | exact S112]. }
split; [exact Hres|]. split; [exact HMLE|]. split; [exact HMOK | exact Ha0].
Qed.

End f.

Theorem up_seg :
  (forall fx : YK11.FPState, @up_A1_stmt fx) -> (forall fx : YK11.FPState, @up_A2_stmt fx) ->
  (forall fx : YK11.FPState, @up_B_stmt fx) -> (forall fx : YK11.FPState, @up_C_stmt fx) ->
  (forall fx : YK11.FPState, @up_D_stmt fx) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    up_base cx -> dec_a_rom cx -> llvm_a_st_748 B MT cx W' c' ->
    SRr segs W' c' (llvm_a_st_86c B MT cx).
Proof.
intros HA1 HA2 HB HC HD cx W' c' HBASE HROMcx H748.
destruct (up_pre_of_748 cx W' c' HBASE H748) as
  (HGEOM & fx' & ly' & S' & regs' & mem' & md' & res & mode & nch & ns & -> & Hfrm & HPRE).
eapply SRr_bind; [exact (HA1 fx' cx res mode nch ns ly' S' W' regs' mem' md' HBASE HROMcx HGEOM HPRE)|].
intros W1 c1 _ H79c.
eapply SRr_bind; [exact (HA2 fx' cx res mode nch ns W1 c1 HBASE HROMcx HGEOM H79c)|].
intros W2 c2 _ H7c4.
eapply SRr_bind; [exact (HB fx' cx res mode nch ns W2 c2 HBASE HROMcx HGEOM H7c4)|].
intros W3 c3 _ H7fc.
eapply SRr_bind; [exact (HC fx' cx res mode nch ns W3 c3 HBASE HROMcx HGEOM H7fc)|].
intros W4 c4 _ H858.
exact (HD fx' cx res mode nch ns W4 c4 Hfrm HBASE HROMcx HGEOM H858).
Qed.


(* The segment lemma: llvm_a_up_stmt (LLVMFuzzerTestOneInput_segs.v), from the five stages. *)
Theorem llvm_a_up_ok :
  llvm_a_up_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_a_up_stmt.
intros HPCM UTR CELLS HOWN HNERR LAWS ML MTL AMS AM LUP cx W' c' HBASE HROMcx H748.
apply up_seg; [ intros fx'; eapply (@up_A1 fx'); eassumption
              | intros fx'; eapply (@up_A2 fx'); eassumption
              | intros fx'; eapply (@up_B fx'); eassumption
              | intros fx'; eapply (@up_C fx'); eassumption
              | intros fx'; eapply (@up_D fx'); eassumption
              | exact HBASE | exact HROMcx | exact H748 ].
Qed.

End up.
