(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgMain0.v at 6ebe35ba632 (the harness entry
   segment: the save area, sp1, the call of the side stack for frames, the frame facts, the frame and shadow regions,
   the header and shadow writes, the hand-off) made the first segment of reac_box_pin_parse on reac-pw/fuzz_pin's
   image A (fuzz_pin.asan, sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16): 0x80b44 -> the
   cut P1 at 0x80c4c (lib/A/PPgParseCx.v ss_P1). rule 24: no function proved (a segment of the walk).

   What changed against the donor, each read from the neutral excerpt of 0x80b44-0x80c48:
   - the function is a callee: the start is the contract's premises (PPgParseCx.v pp_pre, the caller's journal of
     pin_pre_kit) and the entry state ss_pp0 (pp_entry), not afn_pre / ajournal_init; every write of the walk is
     allowed by that journal (the save area lies in [sp0 - STK, sp0), the frame is in the journal's own list
     after the call).
   - 160-byte save area (`addi sp,sp,-0xa0` 0x80b44, `sd zero,0(sp)` at sp-160, ra .. s11 at sp-8 .. sp-104),
     `andi sp,sp,-0x20` at 0x80b84: sp1 = 32 * ((sp - 160) / 32) in [sp - 176, sp - 160] (donor: 192 / 208);
     the stack region is trimmed to the saves [-104, 0) (donor :228-234) and region 70 = [sp1+8, sp1+56) holds the
     spill of F at sp1+0x30 (donor :235-246 [16, 88)).
   - the GOT loads at 0x80b94-0x80ba8 (0x990a8 -> 0xa1600, the option word 1; 0x99050 -> 0xa15f8, SB into s3),
     `beqz a2` at 0x80bb0 decided by the option word, `li a0,0x40` and `jal 0x3c8e4` at 0x80bb4 / 0x80bb8 (RA
     0x80bbc): the class-0 call through aj_stack_malloc_atS with ASM0, its premises the call-site lemma
     pin_fs0_site below (count_cid 0 (frames Sc) < fs_frames 0 is the contract's premise).
   - the class-0 frame: 64 bytes, 8 shadow bytes, the flag pointer at F + 56 (donor class 1: 128 / 16 / F + 120).
   - 0x80bbc-0x80c48: `bnez s2` at 0x80bcc decided by HPTR 5 on F (the probe loop 0x80bd0-0x80be8 is not reached),
     `sd s11,0x30(s1)`, the header words F+0 = 0x41B58AB3, F+8 = 0x10add, F+16 = 0x80b44, s4 = SB + F/8, the 8
     shadow bytes f1 f1 f1 f1 f8 f3 f3 f3, a3 = -1; the run stops at 0x80c4c (the donor's size split has no
     counterpart here).
   - the hand-off is the continuation pp_from ss_P1 INV_P1 (PPgParseCx.v): the frame's shadow region made
     read-only, the four cell regions dropped, and the kept-memory fact (lib/Reusable/YCbq.v acall_kept, the
     form of proofs/libreac/fuzz_grant/lib/A/Prog/CtrlParse.v at 6ebe35ba632) carried from the entry memory
     through every step (lib/A/PPgParseLib.v pz_kept_refl / pz_kept_run / pz_kept_trans / pz_kept_own). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgParse0.v, with its module paths and module names changed; 299 of its 338 lines of code are new or changed and 354 lines of the source are left out. *)
(* The tail of check_text_scribble at image A, from the return of diginet_scribble_text at 0x839b8:
     0x839b8          bne a0,s10: the two used counts, equal by the walk's agreement premise, so the
                      abort at 0x83ac4 is not reached
     0x839bc-0x839c8  bcmp(chars, want, n) through the wrapper at 0x422e0
     0x839cc          bnez a0: the two texts agree, so the abort is not reached
     0x839d0-0x839d4  bne s3,24: n <= 8, so the inlined fuzz_all of the record's bytes [n, 24) runs
     0x83a20-0x83a58  that loop: each byte is checked against 0xa5, which the record's tail holds
     0x839d8-0x83a1c  want out of scope (shadow 0xf8), the frame header retired, the frame's eight
                      shadow bytes 0xf5 and the flag byte cleared: the class-0 frame is released
     0x83a88-0x83ac0  sp = s0 - 128, ra and s0..s10 from the save area, sp += 128, ret.
   The state at 0x839b8 is lib/A/Prog/check_text_scribble_A.v's cts_cut_ret and the goal is its
   cts_tail_goal; the walk before the cut delivers the one and takes the other.
   The env of this walk is the CUT's registers (atoms 0 .. 31) and eight more atoms: the frame's flag
   byte and the seven entry values the epilogue puts back. The engine's shadow base is the register
   that holds it (s7 = atom 23), so the record's instrumented checks are paid by one shadow entry.
   Measured: from 0x839b8 the run reaches the wrapper's entry with no obligation, and from the
   wrapper's return it runs the whole fill loop and stops at the first store of the release. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalkKept CPgWalkFrame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import check_text_scribble_A.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the bcmp wrapper's 4-byte jump *)
Definition A_BCMP : Z := 0x422e0.
(* the engine's shadow base for this walk: s7, the register that holds it *)
Definition CTS_Bx : sv := SOff 23 0.
(* the extra atoms: the frame's flag byte, then the seven entry values the epilogue restores that the
   contract's aregs_preserved names (ra and s0 .. s11 are restored; the others are the cut's own) *)
Definition cts_extra (FL ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sa0 : Z) : list word :=
  map (Z_to_bv 64) [FL; ra0; s00; s10; s20; s30; s40; s50; s60; s70; s80; s90; sa0].
(* the record's bytes from n on: the fill byte 0xa5 the memset left *)
Definition cts_fill_chunks (n : Z) : list YP09.chunk :=
  map (fun j => YP09.mkChunk (n + Z.of_nat j) (CVal 1 (SLit 165))) (seq 0 (Z.to_nat (24 - n))).
Definition cts_rec_region (n : Z) : YP09.region :=
  YP09.mkRegion (Some 20%nat) 0 24 0 0 (cts_fill_chunks n).
(* the twelve saved words at [s0 - 96, s0), as the entry values the epilogue puts back *)
Definition cts_save_chunks : list YP09.chunk :=
  [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0))].
Definition cts_save_region : YP09.region := YP09.mkRegion (Some 8%nat) (-96) 0 0 0 cts_save_chunks.
(* the frame, with its flag pointer at F + 56, and the frame's eight shadow bytes. The token engine
   refuses a write window that meets the shadow band, and the frame's atom range meets it, so the
   token part of the tail keeps every window closed; the release opens them. *)
Definition cts_frame_region : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 64 0 0 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition cts_fshadow_chunks : list YP09.chunk :=
  map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SLit (nth j cts_shm_live 0)))) (seq 0 8).
Definition cts_fshadow_region : YP09.region :=
  YP09.mkRegion (Some 24%nat) 0 8 0 0 cts_fshadow_chunks.
(* the tail touches only the save area and the record before the release; the frame, its shadow and
   its flag byte come back as regions at the release, with their write windows open *)
Definition cts_regions (n : Z) : smem := [cts_save_region; cts_rec_region n].
Definition cts_atoms : list (nat * afact) :=
  [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (18%nat, HPTR 5); (20%nat, HPTR 0); (23%nat, mkAF SB SB 0)].
Definition cts_SH : list shent := [mkSHE 20%nat 0 24].
(* the cut's registers, with the four the run must see as one value: n as the literal of the case, the
   want pointer and s9 as offsets of the frame atom, and the used count of s10 as a0's atom *)
Definition cts_sr (n : Z) : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 19%bv (SLit n)) 22%bv (SOff 18 32)) 25%bv (SOff 18 0))
         26%bv (SOff 10 0).
Definition cts_ss (n pc : Z) : sstate :=
  mkSS pc (cts_sr n) (cts_regions n) None (mkFacts cts_atoms [] []).
(* Measured on this state (the engine's own run): regions_wf = true and the token layer's static
   check = true for every case of n, the run from 0x839b8 reaches the wrapper's entry 0x422e0 with no
   obligation, and the run from the wrapper's return reaches the first store of the release at
   0x839dc, the whole fill loop decided by the one shadow entry of the record. *)

(* a run over regions whose windows are all closed writes nothing *)
Ltac cts_wr_none := let b := fresh "b" in let Hw := fresh "Hw" in let r := fresh "r" in
  let Hr := fresh "Hr" in let Hw2 := fresh "Hw" in
  intros b Hw; unfold in_wrange in Hw; destruct Hw as (r & Hr & Hw2);
  lazymatch type of Hr with In _ ?rl => let rl' := eval vm_compute in rl in change (In r rl') in Hr end;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_wlo YP09.r_whi] in Hw2; lia | ]); destruct Hr.
(* the walk writes nothing before the release, so every region of its state is read-only *)
Ltac cts_awr_ro := repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [azlit_tac|]].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis ABC : abcmp_realizes tfibsegs B A_BCMP.
(* the env of the tail: the cut's registers, the frame's flag byte and the twelve entry values *)
Definition cts_E (regs3 regs : bvmap 5 word) (FL : Z) : env :=
  Ereg regs3 (cts_extra FL
    (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
    (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))
    (bv_unsigned (getr regs 21)) (bv_unsigned (getr regs 22)) (bv_unsigned (getr regs 23))
    (bv_unsigned (getr regs 24)) (bv_unsigned (getr regs 25)) (bv_unsigned (getr regs 26))).
Lemma cts_E_reg : forall regs3 regs FL n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (cts_E regs3 regs FL) n = getr regs3 r.
Proof. intros regs3 regs FL n r H. exact (ew_Ereg_nat regs3 _ n r H). Qed.
Lemma cts_E_x : forall regs3 regs FL j,
  ew (cts_E regs3 regs FL) (32 + j) = nth j (cts_extra FL
    (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
    (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))
    (bv_unsigned (getr regs 21)) (bv_unsigned (getr regs 22)) (bv_unsigned (getr regs 23))
    (bv_unsigned (getr regs 24)) (bv_unsigned (getr regs 25)) (bv_unsigned (getr regs 26)))
    (Z_to_bv 64 0).
Proof. intros regs3 regs FL j. exact (ew_Ereg_extra regs3 _ j). Qed.
(* the engine's shadow entry of the record, at the register that holds the record's address *)
Lemma cts_shent : forall (W2 : world tfibsegs) mem2 E q,
range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF q 24 -> amem_range q 24 ->
0 <= q -> q + 24 <= 2 ^ 63 ->
ew E 20 = Z_to_bv 64 q -> ew E 23 = Z_to_bv 64 SB ->
shent_ok tfibsegs CTS_Bx E (mrestrict (w_H W2) mem2) (mkSHE 20%nat 0 24).
Proof.
intros W2 mem2 E q Hra Ham Hq Hqn Em E23.
unfold shent_ok, app_apart, CTS_Bx. cbn [she_m she_lo she_hi].
rewrite (cw_U_atom0 E 23 SB E23 ltac:(unfold SB; lia)), (cw_U_atom0 E 20 q Em ltac:(lia)), Z.add_0_r.
rewrite <- (aview_rd_of tfibsegs). rewrite SB_SHADOW_OFF.
split.
- replace (24 - 0) with 24 by lia. exact Hra.
- intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold amem_range in Ham. rewrite C3, C4, C5 in Ham. unfold SHADOW_OFF. lia.
Qed.

(* a chunk that holds a word of an atom, and a chunk that holds one literal byte *)
Lemma cts_chunk8 : forall E m base off j v, ew E j = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem tfibsegs m (base + off) 8 v ->
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 8 (SOff j 0))).
Proof.
intros E m base off j v Hj Hv Hm.
apply (chunk_ok_val tfibsegs E m base off 8 (SOff j 0) v);
[ cbn [sv_denot]; rewrite Hj, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hm ].
Qed.
Lemma cts_chunk1 : forall E m base off v, 0 <= v < 256 -> val_mem tfibsegs m (base + off) 1 v ->
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 1 (SLit v))).
Proof.
intros E m base off v Hv Hm.
apply (chunk_ok_val tfibsegs E m base off 1 (SLit v) v);
[ reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | exact Hm ].
Qed.

(* The state at the cut: the four regions of the tail, the atom facts, and the engine's shadow entry
   of the record. *)
Lemma cts_tail_st : forall n STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(q ch : Z) (tb cj : list Z) ly3 S3 W3 regs3 mem3 md3 fpos,
cts_cut_ret B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj
  ly3 S3 W3 regs3 mem3 md3 fpos ->
regions_wf (cts_regions n) = true ->
st_ok tfibsegs (cts_E regs3 regs (flag_addr ly3 0 fpos)) (cts_ss n A_CTS_RET)
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 A_CTS_RET) mem3 (seg_rom tfibsegs))) /\
sh_ok tfibsegs CTS_Bx cts_SH (cts_E regs3 regs (flag_addr ly3 0 fpos))
  (mrestrict (w_H W3) mem3) /\
range_addressable (aview tfibsegs (w_H W3) mem3) SHADOW_OFF ch 24.
Proof.
intros n STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch tb cj
  ly3 S3 W3 regs3 mem3 md3 fpos HC HWF.
destruct HC as (HE & H10 & H11 & H12 & Hn & HOBJ & HDST & HCJ & HAGR & HLEN & HJ3 & HIN3 & HFRS3 & HP3 & HIO3 & HM3
  & HKEPT & HSP3 & HAL3 & Hgp3 & Htp3 & Hs0 & Hs1 & Ha0 & Hs2 & Hs9 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8
  & Hs10 & Hs11 & HREC & HWANT & HFLP & HFSH & HSAV).
pose proof HE as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
  T_check_text_scribble HE ltac:(unfold T_check_text_scribble, ESTACK; lia))
  as (Hceil0 & H47 & H46 & Hal0 & Hpres0).
unfold T_check_text_scribble, ESTACK in Hwlo, Hceil0, H46.
pose proof HJ0 as (HAR0 & _). pose proof HJ3 as (HAR3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (F := frame_addr ly3 0 fpos) in *. set (FL := flag_addr ly3 0 fpos) in *.
set (E := cts_E regs3 regs FL) in *.
(* the frame's bounds and its 64-alignment *)
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 mem3 md3 0 fpos HAR3 HIN3) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 tfibsegs B ly3 S3 W3 mem3 md3 0 fpos HAR3 HIN3) as (HA64 & _ & _).
change (fs_frame_bytes 0) with 64 in *.
(* the record's bytes lie in application memory, below the ceiling and off the call's window *)
destruct HDST as (Hch0 & Hch63 & Hchd & Hchw & Hchra & Hchh & Hcham & Hchoff).
pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc ch 24 ch HAR0 Hchd ltac:(lia)) as (Hch1 & _).
pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc ch 24 (ch + 23) HAR0 Hchd ltac:(lia)) as (Hch2 & _).
(* the record's bytes and its usable marks at the state of the cut *)
assert (HRA3 : range_addressable (aview tfibsegs (w_H W3) mem3) SHADOW_OFF ch 24).
{ apply (cts_obj_ra B LAWS lyc Sc W memc mdc ly3 S3 W3 mem3 md3 T_check_text_scribble (spZ regs)
    (fun x => ch <= x < ch + 24) ch 24 HAR0 HAR3
    ltac:(intros b m Hin; eapply Permutation_in; [apply Permutation_sym; exact HP3 | exact Hin])
    ltac:(intros cid pos; pose proof HJ0 as (_ & Hly0 & _); pose proof HJ3 as (_ & Hly3' & _);
          unfold frame_addr; destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _);
          destruct Hly3' as (_ & _ & _ & _ & _ & EF3 & _); rewrite EF0, EF3; reflexivity)
    HOBJ ltac:(lia) ltac:(lia) Hchra HKEPT
    ltac:(intros x Hx; apply (cts_shadow_apart x ch 24); try lia;
          unfold amem_range in Hcham |- *; lia)). }
(* every atom the regions are based on, and the values of the twelve saved words *)
assert (HBV : forall w : word, 0 <= bv_unsigned w < 2 ^ 64) by (intros w; apply u64_range).
assert (HX : forall j, ew E (32 + j)%nat = Z_to_bv 64 (nth j
  [FL; bv_unsigned (getr regs 1); bv_unsigned (getr regs 8); bv_unsigned (getr regs 9);
   bv_unsigned (getr regs 18); bv_unsigned (getr regs 19); bv_unsigned (getr regs 20);
   bv_unsigned (getr regs 21); bv_unsigned (getr regs 22); bv_unsigned (getr regs 23);
   bv_unsigned (getr regs 24); bv_unsigned (getr regs 25); bv_unsigned (getr regs 26)] 0)).
{ intros j. subst E. rewrite (cts_E_x regs3 regs FL j). unfold cts_extra.
  exact (map_nth (Z_to_bv 64) _ 0 j). }
assert (E8 : ew E 8 = getr regs 2)
  by (subst E; rewrite (cts_E_reg regs3 regs FL 8 8%bv eq_refl); exact Hs0).
assert (E18 : ew E 18 = Z_to_bv 64 F)
  by (subst E; rewrite (cts_E_reg regs3 regs FL 18 18%bv eq_refl); exact Hs2).
assert (E20 : ew E 20 = Z_to_bv 64 ch)
  by (subst E; rewrite (cts_E_reg regs3 regs FL 20 20%bv eq_refl); exact Hs4).
assert (E24 : ew E 24 = Z_to_bv 64 (shadow_addr F))
  by (subst E; rewrite (cts_E_reg regs3 regs FL 24 24%bv eq_refl); exact Hs8).
assert (B8 : base_val E (Some 8%nat) = spZ regs)
  by (cbn [base_val]; rewrite E8; reflexivity).
assert (B18 : base_val E (Some 18%nat) = F)
  by (cbn [base_val]; rewrite E18; apply unsigned_lit_small; lia).
assert (B20 : base_val E (Some 20%nat) = ch)
  by (cbn [base_val]; rewrite E20; apply unsigned_lit_small; lia).
assert (E10a : ew E 10 = Z_to_bv 64 (snd (DgnLib.scribble_text_spec tb n)))
  by (subst E; rewrite (cts_E_reg regs3 regs FL 10 10%bv eq_refl); exact Ha0).
assert (HF8 : 0 <= F / 8 <= F)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (B24 : base_val E (Some 24%nat) = shadow_addr F)
  by (cbn [base_val]; rewrite E24; apply unsigned_lit_small;
      unfold shadow_addr, SHADOW_OFF; lia).
(* the record's fill bytes *)
assert (HFILL : forall j, (j < Z.to_nat (24 - n))%nat ->
  val_mem tfibsegs (mrestrict (w_H W3) mem3) (ch + (n + Z.of_nat j)) 1 165).
{ intros j Hj. apply (proj1 (garr8_app tfibsegs _ ch _ _)) in HREC.
  destruct HREC as (_ & HR2). rewrite HLEN, Z2Nat.id in HR2 by lia.
  destruct (HR2 j ltac:(rewrite repeat_length; exact Hj)) as (Hv & _).
  rewrite (nth_indep _ 0 165) in Hv by (rewrite repeat_length; exact Hj).
  rewrite nth_repeat in Hv. replace (ch + (n + Z.of_nat j)) with (ch + n + Z.of_nat j) by lia.
  exact Hv. }
split.
- apply (cw_st_ok_at E A_CTS_RET (cts_sr n) (cts_regions n) (mkFacts cts_atoms [] []) regs3).
  + (* the cut's registers, with the four the run must see as one value *)
    unfold cts_sr.
    apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
      [subst E; apply regs_ok_Ereg | discriminate |] | discriminate |] | discriminate |] | discriminate |].
    * rewrite Hs3. cbn [sv_denot]. reflexivity.
    * rewrite Hs6. cbn [sv_denot]. rewrite E18, unsigned_lit_small by lia. reflexivity.
    * rewrite Hs9. cbn [sv_denot]. rewrite E18, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    * rewrite Hs10, HAGR. cbn [sv_denot].
      rewrite E10a, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + exact HWF.
  + (* the two regions of the token part *)
    unfold cts_regions. repeat apply Forall_cons; try apply Forall_nil.
    * (* the twelve saved words, as the entry values the epilogue puts back *)
      unfold cts_save_region, region_ok, cts_save_chunks.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite B8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      destruct HSAV as (V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26).
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (cts_chunk8 E _ (spZ regs) (-8) 33 (bv_unsigned (getr regs 1)));
         [exact (HX 1%nat) | apply HBV | replace (spZ regs + - 8) with (spZ regs - 8) by lia; exact V1].
      -- apply (cts_chunk8 E _ (spZ regs) (-16) 34 (bv_unsigned (getr regs 8)));
         [exact (HX 2%nat) | apply HBV | replace (spZ regs + - 16) with (spZ regs - 16) by lia; exact V8].
      -- apply (cts_chunk8 E _ (spZ regs) (-24) 35 (bv_unsigned (getr regs 9)));
         [exact (HX 3%nat) | apply HBV | replace (spZ regs + - 24) with (spZ regs - 24) by lia; exact V9].
      -- apply (cts_chunk8 E _ (spZ regs) (-32) 36 (bv_unsigned (getr regs 18)));
         [exact (HX 4%nat) | apply HBV | replace (spZ regs + - 32) with (spZ regs - 32) by lia; exact V18].
      -- apply (cts_chunk8 E _ (spZ regs) (-40) 37 (bv_unsigned (getr regs 19)));
         [exact (HX 5%nat) | apply HBV | replace (spZ regs + - 40) with (spZ regs - 40) by lia; exact V19].
      -- apply (cts_chunk8 E _ (spZ regs) (-48) 38 (bv_unsigned (getr regs 20)));
         [exact (HX 6%nat) | apply HBV | replace (spZ regs + - 48) with (spZ regs - 48) by lia; exact V20].
      -- apply (cts_chunk8 E _ (spZ regs) (-56) 39 (bv_unsigned (getr regs 21)));
         [exact (HX 7%nat) | apply HBV | replace (spZ regs + - 56) with (spZ regs - 56) by lia; exact V21].
      -- apply (cts_chunk8 E _ (spZ regs) (-64) 40 (bv_unsigned (getr regs 22)));
         [exact (HX 8%nat) | apply HBV | replace (spZ regs + - 64) with (spZ regs - 64) by lia; exact V22].
      -- apply (cts_chunk8 E _ (spZ regs) (-72) 41 (bv_unsigned (getr regs 23)));
         [exact (HX 9%nat) | apply HBV | replace (spZ regs + - 72) with (spZ regs - 72) by lia; exact V23].
      -- apply (cts_chunk8 E _ (spZ regs) (-80) 42 (bv_unsigned (getr regs 24)));
         [exact (HX 10%nat) | apply HBV | replace (spZ regs + - 80) with (spZ regs - 80) by lia; exact V24].
      -- apply (cts_chunk8 E _ (spZ regs) (-88) 43 (bv_unsigned (getr regs 25)));
         [exact (HX 11%nat) | apply HBV | replace (spZ regs + - 88) with (spZ regs - 88) by lia; exact V25].
      -- apply (cts_chunk8 E _ (spZ regs) (-96) 44 (bv_unsigned (getr regs 26)));
         [exact (HX 12%nat) | apply HBV | replace (spZ regs + - 96) with (spZ regs - 96) by lia; exact V26].
    * (* the record's fill bytes *)
      unfold cts_rec_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite B20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_forall. intros c Hc. unfold cts_fill_chunks in Hc.
      apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
      apply (cts_chunk1 E _ ch (n + Z.of_nat j) 165); [lia|].
      apply HFILL. lia.
  + (* the two are apart: the record lies below the allocation ceiling, the save area above it *)
    apply pairwise_disjoint_of_extents.
    unfold cts_regions, cts_save_region, cts_rec_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint].
    rewrite B8, B20. unfold zdisj. cbn [fst snd].
    unfold T_check_text_scribble, ESTACK in *.
    destruct Hchoff as [Hoff | Hoff]; repeat split; first [exact I | lia].
  + (* the atoms: the entry stack pointer, the frame, the record and the shadow base *)
    assert (E23 : ew E 23 = Z_to_bv 64 SB)
      by (subst E; rewrite (cts_E_reg regs3 regs FL 23 23%bv eq_refl); exact Hs7).
    assert (HF32 : F mod 32 = 0).
    { destruct (proj1 (Z.mod_divide F 64 ltac:(lia)) HA64) as (kk & Hkk).
      replace F with (kk * 2 * 32) by lia. apply Z_mod_mult. }
    unfold amem_range in Hcham, HFapp. rewrite ?C1, ?C2, ?C3, ?C4, ?C5 in Hcham, HFapp.
    assert (A8 : afact_ok E 8 (mkAF (2 ^ 46) (2 ^ 47) 4)).
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E8.
      change (bv_unsigned (getr regs 2)) with (spZ regs).
      split; [lia|]. split; [exact Hal0 | lia]. }
    assert (A18 : afact_ok E 18 (HPTR 5)).
    { unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite E18, unsigned_lit_small by lia. split; [lia|]. split; [exact HF32 | lia]. }
    assert (A20 : afact_ok E 20 (HPTR 0)).
    { unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite E20, unsigned_lit_small by lia. split; [lia|].
      split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
    assert (A23 : afact_ok E 23 (mkAF SB SB 0)).
    { unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E23, unsigned_lit_small by (unfold SB; lia). split; [lia|].
      split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
    unfold facts_ok. cbn [f_atoms f_conds f_alias cts_atoms atoms_ok conds_ok alias_ok].
    split; [|split; exact I].
    split; [exact A8|]. split; [exact A18|]. split; [exact A20|]. split; [exact A23 | exact I].
- split; [|exact HRA3].
  unfold sh_ok, cts_SH. constructor; [|constructor].
  apply (cts_shent W3 mem3 E ch HRA3 Hcham ltac:(lia) ltac:(lia));
  [ subst E; exact (eq_trans (cts_E_reg regs3 regs FL 20 20%bv eq_refl) Hs4)
  | subst E; exact (eq_trans (cts_E_reg regs3 regs FL 23 23%bv eq_refl) Hs7) ].
Qed.
(* The want buffer at F + 32: its granule is the frame map's live slot (shadow byte 4 of the frame is
   0), so the whole 8-byte slot is usable, and the shadow window the wrapper reads is the frame's own
   eight shadow bytes. *)
Lemma cts_want_ok : forall (W2 : world tfibsegs) mem2 Fa m,
YI00.garr8 tfibsegs (mrestrict (w_H W2) mem2) (shadow_addr Fa) cts_shm_live ->
Fa mod 64 = 0 -> 0 <= Fa -> 0 <= m <= 8 ->
range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (Fa + 32) m /\
(0 < m -> shadow_hull_vis (aview tfibsegs (w_H W2) mem2) (Fa + 32) m).
Proof.
intros W2 mem2 Fa m HFSH HA64 HFa Hm.
destruct (proj1 (Z.mod_divide Fa 64 ltac:(lia)) HA64) as (kk & Hkk).
assert (HFd : Fa / 8 = 8 * kk) by (rewrite Hkk; replace (kk * 64) with (8 * kk * 8) by lia;
  apply Z.div_mul; lia).
assert (Hgr : forall x, Fa + 32 <= x < Fa + 40 -> x / 8 = Fa / 8 + 4).
{ intros x Hx. rewrite HFd. replace x with (8 * (8 * kk + 4) + (x - Fa - 32)) by lia.
  rewrite Z.mul_comm, Z.div_add_l by lia. rewrite (Z.div_small (x - Fa - 32) 8) by lia. lia. }
assert (Hsh : forall j, (j < 8)%nat ->
  mbyte tfibsegs (mrestrict (w_H W2) mem2) (shadow_addr Fa + Z.of_nat j)
  = Some (Z_to_bv 8 (nth j cts_shm_live 0))).
{ intros j Hj. apply (garr8_mbyte tfibsegs _ _ cts_shm_live j HFSH). cbn [length cts_shm_live]. lia. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. rewrite (Hgr x ltac:(lia)).
  replace (SHADOW_OFF + (Fa / 8 + 4)) with (shadow_addr Fa + Z.of_nat 4)
    by (unfold shadow_addr; cbn [Z.of_nat]; lia).
  unfold aview. rewrite (Hsh 4%nat ltac:(lia)). vm_compute. reflexivity.
- intros Hm0 s Hs. unfold shadow_addr in Hs.
  rewrite (Hgr (Fa + 32) ltac:(lia)), (Hgr (Fa + 32 + m - 1) ltac:(lia)) in Hs.
  rewrite HFd in Hs.
  assert (HS8 : (SHADOW_OFF + (8 * kk + 4)) / 8 * 8 = SHADOW_OFF + 8 * kk).
  { unfold SHADOW_OFF.
    replace (2147450880 + (8 * kk + 4)) with ((268431360 + kk) * 8 + 4) by lia.
    rewrite (Z.div_add_l (268431360 + kk) 8 4 ltac:(lia)).
    rewrite (Z.div_small 4 8) by lia. lia. }
  rewrite HS8 in Hs.
  assert (Hj : exists j, (j < 8)%nat /\ s = shadow_addr Fa + Z.of_nat j).
  { exists (Z.to_nat (s - (SHADOW_OFF + 8 * kk))). split; [lia|].
    unfold shadow_addr. rewrite HFd. lia. }
  destruct Hj as (j & Hj8 & ->). unfold aview. rewrite (Hsh j Hj8). discriminate.
Qed.

(* a byte's value, read back *)
Lemma cts_u8 : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof.
intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact Hv.
Qed.
(* the frame's shadow as the frame setup left it (the frame map), writable for the release *)
Definition cts_fsh_region : YP09.region :=
  YP09.mkRegion (Some 24%nat) 0 8 0 8
    (map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SLit (nth j cts_shm_live 0)))) (seq 0 8)).
End d.
End b.
