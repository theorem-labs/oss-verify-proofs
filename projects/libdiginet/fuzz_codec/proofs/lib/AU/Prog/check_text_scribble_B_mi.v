(* Segment M of check_text_scribble's walk in image B (fuzz_codec.asan-ubsan 0x83dbc), its two inner boundaries and the
   facts its three parts share:
     M1  0x83ff4 .. 0x84000  __asan_memset (ch, 0xa5, 24) (the runtime's contract), 0x84004 .. 0x84010 a0 = q, a1 = ch,
                             a2 = n, jal diginet_scribble_text: to the callee's entry 0x86500 (bs_cut .. PC_C1).
     M2  0x86500             diginet_scribble_text through its contract; 0x84014 bne a0,s10 not taken (the bytes used
                             are the owed ones), 0x84018 .. 0x84024 a0 = ch, a1 = want, a2 = n, jal the compare
                             wrapper: to its entry 0x42430 (bs_cut .. PC_C2).
     M3  0x42430             the compare wrapper through its contract: equal; 0x84028 bnez a0 not taken, the UBSan
                             check of ch + n (0x84030), n <> 24, the setup of the fuzz_all loop: to 0x84098.
   Each inner boundary is a bs_cut (check_text_scribble_B_inv.v) with its own facts: the registers the call takes and
   the bytes of the record and of want. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_base check_text_scribble_B_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition PC_C1 : Z := 0x86500.     (* diginet_scribble_text, called from 0x84010 *)
Definition PC_C2 : Z := 0x42430.     (* the compare wrapper, called from 0x84024 *)
Definition B_MEMSET : Z := 0x51f84.  (* __asan_memset, called from 0x84000 *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws tfibsegs B.

(* at the entry of diginet_scribble_text: ra = 0x84014, a0 = q, a1 = ch, a2 = n, s4 = ch, s10 = the bytes used, the
   record 24 bytes 0xa5, want the owed text *)
Definition P_C1 (g : bs_ctx) (pos : Z) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 =>
    getr regs2 1 = w64 0x84014 /\ getr regs2 10 = w64 (bs_q g) /\ getr regs2 11 = w64 (bs_ch g) /\
    getr regs2 12 = w64 (bs_n g) /\ getr regs2 20 = w64 (bs_ch g) /\ getr regs2 26 = w64 (snd (bs_owe g)) /\
    garr8 tfibsegs (rd W2 mem2) (bs_ch g) (repeat 165 24) /\
    garr8 tfibsegs (rd W2 mem2) (bs_F g pos + 32) (fst (bs_owe g)).
(* at the entry of the compare wrapper: ra = 0x84028, a0 = ch, a1 = want, a2 = n, s4 = ch, the record scribble_bytes,
   want the owed text *)
Definition P_C2 (g : bs_ctx) (pos : Z) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 =>
    getr regs2 1 = w64 0x84028 /\ getr regs2 10 = w64 (bs_ch g) /\ getr regs2 11 = w64 (bs_F g pos + 32) /\
    getr regs2 12 = w64 (bs_n g) /\ getr regs2 20 = w64 (bs_ch g) /\
    garr8 tfibsegs (rd W2 mem2) (bs_ch g) (scribble_bytes (bs_tb g) (bs_n g)) /\
    garr8 tfibsegs (rd W2 mem2) (bs_F g pos + 32) (fst (bs_owe g)).

(* a byte the caller's journal lets it write stays so with more blocks and own frames at the same addresses *)
Lemma bsm_awr_mono : forall STK sp0 FP bl0 blc blc' ly ly' own own' a,
  awr_byte STK sp0 FP bl0 blc ly own a ->
  (forall b m, In (b, m) blc -> In (b, m) blc') -> incl own own' -> (forall c p, frame_addr ly' c p = frame_addr ly c p) ->
  awr_byte STK sp0 FP bl0 blc' ly' own' a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own own' a [H|[(H1 & bb & mm & Hin & Hr)|[(bb & mm & Hin & Hn & Hr)|(cid & ps & Hin & Hr)]]] Hb Hown Efa.
- left. exact H.
- right; left. split; [exact H1|]. exists bb, mm. split; [exact (Hb bb mm Hin) | exact Hr].
- right; right; left. exists bb, mm. split; [exact (Hb bb mm Hin)|]. split; [exact Hn | exact Hr].
- right; right; right. exists cid, ps. split; [exact (Hown _ Hin)|]. rewrite !Efa. exact Hr.
Qed.

(* what a boundary carries, at a later state (a call's post or a run) whose registers of bs_common are the same and
   whose bytes of the save area, the frame and the frame's shadow are the same *)
Lemma bsm_common_keep : forall g pos regs2 mem2 (W2 : world tfibsegs) regs3 mem3 (W3 : world tfibsegs),
  bs_common g pos regs2 mem2 W2 ->
  getr regs3 8 = getr regs2 8 -> getr regs3 2 = getr regs2 2 -> getr regs3 9 = getr regs2 9 ->
  getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 -> getr regs3 18 = getr regs2 18 ->
  getr regs3 24 = getr regs2 24 -> getr regs3 22 = getr regs2 22 -> getr regs3 23 = getr regs2 23 ->
  getr regs3 25 = getr regs2 25 -> getr regs3 19 = getr regs2 19 -> getr regs3 21 = getr regs2 21 ->
  getr regs3 27 = getr regs2 27 ->
  (forall a, (bs_sp g - 96 <= a < bs_sp g) \/ (bs_F g pos <= a < bs_F g pos + 64) \/
     (SB + bs_F g pos / 8 <= a < SB + bs_F g pos / 8 + 8) -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  bs_common g pos regs3 mem3 W3.
Proof.
intros g pos regs2 mem2 W2 regs3 mem3 W3 HC E8 E2 E9 E3 E4 E18 E24 E22 E23 E25 E19 E21 E27 KE.
destruct HC as (R8 & R2 & R9 & R3 & R4 & R18 & R24 & R22 & R23 & R25 & R19 & R21 & R27 & V1 & V2 & V3 & V4 & V5 & V6 &
  V7 & V8 & V9 & V10 & V11 & V12 & Hfl & Hsh).
split; [rewrite E8; exact R8|]. split; [rewrite E2; exact R2|]. split; [rewrite E9; exact R9|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. split; [rewrite E18; exact R18|].
split; [rewrite E24; exact R24|]. split; [rewrite E22; exact R22|]. split; [rewrite E23; exact R23|].
split; [rewrite E25; exact R25|]. split; [rewrite E19; exact R19|]. split; [rewrite E21; exact R21|].
split; [rewrite E27; exact R27|].
repeat (split; [apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [intros x Hx; apply KE; left; cbn in Hx; lia | assumption]|]).
split.
- apply (bs_rdword_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hfl]. intros x Hx. apply KE. right; left. lia.
- apply (bs_garr8_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hsh]. intros x Hx. cbn [length BS_FRAME_SHADOW] in Hx.
  change (Z.of_nat 8) with 8 in Hx. apply KE. right; right. lia.
Qed.
End h.
End d.
