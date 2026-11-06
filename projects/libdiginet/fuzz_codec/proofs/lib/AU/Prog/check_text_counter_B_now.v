(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the proof of cpg_stack_malloc_keep_io is the text of lib/Reusable/YC85.v's
   aj_stack_malloc_atS (copied there from proofs/libreac/fuzz_knock/lib/Reusable/YC85.v, origin/ossv/recipes
   4b6f0df50aa7), with the runtime contract's kept-memory clause and the model clause carried to the post, for
   libdiginet/fuzz_codec's ASan build (image A); the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalkFrame.v, with its module paths and module names changed; 176 of its 217 lines of code are new or changed and 447 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/owed_counter_text_B_now.v, with its module paths and module names changed; 41 of its 74 lines of code are new or changed and 184 lines of the source are left out. *)
(* check_text_counter at image B: cc_now (lib/AU/Prog/check_text_counter_B_inv.v) from the contract's premises. The
   text, the record and dt each lie in one object of the call state (cobj_ok). At a boundary state the text's bytes
   are kept (it meets no byte of the write set), the usable marks of the three are kept and their shadow windows
   are readable (check_text_scribble_B_now.v's object lemmas). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP09 YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCeh YCem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_now.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_counter_B_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variables SEG7TBL GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis LAWS : AR_laws tfibsegs B.

(* The record and dt hold no byte of the shadow map's range. *)
Lemma cc_wr_off_shadow : forall g, cc_pre B SEG7TBL GLYPHA ROSTRS g -> forall a, SB <= a < SB + 2 ^ 44 -> ~ cc_wr g a.
Proof.
intros g Hpre a Ha Hw.
destruct Hpre as ((HJ & _) & _ & _ & _ & _ & _ & _ & Hsg & _ & _ & _ & Hdt & _).
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hsg as (_ & _ & Htsg & _). destruct Hdt as (_ & _ & Htdt & _).
destruct Hw as [Hw | Hw].
- destruct (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ _ _ a HAR Htsg Hw) as (_ & Hz).
  unfold SB, kLowShadowBeg, kHighMemBeg in *. lia.
- destruct (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ _ _ a HAR Htdt Hw) as (_ & Hz).
  unfold SB, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma cc_now_of : forall g, cc_pre B SEG7TBL GLYPHA ROSTRS g -> cc_now B g.
Proof.
intros g Hpre pos ly2 S2 W2 mem2 md2 HJ2 HK Hperm _.
pose proof Hpre as ((HJ & _) & _ & Hcs & Hoq & Hosg & Hodt & _ & Hsg & _ & _ & _ & Hdt & _ & _ & Hdqs & Hdqd & _).
pose proof HJ as (HAR & Hlyc & _ & _ & _ & Hfrsc & _). pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _).
assert (Hbl : forall b m, In (b, m) (ablocks B (cc_lyc g) (cc_Sc g)) -> In (b, m) (ablocks B ly2 S2))
  by (intros b m Hin; exact (Permutation_in _ (Permutation_sym Hperm) Hin)).
assert (Hfr : forall c q, In (c, q) (frames (cc_Sc g)) -> In (c, q) (frames S2))
  by (intros c q Hin; rewrite Hfrs2, <- app_comm_cons; right; rewrite <- Hfrsc; exact Hin).
assert (Efa : forall c q, frame_addr ly2 c q = frame_addr (cc_lyc g) c q).
{ intros c q. unfold frame_addr.
  destruct Hly2 as (_ & _ & _ & _ & _ & E1 & _). destruct Hlyc as (_ & _ & _ & _ & _ & E2 & _).
  rewrite E1, E2. reflexivity. }
pose proof (cc_wr_off_shadow g Hpre) as Hws.
destruct Hcs as (_ & Hg & Hz0 & (_ & _ & _ & Hra & _)).
assert (Hlen : 0 < cc_len g) by (unfold cc_len; destruct (cc_tb g) as [|x t]; [destruct Hz0 | cbn [length]; lia]).
split; [|split; split].
- split; [|split].
  + apply (bs_obj_garr8 B TB_check_text_counter (cc_lyc g) (cc_Sc g) (cc_W g) (cc_memc g) W2 mem2 (cc_sp g) (cc_wr g)
      (cc_q g) (cc_tb g) HK (bs_cobj_tdst B _ _ _ _ Hoq)); [|exact Hg].
    intros a Ha Hw. unfold cc_wr, cc_len in *. lia.
  + exact (bs_obj_ra B LAWS TB_check_text_counter _ _ _ _ _ ly2 S2 W2 mem2 md2 _ _ _ _ HAR HAR2 Hbl HK
      (bs_cobj_tdst B _ _ _ _ Hoq) Hws Hra).
  + exact (bs_obj_hull B LAWS (cc_lyc g) (cc_Sc g) ly2 S2 W2 mem2 md2 (cc_q g) (cc_len g) HAR2 Hbl Hfr Efa Hoq Hlen).
- destruct Hsg as (_ & _ & Htd & _ & Hra' & _).
  exact (bs_obj_ra B LAWS TB_check_text_counter _ _ _ _ _ ly2 S2 W2 mem2 md2 _ _ _ _ HAR HAR2 Hbl HK Htd Hws Hra').
- exact (bs_obj_hull B LAWS (cc_lyc g) (cc_Sc g) ly2 S2 W2 mem2 md2 (cc_sg g) 24 HAR2 Hbl Hfr Efa Hosg ltac:(lia)).
- destruct Hdt as (_ & _ & Htd & _ & Hra' & _).
  exact (bs_obj_ra B LAWS TB_check_text_counter _ _ _ _ _ ly2 S2 W2 mem2 md2 _ _ _ _ HAR HAR2 Hbl HK Htd Hws Hra').
- exact (bs_obj_hull B LAWS (cc_lyc g) (cc_Sc g) ly2 S2 W2 mem2 md2 (cc_dt g) 1 HAR2 Hbl Hfr Efa Hodt ltac:(lia)).
Qed.
End h.
End d.
