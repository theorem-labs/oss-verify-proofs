(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step ItabOk.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require Import SpecFrame SpecLeib WalkL Init SegL FxOut.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St.
Open Scope Z_scope.
Unset Lia Cache.

Module PrintfFmt2.

Definition PCS : list int := pcs_from 442744%uint63 8192%nat.
Definition ITABW : itab := Eval vm_compute in build_itab asegs PCS IMap.empty.
Lemma ITABW_eq : build_itab asegs PCS IMap.empty = ITABW.
Proof. vm_cast_no_check (eq_refl ITABW). Qed.
Lemma ITABW_ok : itab_ok asegs ITABW.
Proof. exact (ItabOk.build_itab_ok_of_eq asegs PCS ITABW ITABW_eq). Qed.

Definition ROOMP : Z := 1280.
Definition ENTRYP : int := 472032%uint63.
Definition STOPP : int := 473832%uint63.
Definition FUELP : positive := 32768%positive.
Definition FACTSP : list fact := [FRange 1%uint63 (wlit 6483968%uint63) (wlit 9223372036854775807%uint63)].

Definition SLOTS (RA FMT : int) : list (Z * sv) :=
  [(-640, VL wzero); (-632, VL wzero);
   (-600, VP 125%uint63 wzero); (-592, VP 124%uint63 wzero); (-584, VP 123%uint63 wzero); (-576, VP 122%uint63 wzero);
   (-568, VP 121%uint63 wzero); (-560, VP 120%uint63 wzero); (-552, VP 119%uint63 wzero);
   (-544, VL wzero); (-536, VL (wlit FMT)); (-528, VP 1%uint63 (Z2w (-56))); (-520, VL (wlit 472176%uint63));
   (-112, VP 118%uint63 wzero); (-104, VP 109%uint63 wzero); (-96, VP 108%uint63 wzero); (-88, VL (wlit 472096%uint63));
   (-72, VL (wlit RA))].
Definition REGS : list (r5 * sv) :=
  [(X2, VP 1%uint63 (Z2w (-640))); (X18, VP 1%uint63 (Z2w (-512))); (X3, VP 103%uint63 wzero); (X4, VP 104%uint63 wzero);
   (X26, VP 126%uint63 wzero); (X27, VP 127%uint63 wzero)].
Definition finP (RA FMT : int) (LEN : nat) (st : sstate) : bool :=
  PrimInt63.eqb (s_pc st) STOPP
  && match s_resv st with RNone => true | _ => false end
  && forallb (fun p => sv_eqb (rf_get (s_rf st) (fst p)) (snd p)) REGS
  && forallb (fun p => FxOut.slot_ok asegs st (VP 1%uint63 (Z2w (fst p))) (snd p)) (SLOTS RA FMT)
  && FxOut.text_ok asegs st 1%uint63 (-512) LEN.

Notation checkP RA FMT LEN xf :=
  (WalkL.wcheck asegs ITABW [STOPP] ROOMP SegL.IMGLO SegL.IMGHI FUELP (finP RA FMT LEN) 6%nat (WInit.wstate ROOMP ENTRYP xf SegL.FFP FACTSP 400%uint63)).

Definition RA1 : int := 270948%uint63.   Definition FMT1 : int := 131897%uint63.
Definition XF1 : rf sv := RF (VL wzero) (VL (wlit RA1)) (VP 1%uint63 wzero) (VP 103%uint63 wzero) (VP 104%uint63 wzero) (VP 105%uint63 wzero) (VP 106%uint63 wzero) (VP 107%uint63 wzero) (VP 108%uint63 wzero) (VP 109%uint63 wzero) (VL (wlit FMT1)) (VL (wlit 139268%uint63)) (VP 112%uint63 wzero) (VP 113%uint63 wzero) (VP 114%uint63 wzero) (VP 115%uint63 wzero) (VP 116%uint63 wzero) (VP 117%uint63 wzero) (VP 118%uint63 wzero) (VP 119%uint63 wzero) (VP 120%uint63 wzero) (VP 121%uint63 wzero) (VP 122%uint63 wzero) (VP 123%uint63 wzero) (VP 124%uint63 wzero) (VP 125%uint63 wzero) (VP 126%uint63 wzero) (VP 127%uint63 wzero) (VP 128%uint63 wzero) (VP 129%uint63 wzero) (VP 130%uint63 wzero) (VP 131%uint63 wzero).
Lemma check1 : checkP RA1 FMT1 33%nat XF1 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Definition RA2 : int := 271064%uint63.   Definition FMT2 : int := 138878%uint63.
Definition XF2 (c sz : int) : rf sv := RF (VL wzero) (VL (wlit RA2)) (VP 1%uint63 wzero) (VP 103%uint63 wzero) (VP 104%uint63 wzero) (VP 105%uint63 wzero) (VP 106%uint63 wzero) (VP 107%uint63 wzero) (VP 108%uint63 wzero) (VP 109%uint63 wzero) (VL (wlit FMT2)) (VL (wlit 4096%uint63)) (VL (wlit c)) (VL (wlit sz)) (VP 114%uint63 wzero) (VP 115%uint63 wzero) (VP 116%uint63 wzero) (VP 117%uint63 wzero) (VP 118%uint63 wzero) (VP 119%uint63 wzero) (VP 120%uint63 wzero) (VP 121%uint63 wzero) (VP 122%uint63 wzero) (VP 123%uint63 wzero) (VP 124%uint63 wzero) (VP 125%uint63 wzero) (VP 126%uint63 wzero) (VP 127%uint63 wzero) (VP 128%uint63 wzero) (VP 129%uint63 wzero) (VP 130%uint63 wzero) (VP 131%uint63 wzero).
Lemma check2_1 : checkP RA2 FMT2 63%nat (XF2 1%uint63 32%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_2 : checkP RA2 FMT2 63%nat (XF2 2%uint63 64%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_3 : checkP RA2 FMT2 63%nat (XF2 3%uint63 96%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_4 : checkP RA2 FMT2 64%nat (XF2 4%uint63 128%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_5 : checkP RA2 FMT2 64%nat (XF2 5%uint63 160%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_6 : checkP RA2 FMT2 64%nat (XF2 6%uint63 192%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_7 : checkP RA2 FMT2 64%nat (XF2 7%uint63 224%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_8 : checkP RA2 FMT2 64%nat (XF2 8%uint63 256%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_9 : checkP RA2 FMT2 64%nat (XF2 9%uint63 288%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_10 : checkP RA2 FMT2 65%nat (XF2 10%uint63 320%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_11 : checkP RA2 FMT2 65%nat (XF2 11%uint63 352%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_12 : checkP RA2 FMT2 65%nat (XF2 12%uint63 384%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_13 : checkP RA2 FMT2 65%nat (XF2 13%uint63 416%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_14 : checkP RA2 FMT2 65%nat (XF2 14%uint63 448%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_15 : checkP RA2 FMT2 65%nat (XF2 15%uint63 480%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_16 : checkP RA2 FMT2 65%nat (XF2 16%uint63 512%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_17 : checkP RA2 FMT2 65%nat (XF2 17%uint63 768%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_18 : checkP RA2 FMT2 66%nat (XF2 18%uint63 1024%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_19 : checkP RA2 FMT2 66%nat (XF2 19%uint63 1536%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_20 : checkP RA2 FMT2 66%nat (XF2 20%uint63 2048%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_21 : checkP RA2 FMT2 66%nat (XF2 21%uint63 3072%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_22 : checkP RA2 FMT2 66%nat (XF2 22%uint63 4096%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_23 : checkP RA2 FMT2 66%nat (XF2 23%uint63 6144%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_24 : checkP RA2 FMT2 66%nat (XF2 24%uint63 8192%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_25 : checkP RA2 FMT2 67%nat (XF2 25%uint63 12288%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_26 : checkP RA2 FMT2 67%nat (XF2 26%uint63 16384%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_27 : checkP RA2 FMT2 67%nat (XF2 27%uint63 24576%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_28 : checkP RA2 FMT2 67%nat (XF2 28%uint63 32768%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_29 : checkP RA2 FMT2 67%nat (XF2 29%uint63 49152%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_30 : checkP RA2 FMT2 67%nat (XF2 30%uint63 65536%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_31 : checkP RA2 FMT2 64%nat (XF2 31%uint63 64%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma check2_all : forall c, 1 <= c < K_NUM_CLASSES ->
  exists (ci szi : int) (len : nat), to_Z ci = c /\ to_Z szi = size_of_class c /\ Z.of_nat len = exh_len2 c /\ (1 <= len <= 400)%nat
    /\ checkP RA2 FMT2 len (XF2 ci szi) = true.
Proof.
  intros c Hc. unfold K_NUM_CLASSES in Hc.
  assert (D : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/ c = 31) by lia.
  destruct D as [->|D]. { exists 1%uint63, 32%uint63, 63%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_1]. }
  destruct D as [->|D]. { exists 2%uint63, 64%uint63, 63%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_2]. }
  destruct D as [->|D]. { exists 3%uint63, 96%uint63, 63%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_3]. }
  destruct D as [->|D]. { exists 4%uint63, 128%uint63, 64%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_4]. }
  destruct D as [->|D]. { exists 5%uint63, 160%uint63, 64%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_5]. }
  destruct D as [->|D]. { exists 6%uint63, 192%uint63, 64%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_6]. }
  destruct D as [->|D]. { exists 7%uint63, 224%uint63, 64%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_7]. }
  destruct D as [->|D]. { exists 8%uint63, 256%uint63, 64%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_8]. }
  destruct D as [->|D]. { exists 9%uint63, 288%uint63, 64%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_9]. }
  destruct D as [->|D]. { exists 10%uint63, 320%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_10]. }
  destruct D as [->|D]. { exists 11%uint63, 352%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_11]. }
  destruct D as [->|D]. { exists 12%uint63, 384%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_12]. }
  destruct D as [->|D]. { exists 13%uint63, 416%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_13]. }
  destruct D as [->|D]. { exists 14%uint63, 448%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_14]. }
  destruct D as [->|D]. { exists 15%uint63, 480%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_15]. }
  destruct D as [->|D]. { exists 16%uint63, 512%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_16]. }
  destruct D as [->|D]. { exists 17%uint63, 768%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_17]. }
  destruct D as [->|D]. { exists 18%uint63, 1024%uint63, 66%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_18]. }
  destruct D as [->|D]. { exists 19%uint63, 1536%uint63, 66%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_19]. }
  destruct D as [->|D]. { exists 20%uint63, 2048%uint63, 66%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_20]. }
  destruct D as [->|D]. { exists 21%uint63, 3072%uint63, 66%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_21]. }
  destruct D as [->|D]. { exists 22%uint63, 4096%uint63, 66%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_22]. }
  destruct D as [->|D]. { exists 23%uint63, 6144%uint63, 66%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_23]. }
  destruct D as [->|D]. { exists 24%uint63, 8192%uint63, 66%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_24]. }
  destruct D as [->|D]. { exists 25%uint63, 12288%uint63, 67%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_25]. }
  destruct D as [->|D]. { exists 26%uint63, 16384%uint63, 67%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_26]. }
  destruct D as [->|D]. { exists 27%uint63, 24576%uint63, 67%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_27]. }
  destruct D as [->|D]. { exists 28%uint63, 32768%uint63, 67%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_28]. }
  destruct D as [->|D]. { exists 29%uint63, 49152%uint63, 67%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_29]. }
  destruct D as [->|D]. { exists 30%uint63, 65536%uint63, 67%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_30]. }
  subst c. exists 31%uint63, 64%uint63, 64%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_31].
Qed.
End PrintfFmt2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ItabOk.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import SpecFrame.TwinB SpecLeib.TwinB WalkL.TwinB Init.TwinB SegL.TwinB FxOut.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St.
Open Scope Z_scope.
Unset Lia Cache.

Module PrintfFmt2.

Definition PCS : list int := pcs_from 445192%uint63 8192%nat.
Definition ITABW : itab := Eval vm_compute in build_itab bsegs PCS IMap.empty.
Lemma ITABW_eq : build_itab bsegs PCS IMap.empty = ITABW.
Proof. vm_cast_no_check (eq_refl ITABW). Qed.
Lemma ITABW_ok : itab_ok bsegs ITABW.
Proof. exact (ItabOk.build_itab_ok_of_eq bsegs PCS ITABW ITABW_eq). Qed.

Definition ROOMP : Z := 1280.
Definition ENTRYP : int := 474480%uint63.
Definition STOPP : int := 476280%uint63.
Definition FUELP : positive := 32768%positive.
Definition FACTSP : list fact := [FRange 1%uint63 (wlit 6492160%uint63) (wlit 9223372036854775807%uint63)].

Definition SLOTS (RA FMT : int) : list (Z * sv) :=
  [(-640, VL wzero); (-632, VL wzero);
   (-600, VP 125%uint63 wzero); (-592, VP 124%uint63 wzero); (-584, VP 123%uint63 wzero); (-576, VP 122%uint63 wzero);
   (-568, VP 121%uint63 wzero); (-560, VP 120%uint63 wzero); (-552, VP 119%uint63 wzero);
   (-544, VL wzero); (-536, VL (wlit FMT)); (-528, VP 1%uint63 (Z2w (-56))); (-520, VL (wlit 474624%uint63));
   (-112, VP 118%uint63 wzero); (-104, VP 109%uint63 wzero); (-96, VP 108%uint63 wzero); (-88, VL (wlit 474544%uint63));
   (-72, VL (wlit RA))].
Definition REGS : list (r5 * sv) :=
  [(X2, VP 1%uint63 (Z2w (-640))); (X18, VP 1%uint63 (Z2w (-512))); (X3, VP 103%uint63 wzero); (X4, VP 104%uint63 wzero);
   (X26, VP 126%uint63 wzero); (X27, VP 127%uint63 wzero)].
Definition finP (RA FMT : int) (LEN : nat) (st : sstate) : bool :=
  PrimInt63.eqb (s_pc st) STOPP
  && match s_resv st with RNone => true | _ => false end
  && forallb (fun p => sv_eqb (rf_get (s_rf st) (fst p)) (snd p)) REGS
  && forallb (fun p => FxOut.TwinB.FxOut.slot_ok bsegs st (VP 1%uint63 (Z2w (fst p))) (snd p)) (SLOTS RA FMT)
  && FxOut.TwinB.FxOut.text_ok bsegs st 1%uint63 (-512) LEN.

Notation checkP RA FMT LEN xf :=
  (WalkL.TwinB.WalkL.wcheck bsegs ITABW [STOPP] ROOMP SegL.TwinB.SegL.IMGLO SegL.TwinB.SegL.IMGHI FUELP (finP RA FMT LEN) 6%nat (WInit.wstate ROOMP ENTRYP xf SegL.TwinB.SegL.FFP FACTSP 400%uint63)).

Definition RA1 : int := 273396%uint63.   Definition FMT1 : int := 132096%uint63.
Definition XF1 : rf sv := RF (VL wzero) (VL (wlit RA1)) (VP 1%uint63 wzero) (VP 103%uint63 wzero) (VP 104%uint63 wzero) (VP 105%uint63 wzero) (VP 106%uint63 wzero) (VP 107%uint63 wzero) (VP 108%uint63 wzero) (VP 109%uint63 wzero) (VL (wlit FMT1)) (VL (wlit 139426%uint63)) (VP 112%uint63 wzero) (VP 113%uint63 wzero) (VP 114%uint63 wzero) (VP 115%uint63 wzero) (VP 116%uint63 wzero) (VP 117%uint63 wzero) (VP 118%uint63 wzero) (VP 119%uint63 wzero) (VP 120%uint63 wzero) (VP 121%uint63 wzero) (VP 122%uint63 wzero) (VP 123%uint63 wzero) (VP 124%uint63 wzero) (VP 125%uint63 wzero) (VP 126%uint63 wzero) (VP 127%uint63 wzero) (VP 128%uint63 wzero) (VP 129%uint63 wzero) (VP 130%uint63 wzero) (VP 131%uint63 wzero).
Lemma check1 : checkP RA1 FMT1 33%nat XF1 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Definition RA2 : int := 273512%uint63.   Definition FMT2 : int := 139036%uint63.
Definition XF2 (c sz : int) : rf sv := RF (VL wzero) (VL (wlit RA2)) (VP 1%uint63 wzero) (VP 103%uint63 wzero) (VP 104%uint63 wzero) (VP 105%uint63 wzero) (VP 106%uint63 wzero) (VP 107%uint63 wzero) (VP 108%uint63 wzero) (VP 109%uint63 wzero) (VL (wlit FMT2)) (VL (wlit 4096%uint63)) (VL (wlit c)) (VL (wlit sz)) (VP 114%uint63 wzero) (VP 115%uint63 wzero) (VP 116%uint63 wzero) (VP 117%uint63 wzero) (VP 118%uint63 wzero) (VP 119%uint63 wzero) (VP 120%uint63 wzero) (VP 121%uint63 wzero) (VP 122%uint63 wzero) (VP 123%uint63 wzero) (VP 124%uint63 wzero) (VP 125%uint63 wzero) (VP 126%uint63 wzero) (VP 127%uint63 wzero) (VP 128%uint63 wzero) (VP 129%uint63 wzero) (VP 130%uint63 wzero) (VP 131%uint63 wzero).
Lemma check2_1 : checkP RA2 FMT2 63%nat (XF2 1%uint63 32%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_2 : checkP RA2 FMT2 63%nat (XF2 2%uint63 64%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_3 : checkP RA2 FMT2 63%nat (XF2 3%uint63 96%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_4 : checkP RA2 FMT2 64%nat (XF2 4%uint63 128%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_5 : checkP RA2 FMT2 64%nat (XF2 5%uint63 160%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_6 : checkP RA2 FMT2 64%nat (XF2 6%uint63 192%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_7 : checkP RA2 FMT2 64%nat (XF2 7%uint63 224%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_8 : checkP RA2 FMT2 64%nat (XF2 8%uint63 256%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_9 : checkP RA2 FMT2 64%nat (XF2 9%uint63 288%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_10 : checkP RA2 FMT2 65%nat (XF2 10%uint63 320%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_11 : checkP RA2 FMT2 65%nat (XF2 11%uint63 352%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_12 : checkP RA2 FMT2 65%nat (XF2 12%uint63 384%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_13 : checkP RA2 FMT2 65%nat (XF2 13%uint63 416%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_14 : checkP RA2 FMT2 65%nat (XF2 14%uint63 448%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_15 : checkP RA2 FMT2 65%nat (XF2 15%uint63 480%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_16 : checkP RA2 FMT2 65%nat (XF2 16%uint63 512%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_17 : checkP RA2 FMT2 65%nat (XF2 17%uint63 768%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_18 : checkP RA2 FMT2 66%nat (XF2 18%uint63 1024%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_19 : checkP RA2 FMT2 66%nat (XF2 19%uint63 1536%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_20 : checkP RA2 FMT2 66%nat (XF2 20%uint63 2048%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_21 : checkP RA2 FMT2 66%nat (XF2 21%uint63 3072%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_22 : checkP RA2 FMT2 66%nat (XF2 22%uint63 4096%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_23 : checkP RA2 FMT2 66%nat (XF2 23%uint63 6144%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_24 : checkP RA2 FMT2 66%nat (XF2 24%uint63 8192%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_25 : checkP RA2 FMT2 67%nat (XF2 25%uint63 12288%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_26 : checkP RA2 FMT2 67%nat (XF2 26%uint63 16384%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_27 : checkP RA2 FMT2 67%nat (XF2 27%uint63 24576%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_28 : checkP RA2 FMT2 67%nat (XF2 28%uint63 32768%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_29 : checkP RA2 FMT2 67%nat (XF2 29%uint63 49152%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_30 : checkP RA2 FMT2 67%nat (XF2 30%uint63 65536%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma check2_31 : checkP RA2 FMT2 64%nat (XF2 31%uint63 64%uint63) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma check2_all : forall c, 1 <= c < K_NUM_CLASSES ->
  exists (ci szi : int) (len : nat), to_Z ci = c /\ to_Z szi = size_of_class c /\ Z.of_nat len = exh_len2 c /\ (1 <= len <= 400)%nat
    /\ checkP RA2 FMT2 len (XF2 ci szi) = true.
Proof.
  intros c Hc. unfold K_NUM_CLASSES in Hc.
  assert (D : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/ c = 31) by lia.
  destruct D as [->|D]. { exists 1%uint63, 32%uint63, 63%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_1]. }
  destruct D as [->|D]. { exists 2%uint63, 64%uint63, 63%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_2]. }
  destruct D as [->|D]. { exists 3%uint63, 96%uint63, 63%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_3]. }
  destruct D as [->|D]. { exists 4%uint63, 128%uint63, 64%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_4]. }
  destruct D as [->|D]. { exists 5%uint63, 160%uint63, 64%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_5]. }
  destruct D as [->|D]. { exists 6%uint63, 192%uint63, 64%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_6]. }
  destruct D as [->|D]. { exists 7%uint63, 224%uint63, 64%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_7]. }
  destruct D as [->|D]. { exists 8%uint63, 256%uint63, 64%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_8]. }
  destruct D as [->|D]. { exists 9%uint63, 288%uint63, 64%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_9]. }
  destruct D as [->|D]. { exists 10%uint63, 320%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_10]. }
  destruct D as [->|D]. { exists 11%uint63, 352%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_11]. }
  destruct D as [->|D]. { exists 12%uint63, 384%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_12]. }
  destruct D as [->|D]. { exists 13%uint63, 416%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_13]. }
  destruct D as [->|D]. { exists 14%uint63, 448%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_14]. }
  destruct D as [->|D]. { exists 15%uint63, 480%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_15]. }
  destruct D as [->|D]. { exists 16%uint63, 512%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_16]. }
  destruct D as [->|D]. { exists 17%uint63, 768%uint63, 65%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_17]. }
  destruct D as [->|D]. { exists 18%uint63, 1024%uint63, 66%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_18]. }
  destruct D as [->|D]. { exists 19%uint63, 1536%uint63, 66%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_19]. }
  destruct D as [->|D]. { exists 20%uint63, 2048%uint63, 66%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_20]. }
  destruct D as [->|D]. { exists 21%uint63, 3072%uint63, 66%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_21]. }
  destruct D as [->|D]. { exists 22%uint63, 4096%uint63, 66%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_22]. }
  destruct D as [->|D]. { exists 23%uint63, 6144%uint63, 66%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_23]. }
  destruct D as [->|D]. { exists 24%uint63, 8192%uint63, 66%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_24]. }
  destruct D as [->|D]. { exists 25%uint63, 12288%uint63, 67%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_25]. }
  destruct D as [->|D]. { exists 26%uint63, 16384%uint63, 67%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_26]. }
  destruct D as [->|D]. { exists 27%uint63, 24576%uint63, 67%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_27]. }
  destruct D as [->|D]. { exists 28%uint63, 32768%uint63, 67%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_28]. }
  destruct D as [->|D]. { exists 29%uint63, 49152%uint63, 67%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_29]. }
  destruct D as [->|D]. { exists 30%uint63, 65536%uint63, 67%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_30]. }
  subst c. exists 31%uint63, 64%uint63, 64%nat. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| exact check2_31].
Qed.
End PrintfFmt2.
End TwinB.
