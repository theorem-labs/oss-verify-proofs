(* io_send_seg_frm: what the parse of the frame gives the image-A walk of io_send (lib/A/Prog/io_send_cg.v).

   The inlined spec_read_frame (0x82dc8 - 0x83294) fills io_send's struct spec_frame f from the frame bytes, and
   check_sent_frame's model call (lib/A/Prog/io_send_segs.v ios_m_arm) says the parse succeeded. This file reads
   that off, model-side only:
   - ios_sf_code: the parse code is SPEC_OK (check_sent_frame_m's first test, fuzz_transport.c:405);
   - ios_len60: the frame is at least SPEC_MIN_FRAME = 60 bytes (its length test, :417-419), which is what keeps
     every pointer the parse builds into the frame inside it;
   - ios_fields: at code 0 the struct's fields are fuzz_frame's reading of the bytes (lib/Spec/DgnLib.v
     spec_read_frame_fr), with the bounds of lib/Spec/DgnSpec.v fr_code_ok: 30 <= len, the ethertype 0x885f and
     16 <= numbytes <= len - 14. The walk reads each field out of this list and compares it with the value its
     checked loads built.
   - ios_body_len: f.body = 30 and the body list ios_body frame (lib/A/Prog/io_send_segs.v) is the frame from 30 on,
     so body_len <= length body: every body byte the count loop and the memcpy read lies in the frame. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs.
Import ListNotations.
Open Scope Z_scope.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.

(* The parse succeeded: check_sent_frame_m's first test (:405) is false. *)
Lemma ios_sf_code : forall B frame B',
  TC.check_sent_frame_m B frame = Some (B', tt) -> DSpec.sf_code (TC.rf frame) = DSpec.SPEC_OK.
Proof.
  intros B frame B' H.
  destruct (Z.eqb_spec (DSpec.sf_code (TC.rf frame)) DSpec.SPEC_OK) as [E|E]; [exact E|].
  exfalso. unfold TC.check_sent_frame_m in H. cbv zeta in H.
  rewrite (proj2 (Z.eqb_neq _ _) E) in H. cbn [negb orb] in H. cbv beta iota in H. discriminate H.
Qed.

(* The length test (:417-419): len is 60 or the body's end, so the frame is at least SPEC_MIN_FRAME bytes. *)
Lemma ios_len60 : forall B frame B',
  TC.check_sent_frame_m B frame = Some (B', tt) -> 60 <= Z.of_nat (length frame).
Proof.
  intros B frame B' H. unfold TC.check_sent_frame_m in H. cbv zeta in H.
  match type of H with context [if ?c then None else _] => destruct c eqn:C1 end;
    cbv beta iota in H; [discriminate H|].
  match type of H with context [if ?c then None else _] => destruct c eqn:C2 end;
    cbv beta iota in H; [discriminate H|].
  apply orb_false_iff in C2. destruct C2 as [C2 _].
  apply orb_false_iff in C2. destruct C2 as [C2 _].
  apply negb_false_iff, Z.eqb_eq in C2. rewrite C2.
  destruct (DSpec.SPEC_BODY_AT + DSpec.sf_body_len (TC.rf frame) <? TC.SPEC_MIN_FRAME) eqn:Cn;
    [ apply Z.ltb_lt in Cn | apply Z.ltb_ge in Cn ];
    unfold TC.SPEC_MIN_FRAME, DSpec.SPEC_BODY_AT in *; lia.
Qed.

(* At code 0 the struct's fields are fuzz_frame's reading of the bytes, with fr_code_ok's bounds. *)
Lemma ios_fields : forall frame, DSpec.sf_code (TC.rf frame) = DSpec.SPEC_OK ->
  (30 <= length frame)%nat /\ DSpec.fr_ethertype frame = 0x885f /\
  16 <= DSpec.fr_numbytes frame /\ DSpec.fr_numbytes frame <= Z.of_nat (length frame) - 14 /\
  DSpec.sf_dst (TC.rf frame) = 0 /\ DSpec.sf_src (TC.rf frame) = 6 /\
  DSpec.sf_ethertype (TC.rf frame) = DSpec.fr_ethertype frame /\
  DSpec.sf_numbytes (TC.rf frame) = DSpec.fr_numbytes frame /\
  DSpec.sf_sum (TC.rf frame) = DSpec.fr_sum frame /\
  DSpec.sf_send (TC.rf frame) = DSpec.fr_send frame /\
  DSpec.sf_ack (TC.rf frame) = DSpec.fr_ack frame /\
  DSpec.sf_retry (TC.rf frame) = DSpec.fr_retry frame /\
  DSpec.sf_cmd (TC.rf frame) = DSpec.fr_cmd frame /\
  DSpec.sf_ncmds (TC.rf frame) = DSpec.fr_ncmds frame /\
  DSpec.sf_body (TC.rf frame) = 30 /\
  DSpec.sf_body_len (TC.rf frame) = DSpec.fr_body_len frame /\
  DSpec.sf_pad_len (TC.rf frame) = DSpec.fr_pad_len frame /\
  DSpec.sf_body_sum (TC.rf frame) = DSpec.fr_body_sum frame.
Proof.
  intros frame HOK.
  destruct (DLib.spec_read_frame_fr (TW.zs frame) frame (DLib.holds_body_map frame)) as (HC & HFLD).
  change (DSpec.spec_read_frame (TW.zs frame) (Z.of_nat (length frame))) with (TC.rf frame) in HC, HFLD.
  assert (HFC : DSpec.fr_code frame = 0) by (rewrite <- HC; exact HOK).
  destruct (DSpec.fr_code_ok frame HFC) as (HL30 & HET & HNB1 & HNB2).
  specialize (HFLD HFC). cbv zeta in HFLD.
  destruct HFLD as (Fdst & Fsrc & Fet & Fnb & Fsum & Fsend & Fack & Fretry & Fcmd & Fncmds & Fbody & Fblen &
                    Fpad & Fbsum).
  repeat (split; [first [exact HL30 | exact HET | exact HNB1 | exact HNB2 | exact Fdst | exact Fsrc | exact Fet
                        | exact Fnb | exact Fsum | exact Fsend | exact Fack | exact Fretry | exact Fcmd
                        | exact Fncmds | exact Fbody | exact Fblen | exact Fpad] |]).
  exact Fbsum.
Qed.

(* The body list is the frame from offset 30 on, and the body's length is numbytes - 16, so every body byte lies in
   the frame: the count loop's and the display's reads stay inside [p, p + len). *)
Lemma ios_body_len : forall frame, DSpec.sf_code (TC.rf frame) = DSpec.SPEC_OK ->
  ios_body frame = skipn 30 frame /\
  Z.of_nat (length (ios_body frame)) = Z.of_nat (length frame) - 30 /\
  0 <= ios_blen frame /\ ios_blen frame <= Z.of_nat (length (ios_body frame)).
Proof.
  intros frame HOK.
  destruct (ios_fields frame HOK) as (HL30 & _ & HNB1 & HNB2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fbody &
                                      Fblen & _).
  assert (EB : ios_body frame = skipn 30 frame).
  { unfold ios_body. rewrite Fbody. reflexivity. }
  split; [exact EB|].
  assert (EL : Z.of_nat (length (ios_body frame)) = Z.of_nat (length frame) - 30)
    by (rewrite EB, length_skipn; lia).
  split; [exact EL|].
  unfold ios_blen. rewrite Fblen. unfold DSpec.fr_body_len. rewrite EL. lia.
Qed.
