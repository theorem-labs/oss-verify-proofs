(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths and module names changed; 830 of its 891 lines of code are new or changed and 1078 lines of the source are left out. *)
(* io_send_seg_fly: the frame in flight, the tail 0x83338 .. 0x83384 of the image-A walk of io_send
   (the statement is lib/A/Prog/io_send_cg.v transport_io_send_cg_holds_stmt, entry 0x82d60 = TImgA.v
   ti_io_send timg_A; the cuts are lib/A/Prog/io_send_seg_cut.v, the model lib/A/Prog/io_send_segs.v and the
   world lemmas lib/A/Prog/io_send_seg_world.v).

   The stretch (io_send_cg.v:144-149, fuzz_transport.c:883-889), from transport_text + IOS_FLY to
   transport_text + IOS_EPI:
     +0x5d8 .. +0x5ec  a0 = M (0x5df160), a1 = 1, a2 = f.send (the 4-byte load at sp + 40), a3 = g_now
                       (the 8-byte load at 0x5df100);
     +0x5f0 .. +0x60c  the 4-byte store of 1 at M + 96 (M.fly.on), the 1-byte store of s5 (f.cmd) at M + 100,
                       the 4-byte store of f.send at M + 104, the 4-byte store of 0 at M + 108, a1 = 1514,
                       the 8-byte store of g_now at M + 112;
     +0x610            `bltu s0, a1`: s0 = len stays when len < 1514, else s0 = 1514 (+0x614), so s0 is
                       min (len, 1514) = io_send_segs.v ios_flen;
     +0x618 .. +0x61c  the 8-byte store of s0 at M + 1640 (M.fly.len), a0 = M + 120 (M.fly.frame, 0x5df1d8);
     +0x620            a1 = p, a2 = s0, `jal` __asan_memcpy (transport_sigma TS___asan_memcpy), return
                       address transport_text + IOS_EPI.
   None of the six stores has an instrumented check (each is at a constant address of G), and the load at
   sp + 40 is sp-relative, so the run carries no shadow entry (IFLY_SH = []).

   The segment is one lemma, ios_fly_seg, in continuation form, with its own premises, so it does not wait on
   the other segments. It runs two symbolic runs of lib/A/Prog/PaShadow.v over the walk's G journal
   (TransportGRunA.v paj_run_x; the write obligation of each store closes with W_journalG.v awr_ok_x_cons_g,
   every written byte being a byte of M's payload and so of G), one per arm of the branch, and lifts the call
   of __asan_memcpy with TransportGCg.v gx_intrin_at (d = M + 120, n = ios_flen frame, x = p). The world it
   leaves is io_send_segs.v `ios_fly frame Bx`, built field by field with io_send_seg_world.v's ios_tw_start /
   ios_tw_step / ios_tw_fill / ios_tw_end, each stored value read back from the chunks of the run's last state
   and from the intrinsic's post. The bytes it writes are bytes of io_send_cg.v iosend_wr (io_send_seg_world.v
   ios_wr_fly_on .. ios_wr_fly_frame), so the walk's running acall_kept_g extends by TransportGCg.v
   dk_kept_step_g. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  io_send_cg io_send_segs io_send_seg_cut io_send_seg_world.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the cut                                       *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the cut, 32 the shadow base, 33 f.send (the 4 bytes at sp + 40 of the
   struct spec_frame), 34 g_now (the 8 bytes at 0x5df100). Regions: the struct's int f.send and g_now, read
   only, and the six fields of M the stretch stores (M is the listing's image object 8, g_now object 27). *)
Definition ifly_f_region : YP09.region := YP09.mkRegion (Some 2%nat) 40 44 0 0 [YP09.mkChunk 40 (CVal 4 (SOff 33 0))].
Definition ifly_now_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 27)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition ifly_on_region : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 96 100 96 100 [].
Definition ifly_cmd_region : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 100 101 100 101 [].
Definition ifly_cnt_region : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 104 108 104 108 [].
Definition ifly_ret_region : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 108 112 108 112 [].
Definition ifly_sent_region : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 112 120 112 120 [].
Definition ifly_len_region : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 1640 1648 1640 1648 [].
Definition ifly_regions : smem :=
  [ifly_f_region; ifly_now_region; ifly_on_region; ifly_cmd_region; ifly_cnt_region; ifly_ret_region;
   ifly_sent_region; ifly_len_region].
Definition ifly_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (A_OBJ 8, mkAF TA_M TA_M 5); (A_OBJ 27, mkAF TA_g_now TA_g_now 5)] [] [].
Definition ss_ifly : sstate := mkSS IOS_FLY sr_atoms ifly_regions None ifly_facts.
(* No instrumented check in the stretch: the run needs no shadow entry. *)
Definition IFLY_SH : list shent := [].
Definition IFLY_Bx : sv := SOff 32 0.

(* The destination of the copy: M.fly.frame. *)
Definition IFLY_D : Z := TA_M + 120.

(* The bytes of M's payload the stretch may store, field by field (the padding at M + 101 .. M + 103 is not
   one of them). *)
Definition ifly_W (a : Z) : Prop :=
  (TA_M + 96 <= a < TA_M + 100) \/ (TA_M + 100 <= a < TA_M + 101) \/ (TA_M + 104 <= a < TA_M + 108) \/
  (TA_M + 108 <= a < TA_M + 112) \/ (TA_M + 112 <= a < TA_M + 120) \/ (TA_M + 1640 <= a < TA_M + 1648).

(* ------------------------------------------------------------------ *)
(* Bytes                                                               *)
(* ------------------------------------------------------------------ *)

(* Byte j < w <= 8 of a 64-bit word holding v is byte j of the w-byte little-endian v. *)
Lemma ifly_bow : forall v (w j : nat), (j < w)%nat -> (w <= 8)%nat ->
  bv_unsigned (byte_of_word (Z_to_bv 64 v) (Z.of_nat j)) = YO0f.le_byte v w j.
Proof.
intros v w j Hj Hw. unfold byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). change (2 ^ Z.of_N 64) with (2 ^ 64). change 256 with (2 ^ 8).
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* A signed wrap does not change the low bytes. *)
Lemma ifly_swrap_mod : forall (n : N) z, bv_swrap n z mod 2 ^ Z.of_N n = z mod 2 ^ Z.of_N n.
Proof.
intros n z. unfold bv_swrap, bv_wrap, bv_modulus. rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma ifly_le_byte_swrap : forall (n : N) (w j : nat) v, Z.of_N n = 8 * Z.of_nat w ->
  YO0f.le_byte (bv_swrap n v) w j = YO0f.le_byte v w j.
Proof.
intros n w j v Hn. unfold YO0f.le_byte. rewrite <- Hn, ifly_swrap_mod. reflexivity.
Qed.

Lemma ifly_Forall_nth : forall {A : Type} (P : A -> Prop) (l : list A) (n : nat) (x : A),
  Forall P l -> nth_error l n = Some x -> P x.
Proof. intros A P l n x HF Hn. rewrite Forall_forall in HF. apply HF. exact (nth_error_In l n Hn). Qed.

(* ------------------------------------------------------------------ *)
(* G                                                                   *)
(* ------------------------------------------------------------------ *)

Lemma ifly_inM : forall a, TA_M <= a < TA_M + 1648 -> inG TG.G_HARNESS a.
Proof.
intros a Ha. apply (ios_inG_row _ _ _ a TMAP_A_M). unfold TW.SZ_M. lia.
Qed.

(* min (len, 1514), the length the tail stores and copies. *)
Lemma ifly_flen : forall frame,
  0 <= ios_flen frame <= TC.SPEC_MAX_FRAME /\ ios_flen frame <= Z.of_nat (length frame) /\
  ios_flen frame = Z.min (Z.of_nat (length frame)) TC.SPEC_MAX_FRAME.
Proof.
intros frame. pose proof (Zle_0_nat (length frame)) as H0. unfold ios_flen.
destruct (Z.ltb_spec (Z.of_nat (length frame)) TC.SPEC_MAX_FRAME) as [Hl|Hl];
  unfold TC.SPEC_MAX_FRAME in *; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The world the tail leaves                                           *)
(* ------------------------------------------------------------------ *)

(* ios_fly frame Bx, field by field: the six stores and the copy, every other payload byte unchanged. *)
Lemma ifly_world : forall (frame Bx : list byte) (rd0 rdF : Z -> option Z) (flen : Z),
  tw_at TMAP_A rd0 Bx -> flen = ios_flen frame ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall j, (j < 1)%nat ->
     rdF (TA_M + 100 + Z.of_nat j) = Some (YO0f.le_byte (DSpec.sf_cmd (TC.rf frame)) 1 j)) ->
  (forall j, (j < 4)%nat ->
     rdF (TA_M + 104 + Z.of_nat j) = Some (YO0f.le_byte (DSpec.sf_send (TC.rf frame)) 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 108 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 8)%nat -> rdF (TA_M + 112 + Z.of_nat j) = Some (YO0f.le_byte (TW.g_now Bx) 8 j)) ->
  (forall j, (j < 8)%nat -> rdF (TA_M + 1640 + Z.of_nat j) = Some (YO0f.le_byte flen 8 j)) ->
  (forall i, 0 <= i < flen ->
     rdF (TA_M + 120 + i) =
       Some (bv_unsigned (nth (Z.to_nat i) (firstn (Z.to_nat flen) frame) (Z_to_bv 8 0)))) ->
  (forall x, tw_in TMAP_A x ->
     ~ (TA_M + 96 <= x < TA_M + 100) -> ~ (TA_M + 100 <= x < TA_M + 101) ->
     ~ (TA_M + 104 <= x < TA_M + 108) -> ~ (TA_M + 108 <= x < TA_M + 112) ->
     ~ (TA_M + 112 <= x < TA_M + 120) -> ~ (TA_M + 1640 <= x < TA_M + 1648) ->
     ~ (TA_M + 120 <= x < TA_M + 120 + flen) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (ios_fly frame Bx).
Proof.
intros frame Bx rd0 rdF flen Htw Hflen V96 V100 V104 V108 V112 V1640 VFR Hk.
destruct (ifly_flen frame) as (HF1 & HF2 & _).
assert (HMX : TC.SPEC_MAX_FRAME = 1514) by reflexivity. rewrite HMX in HF1.
assert (SM : TW.SZ_M = 1648) by reflexivity.
assert (HLs : length (firstn (Z.to_nat flen) frame) = Z.to_nat flen)
  by (apply firstn_length_le; lia).
unfold ios_fly. rewrite <- Hflen.
unfold TW.set_M_fly_frame, TW.set_M_fly_len, TW.set_M_fly_sent, TW.set_M_fly_retries, TW.set_M_fly_counter,
  TW.set_M_fly_cmd, TW.set_M_fly_on, TW.A_M_fly_frame, TW.A_M_fly_len, TW.A_M_fly_sent, TW.A_M_fly_retries,
  TW.A_M_fly_counter, TW.A_M_fly_cmd, TW.A_M_fly_on.
pose proof (ios_tw_start rdF rd0 Bx Htw) as H0.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 96 (TW.OFF_M + 96 + 0) 4 1 H0 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V96) as H1.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 100 (TW.OFF_M + 96 + 4) 1
  (DSpec.sf_cmd (TC.rf frame)) H1 TMAP_A_M ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V100) as H2.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 104 (TW.OFF_M + 96 + 8) 4
  (DSpec.sf_send (TC.rf frame)) H2 TMAP_A_M ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V104) as H3.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 108 (TW.OFF_M + 96 + 12) 4 0 H3 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V108) as H4.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 112 (TW.OFF_M + 96 + 16) 8 (TW.g_now Bx) H4
  TMAP_A_M ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V112) as H5.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 1640 (TW.OFF_M + 96 + 1544) 8 flen H5 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V1640) as H6.
pose proof (ios_tw_fill rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 120 (TW.OFF_M + 96 + 24)
  (firstn (Z.to_nat flen) frame) H6 TMAP_A_M ltac:(lia) ltac:(lia) ltac:(rewrite HLs; lia)
  ltac:(rewrite HLs; intros i Hi; apply VFR; lia)) as H7.
rewrite HLs in H7. rewrite Z2Nat.id in H7 by lia.
apply (ios_tw_end rdF rd0 _ _ H7).
intros x Hx HP. ios_unP HP. apply Hk; (exact Hx || lia).
Qed.

(* ------------------------------------------------------------------ *)
(* Tactics                                                             *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac ifly_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx
      (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ifly_reg: no match for" T; fail
  end.

(* The windows a run wrote, each inside the bytes Zs. *)
Ltac ifly_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write rights of a run from a state with ifly_regions: the two read-only regions have no writable byte,
   the six fields of M are bytes of G. *)
Ltac ifly_awr UME :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (first
    [ apply awr_ok_x_cons_g;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
        rewrite UME in Ha; apply ifly_inM; lia |]
    | apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |] ]);
  apply awr_ok_x_nil.

Section ifly. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma ifly_vals : VAL (A_OBJ 8) = TA_M /\ VAL (A_OBJ 27) = TA_g_now /\ BASE = transport_text.
Proof. vm_compute. repeat split. Qed.

(* The w bytes of a chunk of value v, read through the view. *)
Lemma ifly_chunk_rd : forall (E : env) (H : word -> bool) (mm : word -> option byte) (base off : Z)
    (wN : N) (wn : nat) (e : sv) (v : Z),
  Z.of_N wN = Z.of_nat wn -> (wn <= 8)%nat ->
  YP09.chunk_ok segs E (mrestrict H mm) base (YP09.mkChunk off (CVal wN e)) ->
  sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < wn)%nat -> aview segs H mm (base + off + Z.of_nat j) = Some (YO0f.le_byte v wn j).
Proof.
intros E H mm base off wN wn e v HwN Hwn HC He j Hj. unfold YP09.chunk_ok in HC.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC.
destruct (HC (Z.of_nat j) ltac:(lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview segs H mm (base + off + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict H mm) (base + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. f_equal. apply ifly_bow; [exact Hj | exact Hwn].
Qed.

(* The value of a sign-extended load of wn bytes. *)
Lemma ifly_sext_den : forall (E : env) (n : nat) (wN : N) (wn : nat) (u : Z),
  ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 64 -> Z.of_N wN = 8 * Z.of_nat wn ->
  (0 < wn)%nat -> (wn <= 8)%nat ->
  sv_denot E (SExt true wN (SOff n 0)) = Z_to_bv 64 (bv_swrap wN u).
Proof.
intros E n wN wn u Hn Hu HwN Hwn0 Hwn. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 wN (Z_to_bv 64 u)))
  with (Z_to_bv 64 (bv_signed (bv_extract 0 wN (Z_to_bv 64 u)))).
f_equal. rewrite (LMem.signed_of_extract wN (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The copy's destination [M + 120, M + 120 + n): M's payload has shadow 0, so every byte is addressable, and
   the shadow bytes of its hull are M's and the six guard granules after M (trans_iosend_cells). *)
Lemma ifly_dest_ra : forall ly S (W : world segs) mem md (n : Z),
  trans_iosend_cells B -> @AR rc segs B ly S W mem md -> 0 < n <= 1514 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF IFLY_D n.
Proof.
intros ly S W mem md n [_ [HZ _]] HAR Hn x Hx.
assert (EM : TA_M = 6156640) by reflexivity. assert (SM : TW.SZ_M = 1648) by reflexivity.
unfold IFLY_D in Hx.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold shadow_of_addr. exists 0. split; [|left; reflexivity].
assert (Hz := decode_zshadow_rd B ly S W mem md TA_M (TA_M + TW.SZ_M) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma ifly_dest_hull : forall ly S (W : world segs) mem md (n : Z),
  trans_iosend_cells B -> @AR rc segs B ly S W mem md -> 0 < n <= 1514 ->
  shadow_hull_vis (aview segs (w_H W) mem) IFLY_D n.
Proof.
intros ly S W mem md n HC HAR Hn s Hs.
destruct HC as [_ [HZ HG]].
assert (EM : TA_M = 6156640) by reflexivity. assert (SM : TW.SZ_M = 1648) by reflexivity.
assert (EB : shadow_addr IFLY_D / 8 * 8 = 2148220472) by reflexivity.
assert (Hhi : shadow_addr (IFLY_D + n - 1) / 8 * 8 + 8 <= 2148220672).
{ unfold shadow_addr, SHADOW_OFF.
  assert (Hq1 : (IFLY_D + n - 1) / 8 < 769785)
    by (apply Z.div_lt_upper_bound; [lia | unfold IFLY_D; lia]).
  assert (Hq0 : 0 <= (IFLY_D + n - 1) / 8)
    by (apply Z.div_pos; [unfold IFLY_D; lia | lia]).
  assert (Hr1 : (2147450880 + (IFLY_D + n - 1) / 8) / 8 <= 268527583)
    by (apply Z.div_le_upper_bound; lia).
  assert (Hr0 : 0 <= (2147450880 + (IFLY_D + n - 1) / 8) / 8) by (apply Z.div_pos; lia).
  lia. }
rewrite EB in Hs.
assert (Hslo : 2148220472 <= s) by lia. assert (Hshi : s < 2148220672) by lia.
destruct (Z_lt_le_dec s 2148220666) as [Hlt|Hge].
- (* a shadow byte of M's payload: its granule's shadow is 0 *)
  assert (Hz := decode_zshadow_rd B ly S W mem md TA_M (TA_M + TW.SZ_M) (8 * (s - 2147450880)) HAR
    ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
  replace s with (FCells.shadow_addr (8 * (s - 2147450880))); [rewrite Hz; discriminate|].
  unfold FCells.shadow_addr, FCells.ASAN_K. rewrite Z.mul_comm, Z.div_mul by lia. lia.
- (* one of the six guard granules after M, a constant cell of the record *)
  specialize (HG ly). destruct HAR as (Mm & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c)
    by (intros c Hc; exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mm) c Hc)).
  assert (RD : forall c, In (z1 (ANum c) 0xf9) (as_const B ly) ->
    aview segs (w_H W) mem c = Some 249).
  { intros c Hin. pose proof (CH _ Hin) as Hh.
    unfold cell_holds in Hh. cbn [c_at c_w YG0f.c_val z1 c1 aeval] in Hh.
    specialize (Hh 0%nat ltac:(lia)). cbn [Z.of_nat] in Hh. rewrite Z.add_0_r in Hh.
    change (YG0f.le_byte 249 1 0) with 249 in Hh. exact Hh. }
  destruct HG as (G0 & G1 & G2 & G3 & G4 & G5).
  assert (Hj : s = 2148220666 \/ s = 2148220667 \/ s = 2148220668 \/ s = 2148220669 \/
               s = 2148220670 \/ s = 2148220671) by lia.
  destruct Hj as [-> | [-> | [-> | [-> | [-> | ->]]]]].
  + replace 2148220666 with (FCells.shadow_addr (TA_M + TW.SZ_M)) by reflexivity.
    rewrite (RD _ G0). discriminate.
  + replace 2148220667 with (FCells.shadow_addr (TA_M + TW.SZ_M + 8)) by reflexivity.
    rewrite (RD _ G1). discriminate.
  + replace 2148220668 with (FCells.shadow_addr (TA_M + TW.SZ_M + 16)) by reflexivity.
    rewrite (RD _ G2). discriminate.
  + replace 2148220669 with (FCells.shadow_addr (TA_M + TW.SZ_M + 24)) by reflexivity.
    rewrite (RD _ G3). discriminate.
  + replace 2148220670 with (FCells.shadow_addr (TA_M + TW.SZ_M + 32)) by reflexivity.
    rewrite (RD _ G4). discriminate.
  + replace 2148220671 with (FCells.shadow_addr (TA_M + TW.SZ_M + 40)) by reflexivity.
    rewrite (RD _ G5). discriminate.
Qed.

(* The walk's valuation at the cut: the registers, the shadow base, f.send and g_now. *)
Definition ifly_E (regs2 : bvmap 5 word) (send now : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs2 [w64 SHADOW_OFF; Z_to_bv 64 send; Z_to_bv 64 now]).

Lemma ifly_agree : forall regs2 send now,
  env_agree 32 (Ereg regs2 [w64 SHADOW_OFF; Z_to_bv 64 send; Z_to_bv 64 now]) (ifly_E regs2 send now).
Proof.
intros regs2 send now. split.
- intros n Hn. unfold ifly_E. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity.
- reflexivity.
Qed.

(* The state at the cut, and the (empty) shadow entry. *)
Lemma ifly_entry : forall (W : world segs) (regs2 : bvmap 5 word) mem2 (sp send now : Z),
  YK11.getr regs2 2 = w64 sp -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 ->
  0 <= send < 2 ^ 32 -> 0 <= now < 2 ^ 64 ->
  YI04.val_mem segs (mrestrict (w_H W) mem2) (sp + 40) 4 send ->
  YI04.val_mem segs (mrestrict (w_H W) mem2) (TA_g_now + 0) 8 now ->
  st_ok_pi segs VAL (ifly_E regs2 send now) ss_ifly
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_FLY)) mem2 (YK11.seg_rom segs)))
  /\ sh_ok segs IFLY_Bx IFLY_SH (ifly_E regs2 send now) (mrestrict (w_H W) mem2).
Proof.
intros W regs2 mem2 sp send now H2 Hsp Hsp16 Hsend Hnow Vsend Vnow.
assert (EM : TA_M = 6156640) by reflexivity. assert (EN : TA_g_now = 6156544) by reflexivity.
set (E := ifly_E regs2 send now).
assert (E2 : ew E 2 = YK11.getr regs2 2) by (unfold E, ifly_E; apply ew_Eimg_Ereg_nat; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2, H2; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E, ifly_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 send)
  by (unfold E, ifly_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 now)
  by (unfold E, ifly_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
  by (intros j Hj; unfold E, ifly_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
destruct ifly_vals as (V8 & V27 & _).
assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
  by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
assert (B8 : base_val E (Some (A_OBJ 8)) = TA_M)
  by (apply VB; [rewrite (EOB 8%nat ltac:(lia)), V8; reflexivity | lia]).
assert (B27 : base_val E (Some (A_OBJ 27)) = TA_g_now)
  by (apply VB; [rewrite (EOB 27%nat ltac:(lia)), V27; reflexivity | lia]).
assert (U8 : bv_unsigned (ew E (A_OBJ 8)) = TA_M) by exact B8.
assert (U27 : bv_unsigned (ew E (A_OBJ 27)) = TA_g_now) by exact B27.
split; [|unfold sh_ok, IFLY_SH; constructor].
rewrite restrict_mkst_fx. unfold ss_ifly, ifly_regions.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
    [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]]]].
  + unfold ifly_f_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ sp 40 4 (SOff 33 0) send);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Vsend].
  + unfold ifly_now_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ TA_g_now 0 8 (SOff 34 0) now);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Vnow].
  + unfold ifly_on_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B8. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply ifly_inM. lia.
  + unfold ifly_cmd_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B8. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply ifly_inM. lia.
  + unfold ifly_cnt_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B8. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply ifly_inM. lia.
  + unfold ifly_ret_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B8. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply ifly_inM. lia.
  + unfold ifly_sent_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B8. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply ifly_inM. lia.
  + unfold ifly_len_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B8. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply ifly_inM. lia.
- apply pairwise_disjoint_of_extents.
  unfold ifly_f_region, ifly_now_region, ifly_on_region, ifly_cmd_region, ifly_cnt_region, ifly_ret_region,
    ifly_sent_region, ifly_len_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite B8, B27. cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold ifly_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, U8, U27, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite ?EM, ?EN; reflexivity].
Qed.

(* The callee-saved registers the stretch keeps: every one but s0, which it sets to min (len, 1514). *)
Definition IFLY_KEEP : list (bv 5) := [2; 3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma ifly_nth_firstn : forall (A : Type) (l : list A) (k j : nat) (d : A), (j < k)%nat ->
  nth j (firstn k l) d = nth j l d.
Proof.
intros A l. induction l as [|x l IH]; intros k j d Hj.
- rewrite firstn_nil. destruct j; reflexivity.
- destruct k as [|k]; [lia|]. cbn [firstn]. destruct j as [|j]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

Lemma ifly_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
intros a b Ha Hb. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with 18446744073709551616. rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* The 4 bytes of a chunk of a region of the state, read through the view. *)
Ltac ifly_chunk HS idx c UB wn v tac V :=
  let RG := fresh "RG" in let HC := fresh "HC" in let HC1 := fresh "HCk" in let Hden := fresh "Hden" in
  pose proof (YC4b.st_ok_region_nth _ _ _ idx _ HS eq_refl) as RG;
  cbn [ms_mem restrict] in RG;
  destruct RG as (_ & _ & _ & HC);
  cbn [YP09.r_base YP09.r_chunks base_val] in HC;
  rewrite UB in HC;
  pose proof (ifly_Forall_nth _ _ c _ HC eq_refl) as HC1;
  lazymatch type of HC1 with
  | YP09.chunk_ok _ ?Ex _ _ (YP09.mkChunk _ (CVal ?wN ?e)) =>
      assert (Hden : sv_denot Ex e = Z_to_bv 64 v) by tac;
      pose proof (ifly_chunk_rd _ _ _ _ _ wN wn _ v eq_refl ltac:(lia) HC1 Hden) as V
  end;
  clear HC HC1 Hden.

(* One byte of a garr8 array, read through the view. *)
Lemma ifly_garr_byte : forall (W : world segs) (mem : word -> option byte) (p : Z) (frame : list byte) (i : Z),
  garr8 segs (mrestrict (w_H W) mem) p (map DSpec.bz frame) -> 0 <= i < Z.of_nat (length frame) ->
  aview segs (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) frame (Z_to_bv 8 0))).
Proof.
intros W mem p frame i HG Hi.
assert (Hj : (Z.to_nat i < length (map DSpec.bz frame))%nat) by (rewrite length_map; lia).
destruct (HG (Z.to_nat i) Hj) as [HV HB].
assert (EN : nth (Z.to_nat i) (map DSpec.bz frame) 0 = bv_unsigned (nth (Z.to_nat i) frame (Z_to_bv 8 0))).
{ change 0 with (DSpec.bz (Z_to_bv 8 0)) at 1. apply map_nth. }
rewrite EN in HV, HB.
specialize (HV 0%nat ltac:(lia)). cbn [Z.of_nat] in HV. rewrite !Z.add_0_r in HV.
rewrite Z2Nat.id in HV by lia.
change (aview segs (w_H W) mem (p + i))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict (w_H W) mem) (p + i))).
rewrite HV. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, YO0f.le_byte.
change (2 ^ Z.of_N 8) with 256. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. apply Z.mod_small. exact HB.
Qed.

(* The source of the copy at a later memory: visible, outside the call's ESTACK window, addressable, with its
   shadow hull visible. The shadow bytes of a range below 2 ^ 63 lie above 2147450873. *)
Lemma ifly_src : forall (W : world segs) (memA memB : word -> option byte) (regsR : bvmap 5 word)
    (p n m : Z),
  (forall a, p <= a < p + n -> aview segs (w_H W) memA a <> None) ->
  range_addressable (aview segs (w_H W) memA) SHADOW_OFF p n ->
  shadow_hull_vis (aview segs (w_H W) memA) p n ->
  0 <= p -> p + n <= 2 ^ 63 -> 0 < m -> m <= n ->
  (forall a, p <= a < p + n -> aview segs (w_H W) memB a = aview segs (w_H W) memA a) ->
  (forall a, 2147450873 <= a -> 0 <= a < 2 ^ 64 ->
     aview segs (w_H W) memB a = aview segs (w_H W) memA a) ->
  (forall a, p <= a < p + n -> ~ (spZ regsR - ESTACK <= a < spZ regsR)) ->
  src_ok segs W regsR memB p m /\
  range_addressable (aview segs (w_H W) memB) SHADOW_OFF p m /\
  shadow_hull_vis (aview segs (w_H W) memB) p m.
Proof.
intros W memA memB regsR p n m Hv Hra Hhu Hp0 Hp63 Hm0 Hmn Kin Ksh Hwin.
split; [|split].
- intros a Ha. split; [rewrite (Kin a ltac:(lia)); exact (Hv a ltac:(lia)) | exact (Hwin a ltac:(lia))].
- intros x Hx. destruct (Hra x ltac:(lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as Hp.
  assert (Hub : x / 8 <= 2 ^ 60) by (apply Z.div_le_upper_bound; lia).
  apply Ksh; unfold shadow_of_addr, SHADOW_OFF; lia.
- intros s Hs.
  assert (Hsub : shadow_hull_vis (aview segs (w_H W) memA) p m)
    by (apply (trans_hull_sub _ p n); [exact Hhu | lia | lia]).
  unfold shadow_addr, SHADOW_OFF in Hs.
  pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)) as Hp8.
  assert (Hlo : 268431360 <= (2147450880 + p / 8) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (Hd : (p + m - 1) / 8 <= 2 ^ 60) by (apply Z.div_le_upper_bound; lia).
  pose proof (Z.div_pos (p + m - 1) 8 ltac:(lia) ltac:(lia)) as Hd0.
  pose proof (Z.mul_div_le (2147450880 + (p + m - 1) / 8) 8 ltac:(lia)) as Hml.
  pose proof (Z.div_pos (2147450880 + (p + m - 1) / 8) 8 ltac:(lia) ltac:(lia)) as Hdp.
  rewrite Ksh; [exact (Hsub s Hs) | lia | lia].
Qed.

(* The copy's destination and its source are apart: the frame lies wholly outside G, or wholly inside g_s's
   payload, which begins above M's last byte. *)
Lemma ifly_apart : forall (p n m : Z), iosend_frame_at p n -> 0 < n -> 0 <= m -> m <= 1514 -> m <= n ->
  IFLY_D + m <= p \/ p + m <= IFLY_D.
Proof.
intros p n m Hfr Hn Hm0 Hm1 Hmn.
assert (EM : TA_M = 6156640) by reflexivity. assert (EGS : TA_g_s = 6158784) by reflexivity.
assert (SMW : TW.SZ_g_s = 18264) by reflexivity.
destruct Hfr as [HnG | [HG1 HG2]]; [|left; unfold IFLY_D; lia].
destruct (Z_le_gt_dec (IFLY_D + m) p) as [Hap|Hap]; [left; exact Hap|].
destruct (Z_le_gt_dec (p + m) IFLY_D) as [Hap2|Hap2]; [right; exact Hap2|].
exfalso. apply (HnG (Z.max p IFLY_D) ltac:(unfold IFLY_D in *; lia)).
apply ifly_inM. unfold IFLY_D in *. lia.
Qed.

(* TransportGCg.v dk_kept_step_g with the running world split from the entry world: the walk's kept fact
   compares the CURRENT world W at memY with the ENTRY world Wen at memc (as io_send_seg_cut.v ios_cur states
   it), and the step memX -> memY is taken at W. The proof is dk_kept_step_g's, whose AR is only read for the
   bounds of the caller's blocks and side-stack frames, which are the entry state's. *)
Lemma ifly_kept_step : forall lyc Sc (Wen : world segs) memc mdc (W : world segs) memX memY slo shi
    (Eo Zs : Z -> Prop),
  AR_laws segs B ->
  @AR rc segs B lyc Sc Wen memc mdc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc Wen memc W memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) memY a = aview segs (w_H W) memX a) ->
  (forall a, apresent (w_H W) memX a -> apresent (w_H W) memY a) ->
  (forall a, Zs a -> alloc_ceiling <= a < 2 ^ 64 -> slo <= a < shi) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> Zs (b + i) -> Eo (b + i)) ->
  (forall a, Zs a -> in_img segs a -> ~ inG TG.G_HARNESS a ->
     ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) -> False) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     Zs a -> Eo a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc Wen memc W memY slo shi Eo.
Proof.
intros lyc Sc Wen memc mdc W memX memY slo shi Eo Zs LAWS HAR (K1 & K2 & K3 & K4 & K5 & K6)
  Hkp Hgr HZw HZb HZi HZf.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite Hkp; [apply K1; assumption | lia | intros HZ; exact (Hw (HZw a HZ Ha))].
- intros b m i Hb Hi Hn.
  destruct (al_blocks _ _ LAWS lyc Sc Wen memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
  rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia | intros HZ; exact (Hn (HZb b m i Hb Hi HZ))].
- intros a Hi HnG Hno He. pose proof (transport_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite Hkp; [apply K3; assumption | lia | intros HZ; exact (HZi a HZ Hi HnG Hno He)].
- intros cid pos a Hin Hr Hn.
  destruct (frames_bounds segs B LAWS lyc Sc Wen memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (Ha : 0 <= a < 2 ^ 64).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8)
      by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | exact Ha | intros HZ; exact (Hn (HZf cid pos a Hin Hr HZ))].
- intros a Ha Hw Hp. apply Hgr. apply K5; assumption.
- intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.

(* The walk's running acall_kept_g, extended by the bytes the tail writes: the six fields of M.fly, the
   min (n, 1514) bytes it copies to M.fly.frame (all of them bytes of iosend_wr n) and the bytes of the
   call's ESTACK window, which lies inside io_send's own stack window. *)
Lemma ifly_kept : forall lyc Sc (Wen : world segs) memc mdc (W : world segs) mem2 mem3 (sp n : Z),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS ->
  @AR rc segs B lyc Sc Wen memc mdc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc Wen memc W mem2 (sp - IOSEND_STK) sp (iosend_wr n) ->
  0 <= n -> alloc_ceiling <= sp - IOSEND_STK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ifly_W a ->
     ~ (TA_M + 120 <= a < TA_M + 120 + Z.min n TC.SPEC_MAX_FRAME) ->
     ~ (sp - IOSEND_FRAME - ESTACK <= a < sp - IOSEND_FRAME) ->
     aview segs (w_H W) mem3 a = aview segs (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc Wen memc W mem3 (sp - IOSEND_STK) sp (iosend_wr n).
Proof.
intros lyc Sc Wen memc mdc W mem2 mem3 sp n LAWS HGX HAR HK2 Hn Hce KFIN GFIN.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EST : ESTACK = 4096) by reflexivity.
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (FS : IOSEND_STK = 8496) by reflexivity.
assert (EM : TA_M = 6156640) by reflexivity.
assert (GLOW : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transport_segs_low a (proj1 (HGX a Ha)))).
apply (ifly_kept_step lyc Sc Wen memc mdc W mem2 mem3
  (sp - IOSEND_STK) sp (iosend_wr n)
  (fun a => (sp - IOSEND_STK <= a < sp) \/ iosend_wr n a) LAWS HAR HK2).
- intros a Ha Hw. apply KFIN.
  + exact Ha.
  + intros HW. apply Hw. right. unfold ifly_W in HW.
    destruct HW as [HW | [HW | [HW | [HW | [HW | HW]]]]].
    * exact (ios_wr_fly_on n a ltac:(lia)).
    * exact (ios_wr_fly_cmd n a ltac:(lia)).
    * exact (ios_wr_fly_counter n a ltac:(lia)).
    * exact (ios_wr_fly_retries n a ltac:(lia)).
    * exact (ios_wr_fly_sent n a ltac:(lia)).
    * exact (ios_wr_fly_len n a ltac:(lia)).
  + intros HW. apply Hw. right. apply (ios_wr_fly_frame n a Hn).
    unfold TW.A_M_fly_frame, TW.OFF_M. lia.
  + intros HW. apply Hw. left. lia.
- exact GFIN.
- intros a [Hw|Hw] Hc; [exact Hw|]. exfalso.
  pose proof (GLOW a (ios_wr_inG n a Hw)) as Hl. unfold kLowMemEnd in Hl. lia.
- intros b m i Hb Hi [Hw|Hw]; [|exact Hw]. exfalso.
  destruct (al_blocks _ _ LAWS lyc Sc Wen memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
- intros a [Hw|Hw] Hi HnG _ _.
  + pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
  + apply HnG. exact (ios_wr_inG n a Hw).
- intros cid pos a Hin Hr [Hw|Hw]; [|exact Hw]. exfalso.
  destruct (frames_bounds segs B LAWS lyc Sc Wen memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8)
    by (apply Z.div_le_mono; lia).
  unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

(* The frame in flight: the stretch from the cut IOS_FLY to the cut IOS_EPI, in continuation form. *)
Lemma ios_fly_seg : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (Wen : world segs) memc mdc
    ly2 S2 (W : world segs) mem2 md2 k (regs regs2 : bvmap 5 word) (p : Z) (frame Bx : list byte)
    (Q : world segs -> config -> Prop),
  trans_iosend_cells B -> AR_laws segs B -> gx_ok segs B TG.G_HARNESS ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 []
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc Wen memc mdc k ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 []
    STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem2 md2 k ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc Wen memc W mem2
    (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - IOSEND_STK -> spZ regs <= sp0 ->
  YK11.getr regs2 2 = w64 (spZ regs - IOSEND_FRAME) ->
  YK11.getr regs2 3 = w64 (as_gp B) -> YK11.getr regs2 4 = w64 (as_tp B) ->
  YK11.getr regs2 8 = w64 (Z.of_nat (length frame)) ->
  YK11.getr regs2 9 = w64 p ->
  YK11.getr regs2 21 = w64 (DSpec.sf_cmd (TC.rf frame)) ->
  0 <= DSpec.sf_send (TC.rf frame) < 2 ^ 32 ->
  YI04.val_mem segs (mrestrict (w_H W) mem2) (spZ regs - IOSEND_FRAME + 40) 4
    (DSpec.sf_send (TC.rf frame)) ->
  0 < Z.of_nat (length frame) -> Z.of_nat (length frame) < 2 ^ 32 ->
  garr8 segs (mrestrict (w_H W) mem2) p (map DSpec.bz frame) ->
  trans_src_ok B ly2 S2 W mem2 p (Z.of_nat (length frame)) ->
  decode_off_win regs IOSEND_STK p (Z.of_nat (length frame)) ->
  iosend_frame_at p (Z.of_nat (length frame)) ->
  tw_at TMAP_A (aview segs (w_H W) mem2) Bx ->
  (forall (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model),
     @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 []
       STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem3 md3 k ->
     acall_kept_g segs B TG.G_HARNESS lyc Sc Wen memc W mem3
       (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) ->
     (forall a, 0 <= a < 2 ^ 64 ->
        ~ (TA_M + 96 <= a < TA_M + 120) -> ~ (TA_M + 1640 <= a < TA_M + 1648) ->
        ~ (TA_M + 120 <= a < TA_M + 120 + ios_flen frame) ->
        ~ (spZ regs - IOSEND_FRAME - ESTACK <= a < spZ regs - IOSEND_FRAME) ->
        aview segs (w_H W) mem3 a = aview segs (w_H W) mem2 a) ->
     (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a) ->
     (forall r, acallee_saved r -> r <> 8 ->
        YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)) ->
     YK11.getr regs3 8 = w64 (ios_flen frame) ->
     tw_at TMAP_A (aview segs (w_H W) mem3) (ios_fly frame Bx) ->
     SRr segs W (@cfg_at fx segs (transport_text + IOS_EPI) regs3 mem3 md3) Q) ->
  SRr segs W (@cfg_at fx segs (transport_text + IOS_FLY) regs2 mem2 md2) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc Wen memc mdc ly2 S2 W mem2 md2 k regs regs2 p frame Bx Q
  HCELLS LAWS HGX HAI HJ0 HJ HK2 Hsp16 Hlo Hhi H2 H3 H4 H8 H9 H21 Hsend Vsend Hlen0 Hlen32
  Hgarr Hsrc Hoff Hfr Htw HCONT.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EST : ESTACK = 4096) by reflexivity.
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (FS : IOSEND_STK = 8496) by reflexivity.
assert (EM : TA_M = 6156640) by reflexivity.
assert (EGS : TA_g_s = 6158784) by reflexivity.
assert (ENW : TA_g_now = 6156544) by reflexivity.
assert (SMW : TW.SZ_g_s = 18264) by reflexivity.
assert (HMX : TC.SPEC_MAX_FRAME = 1514) by reflexivity.
destruct (ifly_flen frame) as (HF1 & HF2 & HF3). rewrite HMX in HF1.
(* the entry journal: the AR of the call state, the window, the stack bounds *)
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - IOSEND_STK) by lia.
assert (Hwin : forall a, spZ regs - IOSEND_STK <= a < spZ regs -> apresent (w_H Wen) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (Hsp2 : 2 ^ 46 <= spZ regs - IOSEND_FRAME <= 2 ^ 47) by lia.
assert (Hsp2m : (spZ regs - IOSEND_FRAME) mod 16 = 0).
{ replace (spZ regs - IOSEND_FRAME) with (spZ regs + (-10) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hsp16. }
assert (Hm16 : (spZ regs - IOSEND_FRAME - sp0) mod 16 = 0).
{ rewrite Zminus_mod, Hsp2m, Hsp0a. reflexivity. }
assert (GLOW : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transport_segs_low a (proj1 (HGX a Ha)))).
(* g_now, as the world holds it *)
assert (Vnow : YI04.val_mem segs (mrestrict (w_H W) mem2) (TA_g_now + 0) 8
                 (TW.u_at Bx (TW.OFF_g_now + 0) 8))
  by exact (tw_read_val segs (mrestrict (w_H W) mem2) TMAP_A Bx TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8
    TMAP_A_ok Htw TMAP_A_g_now ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)).
replace (TW.OFF_g_now + 0) with TW.OFF_g_now in Vnow by lia.
assert (Hnow64 : 0 <= TW.g_now Bx < 2 ^ 64).
{ pose proof (TWL.u_at_range Bx TW.OFF_g_now 8) as R. change (8 * Z.of_nat 8) with 64 in R.
  unfold TW.g_now. lia. }
(* the state at the cut *)
destruct (ifly_entry W regs2 mem2 (spZ regs - IOSEND_FRAME) (DSpec.sf_send (TC.rf frame)) (TW.g_now Bx)
  H2 Hsp2 Hsp2m Hsend Hnow64 Vsend Vnow) as [HS SHOK].
set (E0 := ifly_E regs2 (DSpec.sf_send (TC.rf frame)) (TW.g_now Bx)) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ifly_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, ifly_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs - IOSEND_FRAME)
  by (rewrite (EE 2%nat 2%bv eq_refl), H2; apply unsigned_lit_small; lia).
assert (E32 : ew E0 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E0, ifly_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 (DSpec.sf_send (TC.rf frame)))
  by (unfold E0, ifly_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 (TW.g_now Bx))
  by (unfold E0, ifly_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
destruct ifly_vals as (V8 & V27 & VBASE).
assert (UM : bv_unsigned (ew E0 (A_OBJ 8)) = TA_M).
{ unfold E0, ifly_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V8.
  apply unsigned_lit_small. lia. }
assert (UN : bv_unsigned (ew E0 (A_OBJ 27)) = TA_g_now).
{ unfold E0, ifly_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V27.
  apply unsigned_lit_small. lia. }
assert (UM' : bv_unsigned (ew E0 249%nat) = TA_M) by exact UM.
assert (UN' : bv_unsigned (ew E0 268%nat) = TA_g_now) by exact UN.
assert (EM8 : ew E0 249%nat = Z_to_bv 64 TA_M)
  by (apply bv_eq; rewrite UM'; symmetry; apply unsigned_lit_small; lia).
assert (D8 : sv_denot E0 (SOff 8 0) = Z_to_bv 64 (Z.of_nat (length frame))).
{ cbn [sv_denot]. rewrite (EE 8%nat 8%bv eq_refl), H8, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUN.
pose proof (paj_branch (PI := PI_transport)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_FLY)) mem2
    (YK11.seg_rom segs)) md2) Qx) end.
(* run 1, +0x5d8 .. +0x610: a0 = M, a1 = 1, a2 = f.send, a3 = g_now, the five stores, a1 = 1514; it stops at
   `bltu s0, a1`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ifly_awr UM'. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
rename ms into ms1.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ ifly_W a ->
  aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem2 a).
{ intros a Ha H1. apply (kept_of_frame _ _ _ _ _ ifly_W HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. ifly_win Hin Hx ltac:(rewrite ?Usp, ?UM', ?UN' in Hx; unfold ifly_W; lia). }
assert (GA1 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
all: rewrite D8 in Hc.
all: cbn [branch_taken sv_denot] in Hc.
all: rewrite (ifly_ltu (Z.of_nat (length frame)) 1514 ltac:(lia) ltac:(lia)) in Hc.
all: assert (HFL : ios_flen frame =
       (if Z.of_nat (length frame) <? 1514 then Z.of_nat (length frame) else 1514))
     by (unfold ios_flen; rewrite HMX; reflexivity).
all: rewrite Hc in HFL; cbv iota in HFL.
(* run 2, +0x610 .. +0x620: s0 = min (len, 1514), the store at M + 1640, a0 = M + 120, a1 = p, a2 = s0, and
   the call of __asan_memcpy. *)
all: paj_run_tok RUN HS HJ SHOK YC4b.Bspan; [ifly_awr UM' |].
all: set (mdR := with_vm_backing (m_vm_lazy md1) mat md1) in *; clearbody mdR; clear mat;
     rename ms into msR.
all: assert (KAR : forall a, 0 <= a < 2 ^ 64 -> ~ ifly_W a ->
       aview segs (w_H W) (ms_mem msR) a = aview segs (w_H W) mem2 a)
     by (intros a Ha H1; rewrite <- (KA1 a Ha H1);
         apply (kept_of_frame _ _ _ _ _ ifly_W HFr); [| exact Ha | exact H1];
         intros b wlo whi x Hin Hx;
         ifly_win Hin Hx ltac:(rewrite ?Usp, ?UM', ?UN' in Hx; unfold ifly_W; lia)).
all: assert (GAR : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem msR) a)
     by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
all: clear HF HFr HG.
(* the bytes the two runs stored, read from the last state's chunks *)
all: pmkst HS.
all: ifly_chunk HS 2%nat 0%nat UM' 4%nat 1 ltac:(reflexivity) V96.
all: ifly_chunk HS 3%nat 0%nat UM' 1%nat (DSpec.sf_cmd (TC.rf frame))
       ltac:(cbn [sv_denot]; rewrite (EE 21%nat 21%bv eq_refl), H21, Z.add_0_r;
             apply Z_to_bv_bv_unsigned) V100.
all: ifly_chunk HS 4%nat 0%nat UM' 4%nat (bv_swrap 32 (DSpec.sf_send (TC.rf frame)))
       ltac:(apply (ifly_sext_den E0 33 32 4); [exact E33 | lia | reflexivity | lia | lia]) V104.
all: ifly_chunk HS 5%nat 0%nat UM' 4%nat 0 ltac:(reflexivity) V108.
all: ifly_chunk HS 6%nat 0%nat UM' 8%nat (TW.g_now Bx)
       ltac:(first [ cbn [sv_denot]; rewrite E34, Z.add_0_r; apply Z_to_bv_bv_unsigned
                   | rewrite (ifly_sext_den E0 34 64 8 (TW.g_now Bx) E34 Hnow64 eq_refl ltac:(lia)
                       ltac:(lia));
                     f_equal; apply bv_swrap_small; change (bv_half_modulus 64) with (2 ^ 63); lia ]) V112.
all: ifly_chunk HS 7%nat 0%nat UM' 8%nat (ios_flen frame)
       ltac:(rewrite HFL;
             first [ reflexivity
                   | cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), H8, Z.add_0_r;
                     apply Z_to_bv_bv_unsigned ]) V1640.
all: assert (V104' : forall j, (j < 4)%nat ->
       aview segs (w_H W) (ms_mem msR) (TA_M + 104 + Z.of_nat j) =
         Some (YO0f.le_byte (DSpec.sf_send (TC.rf frame)) 4 j))
     by (intros j Hj;
         rewrite <- (ifly_le_byte_swrap 32 4 j (DSpec.sf_send (TC.rf frame)) eq_refl);
         exact (V104 j Hj)).
all: clear V104.
all: rename V104' into V104.
(* the registers at the call *)
all: ifly_reg HS (10%bv : bv 5) (w64 IFLY_D) Qa0
       ltac:(cbn [sv_denot]; rewrite UM'; unfold IFLY_D, w64; reflexivity).
all: ifly_reg HS (11%bv : bv 5) (w64 p) Qa1
       ltac:(cbn [sv_denot]; rewrite (EE 9%nat 9%bv eq_refl), H9, Z.add_0_r; apply Z_to_bv_bv_unsigned).
all: ifly_reg HS (12%bv : bv 5) (w64 (ios_flen frame)) Qa2
       ltac:(rewrite HFL;
             first [ reflexivity
                   | cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), H8, Z.add_0_r;
                     apply Z_to_bv_bv_unsigned ]).
all: ifly_reg HS (8%bv : bv 5) (w64 (ios_flen frame)) Qs0
       ltac:(rewrite HFL;
             first [ reflexivity
                   | cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), H8, Z.add_0_r;
                     apply Z_to_bv_bv_unsigned ]).
all: ifly_reg HS (2%bv : bv 5) (w64 (spZ regs - IOSEND_FRAME)) Qsp
       ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), H2, Z.add_0_r; apply Z_to_bv_bv_unsigned).
all: ifly_reg HS (3%bv : bv 5) (w64 (as_gp B)) Qgp
       ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), H3, Z.add_0_r; apply Z_to_bv_bv_unsigned).
all: ifly_reg HS (4%bv : bv 5) (w64 (as_tp B)) Qtp
       ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), H4, Z.add_0_r; apply Z_to_bv_bv_unsigned).
all: ifly_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + IOS_EPI)) Qra ltac:(apply codeptr_val; exact HEI).
all: assert (KREG : forall r, In r IFLY_KEEP -> YK11.getr (ms_regs msR) r = YK11.getr regs2 r)
     by (apply (regs_kept_of_st_ok _ E0 _ _ regs2
           [w64 SHADOW_OFF; Z_to_bv 64 (DSpec.sf_send (TC.rf frame)); Z_to_bv 64 (TW.g_now Bx)]
           IFLY_KEEP HS (ifly_agree regs2 _ _) ltac:(vm_compute; reflexivity))).
all: assert (Hspr : spZ (ms_regs msR) = spZ regs - IOSEND_FRAME)
     by (unfold spZ at 1; rewrite Qsp; apply unsigned_lit_small; lia).
(* the frame's bytes: never bytes of M, so the two runs kept them *)
all: assert (HFNM : forall a, p <= a < p + Z.of_nat (length frame) -> ~ ifly_W a)
     by (intros a Ha HW; destruct Hfr as [HnG | [HG1 HG2]];
         [ apply (HnG a Ha); apply ifly_inM; unfold ifly_W in HW; lia
         | unfold ifly_W in HW; lia ]).
all: assert (HRD : decode_rd_ok W mem2 p (Z.of_nat (length frame)))
     by exact (trans_src_ok_rd B LAWS ly2 S2 W mem2 md2 p (Z.of_nat (length frame)) HAR2 Hsrc Hlen0).
all: destruct HRD as (HRDv & HRDa & HRDh & HRDm & HRDp & HRDe).
all: assert (KFR : forall a, p <= a < p + Z.of_nat (length frame) ->
       aview segs (w_H W) (ms_mem msR) a = aview segs (w_H W) mem2 a)
     by (intros a Ha; apply KAR; [lia | exact (HFNM a Ha)]).
all: assert (HSRC3 : src_ok segs W (ms_regs msR) (ms_mem msR) p (ios_flen frame) /\
       range_addressable (aview segs (w_H W) (ms_mem msR)) SHADOW_OFF p (ios_flen frame) /\
       shadow_hull_vis (aview segs (w_H W) (ms_mem msR)) p (ios_flen frame))
     by (apply (ifly_src W mem2 (ms_mem msR) (ms_regs msR) p (Z.of_nat (length frame)) (ios_flen frame)
           HRDv HRDa HRDh HRDp HRDe ltac:(lia) ltac:(lia) KFR);
         [ intros a Ha Ha64; apply KAR; [exact Ha64 | unfold ifly_W; lia]
         | rewrite Hspr; unfold decode_off_win in Hoff; intros a Ha; lia ]).
all: destruct HSRC3 as (HSRC & HRAR & HHUR).
all: assert (HAPART : IFLY_D + ios_flen frame <= p \/ p + ios_flen frame <= IFLY_D)
     by (apply (ifly_apart p (Z.of_nat (length frame))); [exact Hfr | lia | lia | lia | lia]).
all: pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARR.
(* +0x620: the call of __asan_memcpy (M + 120, p, min (len, 1514)) *)
all: lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
       change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom)
         mdx) Qx) end.
all: eapply SRr_bind;
     [ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OCpy
         (transport_sigma TS___asan_memcpy) (HAI fx) TG.G_HARNESS W (ms_regs msR) (ms_mem msR)
         STK sp0 FP ly S W0 mem0 md0 own ly2 S2 mdR k
         IFLY_D p (ios_flen frame) (spZ regs - IOSEND_FRAME - sp0) (Z_to_bv 64 (BASE + IOS_EPI))
         HGX G_HARNESS_rw HJ Qa0 Qa1 Qa2);
       [ lia
       | unfold IFLY_D; lia
       | unfold IFLY_D; lia
       | rewrite Hspr; lia
       | exact Hm16
       | lia
       | lia
       | exact Qgp
       | exact Qtp
       | exact Qra
       | apply (ret_ok_codeptr_v (PI := PI_transport));
         [unfold IOS_EPI, IOS_AT, AF_io_send; lia | reflexivity]
       | eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|];
         intros a Ha; right; apply ifly_inM; unfold IFLY_D in Ha; lia
       | left; unfold IFLY_D, kLowMemEnd; lia
       | apply (ifly_dest_ra ly2 S2 W (ms_mem msR) mdR (ios_flen frame) HCELLS HARR ltac:(lia))
       | intros _; apply (ifly_dest_hull ly2 S2 W (ms_mem msR) mdR (ios_flen frame) HCELLS HARR
           ltac:(lia))
       | split; [lia|]; split; [lia|]; split; [exact HSRC|]; split; [exact HAPART|];
         split; [unfold amem_range in HRDm |- *; lia|]; split; [exact HRAR | intros _; exact HHUR] ]
     | ].
all: cbv beta.
all: intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HPR3 & Qd3 & Hset3 & Heff3 & Hgr3).
all: assert (KFIN : forall a, 0 <= a < 2 ^ 64 -> ~ ifly_W a ->
       ~ (TA_M + 120 <= a < TA_M + 120 + ios_flen frame) ->
       ~ (spZ regs - IOSEND_FRAME - ESTACK <= a < spZ regs - IOSEND_FRAME) ->
       aview segs (w_H W) mem3 a = aview segs (w_H W) mem2 a)
     by (intros a Ha HWa HWb HWc; rewrite (Heff3 a Ha ltac:(unfold IFLY_D; lia) ltac:(lia));
         exact (KAR a Ha HWa)).
all: assert (GFIN : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a)
     by (intros a Ha; exact (Hgr3 a (GAR a Ha))).
all: assert (KM : forall a, TA_M <= a < TA_M + 120 \/ TA_M + 1640 <= a < TA_M + 1648 ->
       aview segs (w_H W) mem3 a = aview segs (w_H W) (ms_mem msR) a)
     by (intros a Ha; apply Heff3; [lia | unfold IFLY_D; lia | lia]).
all: assert (WF96 : forall j, (j < 4)%nat ->
       aview segs (w_H W) mem3 (TA_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j))
     by (intros j Hj; rewrite KM by lia; exact (V96 j Hj)).
all: assert (WF100 : forall j, (j < 1)%nat ->
       aview segs (w_H W) mem3 (TA_M + 100 + Z.of_nat j) =
         Some (YO0f.le_byte (DSpec.sf_cmd (TC.rf frame)) 1 j))
     by (intros j Hj; rewrite KM by lia; exact (V100 j Hj)).
all: assert (WF104 : forall j, (j < 4)%nat ->
       aview segs (w_H W) mem3 (TA_M + 104 + Z.of_nat j) =
         Some (YO0f.le_byte (DSpec.sf_send (TC.rf frame)) 4 j))
     by (intros j Hj; rewrite KM by lia; exact (V104 j Hj)).
all: assert (WF108 : forall j, (j < 4)%nat ->
       aview segs (w_H W) mem3 (TA_M + 108 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j))
     by (intros j Hj; rewrite KM by lia; exact (V108 j Hj)).
all: assert (WF112 : forall j, (j < 8)%nat ->
       aview segs (w_H W) mem3 (TA_M + 112 + Z.of_nat j) = Some (YO0f.le_byte (TW.g_now Bx) 8 j))
     by (intros j Hj; rewrite KM by lia; exact (V112 j Hj)).
all: assert (WF1640 : forall j, (j < 8)%nat ->
       aview segs (w_H W) mem3 (TA_M + 1640 + Z.of_nat j) = Some (YO0f.le_byte (ios_flen frame) 8 j))
     by (intros j Hj; rewrite KM by lia; exact (V1640 j Hj)).
all: assert (WFR : forall i, 0 <= i < ios_flen frame ->
       aview segs (w_H W) mem3 (TA_M + 120 + i) =
         Some (bv_unsigned (nth (Z.to_nat i) (firstn (Z.to_nat (ios_flen frame)) frame) (Z_to_bv 8 0))))
     by (intros i Hi;
         replace (TA_M + 120 + i) with (IFLY_D + i) by (unfold IFLY_D; lia);
         rewrite (Hset3 i Hi), (KFR (p + i) ltac:(lia)),
           (ifly_nth_firstn byte frame (Z.to_nat (ios_flen frame)) (Z.to_nat i) (Z_to_bv 8 0) ltac:(lia));
         exact (ifly_garr_byte W mem2 p frame i Hgarr ltac:(lia))).
all: assert (HWF : tw_at TMAP_A (aview segs (w_H W) mem3) (ios_fly frame Bx))
     by (apply (ifly_world frame Bx (aview segs (w_H W) mem2) (aview segs (w_H W) mem3) (ios_flen frame)
           Htw eq_refl WF96 WF100 WF104 WF108 WF112 WF1640 WFR);
         intros x Hx N1 N2 N3 N4 N5 N6 N7;
         pose proof (GLOW x (ios_tw_in_G x Hx)) as Hl; unfold kLowMemEnd in Hl;
         apply KFIN; [lia | unfold ifly_W; lia | lia | lia]).
(* the running kept fact, extended by the bytes the tail wrote *)
all: assert (HK3 : acall_kept_g segs B TG.G_HARNESS lyc Sc Wen memc W mem3
       (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))))
     by (apply (ifly_kept lyc Sc Wen memc mdc W mem2 mem3 (spZ regs) (Z.of_nat (length frame))
           LAWS HGX HAR HK2 ltac:(lia) ltac:(lia));
         [ intros a Ha N1 N2 N3; apply KFIN;
           [exact Ha | exact N1 | rewrite HF3; exact N2 | exact N3]
         | exact GFIN ]).
(* the coarse kept fact and the registers the tail keeps *)
all: assert (KCRS : forall a, 0 <= a < 2 ^ 64 ->
       ~ (TA_M + 96 <= a < TA_M + 120) -> ~ (TA_M + 1640 <= a < TA_M + 1648) ->
       ~ (TA_M + 120 <= a < TA_M + 120 + ios_flen frame) ->
       ~ (spZ regs - IOSEND_FRAME - ESTACK <= a < spZ regs - IOSEND_FRAME) ->
       aview segs (w_H W) mem3 a = aview segs (w_H W) mem2 a)
     by (intros a Ha N1 N2 N3 N4; apply KFIN; [exact Ha | unfold ifly_W; lia | lia | lia]).
all: assert (KRG : forall r, acallee_saved r -> r <> 8 ->
       YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r))
     by (intros r Hr Hr8; rewrite (HPR3 r Hr); apply KREG; unfold IFLY_KEEP; cbn [In];
         unfold acallee_saved in Hr;
         destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]];
         [ | | | exfalso; exact (Hr8 eq_refl) | |
           assert (Hcase : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/
                           r = 25 \/ r = 26 \/ r = 27) by lia;
           repeat (destruct Hcase as [Hcase | Hcase]); subst r ];
         repeat first [left; apply bv_eq; vm_compute; reflexivity | right]).
all: exact (HCONT regs3 mem3 md3 HJ3 HK3 KCRS GFIN KRG
              (eq_trans (HPR3 8 ltac:(unfold acallee_saved; lia)) Qs0) HWF).
Qed.
End ifly.
