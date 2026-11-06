(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v; 507 of its 577 lines of code are new or changed and 960 lines of the source are left out. *)
(* diginet_session_submit_seg_app: Lemma ssw_seg_app, the append of diginet_session_submit (diginet_session.c:345-348)
   from the cut APP (+0xcc, 0x89fbc) of lib/A/Prog/diginet_session_submit_segs.v to the return.

   What the code does (a2 = s2 >> 3 on entry, s2 = &g_s.queued):
     +0xcc .. +0xd8   the shadow check of the 4-byte load at s2 (one granule, shadow 0), a0 = queued;
     +0xdc / +0xe0    `bne a0, 512`;
     +0xe4 / +0xe8    queued = 512: a0 = -5, to the epilogue (+0x118) and the return;
     +0xec .. +0x10c  the shadow check of the store, `sw queued + 1, 0(s2)`, a0 = s + 1760 + 32 queued, a1 = c,
                      a2 = 32, the call of __asan_memcpy at +0x110 (return address +0x114);
     +0x114 .. +0x130 a0 = 0, the epilogue, the return.

   The symbolic state at the cut: the registers as atoms 0 .. 31 (a2, s2, s3 as the cut's registers say), atom 32
   the shadow base, atom 33 the queued count of the world, atoms 34 .. 38 the entry values of s3, s2, s1, s0, ra (the
   words the prologue saved at sp + 8 .. sp + 40 of this frame). Regions: queued (read-only; replaced by a writable
   copy on the store path, after the test) and the frame (read-only). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg diginet_session_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_body_check_cg diginet_session_submit_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_submit_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0 TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module PBC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_body_check_cg.
Module SSK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_submit_seg_kit.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the cut                                       *)
(* ------------------------------------------------------------------ *)

Definition app_sr : list sv :=
  sr_set (sr_set (sr_set sr_atoms 12 (SAlu ALU_SRL (SOff 9 18144) (SLit 3))) 18 (SOff 9 18144)) 19 (SOff 32 0).
(* queued (s + 18144, 4 bytes), read-only, and its writable copy for the store path. *)
Definition app_gq : YP09.region := YP09.mkRegion (Some 9%nat) 18144 18148 0 0 [YP09.mkChunk 18144 (CVal 4 (SOff 33 0))].
Definition app_gqw : YP09.region :=
  YP09.mkRegion (Some 9%nat) 18144 18148 18144 18148 [YP09.mkChunk 18144 (CVal 4 (SOff 33 0))].
(* The frame [sp, sp + 48) of the cut's sp, read-only, with the five saved words. *)
Definition ssw_fr (a0 : nat) : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 48 0 0
    [YP09.mkChunk 8 (CVal 8 (SOff a0 0)); YP09.mkChunk 16 (CVal 8 (SOff (S a0) 0));
     YP09.mkChunk 24 (CVal 8 (SOff (S (S a0)) 0)); YP09.mkChunk 32 (CVal 8 (SOff (S (S (S a0))) 0));
     YP09.mkChunk 40 (CVal 8 (SOff (S (S (S (S a0)))) 0))].
Definition app_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46 - 48) (2 ^ 47 - 48) 4); (8%nat, mkAF 4096 (2 ^ 47 - 32) 2);
           (9%nat, mkAF TA_g_s TA_g_s 6); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition app_ss : sstate := mkSS SSW_APP app_sr [app_gq; ssw_fr 34] None app_facts.
Definition APP_SH : list shent := [mkSHE 9 18144 18152].
Definition SSW_Bx : sv := SOff 32 0.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ssw_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ssw_reg: no match for" T; fail
  end.

(* The symbolic value of register r in HS, as an equation H. *)
Ltac ssw_rv HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = sv_denot Ex e) by exact (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)
  end.

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac ssw_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write rights of a run whose regions have no writable byte. *)
Ltac ssw_awr_ro :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* ------------------------------------------------------------------ *)
(* Small facts                                                         *)
(* ------------------------------------------------------------------ *)

Lemma ssw_regs_ok_pin : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> bv_eqb r 0 = false -> sv_denot E e = YK11.getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
  intros E sr regs r e H Hr0 He rr. destruct (decide (rr = r)) as [->|Hne].
  - rewrite sr_get_set_same by exact Hr0. symmetry. exact He.
  - rewrite sr_get_set_other by exact Hne. apply H.
Qed.

Lemma ssw_soff0 : forall E a v, ew E a = v -> sv_denot E (SOff a 0) = v.
Proof. intros E a v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma ssw_soffk : forall E a k v, ew E a = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff a k) = Z_to_bv 64 (v + k).
Proof. intros E a k v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. reflexivity. Qed.

Lemma ssw_base : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v.
Proof. intros E n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. Qed.

Lemma ssw_U : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v Hn Hv. rewrite Hn. apply unsigned_lit_small. exact Hv. Qed.

(* A read-only region made writable on a range of bytes that are writable. *)
Lemma ssw_region_widen : forall E (m : word -> option byte) n lo hi wlo whi cs,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi 0 0 cs) ->
  (forall o, wlo <= o < whi -> writable_at tfibsegs m (base_val E (Some n) + o)) ->
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
  intros E m n lo hi wlo whi cs (H1 & H2 & _ & H4) Hw. unfold region_ok in *.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
  split; [exact H1|]. split; [exact H2|]. split; [exact Hw | exact H4].
Qed.

(* aregs_preserved at a return of a cut's run: ra, s0 .. s3 restored from the cut's frame atoms a0 .. a0 + 4, sp
   = the cut's sp + 48, gp, tp, s4 .. s11 the cut's registers. *)
Lemma ssw_aregs_cut : forall c regs' (E : env) regsF (a0 : nat) (B : asyms),
  ssw_rg B c regs' -> 2 ^ 46 <= ssw_SP c <= 2 ^ 47 ->
  (forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs' r) ->
  ew E a0 = YK11.getr (cx_regs c) 19 -> ew E (S a0) = YK11.getr (cx_regs c) 18 ->
  ew E (S (S a0)) = YK11.getr (cx_regs c) 9 -> ew E (S (S (S a0))) = YK11.getr (cx_regs c) 8 ->
  YK11.getr (cx_regs c) 3 = w64 (as_gp B) -> YK11.getr (cx_regs c) 4 = w64 (as_tp B) ->
  YK11.getr regsF (Z_to_bv 5 2) = sv_denot E (SOff 2 48) ->
  YK11.getr regsF (Z_to_bv 5 3) = sv_denot E (SOff 3 0) -> YK11.getr regsF (Z_to_bv 5 4) = sv_denot E (SOff 4 0) ->
  YK11.getr regsF (Z_to_bv 5 8) = sv_denot E (SOff (S (S (S a0))) 0) ->
  YK11.getr regsF (Z_to_bv 5 9) = sv_denot E (SOff (S (S a0)) 0) ->
  YK11.getr regsF (Z_to_bv 5 18) = sv_denot E (SOff (S a0) 0) ->
  YK11.getr regsF (Z_to_bv 5 19) = sv_denot E (SOff a0 0) ->
  (forall r, 20 <= r <= 27 -> YK11.getr regsF (Z_to_bv 5 r) = sv_denot E (SOff (Z.to_nat r) 0)) ->
  aregs_preserved (cx_regs c) regsF.
Proof.
  intros c regs' E regsF a0 B HRG Hsp HE E0 E1 E2 E3 Hgp Htp R2 R3 R4 R8 R9 R18 R19 R20.
  destruct HRG as (G2 & G3 & G4 & _ & _ & _ & _ & _ & G20).
  apply ssw_aregs_of. intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [| ]); [ | | | | | | | | | | | | | | | destruct Hr].
  - rewrite R2. rewrite (ssw_soffk E 2 48 (ssw_SP c - 48)); [| rewrite (HE 2%nat (Z_to_bv 5 2)) by (reflexivity || lia); exact G2 | lia].
    replace (ssw_SP c - 48 + 48) with (ssw_SP c) by lia. unfold ssw_SP, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite R3, (ssw_soff0 E 3 (YK11.getr regs' (Z_to_bv 5 3))) by (apply HE; (reflexivity || lia)).
    replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G3, Hgp. reflexivity.
  - rewrite R4, (ssw_soff0 E 4 (YK11.getr regs' (Z_to_bv 5 4))) by (apply HE; (reflexivity || lia)).
    replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G4, Htp. reflexivity.
  - rewrite R8. apply ssw_soff0. exact E3.
  - rewrite R9. apply ssw_soff0. exact E2.
  - rewrite R18. apply ssw_soff0. exact E1.
  - rewrite R19. apply ssw_soff0. exact E0.
  - rewrite R20, <- (G20 20) by lia. apply ssw_soff0. apply HE; (reflexivity || lia).
  - rewrite R20, <- (G20 21) by lia. apply ssw_soff0. apply HE; (reflexivity || lia).
  - rewrite R20, <- (G20 22) by lia. apply ssw_soff0. apply HE; (reflexivity || lia).
  - rewrite R20, <- (G20 23) by lia. apply ssw_soff0. apply HE; (reflexivity || lia).
  - rewrite R20, <- (G20 24) by lia. apply ssw_soff0. apply HE; (reflexivity || lia).
  - rewrite R20, <- (G20 25) by lia. apply ssw_soff0. apply HE; (reflexivity || lia).
  - rewrite R20, <- (G20 26) by lia. apply ssw_soff0. apply HE; (reflexivity || lia).
  - rewrite R20, <- (G20 27) by lia. apply ssw_soff0. apply HE; (reflexivity || lia).
Qed.

Section app. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The cut's valuation: the registers, the shadow base, the queued count, the five saved words. *)
Definition app_extra (c : ssw_ctx) : list word :=
  [w64 SHADOW_OFF; w64 (ssw_q c); YK11.getr (cx_regs c) 19; YK11.getr (cx_regs c) 18; YK11.getr (cx_regs c) 9;
   YK11.getr (cx_regs c) 8; YK11.getr (cx_regs c) 1].
Definition app_E (c : ssw_ctx) (regs' : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs' (app_extra c)).

(* The frame of a cut holds the saved words (ssw_saved) at the cut's sp = entry sp - 48. *)
Lemma ssw_fr_ok : forall c (E : env) (WX : world segs) m (a0 : nat),
  ssw_saved c WX m -> bv_unsigned (ew E 2) = ssw_SP c - 48 -> 2 ^ 46 <= ssw_SP c <= 2 ^ 47 ->
  ew E a0 = YK11.getr (cx_regs c) 19 -> ew E (S a0) = YK11.getr (cx_regs c) 18 ->
  ew E (S (S a0)) = YK11.getr (cx_regs c) 9 -> ew E (S (S (S a0))) = YK11.getr (cx_regs c) 8 ->
  ew E (S (S (S (S a0)))) = YK11.getr (cx_regs c) 1 ->
  region_ok segs E (mrestrict (w_H WX) m) (ssw_fr a0).
Proof.
  intros c E WX m a0 (V19 & V18 & V9 & V8 & V1) Usp Hsp E0 E1 E2 E3 E4.
  unfold ssw_fr, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  assert (CH : forall (a : nat) (r : bv 5) (off : Z), ew E a = YK11.getr (cx_regs c) r ->
    val_mem segs (mrestrict (w_H WX) m) (ssw_SP c - 48 + off) 8 (bv_unsigned (YK11.getr (cx_regs c) r)) ->
    YP09.chunk_ok segs E (mrestrict (w_H WX) m) (ssw_SP c - 48) (YP09.mkChunk off (CVal 8 (SOff a 0)))).
  { intros a r off Ha Hv. apply (chunk_ok_val segs E _ (ssw_SP c - 48) off 8 (SOff a 0) (bv_unsigned (YK11.getr (cx_regs c) r)));
      [apply ssw_soff0; rewrite Ha; symmetry; apply Z_to_bv_bv_unsigned | apply bv_unsigned_in_range | lia | exact Hv]. }
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (CH a0 19%bv 8 E0). replace (ssw_SP c - 48 + 8) with (ssw_SP c - 40) by lia. exact V19.
  - apply (CH (S a0) 18%bv 16 E1). replace (ssw_SP c - 48 + 16) with (ssw_SP c - 32) by lia. exact V18.
  - apply (CH (S (S a0)) 9%bv 24 E2). replace (ssw_SP c - 48 + 24) with (ssw_SP c - 24) by lia. exact V9.
  - apply (CH (S (S (S a0))) 8%bv 32 E3). replace (ssw_SP c - 48 + 32) with (ssw_SP c - 16) by lia. exact V8.
  - apply (CH (S (S (S (S a0)))) 1%bv 40 E4). replace (ssw_SP c - 48 + 40) with (ssw_SP c - 8) by lia. exact V1.
Qed.

(* The cut's shadow entry: g_s's granule of queued, at every AR state. *)
Lemma app_shok : forall ly S (W : world segs) mem md (E : env),
  trans_ssubmit_cells B -> @AR rc segs B ly S W mem md ->
  ew E 9 = w64 TA_g_s -> ew E 32 = w64 SHADOW_OFF ->
  sh_ok segs SSW_Bx APP_SH E (mrestrict (w_H W) mem).
Proof.
  intros ly S W mem md E HSC HAR E9 E32.
  unfold sh_ok, APP_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem E SSW_Bx 9 TA_g_s 18264 TA_g_s 18144 18152 (ssw_gs_ra B ly S W mem md HSC HAR)).
  - unfold U, SSW_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
  - unfold U. cbn [sv_denot]. rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold TA_g_s. lia.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, TA_g_s in *. lia.
Qed.

(* The symbolic state at the cut holds of the machine state there. *)
Lemma app_entry : forall c lyX SX (WX : world segs) regs' m md,
  ssw_rt B MT -> ssw_ok B c -> ssw_cur B MT c lyX SX WX m md -> ssw_rg B c regs' ->
  st_ok_pi segs VAL (app_E c regs') app_ss
    (restrict (w_H WX) (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + SSW_APP)) m (YK11.seg_rom segs))) /\
  sh_ok segs SSW_Bx APP_SH (app_E c regs') (mrestrict (w_H WX) m).
Proof.
  intros c lyX SX WX regs' m md HRT HOK HCUR HRG.
  pose proof HRT as (_ & HSC & LAWS & _).
  pose proof (ssw_ok_stack B c HOK) as (_ & Hsp & _).
  pose proof (ssw_ok_cp B MT c HRT HOK) as (Hc0 & Hc47 & _).
  assert (Hcp4 : cx_cp c mod 4 = 0)
    by (destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H4 & _); exact H4).
  assert (Hsp16 : ssw_SP c mod 16 = 0) by (destruct HOK as (_ & _ & _ & _ & _ & _ & _ & H16 & _); exact H16).
  destruct HCUR as (HJ & _ & _ & _ & (_ & _ & _ & Htw) & HSV).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  pose proof HRG as (G2 & G3 & G4 & G8 & G9 & G12 & G18 & G19 & _).
  set (E := app_E c regs').
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs' r)
    by (intros n r Hn; unfold E, app_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (EX : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (app_extra c) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, app_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
  pose proof (EX 6%nat ltac:(lia)) as E38.
  cbn [Nat.add nth app_extra] in E32, E33, E34, E35, E36, E37, E38.
  pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite G2 in E2.
  pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite G8 in E8.
  pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite G9 in E9.
  assert (EC : TA_g_s = 6158784) by reflexivity.
  assert (Rq : 0 <= ssw_q c < 2 ^ 32) by (unfold ssw_q; exact (TWL.u_at_range _ _ 4)).
  assert (U2 : bv_unsigned (ew E 2) = ssw_SP c - 48) by (apply ssw_U; [exact E2 | lia]).
  assert (U9 : bv_unsigned (ew E 9) = TA_g_s) by (apply ssw_U; [exact E9 | lia]).
  split.
  - rewrite restrict_mkst_fx. unfold app_ss.
    apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    + unfold app_sr.
      apply ssw_regs_ok_pin; [| reflexivity | rewrite G19; apply ssw_soff0; exact E32].
      apply ssw_regs_ok_pin; [| reflexivity | rewrite G18; cbn [sv_denot]; rewrite E9; apply bv_eq; vm_compute; reflexivity].
      apply ssw_regs_ok_pin; [apply regs_ok_Eimg_Ereg | reflexivity |].
      rewrite G12. cbn [sv_denot]. rewrite E9. apply bv_eq. vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold app_gq, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ TA_g_s 18144 4 (SOff 33 0) (ssw_q c)); [apply ssw_soff0; exact E33 | exact Rq | lia |].
        exact (tw_read_val segs _ TMAP_A (cx_Bw c) TW.OFF_g_s TA_g_s TW.SZ_g_s 18144 4 TMAP_A_ok Htw TMAP_A_g_s
          ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * exact (ssw_fr_ok c E WX m 34 HSV U2 Hsp E34 E35 E36 E37 E38).
    + apply pairwise_disjoint_of_extents.
      unfold app_gq, ssw_fr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U2, U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; first [exact I | lia].
    + unfold app_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U9, (ssw_U E 8 (cx_cp c) E8 ltac:(lia)), (ssw_U E 32 SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)),
        (ssw_U E 33 (ssw_q c) E33 ltac:(lia)).
      change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
      assert (H48 : (ssw_SP c - 48) mod 16 = 0)
        by (replace (ssw_SP c - 48) with (ssw_SP c + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact Hsp16).
      repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite EC; reflexivity].
  - exact (app_shok lyX SX WX m md E HSC HAR E9 E32).
Qed.

(* The memcpy's destination a0 = s + 1760 + (queued << 5) (+0xf4 .. +0x104). *)
Lemma ssw_den_dest : forall E q, ew E 9 = Z_to_bv 64 TA_g_s -> ew E 33 = Z_to_bv 64 q -> 0 <= q < 512 ->
  sv_denot E (SAlu ALU_ADD (SOff 9 1760) (SAlu ALU_SLL (SOff 33 0) (SLit 5))) = Z_to_bv 64 (TA_g_s + 1760 + 32 * q).
Proof.
  intros E q H9 H33 Hq. assert (EC : TA_g_s = 6158784) by reflexivity.
  rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal.
  change (U E (SAlu ALU_ADD (SOff 9 1760) (SAlu ALU_SLL (SOff 33 0) (SLit 5))) = TA_g_s + 1760 + 32 * q).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, H9, H33.
  rewrite !unsigned_lit_small by (rewrite ?EC; lia). rewrite Z.add_0_r.
  change (Z.land (zcanon 5) 63) with 5. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
  unfold zcanon, M64. rewrite (Z.mod_small q) by lia. rewrite (Z.mod_small (q * 32)) by lia.
  rewrite (Z.mod_small (TA_g_s + 1760)) by (rewrite EC; lia). rewrite Z.mod_small by (rewrite EC; lia). lia.
Qed.

Lemma ssw_br_ne : forall a b, branch_taken BC_NE a b = negb (branch_taken BC_EQ a b).
Proof. intros a b. reflexivity. Qed.

(* The 4 bytes of queued + 1 (q < 512) the store left, read through aview. *)
Lemma ssw_le4 : forall q, 0 <= q < 512 ->
  bv_unsigned (Z_to_bv 64 (q + 1)) mod 2 ^ (8 * Z.of_N 4) = q + 1.
Proof. intros q Hq. rewrite unsigned_lit_small by lia. apply Z.mod_small. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia. Qed.

(* The 8 bytes of a stored counter + 1, read back modulo 2^64. *)
Lemma ssw_le8 : forall v j, YO0f.le_byte (((v + 1) mod 2 ^ 64) mod 2 ^ (8 * Z.of_N 8)) 8 j = YO0f.le_byte (v + 1) 8 j.
Proof.
  intros v j. unfold YO0f.le_byte. change (8 * Z.of_N 8) with 64. change (8 * Z.of_nat 8) with 64.
  rewrite !Z.mod_mod by lia. reflexivity.
Qed.

Lemma ssw_le8' : forall v j,
  YO0f.le_byte (bv_unsigned (Z_to_bv 64 (v + 1)) mod 2 ^ (8 * Z.of_N 8)) 8 j = YO0f.le_byte (v + 1) 8 j.
Proof.
  intros v j. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  apply ssw_le8.
Qed.

End app.

(* After a run whose regions write nothing: the model named, ssw_lite and ssw_saved carried to the run's memory. *)
Ltac ssw_after_ro Bv MTv cv HRT HOK HL HSV :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt end;
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict (w_H ?Wx) ?m1) (mrestrict (w_H ?Wx) ?m2),
                      HG : mem_grows _ _, HF : frame_of _ _ _ _ |- _ =>
    let KR := fresh "KR" in
    assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H Wx) m2 a = aview tfibsegs (w_H Wx) m1 a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr);
          [ let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
            let Hin := fresh "Hin" in let Hx := fresh "Hx" in
            intros b wlo whi x Hin Hx; ssw_win Hin Hx ltac:(lia) | exact Ha | intros [] ]);
    let HL' := fresh "HL" in
    pose proof (ssw_lite_step Bv MTv cv Wx m1 m2 _ HRT HOK HL (fun a Ha _ => KR a Ha)
      (fun a Ha => apresent_grows _ _ _ a HG Ha)) as HL';
    let HSV' := fresh "HSV" in
    assert (HSV' : ssw_saved cv Wx m2)
      by (apply (ssw_saved_xfer cv Wx Wx m1 m2); [intros; apply KR; lia | exact HSV]);
    clear HL HSV HF HFr HG; rename HL' into HL; rename HSV' into HSV; clear KR
  end.

(* The low atoms of the current valuation are those of E0. *)
Ltac ssw_low HS E0 HEX :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ _ =>
      assert (HEX : forall n, (n < 1024)%nat -> ew Ex n = ew E0 n)
        by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
            repeat rewrite ew_ewset_other by lia; repeat rewrite ew_havoc_old by lia; reflexivity)
  | YP0l.st_ok _ ?Ex _ _ =>
      assert (HEX : forall n, (n < 1024)%nat -> ew Ex n = ew E0 n)
        by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
            repeat rewrite ew_ewset_other by lia; repeat rewrite ew_havoc_old by lia; reflexivity)
  end.

(* getr of the machine state of HS at a register = the denotation of a given symbolic value (its computed one). *)
Ltac ssw_rv_exact HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS) _);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
    reflexivity
  end.

(* Rewrite the goal's getr of HS's machine state at a register to the denotation of its computed symbolic value. *)
Ltac ssw_rv_open HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS) _);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.

(* aregs_preserved at a return of a run from a cut whose frame atoms start at a0 (ssw_aregs_cut); HEXF relates the
   current valuation to the cut's E0, EE reads E0's registers, Ea .. Ed are E0's frame atoms. *)
Ltac ssw_aregs_tac HS Bv cv regs' a0 HRG Hsp HEXF EE Ea Eb Ec Ed Hgp Htp :=
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?msF) =>
    apply (ssw_aregs_cut cv regs' EF (ms_regs msF) a0 Bv HRG Hsp
      (fun n r (Hn : (n < 32)%nat) Hr => eq_trans (HEXF n ltac:(lia)) (EE n r Hr)));
    [ first [exact Ea | rewrite HEXF by lia; exact Ea] | first [exact Eb | rewrite HEXF by lia; exact Eb]
    | first [exact Ec | rewrite HEXF by lia; exact Ec] | first [exact Ed | rewrite HEXF by lia; exact Ed]
    | exact Hgp | exact Htp
    | ssw_rv_exact HS | ssw_rv_exact HS | ssw_rv_exact HS | ssw_rv_exact HS | ssw_rv_exact HS
    | ssw_rv_exact HS | ssw_rv_exact HS
    | let r := fresh "r" in let Hr := fresh "Hr" in let Er := fresh "Er" in intros r Hr;
      assert (Er : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
      repeat (destruct Er as [-> | Er]; [ssw_rv_exact HS |]); subst r; ssw_rv_exact HS ]
  end.

Section appw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The walk from the cut APP. *)
Lemma ssw_seg_app : forall c, @ssw_app_cut fx rc B MT c.
Proof.
intros c lyX SX WX regs' m md HRT HOK HCUR HRG HM.
pose proof HRT as (HCELLS & HSC & LAWS & MTL & HGX & HGE & HBC & HAI0).
pose proof (ssw_ok_stack B c HOK) as (HAR0 & Hsp & Hce & _).
pose proof (ssw_ok_sp B c HOK) as (Hsp16 & Hsp0 & Hlo & Hhi & Ho16 & ESS).
pose proof (ssw_ok_cp B MT c HRT HOK) as (Hc0 & Hc47 & Hcoff & _).
assert (HL0 : length (cx_C c) = 32%nat)
  by (destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL0 & _); exact HL0).
assert (HNG : forall x, cx_cp c <= x < cx_cp c + 32 -> ~ inG G x)
  by (intros x Hx; destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNG & _);
      exact (proj1 (HNG x ltac:(unfold SSUBMIT_CMD_LEN; lia)))).
assert (Hgp : YK11.getr (cx_regs c) 3 = w64 (as_gp B)) by (destruct HOK as (_ & _ & _ & H3 & _); exact H3).
assert (Htp : YK11.getr (cx_regs c) 4 = w64 (as_tp B)) by (destruct HOK as (_ & _ & _ & _ & H4 & _); exact H4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EST : ESTACK = 4096) by reflexivity.
assert (EC : TA_g_s = 6158784) by reflexivity.
destruct (app_entry B MT c lyX SX WX regs' m md HRT HOK HCUR HRG) as [HS SHOK].
destruct HCUR as (HJ & Hfr & Hperm & Hmo & HL & HSV).
pose proof HRG as (G2 & G3 & G4 & G8 & G9 & G12 & G18 & G19 & G20).
set (E0 := app_E c regs') in HS, SHOK.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, app_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs' r)
  by (intros n r Hn; unfold E0, app_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EXT : forall j, (j < 7)%nat -> ew E0 (32 + j) = nth j (app_extra c) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, app_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EXT 0%nat ltac:(lia)) as E32. pose proof (EXT 1%nat ltac:(lia)) as E33.
pose proof (EXT 2%nat ltac:(lia)) as E34. pose proof (EXT 3%nat ltac:(lia)) as E35.
pose proof (EXT 4%nat ltac:(lia)) as E36. pose proof (EXT 5%nat ltac:(lia)) as E37.
pose proof (EXT 6%nat ltac:(lia)) as E38.
cbn [Nat.add nth app_extra] in E32, E33, E34, E35, E36, E37, E38. clear EXT.
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite G2 in E2.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite G9 in E9.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite G3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite G4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite G8 in E8.
assert (Rq : 0 <= ssw_q c < 2 ^ 32) by (unfold ssw_q; exact (TWL.u_at_range _ _ 4)).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS G HGX 0 []) as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport)) as RET.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + SSW_APP)) m (YK11.seg_rom segs)) md) Q) end.
(* +0xcc .. +0xe0: the shadow check of queued, the load, `bne a0, 512`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ssw_awr_ro. }
ssw_after_ro B MT c HRT HOK HL HSV.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* queued <> 512: the store and the memcpy *)
  ssw_low HS E0 HEX.
  rewrite ssw_br_ne, (SSK.ssk_br_q512 _ 33 (ssw_q c) ltac:(rewrite HEX by lia; exact E33) Rq) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hq512.
  destruct (SSK.ssk_k_none _ _ _ _ HM) as [(Hq & _) | (Hq & HBw' & Hr)]; [exfalso; exact (Hq512 Hq)|].
  fold (ssw_q c) in Hq, HBw'.
  assert (Hq0 : 0 <= ssw_q c < 512) by lia.
  (* queued made writable *)
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
  pose proof (st_ok_pi_region_nth (PI := PI_transport) _ _ _ 0 _ HS eq_refl) as RQ.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?s ?msx =>
    let rs := eval vm_compute in (tl (ss_mem s)) in
    pose proof (st_ok_pi_submem (PI := PI_transport) Ex s msx rs HS ltac:(submem_tac) ltac:(vm_compute; reflexivity)) as HS1
  end.
  clear HS.
  lazymatch type of HS1 with st_ok_pi _ _ ?Ex ?s ?msx =>
    assert (HS : st_ok_pi segs VAL Ex (mkSS (ss_pc s) (ss_regs s) (app_gqw :: ss_mem s) (ss_resv s) (ss_facts s)) msx)
  end.
  { apply (st_ok_pi_add_region (PI := PI_transport) _ _ _ app_gqw HS1); [vm_compute; reflexivity | |].
    - cbn [ms_mem restrict]. apply ssw_region_widen; [exact RQ|].
      intros o Ho. rewrite (ssw_base _ 9 TA_g_s) by (first [exact E9 | rewrite HEX by lia; exact E9 | rewrite EC; lia]).
      apply (gx_rw_writable segs G _ G_HARNESS_rw). apply ssw_gs_inG. unfold TW.SZ_g_s. lia.
    - cbn [ss_mem all_disjoint]. unfold extent_disjoint, app_gqw. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (ssw_base _ 9 TA_g_s) by (first [exact E9 | rewrite HEX by lia; exact E9 | rewrite EC; lia]).
      rewrite (ssw_base _ 2 (ssw_SP c - 48)) by (first [exact E2 | rewrite HEX by lia; exact E2 | lia]).
      split; [lia | exact I]. }
  clear HS1 RQ.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
  (* +0xec .. +0x110: the store's check, `sw queued + 1`, the memcpy's arguments, `jal __asan_memcpy` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_cons_g.
    - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha.
      rewrite (ssw_base _ 9 TA_g_s) in Ha by (first [exact E9 | rewrite HEX by lia; exact E9 | rewrite EC; lia]).
      apply ssw_gs_inG. unfold TW.SZ_g_s. lia.
    - ssw_awr_ro. }
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    set (md1 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md1; clear mt end.
  ssw_low HS E0 HEX1.
  (* queued + 1 is stored; nothing else outside the frame changed *)
  assert (HWR : forall a, TA_g_s + 18144 <= a < TA_g_s + 18144 + Z.of_nat 4 -> ssubmit_wr a)
    by (intros a Ha; left; unfold twa_fld, TW.A_S_queued; lia).
  lazymatch goal with HFr : frame_of _ _ (mrestrict (w_H WX) ?m1) (mrestrict (w_H WX) ?m2), HG : mem_grows _ _ |- _ =>
    assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_g_s + 18144 <= a < TA_g_s + 18144 + Z.of_nat 4) ->
      aview segs (w_H WX) m2 a = aview segs (w_H WX) m1 a)
      by (intros a Ha Hn;
          apply (kept_of_frame _ _ _ _ _ (fun x => TA_g_s + 18144 <= x < TA_g_s + 18144 + Z.of_nat 4) HFr);
          [ intros b wlo whi x Hin Hx; ssw_win Hin Hx ltac:(first [lia |
              rewrite ?HEX1 in Hx by lia; rewrite E9 in Hx; unfold w64 in Hx;
              rewrite unsigned_lit_small in Hx by (rewrite EC; lia); cbv beta; lia]) | exact Ha | exact Hn ]);
    pose proof (YC4b.st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RGQ;
    cbn [ms_mem restrict] in RGQ;
    pose proof (field_of_region_any _ _ 9%nat TA_g_s _ _ _ _ _ 18144 4 (SOff 33 1) RGQ
      ltac:(apply ssw_U; [first [exact E9 | rewrite HEX1 by lia; exact E9] | rewrite EC; lia])
      ltac:(cbn; tauto) ltac:(lia)) as VQ;
    rewrite (ssw_soffk _ 33 1 (ssw_q c)) in VQ by (first [exact E33 | rewrite HEX1 by lia; exact E33 | lia]);
    rewrite (ssw_le4 (ssw_q c) Hq0) in VQ; change (N.to_nat 4) with 4%nat in VQ;
    pose proof (ssw_lite_store B MT c WX m1 m2 _ 18144 4 (ssw_q c + 1) HRT HOK HL ltac:(lia)
      ltac:(unfold TW.SZ_g_s; lia) HWR (fun a Ha _ H2 => KW a Ha H2) (fun a Ha => apresent_grows _ _ _ a HG Ha)
      (fun j Hj => ssw_vm_aview (w_H WX) m2 _ 4 _ j VQ Hj)) as HL1;
    assert (HSV1 : ssw_saved c WX m2)
      by (apply (ssw_saved_xfer c WX WX m1 m2); [intros a Ha; apply KW; lia | exact HSV]);
    clear RGQ VQ
  end.
  clear HL HSV KW. rename HL1 into HL. rename HSV1 into HSV.
  lazymatch goal with HF : frame_of _ _ _ _, HFr : frame_of _ _ _ _, HG : mem_grows _ _ |- _ => clear HF HFr HG end.
  (* +0x110: __asan_memcpy (s->queue[queued], c, 32) *)
  pmkst HS.
  ssw_reg HS (Z_to_bv 5 10) (w64 (TA_g_s + 1760 + 32 * ssw_q c)) Q10
    ltac:(apply ssw_den_dest; [first [exact E9 | rewrite HEX1 by lia; exact E9]
                              | first [exact E33 | rewrite HEX1 by lia; exact E33] | lia]).
  ssw_reg HS (Z_to_bv 5 11) (w64 (cx_cp c)) Q11
    ltac:(apply ssw_soff0; first [exact E8 | rewrite HEX1 by lia; exact E8]).
  ssw_reg HS (Z_to_bv 5 12) (w64 32) Q12 ltac:(reflexivity).
  ssw_reg HS (Z_to_bv 5 2) (w64 (ssw_SP c - 48)) Q2
    ltac:(apply ssw_soff0; first [exact E2 | rewrite HEX1 by lia; exact E2]).
  ssw_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + SSW_RET_CA)) R1
    ltac:(apply codeptr_val; lazymatch goal with H : img_env _ _ ?Ex |- img_env _ _ ?Ex => exact H end).
  ssw_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) R3
    ltac:(apply ssw_soff0; first [exact E3 | rewrite HEX1 by lia; exact E3]).
  ssw_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) R4
    ltac:(apply ssw_soff0; first [exact E4 | rewrite HEX1 by lia; exact E4]).
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom) mdx) Q) end.
  lazymatch type of HL with ssw_lite _ _ _ ?mm _ =>
    assert (HAR1 : @AR rc segs B lyX SX WX mm md1) by exact (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
  end.
  pose proof HL as (_ & _ & HRD & _).
  pose proof HRD as (Hvis & Hra_c & Hhull_c & Hamr_c & Hc0' & Hc63).
  lazymatch type of Q2 with YK11.getr ?rg _ = _ =>
    assert (Hsp1 : spZ rg = ssw_SP c - 48)
      by (change (bv_unsigned (YK11.getr rg (Z_to_bv 5 2)) = ssw_SP c - 48); rewrite Q2; apply unsigned_lit_small; lia)
  end.
  eapply SRr_bind.
  { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OCpy (transport_sigma TS___asan_memcpy)
      (HAI0 fx) G WX _ _ (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
      (cx_own c) lyX SX md1 (cx_k c) (TA_g_s + 1760 + 32 * ssw_q c) (cx_cp c) 32 (ssw_SP c - 48 - cx_sp0 c)
      (Z_to_bv 64 (BASE + SSW_RET_CA)) HGX G_HARNESS_rw HJ Q10 Q11 Q12).
    - lia.
    - lia.
    - lia.
    - rewrite Hsp1. lia.
    - exact Ho16.
    - lia.
    - lia.
    - exact R3.
    - exact R4.
    - exact R1.
    - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold SSW_RET_CA, AF_diginet_session_submit; lia | reflexivity].
    - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right. apply ssw_gs_inG.
      unfold TW.SZ_g_s. lia.
    - left. unfold kLowMemEnd. lia.
    - exact (proj1 (ssw_entry_ra B _ _ _ _ _ (ssw_q c) HSC HAR1 Hq0)).
    - intros _. exact (proj2 (ssw_entry_ra B _ _ _ _ _ (ssw_q c) HSC HAR1 Hq0)).
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split; [exact (Hvis a Ha)|]. rewrite Hsp1. lia. }
      split.
      { destruct (Z_le_gt_dec (TA_g_s + 1760 + 32 * ssw_q c + 32) (cx_cp c)) as [H1|H1]; [left; exact H1|].
        destruct (Z_le_gt_dec (cx_cp c + 32) (TA_g_s + 1760 + 32 * ssw_q c)) as [H2|H2]; [right; exact H2|].
        exfalso. apply (HNG (Z.max (cx_cp c) (TA_g_s + 1760 + 32 * ssw_q c))); [lia|].
        apply ssw_gs_inG. unfold TW.SZ_g_s. lia. }
      split; [exact Hamr_c|]. split; [exact Hra_c | intros _; exact Hhull_c]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hcpy & Heff & Hgr2).
  lazymatch type of HL with ssw_lite _ _ _ ?mm _ =>
    pose proof (ssw_lite_cpy B MT c WX mm mem2 _ (ssw_q c) HRT HOK HL Hq0 Hcpy
      (fun a Ha H1 H2 => Heff a Ha H1 ltac:(lia)) Hgr2) as HL2;
    assert (HSV2 : ssw_saved c WX mem2)
      by (apply (ssw_saved_xfer c WX WX mm mem2); [intros a Ha; apply Heff; lia | exact HSV])
  end.
  clear HL HSV.
  (* the frame kept by the call *)
  jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H WX) mem2) HP2 [1%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    apply (region_kept_aview _ _ _ _ 2%nat (ssw_SP c - 48)); [| | exact Hgr2].
    - apply ssw_U; [first [exact E2 | rewrite HEX1 by lia; exact E2] | lia].
    - intros a Ha. apply Heff; lia. }
  specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Ex ?kk ?ws) _ _ =>
    lazymatch goal with H : img_env _ _ Ex |- _ =>
      assert (HEIc : img_env VAL A_LIM (havoc Ex kk ws)) by (apply img_env_havoc_hi; [exact H | cbv; lia]) end end.
  ssw_low HS E0 HEX3.
  lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
    assert (SHOK1 : sh_ok segs SSW_Bx APP_SH E1 (mrestrict (w_H WX) mem2))
      by (apply (app_shok B _ _ _ _ _ _ HSC (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2));
          [rewrite HEX3 by lia; exact E9 | rewrite HEX3 by lia; exact E32]) end.
  clear SHOK.
  (* +0x114 .. +0x130: a0 = 0, the epilogue, `ret` *)
  paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
  { ssw_awr_ro. }
  ssw_after_ro B MT c HRT HOK HL2 HSV2.
  ssw_low HS E0 HEXF.
  eapply (RET WX _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  assert (HLB : length (cx_Bw c) = Z.to_nat TW.W_LEN)
    by (destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htw0 & _); exact (tw_len _ _ _ Htw0)).
  apply (ssw_close B MT c lyX SX WX _ _ _ HRT HOK HJ2 Hfr Hperm Hmo (proj1 HL2)).
  + ssw_aregs_tac HS B c regs' 34%nat HRG Hsp HEXF EE E34 E35 E36 E37 Hgp Htp.
  + ssw_rv_open HS. apply ssw_soff0. rewrite HEXF by lia. exact E38.
  + ssw_rv_open HS. rewrite Hr. apply bv_eq. reflexivity.
  + destruct HL2 as (_ & _ & _ & Htw2). rewrite HBw'.
    rewrite <- (SSK.ssk_app_world (cx_Bw c) (cx_C c) (ssw_q c) HLB HL0 Hq0).
    replace (TW.A_S_queue_bytes (ssw_q c)) with (TW.OFF_g_s + (1760 + 32 * ssw_q c)) by (unfold TW.A_S_queue_bytes; lia).
    exact Htw2.
- (* queued = 512: a0 = -5, the return *)
  ssw_low HS E0 HEX.
  rewrite ssw_br_ne, (SSK.ssk_br_q512 _ 33 (ssw_q c) ltac:(rewrite HEX by lia; exact E33) Rq) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hq512.
  destruct (SSK.ssk_k_none _ _ _ _ HM) as [(_ & HBw' & Hr) | (Hq & _)]; [| unfold ssw_q in Hq512; lia].
  (* +0xe4 .. +0x130: a0 = -5, the epilogue, `ret` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ssw_awr_ro. }
  ssw_after_ro B MT c HRT HOK HL HSV.
  ssw_low HS E0 HEXF.
  eapply (RET WX _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  apply (ssw_close B MT c lyX SX WX _ _ _ HRT HOK HJ Hfr Hperm Hmo (proj1 HL)).
  + ssw_aregs_tac HS B c regs' 34%nat HRG Hsp HEXF EE E34 E35 E36 E37 Hgp Htp.
  + ssw_rv_open HS. apply ssw_soff0. first [exact E38 | rewrite HEXF by lia; exact E38].
  + ssw_rv_open HS. rewrite Hr. apply bv_eq. reflexivity.
  + rewrite HBw'. exact (proj2 (proj2 (proj2 HL))).
Qed.

End appw.
