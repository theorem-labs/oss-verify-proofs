(* io_send_seg_hdr: the header parse of the image-A walk of io_send (fuzz_transport.asan e89be137db17; the
   statement is lib/A/Prog/io_send_cg.v), from 0x82db8 (IOS_PARSE, the return of __asan_memset) to 0x8302c
   (IOS_AT 0x2cc, the head of the body-sum loop), as one segment lemma in continuation form: ios_hdr_seg.

   The code (io_send_cg.v header lines 86-97; every load of a frame byte is preceded by its instrumented check):
     0x82db8 - 0x82dc4  len < 30 (unsigned) goes to 0x83074 with a0 = -2;
     0x82dc8 - 0x82e0c  the checked loads of p[12], p[13]; ethertype = p[12] << 8 | p[13], the 2-byte store at
                        sp + 32 (f + 24); ethertype <> 0x885f goes to 0x83070 (a0 = -3);
     0x82e10 - 0x82e5c  the checked loads of p[14], p[15]; numbytes, the 2-byte store at sp + 34 (f + 26);
                        numbytes < 16 or len - 14 < numbytes (unsigned) goes to 0x83074 with a0 = -4;
     0x82e60 - 0x82e6c  the 8-byte stores of p at sp + 16 (f + 8) and p + 6 at sp + 24 (f + 16);
     0x82e70 - 0x82fdc  the checked loads of p[16] .. p[27]: sum (sp + 36), send (be32, sp + 40), ack (be32,
                        sp + 44), retry (sp + 38);
     0x82fe0 - 0x8301c  the checked loads of p[28], p[29]: cmd (sp + 48), ncmds (sp + 49);
     0x83010 - 0x83028  the 8-byte stores of p + 30 at sp + 56 (f + 48), numbytes - 16 at sp + 64 (f + 56) and
                        len - 14 - numbytes at sp + 72 (f + 64).
   sp is the walk's sp (the entry sp less IOSEND_FRAME), s0 = len, s1 = p, s4 = the shadow base.

   How it is proved. Four symbolic runs of lib/A/Prog/PaShadow.v over the caller's G journal (TransportGRunA.v
   paj_run_to_x, to the stop IOS_AT 0x2cc), from one symbolic state ih_ss at IOS_PARSE whose regions are the 18
   header bytes p[12] .. p[29] (read-only, atoms 32 .. 49) and the two written stretches of the struct,
   [sp + 16, sp + 50) and [sp + 56, sp + 80) (writable bytes of the caller's stack window: awr_byte, so awr_ok_x
   closes without a byte of G). The shadow entry [p + 12, p + 30) (range_addressable from trans_src_ok through
   DgnTransportCg.v trans_src_ok_rd) decides every one of the eighteen checks, so no call of the error paths
   0x833d4 .. 0x834a0 is reached. The len test is decided by the fact 30 <= len on s0; the engine stops at the
   three other tests and the walk splits on each (paj_branch): the taken side contradicts the premise
   fr_ethertype frame = 0x885f, 16 <= fr_numbytes frame, fr_numbytes frame <= len - 14.

   What it takes (all at 0x82db8, registers regs, memory mem): the caller's G journal (ajournal_gx G_HARNESS 0 []),
   AR_laws and gx_ok; sp = getr regs 2 (16-aligned, sp0 - STK <= sp, sp + IOSEND_FRAME <= sp0), s0 = len,
   s1 = p, s4 = SHADOW_OFF; the 80 bytes of f = sp + IOS_F_OFF zero (the memset); the frame's bytes (garr8) and
   where it lies (trans_src_ok) at mem, apart from io_send's frame [sp, sp + IOSEND_FRAME); and the parse facts of
   lib/A/Prog/io_send_seg_frm.v ios_fields: 30 <= len, fr_ethertype frame = 0x885f,
   16 <= fr_numbytes frame <= len - 14. (io_send_seg_cut.v ios_at_parse and ios_fix give the state facts, the
   off-frame one from decode_off_win regs IOSEND_STK; io_send_seg_frm.v ios_sf_code and ios_fields the parse.)

   What it produces (the premises of the continuation, at 0x8302c with registers regs2, memory mem2):
   - every register of ios_hdr_keep (all but a0 .. a7) as at 0x82db8; a2 = fr_body_len frame (numbytes - 16),
     a3 = p + 30 (the body pointer);
   - the caller's journal at mem2, with the same layout, state and event count;
   - every byte present before is present after; every byte outside ios_hdr_wr sp (= [sp + 16, sp + 50) and
     [sp + 56, sp + 80)) reads as before;
   - ios_hdr_fields: one val_mem fact per stored field of the struct spec_frame f at sp + 8, in fuzz_frame's
     reading of the frame bytes (the fr_ functions of lib/Spec/DgnSpec.v): dst p (f + 8), src p + 6 (f + 16),
     ethertype (f + 24), numbytes (f + 26), sum (f + 28), retry (f + 30), send (f + 32), ack (f + 36),
     cmd (f + 40), ncmds (f + 41), body p + 30 (f + 48), body_len (f + 56), pad_len (f + 64);
   - the memset's zero bytes the stretch does not write: f + 0 .. f + 7 (code and padding), f + 42 .. f + 47
     (padding) and f + 72 .. f + 79 (body_sum and padding);
   - the frame's bytes (garr8) and trans_src_ok at mem2 (no store reaches the frame or a shadow byte).
   With lib/A/Prog/io_send_seg_frm.v ios_fields (each sf_ field is its fr_ reading; sf_dst = 0, sf_src = 6,
   sf_body = 30 at code 0), these are the fields of check_sent_frame_cg.v trans_sframe_at for f = rf frame once
   0x83290 has stored body_sum at f + 72 and 0x83074 the code 0 at f + 0. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_sent_frame_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.

(* ------------------------------------------------------------------ *)
(* The symbolic state at 0x82db8                                       *)
(* ------------------------------------------------------------------ *)

(* s4 (atom 20) holds the shadow base; the shadow entry [p + 12, p + 30) of the header bytes (s1 = atom 9). *)
Definition ih_Bx : sv := SOff 20 0.
Definition ih_SH : list shent := [mkSHE 9 12 30].
(* The header bytes p[12] .. p[29] as atoms 32 .. 49 (read-only). *)
Definition ih_frg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 12 30 0 0
    (map (fun i => YP09.mkChunk (12 + Z.of_nat i) (CVal 1 (SOff (32 + i) 0))) (seq 0 18)).
(* The two stretches of the struct f = sp + 8 the code stores into. *)
Definition ih_s1 : YP09.region := YP09.mkRegion (Some 2%nat) 16 50 16 50 [].
Definition ih_s2 : YP09.region := YP09.mkRegion (Some 2%nat) 56 80 56 80 [].
Definition ih_G : facts :=
  mkFacts ([(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
            (9%nat, mkAF 0 (2 ^ 47 - 31) 0); (8%nat, mkAF 30 (2 ^ 47) 0)] ++
           map (fun i => ((32 + i)%nat, mkAF 0 255 0)) (seq 0 18)) [] [].
Definition ih_ss : sstate := mkSS IOS_PARSE sr_atoms [ih_frg; ih_s1; ih_s2] None ih_G.

(* The bytes of the struct the stretch writes. *)
Definition ios_hdr_wr (sp a : Z) : Prop := (sp + 16 <= a < sp + 50) \/ (sp + 56 <= a < sp + 80).

(* The registers the stretch keeps: all but a0 .. a7. The code writes a0 .. a6; the engine's decision of an
   instrumented check whose slow block is `andi a7,a0,7` (0x83438, 0x83468) leaves a7 a fresh value. *)
Definition ios_hdr_keep : list (bv 5) :=
  [1%bv; 2%bv; 3%bv; 4%bv; 5%bv; 6%bv; 7%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv;
   24%bv; 25%bv; 26%bv; 27%bv; 28%bv; 29%bv; 30%bv; 31%bv].

(* ------------------------------------------------------------------ *)
(* Bytes and the unsigned values of the engine's expressions           *)
(* ------------------------------------------------------------------ *)

Lemma ih_nth_bz : forall (l : list byte) j, nth j (map DSpec.bz l) 0 = DSpec.at8 l j.
Proof. intros l j. unfold DSpec.at8. rewrite <- (map_nth DSpec.bz l (DSpec.b8 0) j). reflexivity. Qed.

Lemma ih_at8_range : forall l j, 0 <= DSpec.at8 l j < 256.
Proof.
  intros l j. unfold DSpec.at8, DSpec.bz. pose proof (bv_unsigned_in_range 8 (nth j l (DSpec.b8 0))) as R.
  change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma ih_den_of_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. subst v. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma ih_U_sll : forall E e x k, U E e = x -> 0 <= x -> 0 <= k < 64 -> x * 2 ^ k < 2 ^ 64 ->
  U E (SAlu ALU_SLL e (SLit k)) = x * 2 ^ k.
Proof.
  intros E e x k He Hx Hk Hr. rewrite U_SAlu, U_SLit, He. cbn [zalu_raw].
  assert (Ek : Z.land (zcanon k) 63 = k).
  { unfold zcanon, M64. rewrite (Z.mod_small k) by lia. change 63 with (Z.ones 6).
    rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 6) with 64. lia. }
  rewrite Ek, Z.shiftl_mul_pow2 by lia. unfold zcanon, M64. apply Z.mod_small.
  split; [apply Z.mul_nonneg_nonneg; [exact Hx | apply Z.pow_nonneg; lia] | exact Hr].
Qed.

Lemma ih_U_or : forall E e1 e2 x y k, U E e1 = x * 2 ^ k -> U E e2 = y -> 0 <= k -> 0 <= y < 2 ^ k ->
  0 <= x * 2 ^ k + y < 2 ^ 64 -> U E (SAlu ALU_OR e1 e2) = x * 2 ^ k + y.
Proof.
  intros E e1 e2 x y k H1 H2 Hk Hy Hr. rewrite U_SAlu, H1, H2. cbn [zalu_raw].
  rewrite DLib.lk_lor_mul_pow2 by lia. unfold zcanon, M64. apply Z.mod_small. exact Hr.
Qed.

Lemma ih_U_or_c : forall E e1 e2 x y k, U E e1 = y -> U E e2 = x * 2 ^ k -> 0 <= k -> 0 <= y < 2 ^ k ->
  0 <= x * 2 ^ k + y < 2 ^ 64 -> U E (SAlu ALU_OR e1 e2) = x * 2 ^ k + y.
Proof.
  intros E e1 e2 x y k H1 H2 Hk Hy Hr. rewrite U_SAlu, H1, H2. cbn [zalu_raw].
  rewrite Z.lor_comm, DLib.lk_lor_mul_pow2 by lia. unfold zcanon, M64. apply Z.mod_small. exact Hr.
Qed.

(* `slli a,a,8; or a,a,b` of two bytes: the big-endian 16-bit value. *)
Lemma ih_U_be16 : forall E a b xa xb, U E (SOff a 0) = xa -> U E (SOff b 0) = xb ->
  0 <= xa < 256 -> 0 <= xb < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SOff a 0) (SLit 8)) (SOff b 0)) = xa * 2 ^ 8 + xb.
Proof.
  intros E a b xa xb Ha Hb Ra Rb.
  apply ih_U_or; [apply ih_U_sll; [exact Ha | lia | lia | lia] | exact Hb | lia | lia | lia].
Qed.

(* The four-byte assembly of send and ack: the big-endian 32-bit value. *)
Lemma ih_U_be32 : forall E a b c d xa xb xc xd,
  U E (SOff a 0) = xa -> U E (SOff b 0) = xb -> U E (SOff c 0) = xc -> U E (SOff d 0) = xd ->
  0 <= xa < 256 -> 0 <= xb < 256 -> 0 <= xc < 256 -> 0 <= xd < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff b 0) (SLit 16)) (SAlu ALU_SLL (SOff a 0) (SLit 24)))
                   (SAlu ALU_OR (SAlu ALU_SLL (SOff c 0) (SLit 8)) (SOff d 0)))
  = xa * 2 ^ 24 + xb * 2 ^ 16 + xc * 2 ^ 8 + xd.
Proof.
  intros E a b c d xa xb xc xd Ha Hb Hc Hd Ra Rb Rc Rd.
  assert (I1 : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff b 0) (SLit 16)) (SAlu ALU_SLL (SOff a 0) (SLit 24)))
               = (xa * 2 ^ 8 + xb) * 2 ^ 16).
  { rewrite (ih_U_or_c E _ _ xa (xb * 2 ^ 16) 24).
    - lia.
    - apply ih_U_sll; [exact Hb | lia | lia | lia].
    - apply ih_U_sll; [exact Ha | lia | lia | lia].
    - lia.
    - lia.
    - lia. }
  assert (I2 : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff c 0) (SLit 8)) (SOff d 0)) = xc * 2 ^ 8 + xd).
  { apply ih_U_or; [apply ih_U_sll; [exact Hc | lia | lia | lia] | exact Hd | lia | lia | lia]. }
  rewrite (ih_U_or E _ _ (xa * 2 ^ 8 + xb) (xc * 2 ^ 8 + xd) 16 I1 I2) by lia. lia.
Qed.

Lemma ih_U_add_lit : forall E e c x, U E e = x -> 0 <= x + c < 2 ^ 64 -> U E (SAlu ALU_ADD e (SLit c)) = x + c.
Proof.
  intros E e c x He Hr. rewrite U_SAlu, U_SLit, He. cbn [zalu_raw]. unfold zcanon, M64.
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. exact Hr.
Qed.

Lemma ih_U_sub : forall E e1 e2 x y, U E e1 = x -> U E e2 = y -> 0 <= x - y < 2 ^ 64 ->
  U E (SAlu ALU_SUB e1 e2) = x - y.
Proof.
  intros E e1 e2 x y H1 H2 Hr. rewrite U_SAlu, H1, H2. cbn [zalu_raw]. unfold zcanon, M64.
  apply Z.mod_small. exact Hr.
Qed.

Lemma ih_atoms_ok : forall E l, (forall n f, In (n, f) l -> afact_ok E n f) -> atoms_ok E l.
Proof.
  intros E l. induction l as [|[n f] l IH]; intros H; cbn [atoms_ok]; [exact I|].
  split; [apply H; left; reflexivity | apply IH; intros n' f' Hin; apply H; right; exact Hin].
Qed.

(* ------------------------------------------------------------------ *)
(* Tactics                                                             *)
(* ------------------------------------------------------------------ *)

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac ih_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write rights of a run: the header bytes are read-only, the two stretches of the struct are bytes of the
   caller's stack window. *)
Ltac ih_awr UspE :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ lia
      | rewrite UspE in Ha; left; split; [unfold awr_byte; left; lia | lia] ] |]);
  apply awr_ok_x_nil.

(* The value of register r in the machine state HS describes, as the symbolic value the run computed. *)
Ltac ih_reg HS r R :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      pose proof (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) as R;
      change (sr_get (ss_regs ssx) r) with e in R
  end.

Ltac ih_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* ------------------------------------------------------------------ *)
(* The entry state of the segment                                      *)
(* ------------------------------------------------------------------ *)

Section hdr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The walk's valuation: the 32 registers at 0x82db8 and the 18 header bytes. *)
Definition ih_byte_w (frame : list byte) (i : nat) : word := w64 (DSpec.at8 frame (12 + i)).
Definition ih_bytes (frame : list byte) : list word := map (ih_byte_w frame) (seq 0 18).
Definition ih_E (regs : bvmap 5 word) (frame : list byte) : env :=
  Eimg (PI := PI_transport) (Ereg regs (ih_bytes frame)).

Lemma ih_ew_byte : forall regs frame i, (i < 18)%nat ->
  ew (ih_E regs frame) (32 + i) = Z_to_bv 64 (DSpec.at8 frame (12 + i)).
Proof.
  intros regs frame i Hi. unfold ih_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite ew_Ereg_extra. unfold ih_bytes.
  rewrite (nth_indep _ _ (ih_byte_w frame 0)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma ih_entry : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (sp p : Z)
    (frame : list byte),
  YK11.getr regs 2 = w64 sp -> YK11.getr regs 8 = w64 (Z.of_nat (length frame)) -> YK11.getr regs 9 = w64 p ->
  YK11.getr regs 20 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 ->
  (forall a, sp + 16 <= a < sp + 80 -> apresent (w_H W) mem a) ->
  garr8 segs (mrestrict (w_H W) mem) p (map DSpec.bz frame) ->
  (30 <= length frame)%nat -> 0 <= p -> p + Z.of_nat (length frame) <= 2 ^ 47 - 1 ->
  (p + Z.of_nat (length frame) <= sp \/ sp + 160 <= p) ->
  st_ok_pi segs VAL (ih_E regs frame) ih_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + IOS_PARSE)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem sp p frame H2 H8 H9 H20 Hsp Hsp16 Hpres HGA HL30 Hp0 Hp47 HOFF.
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ih_E regs frame) n = YK11.getr regs r)
    by (intros n r Hn; unfold ih_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (Usp : bv_unsigned (ew (ih_E regs frame) 2) = sp)
    by (rewrite (EE 2%nat 2%bv eq_refl), H2; apply unsigned_lit_small; lia).
  assert (Up : bv_unsigned (ew (ih_E regs frame) 9) = p)
    by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (Ul : bv_unsigned (ew (ih_E regs frame) 8) = Z.of_nat (length frame))
    by (rewrite (EE 8%nat 8%bv eq_refl), H8; apply unsigned_lit_small; lia).
  assert (Ush : bv_unsigned (ew (ih_E regs frame) 20) = SHADOW_OFF)
    by (rewrite (EE 20%nat 20%bv eq_refl), H20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (Ub : forall i, (i < 18)%nat -> bv_unsigned (ew (ih_E regs frame) (32 + i)) = DSpec.at8 frame (12 + i))
    by (intros i Hi; rewrite (ih_ew_byte regs frame i Hi); apply unsigned_lit_small;
        pose proof (ih_at8_range frame (12 + i)); lia).
  rewrite restrict_mkst_fx. unfold ih_ss.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold ih_frg, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Up. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as (i & <- & Hi).
      apply in_seq in Hi.
      pose proof (ih_at8_range frame (12 + i)) as Ri.
      apply (chunk_ok_val segs (ih_E regs frame) _ p (12 + Z.of_nat i) 1 (SOff (32 + i) 0)
               (DSpec.at8 frame (12 + i))).
      * cbn [sv_denot]. rewrite (ih_ew_byte regs frame i ltac:(lia)), Z.add_0_r.
        rewrite unsigned_lit_small by lia. reflexivity.
      * change (2 ^ (8 * Z.of_N 1)) with 256. exact Ri.
      * change (Z.of_N 1) with 1. lia.
      * assert (Hj : (12 + i < length (map DSpec.bz frame))%nat) by (rewrite length_map; lia).
        destruct (HGA (12 + i)%nat Hj) as [Hv _]. rewrite ih_nth_bz in Hv.
        replace (p + (12 + Z.of_nat i)) with (p + Z.of_nat (12 + i)) by lia. exact Hv.
    + unfold ih_s1, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
    + unfold ih_s2, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold ih_frg, ih_s1, ih_s2, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Usp, Up.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct HOFF as [HOFF | HOFF]; repeat split; first [exact I | lia].
  - unfold facts_ok, ih_G. cbn [f_atoms f_conds f_alias].
    split; [| split; cbn [conds_ok alias_ok]; exact I].
    apply ih_atoms_ok. intros n f Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + cbn [In] in Hin.
      destruct Hin as [E1 | [E1 | [E1 | [E1 | []]]]]; injection E1 as <- <-; unfold afact_ok;
        cbn [af_lo af_hi af_al2].
      * rewrite Ush, Z.pow_0_r, Z.mod_1_r. lia.
      * rewrite Usp. change (2 ^ 4) with 16. lia.
      * rewrite Up, Z.pow_0_r, Z.mod_1_r. lia.
      * rewrite Ul, Z.pow_0_r, Z.mod_1_r. lia.
    + apply in_map_iff in Hin. destruct Hin as (i & E1 & Hi). cbv beta in E1. apply pair_equal_spec in E1.
      destruct E1 as [<- <-]. apply in_seq in Hi.
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (Ub i ltac:(lia)), Z.pow_0_r, Z.mod_1_r.
      pose proof (ih_at8_range frame (12 + i)). lia.
Qed.

(* The shadow entry of the header bytes: [p + 12, p + 30) inside the addressable frame [p, p + len). *)
Lemma ih_shok : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (p : Z)
    (frame : list byte),
  YK11.getr regs 9 = w64 p -> YK11.getr regs 20 = w64 SHADOW_OFF ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p (Z.of_nat (length frame)) ->
  (30 <= length frame)%nat -> 0 <= p -> p + Z.of_nat (length frame) <= 2 ^ 47 - 1 ->
  amem_range p (Z.of_nat (length frame)) ->
  sh_ok segs ih_Bx ih_SH (ih_E regs frame) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem p frame H9 H20 HRA HL30 Hp0 Hp47 HAM.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ih_E regs frame) n = YK11.getr regs r)
    by (intros n r Hn; unfold ih_E; apply ew_Eimg_Ereg_nat; exact Hn).
  unfold sh_ok, ih_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range segs (w_H W) mem (ih_E regs frame) ih_Bx 9%nat p (Z.of_nat (length frame)) p 12 30
           HRA).
  - unfold ih_Bx. apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl); exact H20 | unfold SHADOW_OFF; lia].
  - apply U_atom; [rewrite (EE 9%nat 9%bv eq_refl); exact H9 | lia].
  - lia.
  - lia.
  - intros x Hx. change (Z.min 12 30) with 12 in Hx. change (Z.max 12 30) with 30 in Hx. unfold amem_range in HAM.
    destruct HAM as [HAM | HAM]; unfold SHADOW_OFF; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The segment                                                         *)
(* ------------------------------------------------------------------ *)

(* The fields the stretch stores into the struct f = sp + 8, in fuzz_frame's reading of the frame bytes. *)
Definition ios_hdr_fields (m : word -> option byte) (sp p : Z) (frame : list byte) : Prop :=
  val_mem segs m (sp + 16) 8 p /\ val_mem segs m (sp + 24) 8 (p + 6) /\
  val_mem segs m (sp + 32) 2 (DSpec.fr_ethertype frame) /\ val_mem segs m (sp + 34) 2 (DSpec.fr_numbytes frame) /\
  val_mem segs m (sp + 36) 2 (DSpec.fr_sum frame) /\ val_mem segs m (sp + 38) 2 (DSpec.fr_retry frame) /\
  val_mem segs m (sp + 40) 4 (DSpec.fr_send frame) /\ val_mem segs m (sp + 44) 4 (DSpec.fr_ack frame) /\
  val_mem segs m (sp + 48) 1 (DSpec.fr_cmd frame) /\ val_mem segs m (sp + 49) 1 (DSpec.fr_ncmds frame) /\
  val_mem segs m (sp + 56) 8 (p + 30) /\ val_mem segs m (sp + 64) 8 (DSpec.fr_body_len frame) /\
  val_mem segs m (sp + 72) 8 (DSpec.fr_pad_len frame).

Lemma ios_hdr_seg : forall (Q : world segs -> config -> Prop)
    (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (ly2 : alayout) (S2 : astate) (W : world segs) (mem : word -> option byte) (md : Model) (k : Z)
    (regs : bvmap 5 word) (sp p : Z) (frame : list byte),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem md k ->
  YK11.getr regs 2 = w64 sp -> sp mod 16 = 0 -> sp0 - STK <= sp -> sp + IOSEND_FRAME <= sp0 ->
  YK11.getr regs 8 = w64 (Z.of_nat (length frame)) -> YK11.getr regs 9 = w64 p ->
  YK11.getr regs 20 = w64 SHADOW_OFF ->
  (forall i, 0 <= i < SF_SIZE -> aview segs (w_H W) mem (sp + IOS_F_OFF + i) = Some 0) ->
  garr8 segs (mrestrict (w_H W) mem) p (map DSpec.bz frame) ->
  trans_src_ok B ly2 S2 W mem p (Z.of_nat (length frame)) ->
  (p + Z.of_nat (length frame) <= sp \/ sp + IOSEND_FRAME <= p) ->
  (30 <= length frame)%nat -> DSpec.fr_ethertype frame = 0x885f ->
  16 <= DSpec.fr_numbytes frame -> DSpec.fr_numbytes frame <= Z.of_nat (length frame) - 14 ->
  (forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model),
     (forall r, In r ios_hdr_keep -> YK11.getr regs2 r = YK11.getr regs r) ->
     YK11.getr regs2 12 = w64 (DSpec.fr_body_len frame) ->
     YK11.getr regs2 13 = w64 (p + 30) ->
     ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem2 md2 k ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ ios_hdr_wr sp a -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a) ->
     ios_hdr_fields (mrestrict (w_H W) mem2) sp p frame ->
     (forall i, 0 <= i < 8 \/ 42 <= i < 48 \/ 72 <= i < SF_SIZE ->
        aview segs (w_H W) mem2 (sp + IOS_F_OFF + i) = Some 0) ->
     garr8 segs (mrestrict (w_H W) mem2) p (map DSpec.bz frame) ->
     trans_src_ok B ly2 S2 W mem2 p (Z.of_nat (length frame)) ->
     SRr segs W (@cfg_at fx segs (transport_text + IOS_AT 0x2cc) regs2 mem2 md2) Q) ->
  SRr segs W (@cfg_at fx segs (transport_text + IOS_PARSE) regs mem md) Q.
Proof.
  intros Q STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem md k regs sp p frame
    LAWS HGX HJ H2 Hsp16 Hlo Hhi H8 H9 H20 HZ HGA HSRC HOFF HL30 HET HNB1 HNB2 HK.
  pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
  pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  clear HJi memS.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FR : IOSEND_FRAME = 160) by reflexivity.
  assert (SZ : SF_SIZE = 80) by reflexivity.
  assert (FO : IOS_F_OFF = 8) by reflexivity.
  rewrite FR in Hhi, HOFF.
  assert (Hsp : 2 ^ 46 <= sp <= 2 ^ 47) by lia.
  destruct (trans_src_ok_rd B LAWS ly2 S2 W mem md p (Z.of_nat (length frame)) HAR HSRC ltac:(lia))
    as (_ & HRA & _ & HAM & Hp0 & _).
  assert (Hp47 : p + Z.of_nat (length frame) <= 2 ^ 47 - 1)
    by (unfold amem_range in HAM; destruct HAM as [HAM | HAM]; lia).
  (* the valuation and the atoms *)
  set (E0 := ih_E regs frame).
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ih_E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
    by (intros n r Hn; unfold E0, ih_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (X2 : ew E0 2 = Z_to_bv 64 sp) by (rewrite (EE 2%nat 2%bv eq_refl); exact H2).
  assert (X8 : ew E0 8 = Z_to_bv 64 (Z.of_nat (length frame))) by (rewrite (EE 8%nat 8%bv eq_refl); exact H8).
  assert (X9 : ew E0 9 = Z_to_bv 64 p) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
  assert (XB : forall i, (i < 18)%nat -> ew E0 (32 + i) = Z_to_bv 64 (DSpec.at8 frame (12 + i)))
    by (intros i Hi; exact (ih_ew_byte regs frame i Hi)).
  assert (Usp : bv_unsigned (ew E0 2) = sp) by (rewrite X2; apply unsigned_lit_small; lia).
  assert (Up : bv_unsigned (ew E0 9) = p) by (rewrite X9; apply unsigned_lit_small; lia).
  assert (U0 : forall i, (i < 18)%nat -> U E0 (SOff (32 + i) 0) = DSpec.at8 frame (12 + i)).
  { intros i Hi. apply U_atom; [exact (XB i Hi) | pose proof (ih_at8_range frame (12 + i)); lia]. }
  assert (Ulen : U E0 (SOff 8 (-14)) = Z.of_nat (length frame) - 14)
    by (apply U_atom_off; [exact X8 | lia | lia]).
  assert (UNB0 : U E0 (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 8)) (SOff 35 0)) = DSpec.fr_numbytes frame)
    by exact (ih_U_be16 E0 34 35 _ _ (U0 2%nat ltac:(lia)) (U0 3%nat ltac:(lia))
                (ih_at8_range _ _) (ih_at8_range _ _)).
  assert (UET0 : U E0 (SAlu ALU_OR (SAlu ALU_SLL (SOff 32 0) (SLit 8)) (SOff 33 0)) = DSpec.fr_ethertype frame)
    by exact (ih_U_be16 E0 32 33 _ _ (U0 0%nat ltac:(lia)) (U0 1%nat ltac:(lia))
                (ih_at8_range _ _) (ih_at8_range _ _)).
  (* the entry state, the shadow entry and the run *)
  pose proof (ih_entry W regs mem sp p frame H2 H8 H9 H20 Hsp Hsp16
    ltac:(intros a Ha; apply Hpres0; lia) HGA HL30 Hp0 Hp47 HOFF) as HS.
  pose proof (ih_shok W regs mem p frame H9 H20 HRA HL30 Hp0 Hp47 HAM) as SHOK.
  fold E0 in HS, SHOK.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
    TG.G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (PI := PI_transport)) as BR.
  unfold cfg_at.
  lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + IOS_PARSE)) mem (YK11.seg_rom segs)) md) Qx)
  end.
  (* run 1, +0x058 .. +0x0ac: len >= 30 (decided by the fact on s0), the checked loads of p[12], p[13], the
     store of the ethertype; it stops at `bne a0,a1` *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (IOS_AT 0x2cc).
  { ih_awr Usp. }
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
  rename ms into ms1.
  assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ ios_hdr_wr sp a ->
    aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (ios_hdr_wr sp) HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. ih_win Hin Hx ltac:(rewrite ?Usp, ?Up in Hx; unfold ios_hdr_wr; lia). }
  assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
  { (* ethertype <> 0x885f: the error code -3 (refuted) *)
    exfalso. rewrite branch_ne_U, UET0, U_lit in Hc by lia. rewrite HET in Hc. cbv in Hc. discriminate Hc. }
  clear Hc.
  (* run 2, +0x0b0 .. +0x0f4: the checked loads of p[14], p[15], the store of numbytes; it stops at
     `bltu a1,a2` (numbytes < 16) *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (IOS_AT 0x2cc).
  { ih_awr Usp. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  rename ms into ms2.
  assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ ios_hdr_wr sp a ->
    aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) mem a).
  { intros a Ha Hn. rewrite <- (KA1 a Ha Hn).
    apply (kept_of_frame _ _ _ _ _ (ios_hdr_wr sp) HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. ih_win Hin Hx ltac:(rewrite ?Usp, ?Up in Hx; unfold ios_hdr_wr; lia). }
  assert (GA2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
  clear HF HFr HG KA1 GA1.
  clear dependent ms1.
  psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
  { (* numbytes < 16: the error code -4 (refuted) *)
    exfalso. rewrite branch_ltu_U, UNB0, U_lit in Hc by lia. apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  (* run 3, +0x0f8 .. +0x0fc; it stops at `bltu a2,a1` (len - 14 < numbytes) *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (IOS_AT 0x2cc).
  { ih_awr Usp. }
  set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
  rename ms into ms3.
  assert (KA3 : forall a, 0 <= a < 2 ^ 64 -> ~ ios_hdr_wr sp a ->
    aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) mem a).
  { intros a Ha Hn. rewrite <- (KA2 a Ha Hn).
    apply (kept_of_frame _ _ _ _ _ (ios_hdr_wr sp) HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. ih_win Hin Hx ltac:(rewrite ?Usp, ?Up in Hx; unfold ios_hdr_wr; lia). }
  assert (GA3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms3) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
  clear HF HFr HG KA2 GA2.
  clear dependent ms2.
  psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
  { (* len - 14 < numbytes: the error code -4 (refuted) *)
    exfalso. rewrite branch_ltu_U, Ulen, UNB0 in Hc. apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  (* run 4, +0x100 .. +0x2cc: dst, src, the checked loads of p[16] .. p[29] and the stores of sum, send, ack,
     retry, cmd, ncmds, body, body_len and pad_len *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (IOS_AT 0x2cc).
  { ih_awr Usp. }
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
  rename ms into ms4.
  assert (KA4 : forall a, 0 <= a < 2 ^ 64 -> ~ ios_hdr_wr sp a ->
    aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) mem a).
  { intros a Ha Hn. rewrite <- (KA3 a Ha Hn).
    apply (kept_of_frame _ _ _ _ _ (ios_hdr_wr sp) HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. ih_win Hin Hx ltac:(rewrite ?Usp, ?Up in Hx; unfold ios_hdr_wr; lia). }
  assert (GA4 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms4) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA3 a Ha))).
  clear HF HFr HG KA3 GA3.
  clear dependent ms3.
  (* the valuation at the stop: the run's token atoms 1024 .. 1037 above E0 *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (EF := Ex) in * end.
  assert (HX : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
    by (intros n Hn; unfold EF; repeat rewrite ew_ewset_other by lia; reflexivity).
  assert (UF : forall i, (i < 18)%nat -> U EF (SOff (32 + i) 0) = DSpec.at8 frame (12 + i)).
  { intros i Hi. apply U_atom; [rewrite HX by lia; exact (XB i Hi) | pose proof (ih_at8_range frame (12 + i)); lia]. }
  assert (UspF : bv_unsigned (ew EF 2) = sp) by (rewrite HX by lia; exact Usp).
  assert (X9F : ew EF 9 = Z_to_bv 64 p) by (rewrite HX by lia; exact X9).
  assert (UlenF : U EF (SOff 8 (-14)) = Z.of_nat (length frame) - 14)
    by (apply U_atom_off; [rewrite HX by lia; exact X8 | lia | lia]).
  assert (UNB : U EF (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 8)) (SOff 35 0)) = DSpec.fr_numbytes frame)
    by exact (ih_U_be16 EF 34 35 _ _ (UF 2%nat ltac:(lia)) (UF 3%nat ltac:(lia))
                (ih_at8_range _ _) (ih_at8_range _ _)).
  pose proof (ih_at8_range frame 16) as R16. pose proof (ih_at8_range frame 17) as R17.
  pose proof (ih_at8_range frame 18) as R18. pose proof (ih_at8_range frame 19) as R19.
  pose proof (ih_at8_range frame 20) as R20. pose proof (ih_at8_range frame 21) as R21.
  pose proof (ih_at8_range frame 22) as R22. pose proof (ih_at8_range frame 23) as R23.
  pose proof (ih_at8_range frame 24) as R24. pose proof (ih_at8_range frame 25) as R25.
  pose proof (ih_at8_range frame 26) as R26. pose proof (ih_at8_range frame 27) as R27.
  pose proof (ih_at8_range frame 28) as R28. pose proof (ih_at8_range frame 29) as R29.
  (* the registers: those of ios_hdr_keep kept, a2 = body_len, a3 = p + 30 *)
  assert (HAG : env_agree 32 (Ereg regs (ih_bytes frame)) EF).
  { split; [intros n Hn; rewrite HX by lia; unfold E0, ih_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
    pose proof (regs_kept_of_st_ok_pi EF ssx msx regs (ih_bytes frame) ios_hdr_keep HS HAG
      ltac:(vm_compute; reflexivity)) as KR end.
  ih_reg HS (12%bv : bv 5) HRa2.
  ih_reg HS (13%bv : bv 5) HRa3.
  assert (Q12 : YK11.getr (ms_regs ms4) 12 = w64 (DSpec.fr_body_len frame)).
  { rewrite HRa2. apply ih_den_of_U. rewrite (ih_U_add_lit EF _ (-16) _ UNB) by lia.
    unfold DSpec.fr_body_len. lia. }
  assert (Q13 : YK11.getr (ms_regs ms4) 13 = w64 (p + 30)).
  { rewrite HRa3. apply ih_den_of_U. apply U_atom_off; [exact X9F | lia | lia]. }
  (* the stored fields, read from the chunks of the two stretches of the struct *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
    pose proof (st_ok_pi_region_nth EF ssx msx 1 _ HS eq_refl) as RG1;
    pose proof (st_ok_pi_region_nth EF ssx msx 2 _ HS eq_refl) as RG2 end.
  cbn [ms_mem restrict] in RG1, RG2.
  assert (F16 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (sp + 16) 8 p).
  { eapply (field_of_region _ _ _ _ _ _ _ _ _ 16 8%N _ _ RG1 UspF); [ih_in | | | lia].
    - apply ih_den_of_U. apply U_atom; [exact X9F | lia].
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia. }
  assert (F24 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (sp + 24) 8 (p + 6)).
  { eapply (field_of_region _ _ _ _ _ _ _ _ _ 24 8%N _ _ RG1 UspF); [ih_in | | | lia].
    - apply ih_den_of_U. apply U_atom_off; [exact X9F | lia | lia].
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia. }
  assert (F32 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (sp + 32) 2 (DSpec.fr_ethertype frame)).
  { eapply (field_of_region _ _ _ _ _ _ _ _ _ 32 2%N _ _ RG1 UspF); [ih_in | | | lia].
    - apply ih_den_of_U.
      exact (ih_U_be16 EF 32 33 _ _ (UF 0%nat ltac:(lia)) (UF 1%nat ltac:(lia)) (ih_at8_range _ _) (ih_at8_range _ _)).
    - change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16). rewrite HET. lia. }
  assert (F34 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (sp + 34) 2 (DSpec.fr_numbytes frame)).
  { eapply (field_of_region _ _ _ _ _ _ _ _ _ 34 2%N _ _ RG1 UspF); [ih_in | | | lia].
    - apply ih_den_of_U. exact UNB.
    - change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16). unfold DSpec.fr_numbytes, DSpec.be16.
      pose proof (ih_at8_range frame 14). pose proof (ih_at8_range frame 15). lia. }
  assert (F36 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (sp + 36) 2 (DSpec.fr_sum frame)).
  { eapply (field_of_region _ _ _ _ _ _ _ _ _ 36 2%N _ _ RG1 UspF); [ih_in | | | lia].
    - apply ih_den_of_U.
      exact (ih_U_be16 EF 36 37 _ _ (UF 4%nat ltac:(lia)) (UF 5%nat ltac:(lia)) (ih_at8_range _ _) (ih_at8_range _ _)).
    - change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16). unfold DSpec.fr_sum, DSpec.be16. lia. }
  assert (F38 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (sp + 38) 2 (DSpec.fr_retry frame)).
  { eapply (field_of_region _ _ _ _ _ _ _ _ _ 38 2%N _ _ RG1 UspF); [ih_in | | | lia].
    - apply ih_den_of_U.
      exact (ih_U_be16 EF 46 47 _ _ (UF 14%nat ltac:(lia)) (UF 15%nat ltac:(lia)) (ih_at8_range _ _) (ih_at8_range _ _)).
    - change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16). unfold DSpec.fr_retry, DSpec.be16. lia. }
  assert (F40 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (sp + 40) 4 (DSpec.fr_send frame)).
  { eapply (field_of_region _ _ _ _ _ _ _ _ _ 40 4%N _ _ RG1 UspF); [ih_in | | | lia].
    - apply ih_den_of_U.
      exact (ih_U_be32 EF 38 39 40 41 _ _ _ _ (UF 6%nat ltac:(lia)) (UF 7%nat ltac:(lia)) (UF 8%nat ltac:(lia))
               (UF 9%nat ltac:(lia)) (ih_at8_range _ _) (ih_at8_range _ _) (ih_at8_range _ _) (ih_at8_range _ _)).
    - change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). unfold DSpec.fr_send, DSpec.be32. lia. }
  assert (F44 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (sp + 44) 4 (DSpec.fr_ack frame)).
  { eapply (field_of_region _ _ _ _ _ _ _ _ _ 44 4%N _ _ RG1 UspF); [ih_in | | | lia].
    - apply ih_den_of_U.
      exact (ih_U_be32 EF 42 43 44 45 _ _ _ _ (UF 10%nat ltac:(lia)) (UF 11%nat ltac:(lia)) (UF 12%nat ltac:(lia))
               (UF 13%nat ltac:(lia)) (ih_at8_range _ _) (ih_at8_range _ _) (ih_at8_range _ _) (ih_at8_range _ _)).
    - change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). unfold DSpec.fr_ack, DSpec.be32. lia. }
  assert (F48 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (sp + 48) 1 (DSpec.fr_cmd frame)).
  { eapply (field_of_region _ _ _ _ _ _ _ _ _ 48 1%N _ _ RG1 UspF); [ih_in | | | lia].
    - apply ih_den_of_U. exact (UF 16%nat ltac:(lia)).
    - change (2 ^ (8 * Z.of_N 1)) with (2 ^ 8). unfold DSpec.fr_cmd. lia. }
  assert (F49 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (sp + 49) 1 (DSpec.fr_ncmds frame)).
  { eapply (field_of_region _ _ _ _ _ _ _ _ _ 49 1%N _ _ RG1 UspF); [ih_in | | | lia].
    - apply ih_den_of_U. exact (UF 17%nat ltac:(lia)).
    - change (2 ^ (8 * Z.of_N 1)) with (2 ^ 8). unfold DSpec.fr_ncmds. lia. }
  assert (F56 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (sp + 56) 8 (p + 30)).
  { eapply (field_of_region _ _ _ _ _ _ _ _ _ 56 8%N _ _ RG2 UspF); [ih_in | | | lia].
    - apply ih_den_of_U. apply U_atom_off; [exact X9F | lia | lia].
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia. }
  assert (F64 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (sp + 64) 8 (DSpec.fr_body_len frame)).
  { eapply (field_of_region _ _ _ _ _ _ _ _ _ 64 8%N _ _ RG2 UspF); [ih_in | | | lia].
    - apply ih_den_of_U. rewrite (ih_U_add_lit EF _ (-16) _ UNB) by lia. unfold DSpec.fr_body_len. lia.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold DSpec.fr_body_len. lia. }
  assert (F72 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (sp + 72) 8 (DSpec.fr_pad_len frame)).
  { eapply (field_of_region _ _ _ _ _ _ _ _ _ 72 8%N _ _ RG2 UspF); [ih_in | | | lia].
    - apply ih_den_of_U. rewrite (ih_U_sub EF _ _ _ _ UlenF UNB) by lia.
      unfold DSpec.fr_pad_len, DSpec.fr_body_len. lia.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold DSpec.fr_pad_len, DSpec.fr_body_len. lia. }
  (* the stop: 0x8302c, the head of the body-sum loop *)
  pmkst HS.
  change (SRr segs W (@cfg_at fx segs (transport_text + IOS_AT 0x2cc) (ms_regs ms4) (ms_mem ms4) md4) Q).
  apply HK.
  - exact KR.
  - exact Q12.
  - exact Q13.
  - exact HJ.
  - exact GA4.
  - exact KA4.
  - exact (conj F16 (conj F24 (conj F32 (conj F34 (conj F36 (conj F38 (conj F40 (conj F44 (conj F48 (conj F49
      (conj F56 (conj F64 F72)))))))))))).
  - intros i Hi.
    assert (Hi' : 0 <= i < 80) by (destruct Hi as [Hi | [Hi | Hi]]; rewrite ?SZ in Hi; lia).
    assert (Hn : ~ ios_hdr_wr sp (sp + IOS_F_OFF + i))
      by (unfold ios_hdr_wr; rewrite FO; destruct Hi as [Hi | [Hi | Hi]]; rewrite ?SZ in Hi; intros [Hw | Hw]; lia).
    rewrite (KA4 (sp + IOS_F_OFF + i) ltac:(rewrite FO; lia) Hn). apply HZ. rewrite SZ. exact Hi'.
  - intros j Hj. destruct (HGA j Hj) as [Hv Hr]. split; [|exact Hr].
    rewrite length_map in Hj.
    intros kk Hk. rewrite <- (Hv kk Hk). apply (mbyte_of_aview segs). apply KA4.
    + lia.
    + unfold ios_hdr_wr. destruct HOFF as [HO | HO]; intros [Hw | Hw]; lia.
  - destruct HSRC as [Hblk | (HPL & Hrd)]; [left; exact Hblk | right; split; [exact HPL |]].
    eapply trans_rd_ok_view; [exact Hrd | |].
    + intros a Ha. apply KA4; [lia | unfold ios_hdr_wr; destruct HOFF as [HO | HO]; intros [Hw | Hw]; lia].
    + intros s Hs. apply KA4; [lia | unfold ios_hdr_wr; intros [Hw | Hw]; lia].
Qed.

End hdr.

Print Assumptions ios_hdr_seg.
