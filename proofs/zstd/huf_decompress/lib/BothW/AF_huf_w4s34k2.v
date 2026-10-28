(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AF_huf_w4s3b AF_huf_w4s34k.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation amem := (word -> option byte).


Ltac w4_bnd :=
  lazymatch goal with HK : know_ok _ ?E _ ?kn |- _ =>
    repeat match goal with
    | |- context [bv_unsigned (ev E ?j)] =>
        lazymatch goal with _ : _ <= bv_unsigned (ev E j) <= _ |- _ => fail | _ => idtac end;
        let r := eval vm_compute in (erange0 kn (EVar j)) in
        lazymatch r with Some (?lo, ?hi) =>
          let R := fresh "R" in pose proof (erange0_sound _ _ _ _ (EVar j) lo hi HK ltac:(vm_compute; reflexivity)) as R;
          cbn [edenot] in R end
    | |- context [bv_unsigned (edenot E ?e)] =>
        lazymatch goal with _ : _ <= bv_unsigned (edenot E e) <= _ |- _ => fail | _ => idtac end;
        let r := eval vm_compute in (erange0 kn e) in
        lazymatch r with Some (?lo, ?hi) =>
          let R := fresh "R" in pose proof (erange0_sound _ _ _ _ e lo hi HK ltac:(vm_compute; reflexivity)) as R end
    end
  end.

Ltac w4dj := cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
  unfold KXGoM.apart in *; repeat split; lia.

Lemma w4_x5 : forall E e dl tl rsv, edenot E e = Z_to_bv 64 dl -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv ->
  edenot E (EAlu ALU_AND (EAluw ALU_SUB (ELit 0) e) (ELit 63)) = Z_to_bv 64 (64 - tl).
Proof.
  intros E e dl tl rsv He Hd Ht Hr.
  apply bv_eq. cbn [edenot]. rewrite He, u_and64.
  set (v := alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 (Z_to_bv 64 dl))).
  assert (HV : bv_unsigned (sext 64 v) mod 2^32 = (- dl) mod 2^32).
  { pose proof (low32_unsigned (sext 64 v)) as L0. rewrite low32_sext64_32 in L0.
    unfold bv_wrap, bv_modulus in L0. change (2 ^ Z.of_N 32) with (2^32) in L0. rewrite <- L0.
    unfold v, alu32, alu. rewrite bv_sub_unsigned, !low32_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2 ^ Z.of_N 64) with (2^64).
    Z.div_mod_to_equations. lia. }
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  change (63 mod 2^64) with 63. change 63 with (Z.ones 6). rewrite Z.land_ones by lia.
  revert HV. generalize (bv_unsigned (sext 64 v)). intros V HV.
  Z.div_mod_to_equations. lia.
Qed.

Ltac w4_fix_x5 dl tl rsv :=
  repeat match goal with |- context [edenot ?E (EAlu ALU_AND (EAluw ALU_SUB (ELit 0) ?e) (ELit 63))] =>
    rewrite (w4_x5 E e dl tl rsv); [| w4ez; first [reflexivity | f_equal; lia] | lia | lia | lia] end.


Ltac w4_norm_to T :=
  repeat match goal with |- context [Z_to_bv 64 ?X] =>
    assert_fails (constr_eq X T); replace X with T by lia
  end.


Ltac w4_fix_srlw3 x :=
  repeat match goal with |- context [edenot ?E (EAluw ALU_SRL ?e (ELit 3))] =>
    rewrite (w4_srlw3 E e x); [| w4ez; first [reflexivity | f_equal; lia] | lia] end.

Ltac w4_phase_clear :=
  repeat match goal with
  | H : know_ok _ _ _ _ |- _ => clear H
  | H : log_flat _ _ |- _ => clear H
  end;
  try (change (mem_denot _ ?m []) with m);
  repeat match goal with E := kx_env _ _ |- _ => clear E end.


Lemma w4_br_nzk : forall E P Y,
  bv_unsigned (edenot E Y) < bv_unsigned (edenot E P) ->
  branch_taken BC_EQ
    (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P Y) (ELit 1))))
    (edenot E (ELit 0)) = false.
Proof.
  intros E P Y H.
  pose proof (bv_unsigned_in_range _ (edenot E P)) as [RP _].
  pose proof (bv_unsigned_in_range _ (edenot E Y)) as [RY _].
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E Y))).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E Y))).
    { apply Z.lxor_nonneg; split; intros; lia. }
    assert (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E Y)) <> 0).
    { intros HZ. pose proof (Z.lxor_eq _ _ HZ). lia. }
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E Y))) 1); [lia|].
  reflexivity.
Qed.

Ltac w4br5 :=
  lazymatch goal with
  | |- branch_taken BC_EQ (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
         (EAlu ALU_XOR ?P ?Y) (ELit 1)))) (edenot ?E (ELit 0)) = false =>
      apply (w4_br_nzk E P Y); w4uzm
  end.

Ltac w4_c4fix :=
  repeat match goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- _ =>
    rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end.


Section CANSEC1. Context {rc : runConstT}.
Lemma w4s34_hfx : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x7 x8 x9 x10 x12 x13 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 0 <= i -> 3 * seg + q + i <= dcap -> dcap < 3 * seg + q + i + 4 ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 8 <= off -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q + i)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 18446744073709551615) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 2) x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c024) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  Time kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 8 (2^32); KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 16 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q - i) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ first [ w4xbw | w4s34_xbs ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ first [ w4xbw | w4s34_xbs ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 1)) /\ _ =>
      apply (w4_shd_ap E X B O k); [ first [ w4xbw | w4s34_xbs | w4s34_xbt tl ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4br5.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q + i) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Lemma w4s34_hz : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x7 x8 x9 x10 x12 x13 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 0 <= i -> 3 * seg + q + i <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> off = 0 -> 1 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q + i)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 18446744073709551615) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 2) x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c024) fc None mm (seg_rom bsegs)).
Proof.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  Time kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 0; KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange i 0 (2^32); KZRange c 0 (2^64 - 1); KZRange len 1 (2^32); KZRange (len - off) 1 (2^32);
       KZRange (dcap - 3 * seg - q - i) 0 (2^32);
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ first [ w4xbw | w4s34_xbs ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ first [ w4xbw | w4s34_xbs ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 1)) /\ _ =>
      apply (w4_shd_ap E X B O k); [ first [ w4xbw | w4s34_xbs | w4s34_xbt tl ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try w4br5.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q + i) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- evtF _ _ _ _ =>
      repeat match goal with HA : KXGoM.apart _ _ (_ + -480) 480 |- _ =>
        let H' := fresh "APS" in pose proof HA as H'; unfold KXGoM.apart in H'; revert HA end; intros end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

End CANSEC1.

