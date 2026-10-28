(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AF_huf_w4s3b AF_huf_w4s33z AF_huf_w4s33k.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import ABase AHarness_iface AF_huf_reloadi AF_huf_w4s32k3 AFrameD.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw Stdio_pure.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Set Ltac Backtrace. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation amem := (word -> option byte).


Section CANSEC1. Context {rc : runConstT}.
Lemma w4s33_e3z : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> off = 0 -> 1 <= len -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until len. intros CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; destruct (Z_le_gt_dec b 64) as [HB|HB]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354] 300%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 0; KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 1 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354] 300%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 0; KZRange b 65 (2^31 - 1); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 1 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354] 300%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 0; KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 1 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354] 300%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 0; KZRange b 65 (2^31 - 1); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 1 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  ].
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) =>
      replace (Z_to_bv 64 (DST + 2 * seg + q)) with (Z_to_bv 64 (DST + 2 * seg + q + 0)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end).
  all: try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A ?ob |- evtF _ _ _ _ =>
      pose proof (kx_u8arr_replay bsegs E m log A ob HU KXLF) as HU'; clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(SP + -184, SP + -144)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - 0))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- munch _ _ _ => eapply munch_weaken; [ | exact MUW]; apply w4s33_sub1 end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end).
  all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with MW : munch ?W ?m ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
  all: try lia.
Qed.

Lemma w4s33_br_eqw : forall E P B,
  bv_unsigned (edenot E B) <= 64 -> 64 < bv_unsigned (edenot E P) ->
  branch_taken BC_EQ
    (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P (EAluw ALU_SRL B (ELit 3))) (ELit 1))))
    (edenot E (ELit 0)) = false.
Proof.
  intros E P B HB HP.
  pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64.
  rewrite (u_srlw_small (edenot E B) (Z_to_bv 64 3) 3) by
    (first [reflexivity | lia | change (2 ^ (3 mod 32)) with 8; Z.div_mod_to_equations; lia]).
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  change (2 ^ (3 mod 32)) with 8.
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
    { apply Z.lxor_nonneg; split; intros; Z.div_mod_to_equations; lia. }
    assert (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8) <> 0).
    { assert (HB8 : bv_unsigned (edenot E B) / 8 <= 8) by (apply Z.div_le_upper_bound; lia).
      intros H0. pose proof (Z.lxor_eq _ _ H0). lia. }
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)) 1); [lia|].
  reflexivity.
Qed.

Ltac w4s33_breqw :=
  lazymatch goal with
  | |- branch_taken BC_EQ (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
         (EAlu ALU_XOR ?P (EAluw ALU_SRL ?B (ELit 3))) (ELit 1)))) (edenot ?E (ELit 0)) = false =>
      apply (w4s33_br_eqw E P B); w4uz
  end.

Lemma w4s33_br_eqy : forall E P Y,
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

Ltac w4s33_breqy :=
  lazymatch goal with
  | |- branch_taken BC_EQ (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
         (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = false =>
      apply (w4s33_br_eqy E P (ELit k)); w4uz
  end.

Ltac e3_pre m S off b A2 L2 A3 L3 KD DST seg q SP :=
  try w4s33_breqw; try w4s33_breqy; try w4br; try w4word4; try w4shd;
  try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end);
  try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ w4xbw | lia | lia | w4uz | w4uz | w4apz ] end);
  try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; rewrite ?Z.add_assoc end);
  try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) =>
      replace (Z_to_bv 64 (DST + 2 * seg + q)) with (Z_to_bv 64 (DST + 2 * seg + q + 0)) by (f_equal; lia) end);
  try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ => kx_frame H end end end);
  try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD; w4_cells_post end);
  try (lazymatch goal with |- evtF _ _ _ _ => w4_ptr_fix S off b end);
  try (lazymatch goal with H : rw_cells _ _ _ [C4 (edenot ?E ?e)] |- evtF _ _ _ _ =>
      rewrite <- (Z_to_bv_bv_unsigned (edenot E e)) in H end);
  try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end);
  try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m0 ?A ?ob |- evtF _ _ _ _ =>
      let HU' := fresh "HU'" in pose proof (kx_u8arr_replay bsegs E m0 log A ob HU KXLF) as HU'; clear HU end);
  try (lazymatch goal with |- evtF _ _ _ _ =>
      let MUW := fresh "MUW" in
      pose proof (munch_refl [(SP + -184, SP + -144)] m) as MUW;
      kx_munch_wins MUW [(SP + -184, 40)] end);
  try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).

Ltac e3_apps m S off b A2 L2 A3 L3 KD DST seg q SP :=
  try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bff0) _ _ _ _) => eapply KD end);
  try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bee4) _ _ _ _) => eapply w4s33_ts3 end);
  try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bef8) _ _ _ _) =>
      eapply (w4s33_t3 (Z.to_nat (seg - q - 0))) with (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end).

Ltac e3_fin m S off b A2 L2 A3 L3 KD DST seg q SP :=
  try (lazymatch goal with |- rw_cells _ _ (_ + -184) _ => kx_cells_merge end);
  try (lazymatch goal with MW : munch [(_ + -184, _ + -144)] _ _ |- munch _ _ _ =>
      eapply munch_weaken; [ | exact MW]; apply w4s33_sub1 end);
  try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => w4_rng_all; lia | |- 0 <= _ < 2 ^ 32 => w4_rng_all; lia end);
  try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end);
  try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end);
  try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end);
  try (lazymatch goal with MW : munch ?W ?m1 ?m' |- unpoisoned ?m' ?lo ?hi =>
      apply (unpoisoned_munch W m1 m' lo hi); [assumption | exact MW |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end);
  try (lazymatch goal with MW : munch ?W ?m1 ?m' |- ztab_fact _ ?m' ?A ?N _ _ =>
      apply (w4_ztab_munch m1 m' W A N); [assumption | exact MW | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end);
  try (lazymatch goal with |- context [bv_unsigned (edenot ?E (EAluw ALU_SRL ?e (ELit 3)))] =>
    lazymatch goal with |- 0 <= ?x + _ < _ =>
      rewrite (w4_srlw3 E e x); [Z.div_mod_to_equations; lia | w4ez; first [reflexivity | f_equal; lia] | lia] end end);
  try (lazymatch goal with |- 0 <= _ <= 64 => first [w4b8 | w4_rng_all; lia] end);
  try lia.

Ltac e3_post m S off b A2 L2 A3 L3 KD DST seg q SP :=
  e3_pre m S off b A2 L2 A3 L3 KD DST seg q SP; e3_apps m S off b A2 L2 A3 L3 KD DST seg q SP; e3_fin m S off b A2 L2 A3 L3 KD DST seg q SP.

Lemma w4s33_e3k : forall (Q : machine_state -> Prop) (RNG : footprint) (mm0 mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp : word) (pad1 : list byte) (SP DST dcap seg q DT dl lo : Z),
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm0 mm' -> wmono bsegs mm0 mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm0 mm -> wmono bsegs mm0 mm ->
  stk bsegs mm lo (SP + -480) -> DST + dcap <= lo ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))).
Proof.
  intros until lo. intros K0 MU0 WM0 STK HLO.
  intros mm' ob' cw' bw' pw' aw' ew' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 MU' WM' MI' U' UL' RW'.
  eapply K0.
  - eapply munch_trans; [exact MU0 | eapply munch_weaken; [ | exact MU']; unfold sub_fp; intros; cbn [outside] in *; tauto].
  - eapply wmono_trans; [exact WM0 | exact WM'].
  - exact MI'.
  - eapply stk_transportD; [exact STK | exact MU' | cbn [disjoint_from]; lia].
  - exact U'.
  - exact UL'.
  - exact RW'.
Qed.

Lemma w4s33_e3k2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm0 mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp : word) (pad1 : list byte) (SP DST dcap seg q DT dl : Z),
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm0 mm' -> wmono bsegs mm0 mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm0 mm -> wmono bsegs mm0 mm ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))).
Proof.
  intros until dl. intros K0 MU0 WM0.
  intros mm' ob' cw' bw' pw' aw' ew' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 MU' WM' MI' U' UL' RW'.
  eapply K0.
  - eapply munch_trans; [exact MU0 | exact MU'].
  - eapply wmono_trans; [exact WM0 | exact WM'].
  - exact MI'.
  - exact U'.
  - exact UL'.
  - exact RW'.
Qed.

Lemma w4s33_e3t : forall (Q : machine_state -> Prop) (RNG : footprint) (mm0 mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pw aw ew : word)
    (pad1 : list byte) (cbs ob : list byte) (SP DST dcap seg q DT dl b c tl rsv : Z),
  munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm0 mm -> wmono bsegs mm0 mm ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 pw; C8 aw; C8 ew] ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A2 L2 A3 L3 : Z), A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A2 -> 0 <= A3 ->
  A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -480) 480 ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) ->
  KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm0 mm' -> wmono bsegs mm0 mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + 3 * seg)) x9 x10 x11
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 (0x8bdbc + 288)) fc None mm (seg_rom bsegs)).
Proof.
  intros until rsv. intros MU0 WM0 CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  pose proof (w4s33_e3k2 Q RNG mm0 mm F fc gp tp pad1 SP DST dcap seg q DT dl K0 MU0 WM0) as KD.
  clear K0 MU0 WM0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [(0x8bdbc + 288); 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; 0x8bdbc] 300%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b;
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (DT + 4, 2 * 2^tl)] [(DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [(0x8bdbc + 288); 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; 0x8bdbc] 300%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b;
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (DT + 4, 2 * 2^tl)] [(DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post mm 0 0 b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Ltac e3_post3 m S off b A2 L2 A3 L3 KD DST seg q SP :=
  e3_pre m S off b A2 L2 A3 L3 KD DST seg q SP; e3_apps m S off b A2 L2 A3 L3 KD DST seg q SP;
  try (lazymatch goal with |- evtF _ _ _ _ => eapply w4s33_e3t with (mm0 := m) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) end);
  e3_fin m S off b A2 L2 A3 L3 KD DST seg q SP.

Lemma w4s33_e3o : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  64 < b ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354] 300%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 (2^32); KZRange b 65 (2^31 - 1); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 0 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354] 300%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 (2^32); KZRange b 65 (2^31 - 1); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 0 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3a : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  b <= 64 -> off = 0 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 0; KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 0 (2^32); KZRange (seg - q) 0 3; KZRange (dcap - 2 * seg - q) 0 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3f : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  b <= 64 -> 8 <= off ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB H8 CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354] 300%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 8 (2^32); KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 16 (2^32); KZRange (seg - q) 0 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  kx_post_regs. rewrite ?Z.add_assoc.
  eapply w4_rl_call with (lo := lo) (S := S) (bc := b) (q := off) (cont := Z_to_bv 64 c) (jp := pad1) (bs := map bv_unsigned bs).
  - unfold reload_cellsA. exact CD.
  - rewrite zbytes_map_unsigned'. eassumption.
  - apply map_unsigned_range.
  - Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - rewrite length_map. replace (S + Z.of_nat (length bs)) with (S + len) by lia. eassumption.
  - lia.
  - lia.
  - rewrite length_map. lia.
  - exact STK.
  - lia.
  - unfold RELOADI_STACK. lia.
  - eassumption.
  - eassumption.
  - replace (SP + -184 + 40) with (SP + -144) by lia. eassumption.
  - rewrite length_map. replace (S + Z.of_nat (length bs)) with (S + len) by lia. eassumption.
  - eapply (rng_sub RNG (SP + -480) 480); [eassumption | lia | lia].
  - eassumption.
  - rewrite length_map. replace (Z.of_nat (length bs)) with len by lia. eassumption.
  - rewrite length_map. eapply (rng_sub RNG (shad A1) (shlen (L1 + 7))); [eassumption | | ];
      unfold shad, shlen, nshad; rewrite ?Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia.
  - unfold RELOADI_STACK. replace (SP + -480 - 16) with (SP + -496) by lia. eassumption.
  - eassumption.
  - eassumption.
  - intros m' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 MU WM MI' STK' RW'.
    unfold RELOADI_STACK in MU. replace (SP + -184 + 40) with (SP + -144) in MU by lia.
    replace (SP + -480 - 16) with (SP + -496) in MU by lia.
    rewrite ret_pc_even by (first [lia | reflexivity]).
    pose proof (w4s33_e3k Q RNG mm m' F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
      ltac:(eapply munch_weaken; [ | exact MU]; unfold sub_fp; intros; cbn [outside] in *; tauto) WM STK' ltac:(lia)) as KD.
    unfold reload_cellsA in RW'.
    rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 (HufWalkKit.le64v (map bv_unsigned bs) (off - b / 8)))) in RW'.
    pose proof (bv_unsigned_in_range _ (Z_to_bv 64 (HufWalkKit.le64v (map bv_unsigned bs) (off - b / 8)))) as HC'.
    unfold bv_modulus in HC'. change (Z.of_N 64) with 64 in HC'.
    assert (UZ1 : unpoisoned m' (DT + 4) (DT + 4 + 2 * 2^tl)).
    { eapply (unpoisoned_munch _ mm m' (DT + 4) (DT + 4 + 2 * 2^tl)); [assumption | exact MU | ].
      cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia. }
    assert (UZ2 : unpoisoned m' DST (DST + dcap)).
    { eapply (unpoisoned_munch _ mm m' DST (DST + dcap)); [assumption | exact MU | ].
      cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia. }
    assert (ZT' : ztab_fact bsegs m' (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]).
    { eapply (w4_ztab_munch mm m' _ (DT + 4) (2 * 2^tl)); [assumption | exact MU | | lia | lia].
      cbn [disjoint_from]; unfold KXGoM.apart in *; lia. }
    eapply w4s33_e3t with (mm0 := m') (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3).
    all: try apply munch_refl.
    all: try apply wmono_refl.
    all: try exact KD.
    all: try exact RW'.
    all: try exact MI'.
    all: try (lazymatch goal with |- rw_cells _ _ (_ + -480) _ =>
        eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [disjoint_from cells_size csize]; lia] end).
    all: try (lazymatch goal with |- bytes_at _ _ ?A ?l =>
        eapply (bytes_at_transport bsegs _ mm _ A l); [eassumption | exact MU | cbn [disjoint_from]; unfold KXGoM.apart in *; lia] end).
    all: try (lazymatch goal with |- u8arr _ _ ?A ?l =>
        eapply (u8arr_transportD bsegs _ mm _ A l); [eassumption | exact MU | cbn [disjoint_from]; lia] end).
    all: try (lazymatch goal with |- unpoisoned ?m1 ?lo0 ?hi0 =>
        apply (unpoisoned_munch _ mm m1 lo0 hi0); [eassumption | exact MU |
          cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
    all: try (lazymatch goal with |- ztab_fact _ ?m1 ?A ?N _ _ =>
        apply (w4_ztab_munch mm m1 _ A N); [eassumption | exact MU | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
    all: try (lazymatch goal with |- 0 <= _ < _ => fail | |- 0 <= _ <= _ => fail | |- _ <= _ => fail | |- _ < _ => fail | |- _ = Z.of_nat _ => fail | _ => eassumption end).
    all: try lia.
Qed.

Lemma w4s33_e3c1a : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  b <= 15 -> off = 1 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 1; KZRange b 0 15; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 1; KZRange b 0 15; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3c1b : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  16 <= b -> b <= 64 -> off = 1 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB1 HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 1; KZRange b 16 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 1; KZRange b 16 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3c2a : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  b <= 23 -> off = 2 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 2 2; KZRange b 0 23; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 10 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 2 2; KZRange b 0 23; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 10 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3c2b : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  24 <= b -> b <= 64 -> off = 2 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB1 HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 2 2; KZRange b 24 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 10 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 2 2; KZRange b 24 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 10 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3c3a : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  b <= 31 -> off = 3 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 3 3; KZRange b 0 31; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 11 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 3 3; KZRange b 0 31; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 11 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3c3b : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  32 <= b -> b <= 64 -> off = 3 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB1 HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 3 3; KZRange b 32 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 11 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 3 3; KZRange b 32 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 11 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3c4a : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  b <= 39 -> off = 4 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 4 4; KZRange b 0 39; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 12 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 4 4; KZRange b 0 39; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 12 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3c4b : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  40 <= b -> b <= 64 -> off = 4 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB1 HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 4 4; KZRange b 40 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 12 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 4 4; KZRange b 40 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 12 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3c5a : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  b <= 47 -> off = 5 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 5 5; KZRange b 0 47; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 13 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 5 5; KZRange b 0 47; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 13 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3c5b : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  48 <= b -> b <= 64 -> off = 5 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB1 HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 5 5; KZRange b 48 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 13 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 5 5; KZRange b 48 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 13 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3c6a : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  b <= 55 -> off = 6 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 6 6; KZRange b 0 55; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 14 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 6 6; KZRange b 0 55; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 14 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3c6b : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  56 <= b -> b <= 64 -> off = 6 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB1 HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 6 6; KZRange b 56 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 14 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 6 6; KZRange b 56 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 14 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3c7a : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  b <= 63 -> off = 7 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 7 7; KZRange b 0 63; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 15 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 7 7; KZRange b 0 63; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 15 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3c7b : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  64 <= b -> b <= 64 -> off = 7 ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros HB1 HB HO CF CD. intros.
  match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into K0 end.
  match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
  pose proof (w4s33_e3k Q RNG mm mm F fc gp tp pad1 SP DST dcap seg q DT dl lo K0
    ltac:(apply munch_refl) ltac:(apply wmono_refl) STK ltac:(lia)) as KD.
  clear K0.
  destruct (Z.eq_dec (seg - q) 0) as [HE|HE]; [
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 7 7; KZRange b 64 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 15 (2^32); KZRange (seg - q) 0 0; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
  |
    kx_runFLd [0x8bdbc; 0x8bee4; 0x8bff0; 0x8bfd8; 0x8b9d0; 0x8bef8; 0x8e354; (0x8bdbc + 288)] 300%nat (repeat false 64)
      [KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 7 7; KZRange b 64 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 15 (2^32); KZRange (seg - q) 1 3; KZRange (dcap - 2 * seg - q) 0 (2^32); KZRange (len - off) 8 (2^32);
       KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (S + off); KZWord (SP + -160) 8 S; KZWord (SP + -152) 8 (S + 8);
       KZWr (SP + -184) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)] ].
  all: e3_post3 mm S off b A2 L2 A3 L3 KD DST seg q SP.
Qed.

Lemma w4s33_e3 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len lo : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo -> artcells mm ->
  rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + len) ->
  unpoisoned mm (SP + -184) (SP + -144) -> rng RNG (shad (SP + -184)) 5 -> rng RNG (SP + -496) 16 ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) (Z_to_bv 64 (seg - q))
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bdbc) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros CF CD. intros.
  destruct (Z_le_gt_dec b 64) as [CB|CB].
  2: { eapply w4s33_e3o with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
        (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia. }
  destruct (Z.eq_dec off 0) as [CO|CO].
  { eapply w4s33_e3a with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
        (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia. }
  destruct (Z_le_gt_dec 8 off) as [C8|C8].
  { eapply w4s33_e3f with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
        (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia. }
  assert (CO7 : off = 1 \/ off = 2 \/ off = 3 \/ off = 4 \/ off = 5 \/ off = 6 \/ off = 7) by lia.
  destruct CO7 as [CO7 | [CO7 | [CO7 | [CO7 | [CO7 | [CO7 | CO7]]]]]].
  - destruct (Z_le_gt_dec b 15) as [CB1|CB1].
    + eapply w4s33_e3c1a with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
          (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia.
    + eapply w4s33_e3c1b with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
          (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia.
  - destruct (Z_le_gt_dec b 23) as [CB1|CB1].
    + eapply w4s33_e3c2a with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
          (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia.
    + eapply w4s33_e3c2b with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
          (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia.
  - destruct (Z_le_gt_dec b 31) as [CB1|CB1].
    + eapply w4s33_e3c3a with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
          (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia.
    + eapply w4s33_e3c3b with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
          (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia.
  - destruct (Z_le_gt_dec b 39) as [CB1|CB1].
    + eapply w4s33_e3c4a with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
          (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia.
    + eapply w4s33_e3c4b with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
          (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia.
  - destruct (Z_le_gt_dec b 47) as [CB1|CB1].
    + eapply w4s33_e3c5a with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
          (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia.
    + eapply w4s33_e3c5b with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
          (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia.
  - destruct (Z_le_gt_dec b 55) as [CB1|CB1].
    + eapply w4s33_e3c6a with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
          (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia.
    + eapply w4s33_e3c6b with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
          (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia.
  - destruct (Z_le_gt_dec b 63) as [CB1|CB1].
    + eapply w4s33_e3c7a with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
          (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia.
    + eapply w4s33_e3c7b with (S := S) (off := off) (b := b) (c := c) (len := len) (lo := lo) (tl := tl) (rsv := rsv) (bs := bs) (cbs := cbs) (ob := ob) (pad1 := pad1)
          (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; lia.
Qed.

End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
