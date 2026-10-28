(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_0b RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx42_5 RZ_huf_dx42_6 RZ_huf_dx42_8.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_9.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis NBOK : huf_nb_ok true dtb tl.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation WDF := [(DST, DST + dcap); (SPV - 912, SPV - 616)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -912)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -912) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation SINV := RZ_huf_dx41.SINV.
  Notation WD4 := [(DST, DST + dcap); (SPV - 776, SPV - 736)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -776) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD3 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -736) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD2 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -696) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -656) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).

  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X42P := (RZ_huf_dx42_5.X42P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x42p_transport := (RZ_huf_dx42_5.x42p_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation sbuf_transport := (RZ_huf_dx42_5.x42_sbuf_transport SPV DST dcap DT lo dtb CTX).
  Notation HINV := RZ_huf_dx41g.HINV.
  Notation x42_it := (RZ_huf_dx42_8.x42_it ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).
  Notation x42_c0 := (RZ_huf_dx42_6.x42_c0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).

  Lemma x42_m1 : forall (k : nat) mm rest j1 j2 j3 j4 e1 e2 e3 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl
      (k1 k2 k3 k4 : word) pad1 pad2 pad3 pad4
      (x7 x8 x10 x12 x13 x14 x21 x22 x24 x26 x30 : word)
      (w0 w8 : word),
    X42P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + e3)) (Z_to_bv 64 dcap) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (DST + dcap - 7)) w8 k4 k2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 (DST + e2)) k1 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DT + 4)) ->
    BD1 mm k1 (Z_to_bv 64 c1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
    BD2 mm k2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    BD3 mm k3 (Z_to_bv 64 c3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    BD4 mm k4 (Z_to_bv 64 c4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    HINV o1 n1 c1 -> HINV o2 n2 c2 -> HINV o3 n3 c3 -> HINV o4 n4 c4 ->
    dcap - j4 <= Z.of_nat k -> j4 + 8 <= dcap -> e3 <= j4 ->
    0 <= j1 <= 2 * (j4 - e3) -> e1 <= j2 <= e1 + 2 * (j4 - e3) -> e2 <= j3 <= e2 + 2 * (j4 - e3) ->
    0 <= e1 <= e2 -> e2 <= e3 -> e3 <= dcap -> dcap + e2 <= 2 * e3 + 8 ->
    dl = tl + 256 * rsv -> sh = 64 - tl ->
    evt usegs POST (ST 0x26000 mm (Z_to_bv 64 c2) (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 (DT + 4)) x7 x8 (Z_to_bv 64 c1) x10 (Z_to_bv 64 (DST + j1)) x12 x13 x14 (Z_to_bv 64 (2^61)) (Z_to_bv 64 sh) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (DST + j4)) k3 (Z_to_bv 64 (DST + j3)) x21 x22 (Z_to_bv 64 c3) x24 (Z_to_bv 64 c4) x26 (Z_to_bv 64 (DST + j2)) (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (S1 + o1)) x30 (Z_to_bv 64 (DST + dcap))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH];
      intros mm rest j1 j2 j3 j4 e1 e2 e3 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl k1 k2 k3 k4 pad1 pad2 pad3 pad4
        x7 x8 x10 x12 x13 x14 x21 x22 x24 x26 x30
        w0 w8 PV MI OUT DTB FA BS1 BS2 BS3 BS4 SB1 SB2 SB3 SB4 HI1 HI2 HI3 HI4 HK HROOM HE3J HJ1 HJ2 HJ3 HE1 HE2 HE3 HSEG HDL HSH; [exfalso; lia|].
    eapply (x42_it mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 k1 k2 k3 k4 pad1 pad2 pad3 pad4);
      try eassumption; try lia.
    - (* [comment removed for export] *)
      intros mm' T1 T2 T3 T4 P1 P2 P3 P4 c1' c2' c3' c4' k1' k2' k3' k4' w8' ? ? ? ? ? ? ? ? ? ? ? MU' WM' MI' OUT' DTB' FA' BD1' BD2' BD3' BD4' HI1' HI2' HI3' HI4' HT1 HT2 HT3 HT4 HRM.
      replace T1 with (DST + (T1 - DST)) by lia. replace T2 with (DST + (T2 - DST)) by lia.
      replace T3 with (DST + (T3 - DST)) by lia. replace T4 with (DST + (T4 - DST)) by lia.
      replace P1 with (S1 + (P1 - S1)) by lia. replace P3 with (S3 + (P3 - S3)) by lia. replace P4 with (S4 + (P4 - S4)) by lia.
      replace P1 with (S1 + (P1 - S1)) in BD1' by lia. replace P2 with (S2 + (P2 - S2)) in FA' by lia.
      replace P2 with (S2 + (P2 - S2)) in BD2' by lia. replace P3 with (S3 + (P3 - S3)) in BD3' by lia.
      replace P4 with (S4 + (P4 - S4)) in BD4' by lia.
      eapply (IH mm' rest (T1 - DST) (T2 - DST) (T3 - DST) (T4 - DST) e1 e2 e3 sh S1 n1 b1 (P1 - S1) c1' S2 n2 b2 (P2 - S2) c2'
                 S3 n3 b3 (P3 - S3) c3' S4 n4 b4 (P4 - S4) c4' dl).
      all: first [ exact MI' | exact OUT' | exact DTB' | exact FA' | exact BD1' | exact BD2' | exact BD3' | exact BD4' | exact HI1' | exact HI2' | exact HI3' | exact HI4' | exact HDL | exact HSH
                 | lia
                 | eapply x42p_transport; first [exact PV | exact MU' | exact WM']
                 | eapply sbuf_transport; first [exact SB1 | exact SB2 | exact SB3 | exact SB4 | exact MU'] ].
    - (* [comment removed for export] *)
      intros mm' T1 T2 T3 T4 P1 P2 P3 P4 c1' c2' c3' c4' k1' k2' k3' k4' w8' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU' WM' MI' OUT' DTB' FA' BD1' BD2' BD3' BD4' HI1' HI2' HI3' HI4'
        HC1 HC2 HC3 HC4 HT1 HT2 HT3 HT4.
      replace T1 with (DST + (T1 - DST)) by lia. replace T2 with (DST + (T2 - DST)) by lia.
      replace T3 with (DST + (T3 - DST)) by lia. replace T4 with (DST + (T4 - DST)) by lia.
      replace P1 with (S1 + (P1 - S1)) in BD1' by lia. replace P2 with (S2 + (P2 - S2)) in FA' by lia.
      replace P2 with (S2 + (P2 - S2)) in BD2' by lia. replace P3 with (S3 + (P3 - S3)) in BD3' by lia.
      replace P4 with (S4 + (P4 - S4)) in BD4' by lia.
      eapply (x42_c0 mm' rest (T1 - DST) (T2 - DST) (T3 - DST) (T4 - DST) e1 e2 e3 dcap S1 n1 b1 (P1 - S1) c1' S2 n2 b2 (P2 - S2) c2'
                 S3 n3 b3 (P3 - S3) c3' S4 n4 b4 (P4 - S4) c4' dl k1' k2' k3' k4' pad1 pad2 pad3 pad4).
      all: first [ exact HC1 | exact HC2 | exact HC3 | exact HC4 | first [ exact MI' | exact OUT' | exact DTB' | exact FA' | exact BD1' | exact BD2' | exact BD3' | exact BD4' | exact HI1' | exact HI2' | exact HI3' | exact HI4' | exact HDL | exact HSH
                 | lia
                 | eapply x42p_transport; first [exact PV | exact MU' | exact WM']
                 | eapply sbuf_transport; first [exact SB1 | exact SB2 | exact SB3 | exact SB4 | exact MU'] ] ].
  Qed.

  (* [comment removed for export] *)
  Lemma x42_m0 : forall mm rest e1 e2 e3 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl
      (k1 k2 k3 k4 : word) pad1 pad2 pad3 pad4
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w14 : word),
    X42P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 (DST + e2)) w14 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DT + 4)) ->
    BD1 mm k1 (Z_to_bv 64 c1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
    BD2 mm k2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    BD3 mm k3 (Z_to_bv 64 c3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    BD4 mm k4 (Z_to_bv 64 c4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    HINV o1 n1 c1 -> HINV o2 n2 c2 -> HINV o3 n3 c3 -> HINV o4 n4 c4 ->
    0 <= e1 <= e2 -> e2 <= e3 -> e3 <= dcap -> dcap + e2 <= 2 * e3 + 8 ->
    dl = tl + 256 * rsv ->
    evt usegs POST (ST 0x25f54 mm x1 x5 x6 x7 (Z_to_bv 64 DST) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + e2)) (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + e3)) x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest e1 e2 e3 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl k1 k2 k3 k4 pad1 pad2 pad3 pad4
      x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w14 PV MI OUT DTB FA BS1 BS2 BS3 BS4 SB1 SB2 SB3 SB4 HI1' HI2' HI3' HI4' HE1 HE2 HE3 HSEG HDL.
    assert (MU' : munch WDF mm mm) by apply munch_refl.
    assert (WM' : wmono usegs mm mm) by apply wmono_refl.
    pose proof (proj1 HI1') as C1. pose proof (proj1 HI2') as C2. pose proof (proj1 HI3') as C3. pose proof (proj1 HI4') as C4.
    kx_autoLx [0x26000; 0x26928] 80%nat
      [KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47);
       KZRange SPV 4096 (2^47); KZRange dl 0 65536; KZRange c1 0 64; KZRange c2 0 64; KZRange c3 0 64; KZRange c4 0 64;
       KZWr (SPV - 912) 136;
       KZDisj (SPV - 912) 296 DST dcap; KZDisj (SPV - 912) 296 DT 16388]
      [(SPV - 912, 136); (SPV - 776, 40); (SPV - 736, 40); (SPV - 696, 40); (SPV - 656, 40)].
    all: kx_mem.
    all: try replace (DST + dcap + -7) with (DST + dcap - 7) in * by lia.
    all: lazymatch goal with
         | MU' : munch _ _ ?m2, WM' : wmono _ _ ?m2, MI' : mem_inv _ ?m2, OUT' : stk _ ?m2 _ _, DTB' : bytes_at _ ?m2 DT _, FA' : rw_cells _ ?m2 (SPV + -912) _,
           BD1' : rw_cells _ ?m2 (SPV + -656) _, BD2' : rw_cells _ ?m2 (SPV + -696) _, BD3' : rw_cells _ ?m2 (SPV + -736) _,
           BD4' : rw_cells _ ?m2 (SPV + -776) _ |- evt _ _ (MS _ _ (Z_to_bv 64 155648) _ _ ?m2 _) =>
             subst dl; rewrite (neg_dl_sh tl rsv TL) in *;
             let HM := fresh "HM" in
             pose proof (x42_m1 (Z.to_nat dcap) m2 rest 0) as HM; replace (DST + 0) with DST in HM by lia;
             eapply (HM e1 e2 e3 e1 e2 e3 (64 - tl) S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 (tl + 256 * rsv));
             first [ reflexivity | first [ exact MI' | exact OUT' | exact DTB' | exact FA' | exact BD1' | exact BD2' | exact BD3' | exact BD4' | exact HI1' | exact HI2' | exact HI3' | exact HI4' | exact HDL | exact HSH
                 | lia
                 | eapply x42p_transport; first [exact PV | exact MU' | exact WM']
                 | eapply sbuf_transport; first [exact SB1 | exact SB2 | exact SB3 | exact SB4 | exact MU'] ] ]
         | MU' : munch _ _ ?m2, WM' : wmono _ _ ?m2, MI' : mem_inv _ ?m2, OUT' : stk _ ?m2 _ _, DTB' : bytes_at _ ?m2 DT _, FA' : rw_cells _ ?m2 (SPV + -912) _,
           BD1' : rw_cells _ ?m2 (SPV + -656) _, BD2' : rw_cells _ ?m2 (SPV + -696) _, BD3' : rw_cells _ ?m2 (SPV + -736) _,
           BD4' : rw_cells _ ?m2 (SPV + -776) _ |- evt _ _ (MS _ _ (Z_to_bv 64 157992) _ _ ?m2 _) =>
             let HC := fresh "HC" in
             pose proof (x42_c0 m2 rest 0) as HC; replace (DST + 0) with DST in HC by lia;
             eapply (HC e1 e2 e3 e1 e2 e3 dcap S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl k1 k2 k3 k4 pad1 pad2 pad3 pad4);
             first [ first [ exact MI' | exact OUT' | exact DTB' | exact FA' | exact BD1' | exact BD2' | exact BD3' | exact BD4' | exact HI1' | exact HI2' | exact HI3' | exact HI4' | exact HDL | exact HSH
                 | lia
                 | eapply x42p_transport; first [exact PV | exact MU' | exact WM']
                 | eapply sbuf_transport; first [exact SB1 | exact SB2 | exact SB3 | exact SB4 | exact MU'] ]
                   | intro; unfold RZ_huf_dx41.SINV; unfold RZ_huf_dx41g.HINV in HI1', HI2', HI3', HI4'; lia
                   | unfold RZ_huf_dx41g.HINV in HI1', HI2', HI3', HI4'; lia ]
         end.
  Qed.

End DX42_9.
