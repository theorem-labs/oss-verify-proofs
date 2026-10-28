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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_0b RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx42_5 RZ_huf_dx42_10 huf411_kit_rs huf421_kit_c1_entry.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_11.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  Hypothesis BITINIT : bit_init_stmt.
  Hypothesis SPVA : rsk_al SPV 16.
  Hypothesis DTA : rsk_al DT 4.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
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

  Notation WDF := [(DST, DST + dcap); (SPV - 912, SPV - 616)].
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X42P := (RZ_huf_dx42_5.X42P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x42p_transport := (RZ_huf_dx42_5.x42p_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation sbuf_transport := (RZ_huf_dx42_5.x42_sbuf_transport SPV DST dcap DT lo dtb CTX).
  Notation x42_ret := (RZ_huf_dx42_5.x42_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation HINV := RZ_huf_dx41g.HINV.
  Notation x42_i4 := (RZ_huf_dx42_10.x42_i4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK BITINIT SPVA DTA).
  (* [comment removed for export] *)
  Ltac x42_bc_enum V :=
    let BCE := fresh "BCE" in
    lazymatch V with
    | context [bv_unsigned (edenot ?E ?e)] =>
        let X := constr:(bv_unsigned (edenot E e)) in
        let f := lazymatch (eval pattern X in V) with ?f _ => f end in
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          first [ kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (f v) mod 2^64) && ((f v) mod 2^64 <=? 8))%bool
                | kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (f v) mod 2^64) && ((f v) mod 2^64 <=? 64))%bool ]
        end;
        cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2
    end.

  Lemma x42_i3 : forall mm rest e1 S1 n1 b1 k1 c1 pad1 S2 n2 b2 k2 c2 pad2 S3 n3 b3 k3 c3 pad3 S4 n4 b4 dl junk4
      (y8 y10 y11 y12 y19 y24 y25 y26 y27 : Z)
      (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w14 : word),
    X42P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 (DST + 2 * e1)) w14
        (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DT + 4)) ->
    rw_cells usegs mm (SPV + -656) (bitd_cells k1 (Z_to_bv 64 c1) pad1 (bitd_ptr S1 n1) S1) ->
    rw_cells usegs mm (SPV + -696) (bitd_cells k2 (Z_to_bv 64 c2) pad2 (bitd_ptr S2 n2) S2) ->
    rw_cells usegs mm (SPV + -736) (bitd_cells k3 (Z_to_bv 64 c3) pad3 (bitd_ptr S3 n3) S3) ->
    rw_cells usegs mm (SPV + -776) [CB 40 junk4] ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    1 <= c1 <= 64 -> (8 <= n1 -> c1 <= 8) -> 1 <= c2 <= 64 -> (8 <= n2 -> c2 <= 8) -> 1 <= c3 <= 64 -> (8 <= n3 -> c3 <= 8) ->
    0 <= e1 -> 3 * e1 <= dcap -> dcap <= 4 * e1 -> dl = tl + 256 * rsv ->
    y8 mod 2^64 = DST mod 2^64 -> y10 mod 2^64 = (SPV + -776) mod 2^64 -> y11 mod 2^64 = S4 mod 2^64 ->
    y12 mod 2^64 = n4 mod 2^64 -> y19 mod 2^64 = (-120) mod 2^64 ->
    y24 mod 2^64 = dl mod 2^64 -> y25 mod 2^64 = (DST + 2 * e1) mod 2^64 -> y26 mod 2^64 = dcap mod 2^64 ->
    y27 mod 2^64 = (DST + 3 * e1) mod 2^64 ->
    evt usegs POST (ST 0x25f48 mm x1 x5 x6 x7 (Z_to_bv 64 y8) x9 (Z_to_bv 64 y10) (Z_to_bv 64 y11) (Z_to_bv 64 y12)
       x13 x14 x15 x16 x17 x18 (Z_to_bv 64 y19) x20 x21 x22 x23
       (Z_to_bv 64 y24) (Z_to_bv 64 y25) (Z_to_bv 64 y26) (Z_to_bv 64 y27) x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest e1 S1 n1 b1 k1 c1 pad1 S2 n2 b2 k2 c2 pad2 S3 n3 b3 k3 c3 pad3 S4 n4 b4 dl junk4
      y8 y10 y11 y12 y19 y24 y25 y26 y27
      x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w14
      PV MI OUT DTB FA BD1 BD2 BD3 BD4 SB1 SB2 SB3 SB4 HC1 HC18 HC2 HC28 HC3 HC38 HE1 HE3 HE4 HDL
      H8 H10 H11 H12 H19 H24 H25 H26 H27.
    (* [comment removed for export] *)
    pose proof (rsk_al_e _ _ SPVA) as SPA.
    assert (BD8 : (SPV + -776) mod 8 = 0) by (clear - SPA; lia).
    rewrite (zbv_eqm _ _ H8), (zbv_eqm _ _ H10), (zbv_eqm _ _ H11), (zbv_eqm _ _ H12), (zbv_eqm _ _ H19), (zbv_eqm _ _ H24),
            (zbv_eqm _ _ H25), (zbv_eqm _ _ H26), (zbv_eqm _ _ H27).
    clear H8 H10 H11 H12 H19 H24 H25 H26 H27.
    assert (MU : munch WDF mm mm) by apply munch_refl.
    assert (WM : wmono usegs mm mm) by apply wmono_refl.
    unfold bitd_cells in BD1, BD2, BD3.
    pose proof SB4 as (B0 & L0 & R00 & R01 & R02 & D01 & D02).
    step.
    eapply evt_cut.
    { eapply (BITINIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm (SPV + -776) S4 n4 b4 junk4); first [exact BD8 | eassumption | lia]. }
    clear B0 L0 R00 R01 R02 D01 D02 BD8 SPA.
    unfold bit_init_post. post_call usegs mm.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm' _) => rename mm' into m1 end.
    pose proof (x42p_transport mm m1 rest PV MU WM) as PV1.
    pose proof (sbuf_transport mm m1 S1 n1 b1 SB1 MU) as SB1'.
    pose proof (sbuf_transport mm m1 S2 n2 b2 SB2 MU) as SB2'.
    pose proof (sbuf_transport mm m1 S3 n3 b3 SB3 MU) as SB3'.
    pose proof (sbuf_transport mm m1 S4 n4 b4 SB4 MU) as SB4'.
    clear PV SB1 SB2 SB3 SB4.
    lazymatch goal with H : (?r = n4 /\ _) \/ _ |- _ =>
      eapply (x42_i4 m1 rest e1 S1 n1 b1 k1 c1 pad1 S2 n2 b2 k2 c2 pad2 S3 n3 b3 k3 c3 pad3 S4 n4 b4 dl r)
    end.
    all: first [eassumption | reflexivity | f_equal; lia | lia].
  Qed.

End DX42_11.
