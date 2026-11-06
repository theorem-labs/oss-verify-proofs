(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx41h RZ_huf_dx41i RZ_huf_dx41j RZ_huf_dx41k RZ_huf_dx41l RZ_huf_dx41m.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41N.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis BITINIT : bit_init_stmt.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 :=
    (rw_cells psegs mm (SPV + -416) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19]).


  Notation WD4 := [(DST, DST + dcap); (SPV - 256, SPV - 216)].
  Notation WDF := [(DST, DST + dcap); (SPV - 416, SPV - 216)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells psegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SINV := RZ_huf_dx41.SINV.

  Notation WFR := [(SPV - 416, SPV - 216)].
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation HINV := RZ_huf_dx41g.HINV.

  (* [comment removed for export] *)
  Ltac x41_bc_enum V :=
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

  Lemma x41_i1 : forall mm rest e1 n tot S1 n1 b1 n2 b2 n3 b3 n4 b4 dl tl rsv
       junk
      (x5 x6 x7 x16 x21 x22 x23 x24 x26 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    X41P mm rest -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb -> huf_nb_ok false dtb tl ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    rw_cells psegs mm (SPV + -256) [CB 40 junk] ->
    SBUF mm S1 n1 b1 -> SBUF mm (S1 + n1) n2 b2 -> SBUF mm (S1 + n1 + n2) n3 b3 -> SBUF mm (S1 + n1 + n2 + n3) n4 b4 ->
    1 <= n1 -> n4 = n - tot -> 0 <= tot <= n -> n < 2^32 ->
    0 <= e1 -> 3 * e1 <= dcap ->
    dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    evt psegs POST (ST 0x22748 mm (Z_to_bv 64 n) x5 x6 x7 (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + n1)) (Z_to_bv 64 18446744073709551544) (Z_to_bv 64 n2) (Z_to_bv 64 tot) (Z_to_bv 64 n3) (Z_to_bv 64 n1) (Z_to_bv 64 8) x16 (Z_to_bv 64 (DST + 2 * e1)) (Z_to_bv 64 (S1 - 6)) (Z_to_bv 64 (DST + 3 * e1)) (Z_to_bv 64 (DST + e1)) x21 x22 x23 x24 (Z_to_bv 64 e1) x26 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 dl) (Z_to_bv 64 DT)).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest e1 n tot S1 n1 b1 n2 b2 n3 b3 n4 b4 dl tl rsv  junk
      x5 x6 x7 x16 x21 x22 x23 x24 x26
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 PV MI OUT DTB NBOK FA BD SB1 SB2 SB3 SB4  HNV1 HN4 HTOT HN HE1 HE3 HDL HTL HRSV.
    assert (MU : munch WDF mm mm) by apply munch_refl.
    assert (WM : wmono psegs mm mm) by apply wmono_refl.
    pose proof SB1 as (B3 & L3 & R30 & R31 & R32 & D31 & D32).
    assert (K3 : S1 + n1 <= SPV - 416 \/ SPV <= S1) by (clear - D32 LO; lia).
    clear D31 D32 OS1 DJ2.
    (* [comment removed for export] *)
    destruct (Z.eq_dec n1 1) as [N31|N31]; [rewrite N31 in *|].
    1: kx_autoLx [0x23454; 0x22940] 200%nat
         [KZImg 0x10000 0x14000; KZRange S1 4096 (2^47); KZRange (S1 + 1) 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 416) 160;
          KZDisj (SPV - 416) 160 S1 1]
         [(S1, 1); (SPV - 416, 160)].
    all: lazymatch goal with
         | N31 : _ <> 1 |- _ =>
             kx_auto_v 8 [0x23454; 0x22940] 200%nat
               [KZImg 0x10000 0x14000; KZRange n1 1 (2^32); KZRange S1 4096 (2^47); KZRange (S1 + n1) 4096 (2^47);
                KZRange SPV 4096 (2^47); KZWr (SPV - 416) 160; KZDisj (SPV - 416) 160 S1 n1]
               [(S1, n1); (SPV - 416, 160)]
         | _ => idtac
         end.
    all: try solve [exfalso; clear - N31 L3 KXBR KXBR0 KXBR1; lia].
    all: kx_mem.
    all: try replace (n1 + S1) with (S1 + n1) in * by lia.
    all: lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 144468) _ _ ?mm' _) =>
      eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm');
      [ eapply RZ_huf_dx41k.x41_einv_gen with (rest := rest);
        first [ exact CTX | exact DJ3 | exact KXMI | exact OUT | exact FA | exact BD | reflexivity
              | eapply x41p_transport; first [exact CTX | exact DJ3 | exact PV | exact MU | exact WM] ]
      | right; split; reflexivity ]
  | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?PP) _ _ _ _ _ _ _) _ (Z_to_bv 64 141632) _ _ ?mm' _) =>
      lazymatch type of FA with
      | rw_cells _ _ _ [_; _; _; _; _; _; _; _; _; C8 (Z_to_bv 64 ?V); _; _; _; _; _; _; _; _; _; _] =>
      x41_bc_enum V;
      replace (Z_to_bv 64 V) with (Z_to_bv 64 (V mod 2^64)) in FA by apply KXS.Z_to_bv64_mod;
      lazymatch type of SB1 with
      | _ _ ?NN _ =>
          let HI := fresh "HI" in
          pose proof ((x41_i2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 BITINIT) mm' rest e1 n tot S1 NN b1 (PP - S1) (V mod 2^64)) as HI;
          replace (S1 + (PP - S1)) with PP in HI by lia;
          eapply HI
      end
      end
  end.
    all: first [ exact KXMI | exact OUT | exact DTB | exact NBOK | exact FA | exact BD | exact HN4 | exact HDL
               | exact HTL | exact HRSV | exact HTOT | exact HN | exact HE1 | exact HE3
               | eapply x41p_transport; first [exact CTX | exact DJ3 | exact PV | exact MU | exact WM]
               | eapply sbuf_transport; first [exact CTX | exact DJ3 | exact SB1 | exact SB2 | exact SB3 | exact SB4 | exact MU]
               | unfold RZ_huf_dx41g.HINV; lia ].
  Qed.

End DX41N.
