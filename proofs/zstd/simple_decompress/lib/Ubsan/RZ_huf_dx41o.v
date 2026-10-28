(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2 ZdWalkKit ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx41j RZ_huf_dx41k RZ_huf_dx41l RZ_huf_dx41m RZ_huf_dx41n huf41_kit_x41ck huf411_kit_rs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41O.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis BITINIT : bit_init_stmt.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).


  Notation BD1 mm c b pad p st lm := (rw_cells usegs mm (SPV + -376) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD2 mm c b pad p st lm := (rw_cells usegs mm (SPV + -144) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD3 mm c b pad p st lm := (rw_cells usegs mm (SPV + -184) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD4 mm c b pad p st lm := (rw_cells usegs mm (SPV + -224) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SINV := RZ_huf_dx41.SINV.

  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation HINV := RZ_huf_dx41g.HINV.

  Ltac kreg i E :=
    lazymatch goal with
    | |- evt _ _ (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
                          ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) _ _ _ _ _ _) =>
        let xs := constr:([x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
                           x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31]) in
        let j := eval vm_compute in (pred i) in
        let xi := kx_nth j xs in
        lazymatch xi with
        | Z_to_bv 64 E => idtac
        | Z_to_bv 64 ?X => replace (Z_to_bv 64 X) with (Z_to_bv 64 E) in * by (apply zbv_eqm; first [reflexivity | f_equal; lia | lia])
        end
    end.

  Ltac cb8_split cs :=
    lazymatch cs with
    | CB 8 ?j :: ?post => constr:((@nil cell, j, post))
    | ?c :: ?t => let r := cb8_split t in lazymatch r with (?pre, ?j, ?post) => constr:((c :: pre, j, post)) end
    end.
  Ltac cb8_all H :=
    repeat (lazymatch type of H with
            | rw_cells ?sg ?m ?A ?cs =>
                let r := cb8_split cs in
                lazymatch r with (?pre, ?j, ?post) =>
                  let w := fresh "w" in let H' := fresh "H" in
                  destruct (cb8_as_c8 sg m A pre j post H) as [w H']; cbn [app] in H'; clear H; rename H' into H
                end
            end).

  (* [comment removed for export] *)
  Lemma sbuf_sub : forall mm SRC n src A k len,
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 <= k -> 0 <= len -> k + len <= n -> A = SRC + k ->
    SBUF mm A len (firstn (Z.to_nat len) (skipn (Z.to_nat k) src)).
  Proof.
    intros mm SRC n src A k len HB HL R0 R1' R2 D1 D2 HK HLEN HKL ->.
    assert (LEN : zlen (firstn (Z.to_nat len) (skipn (Z.to_nat k) src)) = len) by (rewrite firstn_length, skipn_length; lia).
    split; [|split; [exact LEN|]; repeat split; lia].
    rewrite <- (firstn_skipn (Z.to_nat k) src) in HB. apply bytes_at_app in HB as [_ HB].
    rewrite firstn_length, Nat.min_l in HB by lia. rewrite Z2Nat.id in HB by lia.
    rewrite <- (firstn_skipn (Z.to_nat len) (skipn (Z.to_nat k) src)) in HB. apply bytes_at_app in HB as [HB _]. exact HB.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_dl_read : forall tl rsv, nth_error dtb 2 = Some (Z_to_bv 8 tl) -> nth_error dtb 3 = Some (Z_to_bv 8 rsv) ->
    1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    extz false 2 (bytes_le_to_Z (firstn 2 (skipn (Z.to_nat 2) dtb))) = tl + 256 * rsv.
  Proof.
    intros tl rsv DT2 DT3 HTL HRSV.
    assert (E : firstn 2 (skipn (Z.to_nat 2) dtb) = [Z_to_bv 8 tl; Z_to_bv 8 rsv]).
    { change (Z.to_nat 2) with 2%nat.
      destruct dtb as [|y0 [|y1 [|y2 [|y3 r]]]]; cbn in DT2, DT3; try discriminate.
      injection DT2 as ->. injection DT3 as ->. reflexivity. }
    rewrite E. unfold extz. rewrite Bytes.bytes_le_to_Z_le_val. cbn [map Bytes.le_val].
    rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia). lia.
  Qed.

  Lemma x41p_tr_s0 : forall mm mm' rest, X41P mm rest -> munch [(DST, DST + dcap); (SPV - 512, SPV - 376)] mm mm' ->
    wmono usegs mm mm' -> X41P mm' rest.
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm mm' rest (SV & STK & RS & MU & WM) MU' WM'.
    split; [|split; [|split; [|split]]].
    - eapply (rw_cells_transport usegs _ mm mm' _ _ SV MU' WM');
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - eapply (stk_transport_disjoint usegs _ mm mm' _ _ STK MU' WM'); cbn [disjoint_from]; lia.
    - eapply (rw_cells_transport usegs _ mm mm' _ _ RS MU' WM');
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. unfold sub_fp; cbn [outside]; intros; lia.
    - exact (wmono_trans usegs m0 mm mm' WM WM').
  Qed.

  Lemma x41_s0 : forall mm rest SRC n src tl rsv j1 j2
      (x1 x5 x6 x7 x9 x10 x11 x12 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    X41P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb -> huf_nb_ok false dtb tl ->
    nth_error dtb 2 = Some (Z_to_bv 8 tl) -> nth_error dtb 3 = Some (Z_to_bv 8 rsv) -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    rw_cells usegs mm (SPV + -512) [CB 176 j1] -> rw_cells usegs mm (SPV + -224) [CB 120 j2] ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    SPV mod 16 = 0 -> DT mod 4 = 0 ->
    evt usegs POST (ST 0x22b84 mm x1 x5 x6 x7 (Z_to_bv 64 SRC) x9 x10 x11 x12 (Z_to_bv 64 n) (Z_to_bv 64 DT) (Z_to_bv 64 DST) x16 (Z_to_bv 64 dcap)
                     x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest SRC n src tl rsv j1 j2
      x1 x5 x6 x7 x9 x10 x11 x12 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      PV MI OUT DTB NBOK DT2 DT3 HTL HRSV FJ1 FJ2 SRCB SRCL R20 R21 R22 DJS DKS SPA DTA.
    apply (rw_cells_split_CB usegs mm (SPV + -512) [] 176 j1 [] [136; 40]%nat) in FJ1; [| reflexivity].
    cbn [mk_CB_cells app] in FJ1.
    lazymatch type of FJ1 with rw_cells _ _ _ (?c0 :: ?rest) =>
      apply (proj1 (rw_cells_app usegs _ _ [c0] rest)) in FJ1; destruct FJ1 as [FA BJ1] end.
    cbn [cells_size csize Nat.add] in BJ1. replace (SPV + -512 + Z.of_nat 136) with (SPV + -376) in BJ1 by lia.
    apply (rw_cells_split_CB usegs mm (SPV + -512) [] 136 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FA; [| reflexivity].
    cbn [mk_CB_cells app] in FA.
    cb8_all FA.
    apply (rw_cells_split_CB usegs mm (SPV + -224) [] 120 j2 [] [40; 40; 40]%nat) in FJ2; [| reflexivity].
    cbn [mk_CB_cells app] in FJ2.
    lazymatch type of FJ2 with rw_cells _ _ _ (?c0 :: ?rest) =>
      apply (proj1 (rw_cells_app usegs _ _ [c0] rest)) in FJ2; destruct FJ2 as [BJ4 FJ2] end.
    cbn [cells_size csize Nat.add] in FJ2. replace (SPV + -224 + Z.of_nat 40) with (SPV + -184) in FJ2 by lia.
    lazymatch type of FJ2 with rw_cells _ _ _ (?c0 :: ?rest) =>
      apply (proj1 (rw_cells_app usegs _ _ [c0] rest)) in FJ2; destruct FJ2 as [BJ3 BJ2] end.
    cbn [cells_size csize Nat.add] in BJ2. replace (SPV + -184 + Z.of_nat 40) with (SPV + -144) in BJ2 by lia.
    assert (MU : munch [(DST, DST + dcap); (SPV - 512, SPV - 376)] mm mm) by apply munch_refl.
    assert (WM : wmono usegs mm mm) by apply wmono_refl.
    kx_autoLx [0x23594; 0x22cd8] 120%nat
      [KZRange n 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange (DT + 4) 4100 (2^47); KZAlign DT 4; KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
       KZRange SPV 4096 (2^47); KZWr (SPV - 512) 136; KZDisj (SPV - 512) 136 DT 16388; KZDisj (SPV - 512) 136 SRC n]
      [(SRC, n); (DT, 16388)].
    all: x41_ck.
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x23594) _ _ _ _) => kx_mem | _ => idtac end.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23594) _ _ ?mm' _) =>
             eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm');
             [ eapply (RZ_huf_dx41k.x41_einv_gen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX mm' rest);
               first [ exact PV | eassumption | reflexivity | eapply x41p_tr_s0; eassumption ]
             | right; split; reflexivity ]
         | _ => idtac
         end.
    lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ev _ ?J) _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        kx_read_eq J RD;
        rewrite (rdval_bytes_at usegs _ DT dtb 2 2 false DTB ltac:(lia) ltac:(change (Z.to_nat 2) with 2%nat; lia)),
                (x41_dl_read tl rsv DT2 DT3 HTL HRSV) in RD;
        rewrite RD
    end.
    kx_read_ranges. kx_strip_mod. kx_mem. kx_strip_mod.
    lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ (Z_to_bv 64 ?TOT) _ _ _ (Z_to_bv 64 ?L1) _ _ _ _ _ _ _ _ (Z_to_bv 64 ?L3) _ (Z_to_bv 64 ?L2) _ _ (Z_to_bv 64 ?SEG) _ _ _ _ _) _ _ _ _ _ _) =>
        kreg 10%nat (SPV + -376); kreg 11%nat (SRC + 6); kreg 5%nat (DST + SEG); kreg 16%nat (DST + 2 * SEG);
        kreg 22%nat (SRC + 6 + L1); kreg 20%nat (SRC + 6 + L1 + L2); kreg 24%nat (DST + 3 * SEG); kreg 25%nat (DT + 4);
        kreg 27%nat (DST + dcap);
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ ?mm' _) =>
            eapply (RZ_huf_dx41n.x41_i1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 BITINIT
                      (rsk_al_i _ _ SPA) (rsk_al_i _ _ DTA) mm' rest SEG n TOT (SRC + 6) L1 (firstn (Z.to_nat L1) (skipn (Z.to_nat 6) src))
                      (SRC + 6 + L1) L2 (firstn (Z.to_nat L2) (skipn (Z.to_nat (6 + L1)) src))
                      (SRC + 6 + L1 + L2) L3 (firstn (Z.to_nat L3) (skipn (Z.to_nat (6 + L1 + L2)) src))
                      (SRC + 6 + L1 + L2 + L3) (n - TOT) (firstn (Z.to_nat (n - TOT)) (skipn (Z.to_nat TOT) src))
                      (tl + 256 * rsv) tl rsv)
        end
    end.
    all: first [ exact PV | exact MI | exact OUT | exact DTB | exact NBOK | exact FA | exact HTL | exact HRSV | eassumption | reflexivity | lia
               | eapply x41p_tr_s0; eassumption
               | eapply (sbuf_sub _ SRC n src); first [eassumption | lia] ].
  Qed.

End DX41O.
