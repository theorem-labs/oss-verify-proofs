(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_fkit2 RZ_huf_dx41r RZ_huf_dx42_5 RZ_huf_dx42_20 RZ_huf_dx42_22a RZ_huf_dx42_22b huf411_kit_rs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.BothW Require Import AZ_hufkit42e.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_23.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis TL11 : tl = 11.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  Hypothesis DTA : rsk_al DT 4.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation WDL := [(DST, DST + dcap); (SPV - 232, SPV - 104)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11;
                                     C8 w12; C8 w13; C8 w14; C8 w15]).
  Notation SINV := RZ_huf_dx41.SINV.
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw ilo oew ie0 ie1 ie2 ie3 :=
    (rw_cells usegs mm (SPV + -384) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 bt0; C8 bt1; C8 bt2; C8 bt3; C8 dtw; C8 ilo; C8 oew; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).
  Notation LOC mm e0 e1 e2 e3 p0 p1 p2 p3 i0 i1 i2 i3 c0 c1 c2 c3 :=
    (rw_cells usegs mm (SPV + -232) [C8 e0; C8 e1; C8 e2; C8 e3; C8 p0; C8 p1; C8 p2; C8 p3; C8 i0; C8 i1; C8 i2; C8 i3;
                                     C8 c0; C8 c1; C8 c2; C8 c3]).
  Notation M10 := (Z_to_bv 64 14757395258967641293).
  Notation M7 := (Z_to_bv 64 2635249153387078803).
  Notation X41PF := (RZ_huf_dx41r.X41PF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41pf_transport := (RZ_huf_dx41r.x41pf_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation x42_f3_0 := (RZ_huf_dx42_22b.x42_f3_0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK TL11 DJ3 DTA).
  Notation x42_fi := (RZ_huf_dx42_20.x42_fi ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK TL11 NBOK DJ3).
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  (* [comment removed for export] *)
  Ltac x42_mulhu_rb :=
    repeat match goal with
    | KXA : atoms_ok ?zs ?E |- _ =>
        let go a b :=
            let nz := kx_len zs in let ua := kx_uz E zs nz a in let ub := kx_uz E zs nz b in
            let HD := fresh "HD" in
            assert (HD : bv_unsigned (edenot E (EMd M_MULHU a b)) = ua * ub / 2 ^ 64)
              by (change (edenot E (EMd M_MULHU a b)) with (mul_div M_MULHU (edenot E a) (edenot E b)); rewrite KXS.u_mulhu64;
                  rewrite (uz_sound zs E a KXA), (uz_sound zs E b KXA); reflexivity);
            rewrite HD in *; clear HD in
        match goal with
        | |- context [bv_unsigned (edenot E (EMd M_MULHU ?a ?b))] => go a b
        | H : context [bv_unsigned (edenot E (EMd M_MULHU ?a ?b))] |- _ => go a b
        end
    end.

  Lemma x42_l10 : forall x, 0 <= x < 2^64 -> x mod 2^64 * 14757395258967641293 / 2^64 / 8 = x / 10.
  Proof using. intros x Hx. rewrite (Z.mod_small x) by lia. Z.div_mod_to_equations; lia. Qed.
  Lemma x42_l7 : forall x, 0 <= x < 2^64 ->
    ((x + -1 * (x mod 2^64 * 2635249153387078803 / 2^64)) mod 2^64 / 2 + x mod 2^64 * 2635249153387078803 / 2^64) mod 2^64 / 4 = x / 7.
  Proof using.
    intros x Hx. rewrite (Z.mod_small x) by lia.
    set (h := x * 2635249153387078803 / 2^64).
    assert (Hh : 0 <= h <= x) by (subst h; Z.div_mod_to_equations; lia).
    replace (x + -1 * h) with (x - h) by lia. rewrite (Z.mod_small (x - h)) by lia.
    rewrite (Z.mod_small ((x - h) / 2 + h)) by (Z.div_mod_to_equations; lia).
    subst h. Z.div_mod_to_equations; lia.
  Qed.

  Lemma x42_fo_eqs : forall q dcap o0 o1 o2 o3 i0 n,
    0 <= o0 <= q -> 0 <= o1 <= 2 * q -> 0 <= o2 <= 3 * q -> 0 <= o3 <= dcap -> 0 <= q -> 3 * q <= dcap -> dcap < 2^32 ->
    0 <= i0 -> i0 + 8 <= n -> n < 2^32 ->
    ((-1 * o0 + q) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (q - o0) / 10) /\
    ((-1 * o1 + 2 * q) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (2 * q - o1) / 10) /\
    ((-1 * o2 + 3 * q) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (3 * q - o2) / 10) /\
    ((-1 * o3 + dcap) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (dcap - o3) / 10) /\
    (((i0 + -1 * (i0 mod 2^64 * 2635249153387078803 / 2^64)) mod 2^64 / 2 + i0 mod 2^64 * 2635249153387078803 / 2^64) mod 2^64 / 4 = i0 / 7) /\
    (0 <= (q - o0) / 10 /\ 10 * ((q - o0) / 10) <= q - o0) /\ (0 <= (2 * q - o1) / 10 /\ 10 * ((2 * q - o1) / 10) <= 2 * q - o1) /\
    (0 <= (3 * q - o2) / 10 /\ 10 * ((3 * q - o2) / 10) <= 3 * q - o2) /\ (0 <= (dcap - o3) / 10 /\ 10 * ((dcap - o3) / 10) <= dcap - o3) /\
    (0 <= i0 / 7 /\ 7 * (i0 / 7) <= i0).
  Proof using.
    intros q dcap' o0 o1 o2 o3 i0 n H0 H1 H2 H3 HQ HQ3 HD HI HJ HN.
    split; [rewrite x42_l10 by lia; f_equal; lia|]. split; [rewrite x42_l10 by lia; f_equal; lia|].
    split; [rewrite x42_l10 by lia; f_equal; lia|]. split; [rewrite x42_l10 by lia; f_equal; lia|].
    split; [apply x42_l7; lia|].
    repeat split; Z.div_mod_to_equations; lia.
  Qed.

  Notation FRS0 mm w0 w1 SRC n q :=
    (FRS mm w0 w1 (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 DT) (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + dcap)) M10 M7
         (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 SRC) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DT + 4))).
  Notation ARGS0 mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 SRC l1 l2 l3 :=
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SRC) (Z_to_bv 64 (DST + dcap))
          (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))).
  Notation LOC0 mm q o0 o1 o2 o3 SRC i0 i1 i2 i3 c0 c1 c2 c3 :=
    (LOC mm (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + dcap))
         (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3))
         (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3).

  Lemma x42pf_tr : forall mm mm', X41PF mm -> munch WDL mm mm' -> wmono usegs mm mm' -> X41PF mm'.
  Proof using CTX DJ3.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm mm' (SV & STK & MU & WM) MU' WM'.
    split; [|split; [|split]].
    - eapply (rw_cells_transport usegs _ mm mm' _ _ SV MU' WM');
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - eapply (stk_transport_disjoint usegs _ mm mm' _ _ STK MU' WM'); cbn [disjoint_from]; lia.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. unfold sub_fp; cbn [outside]; intros; lia.
    - exact (wmono_trans usegs m0 mm mm' WM WM').
  Qed.

  Lemma x42_f2 : forall mm SRC n src q l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (c0 c1 c2 c3 : word)
      (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 w0 w1 : word)
      (x1 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    X41PF mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRS0 mm w0 w1 SRC n q -> ARGS0 mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 SRC l1 l2 l3 ->
    LOC0 mm q o0 o1 o2 o3 SRC i0 i1 i2 i3 c0 c1 c2 c3 ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 < dcap -> q = (dcap + 3) / 4 -> 3 * q < dcap -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
    0 <= o0 <= q -> q <= o1 <= 2 * q -> 2 * q <= o2 <= 3 * q -> 3 * q <= o3 <= dcap ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    evt usegs POST (ST 0x219a4 mm x1 (Z_to_bv 64 0x110e0) x6 x7 x8 x9 x10 x11 (Z_to_bv 64 0x11078) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
                      x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm SRC n src q l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 w0 w1
      x1 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      PV MI OUT DTB FS AS LC SB SL S0 S1 SL32 DJS DKS HDC HQ HQ3 HL1 HL2 HL3 HLN HI0 HJ0 HI1 HJ1 HI2 HJ2 HI3 HJ3 HO0 HO1 HO2 HO3
      HB0 HB1 HB2 HB3.
    pose proof (lbw_pos _ _ HB0) as HC0. pose proof (lbw_pos _ _ HB1) as HC1.
    pose proof (lbw_pos _ _ HB2) as HC2. pose proof (lbw_pos _ _ HB3) as HC3.
    assert (HQ0 : 0 <= q) by (subst q; Z.div_mod_to_equations; lia).
    destruct PV as (SV & STK & MUP & WMP).
    kx_auto [0x21a48] 60%nat
      [KZImg 0x10000 0x14000; KZRange q 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange SRC 4096 (2^47);
       KZRange SPV 4096 (2^47); KZRange DT 4096 (2^47); KZWr (SPV - 384) 152]
      [(SPV - 512, 128); (SPV - 384, 152); (SPV - 232, 128)].
    all: kx_ev_ranges; kx_mem.
    all: replace ((dcap + 3) mod 2 ^ 64 / 4) with q by (subst q; rewrite Z.mod_small by lia; reflexivity).
    all: replace (SRC + 6 + l1 + l2 + l3) with (SRC + (6 + l1 + l2 + l3)) in AS by lia;
         replace (SRC + 6 + l1 + l2) with (SRC + (6 + l1 + l2)) in AS by lia;
         replace (SRC + 6 + l1) with (SRC + (6 + l1)) in AS by lia.
    all: pose proof (conj SV (conj STK (conj MUP WMP))) as PV2.
    all: eapply (x42_f3_0 _ q SRC n src i0 o0 6 i1 o1 (6 + l1) i2 o2 (6 + l1 + l2) i3 o3 (6 + l1 + l2 + l3)).
    all: first [ exact PV2 | eassumption | lia ].
  Qed.

  Ltac fob_tp := lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x220dc) _ _ _ _) => kx_trap_fast
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2213c) _ _ _ _) => kx_trap_fast
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22180) _ _ _ _) => kx_trap_fast
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22188) _ _ _ _) => kx_trap_fast
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22190) _ _ _ _) => kx_trap_fast
    | _ => idtac end.

  Ltac fob_finish mm SRC n src q l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 R c0 c1 c2 c3 KO :=
    lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x2112c) _ _ ?m2 _) =>
        assert (1 <= R) by lia;
        replace A0 with (DST + (o3 + 5 * R)) by lia;
        eapply (x42_fi (Z.to_nat R) m2 m2 SRC n src i0 i1 i2 i3 o0 o1 o2 o3 (o3 + 5 * R) q (2 * q) (3 * q) dcap);
        [ .. | let mm' := fresh "mm'" in
               intros mm' ? ? ? ? ? ? ? ? ? ? ? ?; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
               intros MU' WM' MI' OUT' DTB' LC' HI0' HI1' HI2' HI3' HN0' HN1' HN2' HN3' HF0' HF1' HF2' HF3' HB0' HB1' HB2' HB3';
               lazymatch goal with
               | PV : X41PF ?mz, FS : rw_cells _ ?mz (SPV + -512) _, AS : rw_cells _ ?mz (SPV + -384) _, SB : bytes_at _ ?mz SRC _ |- _ =>
                   pose proof (x42pf_tr mz mm' PV MU' WM') as PV';
                   pose proof (rw_cells_transport usegs _ mz mm' _ _ FS MU' WM') as FS';
                   pose proof (rw_cells_transport usegs _ mz mm' _ _ AS MU' WM') as AS';
                   pose proof (bytes_at_transport usegs _ mz mm' SRC src SB MU') as SB';
                   cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FS', AS', SB';
                   specialize (FS' ltac:(lia)); specialize (AS' ltac:(lia)); specialize (SB' ltac:(lia))
               end;
               eapply KO; first [ eassumption | lia ] ];
        first [ eassumption | apply munch_refl | apply wmono_refl | lia ]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x219a4) _ _ ?m2 _) =>
        eapply (x42_f2 m2 SRC n src q l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3); first [ eassumption | lia ]
    end.

  (* [comment removed for export] *)
  Lemma x42_fo_b : forall mm SRC n src q l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 R (c0 c1 c2 c3 : word)
      (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 w0 w1 : word)
      (x5 x8 x10 x12 x15 x16 x20 x21 x24 x26 x27 x28 x29 x31 : word),
    X41PF mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRS0 mm w0 w1 SRC n q -> ARGS0 mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 SRC l1 l2 l3 ->
    LOC0 mm q o0 o1 o2 o3 SRC i0 i1 i2 i3 c0 c1 c2 c3 ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 < dcap -> q = (dcap + 3) / 4 -> 3 * q < dcap -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
    0 <= o0 <= q -> q <= o1 <= 2 * q -> 2 * q <= o2 <= 3 * q -> 3 * q <= o3 <= dcap ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    0 <= R -> 10 * R <= q - o0 -> 10 * R <= 2 * q - o1 -> 10 * R <= 3 * q - o2 -> 10 * R <= dcap - o3 -> 7 * R <= i0 ->
    (forall mm' I0 I1 I2 I3 F0 F1 F2 F3 (d0 d1 d2 d3 : word) (y5 y7 y8 y10 y12 y20 y21 y24 y26 y27 y28 y29 y31 : word),
        X41PF mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRS0 mm' w0 w1 SRC n q -> ARGS0 mm' av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 SRC l1 l2 l3 ->
        LOC0 mm' q F0 F1 F2 F3 SRC I0 I1 I2 I3 d0 d1 d2 d3 ->
        bytes_at usegs mm' SRC src ->
        0 <= I0 -> I0 + 8 <= n -> 0 <= I1 -> I1 + 8 <= n -> 0 <= I2 -> I2 + 8 <= n -> 0 <= I3 -> I3 + 8 <= n ->
        o0 <= F0 <= q -> o1 <= F1 <= 2 * q -> o2 <= F2 <= 3 * q -> o3 + 5 <= F3 <= dcap ->
        LBW 8 d0 -> LBW 8 d1 -> LBW 8 d2 -> LBW 8 d3 ->
        evt usegs POST (ST 0x20fe4 mm' (Z_to_bv 64 (-25)) y5 (Z_to_bv 64 (DST + F3)) y7 y8 (Z_to_bv 64 (SRC + I2)) y10 (Z_to_bv 64 (SRC + I3)) y12
                          (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC + I0)) (Z_to_bv 64 (DST + F1)) (Z_to_bv 64 (DST + F2)) (Z_to_bv 64 (SPV + -168))
                          (Z_to_bv 64 (DST + F0)) (Z_to_bv 64 (SRC + I1)) y20 y21 d0 (Z_to_bv 64 (SPV + -136)) y24 (Z_to_bv 64 (-16)) y26 y27 y28 y29
                          (Z_to_bv 64 (-1 * DT + -5)) y31)) ->
    evt usegs POST (ST 0x21060 mm (Z_to_bv 64 (-25)) x5 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 R) x8 (Z_to_bv 64 (SRC + i2)) x10 (Z_to_bv 64 (SRC + i3)) x12
                      (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC + i0)) x15 x16 (Z_to_bv 64 (SPV + -168)) (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (SRC + i1)) x20 x21 c0
                      (Z_to_bv 64 (SPV + -136)) x24 (Z_to_bv 64 (-16)) x26 x27 x28 x29 (Z_to_bv 64 (-1 * DT + -5)) x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm SRC n src q l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 R c0 c1 c2 c3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 w0 w1
      x5 x8 x10 x12 x15 x16 x20 x21 x24 x26 x27 x28 x29 x31
      PV MI OUT DTB FS AS LC SB SL S0 S1 SL32 DJS DKS HDC HQ HQ3 HL1 HL2 HL3 HLN HI0 HJ0 HI1 HJ1 HI2 HJ2 HI3 HJ3 HO0 HO1 HO2 HO3
      HB0 HB1 HB2 HB3 HR0 HRA HRB HRC HRD HR7 KO.
    kx_auto [0x2112c; 0x219a4; 0x220dc; 0x2213c; 0x22180; 0x22188; 0x22190] 80%nat
      [KZImg 0x10000 0x14000; KZRange R 0 (2^32); KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
       KZRange i0 0 (2^32); KZRange i1 0 (2^32); KZRange i2 0 (2^32); KZRange i3 0 (2^32); KZRange q 0 (2^32);
       KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange SRC 4096 (2^47); KZRange SPV 4096 (2^47); KZRange DT 4096 (2^47)]
      [(SPV - 512, 128); (SPV - 232, 128)].
    all: fob_tp.
    all: kx_ev_ranges; kx_mem.
    (* [comment removed for export] *)
    all: fob_finish mm SRC n src q l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 R c0 c1 c2 c3 KO.
  Qed.

  Lemma x42_fo_b2 : forall mm SRC n src q l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 R (c0 c1 c2 c3 : word)
      (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 w0 w1 : word)
      (x5 x7 x8 x12 x15 x16 x20 x21 x24 x26 x27 x28 x29 x31 : word),
    X41PF mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRS0 mm w0 w1 SRC n q -> ARGS0 mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 SRC l1 l2 l3 ->
    LOC0 mm q o0 o1 o2 o3 SRC i0 i1 i2 i3 c0 c1 c2 c3 ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 < dcap -> q = (dcap + 3) / 4 -> 3 * q < dcap -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
    0 <= o0 <= q -> q <= o1 <= 2 * q -> 2 * q <= o2 <= 3 * q -> 3 * q <= o3 <= dcap ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    0 <= R -> 10 * R <= q - o0 -> 10 * R <= 2 * q - o1 -> 10 * R <= 3 * q - o2 -> 10 * R <= dcap - o3 -> 7 * R <= i0 ->
    (forall mm' I0 I1 I2 I3 F0 F1 F2 F3 (d0 d1 d2 d3 : word) (y5 y7 y8 y10 y12 y20 y21 y24 y26 y27 y28 y29 y31 : word),
        X41PF mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRS0 mm' w0 w1 SRC n q -> ARGS0 mm' av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 SRC l1 l2 l3 ->
        LOC0 mm' q F0 F1 F2 F3 SRC I0 I1 I2 I3 d0 d1 d2 d3 ->
        bytes_at usegs mm' SRC src ->
        0 <= I0 -> I0 + 8 <= n -> 0 <= I1 -> I1 + 8 <= n -> 0 <= I2 -> I2 + 8 <= n -> 0 <= I3 -> I3 + 8 <= n ->
        o0 <= F0 <= q -> o1 <= F1 <= 2 * q -> o2 <= F2 <= 3 * q -> o3 + 5 <= F3 <= dcap ->
        LBW 8 d0 -> LBW 8 d1 -> LBW 8 d2 -> LBW 8 d3 ->
        evt usegs POST (ST 0x20fe4 mm' (Z_to_bv 64 (-25)) y5 (Z_to_bv 64 (DST + F3)) y7 y8 (Z_to_bv 64 (SRC + I2)) y10 (Z_to_bv 64 (SRC + I3)) y12
                          (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC + I0)) (Z_to_bv 64 (DST + F1)) (Z_to_bv 64 (DST + F2)) (Z_to_bv 64 (SPV + -168))
                          (Z_to_bv 64 (DST + F0)) (Z_to_bv 64 (SRC + I1)) y20 y21 d0 (Z_to_bv 64 (SPV + -136)) y24 (Z_to_bv 64 (-16)) y26 y27 y28 y29
                          (Z_to_bv 64 (-1 * DT + -5)) y31)) ->
    evt usegs POST (ST 0x210b4 mm (Z_to_bv 64 (-25)) x5 (Z_to_bv 64 (DST + o3)) x7 x8 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 R) (Z_to_bv 64 (SRC + i3)) x12
                      (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC + i0)) x15 x16 (Z_to_bv 64 (SPV + -168)) (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (SRC + i1)) x20 x21 c0
                      (Z_to_bv 64 (SPV + -136)) x24 (Z_to_bv 64 (-16)) x26 x27 x28 x29 (Z_to_bv 64 (-1 * DT + -5)) x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm SRC n src q l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 R c0 c1 c2 c3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 w0 w1
      x5 x7 x8 x12 x15 x16 x20 x21 x24 x26 x27 x28 x29 x31
      PV MI OUT DTB FS AS LC SB SL S0 S1 SL32 DJS DKS HDC HQ HQ3 HL1 HL2 HL3 HLN HI0 HJ0 HI1 HJ1 HI2 HJ2 HI3 HJ3 HO0 HO1 HO2 HO3
      HB0 HB1 HB2 HB3 HR0 HRA HRB HRC HRD HR7 KO.
    kx_auto [0x2112c; 0x219a4; 0x220dc; 0x2213c; 0x22180; 0x22188; 0x22190] 80%nat
      [KZImg 0x10000 0x14000; KZRange R 0 (2^32); KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
       KZRange i0 0 (2^32); KZRange i1 0 (2^32); KZRange i2 0 (2^32); KZRange i3 0 (2^32); KZRange q 0 (2^32);
       KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange SRC 4096 (2^47); KZRange SPV 4096 (2^47); KZRange DT 4096 (2^47)]
      [(SPV - 512, 128); (SPV - 232, 128)].
    all: fob_tp.
    all: kx_ev_ranges; kx_mem.
    all: fob_finish mm SRC n src q l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 R c0 c1 c2 c3 KO.
  Qed.

  (* [comment removed for export] *)
  Ltac x42_kx_lia_fast := kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].
  #[local] Ltac kx_lia ::= lazymatch goal with |- context [edenot _ _] => fail "opaque" | _ => x42_kx_lia_fast end.

  Lemma x42_fo : forall (k : nat) mm SRC n src q l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (c0 c1 c2 c3 : word)
      (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 w0 w1 : word)
      (x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31 : word),
    X41PF mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRS0 mm w0 w1 SRC n q -> ARGS0 mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 SRC l1 l2 l3 ->
    LOC0 mm q o0 o1 o2 o3 SRC i0 i1 i2 i3 c0 c1 c2 c3 ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 < dcap -> q = (dcap + 3) / 4 -> 3 * q < dcap -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
    0 <= o0 <= q -> q <= o1 <= 2 * q -> 2 * q <= o2 <= 3 * q -> 3 * q <= o3 <= dcap ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    dcap - o3 < Z.of_nat k ->
    evt usegs POST (ST 0x20fe4 mm (Z_to_bv 64 (-25)) x5 (Z_to_bv 64 (DST + o3)) x7 x8 (Z_to_bv 64 (SRC + i2)) x10 (Z_to_bv 64 (SRC + i3)) x12
                      (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (SPV + -168))
                      (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (SRC + i1)) x20 x21 c0 (Z_to_bv 64 (SPV + -136)) x24 (Z_to_bv 64 (-16)) x26 x27 x28 x29
                      (Z_to_bv 64 (-1 * DT + -5)) x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mm SRC n src q l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 w0 w1
      x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31
      PV MI OUT DTB FS AS LC SB SL S0 S1 SL32 DJS DKS HDC HQ HQ3 HL1 HL2 HL3 HLN HI0 HJ0 HI1 HJ1 HI2 HJ2 HI3 HJ3 HO0 HO1 HO2 HO3
      HB0 HB1 HB2 HB3 HK;
      [exfalso; lia|].
    assert (HQ0 : 0 <= q) by (subst q; Z.div_mod_to_equations; lia).
    kx_auto [0x21060; 0x210b4] 60%nat
      [KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32); KZRange q 0 (2^32);
       KZRange i0 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange SRC 4096 (2^47); KZRange SPV 4096 (2^47)]
      [(SPV - 512, 128)].
    all: x42_mulhu_rb.
    all: clear KXK KXRD KXA.
    (* [comment removed for export] *)
    all: pose proof (x42_fo_eqs q dcap o0 o1 o2 o3 i0 n ltac:(clear - HO0; lia) ltac:(clear - HO1 HQ0; lia) ltac:(clear - HO2 HQ0; lia)
                       ltac:(clear - HO3 HQ0; lia) HQ0 ltac:(clear - HQ3; lia) ltac:(clear - R1; lia) HI0 HJ0 SL32)
         as (E0 & E1 & E2 & E3 & E7 & HQA & HQB & HQC & HQD & HQ7).
    all: rewrite ?E0, ?E1, ?E2, ?E3, ?E7 in *.
    all: clear E0 E1 E2 E3 E7.
    all: set (Q0 := (q - o0) / 10) in *; set (Q1 := (2 * q - o1) / 10) in *; set (Q2 := (3 * q - o2) / 10) in *;
         set (Q3 := (dcap - o3) / 10) in *; set (Q7 := i0 / 7) in *.
    all: clearbody Q0 Q1 Q2 Q3 Q7.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ (Z_to_bv 64 ?R) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x21060) _ _ _ _) =>
             eapply (x42_fo_b mm SRC n src q l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 R)
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?R) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x210b4) _ _ _ _) =>
             eapply (x42_fo_b2 mm SRC n src q l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 R)
         end.
    all: first [ eassumption | lazymatch goal with |- forall _, _ => idtac end | lia ].
    all: intros mm' I0 I1 I2 I3 F0' F1' F2' F3'; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
         intros PV' MI' OUT' DTB' FS' AS' LC' SB' HI0' HN0' HI1' HN1' HI2' HN2' HI3' HN3' HF0' HF1' HF2' HF3' HB0' HB1' HB2' HB3'.
    all: eapply (IH mm' SRC n src q l1 l2 l3 I0 I1 I2 I3 F0' F1' F2' F3');
         first [ eassumption | lia ].
  Qed.

End DX42_23.
