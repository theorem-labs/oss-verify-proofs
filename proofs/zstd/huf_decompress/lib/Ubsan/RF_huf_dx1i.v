(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_dx1.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Ltac dec_if := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let b := eval vm_compute in c in change c with b; cbv iota end.

(* [comment removed for export] *)
Ltac rd_refresh S bs :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) =>
  tryif (match goal with _ : ov_read_bytes usegs mg (Z_to_bv 64 (S + _)) 1 = Some _ |- _ => idtac end) then idtac
  else (
  repeat match goal with H : ov_read_bytes usegs _ (Z_to_bv 64 (S + _)) 1 = Some _ |- _ => clear H end;
  lazymatch goal with
  | EL : zlen bs = ?N, H : bytes_at usegs mg S (map (Z_to_bv 8) bs) |- _ =>
    let t k := let b := eval vm_compute in (k <? N) in
               lazymatch b with
               | true => pose proof (src_rd usegs mg S bs k H ltac:(rewrite EL; split; [discriminate| reflexivity]))
               | false => idtac
               end in
    t 0; t 1; t 2; t 3; t 4; t 5; t 6
  end) end.

Ltac step_to S bs pc := repeat (lazymatch goal with
   | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
   | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => dec_if
   | |- evt _ _ (MS _ _ _ _ _ _ _) => rd_refresh S bs; zstep end).

Ltac zbr := repeat (lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail | _ => zstep end).

Ltac ck U := if_cases U; zify_cond U; try (exfalso; lia).
Ltac probe := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 0 "PC:" pc end.

Section CANSEC1. Context {rc : runConstT}.
Section DX1I.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 2 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 2 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis DPOS : 0 < dcap -> 0 < DST.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation DINVU := (RF_huf_dx1.DINVU ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 DST dcap SS DT lo src cbs).
  Notation BDC := (RF_huf_dx1.BDC sp SS).
  (* [comment removed for export] *)
  Notation D1 l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL D0 DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 DPOS) (only parsing).

  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * mtl)) x21 x22 x23 x24 x25 x26 s11
             x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Notation LST pc mm x1 x9 x10 x11 p p3 x21 x22 x23 x24 x25 x26 x28 :=
    (ST pc mm x1 (Z_to_bv 64 65) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 dcap) x9 x10 x11
        (Z_to_bv 64 p) (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 (dcap + DST + -3)) (Z_to_bv 64 (-1 * DT + -5))
        (Z_to_bv 64 p3) x21 x22 x23 x24 x25 x26 x28 (Z_to_bv 64 3) (Z_to_bv 64 2) (Z_to_bv 64 (-1))).

  Ltac x1_val v VR := lazymatch goal with |- context [Z.shiftr ((Z.shiftl (bv_unsigned ?c) ?b) mod ?M) ?sh] =>
    remember (Z.shiftr ((Z.shiftl (bv_unsigned c) b) mod M) sh) as v eqn:EV;
    assert (VR : 0 <= v < 2^tl) by (subst v; apply (D1 RF_huf_dx1.x1_idx_bound); apply bv_unsigned_in_range);
    clear EV end.

  Ltac x1_rd TCK v VR NB BY :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with H : bytes_at usegs mc (DT + 4) cbs |- _ =>
        let R0 := fresh "RC" in let R1 := fresh "RC" in
        destruct (x1_cell_rd usegs mc (DT + 4) cells (Z.to_nat (2 * 2^tl)) v ltac:(rewrite <- ECB; exact H)
                    ltac:(lia) ltac:(lia) ltac:(lia)) as [R0 R1]
      end
    end;
    destruct (TCK v VR) as (NB & BY).

  Ltac x1_clr := repeat match goal with H : ov_read_bytes _ _ _ _ = Some _ |- _ => clear H end.

  Ltac x1_gen := lazymatch goal with ARR : u8arr _ _ DST (map (Z_to_bv 8) (Zupd ?i ?v ?b)), LB : zlen ?b = dcap |- _ =>
    let b' := fresh "buf" in let LB' := fresh "LB" in
    remember (Zupd i v b) as b' eqn:EB;
    assert (LB' : zlen b' = dcap) by (subst b'; rewrite Zupd_length; exact LB);
    clear EB LB; rename LB' into LB end.

  Ltac dinvu_close :=
    unfold RF_huf_dx1.DINVU; split; [eexists; split; [eassumption | rewrite ?Zupd_length; assumption] |];
    repeat (split; [eassumption|]); eassumption.

  Ltac x1_src8 O :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with H : bytes_at usegs mc SS (map (Z_to_bv 8) src) |- _ =>
        pose proof (src_rd2 usegs mc SS src O 0 H ltac:(lia)) as SR0;
        pose proof (src_rd2 usegs mc SS src O 1 H ltac:(lia)) as SR1;
        pose proof (src_rd2 usegs mc SS src O 2 H ltac:(lia)) as SR2;
        pose proof (src_rd2 usegs mc SS src O 3 H ltac:(lia)) as SR3;
        pose proof (src_rd2 usegs mc SS src O 4 H ltac:(lia)) as SR4;
        pose proof (src_rd2 usegs mc SS src O 5 H ltac:(lia)) as SR5;
        pose proof (src_rd2 usegs mc SS src O 6 H ltac:(lia)) as SR6;
        pose proof (src_rd2 usegs mc SS src O 7 H ltac:(lia)) as SR7
      end end.

  Ltac x1_null :=
    lazymatch goal with
    | |- context [Z.b2z (0 <? ?a)] => rewrite (proj2 (Z.ltb_lt 0 a)) by lia; x1_null
    | |- context [Z.lxor (Z.b2z true) (Z.b2z (Z.lxor ?a ?b <? 1))] =>
      let XN := fresh "XN" in
      assert (XN : 1 <= Z.lxor a b) by (
        assert (Z.lxor a b <> 0) by (rewrite Z.lxor_eq_0_iff; lia);
        assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia); lia);
      rewrite (proj2 (Z.ltb_ge (Z.lxor a b) 1)) by lia;
      clear XN; dec_if
    end.

  (* [comment removed for export] *)
  Definition LINV (P bc : Z) : Prop := 0 <= bc <= 64 /\ (P = SS \/ (SS < P /\ P + 8 <= SS + n)).

  (* [comment removed for export] *)
  Lemma x1_body : forall mm j bc bcr P Pr fl flr cw pad (x1 x9 x22 x24 x25 x26 x28 : word),
    DINVU mm -> BDC mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 0 <= j <= dcap -> 4 <= dcap -> (fl = 0 \/ fl = 1) -> 0 <= bc <= 64 ->
    bcr mod 2^64 = bc mod 2^64 -> Pr mod 2^64 = P mod 2^64 -> flr mod 2^64 = fl mod 2^64 ->
    (j + 4 <= dcap -> forall mm' bcn bcr' bcs' p' p3' Pr' (y9 y23 y24 y25 y26 : word),
        DINVU mm' -> BDC mm' cw (Z_to_bv 64 bcn) pad (Z_to_bv 64 P) -> 0 <= bcn <= 64 ->
        p' mod 2^64 = (DST + (j + 4)) mod 2^64 -> p3' mod 2^64 = (DST + (j + 4) + 3) mod 2^64 ->
        bcr' mod 2^64 = bcn mod 2^64 -> bcs' mod 2^64 = bcn mod 2^64 -> Pr' mod 2^64 = P mod 2^64 ->
        evt usegs POST (LST 0x155d0 mm' x1 y9 (Z_to_bv 64 bcr') (Z_to_bv 64 bcs') p' p3' cw (Z_to_bv 64 Pr') y23 y24 y25 y26 x28)) ->
    evt usegs POST (LST 0x15744 mm x1 x9 (Z_to_bv 64 bcr) (Z_to_bv 64 Pr) (DST + j) (DST + j + 3) cw x22 (Z_to_bv 64 flr) x24 x25 x26 x28).
  Proof using All.
    intros mm j bc bcr P Pr fl flr cw pad x1 x9 x22 x24 x25 x26 x28 DI BD HJ HD4 HFL HBC HBR HPR HFR KH.
    pose proof TOK as (TL & TLEN & TCK). unfold HUF_TABLELOG_MAX in TL.
    assert (CL : 2^tl <= Z.of_nat (length cells)) by exact TLEN.
    assert (PT : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    rewrite (x1_zbv_eqm bcr bc) by exact HBR. rewrite (x1_zbv_eqm Pr P) by exact HPR. rewrite (x1_zbv_eqm flr fl) by exact HFR.
    clear bcr Pr flr HBR HPR HFR.
    pose proof DI as DI'. destruct DI' as ((buf & ARR & LB) & SRCB & CBB & STK & FR & MI & MU & WM).
    unfold RF_huf_dx1.BDC in BD.
    assert (DP : 0 < DST) by (apply DPOS; lia).
    zbr.
    destruct (Z.ltb_spec (DST + j) (dcap + DST + -3)) as [LT|GE]; destruct HFL as [-> | ->]; dec_if.
    1,3,4: eapply ((D1 RF_huf_dx1.x1_tset) mm j); [exact DI | exact BD | lia | x1_modg ..].
    zbr.
    x1_val v1 VR1. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
    ck U1.
    zbr.
    ck U2.
    destruct (x1_cell_rd usegs mm (DT + 4) cells (Z.to_nat (2 * 2^tl)) v1 ltac:(rewrite <- ECB; exact CBB)
                ltac:(lia) ltac:(lia) ltac:(lia)) as [RC0 RC1].
    destruct (TCK v1 VR1) as (NB1 & BY1).
    zbr.
    ck U3.
    zbr.
    u8_sok ARR j. zstep. u8_store ARR j (x1_byte (nth (Z.to_nat v1) cells x1_default)); [rewrite byte_lit by lia; reflexivity|]. x1_gen.
    zbr. clear RC0 RC1. rewrite !byte_lit by lia.
    x1_val v2 VR2. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
    ck U4. zbr. ck U5.
    x1_rd TCK v2 VR2 NB2 BY2.
    zbr.
    ck U6. zbr.
    u8_sok ARR (j + 1). zstep. u8_store ARR (j + 1) (x1_byte (nth (Z.to_nat v2) cells x1_default)); [rewrite byte_lit by lia; reflexivity|]. x1_gen.
    zbr. x1_clr. rewrite !byte_lit by lia.
    x1_val v3 VR3. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
    ck U7. zbr. ck U8.
    x1_rd TCK v3 VR3 NB3 BY3.
    zbr. ck U9. zbr.
    u8_sok ARR (j + 2). zstep. u8_store ARR (j + 2) (x1_byte (nth (Z.to_nat v3) cells x1_default)); [rewrite byte_lit by lia; reflexivity|]. x1_gen.
    zbr. x1_clr. rewrite !byte_lit by lia.
    x1_val v4 VR4. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
    ck U10. zbr. ck U11.
    x1_rd TCK v4 VR4 NB4 BY4.
    zbr. ck U12. zbr.
    u8_sok ARR (j + 3). zstep. u8_store ARR (j + 3) (x1_byte (nth (Z.to_nat v4) cells x1_default)); [rewrite byte_lit by lia; reflexivity|]. x1_gen.
    zbr. x1_clr. rewrite ?byte_lit by lia. rewrite ?byte_lit in BD by lia.
    lazymatch goal with |- context [bv_swrap 32 (?x mod 18446744073709551616 + 0)] => remember x as bn eqn:EBN in * end.
    assert (BN : 0 <= bn <= 112) by (subst bn; lia).
    rewrite (Z.mod_small bn 18446744073709551616) by lia. rewrite Z.add_0_r.
    rewrite bv_swrap_small by (change (bv_half_modulus 32) with 2147483648; lia).
    ck K.
    - eapply (KH ltac:(lia) _ bn); [dinvu_close | exact BD | lia | x1_modg ..].
    - zbr. ck K2. zbr. rewrite ?Z.land_0_r. dec_if.
      eapply ((D1 RF_huf_dx1.x1_tset) _ (j + 4)); [dinvu_close | exact BD | lia | x1_modg ..].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_reload : forall mm j p p3 P Pr bc bcr bcs cw pad (x1 x9 x23 x24 x25 x26 x28 : word),
    DINVU mm -> BDC mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 0 <= j <= dcap -> 4 <= dcap ->
    p mod 2^64 = (DST + j) mod 2^64 -> p3 mod 2^64 = (DST + j + 3) mod 2^64 ->
    bcr mod 2^64 = bc mod 2^64 -> bcs mod 2^64 = bc mod 2^64 -> Pr mod 2^64 = P mod 2^64 -> LINV P bc ->
    (forall mm' fl flr bc' bcr' P' Pr' cw' pad' (y9 y22 y24 y25 y26 : word),
        DINVU mm' -> BDC mm' cw' (Z_to_bv 64 bc') pad' (Z_to_bv 64 P') -> (fl = 0 \/ fl = 1) -> flr mod 2^64 = fl mod 2^64 ->
        bcr' mod 2^64 = bc' mod 2^64 -> Pr' mod 2^64 = P' mod 2^64 -> LINV P' bc' ->
        evt usegs POST (LST 0x15744 mm' x1 y9 (Z_to_bv 64 bcr') (Z_to_bv 64 Pr') (DST + j) (DST + j + 3) cw' y22 (Z_to_bv 64 flr) y24 y25 y26 x28)) ->
    evt usegs POST (LST 0x155d0 mm x1 x9 (Z_to_bv 64 bcr) (Z_to_bv 64 bcs) p p3 cw (Z_to_bv 64 Pr) x23 x24 x25 x26 x28).
  Proof using All.
    intros mm j p p3 P Pr bc bcr bcs cw pad x1 x9 x23 x24 x25 x26 x28 DI BD HJ HD4 HP HP3 HBR HBS HPR INV KB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    rewrite (x1_zbv_eqm p (DST + j)) by exact HP. rewrite (x1_zbv_eqm p3 (DST + j + 3)) by exact HP3.
    rewrite (x1_zbv_eqm bcr bc) by exact HBR. rewrite (x1_zbv_eqm bcs bc) by exact HBS. rewrite (x1_zbv_eqm Pr P) by exact HPR.
    clear p p3 bcr bcs Pr HP HP3 HBR HBS HPR.
    destruct INV as (HBC & HPI).
    pose proof DI as DI'. destruct DI' as ((buf & ARR & LB) & SRCB & CBB & STK & FR & MI & MU & WM).
    unfold RF_huf_dx1.BDC in BD.
    assert (DP : 0 < DST) by (apply DPOS; lia).
    assert (EW : bv_swrap 32 (Z.shiftr (bv_wrap 32 bc) 3) = bc / 8).
    { rewrite (bv_wrap_small 32 bc) by (unfold bv_modulus; cbn; lia).
      rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. lia. }
    zbr.
    ck K1.
    - zbr. rewrite ?EW. ck U1. zbr. x1_null. zbr. ck U3.
      x1_src8 (P - bc / 8 - SS).
      zbr. ck K2. x1_clr.
      eapply KB; [dinvu_close | exact BD | right; reflexivity | x1_modg | x1_modg | x1_modg | ].
      unfold LINV. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8.
      split; [lia|]. destruct (Z.eq_dec (P - bc / 8) SS); [left; lia | right; lia].
    - zbr. ck K3.
      + zbr. ck K4. x1_clr.
        eapply KB; [dinvu_close | exact BD | left; reflexivity | x1_modg | x1_modg | x1_modg | ].
        unfold LINV; split; [lia | left; lia].
      + zbr. rewrite ?EW. ck U1. zbr. x1_null. zbr. ck K5.
        * zbr. rewrite ?(Z.mod_small (bc / 8) 4294967296) by lia.
          ck U2. zbr. x1_null. zbr. ck U3.
          x1_src8 (P - bc / 8 - SS).
          zbr. ck K6. x1_clr.
          rewrite (proj2 (Z.ltb_ge (P - bc / 8) SS)) by lia.
          eapply KB; [dinvu_close | exact BD | right; reflexivity | reflexivity | x1_modg | x1_modg | ].
          unfold LINV. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
          rewrite (Z.mod_small (bc / 8 * 8) 18446744073709551616) by lia.
          rewrite bv_swrap_small by (change (bv_half_modulus 32) with 2147483648; lia).
          split; [lia|]. destruct (Z.eq_dec (P - bc / 8) SS); [left; lia | right; lia].
        * zbr. rewrite ?(Z.mod_small (P - SS) 4294967296) by lia.
          ck U2. zbr. x1_null. zbr. ck U3.
          x1_src8 0.
          zbr. ck K6. x1_clr.
          rewrite (proj2 (Z.ltb_lt (P - bc / 8) SS)) by lia.
          eapply KB; [dinvu_close | exact BD | left; reflexivity | reflexivity | x1_modg | x1_modg | ].
          unfold LINV. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
          rewrite (Z.mod_small ((P - SS) * 8) 18446744073709551616) by lia.
          rewrite bv_swrap_small by (change (bv_half_modulus 32) with 2147483648; lia).
          split; [lia | left; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_loop : forall (k : nat) mm j p p3 P Pr bc bcr bcs cw pad (x1 x9 x23 x24 x25 x26 x28 : word),
    DINVU mm -> BDC mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 0 <= j <= dcap -> 4 <= dcap -> dcap - j <= Z.of_nat k ->
    p mod 2^64 = (DST + j) mod 2^64 -> p3 mod 2^64 = (DST + j + 3) mod 2^64 ->
    bcr mod 2^64 = bc mod 2^64 -> bcs mod 2^64 = bc mod 2^64 -> Pr mod 2^64 = P mod 2^64 -> LINV P bc ->
    evt usegs POST (LST 0x155d0 mm x1 x9 (Z_to_bv 64 bcr) (Z_to_bv 64 bcs) p p3 cw (Z_to_bv 64 Pr) x23 x24 x25 x26 x28).
  Proof using All.
    induction k as [|k IH]; intros mm j p p3 P Pr bc bcr bcs cw pad x1 x9 x23 x24 x25 x26 x28 DI BD HJ HD4 HK HP HP3 HBR HBS HPR INV.
    all: eapply x1_reload; [exact DI | exact BD | exact HJ | exact HD4 | exact HP | exact HP3 | exact HBR | exact HBS | exact HPR | exact INV |].
    all: intros mm' fl flr bc' bcr' P' Pr' cw' pad' y9 y22 y24 y25 y26 DI' BD' HFL HFR HBR' HPR' INV'.
    all: pose proof INV' as INV2; destruct INV2 as (HBC' & _).
    all: eapply x1_body; [exact DI' | exact BD' | exact HJ | exact HD4 | exact HFL | exact HBC' | exact HBR' | exact HPR' | exact HFR |].
    - intros HR. exfalso. lia.
    - intros HR mm'' bcn bcr'' bcs'' p' p3' Pr'' z9 z23 z24 z25 z26 DI'' BD'' HBCN HP' HP3' HBR'' HBS'' HPR''.
      eapply (IH _ (j + 4)); [exact DI'' | exact BD'' | lia | exact HD4 | lia | exact HP' | exact HP3' | exact HBR'' | exact HBS'' | exact HPR'' |].
      destruct INV' as (_ & HP2). split; [exact HBCN | exact HP2].
  Qed.

End DX1I.
End CANSEC1.
