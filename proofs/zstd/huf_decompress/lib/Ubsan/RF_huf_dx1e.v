(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_bitinit RF_huf_dx1 RF_huf_dx1i.
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

Lemma x1_init_err : forall bs e, init_dstream bs = Err e -> 0 < e < 120.
Proof.
  intros bs e EE. unfold init_dstream, add_byte, load, readLE64, highbit32 in EE.
  repeat (match type of EE with context [if ?c then _ else _] => destruct c end; cbn [bind] in EE).
  all: first [discriminate EE | injection EE as <-; split; vm_compute; reflexivity].
Qed.

Lemma x1_lhu : forall (a b : byte) c d, 1 <= c <= 12 -> 1 <= d <= 12 ->
  zext 64 (bv_extract 0 16 (le_bytes_to_word (firstn 2 (skipn (Z.to_nat 2) [a; b; Z_to_bv 8 c; Z_to_bv 8 d])))) =
  Z_to_bv 64 (c + 256 * d).
Proof.
  intros a b c d Hc Hd.
  assert (HC : List.In c [1;2;3;4;5;6;7;8;9;10;11;12]) by (cbn; lia).
  assert (HD : List.In d [1;2;3;4;5;6;7;8;9;10;11;12]) by (cbn; lia).
  cbn [List.In] in HC, HD.
  repeat (destruct HC as [<- | HC]); repeat (destruct HD as [<- | HD]); try contradiction; vm_compute; reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section DX1E.
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
  Hypothesis DT4 : DT mod 4 = 0.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation DINVU := (RF_huf_dx1.DINVU ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 DST dcap SS DT lo src cbs).
  Notation BDC := (RF_huf_dx1.BDC sp SS).
  Notation LINV := (RF_huf_dx1i.LINV SS src).
  (* [comment removed for export] *)
  Notation D1 l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL D0 DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 DPOS) (only parsing).

  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * mtl)) x21 x22 x23 x24 x25 x26 s11
             x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Ltac dinvu_close :=
    unfold RF_huf_dx1.DINVU; split; [eexists; split; [eassumption | rewrite ?Zupd_length; assumption] |];
    repeat (split; [eassumption|]); eassumption.

  Lemma x1_st0 : dcap = 0 -> forall pc mm (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    evt usegs POST (ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31) ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 DST) (Z_to_bv 64 (tl + 256 * mtl)) x21 x22 x23 x24 x25 x26 s11
             x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Proof. intros E0 *. replace (DST + dcap) with DST by lia. auto. Qed.

  Ltac x1_clr := repeat match goal with H : ov_read_bytes _ _ _ _ = Some _ |- _ => clear H end.

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

  (* [comment removed for export] *)
  Lemma x1_short : forall mm P bc cw pad (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    DINVU mm -> BDC mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> LINV P bc -> dcap < 4 ->
    evt usegs POST (ST 0x15858 mm x1 x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) (Z_to_bv 64 bc) (Z_to_bv 64 (DST + dcap - DST))
                      x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof using All.
    intros mm P bc cw pad x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 DI BD INV HD.
    pose proof TOK as (TL & TLEN & TCK). unfold HUF_TABLELOG_MAX in TL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof INV as (HBC & HPI).
    pose proof DI as DI'. destruct DI' as ((buf & ARR & LB) & SRCB & CBB & STK & FR & MI & MU & WM).
    unfold RF_huf_dx1.BDC in BD.
    assert (EW : bv_swrap 32 (Z.shiftr (bv_wrap 32 bc) 3) = bc / 8).
    { rewrite (bv_wrap_small 32 bc) by (unfold bv_modulus; cbn; lia).
      rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. lia. }
    assert (EW2 : Z.shiftr bc 3 = bc / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    zbr.
    ck K0. zbr. ck K1.
    - zbr. rewrite ?EW, ?EW2. ck U1. zbr. x1_null. zbr. ck U3.
      x1_src8 (P - bc / 8 - SS).
      zto 0x15958. x1_clr.
      eapply ((D1 RF_huf_dx1.x1_tset) _ 0); [dinvu_close | exact BD | lia | x1_modg ..].
    - zbr. ck K3.
      2: { zbr. rewrite ?EW, ?EW2. ck U1. zbr. x1_null. zbr. ck K5.
        - zbr. rewrite ?(Z.mod_small (bc / 8) 4294967296) by lia.
          ck U2. zbr. x1_null. zbr. ck U3.
          x1_src8 (P - bc / 8 - SS).
          zto 0x15958. x1_clr.
          eapply ((D1 RF_huf_dx1.x1_tset) _ 0); [dinvu_close | exact BD | lia | x1_modg ..].
        - zbr. rewrite ?(Z.mod_small (P - SS) 4294967296) by lia.
          ck U2. zbr. x1_null. zbr. ck U3.
          x1_src8 0.
          zto 0x15958. x1_clr.
          eapply ((D1 RF_huf_dx1.x1_tset) _ 0); [dinvu_close | exact BD | lia | x1_modg ..]. }
      zbr. ck K4.
      + do 8 zstep.
        eapply ((D1 RF_huf_dx1.x1_tail) (Z.to_nat dcap) _ 0); [dinvu_close | exact BD | lia | lia | x1_modg ..].
      + zto 0x159d4. eapply (D1 RF_huf_dx1.x1_end); [dinvu_close | exact BD].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_ok : forall mm P bc cw pad (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    DINVU mm -> BDC mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> LINV P bc ->
    evt usegs POST (ST 0x15570 mm x1 x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) x10 x11 x12 x13 x14 x15 x16 x17
                      x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof using All.
    intros mm P bc cw pad x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 DI BD INV.
    pose proof TOK as (TL & TLEN & TCK). unfold HUF_TABLELOG_MAX in TL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof INV as (HBC & HPI).
    pose proof DI as DI'. destruct DI' as ((buf & ARR & LB) & SRCB & CBB & STK & FR & MI & MU & WM).
    unfold RF_huf_dx1.BDC in BD.
    assert (EZ : zx32 (Z_to_bv 64 bc) = Z_to_bv 64 bc).
    { unfold zx32. f_equal. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
      apply Z.mod_small. lia. }
    assert (UB : bv_unsigned (Z_to_bv 64 bc) = bc) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
    assert (SW : bv_swrap 32 bc = bc) by (apply bv_swrap_small; change (bv_half_modulus 32) with 2147483648; lia).
    zbr. rewrite EZ.
    ck KS. all: rewrite ?signed_lit in KS by lia.
    2: (zbr; rewrite ?UB; repeat rewrite Z.add_0_r; rewrite ?SW; ck KB;
        rewrite (neg_desc_shift tl mtl) by lia; rewrite (zb_lxor_ones (DT + 4)) by lia;
        replace (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (-1 * DT + -5))
          by (apply x1_zbv_eqm; Z.div_mod_to_equations; lia);
        replace (Z_to_bv 64 (DST + dcap + -3)) with (Z_to_bv 64 (dcap + DST + -3)) by (f_equal; lia);
        change (Z_to_bv 64 4611686018427387904) with (Z_to_bv 64 (2^62));
        eapply ((D1 RF_huf_dx1i.x1_loop) (Z.to_nat dcap) _ 0);
        [dinvu_close | exact BD | lia | lia | lia | x1_modg | x1_modg | x1_modg | x1_modg | x1_modg | exact INV]).
    eapply x1_short; [exact DI | exact BD | exact INV | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_entry : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (buf : list Z),
    u8arr usegs m0 DST (map (Z_to_bv 8) buf) -> zlen buf = dcap ->
    bytes_at usegs m0 SS (map (Z_to_bv 8) src) -> bytes_at usegs m0 (DT + 4) cbs ->
    bytes_at usegs m0 DT [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl] ->
    stk usegs m0 lo SP -> mem_inv usegs m0 ->
    evt usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SS) (Z_to_bv 64 n)
                           (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 PHUF_DX1_1X) fc None m0 (seg_rom usegs)).
  Proof using All.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 buf ARR LB SRCB CBB HDR STK MI.
    pose proof TOK as (TL & TLEN & TCK). unfold HUF_TABLELOG_MAX in TL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (MU : munch DW m0 m0) by apply munch_refl. assert (WM : wmono usegs m0 m0) by apply wmono_refl.
    carve_frame 96%nat STK. rename FR into FRS.
    carve_frame 40%nat STK. rename FR into FRB.
    carve_frame 8%nat STK. rename FR into FRP.
    unfold PHUF_DX1_1X.
    zbr.
    ck K0.
    2: (assert (DP : 0 < DST) by (apply DPOS; lia); zbr; ck U1; zbr; ck U2; zbr; ck U3).
    all: zbr. all: ck U4. all: zbr.
    all: assert (A3 : Z.land DT 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; exact DT4).
    all: rewrite A3; dec_if.
    all: lazymatch goal with H : bytes_at usegs ?mc DT _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
           pose proof (bytes_at_read usegs mc DT _ 2 2 H ltac:(lia) ltac:(cbn; lia)) as RDT end.
    all: zto 0x1a500.
    all: assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -144)) = SP + -144)
           by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
    all: call (bit_init_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -136) SS src _ lo).
    all: rewrite ?ESP.
    all: try (first [eassumption | exact BYS | lia | reflexivity | (f_equal; lia)]).
    all: pose proof (init_dstream_ok src) as INI0.
    all: first [pose proof (INI0 (Forall_all_bytes _ BYS)) as INI | pose proof INI0 as INI]; clear INI0.
    all: destruct INI as [(e & EE) | (d & ED & BOK & BZ & SH)].
    all: pose proof (stk_of_rw_cells usegs _ _ _ FRP) as HP8; cbn [cells_size csize Nat.add] in HP8;
         change (Z.of_nat 8) with 8 in HP8; replace (SP + -144 + 8) with (SP + -136) in HP8 by lia.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
           assert (STK2 : stk usegs mc lo (SP + -136)) by (eapply stk_merge; [exact STK | exact HP8 | lia]) end.
    all: clear STK HP8 FRP; rename STK2 into STK.
    all: lazymatch goal with
         | EE : init_dstream src = Err ?e |- _ =>
             lazymatch goal with H : context [match init_dstream src with _ => _ end] |- _ =>
               rewrite EE in H; cbn iota in H; destruct H as (RET & jj & RJ) end;
             pose proof (x1_init_err src e EE) as ER
         | ED : init_dstream src = Ok ?d |- _ =>
             lazymatch goal with H : context [match init_dstream src with _ => _ end] |- _ =>
               rewrite ED in H; cbn iota in H; destruct H as (RET & BZ2 & jp & RJ) end
         end.
    all: lazymatch type of RET with ?r = _ => subst r end.
    all: rewrite x1_lhu by lia.
    all: zbr.
    all: ck KE.
    all: try (apply x1_st0; [lia|]).
    all: lazymatch goal with ER : 0 < _ < 120 |- _ =>
           eapply (D1 RF_huf_dx1.x1_err); [dinvu_close | exact RJ | reflexivity] | _ => idtac end.
    all: eapply x1_ok; [dinvu_close | exact RJ | ].
    all: unfold RF_huf_dx1i.LINV; rewrite ?Zlength_correct in SH; try unfold FseNCount.Zlength in SH;
         destruct SH as [(L & EP & EB) | (L & EP & EB)]; rewrite EP; (split; [lia|]);
         destruct (Z.eq_dec (zlen src) 8); first [left; lia | right; lia].
  Qed.

End DX1E.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem dec_1x1_proof : dec1_int_stmt x1_tab PHUF_DX1_1X.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m DST dcap SR DT mtl src jd lo
    MTL TAB HD DC SRCB BYS NSM S16 SP0 DT0 DT8 DTL DL SL DJ1 DJ2 DJ3 STK LOS SP16 MI E0 E1 E2 E3 E4.
  subst a0 a1 a2 a3 a4.
  destruct TAB as (tl & cells & HDR & ZC & TOK & TLE & CBB).
  pose proof TOK as (TL & TLEN & _). unfold HUF_TABLELOG_MAX in TL.
  assert (P0 : 0 < 2^tl) by (apply Z.pow_pos_nonneg; lia).
  assert (P2 : 2^tl <= 2^(mtl+1)) by (apply Z.pow_le_mono_r; lia).
  assert (P2' : 2^(mtl+1) = 2 * 2^mtl) by (rewrite Z.pow_add_r by lia; lia).
  unfold DTABLE_BYTES, HufHarness.DT_BYTES in DTL, DJ1.
  unfold HUF_DEC_STACK in LOS.
  assert (BUF : exists buf, u8arr usegs m DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap).
  { destruct HD as [(-> & ->) | (DP & D8 & RW)].
    - exists []. split; [| reflexivity]. split; [apply bytes_at_nil; lia |].
      unfold wr_at. cbn [map length Z.of_nat]. split; [lia | split; [lia | intros; lia]].
    - exists (map bv_unsigned jd).
      pose proof (proj1 (proj1 RW)) as WF. cbn in WF. destruct WF as (WF & _).
      rewrite map_map, (map_ext _ (fun x => x))
        by (intros; apply bv_eq; rewrite Z_to_bv_unsigned;
            first [apply bv_wrap_bv_unsigned | apply bv_wrap_small, bv_unsigned_in_range]).
      rewrite map_id.
      split; [exact (u8arr_of_rw_cells usegs m DST _ jd RW) | rewrite length_map; lia]. }
  destruct BUF as (buf & ARR & LB).
  eapply (x1_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DST dcap SR DT mtl tl lo src cells
            (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells))).
  all: try first [ exact ARR | exact CBB | eassumption | reflexivity ].
  all: try (destruct HD as [(? & ?) | (? & ? & ?)]; intros; lia).
  rewrite length_firstn, x1_bytes'_length. lia.
Qed.
End CANSEC1.
