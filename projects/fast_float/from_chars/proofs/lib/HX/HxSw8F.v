(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxEnt FxRgs FxFacts FxPlan FxFrame FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require HxGen HxSem HxInt HxTm HxSw4W HxSw8.

Module HxSw8FW.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxSw4W.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ms_eq_tac ::=
  cbv beta delta [mkR];
  repeat first [ reflexivity
               | lazymatch goal with |- @eq (bv _) _ _ => ms_leaf_eq end
               | progress f_equal ].

Notation ASEGS := Asan.M.loaded_segments.

Lemma v8_facts : forall z0 z1 z2 z3 z4 z5 z6 z7,
  (0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 ->
   0 <= z4 < 256 -> 0 <= z5 < 256 -> 0 <= z6 < 256 -> 0 <= z7 < 256 ->
   0 <= v8 z0 z1 z2 z3 z4 z5 z6 z7 < 2^64 /\ v8 z0 z1 z2 z3 z4 z5 z6 z7 mod 2^32 = v4 z0 z1 z2 z3)%Z.
Proof.
  intros. pose proof (v4_range z0 z1 z2 z3). pose proof (v4_range z4 z5 z6 z7). unfold v8. split; [lia|].
  rewrite (Z.mul_comm (2^32)). rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section SW8F.
  Variables (x2 x3 x4 x8 x9 x10 x20 x21 x22 x23 x27 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (T FP Y0 Y1 : Z).
  #[local] Notation L := (Z.of_nat (length bs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  Hypothesis TXT : bytes_at ASEGS m T bs.
  Hypothesis HL : (1 <= L <= 128)%Z.
  Hypothesis HT : (6529024 <= T <= 140737488355072)%Z.
  Hypothesis SHT : shz ASEGS m (ASAN_B + Y0) (Y1 - Y0).
  Hypothesis HY : (8 * Y0 <= T /\ T + L <= 8 * Y1)%Z.
  Hypothesis HFP : (T <= FP)%Z.

  #[local] Notation S8T pc x11 x12 x13 x14 x15 x16 x17 x18 x24 x25 x26 :=
    (MS (mkR (Zw 7) x2 x3 x4 (Zw 14974415777481871312) (Zw 9259542123273814144) (Zw 5063812098665367110) x8 x9 x10
             x11 x12 x13 x14 x15 x16 x17 x18 (Zw ASAN_B) x20 x21 x22 x23 x24 x25 x26 x27
             (Zw 100000000) (Zw 4294967296000100) (Zw 42949672960001) (Zw 1095216660735))
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).

  Definition sw8_post : machine_state -> Prop := fun ms' =>
    exists y11 y12 y13 y14 y15 y16 y17 y18 y24 y25 y26 : word,
      ((ms' = S8T 0x9a230 y11 y12 y13 y14 y15 y16 y17 y18 y24 y25 y26 /\ bv_unsigned y26 + 8 <= T + L)%Z \/
       ms' = S8T 0x9a118 y11 y12 y13 y14 y15 y16 y17 y18 y24 y25 y26) /\
      (FP <= bv_unsigned y26 <= T + L)%Z /\ bv_unsigned y11 = (T + L - bv_unsigned y26)%Z /\
      digs bs (FP - T) (bv_unsigned y26 - T).

  #[using="HY"] Lemma gran8 : forall A, (T <= A < T + L)%Z -> (ASAN_B + Y0 <= A / 8 + ASAN_B)%Z /\ (A / 8 + ASAN_B + 1 <= ASAN_B + Y0 + (Y1 - Y0))%Z.
  Proof. LiaFast.lf_pins (fun (HY : LiaFast.U) => LiaFast.u0). intros A HA. destruct HY as [Y1a Y2a]. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HFP"] Lemma loop8 : forall (n : nat) (kc : Z) (x13 x14 x15 x16 x17 x18 x25 : word),
      (L - kc <= Z.of_nat n)%Z -> (FP - T <= kc)%Z -> (kc + 8 <= L)%Z -> digs bs (FP - T) kc ->
      evt ASEGS sw8_post (S8T 0x99d04 (Zw (L - kc)) (Zw (T + kc + 7)) x13 x14 x15 x16 x17 x18 (Zw (ASAN_B + (T + kc) / 8)) x25
                             (Zw (T + kc))).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HFP : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros kc x13 x14 x15 x16 x17 x18 x25 Hn KC KC8 DGF; [exfalso; lia|].
    pose proof (shz_bound _ _ _ _ SHT) as BT.
    pose proof (tx_range bs kc) as R0. pose proof (tx_range bs (kc + 1)) as R1.
    pose proof (tx_range bs (kc + 2)) as R2. pose proof (tx_range bs (kc + 3)) as R3.
    pose proof (tx_range bs (kc + 4)) as R4. pose proof (tx_range bs (kc + 5)) as R5.
    pose proof (tx_range bs (kc + 6)) as R6. pose proof (tx_range bs (kc + 7)) as R7.
    pose proof (gran8 (T + kc) ltac:(lia)) as G0. pose proof (gran8 (T + kc + 7) ltac:(lia)) as G7.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (kc + 1)%Z RD. step. clear RD. fold_tx bs (kc + 1)%Z.
    txt_rd TXT (kc + 2)%Z RD. step. clear RD. fold_tx bs (kc + 2)%Z.
    txt_rd TXT (kc + 3)%Z RD. step. clear RD. fold_tx bs (kc + 3)%Z.
    txt_rd TXT (kc + 0)%Z RD. step. clear RD. fold_tx bs (kc + 0)%Z. try rewrite (Z.add_0_r kc).
    do 4 step. (* [comment removed for export] *)
    txt_rd TXT (kc + 4)%Z RD. step. clear RD. fold_tx bs (kc + 4)%Z.
    txt_rd TXT (kc + 5)%Z RD. step. clear RD. fold_tx bs (kc + 5)%Z.
    step. (* [comment removed for export] *)
    txt_rd TXT (kc + 6)%Z RD. step. clear RD. fold_tx bs (kc + 6)%Z.
    txt_rd TXT (kc + 7)%Z RD. step. clear RD. fold_tx bs (kc + 7)%Z.
    do 9 step. (* [comment removed for export] *)
    rewrite (ortree8_eq (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3))
                        (tx bs (kc + 4)) (tx bs (kc + 5)) (tx bs (kc + 6)) (tx bs (kc + 7))) by (apply tx_range).
    destruct (v8_facts _ _ _ _ _ _ _ _ R0 R1 R2 R3 R4 R5 R6 R7) as [VR VM].
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hsw.
    - clear Hsw. step. (* [comment removed for export] *) apply evt_done. do 11 eexists. split; [left; split; [reflexivity | rewrite unsigned_lit by lia; lia]|].
      rewrite !unsigned_lit by lia. split; [lia|]. split; [lia|]. replace (T + kc - T)%Z with kc by lia. exact DGF.
    - rewrite ?(unsigned_lit (v8 (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3))
                        (tx bs (kc + 4)) (tx bs (kc + 5)) (tx bs (kc + 6)) (tx bs (kc + 7)))) in Hsw by lia.
      destruct (swar8_dig _ _ _ _ _ _ _ _ _ R0 R1 R2 R3 R4 R5 R6 R7 eq_refl Hsw) as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7).
      clear Hsw.
      assert (DGF' : digs bs (FP - T) (kc + 8)).
      { replace (kc + 8)%Z with (kc + 4 + 4)%Z by lia.
        apply digs_snoc4; [apply digs_snoc4; assumption | exact D4 | | |].
        - replace (kc + 4 + 1)%Z with (kc + 5)%Z by lia. exact D5.
        - replace (kc + 4 + 2)%Z with (kc + 6)%Z by lia. exact D6.
        - replace (kc + 4 + 3)%Z with (kc + 7)%Z by lia. exact D7. }
      do 18 step. (* [comment removed for export] *)
      rewrite ?(unsigned_lit (L - kc)%Z) by lia.
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore. try rewrite signed_lit in Hmore by lia.
        goto (eapply (IH (kc + 8)%Z)); [lia | lia | lia | exact DGF'].
      + cond_cleanup Hmore. try rewrite signed_lit in Hmore by lia.
        step. (* [comment removed for export] *)
        apply evt_done. do 11 eexists. split; [right; reflexivity|].
        rewrite !unsigned_lit by lia. split; [lia|]. split; [lia|]. replace (T + kc + 8 - T)%Z with (kc + 8)%Z by lia. exact DGF'.
  Qed.
End SW8F.
End HxSw8FW.

Import OSSVerify.Proofs.fast_float.from_chars.lib.HX.HxGen OSSVerify.Proofs.fast_float.from_chars.lib.HX.HxSem OSSVerify.Proofs.fast_float.from_chars.lib.HX.HxInt OSSVerify.Proofs.fast_float.from_chars.lib.HX.HxTm OSSVerify.Proofs.fast_float.from_chars.lib.HX.HxSw4W OSSVerify.Proofs.fast_float.from_chars.lib.HX.HxSw8 OSSVerify.Proofs.fast_float.from_chars.lib.HX.HxSw8F.HxSw8FW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition SW8_KEYS_F : list Z := [11; 12; 13; 14; 15; 16; 17; 18; 24; 25; 26].
Definition sw8_chk_f (X : xst) : bool :=
  let L := xs_st X in
  match s_resv L with
  | RNone => (txt_rgs_ok L && lin_eqb (rgl L 19) (lconst SHBz) && lin_eqb (rgl L 12) (laddc (rgl L 26) 7)
              && forallb (fun '(k, c) => lin_eqb (rgl L k) (lconst c)) SW8_CONSTS
              && forallb (fact_implied (s_facts L)) (txt_facts ++ sw8_facts L))%bool
  | _ => false
  end.
Definition sw8_newf_f (L : sst) : list fact :=
  let P' := lvar (fv (s_next L) 10) in
  [FRange (lsub P' (rgl L 26)) 0 128; FRange (lsub TXT_TL P') 0 128; FRange (lsub (lvar (fv (s_next L) 0)) (lsub TXT_TL P')) 0 0].
Definition sw8_newf8_f (L : sst) : list fact := FRange (lsub TXT_TL (lvar (fv (s_next L) 10))) 8 128 :: sw8_newf_f L.
Definition sw8_newx_f (L : sst) : list xfact := [XF 0 [rgl L 26; lvar (fv (s_next L) 10)]].
Definition SW8_EXITS_F : list hx_exit := [(0x9a230, sw8_newf8_f, sw8_newx_f); (0x9a118, sw8_newf_f, sw8_newx_f)].
Definition H_SW8_F : xst -> option (list xst) := hx_regm 0x99d04 SW8_KEYS_F sw8_chk_f SW8_EXITS_F.

Theorem sw8_kit_f : hx_kitm ASEGS xok_spd 0x99d04 SW8_KEYS_F sw8_chk_f SW8_EXITS_F.
Proof.
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold sw8_chk_f in Hchk. cbn [xs_st xs_x] in Hchk.
  destruct (s_resv L) eqn:Hrv; try discriminate.
  apply andb_prop in Hchk as [Hchk Hfx]. apply andb_prop in Hchk as [Hchk Hcs]. apply andb_prop in Hchk as [Hchk H12].
  apply andb_prop in Hchk as [Hrg H19]. apply lin_eqb_eq in H19, H12.
  unfold SW8_CONSTS in Hcs. cbn [forallb] in Hcs. cbv beta iota in Hcs.
  repeat match type of Hcs with (?a && ?b)%bool = true => apply andb_prop in Hcs as [?C Hcs] end.
  apply lin_eqb_eq in C, C0, C1, C2, C3, C4, C5, C6.
  rewrite forallb_app in Hfx. apply andb_prop in Hfx as [Hfx HfS].
  pose proof (txt_bounds E ms L Hd Hfx) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (txt_bytes E ms L Hd Hrg Hfx) as (bs & TXT & Hlen).
  pose proof (txt_shadow E ms L Hd Hrg Hfx) as SHT.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  set (Tz := bv_unsigned (E 1%positive)) in *. set (Lz := bv_unsigned (E 2%positive)) in *.
  set (Y0z := bv_unsigned (E 7%positive)) in *. set (Y1z := bv_unsigned (E 8%positive)) in *.
  set (Xl := rgl L 26) in *. set (Xz := bv_unsigned (lden E Xl)).
  set (A1z := bv_unsigned (lden E (rgl L 11))). set (S8z := bv_unsigned (lden E (rgl L 24))).
  pose proof (bv_unsigned_in_range _ (lden E Xl)) as BX. pose proof (bv_unsigned_in_range _ (lden E (rgl L 11))) as BA1.
  pose proof (bv_unsigned_in_range _ (lden E (rgl L 24))) as BS8.
  unfold bv_modulus in BX, BA1, BS8. change (2 ^ Z.of_N 64) with two64 in BX, BA1, BS8.
  unfold sw8_facts in HfS. fold Xl in HfS. cbn [forallb] in HfS.
  repeat match type of HfS with (?a && ?b)%bool = true => apply andb_prop in HfS as [?F HfS] end.
  pose proof (fact_implied_ok E _ _ HF F) as X1. pose proof (fact_implied_ok E _ _ HF F0) as X2.
  pose proof (fact_implied_ok E _ _ HF F1) as X3. pose proof (fact_implied_ok E _ _ HF F2) as X4.
  pose proof (fact_implied_ok E _ _ HF F3) as X5.
  cbn [fact_ok] in X1, X2, X3, X4, X5. rewrite (u_sub E) in X1, X2, X3, X4. rewrite (u_sub E) in X3.
  rewrite (u_scale E), lden_laddc, u_Z_to_bv in X4. rewrite lden_laddc, u_Z_to_bv in X5.
  unfold TXT_TL, TXT_T, TXT_L in X1, X2, X3. rewrite (u_add E) in X2, X3. rewrite !lden_lvar in X1. rewrite !lden_lvar in X2.
  rewrite !lden_lvar in X3. fold Tz Lz Xz A1z S8z in X1, X2, X3, X4, X5.
  assert (M3 : (Tz + Lz) mod two64 = Tz + Lz) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite M3 in X2, X3.
  assert (HS : Tz <= Xz /\ Xz + 8 <= Tz + Lz) by (clear -X1 X2 BX B1 B2; unfold two64 in *; split; Z.div_mod_to_equations; lia).
  assert (HA1 : A1z = Tz + Lz - Xz).
  { clear -X3 HS BX BA1 B1 B2. unfold two64 in *. rewrite (Z.mod_small (Tz + Lz - Xz)) in X3 by lia.
    Z.div_mod_to_equations. lia. }
  assert (HS8 : S8z = ASAN_B + Xz / 8).
  { set (d := (S8z + - SHBz) mod two64) in *.
    assert (Hd8 : 0 <= d <= 2 ^ 48) by exact X5.
    assert (M8 : (8 * d) mod two64 = 8 * d) by (apply Z.mod_small; unfold two64; lia).
    rewrite M8 in X4.
    assert (HX8 : 8 * d <= Xz <= 8 * d + 7).
    { clear -X4 Hd8 HS BX B2. unfold two64 in *. Z.div_mod_to_equations. lia. }
    assert (Hq : d = Xz / 8) by (clear -HX8; Z.div_mod_to_equations; lia).
    assert (HdS : d = S8z - SHBz).
    { clear -X5 BS8 Hd8. unfold d, SHBz, two64 in *. Z.div_mod_to_equations. lia. }
    unfold SHBz in HdS. lia. }
  clear X1 X2 X3 X4 X5.
  assert (RG : forall k, getr (ms_regs ms) (Z_to_bv 5 k) = lden E (rgl L k)) by (intros k; rewrite (HR _); reflexivity).
  assert (Rc : forall k c, rgl L k = lconst c -> getr (ms_regs ms) (Z_to_bv 5 k) = Z_to_bv 64 c).
  { intros k c Hk. rewrite (RG k), Hk, lden_lconst. reflexivity. }
  assert (R1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 7) by (exact (Rc 1 7 C)).
  assert (R5 : getr (ms_regs ms) 5%bv = Z_to_bv 64 14974415777481871312) by (exact (Rc 5 _ C0)).
  assert (R6 : getr (ms_regs ms) 6%bv = Z_to_bv 64 9259542123273814144) by (exact (Rc 6 _ C1)).
  assert (R7 : getr (ms_regs ms) 7%bv = Z_to_bv 64 5063812098665367110) by (exact (Rc 7 _ C2)).
  assert (R28 : getr (ms_regs ms) 28%bv = Z_to_bv 64 100000000) by (exact (Rc 28 _ C3)).
  assert (R29 : getr (ms_regs ms) 29%bv = Z_to_bv 64 4294967296000100) by (exact (Rc 29 _ C4)).
  assert (R30 : getr (ms_regs ms) 30%bv = Z_to_bv 64 42949672960001) by (exact (Rc 30 _ C5)).
  assert (R31 : getr (ms_regs ms) 31%bv = Z_to_bv 64 1095216660735) by (exact (Rc 31 _ C6)).
  assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 ASAN_B) by (exact (Rc 19 _ H19)).
  assert (Rw : forall k z, bv_unsigned (lden E (rgl L k)) = z -> getr (ms_regs ms) (Z_to_bv 5 k) = Z_to_bv 64 z).
  { intros k z Hz. rewrite RG. rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R26 : getr (ms_regs ms) 26%bv = Z_to_bv 64 Xz) by (apply (Rw 26); reflexivity).
  assert (R26' : getr (ms_regs ms) 26%bv = Z_to_bv 64 (Tz + (Xz - Tz))) by (apply (Rw 26); fold Xl Xz; ring).
  assert (R11 : getr (ms_regs ms) 11%bv = Z_to_bv 64 (Z.of_nat (length bs) - (Xz - Tz))) by (apply (Rw 11); fold A1z; rewrite HA1, Hlen; ring).
  assert (R24 : getr (ms_regs ms) 24%bv = Z_to_bv 64 (ASAN_B + (Tz + (Xz - Tz)) / 8)).
  { apply (Rw 24). fold S8z. rewrite HS8. f_equal. f_equal. ring. }
  assert (R12 : getr (ms_regs ms) 12%bv = Z_to_bv 64 (Tz + (Xz - Tz) + 7)).
  { transitivity (lden E (rgl L 12)); [exact (RG 12)|]. rewrite H12. rewrite lden_laddc. fold Xl Xz. f_equal. ring. }
  set (R := ms_regs ms) in *.
  assert (HK : evt ASEGS (sw8_post (getr R 2) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 10) (getr R 20) (getr R 21) (getr R 22)
                 (getr R 23) (getr R 27) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) bs Tz Xz)
             (kms ASEGS ms)).
  { assert (P1 : 1 <= Z.of_nat (length bs) <= 128) by (clear -Hlen B1; lia).
    assert (P2 : 6529024 <= Tz <= 140737488355072) by (clear -B2; lia).
    assert (P3 : 8 * Y0z <= Tz /\ Tz + Z.of_nat (length bs) <= 8 * Y1z) by (clear -Hlen B5 B6; lia).
    assert (P4 : Tz <= Xz) by (clear -HS; lia).
    unfold kms, mkR_of. fold R. rewrite Hpc0, Hresv0, R1, R5, R6, R7, R11, R12, R24, R19, R26', R28, R29, R30, R31, Hpc.
    exact (loop8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs Tz Xz Y0z Y1z TXT P1 P2 SHT P3 P4 (Datatypes.S (Z.to_nat (Z.of_nat (length bs) - (Xz - Tz))))
             (Xz - Tz) _ _ _ _ _ _ _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -Hlen HS; lia) ltac:(replace (Xz - Tz) with (Xz - Tz) by lia; apply digs_nil)). }
  destruct (kit_run ASEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y24 & y25 & y26 & Hms2 & HFE & HA1' & HDG).
  set (vs := [y11; y12; y13; y14; y15; y16; y17; y18; y24; y25; y26]).
  set (E' := E_of SW8_KEYS_F vs (s_next L) E).
  assert (Hy26 : E' (fv (s_next L) 10) = y26) by (exact (E_of_nth SW8_KEYS_F vs (s_next L) E 10 y26 eq_refl eq_refl)).
  assert (Hy11 : E' (fv (s_next L) 0) = y11) by (exact (E_of_nth SW8_KEYS_F vs (s_next L) E 0 y11 eq_refl eq_refl)).
  assert (Hag : agree (s_next L) E E') by apply E_of_agree.
  unfold state_wf in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hwr Hwg].
  assert (HwX : lwf (s_next L) Xl = true) by (exact (regs_wf_n_spec _ _ 31 Hwr 26%nat ltac:(lia))).
  assert (EX : lden E' Xl = lden E Xl) by (symmetry; exact (lden_agree _ E E' Xl HwX Hag)).
  assert (Hv12 : (1 < s_next L)%positive /\ (2 < s_next L)%positive).
  { unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1' rs]] eqn:Hr; try discriminate.
    apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 _].
    apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. cbn [forallb] in Hwg. apply andb_prop in Hwg as [Hw0 _].
    unfold rwf in Hw0. apply andb_prop in Hw0 as [Hw0 _]. apply andb_prop in Hw0 as [Hw0a Hw0b]. rewrite Hb0 in Hw0a. rewrite Hs0 in Hw0b.
    unfold lwf, TXT_T, TXT_L, lvar in Hw0a, Hw0b. cbn in Hw0a, Hw0b. apply andb_prop in Hw0a as [Hw0a _]. apply andb_prop in Hw0b as [Hw0b _].
    apply Pos.ltb_lt in Hw0a, Hw0b. split; assumption. }
  assert (E1' : E' 1%positive = E 1%positive) by (unfold E'; apply E_of_old; lia).
  assert (E2' : E' 2%positive = E 2%positive) by (unfold E'; apply E_of_old; lia).
  assert (COMMON : forall pc1 (msx : machine_state),
     msx = MS (mkR (Z_to_bv 64 7) (getr R 2) (getr R 3) (getr R 4) (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 9259542123273814144)
                   (Z_to_bv 64 5063812098665367110) (getr R 8) (getr R 9) (getr R 10) y11 y12 y13 y14 y15 y16 y17 y18 (Z_to_bv 64 ASAN_B)
                   (getr R 20) (getr R 21) (getr R 22) (getr R 23) y24 y25 y26 (getr R 27)
                   (Z_to_bv 64 100000000) (Z_to_bv 64 4294967296000100) (Z_to_bv 64 42949672960001) (Z_to_bv 64 1095216660735))
              (ms_fregs ms) (Z_to_bv 64 pc1) (ms_fcsr ms) None (ms_mem ms) (seg_rom ASEGS) ->
     ms_eqv ms1 (with_rom msx (ms_rom ms)) ->
     isteps ASEGS ms ms1 /\ length vs = length SW8_KEYS_F /\
      ms_mem ms1 = ms_mem ms /\ ms_fcsr ms1 = ms_fcsr ms /\ ms_resv ms1 = ms_resv ms /\ ms_svc_pending ms1 = None /\
      ms_pc_val ms1 = Z_to_bv 64 pc1 /\
      (forall r, ~ In (bv_unsigned r) SW8_KEYS_F -> getr (ms_regs ms1) r = getr (ms_regs ms) r) /\
      (forall i k v, nth_error SW8_KEYS_F i = Some k -> nth_error vs i = Some v -> getr (ms_regs ms1) (Z_to_bv 5 k) = v)).
  { intros pc1 msx -> Heq2. destruct Heq2 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
    split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
    split; [exact E4|]. split; [exact E3|]. split.
    - intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
      unfold SW8_KEYS_F in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
      do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact R1) | (symmetry; exact R5) | (symmetry; exact R6)
                                              | (symmetry; exact R7) | (symmetry; exact R19) | (symmetry; exact R28) | (symmetry; exact R29)
                                              | (symmetry; exact R30) | (symmetry; exact R31)
                                              | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
      lia.
    - intros i k v Hi Hv. rewrite (E1 _).
      destruct i as [|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]; cbn in Hi, Hv;
        first [ (injection Hi as <-; injection Hv as <-; reflexivity) | (destruct i; discriminate) ]. }
  assert (FACTS : Forall (fact_ok E') (sw8_newf_f L) /\ Forall (xfact_ok xok_spd E' m0) (sw8_newx_f L)).
  { split.
    - unfold sw8_newf_f. fold Xl. constructor; [|constructor; [|constructor; [|constructor]]]; cbn [fact_ok].
      + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy26, EX. fold Xz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
        rewrite Z.mod_small by (unfold two64 in *; lia). lia.
      + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy26. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, bv_add_unsigned, !lden_lvar, E1', E2'.
        fold Tz Lz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite (Z.mod_small (Tz + Lz)) by (unfold two64 in *; lia).
        rewrite Z.mod_small by (unfold two64 in *; lia). lia.
      + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy11, lden_lsub, bv_sub_unsigned, lden_lvar, Hy26.
        unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, bv_add_unsigned, !lden_lvar, E1', E2'.
        fold Tz Lz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite (Z.mod_small (Tz + Lz)) by (unfold two64 in *; lia).
        rewrite (Z.mod_small (Tz + Lz - bv_unsigned y26)) by (unfold two64 in *; lia). rewrite HA1', Hlen. rewrite Z.sub_diag.
        change (0 mod two64) with 0. lia.
    - unfold sw8_newx_f. fold Xl. constructor; [|constructor]. unfold xfact_ok. cbn [xf_tag xf_args List.map xok_spd].
      rewrite EX, lden_lvar, Hy26. fold Xz.
      exists Tz, bs. split.
      + apply (bytes_at_transport (ms_mem ms)); [exact TXT|]. intros i Hi.
        unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1' rs]] eqn:Hr; try discriminate.
        apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 Hk0].
        apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. destruct (rg_kind R0) eqn:Hk; cbn in Hk0; try discriminate.
        rewrite <- Hr in Hm0. exact (txt_frame E L ms m0 R0 (R1' :: rs) i Hr Hb0 Hs0 Hk Hm0 ltac:(lia) ltac:(unfold two64 in *; lia)).
      + split; [lia|]. split; [lia|]. exact HDG. }
  destruct Hms2 as [(Hms2 & H8)|Hms2].
  - exists 0x9a230, sw8_newf8_f, sw8_newx_f, ms1, vs. split; [left; reflexivity|].
    destruct (COMMON 0x9a230 ms2 Hms2 Heq) as (C1' & C2' & C3' & C4' & C5' & C6' & C7' & C8' & C9').
    do 9 (split; [assumption|]). fold E'. destruct FACTS as [FA FX]. split; [|exact FX].
    unfold sw8_newf8_f. constructor; [|exact FA]. cbn [fact_ok].
    rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy26. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, bv_add_unsigned, !lden_lvar, E1', E2'.
    fold Tz Lz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite (Z.mod_small (Tz + Lz)) by (unfold two64 in *; lia).
    rewrite Z.mod_small by (unfold two64 in *; lia). rewrite <- Hlen. lia.
  - exists 0x9a118, sw8_newf_f, sw8_newx_f, ms1, vs. split; [right; left; reflexivity|].
    destruct (COMMON 0x9a118 ms2 Hms2 Heq) as (C1' & C2' & C3' & C4' & C5' & C6' & C7' & C8' & C9').
    do 9 (split; [assumption|]). fold E'. exact FACTS.
Qed.

Theorem H_SW8_F_ok : hand_okx ASEGS xok_spd H_SW8_F.
Proof. apply hx_okm. exact sw8_kit_f. Qed.
