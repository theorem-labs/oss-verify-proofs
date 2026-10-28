(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv DecCut. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0_glue10K.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require UKit.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require FLiaA.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= FLiaA.lia_f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.
Section M.
  Variables (usp S strm src len : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (payload : list byte).
  Hypothesis GEO : (0 < S /\ S + 64144 <= strm /\ alloc_ceiling <= usp - 1024 /\ usp + 112 <= strm /\ strm + 80 < 2 ^ 64 /\
                    0 < src /\ src + len <= alloc_ceiling /\ 0 <= len < 2 ^ 27 /\ Z.of_nat (length payload) = len)%Z.
  Hypothesis SEPsrc : (S + 64144 <= src \/ src + len <= S)%Z.
  Hypothesis SAL : (strm mod 8 = 0)%Z.

  Definition MXF (OUT : Z -> Prop) (Q : machine_state -> Prop) (m : word -> option byte) (h : dsh) (b : bzs)
      (x1 x5 x6 x7 x8 x9 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word) : Prop :=
    forall (rc : Z) (y11 y12 y13 y14 y15 y16 y17 : word) (m' : word -> option byte) (st bsBuff' bsLive' nn ai' : Z) (til' tih' : word),
      let h' := DSH (sh_strm h) st (sh_soch h) (sh_p1 h) (sh_solen h) (sh_brand h) (sh_p2 h) (sh_rNToGo h) (sh_rTPos h)
                    bsBuff' bsLive' nn (sh_small h) (sh_p3 h) (sh_cbn h) (sh_verb h) (sh_origPtr h) (sh_tPos h) (sh_k0 h) in
      rw_cells s0segs m' S (HEAD_CELLS h') -> (10 <= st <= 13)%Z -> (0 <= bsBuff' < 2 ^ 32)%Z -> (0 <= nn < 2 ^ 32)%Z ->
      rw_cells s0segs m' strm (STRM_CELLS (bupd b ai' til' tih')) -> (0 <= ai' <= bs_ai b)%Z ->
      (0 <= bsLive' <= 8 * (len - ai'))%Z ->
      munch [(S, S + 68); (strm, strm + 20)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
      (rc = 0 \/ rc = -5)%Z -> OUT rc ->
      evt s0segs Q (MSd usp S strm gp tp F fc 0x2613c m' x1 x5 x6 x7 x8 x9 (Z_to_bv 64 rc) y11 y12 y13 y14 y15 y16 y17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31).


  (* [comment removed for export] *)
  Lemma srl_mask_byte : forall bb b, (0 <= bb)%Z -> (0 <= b < 256)%Z ->
    Z.land (bv_swrap 32 ((bb * 256 + b) / 1) mod 18446744073709551616) 255 = b.
  Proof.
    intros bb b Hbb Hb. rewrite Z.div_1_r. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
    change (2 ^ 8)%Z with 256%Z.
    rewrite (Z.mod_mod_divide _ 18446744073709551616 256) by (exists 72057594037927936%Z; reflexivity).
    unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 `div` 2)%Z with 2147483648%Z.
    rewrite <- (Z.mod_mod_divide _ 4294967296 256) by (exists 16777216%Z; reflexivity).
    rewrite Zminus_mod_idemp_l.
    replace (bb * 256 + b + 2147483648 - 2147483648)%Z with (b + bb * 256)%Z by lia.
    rewrite (Z.mod_mod_divide _ 4294967296 256) by (exists 16777216%Z; reflexivity).
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  Qed.

  Lemma sx32_srl_mask_byte : forall bb b, (0 <= bb < 2 ^ 24)%Z -> (0 <= b < 256)%Z ->
    Z.land (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 (bb * 256 + b))) mod 4294967296 / 1) mod 18446744073709551616) 255 = b.
  Proof.
    intros bb b Hbb Hb.
    assert (E : (bv_unsigned (sx32 (Z_to_bv 64 (bb * 256 + b))) mod 4294967296 = bb * 256 + b)%Z).
    { unfold sx32. rewrite (unsigned_lit (bb * 256 + b)) by lia. rewrite Z_to_bv_unsigned.
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
      rewrite (Z.mod_mod_divide _ 18446744073709551616 4294967296) by (exists 4294967296%Z; reflexivity).
      unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
      change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 `div` 2)%Z with 2147483648%Z.
      rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
      replace (bb * 256 + b + 2147483648 - 2147483648)%Z with (bb * 256 + b)%Z by lia.
      apply Z.mod_small. lia. }
    rewrite E. apply srl_mask_byte; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma g10F_M123 : forall (hd lbl cmpv nx : Z),
    ((hd = 0x247c4 /\ lbl = 10 /\ cmpv = 66 /\ nx = 0x24888) \/
     (hd = 0x24888 /\ lbl = 11 /\ cmpv = 90 /\ nx = 0x2494c) \/
     (hd = 0x2494c /\ lbl = 12 /\ cmpv = 104 /\ nx = 0x24a0c))%Z ->
    forall (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (h : dsh) (b : bzs) (Q : machine_state -> Prop),
    rw_cells s0segs m S (HEAD_CELLS h) -> sh_strm h = strm -> sh_bsLive h = 0%Z -> (0 <= sh_bsBuff h < 2 ^ 24)%Z ->
    (0 <= sh_n h < 2 ^ 32)%Z ->
    length (sh_p1 h) = 3%nat -> length (sh_p2 h) = 3%nat -> length (sh_p3 h) = 3%nat ->
    rw_cells s0segs m strm (STRM_CELLS b) -> bs_src b = src -> bs_len b = len -> (0 <= bs_ai b <= len)%Z ->
    bs_til b = Z_to_bv 64 (len - bs_ai b) -> (0 <= bs_av b <= bs_dlen b)%Z -> (0 <= bs_dst b /\ bs_dst b + bs_dlen b < 2 ^ 64)%Z ->
    (0 <= bs_S b < 2 ^ 64)%Z ->
    bytes_at s0segs m src payload ->
    mem_inv s0segs m ->
    MXF (fun rc => (rc = 0 /\ bs_ai b = 0) \/
                   (rc = -5 /\ exists b8, nth_error payload (Z.to_nat (len - bs_ai b)) = Some b8 /\ bv_unsigned b8 <> cmpv))%Z
        Q m h b x1 x5 x6 x7 x8 x9 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 ->
    (forall (y12 y13 y14 y15 y16 : word) (m' : word -> option byte) (b8 : byte),
        let h' := DSH (sh_strm h) lbl (sh_soch h) (sh_p1 h) (sh_solen h) (sh_brand h) (sh_p2 h) (sh_rNToGo h) (sh_rTPos h)
                      (sh_bsBuff h * 256 + cmpv)%Z 0 (sh_n h) (sh_small h) (sh_p3 h) (sh_cbn h) (sh_verb h) (sh_origPtr h) (sh_tPos h) (sh_k0 h) in
        rw_cells s0segs m' S (HEAD_CELLS h') ->
        nth_error payload (Z.to_nat (len - bs_ai b)) = Some b8 -> bv_unsigned b8 = cmpv ->
        rw_cells s0segs m' strm (STRM_CELLS (bupd b (bs_ai b - 1) (Z_to_bv 64 (len - (bs_ai b - 1))) (bs_tih b))) -> (1 <= bs_ai b)%Z ->
        munch [(S, S + 68); (strm, strm + 20)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
        evt s0segs Q (MSd usp S strm gp tp F fc nx m' x1 x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 cmpv) y12 y13 y14 y15 y16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31)) ->
    evt s0segs Q (MSd usp S strm gp tp F fc hd m x1 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31).
  Proof.
    intros hd lbl cmpv nx SITE. intros until Q.
    intros HD Hstrm HBL HBB HN L1 L2 L3 STRM Hsrc Hlen Hai TIL Hav Hdst HS PAY MI HX HN'.
    cps_pose GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
    assert (LS7 : (Z.land strm 7 = 0)%Z) by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; exact SAL).
    unfold MSd in *. unfold MXF in HX.
    rewrite Hstrm, HBL in HD. rewrite TIL, Hsrc, Hlen in STRM.
    set (ai := bs_ai b) in *. set (bb := sh_bsBuff h) in *.
    pose proof (munch_refl [(S, S + 68); (strm, strm + 20)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    destruct SITE as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (-> & -> & -> & ->)]].
    all: UKit.ustep; UKit.ustep; UKit.ustep; wstepl; if_false_z.
    (* [comment removed for export] *)
    all: UKit.ustep; UKit.ustep; rewrite ?LS7.
    all: UKit.ustep; UKit.ustep; UKit.ustep; wstepl; UKit.u_guard.
    all: UKit.ustep.
    all: wstepl; if_cases K2; zify_cond K2;
      [ (* [comment removed for export] *)
          wstepl; wstepl;
          enter_with (HX 0%Z); [ st_eq | by_head S Hstrm | lia | lia | lia | by_strm strm Hsrc Hlen | lia | lia | exact MUL | exact WML | by_mi | lia
                               | left; split; [reflexivity| clear -K2 Hai G8; mlia] ] | ].
    (* [comment removed for export] *)
    all: assert (AI1 : (1 <= ai)%Z) by (clear -K2 Hai G8; mlia); clear K2.
    all: UKit.ustep; wstepl; UKit.u_guard; UKit.ustep.
    all: destruct (nth_error_ok payload (len - ai)%Z (length payload) eq_refl ltac:(lia)) as [b8 NTH];
         pose proof (u8ro_read s0segs _ src payload (len - ai)%Z b8 _ PAY NTH ltac:(lia) eq_refl) as RD.
    all: wstepl; clear RD.
    (* [comment removed for export] *)
    all: pose proof (bv_unsigned_in_range 8 b8) as Rb8; unfold bv_modulus in Rb8; cbn in Rb8.
    all: wstepl; wstepl; wstepl; or_lin.
    all: UKit.ustep; UKit.ustep; wstepl; UKit.u_guard.
    all: wstepl; wstepl; wstepl; wstepl; wstepl; wstepl; wstepl.
    all: wstepl; if_true_z.
    (* [comment removed for export] *)
    all: UKit.ustep; wstepl; if_false_z.
    all: UKit.ustep; UKit.ustep; wstepl; UKit.u_guard.
    (* [comment removed for export] *)
    all: wstepl; wstepl; wstepl; rewrite (sx32_srl_mask_byte bb (bv_unsigned b8)) by lia; wstepl; wstepl.
    all: wstepl; if_cases K3; zify_cond K3;
      [ (* [comment removed for export] *)
        wstepl; wstepl;
        enter_with (HX (-5)%Z); [ st_eq | by_head S Hstrm | lia | lia | lia | by_strm strm Hsrc Hlen | lia | lia | exact MUL | exact WML | by_mi | lia
                                  | right; split; [reflexivity| exists b8; split; [exact NTH| clear -K3 Rb8; mlia]] ]
      | ].
    1-2: wstepl.
    (* [comment removed for export] *)
    all: lazymatch type of HN' with context [bv_unsigned _ = ?c -> _] => assert (E8 : bv_unsigned b8 = c) by (clear -K3 Rb8; mlia) end.
    all: enter_with (HN' _ _ _ _ _ _ b8); [ st_eq | by_head S Hstrm | exact NTH | exact E8 | by_strm strm Hsrc Hlen | lia | exact MUL | exact WML | by_mi ].
  Qed.

  (* [comment removed for export] *)
  Lemma g10F_M4 :
    forall (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (h : dsh) (b : bzs) (Q : machine_state -> Prop),
    rw_cells s0segs m S (HEAD_CELLS h) -> sh_strm h = strm -> sh_bsLive h = 0%Z -> (0 <= sh_bsBuff h < 2 ^ 24)%Z ->
    (0 <= sh_n h < 2 ^ 32)%Z ->
    length (sh_p1 h) = 3%nat -> length (sh_p2 h) = 3%nat -> length (sh_p3 h) = 3%nat ->
    rw_cells s0segs m strm (STRM_CELLS b) -> bs_src b = src -> bs_len b = len -> (0 <= bs_ai b <= len)%Z ->
    bs_til b = Z_to_bv 64 (len - bs_ai b) -> (0 <= bs_av b <= bs_dlen b)%Z -> (0 <= bs_dst b /\ bs_dst b + bs_dlen b < 2 ^ 64)%Z ->
    (0 <= bs_S b < 2 ^ 64)%Z ->
    bytes_at s0segs m src payload ->
    mem_inv s0segs m ->
    MXF (fun rc => (rc = 0 /\ bs_ai b = 0) \/
                   (rc = -5 /\ exists b8, nth_error payload (Z.to_nat (len - bs_ai b)) = Some b8 /\
                                          ~ (49 <= bv_unsigned b8 <= 57)))%Z
        Q m h b x1 x5 x6 x7 x8 x9 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 ->
    (forall (y11 y13 y14 y15 y16 y17 : word) (m' : word -> option byte) (b8 : byte) (uc : Z),
        let h' := DSH (sh_strm h) 13 (sh_soch h) (sh_p1 h) (sh_solen h) (sh_brand h) (sh_p2 h) (sh_rNToGo h) (sh_rTPos h)
                      (sh_bsBuff h * 256 + uc)%Z 0 uc (sh_small h) (sh_p3 h) (sh_cbn h) (sh_verb h) (sh_origPtr h) (sh_tPos h) (sh_k0 h) in
        rw_cells s0segs m' S (HEAD_CELLS h') -> (49 <= uc <= 57)%Z ->
        nth_error payload (Z.to_nat (len - bs_ai b)) = Some b8 -> bv_unsigned b8 = uc ->
        rw_cells s0segs m' strm (STRM_CELLS (bupd b (bs_ai b - 1) (Z_to_bv 64 (len - (bs_ai b - 1))) (bs_tih b))) -> (1 <= bs_ai b)%Z ->
        munch [(S, S + 68); (strm, strm + 20)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
        evt s0segs Q (MSd usp S strm gp tp F fc 0x24b14 m' x1 x5 x6 x7 x8 x9 (Z_to_bv 64 0) y11 (Z_to_bv 64 uc) y13 y14 y15 y16 y17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31)) ->
    evt s0segs Q (MSd usp S strm gp tp F fc 0x24a0c m x1 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until Q.
    intros HD Hstrm HBL HBB HN L1 L2 L3 STRM Hsrc Hlen Hai TIL Hav Hdst HS PAY MI HX HN'.
    cps_pose GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
    assert (LS7 : (Z.land strm 7 = 0)%Z) by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; exact SAL).
    unfold MSd in *. unfold MXF in HX.
    rewrite Hstrm, HBL in HD. rewrite TIL, Hsrc, Hlen in STRM.
    set (ai := bs_ai b) in *. set (bb := sh_bsBuff h) in *.
    pose proof (munch_refl [(S, S + 68); (strm, strm + 20)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    UKit.ustep; UKit.ustep; UKit.ustep; UKit.ustep; UKit.ustep; rewrite ?LS7.
    wstepl; if_false_z.
    (* [comment removed for export] *)
    UKit.ustep; UKit.ustep; UKit.ustep; UKit.ustep; wstepl; UKit.u_guard.
    UKit.ustep.
    wstepl; if_cases K2; zify_cond K2;
      [ (* [comment removed for export] *)
          wstepl; wstepl;
          enter_with (HX 0%Z); [ st_eq | by_head S Hstrm | lia | lia | lia | by_strm strm Hsrc Hlen | lia | lia | exact MUL | exact WML | by_mi | lia
                               | left; split; [reflexivity| clear -K2 Hai G8; mlia] ] | ].
    assert (AI1 : (1 <= ai)%Z) by (clear -K2 Hai G8; mlia); clear K2.
    UKit.ustep; wstepl; UKit.u_guard; UKit.ustep.
    destruct (nth_error_ok payload (len - ai)%Z (length payload) eq_refl ltac:(lia)) as [b8 NTH];
      pose proof (u8ro_read s0segs _ src payload (len - ai)%Z b8 _ PAY NTH ltac:(lia) eq_refl) as RD.
    wstepl; clear RD.
    pose proof (bv_unsigned_in_range 8 b8) as Rb8; unfold bv_modulus in Rb8; cbn in Rb8.
    wstepl; wstepl; wstepl; or_lin.
    UKit.ustep; UKit.ustep; wstepl; UKit.u_guard.
    wstepl; wstepl; wstepl; wstepl; wstepl; wstepl; wstepl.
    wstepl; if_true_z.
    UKit.ustep; wstepl; if_false_z.
    UKit.ustep; UKit.ustep; wstepl; UKit.u_guard.
    (* [comment removed for export] *)
    wstepl; wstepl; wstepl; wstepl; rewrite (sx32_srl_mask_byte bb (bv_unsigned b8)) by lia; wstepl; wstepl; wstepl.
    wstepl; if_cases K3; zify_cond K3;
      [ | (* [comment removed for export] *)
          wstepl; wstepl;
          enter_with (HX (-5)%Z); [ st_eq | by_head S Hstrm | lia | lia | lia | by_strm strm Hsrc Hlen | lia | lia | exact MUL | exact WML | by_mi | lia
                                    | right; split; [reflexivity| exists b8; split; [exact NTH| clear -K3 Rb8; mlia]] ] ].
    enter_with (HN' _ _ _ _ _ _ _ b8 (bv_unsigned b8)); [ st_eq | by_head S Hstrm | clear -K3 Rb8; mlia | exact NTH | reflexivity | by_strm strm Hsrc Hlen | lia | exact MUL | exact WML | by_mi ].
  Qed.
End M.
End ACeilS1.
