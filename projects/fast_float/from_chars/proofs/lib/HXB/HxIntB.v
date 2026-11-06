(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxEnt FxRgs FxFacts FxPlan FxFrame FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require Import HxGenFp.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require HxSemB.

Module HxIntBW.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ms_eq_tac ::=
  cbv beta delta [mkR];
  repeat first [ reflexivity
               | lazymatch goal with |- @eq (bv _) _ _ => ms_leaf_eq end
               | progress f_equal ].

Notation BSEGS := AsanUbsan.M.loaded_segments.

Section INT.
  Variables (x1 x2 x3 x4 x6 x7 x8 x9 x18 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (T S Y0 Y1 : Z).
  #[local] Notation L := (Z.of_nat (length bs)).
  Hypothesis TXT : bytes_at BSEGS m T bs.
  Hypothesis HL : (1 <= L <= 128)%Z.
  Hypothesis HT : (6537216 <= T <= 140737488355072)%Z.
  Hypothesis HS : (T <= S <= T + L)%Z.
  Hypothesis SHT : shz BSEGS m (ASAN_B + Y0) (Y1 - Y0).
  Hypothesis HY : (8 * Y0 <= T /\ T + L <= 8 * Y1)%Z.

  Definition int_post : machine_state -> Prop := fun ms' =>
    exists a0 a1 a2 a3 a4 a5 a6 a7 t0 : word,
      ms' = MS (mkR x1 x2 x3 x4 t0 x6 x7 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 ASAN_B) x20 (Z_to_bv 64 S) (Z_to_bv 64 (T + L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x931dc) fc None m (seg_rom BSEGS)
      /\ (S <= bv_unsigned a0 <= T + L)%Z /\ digs bs (S - T) (bv_unsigned a0 - T).

  #[using="HY"] Lemma tx_gran : forall A, (T <= A < T + L)%Z -> (ASAN_B + Y0 <= A / 8 + ASAN_B)%Z /\ (A / 8 + ASAN_B + 1 <= ASAN_B + Y0 + (Y1 - Y0))%Z.
  Proof. LiaFast.lf_pins (fun (HY : LiaFast.U) => LiaFast.u0). intros A HA. destruct HY as [Y1a Y2a]. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT HS SHT HY"] Lemma loopI : forall (n : nat) (k : Z) (a4 a5 a7 t0 : word),
      (T + L - (T + k) <= Z.of_nat n)%Z -> (S - T <= k <= L)%Z -> digs bs (S - T) k ->
      evt BSEGS int_post
        (MS (mkR x1 x2 x3 x4 t0 x6 x7 x8 x9 (Z_to_bv 64 (T + k)) (Z_to_bv 64 (T + k)) (Z_to_bv 64 2) (Z_to_bv 64 10) a4 a5 (Z_to_bv 64 9) a7
                 x18 (Z_to_bv 64 ASAN_B) x20 (Z_to_bv 64 S) (Z_to_bv 64 (T + L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x93128) fc None m (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT HS SHT HY : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros k a4 a5 a7 t0 Hn HK DG;
      (step; (* [comment removed for export] *) if_cases He;
       [ cond_cleanup He | cond_cleanup He;
         step; (* [comment removed for export] *) step; (* [comment removed for export] *) step; (* [comment removed for export] *)
         apply evt_done; do 9 eexists; split; [reflexivity|]; rewrite unsigned_lit by lia; split; [lia|];
         replace (T + L - T)%Z with k by lia; exact DG ]).
    - exfalso. lia.
    - pose proof (shz_bound _ _ _ _ SHT) as BT.
      pose proof (tx_gran (T + k) ltac:(lia)) as G0.
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      txt_rd TXT k RD. pose proof (tx_range bs k) as Rk.
      step. (* [comment removed for export] *)
      clear RD. fold_tx bs k.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hd.
      + cond_cleanup Hd. clear Hd. apply evt_done.
        do 9 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|]. replace (T + k - T)%Z with k by lia. exact DG.
      + cond_cleanup Hd. pose proof (dig_yes _ Rk Hd) as D. clear Hd.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hu; [| cond_cleanup Hu; exfalso; lia].
        cond_cleanup Hu.
        goto (eapply (IH (k + 1)%Z)); [lia | lia | apply digs_snoc; assumption].
  Qed.

  #[local] Ltac exitI DG := apply evt_done; do 9 eexists; split; [reflexivity|]; rewrite unsigned_lit by lia; split; [lia|].
  #[local] Ltac ub_ok := let Hu := fresh "Hu" in step; if_cases Hu; [| cond_cleanup Hu; exfalso; lia]; cond_cleanup Hu.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT HS SHT HY"] Lemma blockI : forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 : word),
      evt BSEGS int_post
        (MS (mkR x1 x2 x3 x4 t0 x6 x7 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                 x18 (Z_to_bv 64 ASAN_B) x20 (Z_to_bv 64 S) (Z_to_bv 64 (T + L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x92fb8) fc None m (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT HS SHT HY : LiaFast.U) => LiaFast.u0).
    intros a0 a1 a2 a3 a4 a5 a6 a7 t0.
    pose proof (shz_bound _ _ _ _ SHT) as BT.
    pose proof (digs_nil bs (S - T)) as DG0.
    step. (* [comment removed for export] *)
    if_cases Hend.
    { cond_cleanup Hend.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      exitI DG0. exact DG0. }
    cond_cleanup Hend.
    pose proof (tx_gran S ltac:(lia)) as G0.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (S - T)%Z RD. pose proof (tx_range bs (S - T)) as R0.
    replace (T + (S - T))%Z with S in RD by lia.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs (S - T)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd0.
    { cond_cleanup Hd0. clear Hd0.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      exitI DG0. exact DG0. }
    cond_cleanup Hd0. pose proof (dig_yes _ R0 Hd0) as D0. clear Hd0.
    pose proof (digs_snoc _ _ _ DG0 D0) as DG1.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    ub_ok. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He1.
    { cond_cleanup He1. exitI DG1. replace (S + 1 - T)%Z with (S - T + 1)%Z by lia. exact DG1. }
    cond_cleanup He1.
    pose proof (tx_gran (S + 1) ltac:(lia)) as G1.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (S - T + 1)%Z RD. pose proof (tx_range bs (S - T + 1)) as R1.
    replace (T + (S - T + 1))%Z with (S + 1)%Z in RD by lia.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs (S - T + 1)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd1.
    { cond_cleanup Hd1. clear Hd1. exitI DG1. replace (S + 1 - T)%Z with (S - T + 1)%Z by lia. exact DG1. }
    cond_cleanup Hd1. pose proof (dig_yes _ R1 Hd1) as D1. clear Hd1.
    pose proof (digs_snoc _ _ _ DG1 D1) as DG2. replace (S - T + 1 + 1)%Z with (S - T + 2)%Z in DG2 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    ub_ok. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He2.
    { cond_cleanup He2. exitI DG2. replace (S + 2 - T)%Z with (S - T + 2)%Z by lia. exact DG2. }
    cond_cleanup He2.
    pose proof (tx_gran (S + 2) ltac:(lia)) as G2.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (S - T + 2)%Z RD. pose proof (tx_range bs (S - T + 2)) as R2.
    replace (T + (S - T + 2))%Z with (S + 2)%Z in RD by lia.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs (S - T + 2)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd2.
    { cond_cleanup Hd2. clear Hd2. exitI DG2. replace (S + 2 - T)%Z with (S - T + 2)%Z by lia. exact DG2. }
    cond_cleanup Hd2. pose proof (dig_yes _ R2 Hd2) as D2. clear Hd2.
    pose proof (digs_snoc _ _ _ DG2 D2) as DG3. replace (S - T + 2 + 1)%Z with (S - T + 3)%Z in DG3 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    ub_ok. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He3.
    { cond_cleanup He3. exitI DG3. replace (S + 3 - T)%Z with (S - T + 3)%Z by lia. exact DG3. }
    cond_cleanup He3.
    pose proof (tx_gran (S + 3) ltac:(lia)) as G3.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (S - T + 3)%Z RD. pose proof (tx_range bs (S - T + 3)) as R3.
    replace (T + (S - T + 3))%Z with (S + 3)%Z in RD by lia.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs (S - T + 3)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd3.
    { cond_cleanup Hd3. clear Hd3. exitI DG3. replace (S + 3 - T)%Z with (S - T + 3)%Z by lia. exact DG3. }
    cond_cleanup Hd3. pose proof (dig_yes _ R3 Hd3) as D3. clear Hd3.
    pose proof (digs_snoc _ _ _ DG3 D3) as DG4. replace (S - T + 3 + 1)%Z with (S - T + 4)%Z in DG4 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    ub_ok. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He4.
    { cond_cleanup He4. exitI DG4. replace (S + 4 - T)%Z with (S - T + 4)%Z by lia. exact DG4. }
    cond_cleanup He4.
    pose proof (tx_gran (S + 4) ltac:(lia)) as G4.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (S - T + 4)%Z RD. pose proof (tx_range bs (S - T + 4)) as R4.
    replace (T + (S - T + 4))%Z with (S + 4)%Z in RD by lia.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs (S - T + 4)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd4.
    { cond_cleanup Hd4. clear Hd4. exitI DG4. replace (S + 4 - T)%Z with (S - T + 4)%Z by lia. exact DG4. }
    cond_cleanup Hd4. pose proof (dig_yes _ R4 Hd4) as D4. clear Hd4.
    pose proof (digs_snoc _ _ _ DG4 D4) as DG5. replace (S - T + 4 + 1)%Z with (S - T + 5)%Z in DG5 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    ub_ok. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    goto (eapply (loopI (Datatypes.S (Z.to_nat (L - (S - T + 5)))) (S - T + 5)%Z)); [lia | lia | exact DG5].
  Qed.
End INT.
End HxIntBW.

Import OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxSemB OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxIntB.HxIntBW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition TXT_T : lin := lvar 1.  Definition TXT_L : lin := lvar 2.
Definition TXT_Y0 : lin := lvar 7. Definition TXT_Y1 : lin := lvar 8.
Definition TXT_TL : lin := ladd TXT_T TXT_L.
Definition SHBz : Z := 2147450880.

Definition rg_is (R : region) (b s : lin) (k : rkind) : bool :=
  (lin_eqb (rg_base R) b && lin_eqb (rg_size R) s && rkind_eqb (rg_kind R) k && match rg_cont R with TEmpty => true | _ => false end)%bool.
(* [comment removed for export] *)
Definition txt_rgs_ok (L : sst) : bool :=
  match s_rgs L with
  | R0 :: R1 :: _ => (rg_is R0 TXT_T TXT_L RT && rg_is R1 (ladd TXT_Y0 (lconst SHBz)) (lsub TXT_Y1 TXT_Y0) RZ)%bool
  | _ => false
  end.
(* [comment removed for export] *)
Definition txt_facts : list fact :=
  [FRange TXT_L 1 128; FRange TXT_T 6537216 140737488355072; FRange TXT_Y0 800288 17592186044416; FRange TXT_Y1 800288 17592186044416;
   FRange (lsub TXT_T (lscale 8 TXT_Y0)) 0 256; FRange (lsub (lscale 8 TXT_Y1) TXT_TL) 0 256].

Definition INT_KEYS : list Z := [10; 11; 12; 13; 14; 15; 16; 17; 5].
Definition int_S (L : sst) : lin := rget (s_regs L) (rkz 21).
Definition int_chk (L : sst) : bool :=
  match s_resv L with
  | RNone => (txt_rgs_ok L && lin_eqb (rget (s_regs L) (rkz 22)) TXT_TL && lin_eqb (rget (s_regs L) (rkz 19)) (lconst SHBz)
              && forallb (fact_implied (s_facts L)) (txt_facts ++ [FRange (lsub (int_S L) TXT_T) 0 128; FRange (lsub TXT_TL (int_S L)) 0 128]))%bool
  | _ => false
  end.
Definition int_newf (L : sst) : list fact :=
  [FRange (lsub (lvar (s_next L)) (int_S L)) 0 128; FRange (lsub TXT_TL (lvar (s_next L))) 0 128].
Definition int_newx (L : sst) : list xfact := [XF 0 [int_S L; lvar (s_next L)]].
Definition H_INT : xst -> option (list xst) := hx_reg 0x92fb8 0x931dc INT_KEYS int_chk int_newf int_newx.

(* [comment removed for export] *)
Section Open.
Variable E : valu.
Variable ms : machine_state.
Variable L : sst.
Hypothesis Hd : sden BSEGS E L ms.
Hypothesis Hrg : txt_rgs_ok L = true.
Hypothesis Hfx : forallb (fact_implied (s_facts L)) txt_facts = true.

Local Abbreviation Tz := (bv_unsigned (E 1%positive)).
Local Abbreviation Lz := (bv_unsigned (E 2%positive)).
Local Abbreviation Y0z := (bv_unsigned (E 7%positive)).
Local Abbreviation Y1z := (bv_unsigned (E 8%positive)).

#[using="Type"] Lemma Bnd : forall x : positive, 0 <= bv_unsigned (E x) < two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. pose proof (bv_unsigned_in_range _ (E x)) as X. unfold bv_modulus in X. exact X. Qed.

#[using="Type"] Lemma u_sub : forall a b, bv_unsigned (lden E (lsub a b)) = (bv_unsigned (lden E a) - bv_unsigned (lden E b)) mod two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros a b. rewrite lden_lsub, bv_sub_unsigned. reflexivity. Qed.
#[using="Type"] Lemma u_add : forall a b, bv_unsigned (lden E (ladd a b)) = (bv_unsigned (lden E a) + bv_unsigned (lden E b)) mod two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros a b. rewrite lden_ladd, bv_add_unsigned. reflexivity. Qed.
#[using="Type"] Lemma u_scale : forall k a, bv_unsigned (lden E (lscale k a)) = (k * bv_unsigned (lden E a)) mod two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros k a. rewrite lden_lscale, u_Z_to_bv. reflexivity. Qed.

#[using="ms L Hd Hfx"] Lemma txt_bounds : 1 <= Lz <= 128 /\ 6537216 <= Tz <= 140737488355072 /\ 800288 <= Y0z <= 17592186044416 /\ 800288 <= Y1z <= 17592186044416 /\
  8 * Y0z <= Tz /\ Tz + Lz <= 8 * Y1z.
Proof. LiaFast.lf_pins (fun (ms L Hd Hfx : LiaFast.U) => LiaFast.u0).
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & HF & _).
  unfold txt_facts in Hfx. cbn [forallb] in Hfx.
  repeat match type of Hfx with (?a && ?b)%bool = true => apply andb_prop in Hfx as [?F Hfx] end.
  pose proof (fact_implied_ok E _ _ HF F) as X1. pose proof (fact_implied_ok E _ _ HF F0) as X2.
  pose proof (fact_implied_ok E _ _ HF F1) as X3. pose proof (fact_implied_ok E _ _ HF F2) as X4.
  pose proof (fact_implied_ok E _ _ HF F3) as X5. pose proof (fact_implied_ok E _ _ HF F4) as X6.
  cbn [fact_ok] in X1, X2, X3, X4, X5, X6. unfold TXT_TL, TXT_T, TXT_L, TXT_Y0, TXT_Y1 in *.
  rewrite !lden_lvar in X1, X2, X3, X4. rewrite u_sub, u_scale, !lden_lvar in X5. rewrite u_sub, u_scale, u_add, !lden_lvar in X6.
  pose proof (Bnd 1%positive). pose proof (Bnd 2%positive). pose proof (Bnd 7%positive). pose proof (Bnd 8%positive).
  assert (M1 : (8 * Y0z) mod two64 = 8 * Y0z) by (apply Z.mod_small; unfold two64 in *; lia).
  assert (M2 : (8 * Y1z) mod two64 = 8 * Y1z) by (apply Z.mod_small; unfold two64 in *; lia).
  assert (M3 : (Tz + Lz) mod two64 = Tz + Lz) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite M1 in X5. rewrite M2, M3 in X6. unfold two64 in *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
#[using="L Hd Hrg Hfx"] Lemma txt_bytes : exists bs, bytes_at BSEGS (ms_mem ms) Tz bs /\ Z.of_nat (length bs) = Lz.
Proof. LiaFast.lf_pins (fun (L Hd Hrg Hfx : LiaFast.U) => LiaFast.u0).
  pose proof txt_bounds as (B1 & B2 & _).
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & HG & _ & _ & _).
  unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1 rs]] eqn:Hr; try discriminate.
  apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0.
  apply andb_prop in H0 as [H0 Hc0]. apply andb_prop in H0 as [H0 Hk0]. apply andb_prop in H0 as [H0 X].
  apply lin_eqb_eq in H0. apply lin_eqb_eq in X. destruct (rg_kind R0) eqn:Hk; cbn in Hk0; try discriminate.
  apply Forall_cons_iff in HG as [G0 _].
  destruct (bytes_exist BSEGS (ms_mem ms) Tz (Z.to_nat Lz) ltac:(lia) ltac:(pose proof (Bnd 1%positive); lia)) as (bs & Hbs & Hl).
  { intros i Hi. pose proof (rd_of_rg BSEGS E (ms_mem ms) R0 (Z.of_nat i) G0) as Y.
    unfold rsz in Y. rewrite H0, X in Y. unfold TXT_T, TXT_L in Y. rewrite !lden_lvar in Y. apply Y; [lia|]. rewrite Hk. discriminate. }
  exists bs. split; [exact Hbs | lia].
Qed.

(* [comment removed for export] *)
#[using="L Hd Hrg Hfx"] Lemma txt_shadow : shz BSEGS (ms_mem ms) (ASAN_B + Y0z) (Y1z - Y0z).
Proof. LiaFast.lf_pins (fun (L Hd Hrg Hfx : LiaFast.U) => LiaFast.u0).
  pose proof txt_bounds as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & HG & _ & _ & _).
  unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1 rs]] eqn:Hr; try discriminate.
  apply andb_prop in Hrg as [_ H1]. unfold rg_is in H1.
  apply andb_prop in H1 as [H1 Hc1]. apply andb_prop in H1 as [H1 Hk1]. apply andb_prop in H1 as [H1 X].
  apply lin_eqb_eq in H1. apply lin_eqb_eq in X. destruct (rg_kind R1) eqn:Hk; cbn in Hk1; try discriminate.
  destruct (rg_cont R1) eqn:Hc; [|discriminate].
  apply Forall_cons_iff in HG as [_ HG]. apply Forall_cons_iff in HG as [G1 _].
  split; [lia|].
  apply (zeros_bytes_of_rz BSEGS E (ms_mem ms) R1 (ASAN_B + Y0z) (Z.to_nat (Y1z - Y0z)) G1 Hk Hc).
  - rewrite H1. unfold TXT_Y0. rewrite u_add, lden_lvar, lden_lconst, u_Z_to_bv. unfold SHBz, two64. rewrite (Z.mod_small 2147450880) by lia.
    rewrite Z.mod_small by lia. lia.
  - unfold rsz. rewrite X. unfold TXT_Y0, TXT_Y1. rewrite u_sub, !lden_lvar. unfold two64. rewrite Z.mod_small by lia. lia.
Qed.
End Open.

(* [comment removed for export] *)
Lemma txt_frame : forall E (L : sst) (ms : machine_state) (m0 : word -> option byte) R0 rs i,
  s_rgs L = R0 :: rs -> rg_base R0 = TXT_T -> rg_size R0 = TXT_L -> rg_kind R0 = RT ->
  (forall x, fr_pt E (s_rgs L) x -> ms_mem ms x = m0 x) ->
  0 <= i < bv_unsigned (E 2%positive) -> bv_unsigned (E 1%positive) + bv_unsigned (E 2%positive) < two64 ->
  ms_mem ms (wa (bv_unsigned (E 1%positive) + i)) = m0 (wa (bv_unsigned (E 1%positive) + i)).
Proof.
  intros E L ms m0 R0 rs i Hr Hb Hs Hk Hm0 Hi Hn. apply Hm0. right. rewrite Hr. apply Exists_cons_hd. split; [rewrite Hk; reflexivity|].
  unfold FxStep.in_rg, rsz. rewrite Hb, Hs. unfold TXT_T, TXT_L. rewrite !lden_lvar. rewrite wa_unsigned by (pose proof (bv_unsigned_in_range _ (E 1%positive)); unfold two64 in *; lia).
  lia.
Qed.

Theorem int_kit : hx_kit_fp BSEGS xok_spd 0x92fb8 0x931dc INT_KEYS int_chk int_newf int_newx.
Proof.
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold int_chk in Hchk. destruct (s_resv L) eqn:Hrv; try discriminate.
  apply andb_prop in Hchk as [Hchk Hfx]. apply andb_prop in Hchk as [Hchk H25]. apply andb_prop in Hchk as [Hrg H23].
  apply lin_eqb_eq in H23, H25.
  rewrite forallb_app in Hfx. apply andb_prop in Hfx as [Hfx HfS].
  pose proof (txt_bounds E ms L Hd Hfx) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (txt_bytes E ms L Hd Hrg Hfx) as (bs & TXT & Hlen).
  pose proof (txt_shadow E ms L Hd Hrg Hfx) as SHT.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  set (S := int_S L) in *. set (Sz := bv_unsigned (lden E S)).
  set (Tz := bv_unsigned (E 1%positive)) in *. set (Lz := bv_unsigned (E 2%positive)) in *.
  set (Y0z := bv_unsigned (E 7%positive)) in *. set (Y1z := bv_unsigned (E 8%positive)) in *.
  pose proof (bv_unsigned_in_range _ (lden E S)) as BS. unfold bv_modulus in BS. change (2 ^ Z.of_N 64) with two64 in BS.
  cbn [forallb] in HfS. apply andb_prop in HfS as [F1 HfS]. apply andb_prop in HfS as [F2 _].
  pose proof (fact_implied_ok E _ _ HF F1) as X1. pose proof (fact_implied_ok E _ _ HF F2) as X2. cbn [fact_ok] in X1, X2.
  rewrite (u_sub E) in X1, X2. unfold TXT_TL, TXT_T, TXT_L in X1, X2. rewrite (u_add E) in X2.
  rewrite !lden_lvar in X1. rewrite !lden_lvar in X2.
  fold Sz Tz Lz in X1, X2.
  assert (M3 : (Tz + Lz) mod two64 = Tz + Lz) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite M3 in X2.
  assert (HS : Tz <= Sz <= Tz + Lz) by (unfold two64 in *; split; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (R21 : getr (ms_regs ms) 21%bv = Z_to_bv 64 Sz).
  { rewrite (HR 21%bv). change (rkey 21%bv) with (rkz 21). fold S. unfold Sz. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R22 : getr (ms_regs ms) 22%bv = Z_to_bv 64 (Tz + Lz)).
  { rewrite (HR 22%bv). change (rkey 22%bv) with (rkz 22). rewrite H23. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, !lden_lvar.
    apply bv_eq. rewrite bv_add_unsigned, u_Z_to_bv. reflexivity. }
  assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 ASAN_B).
  { rewrite (HR 19%bv). change (rkey 19%bv) with (rkz 19). rewrite H25. rewrite lden_lconst. reflexivity. }
  set (R := ms_regs ms) in *.
  assert (HK : evt BSEGS (int_post (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 6) (getr R 7) (getr R 8) (getr R 9)
                 (getr R 18) (getr R 20) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28)
                 (getr R 29) (getr R 30) (getr R 31) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) bs Tz Sz)
             (kms BSEGS ms)).
  { unfold kms, mkR_of. fold R. rewrite Hpc0, Hresv0, R21, R22, R19, Hpc. rewrite <- Hlen.
    apply (blockI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs Tz Sz Y0z Y1z TXT); [lia | lia | lia | exact SHT | split; lia]. }
  destruct (kit_run BSEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t0 & Hms2 & HIE & HDG). subst ms2.
  destruct Heq as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
  exists ms1, [a0; a1; a2; a3; a4; a5; a6; a7; t0].
  split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
  split; [exact E4|]. split; [exact E3|].
  split; [|split; [|split; [|split]]].
  - (* [comment removed for export] *)
    intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
    unfold INT_KEYS in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
    do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact R21) | (symmetry; exact R22) | (rewrite Hlen; symmetry; exact R22)
                                            | (symmetry; exact R19) | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
    lia.
  - (* [comment removed for export] *)
    intros i k v Hi Hv. rewrite (E1 _).
    destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]]; cbn in Hi, Hv;
      first [ (injection Hi as <-; injection Hv as <-; reflexivity) | (destruct i; discriminate) ].
  - (* [comment removed for export] *)
    set (E' := E_of INT_KEYS [a0; a1; a2; a3; a4; a5; a6; a7; t0] (s_next L) E).
    assert (Ha0 : E' (s_next L) = a0).
    { pose proof (E_of_nth INT_KEYS [a0; a1; a2; a3; a4; a5; a6; a7; t0] (s_next L) E 0 a0 eq_refl eq_refl) as X.
      rewrite Nat.add_0_r, Pos2Nat.id in X. exact X. }
    assert (Hag : agree (s_next L) E E') by apply E_of_agree.
    unfold state_wf in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hwr Hwg].
    assert (HwS : lwf (s_next L) S = true) by (exact (regs_wf_n_spec _ _ 31 Hwr 21%nat ltac:(lia))).
    assert (Hv12 : (1 < s_next L)%positive /\ (2 < s_next L)%positive).
    { unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1 rs]] eqn:Hr; try discriminate.
      apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 _].
      apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. cbn [forallb] in Hwg. apply andb_prop in Hwg as [Hw0 _].
      unfold rwf in Hw0. apply andb_prop in Hw0 as [Hw0 _]. apply andb_prop in Hw0 as [Hw0a Hw0b]. rewrite Hb0 in Hw0a. rewrite Hs0 in Hw0b.
      unfold lwf, TXT_T, TXT_L, lvar in Hw0a, Hw0b. cbn in Hw0a, Hw0b. apply andb_prop in Hw0a as [Hw0a _]. apply andb_prop in Hw0b as [Hw0b _].
      apply Pos.ltb_lt in Hw0a, Hw0b. split; assumption. }
    assert (E1' : E' 1%positive = E 1%positive) by (unfold E'; apply E_of_old; lia).
    assert (E2' : E' 2%positive = E 2%positive) by (unfold E'; apply E_of_old; lia).
    assert (ES : lden E' S = lden E S) by (symmetry; exact (lden_agree _ E E' S HwS Hag)).
    unfold int_newf. fold S. constructor; [|constructor; [|constructor]]; cbn [fact_ok].
    + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Ha0, ES. fold Sz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Z.mod_small by (unfold two64 in *; lia). lia.
    + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Ha0. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, bv_add_unsigned, !lden_lvar, E1', E2'.
      fold Tz Lz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite (Z.mod_small (Tz + Lz)) by (unfold two64 in *; lia).
      rewrite Z.mod_small by (unfold two64 in *; lia). lia.
  - (* [comment removed for export] *)
    set (E' := E_of INT_KEYS [a0; a1; a2; a3; a4; a5; a6; a7; t0] (s_next L) E).
    assert (Ha0 : E' (s_next L) = a0).
    { pose proof (E_of_nth INT_KEYS [a0; a1; a2; a3; a4; a5; a6; a7; t0] (s_next L) E 0 a0 eq_refl eq_refl) as X.
      rewrite Nat.add_0_r, Pos2Nat.id in X. exact X. }
    assert (Hag : agree (s_next L) E E') by apply E_of_agree.
    unfold state_wf in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hwr _].
    assert (HwS : lwf (s_next L) S = true) by (exact (regs_wf_n_spec _ _ 31 Hwr 21%nat ltac:(lia))).
    assert (ES : lden E' S = lden E S) by (symmetry; exact (lden_agree _ E E' S HwS Hag)).
    unfold int_newx. fold S. constructor; [|constructor]. unfold xfact_ok. cbn [xf_tag xf_args List.map xok_spd].
    rewrite ES, lden_lvar, Ha0. fold Sz.
    exists Tz, bs. split; [|split; [lia|split; [lia | exact HDG]]].
    apply (bytes_at_transport (ms_mem ms)); [exact TXT|]. intros i Hi.
    unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1 rs]] eqn:Hr; try discriminate.
    apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 Hk0].
    apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. destruct (rg_kind R0) eqn:Hk; cbn in Hk0; try discriminate.
    rewrite <- Hr in Hm0. exact (txt_frame E L ms m0 R0 (R1 :: rs) i Hr Hb0 Hs0 Hk Hm0 ltac:(lia) ltac:(unfold two64 in *; lia)).
  - (* [comment removed for export] *)
    exact E2.
Qed.

Theorem H_INT_ok : hand_okx_fp BSEGS xok_spd H_INT.
Proof. apply hx_ok_fp. exact int_kit. Qed.
