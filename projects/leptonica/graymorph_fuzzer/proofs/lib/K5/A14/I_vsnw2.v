(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import SysStep.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import I_pck I_pcrr I_pcbits I_pcseg I_pchead I_pcfmt I_pcmsg2 I_vprintfw I_vsnw.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
(* [comment removed for export] *)
Local Ltac zidle_nspz H A SP := lazymatch A with context [SP] => fail | _ => zidle1 H end.
Local Ltac zidle_beginz SP n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(SP - n, SP)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : ro_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u8arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u32arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u64arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : bytes_at segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u8ro segs m ?A _ |- _ => zidle_nspz H A SP
    end
  end.

(* [comment removed for export] *)
Notation IVSNW_DEPTH := 4480 (only parsing).

(* [comment removed for export] *)
Definition vsncells (m : mem) : Prop := ro_cells asegs m 0xe3dd8 [C8 (Z_to_bv 64 0xd7cb0)].

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Definition ivsnA_post (usp D n A VA : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j8 junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x5419c) (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 A)
                  (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 VA) a4 a5 a6 a7 (Z_to_bv 64 D) (Z_to_bv 64 n)
                  (Z_to_bv 64 0x17f328) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xd7cb0) fc None m' (seg_rom asegs)
    /\ munch [(usp - IVSNW_DEPTH, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -2160)
    /\ rw_cells asegs m' (usp + -96) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2;
                                      C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (usp + -2160) [CB 2064 junk].

Lemma ivsn_walkA : forall (usp D n A VA S1 S2 lo : Z) (str1 str2 : list byte)
    ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - IVSNW_DEPTH -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
  0 <= D < 2^64 -> 0 <= n < 2^64 ->
  cstr_at m A (zb8 (FMA [])) -> A + 11 <= lo -> chk_ok m A 11 ->
  ro_cells asegs m VA [C8 (Z_to_bv 64 S1)] -> ro_cells asegs m (VA + 16) [C8 (Z_to_bv 64 S2)] -> usp <= VA -> VA + 24 < 2^63 ->
  cstr_at m S1 str1 -> 0 < S1 -> S1 + Z.of_nat (length str1) + 1 <= lo -> chk_ok m S1 (Z.of_nat (length str1) + 1) ->
  cstr_at m S2 str2 -> 0 < S2 -> S2 + Z.of_nat (length str2) + 1 <= lo -> chk_ok m S2 (Z.of_nat (length str2) + 1) ->
  pctx m -> pfcells m -> vsncells m -> mem_inv asegs m ->
  evt asegs (ivsnA_post usp D n A VA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 VA) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x509a4) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH S16 D0 N0 CSA ABL CHKA SL1 SL3 QVA VAH CS1 S10 SB1 CHK1 CS2 S20 SB2 CHK2 PCX PFC VSN MI.
  unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(usp - IVSNW_DEPTH, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  pose proof (cstr_bound _ _ _ CS1) as (_ & B1). pose proof (cstr_bound _ _ _ CS2) as (_ & B2). pose proof (cstr_bound _ _ _ CSA) as (A0 & _).
  destruct PFC as (AI & GCF & CPF & RVP & RVF). unfold vsncells in VSN.
  carve_frame 96%nat ST. rename FR into FRt.
  carve_frame 2064%nat ST. rename FR into FRb.
  apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRt; [| reflexivity].
  cbn [mk_CB_cells app] in FRt.
  zidle_beginz usp 2160%Z MUz1 WMz1.
  zhide.
  xsteps_to 0x69360%Z.
  zidle_end MUz1 WMz1.
  call try_init_spec; [exact AI | rewrite EU2160; exact ST | rewrite EU2160; lia | lia | assumption |].
  xsteps_to 0x5358c%Z.
  rename POST into ST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CSA1 : cstr_at mm A (zb8 (FMA []))) by
      (apply (cstr_agree m mm _ _ CSA); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside];
       rewrite ?length_zb8 in Hx; cbn [FMA MSG_PRE app length] in Hx; lia);
    assert (CHKA1 : chk_ok mm A 11) by
      (eapply chk_ok_agree; [exact CHKA | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
    assert (CS1' : cstr_at mm S1 str1) by
      (apply (cstr_agree m mm _ _ CS1); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; lia);
    assert (CS2' : cstr_at mm S2 str2) by
      (apply (cstr_agree m mm _ _ CS2); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; lia);
    assert (CHK1' : chk_ok mm S1 (Z.of_nat (length str1) + 1)) by
      (eapply chk_ok_agree; [exact CHK1 | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
    assert (CHK2' : chk_ok mm S2 (Z.of_nat (length str2) + 1)) by
      (eapply chk_ok_agree; [exact CHK2 | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
    assert (PCX1 : pctx mm) by
      (apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]) end.
  call (pcom_msgA_spec RIP A [] VA S1 S2 str1 str2 lo);
    [ reflexivity | reflexivity | reflexivity | exact CSA1 | cbn [length Z.of_nat]; lia | exact SL1 | exact SL3 | rewrite EU2160; lia | lia
    | exact CS1' | exact S10 | left; lia | lia | exact CHK1' | exact CS2' | exact S20 | left; lia | lia | exact CHK2'
    | exact ST | rewrite EU2160; lia | (unfold kHighShadowEnd; lia) | rewrite EU2160; lia
    | rewrite EU2160; Z.div_mod_to_equations; lia | cbn [length Z.of_nat]; exact CHKA1 | exact PCX1 | assumption | ].
  clear CSA1 CHKA1 CS1' CS2' CHK1' CHK2' PCX1. rename POST into ST. rewrite EU2160 in ST.
  xsteps_to 0xd7cb0%Z.
  apply evt_done. unfold ivsnA_post. do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FRt| exact FRb].
Qed.

(* [comment removed for export] *)
Lemma ivsn_walkC : forall (usp D n r lo : Z) (j8 junk : list byte)
    (ra' ra gp tp t0 t1 t2 s0 s1 s1' s2 s3 s4 s5 s6 s7 s4' s5' s6' s7' s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 VAw : word)
    F fc (m : mem),
  stk asegs m lo (usp + -2160) -> lo <= usp - 2240 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 ->
  rw_cells asegs m (usp + -96) [C8 VAw; C8 VAw; CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (usp + -2160) [CB 2064 junk] ->
  0 <= r -> r < n -> n < 2^31 -> 0 <= D -> D + r + 1 < 2^47 ->
  chk_ok m D (r + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(usp - 2240, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1' (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 D) (Z_to_bv 64 n) s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5419c) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH FRt FRb R0 RN NH D0 DH CHK M2S MI.
  unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(usp - 2240, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ESr : bv_signed (Z_to_bv 64 r) = r).
  { unfold bv_signed. rewrite EUr. apply bv_swrap_small. change (bv_half_modulus 64) with (2^63). lia. }
  zhide.
  lstep. if_false.
  lstep. lstep. lstep.
  rewrite (bv_swrap_small 32 (r + 1)) by (change (bv_half_modulus 32) with (2^31); lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (r + 1)) = r + 1) by (apply unsigned_lit; lia).
  if_true.
  lstep. lstep. rewrite (lxor_ones64 D) by lia.
  assert (EUnd : bv_unsigned (Z_to_bv 64 (18446744073709551615 - D)) = 18446744073709551615 - D) by (apply unsigned_lit; lia).
  lstep. lstep. lstep. if_true.
  eapply evt_cut.
  { apply (ivsn_chk RIP usp D n (r + 1) r); first [exact ST | exact CHK | exact M2S | exact MI | lia | (unfold kHighShadowEnd; lia)]. }
  cbv beta. intros ms' P. unfold ivsn_pre_epi in P.
  destruct P as (m1 & ra1 & u0 & u1 & u2 & u3 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & -> & MU1 & WM1 & MI1 & ST1).
  pose proof (rw_cells_transport asegs _ _ _ _ _ FRt MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRt1.
  pose proof (rw_cells_transport asegs _ _ _ _ _ FRb MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRb1.
  clear FRt FRb ST. rename ST1 into ST.
  assert (MU2 : munch [(usp - 2240, usp)] m m1)
    by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia).
  assert (WM2 : wmono asegs m m1) by exact (wmono_trans _ _ _ _ WM WM1).
  clear MU MU1 WM WM1. rename MU2 into MU. rename WM2 into WM.
  lstep.
  release_frame FRb1 ST (usp + -96).
  do 11 lstep.
  release_frame FRt1 ST usp.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.
End WithRIP.
