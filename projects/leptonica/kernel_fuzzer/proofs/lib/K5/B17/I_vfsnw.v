(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import SysStep.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import I_pck I_pcrr I_pcbits I_pcseg I_pchead I_pcfmt I_pcmsg2 I_vprintfw.
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
Notation IVFW_DEPTH := 2368 (only parsing).

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Definition ivfA_post (usp Fp A VA : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR (Z_to_bv 64 0x509dc) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 Fp)
                  (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 VA) a3 a4 a5 a6 a7 (Z_to_bv 64 VA) s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0xbd6e4) fc None m' (seg_rom asegs)
    /\ munch [(usp - IVFW_DEPTH, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -48)
    /\ rw_cells asegs m' (usp + -48) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); C8 s2; C8 s1; C8 s0; C8 ra].

Lemma ivfsn_walkA : forall (usp Fp A VA S1 S2 lo : Z) (str1 str2 : list byte)
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - IVFW_DEPTH -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 -> 0 <= Fp < 2^64 ->
  cstr_at m A (zb8 (FMA [])) -> A + 11 <= lo -> chk_ok m A 11 ->
  ro_cells asegs m VA [C8 (Z_to_bv 64 S1)] -> ro_cells asegs m (VA + 16) [C8 (Z_to_bv 64 S2)] -> usp <= VA -> VA + 24 < 2^63 ->
  cstr_at m S1 str1 -> 0 < S1 -> S1 + Z.of_nat (length str1) + 1 <= lo -> chk_ok m S1 (Z.of_nat (length str1) + 1) ->
  cstr_at m S2 str2 -> 0 < S2 -> S2 + Z.of_nat (length str2) + 1 <= lo -> chk_ok m S2 (Z.of_nat (length str2) + 1) ->
  pctx m -> pfcells m -> mem_inv asegs m ->
  evt asegs (ivfA_post usp Fp A VA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 VA) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4d2b8) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH S16 FP0 CSA ABL CHKA SL1 SL3 QVA VAH CS1 S10 SB1 CHK1 CS2 S20 SB2 CHK2 PCX PFC MI.
  unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(usp - IVFW_DEPTH, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  pose proof (cstr_bound _ _ _ CS1) as (_ & B1). pose proof (cstr_bound _ _ _ CS2) as (_ & B2). pose proof (cstr_bound _ _ _ CSA) as (A0 & _).
  destruct PFC as (AI & GCF & CPF & RVP & RVF).
  carve_frame 48%nat ST. rename FR into FRf.
  apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FRf; [| reflexivity]. cbn [mk_CB_cells app] in FRf.
  zhide.
  xsteps_to 0x65c78%Z.
  call try_init_spec; [exact AI | rewrite EU48; exact ST | rewrite EU48; lia | lia | assumption |].
  xsteps_to 0x4fea4%Z.
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
    [ reflexivity | reflexivity | reflexivity | exact CSA1 | cbn [length Z.of_nat]; lia | exact SL1 | exact SL3 | rewrite EU48; lia | lia
    | exact CS1' | exact S10 | left; lia | lia | exact CHK1' | exact CS2' | exact S20 | left; lia | lia | exact CHK2'
    | exact ST | rewrite EU48; lia | (unfold kHighShadowEnd; lia) | rewrite EU48; lia
    | rewrite EU48; Z.div_mod_to_equations; lia | cbn [length Z.of_nat]; exact CHKA1 | exact PCX1 | assumption | ].
  clear CSA1 CHKA1 CS1' CS2' CHK1' CHK2' PCX1. rename POST into ST. rewrite EU48 in ST.
  xsteps_to 0xbd6e4%Z.
  apply evt_done. unfold ivfA_post. do 13 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FRf.
Qed.
End WithRIP.

(* [comment removed for export] *)
Lemma ivfsn_walkB : forall (usp VA lo : Z)
    (ra' ra gp tp t0 t1 t2 s0 s1 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  stk asegs m lo (usp + -48) -> lo <= usp + -48 -> usp <= 2^47 ->
  rw_cells asegs m (usp + -48) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv asegs m ->
  evt asegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom asegs))
                 /\ stk asegs m lo usp)
    (MS (mkR ra' (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x509dc) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO UT FRf MI.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  zhide.
  do 6 lstep.
  release_frame FRf ST usp.
  apply evt_done. split; [| exact ST]. do 14 eexists. first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; lia].
Qed.
