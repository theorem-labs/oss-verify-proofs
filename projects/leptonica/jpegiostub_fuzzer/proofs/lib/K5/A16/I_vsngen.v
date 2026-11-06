(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import ImageA.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import SysStep.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import Layout.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import I_pck I_pcrr I_pcbits I_pcseg I_pchead I_pcfmt I_vprintfw I_vsnw I_vfsnw I_vsnw2 I_pcgen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

(* [comment removed for export] *)
Lemma pargs_weaken : forall ds m q q' lo ap, pargs m q lo ap ds -> q' <= q -> pargs m q' lo ap ds.
Proof.
  induction ds as [|[[d nx] t] r IH]; intros m q q' lo ap H Hq; [exact I|].
  cbn [pargs] in *. destruct H as [Hd Hr]. split; [| exact (IH m q q' lo (ap + 8) Hr Hq)].
  destruct d as [c|Sa str|]; [exact I| |exact I].
  destruct Hd as (SL & CS & S0 & SEP & SH & CHK).
  split; [exact SL|]. split; [exact CS|]. split; [exact S0|]. split; [lia|]. split; [exact SH | exact CHK].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Definition pfmt_ok (m : mem) (usp lo A VA : Z) (t0 : list Z) (ds : list pitem) : Prop :=
  txt_ok t0 = true /\ Forall pitem_ok ds /\ (1 <= length (t0 ++ ptail ds))%nat
  /\ cstr_at m A (zb8 (t0 ++ ptail ds)) /\ A + Z.of_nat (length t0) + Z.of_nat (length (ptail ds)) + 1 <= lo
  /\ chk_ok m A (Z.of_nat (length t0) + Z.of_nat (length (ptail ds)) + 1)
  /\ pargs m usp lo VA ds /\ usp <= VA /\ VA + 8 * Z.of_nat (length ds) < 2^63.

Lemma pfmt_ok_munch : forall W m m' usp lo A VA t0 ds, pfmt_ok m usp lo A VA t0 ds -> munch W m m' ->
  (forall x, (x < lo \/ usp <= x) -> outside W x) -> kHighShadowEnd + 8 <= lo -> lo <= usp -> usp <= 2^47 -> 0 <= A ->
  pfmt_ok m' usp lo A VA t0 ds.
Proof.
  intros W m m' usp lo A VA t0 ds (H1 & H2 & H3 & CS & AB & CHK & PA & QVA & VAH) MU HW LOLO LOU U47 A0.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [apply (cstr_agree m m' _ _ CS); apply (agree_of_munch _ _ _ _ MU); intros x Hx; apply HW;
          rewrite length_zb8, length_app in Hx; lia|].
  split; [exact AB|].
  split; [eapply chk_ok_agree; [exact CHK | lia | unfold kHighShadowEnd in LOLO; lia |];
          apply (agree_of_munch _ _ _ _ MU); intros x Hx; apply HW; unfold kHighShadowEnd in LOLO; lia|].
  split; [apply (pargs_munch ds W m m' usp lo VA PA MU HW); assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma ivfsn_walkA_gen : forall (usp Fp A VA lo : Z) (t0f : list Z) (ds : list pitem)
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - IVFW_DEPTH -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 -> 0 <= Fp < 2^64 ->
  pfmt_ok m usp lo A VA t0f ds ->
  pctx m -> pfcells m -> mem_inv asegs m ->
  evt asegs (ivfA_post usp Fp A VA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 VA) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4c970) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH S16 FP0 PF PCX PFC MI.
  pose proof LOLO as LOLO'. unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(usp - IVFW_DEPTH, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  pose proof PF as (_ & _ & _ & CSA & _). pose proof (cstr_bound _ _ _ CSA) as (A0 & _). clear CSA.
  assert (HW : forall x, x < lo \/ usp <= x -> outside [(usp - IVFW_DEPTH, usp)] x) by (intros x Hx; cbn [outside]; lia).
  destruct PFC as (AI & GCF & CPF & RVP & RVF).
  carve_frame 48%nat ST. rename FR into FRf.
  apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FRf; [| reflexivity]. cbn [mk_CB_cells app] in FRf.
  zhide.
  xsteps_to 0x65330%Z.
  call try_init_spec; [exact AI | rewrite EU48; exact ST | rewrite EU48; lia | lia | assumption |].
  xsteps_to 0x4f55c%Z.
  rename POST into ST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (PF1 : pfmt_ok mm usp lo A VA t0f ds) by (apply (pfmt_ok_munch _ m mm _ _ _ _ _ _ PF MU HW); first [assumption | lia]);
    assert (PCX1 : pctx mm) by
      (apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]) end.
  destruct PF1 as (OK0 & OKD & L1 & CSA1 & ABL & CHKA1 & PA1 & QVA & VAH).
  call (pcom_gen_spec RIP A t0f ds VA lo);
    [ reflexivity | reflexivity | exact OK0 | exact OKD | exact L1 | exact CSA1 | exact ABL
    | rewrite EU48; apply (pargs_weaken ds _ usp); [exact PA1 | lia] | rewrite EU48; lia | exact VAH
    | exact ST | rewrite EU48; lia | exact LOLO' | rewrite EU48; lia
    | rewrite EU48; Z.div_mod_to_equations; lia | exact CHKA1 | exact PCX1 | assumption | ].
  clear CSA1 CHKA1 PA1 PCX1. rename POST into ST. rewrite EU48 in ST.
  xsteps_to 0xbb3a8%Z.
  apply evt_done. unfold ivfA_post. do 13 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FRf.
Qed.

(* [comment removed for export] *)
Lemma ivsn_walkA_gen : forall (usp D n A VA lo : Z) (t0f : list Z) (ds : list pitem)
    ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - IVSNW_DEPTH -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
  0 <= D < 2^64 -> 0 <= n < 2^64 ->
  pfmt_ok m usp lo A VA t0f ds ->
  pctx m -> pfcells m -> vsncells m -> mem_inv asegs m ->
  evt asegs (ivsnA_post usp D n A VA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 VA) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4c974) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH S16 D0 N0 PF PCX PFC VSN MI.
  pose proof LOLO as LOLO'. unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(usp - IVSNW_DEPTH, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  pose proof PF as (_ & _ & _ & CSA & _). pose proof (cstr_bound _ _ _ CSA) as (A0 & _). clear CSA.
  assert (HW : forall x, x < lo \/ usp <= x -> outside [(usp - IVSNW_DEPTH, usp)] x) by (intros x Hx; cbn [outside]; lia).
  destruct PFC as (AI & GCF & CPF & RVP & RVF). unfold vsncells in VSN.
  carve_frame 96%nat ST. rename FR into FRt.
  carve_frame 2064%nat ST. rename FR into FRb.
  apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRt; [| reflexivity].
  cbn [mk_CB_cells app] in FRt.
  zidle_beginz usp 2160%Z MUz1 WMz1.
  zhide.
  xsteps_to 0x65330%Z.
  zidle_end MUz1 WMz1.
  call try_init_spec; [exact AI | rewrite EU2160; exact ST | rewrite EU2160; lia | lia | assumption |].
  xsteps_to 0x4f55c%Z.
  rename POST into ST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (PF1 : pfmt_ok mm usp lo A VA t0f ds) by (apply (pfmt_ok_munch _ m mm _ _ _ _ _ _ PF MU HW); first [assumption | lia]);
    assert (PCX1 : pctx mm) by
      (apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]) end.
  destruct PF1 as (OK0 & OKD & L1 & CSA1 & ABL & CHKA1 & PA1 & QVA & VAH).
  call (pcom_gen_spec RIP A t0f ds VA lo);
    [ reflexivity | reflexivity | exact OK0 | exact OKD | exact L1 | exact CSA1 | exact ABL
    | rewrite EU2160; apply (pargs_weaken ds _ usp); [exact PA1 | lia] | rewrite EU2160; lia | exact VAH
    | exact ST | rewrite EU2160; lia | exact LOLO' | rewrite EU2160; lia
    | rewrite EU2160; Z.div_mod_to_equations; lia | exact CHKA1 | exact PCX1 | assumption | ].
  clear CSA1 CHKA1 PA1 PCX1. rename POST into ST. rewrite EU2160 in ST.
  xsteps_to 0xbe4d4%Z.
  apply evt_done. unfold ivsnA_post. do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FRt| exact FRb].
Qed.

End WithRIP.
