(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_pcxchk.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 23 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_manifest.asan from proofs/omx-clap-core/fuzz_state/lib/A/Bz/A/I_pcxchk.v: module paths and 23 address numerals by the address relocator 7a60a01f65f446d8, each paired by object; the decided numerals are listed in the commit body. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import Shadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import I_pck I_pcbits I_pcseg I_pchead I_pcdint.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import I_pcrr I_pcdstr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import I_pcxa I_pcxdir.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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



Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Definition pck_post (q p ap' : Z) (gp tp s0 s2 s4 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra' (Z_to_bv 64 (q + -2240)) gp tp t0' t1' t2' s0 s1' a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 p) s4 (Z_to_bv 64 ap')
                  s6' (Z_to_bv 64 9) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x481f4) fc None m' (seg_rom asegs)
    /\ munch [(q + -2320, q + -2240)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (q + -2240)
    /\ (exists junk, rw_cells asegs m' (q + -2216) [CB 40 junk]).

Definition zws (ws : Z) : Z := if ws =? 0 then 0 else 8.

(* [comment removed for export] *)
Lemma pcx_ck_int_spec : forall (q p ap lo : Z) (fw : word) (bg en ws lm lm2 cv : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) -> s0 = Z_to_bv 64 q -> s3 = Z_to_bv 64 p -> s5 = Z_to_bv 64 ap -> s8 = Z_to_bv 64 (q + -2184) ->
  s10 = Z_to_bv 64 (-1) ->
  (ws = 0 \/ ws = 1) -> (lm = 0 \/ lm = 108 \/ lm = 122) -> pcx_iconv cv ->
  rw_cells asegs m (q + -2216) (DIRX2 fw bg en ws lm lm2 cv) ->
  stk asegs m lo (q + -2240) -> lo <= q + -2320 -> kHighShadowEnd < lo -> q <= 2^47 -> 0 <= ap -> ap + 16 < 2^63 ->
  mem_inv asegs m ->
  evt asegs (pck_post q p (ap + zws ws + 8) gp tp s0 s2 s4 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x483a4) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros -> -> -> -> -> -> WS LM CC DIR ST LO LOLO QHI AP0 APH MI. unfold DIRX2 in DIR.
  unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(q + -2320, q + -2240)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  assert (EUap : bv_unsigned (Z_to_bv 64 ap) = ap) by (apply unsigned_lit; lia).
  assert (LMB : bytes_at asegs m (q + -2182) [Z_to_bv 8 lm]) by (eapply (cells_byte _ _ _ 34%nat); [exact DIR | reflexivity | lia]).
  zhide.
  destruct WS as [-> | ->]; destruct LM as [-> | [-> | ->]]; destruct CC as [-> | [-> | [-> | [-> | ->]]]]; cbn [zws Z.eqb].
  all: xsteps_to 0x682c0%Z.
  all: strchr_call.
  (* [comment removed for export] *)
  all: try (xsteps_to 0x682c0%Z; strchr_call).
  all: xsteps_to 0x4b8a0%Z.
  all: lazymatch goal with H : bytes_at asegs _ (?qq + -2182) [Z_to_bv 8 ?l] |- _ => call (fgvs_spec2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l) end;
    [ reflexivity | reflexivity | reflexivity | (unfold pcx_iconv; lia) | lia
    | assumption | rewrite EUs; lia | rewrite EUs; exact ST | rewrite EUs; lia | rewrite EUs; lia | assumption | ].
  all: cbn [Z.eqb].
  all: xsteps_to 0x682c0%Z.
  all: strchr_call.
  all: xsteps_to 0x481f4%Z.
  all: rewrite EUs in POST.
  all: apply rw_forget in DIR; cbn [cells_size csize Nat.add] in DIR.
  all: lazymatch goal with |- evt _ (pck_post _ _ ?apv _ _ _ _ _ _ _ _ _ _ _ _ _) _ => setreg 21%Z (Z_to_bv 64 apv) ltac:(f_equal; lia) end.
  all: apply evt_done; unfold pck_post; do 19 eexists; split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact POST| eexists; exact DIR].
Qed.

(* [comment removed for export] *)
Local Ltac ck_head_cs :=
  xsteps_to 0x682c0%Z; strchr_call;                 (* [comment removed for export] *)
  xsteps_to 0x682c0%Z; strchr_call;                 (* [comment removed for export] *)
  xsteps_to 0x682c0%Z; strchr_call;                 (* [comment removed for export] *)
  xsteps_to 0x682c0%Z; strchr_call.                 (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma pcx_ck_char_spec : forall (q p ap lo : Z) (fw : word) (bg en ws : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) -> s0 = Z_to_bv 64 q -> s3 = Z_to_bv 64 p -> s5 = Z_to_bv 64 ap -> s8 = Z_to_bv 64 (q + -2184) ->
  s10 = Z_to_bv 64 (-1) ->
  (ws = 0 \/ ws = 1) ->
  rw_cells asegs m (q + -2216) (DIRX fw bg en ws 0 99) ->
  stk asegs m lo (q + -2240) -> lo <= q + -2320 -> kHighShadowEnd < lo -> q <= 2^47 -> 0 <= ap -> ap + 16 < 2^63 ->
  mem_inv asegs m ->
  evt asegs (pck_post q p (ap + zws ws + 8) gp tp s0 s2 s4 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x483a4) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros -> -> -> -> -> -> WS DIR ST LO LOLO QHI AP0 APH MI. unfold DIRX in DIR.
  unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(q + -2320, q + -2240)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  assert (EUap : bv_unsigned (Z_to_bv 64 ap) = ap) by (apply unsigned_lit; lia).
  zhide.
  destruct WS as [-> | ->]; cbn [zws Z.eqb].
  2: xsteps_to 0x682c0%Z; strchr_call.            (* [comment removed for export] *)
  all: ck_head_cs.
  all: xsteps_to 0x682c0%Z.
  all: strchr_call.                                  (* [comment removed for export] *)
  all: xsteps_to 0x481f4%Z.
  all: apply rw_forget in DIR; cbn [cells_size csize Nat.add] in DIR.
  all: lazymatch goal with |- evt _ (pck_post _ _ ?apv _ _ _ _ _ _ _ _ _ _ _ _ _) _ => setreg 21%Z (Z_to_bv 64 apv) ltac:(f_equal; lia) end.
  all: apply evt_done; unfold pck_post; do 19 eexists; split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST| eexists; exact DIR].
Qed.

(* [comment removed for export] *)
Lemma pcx_ck_null_spec : forall (q p ap lo : Z) (fw : word) (bg en ws : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) -> s0 = Z_to_bv 64 q -> s3 = Z_to_bv 64 p -> s5 = Z_to_bv 64 ap -> s8 = Z_to_bv 64 (q + -2184) ->
  s10 = Z_to_bv 64 (-1) ->
  (ws = 0 \/ ws = 1) ->
  rw_cells asegs m (q + -2216) (DIRX fw bg en ws 0 115) ->
  ro_cells asegs m (ap + zws ws) [C8 (Z_to_bv 64 0)] ->
  stk asegs m lo (q + -2240) -> lo <= q + -2320 -> kHighShadowEnd < lo -> q <= 2^47 -> 0 <= ap ->
  (ap + 8 * ws + 8 <= q + -2320 \/ q <= ap + 8 * ws) -> ap + 16 < 2^63 ->
  mem_inv asegs m ->
  evt asegs (pck_post q p (ap + zws ws + 8) gp tp s0 s2 s4 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x483a4) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros -> -> -> -> -> -> WS DIR SLOT ST LO LOLO QHI AP0 APQ APH MI. unfold DIRX in DIR.
  unfold kHighShadowEnd in LOLO. pose proof (proj1 ST) as LO0.
  pose proof (munch_refl [(q + -2320, q + -2240)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  assert (EUap : bv_unsigned (Z_to_bv 64 ap) = ap) by (apply unsigned_lit; lia).
  assert (EUap8 : bv_unsigned (Z_to_bv 64 (ap + 8)) = ap + 8) by (apply unsigned_lit; lia).
  zhide.
  destruct WS as [-> | ->]; cbn [zws Z.eqb] in SLOT |- *.
  2: xsteps_to 0x682c0%Z; strchr_call.
  all: ck_head_cs.
  all: try rewrite Z.add_0_r in SLOT.
  all: xsteps_to 0x481f4%Z.
  all: apply rw_forget in DIR; cbn [cells_size csize Nat.add] in DIR.
  all: lazymatch goal with |- evt _ (pck_post _ _ ?apv _ _ _ _ _ _ _ _ _ _ _ _ _) _ => setreg 21%Z (Z_to_bv 64 apv) ltac:(f_equal; lia) end.
  all: apply evt_done; unfold pck_post; do 19 eexists; split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST| eexists; exact DIR].
Qed.

(* [comment removed for export] *)
Lemma pcx_ck_str_spec : forall (q p ap lo S : Z) (str : list byte) (fw : word) (bg en ws : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) -> s0 = Z_to_bv 64 q -> s3 = Z_to_bv 64 p -> s5 = Z_to_bv 64 ap -> s8 = Z_to_bv 64 (q + -2184) ->
  s10 = Z_to_bv 64 (-1) ->
  (ws = 0 \/ ws = 1) ->
  rw_cells asegs m (q + -2216) (DIRX fw bg en ws 0 115) ->
  ro_cells asegs m (ap + zws ws) [C8 (Z_to_bv 64 S)] ->
  cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ q <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
  chk_ok m S (Z.of_nat (length str) + 1) -> pctx m ->
  stk asegs m lo (q + -2240) -> lo <= q + -2320 -> kHighShadowEnd < lo -> q <= 2^47 -> 0 <= ap ->
  (ap + 8 * ws + 8 <= q + -2320 \/ q <= ap + 8 * ws) -> ap + 16 < 2^63 ->
  mem_inv asegs m ->
  evt asegs (pck_post q p (ap + zws ws + 8) gp tp s0 s2 s4 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x483a4) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros -> -> -> -> -> -> WS DIR SLOT CS S0 SSEP SH CHK PCX ST LO LOLO QHI AP0 APQ APH MI. unfold DIRX in DIR.
  unfold kHighShadowEnd in LOLO. pose proof (proj1 ST) as LO0.
  pose proof (munch_refl [(q + -2320, q + -2240)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  assert (EUap : bv_unsigned (Z_to_bv 64 ap) = ap) by (apply unsigned_lit; lia).
  assert (EUap8 : bv_unsigned (Z_to_bv 64 (ap + 8)) = ap + 8) by (apply unsigned_lit; lia).
  assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  zhide.
  destruct WS as [-> | ->]; cbn [zws Z.eqb] in SLOT |- *.
  2: xsteps_to 0x682c0%Z; strchr_call.
  all: ck_head_cs.
  all: try rewrite Z.add_0_r in SLOT.
  all: xsteps_to 0x68360%Z.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         assert (CS1 : cstr_at mm S str) by
           (apply (cstr_agree m mm S str CS); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; lia) end.
  all: call internal_strlen_spec; [reflexivity| exact CS1| assumption|].
  all: xsteps_to 0x48618%Z.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         assert (CHK1 : chk_ok mm S (Z.of_nat (length str) + 1)) by
           (eapply chk_ok_agree; [exact CHK | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
         assert (PCX1 : pctx mm) by
           (apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]);
         destruct PCX1 as (M2S1 & PC1) end.
  all: call (pcs_check RIP (q + -2240) S (Z.of_nat (length str) + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try first [ exact ST | exact CHK1 | exact M2S1 | exact PC1 | assumption | lia ].
  all: xsteps_to 0x481f4%Z.
  all: lazymatch goal with H : stk asegs _ ?lo0 (bv_unsigned (Z_to_bv 64 (?qq + -2240))) |- _ => rewrite EUs in H; rename H into ST2 end.
  all: apply rw_forget in DIR; cbn [cells_size csize Nat.add] in DIR.
  all: lazymatch goal with |- evt _ (pck_post _ _ ?apv _ _ _ _ _ _ _ _ _ _ _ _ _) _ => setreg 21%Z (Z_to_bv 64 apv) ltac:(f_equal; lia) end.
  all: apply evt_done; unfold pck_post; do 19 eexists; split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST2| eexists; exact DIR].
Qed.
End WithRIP.
