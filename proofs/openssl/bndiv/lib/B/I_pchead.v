(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_m2s R_thread I_consts I_qck X_atexit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import D_kit I_pck I_pcrr I_pcbits I_pcseg.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require F_fwritex.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Notation PCOM_DEPTH := 2320%Z (only parsing).

(* [comment removed for export] *)
Definition pctx (m : mem) : Prop := m2s_cells m /\ pcells m.
Definition in_PCR (x : Z) : Prop := (0x5e0cd8 <= x < 0x5e0cf8) \/ (0x6a39f8 <= x < 0x6a3a00) \/ (0x6a46e0 <= x < 0x6a46f8).

Lemma pctx_munch : forall W m m', pctx m -> munch W m m' -> wmono bsegs m m' ->
  (forall x, in_PCR x -> outside W x) -> pctx m'.
Proof.
  intros W m m' ((X1 & X2 & X3) & (P1 & P2)) MU WM HW.
  pose proof (agree_of_munch W m m' _ MU HW) as AG.
  assert (RO : forall A cs, ro_cells bsegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> in_PCR x) ->
                 ro_cells bsegs m' A cs).
  { intros A cs H HX. apply (ro_cells_agree bsegs m m' _ _ H). apply (agree_sub _ _ _ _ AG). exact HX. }
  assert (RW : forall A cs, rw_cells bsegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> in_PCR x) ->
                 rw_cells bsegs m' A cs).
  { intros A cs H HX. apply (rw_cells_agree bsegs m m' _ _ H); [| exact WM].
    apply (agree_sub _ _ _ _ AG). exact HX. }
  split; [split; [| split] | split].
  all: first [ apply RO; [assumption| cbn [cells_size csize]; intros x Hx; unfold in_PCR; lia]
             | apply RW; [assumption| cbn [cells_size csize]; intros x Hx; unfold in_PCR; lia] ].
Qed.

Lemma cstr_agree : forall m m' A str, cstr_at m A str -> agree_on (fun x => A <= x < A + Z.of_nat (length str) + 1) m m' ->
  cstr_at m' A str.
Proof.
  intros m m' A str (BY & NZ) AG. split; [| exact NZ]. apply (bytes_at_agree bsegs m m' _ _ BY).
  apply (agree_sub _ _ _ _ AG). intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

(* [comment removed for export] *)
Definition pch_post (q A ap : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra' (Z_to_bv 64 (q + -2240)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 10) (Z_to_bv 64 A)
                  (Z_to_bv 64 133945) (Z_to_bv 64 ap) s6 (Z_to_bv 64 9) (Z_to_bv 64 (q + -2184)) (Z_to_bv 64 12297829382473034410)
                  (Z_to_bv 64 (-1)) (Z_to_bv 64 37) t3 t4 t5 t6)
             F (Z_to_bv 64 0x1abbfc) fc None m' (seg_rom bsegs)
    /\ munch [(q - PCOM_DEPTH, q)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (q + -2240)
    /\ rw_cells bsegs m' (q + -104) (pcom_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ (exists junk, rw_cells bsegs m' (q + -2176) [CB 2072 junk])
    /\ (exists junk, rw_cells bsegs m' (q + -2216) [CB 40 junk])
    /\ (exists junk, rw_cells bsegs m' (q + -2240) [CB 24 junk]).

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma pcom_head_spec : forall (q A ap : Z) (fmt : list byte) (lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 q -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap ->
  stk bsegs m lo q -> lo <= q - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> q <= 2^47 -> q mod 16 = 0 ->
  cstr_at m A fmt -> (1 <= length fmt)%nat -> A + Z.of_nat (length fmt) + 1 <= lo ->
  chk_ok m A (Z.of_nat (length fmt) + 1) -> pctx m -> mem_inv bsegs m ->
  evt bsegs (pch_post q A ap ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1abae8) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until m. intros -> -> -> ST LO LOLO SPH S16 CS L1 AB CHK PCX MI.
  pose proof (cstr_bound m A fmt CS) as (A0 & AB').
  unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(q - PCOM_DEPTH, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EUA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  carve_frame 104%nat ST. rename FR into FRh.
  carve_frame 2072%nat ST. rename FR into FRb.
  carve_frame 40%nat ST. rename FR into DIR.
  carve_frame 24%nat ST. rename FR into FRa.
  apply (rw_cells_split_CB bsegs _ _ [] 104 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRh; [| reflexivity].
  cbn [mk_CB_cells app] in FRh.
  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FRa; [| reflexivity]. cbn [mk_CB_cells app] in FRa.
  xsteps_to 0x1d02fc%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (CS1 : cstr_at mm A fmt) by
    (apply (cstr_agree m mm A fmt CS); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside] in *; lia) end.
  call internal_strlen_spec; [reflexivity| exact CS1| assumption|].
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CHK1 : chk_ok mm A (Z.of_nat (length fmt) + 1)) by
      (eapply chk_ok_agree; [exact CHK | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
    assert (PCX1 : pctx mm) by
      (apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]);
    destruct PCX1 as (M2S1 & PC1) end.
  call (pcf_check RIP (q + -2240) A (Z.of_nat (length fmt))).
  all: first [ exact ST | exact CHK1 | exact M2S1 | exact PC1 | assumption | lia | idtac ].
  destruct (cstr_byte _ A fmt 0 CS ltac:(lia)) as (b0 & Hb0 & Bnz0 & _). rewrite Z.add_0_r in Hb0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (Hb0' : bytes_at bsegs mm A [b0]) by
    (apply (bytes_at_agree bsegs m mm _ _ Hb0); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside length] in *; lia) end.
  pose proof (ro_C1_of_bytes _ _ _ Hb0') as CB0. clear Hb0 Hb0'.
  pose proof (z8_neq b0 Bnz0) as BNZ.
  xsteps_to 0x1abbfc%Z.
  replace (q - 4096) with (q + -4096) by lia.
  xsteps_to 0x1abbfc%Z.
  pose proof (bv_unsigned_in_range 8 b0) as BR0. unfold bv_modulus in BR0. change (2 ^ Z.of_N 8) with 256 in BR0.
  brF K0.
  xsteps_to 0x1abbfc%Z.
  replace (q - 4096) with (q + -4096) by lia.
  xsteps_to 0x1abbfc%Z.
  rewrite EUq in POST.
  apply rw_forget in FRa. cbn [cells_size csize Nat.add] in FRa.
  apply evt_done. unfold pch_post. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact POST|]. split; [exact FRh|].
  split; [eexists; exact FRb|]. split; [eexists; exact DIR| eexists; exact FRa].
Qed.
End WithRIP.
