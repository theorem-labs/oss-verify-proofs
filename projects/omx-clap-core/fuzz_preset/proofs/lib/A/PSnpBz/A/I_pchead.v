(* Modified by Theorem Labs, 2026-10: moved from image A (fuzz_preset.asan d83eb25d), commit 3244f5c71f6, to the #102 pin A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b): 14 address numerals by the frozen alreloc (sha256 c4338d099cfb8025, commit d99acc3edd9, same-unit move, --assume-source), each by symbol + offset in both images, or for a .rodata string by its unique content in both; GXA keys and history lines kept (report and decisions: the relocation record, the internal file resolve-A-why.tsv). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_manifest.asan from commit 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Bz/A/I_pchead.v: module paths and 14 address numerals by alreloc 7a60a01f65f446d8, each paired by object; the decided numerals are listed in the commit body. *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_preset.asan (image A, d83eb25d) from commit 7e395de08f5 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_pchead.v: module paths (lib/A/Bz -> lib/A/PSnpBz) and 11 address numerals by alreloc (sha256 c4338d099cfb8025, commit d99acc3edd97), each by symbol + offset in both images (per-numeral report: the relocation record, reloc-A). Hand-resolved (the relocation record, the internal file resolve-A.txt, each from the auipc/addi pair in the function that reads it and checked by its unique NUL-terminated bytes): 1. CROSS-CHECK TEMPLATE ONLY: commit 98f5f077ab2e lib/A/Bk/A/I_pchead.v:80 pcom_head_spec (Bk framework, rebuilt image A, entry 0x4560c) is not used: it has no %04x arm (its pcom_fint_spec covers [37; c] only, I_pcfmt.v:81 / :130), it is another framework with no bridge into sh_apcommon_realizes_xz, and that lane stopped on 10-28 19:27Z (the stdio lead, 13:0xZ). *)
(* [comment removed for export] *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A Require Import Shadow.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A Require Import R_small R_m2s R_thread I_consts I_qck X_atexit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A Require Import D_kit I_pck I_pcrr I_pcbits I_pcseg.
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
Definition in_PCR (x : Z) : Prop := (0xa2010 <= x < 0xa2030) \/ (0xaaeb8 <= x < 0xaaec0) \/ (0xabba0 <= x < 0xabbb8).

Lemma pctx_munch : forall W m m', pctx m -> munch W m m' -> wmono asegs m m' ->
  (forall x, in_PCR x -> outside W x) -> pctx m'.
Proof.
  intros W m m' ((X1 & X2 & X3) & (P1 & P2)) MU WM HW.
  pose proof (agree_of_munch W m m' _ MU HW) as AG.
  assert (RO : forall A cs, ro_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> in_PCR x) ->
                 ro_cells asegs m' A cs).
  { intros A cs H HX. apply (ro_cells_agree asegs m m' _ _ H). apply (agree_sub _ _ _ _ AG). exact HX. }
  assert (RW : forall A cs, rw_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> in_PCR x) ->
                 rw_cells asegs m' A cs).
  { intros A cs H HX. apply (rw_cells_agree asegs m m' _ _ H); [| exact WM].
    apply (agree_sub _ _ _ _ AG). exact HX. }
  split; [split; [| split] | split].
  all: first [ apply RO; [assumption| cbn [cells_size csize]; intros x Hx; unfold in_PCR; lia]
             | apply RW; [assumption| cbn [cells_size csize]; intros x Hx; unfold in_PCR; lia] ].
Qed.

Lemma cstr_agree : forall m m' A str, cstr_at m A str -> agree_on (fun x => A <= x < A + Z.of_nat (length str) + 1) m m' ->
  cstr_at m' A str.
Proof.
  intros m m' A str (BY & NZ) AG. split; [| exact NZ]. apply (bytes_at_agree asegs m m' _ _ BY).
  apply (agree_sub _ _ _ _ AG). intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

(* [comment removed for export] *)
Definition pch_post (q A ap : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra' (Z_to_bv 64 (q + -2240)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 10) (Z_to_bv 64 A)
                  (Z_to_bv 64 86784) (Z_to_bv 64 ap) s6 (Z_to_bv 64 9) (Z_to_bv 64 (q + -2184)) (Z_to_bv 64 12297829382473034410)
                  (Z_to_bv 64 (-1)) (Z_to_bv 64 37) t3 t4 t5 t6)
             F (Z_to_bv 64 0x457b4) fc None m' (seg_rom asegs)
    /\ munch [(q - PCOM_DEPTH, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q + -2240)
    /\ rw_cells asegs m' (q + -104) (pcom_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ (exists junk, rw_cells asegs m' (q + -2176) [CB 2072 junk])
    /\ (exists junk, rw_cells asegs m' (q + -2216) [CB 40 junk])
    /\ (exists junk, rw_cells asegs m' (q + -2240) [CB 24 junk]).

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma pcom_head_spec : forall (q A ap : Z) (fmt : list byte) (lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 q -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap ->
  stk asegs m lo q -> lo <= q - PCOM_DEPTH -> kHighShadowEnd < lo -> q <= 2^47 -> q mod 16 = 0 ->
  cstr_at m A fmt -> (1 <= length fmt)%nat -> A + Z.of_nat (length fmt) + 1 <= lo ->
  chk_ok m A (Z.of_nat (length fmt) + 1) -> pctx m -> mem_inv asegs m ->
  evt asegs (pch_post q A ap ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x456a0) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros -> -> -> ST LO LOLO SPH S16 CS L1 AB CHK PCX MI.
  pose proof (cstr_bound m A fmt CS) as (A0 & AB').
  unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(q - PCOM_DEPTH, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EUA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  carve_frame 104%nat ST. rename FR into FRh.
  carve_frame 2072%nat ST. rename FR into FRb.
  carve_frame 40%nat ST. rename FR into DIR.
  carve_frame 24%nat ST. rename FR into FRa.
  apply (rw_cells_split_CB asegs _ _ [] 104 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRh; [| reflexivity].
  cbn [mk_CB_cells app] in FRh.
  apply (rw_cells_split_CB asegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FRa; [| reflexivity]. cbn [mk_CB_cells app] in FRa.
  xsteps_to 0x64c0c%Z.
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
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (Hb0' : bytes_at asegs mm A [b0]) by
    (apply (bytes_at_agree asegs m mm _ _ Hb0); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside length] in *; lia) end.
  pose proof (ro_C1_of_bytes _ _ _ Hb0') as CB0. clear Hb0 Hb0'.
  pose proof (z8_neq b0 Bnz0) as BNZ.
  xsteps_to 0x457b4%Z.
  replace (q - 4096) with (q + -4096) by lia.
  xsteps_to 0x457b4%Z.
  pose proof (bv_unsigned_in_range 8 b0) as BR0. unfold bv_modulus in BR0. change (2 ^ Z.of_N 8) with 256 in BR0.
  brF K0.
  xsteps_to 0x457b4%Z.
  replace (q - 4096) with (q + -4096) by lia.
  xsteps_to 0x457b4%Z.
  rewrite EUq in POST.
  apply rw_forget in FRa. cbn [cells_size csize Nat.add] in FRa.
  apply evt_done. unfold pch_post. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact POST|]. split; [exact FRh|].
  split; [eexists; exact FRb|]. split; [eexists; exact DIR| eexists; exact FRa].
Qed.
End WithRIP.
