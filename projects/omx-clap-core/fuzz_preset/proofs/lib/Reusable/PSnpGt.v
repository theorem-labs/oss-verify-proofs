(* fm's snprintf glue, transport: the chain's premises (gl_pre, vsn_file, snk_base) after a step of a walk that changes
   only the band and the destination's first byte, ecall_preU from ARU, and the shadow facts of a stack range or a prefix
   of the destination. New file. *)
(* Modified by Theorem Labs, 2026-10: restated over the engine's generic ARx with the ghost list Hp fixed (route (a),
   c-omx-hpreset 10:51Z), from origin/cold/port-fm-rtprintf-param 7e395de08f5 proofs/omx-clap-core/fuzz_manifest/lib/A/
   FMsnprintfGt.v; image-free (segs, B, ARx are Section variables; no image numeral). Only the two items the four roots'
   closure reaches are kept: writable_xfer (:52-61, unchanged but over segs) and g_ecall_preU (:273-289), which becomes
   g_ecall_pre_x: ecall_pre_x (FCiface.v:42-48) is ARx plus the register facts, with no unpoison, so the ESTACK window
   argument of the U form (ush_facts, unpoison_out) is not needed. ac_bounds, rom_seg0, fmt_place, x_*, cstr_ok_x,
   frender_x, gl_pre_mk, gl_pre_xfer, vsn_file_xfer, snk_base_frame, band_addressable, dest_sub are not reached by
   snp_ok / svsni_ok / svsn_ok / svfi_ok and are not ported. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI00 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface.
Import ListNotations.
Open Scope Z_scope.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {segs : list Segment}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation H W := (w_H W).

(* a byte the world may hide stays writable when its presence is kept *)
Lemma writable_xfer : forall (Hd : word -> bool) (m m' : word -> option byte) a,
  writable_at segs (mrestrict Hd m) a -> (apresent Hd m a -> apresent Hd m' a) ->
  writable_at segs (mrestrict Hd m') a.
Proof.
intros Hd m m' a Hw Hp. unfold writable_at, wview, mrestrict in *.
destruct (Hd (Z_to_bv 64 a)) eqn:Eh; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj Eh (ex_intro _ b Em))) as [_ [b' Hb']]. rewrite Hb'. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* ecall_pre_x from ARx, the registers and the ESTACK window *)
Lemma g_ecall_pre_x : forall ly S Hp W regs mem md,
  ARx ly S Hp W mem md -> YK0s.ret_ok (getr regs 1) -> spZ regs mod 16 = 0 ->
  ly_stk_lo ly + ESTACK <= spZ regs -> spZ regs <= ly_stk_hi ly ->
  (forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (H W) mem a) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  ecall_pre_x segs B ARx ly S Hp W regs mem md.
Proof.
intros ly S Hp W regs mem md H1 H2 H3 H4 H5 H6 H7 H8.
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 H8))))))).
Qed.
End t.
