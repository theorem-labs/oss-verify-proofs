(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetGa0), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySetGa0.v, with its module paths and module names changed; 671 of its 703 lines of code are new or changed and 147 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxCase0Strn.v, with its module paths and module names changed; 36 of its 84 lines of code are new or changed and 655 lines of the source are left out. *)
(* The walk of LLVMFuzzerTestOneInput's case op & 3 = 0, declare (fuzz_boxreg.c:213-286), on the ASan build
   (fuzz_boxreg.asan 0x802ec .. 0x80ab4): the phase lemma gb_case0 of the walk (GI_T 0 i -> ... -> GI_K i, in the
   vocabulary of BoxLxDefs.v), composed from its pieces between the case's inner cuts (BoxLxCase0Defs.v):
     GI_T 0 --c0_inp (BoxLxCase0Inp.v: nch, base, read_name)--> C0_N
     C0_N --c0_want_ok (BoxLxCase0Want.v: the width tests, range_free / lowest_free)--> C0_W
     C0_W --c0_decl (BoxLxCase0Decl.v: reac_boxreg_declare)--> C0_D
     C0_D --c0_chk (BoxLxCase0Chk.v: idx and n; refused -> F, placed -> bcmp)--> C0_F | C0_B
     C0_B --c0_strn (BoxLxCase0Strn.v: pinned, base, strncmp)--> C0_S
     C0_S --c0_fin (BoxLxCase0Fin.v: want, base)--> C0_F
     C0_F --c0_free (BoxLxCase0Free.v: free (name), ren = -1)--> GI_K.
   reac_boxreg_declare returns at an FP state fx' of its own (BoxBase.v apost_baseF; BoxLxDefs.v lx_fxr fx fx'), so
   the pieces from C0_D on run at fx': the phase lemma's continuation GI_K is taken at every such fx', and the
   contracts those pieces apply whose statements name the FP state (bcmp, strncmp, free) are taken at every FP state.
   The Section hypotheses are the contracts the pieces apply and the image's facts their premises need. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YC5d YM05 YG0s YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b YC1g YC1h YC85 BoxFrame BoxCJ BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit BoxLxDefs ReadName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require read_name_c reac_boxreg_declare_c.

From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxCase0Defs
  BoxLxCase0Inp BoxLxCase0Want BoxLxCase0Decl BoxLxCase0Chk BoxLxCase0Strn BoxLxCase0Fin BoxLxCase0Free.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import RangeFree LowestFree ReacBoxregDeclare BoxTailVis.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import StrncmpDef SnprintfDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
Context {RO : ro_below_ofl (@pa_segs _ box_listing PI) pa_relro_lo pa_relro_hi}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable POST : bcx -> world SEGS -> config -> Prop.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AFREE4 : forall fx' : YK11.FPState, afree04_rule (fx := fx') SEGS B MT.
Hypothesis TREADNAME : tread_name_spec B MT.
Hypothesis HRNTR : In [pc_malloc_ra0 (as_code B); A_read_name_mallocRA] (as_universe B).
Hypothesis TRANGEFREE : trange_free_spec B.
Hypothesis TLOWFREE : tlowest_free_spec B.
Hypothesis TDECL : treac_boxreg_declare_spec B.
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis HMRG : Forall (fun g => IMG_LO + 64 <= fst g /\ fst g + snd g + 64 <= IMG_HI) BX_G.
Hypothesis HFMT : asn_rom_bytes SEGS B (VAL (A_OBJ 10)) ASN_FMT.
(* R2: the format below the image's GOT canary slot (declare's P2 premise; BoxLxCase0Decl.v c0_decl) *)
Hypothesis HFMTg : VAL (A_OBJ 10) + 3 <= 0x99b40.
Hypothesis HZERO : asn_rom_bytes SEGS B (VAL (A_OBJ 6)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis HEMP5 : asn_rom_str SEGS B (VAL (A_OBJ 5)) [].
Hypothesis ABCMP : forall fx' : YK11.FPState, abcmp_realizes (fx := fx') SEGS B (SIGMA BS___interceptor_trampoline_bcmp).
Hypothesis ASTRNCMP : forall fx' : YK11.FPState,
  astrncmp_realizes (fx := fx') SEGS B (SIGMA BS___interceptor_trampoline_strncmp).
(* The strncmp contract's view of the runtime's owned read-only statics (AR's const law gives it for boxreg's B
   from the read-only pins; the closing discharges it). Its other view, fm_rom_viewN, comes from gb_base's arodata_okP
   inside BoxLxCase0Strn.v. *)
Hypothesis HROMO : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> fm_rom_viewO SEGS B W mem.

(* The entry fcsr's rounding mode 0 is what the declare contract asks for at its call (freeze change 4). *)
Theorem gb_case0 : forall i,
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  (forall fx' : YK11.FPState, lx_fxr fx fx' -> gb_from B MT POST (GI_K (fx := fx') B MT i)) ->
  gb_from B MT POST (GI_T B MT 0 i).
Proof.
intros i HRM0 HK.
(* the pieces after the declare call, at the FP state fx' it returns with *)
assert (HD : forall fx' : YK11.FPState, lx_fxr fx fx' -> gb_from B MT POST (C0_D (fx := fx') B MT i)).
{ intros fx' Hfx.
  assert (HF : gb_from B MT POST (C0_F (fx := fx') B MT i))
    by (eapply (c0_free (fx := fx')); first [exact (AFREE4 fx') | exact (HK fx' Hfx) | eassumption]).
  assert (HS : gb_from B MT POST (C0_S (fx := fx') B MT i)) by (eapply (c0_fin (fx := fx')); eassumption).
  assert (HBc : gb_from B MT POST (C0_B (fx := fx') B MT i))
    by (eapply (c0_strn (fx := fx')); first [exact (ASTRNCMP fx') | eassumption]).
  eapply (c0_chk (fx := fx')); first [exact (ABCMP fx') | eassumption]. }
assert (HW : gb_from B MT POST (C0_W B MT i))
  by (eapply c0_decl; first [exact (asn_blk_tail_vis_ok SEGS B) | exact HRM0 | exact HD | eassumption]).
assert (HN : gb_from B MT POST (C0_N B MT i)) by (eapply c0_want_ok; eassumption).
eapply c0_inp; eassumption.
Qed.

End c.
End b.
End a.
