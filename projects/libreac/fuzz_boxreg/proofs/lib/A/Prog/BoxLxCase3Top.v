(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryUnset), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryUnset.v, with its module paths and module names changed; 2249 of its 2361 lines of code are new or changed and 693 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxCase3.v, with its module paths and module names changed; 28 of its 103 lines of code are new or changed and 2286 lines of the source are left out. *)
(* The top of the ASan walk of LLVMFuzzerTestOneInput's case 3 (fuzz_boxreg.c:385-399): it ties the head of the
   case (lib/A/Prog/BoxLxCase3A.v c3_segA, 0x803fc .. 0x80580's return) to the set_name call and the tail
   (lib/A/Prog/BoxLxCase3.v), and states the phase's theorem for the integrator.

   reac_boxreg_set_name returns at a new FP state (BoxBase.v apost_baseF), so the cut after the call and the
   join's continuation are taken at every fx' with lx_fxr fx fx' (BoxLxDefs.v); gb_from itself carries no fx. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YImgTop YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase YC1g YC1h YC4b YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
BoxCJ BoxRo BoxFrame BoxTailVis ReacBoxregInit ReacBoxregSetName ReadName BoxLxDefs BoxLxCase3.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfDef StrncmpDef StrncmpView.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
(* The two runtime contracts the tail takes after the call, at every FP state the call may return at. *)
Hypothesis AFREE4 : forall fx' : YK11.FPState, lx_fxr fx fx' -> @afree04_rule fx' rc SK SEGS B MT.
Hypothesis ASTRNCMP : forall fx' : YK11.FPState, lx_fxr fx fx' ->
  @astrncmp_realizes fx' rc SEGS B (SIGMA BS___interceptor_trampoline_strncmp).
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis TSETNAME : treac_boxreg_set_name_spec B.
Hypothesis HFMT : asn_rom_bytes SEGS B (VAL (A_OBJ 10)) ASN_FMT.
Hypothesis HFMTa : IMG_LO + 64 <= VAL (A_OBJ 10).
Hypothesis HFMTb : VAL (A_OBJ 10) + 3 + 64 <= IMG_HI.
(* R2: the format below the image's GOT canary slot (set_name's P2 premise; BoxLxCase3.v c3_segB) *)
Hypothesis HFMTg : VAL (A_OBJ 10) + 3 <= 0x99b40.
Hypothesis HE11 : asn_rom_str SEGS B (VAL (A_OBJ 11)) [].
Hypothesis HE11a : IMG_LO + 64 <= VAL (A_OBJ 11).
Hypothesis HE11b : VAL (A_OBJ 11) + 1 + 64 <= IMG_HI.
Hypothesis HE5 : asn_rom_str SEGS B (VAL (A_OBJ 5)) [].
Hypothesis HE5a : IMG_LO + 64 <= VAL (A_OBJ 5).
Hypothesis HE5b : VAL (A_OBJ 5) + 1 + 64 <= IMG_HI.
Hypothesis HROMO : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> fm_rom_viewO SEGS B W mem.

(* The head of the case, 0x803fc .. the return of read_name at 0x80584, with the state at 0x80584 (the cut
   c3_segB takes) as its continuation: lib/A/Prog/BoxLxCase3A.v (a Theorem Labs lane). *)
Hypothesis C3SEGA : forall (cx : bcx) (fp : Z) (POST : bcx -> world SEGS -> config -> Prop) (i : Z),
  gb_base B MT cx ->
  (forall ly' S' W' (ms' : machine_state) md' k' acc' r bs idxb pos nm szn op sstr,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(GB_CID, fp)] ly' S' W' (ms_mem ms') md' k' ->
  frames S' = [(GB_CID, fp)] -> mo_le MT (c_S cx) S' acc' ->
  0 <= i < 64 -> k' <= 2 + 2 * i -> acc' + mo_free MT <= GB_A MT (i + 1) ->
  ms_pc_val ms' = w64 (BASE + 0x638) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  gregs cx fp ms' ->
  getr (ms_regs ms') 10 = w64 nm -> getr (ms_regs ms') 20 = w64 r ->
  getr (ms_regs ms') 21 = Z_to_bv 64 idxb -> getr (ms_regs ms') 22 = w64 op ->
  getr (ms_regs ms') 25 = w64 (Boxreg.bx_fabric bs) -> getr (ms_regs ms') 26 = w64 (Boxreg.bx_n bs) ->
  0 <= idxb < 256 -> 0 <= op < 256 ->
  c3_M0 cx fp W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') ->
  gcursor cx W' ms' pos ->
  greg B ly' S' W' ms' r bs ->
  ablocks B ly' S' = ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE); (nm, szn)] ->
  0 < szn <= 48 ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly' S')) ->
  Boxreg.boxreg_inv bs ->
  Forall (fun c => 0 < c < 256) sstr -> Z.of_nat (length sstr) + 1 <= szn ->
  (forall j, 0 <= j <= Z.of_nat (length sstr) ->
  aview SEGS (w_H W') (ms_mem ms') (nm + j) = Some (nth (Z.to_nat j) (sstr ++ [0]) 0)) ->
  SRr SEGS W' (mkCfg ms' md') (POST cx)) ->
  forall k acc ly3 S3 W3 (ms3 : machine_state) md3,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GB_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  GI_T B MT 3 i cx fp k acc ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

(* ---- the phase's theorem ---- *)
(* The entry fcsr's rounding mode 0 is what the set_name contract asks for at its call (freeze change 4). *)
Theorem gb_case3 : forall (POST : bcx -> world SEGS -> config -> Prop) (i : Z),
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  (forall fx' : YK11.FPState, lx_fxr fx fx' -> gb_from B MT POST (GI_K (fx := fx') B MT i)) ->
  gb_from B MT POST (GI_T B MT 3 i).
Proof.
  intros POST i HRM0 HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
  eapply (C3SEGA cx fp POST i HB); [| exact HJ | exact HFR | exact HMO | exact HI].
  eapply c3_segB.
  all: try eassumption.
  all: try (intros fx' Hfx; eapply (c3_segC (fx := fx'));
            first [ eassumption | exact (AFREE4 fx' Hfx) | exact (ASTRNCMP fx' Hfx)
                  | exact (HNEXT fx' Hfx) ]).
  all: first [ exact (AFREE4 fx (lx_fxr_refl fx)) | exact (ASTRNCMP fx (lx_fxr_refl fx)) ].
Qed.
End c.
End b.
End a.
