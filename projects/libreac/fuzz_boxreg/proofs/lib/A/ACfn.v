(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_boxreg's ASan build from the module of the same name in
   proofs/cgif/cgif_file_fuzzer/lib/A/ACfn.v (origin/ossv/recipes c8557374ad2): its names and statement shapes,
   boxreg's content. *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane): the float state at return of LLVMFuzzerTestOneInput left open, in
   fuzz_grant's shape (a working branch bd0315ce146, proofs/libreac/fuzz_grant/lib/A/ACfn.v:73-141): the slot
   tfib_lib_contract_xP P, cgif's exists-fx' form tfib_lib_contract_xf / _all (lib/Reusable/YL0g.v:58-64 lib_contract),
   and the lemmas from lib/A/Prog/BoxLibX.v's contract into them. BoxLibX.v's tfib_lib_contract_x already returns at some fx' (since
   a working branch ac56ab8e8ff: the f registers but f10 kept, and fp_csr kept or a zero rounding
   mode), so it is NOT the pinned slot: grant's tfib_lib_contract_xP_pinned has no boxreg form, and the two
   disjuncts of the clause give frm_zero (fp_csr fx') at an entry with frm_zero (fp_csr fx)
   (tfib_lib_contract_xf_of_x). *)
(* boxreg content behind cgif's module name; source BoxLibX.v / BoxShape.v.
   The relocated core reads three names of cgif's ACfn.v (cgif line numbers):
   - LLVMF_STK: AD1m.v:46 (`unfold ... LLVMF_STK ... in *`).
   - tfib_lib_contract_x: AD1m.v:31 and AD1p.v:49 (Hypothesis LIBC; AD1m.v:41 applies it and builds the pre field by
     field, AD1m.v:52 the sink conjunct as `conj Henv (conj Hhead Hnames)`, AD1m.v:54 the meta conjunct).
   - tfib_lib_contract_x_all: AD1q.v:50 (Hypothesis LIBX); outside the core cgif's AD2o.v:45, whose place
     lib/A/Prog/BoxClose.v takes (its hypothesis CORE_A).
   With the fx-slot (fuzz_grant's kit) the core also reads tfib_lib_contract_xP (its AD1m.v:34 / AD1p.v:55 LIBC, at
   `forall fx, P fx -> tfib_lib_contract_xP (fx := fx) B MT XM_LIB XN_LIB RLO RHI P`), tfib_lib_contract_xf_all (AD1q.v's
   tfib_srealizesXF) and tfib_lib_contract_xP_of_xf. This file states the three names below in cgif's shapes and those,
   in fuzz_grant's shapes:
   - LLVMF_STK is an abbreviation of BoxLibX.LLVMF_STK (32768), the same constant as lib/A/ACfl.v's.
   - tfib_lib_contract_x (implicit fx rc LS; then B MT XM_LIB XN_LIB RLO RHI) and tfib_lib_contract_x_all (implicit rc LS;
     the same six) are lib/A/Prog/BoxLibX.v's statements of LLVMFuzzerTestOneInput's whole run, at the instance that
     cgif's ACfn.v writes inline:
     . segs = BoxImg.box_segs (images.Asan's loaded segments; the core's tfibsegs of lib/A/AB1v.v is the same term);
     . SINKN = YE00.asink_none box_segs tfib_K and METAI = YE01.ameta_inv box_segs tfib_K, over the core's sink record
       tfib_K (lib/A/AE2k.v; YE00 / YE01 / AE2k as the relocated core states them, string fields deleted per the
       ruling a Theorem Labs lane gave at 23:45Z, ofl_head and ameta_inv kept);
     . the sink head passed explicitly as YI16.mkSinkHead (YE00.ak_ofl_head tfib_K), never an inferred instance: the
       head of tfib_K's open-file list. On fuzz_boxreg.asan it is ofl_head 0x5f4608 = ofl_lock 0x5f4600 + 8 (symtab of
       the ORIGINAL unstripped image 4532568b..., twin of eacfa205...), the value of BoxClose.v's BOX_OFL_HEAD, and
       YE01.v's ail_head (ak_ofl_head K = AOFL_HEAD) holds for it by reflexivity.
     BoxLibX.v's arodata_okP segs RLO RHI B unfolds to the body of cgif's YE01.v arodata_okS segs B RLO RHI.
   No value is defined here. BoxLibX.v's proof of the contract (a Theorem Labs lane) is not used here: the core
   takes the contract as a hypothesis, and lib/A/Prog/BoxClose.v supplies it. *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane): BoxLibX.v tfib_lib_pre_x reads fx since freeze 4 + 5 (-pa 86a3b6dc9e3,
   its last conjunct is the rounding mode at fx), so the two explicit uses below pass fx before rc. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YK11 YM05 YO09 YG0f YC5d YI16 YE00 YE01.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YK0o.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0n YG0d YCbq YO09 YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require BoxImg BoxLibX.
Local Open Scope Z_scope.

Abbreviation LLVMF_STK := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.LLVMF_STK.

Section a.
Context {fx : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YK11.FPState}
  {rc : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YM05.RunCeil}
  {LS : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YO09.lib_shape}.
Variable B : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YG0f.asyms.
Variable MT : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Definition tfib_lib_contract_x : Prop :=
  @OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.tfib_lib_contract_x fx rc LS
    (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YI16.mkSinkHead
       (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YE00.ak_ofl_head
          OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.AE2k.tfib_K))
    B MT XM_LIB XN_LIB RLO RHI
    (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YE00.asink_none
       OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxImg.box_segs
       OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.AE2k.tfib_K)
    (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YE01.ameta_inv
       OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxImg.box_segs
       OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.AE2k.tfib_K).
(* The instance cgif's ACfn.v writes inline, as abbreviations (the terms are the same as in tfib_lib_contract_x above). *)
Local Notation SK0 := (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YI16.mkSinkHead
  (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YE00.ak_ofl_head OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.AE2k.tfib_K)).
Local Notation SINKN0 := (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YE00.asink_none OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxImg.box_segs OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.AE2k.tfib_K).
Local Notation METAI0 := (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YE01.ameta_inv OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxImg.box_segs OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.AE2k.tfib_K).
Local Notation segs := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxImg.box_segs.
(* The slot with the float state at return left open (fuzz_grant ACfn.v:73-86): LLVMFuzzerTestOneInput returns at some
   float state fx' with P, and the driver goes on at fx'. Pre and post are BoxLibX.v's at this instance. *)
Definition tfib_lib_contract_xP (P : YK11.FPState -> Prop) : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
@OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.tfib_lib_pre_x fx rc B MT XM_LIB RLO RHI SINKN0 METAI0 regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = mkCfg (@YK11.mkst fx' regs' (w64 OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.RA_LLVMF) mem' (YK11.seg_rom segs)) md' /\ P fx' /\
@OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.tfib_lib_post_x rc SK0 B MT XN_LIB SINKN0 METAI0 regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
(* cgif's exists-fx' form (lib/Reusable/YL0g.v:58-64 lib_contract; fuzz_grant ACfn.v:87-118): the entry asks a zero
   rounding mode, and the return is at some float state fx' with a zero rounding mode. tfib_lib_pre_xf is BoxLibX.v's pre
   and the zero rounding mode (a pair, not fuzz_grant's flat list: only this file destructs it). *)
Definition tfib_lib_pre_xf (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (M : Z) : Prop :=
@OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.tfib_lib_pre_x fx rc B MT XM_LIB RLO RHI SINKN0 METAI0 regs ly S W mem md p n pl M /\ YK0o.frm_zero (@fp_csr fx).
Definition tfib_lib_contract_xf : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
tfib_lib_pre_xf regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = mkCfg (@YK11.mkst fx' regs' (w64 OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.RA_LLVMF) mem' (YK11.seg_rom segs)) md' /\
YK0o.frm_zero (@fp_csr fx') /\
@OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.tfib_lib_post_x rc SK0 B MT XN_LIB SINKN0 METAI0 regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
(* BoxLibX.v's contract gives the exists-fx' form: its clause (fp_csr fx' = fp_csr fx, or a zero rounding mode at fx')
   gives frm_zero (fp_csr fx') under xf's frm_zero (fp_csr fx). The same two lines as a Theorem Labs lane's bridge
   box_lib_contract_xf_of_x below BoxLibX.v's frozen prefix; this one is stated at this file's names. *)
Lemma tfib_lib_contract_xf_of_x : tfib_lib_contract_x -> tfib_lib_contract_xf.
Proof.
intros LIBC ly S W regs mem md p n pl M K HAI [HPRE Hz] CONT.
apply (LIBC ly S W regs mem md p n pl M K HAI HPRE).
intros l W' c' Hwle HAI' (fx' & ly' & S' & regs' & mem' & md' & k & Hc & _ & Hcsr & HPOST).
apply (CONT l W' c' Hwle HAI'). exists fx', ly', S', regs', mem', md', k.
split; [exact Hc|]. split; [|exact HPOST].
destruct Hcsr as [Ecsr | Ecsr]; [unfold YK0o.frm_zero; rewrite Ecsr; exact Hz | exact Ecsr].
Qed.
(* The exists-fx' slot, entered at a zero rounding mode (fuzz_grant ACfn.v:127-137). *)
Lemma tfib_lib_contract_xP_of_xf : YK0o.frm_zero (@fp_csr fx) -> tfib_lib_contract_xf ->
tfib_lib_contract_xP (fun f : YK11.FPState => YK0o.frm_zero (@fp_csr f)).
Proof.
intros Hz LIBF ly S W regs mem md p n pl M K HAI HPRE CONT.
apply (LIBF ly S W regs mem md p n pl M K HAI (conj HPRE Hz)).
intros l W' c' Hwle HAI' (fx' & ly' & S' & regs' & mem' & md' & k & Hc & Hz' & HPOST).
apply (CONT l W' c' Hwle HAI'). exists fx', ly', S', regs', mem', md', k. exact (conj Hc (conj Hz' HPOST)).
Qed.
(* BoxLibX.v's contract in the slot, at P = a zero rounding mode: the slot the core's LIBC asks. *)
Lemma tfib_lib_contract_xP_of_x : YK0o.frm_zero (@fp_csr fx) -> tfib_lib_contract_x ->
tfib_lib_contract_xP (fun f : YK11.FPState => YK0o.frm_zero (@fp_csr f)).
Proof. intros Hz LIBC. exact (tfib_lib_contract_xP_of_xf Hz (tfib_lib_contract_xf_of_x LIBC)). Qed.
End a.

Definition tfib_lib_contract_x_all {rc : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YM05.RunCeil}
  {LS : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YO09.lib_shape}
  (B : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YG0f.asyms)
  (MT : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YC5d.ameter_ops)
  (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
  @OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxLibX.tfib_lib_contract_x_all rc LS
    (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YI16.mkSinkHead
       (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YE00.ak_ofl_head
          OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.AE2k.tfib_K))
    B MT XM_LIB XN_LIB RLO RHI
    (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YE00.asink_none
       OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxImg.box_segs
       OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.AE2k.tfib_K)
    (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YE01.ameta_inv
       OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxImg.box_segs
       OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.AE2k.tfib_K).
Definition tfib_lib_contract_xf_all {rc : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YM05.RunCeil}
  {LS : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YO09.lib_shape}
  (B : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YG0f.asyms)
  (MT : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YC5d.ameter_ops)
  (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
  forall fx : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YK11.FPState,
  @tfib_lib_contract_xf fx rc LS B MT XM_LIB XN_LIB RLO RHI.
(* The whole-run contract for every entry float state gives the exists-fx' form for every one. *)
Lemma tfib_lib_contract_xf_all_of_x_all {rc : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YM05.RunCeil}
  {LS : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YO09.lib_shape}
  (B : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YG0f.asyms)
  (MT : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YC5d.ameter_ops)
  (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) :
  tfib_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI -> tfib_lib_contract_xf_all B MT XM_LIB XN_LIB RLO RHI.
Proof. intros LIBX fx. exact (tfib_lib_contract_xf_of_x (fx := fx) B MT XM_LIB XN_LIB RLO RHI (LIBX fx)). Qed.
