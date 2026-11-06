(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 23 of its 73 lines of code are new or changed and 1030 lines of the source are left out. *)
(* Two cuts of seg_I (LLVMFuzzerTestOneInput_I.v): the premises reac_box_name's contract asks of the entry's call
   at 0x8196c (reac_box_name.v:132-133, under bn_args_ok), stated over a state of the entry's journal. Each is a
   Prop here; its proof is `Lemma I_rbn_said : I_rbn_said_stmt.` / `Lemma I_rbn_bufs : I_rbn_bufs_stmt.`
   in the same Section (the helper lane appends them below the statements).

   said is id.model_name (SF + 355, 0x81890 / 0x81900) when id.has_model_name <> 0, else 0; sd is the C string
   there (the plain model's name_str of the decoded identity), which is IM.sdZ of LLVMFuzzerTestOneInput_I.v.
   The three buffers are the run's three heap blocks nm / tk / dp of sizes max cap 1 (0x818b8, 0x818d0, 0x818e8). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require reac_box_name.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section c.
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v / _I.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation EPRE g := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS g).
#[local] Notation AJ g pos := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(4, pos)]).
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.

(* the C string reac_box_name gets as said (LLVMFuzzerTestOneInput_I.v IM.sdZ) *)
Definition I_sd (inp : list byte) : list Z :=
  if SlotModel.n_said inp then map RcIdentModel.bz (SlotModel.name_str (SlotModel.idT inp)) else [].
Definition I_said (g : ectx) (pos : Z) : Z :=
  if RcIdentModel.has_model_name (m_id g (m_nrec g)) =? 0 then 0 else SFa g pos + V_id + 3.

(* said / sd: from id's bytes and shadow (id_at, kept from 0x80990 on) and the class-4 frame *)
Definition I_rbn_said_stmt : Prop :=
  forall g pos lyc Sc (W : world SEGS) mem md k,
  EPRE g -> AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] ->
  id_at g pos (m_nrec g) W mem ->
  reac_box_name.rbn_said lyc Sc W mem (I_said g pos) (I_sd (e_pl g)).

(* the three output buffers: the run's three heap blocks, pairwise apart *)
Definition I_rbn_bufs_stmt : Prop :=
  forall g pos lyc Sc (W : world SEGS) mem md k nm tk dp,
  EPRE g -> AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] ->
  hblocks B g lyc Sc [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
                      (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
                      (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] ->
  reac_box_name.rbn_bufs B lyc Sc nm (SlotModel.t_cap_name (e_pl g)) tk (SlotModel.t_cap_tok (e_pl g))
    dp (SlotModel.t_cap_disp (e_pl g)).

End c.
End b.
End a.
