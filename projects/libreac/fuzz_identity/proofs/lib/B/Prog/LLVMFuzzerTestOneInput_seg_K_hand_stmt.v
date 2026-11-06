(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v, with its module paths changed; 144 of its 182 lines of code are new or changed and 1105 lines of the source are left out. *)
(* Closed statements of the pieces of seg_K of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B), for provers
   outside the K lane: lib/B/Prog/LLVMFuzzerTestOneInput_seg_K.v takes each as a premise. Definitions only. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81 IdentBlkTail.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
check_str reac_box_catalogue reac_box_catalogue_defect.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The pieces of seg_K (LLVMFuzzerTestOneInput_inv.v seg_K_stmt, +0x1988 .. +0x1bec, the n_r = 0 path) as closed
   statements: each is one stretch of the listing between two call returns, in continuation form, from the state
   predicate KC at its first slot to KC at its last. KH is inv_J_end's body at the start state with n_r = 0;
   KPRE is the contract hypotheses the pieces use, as LLVMFuzzerTestOneInput.v states them. Offsets are from the
   entry (BASE + off = fuzz_identity.asan-ubsan 0x80774 + off). *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The boundary file's Section c, in the same order. *)
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
Variable G : list (Z * Z).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).

(* The contract hypotheses the pieces use (LLVMFuzzerTestOneInput.v, Section c). *)
Definition KPRE : Prop :=
  STK_LLVMF <= LLVMF_STK /\
  AR_laws SEGS B /\ PALib B /\ identb_prog_sig_ok (PI := PI) /\
  ro_below_ofl SEGS pa_relro_lo pa_relro_hi /\
  (forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr) /\
  globs_marked SEGS B G /\ img_shadow_vis SEGS B /\ In (VAL (A_OBJ 28), 3256) G /\
  (forall (W : world SEGS) mem,
    arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem) /\
  astrlen_realizes SEGS B (SIGMA IB___interceptor_trampoline_strlen) /\
  astrcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_strcmp) /\
  (forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
    ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
    m_fds md' = m_fds md /\ m_fs md' = m_fs md) /\
  check_str.tcheck_str_spec B /\ reac_box_catalogue.tcat_spec B /\
  reac_box_catalogue_defect.treac_box_catalogue_defect_spec B G.

(* inv_J_end's acut and body at the start state (LLVMFuzzerTestOneInput_inv.v:523-548), with n_r = 0. *)
Definition KH (g : ectx) (pos mf nm tk dp : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) /\
  frames S2 = [(4, pos)] /\ 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF /\
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * MEV MT) /\
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * MEV MT) /\
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 /\
  hblocks B g ly2 S2 [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
    (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
    (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] /\
  sh_reg g pos regs2 /\ getr regs2 24 = w64 (SlotModel.n_r (e_pl g)) /\
  getr regs2 21 = w64 tk /\
  getr regs2 22 = w64 (SlotModel.t_cap_disp (e_pl g)) /\
  getr regs2 25 = w64 (SFa g pos + V_nm) /\ getr regs2 26 = w64 (SFa g pos + V_dp) /\
  val_mem SEGS (rd W2 mem2) (mf + 152) 8 nm /\
  val_mem SEGS (rd W2 mem2) (mf + 184) 8 dp /\
  val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SlotModel.t_cap_name (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 128) 8 (SlotModel.t_cap_tok (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.t_cap_disp (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 176) 8 (SlotModel.t_in (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_out (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 112) 8 (SlotModel.t_row (e_pl g)) /\
  sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
  (SlotModel.n_wok (e_pl g) = true ->
    bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
    bytes_at8 W2 mem2 (SFa g pos + V_dp) (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0])) /\
  (SlotModel.n_r (e_pl g) = 0 ->
    bytes_at8 W2 mem2 nm (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
    bytes_at8 W2 mem2 tk (SlotModel.n_TK (e_pl g) ++ [RcIdentModel.zb 0]) /\
    bytes_at8 W2 mem2 dp (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0])) /\
  SlotModel.n_r (e_pl g) = 0.

(* The bytes seg_K may change: the callees' stack below sp = mf (check_str and reac_box_catalogue_defect use
   16 + 2 * ESTACK, the wrappers 2 * ESTACK, reac_box_catalogue 16 + ESTACK), `count` (SF+720, 8 bytes, written
   at 0x82250 and by reac_box_catalogue) and its shadow byte (written at 0x8224c and 0x8235c). *)
Definition kwin (g : ectx) (pos mf : Z) (a : Z) : Prop :=
  (mf - (16 + 2 * ESTACK) <= a < mf) \/ (SFa g pos + V_cnt <= a < SFa g pos + V_cnt + 8) \/
  a = shadow_addr (SFa g pos) + 90.
Definition kkeep (g : ectx) (pos mf : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (mem2 mem : word -> option byte) : Prop :=
  (* what a call keeps, in the shape of IdentBCJ.tcj_kept / YCbq.acall_kept: the machine stack above the
     callees' window, the live heap blocks, and the entry's own side-stack frame and its shadow outside
     `count` (SF+720, 8 bytes) and count's shadow byte (shadow(SF)+90). *)
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (mf - (16 + 2 * ESTACK) <= a < mf) ->
     aview SEGS (w_H W2) mem a = aview SEGS (w_H W2) mem2 a) /\
  (forall b n i, In (b, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
     aview SEGS (w_H W2) mem (b + i) = aview SEGS (w_H W2) mem2 (b + i)) /\
  (forall a, (in_zr a (frame_rng ly2 (4, pos)) \/
              in_zr a (shadow_addr (frame_addr ly2 4 pos), fs_frame_bytes 4 / 8)) ->
     ~ (SFa g pos + V_cnt <= a < SFa g pos + V_cnt + 8) -> a <> shadow_addr (SFa g pos) + 90 ->
     aview SEGS (w_H W2) mem a = aview SEGS (w_H W2) mem2 a).
(* The state between two pieces: the boundary's journal (same ly2 S2 W2: no callee of seg_K changes them),
   memory as at the start outside kwin, sp = s1 = mf, s0 = sp0, gp, tp, s5 = tk, s7 = the frame's shadow. *)
Definition KC (g : ectx) (pos mf tk : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (mem2 : word -> option byte) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem md (4 * Z.of_nat (m_nrec g) + 7) /\
  kkeep g pos mf ly2 S2 W2 mem2 mem /\
  getr regs 2 = w64 mf /\ getr regs 9 = w64 mf /\ getr regs 8 = w64 (e_sp0 g) /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 21 = w64 tk /\ getr regs 23 = w64 (shadow_addr (SFa g pos)).
(* s6 = the display capacity, s9 = &exp_nm, s10 = &exp_dp (set before +0x1988, read by the pieces up to 0x82164). *)
Definition KR (g : ectx) (pos : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 22 = w64 (SlotModel.t_cap_disp (e_pl g)) /\
  getr regs 25 = w64 (SFa g pos + V_nm) /\ getr regs 26 = w64 (SFa g pos + V_dp).

(* +0x1988 .. +0x19a8 (0x820fc .. 0x8211c): `bnez s8` (s8 = n_r = 0, falls through), s2 = nm (mf+152), the strlen
   wrapper on nm (0x82108, returns n_ln), check_str (n_ln, nm, cap_name from mf+144) at 0x82118. *)
Definition k_name_stmt : Prop := KPRE ->
  forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2, KH g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 ->
  forall regs mem md (Q : world SEGS -> config -> Prop),
  KC g pos mf tk ly2 S2 W2 mem2 regs mem md -> KR g pos regs -> getr regs 24 = w64 0 ->
  (forall regs' mem' md', KC g pos mf tk ly2 S2 W2 mem2 regs' mem' md' -> KR g pos regs' -> getr regs' 18 = w64 nm ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x19a8) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1988) regs mem md) Q.
(* +0x19a8 .. +0x19c0 (0x8211c .. 0x82134): the strlen wrapper on tk = s5 (0x82120, returns n_lt), check_str
   (n_lt, tk, cap_tok from mf+128) at 0x82130. *)
Definition k_tok_stmt : Prop := KPRE ->
  forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2, KH g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 ->
  forall regs mem md (Q : world SEGS -> config -> Prop),
  KC g pos mf tk ly2 S2 W2 mem2 regs mem md -> KR g pos regs -> getr regs 18 = w64 nm ->
  (forall regs' mem' md', KC g pos mf tk ly2 S2 W2 mem2 regs' mem' md' -> KR g pos regs' -> getr regs' 18 = w64 nm ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x19c0) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x19a8) regs mem md) Q.
(* +0x19c0 .. +0x19dc (0x82134 .. 0x82150): s3 = dp (mf+184), the strlen wrapper on dp (0x8213c, returns n_ld),
   check_str (n_ld, dp, s6 = cap_disp) at 0x8214c. *)
Definition k_disp_stmt : Prop := KPRE ->
  forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2, KH g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 ->
  forall regs mem md (Q : world SEGS -> config -> Prop),
  KC g pos mf tk ly2 S2 W2 mem2 regs mem md -> KR g pos regs -> getr regs 18 = w64 nm ->
  (forall regs' mem' md', KC g pos mf tk ly2 S2 W2 mem2 regs' mem' md' -> KR g pos regs' -> getr regs' 18 = w64 nm ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x19dc) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x19c0) regs mem md) Q.
(* +0x19dc .. +0x19f8 (0x82150 .. 0x8216c): strcmp (nm, s9 = exp_nm) at 0x82158 and its abort test 0x8215c
   (not taken: both hold n_EXP_NM ++ [0]); strcmp (dp from mf+184, s10 = exp_dp) at 0x82168; ends at its return
   with a0 = 0. *)
Definition k_cmp_stmt : Prop := KPRE ->
  forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2, KH g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 ->
  forall regs mem md (Q : world SEGS -> config -> Prop),
  KC g pos mf tk ly2 S2 W2 mem2 regs mem md -> KR g pos regs -> getr regs 18 = w64 nm ->
  (forall regs' mem' md', KC g pos mf tk ly2 S2 W2 mem2 regs' mem' md' -> getr regs' 10 = w64 0 ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x19f8) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x19dc) regs mem md) Q.
(* +0x19f8 .. +0x1ad8 (0x8216c .. 0x8224c): the abort test of the second strcmp (0x82170, not taken), the token
   loop 0x8219c..0x82204 over nm against tk (tk[j] = lower nm[i], the first '-' dropped: SlotModel.n_TK), its UBSan
   traps (0x821c0, 0x82200, 0x82204) and ASan checks, and the NUL test of tk (0x8222c..0x82248); ends with
   s2 = &count (SF+720, set at 0x82184). *)
Definition k_loop_stmt : Prop := KPRE ->
  forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2, KH g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 ->
  forall regs mem md (Q : world SEGS -> config -> Prop),
  KC g pos mf tk ly2 S2 W2 mem2 regs mem md -> getr regs 10 = w64 0 ->
  (forall regs' mem' md', KC g pos mf tk ly2 S2 W2 mem2 regs' mem' md' -> getr regs' 18 = w64 (SFa g pos + V_cnt) ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x1ad8) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x19f8) regs mem md) Q.
(* +0x1ad8 .. +0x1ae8 (0x8224c .. 0x8225c): count's shadow byte cleared (0x8224c), count = 0 (0x82250),
   reac_box_catalogue (&count) at 0x82258 (caller-journal form, cat_pR_ok's left disjunct); ends at its return
   with a0 = BOX_CATALOGUE and count = 11. *)
Definition k_cat_stmt : Prop := KPRE ->
  forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2, KH g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 ->
  forall regs mem md (Q : world SEGS -> config -> Prop),
  KC g pos mf tk ly2 S2 W2 mem2 regs mem md -> getr regs 18 = w64 (SFa g pos + V_cnt) ->
  (forall regs' mem' md', KC g pos mf tk ly2 S2 W2 mem2 regs' mem' md' -> getr regs' 18 = w64 (SFa g pos + V_cnt) ->
    getr regs' 10 = w64 (VAL reac_box_catalogue.CAT_OBJ) ->
    val_mem SEGS (rd W2 mem') (SFa g pos + V_cnt) 8 reac_box_catalogue.BOX_COUNT ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x1ae8) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1ad8) regs mem md) Q.
(* +0x1ae8 .. +0x1bec (0x8225c .. 0x82360): count = 11 (0x82260 not taken), the row e = BOX_CATALOGUE + 296 *
   (t_row mod 11) (0x8226c..0x82278) and its UBSan traps (0x8227c, 0x8228c), reac_box_catalogue_defect (e, t_in,
   t_out, dp) at 0x822a8, the inline mask (0x822b0..0x82350: the alignment trap 0x822b8, I / O compares, P,
   strcmp (P, dp) at 0x82344 when P <> 0), the mask compare 0x82354 (equal: both are CATALOGUE_DEFECT_MASK) and
   count's shadow poisoned again (0x8235c). *)
Definition k_def_stmt : Prop := KPRE ->
  forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2, KH g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 ->
  forall regs mem md (Q : world SEGS -> config -> Prop),
  KC g pos mf tk ly2 S2 W2 mem2 regs mem md -> getr regs 18 = w64 (SFa g pos + V_cnt) ->
  getr regs 10 = w64 (VAL reac_box_catalogue.CAT_OBJ) ->
  val_mem SEGS (rd W2 mem) (SFa g pos + V_cnt) 8 reac_box_catalogue.BOX_COUNT ->
  (forall regs' mem' md', KC g pos mf tk ly2 S2 W2 mem2 regs' mem' md' ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x1bec) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1ae8) regs mem md) Q.
End c.
End b.
End a.
