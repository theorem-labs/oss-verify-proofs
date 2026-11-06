(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the contract of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACfn.v:33-69
   (tfib_lib_pre_x, tfib_lib_post_x, tfib_lib_contract_x) restated for libreac/fuzz_identity's ASan+UBSan
   build: the module paths are this unit's lib.B, the image is the position-abstract one (pa_segs,
   BASE + AF_LLVMFuzzerTestOneInput of identb_listing), the library shape and every constant of the unit's
   relocated core are parameters of the Section, and the measured needs of this build's entry (events, live
   bytes, stack) are stated beside it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput.v, with its module paths and module names changed; 202 of its 267 lines of code are new or changed and 162 lines of the source are left out. *)
(* The shared lemmas of seg_K of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B), over the statements of
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_K_hand_stmt.v (KPRE, KH, kwin, kkeep, KC, KR): the contract hypotheses
   unpacked from KPRE, the plain-model lemmas the checks read (KModel), the four callees in the journal form
   (strlen and strcmp wrappers, check_str, reac_box_catalogue_defect), the geometry of the start state (k_geom),
   what a piece keeps (k_vm_kept, k_vm_hi, k_garr8_moved), the read-only image at a piece's state (k_aro), the
   call chain at sp = mf (k_achain), and the last piece's step to inv_K_end (k_finish). A piece of the segment
   proves `k_<part>_stmt` using these; lib/B/Prog/LLVMFuzzerTestOneInput_seg_K.v chains the pieces. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_seg_K_hand_stmt LLVMFuzzerTestOneInput_seg_K_base.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
LLVMFuzzerTestOneInput_seg_K_hand_disp LLVMFuzzerTestOneInput_seg_K_hand_cat
LLVMFuzzerTestOneInput_seg_K_hand_cmp
LLVMFuzzerTestOneInput_seg_K_hand_name LLVMFuzzerTestOneInput_seg_K_hand_tok
LLVMFuzzerTestOneInput_seg_K_hand_loop LLVMFuzzerTestOneInput_seg_K_hand_def.

(* ---- seg_K: the r <> 0 branch and the chain of the pieces ---------------------------------------------------- *)
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
#[local] Notation KHn := (KH B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation KCn := (KC B LLVMF_STK).
#[local] Notation KRn := (KR (PI := PI)).
#[local] Notation KENDn := (inv_K_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JENDn := (inv_J_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
(* The contract's hypotheses seg_K uses, in the contract's order (LLVMFuzzerTestOneInput.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis PSIG : identb_prog_sig_ok (PI := PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis G_CAT : In (VAL (A_OBJ 28), 3256) G.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis ASTRLEN : astrlen_realizes SEGS B (SIGMA IB___interceptor_trampoline_strlen).
Hypothesis ASTRCMP : astrcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_strcmp).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Hypothesis HCHK : check_str.tcheck_str_spec B.
Hypothesis HCAT : reac_box_catalogue.tcat_spec B.
Hypothesis HCATD : reac_box_catalogue_defect.treac_box_catalogue_defect_spec B G.
#[local] Notation KPREn := (KPRE B RLO RHI LLVMF_STK arodata_okS G).
Let HPRE : KPREn :=
  conj HSTK (conj LAWS (conj TL (conj PSIG (conj RO (conj HRO (conj GM (conj IV (conj G_CAT (conj HIMG
  (conj ASTRLEN (conj ASTRCMP (conj AJ_NIL_IO (conj HCHK (conj HCAT HCATD)))))))))))))).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* The symbolic state at +0x1988 with no region: the branch slot. *)
Definition kc_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Lemma kc_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (kc_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. unfold kc_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. exact I.
- split; [exact I | split; exact I].
Qed.

(* ecommon across a run that changes nothing. *)
Lemma k_ec_total : forall g pos mf ly S W regs mem md regs' mem' md',
  ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS g pos mf ly S W regs mem md ->
  (forall a, aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) -> m_fs md' = m_fs md ->
  getr regs' 2 = getr regs 2 -> getr regs' 9 = getr regs 9 -> getr regs' 8 = getr regs 8 ->
  getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS g pos mf ly S W regs' mem' md'.
Proof.
intros g pos mf ly S W regs mem md regs' mem' md' HEC KEEP Hfd Hfs E2 E9 E8 E3 E4.
assert (VK : forall a n v, val_mem SEGS (rd W mem) a n v -> val_mem SEGS (rd W mem') a n v).
{ intros a n v Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem' a n v); [|exact Hv].
  intros k Hk. apply KEEP. }
destruct HEC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 & W9 & W18 & W19 &
  W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & Vflag & HPREe & Hfds & Hfse & Hinb).
unfold ecommon.
split; [rewrite E2; exact Rsp|]. split; [rewrite E9; exact Rs1|]. split; [rewrite E8; exact Rs0|].
split; [exact Hmfb|]. split; [exact Hmf32|]. split; [rewrite E3; exact Rgp|]. split; [rewrite E4; exact Rtp|].
do 18 (split; [apply VK; assumption|]).
split; [exact HPREe|].
split; [intros fd; rewrite Hfd; exact (Hfds fd)|].
split; [rewrite Hfs; exact Hfse|].
unfold bytes_at8 in *. apply (k_garr8_moved (w_H W) (w_H W) mem mem' _ _); [|exact Hinb].
intros k Hk. apply KEEP.
Qed.

(* The r <> 0 side: `bnez s8` at 0x820fc jumps straight to +0x1bec; nothing is read or written. *)
Lemma k_rne : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * MEV MT) ->
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * MEV MT) ->
  ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  hblocks B g ly2 S2 [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
    (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1); (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] ->
  sh_reg g pos regs2 -> getr regs2 21 = w64 tk ->
  val_mem SEGS (rd W2 mem2) (mf + 152) 8 nm -> val_mem SEGS (rd W2 mem2) (mf + 184) 8 dp ->
  getr regs2 24 = w64 (SlotModel.n_r (e_pl g)) -> SlotModel.n_r (e_pl g) = -1 ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1988) regs2 mem2 md2) (KENDn g pos mf nm tk dp).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HJ HFR HK HMLE HMOK HEC HHB HSR R21 V152 V184 R24 Hr.
pose proof (kc_entry W2 regs2 mem2 0x1988) as HS.
pose proof (Eimg_env (Ereg regs2 (@nil word))) as HEI.
assert (E24 : getr regs2 24 = Z_to_bv 64 (-1)) by (rewrite R24, Hr; reflexivity).
pose proof (st_ok_pi_pin_reg' _ _ _ (24%bv : bv 5) (-1) HS E24 eq_refl) as HS1. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts kc_ss] in HS1.
unfold cfg_at. change (w64 (BASE + 0x1988)) with (Z_to_bv 64 (BASE + 0x1988)).
paj_run_to_sh RUNTOP HS1 HJ 0x1bec.
{ cbn [ss_mem]. apply awr_ok_nil. }
assert (KEEP : forall a, aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a. apply aview_eq_of. apply HFr. intros (r' & Hin & _). cbn in Hin. destruct Hin. }
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (8%bv : bv 5) Q8.
prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (21%bv : bv 5) Q21. prreg HS1 (23%bv : bv 5) Q23.
rewrite (ew_Eimg_Ereg_nat regs2 (@nil word) 2 2%bv eq_refl) in Q2.
rewrite (ew_Eimg_Ereg_nat regs2 (@nil word) 9 9%bv eq_refl) in Q9.
rewrite (ew_Eimg_Ereg_nat regs2 (@nil word) 8 8%bv eq_refl) in Q8.
rewrite (ew_Eimg_Ereg_nat regs2 (@nil word) 3 3%bv eq_refl) in Q3.
rewrite (ew_Eimg_Ereg_nat regs2 (@nil word) 4 4%bv eq_refl) in Q4.
rewrite (ew_Eimg_Ereg_nat regs2 (@nil word) 21 21%bv eq_refl) in Q21.
rewrite (ew_Eimg_Ereg_nat regs2 (@nil word) 23 23%bv eq_refl) in Q23.
pmkst HS1. apply SRr_ret.
unfold inv_K_end, acut.
exists ly2, S2, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
split; [reflexivity|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact HK|].
split; [exact HMLE|]. split; [exact HMOK|].
split.
- apply (k_ec_total g pos mf ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms)
    (with_vm_backing (m_vm_lazy md2) mat md2));
  [ exact HEC | intros a; apply KEEP
  | intros fd; destruct md2 as [f [mp lz mt] io fs pr li ti]; reflexivity
  | destruct md2 as [f [mp lz mt] io fs pr li ti]; reflexivity
  | exact Q2 | exact Q9 | exact Q8 | exact Q3 | exact Q4 ].
- split; [exact HHB|]. split; [unfold sh_reg; rewrite Q23; exact HSR|]. split; [rewrite Q21; exact R21|].
  split; (apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms)); [intros k Hk; apply KEEP | assumption]).
Qed.

(* ---- the pieces (proved in the lane's hand files; premises here until they land) ------------------------------ *)
Let k_name : k_name_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS G :=
  LLVMFuzzerTestOneInput_seg_K_hand_name.k_name B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
    asink_syms_T KS asink_none ameta_inv arodata_okS G.
Let k_tok : k_tok_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS G :=
  LLVMFuzzerTestOneInput_seg_K_hand_tok.k_tok B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
    asink_syms_T KS asink_none ameta_inv arodata_okS G.
Let k_disp : k_disp_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS G :=
  LLVMFuzzerTestOneInput_seg_K_hand_disp.k_disp B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
    asink_syms_T KS asink_none ameta_inv arodata_okS G.
Let k_cmp : k_cmp_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS G :=
  LLVMFuzzerTestOneInput_seg_K_hand_cmp.k_cmp B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
    asink_syms_T KS asink_none ameta_inv arodata_okS G HPRE.
Let k_loop : k_loop_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS G :=
  LLVMFuzzerTestOneInput_seg_K_hand_loop.k_loop B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
    asink_syms_T KS asink_none ameta_inv arodata_okS G HPRE.
Let k_cat : k_cat_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS G :=
  LLVMFuzzerTestOneInput_seg_K_hand_cat.k_cat B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
    asink_syms_T KS asink_none ameta_inv arodata_okS G HPRE HEV.
Let k_def : k_def_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS G :=
  LLVMFuzzerTestOneInput_seg_K_hand_def.k_def_A B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
    asink_syms_T KS asink_none ameta_inv arodata_okS G
    (fun HP => LLVMFuzzerTestOneInput_seg_K_base.k_defect_at B RLO RHI LLVMF_STK arodata_okS G HP).

(* The r = 0 side: the seven pieces in a row, then inv_K_end. *)
Lemma k_req : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2,
  KHn g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 -> SlotModel.n_r (e_pl g) = 0 ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1988) regs2 mem2 md2) (KENDn g pos mf nm tk dp).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH Hr.
pose proof HKH as (HJ & HFR & HK & HMLE & HMOK & HEC & HHB & HSR & R24 & R21 & R22 & R25 & R26 & _).
pose proof HEC as (Rsp & Rs1 & Rs0 & _ & _ & Rgp & Rtp & _).
assert (HC0 : KCn g pos mf tk ly2 S2 W2 mem2 regs2 mem2 md2).
{ unfold KC. split; [exact HJ|].
  split; [split; [intros; reflexivity | split; intros; reflexivity]|].
  split; [exact Rsp|]. split; [exact Rs1|]. split; [exact Rs0|]. split; [exact Rgp|]. split; [exact Rtp|].
  split; [exact R21 | exact HSR]. }
assert (HR0 : KRn g pos regs2) by (split; [exact R22 | split; [exact R25 | exact R26]]).
apply (k_name HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs2 mem2 md2 _ HC0 HR0
  ltac:(rewrite R24, Hr; reflexivity)).
intros regs3 mem3 md3 HC3 HR3 Hnm3.
apply (k_tok HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs3 mem3 md3 _ HC3 HR3 Hnm3).
intros regs4 mem4 md4 HC4 HR4 Hnm4.
apply (k_disp HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs4 mem4 md4 _ HC4 HR4 Hnm4).
intros regs5 mem5 md5 HC5 HR5 Hnm5.
apply (k_cmp HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs5 mem5 md5 _ HC5 HR5 Hnm5).
intros regs6 mem6 md6 HC6 Hz6.
apply (k_loop HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs6 mem6 md6 _ HC6 Hz6).
intros regs7 mem7 md7 HC7 Hcnt7.
apply (k_cat HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs7 mem7 md7 _ HC7 Hcnt7).
intros regs8 mem8 md8 HC8 Hcnt8 Ha08 Hv8.
apply (k_def HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs8 mem8 md8 _ HC8 Hcnt8 Ha08 Hv8).
intros regs9 mem9 md9 HC9.
apply SRr_ret.
exact (k_finish B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs9 mem9 md9 HC9).
Qed.

(* ---- seg_K --------------------------------------------------------------------------------------------------- *)
Lemma seg_K : seg_K_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf nm tk dp W2 c2 HJE.
destruct HJE as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HFR & HK & HMLE & HMOK & HEC & HP).
destruct HP as (HHB & HSR & R24 & R21 & R22 & R25 & R26 & V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 &
  SZnm & SZdp & HWOK & HR0).
destruct (KModel.n_r_cases (e_pl g)) as [Hr | Hr].
- apply (k_req g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2); [|exact Hr].
  unfold KH.
  split; [exact HJ|]. split; [exact HFR|]. split; [exact HK|]. split; [exact HMLE|]. split; [exact HMOK|].
  split; [exact HEC|]. split; [exact HHB|]. split; [exact HSR|]. split; [exact R24|]. split; [exact R21|].
  split; [exact R22|]. split; [exact R25|]. split; [exact R26|]. split; [exact V152|]. split; [exact V184|].
  split; [exact V144|]. split; [exact V128|]. split; [exact V120|]. split; [exact V176|]. split; [exact V160|].
  split; [exact V112|]. split; [exact SZnm|]. split; [exact SZdp|]. split; [exact HWOK|].
  split; [exact HR0 | exact Hr].
- exact (k_rne g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HJ HFR HK HMLE HMOK HEC HHB HSR R21 V152 V184 R24 Hr).
Qed.

Check (seg_K : seg_K_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
End c.
End b.
End a.

Print Assumptions seg_K.
