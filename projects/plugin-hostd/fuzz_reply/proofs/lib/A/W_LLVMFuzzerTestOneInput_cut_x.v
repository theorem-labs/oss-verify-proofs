(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of lib/A/W_LLVMFuzzerTestOneInput_cut.v (a Theorem Labs lane's step 1 of route
   (b)), from its owner's text at ebe8aee727b (sha256 fe8f8ac9b974; internal record: no sink token in fr_FP,
   G_fr writable not present, the FP over a block's request size, the fake frame's flag word). The AR file is NOT edited.
   W8's CHANGES since the emission (W8Entry-2, the one header round agreed with a Theorem Labs lane / ATopKeeper / DriverCF):
   fr_surv names the memories (alayout -> astate -> world -> mem -> alayout -> astate -> world -> mem -> Prop, the
   form ACfn_cf.v's memory-named fr_surv instantiates); the pre gains `LIBROOM S /\ NP S` after fr_live_pre and the
   post `NP S'` after fr_live_post (DriverCF's fr_lib_pre_drv / fr_lib_post_drv order; both Variables); Section w
   gains HP0 (the ghost set stays empty) beside LAWS.  Segment statements' bodies are unchanged; the bridges in
   Section br instantiate LIBROOM / NP := True and fr_surv with the memories ignored.
   - Section cf: fr_lib_pre_cf_x / fr_lib_post_cf_x / fr_lib_contract_cf_x, the program contract over a relation ARx
     with its ghost list (Hp at the entry, Hp' at the return; the instance's parameter is Hp = [] at both ends, an
     instantiation), the pre over YCbqG.afn_pre_x and the post's journal W_journal_x.ajournal_gx_x with its placement
     PST. Every other conjunct is the owner's text; fr_gi is cited.
   - Section w: the walk's skeleton over the generic journal: lf_base_x / lf_post_x / lcut_x / lf_jour_x / LF_x and the
     cut-point invariants INV_*_x take the entry's ghost list Hp beside the call context cx (the record lfcx is the
     owner's, unchanged); the AR-free cut-point facts (aframe_at, amodel_at, ainput_at, ablocks_sep, lregs_*, jt_rom,
     sv8, ...) are cited. SEG_JT is walked (lf_seg_jt_x, over W_journal_x's generic run chain and W_kit_x's
     paj_run_tok_x); the other segments are Section hypotheses, as in the owner's file; the composition lf_main_x and
     lf_contract_of_segments_x is the owner's proof.
   - Section br: at ARx := AR (Hp ignored), PST := [], fr_lib_pre_cf_x / fr_lib_post_cf_x are iff-equal to the owner's
     (W_journal_x.ajournal_gx_x_AR; afn_pre_x is afn_pre's text at that instance).
   OWNERSHIP: this file passes to W8 (W8Entry-2) once it is green. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
(* the zify flag as this file's own proofs expect it, whatever a Required file leaves (BUILD.md (sha256 a15bb0f1b85d; internal record) 'Tactic hygiene') *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section cf.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world tfibsegs -> (word -> option byte) -> alayout -> astate ->
  world tfibsegs ->
  (word -> option byte) -> Prop.
Variable LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Local Notation segs := tfibsegs.
Local Notation rd W mem := (mrestrict (w_H W) mem).
(* W_LLVMFuzzerTestOneInput_cut.v:182 fr_lib_pre_cf *)
Definition fr_lib_pre_cf_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
(mem : word -> option byte) (md : Model) (p n : Z) (pl : list byte) (M : Z) : Prop :=
afn_pre_x segs B ARx LLVMF_STK ly S Hp W regs mem md [] /\
raZ regs = RA_LLVMF /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ fr_live_pre S /\ LIBROOM S /\ NP S /\ fr_gi B G_fr ly S W mem /\
rom_view segs W mem /\
arodata_okS segs B RLO RHI (aview segs (w_H W) mem) /\
asink_none segs tfib_K (rd W mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
ameta_inv segs tfib_K ly (rd W mem) M /\
mo_ok MT S (XM_LIB n) /\
(* STKR: the caller's stack is readable from the entry's sp up to ly_top (a Theorem Labs lane's ruling 16:46Z / 18:16Z; W3's
   shared cnl_spec takes this text as its LAST premise, W_contract.v Section w3n on a working branch, read on
   image B and unused on A, so an A arm calling check_no_loss passes it: from here, kept by the journal's view clause
   above the callee's window).  Stated LAST so every positional destruct of the pre above it still binds; the
   driver supplies it from RelocA-2's AStkPres.v and StartupTrace's covered-range lemma. *)
(forall a, spZ regs <= a < ly_top ly -> aview segs (w_H W) mem a <> None) /\
(* HB (_cut.v's eighth clause, the one fr_hblks of _cut.v): the input block and the harness blocks are live and
   pairwise distinct.  Stated LAST, after STKR. *)
(List.NoDup ((if n =? 0 then [] else [(p, n)]) ++ fr_hblks W mem) /\ incl (fr_hblks W mem) (ablocks B ly S)) /\
(* XCNT (_cut.v's last clause, ReplyCnt.xcnt_ok): the entry's live blocks other than the input, the table and g_out are
   few.  Stated LAST, after HB. *)
(exists T0 c O mx cap out, ra_rel B fr_RG ly S W mem T0 [] /\ aout_at B fr_RG ly S W mem c O mx (Z.of_nat (length O)) cap out /\
  ReplyCnt.xcnt_ok B S ly (if n =? 0 then [] else [(p, n)]) T0 cap out) /\
(* CAPOUT (_cut.v's last clause): g_capout at most CAPOUT_MAX.  Stated LAST, after XCNT. *)
(exists c, val_mem segs (arm W mem) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).
(* W_LLVMFuzzerTestOneInput_cut.v:214 fr_lib_post_cf *)
Definition fr_lib_post_cf_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
(mem : word -> option byte) (md : Model) (p n : Z) (M : Z) (l : lleaf)
(ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte)
(md' : Model) (k : Z) : Prop :=
ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ regs) (fr_FP regs ly S W mem) ly S Hp W mem md []
  ly' S' Hp' W' mem' md' k /\ fr_live_post S S' k /\ NP S' /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
fr_surv ly S W mem ly' S' W' mem' /\ fr_gi B G_fr ly' S' W' mem' /\ rom_view segs W' mem' /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
asink_none segs tfib_K (rd W' mem') md' /\
ameta_inv segs tfib_K ly' (rd W' mem') M /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
(* HB at the return (_cut.v's post clause) *)
(List.NoDup (fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S')) /\
(* XCNT at the return (_cut.v's last post clause) *)
(exists T0 c O mx cap out, ra_rel B fr_RG ly' S' W' mem' T0 [] /\
  aout_at B fr_RG ly' S' W' mem' c O mx (Z.of_nat (length O)) cap out /\
  ReplyCnt.xcnt_ok B S' ly' (if n =? 0 then [] else [(p, n)]) T0 cap out) /\
(* CAPOUT at the return (_cut.v's last post clause) *)
(exists c, val_mem segs (arm W' mem') (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).
(* W_LLVMFuzzerTestOneInput_cut.v:234 fr_lib_contract_cf *)
Definition fr_lib_contract_cf_x : Prop :=
forall ly S Hp (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
fr_lib_pre_cf_x regs ly S Hp W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' Hp' regs' mem' md' k,
c' = cfg_at segs RA_LLVMF regs' mem' md' /\
fr_lib_post_cf_x regs ly S Hp W mem md p n M l ly' S' Hp' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the post and the contract at a world relation R.  At R := wle they are
   fr_lib_post_cf_x / fr_lib_contract_cf_x (the two _wle lemmas below, by reflexivity). *)
Section cfR.
Variable R : world segs -> world segs -> Prop.
(* W_LLVMFuzzerTestOneInput_cut.v:214 fr_lib_post_cf *)
Definition fr_lib_post_cf_xR (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
(mem : word -> option byte) (md : Model) (p n : Z) (M : Z) (l : lleaf)
(ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte)
(md' : Model) (k : Z) : Prop :=
ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ regs) (fr_FP regs ly S W mem) ly S Hp W mem md []
  ly' S' Hp' W' mem' md' k /\ fr_live_post S S' k /\ NP S' /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
fr_surv ly S W mem ly' S' W' mem' /\ fr_gi B G_fr ly' S' W' mem' /\ rom_view segs W' mem' /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
asink_none segs tfib_K (rd W' mem') md' /\
ameta_inv segs tfib_K ly' (rd W' mem') M /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
(* HB at the return (_cut.v's post clause) *)
(List.NoDup (fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S')) /\
(* XCNT at the return (_cut.v's last post clause) *)
(exists T0 c O mx cap out, ra_rel B fr_RG ly' S' W' mem' T0 [] /\
  aout_at B fr_RG ly' S' W' mem' c O mx (Z.of_nat (length O)) cap out /\
  ReplyCnt.xcnt_ok B S' ly' (if n =? 0 then [] else [(p, n)]) T0 cap out) /\
(* CAPOUT at the return (_cut.v's last post clause) *)
(exists c, val_mem segs (arm W' mem') (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).
(* W_LLVMFuzzerTestOneInput_cut.v:234 fr_lib_contract_cf *)
Definition fr_lib_contract_cf_xR : Prop :=
forall ly S Hp (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
fr_lib_pre_cf_x regs ly S Hp W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
R W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' Hp' regs' mem' md' k,
c' = cfg_at segs RA_LLVMF regs' mem' md' /\
fr_lib_post_cf_xR regs ly S Hp W mem md p n M l ly' S' Hp' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
End cfR.
Lemma fr_lib_post_cf_x_wle : fr_lib_post_cf_x = fr_lib_post_cf_xR (@wle segs). Proof. reflexivity. Qed.
Lemma fr_lib_contract_cf_x_wle : fr_lib_contract_cf_x = fr_lib_contract_cf_xR (@wle segs). Proof. reflexivity. Qed.
End cf.

(* ------------------------------------------------------------------ the walk's skeleton, over ARx *)
Section w.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* the instance's ghost poisoned-head set stays empty (a Theorem Labs lane's HP0 ruling, W_journal_x at 0c4d57d9bf1;
   fuzz_reply calls no poison routine): the driver reads the post's Hp' = [] from the journal's ARx through it *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
(* W_LLVMFuzzerTestOneInput_cut.v:328 errno_law over ARx *)
Definition errno_law_x : Prop :=
  forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md ->
  (exists v, val_mem segs (arm W mem) (as_errno B) 4 v /\ 0 <= v < 2 ^ 32) /\ awr W mem (as_errno B) 4.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
Local Notation AJG := (ajournal_gx_x segs B PST ARx G_fr 0 []).

(* :238 lf_base, :244 lf_post, over the entry's ghost list Hp *)
Definition lf_base_x (cx : lfcx) (Hp : list Z) : Prop :=
  AI segs (w_H (c_W cx)) (w_A (c_W cx)) (c_md cx) /\
  fr_lib_pre_cf_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx (c_regs cx) (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx)
    (c_md cx) (c_p cx) (c_n cx) (c_pl cx) (c_M cx).
Definition lf_post_x (cx : lfcx) (Hp : list Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' Hp' regs' mem' md' k,
    c' = cfg_at segs RA_LLVMF regs' mem' md' /\
    fr_lib_post_cf_x B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx (c_regs cx) (c_ly cx) (c_S cx) Hp (c_W cx)
      (c_mem cx) (c_md cx) (c_p cx) (c_n cx) (c_M cx) (LL 0 (m_fs (c_md cx)) []) ly' S' Hp' W' regs' mem' md' k.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* :339 lcut *)
Definition lcut_x (cx : lfcx) (Hp : list Z) (t : Z) (full : bool)
    (R : lmod -> Z -> bvmap 5 word -> world segs -> (word -> option byte) -> Prop)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (W : world segs) : Prop :=
  exists own ly3 S3 Hp3 k m fpos,
    AJG LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 Hp3 W mem md k /\
    own = [(1, fpos)] /\
    aframe_at cx full (frame_addr ly3 1 fpos) W mem /\
    sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    amodel_at B ly3 S3 W mem m /\ ainput_at B cx ly3 S3 W mem /\ rom_view segs W mem /\
    ablocks_sep B fr_FP cx m ly3 S3 /\ LSx cx t m ly3 S3 /\
    (* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d)): the allocator's room invariant NP (room_live_cf at the cf
       instance) at the cut's state, threaded from the entry's NP through every allocator call's post to the exit *)
    NP S3 /\
    RINV cx t m /\ R m (frame_addr ly3 1 fpos) regs W mem.
(* :409 LF *)
Definition LF_x (cx : lfcx) (Hp : list Z) (t : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (W : world segs) : Prop := lcut_x cx Hp t true (lregs_D B cx t) regs mem md W.
Lemma LF_stable_x : forall cx Hp t regs mem md W X,
  LF_x cx Hp t regs mem md W -> LF_x cx Hp t regs mem (with_vm_backing (m_vm_lazy md) X md) W.
Proof.
  intros cx Hp t regs mem md W X (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & HR).
  exists own, ly3, S3, Hp3, k, m, fpos. split; [|exact HR].
  apply (ajournal_gx_materialize_x segs B PST ARx LAWS pa_segs_low). exact HJ.
Qed.
(* :418 lf_jour *)
Definition lf_jour_x (cx : lfcx) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model) : Prop :=
  exists own ly3 S3 Hp3 k, AJG LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 Hp3 W mem md k.
(* WITNESS (b) over ARx: _cut.v's fr_hb_of_model with the block facts from AR_laws_x (alx_blocks, alx_sep).  The laws
   give no lower bound on a block's size, so a live block's 0 <= n is a premise (W_kit_x.v's BLKN text at this state;
   the cf instance proves it, W_LLVMFuzzerTestOneInput_top_x.v). *)
Lemma fr_hb_post_x : forall cx m ly S Hp (W : world segs) mem md rest,
  ARx ly S Hp W mem md ->
  (forall p n, In (p, n) (ablocks B ly S) -> 0 <= n) ->
  amodel_at B ly S W mem m ->
  Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
  List.NoDup (fr_hblks W mem) /\ incl (fr_hblks W mem) (ablocks B ly S).
Proof.
  intros cx m ly S Hp W mem md rest HAR HBN HM HP.
  assert (HBK : forall p n, In (p, n) (ablocks B ly S) -> 0 < p /\ p + req_size n <= alloc_ceiling)
    by (intros p n Hin; destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & H1 & H2 & _); lia).
  assert (HND : List.NoDup (ablocks B ly S)).
  { assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
    { apply Forall_forall. intros [p n] Hin. cbn [snd].
      pose proof (req_size_pos n (HBN p n Hin)) as [Hq _]. exact Hq. }
    destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hpw _]. apply pairwise_app_l in Hpw as [Hpw _].
    clear - Hpos Hpw. revert Hpos Hpw. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hpw; [constructor|].
    inversion Hpos as [|b0 l0 Hb Hl]; subst.
    cbn [map pairwise] in Hpw. destruct Hpw as [Hf Hpw]. constructor; [|exact (IH Hl Hpw)].
    intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
    unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia. }
  destruct (fr_hb_of_model B cx m ly S W mem rest HBK HND HM HP) as (_ & H1 & H2). split; assumption.
Qed.
(* :429-448 the cut points' invariants *)
Definition INV_H_x (cx : lfcx) (Hp : list Z) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_LLVM_head) regs mem md /\
    jt_rom W mem /\ lcut_x cx Hp t true (lregs_H B cx t) regs mem md W.
Definition INV_D_x (cx : lfcx) (Hp : list Z) (t op : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_LLVM_dispatch) regs mem md /\
    getr regs 11 = w64 op /\ lf_jour_x cx Hp W mem md /\ jt_rom W mem /\ LF_x cx Hp t regs mem md W.
Definition INV_A_x (i : Z) (cx : lfcx) (Hp : list Z) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs regsD mem md, c = cfg_at segs (fr_B0 + fr_arm i) regs mem md /\
    (forall r, In r jt_kept -> getr regs r = getr regsD r) /\ getr regsD 11 = w64 i /\
    lf_jour_x cx Hp W mem md /\ jt_rom W mem /\ LF_x cx Hp t regsD mem md W.
Definition INV_K_x (cx : lfcx) (Hp : list Z) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_LLVM_latch) regs mem md /\
    jt_rom W mem /\ lcut_x cx Hp (t + 1) true (lregs_K B cx t) regs mem md W.
Definition INV_X_x (cx : lfcx) (Hp : list Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md t, c = cfg_at segs (fr_B0 + AF_LLVM_exit) regs mem md /\
    jt_rom W mem /\ lcut_x cx Hp t false (fun m FF => lregs_X B cx t m FF) regs mem md W.

(* :514 SEG_JT walked, over the generic chain *)
Ltac lf_close_x HLF :=
  first [ exact HLF | apply LF_stable_x; lf_close_x HLF ].
(* :512 jt_mem, a Section-local Ltac of the owner's file (dropped at its End w), restated *)
Ltac jt_mem HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the walk's skeleton at a world relation R.  The cut journal runs from the
   entry, so across earlier operations' frees / reallocs; at R := wle' segs RZ_cf it is the re-hiding form.  At
   R := wle every text below is its strict twin above / below by conversion (ajournal_gx_x_wle, SRrG at wle is SRr). *)
Section wR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Let RUNR := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Local Notation AJGR := (ajournal_gx_xR segs B PST ARx R G_fr 0 []).
Definition lf_post_xR (cx : lfcx) (Hp : list Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' Hp' regs' mem' md' k,
    c' = cfg_at segs RA_LLVMF regs' mem' md' /\
    fr_lib_post_cf_xR B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx R (c_regs cx) (c_ly cx) (c_S cx) Hp (c_W cx)
      (c_mem cx) (c_md cx) (c_p cx) (c_n cx) (c_M cx) (LL 0 (m_fs (c_md cx)) []) ly' S' Hp' W' regs' mem' md' k.
(* :339 lcut *)
Definition lcut_xR (cx : lfcx) (Hp : list Z) (t : Z) (full : bool)
    (RC : lmod -> Z -> bvmap 5 word -> world segs -> (word -> option byte) -> Prop)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (W : world segs) : Prop :=
  exists own ly3 S3 Hp3 k m fpos,
    AJGR LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 Hp3 W mem md k /\
    own = [(1, fpos)] /\
    aframe_at cx full (frame_addr ly3 1 fpos) W mem /\
    sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    amodel_at B ly3 S3 W mem m /\ ainput_at B cx ly3 S3 W mem /\ rom_view segs W mem /\
    ablocks_sep B fr_FP cx m ly3 S3 /\ LSx cx t m ly3 S3 /\
    (* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d)): the allocator's room invariant NP (room_live_cf at the cf
       instance) at the cut's state, threaded from the entry's NP through every allocator call's post to the exit *)
    NP S3 /\
    RINV cx t m /\ RC m (frame_addr ly3 1 fpos) regs W mem.
(* :409 LF *)
Definition LF_xR (cx : lfcx) (Hp : list Z) (t : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (W : world segs) : Prop := lcut_xR cx Hp t true (lregs_D B cx t) regs mem md W.
Lemma LF_stable_xR : forall cx Hp t regs mem md W X,
  LF_xR cx Hp t regs mem md W -> LF_xR cx Hp t regs mem (with_vm_backing (m_vm_lazy md) X md) W.
Proof.
  intros cx Hp t regs mem md W X (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & HR).
  exists own, ly3, S3, Hp3, k, m, fpos. split; [|exact HR].
  apply (ajournal_gx_materialize_xR segs B PST ARx LAWS pa_segs_low). exact HJ.
Qed.
(* :418 lf_jour *)
Definition lf_jour_xR (cx : lfcx) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model) : Prop :=
  exists own ly3 S3 Hp3 k, AJGR LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 Hp3 W mem md k.
(* :429-448 the cut points' invariants *)
Definition INV_H_xR (cx : lfcx) (Hp : list Z) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_LLVM_head) regs mem md /\
    jt_rom W mem /\ lcut_xR cx Hp t true (lregs_H B cx t) regs mem md W.
Definition INV_D_xR (cx : lfcx) (Hp : list Z) (t op : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_LLVM_dispatch) regs mem md /\
    getr regs 11 = w64 op /\ lf_jour_xR cx Hp W mem md /\ jt_rom W mem /\ LF_xR cx Hp t regs mem md W.
Definition INV_A_xR (i : Z) (cx : lfcx) (Hp : list Z) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs regsD mem md, c = cfg_at segs (fr_B0 + fr_arm i) regs mem md /\
    (forall r, In r jt_kept -> getr regs r = getr regsD r) /\ getr regsD 11 = w64 i /\
    lf_jour_xR cx Hp W mem md /\ jt_rom W mem /\ LF_xR cx Hp t regsD mem md W.
Definition INV_K_xR (cx : lfcx) (Hp : list Z) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_LLVM_latch) regs mem md /\
    jt_rom W mem /\ lcut_xR cx Hp (t + 1) true (lregs_K B cx t) regs mem md W.
Definition INV_X_xR (cx : lfcx) (Hp : list Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md t, c = cfg_at segs (fr_B0 + AF_LLVM_exit) regs mem md /\
    jt_rom W mem /\ lcut_xR cx Hp t false (fun m FF => lregs_X B cx t m FF) regs mem md W.
Ltac lf_close_xR HLF :=
  first [ exact HLF | apply LF_stable_xR; lf_close_xR HLF ].
Theorem lf_seg_jt_xR : forall cx Hp t op W c, lf_base_x cx Hp -> 0 <= op <= 9 -> INV_D_xR cx Hp t op W c ->
  SRrG segs R W c (INV_A_xR op cx Hp t).
Proof.
  intros cx Hp t op W c HB Rop (regs & mem & md & -> & Hop & (own & ly3 & S3 & Hp3 & k & HJ) & HROM & HLF).
  (* the segment moves no world: its strict walk, over the R journal (paj_run_x_xR), lifts to R *)
  apply (SRr_SRrG segs R WLE_R).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  destruct (jt_entry W regs mem op Hop Rop HROM) as [HS SHOK].
  remember (Eimg (Ereg regs jt_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E11 : ew E 11 = Z_to_bv 64 op)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact Hop).
  assert (EJ : ew E 268 = Z_to_bv 64 fr_jtab)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); exact (f_equal (Z_to_bv 64) VAL_jtab)).
  assert (HAE : env_agree 32 (Ereg regs jt_extra) E)
    by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_dispatch)) with (Z_to_bv 64 (BASE + AF_LLVM_dispatch)).
  (* li a0, 8 *)
  paj_run_tok_x RUNR HS HJ SHOK JBspan.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  jt_mem HF Em1. clear HF HFr HG0.
  (* bltu a0, a1: op > 8 goes to the default arm *)
  psrr_branch_tok RUNR BR HS SHOK JBspan.
  - assert (Hop9 : op = 9).
    { rewrite branch_ltu_U, (U_lit E 8), (U_atom E 11 op E11) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
    subst op.
    paj_run_to_tok_x RUNTOR HS HJ SHOK JBspan AF_arm_default.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    jt_mem HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs jt_extra jt_kept HS HAE ltac:(vm_compute; reflexivity)) as KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret.
    lazymatch goal with |- INV_A_xR _ _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} =>
      exists r, regs, mem, d end.
    split; [reflexivity|].
    split; [intros r Hr; exact (KR r Hr)|]. split; [exact Hop|].
    split; [exists own, ly3, S3, Hp3, k; exact HJ|].
    split; [exact HROM|].
    lf_close_xR HLF.
  - assert (Hop8 : op <= 8).
    { rewrite branch_ltu_U, (U_lit E 8), (U_atom E 11 op E11) in Hc by lia. apply Z.ltb_ge in Hc. lia. }
    prreg HS (11%bv : bv 5) R11. rewrite E11 in R11.
    assert (Hc9 : op = 0 \/ op = 1 \/ op = 2 \/ op = 3 \/ op = 4 \/ op = 5 \/ op = 6 \/ op = 7 \/ op = 8) by lia.
    destruct Hc9 as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]].
    all: pose proof (st_ok_pi_pin_reg' (PI := PB_fr) _ _ _ (11%bv) _ HS R11 eq_refl) as HS2; clear HS; rename HS2 into HS.
    all: cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
    all: paj_run_tok_x RUNR HS HJ SHOK JBspan;
      [ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil] |].
    all: jt_mem HF Em2.
    all: pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs jt_extra jt_kept HS HAE ltac:(vm_compute; reflexivity)) as KR.
    all: prreg HS (10%bv : bv 5) R10.
    all: rewrite EJ, unsigned_lit_small in R10 by (unfold fr_jtab; lia).
    (* jr a0, to fr_jtab + the table word = the arm *)
    all: eapply (SRr_jr_pi (PL := PL_fr) (PI := PB_fr) W E _ _ _ _ 327783 (10%bv : bv 5) _ HS eq_refl);
      [ vm_compute; reflexivity | vm_refl_bv | exact R10 | unfold fr_jtab; lia
      | vm_compute; reflexivity | ].
    all: intros mat' ms1 -> _.
    all: rewrite Em2 in *; rewrite Em1 in *.
    all: apply SRr_ret.
    all: lazymatch goal with |- INV_A_xR _ _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} =>
      exists r, regs, mem, d end.
    all: split; [reflexivity|].
    all: split; [intros r Hr; exact (KR r Hr)|]. all: split; [exact Hop|].
    all: rewrite wvb_collapse in HJ.
    all: split; [exists own, ly3, S3, Hp3, k; apply (ajournal_gx_materialize_xR segs B PST ARx LAWS Hsegs); exact HJ|].
    all: split; [exact HROM|].
    all: lf_close_xR HLF.
Qed.
Definition SEG_JT_xR := lf_seg_jt_xR.
(* :586-616 the segments, as Section hypotheses over the generic invariants *)
Hypothesis SEG_PRO_R : forall cx Hp, lf_base_x cx Hp ->
  SRrG segs R (c_W cx) (lf_entry cx) (fun W' c' => INV_H_xR cx Hp 0 W' c' \/ INV_X_xR cx Hp W' c').
Hypothesis SEG_HEAD_R : forall cx Hp t W c, lf_base_x cx Hp -> INV_H_xR cx Hp t W c ->
  SRrG segs R W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_xR cx Hp t op W' c') \/ INV_A_xR 1 cx Hp t W' c' \/
    INV_H_xR cx Hp (t + 1) W' c' \/ INV_X_xR cx Hp W' c').
Hypothesis ARM_add_R : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_xR 0 cx Hp t W c -> SRrG segs R W c (INV_K_xR cx Hp t).
Hypothesis ARM_write_R : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_xR 1 cx Hp t W c -> SRrG segs R W c (INV_K_xR cx Hp t).
Hypothesis ARM_drain_R : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_xR 2 cx Hp t W c -> SRrG segs R W c (INV_K_xR cx Hp t).
Hypothesis ARM_close_R : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_xR 3 cx Hp t W c -> SRrG segs R W c (INV_K_xR cx Hp t).
Hypothesis ARM_remove_R : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_xR 4 cx Hp t W c -> SRrG segs R W c (INV_K_xR cx Hp t).
Hypothesis ARM_gone_R : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_xR 5 cx Hp t W c -> SRrG segs R W c (INV_K_xR cx Hp t).
Hypothesis ARM_eintr_R : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_xR 6 cx Hp t W c -> SRrG segs R W c (INV_K_xR cx Hp t).
Hypothesis ARM_event_R : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_xR 7 cx Hp t W c -> SRrG segs R W c (INV_K_xR cx Hp t).
Hypothesis ARM_sendmax_R : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_xR 8 cx Hp t W c -> SRrG segs R W c (INV_K_xR cx Hp t).
Hypothesis ARM_default_R : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_xR 9 cx Hp t W c -> SRrG segs R W c (INV_K_xR cx Hp t).
Hypothesis SEG_LATCH_R : forall cx Hp t W c, lf_base_x cx Hp -> INV_K_xR cx Hp t W c ->
  SRrG segs R W c (fun W' c' => INV_H_xR cx Hp (t + 1) W' c' \/ INV_X_xR cx Hp W' c').
Lemma H_BOUND_xR : forall cx Hp t W c, INV_H_xR cx Hp t W c -> 0 <= t < OPS_MAX.
Proof.
  intros cx Hp t W c (regs & mem & md & _ & _ & (own & ly3 & S3 & Hp3 & k & m & fpos & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HR)).
  destruct HR as (_ & _ & _ & _ & _ & _ & Ht & _). exact Ht.
Qed.
Hypothesis SEG_EXIT_R : forall cx Hp W c, lf_base_x cx Hp -> INV_X_xR cx Hp W c -> SRrG segs R W c (lf_post_xR cx Hp).

(* :619-667 the composition, the owner's proof *)
Lemma lf_arm_xR : forall cx Hp t op W c, lf_base_x cx Hp -> 0 <= op <= 9 -> INV_A_xR op cx Hp t W c ->
  SRrG segs R W c (INV_K_xR cx Hp t).
Proof.
  intros cx Hp t op W c HB Hop HA.
  assert (op = 0 \/ op = 1 \/ op = 2 \/ op = 3 \/ op = 4 \/ op = 5 \/ op = 6 \/ op = 7 \/ op = 8 \/ op = 9) as Hc by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]].
  - exact (ARM_add_R cx Hp t W c HB HA).
  - exact (ARM_write_R cx Hp t W c HB HA).
  - exact (ARM_drain_R cx Hp t W c HB HA).
  - exact (ARM_close_R cx Hp t W c HB HA).
  - exact (ARM_remove_R cx Hp t W c HB HA).
  - exact (ARM_gone_R cx Hp t W c HB HA).
  - exact (ARM_eintr_R cx Hp t W c HB HA).
  - exact (ARM_event_R cx Hp t W c HB HA).
  - exact (ARM_sendmax_R cx Hp t W c HB HA).
  - exact (ARM_default_R cx Hp t W c HB HA).
Qed.
Lemma lf_iter_xR : forall cx Hp t W c, lf_base_x cx Hp -> INV_H_xR cx Hp t W c ->
  SRrG segs R W c (fun W' c' => INV_H_xR cx Hp (t + 1) W' c' \/ INV_X_xR cx Hp W' c').
Proof.
  intros cx Hp t W c HB HH.
  eapply (SRrG_bind segs R R_trans); [exact (SEG_HEAD_R cx Hp t W c HB HH)|].
  intros W1 c1 _ [(op & Hop & HD) | [HA | HHX]].
  - eapply (SRrG_bind segs R R_trans); [exact (SEG_JT_xR cx Hp t op W1 c1 HB Hop HD)|].
    intros W2 c2 _ HA. eapply (SRrG_bind segs R R_trans); [exact (lf_arm_xR cx Hp t op W2 c2 HB Hop HA)|].
    intros W3 c3 _ HK. exact (SEG_LATCH_R cx Hp t W3 c3 HB HK).
  - eapply (SRrG_bind segs R R_trans); [exact (ARM_write_R cx Hp t W1 c1 HB HA)|].
    intros W3 c3 _ HK. exact (SEG_LATCH_R cx Hp t W3 c3 HB HK).
  - exact (SRrG_ret segs R R_refl W1 c1 _ HHX).
Qed.
Lemma lf_loop_xR : forall cx Hp, lf_base_x cx Hp -> forall (m : nat) t W c, OPS_MAX - t <= Z.of_nat m ->
  INV_H_xR cx Hp t W c -> SRrG segs R W c (lf_post_xR cx Hp).
Proof.
  intros cx Hp HB m. induction m as [|m IH]; intros t W c Hm HH.
  - pose proof (H_BOUND_xR cx Hp t W c HH) as Ht. cbn in Hm. lia.
  - pose proof (H_BOUND_xR cx Hp t W c HH) as Ht.
    eapply (SRrG_bind segs R R_trans); [exact (lf_iter_xR cx Hp t W c HB HH)|].
    intros W' c' _ [HH' | HX].
    + apply (IH (t + 1) W' c'); [rewrite Nat2Z.inj_succ in Hm; lia | exact HH'].
    + exact (SEG_EXIT_R cx Hp W' c' HB HX).
Qed.
Theorem lf_main_xR : forall cx Hp, lf_base_x cx Hp -> SRrG segs R (c_W cx) (lf_entry cx) (lf_post_xR cx Hp).
Proof.
  intros cx Hp HB.
  eapply (SRrG_bind segs R R_trans); [exact (SEG_PRO_R cx Hp HB)|].
  intros W' c' _ [HH | HX].
  - exact (lf_loop_xR cx Hp HB (Z.to_nat OPS_MAX) 0 W' c' ltac:(unfold OPS_MAX; lia) HH).
  - exact (SEG_EXIT_R cx Hp W' c' HB HX).
Qed.
Theorem lf_contract_of_segments_xR :
  @fr_lib_contract_cf_xR fx rc checksum_shape B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr
    fr_FP PST ARx R.
Proof.
  intros ly S Hp W regs mem md p n pl M K HAI HPRE HK.
  change tfibsegs with segs in *.
  change (LIBK pl (m_fs md) K) with (K (LL 0 (m_fs md) [])).
  eapply (SRrG_srealizes segs R); [exact (lf_main_xR (LFCX ly S W regs mem md p n pl M) Hp (conj HAI HPRE)) | exact HAI |].
  intros W' c' HR HAI' (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HP).
  apply (HK (LL 0 (m_fs md) []) W' c' HR HAI'). exists ly', S', Hp', regs', mem', md', k. split; [exact Hc | exact HP].
Qed.
End wR.
(* the strict texts below are the R section's at R := wle (route R's rule: one walk text): each R premise at wle is
   the strict hypothesis of the same name, and the three laws hold for wle *)
Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].
Theorem lf_seg_jt_x : forall cx Hp t op W c, lf_base_x cx Hp -> 0 <= op <= 9 -> INV_D_x cx Hp t op W c ->
  SRr segs W c (INV_A_x op cx Hp t).
Proof. eapply (lf_seg_jt_xR (@wle segs)); wle_inst. Qed.
Definition SEG_JT_x := lf_seg_jt_x.

(* :586-616 the segments, as Section hypotheses over the generic invariants *)
Hypothesis SEG_PRO : forall cx Hp, lf_base_x cx Hp ->
  SRr segs (c_W cx) (lf_entry cx) (fun W' c' => INV_H_x cx Hp 0 W' c' \/ INV_X_x cx Hp W' c').
Hypothesis SEG_HEAD : forall cx Hp t W c, lf_base_x cx Hp -> INV_H_x cx Hp t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_x cx Hp t op W' c') \/ INV_A_x 1 cx Hp t W' c' \/
    INV_H_x cx Hp (t + 1) W' c' \/ INV_X_x cx Hp W' c').
Hypothesis ARM_add : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_x 0 cx Hp t W c -> SRr segs W c (INV_K_x cx Hp t).
Hypothesis ARM_write : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_x 1 cx Hp t W c -> SRr segs W c (INV_K_x cx Hp t).
Hypothesis ARM_drain : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_x 2 cx Hp t W c -> SRr segs W c (INV_K_x cx Hp t).
Hypothesis ARM_close : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_x 3 cx Hp t W c -> SRr segs W c (INV_K_x cx Hp t).
Hypothesis ARM_remove : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_x 4 cx Hp t W c -> SRr segs W c (INV_K_x cx Hp t).
Hypothesis ARM_gone : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_x 5 cx Hp t W c -> SRr segs W c (INV_K_x cx Hp t).
Hypothesis ARM_eintr : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_x 6 cx Hp t W c -> SRr segs W c (INV_K_x cx Hp t).
Hypothesis ARM_event : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_x 7 cx Hp t W c -> SRr segs W c (INV_K_x cx Hp t).
Hypothesis ARM_sendmax : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_x 8 cx Hp t W c -> SRr segs W c (INV_K_x cx Hp t).
Hypothesis ARM_default : forall cx Hp t W c, lf_base_x cx Hp -> INV_A_x 9 cx Hp t W c -> SRr segs W c (INV_K_x cx Hp t).
Hypothesis SEG_LATCH : forall cx Hp t W c, lf_base_x cx Hp -> INV_K_x cx Hp t W c ->
  SRr segs W c (fun W' c' => INV_H_x cx Hp (t + 1) W' c' \/ INV_X_x cx Hp W' c').
Lemma H_BOUND_x : forall cx Hp t W c, INV_H_x cx Hp t W c -> 0 <= t < OPS_MAX.
Proof. eapply (H_BOUND_xR (@wle segs)); wle_inst. Qed.
Hypothesis SEG_EXIT : forall cx Hp W c, lf_base_x cx Hp -> INV_X_x cx Hp W c -> SRr segs W c (lf_post_x cx Hp).

(* :619-667 the composition, the owner's proof *)
Lemma lf_arm_x : forall cx Hp t op W c, lf_base_x cx Hp -> 0 <= op <= 9 -> INV_A_x op cx Hp t W c ->
  SRr segs W c (INV_K_x cx Hp t).
Proof. eapply (lf_arm_xR (@wle segs)); wle_inst. Qed.
Lemma lf_iter_x : forall cx Hp t W c, lf_base_x cx Hp -> INV_H_x cx Hp t W c ->
  SRr segs W c (fun W' c' => INV_H_x cx Hp (t + 1) W' c' \/ INV_X_x cx Hp W' c').
Proof. eapply (lf_iter_xR (@wle segs)); wle_inst. Qed.
Lemma lf_loop_x : forall cx Hp, lf_base_x cx Hp -> forall (m : nat) t W c, OPS_MAX - t <= Z.of_nat m ->
  INV_H_x cx Hp t W c -> SRr segs W c (lf_post_x cx Hp).
Proof. eapply (lf_loop_xR (@wle segs)); wle_inst. Qed.
Theorem lf_main_x : forall cx Hp, lf_base_x cx Hp -> SRr segs (c_W cx) (lf_entry cx) (lf_post_x cx Hp).
Proof. eapply (lf_main_xR (@wle segs)); wle_inst. Qed.
Theorem lf_contract_of_segments_x :
  @fr_lib_contract_cf_x fx rc checksum_shape B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr
    fr_FP PST ARx.
Proof. eapply (lf_contract_of_segments_xR (@wle segs)); wle_inst. Qed.
End w.

(* THE BRIDGES: at ARx := AR (Hp ignored) and PST := [], the generic pre and post are the owner's. *)
Section br.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> list (Z * Z).
Local Notation ARi := (fun ly S (_ : list Z) W mem md => AR tfibsegs B ly S W mem md).
(* the x-contract's three additions are trivial on the AR side: LIBROOM and NP are True, and fr_surv ignores the
   memories *)
Local Notation T1 := (fun _ : astate => True).
Local Notation SV := (fun ly S (_ : world tfibsegs) (_ : word -> option byte) ly' S' (_ : world tfibsegs)
  (_ : word -> option byte) => fr_surv ly S ly' S').
Lemma fr_lib_pre_cf_x_AR : forall regs ly S Hp W mem md p n pl M,
  fr_lib_pre_cf_x B MT XM_LIB RLO RHI fr_live_pre T1 T1 G_fr ARi regs ly S Hp W mem md p n pl M <->
  fr_lib_pre_cf B MT XM_LIB RLO RHI fr_live_pre G_fr regs ly S W mem md p n pl M.
Proof.
  intros. unfold fr_lib_pre_cf_x, fr_lib_pre_cf. cbv beta.
  split; intros (H1 & H2); (split; [exact H1 | tauto]).
Qed.
Lemma fr_lib_post_cf_x_AR : forall regs ly S Hp W mem md p n M l ly' S' Hp' W' regs' mem' md' k,
  fr_lib_post_cf_x B MT XN_LIB fr_live_post SV T1 G_fr fr_FP [] ARi regs ly S Hp W mem md p n M l ly' S' Hp' W'
    regs' mem' md' k <->
  fr_lib_post_cf B MT XN_LIB fr_live_post fr_surv G_fr fr_FP regs ly S W mem md p n M l ly' S' W' regs' mem' md' k.
Proof.
  intros. unfold fr_lib_post_cf_x, fr_lib_post_cf. cbv beta. split; intros (HJ & HR); split; try tauto.
  - exact (proj1 (ajournal_gx_x_AR tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) HJ).
  - exact (proj2 (ajournal_gx_x_AR tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) HJ).
Qed.
End br.
