(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102L0A.v, with its module paths changed; 517 of its 1128 lines of code are new or changed and 23 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, PIN sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44): segments L0a and L0b of the walk of
   LLVMFuzzerTestOneInput (A' 0x815e0, 201 instructions).
   LISTING: lib/A/Listing_prog.v (a Theorem Labs lane's whole-program listing of A', blob 7ed1529926bd), with the PAListing
   lib/A/Ent102PLA.v (blob a55fa7414ddf, PL_102_A); the image half stays PARAMETRIC ({PA : PAImg A_prog_listing}):
   this file imports no PAImg instance and computes no pa_val / pa_sigma; image facts come from ec_img only.
   STATEMENT: lib/A/Ent102CutsA.v (blob 2fb50b636f51 at the CUT IN FLIGHT kit
   sync to the kit of record (lib/A/PRH_Base.v, below), statements = CUT STABLE: THE EXACT ROOM POSITION record (section 6, ec_inv),
   prh_ledger's arity in lib/A/PRH_Base.v, the run's data words e_dw, since dropped): seg_L0a_stmt / seg_L0b_stmt,
   now each over `ec_hyps` (no data words); the count / live budgets of cut_frame / cut_s1 / cut_exit come from the record laws
   ech_ccut_ok / ech_lcut_ok (bound at 0, antitone in the cut index). RE-FIT on it from this file's proof on
   9a4f89c34639 (66a3e722272f); the re-fit follows the shapes of the B' twin lib/AU/Prog/Ent102L0B.v
   (blob 7c480089ab0e, green on the CUT STABLE statements; A' and B' differ only in pc-relative
   words, which the engine runs symbolically), which is not imported. ec_pre / ec_inv are read BY NAME (section 2':
   lib/A/Prog/Ent102CallA.v's projections, blob aefcab75548d, where it has one, else the l0_pre_* / l0_inv_*
   projections picked by type with its ec_conj_pick), never by position; the ledger is
   `exists most own, prh_ledger .. most own` in ec_pre and ec_inv, and l0_glob_keep carries g_most / g_own_ran_out
   as PST cells. cut_frame / cut_s1 are at the entry index e_i0 over e_os (ec_pre's own position, unchanged by L0,
   which makes no model event); the size guard's EXIT arm (n > PRESET_FILE_MAX_BYTES = MAXB) is at e_os ++ [trp] and
   e_i0 + |ec_call_evs E trp| with trp := (None, None, None): call_evs is [] above MAXB (PresetRun.call_evs_blocks),
   and ec_pre's index tie e_i0 = |hruns e_os| lets lib/A/Ent102PosA.v's ec_pos_extend (blob fd7e26dd0721) carry the
   position (l0_pos_exit; Ent102PosA has no lemma of its form). L0 makes no grant and reads no ledger cell of a
   callee, so neither lib/A/Prog/Ent102GrantA.v nor CallA's ec_ledger_cells is used, and no copy of either is here.
   TEXT blobs read from the kit of record: lib/A/PRH_Base.v fdb45545469b (prh_ledger / prh_glob /
   prh_most / prh_own / prh_pst, ledger read through its named projection prh_ledger_glob). L0 calls no kit callee,
   so no kit function text is used here.
   ENGINE: YC80x / YC1fPx's memnorm-carrying runners paj_run_to_x_inv / paj_run_x_inv (YC1fPx.v 7814b594066f) at
   P := memnorm (YSRrMemnorm.srr_inv_laws_memnorm_k), over YCbqG's ajournal_x at ARX := ARcf /\ xs_placed_cf
   (ec_ARx); the frame call is YGcallMxmn.aj_stack_malloc_at_xm (YGcallMxmn.v b47cf7942c3d), the memnorm-keeping
   twin of YGcallSx.aj_stack_malloc_at_x, with ec_frame_area's ec_stack_malloc_cfm as its text; count_cid is
   discharged from ec_pre's frames S = []. The three conditional branches of L0 (the option test `beqz a2` at
   +0x068 and `bnez s2` at +0x084 inside the runs, the size guard `bltu a0, s3` at +0x120 by psrr_branch_tok) are
   symbolic-run steps of the engine; no listing-slot branch lemma is used.
   Image-free arithmetic ported BY PATH from a working branch d63027f077c5 lib/A/H6_Base.v
   (h6_land_m32 / h6_and_m32 / h6_val_mem_of_rd32 as l0_land_m32 / l0_and_m32 / l0_val_mem_of_rd32; h6_alias_U
   as l1_alias_U).
   rule 24: proves function LLVMFuzzerTestOneInput, segments L0a / L0b (reuse search
   the lane's index output, the internal file idx-llvm-newpin.txt exit=0; NEW walk on the #102 pins; checker R24CheckLLVMF
   CONFIRM). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YImgTop YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf YGcfRoomPre YGcfRoomKeep YG0lawscf YGcfExtra.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcallx YGcallcf FCiface YGcallSx YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
(* Required, not Imported: YGcallMxmn carries its own copies of in_roP / arodata_okP (its header) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog Ent102PLA Ent102CutsA.
(* Required, not Imported: ec_pos_extend (Ent102PosA) and the shared A' call-site file's projections and its
   ec_conj_pick (Ent102CallA) are cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Ent102PosA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Ent102CallA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Image-free arithmetic the prologue needs (ported BY PATH from a working branch d63027f077c5,
      lib/A/H6_Base.v:66-98 h6_land_m32 / h6_and_m32 / h6_add0, and :41-47 h6_val_mem_of_rd32; the old image's
      numbers are not carried, only these pure lemmas). *)
Lemma l0_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = x / 32 * 32.
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.shiftl (Z.ones 59) 5) by (vm_compute; reflexivity).
assert (E2 : x / 32 * 32 = Z.shiftl (Z.shiftr x 5) 5)
  by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
rewrite E1, E2. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.shiftl_spec by lia.
destruct (Z.lt_ge_cases i 5) as [H5|H5].
- rewrite !(Z.testbit_neg_r _ (i - 5)) by lia. apply Bool.andb_false_r.
- rewrite Z.shiftr_spec by lia. replace (i - 5 + 5) with i by lia.
  destruct (Z.lt_ge_cases (i - 5) 59) as [H59|H59].
  + rewrite Z.ones_spec_low by lia. apply Bool.andb_true_r.
  + rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r.
    rewrite <- (Z.mod_small x (2 ^ 64)) by lia. symmetry. apply Z.mod_pow2_bits_high. lia.
Qed.
Lemma l0_and_m32 : forall x, 0 <= x < 2 ^ 64 ->
  alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 (-32)) = Z_to_bv 64 (x / 32 * 32).
Proof.
intros x Hx. unfold alu64, alu. cbn. apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite (Z.mod_small x) by lia.
replace ((-32) mod 2 ^ 64) with (2 ^ 64 - 32) by reflexivity. rewrite l0_land_m32 by exact Hx.
pose proof (Z.div_pos x 32 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le x 32 ltac:(lia)).
rewrite Z.mod_small by lia. reflexivity.
Qed.
(* the prologue's `andi sp, sp, -32` as the statement writes it (ec_A = Z.land (sp0 - 128) (-32)) *)
Lemma l0_land_neg32 : forall x, 0 <= x -> Z.land x (-32) = x / 32 * 32.
Proof.
intros x Hx.
assert (E2 : x / 32 * 32 = Z.shiftl (Z.shiftr x 5) 5)
  by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
assert (E1 : (-32) = Z.lnot (Z.ones 5)) by (vm_compute; reflexivity).
rewrite E1, E2. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.shiftl_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases i 5) as [H5|H5].
- rewrite (Z.testbit_neg_r _ (i - 5)) by lia. rewrite Z.ones_spec_low by lia. apply Bool.andb_false_r.
- rewrite Z.ones_spec_high by lia. rewrite Bool.andb_true_r.
  rewrite Z.shiftr_spec by lia. f_equal. lia.
Qed.

(* the byte view of a 4-byte little-endian read as a value read (H6_Base.v:41-47 by path) *)
Lemma l0_val_mem_of_rd32 : forall (segs : list Segment) H mem a v,
  rd32 (aview segs H mem) a v -> val_mem segs (mrestrict H mem) a 4 v.
Proof.
intros segs H mem a v Hr k Hk. specialize (Hr k Hk). unfold aview in Hr.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn [option_map] in Hr; [|discriminate Hr].
injection Hr as Hb. f_equal. cbv [YO0f.le_byte YG0f.le_byte] in *. rewrite <- Hb. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Section D.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PI : PrhImg} {RL : PrhRoomLive}.
Context {PA : @PAImg rc A_prog_listing}.
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation VAL := (@pa_val rc A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst PI).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
Variables ec_ccut ec_lcut : ecx -> nat -> Z.

#[local] Notation ARX := (fun ly S Hp W mem md => ARcf (cp := cp) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).

(* ---------------------------------------------------------------------- *)
(* 2'. ec_pre's and ec_inv's parts BY NAME. lib/A/Prog/Ent102CallA.v (blob aefcab75548d) gives ec_pre_payload /
      ec_pre_len / ec_pre_bytes / ec_pre_pay8 and ec_inv_ledger / ec_inv_pre / ec_inv_pay / ec_inv_perm /
      ec_inv_bytes; they are cited from there. The parts it does not give are projected here the same way, with its
      ec_conj_pick: split the definition's top-level conjunctions, pick the conjunct by TYPE. No proof below depends
      on a conjunct's position in ec_pre or ec_inv. *)
#[local] Notation ECX := (@ecx rc A_prog_listing PA).
#[local] Notation ECPRE := (@ec_pre fx rc ci cp PI RL A_prog_listing PA B EC_RA EC_EMPTY EC_SIO).
#[local] Notation ECINV := (@ec_inv fx rc ci cp PI RL A_prog_listing PA B SK EC_RA EC_EMPTY EC_SIO).
#[local] Notation ARC := (@ec_ARx rc ci cp A_prog_listing PA B).

Lemma l0_pre_afn : forall {E : ECX}, ECPRE E ->
  afn_pre_x SEGS B ARC LLVMF_STK (e_ly E) (e_S E) [] (e_W E) (e_regs E) (e_mem E) (e_md E) [].
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_s0 : forall {E : ECX}, ECPRE E -> s0Z (e_regs E) < YM05.alloc_ceiling.
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_frz : forall {E : ECX}, ECPRE E -> YK0o.frm_zero (@YK11.fp_csr fx).
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_ra : forall {E : ECX}, ECPRE E -> raZ (e_regs E) = EC_RA.
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_a0 : forall {E : ECX}, ECPRE E -> getr (e_regs E) 10 = w64 (e_p E).
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_a1 : forall {E : ECX}, ECPRE E -> getr (e_regs E) 11 = w64 (e_n E).
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_frames : forall {E : ECX}, ECPRE E -> frames (e_S E) = [].
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_rl : forall {E : ECX}, ECPRE E -> @room_live_cf RL (e_S E).
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_pos : forall {E : ECX}, ECPRE E ->
  PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E) (e_i0 E) (e_H0 E) (e_hist0 E) (e_S E).
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_i0 : forall {E : ECX}, ECPRE E -> e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E)).
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_sm : forall {E : ECX}, ECPRE E -> e_sm E = ReaderRes.jr_strtod.
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_live : forall {E : ECX}, ECPRE E -> blocks_bytes (e_S E) + LIVE_LIB <= LIVE_MAX.
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_rod : forall {E : ECX}, ECPRE E ->
  arodata_okP SEGS (@pa_relro_lo rc A_prog_listing PA) (@pa_relro_hi rc A_prog_listing PA) B
    (aview SEGS (w_H (e_W E)) (e_mem E)).
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_led : forall {E : ECX}, ECPRE E ->
  exists peak most own, @prh_ledger rc cp PI A_prog_listing PA B (e_ly E) (e_S E) [] (e_W E) (e_mem E) [] peak
    (e_cnt E) SIZE_MAX (e_ran E) most own.
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_sio : forall {E : ECX}, ECPRE E -> EC_SIO (aview SEGS (w_H (e_W E)) (e_mem E)).
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_cnt : forall {E : ECX}, ECPRE E -> e_cnt E + LCNT <= SIZE_MAX.
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_cnt62 : forall {E : ECX}, ECPRE E -> e_cnt E + LCNT < 2 ^ 62 - 2 ^ 30.
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_pre_mn : forall {E : ECX}, ECPRE E -> YAkMemnorm.memnorm SEGS (e_mem E).
Proof. intros E H. unfold ec_pre in H. Ent102CallA.ec_conj_pick H. Qed.

(* ec_inv's parts CallA does not give; E .. i_c implicit, so a call does not depend on ec_inv's arity *)
Lemma l0_inv_j : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  exists WS, ajournal_xw (SK := SK) SEGS B PST ARC LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E)
    (e_md E) own ly S Hp W mem md k WS /\ YCbqGwild.wbudget [] wk WS.
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_inv in H. Ent102CallA.ec_conj_pick H. Qed.
(* the same journal, plain, at a cut whose spent wild budget is 0 (L0 makes no allocator call) *)
Lemma l0_inv_jp : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c 0%nat ->
  ajournal_x (SK := SK) SEGS B PST ARC LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k.
Proof.
  intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c H.
  destruct (l0_inv_j H) as (WS & HJ & HWB). eapply ec_journal_plain; [exact HJ | exact HWB].
Qed.
Lemma l0_inv_own : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> ec_own fk ly W mem own.
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_inv in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_inv_sio : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> EC_SIO (aview SEGS (w_H W) mem).
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_inv in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_inv_rod : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  arodata_okP SEGS (@pa_relro_lo rc A_prog_listing PA) (@pa_relro_hi rc A_prog_listing PA) B (aview SEGS (w_H W) mem).
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_inv in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_inv_rl : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> @room_live_cf RL S.
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_inv in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_inv_pos : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) os_c i_c (e_H0 E) hist S.
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_inv in H. Ent102CallA.ec_conj_pick H. Qed.
Lemma l0_inv_cnt : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> e_cnt E <= cnt <= e_cnt E + LCNT.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_inv in H. Ent102CallA.ec_conj_split H.
split; assumption.
Qed.
Lemma l0_inv_mn : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> YAkMemnorm.memnorm SEGS mem.
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_inv in H. Ent102CallA.ec_conj_pick H. Qed.

(* every part of ec_pre, by its projection (CallA's or this section's), under the names the two proofs read *)
Local Ltac l0_pre_parts H :=
  pose proof (l0_pre_afn H) as HPREx; pose proof (l0_pre_s0 H) as Hs0c; pose proof (l0_pre_frz H) as Hfrz;
  pose proof (l0_pre_ra H) as Hraeq; pose proof (l0_pre_a0 H) as Hp10; pose proof (l0_pre_a1 H) as Hp11;
  pose proof (Ent102CallA.ec_pre_payload (fx := fx) B EC_RA EC_EMPTY EC_SIO H) as Hblkd;
  pose proof (Ent102CallA.ec_pre_len (fx := fx) B EC_RA EC_EMPTY EC_SIO H) as Hnlen;
  pose proof (Ent102CallA.ec_pre_bytes (fx := fx) B EC_RA EC_EMPTY EC_SIO H) as Hgarr;
  pose proof (l0_pre_frames H) as HfrS; pose proof (l0_pre_rl H) as HRLe; pose proof (l0_pre_pos H) as HROOMe;
  pose proof (l0_pre_i0 H) as Hi0e; pose proof (l0_pre_sm H) as Hsme;
  pose proof (l0_pre_live H) as HLIVEe;
  pose proof (l0_pre_rod H) as HRODe;
  pose proof (l0_pre_led H) as HLEDe; pose proof (l0_pre_sio H) as HSIOe; pose proof (l0_pre_cnt H) as HCNTe;
  pose proof (l0_pre_cnt62 H) as HCNT62; pose proof (l0_pre_mn H) as HMNe;
  pose proof (Ent102CallA.ec_pre_pay8 (fx := fx) B EC_RA EC_EMPTY EC_SIO H) as HPAY8.

(* THE EXIT ARM'S POSITION: above PRESET_FILE_MAX_BYTES (= MAXB) the call makes no model event (call_evs = [] for
   every triple; (None, None, None) is chosen), and the entry index e_i0 = |hruns e_os| is within e_os, so the
   entry position extends to e_os ++ [trp] at the same index (Ent102PosA.ec_pos_extend) *)
Lemma l0_pos_exit : forall (E : ECX) S, ECPRE E -> EC_NMAX < e_n E ->
  (exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E) (e_i0 E) (e_H0 E) hist S) ->
  exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E ++ [(None, None, None)])
    (e_i0 E + length (ec_call_evs E (None, None, None)))%nat (e_H0 E) hist S.
Proof.
intros E S HP Hn (hist & Hpos).
assert (HL : Z.of_nat (length (e_x E)) = e_n E)
  by (unfold e_x, ec_bytes; rewrite length_map; symmetry;
      exact (Ent102CallA.ec_pre_len (fx := fx) B EC_RA EC_EMPTY EC_SIO HP)).
assert (Hev : ec_call_evs E (None, None, None) = []).
{ unfold ec_call_evs. cbv beta iota. rewrite PresetRun.call_evs_blocks.
  destruct (Z.ltb_spec PresetReqAt.MAXB (Z.of_nat (length (e_x E)))) as [_|Hge]; [reflexivity|].
  exfalso. unfold PresetReqAt.MAXB, EC_NMAX in *. lia. }
rewrite Hev. cbn [length]. rewrite Nat.add_0_r. exists hist.
apply Ent102PosA.ec_pos_extend; [|exact Hpos]. rewrite (l0_pre_i0 HP). lia.
Qed.

(* the three laws the engine and the frame rule take, each PROVED here from the cf instance *)
Lemma l0_LAWS : AR_laws_x SEGS B ARX cf_head.
Proof. exact (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)). Qed.
Lemma l0_OWNLOW : ARx_owned_low_law SEGS B ARX.
Proof. exact (ARx_owned_low_law_xs SEGS B (AR_laws_ok_cf SEGS B)). Qed.
Lemma l0_SMX : forall ly S Hp W mem md cid, ARX ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
Proof. intros ly S Hp W mem md cid HAR Hc Hn. exact (stack_malloc_x_any SEGS ARX ly S Hp W mem md cid HAR Hc Hn). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. What ARX gives about the runtime's four cells: their bounds (the image's owned statics) and their values. *)
Lemma l0_syms : forall ly S Hp W mem md, ARX ly S Hp W mem md -> asyms_ok B.
Proof. intros ly S Hp W mem md [HAR _]. exact (amc_syms _ _ _ _ _ (proj1 HAR)). Qed.

Lemma l0_cells : asyms_ok B ->
  (4096 <= as_shadow_cell B /\ as_shadow_cell B + 8 <= kImgEnd) /\
  (4096 <= as_uar_cell B /\ as_uar_cell B + 4 <= kImgEnd) /\
  (4096 <= as_got_shadow B /\ as_got_shadow B + 8 <= kImgEnd) /\
  (4096 <= as_got_uar B /\ as_got_uar B + 8 <= kImgEnd).
Proof.
intros SY.
pose proof (asyms_area_bound B (as_shadow_cell B, 8) SY ltac:(cbn; tauto)) as C1.
pose proof (asyms_area_bound B (as_uar_cell B, 4) SY ltac:(cbn; tauto)) as C2.
pose proof (asyms_area_bound B (as_got_shadow B, 8) SY ltac:(cbn; tauto)) as C3.
pose proof (asyms_area_bound B (as_got_uar B, 8) SY ltac:(cbn; tauto)) as C4.
cbn [fst snd] in C1, C2, C3, C4. tauto.
Qed.

Lemma l0_const : forall ly S Hp W mem md, ARX ly S Hp W mem md ->
  rdword (aview SEGS (w_H W) mem) (as_shadow_cell B) = Some SHADOW_OFF /\
  rd32 (aview SEGS (w_H W) mem) (as_uar_cell B) 1 /\
  rdword (aview SEGS (w_H W) mem) (as_got_shadow B) = Some (as_shadow_cell B) /\
  rdword (aview SEGS (w_H W) mem) (as_got_uar B) = Some (as_uar_cell B).
Proof. intros ly S Hp W mem md H. exact (alx_const SEGS B ARX l0_LAWS ly S Hp W mem md H). Qed.

(* an 8-byte / 4-byte read-only chunk of the symbolic memory, from a value read of the current view *)
Lemma l0_chunk8 : forall (E : env) (m : word -> option byte) (e : sv) (base v : Z),
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem SEGS m base 8 v ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk 0 (CVal 8 e)).
Proof.
intros E m e base v He Hv Hm.
apply (YI04.chunk_ok_val SEGS E m base 0 8 e v He).
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
- change (Z.of_N 8) with 8. lia.
- change (N.to_nat 8) with 8%nat. replace (base + 0) with base by lia. exact Hm.
Qed.
Lemma l0_chunk4 : forall (E : env) (m : word -> option byte) (e : sv) (base v : Z),
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> val_mem SEGS m base 4 v ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk 0 (CVal 4 e)).
Proof.
intros E m e base v He Hv Hm.
apply (YI04.chunk_ok_val SEGS E m base 0 4 e v He).
- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). exact Hv.
- change (Z.of_N 4) with 4. lia.
- change (N.to_nat 4) with 4%nat. replace (base + 0) with base by lia. exact Hm.
Qed.
(* a value read of the view as a little-endian 64-bit read (the form ec_saved / ec_own ask) *)
Lemma l0_val_mem_rd64 : forall (H : word -> bool) m a v,
  val_mem SEGS (mrestrict H m) a 8 v -> rd64 (aview SEGS H m) a v.
Proof.
intros H m a v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
cbv [YO0f.le_byte YG0f.le_byte]. apply Z.mod_mod. lia.
Qed.
Lemma l0_rd64_of_rdword : forall (H : word -> bool) m a v,
  rdword (aview SEGS H m) a = Some v -> rd64 (aview SEGS H m) a v.
Proof. intros H m a v Hr. exact (l0_val_mem_rd64 H m a v (val_mem_of_rdword SEGS H m a v Hr)). Qed.
(* a value read survives a change of memory that keeps the view on its bytes *)
Lemma l0_val_mem_agree : forall (H : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n -> aview SEGS H m' (a + i) = aview SEGS H m (a + i)) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' a n v Hag Hv k Hk. pose proof (Hv k Hk) as Hk'.
specialize (Hag (Z.of_nat k) ltac:(lia)). unfold aview in Hag. rewrite Hk' in Hag.
destruct (mbyte SEGS (mrestrict H m') (a + Z.of_nat k)) as [b|] eqn:Eb;
cbn [option_map] in Hag; [|discriminate Hag].
injection Hag as Hb. try rewrite Eb. f_equal. apply bv_eq. exact Hb.
Qed.
(* and so does a view equality off a stretch's write windows *)
Lemma l0_aview_kept : forall (W : world SEGS) E rs (m m' : word -> option byte) a,
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> 0 <= a < 2 ^ 64 ->
  ~ in_wrange E rs a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros W E rs m m' a HFr Ha Hw. unfold aview, mbyte.
rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Z.mod_small by lia. exact Hw.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. STRETCH 1 of L0a (+0x000 .. +0x058): the prologue (the saved block in [sp0 - 128, sp0), s0 = sp0,
      sp = s1 = A) and the two GOT loads (slots 19 .. 22: a2 = [A_OBJ 1] = the use-after-return option cell,
      a1 = [A_OBJ 0] = the shadow-base cell). *)
Definition L0_Bx : sv := SLit SHADOW_OFF.
Definition L0_Bspan : Z * Z := (0, 0).
Definition l0_r_gots : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 12) 0))].
Definition l0_r_gotu : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition l0_regions0 : smem := [stack_region EC_SAVE; l0_r_gots; l0_r_gotu].
Definition l0_facts0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition l0_ss0 : sstate := mkSS 0 sr_atoms l0_regions0 None l0_facts0.
Definition l0_E0 (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 (as_uar_cell B)]).

Lemma l0_entry0 : forall ly S Hp W regs mem md ch,
  PALib (L := A_prog_listing) (PI := PA) B ->
  afn_pre_x SEGS B ARX LLVMF_STK ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (l0_E0 regs) l0_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0)) mem (seg_rom SEGS))) /\
  sh_ok SEGS L0_Bx [] (l0_E0 regs) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch PAL HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : LLVMF_STK = 32768) by reflexivity.
destruct (l0_const ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
destruct (l0_cells (l0_syms ly S Hp W mem md HAR)) as ((D1 & D2) & (D3 & D4) & (D5 & D6) & (D7 & D8)).
rewrite (pal_got_shadow B PAL) in Kgot, D5, D6.
rewrite (pal_cell B PAL) in Kgot, Kcell, D1, D2.
rewrite (pal_got_uar B PAL) in Kguar, D7, D8.
pose proof (pal_got_uar_disj B PAL) as (Hdisj01 & Hdisj112).
pose proof (pal_got_cell B PAL) as Hdisj012.
rewrite restrict_mkst_fx.
set (E := l0_E0 regs) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold l0_E0; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 (as_uar_cell B)]) n)
  by (intros n0 Hn0; subst E; unfold l0_E0; apply Eimg_low; exact Hn0).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U0 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply HEI; unfold A_TEXT, A_OBJ, A_LIM; lia).
assert (U1 : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply HEI; unfold A_TEXT, A_OBJ, A_LIM; lia).
assert (U12 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply HEI; unfold A_TEXT, A_OBJ, A_LIM; lia).
assert (HkI : kImgEnd = 0x677000) by reflexivity.
assert (R0 : 0 <= VAL (A_OBJ 0) < 2 ^ 64) by lia.
assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 64) by lia.
assert (R12 : 0 <= VAL (A_OBJ 12) < 2 ^ 64) by lia.
assert (RU : 0 <= as_uar_cell B < 2 ^ 64) by lia.
assert (HN8 : Z.of_N 8 = 8) by reflexivity.
split.
- unfold l0_ss0. apply pa_entry_st_ok_full.
  + subst E. unfold l0_E0. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold l0_regions0, stack_region, l0_r_gots, l0_r_gotu.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [unfold EC_SAVE; lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply Hpres. unfold EC_SAVE in Hq. lia.
    * rewrite U0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (l0_chunk8 E _ (SOff (A_OBJ 12) 0) (VAL (A_OBJ 0)) (VAL (A_OBJ 12)));
      [ cbn [sv_denot]; rewrite Z.add_0_r; apply bv_eq; rewrite U12, Z_to_bv_unsigned;
        unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); rewrite Z.mod_small by lia; reflexivity
      | exact R12
      | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot) ].
    * rewrite U1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (l0_chunk8 E _ (SOff 32 0) (VAL (A_OBJ 1)) (as_uar_cell B));
      [ cbn [sv_denot]; rewrite Z.add_0_r, E32; apply Z_to_bv_bv_unsigned
      | exact RU
      | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar) ].
  + apply pairwise_disjoint_of_extents.
    unfold l0_regions0, stack_region, l0_r_gots, l0_r_gotu, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U0, U1.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold EC_SAVE. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok l0_facts0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. STRETCH 2 (+0x05c): `lw a2, 0(a2)`, the use-after-return option cell (a2 holds its address). Its region is
      the ONLY one of this stretch: the stretch writes nothing, and the option cell's disjointness from the
      shadow-base cell is not an image fact this walk has. *)
Definition l0_E1 (regs1 : bvmap 5 word) : env := Eimg (Ereg regs1 []).
Definition l0_r_uar : YP09.region :=
  YP09.mkRegion (Some 12%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition l0_ss1 : sstate := mkSS 0x5c sr_atoms [l0_r_uar] None (mkFacts [] [] []).
(* STRETCH 3 (+0x060 .. +0x070): `ld s10, 0(a1)` (the shadow base, a1 holds the cell's address), `mv s4, a0`,
   the option test (not taken: the cell reads 1), `addi a0, zero, 0x80` and the class-1 frame call. *)
Definition l0_r_sb : YP09.region :=
  YP09.mkRegion (Some 11%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit SHADOW_OFF))].
Definition l0_ss2 : sstate :=
  mkSS 0x60 sr_atoms [l0_r_sb] None (mkFacts [(12%nat, mkAF 1 1 0)] [] []).


(* a saved-register slot of the prologue, read back from the symbolic state's chunk *)
Lemma l0_saved_chunk : forall (EV : env) (H : word -> bool) (mm : word -> option byte) base off (n : nat),
  YP09.chunk_ok SEGS EV (mrestrict H mm) base (YP09.mkChunk off (CVal 8 (SOff n 0))) ->
  rd64 (aview SEGS H mm) (base + off) (bv_unsigned (ew EV n)).
Proof.
intros EV H mm base off n HC. apply l0_val_mem_rd64.
assert (Hd : sv_denot EV (SOff n 0) = Z_to_bv 64 (bv_unsigned (ew EV n)))
  by (cbn; rewrite Z.add_0_r; reflexivity).
pose proof (bv_unsigned_in_range 64 (ew EV n)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
pose proof (val_of_chunk_ok SEGS EV (mrestrict H mm) base off 8 (SOff n 0) (bv_unsigned (ew EV n)) HC Hd
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia)) as HV.
change (N.to_nat 8) with 8%nat in HV. exact HV.
Qed.
(* an 8-byte read survives a memory change that keeps the view on its bytes *)
Lemma l0_rd64_keep : forall (H : word -> bool) (m m' : word -> option byte) a v,
  (forall i, 0 <= i < 8 -> aview SEGS H m' (a + i) = aview SEGS H m (a + i)) ->
  rd64 (aview SEGS H m) a v -> rd64 (aview SEGS H m') a v.
Proof.
intros H m m' a v Hag Hr k Hk. rewrite (Hag (Z.of_nat k) ltac:(lia)). exact (Hr k Hk).
Qed.

(* The kit's ledger cells are PST: a memory change that keeps the view on PST keeps prh_glob. The proof reads prh_glob's
   cells by shape (every val_mem conjunct is one PST cell, g_most / g_own_ran_out's included since the kit decff67d721f),
   not by position, so a cell the kit owner adds is carried too. *)
Lemma l0_glob_keep : forall (W0 : world SEGS) (m m' : word -> option byte) live peak cnt fail ran most own,
  (forall a, Exists (in_zr a) PST -> aview SEGS (w_H W0) m' a = aview SEGS (w_H W0) m a) ->
  prh_glob W0 m live peak cnt fail ran most own -> prh_glob W0 m' live peak cnt fail ran most own.
Proof.
intros W0 m m' live peak cnt fail ran most own HK HG.
assert (CELL : forall (p : Z) (w : nat) (v : Z), In (p, Z.of_nat w) (@prh_pst PI) ->
  val_mem SEGS (mrestrict (w_H W0) m) p w v -> val_mem SEGS (mrestrict (w_H W0) m') p w v).
{ intros p w v Hin HV. apply (l0_val_mem_agree (w_H W0) m m' p w v); [|exact HV].
  intros i Hi. apply HK. apply Exists_exists. exists (p, Z.of_nat w). split; [exact Hin|].
  unfold in_zr. cbn [fst snd]. lia. }
unfold prh_glob, prh_most, prh_own in *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat split; try assumption;
match goal with H : val_mem SEGS (mrestrict _ m) ?p ?w ?v |- val_mem SEGS (mrestrict _ m') ?p ?w ?v =>
  exact (CELL p w v ltac:(unfold prh_pst; cbn [In]; repeat (first [left; reflexivity | right])) H) end.
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. L0a: from cut_start to cut_frame. *)
Theorem seg_L0a_A :
  @seg_L0a_stmt fx rc ci cp PI RL A_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut.
Proof.
unfold seg_L0a_stmt, ec_lane.
intros E HHYP W c Hcut.
pose proof (ech_frame_area _ _ _ _ _ _ _ _ _ _ HHYP) as HFR. destruct HFR as (HFRM & HFRE).
pose proof (ech_img _ _ _ _ _ _ _ _ _ _ HHYP) as HIM.
pose proof (ech_lcut_ok _ _ _ _ _ _ _ _ _ _ HHYP) as HLC.
pose proof (ech_ccut_ok _ _ _ _ _ _ _ _ _ _ HHYP) as HCC.
destruct Hcut as (HPRE0 & HWE & HCE). subst W c.
(* ec_pre's parts BY NAME (section 2') *)
l0_pre_parts HPRE0.
pose proof (ei_pal _ _ _ _ _ _ HIM) as PAL.
pose proof (ei_entry _ _ _ _ _ _ HIM) as Hentry.
pose proof (ei_sm1 _ _ _ _ _ _ HIM) as Hsm1.
pose proof HPREx as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (l0_entry0 (e_ly E) (e_S E) [] (e_W E) (e_regs E) (e_mem E) (e_md E) [] PAL HPREx) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARX LLVMF_STK [] (e_ly E) (e_S E) [] (e_W E) (e_regs E)
  (e_mem E) (e_md E) [] HPREx) as HJ.
pose proof HMNe as HMN.
set (EV := l0_E0 (e_regs E)) in *.
assert (HEI : img_env VAL A_LIM EV) by (unfold EV, l0_E0; apply Eimg_env).
assert (EWr : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew EV n = getr (e_regs E) r).
{ intros n r Hn Hr. unfold EV, l0_E0. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat (e_regs E) _ n r Hr). }
assert (E2 : ew EV 2 = getr (e_regs E) 2) by (apply EWr; [lia | reflexivity]).
assert (Usp : bv_unsigned (ew EV 2) = spZ (e_regs E)) by (rewrite E2; reflexivity).
assert (E32 : ew EV 32 = Z_to_bv 64 (as_uar_cell B))
  by (unfold EV, l0_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (e_regs E) _ 0)).
assert (HkI : kImgEnd = 0x677000) by reflexivity.
assert (Hspb : YM05.alloc_ceiling + LLVMF_STK <= spZ (e_regs E) <= 2 ^ 47) by lia.
pose (RUNTO := @paj_run_to_x_inv fx rc SK A_prog_listing PL_102_A PA B PST ARX cf_head l0_LAWS
  (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS)).
pose (RUN := @paj_run_x_inv fx rc SK A_prog_listing PL_102_A PA B PST ARX cf_head l0_LAWS
  (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS)).
assert (Hpc : w64 (@pa_sigma rc A_prog_listing PA AS_LLVMFuzzerTestOneInput) = Z_to_bv 64 (BASE + 0))
  by (rewrite Hentry; unfold EC_BASE; rewrite Z.add_0_r; reflexivity).
unfold cfg_at. rewrite Hpc.
(* ---- STRETCH 1: +0x000 .. +0x058 ---- *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HMN L0_Bspan 0x5c.
{ intros a (r & Hr & Ha). unfold l0_ss0, l0_regions0 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]];
  cbn [stack_region l0_r_gots l0_r_gotu YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?Usp in Ha; unfold awr_byte.
  - left. unfold EC_SAVE, LLVMF_STK in *. lia.
  - exfalso. lia.
  - exfalso. lia. }
rename HF into HF1. rename HFr into HFr1. rename HG into HG1.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12.
prreg HS (19%bv : bv 5) R19. prreg HS (10%bv : bv 5) R10.
(* the saved block, read back from the prologue's own chunks *)
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HMO & _).
cbn [ss_mem] in HMO. apply Forall_inv in HMO. destruct HMO as (_ & _ & _ & HCH).
cbn [YP09.r_chunks YP09.r_base base_val] in HCH. rewrite Usp in HCH.
pose proof (proj1 (Forall_forall _ _) HCH) as HCA.
assert (SAV : forall (off : Z) (n : nat) (r : bv 5),
  YP09.chunk_ok SEGS EV (ms_mem (restrict (w_H (e_W E)) ms)) (spZ (e_regs E))
    (YP09.mkChunk (- off) (CVal 8 (SOff n 0))) ->
  (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  rd64 (aview SEGS (w_H (e_W E)) (ms_mem ms)) (spZ (e_regs E) - off) (bv_unsigned (getr (e_regs E) r))).
{ intros off n r HC Hn Hr. rewrite <- (EWr n r Hn Hr).
  replace (spZ (e_regs E) - off) with (spZ (e_regs E) + (- off)) by lia.
  cbn [ms_mem restrict] in HC.
  exact (l0_saved_chunk EV (w_H (e_W E)) (ms_mem ms) (spZ (e_regs E)) (- off) n HC). }
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (e_regs E) - EC_SAVE <= a < spZ (e_regs E)) ->
  aview SEGS (w_H (e_W E)) (ms_mem ms) a = aview SEGS (w_H (e_W E)) (e_mem E) a).
{ intros a Ha Hna. apply (l0_aview_kept (e_W E) EV (ss_mem l0_ss0) (e_mem E) (ms_mem ms) a HFr1 Ha).
  intros (r & Hr & Hb). unfold l0_ss0, l0_regions0 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]];
  cbn [stack_region l0_r_gots l0_r_gotu YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  rewrite ?Usp in Hb; unfold EC_SAVE in *; lia. }
(* ---- STRETCH 2: +0x05c, the option cell ---- *)
destruct (l0_cells (l0_syms _ _ _ _ _ _ (proj1 HJ))) as ((DS1 & DS2) & (DU1 & DU2) & _).
destruct (l0_const _ _ _ _ _ _ (proj1 HJ)) as (K1 & K2 & K3 & K4).
assert (HU : val_mem SEGS (mrestrict (w_H (e_W E)) (ms_mem ms)) (as_uar_cell B) 4 1)
  by (apply l0_val_mem_of_rd32; exact K2).
assert (U12' : bv_unsigned (ew (l0_E1 (ms_regs ms)) 12) = as_uar_cell B).
{ unfold l0_E1. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat (ms_regs ms) [] 12 12%bv eq_refl), R12, E32. apply unsigned_lit_small. lia. }
assert (HEIuar : img_env VAL A_LIM (l0_E1 (ms_regs ms))) by (unfold l0_E1; apply Eimg_env).
assert (SHOK1 : sh_ok SEGS L0_Bx [] (l0_E1 (ms_regs ms)) (mrestrict (w_H (e_W E)) (ms_mem ms)))
  by apply Forall_nil.
assert (HS1 : st_ok_pi SEGS VAL (l0_E1 (ms_regs ms)) l0_ss1
  (restrict (w_H (e_W E)) (mkst (ms_regs ms) (Z_to_bv 64 (BASE + 0x5c)) (ms_mem ms) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold l0_ss1. apply pa_entry_st_ok_full.
  - unfold l0_E1. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, l0_r_uar.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U12'. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (l0_chunk4 _ _ (SLit 1) (as_uar_cell B) 1); [vm_compute; reflexivity | lia | exact HU].
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I|]. split; exact I. }
clear HS HCH.
paj_run_to_tok_x_inv RUNTO HS1 HJ SHOK1 HMN L0_Bspan 0x60.
{ intros a (r & Hr & Ha). unfold l0_ss1 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[]]. cbn [l0_r_uar YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. exfalso. lia. }
rename HF into HF2. rename HFr into HFr2. rename HG into HG2.
pmkst HS1.
prreg HS1 (11%bv : bv 5) Q11. prreg HS1 (12%bv : bv 5) Q12.
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4.
prreg HS1 (8%bv : bv 5) Q8. prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (10%bv : bv 5) Q10.
prreg HS1 (19%bv : bv 5) Q19.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H (e_W E)) (ms_mem ms0) a = aview SEGS (w_H (e_W E)) (ms_mem ms) a).
{ intros a Ha. apply (l0_aview_kept (e_W E) (l0_E1 (ms_regs ms)) (ss_mem l0_ss1) _ _ a HFr2 Ha).
  intros (r & Hr & Hb). unfold l0_ss1 in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<-|[]].
  cbn [l0_r_uar YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. lia. }
(* ---- STRETCH 3: +0x060 .. the frame call ---- *)
assert (U11a : ew (l0_E1 (ms_regs ms)) 11 = Z_to_bv 64 (as_shadow_cell B)).
{ unfold l0_E1. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat (ms_regs ms) [] 11 11%bv eq_refl), R11.
  rewrite (pal_cell B PAL), <- (HEI (A_OBJ 12) ltac:(unfold A_TEXT, A_OBJ, A_LIM; lia)).
  symmetry. apply Z_to_bv_bv_unsigned. }
assert (U11b : bv_unsigned (ew (l0_E1 (ms_regs ms0)) 11) = as_shadow_cell B).
{ unfold l0_E1. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat (ms_regs ms0) [] 11 11%bv eq_refl), Q11, U11a. apply unsigned_lit_small. lia. }
destruct (l0_const _ _ _ _ _ _ (proj1 HJ)) as (M1 & M2 & M3 & M4).
assert (HSB : val_mem SEGS (mrestrict (w_H (e_W E)) (ms_mem ms0)) (as_shadow_cell B) 8 SHADOW_OFF)
  by exact (val_mem_of_rdword SEGS (w_H (e_W E)) (ms_mem ms0) _ _ M1).
assert (HEIsb : img_env VAL A_LIM (l0_E1 (ms_regs ms0))) by (unfold l0_E1; apply Eimg_env).
assert (SHOK2 : sh_ok SEGS L0_Bx [] (l0_E1 (ms_regs ms0)) (mrestrict (w_H (e_W E)) (ms_mem ms0)))
  by apply Forall_nil.
assert (HS2 : st_ok_pi SEGS VAL (l0_E1 (ms_regs ms0)) l0_ss2
  (restrict (w_H (e_W E)) (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + 0x60)) (ms_mem ms0) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold l0_ss2. apply pa_entry_st_ok_full.
  - unfold l0_E1. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, l0_r_sb.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U11b. assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (l0_chunk8 _ _ (SLit SHADOW_OFF) (as_shadow_cell B) SHADOW_OFF);
    [vm_compute; reflexivity | lia | exact HSB].
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    assert (H12 : bv_unsigned (ew (l0_E1 (ms_regs ms0)) 12) = 1).
    { unfold l0_E1. rewrite Eimg_low by (unfold A_TEXT; lia).
      rewrite (ew_Ereg_nat (ms_regs ms0) [] 12 12%bv eq_refl), Q12. apply unsigned_lit_small. lia. }
    rewrite H12. split; [lia|]. split; [reflexivity | lia]. }
clear HS1.
paj_run_tok_x_inv RUN HS2 HJ SHOK2 HMN L0_Bspan.
{ intros a (r & Hr & Ha). unfold l0_ss2 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[]]. cbn [l0_r_sb YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. exfalso. lia. }
rename HF into HF3. rename HFr into HFr3. rename HG into HG3.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H (e_W E)) (ms_mem ms1) a = aview SEGS (w_H (e_W E)) (ms_mem ms0) a).
{ intros a Ha. apply (l0_aview_kept (e_W E) (l0_E1 (ms_regs ms0)) (ss_mem l0_ss2) _ _ a HFr3 Ha).
  intros (r & Hr & Hb). unfold l0_ss2 in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<-|[]].
  cbn [l0_r_sb YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. lia. }
pmkst HS2.
prreg HS2 (1%bv : bv 5) T1. prreg HS2 (2%bv : bv 5) T2. prreg HS2 (3%bv : bv 5) T3.
prreg HS2 (4%bv : bv 5) T4. prreg HS2 (8%bv : bv 5) T8. prreg HS2 (9%bv : bv 5) T9.
prreg HS2 (19%bv : bv 5) T19. prreg HS2 (20%bv : bv 5) T20. prreg HS2 (26%bv : bv 5) T26.
(* the register values at the call, chained back to the entry registers *)
assert (EW1 : forall (regs1 : bvmap 5 word) (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (l0_E1 regs1) n = getr regs1 r).
{ intros regs1 n r Hn Hr. unfold l0_E1. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs1 _ n r Hr). }
rewrite (EW1 (ms_regs ms0) 2%nat 2%bv ltac:(lia) eq_refl), Q2, (EW1 (ms_regs ms) 2%nat 2%bv ltac:(lia) eq_refl),
  R2, Usp in T2.
rewrite (EW1 (ms_regs ms0) 3%nat 3%bv ltac:(lia) eq_refl), Q3, (EW1 (ms_regs ms) 3%nat 3%bv ltac:(lia) eq_refl),
  R3, (EWr 3%nat 3%bv ltac:(lia) eq_refl) in T3.
rewrite (EW1 (ms_regs ms0) 4%nat 4%bv ltac:(lia) eq_refl), Q4, (EW1 (ms_regs ms) 4%nat 4%bv ltac:(lia) eq_refl),
  R4, (EWr 4%nat 4%bv ltac:(lia) eq_refl) in T4.
rewrite (EW1 (ms_regs ms0) 8%nat 8%bv ltac:(lia) eq_refl), Q8, (EW1 (ms_regs ms) 8%nat 8%bv ltac:(lia) eq_refl),
  R8, (EWr 2%nat 2%bv ltac:(lia) eq_refl) in T8.
rewrite (EW1 (ms_regs ms0) 9%nat 9%bv ltac:(lia) eq_refl), Q9, (EW1 (ms_regs ms) 9%nat 9%bv ltac:(lia) eq_refl),
  R9, Usp in T9.
rewrite (EW1 (ms_regs ms0) 19%nat 19%bv ltac:(lia) eq_refl), Q19,
  (EW1 (ms_regs ms) 19%nat 19%bv ltac:(lia) eq_refl), R19, (EWr 11%nat 11%bv ltac:(lia) eq_refl), Hp11 in T19.
rewrite (EW1 (ms_regs ms0) 10%nat 10%bv ltac:(lia) eq_refl), Q10,
  (EW1 (ms_regs ms) 10%nat 10%bv ltac:(lia) eq_refl), R10, (EWr 10%nat 10%bv ltac:(lia) eq_refl), Hp10 in T20.
(* the aligned frame base A *)
assert (HAdiv : e_A E = (spZ (e_regs E) - 128) / 32 * 32)
  by (unfold e_A, ec_A, e_sp0, EC_SAVE; apply l0_land_neg32; lia).
assert (HAlo1 : spZ (e_regs E) - 160 < e_A E <= spZ (e_regs E) - 128).
{ rewrite HAdiv. pose proof (Z.mul_div_le (spZ (e_regs E) - 128) 32 ltac:(lia)).
  pose proof (Z.mod_pos_bound (spZ (e_regs E) - 128) 32 ltac:(lia)).
  pose proof (Z.div_mod (spZ (e_regs E) - 128) 32 ltac:(lia)). lia. }
assert (HAmod : e_A E mod 32 = 0) by (rewrite HAdiv; apply Z_mod_mult).
assert (T2' : getr (ms_regs ms1) 2 = w64 (e_A E)).
{ rewrite T2, (l0_and_m32 (spZ (e_regs E) + -128) ltac:(lia)). unfold w64. rewrite HAdiv.
  replace (spZ (e_regs E) + -128) with (spZ (e_regs E) - 128) by lia. reflexivity. }
assert (T9' : getr (ms_regs ms1) 9 = w64 (e_A E)).
{ rewrite T9, (l0_and_m32 (spZ (e_regs E) + -128) ltac:(lia)). unfold w64.
  replace (spZ (e_regs E) + -128) with (spZ (e_regs E) - 128) by lia. rewrite <- HAdiv.
  unfold alu64, alu. cbn. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity. }
assert (T8' : getr (ms_regs ms1) 8 = w64 (e_sp0 E)).
{ rewrite T8. unfold w64, e_sp0, spZ. symmetry. apply Z_to_bv_bv_unsigned. }
(* THE FRAME CALL (+0x070): the class-1 frame area, with the memnorm keep *)
assert (ASM : YGcallMxmn.astack_malloc_realizes_xm SEGS B ARX LLVMF_FS_CLASS).
{ apply (YGcallMxmn.astack_malloc_realizes_xm_conj SEGS B
    (fun ly0 S0 Hp0 W0 mem0 md0 => ARcf (cp := cp) SEGS B ly0 S0 Hp0 W0 mem0 md0) xs_placed_cf LLVMF_FS_CLASS
    xs_placed_cf_set_fs).
  exact (HFRM fx). }
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + 116))) by (apply (ret_ok_codeptr_v 116); [lia | reflexivity]).
rewrite <- Hsm1.
eapply SRr_bind.
{ eapply (YGcallMxmn.aj_stack_malloc_at_xm (SK := SK) SEGS B PST ARX l0_LAWS pa_segs_low (pal_env B PAL) l0_OWNLOW l0_SMX
    LLVMF_FS_CLASS ASM ltac:(unfold LLVMF_FS_CLASS; lia))
  with (o := e_A E - spZ (e_regs E)) (raw := Z_to_bv 64 (BASE + 116)).
  - exact HJ.
  - unfold spZ at 1. rewrite T2'. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - replace (e_A E - spZ (e_regs E)) with ((2 * (e_A E / 32) - spZ (e_regs E) / 16) * 16)
      by (pose proof (Z.div_mod (e_A E) 32 ltac:(lia)); pose proof (Z.div_mod (spZ (e_regs E)) 16 ltac:(lia)); lia).
    apply Z_mod_mult.
  - lia.
  - unfold LLVMF_STK, ESTACK in *. lia.
  - rewrite T3. exact Hgp.
  - rewrite T4. exact Htp.
  - exact T1.
  - exact Hraw.
  - rewrite HfrS. vm_compute. reflexivity. }
cbv beta. intros W2 c2 Hwle (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HPRES & Ha0 & Eab2 & Hfrs2 & Hfresh
  & Hnev2 & Hbb2 & Hz & Hflag & Hfpres & HKEPT & HJcall & Hsetfs & HMN2).
destruct Hsetfs as (ff & ES2).
destruct HKEPT as (KA & KB & KC & KD & KE & KF).
(* the callee-saved registers at the cut *)
assert (P2 : getr regs2 2%bv = getr (ms_regs ms1) 2%bv) by exact (HPRES 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3%bv = getr (ms_regs ms1) 3%bv) by exact (HPRES 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4%bv = getr (ms_regs ms1) 4%bv) by exact (HPRES 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8%bv = getr (ms_regs ms1) 8%bv) by exact (HPRES 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9%bv = getr (ms_regs ms1) 9%bv) by exact (HPRES 9 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs2 19%bv = getr (ms_regs ms1) 19%bv) by exact (HPRES 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20%bv = getr (ms_regs ms1) 20%bv) by exact (HPRES 20 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs2 26%bv = getr (ms_regs ms1) 26%bv) by exact (HPRES 26 ltac:(unfold acallee_saved; lia)).
(* the two view-keeps the cut needs *)
assert (KEEPS : forall a, spZ (e_regs E) - EC_SAVE <= a < spZ (e_regs E) ->
  aview SEGS (w_H (e_W E)) mem2 a = aview SEGS (w_H (e_W E)) (ms_mem ms) a).
{ intros a Ha. rewrite (KA a ltac:(unfold EC_SAVE, LLVMF_STK, ESTACK in *; lia)
    ltac:(unfold EC_SAVE, ESTACK in *; lia)).
  rewrite (KEEP2 a ltac:(unfold EC_SAVE in *; lia)), (KEEP1 a ltac:(unfold EC_SAVE in *; lia)). reflexivity. }
assert (KEEPI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H (e_W E)) mem2 a = aview SEGS (w_H (e_W E)) (e_mem E) a).
{ intros a Him Hos Her. pose proof (pa_segs_low a Him) as Hlow.
  rewrite (KC a Him Hos Her), (KEEP2 a ltac:(unfold kLowMemEnd in *; lia)),
    (KEEP1 a ltac:(unfold kLowMemEnd in *; lia)),
    (KEEP0 a ltac:(unfold kLowMemEnd in *; lia) ltac:(unfold EC_SAVE, LLVMF_STK, kLowMemEnd in *; lia)).
  reflexivity. }
(* the frame's own facts *)
assert (HFB : fs_frame_bytes LLVMF_FS_CLASS = EC_FRAME_BYTES) by (vm_compute; reflexivity).
assert (Hin2 : In (LLVMF_FS_CLASS, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (HFRA : 4096 <= frame_addr (e_ly E) LLVMF_FS_CLASS pos).
{ destruct (alx_sep SEGS B ARX l0_LAWS (e_ly E) S2 [] (e_W E) mem2 md2 (proj1 HJ2)) as (_ & HFF).
  pose proof (proj1 (Forall_forall _ _) HFF (LLVMF_FS_CLASS, pos) Hin2) as (G1 & G2).
  cbn [fst snd] in G1. lia. }
(* THE CUT *)
apply SRr_ret.
destruct HLEDe as (peak0 & most0 & own0 & HLEDe).
exists (frame_addr (e_ly E) LLVMF_FS_CLASS pos).
exists (e_ly E), S2, (@nil Z), regs2, mem2, md2, [(LLVMF_FS_CLASS, pos)], peak0, 0.
split.
{ exists fx. split; [exact Hfrz|]. split; [intros r Hr; reflexivity|].
  unfold cfg_at, EC_AR_FRAME, EC_BASE, w64. reflexivity. }
split.
{ (* ec_inv *)
  unfold ec_inv.
  split; [exists []; split; [exact HJ2 | unfold YCbqGwild.wbudget; cbn; lia]|].
  split.
  { exists pos. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    rewrite <- HFB. apply l0_rd64_of_rdword. exact Hflag. }
  split.
  { (* the ledger *)
    exists most0, own0.
    assert (GL : prh_glob (e_W E) (e_mem E) (Ledger.lsum []) peak0 (e_cnt E) SIZE_MAX (e_ran E) most0 own0)
      by (eapply prh_ledger_glob; exact HLEDe).
    split; [|split; [constructor | split; [apply Forall_nil | apply perm_nil]]].
    apply (l0_glob_keep (e_W E) (e_mem E) mem2); [|exact GL].
    intros a Hpstc. destruct (ei_pst _ _ _ _ _ _ HIM a Hpstc) as ((HNS & HNE) & HIm).
    exact (KEEPI a HIm HNS HNE). }
  split.
  { apply (ei_sio_frame _ _ _ _ _ _ HIM (aview SEGS (w_H (e_W E)) (e_mem E))); [|exact HSIOe].
    intros a Ha. destruct (ei_sio _ _ _ _ _ _ HIM a Ha) as ((HNS & HNE) & HIm & _).
    exact (KEEPI a HIm HNS HNE). }
  split.
  { intros a Hro Hos Her.
    assert (Him : in_img SEGS a).
    { destruct Hro as [(s & Hs & _ & Hr)|Hr]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hr)]. }
    rewrite (KEEPI a Him Hos Her). exact (HRODe a Hro Hos Her). }
  split; [rewrite ES2; apply RL_set_fs; exact HRLe|].
  (* the exact position of cut_frame: e_os at e_i0, ec_pre's own (the frame call makes no model event) *)
  split; [exists (e_hist0 E); rewrite ES2; apply PresetRoomPosKeep.room_pos_set_fs; exact HROOMe|].
  split; [unfold LCNT; lia|].
  split; [exact HPRE0|].
  split; [rewrite Eab2; destruct Hblkd as [(H0 & _)|(_ & H1)]; [left; exact H0 | right; exact H1]|].
  split; [rewrite Eab2; cbn [ck_hblks map app]; apply Permutation_refl|].
  split; [|exact (HMN2 HMN)].
  intros i Hi.
  destruct Hblkd as [(Hn0 & _)|(Hnpos & Hinblk)]; [lia|].
  pose proof HJ2 as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & JB & JR).
  apply (JB (e_p E) (e_n E) i Hinblk ltac:(rewrite Eab2; exact Hinblk)
    ltac:(unfold req_size; destruct (Z.eqb_spec (e_n E) 0); lia) ltac:(intros (rr & [] & _))). }
split; [reflexivity|].
split; [destruct (HCC E 0%nat 0%nat) as ((CC0 & CC1) & _); lia|].
split; [rewrite Hbb2; destruct (HLC E 0%nat 0%nat) as ((LC0 & LC1) & _); lia|].
split.
{ (* the saved block at the cut: the prologue's chunks, kept by stretches 2 and 3 and by the frame call *)
  unfold ec_saved, e_sp0.
  assert (SK8 : forall (off : Z) (n : nat) (r : bv 5), 8 <= off <= EC_SAVE ->
    YP09.chunk_ok SEGS EV (ms_mem (restrict (w_H (e_W E)) ms)) (spZ (e_regs E))
      (YP09.mkChunk (- off) (CVal 8 (SOff n 0))) ->
    (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
    rd64 (aview SEGS (w_H (e_W E)) mem2) (spZ (e_regs E) - off) (bv_unsigned (getr (e_regs E) r))).
  { intros off n r Hoff HC Hn Hr. apply (l0_rd64_keep (w_H (e_W E)) (ms_mem ms) mem2).
    - intros i Hi. apply KEEPS. unfold EC_SAVE in *. lia.
    - exact (SAV off n r HC Hn Hr). }
  assert (INC : forall (c : YP09.chunk), In c [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
    YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
    YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
    YP09.chunk_ok SEGS EV (ms_mem (restrict (w_H (e_W E)) ms)) (spZ (e_regs E)) c).
  { intros c Hc. apply HCA. cbn [In] in Hc |- *. tauto. }
  repeat split.
  - apply (SK8 8 1%nat 1%bv); [unfold EC_SAVE; lia | apply INC; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity].
  - apply (SK8 16 8%nat 8%bv); [unfold EC_SAVE; lia | apply INC; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity].
  - apply (SK8 24 9%nat 9%bv); [unfold EC_SAVE; lia | apply INC; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity].
  - apply (SK8 32 18%nat 18%bv); [unfold EC_SAVE; lia | apply INC; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity].
  - apply (SK8 40 19%nat 19%bv); [unfold EC_SAVE; lia | apply INC; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity].
  - apply (SK8 48 20%nat 20%bv); [unfold EC_SAVE; lia | apply INC; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity].
  - apply (SK8 56 21%nat 21%bv); [unfold EC_SAVE; lia | apply INC; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity].
  - apply (SK8 64 22%nat 22%bv); [unfold EC_SAVE; lia | apply INC; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity].
  - apply (SK8 72 23%nat 23%bv); [unfold EC_SAVE; lia | apply INC; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity].
  - apply (SK8 80 24%nat 24%bv); [unfold EC_SAVE; lia | apply INC; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity].
  - apply (SK8 88 25%nat 25%bv); [unfold EC_SAVE; lia | apply INC; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity].
  - apply (SK8 96 26%nat 26%bv); [unfold EC_SAVE; lia | apply INC; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity].
  - apply (SK8 104 27%nat 27%bv); [unfold EC_SAVE; lia | apply INC; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity]. }
split; [rewrite <- HFB; exact Hz|].
split; [rewrite <- HFB; exact Hfpres|].
split; [exact Ha0|].
split; [rewrite P2; exact T2'|].
split; [rewrite P3; exact T3|].
split; [rewrite P4; exact T4|].
split; [rewrite P8; exact T8'|].
split; [rewrite P9; exact T9'|].
split; [rewrite P19; exact T19|].
split; [rewrite P20; exact T20|].
rewrite P26, T26. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 6. L0b: +0x074 .. +0x120. One stretch writes the slot [A + 16], the frame header [fk, fk + 24) and the frame's
      16 shadow bytes at s10 = (fk >> 3) + SHADOW_OFF (atom 32, the alias below), and stops at the size guard. *)
Definition l1_r_slot : YP09.region := YP09.mkRegion (Some 9%nat) 16 24 16 24 [].
Definition l1_r_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition l1_r_sh : YP09.region := YP09.mkRegion (Some 32%nat) 0 16 0 16 [].
Definition l1_alias : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 26 0).
Definition l1_ss0 : sstate := mkSS 0x74 sr_atoms [l1_r_slot; l1_r_hdr; l1_r_sh] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF 4096 (2 ^ 47) 5); (32%nat, mkAF SHADOW_OFF (2 ^ 47) 0)]
    [] [(l1_alias, SOff 32 0)]).
Definition l1_E0 (regs : bvmap 5 word) (fk : Z) : env := Eimg (Ereg regs [Z_to_bv 64 (shadow_addr fk)]).

(* the frame-shadow address the body computes, `srli a2, s11, 3; add s10, a2, s10` with s11 = fk and s10 =
   SHADOW_OFF, is shadow_addr fk (H6_Base.v h6_alias_U by path, atoms renumbered) *)
Lemma l1_alias_U : forall E F, ew E 10 = Z_to_bv 64 F -> ew E 26 = Z_to_bv 64 SHADOW_OFF ->
  ew E 32 = Z_to_bv 64 (shadow_addr F) -> 0 <= F < 2 ^ 47 ->
  U E l1_alias = U E (SOff 32 0).
Proof.
intros E F E10 E26 E32 HF. unfold l1_alias.
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as D0.
assert (D1 : F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (U10 : U E (SOff 10%nat 0) = F).
{ rewrite U_SOff, E10, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.add_0_r, Z.mod_mod by lia. apply Z.mod_small. lia. }
assert (U3 : U E (SLit 3) = 3) by (rewrite U_SLit; vm_compute; reflexivity).
assert (U26 : U E (SOff 26%nat 0) = SHADOW_OFF).
{ rewrite U_SOff, E26, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.add_0_r, Z.mod_mod by lia. apply Z.mod_small. rewrite HSO. lia. }
assert (U32 : U E (SOff 32%nat 0) = shadow_addr F).
{ rewrite U_SOff, E32, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.add_0_r, Z.mod_mod by lia. apply Z.mod_small. unfold shadow_addr. rewrite HSO. lia. }
assert (Usrl : U E (SAlu ALU_SRL (SOff 10%nat 0) (SLit 3)) = F / 8).
{ rewrite U_SAlu, U10, U3. cbn [zalu_raw]. change (Z.land 3 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64. apply Z.mod_small. lia. }
rewrite U_SAlu, Usrl, U26, U32. cbn [zalu_raw]. unfold zcanon, M64, shadow_addr. rewrite HSO.
rewrite Z.mod_small by lia. lia.
Qed.

(* a one-byte chunk of a literal, read back as a byte value (the frame's shadow bytes the stretch stores) *)
Lemma l1_byte_chunk : forall (EV : env) (m : word -> option byte) base off (v t : Z),
  YP09.chunk_ok SEGS EV m base (YP09.mkChunk off (CVal 1 (SLit v))) -> 0 <= v < 2 ^ 64 -> v mod 256 = t ->
  val_mem SEGS m (base + off) 1 t.
Proof.
intros EV m base off v t HC Hv Ht k Hk. assert (k = 0%nat) as -> by lia.
pose proof (Z.mod_pos_bound v 256 ltac:(lia)) as Hm.
destruct (HC 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_off YP09.c_val sv_denot] in Hb1, Hb2. injection Hb1 as Hb.
cbn [Z.of_nat]. rewrite !Z.add_0_r in Hb2 |- *. rewrite Hb2. f_equal. rewrite <- Hb.
rewrite le_byte_small by (cbn; lia).
unfold byte_of_word. cbn [Z.of_nat]. rewrite !Z.mul_0_r, !Z.shiftr_0_r.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite <- Ht. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Theorem seg_L0b_A :
  @seg_L0b_stmt fx rc ci cp PI RL A_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut.
Proof.
unfold seg_L0b_stmt, ec_lane.
intros E fk HHYP W c Hcut.
pose proof (ech_img _ _ _ _ _ _ _ _ _ _ HHYP) as HIM.
pose proof (ech_lcut_ok _ _ _ _ _ _ _ _ _ _ HHYP) as HLC.
pose proof (ech_ccut_ok _ _ _ _ _ _ _ _ _ _ HHYP) as HCC.
destruct Hcut as (ly & S & Hp & regs & mem & md & own & peak & k & Hat & Hinv & HHp & HCC0 & HLC0 & Hsav & Hzs & Hfp
  & R10 & R2 & R3 & R4 & R8 & R9 & R19 & R20 & R26).
subst Hp.
destruct Hat as (fy & Hfz & Hfkp & ->).
(* ec_inv's and ec_pre's parts BY NAME (section 2') *)
pose proof (l0_inv_jp Hinv) as HJ. pose proof (l0_inv_own Hinv) as Hown.
destruct (Ent102CallA.ec_inv_ledger (fx := fx) B SK EC_RA EC_EMPTY EC_SIO Hinv) as (most1 & own1 & HLED).
pose proof (l0_inv_sio Hinv) as HSIO. pose proof (l0_inv_rod Hinv) as HROD. pose proof (l0_inv_rl Hinv) as HRL.
pose proof (l0_inv_pos Hinv) as HROOM. pose proof (l0_inv_cnt Hinv) as HCNT.
pose proof (Ent102CallA.ec_inv_pre (fx := fx) B SK EC_RA EC_EMPTY EC_SIO Hinv) as HPRE0.
pose proof (Ent102CallA.ec_inv_pay (fx := fx) B SK EC_RA EC_EMPTY EC_SIO Hinv) as HBLK.
pose proof (Ent102CallA.ec_inv_perm (fx := fx) B SK EC_RA EC_EMPTY EC_SIO Hinv) as HPERM.
pose proof (Ent102CallA.ec_inv_bytes (fx := fx) B SK EC_RA EC_EMPTY EC_SIO Hinv) as HPAY.
pose proof (l0_inv_mn Hinv) as HMN.
destruct Hown as (pos & Hown & Hfkeq & Hfk0 & Hflag). subst own.
l0_pre_parts HPRE0.
pose proof HPREx as (HARe & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ei_pal _ _ _ _ _ _ HIM) as PAL.
pose proof HJ as (HAR & J2 & J3 & J4 & J5 & Jfr & J7 & J8 & J9 & JB & J11 & J12 & J13 & Jpres & J15 & J16 & J17).
assert (Hin : In (LLVMF_FS_CLASS, pos) (frames S)) by (rewrite Jfr, HfrS; left; reflexivity).
destruct (alx_frames SEGS B ARX l0_LAWS ly S [] W mem md LLVMF_FS_CLASS pos HAR Hin) as (Fal & Fapp & Fby & Fsh).
destruct (alx_sep SEGS B ARX l0_LAWS ly S [] W mem md HAR) as (_ & HFF).
pose proof (proj1 (Forall_forall _ _) HFF (LLVMF_FS_CLASS, pos) Hin) as (G1 & G2). cbn [fst snd] in G1, G2.
rewrite <- Hfkeq in Fal, Fapp, Fby, Fsh, G1, G2.
change (fs_frame_bytes LLVMF_FS_CLASS / 8) with 16 in Fsh.
change (fs_frame_bytes LLVMF_FS_CLASS) with 128 in Fapp, Fby, G2.
assert (HAdiv : e_A E = (spZ (e_regs E) - 128) / 32 * 32)
  by (unfold e_A, ec_A, e_sp0, EC_SAVE; apply l0_land_neg32; lia).
assert (HAlo1 : spZ (e_regs E) - 160 < e_A E <= spZ (e_regs E) - 128).
{ rewrite HAdiv. pose proof (Z.mul_div_le (spZ (e_regs E) - 128) 32 ltac:(lia)).
  pose proof (Z.mod_pos_bound (spZ (e_regs E) - 128) 32 ltac:(lia)).
  pose proof (Z.div_mod (spZ (e_regs E) - 128) 32 ltac:(lia)). lia. }
assert (HAmod : e_A E mod 32 = 0) by (rewrite HAdiv; apply Z_mod_mult).
(* the entry state of the stretch *)
set (EV := l1_E0 regs fk).
assert (HEI : img_env VAL A_LIM EV) by (unfold EV, l1_E0; apply Eimg_env).
assert (EWr : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew EV n = getr regs r).
{ intros n r Hn Hr. unfold EV, l1_E0. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ n r Hr). }
assert (E32 : ew EV 32 = Z_to_bv 64 (shadow_addr fk))
  by (unfold EV, l1_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (Hsh8 : 8 * (fk / 8) <= fk < 8 * (fk / 8) + 8)
  by (pose proof (Z.div_mod fk 8 ltac:(lia)); pose proof (Z.mod_pos_bound fk 8 ltac:(lia)); lia).
assert (U9 : bv_unsigned (ew EV 9) = e_A E)
  by (rewrite (EWr 9%nat 9%bv ltac:(lia) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew EV 10) = fk)
  by (rewrite (EWr 10%nat 10%bv ltac:(lia) eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew EV 32) = shadow_addr fk)
  by (rewrite E32; apply unsigned_lit_small; unfold shadow_addr; lia).
assert (HS0 : st_ok_pi SEGS VAL EV l1_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x74)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold l1_ss0. apply pa_entry_st_ok_full.
  - unfold EV, l1_E0. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold l1_r_slot, l1_r_hdr, l1_r_sh.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Jpres. unfold LLVMF_STK, e_sp0 in *. lia.
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (Fby (fk + o)). lia.
    + rewrite U32. split; [unfold shadow_addr; lia|]. split; [unfold shadow_addr; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (Fsh o). lia.
  - apply pairwise_disjoint_of_extents.
    unfold l1_r_slot, l1_r_hdr, l1_r_sh, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U10, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, LLVMF_STK in *.
    repeat split; lia.
  - split; [|split].
    + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U10, U32. change (2 ^ 5) with 32. change (2 ^ 0) with 1.
      rewrite Z.mod_1_r. unfold shadow_addr. repeat split; lia.
    + exact I.
    + cbn [f_alias alias_ok]. split; [|exact I]. apply bv_eq. fold (U EV l1_alias). fold (U EV (SOff 32 0)).
      apply (l1_alias_U EV fk).
      * rewrite (EWr 10%nat 10%bv ltac:(lia) eq_refl). exact R10.
      * rewrite (EWr 26%nat 26%bv ltac:(lia) eq_refl). exact R26.
      * exact E32.
      * lia. }
assert (SHOK : sh_ok SEGS L0_Bx [] EV (mrestrict (w_H W) mem)) by apply Forall_nil.
(* fx (the Section's) and fy (the cut's frozen FP state) are both in scope here: the instances go BY NAME *)
pose (RUN := paj_run_x_inv (fx := fy) (rc := rc) (SK := SK) (L := A_prog_listing) (PL := PL_102_A) (PI := PA)
  B PST ARX (HL := cf_head) l0_LAWS (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS)).
assert (Hpc : w64 EC_AR_FRAME = Z_to_bv 64 (BASE + 0x74)) by reflexivity.
unfold cfg_at. rewrite Hpc.
assert (AWR0 : awr_ok EV (ss_mem l1_ss0) LLVMF_STK (e_sp0 E) [] (ablocks B (e_ly E) (e_S E)) (ablocks B ly S) ly
  [(LLVMF_FS_CLASS, pos)]).
{ intros a (r & Hr & Ha). unfold l1_ss0 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]];
  cbn [l1_r_slot l1_r_hdr l1_r_sh YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?U9, ?U10, ?U32 in Ha; unfold awr_byte.
  - left. unfold LLVMF_STK, e_sp0 in *. lia.
  - right; right; right. exists LLVMF_FS_CLASS, pos. split; [left; reflexivity|].
    left. unfold in_zr; cbn [fst snd]. rewrite <- Hfkeq. change (fs_frame_bytes LLVMF_FS_CLASS) with 128. lia.
  - right; right; right. exists LLVMF_FS_CLASS, pos. split; [left; reflexivity|].
    right. unfold in_zr; cbn [fst snd]. rewrite <- Hfkeq. change (fs_frame_bytes LLVMF_FS_CLASS / 8) with 16. lia. }
paj_run_tok_x_inv RUN HS0 HJ SHOK HMN L0_Bspan.
{ exact AWR0. }
rename HF into HF1. rename HFr into HFr1. rename HG into HG1.
(* what lies off the stretch's three write windows, and the image below the frame *)
assert (NW : forall a, ~ (e_A E + 16 <= a < e_A E + 24) -> ~ (fk <= a < fk + 24) ->
  ~ (shadow_addr fk <= a < shadow_addr fk + 16) -> ~ in_wrange EV (ss_mem l1_ss0) a).
{ intros a N1 N2 N3 (r & Hr & Hb). unfold l1_ss0 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]];
  cbn [l1_r_slot l1_r_hdr l1_r_sh YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  rewrite ?U9, ?U10, ?U32 in Hb; lia. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange EV (ss_mem l1_ss0) a ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hw. exact (l0_aview_kept W EV (ss_mem l1_ss0) mem (ms_mem ms) a HFr1 Ha Hw). }
destruct (alx_img SEGS B ARX l0_LAWS ly S [] W mem md HAR) as (HIS & HIF).
assert (HIMG : forall a, in_img SEGS a -> a < fk /\ a < kLowMemEnd).
{ intros a Him. pose proof (pa_segs_low a Him) as Hlow. destruct Him as (sg & Hsg & Ha).
  pose proof (HIS sg Hsg) as (Q1 & Q2). pose proof (HIF LLVMF_FS_CLASS pos Hin) as Q3. rewrite <- Hfkeq in Q3. lia. }
assert (Hshb : SHADOW_OFF <= shadow_addr fk /\ shadow_addr fk + 16 < 2 ^ 45) by (unfold shadow_addr; lia).
pose (RUNTO := paj_run_to_x_inv (fx := fy) (rc := rc) (SK := SK) (L := A_prog_listing) (PL := PL_102_A) (PI := PA)
  B PST ARX (HL := cf_head) l0_LAWS (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS)).
pose (BR := paj_branch (fx := fy) (rc := rc) (L := A_prog_listing) (PI := PA)).
psrr_branch_tok RUN BR HS0 SHOK L0_Bspan.
- (* the guard is taken: n > PRESET_FILE_MAX_BYTES (+0x120 `bltu a0, s3`), to EXIT *)
  assert (HNBx : EC_NMAX < e_n E).
  { assert (Hn64 : 0 <= e_n E < 2 ^ 64) by (destruct Hblkd as [(Hn0 & _)|((Hn1 & Hn2) & _)]; lia).
    rewrite branch_ltu_U, U_SLit, (U_atom EV 19%nat (e_n E)) in Hc;
      [| rewrite (EWr 19%nat 19%bv ltac:(lia) eq_refl), R19; reflexivity | exact Hn64].
    change (zcanon 3145728) with 3145728 in Hc. apply Z.ltb_lt in Hc. unfold EC_NMAX. lia. }
  paj_run_to_tok_x_inv RUNTO HS0 HJ SHOK HMN L0_Bspan 0x1c4.
  { intros a Ha. apply AWR0. eapply in_wrange_skeleton; [|exact Ha]. vm_compute. reflexivity. }
  rename HF into HF2. rename HFr into HFr2. rename HG into HG2.
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange EV (ss_mem l1_ss0) a ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
  { intros a Ha Hw. rewrite <- (KEEP1 a Ha Hw). apply (l0_aview_kept W EV _ (ms_mem ms) (ms_mem ms0) a HFr2 Ha).
    intros Hw2. apply Hw. eapply in_wrange_skeleton; [|exact Hw2]. vm_compute. reflexivity. }
  assert (KEEPI : forall a, in_img SEGS a -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
  { intros a Him. destruct (HIMG a Him) as (Hb1 & Hb2). pose proof (pa_segs_low a Him) as Hlow.
    apply KEEPF; [unfold kLowMemEnd in *; lia|]. apply NW; unfold LLVMF_STK, e_sp0, kLowMemEnd in *; lia. }
  assert (KS : forall a v, e_sp0 E - 104 <= a -> a + 8 <= e_sp0 E ->
    rd64 (aview SEGS (w_H W) mem) a v -> rd64 (aview SEGS (w_H W) (ms_mem ms0)) a v).
  { intros a v Ha1 Ha2 Hr. apply (l0_rd64_keep (w_H W) mem (ms_mem ms0) a v); [|exact Hr].
    intros i Hi. apply KEEPF; [unfold e_sp0 in *; lia|]. apply NW; unfold LLVMF_STK, e_sp0 in *; lia. }
  pose proof (st_ok_mem_ok SEGS _ _ _ HS0) as (_ & HMO & _). cbn [ss_mem add_cond] in HMO.
  apply Forall_inv_tail in HMO. apply Forall_inv_tail in HMO. apply Forall_inv in HMO.
  destruct HMO as (_ & _ & _ & HCH3). cbn [YP09.r_chunks YP09.r_base base_val] in HCH3. rewrite U32 in HCH3.
  pose proof (proj1 (Forall_forall _ _) HCH3) as HCA3.
  pmkst HS0.
  prreg HS0 (2%bv : bv 5) T2. prreg HS0 (3%bv : bv 5) T3. prreg HS0 (4%bv : bv 5) T4.
  prreg HS0 (8%bv : bv 5) T8. prreg HS0 (9%bv : bv 5) T9. prreg HS0 (18%bv : bv 5) T18.
  prreg HS0 (19%bv : bv 5) T19. prreg HS0 (20%bv : bv 5) T20. prreg HS0 (26%bv : bv 5) T26.
  prreg HS0 (27%bv : bv 5) T27.
  apply SRr_ret. right.
  exists ly, S, (@nil Z), (ms_regs ms0), (ms_mem ms0). eexists.
  (* the call's grant triple: none is taken above MAXB, any triple serves; (None, None, None) *)
  exists [(LLVMF_FS_CLASS, pos)], peak, (e_cnt E), (e_ran E), k, (None, None, None).
  split.
  { exists fy. split; [exact Hfz|]. split; [exact Hfkp|]. unfold cfg_at, EC_EXIT, EC_BASE, w64. reflexivity. }
  split.
  { unfold ec_inv.
    split; [exists []; split; [exact HJ | unfold YCbqGwild.wbudget; cbn; lia]|].
    split.
    { exists pos. split; [reflexivity|]. split; [exact Hfkeq|]. split; [exact Hfk0|].
      apply (l0_rd64_keep (w_H W) mem (ms_mem ms0)); [|exact Hflag].
      intros i Hi. unfold EC_FRAME_BYTES, LLVMF_STK, e_sp0 in *. apply KEEPF; [lia|]. apply NW; [lia | lia |].
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr in *. lia. }
    split.
    { exists most1, own1.
      assert (GL : prh_glob W mem (Ledger.lsum []) peak (e_cnt E) SIZE_MAX (e_ran E) most1 own1)
        by (eapply prh_ledger_glob; exact HLED).
      split; [|split; [constructor | split; [apply Forall_nil | apply perm_nil]]].
      apply (l0_glob_keep W mem (ms_mem ms0)); [|exact GL].
      intros a Hpstc. destruct (ei_pst _ _ _ _ _ _ HIM a Hpstc) as (_ & HIm). exact (KEEPI a HIm). }
    split.
    { apply (ei_sio_frame _ _ _ _ _ _ HIM (aview SEGS (w_H W) mem)); [|exact HSIO].
      intros a Ha. destruct (ei_sio _ _ _ _ _ _ HIM a Ha) as (_ & HIm & _). exact (KEEPI a HIm). }
    split.
    { intros a Hro Hos Her.
      assert (Him : in_img SEGS a).
      { destruct Hro as [(s & Hs & _ & Hr)|Hr]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hr)]. }
      rewrite (KEEPI a Him). exact (HROD a Hro Hos Her). }
    split; [exact HRL|]. split; [exact (l0_pos_exit E S HPRE0 HNBx HROOM)|]. split; [exact HCNT|].
    split; [exact HPRE0|].
    split; [exact HBLK|]. split; [exact HPERM|].
    split; [|exact HMN].
    intros i Hi.
    destruct Hblkd as [(Hn0 & _)|(Hnpos & Hinblk)]; [lia|].
    destruct HBLK as [Hn0|Hinblk2]; [lia|].
    pose proof HJ as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & KB & KR).
    apply (KB (e_p E) (e_n E) i Hinblk Hinblk2
      ltac:(unfold req_size; destruct (Z.eqb_spec (e_n E) 0); lia) ltac:(intros (rr & [] & _))). }
  split; [reflexivity|].
  split; [destruct (HCC E 0%nat 11%nat) as (_ & HC11); specialize (HC11 ltac:(lia)); lia|].
  split; [destruct (HLC E 0%nat 11%nat) as (_ & HL11); specialize (HL11 ltac:(lia)); lia|].
  split.
  { unfold ec_rk.
    split; [rewrite T2, (EWr 2%nat 2%bv ltac:(lia) eq_refl); exact R2|].
    split; [rewrite T3, (EWr 3%nat 3%bv ltac:(lia) eq_refl); exact R3|].
    split; [rewrite T4, (EWr 4%nat 4%bv ltac:(lia) eq_refl); exact R4|].
    split; [rewrite T8, (EWr 8%nat 8%bv ltac:(lia) eq_refl); exact R8|].
    split; [rewrite T9, (EWr 9%nat 9%bv ltac:(lia) eq_refl); exact R9|].
    split; [rewrite T18, (EWr 10%nat 10%bv ltac:(lia) eq_refl); exact R10|].
    split; [rewrite T19, (EWr 19%nat 19%bv ltac:(lia) eq_refl); exact R19|].
    split; [rewrite T20, (EWr 20%nat 20%bv ltac:(lia) eq_refl); exact R20|].
    split; [rewrite T26, E32; reflexivity|].
    rewrite T27, (EWr 10%nat 10%bv ltac:(lia) eq_refl); exact R10. }
  { unfold ec_frame.
    split; [unfold ec_saved in *; destruct Hsav as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13);
            repeat split; (apply KS; [lia | lia | assumption])|].
    split; [|exact Fal].
    assert (SHB : forall off v t,
      YP09.chunk_ok SEGS EV (ms_mem (restrict (w_H W) ms0)) (shadow_addr fk) (YP09.mkChunk off (CVal 1 (SLit v))) ->
      0 <= v < 2 ^ 64 -> v mod 256 = t -> val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (shadow_addr fk + off) 1 t)
      by (intros off v t HC Hv Ht; exact (l1_byte_chunk EV _ _ off v t HC Hv Ht)).
    unfold garr8. intros j Hj. unfold ec_frame_shadow in Hj |- *. cbn [length repeat app] in Hj.
    do 16 (destruct j as [|j];
      [ cbn [nth repeat app Z.of_nat]; split;
        [ eapply SHB; [ apply HCA3; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity ]
        | lia ]
      | ]).
    lia. }
- (* the guard is not taken: n <= PRESET_FILE_MAX_BYTES, fall through to +0x124 *)
  assert (HNB : e_n E <= EC_NMAX).
  { assert (Hn64 : 0 <= e_n E < 2 ^ 64) by (destruct Hblkd as [(Hn0 & _)|((Hn1 & Hn2) & _)]; lia).
    rewrite branch_ltu_U, U_SLit, (U_atom EV 19%nat (e_n E)) in Hc;
      [| rewrite (EWr 19%nat 19%bv ltac:(lia) eq_refl), R19; reflexivity | exact Hn64].
    change (zcanon 3145728) with 3145728 in Hc. apply Z.ltb_ge in Hc. unfold EC_NMAX. lia. }
  paj_run_to_tok_x_inv RUNTO HS0 HJ SHOK HMN L0_Bspan 0x124.
  { intros a Ha. apply AWR0. eapply in_wrange_skeleton; [|exact Ha]. vm_compute. reflexivity. }
  rename HF into HF2. rename HFr into HFr2. rename HG into HG2.
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange EV (ss_mem l1_ss0) a ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
  { intros a Ha Hw. rewrite <- (KEEP1 a Ha Hw). apply (l0_aview_kept W EV _ (ms_mem ms) (ms_mem ms0) a HFr2 Ha).
    intros Hw2. apply Hw. eapply in_wrange_skeleton; [|exact Hw2]. vm_compute. reflexivity. }
  assert (KEEPI : forall a, in_img SEGS a -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
  { intros a Him. destruct (HIMG a Him) as (Hb1 & Hb2). pose proof (pa_segs_low a Him) as Hlow.
    apply KEEPF; [unfold kLowMemEnd in *; lia|]. apply NW; unfold LLVMF_STK, e_sp0, kLowMemEnd in *; lia. }
  assert (KS : forall a v, e_sp0 E - 104 <= a -> a + 8 <= e_sp0 E ->
    rd64 (aview SEGS (w_H W) mem) a v -> rd64 (aview SEGS (w_H W) (ms_mem ms0)) a v).
  { intros a v Ha1 Ha2 Hr. apply (l0_rd64_keep (w_H W) mem (ms_mem ms0) a v); [|exact Hr].
    intros i Hi. apply KEEPF; [unfold e_sp0 in *; lia|]. apply NW; unfold LLVMF_STK, e_sp0 in *; lia. }
  pose proof (st_ok_mem_ok SEGS _ _ _ HS0) as (_ & HMO & _). cbn [ss_mem add_cond] in HMO.
  apply Forall_inv_tail in HMO. apply Forall_inv_tail in HMO. apply Forall_inv in HMO.
  destruct HMO as (_ & _ & _ & HCH3). cbn [YP09.r_chunks YP09.r_base base_val] in HCH3. rewrite U32 in HCH3.
  pose proof (proj1 (Forall_forall _ _) HCH3) as HCA3.
  pmkst HS0.
  prreg HS0 (2%bv : bv 5) T2. prreg HS0 (3%bv : bv 5) T3. prreg HS0 (4%bv : bv 5) T4.
  prreg HS0 (8%bv : bv 5) T8. prreg HS0 (9%bv : bv 5) T9. prreg HS0 (18%bv : bv 5) T18.
  prreg HS0 (19%bv : bv 5) T19. prreg HS0 (20%bv : bv 5) T20. prreg HS0 (26%bv : bv 5) T26.
  prreg HS0 (27%bv : bv 5) T27.
  apply SRr_ret. left.
  exists ly, S, (@nil Z), (ms_regs ms0), (ms_mem ms0). eexists.
  exists [(LLVMF_FS_CLASS, pos)], peak, k.
  split.
  { exists fy. split; [exact Hfz|]. split; [exact Hfkp|]. unfold cfg_at, EC_S1, EC_BASE, w64. reflexivity. }
  split.
  { unfold ec_inv.
    split; [exists []; split; [exact HJ | unfold YCbqGwild.wbudget; cbn; lia]|].
    split.
    { exists pos. split; [reflexivity|]. split; [exact Hfkeq|]. split; [exact Hfk0|].
      apply (l0_rd64_keep (w_H W) mem (ms_mem ms0)); [|exact Hflag].
      intros i Hi. unfold EC_FRAME_BYTES, LLVMF_STK, e_sp0 in *. apply KEEPF; [lia|]. apply NW; [lia | lia |].
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr in *. lia. }
    split.
    { exists most1, own1.
      assert (GL : prh_glob W mem (Ledger.lsum []) peak (e_cnt E) SIZE_MAX (e_ran E) most1 own1)
        by (eapply prh_ledger_glob; exact HLED).
      split; [|split; [constructor | split; [apply Forall_nil | apply perm_nil]]].
      apply (l0_glob_keep W mem (ms_mem ms0)); [|exact GL].
      intros a Hpstc. destruct (ei_pst _ _ _ _ _ _ HIM a Hpstc) as (_ & HIm). exact (KEEPI a HIm). }
    split.
    { apply (ei_sio_frame _ _ _ _ _ _ HIM (aview SEGS (w_H W) mem)); [|exact HSIO].
      intros a Ha. destruct (ei_sio _ _ _ _ _ _ HIM a Ha) as (_ & HIm & _). exact (KEEPI a HIm). }
    split.
    { intros a Hro Hos Her.
      assert (Him : in_img SEGS a).
      { destruct Hro as [(s & Hs & _ & Hr)|Hr]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hr)]. }
      rewrite (KEEPI a Him). exact (HROD a Hro Hos Her). }
    split; [exact HRL|]. split; [exact HROOM|]. split; [exact HCNT|]. split; [exact HPRE0|].
    split; [exact HBLK|]. split; [exact HPERM|].
    split; [|exact HMN].
    intros i Hi.
    destruct Hblkd as [(Hn0 & _)|(Hnpos & Hinblk)]; [lia|].
    destruct HBLK as [Hn0|Hinblk2]; [lia|].
    pose proof HJ as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & KB & KR).
    apply (KB (e_p E) (e_n E) i Hinblk Hinblk2
      ltac:(unfold req_size; destruct (Z.eqb_spec (e_n E) 0); lia) ltac:(intros (rr & [] & _))). }
  split; [reflexivity|].
  split; [destruct (HCC E 0%nat 1%nat) as (_ & HC1); specialize (HC1 ltac:(lia)); lia|].
  split; [destruct (HLC E 0%nat 1%nat) as (_ & HL1); specialize (HL1 ltac:(lia)); lia|].
  split.
  { unfold ec_rk.
    split; [rewrite T2, (EWr 2%nat 2%bv ltac:(lia) eq_refl); exact R2|].
    split; [rewrite T3, (EWr 3%nat 3%bv ltac:(lia) eq_refl); exact R3|].
    split; [rewrite T4, (EWr 4%nat 4%bv ltac:(lia) eq_refl); exact R4|].
    split; [rewrite T8, (EWr 8%nat 8%bv ltac:(lia) eq_refl); exact R8|].
    split; [rewrite T9, (EWr 9%nat 9%bv ltac:(lia) eq_refl); exact R9|].
    split; [rewrite T18, (EWr 10%nat 10%bv ltac:(lia) eq_refl); exact R10|].
    split; [rewrite T19, (EWr 19%nat 19%bv ltac:(lia) eq_refl); exact R19|].
    split; [rewrite T20, (EWr 20%nat 20%bv ltac:(lia) eq_refl); exact R20|].
    split; [rewrite T26, E32; reflexivity|].
    rewrite T27, (EWr 10%nat 10%bv ltac:(lia) eq_refl); exact R10. }
  split; [|exact HNB].
  { unfold ec_frame.
    split; [unfold ec_saved in *; destruct Hsav as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13);
            repeat split; (apply KS; [lia | lia | assumption])|].
    split; [|exact Fal].
    assert (SHB : forall off v t,
      YP09.chunk_ok SEGS EV (ms_mem (restrict (w_H W) ms0)) (shadow_addr fk) (YP09.mkChunk off (CVal 1 (SLit v))) ->
      0 <= v < 2 ^ 64 -> v mod 256 = t -> val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (shadow_addr fk + off) 1 t)
      by (intros off v t HC Hv Ht; exact (l1_byte_chunk EV _ _ off v t HC Hv Ht)).
    unfold garr8. intros j Hj. unfold ec_frame_shadow in Hj |- *. cbn [length repeat app] in Hj.
    do 16 (destruct j as [|j];
      [ cbn [nth repeat app Z.of_nat]; split;
        [ eapply SHB; [ apply HCA3; cbn [In]; repeat (first [left; reflexivity | right]) | lia | reflexivity ]
        | lia ]
      | ]).
    lia. }
Qed.

End D.

Print Assumptions seg_L0a_A.
Print Assumptions seg_L0b_A.
(* the ELABORATED statements (every class-implicit instance shown) *)
Local Set Printing Implicit.
About seg_L0a_A.
About seg_L0b_A.
