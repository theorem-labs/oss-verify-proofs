(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of arg_line (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, entry 0x8b128 = BASE + AF_arg_line, 304 bytes, 76 instructions): targ_line_spec of a Theorem Labs lane's
   lib/B/Prog/arg_line_c.v, proved as stated, over its callee contract rec_canonical_c and the strlen wrapper, each
   taken at the walk's FP state (the statement states them at every FP state).

   The B re-walk of the A walk lib/A/Prog/arg_line.v (a Theorem Labs lane a60bdbabd8f), on B's code as measured with capstone
   (symbol-keyed; B adds five UBSan trap branches and a fourth inline check, the store4 of c->nargs; the calls and the
   shadow-check pattern are A's). arg_line(c, line) (recorder.c:229-233): c in a0, line in a1; s1 = c, s0 = c + 4,
   s4 = the shadow byte address of c + 4, s3 = the shadow base (through the GOT word 0xa5f50 = A_OBJ 0 and the cell
   0xb0c38 = A_OBJ 12: an auipc-paired object slot, so no A_HI value is read). c->nargs is read once before the calls
   and once after them; the path splits on it (c->nargs = 6: return, al_walk6; c->nargs < 6: strlen, rec_canonical,
   c->nargs := m + 1, c->args[m] := p, al_walk_lt). On the second path c->nargs is an atom of value 0..5 up to the
   last segment, where the walk splits it into its six values, so that the stores' addresses are constant offsets
   of c.

   Report and UBSan trap edges, each refuted at its branch by the token executor's run (CmdPaLib.v's paj_run, sound by
   SRr_run_pi_tok_AJ), which decides the branch from the symbolic state's shadow entry al_SH (a check) or its facts
   (a trap):
     0x8b224 (__asan_report_load4; guards 0x8b174 bnez, 0x8b21c blt): refuted by the check token of the run at
       al_walk6 / al_walk_lt's first paj_run_tok, from sh_ok al_SH of al_entry / al_entry_lt, i.e. al_slot_addressable
       (the slot premise: c + 4 is in g_rec's or record.spill's zero-shadow range, CmdZsh.cmd_addressable_in).
     0x8b238 (__asan_report_load4; guards 0x8b19c bnez, 0x8b230 blt), 0x8b24c (__asan_report_store4; guards 0x8b1b0
       bnez, 0x8b244 blt), 0x8b254 (__asan_report_store8; guard 0x8b1e8 bnez): refuted by the check tokens of
       al_walk_lt's last paj_run_tok, from SHOK3 (al_slot_addressable at the state after rec_canonical; c + 4 and
       c + 8 + 8m lie in [c, c + 56)), from the slot premise.
     0x8b144 (beqz c -> unimp 0x8b210): refuted by the run's facts: atom 10 = c lies in [A_G_REC, A_REC_SPILL]
       (al_facts / al_facts_lt, facts_ok by al_entry / al_entry_lt's HG), from the slot premise (al_slot_facts).
     0x8b150 (bnez (c & 7) -> unimp): refuted by the same facts' alignment (af_al2 = 3: c mod 8 = 0, al_slot_facts).
     0x8b1a8 (blt (m + 1) m, the signed overflow of c->nargs++): refuted by al_walk_lt's last run on the literal m,
       one of 0..5 (the nargs premise m <= 6 and the branch at 0x8b180, which the first run decides on atom 33's fact
       0 <= m <= 5; the slot is outside rec_canonical's footprint, so the value reloaded at 0x8b1a0 is m: VN).
     0x8b1c4 (beqz (c + 8 + 8m)) and 0x8b1d8 (the pointer c + 8 + 8m wraps below c + 8): refuted by al_walk_lt's last
       run, from the facts on atom 10 (c in [A_G_REC, A_REC_SPILL]) and the literal m.

   Section hypotheses beyond the statement's (named as the lemmas a Theorem Labs lane states only at PI := PB_cmd): HB (CmdBSyms,
   the per-binary allocator record), MTL (the meter's laws), cmd_val_objs_PB (CmdObj.v's cmd_val_objs: the GOT word and
   the shadow cell), cmd_sig_prog_PB (CmdObj.v's cmd_sig_prog: rec_canonical's call target), cmd_img_facts_tfib
   (a Theorem Labs lane's CmdRecImg.v lemma, at this walk's abstract segments) and PRW (the core's prog_rw, for CmdRecCells'
   PROG_WRITABLE: the two stores into the slot). LAWS is AR_laws_ok; PALib's fields are CmdRecCells' cmd_cf_got,
   cmd_cf_cell and cmd_cf_env. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaDenot PaLibG PaLibF PaCall PaArt CmdBase CmdRep CmdObj CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c rec_canonical_c arg_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* aval_mem over aview and YI04's val_mem over the restricted memory are the same statement; the two read
   le_byte from two copies of the same definition (YG0f, YO0f). *)
Lemma al_le_byte_range : forall v n k, 0 <= YO0f.le_byte v n k < 256.
Proof. intros v n k. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma al_aval_of_val_mem : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by apply al_le_byte_range. reflexivity.
Qed.

(* the call slot c: a slot of g_rec's call table or record.spill (arg_line_c.v:85) *)
Definition al_slot (c : Z) : Prop :=
(exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL.
Lemma al_slot_facts : forall c, al_slot c ->
c mod 8 = 0 /\ A_G_REC + 16 <= c <= A_REC_SPILL /\ (forall a, c <= a < c + 56 -> inFP cmd_PG a).
Proof.
unfold al_slot, cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX.
intros c [(i & Hi & ->) | ->].
- split; [|split; [lia|]].
  + replace (0x5e32c0 + 16 + 56 * i) with ((771674 + 7 * i) * 8) by lia. apply Z_mod_mult.
  + intros a Ha. eexists. split; [left; reflexivity | cbn [fst snd]; lia].
- split; [reflexivity|]. split; [lia|]. intros a Ha. eexists. split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* The symbolic state at the entry. Atoms: 0..31 the registers at the entry (a0 = c is atom 10, a1 = line is
   atom 11, sp atom 2), 32 the shadow base 0x7fff8000, A_OBJ 0 / A_OBJ 12 the GOT word and the shadow-base cell.
   Regions: arg_line's 48-byte frame; the GOT word and the cell (read-only); c->nargs [c + 4, c + 8) holding the
   value k, read-only up to the last segment. The last segment (after rec_canonical returns) makes c->nargs
   writable and adds c->args[k] [c + 8 + 8k, c + 16 + 8k), so the runs before it keep the slot byte for byte.
   The one shadow entry [c, c + 56) removes the four inline checks: each reads the shadow of c + 4 or
   c + 8 + 8k. The facts on atom 10 (c in [A_G_REC, A_REC_SPILL], 8-aligned) decide the UBSan traps 0x8b144,
   0x8b150, 0x8b1c4 and 0x8b1d8. *)
Definition al_Bx : sv := SOff 32 0.
Definition al_SH : list shent := [mkSHE 10 0 56].
Definition al_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition al_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF A_G_REC A_REC_SPILL 3); (32%nat, mkAF SB SB 0)] [] [].
Definition al_nargs (k : Z) (w : bool) : YP09.region :=
YP09.mkRegion (Some 10%nat) 4 8 4 (if w then 8 else 4) [YP09.mkChunk 4 (CVal 4 (SLit k))].
Definition al_arg (k : Z) : YP09.region :=
YP09.mkRegion (Some 10%nat) (8 + 8 * k) (16 + 8 * k) (8 + 8 * k) (16 + 8 * k) [].
Definition al_regs (k : Z) : smem := [stack_region 48; got_regionP; bcell_regionP 32; al_nargs k false].
Definition al_ss (rs : smem) : sstate := mkSS AF_arg_line sr_atoms rs None al_facts.
Definition al_extra : list word := map (Z_to_bv 64) [SB].

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's callee contract and runtime entry, each at every FP state (arg_line_c.v:73-74) *)
Hypothesis TREC_CANONICAL : forall fx0 : YK11.FPState, @trec_canonical_spec fx0 rc SK PI B MT.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @astrlen_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strlen).
(* the walk hypotheses: the per-binary allocator record (a Theorem Labs lane's lib/B/YF0m.v), the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
(* a Theorem Labs lane's lemmas stated only at the pinned image (PI := PB_cmd, CmdRecRest.v cmd_val_objs_PB / cmd_sig_prog_PB,
   CmdRecImg.v cmd_img_facts_tfib), here at this walk's abstract PAImg under the lemmas' names *)
Hypothesis cmd_val_objs_PB : cmd_val_objs.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
(* the core's prog_rw (YCbq.v:1145): g_rec's and record.spill's bytes are writable (CmdRecCells' PROG_WRITABLE) *)
Hypothesis PRW : prog_rw SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let HBgot : as_got_shadow B = VAL (A_OBJ 0) := cmd_cf_got B HB cmd_val_objs_PB.
Let HBcell : as_shadow_cell B = VAL (A_OBJ 12) := cmd_cf_cell B HB cmd_val_objs_PB.
Let ENV : api_env SEGS B := cmd_cf_env SEGS B LAWS HB IMG.
Let RUN := paj_run B LAWS.
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

Lemma al_obj0 : VAL (A_OBJ 0) = 0xa5f50.
Proof. exact (cmd_val_objs_PB 0%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)). Qed.
Lemma al_obj12 : VAL (A_OBJ 12) = 0xb0c38.
Proof. exact (cmd_val_objs_PB 12%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)). Qed.

Lemma al_stk : ARG_LINE_STK = 16480.
Proof. vm_compute. reflexivity. Qed.

(* the slot's shadow: the record's zero-shadow range of g_rec's body or of record.spill (lib/B/YF0m.v
   Tfib_zero_shadow: (0xad560, 0x5e3680 - 0xad560) and (0x5e3760, 0x38)) *)
Lemma al_slot_addressable : forall ly S W mem md c a n,
AR SEGS B ly S W mem md -> al_slot c -> c <= a -> a + n <= c + 56 ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md c a n HAR Hsl Ha Hn.
destruct Hsl as [(i & Hi & ->) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX in *.
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xad560, 0x5e3680 - 0xad560) a n HAR);
  [unfold Tfib_zero_shadow; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity
  | cbn [fst snd]; lia | cbn [fst snd]; lia].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3760, 0x5e3798 - 0x5e3760) a n HAR);
  [unfold Tfib_zero_shadow; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity
  | cbn [fst snd]; lia | cbn [fst snd]; lia].
Qed.

Lemma al_entry : forall W ly S regs mem md ch c k,
afn_pre SEGS B ARG_LINE_STK ly S W regs mem md ch ->
getr regs 10 = w64 c -> al_slot c ->
aval_mem (rdW W mem) (c + CALL_OFF_NARGS) 4 k -> 0 <= k <= 6 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs al_extra)) (al_ss (al_regs k))
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arg_line)) mem (seg_rom SEGS)))
/\ sh_ok SEGS al_Bx al_SH (Eimg (Ereg regs al_extra)) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch c k HPRE H10 Hsl Hnargs Hk.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof al_stk as FFS.
destruct (al_slot_facts c Hsl) as (Hc8 & Hcr & Hcin).
unfold A_G_REC, A_REC_SPILL in Hcr.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs al_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof al_obj0 as V0. pose proof al_obj12 as V12.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (CK : YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) c (YP09.mkChunk 4 (CVal 4 (SLit k)))).
{ apply (chunk_ok_val SEGS E _ c 4 4 (SLit k) k); [reflexivity | cbn; lia | lia |].
  exact (val_mem_of_aval SEGS (w_H W) mem (c + 4) 4 k Hnargs). }
assert (RG : forall r, In r [got_regionP; bcell_regionP 32] -> YP09.region_ok SEGS E (mrestrict (w_H W) mem) r).
{ intros r [<- | [<- | []]]; unfold region_ok, got_regionP, bcell_regionP;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  - rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (rewrite V0; lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | rewrite V12; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (rewrite V12; lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 al_Bx SB);
    [cbn [sv_denot al_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell). }
assert (RS : YP09.region_ok SEGS E (mrestrict (w_H W) mem) (stack_region 48)).
{ unfold region_ok, stack_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
assert (HG : facts_ok E al_facts).
{ split; [|split; [exact I | exact I]].
  cbn [al_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E10, E32, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold A_G_REC, A_REC_SPILL. revert Hslo Hshi H47 Hceil Hal16 Hc8 Hcr C1 FFS Hstk0. clear. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
split.
- unfold al_ss. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + reflexivity.
  + unfold al_regs. constructor; [exact RS|]. constructor; [apply RG; left; reflexivity|].
    constructor; [apply RG; right; left; reflexivity|]. constructor; [|constructor].
    unfold region_ok, al_nargs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB 10%nat c E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [exact CK | constructor].
  + apply pairwise_disjoint_of_extents.
    unfold al_regs, stack_region, got_regionP, bcell_regionP, al_nargs, extent_of_region;
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]; rewrite (VB 10%nat c E10) by lia;
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (rewrite V0; lia); rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (rewrite V12; lia);
    cbn [base_val]; rewrite Usp, V0, V12; cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
    revert Hslo Hshi H47 Hceil Hcr C1 C3 FFS Hstk0 Hk; clear; intros; repeat split; lia.
  + exact HG.
- unfold sh_ok, al_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E al_Bx 10 c 56 c 0 56).
  + exact (al_slot_addressable ly S W mem md c c 56 HAR Hsl ltac:(lia) ltac:(lia)).
  + unfold U, al_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF. lia.
Qed.

(* The entry state of the c->nargs < 6 path: the value of c->nargs is the atom 33 (an extra of the environment,
   0 <= k <= 5), so that the runs up to the last segment do not depend on which value it is; the last segment
   replaces it by the literal (al_walk_lt). *)
Definition al_extra_lt (k : Z) : list word := map (Z_to_bv 64) [SB; k].
Definition al_facts_lt : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF A_G_REC A_REC_SPILL 3); (32%nat, mkAF SB SB 0);
(33%nat, mkAF 0 5 0)] [] [].
Definition al_nargs_a : YP09.region := YP09.mkRegion (Some 10%nat) 4 8 4 4 [YP09.mkChunk 4 (CVal 4 (SOff 33 0))].
Definition al_regs_lt : smem := [stack_region 48; got_regionP; bcell_regionP 32; al_nargs_a].
Definition al_ss_lt : sstate := mkSS AF_arg_line sr_atoms al_regs_lt None al_facts_lt.

Lemma al_entry_lt : forall W ly S regs mem md ch c k,
afn_pre SEGS B ARG_LINE_STK ly S W regs mem md ch ->
getr regs 10 = w64 c -> al_slot c ->
aval_mem (rdW W mem) (c + CALL_OFF_NARGS) 4 k -> 0 <= k <= 5 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (al_extra_lt k))) al_ss_lt
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arg_line)) mem (seg_rom SEGS)))
/\ sh_ok SEGS al_Bx al_SH (Eimg (Ereg regs (al_extra_lt k))) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch c k HPRE H10 Hsl Hnargs Hk.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof al_stk as FFS.
destruct (al_slot_facts c Hsl) as (Hc8 & Hcr & Hcin).
unfold A_G_REC, A_REC_SPILL in Hcr.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (al_extra_lt k))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 k) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof al_obj0 as V0. pose proof al_obj12 as V12.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (CK : YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) c (YP09.mkChunk 4 (CVal 4 (SOff 33 0)))).
{ apply (chunk_ok_val SEGS E _ c 4 4 (SOff 33 0) k); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
  exact (val_mem_of_aval SEGS (w_H W) mem (c + 4) 4 k Hnargs). }
assert (RG : forall r, In r [got_regionP; bcell_regionP 32] -> YP09.region_ok SEGS E (mrestrict (w_H W) mem) r).
{ intros r [<- | [<- | []]]; unfold region_ok, got_regionP, bcell_regionP;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  - rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (rewrite V0; lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | rewrite V12; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (rewrite V12; lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 al_Bx SB);
    [cbn [sv_denot al_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell). }
assert (RS : YP09.region_ok SEGS E (mrestrict (w_H W) mem) (stack_region 48)).
{ unfold region_ok, stack_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
assert (HG : facts_ok E al_facts_lt).
{ split; [|split; [exact I | exact I]].
  cbn [al_facts_lt f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold A_G_REC, A_REC_SPILL. revert Hslo Hshi H47 Hceil Hal16 Hc8 Hcr C1 FFS Hstk0 Hk. clear. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
split.
- unfold al_ss_lt. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + reflexivity.
  + unfold al_regs_lt. constructor; [exact RS|]. constructor; [apply RG; left; reflexivity|].
    constructor; [apply RG; right; left; reflexivity|]. constructor; [|constructor].
    unfold region_ok, al_nargs_a. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB 10%nat c E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [exact CK | constructor].
  + apply pairwise_disjoint_of_extents.
    unfold al_regs_lt, stack_region, got_regionP, bcell_regionP, al_nargs_a, extent_of_region;
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]; rewrite (VB 10%nat c E10) by lia;
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (rewrite V0; lia); rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (rewrite V12; lia);
    cbn [base_val]; rewrite Usp, V0, V12; cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
    revert Hslo Hshi H47 Hceil Hcr C1 C3 FFS Hstk0 Hk; clear; intros; repeat split; lia.
  + exact HG.
- unfold sh_ok, al_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E al_Bx 10 c 56 c 0 56).
  + exact (al_slot_addressable ly S W mem md c c 56 HAR Hsl ltac:(lia) ltac:(lia)).
  + unfold U, al_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF. lia.
Qed.

(* c->nargs = 6: the traps 0x8b144 / 0x8b150 and the check 0x8b174 pass, the branch 0x8b180 to the epilogue is
   taken, nothing is written and nothing is called *)
Lemma al_walk6 : forall ly S W regs mem md ch c (T : list byte),
afn_pre SEGS B ARG_LINE_STK ly S W regs mem md ch ->
getr regs 10 = w64 c -> al_slot c ->
aval_mem (rdW W mem) (c + CALL_OFF_NARGS) 4 6 ->
SRr SEGS W (cfg_at SEGS (BASE + AF_arg_line) regs mem md)
(apost_base SEGS B ARG_LINE_STK [] regs ly S W mem md EV_ARG_LINE
(fun ly' S' W' regs' mem' md' => blocks_bytes S' <= blocks_bytes S + LIVE_ARG_LINE T /\
  mo_le MT S S' (XM_ARG_LINE MT T) /\ Permutation (ablocks B ly' S') (ablocks B ly S))).
Proof.
intros ly S W regs mem md ch c T HPRE H10 Hsl Hn.
destruct (al_entry W ly S regs mem md ch c 6 HPRE H10 Hsl Hn ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init SEGS B ARG_LINE_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
remember (Eimg (Ereg regs al_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs al_extra) E) by (rewrite HE; split; [intros n Hn'; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_arg_line)) with (Z_to_bv 64 (BASE + AF_arg_line)).
unfold al_regs, al_ss in HS.
paj_run_tok RUN HS HJ SHOK al_Bspan. { awr_ok_tac. exact Usp. }
prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [apply (ajournal_mono_k SEGS B) with (k := 0); [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ | unfold EV_ARG_LINE, EV_REC_CANONICAL, EV_XMALLOC; lia]|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs al_extra HS); [exact HAE | vm_compute; reflexivity]|].
split; [unfold LIVE_ARG_LINE, LIVE_REC_CANONICAL; lia|].
split; [|apply Permutation_refl].
apply (mle_weaken MT S S 0 _ MTL (mle_start MT S MTL)).
unfold XM_ARG_LINE, XM_REC_CANONICAL, XM_XMALLOC. apply (mo_malloc_nonneg MT MTL). unfold LIVE_XMALLOC. lia.
Qed.

(* the slot's windows are footprint bytes of the program's statics (a Theorem Labs lane's awr_prog_or_caller) *)
Lemma al_awr_slot : forall E r rs STK sp0 FP bl0 blc fr0 lyc own c,
YP09.r_base r = Some 10%nat -> bv_unsigned (ew E 10) = c -> al_slot c -> 0 <= YP09.r_wlo r -> YP09.r_whi r <= 56 ->
(forall a, c + YP09.r_wlo r <= a < c + YP09.r_whi r -> inFP FP a) ->
awr_ok SEGS B E rs STK sp0 FP bl0 blc fr0 lyc own -> awr_ok SEGS B E (r :: rs) STK sp0 FP bl0 blc fr0 lyc own.
Proof.
intros E r rs STK sp0 FP bl0 blc fr0 lyc own c Hb Hc Hsl Hlo Hhi HF H.
destruct (al_slot_facts c Hsl) as (_ & _ & Hcin).
eapply awr_ok_cons_gen; [exact Hb | exact Hc | | exact H].
intros a Ha. do 4 right. unfold awr_prog_or_caller. left.
split; [apply HF; exact Ha|]. split; [apply (rca_HPROG B HB), Hcin; lia | apply (cif_prog_img _ _ IMG), Hcin; lia].
Qed.

(* a region of the symbolic state is kept over a call when the call keeps its bytes and leaves its window present *)
Lemma al_kept_region : forall E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hk Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hk. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma al_sig_rc : SIGMA CS_rec_canonical = BASE + AF_rec_canonical.
Proof.
rewrite (cmd_sig_prog_PB CS_rec_canonical); [reflexivity|].
cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]).
Qed.

(* the slot's bytes are kept by a call whose footprint is empty: they are image bytes outside the runtime's statics *)
Lemma al_slot_unowned : forall c a, al_slot c -> c <= a < c + 56 ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros c a Hsl Ha. destruct (al_slot_facts c Hsl) as (_ & _ & Hcin).
exact (cmd_prog_unowned SEGS B LAWS HB IMG a (Hcin a Ha)).
Qed.

Lemma al_kept_widen : forall rd rd' lo hi lo' hi', kept_out rd rd' lo hi -> lo' <= lo -> hi <= hi' -> kept_out rd rd' lo' hi'.
Proof. intros rd rd' lo hi lo' hi' H H1 H2 a Ha Hn. apply H; [exact Ha | lia]. Qed.

Lemma al_aview_mod : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte, mrestrict.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* the read-only view of the entry holds at a state that differs from the entry only in [lo, hi) above the image:
   no byte of [lo, hi) is in the read-only range, since the entry sees each of them and the image has none *)
Lemma al_arod_kept : forall (W : world SEGS) mem mem' lo hi,
arodata_okP SEGS RLO RHI B (rdW W mem) -> kept_out (rdW W mem) (rdW W mem') lo hi ->
(forall a, lo <= a < hi -> rdW W mem a <> None) -> kLowMemEnd <= lo -> hi <= 2 ^ 64 ->
arodata_okP SEGS RLO RHI B (rdW W mem').
Proof.
intros W mem mem' lo hi HR HK Hv Hlo Hhi a Hro Ho He.
pose proof (HR a Hro Ho He) as Ha.
set (a' := a mod 2 ^ 64). pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha'. fold a' in Ha'.
assert (Er : seg_rom SEGS (Z_to_bv 64 a) = seg_rom SEGS (Z_to_bv 64 a')).
{ f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  subst a'. rewrite Z.mod_mod by lia. reflexivity. }
rewrite al_aview_mod in Ha |- *. fold a' in Ha |- *. rewrite Er in Ha |- *.
destruct (Z_lt_le_dec a' lo) as [Hl | Hl]; [|destruct (Z_lt_le_dec a' hi) as [Hh | Hh]].
- rewrite (HK a' Ha') by lia. exact Ha.
- exfalso. apply (Hv a' ltac:(lia)). rewrite Ha.
  rewrite (seg_rom_none SEGS a' Ha'); [reflexivity|].
  intros Hi. pose proof (pa_segs_low a' Hi). lia.
- rewrite (HK a' Ha') by lia. exact Ha.
Qed.

Lemma al_vm_eq : forall (m : word -> option byte) a a' n v, val_mem SEGS m a n v -> a = a' -> val_mem SEGS m a' n v.
Proof. intros m a a' n v H <-. exact H. Qed.

(* the write windows of the last segment: c->args[k], the frame, c->nargs *)
Local Ltac al_awr U Usp Hsl :=
eapply al_awr_slot; [reflexivity | exact U | exact Hsl | cbn; lia | cbn; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn in Ha; eexists; split;
  [right; left; reflexivity | cbn [fst snd]; unfold CALL_OFF_ARGS; lia] | ];
awr_ok_tac; [exact Usp | eapply al_awr_slot; [reflexivity | exact U | exact Hsl | cbn; lia | cbn; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn in Ha; eexists; split;
  [left; reflexivity | cbn [fst snd]; unfold CALL_OFF_NARGS; lia] | apply awr_ok_nil]].

(* c->nargs = k < 6: strlen, rec_canonical, then the two stores *)
Lemma al_walk_lt : forall ly S W regs mem md ch c pl k (T : list byte),
afn_pre SEGS B ARG_LINE_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 c -> getr regs 11 = w64 pl -> 0 <= pl < 2 ^ 64 -> al_slot c ->
aval_mem (rdW W mem) (c + CALL_OFF_NARGS) 4 k -> (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) ->
astr_atR (rdW W mem) pl T -> Z.of_nat (length T) + 1 <= LMAX + 1 ->
in_blockA (ablocks B ly S) pl (Z.of_nat (length T) + 1) ->
st_nev S + EV_ARG_LINE <= EV_MAX -> blocks_bytes S + LIVE_ARG_LINE T <= LIVE_MAX ->
mo_ok MT S (XM_ARG_LINE MT T) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_arg_line) regs mem md)
(apost_base SEGS B ARG_LINE_STK
[(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * k, c + CALL_OFF_ARGS + 8 * k + 8)]
regs ly S W mem md EV_ARG_LINE
(fun ly' S' W' regs' mem' md' =>
blocks_bytes S' <= blocks_bytes S + LIVE_ARG_LINE T /\
mo_le MT S S' (XM_ARG_LINE MT T) /\ exists p,
let n := Z.of_nat (length T) + 1 in
4096 <= p < 2 ^ 64 /\
Permutation (ablocks B ly' S') ((p, n) :: ablocks B ly S) /\
Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B ly S) /\
aval_mem (rdW W' mem') (c + CALL_OFF_NARGS) 4 (k + 1) /\
aval_mem (rdW W' mem') (c + CALL_OFF_ARGS + 8 * k) 8 p /\
astr_atR (rdW W' mem') p (canon T))).
Proof.
intros ly S W regs mem md ch c pl k T HPRE HROD H10 H11 Hpl Hsl Hn Hk HSTR HLEN HBLK Hev Hlive HMOK.
assert (Hk5 : 0 <= k <= 5) by lia.
destruct (al_entry_lt W ly S regs mem md ch c k HPRE H10 Hsl Hn Hk5) as [HS SHOK].
pose proof (ajournal_init SEGS B ARG_LINE_STK
[(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * k, c + CALL_OFF_ARGS + 8 * k + 8)]
ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof al_stk as FFS.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (al_slot_facts c Hsl) as (Hc8 & Hcr & Hcin).
remember (Eimg (Ereg regs (al_extra_lt k))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn'; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn').
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 k) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (U10 : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL in Hcr; lia).
pose proof al_obj0 as V0. pose proof al_obj12 as V12.
assert (HAE : env_agree 32 (Ereg regs (al_extra_lt k)) E) by (rewrite HE; split; [intros n Hn'; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_arg_line)) with (Z_to_bv 64 (BASE + AF_arg_line)).
unfold al_regs_lt, al_ss_lt in HS.
paj_run_tok RUN HS HJ SHOK al_Bspan. { awr_ok_tac. exact Usp. }
(* at the strlen call (0x8b188): the memory differs from the entry's only in the frame *)
assert (KO1 : kept_out (rdW W mem) (rdW W (ms_mem ms)) (spZ regs - 48) (spZ regs)).
{ intros a Ha Hna. apply (kept_of_frame (segs:=SEGS) E _ (w_H W) mem (ms_mem ms) (fun a => spZ regs - 48 <= a < spZ regs) HFr);
  [| exact Ha | exact Hna].
  intros b wlo whi a' Hin Hr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Usp in Hr; lia|]); destruct Hin. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
pmkst HS.
destruct HBLK as (pb & kb & Hinb & Hpb & Hpbe).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb kb HAR Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hkb).
pose proof (req_size_pos kb ltac:(lia)) as [_ Hreq].
set (n := Z.of_nat (length T)) in *.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs + -48)
by (change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, Usp, unsigned_lit_small by lia; reflexivity).
pose proof (proj1 HJ) as HAR1.
assert (HPRE1 : ecall_pre_stk SEGS B ESTACK ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md)).
{ eapply (ecall_pre_stk_at SEGS B ESTACK ARG_LINE_STK (spZ regs) _ ly S W mem md [] ly S W (ms_mem ms) _ 0 (ms_regs ms) (-48) HJ Hsp1);
  [reflexivity | lia | lia | unfold ESTACK; lia | rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite R3, (EE 3%nat 3%bv eq_refl); exact Hgp | rewrite R4, (EE 4%nat 4%bv eq_refl); exact Htp]. }
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low ENV ESTACK (fun _ => False) (SIGMA CS___interceptor_trampoline_strlen)
  W (ms_regs ms) (ms_mem ms) ARG_LINE_STK (spZ regs) _ ly S W mem md [] ly S _ 0 (-48) (Z_to_bv 64 (BASE + 19548))
  (fun regs' _ => getr regs' 10 = w64 (astr_len T)) HJ Hsp1 eq_refl ltac:(lia) ltac:(unfold ESTACK; lia)
  ltac:(unfold ESTACK; lia) R1 (fun a H => match H with end)).
  apply (ASTRLEN fx ly S W (ms_regs ms) (ms_mem ms) _ pl T HPRE1).
  - rewrite R10, (EE 11%nat 11%bv eq_refl). exact H11.
  - lia.
  - apply (proj1 (astr_atR_view SEGS W (ms_mem ms) pl T)).
    exact (astr_atR_kept _ _ (spZ regs - 48) (spZ regs) pl T KO1 HSTR ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (aread_ok_of_block SEGS B LAWS ESTACK ly S W (ms_regs ms) (ms_mem ms) _ pb kb pl (astr_len T + 1) HAR1 Hinb
    ltac:(lia) ltac:(unfold astr_len; lia) ltac:(unfold astr_len; lia) ltac:(rewrite Hsp1; unfold ESTACK; lia)).
  - unfold astr_len. exact (cmd_heap_tail_vis SEGS B LAWS HB ly S W (ms_mem ms) _ pb kb (pl + n) HAR1 Hinb ltac:(lia)).
  - apply (cmd_rom_view_on SEGS B LAWS HB IMG RLO RHI W (ms_mem ms)).
    apply (al_arod_kept W mem (ms_mem ms) (spZ regs - 48) (spZ regs) HROD KO1); [|lia|lia].
    intros a Ha. apply (aview_some_of_apresent SEGS). apply Hpres. lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Hout2).
(* back at 0x8b18c: the symbolic state over the call, with a0..a7, t0..t6 and ra fresh atoms 64..79 *)
assert (KO2 : kept_out (rdW W (ms_mem ms)) (rdW W mem2) (spZ regs - 48 - 4096) (spZ regs - 48)).
{ intros a Ha Hna. apply Hout2; [exact Ha | unfold ESTACK; lia | intros []]. }
jafter_call_keep_pi HS 64%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  repeat apply Forall_cons; [| | | | apply Forall_nil].
  - eapply al_kept_region; [exact Usp | intros a Ha; apply KO2; lia | intros a Ha; apply Hpres2; lia].
  - eapply al_kept_region; [exact (HEI 241%nat ltac:(unfold A_TEXT, A_LIM; lia)) | intros a Ha; apply KO2 | intros a Ha; lia];
    change (VAL 241%nat) with (VAL (A_OBJ 0)) in *; rewrite V0 in *; lia.
  - eapply al_kept_region; [exact (HEI 253%nat ltac:(unfold A_TEXT, A_LIM; lia)) | intros a Ha; apply KO2 | intros a Ha; lia];
    change (VAL 253%nat) with (VAL (A_OBJ 12)) in *; rewrite V12 in *; lia.
  - eapply al_kept_region; [exact U10 | intros a Ha; apply KO2 | intros a Ha; lia];
    unfold A_G_REC, A_REC_SPILL in Hcr; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 64 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n0, (n0 < 64)%nat -> ew E2 n0 = ew E n0) by (intros n0 Hn0; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn0).
assert (HAE2 : env_agree 32 (Ereg regs (al_extra_lt k)) E2) by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
assert (E68 : ew E2 68 = getr regs2 10%bv) by (rewrite HE2; unfold havoc; cbn [ew]; reflexivity).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (SHOK2 : sh_ok SEGS al_Bx al_SH E2 (mrestrict (w_H W) mem2)).
{ constructor; [|constructor]. apply (shent_ok_of_range SEGS (w_H W) mem2 E2 al_Bx 10 c 56 c 0 56).
  + exact (al_slot_addressable ly S W mem2 md2 c c 56 (proj1 HJ2) Hsl ltac:(lia) ltac:(lia)).
  + unfold U, al_Bx. cbn [sv_denot]. rewrite (OLD2 32%nat) by lia. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite (OLD2 10%nat) by lia. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold A_G_REC, A_REC_SPILL in Hcr; lia). reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF. unfold A_G_REC, A_REC_SPILL in Hcr. lia. }
paj_run_tok RUN HS HJ2 SHOK2 al_Bspan. { awr_ok_tac. exact Usp2. }
(* at the rec_canonical call (0x8b194) *)
assert (KO3 : kept_out (rdW W mem2) (rdW W (ms_mem ms0)) (spZ regs - 48) (spZ regs)).
{ intros a Ha Hna. apply (kept_of_frame (segs:=SEGS) E2 _ (w_H W) mem2 (ms_mem ms0) (fun a => spZ regs - 48 <= a < spZ regs) HFr);
  [| exact Ha | exact Hna].
  intros b wlo whi a' Hin Hr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Usp2 in Hr; lia|]); destruct Hin. }
clear HF HFr HG.
assert (KO : kept_out (rdW W mem) (rdW W (ms_mem ms0)) (spZ regs - 4144) (spZ regs)).
{ eapply kept_out_trans; [eapply kept_out_trans; [apply (al_kept_widen _ _ _ _ _ _ KO1) | exact KO2 | |] | exact KO3 | |];
  unfold ESTACK in *; lia. }
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
pmkst HS.
assert (Hsp2 : spZ (ms_regs ms0) = spZ regs + -48)
by (change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2)); rewrite Q2, Usp2, unsigned_lit_small by lia; reflexivity).
assert (Hvis : forall a, spZ regs - 4144 <= a < spZ regs -> rdW W mem a <> None).
{ intros a Ha. apply (aview_some_of_apresent SEGS). apply Hpres. lia. }
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms0)))
by (apply (al_arod_kept W mem (ms_mem ms0) (spZ regs - 4144) (spZ regs) HROD KO Hvis); lia).
assert (HSTR2 : astr_atR (rdW W (ms_mem ms0)) pl T)
by exact (astr_atR_kept _ _ (spZ regs - 4144) (spZ regs) pl T KO HSTR ltac:(lia) ltac:(lia) ltac:(lia)).
eapply SRr_bind.
{ eapply (cl_callS B LAWS W (ms_regs ms0) (ms_mem ms0) (Z_to_bv 64 (SIGMA CS_rec_canonical)) ARG_LINE_STK (spZ regs) _
  ly S W mem md [] ly S _ 0 REC_CANONICAL_STK [] EV_REC_CANONICAL (-48) (Z_to_bv 64 (BASE + 19560)) []
  (fun ly2 S2 W2 regs2 mem2 md2 => exists p : Z,
    getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
    Permutation (ablocks B ly2 S2) ((p, LIVE_REC_CANONICAL T) :: ablocks B ly S) /\
    Forall (fun qk => iv_apart p (LIVE_REC_CANONICAL T) (fst qk) (snd qk)) (ablocks B ly S) /\
    abytes_atR (rdW W2 mem2) p (canon T ++ [Z_to_bv 8 0]) /\ abytes_atR (rdW W2 mem2) pl T /\
    blocks_bytes S2 <= blocks_bytes S + LIVE_REC_CANONICAL T /\ mo_le MT S S2 (XM_REC_CANONICAL MT T))
  HJ2 Hsp2).
  - reflexivity.
  - lia.
  - unfold REC_CANONICAL_STK, XMALLOC_STK, ASTACK. lia.
  - unfold REC_CANONICAL_STK, XMALLOC_STK, ASTACK. lia.
  - rewrite Q3, OLD2, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite Q4, OLD2, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite Q8, OLD2, U10 by lia.
    rewrite unsigned_lit_small by (unfold A_G_REC, A_REC_SPILL in Hcr; lia). unfold A_G_REC, A_REC_SPILL in Hcr. lia.
  - intros HPRE2. rewrite al_sig_rc.
    eapply SRr_mono.
    { apply (TREC_CANONICAL fx ly S W (ms_regs ms0) (ms_mem ms0) _ [] pl T HPRE2 HROD2).
      - rewrite Q10, OLD2, (EE 11%nat 11%bv eq_refl) by lia. exact H11.
      - exact Hpl.
      - rewrite Q11, E68. exact Ha02.
      - exists pb, kb. split; [exact Hinb | lia].
      - exact HSTR2.
      - exact HLEN.
      - exact Hev.
      - exact Hlive.
      - exact HMOK. }
    cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HK3).
    exists ly3, S3, regs3, mem3, md3. split; [rewrite Q1; reflexivity|]. split; [exact HJ3|]. split; [exact HP3 | exact HK3].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 &
(p & Hp10 & Hp4096 & HPerm3 & Hfresh3 & Hcan3 & Hpl3 & Hbb3 & Hmle3)).
(* back at 0x8b198: the symbolic state over the call, with a0..a7, t0..t6 and ra fresh atoms 96..111 *)
pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _ & G3 & _).
pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
pose proof (proj1 HJ2) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
assert (U10b : bv_unsigned (ew E2 10) = c) by (rewrite OLD2 by lia; exact U10).
jafter_call_keep_pi HS 96%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2; 3]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
  - eapply al_kept_region; [exact Usp2 | intros a Ha | intros a Ha; apply Hpres3; lia].
    apply G1; [lia | unfold REC_CANONICAL_STK, XMALLOC_STK, ASTACK; lia | apply inFP_nil].
  - apply (region_kept_val_at E2 _ _ 241%nat (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
    [exact (HEI2 241%nat ltac:(unfold A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2)
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot3) | lia].
  - apply (region_kept_val_at E2 _ _ 253%nat (VAL (A_OBJ 12)) 8 SHADOW_OFF);
    [exact (HEI2 253%nat ltac:(unfold A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2)
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell3) | lia].
  - eapply al_kept_region; [exact U10b | intros a Ha | intros a Ha; lia].
    destruct (al_slot_unowned c a Hsl ltac:(lia)) as (Hi & Ho & He).
    apply G3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | apply inFP_nil]]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2 96 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n0, (n0 < 96)%nat -> ew E3 n0 = ew E2 n0) by (intros n0 Hn0; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn0).
assert (HAE3 : env_agree 32 (Ereg regs (al_extra_lt k)) E3) by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
assert (E100 : ew E3 100 = getr regs3 10%bv) by (rewrite HE3; unfold havoc; cbn [ew]; reflexivity).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).
assert (U10c : bv_unsigned (ew E3 10) = c) by (rewrite OLD3 by lia; exact U10b).
assert (E10c : ew E3 10 = Z_to_bv 64 c) by (rewrite OLD3, OLD2 by lia; exact E10).
assert (E33c : ew E3 33 = Z_to_bv 64 k) by (rewrite OLD3, OLD2 by lia; exact E33).
assert (E32c : ew E3 32 = Z_to_bv 64 SB) by (rewrite OLD3, OLD2 by lia; exact E32).
change (LIVE_REC_CANONICAL T) with (n + 1) in HPerm3, Hfresh3.
assert (Hinp : In (p, n + 1) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3 | left; reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p (n + 1) HAR3 Hinp) as (Hp16 & _ & Hpceil & _ & Hppres & _ & _).
pose proof (blk_off_imgP _ _ _ _ _ _ p (n + 1) HAR3 Hinp) as Hpimg.
pose proof (req_size_pos (n + 1) ltac:(lia)) as [_ Hreqp].
assert (SHOK3 : sh_ok SEGS al_Bx al_SH E3 (mrestrict (w_H W3) mem3)).
{ constructor; [|constructor]. apply (shent_ok_of_range SEGS (w_H W3) mem3 E3 al_Bx 10 c 56 c 0 56).
  + exact (al_slot_addressable ly3 S3 W3 mem3 md3 c c 56 HAR3 Hsl ltac:(lia) ltac:(lia)).
  + unfold U, al_Bx. cbn [sv_denot]. rewrite E32c, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10c, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold A_G_REC, A_REC_SPILL in Hcr; lia). reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF. unfold A_G_REC, A_REC_SPILL in Hcr. lia. }
(* the last segment stores into the slot: c->nargs becomes writable with its value as the literal k, and
   c->args[k] becomes a writable region *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_region_nth E3 ssx (restrict _ msx) 3 al_nargs_a HS ltac:(vm_compute; reflexivity)) as HR3 end.
cbn [ms_mem restrict mkst] in HR3.
assert (VN : val_mem SEGS (mrestrict (w_H W3) mem3) (c + 4) 4 k).
{ unfold region_ok in HR3. cbv zeta in HR3. destruct HR3 as (_ & _ & _ & HC).
  cbn [YP09.r_chunks YP09.r_base al_nargs_a base_val] in HC. apply Forall_inv in HC. rewrite U10c in HC.
  exact (val_of_chunk_ok SEGS E3 _ c 4 4 (SOff 33 0) k HC
    ltac:(cbn [sv_denot]; rewrite E33c, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(lia)). }
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (ast_ok_pi_set_region E3 ssx msx 3 al_nargs_a (al_nargs k true) HS ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)) as HS4 end.
match type of HS4 with ?P -> _ => assert (HRn : P); [|specialize (HS4 HRn); clear HRn] end.
{ cbn [ms_mem restrict mkst]. unfold region_ok, al_nargs.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U10c. unfold A_G_REC, A_REC_SPILL in Hcr. split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (PROG_WRITABLE SEGS B LAWS HB PRW). apply Hcin. lia.
  - constructor; [|constructor]. apply (chunk_ok_val SEGS E3 _ c 4 4 (SLit k) k); [reflexivity | cbn; lia | lia | exact VN]. }
clear HS. rename HS4 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (st_ok_pi_add_region E3 ssx msx (al_arg k) HS) as HS5 end.
match type of HS5 with ?P1 -> ?P2 -> ?P3 -> _ =>
  assert (HA1 : P1); [|assert (HA2 : P2); [|assert (HA3 : P3); [|specialize (HS5 HA1 HA2 HA3); clear HA1 HA2 HA3]]] end.
{ destruct Hk as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity. }
{ cbn [ms_mem restrict mkst]. unfold region_ok, al_arg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U10c. unfold A_G_REC, A_REC_SPILL in Hcr. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (PROG_WRITABLE SEGS B LAWS HB PRW). apply Hcin. lia. }
{ cbn [ss_mem list_upd all_disjoint]. unfold extent_disjoint, al_arg, al_nargs.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U10c, Usp3, (HEI3 241%nat ltac:(unfold A_TEXT, A_LIM; lia)), (HEI3 253%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  change (VAL 241%nat) with (VAL (A_OBJ 0)). change (VAL 253%nat) with (VAL (A_OBJ 12)). rewrite V0, V12.
  unfold A_G_REC, A_REC_SPILL in Hcr. repeat split; lia. }
clear HS. rename HS5 into HS.
destruct Hk as [-> | [-> | [-> | [-> | [-> | ->]]]]].
all: paj_run_tok RUN HS HJ3 SHOK3 al_Bspan; [al_awr U10c Usp3 Hsl|].
(* at the ret (0x8b20c): the run wrote the frame and the slot only *)
all: pose proof (kept_of_frame (segs:=SEGS) E3 _ (w_H W3) mem3 (ms_mem ms1)
  (fun a => spZ regs - 48 <= a < spZ regs \/ c + 4 <= a < c + 56) HFr
  ltac:(intros b wlo whi a' Hin Hr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Usp3, ?U10c in Hr; lia|]);
    destruct Hin)) as KO4.
all: lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_region_nth E3 ssx (restrict _ msx) 0 _ HS eq_refl) as HRa;
  pose proof (st_ok_pi_region_nth E3 ssx (restrict _ msx) 4 _ HS eq_refl) as HRn end.
all: cbn [ms_mem restrict mkst] in HRa, HRn.
all: prreg HS (1%bv : bv 5) Rra.
all: eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
all: intros mat'; unfold apost_base.
all: lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly3, S3, rg, m, d end.
all: split; [cbn [ms_regs]; rewrite Rra, OLD3, OLD2, (EE 1%nat 1%bv eq_refl), Hra by lia; reflexivity|].
all: split; [apply (ajournal_mono_k SEGS B) with (k := 0 + EV_REC_CANONICAL);
  [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3 | unfold EV_ARG_LINE; lia]|].
all: split; [eapply (aregs_preserved_of_st_ok SEGS _ E3 _ _ regs _ HS); [exact HAE3 | vm_compute; reflexivity]|].
all: split; [exact Hbb3|].
all: split; [exact Hmle3|].
all: exists p.
all: split; [exact Hp4096|]. all: split; [exact HPerm3|]. all: split; [exact Hfresh3|].
all: split; [apply al_aval_of_val_mem; unfold CALL_OFF_NARGS;
  exact (field_of_region E3 _ 10%nat c _ _ _ _ _ 4 4%N _ _ HRn U10c ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(lia))|].
all: split; [apply al_aval_of_val_mem; eapply al_vm_eq;
  [exact (field_of_region E3 _ 10%nat c _ _ _ _ _ _ 8%N _ p HRa U10c ltac:(left; reflexivity)
     ltac:(cbn [sv_denot]; rewrite E100, Hp10, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity)
     ltac:(cbn; lia) ltac:(lia)) | unfold CALL_OFF_ARGS; lia]|].
all: pose proof (canon_length T) as HCL.
all: split; [| exact (canon_no0 T (proj2 HSTR))].
all: intros i Hi; rewrite length_app in Hi; cbn [length] in Hi.
all: rewrite KO4; [exact (Hcan3 i ltac:(rewrite length_app; cbn [length]; lia)) | lia |].
all: unfold off_img in Hpimg; unfold A_G_REC, A_REC_SPILL in Hcr; intros [Hz | Hz]; lia.
Qed.

(* targ_line_spec (arg_line_c.v:75-115) exactly as stated: c->nargs = 6 is al_walk6, c->nargs < 6 is al_walk_lt *)
Theorem targ_line_holds : targ_line_spec B MT.
Proof.
unfold targ_line_spec.
intros ly S W regs mem md ch c pl m T HPRE HROD H10 H11 Hpl Hsl Hn Hm HBLK HSTR HLEN Hev Hlive HMOK.
destruct (Z.eq_dec m REC_ARGS_MAX) as [-> | Hm6].
- eapply SRr_mono; [apply (al_walk6 ly S W regs mem md ch c T HPRE H10 Hsl Hn)|].
  cbv beta. unfold apost_base. intros W' c' _ (ly' & S' & regs' & mem' & md' & Hc & HJ & HP & Hbb & HQ & HPm).
  exists ly', S', regs', mem', md'. split; [exact Hc|]. split; [exact HJ|]. split; [exact HP|].
  split; [exact Hbb|]. split; [exact HQ | left; split; [reflexivity | exact HPm]].
- assert (Hk : m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5) by (unfold REC_ARGS_MAX in *; lia).
  replace (m <? REC_ARGS_MAX) with true by (symmetry; apply Z.ltb_lt; unfold REC_ARGS_MAX in *; lia).
  eapply SRr_mono;
  [apply (al_walk_lt ly S W regs mem md ch c pl m T HPRE HROD H10 H11 Hpl Hsl Hn Hk HSTR HLEN HBLK Hev Hlive HMOK)|].
  cbv beta. unfold apost_base. intros W' c' _ (ly' & S' & regs' & mem' & md' & Hc & HJ & HP & Hbb & HQ & HX).
  exists ly', S', regs', mem', md'. split; [exact Hc|]. split; [exact HJ|]. split; [exact HP|].
  split; [exact Hbb|]. split; [exact HQ | right; split; [unfold REC_ARGS_MAX in *; lia | exact HX]].
Qed.

End e.
End f.
End w.

Print Assumptions targ_line_holds.
