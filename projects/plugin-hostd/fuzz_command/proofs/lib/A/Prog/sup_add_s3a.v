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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/arg_line.v, with its module paths, module names and addresses changed; 923 of its 1002 lines of code are new or changed and 649 lines of the source are left out. *)
(* sup_add's walk on the ASan build of plugin-hostd/fuzz_command, stage M1 -> M2 (sup_add_s3.v), second half: from
   the entry of xstrdup (called at 0x89f68 on uri, never NULL: sa_uri) to M2 (0x89fc0).

   xstrdup goes through cl_callS (footprint []). After it returns (0x89f6c) the walk seeds a symbolic state from the
   machine state (s7 = c + 4 and s11 = the shadow byte address of c + 4 are kept as expressions of c, so that the
   executor removes check 3 and check 5 by the shadow entry of the slot [c, c + 56)), runs the inlined arg_s
   (nargs := 1, args[0] := the copy, check 4) to the call of arg_i (0x89fa8) and composes arg_i by PaFx.v's
   cl_callS_wideF (footprint: c->nargs and c->args[1]; arg_i returns at some FP state fx1 with fxrel fx fx1). From
   arg_i's return (0x89fac) the stage sa_a2_ok, whose statement SA_A2_stmt is
   defined in a closed section so that sa3_cont takes it at fx1, runs check 5, the nargs load (2) and the pruned
   `blt` to M2. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaSB PaDenot PaLibG PaLibF PaLibH PaCall PaArt PaNoChain CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_add_s0 sup_add_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- arithmetic of the stage ---- *)
Lemma s3_s1 : forall sp0, sp0 mod 16 = 0 -> sa_s1 sp0 = sp0 - 160 \/ sa_s1 sp0 = sp0 - 176.
Proof.
intros sp0 H. unfold sa_s1.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as D1.
pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)) as R2.
lia.
Qed.

(* the slot record() filled: a slot of g_rec's call table or record.spill (arg_i_c.v:82) *)
Definition s3_slot (c : Z) : Prop :=
(exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL.
Lemma s3_slot_c : forall R, s3_slot (sa_c R).
Proof.
intros R. unfold s3_slot, sa_c. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [H|H].
- left. exists (Z.of_nat (length (r_calls R))). split; [unfold REC_CALLS_MAX; lia | reflexivity].
- right. reflexivity.
Qed.
Lemma s3_slot_facts : forall c O, s3_slot c ->
c mod 8 = 0 /\ A_G_REC + 16 <= c <= A_REC_SPILL /\ (forall a, c <= a < c + 56 -> inFP cmd_PG a) /\
(forall a, c <= a < c + 56 -> inFP (sa_FP O) a).
Proof.
unfold s3_slot, cmd_PG, sa_FP, A_G_REC, A_REC_SPILL, A_G_QUITTING, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX, OFF_ANSWER, SC_SIZE.
intros c O [(i & Hi & ->) | ->].
- split; [replace (6174528 + 16 + 56 * i) with ((771818 + 7 * i) * 8) by lia; apply Z_mod_mult|].
  split; [lia|]. split.
  + intros a Ha. eexists. split; [left; reflexivity | cbn [fst snd]; lia].
  + intros a Ha. eexists. split; [right; left; reflexivity | cbn [fst snd]; lia].
- split; [reflexivity|]. split; [lia|]. split.
  + intros a Ha. eexists. split; [right; left; reflexivity | cbn [fst snd]; lia].
  + intros a Ha. eexists. split; [right; right; right; left; reflexivity | cbn [fst snd]; lia].
Qed.
Lemma s3_rec_pg : forall a, in_rec a -> inFP cmd_PG a.
Proof.
unfold in_rec, cmd_PG, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE. intros a [Ha | Ha].
- eexists. split; [left; reflexivity | cbn [fst snd]; lia].
- eexists. split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

Lemma s3_den_off : forall E n k v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n k v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma s3_val_mem_of_aval : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; cbn in Hv; [|discriminate].
injection Hv as Hb. f_equal. change (YO0f.le_byte v n k) with (YG0f.le_byte v n k). rewrite <- Hb. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma s3_aval_of_val_mem : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia). reflexivity.
Qed.
End w.

(* the memory facts of sa_core that a step must keep: the saved registers and the three spills of the real frame,
   and the side-stack frame's flag pointer *)
Definition s3_frok (rd : reader) (sp0 : Z) (regs : bvmap 5 word) (F flag : Z) : Prop :=
sa_frame rd sp0 regs /\
aval_mem rd (sa_s1 sp0 + 16) 8 (bv_unsigned (getr regs 13)) /\
aval_mem rd (sa_s1 sp0 + 24) 8 (bv_unsigned (getr regs 12)) /\
aval_mem rd (sa_s1 sp0 + 48) 8 F /\
rdword rd (F + fs_frame_bytes 1 - 8) = Some flag.
Lemma s3_frok_kept : forall (rd rd' : reader) sp0 regs F flag,
s3_frok rd sp0 regs F flag -> sa_s1 sp0 <= sp0 - 160 ->
(forall a, sa_s1 sp0 <= a < sp0 -> rd' a = rd a) ->
(forall a, F <= a < F + 128 -> rd' a = rd a) ->
s3_frok rd' sp0 regs F flag.
Proof.
intros rd rd' sp0 regs F flag (HF & H16 & H24 & H48 & HFL) Hs1 KS KF.
split; [|split; [|split; [|split]]].
- intros j r Hj. assert (Hlt : (j < length sa_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length sa_saved) with 13%nat in Hlt.
  intros k Hk. rewrite KS by lia. exact (HF j r Hj k Hk).
- intros k Hk. rewrite KS by lia. exact (H16 k Hk).
- intros k Hk. rewrite KS by lia. exact (H24 k Hk).
- intros k Hk. rewrite KS by lia. exact (H48 k Hk).
- change (fs_frame_bytes 1) with 128 in *. unfold rdword in *. rewrite !KF by lia. exact HFL.
Qed.
Lemma s3_buf0_kept : forall (rd rd' : reader) F, sa_buf0 rd F ->
(forall a, SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 8 -> rd' a = rd a) -> sa_buf0 rd' F.
Proof. intros rd rd' F H K i Hi. rewrite K by lia. exact (H i Hi). Qed.
Lemma s3_str_kept : forall (rd rd' : reader) p s, astr_atR rd p s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (p + i) = rd (p + i)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s [H1 H2] K. split; [|exact H2]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite K by lia. exact (H1 i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.
(* the statement of the stage from the return of arg_i (0x89fac) to M2 (sa_a2_ok below), at the ambient FP state *)
Section a2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms. Variable MT : ameter_ops.
Definition SA_A2_stmt : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O pos ly3 S3 W3 (regs3 : bvmap 5 word) mem3 md3 O2,
sa_cx B MT ly S W regs mem md ch pu id pp pc uri placement client R O ->
ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] ly3 S3 W3 mem3 md3 (sa_ev2 R) ->
s3_frok (rdW W3 mem3) (spZ regs) regs (frame_addr ly3 1 pos) (flag_addr ly3 1 pos) ->
sa_buf0 (rdW W3 mem3) (frame_addr ly3 1 pos) ->
getr regs3 2 = w64 (sa_s1 (spZ regs)) -> getr regs3 3 = w64 (as_gp B) -> getr regs3 4 = w64 (as_tp B) ->
getr regs3 8 = w64 (spZ regs) -> getr regs3 9 = w64 (sa_s1 (spZ regs)) ->
getr regs3 18 = w64 (frame_addr ly3 1 pos) -> getr regs3 19 = getr regs 11 ->
getr regs3 20 = w64 SHADOW_OFF -> getr regs3 21 = w64 A_G_REC ->
getr regs3 22 = w64 (sa_c R) -> getr regs3 23 = w64 (sa_c R + 4) -> getr regs3 24 = w64 (sa_c R + 8) ->
getr regs3 25 = w64 (SHADOW_OFF + frame_addr ly3 1 pos / 8) -> getr regs3 26 = w64 (frame_addr ly3 1 pos) ->
getr regs3 27 = w64 (SHADOW_OFF + (sa_c R + 4) / 8) ->
aval_mem (rdW W3 mem3) (sa_c R + CALL_OFF_NARGS) 4 2 ->
rec_repA B ly3 S3 (rdW W3 mem3) (rec_record R REC_ADD [sarg uri; dec id]) O2 ->
sa_acct B ly S R O ly3 S3 O2 (sa_live2 uri id) ->
mo_le MT S S3 (sa_acc2 MT R uri id) ->
SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + 15048)) mem3 (seg_rom SEGS)) md3)
  (sa_final B MT ly S W regs mem md R O uri id placement client).
End a2.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Section f. Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the symbolic state after xstrdup returns (0x89f6c): atoms 0..31 the registers, s4 (atom 20) the shadow base, c in
   s6 (atom 22); s7 and s11 as expressions of c; the slot's nargs (0) and args[0] writable; one shadow entry, the
   slot [c, c + 56) *)
Definition s3_Bx : sv := SOff 20 0.
Definition s3_SH : list shent := [mkSHE 22 0 56].
Definition s3_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition s3_facts2 : facts := mkFacts [(20%nat, mkAF SB SB 0); (22%nat, mkAF A_G_REC A_REC_SPILL 3)] [] [].
Definition s3_slotw : YP09.region := YP09.mkRegion (Some 22%nat) 4 16 4 16 [YP09.mkChunk 4 (CVal 4 (SLit 0))].
Definition s3_nargs2 : YP09.region := YP09.mkRegion (Some 22%nat) 4 8 4 4 [YP09.mkChunk 4 (CVal 4 (SLit 2))].
Definition s3_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 4) (SLit 3)) (SOff 20 0).
(* 14984 = AF_sup_add + 0x1b0, the return address of the xstrdup call (0x89f6c) *)
Definition s3_ss2a : sstate := mkSS 14984 sr_atoms [s3_slotw] None s3_facts2.
Definition s3_ss2 : sstate :=
mkSS 14984 (sr_set (sr_set sr_atoms (23%bv : bv 5) (SOff 22 4)) (27%bv : bv 5) s3_shx) [s3_slotw] None s3_facts2.
(* 15048 = AF_sup_add + 0x1ec, the return address of the arg_i call (0x89fac); nargs holds 2 *)
Definition s3_ss3a : sstate := mkSS 15048 sr_atoms [s3_nargs2] None s3_facts2.
Definition s3_ss3 : sstate :=
mkSS 15048 (sr_set (sr_set sr_atoms (23%bv : bv 5) (SOff 22 4)) (27%bv : bv 5) s3_shx) [s3_nargs2] None s3_facts2.

Section e. Variable B : asyms. Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO. #[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a :=
  CmdRecBase.cif_prog_img _ _ IMG.
Let cif_relro_img : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a :=
  CmdRecBase.cif_relro_img _ _ IMG.
Let cif_prog_not_ro : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a :=
  CmdRecBase.cif_prog_not_ro _ _ IMG.
Let cmd_ro_in_img : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI) :=
  CmdRecRo.cmd_ro_in_img SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let cmd_tail_vis_at : forall ly S (W : world SEGS) mem md e, AR SEGS B ly S W mem md -> In e cmd_ro_ends ->
  atail_vis SEGS W mem e :=
  CmdRecRo.cmd_tail_vis_at SEGS B LAWS HB IMG.
(* the rounding mode at this stage's FP state: arg_i's premise *)
Hypothesis FXR : frm0 fx.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.

(* ---- the shared lemmas of sup_add_lem.v, under the statements this stage uses ---- *)
Lemma s3_rep_kept : forall ly S rd ly' S' (rd' : reader) R O,
  rec_repA B ly S rd R O -> (forall a, in_rec a -> rd' a = rd a) ->
  (forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) -> rec_repA B ly' S' rd' R O.
Proof. exact (rec_repA_kept B HB LAWS). Qed.
Lemma s3_rep_append : forall ly S rd ly' S' (rd' : reader) R A O s p n,
  rec_repA B ly S rd (rec_record R REC_ADD A) O -> (length A < 6)%nat ->
  (forall a, in_rec a -> ~ (sa_c R + CALL_OFF_NARGS <= a < sa_c R + CALL_OFF_NARGS + 4) ->
     ~ (sa_c R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < sa_c R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) -> rd' a = rd a) ->
  (forall p0 n0 i, In (p0, n0) O -> 0 <= i < n0 -> rd' (p0 + i) = rd (p0 + i)) ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
  aval_mem rd' (sa_c R + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
  aval_mem rd' (sa_c R + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
  In (p, n) (ablocks B ly' S') -> p <> 0 -> n = Z.of_nat (length s) + 1 -> Z.of_nat (length s) <= LMAX ->
  astr_atR rd' p s -> ~ In p (map fst O) ->
  iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE ->
  rec_repA B ly' S' rd' (rec_record R REC_ADD (A ++ [s])) (O ++ [(p, n)]).
Proof. exact (rec_repA_append B HB LAWS). Qed.
Lemma s3_rep_last : forall ly S rd R A O,
  rec_repA B ly S rd (rec_record R REC_ADD A) O ->
  exists P, acall_at (ablocks B ly S) rd (sa_c R) (REC_ADD, A) P /\ (forall pn, In pn P -> In pn O).
Proof. exact (rec_repA_last_call B HB LAWS). Qed.
Lemma s3_rep_blocks : forall ly S rd R O, rec_repA B ly S rd R O ->
  forall pn, In pn O -> In pn (ablocks B ly S) /\ 1 <= snd pn /\
     iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE.
Proof.
intros ly S rd R O H. apply (rec_repA_fields B HB LAWS) in H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & HO). exact HO.
Qed.
Lemma s3_aro_kept : forall STK sp0 ly S W mem md own lyc Sc Wc memc mdc k R O,
  AR SEGS B ly S W mem md ->
  ajournal SEGS B STK sp0 (sa_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
  rec_repA B ly S (rdW W mem) R O ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof. exact (sa_aro_kept B HB LAWS IMG). Qed.
Lemma s3_str_ready : forall STK sp0 ly S W mem md own lyc Sc Wc memc mdc k R O p x,
  AR SEGS B ly S W mem md ->
  ajournal SEGS B STK sp0 (sa_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
  rec_repA B ly S (rdW W mem) R O ->
  arodata_okP SEGS RLO RHI B (rdW W mem) ->
  astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p (Some x) ->
  arodata_okP SEGS RLO RHI B (rdW Wc memc) ->
  (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
  astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] p (Some x) /\
  atail_vis SEGS Wc memc (p + Z.of_nat (length x)).
Proof. exact (sa_str_ready B HB LAWS IMG). Qed.
Lemma s3_achain : forall ly S W (regs : bvmap 5 word) mem md ch R O own lyc Sc Wc memc mdc k,
  afn_pre SEGS B SUP_ADD_STK ly S W regs mem md ch ->
  rec_repA B ly S (rdW W mem) R O ->
  ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
  sa_frame (rdW Wc memc) (spZ regs) regs ->
  exists ch1, achain lyc (rdW Wc memc) (sa_s1 (spZ regs)) (spZ regs) ch1.
Proof. exact (sa_achain B HB LAWS). Qed.
Lemma s3_uri : forall ly S (W : world SEGS) mem md O pu uri (ro : Z -> Prop), AR SEGS B ly S W mem md ->
  sa_uri B ly S (rdW W mem) O pu uri -> exists u, uri = Some u /\ astr_argA B ly S (rdW W mem) ro O pu (Some u).
Proof. exact (sa_uri_argA B HB LAWS). Qed.
Lemma s3_HPROG : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof. exact (sa_HPROG B HB LAWS). Qed.

(* ---- the program's statics, the slot and the blocks ---- *)
Lemma s3_unowned : forall a, inFP cmd_PG a ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. destruct (sa_prog_unowned B HB LAWS a Ha) as (H1 & H2).
exact (conj (cif_prog_img a Ha) (conj H1 H2)).
Qed.
(* a range of the allocator record's zero-shadow list, by one boolean check *)
Lemma s3_in_zs : forall r, existsb (fun q => (fst q =? fst r) && (snd q =? snd r)) Tfib_zero_shadow = true ->
  In r Tfib_zero_shadow.
Proof.
intros [a b] H. apply existsb_exists in H as ([c d] & Hin & E). cbn [fst snd] in E.
apply andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1, E2. subst. exact Hin.
Qed.
Lemma s3_slot_addressable : forall ly S W mem md c a n,
AR SEGS B ly S W mem md -> s3_slot c -> c <= a -> a + n <= c + 56 ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md c a n HAR Hsl Ha Hn.
destruct Hsl as [(i & Hi & ->) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX in *.
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00) a n HAR);
  [apply s3_in_zs; vm_compute; reflexivity | reflexivity | reflexivity
  | cbn [fst snd]; lia | cbn [fst snd]; lia].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x5e3c18 - 0x5e3be0) a n HAR);
  [apply s3_in_zs; vm_compute; reflexivity | reflexivity | reflexivity
  | cbn [fst snd]; lia | cbn [fst snd]; lia].
Qed.
Lemma s3_shok : forall ly S W mem md c E,
AR SEGS B ly S W mem md -> s3_slot c -> ew E 20 = Z_to_bv 64 SB -> ew E 22 = Z_to_bv 64 c ->
sh_ok SEGS s3_Bx s3_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md c E HAR Hsl E20 E22.
destruct (s3_slot_facts c [] Hsl) as (_ & Hcr & _ & _). unfold A_G_REC, A_REC_SPILL in Hcr.
constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E s3_Bx 22 c 56 c 0 56).
- exact (s3_slot_addressable ly S W mem md c c 56 HAR Hsl ltac:(lia) ltac:(lia)).
- unfold U, s3_Bx. cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
- lia.
- lia.
- intros x Hx. unfold SHADOW_OFF. lia.
Qed.
Lemma s3_awr_slot : forall E r rs STK sp0 O bl0 blc fr0 lyc own c,
YP09.r_base r = Some 22%nat -> bv_unsigned (ew E 22) = c -> s3_slot c -> 0 <= YP09.r_wlo r -> YP09.r_whi r <= 56 ->
awr_ok SEGS B E rs STK sp0 (sa_FP O) bl0 blc fr0 lyc own -> awr_ok SEGS B E (r :: rs) STK sp0 (sa_FP O) bl0 blc fr0 lyc own.
Proof.
intros E r rs STK sp0 O bl0 blc fr0 lyc own c Hb Hc Hsl Hlo Hhi H.
destruct (s3_slot_facts c O Hsl) as (_ & _ & Hcin & HcF).
eapply awr_ok_cons_gen; [exact Hb | exact Hc | | exact H].
intros a Ha. do 4 right. unfold awr_prog_or_caller. left.
split; [apply HcF; lia|]. split; [apply s3_HPROG, Hcin; lia | apply cif_prog_img, Hcin; lia].
Qed.
(* a byte of the program's statics is kept by a call whose footprint does not name it *)
Lemma s3_img_kept_j : forall STK1 sp1 FP1 lyc Sc (W : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
inFP cmd_PG a -> ~ YI16.sink_open_fp FP1 -> ~ inFP FP1 a ->
rdW W2 mem2 a = rdW W memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 a HJc Ha Hso Hnf.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _).
destruct (s3_unowned a Ha) as (Hi & Ho & He).
apply G3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [exact Hso | exact Hnf]].
Qed.
(* a live block lies off the image, so apart from g_rec and record.spill *)
Lemma s3_blk_apart : forall ly S (W : world SEGS) mem md p n, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> 1 <= n ->
  iv_apart p n A_G_REC REC_SIZE /\ iv_apart p n A_REC_SPILL SC_SIZE.
Proof.
intros ly S W mem md p n HAR Hin Hn.
assert (Hreq : req_size n = n) by (apply lem_req_pos; exact Hn).
assert (K : forall a, p <= a < p + n -> a < 0x10000 \/ 0x606000 <= a)
  by (intros a Ha; apply (lem_blk_off B HB LAWS ly S W mem md p n a HAR Hin); rewrite Hreq; exact Ha).
unfold iv_apart, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE.
split.
- destruct (Z_le_gt_dec (p + n) 0x5e3740) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (0x5e3740 + 960) p) as [H'|H']; [right; exact H'|].
  exfalso. destruct (Z_le_gt_dec p 0x5e3740) as [Hp|Hp].
  + destruct (K 0x5e3740 ltac:(lia)); lia.
  + destruct (K p ltac:(lia)); lia.
- destruct (Z_le_gt_dec (p + n) 0x5e3be0) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (0x5e3be0 + 56) p) as [H'|H']; [right; exact H'|].
  exfalso. destruct (Z_le_gt_dec p 0x5e3be0) as [Hp|Hp].
  + destruct (K 0x5e3be0 ltac:(lia)); lia.
  + destruct (K p ltac:(lia)); lia.
Qed.
Lemma s3_fresh_notin : forall (O bl : list (Z * Z)) p n, 1 <= n ->
  Forall (fun qk => iv_apart p n (fst qk) (snd qk)) bl ->
  (forall pn, In pn O -> In pn bl /\ 1 <= snd pn) -> ~ In p (map fst O).
Proof.
intros O bl p n Hn HF HO Hin. apply in_map_iff in Hin as ([q m] & Eq & Hqm). cbn [fst] in Eq. subst q.
destruct (HO (p, m) Hqm) as (Hb & Hm). cbn [snd] in Hm.
pose proof (proj1 (Forall_forall _ _) HF (p, m) Hb) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia.
Qed.
(* the accounting after one more block of the recorder *)
Lemma s3_acct_step : forall ly S R O lyc Sc Ok live ly1 S1 p n live',
  sa_acct B ly S R O lyc Sc Ok live ->
  Permutation (ablocks B ly1 S1) ((p, n) :: ablocks B lyc Sc) ->
  Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B lyc Sc) -> 1 <= n ->
  blocks_bytes S1 <= blocks_bytes Sc + n -> live + n <= live' ->
  sa_acct B ly S R O ly1 S1 (Ok ++ [(p, n)]) live'.
Proof.
intros ly S R O lyc Sc Ok live ly1 S1 p n live' (A1 & A2 & A3 & A4 & A5) HP HF Hn Hbb Hlv.
assert (Hin1 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly1 S1))
  by (intros pn Hpn; eapply Permutation_in; [apply Permutation_sym; exact HP | right; exact Hpn]).
assert (Hnew : In (p, n) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
split; [|split; [|split; [|split]]].
- intros pn Hpn. apply in_app_or in Hpn as [Hpn | Hpn]; [exact (A1 pn Hpn)|].
  cbn [In] in Hpn. destruct Hpn as [Hpn | []]. subst pn.
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) O) as [Hi | Hi];
  [left; exact Hi | right].
  intros Hin. pose proof (A3 (p, n) Hin Hi) as Hc.
  pose proof (proj1 (Forall_forall _ _) HF (p, n) Hc) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia.
- intros pn Hpn. eapply Permutation_in in Hpn; [|exact HP]. cbn [In] in Hpn. destruct Hpn as [Hpn | Hpn].
  + subst pn. right. apply in_or_app. right. left. reflexivity.
  + destruct (A2 pn Hpn) as [Hk | Hk]; [left; exact Hk | right; apply in_or_app; left; exact Hk].
- intros pn Hpn Hno. apply Hin1. exact (A3 pn Hpn Hno).
- intros pn Hpn. apply in_app_or in Hpn as [Hpn | Hpn]; [apply Hin1; exact (A4 pn Hpn)|].
  cbn [In] in Hpn. destruct Hpn as [Hpn | []]. subst pn. exact Hnew.
- lia.
Qed.
(* the stack above the callee's window, the side-stack frame and its shadow are kept by a call whose footprint lies
   in the image *)
Lemma s3_call_agree : forall STK1 sp1 FP1 lyc Sc (W : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 pos F lo hi,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
In (1, pos) (frames Sc) -> F = frame_addr lyc 1 pos ->
alloc_ceiling <= lo -> sp1 <= lo -> hi <= 2 ^ 64 ->
(forall a, inFP FP1 a -> 0x10000 <= a < 0x606000) ->
0 <= F -> F + 128 <= 0x10000 \/ 0x606000 <= F ->
(forall a, lo <= a < hi -> rdW W2 mem2 a = rdW W memc a) /\
(forall a, F <= a < F + 128 -> rdW W2 mem2 a = rdW W memc a) /\
(forall a, SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16 -> rdW W2 mem2 a = rdW W memc a).
Proof.
intros STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 pos F lo hi HJc Hin EF Hlo Hsp Hhi HFP HF0 HFi.
pose proof HJc as (HAR2 & _ & _ & _ & _ & _ & _ & _ & G1 & _ & _ & G4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split].
- intros a Ha. apply G1; [lia | lia | intros Hf; pose proof (HFP a Hf); lia].
- intros a Ha. apply (G4 1 pos a Hin).
  + left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. subst F. lia.
  + intros Hf. pose proof (HFP a Hf). lia.
- intros a Ha. apply (G4 1 pos a Hin).
  + right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. subst F. lia.
  + intros Hf. pose proof (HFP a Hf). unfold SHADOW_OFF in Ha. pose proof (Z.div_pos F 8 HF0 ltac:(lia)). lia.
Qed.

Lemma s3_sig_xstrdup : SIGMA CS_xstrdup = BASE + AF_xstrdup.
Proof. rewrite (SIGP CS_xstrdup); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.
Lemma s3_sig_arg_i : SIGMA CS_arg_i = BASE + AF_arg_i.
Proof. rewrite (SIGP CS_arg_i); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.

(* ---- the seed after xstrdup returns ---- *)
Lemma s3_seed2 : forall ly2 S2 W2 (regs2 : bvmap 5 word) mem2 md2 c,
AR SEGS B ly2 S2 W2 mem2 md2 -> s3_slot c ->
getr regs2 20 = w64 SHADOW_OFF -> getr regs2 22 = w64 c -> getr regs2 23 = w64 (c + 4) ->
getr regs2 27 = w64 (SHADOW_OFF + (c + 4) / 8) ->
aval_mem (rdW W2 mem2) (c + CALL_OFF_NARGS) 4 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs2 [])) s3_ss2
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 14984)) mem2 (seg_rom SEGS)))
/\ sh_ok SEGS s3_Bx s3_SH (Eimg (Ereg regs2 [])) (mrestrict (w_H W2) mem2).
Proof.
intros ly2 S2 W2 regs2 mem2 md2 c HAR Hsl H20 H22 H23 H27 Hn.
destruct (s3_slot_facts c [] Hsl) as (Hc8 & Hcr & Hcin & _).
unfold A_G_REC, A_REC_SPILL in Hcr.
set (E := Eimg (Ereg regs2 [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn'; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn').
assert (E20 : ew E 20 = Z_to_bv 64 SB) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
assert (E22 : ew E 22 = Z_to_bv 64 c) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (U22 : bv_unsigned (ew E 22) = c) by (rewrite E22; apply unsigned_lit_small; lia).
assert (HG : facts_ok E s3_facts2).
{ split; [|split; [exact I | exact I]].
  cbn [s3_facts2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E20, E22, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold A_G_REC, A_REC_SPILL. revert Hc8 Hcr. clear. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
assert (RW : YP09.region_ok SEGS E (mrestrict (w_H W2) mem2) s3_slotw).
{ unfold region_ok, s3_slotw. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U22. split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply PRW. apply s3_HPROG. apply Hcin. lia.
  - constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ c 4 4 (SLit 0) 0); [reflexivity | cbn; lia | lia |].
    exact (s3_val_mem_of_aval SEGS (w_H W2) mem2 (c + 4) 4 0 Hn). }
assert (HS0 : st_ok_pi SEGS VAL E s3_ss2a
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 14984)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold s3_ss2a. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact RW | constructor].
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - exact HG. }
pose proof (ast_ok_pi_set_reg_fp E s3_ss2a _ (23%bv : bv 5) (SOff 22 4) HS0 eq_refl
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite U22, H23; reflexivity)) as HS1.
pose proof (ast_ok_pi_set_reg_fp E _ _ (27%bv : bv 5) s3_shx HS1 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; unfold s3_shx;
        rewrite (denot_shx E 22 20 4 c SB E22 E20) by (unfold SB; lia); rewrite H27; reflexivity)) as HS2.
split; [exact HS2 | exact (s3_shok ly2 S2 W2 mem2 md2 c E HAR Hsl E20 E22)].
Qed.

(* the seed at 0x89fac after arg_i returns: nargs holds 2, read-only; s7 = c + 4, s11 the shadow of c + 4 *)
Lemma s3_seed3 : forall ly3 S3 W3 (regs3 : bvmap 5 word) mem3 md3 c,
AR SEGS B ly3 S3 W3 mem3 md3 -> s3_slot c ->
getr regs3 20 = w64 SHADOW_OFF -> getr regs3 22 = w64 c -> getr regs3 23 = w64 (c + 4) ->
getr regs3 27 = w64 (SHADOW_OFF + (c + 4) / 8) ->
aval_mem (rdW W3 mem3) (c + CALL_OFF_NARGS) 4 2 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs3 [])) s3_ss3
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + 15048)) mem3 (seg_rom SEGS)))
/\ sh_ok SEGS s3_Bx s3_SH (Eimg (Ereg regs3 [])) (mrestrict (w_H W3) mem3).
Proof.
intros ly3 S3 W3 regs3 mem3 md3 c HAR Hsl H20 H22 H23 H27 Hn.
destruct (s3_slot_facts c [] Hsl) as (Hc8 & Hcr & Hcin & _).
unfold A_G_REC, A_REC_SPILL in Hcr.
set (E := Eimg (Ereg regs3 [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
  by (intros n r Hn'; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn').
assert (E20 : ew E 20 = Z_to_bv 64 SB) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
assert (E22 : ew E 22 = Z_to_bv 64 c) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (U22 : bv_unsigned (ew E 22) = c) by (rewrite E22; apply unsigned_lit_small; lia).
assert (HG : facts_ok E s3_facts2).
{ split; [|split; [exact I | exact I]].
  cbn [s3_facts2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E20, E22, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold A_G_REC, A_REC_SPILL. revert Hc8 Hcr. clear. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
assert (RW : YP09.region_ok SEGS E (mrestrict (w_H W3) mem3) s3_nargs2).
{ unfold region_ok, s3_nargs2. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U22. split; [lia|]. split; [lia|]. split.
  - intros o Ho. lia.
  - constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ c 4 4 (SLit 2) 2); [reflexivity | cbn; lia | lia |].
    exact (s3_val_mem_of_aval SEGS (w_H W3) mem3 (c + 4) 4 2 Hn). }
assert (HS0 : st_ok_pi SEGS VAL E s3_ss3a
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + 15048)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold s3_ss3a. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact RW | constructor].
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - exact HG. }
pose proof (ast_ok_pi_set_reg_fp E s3_ss3a _ (23%bv : bv 5) (SOff 22 4) HS0 eq_refl
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite U22, H23; reflexivity)) as HS1.
pose proof (ast_ok_pi_set_reg_fp E _ _ (27%bv : bv 5) s3_shx HS1 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; unfold s3_shx;
        rewrite (denot_shx E 22 20 4 c SB E22 E20) by (unfold SB; lia); rewrite H27; reflexivity)) as HS2.
split; [exact HS2 | exact (s3_shok ly3 S3 W3 mem3 md3 c E HAR Hsl E20 E22)].
Qed.

Local Ltac s3_cs := unfold acallee_saved;
  match goal with |- context[bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.
Local Ltac s3_kof U :=
  intros ?b ?wlo ?whi ?a' ?Hin ?Hrr; vm_compute in Hin;
  repeat (destruct Hin as [?Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U in Hrr; lia|]); destruct Hin.
(* a register of a symbolic state as the denotation of its expression, not normalized *)
Local Ltac s3_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?Ev ?ssv (restrict ?H ?msv) =>
    pose proof (st_ok_pi_restrict_reg H Ev ssv msv r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?Ev ?ssv (restrict ?H ?msv) =>
    pose proof (st_ok_restrict_reg segs H Ev ssv msv r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Local Ltac s3_envof HS := lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => Ev | st_ok _ ?Ev _ _ => Ev end.
(* s7 = c + 4 and s11 = SB + (c + 4) / 8, kept as expressions of atom 22 = c (atom 20 = SB) *)
Local Ltac s3_r23_27 HS c E22 E20 A23 A27 :=
  s3_rreg HS (23%bv : bv 5) A23; s3_rreg HS (27%bv : bv 5) A27;
  let Ev := s3_envof HS in
  rewrite (s3_den_off Ev 22 4 c ltac:(exact E22) ltac:(lia)) in A23;
  rewrite (denot_shx Ev 22 20 4 c SB ltac:(exact E22) ltac:(exact E20) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold SB; lia)) in A27.

(* From the return of arg_i (0x89fac) to M2 (0x89fc0): check 5, the nargs load (2) and the `blt` on it (not taken).
   The run writes nothing. *)
Lemma sa_a2_ok : SA_M2_stmt B MT -> SA_A2_stmt B MT.
Proof using HB LAWS cmd_heap_tail_vis.
intros HM2. unfold SA_A2_stmt.
intros ly S W regs mem md ch pu id pp pc uri placement client R O pos ly3 S3 W3 regs3 mem3 md3 O2
  HCX HJ3 HFROK3 HBUF3 R2 R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 HNA3 HREP3 HACCT3 HMLE3.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCX as HCX0. unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
set (sp0 := spZ regs) in *.
assert (Hs1 : sa_s1 sp0 = sp0 - 160 \/ sa_s1 sp0 = sp0 - 176) by (apply s3_s1; exact Hal16).
pose proof (s3_slot_c R) as Hsl.
destruct (s3_slot_facts (sa_c R) O Hsl) as (Hc8 & Hcr & Hcin & HcFP).
unfold A_G_REC, A_REC_SPILL in Hcr.
pose proof (proj1 HJ3) as HAR3.
pose proof HJ3 as (_ & _ & _ & _ & _ & Hfrs3 & _).
assert (HinF3 : In (1, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 1 pos HAR3 HinF3) as (HF0 & HFc & _).
change (fs_frame_bytes 1) with 128 in HFc.
(* the seed *)
destruct (s3_seed3 ly3 S3 W3 regs3 mem3 md3 (sa_c R) HAR3 Hsl R20 R22 R23 R27 HNA3) as [HS SHOK].
remember (Eimg (Ereg regs3 [])) as E3 eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs3 r)
  by (intros n r Hn'; subst E3; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn').
clear HE3.
assert (U22 : bv_unsigned (ew E3 22) = sa_c R)
  by (rewrite (EE3 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
(* 0x89fac .. 0x89fc0 *)
paj_run_to_tok (paj_run_to B LAWS) HS HJ3 SHOK s3_Bspan L_M2.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U22 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; lia | apply awr_ok_nil]. }
try (set (mdv3 := with_vm_backing _ _ _) in *; clearbody mdv3).
lazymatch goal with Hfr : frame_of E3 _ (mrestrict _ mem3) (mrestrict _ ?m3) |- _ =>
  pose proof (kept_of_frame (segs:=SEGS) E3 _ (w_H W3) mem3 m3 (fun _ => False) Hfr ltac:(s3_kof U22)) as K3 end.
prreg HS (2%bv : bv 5) A2. prreg HS (3%bv : bv 5) A3. prreg HS (4%bv : bv 5) A4. prreg HS (8%bv : bv 5) A8.
prreg HS (9%bv : bv 5) A9. prreg HS (18%bv : bv 5) A18. prreg HS (19%bv : bv 5) A19. prreg HS (20%bv : bv 5) A20.
prreg HS (21%bv : bv 5) A21. prreg HS (22%bv : bv 5) A22. prreg HS (24%bv : bv 5) A24.
prreg HS (25%bv : bv 5) A25. prreg HS (26%bv : bv 5) A26.
assert (E22 : ew E3 22 = Z_to_bv 64 (sa_c R)) by (rewrite (EE3 22%nat 22%bv eq_refl); exact R22).
assert (E20 : ew E3 20 = Z_to_bv 64 SB) by (rewrite (EE3 20%nat 20%bv eq_refl); exact R20).
s3_r23_27 HS (sa_c R) E22 E20 A23 A27.
rewrite (EE3 2%nat 2%bv eq_refl), R2 in A2. rewrite (EE3 3%nat 3%bv eq_refl), R3 in A3.
rewrite (EE3 4%nat 4%bv eq_refl), R4 in A4. rewrite (EE3 8%nat 8%bv eq_refl), R8 in A8.
rewrite (EE3 9%nat 9%bv eq_refl), R9 in A9. rewrite (EE3 18%nat 18%bv eq_refl), R18 in A18.
rewrite (EE3 19%nat 19%bv eq_refl), R19 in A19. rewrite (EE3 20%nat 20%bv eq_refl), R20 in A20.
rewrite (EE3 21%nat 21%bv eq_refl), R21 in A21. rewrite (EE3 22%nat 22%bv eq_refl), R22 in A22.
rewrite (EE3 24%nat 24%bv eq_refl), R24 in A24.
rewrite (EE3 25%nat 25%bv eq_refl), R25 in A25. rewrite (EE3 26%nat 26%bv eq_refl), R26 in A26.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg (Z_to_bv 64 (BASE + ?k)) ?mm _; cfg_model := ?dd |} _ =>
  change (Z_to_bv 64 (BASE + k)) with (Z_to_bv 64 (BASE + L_M2)) end.
(* the run keeps every byte *)
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ ?mm _; cfg_model := ?dd |} _ =>
  assert (KK : forall a, 0 <= a < 2 ^ 64 -> rdW W3 mm a = rdW W3 mem3 a) by (intros a Ha; exact (K3 a Ha (fun H => H)));
  apply (HM2 ly S W regs mem md ch pu id pp pc uri placement client R O ly3 S3 W3 rg mm dd pos HCX0) end.
assert (Hs1r : sp0 - 176 <= sa_s1 sp0 <= sp0 - 160) by lia.
destruct (s3_frok_kept (rdW W3 mem3) (rdW W3 (ms_mem ms)) sp0 regs (frame_addr ly3 1 pos) (flag_addr ly3 1 pos) HFROK3 ltac:(lia)
  (fun a Ha => KK a ltac:(lia)) (fun a Ha => KK a ltac:(lia))) as (HFR & HV16 & HV24 & HV48 & HFLAG).
assert (HBUF : sa_buf0 (rdW W3 (ms_mem ms)) (frame_addr ly3 1 pos)).
{ apply (s3_buf0_kept (rdW W3 mem3)); [exact HBUF3|]. intros a Ha.
  pose proof (Z.div_pos (frame_addr ly3 1 pos) 8 ltac:(lia) ltac:(lia)).
  assert (frame_addr ly3 1 pos / 8 < 2 ^ 60) by (apply Z.div_lt_upper_bound; lia).
  apply KK. unfold SHADOW_OFF in *. lia. }
assert (HREP : rec_repA B ly3 S3 (rdW W3 (ms_mem ms)) (rec_record R REC_ADD [sarg uri; dec id]) O2).
{ destruct HACCT3 as (_ & _ & _ & HO2 & _).
  apply (s3_rep_kept ly3 S3 (rdW W3 mem3) ly3 S3 _ _ O2 HREP3).
  - intros a Ha. apply KK. unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha. lia.
  - intros p n i Hin Hi. destruct (s3_rep_blocks _ _ _ _ _ HREP3 (p, n) Hin) as (Hb & Hn1 & _). cbn [snd] in Hn1.
    destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR3 Hb) as (_ & Hp4096 & Hpceil & _).
    rewrite (lem_req_pos n Hn1) in Hpceil. apply KK. lia.
  - exact HO2. }
unfold sa_M2m, sa_core. cbv zeta. fold sp0.
split; [|split; [exact A20 | split; [exact A22 | split; [exact A23 | split; [exact A24 | split; [exact A27 |
  split; [exact HBUF | exists O2; exact (conj HREP (conj HACCT3 HMLE3))]]]]]]].
exact (conj HJ3 (conj HFR (conj HV16 (conj HV24 (conj HV48 (conj HFLAG (conj A2 (conj A3 (conj A4 (conj A8 (conj A9
  (conj A18 (conj A19 (conj A21 (conj A25 A26))))))))))))))).
Qed.

(* From the entry of xstrdup (called at 0x89f68 with a0 = uri) to M2. *)
Lemma sa3_cont : (forall fx1 : YK11.FPState, frm0 fx1 -> SA_A2_stmt (fx := fx1) B MT) ->
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos
  (regsx : bvmap 5 word) memx mdx,
sa_cx B MT ly S W regs mem md ch pu id pp pc uri placement client R O ->
sa_M1m B MT ly S W regs mem md R O lyc Sc Wc regs1 memc mdc pos ->
ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] lyc Sc Wc memx mdx (sa_ev1 R) ->
(forall a, 0 <= a < 2 ^ 64 ->
  ~ (SHADOW_OFF + frame_addr lyc 1 pos / 8 + 4 <= a < SHADOW_OFF + frame_addr lyc 1 pos / 8 + 8) ->
  rdW Wc memx a = rdW Wc memc a) ->
sa_buf0 (rdW Wc memx) (frame_addr lyc 1 pos) ->
getr regsx 10 = w64 pu -> getr regsx 1 = Z_to_bv 64 (BASE + 14984) ->
getr regsx 2 = getr regs1 2 -> getr regsx 3 = getr regs1 3 -> getr regsx 4 = getr regs1 4 ->
getr regsx 8 = getr regs1 8 -> getr regsx 9 = getr regs1 9 -> getr regsx 18 = getr regs1 18 ->
getr regsx 19 = getr regs1 19 -> getr regsx 20 = getr regs1 20 -> getr regsx 21 = getr regs1 21 ->
getr regsx 22 = getr regs1 22 -> getr regsx 23 = getr regs1 23 -> getr regsx 25 = getr regs1 25 ->
getr regsx 26 = getr regs1 26 -> getr regsx 27 = getr regs1 27 ->
SRr SEGS Wc (mkCfg (mkst regsx (Z_to_bv 64 (SIGMA CS_xstrdup)) memx (seg_rom SEGS)) mdx)
  (sa_final B MT ly S W regs mem md R O uri id placement client).
Proof using HB LAWS MTL SIGP PRW cif_prog_img cif_relro_img cif_prog_not_ro cmd_ro_in_img cmd_ro_ok_of_aro
  cmd_heap_tail_vis cmd_tail_vis_at FXR TXSTRDUP TARG_I.
intros HA2 ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos regsx memx mdx
  HCX HM1 HJx HKx HBUFx X10 X1 X2 X3 X4 X8 X9 X18 X19 X20 X21 X22 X23 X25 X26 X27.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCX as HCX0.
unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & Hfr7 & HROD & HRO & H10 & Hpu & H11 & Hid & H12 & Hpp & H13 & Hpc & HU & HP & HPT &
  HC & HCT & HREP & Hev & Hlive & HMOK).
unfold sa_M1m, sa_core in HM1. cbv zeta in HM1.
destruct HM1 as ((HJ1 & HFR & HV16 & HV24 & HV48 & HFLAG & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R25 & R26) &
  R20 & R22 & R23 & R24 & R27 & O1 & HREP1 & HACCT1 & HMLE1).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (s3_uri ly S W mem md O pu uri (in_roP SEGS RLO RHI) HAR0 HU) as (u & Huri & HUA).
assert (HUA' : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu (Some (sarg uri))) by (rewrite Huri; exact HUA).
set (sp0 := spZ regs) in *.
assert (Hs1 : sa_s1 sp0 = sp0 - 160 \/ sa_s1 sp0 = sp0 - 176) by (apply s3_s1; exact Hal16).
assert (Hs1r : sp0 - 176 <= sa_s1 sp0 <= sp0 - 160) by lia.
assert (Ho16 : (sa_s1 sp0 - sp0) mod 16 = 0).
{ destruct Hs1 as [E|E]; rewrite E;
  [replace (sp0 - 160 - sp0) with (-160) by lia | replace (sp0 - 176 - sp0) with (-176) by lia]; reflexivity. }
pose proof (s3_slot_c R) as Hsl.
destruct (s3_slot_facts (sa_c R) O Hsl) as (Hc8 & Hcr & Hcin & HcFP).
unfold A_G_REC, A_REC_SPILL in Hcr.
assert (HSTK : XSTRDUP_STK + 176 <= SUP_ADD_STK /\ ARG_I_STK + 176 <= SUP_ADD_STK)
  by (unfold SUP_ADD_STK, ARG_I_STK, XSTRDUP_STK; lia).
assert (HXS : XSTRDUP_STK = 16416) by reflexivity.
pose proof HJx as (HARx & _ & _ & _ & _ & Hfrsx & Hnevx & _).
assert (HinF : In (1, pos) (frames Sc)) by (rewrite Hfrsx; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memx mdx 1 pos HARx HinF) as (_ & HFapp & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memx mdx 1 pos HARx HinF) as (HF0 & HFc & _).
pose proof (frm_off_imgP B lyc Sc Wc memx mdx 1 pos HARx HinF) as HFimg.
change (fs_frame_bytes 1) with 128 in HFapp, HFc, HFimg.
hnf in HFimg. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (Hdm : frame_addr lyc 1 pos = 8 * (frame_addr lyc 1 pos / 8) + frame_addr lyc 1 pos mod 8) by (apply Z.div_mod; lia).
assert (Hmb : 0 <= frame_addr lyc 1 pos mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (HSTKSH : forall a, sa_s1 sp0 <= a < sp0 ->
  ~ (SHADOW_OFF + frame_addr lyc 1 pos / 8 + 4 <= a < SHADOW_OFF + frame_addr lyc 1 pos / 8 + 8)).
{ intros a Ha. unfold SHADOW_OFF. lia. }
assert (HFSH : forall a, frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 128 ->
  ~ (SHADOW_OFF + frame_addr lyc 1 pos / 8 + 4 <= a < SHADOW_OFF + frame_addr lyc 1 pos / 8 + 8)).
{ intros a Ha. unfold SHADOW_OFF. lia. }
(* the memory facts of sa_core at the call of xstrdup *)
assert (HFROKx : s3_frok (rdW Wc memx) sp0 regs (frame_addr lyc 1 pos) (flag_addr lyc 1 pos)).
{ apply (s3_frok_kept (rdW Wc memc)); [unfold s3_frok; repeat split; assumption | lia | |].
  - intros a Ha. apply HKx; [lia | apply HSTKSH; exact Ha].
  - intros a Ha. apply HKx; [lia | apply HFSH; exact Ha]. }
assert (Hkeep1 : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc))
  by (destruct HACCT1 as (_ & _ & K & _); exact K).
assert (HO1c : forall pn, In pn O1 -> In pn (ablocks B lyc Sc)) by (destruct HACCT1 as (_ & _ & _ & K & _); exact K).
assert (HRODx : arodata_okP SEGS RLO RHI B (rdW Wc memx))
  by exact (s3_aro_kept SUP_ADD_STK sp0 ly S W mem md [(1, pos)] lyc Sc Wc memx mdx (sa_ev1 R) R O HAR0 HJx HREP HROD).
(* xstrdup's string: the caller's uri, in a live block apart from the recorder's *)
assert (HSTR : astr_argA B lyc Sc (rdW Wc memx) (in_roP SEGS RLO RHI) [] pu (Some (sarg uri)) /\
  atail_vis SEGS Wc memx (pu + Z.of_nat (length (sarg uri))))
  by exact (s3_str_ready SUP_ADD_STK sp0 ly S W mem md [(1, pos)] lyc Sc Wc memx mdx (sa_ev1 R) R O pu (sarg uri)
      HAR0 HJx HREP HROD HUA' HRODx Hkeep1).
assert (HLX : Z.of_nat (length (sarg uri)) <= LMAX) by (destruct HSTR as ((_ & _ & HLn & _) & _); lia).
(* the budgets of the call *)
assert (HMXEV : 0 <= Z.max EV_ANSWER EV_HAND_BACK) by (vm_compute; discriminate).
assert (HEVx : st_nev Sc + EV_XSTRDUP <= EV_MAX).
{ unfold EV_SUP_ADD, sa_ev1 in *. unfold EV_ARG_I in *. change EV_XSTRDUP with 1 in *. lia. }
assert (HLVx : blocks_bytes Sc + LIVE_XSTRDUP (sarg uri) <= LIVE_MAX).
{ destruct HACCT1 as (_ & _ & _ & _ & Hbb).
  unfold LIVE_SUP_ADD, LIVE_ARG_I, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP in *. lia. }
assert (HXMnn : forall x, 0 <= XM_XSTRDUP MT x) by (intros x; unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia).
pose proof (mo_free_nonneg MT MTL) as HFnn.
pose proof (HXMnn (dec id)) as XN1. pose proof (HXMnn (darg placement (bstr "-"%string))) as XN2.
pose proof (HXMnn (darg client (bstr "-"%string))) as XN3.
pose proof (HXMnn (snd (sup_add_m R uri id placement client))) as XN4.
pose proof (HXMnn (sarg uri)) as XN5.
assert (HMOx : mo_ok MT Sc (XM_XSTRDUP MT (sarg uri))).
{ apply (mok_station MT S Sc _ (sa_acc1 MT R) _ MTL HMOK HMLE1 (HXMnn _)).
  unfold XM_SUP_ADD, sa_acc1, XM_ARG_I, XM_ANSWER, XM_HAND_BACK. lia. }
destruct (s3_achain ly S W regs mem md ch R O [(1, pos)] lyc Sc Wc memx mdx (sa_ev1 R) HPRE HREP HJx (proj1 HFROKx)) as [ch1 HCH].
assert (Hspx : spZ regsx = sp0 + (sa_s1 sp0 - sp0)).
{ unfold spZ at 1. rewrite X2, R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HRA1 : YK0s.ret_ok (Z_to_bv 64 (BASE + 14984))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + 14984))) by (rewrite unsigned_lit_small by lia; lia).
(* xstrdup: footprint [] *)
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc regsx memx (Z_to_bv 64 (SIGMA CS_xstrdup)) SUP_ADD_STK sp0 (sa_FP O) ly S W mem md [(1, pos)]
    lyc Sc mdx (sa_ev1 R) XSTRDUP_STK [] EV_XSTRDUP (sa_s1 sp0 - sp0) (Z_to_bv 64 (BASE + 14984)) ch1 _ HJx Hspx).
  - exact Ho16.
  - lia.
  - lia.
  - lia.
  - rewrite X3. exact R3.
  - rewrite X4. exact R4.
  - exact X1.
  - exact HRA1.
  - exact HRA4.
  - replace (sp0 + (sa_s1 sp0 - sp0)) with (sa_s1 sp0) by lia. unfold s0Z. rewrite X8, R8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
  - intros HPREx. rewrite s3_sig_xstrdup. eapply SRr_mono.
    { exact (TXSTRDUP fx lyc Sc Wc regsx memx mdx ch1 pu (sarg uri) HPREx HRODx X10 (or_introl (proj1 HSTR)) (proj2 HSTR)
        HEVx HLVx HMOx). }
    cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Hc3 & HJ3 & HP3 & HK3).
    exists ly3, S3, regs3, mem3, md3. split; [rewrite Hc3, X1; reflexivity|]. split; [exact HJ3|]. split; [exact HP3 | exact HK3].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 &
  (p0 & Hp010 & Hp064 & HPerm2 & Hfresh2 & Hinb2 & Hcp2 & Hsrc2 & Hbb2 & Hmle2)).
(* ---- back at 0x89f6c ---- *)
pose proof (proj1 HJ2) as HAR2.
pose proof HJc2 as (_ & HLYc2 & _ & _ & _ & Hfrs2 & _).
pose proof HLYc2 as (_ & _ & _ & _ & _ & EF2 & _).
assert (EFa2 : frame_addr ly2 1 pos = frame_addr lyc 1 pos) by (unfold frame_addr; rewrite EF2; reflexivity).
assert (EFl2 : flag_addr ly2 1 pos = flag_addr lyc 1 pos) by (unfold flag_addr; rewrite EF2; reflexivity).
assert (CS2 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr regsx rr)
  by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (Q2 : getr regs2 2 = w64 (sa_s1 sp0)) by (rewrite (CS2 2%bv ltac:(s3_cs)), X2; exact R2).
assert (Q3 : getr regs2 3 = w64 (as_gp B)) by (rewrite (CS2 3%bv ltac:(s3_cs)), X3; exact R3).
assert (Q4 : getr regs2 4 = w64 (as_tp B)) by (rewrite (CS2 4%bv ltac:(s3_cs)), X4; exact R4).
assert (Q8 : getr regs2 8 = w64 sp0) by (rewrite (CS2 8%bv ltac:(s3_cs)), X8; exact R8).
assert (Q9 : getr regs2 9 = w64 (sa_s1 sp0)) by (rewrite (CS2 9%bv ltac:(s3_cs)), X9; exact R9).
assert (Q18 : getr regs2 18 = w64 (frame_addr lyc 1 pos)) by (rewrite (CS2 18%bv ltac:(s3_cs)), X18; exact R18).
assert (Q19 : getr regs2 19 = getr regs 11) by (rewrite (CS2 19%bv ltac:(s3_cs)), X19; exact R19).
assert (Q20 : getr regs2 20 = w64 SHADOW_OFF) by (rewrite (CS2 20%bv ltac:(s3_cs)), X20; exact R20).
assert (Q21 : getr regs2 21 = w64 A_G_REC) by (rewrite (CS2 21%bv ltac:(s3_cs)), X21; exact R21).
assert (Q22 : getr regs2 22 = w64 (sa_c R)) by (rewrite (CS2 22%bv ltac:(s3_cs)), X22; exact R22).
assert (Q23 : getr regs2 23 = w64 (sa_c R + 4)) by (rewrite (CS2 23%bv ltac:(s3_cs)), X23; exact R23).
assert (Q25 : getr regs2 25 = w64 (SHADOW_OFF + frame_addr lyc 1 pos / 8)) by (rewrite (CS2 25%bv ltac:(s3_cs)), X25; exact R25).
assert (Q26 : getr regs2 26 = w64 (frame_addr lyc 1 pos)) by (rewrite (CS2 26%bv ltac:(s3_cs)), X26; exact R26).
assert (Q27 : getr regs2 27 = w64 (SHADOW_OFF + (sa_c R + 4) / 8)) by (rewrite (CS2 27%bv ltac:(s3_cs)), X27; exact R27).
(* the block xstrdup made *)
assert (Hin0 : In (p0, LIVE_XSTRDUP (sarg uri)) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2 | left; reflexivity]).
assert (HinS2 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; eapply Permutation_in; [apply Permutation_sym; exact HPerm2 | right; exact Hpn]).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p0 _ HAR2 Hin0) as (_ & Hp0lo & Hp0hi & _).
rewrite (lem_req_pos (LIVE_XSTRDUP (sarg uri)) ltac:(unfold LIVE_XSTRDUP; lia)) in Hp0hi.
(* the recorder's blocks at M1 *)
assert (HO1b : forall pn, In pn O1 -> In pn (ablocks B lyc Sc) /\ 1 <= snd pn)
  by (intros pn Hpn; destruct (s3_rep_blocks _ _ _ _ _ HREP1 pn Hpn) as (H1 & H2 & _); exact (conj H1 H2)).
(* the slot's nargs (0) at the return *)
destruct (s3_rep_last lyc Sc (rdW Wc memc) R [] O1 HREP1) as (P1 & HCALL1 & _).
destruct HCALL1 as (_ & _ & _ & _ & HNA1 & _). cbn [snd length Z.of_nat] in HNA1.
assert (HNA2 : aval_mem (rdW W2 mem2) (sa_c R + CALL_OFF_NARGS) 4 0).
{ intros k Hk.
  rewrite (s3_img_kept_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sa_c R + CALL_OFF_NARGS + Z.of_nat k) HJc2
    ltac:(apply Hcin; unfold CALL_OFF_NARGS; lia) ltac:(intros (r & Hr & _); destruct Hr) (inFP_nil _)).
  rewrite HKx by (unfold CALL_OFF_NARGS, SHADOW_OFF; pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)); lia).
  exact (HNA1 k Hk). }
(* the memory facts of sa_core at the return *)
destruct (s3_call_agree _ _ _ _ _ _ _ _ _ _ _ _ _ _ pos (frame_addr lyc 1 pos) (sa_s1 sp0) sp0 HJc2 HinF eq_refl
  ltac:(lia) ltac:(lia) ltac:(lia) (fun a Ha => False_ind _ (inFP_nil a Ha)) ltac:(lia) HFimg) as (KS2 & KF2 & KSH2).
assert (HFROK2 : s3_frok (rdW W2 mem2) sp0 regs (frame_addr lyc 1 pos) (flag_addr lyc 1 pos)).
{ apply (s3_frok_kept (rdW Wc memx)); [exact HFROKx | lia | intros a Ha; apply KS2; lia | intros a Ha; apply KF2; lia]. }
assert (HBUF2 : sa_buf0 (rdW W2 mem2) (frame_addr lyc 1 pos)).
{ apply (s3_buf0_kept (rdW Wc memx)); [exact HBUFx | intros a Ha; apply KSH2; lia]. }
(* g_rec, record.spill and the recorder's blocks from M1 to the return of xstrdup *)
assert (KREC2 : forall a, in_rec a -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha.
  rewrite (s3_img_kept_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc2 (s3_rec_pg a Ha) ltac:(intros (r & Hr & _); destruct Hr) (inFP_nil _)).
  apply HKx; unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, SHADOW_OFF in *;
  [lia | pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)); lia]. }
assert (KO12 : forall p n i, In (p, n) O1 -> 0 <= i < n -> rdW W2 mem2 (p + i) = rdW Wc memc (p + i)).
{ intros p n i Hin Hi. destruct (HO1b (p, n) Hin) as (Hb & Hn1). cbn [snd] in Hn1.
  destruct (al_blocks _ _ LAWS lyc Sc Wc memx mdx p n HARx Hb) as (_ & Hplo & Hphi & Hpapp & _).
  rewrite (lem_req_pos n Hn1) in Hphi, Hpapp.
  pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
  rewrite (G2 p n i Hb (HinS2 (p, n) Hb) ltac:(rewrite (lem_req_pos n Hn1); lia) (inFP_nil _)).
  apply HKx; [lia|]. intros Hsh.
  exact (fshadow_not_app (frame_addr lyc 1 pos) 8 p n (p + i) ltac:(lia) ltac:(lia) Hpapp ltac:(unfold SHADOW_OFF in Hsh; lia) ltac:(lia)). }
(* the seed *)
destruct (s3_seed2 ly2 S2 W2 regs2 mem2 md2 (sa_c R) HAR2 Hsl Q20 Q22 Q23 Q27 HNA2) as [HS SHOK].
remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
  by (intros n r Hn'; subst E2; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn').
clear HE2.
assert (E22 : ew E2 22 = Z_to_bv 64 (sa_c R)) by (rewrite (EE2 22%nat 22%bv eq_refl); exact Q22).
assert (U22 : bv_unsigned (ew E2 22) = sa_c R) by (rewrite E22; apply unsigned_lit_small; lia).
assert (E20 : ew E2 20 = Z_to_bv 64 SB) by (rewrite (EE2 20%nat 20%bv eq_refl); exact Q20).
assert (E10 : sv_denot E2 (SOff 10 0) = Z_to_bv 64 p0).
{ cbn [sv_denot]. rewrite (EE2 10%nat 10%bv eq_refl), Hp010, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
(* 0x89f6c .. 0x89fa8: check 3, nargs := 1, check 4, args[0] := the copy, the call of arg_i *)
paj_run_tok (paj_run B LAWS) HS HJ2 SHOK s3_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply s3_awr_slot; [reflexivity | exact U22 | exact Hsl | cbn; lia | cbn; lia | apply awr_ok_nil]. }
try (set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2).
lazymatch goal with Hfr : frame_of E2 _ (mrestrict _ mem2) (mrestrict _ ?m2) |- _ =>
  pose proof (kept_of_frame (segs:=SEGS) E2 _ (w_H W2) mem2 m2 (fun a => sa_c R + 4 <= a < sa_c R + 16) Hfr ltac:(s3_kof U22)) as KR2 end.
(* nargs = 1 and args[0] = the copy at the arg_i call, from the slot region *)
pose proof (st_ok_region_nth E2 _ _ 0%nat _ HS eq_refl) as HRg. cbn [ms_mem restrict mkst] in HRg.
assert (HNA1' : aval_mem (rdW W2 (ms_mem ms)) (sa_c R + CALL_OFF_NARGS) 4 1).
{ apply s3_aval_of_val_mem. unfold CALL_OFF_NARGS.
  exact (field_of_region E2 _ 22%nat (sa_c R) _ _ _ _ _ 4 4%N (SLit 1) 1 HRg U22
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(lia)). }
assert (HARG0 : aval_mem (rdW W2 (ms_mem ms)) (sa_c R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte)))) 8 p0).
{ apply s3_aval_of_val_mem. unfold CALL_OFF_ARGS. cbn [length Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r.
  exact (field_of_region E2 _ 22%nat (sa_c R) _ _ _ _ _ 8 8%N (SOff 10 0) p0 HRg U22
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) E10 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(lia)). }
(* register values at the arg_i call (atoms of E2, which is opaque) *)
prreg HS (10%bv : bv 5) A10. prreg HS (11%bv : bv 5) A11. prreg HS (1%bv : bv 5) A1.
prreg HS (2%bv : bv 5) A2. prreg HS (3%bv : bv 5) A3. prreg HS (4%bv : bv 5) A4. prreg HS (8%bv : bv 5) A8.
prreg HS (9%bv : bv 5) A9. prreg HS (18%bv : bv 5) A18. prreg HS (19%bv : bv 5) A19. prreg HS (20%bv : bv 5) A20.
prreg HS (21%bv : bv 5) A21. prreg HS (22%bv : bv 5) A22.
prreg HS (25%bv : bv 5) A25. prreg HS (26%bv : bv 5) A26.
s3_r23_27 HS (sa_c R) E22 E20 A23 A27.
s3_rreg HS (24%bv : bv 5) A24.
let Ev := s3_envof HS in rewrite (s3_den_off Ev 22 8 (sa_c R) ltac:(exact E22) ltac:(lia)) in A24.
assert (A10' : getr (ms_regs ms) 10 = w64 (sa_c R)) by (rewrite A10, E22; reflexivity).
assert (A11' : getr (ms_regs ms) 11 = w64 id) by (rewrite A11, (EE2 19%nat 19%bv eq_refl), Q19, H11; reflexivity).
rewrite (EE2 2%nat 2%bv eq_refl), Q2 in A2. rewrite (EE2 3%nat 3%bv eq_refl), Q3 in A3.
rewrite (EE2 4%nat 4%bv eq_refl), Q4 in A4. rewrite (EE2 8%nat 8%bv eq_refl), Q8 in A8.
rewrite (EE2 9%nat 9%bv eq_refl), Q9 in A9. rewrite (EE2 18%nat 18%bv eq_refl), Q18 in A18.
rewrite (EE2 19%nat 19%bv eq_refl), Q19 in A19. rewrite (EE2 20%nat 20%bv eq_refl), Q20 in A20.
rewrite (EE2 21%nat 21%bv eq_refl), Q21 in A21. rewrite (EE2 22%nat 22%bv eq_refl), Q22 in A22.
rewrite (EE2 25%nat 25%bv eq_refl), Q25 in A25. rewrite (EE2 26%nat 26%bv eq_refl), Q26 in A26.
assert (A24' : getr (ms_regs ms) 24 = w64 (sa_c R + 8)) by exact A24.
pmkst HS.
(* the frame and slot facts at the run-2 output (ly2 S2 W2 (ms_mem ms)) *)
assert (HAR2' : AR SEGS B ly2 S2 W2 (ms_mem ms) mdv2) by exact (proj1 HJ2).
assert (Hfrsc : frames S2 = (1, pos) :: frames S) by (pose proof HJ2 as (_ & _ & _ & _ & _ & Hf & _); exact Hf).
assert (HinF2 : In (1, pos) (frames S2)) by (rewrite Hfrsc; left; reflexivity).
assert (Hfrdisj : forall a, frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 128 -> ~ (sa_c R + 4 <= a < sa_c R + 16)).
{ intros a Ha Hc16. apply (frm_img SEGS B LAWS ly2 S2 W2 (ms_mem ms) mdv2 1 pos a HAR2' HinF2
    ltac:(change (fs_frame_bytes 1) with 128; rewrite EFa2; lia)).
  apply cif_prog_img. apply Hcin. lia. }
assert (HFROK2' : s3_frok (rdW W2 (ms_mem ms)) sp0 regs (frame_addr lyc 1 pos) (flag_addr lyc 1 pos)).
{ apply (s3_frok_kept (rdW W2 mem2)); [exact HFROK2 | lia
    | intros a Ha; apply KR2; [lia | intros Hc16; lia]
    | intros a Ha; apply KR2; [lia | exact (Hfrdisj a Ha)]]. }
assert (HBUF2' : sa_buf0 (rdW W2 (ms_mem ms)) (frame_addr lyc 1 pos)).
{ apply (s3_buf0_kept (rdW W2 mem2)); [exact HBUF2 | intros a Ha; unfold SHADOW_OFF in Ha;
    pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)); apply KR2; [lia | intros Hc16; lia]]. }
(* args[0]: the recorder with uri's copy appended, at the arg_i call *)
assert (HstrO : astr_atR (rdW W2 (ms_mem ms)) p0 (sarg uri)).
{ apply (s3_str_kept (rdW W2 mem2)); [exact Hcp2|]. intros i Hi. unfold LIVE_XSTRDUP in Hp0hi.
  pose proof (lem_blk_off B HB LAWS ly2 S2 W2 mem2 md2 p0 _ (p0 + i) HAR2 Hin0
    ltac:(rewrite (lem_req_pos (LIVE_XSTRDUP (sarg uri)) ltac:(unfold LIVE_XSTRDUP; lia)); unfold LIVE_XSTRDUP; lia)) as Hoff.
  apply KR2; [lia | intros Hc16; unfold A_G_REC, A_REC_SPILL in *; lia]. }
destruct (s3_blk_apart ly2 S2 W2 mem2 md2 p0 (LIVE_XSTRDUP (sarg uri)) HAR2 Hin0 ltac:(unfold LIVE_XSTRDUP; lia))
  as (Hap0a & Hap0b).
assert (HREPa : rec_repA B ly2 S2 (rdW W2 (ms_mem ms)) (rec_record R REC_ADD ([] ++ [sarg uri]))
  (O1 ++ [(p0, LIVE_XSTRDUP (sarg uri))])).
{ apply (s3_rep_append lyc Sc (rdW Wc memc) ly2 S2 (rdW W2 (ms_mem ms)) R [] O1 (sarg uri) p0 (LIVE_XSTRDUP (sarg uri))
    HREP1 ltac:(cbn [length]; lia)).
  - intros a Ha Hn1 Hn2. replace (Z.of_nat (length (@nil (list byte)))) with 0 in Hn2 by reflexivity.
    unfold CALL_OFF_NARGS, CALL_OFF_ARGS in *.
    rewrite <- (KREC2 a Ha). apply KR2; [unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia | lia].
  - intros p n i Hin Hi. rewrite <- (KO12 p n i Hin Hi).
    destruct (HO1b (p, n) Hin) as (Hb & Hn1). cbn [snd] in Hn1.
    pose proof (lem_blk_off B HB LAWS lyc Sc Wc memx mdx p n (p + i) HARx Hb
      ltac:(rewrite (lem_req_pos n Hn1); lia)) as Hoff.
    destruct (al_blocks _ _ LAWS lyc Sc Wc memx mdx p n HARx Hb) as (_ & Hplo & Hphi & _).
    rewrite (lem_req_pos n Hn1) in Hphi.
    apply KR2; [lia | intros Hc16; unfold A_G_REC, A_REC_SPILL in *; lia].
  - intros pn Hpn. apply HinS2. exact (HO1c pn Hpn).
  - exact HNA1'.
  - exact HARG0.
  - exact Hin0.
  - lia.
  - reflexivity.
  - exact HLX.
  - exact HstrO.
  - exact (s3_fresh_notin O1 (ablocks B lyc Sc) p0 (LIVE_XSTRDUP (sarg uri)) ltac:(unfold LIVE_XSTRDUP; lia) Hfresh2 HO1b).
  - exact Hap0a.
  - exact Hap0b. }
assert (HACCa : sa_acct B ly S R O ly2 S2 (O1 ++ [(p0, LIVE_XSTRDUP (sarg uri))]) (LIVE_XSTRDUP (sarg uri)))
  by exact (s3_acct_step ly S R O lyc Sc O1 0 ly2 S2 p0 (LIVE_XSTRDUP (sarg uri)) (LIVE_XSTRDUP (sarg uri)) HACCT1 HPerm2
      Hfresh2 ltac:(unfold LIVE_XSTRDUP; lia) Hbb2 ltac:(lia)).
(* budgets / arodata at the arg_i call *)
assert (HRODa : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms)))
  by exact (s3_aro_kept SUP_ADD_STK sp0 ly S W mem md [(1, pos)] ly2 S2 W2 (ms_mem ms) mdv2 (sa_ev1 R + EV_XSTRDUP) R O
      HAR0 HJ2 HREP HROD).
assert (HROOKa : cmd_ro_ok (rdW W2 (ms_mem ms))) by exact (cmd_ro_ok_of_aro ly2 S2 W2 (ms_mem ms) mdv2 HAR2' HRODa).
assert (HEVa : st_nev S2 + EV_ARG_I <= EV_MAX).
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & HnevJ & _).
  unfold EV_SUP_ADD, sa_ev1 in *. unfold EV_ARG_I in *. change EV_XSTRDUP with 1 in *. lia. }
assert (HLVa : blocks_bytes S2 + LIVE_ARG_I id <= LIVE_MAX).
{ destruct HACCT1 as (_ & _ & _ & _ & Hbb1).
  unfold LIVE_SUP_ADD, LIVE_ARG_I, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP in *. lia. }
assert (HMLES2 : mo_le MT S S2 (sa_acc1 MT R + XM_XSTRDUP MT (sarg uri))) by exact (mle_station MT S Sc S2 _ _ MTL HMLE1 Hmle2).
assert (HMOa : mo_ok MT S2 (XM_ARG_I MT id)).
{ apply (mok_station MT S S2 _ (sa_acc1 MT R + XM_XSTRDUP MT (sarg uri)) _ MTL HMOK HMLES2).
  - unfold XM_ARG_I. apply (mo_malloc_nonneg MT MTL). lia.
  - unfold XM_SUP_ADD, sa_acc1, XM_ARG_I, XM_ANSWER, XM_HAND_BACK. lia. }
(* the frame chain and the stack at the arg_i call *)
destruct (s3_achain ly S W regs mem md ch R O [(1, pos)] ly2 S2 W2 (ms_mem ms) mdv2 (sa_ev1 R + EV_XSTRDUP) HPRE HREP HJ2
  (proj1 HFROK2')) as [ch1' HCH'].
assert (Hsp2' : spZ (ms_regs ms) = sp0 + (sa_s1 sp0 - sp0))
  by (unfold spZ at 1; rewrite A2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (HRAa4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + 15048))) by (rewrite unsigned_lit_small by lia; lia).
(* arg_i: footprint c->nargs, c->args[1]; cl_callS_wideF, then the stage sa_a2_ok at the FP state arg_i returns *)
unfold sa_final.
eapply srr_after_callF.
{ eapply (cl_callS_wideF B LAWS W2 (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (SIGMA CS_arg_i)) SUP_ADD_STK sp0 (sa_FP O)
    ly S W mem md [(1, pos)] ly2 S2 mdv2 (sa_ev1 R + EV_XSTRDUP) ARG_I_STK
    [(sa_c R + CALL_OFF_NARGS, sa_c R + CALL_OFF_NARGS + 4); (sa_c R + CALL_OFF_ARGS + 8 * 1, sa_c R + CALL_OFF_ARGS + 8 * 1 + 8)]
    EV_ARG_I (sa_s1 sp0 - sp0) (Z_to_bv 64 (BASE + 15048)) ch1' _ HJ2 Hsp2').
  - exact Ho16.
  - lia.
  - unfold ARG_I_STK, ASTACK. lia.
  - destruct HSTK as [_ HSTKa]. lia.
  - exact A3.
  - exact A4.
  - exact A1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HRAa4.
  - replace (sp0 + (sa_s1 sp0 - sp0)) with (sa_s1 sp0) by lia. unfold s0Z. rewrite A8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH'.
  - intros HPREa. rewrite s3_sig_arg_i. eapply SRr_mono.
    { exact (TARG_I fx ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdv2 ch1' (sa_c R) id 1 HPREa FXR
        ltac:(rewrite Hfrsc; cbn [length]; lia) HRODa HROOKa A10' A11' Hid Hsl HNA1' ltac:(unfold REC_ARGS_MAX; lia) HEVa HLVa HMOa). }
    cbv beta. intros W3 c3 _ (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hf3 & Hg3 & HJ3 & HP3 & HK3).
    exists fx3, ly3, S3, regs3, mem3, md3. split; [rewrite Hc3, A1; reflexivity|].
    split; [exact Hf3|]. split; [exact Hg3|]. split; [exact HJ3|]. split; [exact HP3 | exact HK3].
  - intros a HaFP. do 4 right. unfold awr_prog_or_caller. left.
    assert (Hain : sa_c R <= a < sa_c R + 56).
    { apply inFP_cons in HaFP. destruct HaFP as [Hr | HaFP]; [unfold CALL_OFF_NARGS in Hr; lia|].
      apply inFP_cons in HaFP. destruct HaFP as [Hr | HaFP]; [unfold CALL_OFF_ARGS in Hr; lia | destruct (inFP_nil a HaFP)]. }
    split; [apply HcFP; lia | split; [apply s3_HPROG; apply Hcin; lia | apply cif_prog_img; apply Hcin; lia]].
  - intros ly3 S3 W3 regs3 mem3 md3 HKK a HaFP Hstk3 Hns. exfalso.
    assert (Hain : a < sa_c R + 56).
    { apply inFP_cons in HaFP. destruct HaFP as [Hr | HaFP]; [unfold CALL_OFF_NARGS in Hr; lia|].
      apply inFP_cons in HaFP. destruct HaFP as [Hr | HaFP]; [unfold CALL_OFF_ARGS in Hr; lia | destruct (inFP_nil a HaFP)]. }
    lia. }
cbv beta. intros fx3 ly3 S3 W3 regs3 mem3 md3 Hwle3 Hfx3 (HJ3 & HJc3 & HP3 & Hbb3 & Hmlea & HKa).
destruct HKa as [(Hm6 & _) | (_ & p1 & HK1)]; [exfalso; unfold REC_ARGS_MAX in Hm6; lia|].
cbv zeta in HK1. destruct HK1 as (Hp1 & HPerm3 & Hfresh3 & HNA3 & HARG1 & Hstr3).
(* ---- back at 0x89fac ---- *)
pose proof (proj1 HJ3) as HAR3.
pose proof HJc3 as (_ & HLYc3 & _ & _ & _ & Hfrs3 & _).
pose proof HLYc3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly3 1 pos = frame_addr lyc 1 pos) by (unfold frame_addr; rewrite EF3; exact EFa2).
assert (EFl3 : flag_addr ly3 1 pos = flag_addr lyc 1 pos) by (unfold flag_addr; rewrite EF3; exact EFl2).
assert (CS3 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs3 rr = getr (ms_regs ms) rr)
  by (intros rr Hr; pose proof (HP3 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (Hin1 : In (p1, Z.of_nat (length (dec id)) + 1) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3 | left; reflexivity]).
assert (HinS3 : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly3 S3))
  by (intros pn Hpn; eapply Permutation_in; [apply Permutation_sym; exact HPerm3 | right; exact Hpn]).
destruct (s3_blk_apart ly3 S3 W3 mem3 md3 p1 (Z.of_nat (length (dec id)) + 1) HAR3 Hin1 ltac:(lia)) as (Hap1a & Hap1b).
pose proof (dec_length id Hid) as Hdl.
(* the arg_i footprint lies in the slot; everything else of the image, and the blocks, are kept *)
assert (Hso3 : ~ YI16.sink_open_fp [(sa_c R + CALL_OFF_NARGS, sa_c R + CALL_OFF_NARGS + 4);
  (sa_c R + CALL_OFF_ARGS + 8 * 1, sa_c R + CALL_OFF_ARGS + 8 * 1 + 8)]).
{ apply sink_closed_cons; [cbn [fst]; unfold CALL_OFF_NARGS; lia|].
  apply sink_closed_cons; [cbn [fst]; unfold CALL_OFF_ARGS; lia|]. intros (r & Hr & _). destruct Hr. }
assert (HnF3 : forall a, inFP [(sa_c R + CALL_OFF_NARGS, sa_c R + CALL_OFF_NARGS + 4);
  (sa_c R + CALL_OFF_ARGS + 8 * 1, sa_c R + CALL_OFF_ARGS + 8 * 1 + 8)] a ->
  sa_c R + 4 <= a < sa_c R + 8 \/ sa_c R + 16 <= a < sa_c R + 24).
{ intros a HaFP. unfold CALL_OFF_NARGS, CALL_OFF_ARGS in HaFP.
  apply inFP_cons in HaFP. destruct HaFP as [Hr | HaFP]; [left; lia|].
  apply inFP_cons in HaFP. destruct HaFP as [Hr | HaFP]; [right; lia | destruct (inFP_nil a HaFP)]. }
assert (HO1b2 : forall pn, In pn (O1 ++ [(p0, LIVE_XSTRDUP (sarg uri))]) -> In pn (ablocks B ly2 S2) /\ 1 <= snd pn).
{ intros pn Hpn. apply in_app_or in Hpn as [Hpn | Hpn].
  - destruct (HO1b pn Hpn) as (H1 & H2). exact (conj (HinS2 pn H1) H2).
  - cbn [In] in Hpn. destruct Hpn as [<- | []]. split; [exact Hin0 | cbn [snd]; unfold LIVE_XSTRDUP; lia]. }
assert (HREP3 : rec_repA B ly3 S3 (rdW W3 mem3) (rec_record R REC_ADD ([sarg uri] ++ [dec id]))
  ((O1 ++ [(p0, LIVE_XSTRDUP (sarg uri))]) ++ [(p1, Z.of_nat (length (dec id)) + 1)])).
{ apply (s3_rep_append ly2 S2 (rdW W2 (ms_mem ms)) ly3 S3 (rdW W3 mem3) R [sarg uri] _ (dec id) p1 _
    HREPa ltac:(cbn [length]; lia)).
  - intros a Ha Hn1 Hn2. replace (Z.of_nat (length [sarg uri])) with 1 in Hn2 by reflexivity.
    unfold CALL_OFF_NARGS, CALL_OFF_ARGS in *.
    apply (s3_img_kept_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3 (s3_rec_pg a Ha) Hso3).
    intros HaFP. destruct (HnF3 a HaFP); lia.
  - intros p n i Hin Hi. destruct (HO1b2 (p, n) Hin) as (Hb & Hn1). cbn [snd] in Hn1.
    pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
    pose proof (lem_blk_off B HB LAWS ly2 S2 W2 (ms_mem ms) mdv2 p n (p + i) HAR2' Hb
      ltac:(rewrite (lem_req_pos n Hn1); lia)) as Hoff.
    apply (G2 p n i Hb (HinS3 (p, n) Hb) ltac:(rewrite (lem_req_pos n Hn1); lia)).
    intros HaFP. destruct (HnF3 _ HaFP); unfold A_G_REC, A_REC_SPILL in *; lia.
  - intros pn Hpn. apply HinS3. exact (proj1 (HO1b2 pn Hpn)).
  - exact HNA3.
  - exact HARG1.
  - exact Hin1.
  - lia.
  - reflexivity.
  - unfold LMAX. lia.
  - exact Hstr3.
  - exact (s3_fresh_notin (O1 ++ [(p0, LIVE_XSTRDUP (sarg uri))]) (ablocks B ly2 S2) p1 (Z.of_nat (length (dec id)) + 1)
      ltac:(lia) Hfresh3 HO1b2).
  - exact Hap1a.
  - exact Hap1b. }
assert (HACC3 : sa_acct B ly S R O ly3 S3 ((O1 ++ [(p0, LIVE_XSTRDUP (sarg uri))]) ++ [(p1, Z.of_nat (length (dec id)) + 1)])
  (sa_live2 uri id))
  by exact (s3_acct_step ly S R O ly2 S2 (O1 ++ [(p0, LIVE_XSTRDUP (sarg uri))]) (LIVE_XSTRDUP (sarg uri)) ly3 S3 p1
      (Z.of_nat (length (dec id)) + 1) (sa_live2 uri id) HACCa HPerm3 Hfresh3 ltac:(lia) Hbb3
      ltac:(unfold sa_live2, LIVE_ARG_I, LIVE_XSTRDUP; lia)).
assert (HMLE3 : mo_le MT S S3 (sa_acc2 MT R uri id)) by exact (mle_station MT S S2 S3 _ _ MTL HMLES2 Hmlea).
(* the frame, its shadow and the real frame through arg_i *)
assert (HinF2' : In (1, pos) (frames S2)) by exact HinF2.
destruct (s3_call_agree _ _ _ _ _ _ _ _ _ _ _ _ _ _ pos (frame_addr ly2 1 pos) (sa_s1 sp0) sp0 HJc3 HinF2' eq_refl
  ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(intros a HaFP; destruct (HnF3 a HaFP); unfold A_G_REC, A_REC_SPILL in *; lia)
  ltac:(rewrite EFa2; lia) ltac:(rewrite EFa2; exact HFimg)) as (KS3 & KF3 & KSH3).
rewrite EFa2 in KF3, KSH3.
assert (HFROK3 : s3_frok (rdW W3 mem3) sp0 regs (frame_addr ly3 1 pos) (flag_addr ly3 1 pos)).
{ rewrite EFa3, EFl3.
  apply (s3_frok_kept (rdW W2 (ms_mem ms))); [exact HFROK2' | lia | intros a Ha; apply KS3; lia | intros a Ha; apply KF3; lia]. }
assert (HBUF3 : sa_buf0 (rdW W3 mem3) (frame_addr ly3 1 pos)).
{ rewrite EFa3. apply (s3_buf0_kept (rdW W2 (ms_mem ms))); [exact HBUF2' | intros a Ha; apply KSH3; lia]. }
(* nargs = 2 *)
assert (HNA3' : aval_mem (rdW W3 mem3) (sa_c R + CALL_OFF_NARGS) 4 2) by exact HNA3.
exact (HA2 fx3 (fxrel_frm0 fx fx3 FXR Hfx3) ly S W regs mem md ch pu id pp pc uri placement client R O pos
  ly3 S3 W3 regs3 mem3 md3 _
  HCX0 HJ3 HFROK3 HBUF3
  ltac:(rewrite (CS3 2%bv ltac:(s3_cs)); exact A2) ltac:(rewrite (CS3 3%bv ltac:(s3_cs)); exact A3)
  ltac:(rewrite (CS3 4%bv ltac:(s3_cs)); exact A4) ltac:(rewrite (CS3 8%bv ltac:(s3_cs)); exact A8)
  ltac:(rewrite (CS3 9%bv ltac:(s3_cs)); exact A9)
  ltac:(rewrite (CS3 18%bv ltac:(s3_cs)), EFa3; exact A18) ltac:(rewrite (CS3 19%bv ltac:(s3_cs)); exact A19)
  ltac:(rewrite (CS3 20%bv ltac:(s3_cs)); exact A20) ltac:(rewrite (CS3 21%bv ltac:(s3_cs)); exact A21)
  ltac:(rewrite (CS3 22%bv ltac:(s3_cs)); exact A22) ltac:(rewrite (CS3 23%bv ltac:(s3_cs)); exact A23)
  ltac:(rewrite (CS3 24%bv ltac:(s3_cs)); exact A24')
  ltac:(rewrite (CS3 25%bv ltac:(s3_cs)), EFa3; exact A25) ltac:(rewrite (CS3 26%bv ltac:(s3_cs)), EFa3; exact A26)
  ltac:(rewrite (CS3 27%bv ltac:(s3_cs)); exact A27)
  HNA3' HREP3 HACC3 HMLE3).
Qed.
End e.
End f.
End d.
