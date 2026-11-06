(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of pins_set (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_pins_set = 0x8c938, 48 instructions, 192 bytes): it proves a Theorem Labs lane's
   `tpins_set_spec` (lib/B/Prog/pins_set_c.v, a working branch 357b1f0783f) in the form of the B walks
   lib/B/Prog/lv2_refusals_forget.v (a working branch 7b0abe3bdf8) and lib/B/Prog/sup_reset.v
   (a working branch c79a9f2daf7): afn_pre at the entry, the symbolic executor over the position-abstract
   listing between the calls, the callee contracts record_c, arg_s_c and mix_call_c through cl_callS_wide
   (pins_set_s2.v psb_call_record / psb_call_arg_s / psb_call_mix), and the tail jump into answer_code through
   callS_wideF (pins_set_s2.v psb_tail), whose post is apost_baseF. It is the B re-walk of the A walk
   lib/A/Prog/pins_set.v (+ _s1 .. _s13.v, a working branch 3cc8391594b), where A inlines record() and
   xstrdup and B calls record and arg_s; the B code template was read from the Generation-N walk
   lib/B/Prog/pins_set.v (template only, not ported: a working branch 3608b19d2cb).

   B's code (capstone on fuzz_command.asan-ubsan, sha256 658cefbe..., symbol pins_set; listing CmdList.v:6481-6528):
     0x8c938 addi sp,sp,-48; sd ra,s0..s4; mv s1,a3; mv s2,a2; mv s3,a1; mv s4,a0; li a0,20
     0x8c968 jal record          0x8c96c mv s0,a0; mv a1,s4
     0x8c974 jal arg_s (uri)     0x8c978 mv a0,s0; mv a1,s3
     0x8c980 jal arg_s (files)   0x8c984 mv a0,s0; mv a1,s2
     0x8c98c jal arg_s (layout)
     0x8c990 bnez s1,0x8c99c; auipc a0 (A_HI 195); addi s1,a0 (= 0x21d80, "-", A_OBJ 52)
     0x8c99c mv a0,s0; mv a1,s1; 0x8c9a4 jal arg_s (verdict or "-")
     0x8c9a8 auipc a0 (A_HI 196); addi s1,a0 (= g_rec, A_OBJ 44); lw a0,0(s1); beqz a0,0x8c9c0
     0x8c9b8 lw a0,4(s1); j 0x8c9d8
     0x8c9c0 ld a0,0x3b0(s1); mv a1,s0; 0x8c9c8 jal mix_call; mv a1,a0; li a0,0; sd a1,0x3b0(s1)
     0x8c9d8 ld ra,s0..s4; addi sp,sp,48; 0x8c9f4 j answer_code
   There is no __asan_report_* call and no UBSan trap (unimp / ebreak) in the function, so it has no report edge to
   refute. The two branches are data branches, split by paj_branch: `bnez s1` at 0x8c990 (verdict NULL or not; the
   arms join at the call of arg_s in the state psw_ssC, where s1 = a1 = the atom of the string), and `beqz a0` at
   0x8c9b4 (g_rec.refuse), whose arms each end in the tail jump. Every load and store of g_rec goes through s1 =
   the object atom A_OBJ 44 (VOBJS), none through an auipc value, so the walk needs no cmd_val_his.

   Section hypotheses beyond the statement's: HB (the allocator record) and MTL (the meter's laws), as the A walk names
   them; and the per-binary facts a Theorem Labs lane proves only at the pinned image (PI := PB_cmd), each under a Theorem Labs lane's lemma name
   with its statement at this walk's abstract PAImg: `cmd_sig_prog_PB : cmd_sig_prog` (the program functions' call
   targets), `cmd_img_facts_tfib` (lib/B/Prog/CmdRecImg.v), and `PRW : prog_rw SEGS B` (the hypothesis of
   lib/B/Prog/CmdRecCells.v PROG_WRITABLE, for the store of g_rec.state at 0x8c9d4). Every other per-binary fact is
   a Theorem Labs lane's lemma over them, by exact. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo CmdZsh PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_calls_free_c record_c arg_s_c mix_call_c hand_back_c answer_code_c pins_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdRecBase CmdRecImg CmdRecCells CmdRecRo CmdRecRest RecBLemmas CmdRecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pins_set_aux pins_set_s1 pins_set_s2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the atoms and the stops of the walk on B's listing (lib/B/Prog/CmdList.v, CmdAddr.v) ------------------ *)
(* the extra atoms above the 32 registers: the fourth string's address (the verdict, or "-"), and g_rec's refuse,
   code (each as its 32-bit word) and state at the entry *)
Definition P_V : nat := 32.
Definition P_RF : nat := 33.
Definition P_CD : nat := 34.
Definition P_ST : nat := 35.
Definition psw_extra (v rf cd st : Z) : list word := map (Z_to_bv 64) [v; rf mod 2 ^ 32; cd mod 2 ^ 32; st].
Definition P_GREC : nat := A_OBJ 44.   (* 0x5e32c0, g_rec: the addi at 0x8c9ac (PAddHi 196) *)
Definition P_DASH : nat := A_OBJ 52.   (* 0x21d80, "-": the addi at 0x8c998 (PAddHi 195) *)
(* the listing offset of the call of arg_s where the arms of `bnez s1` meet (0x8c9a4) *)
Definition PS_ARG4 : Z := AF_pins_set + 0x6c.

(* ---- the symbolic states ----------------------------------------------------------------------------------- *)
(* the entry: the prologue's 48-byte frame below sp; the function has no shadow check of its own *)
Definition psw_facts0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition psw_ss0 : sstate := mkSS AF_pins_set sr_atoms [stack_region 48] None psw_facts0.
Definition psw_retk (ss : sstate) : Z := match sr_get (ss_regs ss) 1 with SOff _ z => z | _ => 0 end.
(* the runs to the calls of record and the first three arg_s, and the states after them (the frame kept, the
   clobbered registers at atoms 36.., 52.., 68.., 84..) *)
Definition psw_r0 := Eval vm_compute in sym_runN_pi cmd_tpi FUEL psw_ss0.
Definition psw_s1 : sstate := Eval vm_compute in
  ss_after_call (fst psw_r0) (pick (ss_mem (fst psw_r0)) [0%nat]) 36 (psw_retk (fst psw_r0)).
Definition psw_r1 := Eval vm_compute in sym_runN_pi cmd_tpi FUEL psw_s1.
Definition psw_s2 : sstate := Eval vm_compute in
  ss_after_call (fst psw_r1) (pick (ss_mem (fst psw_r1)) [0%nat]) 52 (psw_retk (fst psw_r1)).
Definition psw_r2 := Eval vm_compute in sym_runN_pi cmd_tpi FUEL psw_s2.
Definition psw_s3 : sstate := Eval vm_compute in
  ss_after_call (fst psw_r2) (pick (ss_mem (fst psw_r2)) [0%nat]) 68 (psw_retk (fst psw_r2)).
Definition psw_r3 := Eval vm_compute in sym_runN_pi cmd_tpi FUEL psw_s3.
Definition psw_s4 : sstate := Eval vm_compute in
  ss_after_call (fst psw_r3) (pick (ss_mem (fst psw_r3)) [0%nat]) 84 (psw_retk (fst psw_r3)).
(* the join at the call of arg_s: s1 and a1 hold the atom P_V of the string (the verdict, or "-"), the facts are the
   atoms' *)
Definition psw_canon (ss : sstate) : sstate :=
  mkSS (ss_pc ss) (sr_set (sr_set (ss_regs ss) 9 (SOff P_V 0)) 11 (SOff P_V 0)) (ss_mem ss) None
    (mkFacts (f_atoms (ss_facts ss)) [] []).
Definition psw_ssC : sstate := Eval vm_compute in
  psw_canon (fst (sym_run_toN_pi cmd_tpi FUEL PS_ARG4 (add_cond psw_s4 (mkAC BC_NE (SOff 13 0) (SLit 0))))).
Lemma psw_ssC_facts : ss_facts psw_ssC = mkFacts (f_atoms (ss_facts psw_ssC)) [] [].
Proof. vm_compute. reflexivity. Qed.
(* g_rec's refuse, code and state for the loads at 0x8c9b0, 0x8c9b8, 0x8c9c0 (seated after the fourth arg_s returns),
   and the region of the store at 0x8c9d4 (seated after mix_call returns), based at the object atom of g_rec *)
Definition psw_grec_region : YP09.region :=
  YP09.mkRegion (Some P_GREC) 0 0x3b8 0 0
    [YP09.mkChunk 0 (CVal 4 (SOff P_RF 0)); YP09.mkChunk 4 (CVal 4 (SOff P_CD 0)); YP09.mkChunk 0x3b0 (CVal 8 (SOff P_ST 0))].
Definition psw_store_region : YP09.region := YP09.mkRegion (Some P_GREC) 0x3b0 0x3b8 0x3b0 0x3b8 [].

(* the four strings the call records, in the order arg_s appends them *)
Lemma psw_A4 : forall (u f l : list byte) verdict,
[u; f; l] ++ [darg verdict psb_dash] = psb_A (Some u) (Some f) (Some l) verdict.
Proof. intros u f l verdict. reflexivity. Qed.

(* a 32-bit field's atom read back through `lw` (sign extension of its low word) *)
Lemma psw_sext_atom : forall E n z, ew E n = Z_to_bv 64 (z mod 2 ^ 32) -> -2 ^ 31 <= z < 2 ^ 31 ->
sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 z.
Proof.
intros E n z Hn Hz. pose proof (Z.mod_pos_bound z (2 ^ 32) ltac:(lia)) as Hm.
cbn [sv_denot]. rewrite Hn, unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite <- (sext32_small z Hz).
pose proof (zext_low_sound true 32 (z mod 2 ^ 32)) as E1. pose proof (zext_low_sound true 32 z) as E2.
cbv iota in E1, E2. rewrite E1, E2. f_equal. unfold zext_low, zcanon, M64.
change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small (z mod 2 ^ 32) (2 ^ 64)) by lia. rewrite Zmod_mod.
rewrite (Z.mod_mod_divide z (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity). reflexivity.
Qed.

(* the same field read back from its atom, in the form the register printer leaves *)
Lemma psw_sext_ew : forall E n z, ew E n = Z_to_bv 64 (z mod 2 ^ 32) -> -2 ^ 31 <= z < 2 ^ 31 ->
sext 64 (bv_extract 0 32 (ew E n)) = Z_to_bv 64 z.
Proof.
intros E n z Hn Hz. pose proof (Z.mod_pos_bound z (2 ^ 32) ltac:(lia)) as Hm. rewrite Hn.
rewrite <- (sext32_small z Hz).
pose proof (zext_low_sound true 32 (z mod 2 ^ 32)) as E1. pose proof (zext_low_sound true 32 z) as E2.
cbv iota in E1, E2. rewrite E1, E2. f_equal. unfold zext_low, zcanon, M64.
change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small (z mod 2 ^ 32) (2 ^ 64)) by lia. rewrite Zmod_mod.
rewrite (Z.mod_mod_divide z (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity). reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* cgif's region_kept over aview for a region whose window bytes stay present (lv2_refusals_forget's B walk,
   lrfb_region_kept_hi2): the call's world may grow *)
Lemma psw_region_kept_hi2 : forall (segs : list Segment) E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview segs H2 m2 a = aview segs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept segs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros segs E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav. exact Ha.
- intros _. apply (apresent_writable segs). apply Hp. exact Ha.
Qed.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* a symbolic state with other register forms of the same values and fewer facts (lv2_refusals_forget's B walk) *)
Lemma psw_st_ok_canon : forall E ss ms sr G,
st_ok_pi SEGS VAL E ss ms -> (forall r, sv_denot E (sr_get sr r) = sv_denot E (sr_get (ss_regs ss) r)) -> facts_ok E G ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) sr (ss_mem ss) (ss_resv ss) G) ms.
Proof.
intros E [pc sr0 fr0 m0 rv0 G0] ms sr G (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hr HG.
unfold abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
split; [|split; [exact H8 | exact HG]].
intros r. rewrite (H7 r). symmetry. apply Hr.
Qed.
Lemma psw_facts_atoms : forall E at0 cs al, facts_ok E (mkFacts at0 cs al) -> facts_ok E (mkFacts at0 [] []).
Proof. intros E at0 cs al [Ha _]. split; [exact Ha | split; exact I]. Qed.
(* both arms of `bnez s1` reach the call of arg_s in the state psw_ssC, whose s1 and a1 are the atom of the string *)
Lemma psw_canon_ok : forall E ss ms v,
st_ok_pi SEGS VAL E ss ms ->
ss_pc ss = ss_pc psw_ssC -> ss_mem ss = ss_mem psw_ssC -> ss_resv ss = None ->
f_atoms (ss_facts ss) = f_atoms (ss_facts psw_ssC) ->
forallb (fun r => sv_eqb (sr_get (ss_regs ss) r) (sr_get (ss_regs psw_ssC) r) ||
   (sv_eqb (sr_get (ss_regs ss) r) v && sv_eqb (sr_get (ss_regs psw_ssC) r) (SOff P_V 0))) all_regs = true ->
sv_denot E v = sv_denot E (SOff P_V 0) ->
st_ok_pi SEGS VAL E psw_ssC ms.
Proof.
intros E [pc sr0 fr0 m0 rv0 G0] ms v HS Hpc Hm Hrv Hat Hb Hv.
cbn [ss_pc ss_mem ss_resv ss_facts ss_regs] in Hpc, Hm, Hrv, Hat, Hb.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & H9). unfold abs_ss, setpc in H9. cbn [ss_facts] in H9.
assert (HG : facts_ok E (ss_facts psw_ssC)).
{ rewrite psw_ssC_facts. destruct G0 as [at0 cs al]. cbn [f_atoms] in Hat. subst at0. exact (psw_facts_atoms E _ cs al H9). }
assert (Hr : forall r, sv_denot E (sr_get (ss_regs psw_ssC) r) = sv_denot E (sr_get sr0 r)).
{ intros r. pose proof (all_regs_in r) as Hin.
  pose proof (proj1 (forallb_forall _ _) Hb r Hin) as Hbr. cbv beta in Hbr.
  apply orb_true_iff in Hbr as [H1 | H2].
  - rewrite (sv_eqb_eq _ _ H1). reflexivity.
  - apply andb_prop in H2 as [H2 H3]. rewrite (sv_eqb_eq _ _ H2), (sv_eqb_eq _ _ H3). symmetry. exact Hv. }
pose proof (psw_st_ok_canon E _ ms (ss_regs psw_ssC) (ss_facts psw_ssC) HS Hr HG) as H.
cbn [ss_pc ss_mem ss_resv] in H. rewrite Hpc, Hm, Hrv in H.
exact H.
Qed.
Lemma psw_aval_of_val : forall H mem a n v,
val_mem SEGS (mrestrict H mem) a n v -> aval_mem (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YG0f.le_byte, YO0f.le_byte.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma psw_val_of_aval : forall (H : word -> bool) (m : word -> option byte) a n v,
aval_mem (aview SEGS H m) a n v -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a n v Hv k Hk. pose proof (Hv k Hk) as Hb. unfold aview in Hb.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate]. cbn [option_map] in Hb.
injection Hb as Hb. f_equal. transitivity (Z_to_bv 8 (bv_unsigned b)); [symmetry; apply Z_to_bv_bv_unsigned|].
f_equal. rewrite Hb. reflexivity.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (pins_set_c.v, Section e) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis TANSWER_CODE : forall fx0 : YK11.FPState, @tanswer_code_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's hypotheses, with the A walk's names: HB, the allocator record (lib/B/YF0m.v, Record CmdBSyms); MTL,
   the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
(* the call target of every program function (lib/B/Prog/CmdObj.v cmd_sig_prog; a Theorem Labs lane's CmdRecRest.v cmd_sig_prog_PB
   at the pinned image) *)
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
(* the per-binary image facts (a Theorem Labs lane's lib/B/Prog/CmdRecBase.v cmd_img_facts): a Theorem Labs lane proves them at the pinned image
   (CmdRecImg.v cmd_img_facts_tfib, at tfibsegs); this walk is over an abstract PAImg, so it takes that lemma's
   statement at its own segments, under the lemma's name *)
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
(* the program's statics are writable at every state (the core's prog_rw, the hypothesis of a Theorem Labs lane's
   CmdRecCells.v PROG_WRITABLE) *)
Hypothesis PRW : prog_rw SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro (SK := SK) SEGS B LAWS HB IMG.
Let PROG_WRITABLE : forall (m : word -> option byte) a, inFP cmd_PG a -> writable_at SEGS m a :=
  CmdRecCells.PROG_WRITABLE SEGS B LAWS HB PRW.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (L := cmd_listing) B LAWS.
Let BR := paj_branch (PI := PI).

(* the bytes record() may write lie below alloc_ceiling *)
Lemma psw_recfp_low : forall ly S (W : world SEGS) mem md R O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> inFP (psb_recfp R O) a -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md R O a HAR HO (r & Hr & Ha). pose proof asan_consts as (C1 & _).
unfold psb_recfp in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- unfold A_G_REC, OFF_NCALLS in Ha. lia.
- destruct (psb_slot_PG S R a ltac:(unfold CALL_SIZE; lia)) as [Hs _]. unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hs. lia.
- revert Hr. destruct (Nat.ltb (length (r_calls R)) 16); intros Hr; [destruct Hr|].
  destruct (inFP_ablocks_fp_inv O a (ex_intro _ r (conj Hr Ha))) as (p & n & HpO & Hpa).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ HpO)) as (_ & H4 & Hpc & _). lia.
Qed.
(* the bytes arg_s may write: c->nargs and c->args[n] of the slot *)
Lemma psw_argfp_low : forall (S : astate) R A a, (length A < 6)%nat -> inFP (psb_argfp R A) a -> 0 <= a < alloc_ceiling.
Proof.
intros S R A a HA Hf. pose proof asan_consts as (C1 & _).
destruct (psb_slot_PG S R a (psb_argfp_PG S R A a HA Hf)) as [Hs _].
unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hs. lia.
Qed.
(* the region of the store at 0x8c9d4: based at g_rec's object atom, the 8 bytes of g_rec.state *)
Lemma psw_awr_cons_grec : forall E r rs STK sp0 O bl0 blc fr0 ly own,
YP09.r_base r = Some P_GREC -> img_env VAL A_LIM E ->
0 <= YP09.r_wlo r -> YP09.r_whi r <= REC_SIZE ->
awr_ok SEGS B E rs STK sp0 (psb_FP O) bl0 blc fr0 ly own -> awr_ok SEGS B E (r :: rs) STK sp0 (psb_FP O) bl0 blc fr0 ly own.
Proof.
intros E r rs STK sp0 O bl0 blc fr0 ly own Hb HEI Hlo Hhi H.
eapply awr_ok_cons_gen with (n := P_GREC) (b := A_G_REC); [exact Hb | | | exact H].
- rewrite (HEI P_GREC ltac:(unfold P_GREC, A_OBJ, A_TEXT, A_LIM; lia)). exact (psb_grec_val VOBJS).
- intros a Ha. assert (Ha' : A_G_REC <= a < A_G_REC + REC_SIZE) by lia.
  right; right; right; right; left. split; [exact (psb_FP_PG O a (recb_grec_in a Ha') (or_introl Ha'))|].
  split; [rewrite (ts_prog B HB); exact (recb_grec_in a Ha') | exact (cmd_prog_img a (recb_grec_in a Ha'))].
Qed.

(* the run's writes stay in the frame (the stack region's window), and a byte below alloc_ceiling is not in it *)
Local Ltac psw_awr Usp :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil].
Local Ltac psw_keep Usp :=
  let r := fresh "r" in let Hr' := fresh "Hr'" in let Hw := fresh "Hw" in
  intros (r & Hr' & Hw); vm_compute in Hr';
  repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp in Hw; lia|]);
  destruct Hr'.

(* ---- the walk -------------------------------------------------------------------------------------------- *)
Theorem tpins_set_holds : tpins_set_spec B MT.
Proof.
unfold tpins_set_spec.
intros ly S W regs mem md ch pu pf pl pv u f l verdict R O HPRE HFCSR HROD HROOK H10 Hpu64 H11 Hpf64 H12 Hpl64
  H13 Hpv64 HBu HAu HSu HLu HBf HAf HSf HLf HBl HAl HSl HLl HSV HTV HREP HFRM HEV HLIVE HMOK.
change (SRr SEGS W (cfg_at SEGS (BASE + AF_pins_set) regs mem md) (psb_post B MT ly S W regs mem md u f l verdict R O)).
pose proof pa_B_ok as HBASE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKv : PINS_SET_STK = 16608) by exact psb_stk_v.
assert (HRSv : RECORD_STK = 16560) by (vm_compute; reflexivity).
assert (HASv : ARG_S_STK = 16464) by (vm_compute; reflexivity).
assert (HMSv : MIX_CALL_STK = 4192) by (vm_compute; reflexivity).
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (psb_O_live B ly S W mem R O HREP).
destruct (psb_scalars B ly S _ R O HREP) as (Vrf & Vcd & Vst & Rrf & Rcd & Rst).
assert (Hv64 : 0 <= psb_vptr pv < 2 ^ 64) by (unfold psb_vptr; destruct (pv =? 0); lia).
(* the three heap strings at the entry, as astr_argA's block arm *)
pose proof (psb_blk_arg B ly S W mem md O pu u HAR HBu HAu HSu HLu) as HXu.
pose proof (psb_blk_arg B ly S W mem md O pf f HAR HBf HAf HSf HLf) as HXf.
pose proof (psb_blk_arg B ly S W mem md O pl l HAR HBl HAl HSl HLl) as HXl.
(* the meter's and the live bytes' parts are nonnegative *)
assert (XR0 : 0 <= XM_RECORD MT R).
{ unfold XM_RECORD, rec_spill_frees. pose proof (mo_free_nonneg MT MTL). destruct (Nat.ltb _ _); lia. }
assert (XA0 : forall v, 0 <= XM_ARG_S MT v).
{ intros v. unfold XM_ARG_S, XM_XMALLOC. apply (mo_malloc_nonneg MT MTL). unfold LIVE_XMALLOC. lia. }
assert (XN0 : forall c, 0 <= XM_ANSWER_CODE MT c).
{ intros c. unfold XM_ANSWER_CODE, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length (resp c)) + 1)) ltac:(unfold LIVE_XMALLOC; lia)). lia. }
assert (LN0 : forall c, 0 <= LIVE_ANSWER_CODE c) by (intros c; unfold LIVE_ANSWER_CODE, LIVE_HAND_BACK, LIVE_XMALLOC; lia).
assert (LA0 : forall v, 0 <= LIVE_ARG_S v) by (intros v; unfold LIVE_ARG_S, LIVE_XMALLOC; lia).
set (XMT := XM_PINS_SET MT R (Some u) (Some f) (Some l) verdict) in *.
set (LVT := LIVE_PINS_SET R (Some u) (Some f) (Some l) verdict) in *.
assert (EXMT : XMT = psb_xm4 MT u f l verdict R + XM_ANSWER_CODE MT (snd (pins_set_m R (Some u) (Some f) (Some l) verdict)))
  by (unfold XMT, XM_PINS_SET, psb_xm4, psb_dash; reflexivity).
assert (ELVT : LVT = psb_live4 u f l verdict + LIVE_ANSWER_CODE (snd (pins_set_m R (Some u) (Some f) (Some l) verdict)))
  by (unfold LVT, LIVE_PINS_SET, psb_live4, psb_dash; reflexivity).
(* the entry state: every register its own atom, the fourth string's address at atom 32, g_rec's refuse, code and
   state at atoms 33 .. 35 *)
pose proof (ajournal_init SEGS B PINS_SET_STK (psb_FP O) ly S W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs (psw_extra (psb_vptr pv) (r_refuse R) (r_code R) (r_state R)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (psw_extra (psb_vptr pv) (r_refuse R) (r_code R) (r_state R))) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. rewrite HE. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 (psb_vptr pv)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (r_refuse R mod 2 ^ 32))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (r_code R mod 2 ^ 32))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (r_state R)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok_pi SEGS VAL E psw_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_pins_set)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite HSTKv. lia.
  - apply pairwise_disjoint_of_extents. unfold stack_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split; exact I.
  - split; [|split; [exact I | exact I]]. cbn [psw_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. try change (2 ^ 4) with 16. try change (2 ^ 46) with 70368744177664. try change (2 ^ 47) with 140737488355328.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
clear HE.
unfold cfg_at. change (w64 (BASE + AF_pins_set)) with (Z_to_bv 64 (BASE + AF_pins_set)).
(* ==== 0x8c938 .. 0x8c968: the prologue, s1..s4 := the arguments, a0 := 20, the call of record ==== *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr1. rename ms into ms1.
prreg HS (10%bv : bv 5) R10. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (1%bv : bv 5) R1. prreg HS (8%bv : bv 5) R8.
assert (Esp1 : spZ (ms_regs ms1) = spZ regs + -48) by (unfold spZ at 1; rewrite R2, Usp; apply unsigned_lit_small; lia).
assert (Hkeep1 : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem ms1) a = rdW W mem a).
{ intros a Ha. apply (recb_run_keeps_m E _ (w_H W) mem (ms_mem ms1) a HFr1); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'.
  repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp in Hw; lia|]).
  destruct Hr'. }
pose proof (psb_rep_low B ly S W mem md (rdW W mem) (rdW W (ms_mem ms1)) R O HAR HREP Hkeep1) as HREP1.
(* the frame chain at the call of record: s0 is the entry s0 (class A of PASS4-REFIT.md section B): afn_pre's
   chain, kept above the entry sp by the run (it wrote only the frame below sp), at the call's sp *)
assert (Hkeep1h : forall a, spZ regs <= a < 2 ^ 64 -> rdW W (ms_mem ms1) a = rdW W mem a).
{ intros a Ha. apply (recb_run_keeps_m E _ (w_H W) mem (ms_mem ms1) a HFr1); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'.
  repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp in Hw; lia|]).
  destruct Hr'. }
assert (Hs0 : s0Z (ms_regs ms1) = s0Z regs) by (unfold s0Z; rewrite R8, (EE 8%nat 8%bv eq_refl); reflexivity).
assert (Hch1 : achain ly (rdW W (ms_mem ms1)) (spZ regs + -48) (s0Z (ms_regs ms1)) ch).
{ rewrite Hs0. apply (achain_lower ly _ (spZ regs)); [|lia].
  apply (achain_kept ly (rdW W mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia | exact Hkeep1h]. }
pmkst HS. rewrite (rca_sig_record cmd_sig_prog_PB).
eapply SRr_bind.
{ apply (psb_call_record B MT (TRECORD fx) HB cmd_img_facts_tfib ly S W regs mem md ch R O HPRE HROD HREP
    W (ms_regs ms1) (ms_mem ms1) _ 0 25660 ch HJ).
  - rewrite Esp1. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - lia.
  - reflexivity.
  - rewrite R10. reflexivity.
  - exact Hch1.
  - exact HREP1.
  - unfold EV_PINS_SET, EV_ANSWER_CODE, EV_HAND_BACK, EV_ARG_S, EV_XMALLOC in HEV. lia.
  - apply (mo_ok_le MT MTL S _ _ HMOK). rewrite EXMT. unfold psb_xm4.
    pose proof (XA0 (Some u)). pose proof (XA0 (Some f)). pose proof (XA0 (Some l)).
    pose proof (XA0 (Some (darg verdict psb_dash))). pose proof (XN0 (snd (pins_set_m R (Some u) (Some f) (Some l) verdict))). lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & F & O1 & -> & HJ2 & HJc2 & HP2 & Ha02 & Hperm2 & HlenF & HFO &
  HREP2 & HO1 & HBB2 & MLE2).
rewrite R1.
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (psw_region_kept_hi2 SEGS E (w_H W) (w_H W2) (ms_mem ms1) mem2 2 (spZ regs)); [exact Usp | |].
  - intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
    apply K9; [lia | rewrite HRSv; lia |].
    intros Hf. pose proof (psw_recfp_low ly S W mem md R O a HAR HO Hf). lia.
  - intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _).
    apply HP14. rewrite HSTKv. lia. }
clear HS R10 R2 R3 R4 R1 R8. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 36)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs (psw_extra (psb_vptr pv) (r_refuse R) (r_code R) (r_state R))) E2)
  by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
assert (E40 : ew E2 40 = getr regs2 10) by (rewrite HE2; reflexivity).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
pose proof (proj1 HJ2) as HAR2.
assert (Hslot : 0 <= rec_slot R < alloc_ceiling).
{ destruct (psb_slot_PG S R (rec_slot R) ltac:(unfold CALL_SIZE; lia)) as [Hsl _].
  unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hsl. lia. }
pose proof (psb_book_record B ly S O ly S W mem md O ly2 S2 F O1 HAR (psb_book_init B ly S O) Hperm2 HFO HO1) as HBK2.
(* ==== 0x8c96c .. 0x8c974: s0 := the slot, a1 := uri, the call of arg_s ==== *)
paj_run_shc RUNP RUNC HS HJ2.
{ psw_awr Usp2. }
clear HF HG. rename HFr into HFr2. rename ms into ms2.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3.
prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1. prreg HS (8%bv : bv 5) R8.
assert (Esp2 : spZ (ms_regs ms2) = spZ regs + -48) by (unfold spZ at 1; rewrite R2, Usp2; apply unsigned_lit_small; lia).
assert (Hkeep2 : forall a, 0 <= a < alloc_ceiling -> rdW W2 (ms_mem ms2) a = rdW W2 mem2 a).
{ intros a Ha. apply (recb_run_keeps_m E2 _ (w_H W2) mem2 (ms_mem ms2) a HFr2); [lia|]. psw_keep Usp2. }
pose proof (psb_rep_low B ly2 S2 W2 mem2 md2 (rdW W2 mem2) (rdW W2 (ms_mem ms2)) _ O1 HAR2 HREP2 Hkeep2) as HREP2'.
destruct (psb_arg_later B HB cmd_img_facts_tfib ly S W regs mem md ch R O HPRE HROD HREP ly2 S2 W2 (ms_mem ms2) _ _
  O1 pu u HJ2 HBK2 HXu) as [HSTRu HTLu].
assert (Hs08 : s0Z (ms_regs ms2) = rec_slot R) by (unfold s0Z; rewrite R8, E40, Ha02; apply unsigned_lit_small; lia).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hn2 & _).
pmkst HS. rewrite (psb_sig_arg_s cmd_sig_prog_PB).
eapply SRr_bind.
{ apply (psb_call_arg_s B MT (TARG_S fx) HB cmd_img_facts_tfib ly S W regs mem md ch R O HPRE HROD HREP
    ly2 S2 W2 (ms_regs ms2) (ms_mem ms2) _ (0 + EV_RECORD R) pu (Some u) [] O1 25672 HJ2).
  - rewrite Esp2. lia.
  - rewrite R3, OLD2 by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, OLD2 by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - lia.
  - reflexivity.
  - rewrite R10, E40. exact Ha02.
  - rewrite R11, OLD2 by lia. rewrite (EE 10%nat 10%bv eq_refl). exact H10.
  - rewrite Hs08. lia.
  - cbn. lia.
  - exact HREP2'.
  - exact HSTRu.
  - intros x Hx. injection Hx as <-. exact HTLu.
  - unfold EV_PINS_SET, EV_ANSWER_CODE, EV_HAND_BACK, EV_ARG_S, EV_XMALLOC in HEV |- *. lia.
  - rewrite ELVT in HLIVE. unfold psb_live4 in HLIVE.
    pose proof (LA0 (Some f)). pose proof (LA0 (Some l)). pose proof (LA0 (Some (darg verdict psb_dash))).
    pose proof (LN0 (snd (pins_set_m R (Some u) (Some f) (Some l) verdict))). lia.
  - apply (mok_station MT S S2 XMT (XM_RECORD MT R) _ MTL HMOK MLE2 (XA0 _)). rewrite EXMT. unfold psb_xm4.
    pose proof (XA0 (Some f)). pose proof (XA0 (Some l)).
    pose proof (XA0 (Some (darg verdict psb_dash))). pose proof (XN0 (snd (pins_set_m R (Some u) (Some f) (Some l) verdict))). lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & p1 & -> & HJ3 & HJc3 & HP3 & HBB3 & MLE3 & Hp1 & Hperm3 &
  Hfresh3 & HREP3).
rewrite R1.
jafter_call_keep_pi HS 52%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (psw_region_kept_hi2 SEGS E2 (w_H W2) (w_H W3) (ms_mem ms2) mem3 2 (spZ regs)); [exact Usp2 | |].
  - intros a Ha. pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
    apply K9; [lia | rewrite HASv; lia |].
    intros Hf. pose proof (psw_argfp_low S R [] a ltac:(cbn; lia) Hf). lia.
  - intros a Ha. pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _).
    apply HP14. rewrite HSTKv. lia. }
clear HS R10 R11 R2 R3 R4 R1 R8. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2 52 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 52)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE3 : env_agree 32 (Ereg regs (psw_extra (psb_vptr pv) (r_refuse R) (r_code R) (r_state R))) E3)
  by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).
pose proof (proj1 HJ3) as HAR3.
cbn [sarg] in Hperm3, Hfresh3, HREP3, HBB3, MLE3.
pose proof (psb_book_arg B ly S O ly2 S2 O1 ly3 S3 p1 (Z.of_nat (length u) + 1) HBK2 ltac:(lia) Hperm3 Hfresh3) as HBK3.
pose proof (mle_station MT S S2 S3 _ _ MTL MLE2 MLE3) as MLE3S.
(* ==== 0x8c978 .. 0x8c980: a0 := the slot, a1 := files, the call of arg_s ==== *)
paj_run_shc RUNP RUNC HS HJ3.
{ psw_awr Usp3. }
clear HF HG. rename HFr into HFr3. rename ms into ms3.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3.
prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1. prreg HS (8%bv : bv 5) R8.
assert (Esp3 : spZ (ms_regs ms3) = spZ regs + -48) by (unfold spZ at 1; rewrite R2, Usp3; apply unsigned_lit_small; lia).
assert (Hkeep3 : forall a, 0 <= a < alloc_ceiling -> rdW W3 (ms_mem ms3) a = rdW W3 mem3 a).
{ intros a Ha. apply (recb_run_keeps_m E3 _ (w_H W3) mem3 (ms_mem ms3) a HFr3); [lia|]. psw_keep Usp3. }
pose proof (psb_rep_low B ly3 S3 W3 mem3 md3 (rdW W3 mem3) (rdW W3 (ms_mem ms3)) _ _ HAR3 HREP3 Hkeep3) as HREP3'.
destruct (psb_arg_later B HB cmd_img_facts_tfib ly S W regs mem md ch R O HPRE HROD HREP ly3 S3 W3 (ms_mem ms3) _ _
  _ pf f HJ3 HBK3 HXf) as [HSTRf HTLf].
assert (Hs09 : s0Z (ms_regs ms3) = rec_slot R)
  by (unfold s0Z; rewrite R8, OLD3, E40, Ha02 by lia; apply unsigned_lit_small; lia).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hn3 & _).
pmkst HS. rewrite (psb_sig_arg_s cmd_sig_prog_PB).
eapply SRr_bind.
{ apply (psb_call_arg_s B MT (TARG_S fx) HB cmd_img_facts_tfib ly S W regs mem md ch R O HPRE HROD HREP
    ly3 S3 W3 (ms_regs ms3) (ms_mem ms3) _ (0 + EV_RECORD R + EV_ARG_S) pf (Some f) [u] ((p1, Z.of_nat (length u) + 1) :: O1) 25684 HJ3).
  - rewrite Esp3. lia.
  - rewrite R3, OLD3, OLD2 by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, OLD3, OLD2 by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - lia.
  - reflexivity.
  - rewrite R10, OLD3, E40 by lia. exact Ha02.
  - rewrite R11, OLD3, OLD2 by lia. rewrite (EE 11%nat 11%bv eq_refl). exact H11.
  - rewrite Hs09. lia.
  - cbn. lia.
  - exact HREP3'.
  - exact HSTRf.
  - intros x Hx. injection Hx as <-. exact HTLf.
  - unfold EV_PINS_SET, EV_ANSWER_CODE, EV_HAND_BACK, EV_ARG_S, EV_XMALLOC in HEV, Hn3 |- *. lia.
  - rewrite ELVT in HLIVE. unfold psb_live4 in HLIVE. unfold LIVE_ARG_S at 1 in HBB3. cbn [sarg] in HBB3 |- *.
    pose proof (LA0 (Some l)). pose proof (LA0 (Some (darg verdict psb_dash))).
    pose proof (LN0 (snd (pins_set_m R (Some u) (Some f) (Some l) verdict))). unfold LIVE_ARG_S in *. cbn [sarg] in *. lia.
  - apply (mok_station MT S S3 XMT _ _ MTL HMOK MLE3S (XA0 _)). rewrite EXMT. unfold psb_xm4.
    pose proof (XA0 (Some l)).
    pose proof (XA0 (Some (darg verdict psb_dash))). pose proof (XN0 (snd (pins_set_m R (Some u) (Some f) (Some l) verdict))). lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & p2 & -> & HJ4 & HJc4 & HP4 & HBB4 & MLE4 & Hp2 & Hperm4 &
  Hfresh4 & HREP4).
rewrite R1.
jafter_call_keep_pi HS 68%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (psw_region_kept_hi2 SEGS E3 (w_H W3) (w_H W4) (ms_mem ms3) mem4 2 (spZ regs)); [exact Usp3 | |].
  - intros a Ha. pose proof HJc4 as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
    apply K9; [lia | rewrite HASv; lia |].
    intros Hf. pose proof (psw_argfp_low S R [u] a ltac:(cbn; lia) Hf). lia.
  - intros a Ha. pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _).
    apply HP14. rewrite HSTKv. lia. }
clear HS R10 R11 R2 R3 R4 R1 R8. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E3 68 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall n, (n < 68)%nat -> ew E4 n = ew E3 n) by (intros n Hn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE4 : env_agree 32 (Ereg regs (psw_extra (psb_vptr pv) (r_refuse R) (r_code R) (r_state R))) E4)
  by (rewrite HE4; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
clear HE4.
assert (Usp4 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact Usp3).
pose proof (proj1 HJ4) as HAR4.
cbn [sarg] in Hperm4, Hfresh4, HREP4, HBB4, MLE4.
pose proof (psb_book_arg B ly S O ly3 S3 _ ly4 S4 p2 (Z.of_nat (length f) + 1) HBK3 ltac:(lia) Hperm4 Hfresh4) as HBK4.
pose proof (mle_station MT S S3 S4 _ _ MTL MLE3S MLE4) as MLE4S.
(* ==== 0x8c984 .. 0x8c98c: a0 := the slot, a1 := layout, the call of arg_s ==== *)
paj_run_shc RUNP RUNC HS HJ4.
{ psw_awr Usp4. }
clear HF HG. rename HFr into HFr4. rename ms into ms4.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3.
prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1. prreg HS (8%bv : bv 5) R8.
assert (Esp4 : spZ (ms_regs ms4) = spZ regs + -48) by (unfold spZ at 1; rewrite R2, Usp4; apply unsigned_lit_small; lia).
assert (Hkeep4 : forall a, 0 <= a < alloc_ceiling -> rdW W4 (ms_mem ms4) a = rdW W4 mem4 a).
{ intros a Ha. apply (recb_run_keeps_m E4 _ (w_H W4) mem4 (ms_mem ms4) a HFr4); [lia|]. psw_keep Usp4. }
pose proof (psb_rep_low B ly4 S4 W4 mem4 md4 (rdW W4 mem4) (rdW W4 (ms_mem ms4)) _ _ HAR4 HREP4 Hkeep4) as HREP4'.
destruct (psb_arg_later B HB cmd_img_facts_tfib ly S W regs mem md ch R O HPRE HROD HREP ly4 S4 W4 (ms_mem ms4) _ _
  _ pl l HJ4 HBK4 HXl) as [HSTRl HTLl].
assert (Hs0a : s0Z (ms_regs ms4) = rec_slot R)
  by (unfold s0Z; rewrite R8, OLD4, OLD3, E40, Ha02 by lia; apply unsigned_lit_small; lia).
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hn4 & _).
pmkst HS. rewrite (psb_sig_arg_s cmd_sig_prog_PB).
eapply SRr_bind.
{ apply (psb_call_arg_s B MT (TARG_S fx) HB cmd_img_facts_tfib ly S W regs mem md ch R O HPRE HROD HREP
    ly4 S4 W4 (ms_regs ms4) (ms_mem ms4) _ (0 + EV_RECORD R + EV_ARG_S + EV_ARG_S) pl (Some l) [u; f]
    ((p2, Z.of_nat (length f) + 1) :: (p1, Z.of_nat (length u) + 1) :: O1) 25696 HJ4).
  - rewrite Esp4. lia.
  - rewrite R3, OLD4, OLD3, OLD2 by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, OLD4, OLD3, OLD2 by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - lia.
  - reflexivity.
  - rewrite R10, OLD4, OLD3, E40 by lia. exact Ha02.
  - rewrite R11, OLD4, OLD3, OLD2 by lia. rewrite (EE 12%nat 12%bv eq_refl). exact H12.
  - rewrite Hs0a. lia.
  - cbn. lia.
  - exact HREP4'.
  - exact HSTRl.
  - intros x Hx. injection Hx as <-. exact HTLl.
  - unfold EV_PINS_SET, EV_ANSWER_CODE, EV_HAND_BACK, EV_ARG_S, EV_XMALLOC in HEV, Hn4 |- *. lia.
  - rewrite ELVT in HLIVE. unfold psb_live4 in HLIVE. unfold LIVE_ARG_S in HBB3, HBB4 |- *. cbn [sarg] in *.
    pose proof (LA0 (Some (darg verdict psb_dash))). unfold LIVE_ARG_S in *. cbn [sarg] in *.
    pose proof (LN0 (snd (pins_set_m R (Some u) (Some f) (Some l) verdict))). lia.
  - apply (mok_station MT S S4 XMT _ _ MTL HMOK MLE4S (XA0 _)). rewrite EXMT. unfold psb_xm4.
    pose proof (XA0 (Some (darg verdict psb_dash))). pose proof (XN0 (snd (pins_set_m R (Some u) (Some f) (Some l) verdict))). lia. }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & p3 & -> & HJ5 & HJc5 & HP5 & HBB5 & MLE5 & Hp3 & Hperm5 &
  Hfresh5 & HREP5).
rewrite R1.
jafter_call_keep_pi HS 84%nat regs5 (mrestrict (w_H W5) mem5) HP5 [0]%nat HS5.
match type of HS5 with ?t -> _ => assert (HRK : t); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (psw_region_kept_hi2 SEGS E4 (w_H W4) (w_H W5) (ms_mem ms4) mem5 2 (spZ regs)); [exact Usp4 | |].
  - intros a Ha. pose proof HJc5 as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
    apply K9; [lia | rewrite HASv; lia |].
    intros Hf. pose proof (psw_argfp_low S R [u; f] a ltac:(cbn; lia) Hf). lia.
  - intros a Ha. pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _).
    apply HP14. rewrite HSTKv. lia. }
clear HS R10 R11 R2 R3 R4 R1 R8. rewrite <- restrict_mkst_fx in HS5. rename HS5 into HS.
remember (havoc E4 84 (map (getr regs5) CLOB)) as E5 eqn:HE5 in HS.
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc; [exact HEI4 | cbv; lia]).
assert (OLD5 : forall n, (n < 84)%nat -> ew E5 n = ew E4 n) by (intros n Hn; rewrite HE5; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE5 : env_agree 32 (Ereg regs (psw_extra (psb_vptr pv) (r_refuse R) (r_code R) (r_state R))) E5)
  by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE4]).
clear HE5.
assert (Usp5 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lia; exact Usp4).
pose proof (proj1 HJ5) as HAR5.
cbn [sarg] in Hperm5, Hfresh5, HREP5, HBB5, MLE5.
pose proof (psb_book_arg B ly S O ly4 S4 _ ly5 S5 p3 (Z.of_nat (length l) + 1) HBK4 ltac:(lia) Hperm5 Hfresh5) as HBK5.
pose proof (mle_station MT S S4 S5 _ _ MTL MLE4S MLE5) as MLE5S.
set (O4 := (p3, Z.of_nat (length l) + 1) :: (p2, Z.of_nat (length f) + 1) :: (p1, Z.of_nat (length u) + 1) :: O1) in *.
(* ==== 0x8c990: the branch on the verdict pointer; the arms meet at the fourth call of arg_s (0x8c9a4) ==== *)
paj_run_shc RUNP RUNC HS HJ5.
{ psw_awr Usp5. }
clear HF HG. rename HFr into HFr5. rename ms into ms5.
assert (Hkeep5 : forall a, 0 <= a < alloc_ceiling -> rdW W5 (ms_mem ms5) a = rdW W5 mem5 a).
{ intros a Ha. apply (recb_run_keeps_m E5 _ (w_H W5) mem5 (ms_mem ms5) a HFr5); [lia|]. psw_keep Usp5. }
lazymatch goal with |- SRr _ _ _ ?Q =>
enough (CONT : forall msX mdX, st_ok_pi SEGS VAL E5 psw_ssC (restrict (w_H W5) msX) ->
  psb_J B ly S W regs mem md O ly5 S5 W5 (ms_mem msX) mdX (0 + EV_RECORD R + EV_ARG_S + EV_ARG_S + EV_ARG_S) ->
  (forall a, 0 <= a < alloc_ceiling -> rdW W5 (ms_mem msX) a = rdW W5 mem5 a) ->
  SRr SEGS W5 (mkCfg msX mdX) Q) end.
{ assert (E13 : ew E5 13 = Z_to_bv 64 pv) by (rewrite OLD5, OLD4, OLD3, OLD2 by lia; rewrite (EE 13%nat 13%bv eq_refl); exact H13).
  assert (U13 : U E5 (SOff 13 0) = pv).
  { unfold U. cbn [sv_denot]. rewrite E13, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia. }
  psrr_branch_pi RUNP BR HS.
  - (* the verdict is not NULL: s1 = pv *)
    rewrite branch_ne_U, U13 in Hc. change (U E5 (SLit 0)) with 0 in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_sh RUNTOP HS HJ5 PS_ARG4.
    { psw_awr Usp5. }
    assert (Hv : sv_denot E5 (SOff 13 0) = sv_denot E5 (SOff P_V 0)).
    { cbn [sv_denot]. change P_V with 32%nat. rewrite E13, (OLD5 32%nat ltac:(lia)), (OLD4 32%nat ltac:(lia)),
        (OLD3 32%nat ltac:(lia)), (OLD2 32%nat ltac:(lia)), E32.
      unfold psb_vptr. rewrite (proj2 (Z.eqb_neq pv 0) Hc). reflexivity. }
    pose proof (psw_canon_ok E5 _ _ (SOff 13 0) HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hv) as HSC.
    apply (CONT _ _ HSC HJ5). intros a Ha. rewrite <- (Hkeep5 a Ha).
    apply (recb_run_keeps_m E5 _ (w_H W5) (ms_mem ms5) (ms_mem ms) a HFr); [lia|]. psw_keep Usp5.
  - (* the verdict is NULL: s1 = "-" (0x21d80) *)
    rewrite branch_ne_U, U13 in Hc. change (U E5 (SLit 0)) with 0 in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_sh RUNTOP HS HJ5 PS_ARG4.
    { psw_awr Usp5. }
    assert (Hv : sv_denot E5 (SOff P_DASH 0) = sv_denot E5 (SOff P_V 0)).
    { cbn [sv_denot]. change P_V with 32%nat. rewrite (OLD5 32%nat ltac:(lia)), (OLD4 32%nat ltac:(lia)),
        (OLD3 32%nat ltac:(lia)), (OLD2 32%nat ltac:(lia)), E32.
      rewrite (img_env_atomP E5 P_DASH HEI5 ltac:(unfold P_DASH, A_OBJ, A_TEXT, A_LIM; lia)).
      change P_DASH with (A_OBJ 52). rewrite (psb_dash_val VOBJS). unfold psb_vptr. rewrite Hc. reflexivity. }
    pose proof (psw_canon_ok E5 _ _ (SOff P_DASH 0) HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hv) as HSC.
    apply (CONT _ _ HSC HJ5). intros a Ha. rewrite <- (Hkeep5 a Ha).
    apply (recb_run_keeps_m E5 _ (w_H W5) (ms_mem ms5) (ms_mem ms) a HFr); [lia|]. psw_keep Usp5. }
clear HS. intros msX mdX HSX HJX HKX.
(* ==== 0x8c99c .. 0x8c9a4: a0 := the slot, a1 := the string, the fourth call of arg_s ==== *)
paj_run_shc RUNP RUNC HSX HJX.
{ psw_awr Usp5. }
clear HF HG. rename HFr into HFr6. rename ms into ms6.
prreg HSX (10%bv : bv 5) R10. prreg HSX (11%bv : bv 5) R11. prreg HSX (2%bv : bv 5) R2. prreg HSX (3%bv : bv 5) R3.
prreg HSX (4%bv : bv 5) R4. prreg HSX (1%bv : bv 5) R1. prreg HSX (8%bv : bv 5) R8.
assert (Esp6 : spZ (ms_regs ms6) = spZ regs + -48) by (unfold spZ at 1; rewrite R2, Usp5; apply unsigned_lit_small; lia).
assert (Hkeep6 : forall a, 0 <= a < alloc_ceiling -> rdW W5 (ms_mem ms6) a = rdW W5 mem5 a).
{ intros a Ha. rewrite <- (HKX a Ha). apply (recb_run_keeps_m E5 _ (w_H W5) (ms_mem msX) (ms_mem ms6) a HFr6); [lia|].
  psw_keep Usp5. }
pose proof (psb_rep_low B ly5 S5 W5 mem5 md5 (rdW W5 mem5) (rdW W5 (ms_mem ms6)) _ _ HAR5 HREP5 Hkeep6) as HREP5'.
destruct (psb_v4_later B HB cmd_img_facts_tfib ly S W regs mem md ch pv verdict R O HPRE HROD HSV HREP
  ly5 S5 W5 (ms_mem ms6) _ _ O4 HJX HBK5) as [HSTRv HTLv].
assert (Hs0b : s0Z (ms_regs ms6) = rec_slot R)
  by (unfold s0Z; rewrite R8, OLD5, OLD4, OLD3, E40, Ha02 by lia; apply unsigned_lit_small; lia).
pose proof HJX as (_ & _ & _ & _ & _ & _ & Hn5 & _).
pmkst HSX. rewrite (psb_sig_arg_s cmd_sig_prog_PB).
eapply SRr_bind.
{ apply (psb_call_arg_s B MT (TARG_S fx) HB cmd_img_facts_tfib ly S W regs mem md ch R O HPRE HROD HREP
    ly5 S5 W5 (ms_regs ms6) (ms_mem ms6) _ (0 + EV_RECORD R + EV_ARG_S + EV_ARG_S + EV_ARG_S) (psb_vptr pv)
    (Some (darg verdict psb_dash)) [u; f; l] O4 25720 HJX).
  - rewrite Esp6. lia.
  - rewrite R3, OLD5, OLD4, OLD3, OLD2 by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, OLD5, OLD4, OLD3, OLD2 by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - lia.
  - reflexivity.
  - rewrite R10, OLD5, OLD4, OLD3, E40 by lia. exact Ha02.
  - rewrite R11. change P_V with 32%nat. rewrite OLD5, OLD4, OLD3, OLD2 by lia. exact E32.
  - rewrite Hs0b. lia.
  - cbn. lia.
  - exact HREP5'.
  - exact HSTRv.
  - intros x Hx. injection Hx as <-. exact HTLv.
  - unfold EV_PINS_SET, EV_ANSWER_CODE, EV_HAND_BACK, EV_ARG_S, EV_XMALLOC in HEV, Hn5 |- *. lia.
  - rewrite ELVT in HLIVE. unfold psb_live4, LIVE_ARG_S in HLIVE. unfold LIVE_ARG_S in HBB3, HBB4, HBB5 |- *.
    cbn [sarg] in HLIVE, HBB3, HBB4, HBB5 |- *.
    pose proof (LN0 (snd (pins_set_m R (Some u) (Some f) (Some l) verdict))). lia.
  - apply (mok_station MT S S5 XMT _ _ MTL HMOK MLE5S (XA0 _)). rewrite EXMT. unfold psb_xm4.
    pose proof (XN0 (snd (pins_set_m R (Some u) (Some f) (Some l) verdict))). lia. }
cbv beta. intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & p4 & -> & HJ6 & HJc6 & HP6 & HBB6 & MLE6 & Hp4 & Hperm6 &
  Hfresh6 & HREP6).
rewrite R1.
jafter_call_keep_pi HSX 100%nat regs6 (mrestrict (w_H W6) mem6) HP6 [0]%nat HS6.
match type of HS6 with ?t -> _ => assert (HRK : t); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (psw_region_kept_hi2 SEGS E5 (w_H W5) (w_H W6) (ms_mem ms6) mem6 2 (spZ regs)); [exact Usp5 | |].
  - intros a Ha. pose proof HJc6 as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
    apply K9; [lia | rewrite HASv; lia |].
    intros Hf. pose proof (psw_argfp_low S R [u; f; l] a ltac:(cbn; lia) Hf). lia.
  - intros a Ha. pose proof HJ6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _).
    apply HP14. rewrite HSTKv. lia. }
clear HSX R10 R11 R2 R3 R4 R1 R8. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
remember (havoc E5 100 (map (getr regs6) CLOB)) as E6 eqn:HE6 in HS.
assert (HEI6 : img_env VAL A_LIM E6) by (rewrite HE6; apply img_env_havoc; [exact HEI5 | cbv; lia]).
assert (OLD6 : forall n, (n < 100)%nat -> ew E6 n = ew E5 n) by (intros n Hn; rewrite HE6; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE6 : env_agree 32 (Ereg regs (psw_extra (psb_vptr pv) (r_refuse R) (r_code R) (r_state R))) E6)
  by (rewrite HE6; apply env_agree_havoc_ge; [cbv; lia | exact HAE5]).
clear HE6.
assert (Usp6 : bv_unsigned (ew E6 2) = spZ regs) by (rewrite OLD6 by lia; exact Usp5).
pose proof (proj1 HJ6) as HAR6.
cbn [sarg] in Hperm6, Hfresh6, HREP6, HBB6, MLE6.
rewrite psw_A4 in HREP6.
pose proof (psb_book_arg B ly S O ly5 S5 _ ly6 S6 p4 (Z.of_nat (length (darg verdict psb_dash)) + 1) HBK5 ltac:(lia)
  Hperm6 Hfresh6) as HBK6.
pose proof (mle_station MT S S5 S6 _ _ MTL MLE5S MLE6) as MLE6S.
set (O5 := (p4, Z.of_nat (length (darg verdict psb_dash)) + 1) :: O4) in *.
set (RA := rec_record R REC_PINS_SET (psb_A (Some u) (Some f) (Some l) verdict)) in *.
(* g_rec's refuse, code and state at this state: the recorder's scalars, as the loads at 0x8c9b0 / 0x8c9b8 / 0x8c9c0
   read them *)
destruct (psb_scalars B ly6 S6 _ RA O5 HREP6) as (Vrf6 & Vcd6 & Vst6 & Rrf6 & Rcd6 & Rst6).
destruct (psb_rec_record_scalars R REC_PINS_SET (psb_A (Some u) (Some f) (Some l) verdict)) as (Erf & Ecd & Est & _).
fold RA in Erf, Ecd, Est. rewrite Erf in Vrf6, Rrf6. rewrite Ecd in Vcd6, Rcd6. rewrite Est in Vst6, Rst6.
assert (UG6 : bv_unsigned (ew E6 P_GREC) = A_G_REC)
  by (rewrite (HEI6 P_GREC ltac:(unfold P_GREC, A_OBJ, A_TEXT, A_LIM; lia)); exact (psb_grec_val VOBJS)).
(* the region of g_rec for the three loads *)
pose proof (st_ok_pi_add_region E6 _ _ psw_grec_region HS eq_refl) as HSG.
match type of HSG with ?t -> _ => assert (HRK : t); [|specialize (HSG HRK); clear HRK] end.
{ unfold region_ok, psw_grec_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem mkst].
  rewrite UG6. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E6 _ A_G_REC 0 4 (SOff P_RF 0) (r_refuse R mod 2 ^ 32)).
    + cbn [sv_denot]. change P_RF with 33%nat. rewrite OLD6, OLD5, OLD4, OLD3, OLD2 by lia. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + pose proof (Z.mod_pos_bound (r_refuse R) (2 ^ 32) ltac:(lia)). zside.
    + zside.
    + apply psw_val_of_aval. exact (psb_aval_mod _ _ _ _ Vrf6).
  - apply (chunk_ok_val SEGS E6 _ A_G_REC 4 4 (SOff P_CD 0) (r_code R mod 2 ^ 32)).
    + cbn [sv_denot]. change P_CD with 34%nat. rewrite OLD6, OLD5, OLD4, OLD3, OLD2 by lia. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + pose proof (Z.mod_pos_bound (r_code R) (2 ^ 32) ltac:(lia)). zside.
    + zside.
    + apply psw_val_of_aval. change (A_G_REC + 4) with (A_G_REC + OFF_CODE).
      exact (psb_aval_mod _ _ _ _ Vcd6).
  - apply (chunk_ok_val SEGS E6 _ A_G_REC 0x3b0 8 (SOff P_ST 0) (r_state R)).
    + cbn [sv_denot]. change P_ST with 35%nat. rewrite OLD6, OLD5, OLD4, OLD3, OLD2 by lia. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + zside.
    + zside.
    + apply psw_val_of_aval. change (A_G_REC + 0x3b0) with (A_G_REC + OFF_STATE). exact Vst6. }
match type of HSG with ?t -> _ => assert (HRK : t); [|specialize (HSG HRK); clear HRK] end.
{ cbn [all_disjoint ss_mem]. split; [|exact I]. unfold extent_disjoint, psw_grec_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UG6, Usp6. unfold A_G_REC. lia. }
lazymatch type of HSG with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HSG end.
clear HS. rename HSG into HS.
(* ==== 0x8c9a8 .. 0x8c9b4: s1 := g_rec, a0 := g_rec.refuse, the branch on it ==== *)
paj_run_shc RUNP RUNC HS HJ6.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack; [reflexivity | exact Usp6 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr7. rename ms into ms7.
assert (Hkeep7 : forall a, 0 <= a < alloc_ceiling -> rdW W6 (ms_mem ms7) a = rdW W6 mem6 a).
{ intros a Ha. apply (recb_run_keeps_m E6 _ (w_H W6) mem6 (ms_mem ms7) a HFr7); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'.
  repeat (destruct Hr' as [Hr' | Hr'];
    [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp6, ?UG6 in Hw; lia|]).
  destruct Hr'. }
assert (HSXT : sv_denot E6 (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (r_refuse R)).
{ apply psw_sext_atom; [|lia]. rewrite OLD6, OLD5, OLD4, OLD3, OLD2 by lia. exact E33. }
assert (HSXC : sext 64 (bv_extract 0 32 (ew E6 34)) = Z_to_bv 64 (r_code R)).
{ apply psw_sext_ew; [|lia]. rewrite OLD6, OLD5, OLD4, OLD3, OLD2 by lia. exact E34. }
(* the branch's condition is the recorder's refuse field *)
assert (HRZ : (r_refuse R mod 2 ^ 64 =? 0) = (r_refuse R =? 0)).
{ destruct (Z.eqb_spec (r_refuse R) 0) as [E0 | Hne]; [rewrite E0; reflexivity|].
  apply Z.eqb_neq. intros Hm. apply Hne. revert Hm. Z.div_mod_to_equations. lia. }
assert (HUR : U E6 (SExt true 32 (SOff 33 0)) = r_refuse R mod 2 ^ 64).
{ unfold U. rewrite HSXT, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity. }
(* the facts psb_tail needs of the state at the tail jump, in either arm *)
assert (HEVT : 0 + EV_RECORD R + EV_ARG_S + EV_ARG_S + EV_ARG_S + EV_ARG_S + EV_ANSWER_CODE <= EV_PINS_SET R)
  by (unfold EV_PINS_SET; lia).
assert (HBBT : blocks_bytes S6 <= blocks_bytes S + psb_live4 u f l verdict).
{ unfold psb_live4, LIVE_ARG_S in *. cbn [sarg] in *. lia. }
assert (HMLET : mo_le MT S S6 (psb_xm4 MT u f l verdict R))
  by (apply (mle_weaken MT S S6 _ _ MTL MLE6S); unfold psb_xm4; lia).
psrr_branch_pi RUNP BR HS.
- (* ---- g_rec.refuse = 0: mix_call folds the call into g_rec.state ---- *)
  rewrite branch_eq_U, HUR in Hc. change (U E6 (SLit 0)) with 0 in Hc. rewrite HRZ in Hc.
  apply Z.eqb_eq in Hc.
  (* 0x8c9c0 .. 0x8c9c8: a0 := g_rec.state, a1 := the slot, the call of mix_call *)
  paj_run_shc RUNP RUNC HS HJ6.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_stack; [reflexivity | exact Usp6 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
  clear HF HG. rename HFr into HFr8. rename ms into ms8.
  prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3.
  prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
  assert (Esp8 : spZ (ms_regs ms8) = spZ regs + -48) by (unfold spZ at 1; rewrite R2, Usp6; apply unsigned_lit_small; lia).
  assert (Hkeep8 : forall a, 0 <= a < alloc_ceiling -> rdW W6 (ms_mem ms8) a = rdW W6 mem6 a).
  { intros a Ha. rewrite <- (Hkeep7 a Ha).
    apply (recb_run_keeps_m E6 _ (w_H W6) (ms_mem ms7) (ms_mem ms8) a HFr8); [lia|].
    intros (r & Hr' & Hw). vm_compute in Hr'.
    repeat (destruct Hr' as [Hr' | Hr'];
      [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp6, ?UG6 in Hw; lia|]).
    destruct Hr'. }
  pose proof (psb_rep_low B ly6 S6 W6 mem6 md6 (rdW W6 mem6) (rdW W6 (ms_mem ms8)) _ _ HAR6 HREP6 Hkeep8) as HREP6m.
  pose proof HJ6 as (_ & _ & _ & _ & _ & _ & Hn6 & _).
  pmkst HS. rewrite (psb_sig_mix_call cmd_sig_prog_PB).
  eapply SRr_bind.
  { apply (psb_call_mix B MT (TMIX_CALL fx) HB cmd_img_facts_tfib ly S W regs mem md ch R O HPRE HROD HREP
      ly6 S6 W6 (ms_regs ms8) (ms_mem ms8) _ (0 + EV_RECORD R + EV_ARG_S + EV_ARG_S + EV_ARG_S + EV_ARG_S)
      (psb_A (Some u) (Some f) (Some l) verdict) O5 25756 HJ6).
    - rewrite Esp8. lia.
    - rewrite R3, OLD6, OLD5, OLD4, OLD3, OLD2 by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite R4, OLD6, OLD5, OLD4, OLD3, OLD2 by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact R1.
    - lia.
    - reflexivity.
    - rewrite R10. change P_ST with 35%nat. rewrite OLD6, OLD5, OLD4, OLD3, OLD2 by lia. exact E35.
    - rewrite R11, OLD6, OLD5, OLD4, OLD3, E40 by lia. exact Ha02.
    - exact HREP6m.
    - unfold EV_MIX_CALL. unfold EV_PINS_SET, EV_ANSWER_CODE, EV_HAND_BACK, EV_ARG_S, EV_XMALLOC in HEV, Hn6. lia. }
  cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HJc7 & HP7 & Hm10 & Ely7 & ES7).
  rewrite R1.
  jafter_call_keep_pi HS 116%nat regs7 (mrestrict (w_H W7) mem7) HP7 [1]%nat HS7.
  match type of HS7 with ?t -> _ => assert (HRK : t); [|specialize (HS7 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
    eapply (psw_region_kept_hi2 SEGS E6 (w_H W6) (w_H W7) (ms_mem ms8) mem7 2 (spZ regs)); [exact Usp6 | |].
    - intros a Ha. pose proof HJc7 as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
      apply K9; [lia | rewrite HMSv; lia | apply inFP_nil].
    - intros a Ha. pose proof HJ7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _).
      apply HP14. rewrite HSTKv. lia. }
  clear HS R10 R11 R2 R3 R4 R1. rewrite <- restrict_mkst_fx in HS7. rename HS7 into HS.
  remember (havoc E6 116 (map (getr regs7) CLOB)) as E7 eqn:HE7 in HS.
  assert (HEI7 : img_env VAL A_LIM E7) by (rewrite HE7; apply img_env_havoc; [exact HEI6 | cbv; lia]).
  assert (OLD7 : forall n, (n < 116)%nat -> ew E7 n = ew E6 n) by (intros n Hn; rewrite HE7; apply YN3v.ew_havoc_old; exact Hn).
  assert (HAE7 : env_agree 32 (Ereg regs (psw_extra (psb_vptr pv) (r_refuse R) (r_code R) (r_state R))) E7)
    by (rewrite HE7; apply env_agree_havoc_ge; [cbv; lia | exact HAE6]).
  assert (E120 : ew E7 120 = getr regs7 10) by (rewrite HE7; reflexivity).
  clear HE7.
  assert (Usp7 : bv_unsigned (ew E7 2) = spZ regs) by (rewrite OLD7 by lia; exact Usp6).
  assert (UG7 : bv_unsigned (ew E7 P_GREC) = A_G_REC)
    by (rewrite (HEI7 P_GREC ltac:(unfold P_GREC, A_OBJ, A_TEXT, A_LIM; lia)); exact (psb_grec_val VOBJS)).
  subst ly7 S7.
  (* the region of the store at 0x8c9d4: g_rec.state, writable because it is a program static *)
  pose proof (st_ok_pi_add_region E7 _ _ psw_store_region HS eq_refl) as HSG.
  match type of HSG with ?t -> _ => assert (HRK : t); [|specialize (HSG HRK); clear HRK] end.
  { unfold region_ok, psw_store_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem mkst].
    rewrite UG7. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [|constructor].
    intros o Ho. apply PROG_WRITABLE. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|].
    cbn [fst snd]. unfold A_G_REC. lia. }
  match type of HSG with ?t -> _ => assert (HRK : t); [|specialize (HSG HRK); clear HRK] end.
  { cbn [all_disjoint ss_mem]. split; [|exact I]. unfold extent_disjoint, psw_store_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UG7, Usp7. unfold A_G_REC. lia. }
  lazymatch type of HSG with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HSG end.
  clear HS. rename HSG into HS.
  (* 0x8c9cc .. 0x8c9f4: g_rec.state := the digest, a0 := 0, the epilogue, the tail jump *)
  paj_run_shc RUNP RUNC HS HJ7.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply psw_awr_cons_grec; [reflexivity | exact HEI7 | cbn; lia | cbn [YP09.r_whi]; unfold REC_SIZE; lia |].
    eapply awr_ok_cons_stack; [reflexivity | exact Usp7 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
  clear HF HG. rename HFr into HFr9. rename ms into ms9.
  prreg HS (1%bv : bv 5) Rf1. prreg HS (2%bv : bv 5) Rf2. prreg HS (10%bv : bv 5) Rf10.
  (* the word the store put in g_rec.state *)
  pose proof (st_ok_region_nth E7 _ _ 0%nat _ HS eq_refl) as HRf. cbn [ms_mem restrict] in HRf.
  pose proof (field_of_region_any E7 _ P_GREC A_G_REC _ _ _ _ _ 944 8 (SOff 120 0) HRf UG7 ltac:(cbn; tauto)
    ltac:(cbn; lia)) as Fst.
  set (h := mixcall (r_state R) REC_PINS_SET (psb_A (Some u) (Some f) (Some l) verdict)) in *.
  assert (Hh64 : 0 <= h < 2 ^ 64) by (unfold h; apply mixcall_range; lia).
  assert (D120 : bv_unsigned (sv_denot E7 (SOff 120 0)) mod 2 ^ (8 * Z.of_N 8) = h).
  { cbn [sv_denot]. rewrite E120, Hm10, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned, unsigned_lit_small by lia.
    apply Z.mod_small. change (8 * Z.of_N 8) with 64. exact Hh64. }
  rewrite D120 in Fst. change (A_G_REC + 944) with (A_G_REC + OFF_STATE) in Fst.
  (* the bytes the last run and mix_call kept *)
  assert (UG7' : bv_unsigned (ew E7 285) = A_G_REC) by exact UG7.
  assert (K9 : forall a, 0 <= a < alloc_ceiling -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
    rdW W7 (ms_mem ms9) a = rdW W7 mem7 a).
  { intros a Ha Hns. apply (recb_run_keeps_m E7 _ (w_H W7) mem7 (ms_mem ms9) a HFr9); [lia|].
    intros (r & Hr' & Hw). vm_compute in Hr'.
    repeat (destruct Hr' as [Hr' | Hr'];
      [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp7, ?UG7' in Hw;
       unfold A_G_REC, OFF_STATE in Hw, Hns; lia|]).
    destruct Hr'. }
  assert (HREPF : rec_repA B ly6 S6 (rdW W7 (ms_mem ms9)) (set_state (rec_record R REC_PINS_SET
    (psb_A (Some u) (Some f) (Some l) verdict)) h) O5).
  { pose proof (psb_rep_call_kept B HB cmd_img_facts_tfib ly6 S6 W6 (ms_mem ms8) _ ly6 S6 W7 mem7 _ _ _ _ _ _
      (proj1 HJ6) HJc7 ltac:(intros pn Hpn; exact Hpn) HREP6m) as HREP7.
    apply (psb_rep_set_low B ly6 S6 W7 (ms_mem ms9) _ (rdW W7 mem7) _ _ _ h (proj1 HJ7) HREP7).
    - intros a Ha Hns. exact (K9 a Ha Hns).
    - exact (psw_aval_of_val (w_H W7) (ms_mem ms9) _ _ _ Fst).
    - exact Hh64. }
  pmkst HS. rewrite (psb_sig_answer_code cmd_sig_prog_PB).
  apply (psb_tail B MT (TANSWER_CODE fx) MTL HB cmd_img_facts_tfib ly S W regs mem md ch u f l verdict R O
    HPRE HFCSR HROD HREP HFRM HEV HLIVE HMOK ly6 S6 W7 (ms_mem ms9) _
    (0 + EV_RECORD R + EV_ARG_S + EV_ARG_S + EV_ARG_S + EV_ARG_S + EV_MIX_CALL) (ms_regs ms9) (set_state (rec_record R REC_PINS_SET (psb_A (Some u) (Some f) (Some l) verdict)) h) O5 0 HJ7).
  + unfold spZ at 1. rewrite Rf2, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2 by lia. rewrite (EE 2%nat 2%bv eq_refl). reflexivity.
  + rewrite Rf1, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2 by lia. exact (EE 1%nat 1%bv eq_refl).
  + exact (aregs_preserved_of_st_ok SEGS (w_H W7) E7 _ ms9 regs (psw_extra (psb_vptr pv) (r_refuse R) (r_code R) (r_state R))
      HS HAE7 ltac:(vm_compute; reflexivity)).
  + rewrite Rf10. reflexivity.
  + lia.
  + exact HREPF.
  + exact HBK6.
  + rewrite (psb_model_mix R (Some u) (Some f) (Some l) verdict Hc). unfold rec_mix. cbn [fst snd].
    rewrite (proj1 (proj2 (proj2 (psb_rec_record_scalars R REC_PINS_SET (psb_A (Some u) (Some f) (Some l) verdict))))).
    reflexivity.
  + unfold EV_MIX_CALL. lia.
  + exact HBBT.
  + exact HMLET.
- (* ---- g_rec.refuse <> 0: the code it holds answers ---- *)
  rewrite branch_eq_U, HUR in Hc. change (U E6 (SLit 0)) with 0 in Hc. rewrite HRZ in Hc.
  apply Z.eqb_neq in Hc.
  (* 0x8c9b8 .. 0x8c9f4: a0 := g_rec.code, the epilogue, the tail jump *)
  paj_run_shc RUNP RUNC HS HJ6.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_stack; [reflexivity | exact Usp6 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
  clear HF HG. rename HFr into HFr8. rename ms into ms8.
  prreg HS (1%bv : bv 5) Rf1. prreg HS (2%bv : bv 5) Rf2. prreg HS (10%bv : bv 5) Rf10.
  assert (K8 : forall a, 0 <= a < alloc_ceiling -> rdW W6 (ms_mem ms8) a = rdW W6 mem6 a).
  { intros a Ha. rewrite <- (Hkeep7 a Ha).
    apply (recb_run_keeps_m E6 _ (w_H W6) (ms_mem ms7) (ms_mem ms8) a HFr8); [lia|].
    intros (r & Hr' & Hw). vm_compute in Hr'.
    repeat (destruct Hr' as [Hr' | Hr'];
      [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp6, ?UG6 in Hw; lia|]).
    destruct Hr'. }
  pose proof (psb_rep_low B ly6 S6 W6 mem6 md6 (rdW W6 mem6) (rdW W6 (ms_mem ms8)) _ _ HAR6 HREP6 K8) as HREPF.
  pmkst HS. rewrite (psb_sig_answer_code cmd_sig_prog_PB).
  apply (psb_tail B MT (TANSWER_CODE fx) MTL HB cmd_img_facts_tfib ly S W regs mem md ch u f l verdict R O
    HPRE HFCSR HROD HREP HFRM HEV HLIVE HMOK ly6 S6 W6 (ms_mem ms8) _
    (0 + EV_RECORD R + EV_ARG_S + EV_ARG_S + EV_ARG_S + EV_ARG_S) (ms_regs ms8) (rec_record R REC_PINS_SET (psb_A (Some u) (Some f) (Some l) verdict)) O5 (r_code R) HJ6).
  + unfold spZ at 1. rewrite Rf2, OLD6, OLD5, OLD4, OLD3, OLD2 by lia. rewrite (EE 2%nat 2%bv eq_refl). reflexivity.
  + rewrite Rf1, OLD6, OLD5, OLD4, OLD3, OLD2 by lia. exact (EE 1%nat 1%bv eq_refl).
  + exact (aregs_preserved_of_st_ok SEGS (w_H W6) E6 _ ms8 regs (psw_extra (psb_vptr pv) (r_refuse R) (r_code R) (r_state R))
      HS HAE6 ltac:(vm_compute; reflexivity)).
  + rewrite Rf10. exact HSXC.
  + lia.
  + exact HREPF.
  + exact HBK6.
  + exact (psb_model_refuse R (Some u) (Some f) (Some l) verdict Hc).
  + lia.
  + exact HBBT.
  + exact HMLET.
Qed.

End e.
End f.
End d.
Print Assumptions tpins_set_holds.
