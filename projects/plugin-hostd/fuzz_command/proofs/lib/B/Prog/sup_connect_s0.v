(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the interface of sup_connect's walk on fuzz_command.asan-ubsan (image B,
   0x8b45c = BASE + AF_sup_connect, 37 instructions), the B twin of lib/A/Prog/sup_connect_s0.v
   (a working branch 8d55d5a2288), re-derived on B's code. B's sup_connect has no inline ASan
   check, no side-stack frame and no UBSan trap site: it saves ra, s0..s4 in a 48-byte frame, moves its four
   arguments to s3 (verb), s2 (line), s1 (port_a), s0 (port_b), calls record(4) (0x8b48c), keeps the slot in s4,
   calls arg_s(c, verb) (0x8b498), arg_line(c, line) (0x8b4a4), arg_s(c, port_a) (0x8b4b0), arg_s(c, port_b)
   (0x8b4bc), restores the frame and tail-jumps to answer(c, "resp 0", 1) (0x8b4ec).

   The walk is cut at the five return points of the calls, BASE + SCB_R1 .. SCB_R5. At each the state is handed
   over in concrete form (`scb_mid`: the journal from the entry, the registers s0..s3 and the callee-saved ones,
   the frame's six saved words, the recorder holding the call (REC_CONNECT, A) for the arguments A recorded so far,
   and the block and meter bookkeeping), and the next part re-seeds a symbolic state from it (`scb_seed`). The
   parts are stated in continuation form, from the tail back to the entry (SCB_T_stmt, SCB_4_stmt .. SCB_1_stmt):
     - sup_connect_s1.v: the entry to SCB_R1 (the prologue and record(4));
     - sup_connect_s2.v: SCB_R1 -> SCB_R2, SCB_R3 -> SCB_R4, SCB_R4 -> SCB_R5 (the three arg_s calls);
     - sup_connect_s3.v: SCB_R2 -> SCB_R3 (arg_line, through RecBridge.v);
     - sup_connect_s4.v: SCB_R5 -> answer's entry and answer's contract to the post.

   Symbolic states. At the entry: atoms 0..31 the registers; the one region is the 48-byte frame below sp,
   writable. At a return point: atoms 0..31 the registers there (sp = the entry's sp - 48), atoms 32..37 the entry
   values of ra, s0, s1, s2, s3, s4 that the frame holds; the one region is that frame, read-only. No shadow entry:
   the walk reads no shadow byte. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaDenot PaLibG PaCall CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c arg_line_c answer_c sup_connect_c RecBLemmas.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the return points of the five calls, as offsets of the listing's base (BASE + AF_sup_connect = 0x8b45c) *)
Definition SCB_R1 : Z := 0x4f60.    (* 0x8b490, after record(4) *)
Definition SCB_R2 : Z := 0x4f6c.    (* 0x8b49c, after arg_s(c, verb) *)
Definition SCB_R3 : Z := 0x4f78.    (* 0x8b4a8, after arg_line(c, line) *)
Definition SCB_R4 : Z := 0x4f84.    (* 0x8b4b4, after arg_s(c, port_a) *)
Definition SCB_R5 : Z := 0x4f90.    (* 0x8b4c0, after arg_s(c, port_b) *)
(* the registers the frame holds, in the order of their slots below the entry sp: ra at sp0 - 8, s0 at sp0 - 16,
   s1, s2, s3, and s4 at sp0 - 48 *)
Definition scb_saved : list Z := [1; 8; 9; 18; 19; 20].

(* no shadow entry: the shadow base and span the executor asks for are only placeholders *)
Definition SCB_SB : Z := 0x7fff8000.
Definition scb_Bx : sv := SLit SCB_SB.
Definition scb_Bspan : Z * Z := (SCB_SB, SCB_SB + 2 ^ 44 - 1).
Definition scb_SH : list shent := [].

(* the entry state: the frame [sp - 48, sp) writable *)
Definition scb_regs_e : smem := [stack_region 48].
Definition scb_facts_e : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition scb_ss_e : sstate := mkSS AF_sup_connect sr_atoms scb_regs_e None scb_facts_e.
Definition scb_extra_e : list word := [].

(* a return point P: atom 2 is sp = the entry's sp - 48, so the frame is [sp, sp + 48): ra at +40, s0 at +32, s1
   at +24, s2 at +16, s3 at +8, s4 at +0, holding atoms 32..37 *)
Definition scb_stack_m : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 48 0 0
(map (fun j => YP09.mkChunk (40 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 6)).
Definition scb_regs_m : smem := [scb_stack_m].
Definition scb_facts_m : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition scb_ss_m (P : Z) : sstate := mkSS P sr_atoms scb_regs_m None scb_facts_m.
Definition scb_extra_m (regs0 : bvmap 5 word) : list word := map (fun r => getr regs0 (Z_to_bv 5 r)) scb_saved.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma scb_w64 : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the frame of the walk: the six saved registers at their slots below the entry sp (cgif's cl_frame) *)
Definition scb_frame (m : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
forall j r, nth_error scb_saved j = Some r ->
val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 r))).

(* the stack the walk needs: its frame above each callee's need, and answer's need at the entry sp *)
Lemma scb_stk : 48 + RECORD_STK <= SUP_CONNECT_STK /\ 48 + ARG_S_STK <= SUP_CONNECT_STK /\
48 + ARG_LINE_STK <= SUP_CONNECT_STK /\ ANSWER_STK <= SUP_CONNECT_STK /\
0 <= RECORD_STK /\ 0 <= ARG_S_STK /\ 0 <= ARG_LINE_STK /\ 0 <= ANSWER_STK /\ SUP_CONNECT_STK <= 2 ^ 20.
Proof.
assert (H : ((48 + RECORD_STK <=? SUP_CONNECT_STK) && (48 + ARG_S_STK <=? SUP_CONNECT_STK) &&
  (48 + ARG_LINE_STK <=? SUP_CONNECT_STK) && (ANSWER_STK <=? SUP_CONNECT_STK) &&
  (0 <=? RECORD_STK) && (0 <=? ARG_S_STK) && (0 <=? ARG_LINE_STK) && (0 <=? ANSWER_STK) &&
  (SUP_CONNECT_STK <=? 2 ^ 20))%bool = true) by (vm_compute; reflexivity).
repeat rewrite Bool.andb_true_iff in H. rewrite !Z.leb_le in H. tauto.
Qed.

Section e.
Variable B : asyms.
(* the per-binary facts (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.

Lemma scb_obj42 : VAL (A_OBJ 42) = 0x21d20.
Proof. exact (VOBJS 42%nat ltac:(apply Nat.ltb_lt; reflexivity)). Qed.

(* the call targets of the walk *)
Lemma scb_sig_record : SIGMA CS_record = BASE + AF_record.
Proof. rewrite (SIGP CS_record); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.
Lemma scb_sig_arg_s : SIGMA CS_arg_s = BASE + AF_arg_s.
Proof. rewrite (SIGP CS_arg_s); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.
Lemma scb_sig_arg_line : SIGMA CS_arg_line = BASE + AF_arg_line.
Proof. rewrite (SIGP CS_arg_line); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.
Lemma scb_sig_answer : SIGMA CS_answer = BASE + AF_answer.
Proof. rewrite (SIGP CS_answer); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.

(* the seed of the walk at the entry 0x8b45c *)
Lemma scb_entry : forall (W : world SEGS) ly S (regs : bvmap 5 word) mem md ch,
afn_pre SEGS B SUP_CONNECT_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs scb_extra_e)) scb_ss_e
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_connect)) mem (seg_rom SEGS)))
/\ sh_ok SEGS scb_Bx scb_SH (Eimg (Ereg regs scb_extra_e)) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof scb_stk as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs scb_extra_e)).
assert (E2 : ew E 2 = getr regs 2)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (RS : YP09.region_ok SEGS E (mrestrict (w_H W) mem) (stack_region 48)).
{ unfold region_ok, stack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
assert (HG : facts_ok E scb_facts_e).
{ split; [|split; [exact I | exact I]].
  cbn [scb_facts_e f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. try change (2 ^ 4) with 16.
  revert Hslo Hshi H47 Hceil Hal16 C1 K9 Hstk0. clear. intros.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
split.
- unfold scb_ss_e. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold scb_regs_e. constructor; [exact RS | constructor].
  + apply pairwise_disjoint_of_extents. unfold scb_regs_e. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  + exact HG.
- unfold sh_ok, scb_SH. apply Forall_nil.
Qed.

(* the seed at a return point P: the registers there, the frame holding the entry's ra, s0..s4 *)
Lemma scb_seed : forall P ly (regs regsc : bvmap 5 word) lyc Sc (Wc : world SEGS) memc mdc,
astk_ok SUP_CONNECT_STK ly (spZ regs) ->
AR SEGS B lyc Sc Wc memc mdc -> spZ regsc = spZ regs - 48 ->
scb_frame (mrestrict (w_H Wc) memc) (spZ regs) regs ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (scb_extra_m regs))) (scb_ss_m P)
  (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + P)) memc (seg_rom SEGS)))
/\ sh_ok SEGS scb_Bx scb_SH (Eimg (Ereg regsc (scb_extra_m regs))) (mrestrict (w_H Wc) memc).
Proof.
intros P ly regs regsc lyc Sc Wc memc mdc Hstk HAR Hsp HFR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof scb_stk as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsc (scb_extra_m regs))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = getr regs (Z_to_bv 5 (nth j scb_saved 0))).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  unfold scb_extra_m. do 6 (destruct j as [|j]; [reflexivity|]). lia. }
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 48) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (VB2 : base_val E (Some 2%nat) = spZ regs - 48) by (cbn [base_val]; exact U2).
assert (RS : YP09.region_ok SEGS E (mrestrict (w_H Wc) memc) scb_stack_m).
{ unfold region_ok, scb_stack_m.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite VB2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj. destruct Hj as [_ Hj].
  cbn [Nat.add] in Hj.
  apply (chunk_ok_val SEGS E _ (spZ regs - 48) (40 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
    (bv_unsigned (getr regs (Z_to_bv 5 (nth j scb_saved 0))))).
  - cbn [sv_denot]. rewrite (EX j Hj), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - exact (scb_w64 (getr regs (Z_to_bv 5 (nth j scb_saved 0)))).
  - lia.
  - replace (spZ regs - 48 + (40 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
    change (N.to_nat 8) with 8%nat. apply (HFR j (nth j scb_saved 0)).
    do 6 (destruct j as [|j]; [reflexivity|]). lia. }
assert (Hmod16 : (spZ regs - 48) mod 2 ^ 4 = 0).
{ replace (2 ^ 4) with 16 by reflexivity. rewrite Zminus_mod, Hal16. reflexivity. }
assert (HG : facts_ok E scb_facts_m).
{ split; [|split; [exact I | exact I]].
  cbn [scb_facts_m f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2.
  revert Hslo Hshi H47 Hceil Hmod16 C1 K9 Hstk0. clear. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | exact Hmod16 | lia]. }
split.
- unfold scb_ss_m. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold scb_regs_m. constructor; [exact RS | constructor].
  + apply pairwise_disjoint_of_extents. unfold scb_regs_m. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  + exact HG.
- unfold sh_ok, scb_SH. apply Forall_nil.
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* The statement's premises and post, the hand-over at a return point, and the parts' statements.     *)

Section s.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the footprint of the statement (sup_connect_c.v:135-136) *)
Definition scb_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
(A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

(* the recorder's blocks are live *)
Lemma scb_rep_live : forall ly S (rd : reader) R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O pn (Q & HQ & HO) Hin. exact (lay_blocks_in _ _ _ _ _ _ HQ pn (proj1 (HO pn) Hin)). Qed.

(* every byte the footprint names lies below alloc_ceiling (so below the stack): the program's statics are in the
   image and the recorder's blocks are heap blocks *)
Lemma scb_fp_low : forall ly S (W : world SEGS) mem md O a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
inFP (scb_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO Ha.
pose proof asan_consts as ((C1a & C1b) & _).
destruct Ha as (r & Hr & Har). unfold scb_FP in Hr.
destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Har;
try (unfold A_G_REC, A_REC_SPILL, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_STATE, SC_SIZE in Har; lia).
unfold ablocks_fp in Hr. rewrite in_map_iff in Hr. destruct Hr as ([q m] & Heq & Hin).
rewrite <- Heq in Har. cbn [fst snd] in Har.
destruct (al_blocks _ _ LAWS ly S W mem md q m HAR (HO (q, m) Hin)) as (_ & _ & Hc & _). lia.
Qed.

(* a caller string in a live block, the form the statement gives the line and the two ports
   (sup_connect_c.v:118-126) *)
Definition scb_blkarg ly S (rd : reader) (O : list (Z * Z)) (p : Z) (x : list byte) : Prop :=
in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) /\
Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O /\
astr_atR rd p x /\ Z.of_nat (length x) + 1 <= LMAX + 1.
(* a string in a live block is a str_arg of the recorder's form, which arg_s asks (A's scn_argA_of_blkarg) *)
Lemma scb_argA_of_blkarg : forall ly S (W : world SEGS) mem md rd O O0 p x,
AR SEGS B ly S W mem md -> scb_blkarg ly S rd O p x ->
Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O0 ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O0 p (Some x).
Proof.
intros ly S W mem md rd O O0 p x HAR (Hbl & Hap & Hst & Hlen) Hap0. cbn [astr_argA].
split; [|split; [exact Hst | split; [exact Hlen | left; split; [exact Hbl | exact Hap0]]]].
destruct Hbl as (q & m & Hin & Hq & Hm).
destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hin) as (_ & H4096 & _). lia.
Qed.

(* the premises of the statement (sup_connect_c.v:92-130), conjunct for conjunct *)
Definition scb_pre ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch
(pv pl pa pb : Z) (verb : option (list byte)) (line port_a port_b : list byte)
(R : rstate) (O : list (Z * Z)) (t : list byte) : Prop :=
afn_pre SEGS B SUP_CONNECT_STK ly S W regs mem md ch /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 /\
Z.of_nat (length (frames S)) <= 8 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
getr regs 10 = w64 pv /\ 0 <= pv < 2 ^ 64 /\ getr regs 11 = w64 pl /\ 0 <= pl < 2 ^ 64 /\
getr regs 12 = w64 pa /\ 0 <= pa < 2 ^ 64 /\ getr regs 13 = w64 pb /\ 0 <= pb < 2 ^ 64 /\
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pv verb /\
(forall x, verb = Some x -> atail_vis SEGS W mem (pv + Z.of_nat (length x))) /\
scb_blkarg ly S (rdW W mem) O pl line /\
scb_blkarg ly S (rdW W mem) O pa port_a /\
scb_blkarg ly S (rdW W mem) O pb port_b /\
rec_repA B ly S (rdW W mem) R O /\
st_nev S + EV_SUP_CONNECT R <= EV_MAX /\
blocks_bytes S + LIVE_SUP_CONNECT verb line (Some port_a) (Some port_b) t <= LIVE_MAX /\
mo_ok MT S (XM_SUP_CONNECT MT R verb line (Some port_a) (Some port_b) t).

(* the post of the statement (sup_connect_c.v:132-156), word for word *)
Definition scb_post ly S (W : world SEGS) (regs : bvmap 5 word) mem md
(verb : option (list byte)) (line port_a port_b : list byte)
(R : rstate) (O : list (Z * Z)) (t : list byte) : world SEGS -> config -> Prop :=
apost_baseF SEGS B SUP_CONNECT_STK (scb_FP O) regs ly S W mem md (EV_SUP_CONNECT R)
(fun ly' S' W' regs' mem' md' => exists R' O' q,
 sup_connect_m R verb line (Some port_a) (Some port_b) = (R', t) /\
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn (ablocks B ly S) -> In pn O) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 In (q, n) (ablocks B ly' S') /\ (In (q, n) (ablocks B ly S) -> In (q, n) O) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_CONNECT verb line (Some port_a) (Some port_b) t /\
 mo_le MT S S' (XM_SUP_CONNECT MT R verb line (Some port_a) (Some port_b) t)).

(* the registers at a return point: sp is 48 below the entry's; s0, s1, s2, s3 hold port_b, port_a, line and verb
   (the entry's a3, a2, a1, a0); gp, tp and s5..s11 are the entry's *)
Definition scb_regs_at (regs0 regsc : bvmap 5 word) : Prop :=
spZ regsc = spZ regs0 - 48 /\
getr regsc 8 = getr regs0 13 /\ getr regsc 9 = getr regs0 12 /\
getr regsc 18 = getr regs0 11 /\ getr regsc 19 = getr regs0 10 /\
getr regsc 3 = getr regs0 3 /\ getr regsc 4 = getr regs0 4 /\
(forall r : Z, 21 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)).

(* the hand-over at a return point: the journal from the entry (kc events so far, at most EVd), the registers and
   the frame, the recorder holding the call (REC_CONNECT, A) in record()'s slot with Oc its blocks, the block
   bookkeeping of the post (a recorder block that was live at the entry was one of O; a live block is the caller's
   or the recorder's; the caller's blocks stay live), no side-stack frame added, and the live bytes and the meter
   spent so far (at most LVd and XMd) *)
Definition scb_mid ly S (W : world SEGS) (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z))
(A : list (list byte)) (EVd XMd LVd : Z)
lyc Sc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc (kc : Z) (Oc : list (Z * Z)) : Prop :=
ajournal SEGS B SUP_CONNECT_STK (spZ regs) (scb_FP O) ly S W mem md [] lyc Sc Wc memc mdc kc /\
kc <= EVd /\
scb_regs_at regs regsc /\
scb_frame (mrestrict (w_H Wc) memc) (spZ regs) regs /\
rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_CONNECT A) Oc /\
(forall pn, In pn Oc -> In pn (ablocks B ly S) -> In pn O) /\
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn Oc) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
frames Sc = frames S /\
blocks_bytes Sc <= blocks_bytes S + LVd /\
mo_le MT S Sc XMd.

(* the arguments recorded, the events, the meter and the live bytes after each call *)
Definition scb_A2 (verb : option (list byte)) : list (list byte) := [sarg verb].
Definition scb_A3 (verb : option (list byte)) (line : list byte) : list (list byte) := [sarg verb; canon line].
Definition scb_A4 (verb : option (list byte)) (line port_a : list byte) : list (list byte) :=
[sarg verb; canon line; sarg (Some port_a)].
Definition scb_A5 (verb : option (list byte)) (line port_a port_b : list byte) : list (list byte) :=
[sarg verb; canon line; sarg (Some port_a); sarg (Some port_b)].
Definition SCB_EV1 (R : rstate) : Z := EV_RECORD R.
Definition SCB_EV2 (R : rstate) : Z := SCB_EV1 R + EV_ARG_S.
Definition SCB_EV3 (R : rstate) : Z := SCB_EV2 R + EV_ARG_LINE.
Definition SCB_EV4 (R : rstate) : Z := SCB_EV3 R + EV_ARG_S.
Definition SCB_EV5 (R : rstate) : Z := SCB_EV4 R + EV_ARG_S.
Definition SCB_XM1 (R : rstate) : Z := XM_RECORD MT R.
Definition SCB_XM2 (R : rstate) (verb : option (list byte)) : Z := SCB_XM1 R + XM_ARG_S MT verb.
Definition SCB_XM3 (R : rstate) (verb : option (list byte)) (line : list byte) : Z :=
SCB_XM2 R verb + XM_ARG_LINE MT line.
Definition SCB_XM4 (R : rstate) (verb : option (list byte)) (line port_a : list byte) : Z :=
SCB_XM3 R verb line + XM_ARG_S MT (Some port_a).
Definition SCB_XM5 (R : rstate) (verb : option (list byte)) (line port_a port_b : list byte) : Z :=
SCB_XM4 R verb line port_a + XM_ARG_S MT (Some port_b).
Definition SCB_LV1 : Z := 0.
Definition SCB_LV2 (verb : option (list byte)) : Z := SCB_LV1 + LIVE_ARG_S verb.
Definition SCB_LV3 (verb : option (list byte)) (line : list byte) : Z := SCB_LV2 verb + LIVE_ARG_LINE line.
Definition SCB_LV4 (verb : option (list byte)) (line port_a : list byte) : Z :=
SCB_LV3 verb line + LIVE_ARG_S (Some port_a).
Definition SCB_LV5 (verb : option (list byte)) (line port_a port_b : list byte) : Z :=
SCB_LV4 verb line port_a + LIVE_ARG_S (Some port_b).

(* the parts' statements: from a return point (the slot c = rec_slot R in a0 after record, in s4 after that) on
   to sup_connect's post *)
Definition SCB_T_stmt : Prop :=
forall ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc kc Oc,
let t := snd (sup_connect_m R verb line (Some port_a) (Some port_b)) in
scb_pre ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t ->
scb_mid ly S W regs mem md R O (scb_A5 verb line port_a port_b) (SCB_EV5 R)
  (SCB_XM5 R verb line port_a port_b) (SCB_LV5 verb line port_a port_b) lyc Sc Wc regsc memc mdc kc Oc ->
getr regsc 20 = w64 (rec_slot R) ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + SCB_R5)) memc (seg_rom SEGS)) mdc)
  (scb_post ly S W regs mem md verb line port_a port_b R O t).
Definition SCB_4_stmt : Prop :=
forall ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc kc Oc,
let t := snd (sup_connect_m R verb line (Some port_a) (Some port_b)) in
scb_pre ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t ->
scb_mid ly S W regs mem md R O (scb_A4 verb line port_a) (SCB_EV4 R)
  (SCB_XM4 R verb line port_a) (SCB_LV4 verb line port_a) lyc Sc Wc regsc memc mdc kc Oc ->
getr regsc 20 = w64 (rec_slot R) ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + SCB_R4)) memc (seg_rom SEGS)) mdc)
  (scb_post ly S W regs mem md verb line port_a port_b R O t).
Definition SCB_3_stmt : Prop :=
forall ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc kc Oc,
let t := snd (sup_connect_m R verb line (Some port_a) (Some port_b)) in
scb_pre ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t ->
scb_mid ly S W regs mem md R O (scb_A3 verb line) (SCB_EV3 R)
  (SCB_XM3 R verb line) (SCB_LV3 verb line) lyc Sc Wc regsc memc mdc kc Oc ->
getr regsc 20 = w64 (rec_slot R) ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + SCB_R3)) memc (seg_rom SEGS)) mdc)
  (scb_post ly S W regs mem md verb line port_a port_b R O t).
Definition SCB_2_stmt : Prop :=
forall ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc kc Oc,
let t := snd (sup_connect_m R verb line (Some port_a) (Some port_b)) in
scb_pre ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t ->
scb_mid ly S W regs mem md R O (scb_A2 verb) (SCB_EV2 R)
  (SCB_XM2 R verb) (SCB_LV2 verb) lyc Sc Wc regsc memc mdc kc Oc ->
getr regsc 20 = w64 (rec_slot R) ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + SCB_R2)) memc (seg_rom SEGS)) mdc)
  (scb_post ly S W regs mem md verb line port_a port_b R O t).
Definition SCB_1_stmt : Prop :=
forall ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc kc Oc,
let t := snd (sup_connect_m R verb line (Some port_a) (Some port_b)) in
scb_pre ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t ->
scb_mid ly S W regs mem md R O [] (SCB_EV1 R) (SCB_XM1 R) SCB_LV1 lyc Sc Wc regsc memc mdc kc Oc ->
getr regsc 10 = w64 (rec_slot R) ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + SCB_R1)) memc (seg_rom SEGS)) mdc)
  (scb_post ly S W regs mem md verb line port_a port_b R O t).
(* the walk from the entry *)
Definition SCB_E_stmt : Prop :=
forall ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O,
let t := snd (sup_connect_m R verb line (Some port_a) (Some port_b)) in
scb_pre ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_connect) regs mem md)
  (scb_post ly S W regs mem md verb line port_a port_b R O t).
End s.
End e.
End f.
End w.
