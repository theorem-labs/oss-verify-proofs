(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the BODY segment of answer's ASan walk (plugin-hostd/fuzz_command, 0x8a61c ..
   0x8a734 / 0x8a670): the refusal branch, the snprintf of "resp %d", the mix_call of the changes and the store of
   g_rec.state, up to the cut points JOIN and HEAD of lib/A/Prog/answer_s1.v. *)
(* Modified by Theorem Labs, 2026-10: statement passes 4, 4b and 5 (lib/A/Prog/answer_c.v): the snprintf call goes
   through the shared contract (RtPFCmd.v asnprintf_sh) with the kit's printf step (PaFx.v aj_art_own_atF,
   srr_art_postF_of_pf); the refusal arm reaches JOIN at the FP state the wrapper returns, so BODY proves the
   statement's FP-existential post and takes JOIN at every FP state. *)
(* Modified by Theorem Labs, 2026-10: the snprintf buffer's fake frame lies above the image by the kit's
   RtPFDog.v pa_frame_above_img (the local copy br_frame_above_img is gone); the Lia settings and the Zify division
   flag are Local to this file. *)
(* Modified by Theorem Labs, 2026-10: the snprintf contract in omx-clap-core/fuzz_manifest's published form asks for
   8 bytes of band room past the destination (`amem_range d (sn_len (n - 1) T + 8)`); buf's class-7 fake frame gives
   them by the kit's PaLibH.v amem_range_sub_app. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer_br.v; 305 of its 359 lines of code are new or changed and 1027 lines of the source are left out. *)
(* sup_add's walk on the ASan build of plugin-hostd/fuzz_command, stage M0T (0x89f00 .. 0x89f44, the table arm of
   record()): ncalls := n + 1, the slot c := g_rec + 16 + 56 n, c->fn := REC_ADD = 0 and c->nargs := 0 through two
   inline checks, then the mid-state M1 at 0x89f48. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_add_s0 sup_add_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the slot record() fills on the table arm, n = the table's length *)
Definition s2t_c (n : Z) : Z := A_G_REC + OFF_CALLS + CALL_SIZE * n.
(* The symbolic state at 0x89f00. Atoms: the registers (0..31) and the slot c (32). The shadow base is s4 (atom 20).
   Regions: g_rec's ncalls word (base s5 = g_rec, atom 21) and the slot's fn and nargs words (base c). Shadow
   entry: the slot's first 8 bytes (inside g_rec, zero shadow). *)
Definition s2t_Bx : sv := SOff 20 0.
Definition s2t_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition s2t_rg_nc : YP09.region := YP09.mkRegion (Some 21%nat) 8 12 8 12 [].
Definition s2t_rg_c : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 8 [].
Definition s2t_regions : smem := [s2t_rg_nc; s2t_rg_c].
Definition s2t_facts : facts :=
mkFacts [ (20%nat, mkAF SB SB 0); (21%nat, mkAF A_G_REC A_G_REC 0);
(32%nat, mkAF (A_G_REC + OFF_CALLS) (A_G_REC + OFF_CALLS + CALL_SIZE * 15) 3) ] [] [].
Definition ss_s2t : sstate := mkSS L_M0T sr_atoms s2t_regions None s2t_facts.
Definition s2t_SH : list shent := [mkSHE 32 0 8].

Lemma s2t_in_pair : forall (x : Z * Z) l, existsb (fun y => (fst y =? fst x) && (snd y =? snd x)) l = true -> In x l.
Proof.
intros x l H. apply existsb_exists in H as (y & Hy & E). apply andb_prop in E as [E1 E2].
apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. destruct x as [x1 x2], y as [y1 y2]. cbn [fst snd] in *. subst. exact Hy.
Qed.
Lemma s2t_c_facts : forall n, 0 <= n < 16 ->
A_G_REC + OFF_CALLS <= s2t_c n /\ s2t_c n <= A_G_REC + OFF_CALLS + CALL_SIZE * 15 /\ s2t_c n mod 8 = 0.
Proof.
intros n Hn. unfold s2t_c, A_G_REC, OFF_CALLS, CALL_SIZE. split; [lia|]. split; [lia|].
replace (6174528 + 16 + 56 * n) with ((771818 + 7 * n) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition s2t_E (regs : bvmap 5 word) (c : Z) : env := Eimg (Ereg regs [Z_to_bv 64 c]).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a :=
  CmdRecBase.cif_prog_img _ _ IMG.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let RUNTO := paj_run_to B LAWS.

Lemma s2t_seed : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) n,
AR SEGS B ly S W mem md -> getr regs 20 = w64 SHADOW_OFF -> getr regs 21 = w64 A_G_REC -> 0 <= n < 16 ->
st_ok_pi SEGS VAL (s2t_E regs (s2t_c n)) ss_s2t
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + L_M0T)) mem (seg_rom SEGS)))
/\ sh_ok SEGS s2t_Bx s2t_SH (s2t_E regs (s2t_c n)) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs n HAR H20 H21 Hn.
destruct (s2t_c_facts n Hn) as (Hc1 & Hc2 & Hc8).
unfold A_G_REC, OFF_CALLS, CALL_SIZE in Hc1, Hc2.
set (c := s2t_c n) in *.
set (E := s2t_E regs c).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs [Z_to_bv 64 c]) k)
by (intros k Hk; subst E; unfold s2t_E; apply Eimg_low; exact Hk).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E21 : ew E 21 = Z_to_bv 64 A_G_REC)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E32 : ew E 32 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (B21 : base_val E (Some 21%nat) = A_G_REC)
by (cbn [base_val]; rewrite E21; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (B32 : base_val E (Some 32%nat) = c) by (cbn [base_val]; rewrite E32; apply unsigned_lit_small; lia).
assert (PG : forall a, A_G_REC <= a < A_G_REC + 960 -> inFP cmd_PG a).
{ intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia]. }
split.
- unfold ss_s2t. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold s2t_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold s2t_regions, s2t_rg_nc, s2t_rg_c. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite B21. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [|constructor].
      intros o Ho. apply PRW. apply (sa_HPROG B HB LAWS). apply PG. lia.
    * rewrite B32. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply PRW. apply (sa_HPROG B HB LAWS). apply PG.
      unfold A_G_REC. lia.
  + apply pairwise_disjoint_of_extents. unfold s2t_regions, s2t_rg_nc, s2t_rg_c, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B21, B32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_G_REC. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [s2t_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E20, E21, E32, !unsigned_lit_small by (unfold SHADOW_OFF, A_G_REC; lia).
    change (2 ^ 3) with 8. rewrite Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF, A_G_REC, OFF_CALLS, CALL_SIZE.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold sh_ok, s2t_SH. apply Forall_cons; [|apply Forall_nil].
  assert (Hzin : In (0xada00, 0x5e3b00 - 0xada00) Tfib_zero_shadow) by (apply s2t_in_pair; vm_compute; reflexivity).
  apply (shent_ok_of_range SEGS (w_H W) mem E s2t_Bx 32 c 8 c 0 8).
  + exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md _ c 8 HAR Hzin eq_refl eq_refl
      ltac:(cbn [fst snd]; lia) ltac:(cbn [fst snd]; lia)).
  + unfold s2t_Bx. apply U_atom; [exact E20 | unfold SHADOW_OFF; lia].
  + apply U_atom; [exact E32 | lia].
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF. lia.
Qed.

Lemma s2t_aval_kept : forall (rd rd' : reader) a n v,
  (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hk H k Hlt. rewrite (Hk k Hlt). exact (H k Hlt). Qed.
(* the shadow cell of c + 4 the code computes at 0x89f34..0x89f38: s11 := (s7 >> 3) + s4 *)
Lemma s2t_sh_denot : forall E x sb, ew E 32 = Z_to_bv 64 x -> ew E 20 = Z_to_bv 64 sb -> 0 <= x < 2 ^ 40 -> 0 <= sb < 2 ^ 40 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 4) (SLit 3)) (SOff 20 0)) = Z_to_bv 64 (sb + (x + 4) / 8).
Proof.
intros E x sb H32 H20 Hx Hsb. cbn [sv_denot]. rewrite H32, H20.
repeat first [ rewrite alu_add | rewrite alu_srl | progress unfold v_add, v_srl
| progress change (3 mod 64) with 3 | rewrite Z.shiftr_div_pow2 by lia | progress change (2 ^ 3) with 8
| match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
    rewrite (unsigned_lit_small z) by (first [lia | Z.div_mod_to_equations; lia]) end ].
f_equal. lia.
Qed.
(* the write windows of the walk's two runs: g_rec's ncalls (base s5 = g_rec) and the slot's fn and nargs (base c) *)
Lemma s2t_awr : forall E rs STK sp0 FP bl0 blc fr0 ly own,
  map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs = [(Some 21%nat, 8, 12); (Some 32%nat, 0, 8)] ->
  (forall a, bv_unsigned (ew E 21) + 8 <= a < bv_unsigned (ew E 21) + 12 -> awr_byte SEGS B STK sp0 FP bl0 blc fr0 ly own a) ->
  (forall a, bv_unsigned (ew E 32) <= a < bv_unsigned (ew E 32) + 8 -> awr_byte SEGS B STK sp0 FP bl0 blc fr0 ly own a) ->
  awr_ok SEGS B E rs STK sp0 FP bl0 blc fr0 ly own.
Proof.
intros E rs STK sp0 FP bl0 blc fr0 ly own Hmap H1 H2 a (r & Hin & Har).
apply (in_map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r))) in Hin. rewrite Hmap in Hin.
destruct Hin as [Hq | [Hq | []]]; injection Hq as Hb Hl Hh; rewrite <- Hb, <- Hl, <- Hh in Har; cbn [base_val] in Har;
[apply H1 | apply H2]; lia.
Qed.
Lemma s2t_kept_run : forall E rs (m m' : word -> option byte) H a,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs = [(Some 21%nat, 8, 12); (Some 32%nat, 0, 8)] ->
  0 <= a < 2 ^ 64 -> ~ (bv_unsigned (ew E 21) + 8 <= a < bv_unsigned (ew E 21) + 12) ->
  ~ (bv_unsigned (ew E 32) <= a < bv_unsigned (ew E 32) + 8) ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs m m' H a Hf Hmap Ha H1 H2. unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros (r & Hin & Har).
apply (in_map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r))) in Hin. rewrite Hmap in Hin.
destruct Hin as [Hq | [Hq | []]]; injection Hq as Hb Hl Hh; rewrite <- Hb, <- Hl, <- Hh in Har; cbn [base_val] in Har; lia.
Qed.
Lemma s2t_aval_of_val : forall H (m : word -> option byte) a n v,
  val_mem SEGS (mrestrict H m) a n v -> aval_mem (aview SEGS H m) a n v.
Proof.
intros H m a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold le_byte.
pose proof (Z.mod_pos_bound (Z.shiftr (v mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) 256 ltac:(lia)).
unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.
(* a word the run stored, read back from the post-state's region chunk *)
Lemma s2t_chunk_aval : forall E ss (ms : machine_state) H i r j off (w : N) e v,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal w e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  aval_mem (aview SEGS H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat w) v.
Proof.
intros E ss ms H i r j off w e v HS Hi Hj He Hv Hw. apply s2t_aval_of_val.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i r HS Hi) as (_ & _ & _ & Hcs). cbn [ms_mem restrict] in Hcs.
eapply val_of_chunk_ok; [| exact He | exact Hv | exact Hw].
exact (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hj)).
Qed.
(* the slot address the code computes at 0x89f18: s6 := g_rec + 56 n + 16 *)
Lemma s2t_c_denot : forall E n, ew E 10 = Z_to_bv 64 n -> ew E 21 = Z_to_bv 64 A_G_REC -> 0 <= n < 16 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit 56)) (SLit 16)) (SOff 21 0)) = Z_to_bv 64 (s2t_c n).
Proof.
intros E n H10 H21 Hn. cbn [sv_denot]. rewrite H10, H21.
repeat first [ rewrite alu_add | rewrite m_mul | progress unfold v_add, v_mul
| match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit_small z) by (unfold A_G_REC; lia) end ].
f_equal. unfold s2t_c, A_G_REC, OFF_CALLS, CALL_SIZE. lia.
Qed.

Lemma sa_m0t_ok : SA_M1_stmt B MT -> SA_M0T_stmt B MT.
Proof.
intros HM1. unfold SA_M0T_stmt.
intros ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos HCX HM0 Hlen.
pose proof HM0 as (HCORE & H10 & H11 & H20 & H24 & HREP & HACCT & HMO).
pose proof HCORE as (HJ & HFR & HV16 & HV24 & HV48 & HFLAG & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G21 & G25 & G26).
set (n := Z.of_nat (length (r_calls R))) in *.
assert (Hn : 0 <= n < 16) by (unfold n; lia).
destruct (s2t_c_facts n Hn) as (Hc1 & Hc2 & Hc8).
destruct (s2t_seed lyc Sc Wc memc mdc regs1 n (proj1 HJ) H20 G21 Hn) as [HS SHOK].
set (c := s2t_c n) in *.
assert (HEI : img_env VAL A_LIM (s2t_E regs1 c)) by (unfold s2t_E; apply Eimg_env).
assert (U21 : bv_unsigned (ew (s2t_E regs1 c) 21) = A_G_REC).
{ unfold s2t_E. rewrite (ew_Eimg_Ereg_nat regs1 _ 21 21%bv eq_refl), G21. apply unsigned_lit_small. unfold A_G_REC. lia. }
assert (U32 : bv_unsigned (ew (s2t_E regs1 c) 32) = c).
{ unfold s2t_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs1 _ 0). apply unsigned_lit_small.
  unfold A_G_REC, OFF_CALLS, CALL_SIZE in Hc1, Hc2. lia. }
(* a byte of g_rec in the statement's footprint: a program-static store *)
assert (PG : forall a, A_G_REC <= a < A_G_REC + 960 -> inFP cmd_PG a).
{ intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia]. }
assert (AWB : forall a, A_G_REC <= a < A_G_REC + 960 -> inFP (sa_FP O) a ->
  awr_byte SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc [(1, pos)] a).
{ intros a Ha Hfp. unfold awr_byte, awr_prog_or_caller. right; right; right; right; left.
  split; [exact Hfp|]. split; [exact (sa_HPROG B HB LAWS a (PG a Ha)) | exact (cif_prog_img a (PG a Ha))]. }
paj_run_to_tok RUNTO HS HJ SHOK s2t_Bspan (AF_sup_add + 0x160).
- unfold ss_s2t, s2t_regions. cbn [ss_mem].
  eapply awr_ok_cons_gen; [reflexivity | exact U21 | |].
  { intros a Ha. cbn [s2t_rg_nc YP09.r_wlo YP09.r_whi] in Ha. apply AWB; [unfold A_G_REC in *; lia|].
    unfold sa_FP. apply inFP_cons. left. unfold OFF_NCALLS. lia. }
  eapply awr_ok_cons_gen; [reflexivity | exact U32 | | apply awr_ok_nil].
  intros a Ha. cbn [s2t_rg_c YP09.r_wlo YP09.r_whi] in Ha. unfold A_G_REC, OFF_CALLS, CALL_SIZE in Hc1, Hc2.
  apply AWB; [unfold A_G_REC in *; lia|].
  unfold sa_FP. apply inFP_cons. right. apply inFP_cons. left. unfold A_G_REC, OFF_CALLS, OFF_ANSWER. lia.
- lazymatch goal with |- context [with_vm_backing ?a ?b ?c] => set (mdv1 := with_vm_backing a b c) in * end. clearbody mdv1.
  (* 0x89f1c: reseat s6 as the slot's own atom c *)
  assert (E10 : ew (s2t_E regs1 c) 10 = Z_to_bv 64 n) by (unfold s2t_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 10 10%bv eq_refl); exact H10).
  assert (E21 : ew (s2t_E regs1 c) 21 = Z_to_bv 64 A_G_REC) by (unfold s2t_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 21 21%bv eq_refl); exact G21).
  pose proof (st_ok_pi_restrict_reg (w_H Wc) _ _ ms 22%bv HS) as R22.
  lazymatch type of R22 with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in R22 end.
  rewrite (s2t_c_denot _ n E10 E21 Hn) in R22.
  assert (R22' : getr (ms_regs (restrict (w_H Wc) ms)) 22%bv = sv_denot (s2t_E regs1 c) (SOff 32 0)).
  { cbn [sv_denot]. rewrite U32, Z.add_0_r. exact R22. }
  assert (Hne : (22%bv : bv 5) <> 0%bv) by (intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate Hq).
  pose proof (st_ok_pi_set_reg _ _ _ 22%bv (SOff 32 0) HS Hne R22') as HS'. clear HS R22 R22'. rename HS' into HS.
  paj_run_to_tok RUNTO HS HJ SHOK s2t_Bspan L_M1.
  + apply s2t_awr; [vm_compute; reflexivity | rewrite U21; intros a Ha | rewrite U32; intros a Ha].
    * apply AWB; [unfold A_G_REC in *; lia|]. unfold sa_FP. apply inFP_cons. left. unfold A_G_REC, OFF_NCALLS in *. lia.
    * unfold A_G_REC, OFF_CALLS, CALL_SIZE in Hc1, Hc2. apply AWB; [unfold A_G_REC in *; lia|].
      unfold sa_FP. apply inFP_cons. right. apply inFP_cons. left. unfold A_G_REC, OFF_CALLS, OFF_ANSWER. lia.
  + lazymatch goal with |- context [with_vm_backing ?a ?b ?c] => set (mdv2 := with_vm_backing a b c) in * end. clearbody mdv2.
    (* 0x89f48: the mid-state M1 *)
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) => set (E2 := Ex) in *; rename msx into ms2 end.
    lazymatch goal with Hf : frame_of _ _ (mrestrict _ (ms_mem ms)) (mrestrict _ (ms_mem ms2)) |- _ => rename Hf into HFr2 end.
    assert (EW : forall k, (k < 1024)%nat -> ew E2 k = ew (s2t_E regs1 c) k)
      by (intros k Hk; unfold E2; rewrite !ew_ewset_other by lia; reflexivity).
    pose proof HCX as (HPRE & _).
    pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
    pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
    pose proof asan_consts as (C1 & _).
    unfold A_G_REC, OFF_CALLS, CALL_SIZE in Hc1, Hc2.
    assert (Hcdef : c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))) by reflexivity.
    (* the memory outside the two write windows is the memory at M0T *)
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_REC + 8 <= a < A_G_REC + 12) -> ~ (c <= a < c + 8) ->
      rdW Wc (ms_mem ms2) a = rdW Wc memc a).
    { intros a Ha H1 H2. rewrite <- U21 in H1. rewrite <- U32 in H2.
      rewrite (s2t_kept_run (s2t_E regs1 c) _ (ms_mem ms) (ms_mem ms2) (w_H Wc) a HFr2 ltac:(vm_compute; reflexivity) Ha H1 H2).
      exact (s2t_kept_run (s2t_E regs1 c) _ memc (ms_mem ms) (w_H Wc) a HFr ltac:(vm_compute; reflexivity) Ha H1 H2). }
    assert (KEEPhi : forall a, 0x606000 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms2) a = rdW Wc memc a)
      by (intros a Ha; apply KEEP; unfold A_G_REC in *; lia).
    assert (KEEPlo : forall a, 0 <= a < 0x10000 -> rdW Wc (ms_mem ms2) a = rdW Wc memc a)
      by (intros a Ha; apply KEEP; unfold A_G_REC in *; lia).
    (* the registers the two runs keep *)
    assert (HAE2 : env_agree 32 (Ereg regs1 [Z_to_bv 64 c]) E2).
    { split; [|reflexivity]. intros k Hk. rewrite EW by lia. unfold s2t_E. apply Eimg_low. unfold A_TEXT. lia. }
    assert (KR : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26]%bv -> getr (ms_regs ms2) r = getr regs1 r)
      by exact (regs_kept_of_st_ok_pi _ _ _ regs1 [Z_to_bv 64 c] [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26]%bv
        HS HAE2 ltac:(vm_compute; reflexivity)).
    assert (REG : forall (r : bv 5) e, sr_get (ss_regs ltac:(lazymatch type of HS with st_ok_pi _ _ _ ?s _ => exact s end)) r = e ->
      getr (ms_regs ms2) r = sv_denot E2 e).
    { intros r e He. rewrite <- He. exact (st_ok_pi_restrict_reg (w_H Wc) _ _ ms2 r HS). }
    assert (UE20 : ew E2 20 = Z_to_bv 64 SHADOW_OFF).
    { rewrite EW by lia. unfold s2t_E. rewrite (ew_Eimg_Ereg_nat regs1 _ 20 20%bv eq_refl). exact H20. }
    assert (UE32 : ew E2 32 = Z_to_bv 64 c).
    { rewrite EW by lia. unfold s2t_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). }
    assert (R22 : getr (ms_regs ms2) 22%bv = w64 c).
    { rewrite (REG 22%bv (SOff 32 0) ltac:(vm_compute; reflexivity)). cbn [sv_denot]. rewrite UE32.
      rewrite unsigned_lit_small by (unfold A_G_REC in *; lia). rewrite Z.add_0_r. reflexivity. }
    assert (R23 : getr (ms_regs ms2) 23%bv = w64 (c + 4)).
    { rewrite (REG 23%bv (SOff 32 4) ltac:(vm_compute; reflexivity)). cbn [sv_denot]. rewrite UE32.
      rewrite unsigned_lit_small by (unfold A_G_REC in *; lia). reflexivity. }
    assert (R27 : getr (ms_regs ms2) 27%bv = w64 (SHADOW_OFF + (c + 4) / 8)).
    { rewrite (REG 27%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 4) (SLit 3)) (SOff 20 0)) ltac:(vm_compute; reflexivity)). unfold w64.
      apply (s2t_sh_denot E2 c SHADOW_OFF UE32 UE20); unfold SHADOW_OFF, A_G_REC in *; lia. }
    (* the stored words, read back from the regions *)
    assert (D10 : sv_denot E2 (SOff 10 1) = Z_to_bv 64 (n + 1)).
    { cbn [sv_denot]. rewrite EW by lia. rewrite E10, unsigned_lit_small by lia. reflexivity. }
    assert (V4 : forall v, 0 <= v < 17 -> 0 <= v < 2 ^ (8 * Z.of_N 4))
      by (intros v Hv; change (2 ^ (8 * Z.of_N 4)) with 4294967296; lia).
    assert (W4 : Z.of_N 4 <= 8) by (change (Z.of_N 4) with 4; lia).
    pose proof (s2t_chunk_aval _ _ ms2 (w_H Wc) 0 _ 0 8 4 (SOff 10 1) (n + 1) HS eq_refl eq_refl D10 (V4 (n + 1) ltac:(lia)) W4)
      as ANC.
    pose proof (s2t_chunk_aval _ _ ms2 (w_H Wc) 1 _ 1 0 4 (SLit 0) 0 HS eq_refl eq_refl eq_refl (V4 0 ltac:(lia)) W4) as AFN.
    pose proof (s2t_chunk_aval _ _ ms2 (w_H Wc) 1 _ 0 4 4 (SLit 0) 0 HS eq_refl eq_refl eq_refl (V4 0 ltac:(lia)) W4) as ANA.
    cbn [YP09.r_base base_val] in ANC, AFN, ANA.
    change (N.to_nat 4) with 4%nat in ANC, AFN, ANA. rewrite Z.add_0_r in AFN.
    rewrite EW, U21 in ANC by lia. rewrite EW, U32 in AFN, ANA by lia.
    (* the recorder: record()'s table arm *)
    pose proof (rec_repA_fields B HB LAWS) as RF.
    destruct (RF _ _ _ _ _ HREP) as (_ & _ & _ & _ & _ & _ & _ & _ & HO).
    pose proof (rec_repA_record_table B HB LAWS) as RT.
    assert (HREP2 : rec_repA B lyc Sc (rdW Wc (ms_mem ms2)) (rec_record R REC_ADD []) O).
    { apply (RT lyc Sc (rdW Wc memc) lyc Sc (rdW Wc (ms_mem ms2)) R O HREP Hlen).
      - intros a Hin H1 H2. apply KEEP; [unfold in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia | exact H1 |].
        rewrite Hcdef. exact H2.
      - intros p k i Hin Hi. destruct (HO (p, k) Hin) as (Hb & H1k & Hap & _). cbn [fst snd] in Hb, H1k, Hap.
        destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms2) mdv2 p k (proj1 HJ) Hb) as (_ & Hp4096 & Hpceil & _).
        pose proof (req_size_pos0 k ltac:(lia)) as [_ Hrk].
        apply KEEP; unfold iv_apart, A_G_REC, REC_SIZE in *; lia.
      - intros pn Hin. exact (proj1 (HO pn Hin)).
      - unfold OFF_NCALLS. exact ANC.
      - rewrite <- Hcdef. unfold CALL_OFF_FN, REC_ADD. rewrite Z.add_0_r. exact AFN.
      - rewrite <- Hcdef. unfold CALL_OFF_NARGS. exact ANA. }
    pmkst HS.
    change (BASE + 14948) with (BASE + L_M1).
    apply (HM1 ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc
      (ms_regs ms2) (ms_mem ms2) mdv2 pos HCX).
    (* the mid-state M1 at 0x89f48 *)
    assert (Hsac : sa_c R = c) by (unfold sa_c, c, s2t_c; rewrite (proj2 (Nat.ltb_lt _ _) Hlen); reflexivity).
    assert (Hev : sa_ev1 R = 0) by (unfold sa_ev1, rec_spill_frees; rewrite (proj2 (Nat.ltb_lt _ _) Hlen); reflexivity).
    assert (Hacc : sa_acc1 MT R = 0)
      by (unfold sa_acc1, rec_spill_frees; rewrite (proj2 (Nat.ltb_lt _ _) Hlen); lia).
    (* the side-stack frame of this call, and the bytes the two stores did not touch *)
    pose proof HJ as (HARc & _ & _ & _ & _ & HFRAMES & _).
    assert (HinF : In (1, pos) (frames Sc)) by (rewrite HFRAMES; left; reflexivity).
    destruct (frames_bounds SEGS B LAWS lyc Sc Wc (ms_mem ms2) mdv2 1 pos HARc HinF) as (HF1 & HF2 & HF3).
    pose proof (frm_off_imgP B lyc Sc Wc (ms_mem ms2) mdv2 1 pos HARc HinF) as HFimg.
    assert (HFb : fs_frame_bytes 1 = 128) by reflexivity. rewrite HFb in HF2, HF3, HFimg.
    pose proof alloc_ceiling_value as [_ HAC].
    assert (KEEPF : forall a, frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 128 ->
      rdW Wc (ms_mem ms2) a = rdW Wc memc a).
    { intros a Ha. destruct HFimg as [Hlo | Hhi]; [apply KEEPlo | apply KEEPhi]; unfold off_img in *; lia. }
    assert (KEEPST : forall a, spZ regs - 192 <= a < spZ regs -> rdW Wc (ms_mem ms2) a = rdW Wc memc a).
    { intros a Ha. apply KEEPhi. lia. }
    unfold sa_M1m. cbv zeta. rewrite Hsac, Hev, Hacc.
    assert (Hs1 : spZ regs - 192 <= sa_s1 (spZ regs) <= spZ regs - 160).
    { unfold sa_s1. pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)). lia. }
    split.
    { unfold sa_core. cbv zeta. split; [exact HJ|]. split.
      - intros j r Hj.
        assert (Hj13 : (j < length sa_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
        change (length sa_saved) with 13%nat in Hj13.
        apply (s2t_aval_kept (rdW Wc memc)); [intros k Hk; apply KEEPST; lia | exact (HFR j r Hj)].
      - split; [apply (s2t_aval_kept (rdW Wc memc)); [intros k Hk; apply KEEPST; lia | exact HV16]|].
        split; [apply (s2t_aval_kept (rdW Wc memc)); [intros k Hk; apply KEEPST; lia | exact HV24]|].
        split; [apply (s2t_aval_kept (rdW Wc memc)); [intros k Hk; apply KEEPST; lia | exact HV48]|].
        split.
        { rewrite <- HFLAG. apply rdword_ext. intros k Hk. apply KEEPF. rewrite HFb. lia. }
        split; [rewrite (KR 2%bv ltac:(cbn; tauto)); exact G2|].
        split; [rewrite (KR 3%bv ltac:(cbn; tauto)); exact G3|].
        split; [rewrite (KR 4%bv ltac:(cbn; tauto)); exact G4|].
        split; [rewrite (KR 8%bv ltac:(cbn; tauto)); exact G8|].
        split; [rewrite (KR 9%bv ltac:(cbn; tauto)); exact G9|].
        split; [rewrite (KR 18%bv ltac:(cbn; tauto)); exact G18|].
        split; [rewrite (KR 19%bv ltac:(cbn; tauto)); exact G19|].
        split; [rewrite (KR 21%bv ltac:(cbn; tauto)); exact G21|].
        split; [rewrite (KR 25%bv ltac:(cbn; tauto)); exact G25 | rewrite (KR 26%bv ltac:(cbn; tauto)); exact G26]. }
    split; [rewrite (KR 20%bv ltac:(cbn; tauto)); exact H20|].
    split; [exact R22|]. split; [exact R23|].
    split; [rewrite (KR 24%bv ltac:(cbn; tauto)); exact H24|].
    split; [exact R27|].
    exists O. split; [exact HREP2|]. split; [exact HACCT | exact HMO].
Qed.
End e.
End f.
End d.
