(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of mix_call (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, entry BASE + AF_mix_call = 0x8ad54, 480 bytes, 120 instructions): tmix_call_spec of
   a Theorem Labs lane's lib/B/Prog/mix_call_c.v (blob ebd1fd295d8, the same on a working branch f490061c104 and 707acd856cb), proved in the A walk's
   style (lib/A/Prog/mix_call.v, a working branch fa7944d852b): the verified symbolic executor over
   cmd_listing (paj_run_tok / paj_run_to_tok / psrr_branch_tok, lib/B/Prog/CmdPaLib.v), the inline shadow checks
   removed by the token executor with their addressability obligations, the strlen wrapper through its Theorem Labs lane
   contract taken at the current FP state, and one lemma per loop (the 4 bytes of c->fn run straight; the argument
   loop and the byte loop are inductions over a re-seeded loop head).

   The B code, measured with capstone on the pinned fuzz_command.asan-ubsan (.symtab: mix_call LOCAL FUNC 0x8ad54,
   480 bytes), is A's code with a 96-byte frame (ra, s0-s10), other registers and the UBSan checks:
     0x8ad54 .. 0x8ad84  the frame; 0x8ad88 beqz a1 -> trap; 0x8ad94 bnez (c & 7) -> trap
     0x8ad98 / 0x8ada8   the two auipc pairs: the shadow-base GOT word 0xa5f50 (A_OBJ 0) and the FNV-1a offset
                         basis 0x10330 (A_OBJ 58), both object atoms bridged by VOBJS (no A_HI value: no VHIS)
     0x8adc8 .. 0x8adf8  the 4 bytes of c->fn (a4 counts 4 -> 0), each with 0x8adcc bgeu 1, b + 1 -> trap and the
                         load1 check 0x8add8 (slow path 0x8ae00, report 0x8ae08)
     0x8ae0c .. 0x8ae24  the load4 check on c->nargs 0x8ae18 (slow path 0x8af20, report 0x8af2c), blez nargs
     0x8ae28 .. 0x8ae4c  a := 0 (s4), s5 := c + 8, s6 := basis, s7 := ~s5, s8 := nargs, s9 := INT_MAX, s10 := 1
     0x8ae50 .. 0x8ae74  argument loop: 0x8ae54 bltu s7, 8a -> trap; load8 check 0x8ae64 (report 0x8af30);
                         s1 := c->args[a]; jal __interceptor_trampoline_strlen 0x4517c (at 0x8ae74)
     0x8ae78 .. 0x8ae84  basis if the digest is 0, a1 := len + 1, into the byte loop
     0x8ae88 .. 0x8ae94  0x8ae88 beq a, INT_MAX -> trap; a := a + 1; 0x8ae90 beq a, nargs -> epilogue
     0x8ae9c .. 0x8aed0  byte loop: 0x8aea0 bgeu 1, b + 1 -> trap; load1 check 0x8aeac (slow path 0x8aed4, report
                         0x8aedc); digest step; back to 0x8ae88 after the terminator
     0x8aee0 .. 0x8af18  epilogue; 0x8af1c unimp (the one UBSan trap)

   Report / trap edges, each refuted at its branch:
     0x8ad88 (c = NULL -> 0x8af1c): decided by the executor's decide_cond2 (lib/Reusable/YP0e.v:932, sound by
       decide_cond2_sound :981) in mc_core's first run, from the slot premise (atom 11's fact A_G_REC <= c in
       mc_facts0, established in mc_entry).
     0x8ad94 (c mod 8 <> 0 -> 0x8af1c): the same, from the slot premise (atom 11's alignment 2 ^ 3 in mc_facts0).
     0x8adcc (b + 1 <= 1 over c->fn -> 0x8af1c), 4 times: the same, in mc_core's second run (atom 11's range).
     0x8add8 -> 0x8ae00 -> 0x8ae08 (__asan_report_load1 on c->fn): removed by the token executor, whose obligation
       is range_addressable at c + k (OBL in mc_core), from the slot premise by mc_rec_addr (CmdZsh's
       cmd_addressable_in over the record's zero-shadow ranges of g_rec and record.spill, lib/B/YF0m.v:4650-4651).
     0x8ae18 -> 0x8af20 -> 0x8af2c (__asan_report_load4 on c->nargs): the same (OBL in mc_core).
     0x8ae54 (c + 8 + 8a overflows -> 0x8af1c): at a = 0 (mc_core) refuted by mc_ltu0 (s7 < 0 unsigned never
       holds); at a + 1 (mc_inc) decided by the executor from ss_inc's facts (atom 23 = ~(c + 8) >= MC_NOTC
       A_REC_SPILL, atom 20 = a <= 5), from the slot premise and acall_at's nargs <= 6.
     0x8ae64 -> 0x8af30 (__asan_report_load8 on c->args[a]): removed by the token executor in mc_args, its
       obligation discharged by mc_rec_addr from the slot premise.
     0x8ae88 (a = INT_MAX -> 0x8af1c): decided by the executor in mc_inc from ss_inc's facts (atom 20 = a <= 5,
       atom 25 = s9 = 0x7fffffff), from acall_at's nargs <= 6.
     0x8aea0 (b + 1 <= 1 over an argument -> 0x8af1c): decided by the executor in mc_bytes from mc_bl_facts (atom
       10 = b >= 4096, atom 26 = s10 = 1), from acall_at's argument block (AR's block law al_blocks).
     0x8aeac -> 0x8aed4 -> 0x8aedc (__asan_report_load1 on an argument's bytes): removed by the token executor in
       mc_bytes, its obligation discharged by range_addressable_of_block (AR's block law) from acall_at.

   Section hypotheses beyond the statement's (ASTRLEN, VOBJS): the per-binary allocator record CmdBSyms (HB), and
   the per-binary image facts in the form of a Theorem Labs lane's lib/B/Prog/CmdRecImg.v cmd_img_facts_tfib at this walk's
   abstract segments (used for CmdRecCells' cmd_cf_env, the errno / trace facts of the runtime-entry call). The
   shadow-cell and GOT facts are CmdRecCells' cmd_cf_cell / cmd_cf_got (HB + VOBJS), the AR laws AR_laws_ok.

   TAKEN FROM: the A walk lib/A/Prog/mix_call.v (a working branch fa7944d852b), re-walked at the B
   addresses above; the Generation-N B walk lib/B/Prog/mix_call.v (a working branch a3f99d62c52) read as a
   template of the B code only, not ported and not required. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdAddr CmdObj CmdRo CmdPaLib PaDenot PaSB CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecCells CmdRecImg mix_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecRest.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac callee_ok := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

(* The block labels, as offsets from BASE (the pinned image: 0x8ad54 - AF_mix_call = 0x86530 = BASE) *)
Definition MC_A : Z := 0x492c.        (* 0x8ae5c: argument loop, after a0 := c + 8 + 8a *)
Definition MC_LEN : Z := 0x4948.      (* 0x8ae78: back from strlen *)
Definition MC_INC : Z := 0x4958.      (* 0x8ae88: the a = INT_MAX trap check, then a := a + 1 *)
Definition MC_BL : Z := 0x496c.       (* 0x8ae9c: byte loop *)
Definition MC_EPI : Z := 0x49b0.      (* 0x8aee0: epilogue *)

Definition mc_slot (c : Z) : Prop :=
(exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL.

Lemma mc_slot_range : forall c, mc_slot c -> A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_REC_SPILL + SC_SIZE /\ c mod 8 = 0 /\
((A_G_REC <= c /\ c + CALL_SIZE <= A_G_REC + REC_SIZE) \/ c = A_REC_SPILL).
Proof.
intros c [(i & Hi & ->) | ->]; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX, A_REC_SPILL, SC_SIZE, REC_SIZE in *.
- split; [lia|]. split; [lia|]. split; [|left; lia].
  match goal with |- ?x mod 8 = 0 => replace x with ((771674 + 7 * i) * 8) by lia end. apply Z_mod_mult.
- split; [lia|]. split; [lia|]. split; [reflexivity | right; reflexivity].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma mbyte_of_aview : forall H mem a z, aview SEGS H mem a = Some z -> 0 <= z < 256 ->
mbyte SEGS (mrestrict H mem) a = Some (Z_to_bv 8 z).
Proof.
intros H mem a z Ha Hz. unfold aview in Ha. destruct (mbyte SEGS (mrestrict H mem) a) as [b|] eqn:Hb; [|discriminate].
cbn in Ha. injection Ha as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Definition mc_Bx : sv := SOff 32 0.
Definition mc_fnv_region : YP09.region := YP09.mkRegion (Some (A_OBJ 58)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit FNV_B0))].
Definition mc_c_region : YP09.region := YP09.mkRegion (Some 11%nat) 0 8 0 0
[YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0)); YP09.mkChunk 2 (CVal 1 (SOff 35 0));
 YP09.mkChunk 3 (CVal 1 (SOff 36 0)); YP09.mkChunk 4 (CVal 4 (SOff 37 0))].
Definition mc_regions0 : smem := [stack_region 96; got_regionP; bcell_regionP 32; mc_fnv_region; mc_c_region].
Definition mc_facts0 : facts :=
mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (11%nat, mkAF A_G_REC A_REC_SPILL 3); (32%nat, mkAF SB SB 0);
         (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0);
         (37%nat, mkAF 0 6 0)] [] [].
Definition ss_mc0 : sstate := mkSS AF_mix_call sr_atoms mc_regions0 None mc_facts0.
Definition mc_extra0 (fn na : Z) : list word :=
map (Z_to_bv 64) [SB; le_byte fn 4 0; le_byte fn 4 1; le_byte fn 4 2; le_byte fn 4 3; na].

Lemma le_byte_range : forall v n k, 0 <= le_byte v n k < 256.
Proof. intros. unfold le_byte. apply Z.mod_pos_bound. lia. Qed.
Lemma le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.

Lemma ro_10330_val : forall H mem, abytes_atR (aview SEGS H mem) 0x10330 RO_lit_10330 ->
val_mem SEGS (mrestrict H mem) 0x10330 8 FNV_B0.
Proof.
intros H mem Hb k Hk. apply mbyte_of_aview; [|apply le_byte_range].
rewrite (Hb k ltac:(cbn; lia)).
do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's runtime entry (at every FP state) and object bridge (mix_call_c.v:68-69) *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses: the per-binary allocator record (a Theorem Labs lane's lib/B/YF0m.v), and the per-binary image facts in
   the form of a Theorem Labs lane's CmdRecImg.v cmd_img_facts_tfib (proved there at the pinned image), at this walk's segments *)
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> cmd_img_facts SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : cmd_img_facts SEGS B := cmd_img_facts_tfib B HB.
Let HBgot : as_got_shadow B = VAL (A_OBJ 0) := cmd_cf_got (PI := PI) B HB VOBJS.
Let HBcell : as_shadow_cell B = VAL (A_OBJ 12) := cmd_cf_cell (PI := PI) B HB VOBJS.
Let ENV : api_env SEGS B := cmd_cf_env (SK := SK) SEGS B LAWS HB IMG.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

Lemma val_A58 : VAL (A_OBJ 58) = 0x10330.
Proof. exact (VOBJS 58%nat ltac:(vm_compute; lia)). Qed.
Lemma val_A0 : VAL (A_OBJ 0) = 0xa5f50.
Proof. exact (VOBJS 0%nat ltac:(vm_compute; lia)). Qed.
Lemma val_A12 : VAL (A_OBJ 12) = 0xb0c38.
Proof. exact (VOBJS 12%nat ltac:(vm_compute; lia)). Qed.

(* a Theorem Labs lane's view of the ROM, from the statement's read-only view: every ROM byte is in_roP's first arm *)
Lemma mc_rom_view : forall (W : world SEGS) mem, arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> rt_rom_view SEGS B W mem.
Proof. intros W mem HA a Hrom Hown Herr. apply HA; [left; exact Hrom | exact Hown | exact Herr]. Qed.
(* it holds at a later state whose memory below alloc_ceiling is the entry's: every ROM byte is in the image *)
Lemma rt_rom_view_low : forall (W : world SEGS) m0 m, (forall a, 0 <= a < alloc_ceiling ->
aview SEGS (w_H W) m a = aview SEGS (w_H W) m0 a) -> rt_rom_view SEGS B W m0 -> rt_rom_view SEGS B W m.
Proof.
intros W m0 m HL HR a Hrom Hown Herr. pose proof asan_consts as (C1 & _).
pose proof Hrom as (sg & Hsg & Hw & Hr). pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hr))) as Hi.
rewrite (HL a) by lia. exact (HR a Hrom Hown Herr).
Qed.

Lemma mc_entry : forall W ly S regs mem md h c e P,
afn_pre_na SEGS B MIX_CALL_STK ly S W regs mem md ->
getr regs 10 = w64 h -> 0 <= h < 2 ^ 64 -> getr regs 11 = w64 c -> mc_slot c ->
acall_at (ablocks B ly S) (rdW W mem) c e P ->
abytes_atR (rdW W mem) 0x10330 RO_lit_10330 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (mc_extra0 (fst e) (Z.of_nat (length (snd e)))))) ss_mc0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_mix_call)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md h c e P HPRE H10 Hh H11 Hc HCA HRO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (mc_slot_range c Hc) as (Hc1 & Hc2 & Hc8 & _).
unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE in Hc1, Hc2.
pose proof HCA as (Hfn & Hna6 & HlenP & Mfn & Mna & _).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (fn := fst e) in *. set (na := Z.of_nat (length (snd e))) in *.
set (E := Eimg (Ereg regs (mc_extra0 fn na))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (mc_extra0 fn na) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (le_byte fn 4 0)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (le_byte fn 4 1)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (le_byte fn 4 2)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 (le_byte fn 4 3)) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 na) by exact (EX 5%nat ltac:(lia)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E299 : ew E (A_OBJ 58) = Z_to_bv 64 0x10330) by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite val_A58; reflexivity).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (HgcD : VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 0)) by (rewrite val_A0, val_A12; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Hna : 0 <= na <= 6) by (subst na; lia).
pose proof (le_byte_range fn 4 0) as B0. pose proof (le_byte_range fn 4 1) as B1.
pose proof (le_byte_range fn 4 2) as B2. pose proof (le_byte_range fn 4 3) as B3.
assert (VFN : forall k, (k < 4)%nat -> val_mem SEGS (mrestrict (w_H W) mem) (c + Z.of_nat k) 1 (le_byte fn 4 k)).
{ intros k Hk i Hi. replace i with 0%nat by lia. rewrite Z.add_0_r.
  apply mbyte_of_aview; [|apply le_byte_range].
  replace (c + Z.of_nat k) with (c + CALL_OFF_FN + Z.of_nat k) by (unfold CALL_OFF_FN; lia). rewrite (Mfn k Hk).
  f_equal. symmetry. apply le_byte1. apply le_byte_range. }
pose proof (CmdRecRest.val_mem_of_aval SEGS _ _ _ _ _ Mna) as VNA.
unfold ss_mc0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold mc_regions0, stack_region, got_regionP, bcell_regionP, mc_fnv_region, mc_c_region.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. unfold MIX_CALL_STK, ESTACK in *. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold MIX_CALL_STK, ESTACK. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 mc_Bx SB);
    [cbn [sv_denot mc_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB (A_OBJ 58) 0x10330 E299) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0x10330 0 8 (SLit FNV_B0) FNV_B0); [reflexivity | unfold FNV_B0; zside | zside |].
    rewrite Z.add_0_r. apply ro_10330_val. exact HRO.
  + rewrite (VB 11%nat c E11) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ c 0 1 _ (le_byte fn 4 0)); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (VFN 0%nat ltac:(lia))].
    * apply (chunk_ok_val SEGS E _ c 1 1 _ (le_byte fn 4 1)); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (VFN 1%nat ltac:(lia))].
    * apply (chunk_ok_val SEGS E _ c 2 1 _ (le_byte fn 4 2)); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (VFN 2%nat ltac:(lia))].
    * apply (chunk_ok_val SEGS E _ c 3 1 _ (le_byte fn 4 3)); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (VFN 3%nat ltac:(lia))].
    * apply (chunk_ok_val SEGS E _ c 4 4 _ na); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      unfold CALL_OFF_NARGS in VNA. exact VNA.
- apply pairwise_disjoint_of_extents.
  unfold mc_regions0, stack_region, got_regionP, bcell_regionP, mc_fnv_region, mc_c_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 11%nat c E11) by lia. rewrite (VB (A_OBJ 58) 0x10330 E299) by lia.
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold MIX_CALL_STK, ESTACK, A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *.
  rewrite val_A0, val_A12.
  revert Hslo Hshi H47 Hceil C1 Hstk0 Hc1 Hc2. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [mc_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E11, E32, E33, E34, E35, E36, E37, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold MIX_CALL_STK, ESTACK, A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *.
  revert Hslo Hshi H47 Hceil C1 Hstk0 Hal16 Hc1 Hc2 Hc8 Hna B0 B1 B2 B3. clear. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

(* g_rec and record.spill are two zero-shadow ranges of the record (lib/B/YF0m.v:4650-4651 Tfib_zero_shadow) *)
Lemma mc_rec_addr : forall ly S W mem md a n, AR SEGS B ly S W mem md ->
((A_G_REC <= a /\ a + n <= A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a /\ a + n <= A_REC_SPILL + SC_SIZE)) ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hr. unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hr.
destruct Hr as [Hr | Hr].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xad560, 0x5e3680 - 0xad560) a n HAR);
  [unfold Tfib_zero_shadow; repeat (first [apply in_eq | apply in_cons]) | reflexivity | reflexivity | cbn; lia | cbn; lia].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3760, 0x5e3798 - 0x5e3760) a n HAR);
  [unfold Tfib_zero_shadow; repeat (first [apply in_eq | apply in_cons]) | reflexivity | reflexivity | cbn; lia | cbn; lia].
Qed.
Lemma mc_slot_sub : forall c off n, mc_slot c -> 0 <= off -> off + n <= CALL_SIZE ->
(A_G_REC <= c + off /\ c + off + n <= A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= c + off /\ c + off + n <= A_REC_SPILL + SC_SIZE).
Proof.
intros c off n Hc H0 H1. destruct (mc_slot_range c Hc) as (_ & _ & _ & [[Ha Hb] | ->]);
unfold CALL_SIZE, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; [left | right]; lia.
Qed.

Lemma mc_obl_rd : forall E (W : world SEGS) m bx x a n, U E bx = SHADOW_OFF -> U E x = a ->
range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n ->
range_addressable (rd_of SEGS (mrestrict (w_H W) m)) (U E bx) (U E x) n.
Proof. intros E W m bx x a n Hb Hx Hr. rewrite Hb, Hx. exact Hr. Qed.

(* the loop invariant: the journal from the entry, the memory below alloc_ceiling as at the entry, and the twelve
   registers the prologue saved still in the frame *)
Definition mc_low (W : world SEGS) (m0 m : word -> option byte) : Prop :=
forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m0 a.
Definition mc_saved (W : world SEGS) (m : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 8) 8 (bv_unsigned (getr regs0 1)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 32) 8 (bv_unsigned (getr regs0 18)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 40) 8 (bv_unsigned (getr regs0 19)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 48) 8 (bv_unsigned (getr regs0 20)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 56) 8 (bv_unsigned (getr regs0 21)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 64) 8 (bv_unsigned (getr regs0 22)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 72) 8 (bv_unsigned (getr regs0 23)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 80) 8 (bv_unsigned (getr regs0 24)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 88) 8 (bv_unsigned (getr regs0 25)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 96) 8 (bv_unsigned (getr regs0 26)).
Definition mc_inv (ly : alayout) (S : astate) (W : world SEGS) (mem0 : word -> option byte) (md0 : Model)
(regs0 : bvmap 5 word) (m : word -> option byte) (md : Model) : Prop :=
ajournal SEGS B MIX_CALL_STK (spZ regs0) [] ly S W mem0 md0 [] ly S W m md 0 /\
mc_low W mem0 m /\ mc_saved W m (spZ regs0) regs0.

Lemma mbyte_eq_of_aview : forall H m m' a, aview SEGS H m' a = aview SEGS H m a ->
mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof.
intros H m m' a Ha. unfold aview in Ha.
destruct (mbyte SEGS (mrestrict H m') a) as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|]; cbn in Ha;
try discriminate; [|reflexivity]. injection Ha as Ha. f_equal. apply bv_eq. exact Ha.
Qed.
Lemma val_mem_kept_aview : forall H m m' a n v, (forall k, (k < n)%nat -> aview SEGS H m' (a + Z.of_nat k) = aview SEGS H m (a + Z.of_nat k)) ->
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof. intros H m m' a n v Hk Hv k Hlt. rewrite (mbyte_eq_of_aview H m m' _ (Hk k Hlt)). exact (Hv k Hlt). Qed.
Lemma mc_saved_kept : forall (W : world SEGS) m m' sp0 regs0, (forall a, sp0 - 96 <= a < sp0 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
mc_saved W m sp0 regs0 -> mc_saved W m' sp0 regs0.
Proof.
intros W m m' sp0 regs0 Hk (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12).
repeat split; (eapply val_mem_kept_aview; [|eassumption]); intros k Hk'; apply Hk; lia.
Qed.
Lemma mc_low_kept : forall (W : world SEGS) m0 m m', (forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
mc_low W m0 m -> mc_low W m0 m'.
Proof. intros W m0 m m' Hk Hl a Ha. rewrite (Hk a Ha). exact (Hl a Ha). Qed.
Lemma frame_of_nowin : forall E rs (m m' : word -> option byte),
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hw Hf x. apply Hf. intros (r & Hr & Ha).
pose proof (proj1 (forallb_forall _ _) Hw r Hr) as H. apply Z.leb_le in H. lia.
Qed.
Lemma aview_of_frame_nowin : forall E rs H m m',
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs (mrestrict H m) (mrestrict H m') ->
forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hw Hf a. unfold aview, mbyte. rewrite (frame_of_nowin E rs _ _ Hw Hf). reflexivity.
Qed.
Lemma mc_inv_run : forall ly S W mem0 md0 regs0 m md m' md' E rs,
mc_inv ly S W mem0 md0 regs0 m md ->
ajournal SEGS B MIX_CALL_STK (spZ regs0) [] ly S W mem0 md0 [] ly S W m' md' 0 ->
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
mc_inv ly S W mem0 md0 regs0 m' md'.
Proof.
intros ly S W mem0 md0 regs0 m md m' md' E rs (_ & HL & HSV) HJ Hf Hw.
pose proof (aview_of_frame_nowin E rs (w_H W) m m' Hw Hf) as HA.
split; [exact HJ|]. split; [apply (mc_low_kept W mem0 m m'); [intros; apply HA | exact HL]|].
apply (mc_saved_kept W m m'); [intros; apply HA | exact HSV].
Qed.

Lemma U_den : forall E v z, U E v = z -> 0 <= z < 2 ^ 64 -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z Hu Hz. unfold U in Hu. rewrite <- Hu. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma U_fnv_step : forall E v x y g b, U E v = g -> U E x = b -> U E y = FNV_P ->
U E (SMd M_MUL (SAlu ALU_XOR v x) y) = (Z.lxor g b * FNV_P) mod 2 ^ 64.
Proof.
intros E v x y g b Hv Hx Hy. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hv, Hx, Hy.
unfold zcanon, M64. rewrite Z.mul_mod_idemp_l by lia. reflexivity.
Qed.
Lemma fnv_word : forall (E : env) g b, 0 <= g < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
mul_div M_MUL (alu64 ALU_XOR (Z_to_bv 64 g) (Z_to_bv 64 b)) (Z_to_bv 64 FNV_P) = Z_to_bv 64 ((Z.lxor g b * FNV_P) mod 2 ^ 64).
Proof.
intros E g b Hg Hb.
change (mul_div M_MUL (alu64 ALU_XOR (Z_to_bv 64 g) (Z_to_bv 64 b)) (Z_to_bv 64 FNV_P))
with (sv_denot E (SMd M_MUL (SAlu ALU_XOR (SLit g) (SLit b)) (SLit FNV_P))).
apply U_den; [|apply Z.mod_pos_bound; lia].
apply U_fnv_step; apply U_lit; unfold FNV_P; lia.
Qed.
Lemma fnv_snoc : forall g l b, fnv g (l ++ [b]) = (Z.lxor (fnv g l) (bv_unsigned b) * FNV_P) mod 2 ^ 64.
Proof. intros g l b. rewrite fnv_app. reflexivity. Qed.
Lemma firstn_snoc_nth : forall (l : list byte) j, (j < length l)%nat ->
firstn (S j) l = firstn j l ++ [nth j l (Z_to_bv 8 0)].
Proof.
induction l as [|x l IH]; intros j Hj; cbn in Hj; [lia|].
destruct j as [|j]; [reflexivity|]. cbn [firstn nth app]. rewrite (IH j) by lia. reflexivity.
Qed.

Definition MC_KEPT : list (bv 5) := [2; 3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* the byte loop at 0x8ae9c: a0 = s1 = p + j, a1 = the n bytes left of the argument with its NUL, s0 the digest,
   s10 = 1 (the operand of the trap check 0x8aea0) *)
Definition mc_bBx : sv := SOff 18 0.
Definition mc_bl_region : YP09.region := YP09.mkRegion (Some 9%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition mc_bl_facts : facts :=
mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (9%nat, PTR 0); (10%nat, PTR 0); (18%nat, mkAF SB SB 0); (26%nat, mkAF 1 1 0);
         (32%nat, mkAF 0 255 0)] [] [].
Definition ss_bl : sstate := mkSS MC_BL sr_atoms [mc_bl_region] None mc_bl_facts.

Lemma mc_bytes : forall (n : nat) W ly S mem0 md0 regs0 regs memc mdc (p : Z) (l : list byte) (j g0 : Z) (pn : Z * Z),
Z.of_nat n = Z.of_nat (length l) - j -> 0 <= j -> (1 <= n)%nat ->
mc_inv ly S W mem0 md0 regs0 memc mdc ->
In pn (ablocks B ly S) -> fst pn = p -> Z.of_nat (length l) <= snd pn ->
abytes_atR (rdW W mem0) p l ->
getr regs 2 = w64 (spZ regs0 - 96) -> getr regs 18 = w64 SB -> getr regs 19 = w64 FNV_P -> getr regs 26 = w64 1 ->
getr regs 10 = w64 (p + j) -> getr regs 9 = w64 (p + j) -> getr regs 11 = w64 (Z.of_nat n) ->
getr regs 8 = w64 (fnv g0 (firstn (Z.to_nat j) l)) -> 0 <= g0 < 2 ^ 64 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + MC_BL)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + MC_INC)) mem' (seg_rom SEGS)) md' /\
mc_inv ly S W mem0 md0 regs0 mem' md' /\
(forall r, In r MC_KEPT -> getr regs' r = getr regs r) /\
getr regs' 8 = w64 (fnv g0 l)).
Proof.
induction n as [|n IH]; intros W ly S mem0 md0 regs0 regs memc mdc p l j g0 pn Hn Hj0 Hn1 HI Hpn Hp HL Hbytes
H2 H18 H19 H26 H10 H9 H11 H8 Hg0; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HI as (HJ & HLOW & HSV).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct pn as [pp m]. cbn [fst snd] in Hp, HL. subst pp.
destruct (al_blocks _ _ LAWS ly S W memc mdc p m HAR Hpn) as (Hp16 & Hp4096 & Hpceil & Hp_ia & Hppres & _).
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
set (bj := bv_unsigned (nth (Z.to_nat j) l (Z_to_bv 8 0))).
assert (Hbj : 0 <= bj < 256) by (subst bj; apply (bv_unsigned_in_range 8)).
assert (Hjl : (Z.to_nat j < length l)%nat) by lia.
assert (Rbj : aview SEGS (w_H W) memc (p + j) = Some bj).
{ rewrite (HLOW (p + j)) by lia. rewrite <- (Z2Nat.id j) at 1 by lia. apply Hbytes. exact Hjl. }
set (fj := fnv g0 (firstn (Z.to_nat j) l)) in *.
assert (Hfj : 0 <= fj < 2 ^ 64) by (subst fj; apply fnv_range; exact Hg0).
remember (Eimg (Ereg regs [Z_to_bv 64 bj])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 bj]) E) by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EN : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> ew E k = getr regs r).
{ intros k r Hk Hk32. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (E2 : ew E 2 = w64 (spZ regs0 - 96)) by (rewrite (EN 2%nat 2%bv eq_refl) by lia; exact H2).
assert (E8 : ew E 8 = w64 fj) by (rewrite (EN 8%nat 8%bv eq_refl) by lia; exact H8).
assert (E9 : ew E 9 = w64 (p + j)) by (rewrite (EN 9%nat 9%bv eq_refl) by lia; exact H9).
assert (E10 : ew E 10 = w64 (p + j)) by (rewrite (EN 10%nat 10%bv eq_refl) by lia; exact H10).
assert (E11 : ew E 11 = w64 (Z.of_nat (Datatypes.S n))) by (rewrite (EN 11%nat 11%bv eq_refl) by lia; exact H11).
assert (E18 : ew E 18 = w64 SB) by (rewrite (EN 18%nat 18%bv eq_refl) by lia; exact H18).
assert (E19 : ew E 19 = w64 FNV_P) by (rewrite (EN 19%nat 19%bv eq_refl) by lia; exact H19).
assert (E26 : ew E 26 = w64 1) by (rewrite (EN 26%nat 26%bv eq_refl) by lia; exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 bj) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
unfold MIX_CALL_STK, ESTACK in Hslo, Hstk0, Hbot.
assert (HS : st_ok_pi SEGS VAL E ss_bl (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + MC_BL)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_bl. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, mc_bl_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (p + j) 0 1 (SOff 32 0) bj); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  intros k Hk. replace k with 0%nat by lia. rewrite !Z.add_0_r. rewrite le_byte1 by exact Hbj.
  apply mbyte_of_aview; [exact Rbj | exact Hbj].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [mc_bl_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite E2, E9, E10, E18, E26, E32. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (Hm16 : (spZ regs0 - 96) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
  revert Hslo Hshi H47 Hceil C1 Hstk0 Hm16 Hp4096 Hpceil Hrq HL Hn Hj0 Hbj. clear. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
clear HE.
assert (SHOK : sh_ok SEGS mc_bBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HBx : U E mc_bBx = SHADOW_OFF) by (unfold mc_bBx; rewrite (U_atom E 18 SB E18) by (unfold SB; lia); reflexivity).
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem mkst]. apply (mc_obl_rd E W memc mc_bBx (SOff 10 0) (p + j) 1 HBx); [apply U_atom; [exact E10 | lia]|].
  apply (range_addressable_of_block SEGS B LAWS ly S W memc mdc p m (p + j) 1 HAR Hpn); lia. }
{ awr_ok_tac. }
pose proof (mc_inv_run ly S W mem0 md0 regs0 memc mdc (ms_mem ms) _ E [mc_bl_region] HI HJ HFr ltac:(vm_compute; reflexivity)) as HI1.
clear HF HFr HG.
assert (Hn0 : bv_unsigned (ew E 11) = Z.of_nat (Datatypes.S n)) by (rewrite E11; apply unsigned_lit_small; lia).
assert (Hfj1 : (Z.lxor fj bj * FNV_P) mod 2 ^ 64 = fnv g0 (firstn (Datatypes.S (Z.to_nat j)) l)).
{ rewrite (firstn_snoc_nth l (Z.to_nat j) Hjl), fnv_snoc. reflexivity. }
assert (R8f : forall (Ex : env) (ms2 : machine_state), getr (ms_regs ms2) 8 = mul_div M_MUL (alu64 ALU_XOR (ew E 8) (ew E 32)) (ew E 19) ->
  getr (ms_regs ms2) 8 = w64 (fnv g0 (firstn (Datatypes.S (Z.to_nat j)) l))).
{ intros Ex ms2 Hr. rewrite Hr, E8, E32, E19. unfold w64. rewrite (fnv_word Ex) by (unfold FNV_P in *; lia). rewrite Hfj1. reflexivity. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* another byte *)
  rewrite branch_ne_U in Hc. unfold U in Hc. cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite Hn0, !unsigned_lit_small in Hc by lia.
  assert (Hnn : (1 <= n)%nat) by (destruct (Z.eqb_spec (Z.of_nat (Datatypes.S n) + -1) 0); [discriminate | lia]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MC_BL.
  { awr_ok_tac. }
  pose proof (mc_inv_run ly S W mem0 md0 regs0 (ms_mem ms) _ (ms_mem ms0) _ _ _ HI1 HJ HFr ltac:(vm_compute; reflexivity)) as HI2.
  clear HI1 HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 bj]) Ecur) by (env_agree_chain HAE) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ MC_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
  apply (R8f E) in R8.
  rewrite E9 in R9. rewrite E10 in R10. rewrite E11 in R11. unfold w64 in R9, R10, R11. rewrite unsigned_lit_small in R9, R10, R11 by lia.
  pmkst HS.
  eapply SRr_mono.
  { eapply (IH W ly S mem0 md0 regs0 (ms_regs ms0) (ms_mem ms0) _ p l (j + 1) g0 (p, m));
    [ lia | lia | exact Hnn | exact HI2 | exact Hpn | reflexivity | exact HL | exact Hbytes
    | rewrite (HK 2%bv ltac:(cbv; tauto)); exact H2
    | rewrite (HK 18%bv ltac:(cbv; tauto)); exact H18
    | rewrite (HK 19%bv ltac:(cbv; tauto)); exact H19
    | rewrite (HK 26%bv ltac:(cbv; tauto)); exact H26
    | rewrite R10; unfold w64; f_equal; lia
    | rewrite R9; unfold w64; f_equal; lia
    | rewrite R11; unfold w64; f_equal; lia
    | rewrite R8; f_equal; f_equal; f_equal; lia
    | exact Hg0 ]. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HI3 & HK3 & H83).
  split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HI3|]. split; [|exact H83].
  intros r Hr. rewrite (HK3 r Hr). exact (HK r Hr).
- (* the NUL was the last byte *)
  rewrite branch_ne_U in Hc. unfold U in Hc. cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite Hn0, !unsigned_lit_small in Hc by lia.
  assert (Hn00 : n = 0%nat) by (destruct (Z.eqb_spec (Z.of_nat (Datatypes.S n) + -1) 0); [lia | discriminate]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MC_INC.
  { awr_ok_tac. }
  pose proof (mc_inv_run ly S W mem0 md0 regs0 (ms_mem ms) _ (ms_mem ms0) _ _ _ HI1 HJ HFr ltac:(vm_compute; reflexivity)) as HI2.
  clear HI1 HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 bj]) Ecur) by (env_agree_chain HAE) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ MC_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (8%bv : bv 5) R8. apply (R8f E) in R8.
  pmkst HS.
  apply SRr_ret. split; [reflexivity|].
  lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
  split; [reflexivity|]. split; [exact HI2|]. split; [exact HK|].
  rewrite R8. replace (Datatypes.S (Z.to_nat j)) with (length l) by lia. rewrite firstn_all. reflexivity.
Qed.

Lemma callee_saved_in : forall r, acallee_saved r -> In (Z_to_bv 5 r) CALLEE_SAVED.
Proof.
intros r Hr. unfold acallee_saved in Hr.
assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia. clear Hr.
destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
cbv [CALLEE_SAVED In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
Lemma aregs_preserved_of_list : forall regs regs', (forall r, In r CALLEE_SAVED -> getr regs' r = getr regs r) ->
aregs_preserved regs regs'.
Proof. intros regs regs' H r Hr. apply H. apply callee_saved_in. exact Hr. Qed.

(* what the call leaves: the digest in a0, and the allocator state as it was (no allocator call; strlen keeps S) *)
Definition mc_Q (ly : alayout) (S : astate) (W : world SEGS) (mem0 : word -> option byte) (sp0 res : Z) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 res /\ ly' = ly /\ S' = S /\
kept_out (aview SEGS (w_H W) mem0) (aview SEGS (w_H W') mem') (sp0 - MIX_CALL_STK) sp0.

(* the memory outside the call's stack window is the entry's, from the journal above alloc_ceiling and mc_low below *)
Lemma mc_kept_out : forall ly S W mem0 md0 regs0 m md, mc_inv ly S W mem0 md0 regs0 m md ->
kept_out (aview SEGS (w_H W) mem0) (aview SEGS (w_H W) m) (spZ regs0 - MIX_CALL_STK) (spZ regs0).
Proof.
intros ly S W mem0 md0 regs0 m md (HJ & HL & _) a Ha Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & Hhi & _).
destruct (Z_lt_le_dec a alloc_ceiling) as [Hlo | Hge]; [exact (HL a ltac:(lia))|].
apply Hhi; [lia | exact Hn | apply inFP_nil].
Qed.

(* the epilogue at 0x8aee0: a0 := s0, the twelve saved registers back from the frame, ret *)
Definition mc_epi_region : YP09.region := YP09.mkRegion (Some 2%nat) 0 96 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 43 0)); YP09.mkChunk 8 (CVal 8 (SOff 42 0)); YP09.mkChunk 16 (CVal 8 (SOff 41 0));
 YP09.mkChunk 24 (CVal 8 (SOff 40 0)); YP09.mkChunk 32 (CVal 8 (SOff 39 0)); YP09.mkChunk 40 (CVal 8 (SOff 38 0));
 YP09.mkChunk 48 (CVal 8 (SOff 37 0)); YP09.mkChunk 56 (CVal 8 (SOff 36 0)); YP09.mkChunk 64 (CVal 8 (SOff 35 0));
 YP09.mkChunk 72 (CVal 8 (SOff 34 0)); YP09.mkChunk 80 (CVal 8 (SOff 33 0)); YP09.mkChunk 88 (CVal 8 (SOff 32 0))].
Definition ss_epi : sstate := mkSS MC_EPI sr_atoms [mc_epi_region] None (mkFacts [(2%nat, mkAF (2^46) (2^47) 4)] [] []).
Definition mc_epi_extra (regs0 : bvmap 5 word) : list word :=
map (getr regs0) [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv.
Definition MC_K0 : list (bv 5) := [3; 4; 27]%bv.

Lemma mc_epi : forall W ly S mem0 md0 regs0 regs memc mdc res,
mc_inv ly S W mem0 md0 regs0 memc mdc ->
getr regs 2 = w64 (spZ regs0 - 96) -> getr regs 8 = w64 res -> 0 <= res < 2 ^ 64 ->
(forall r, In r MC_K0 -> getr regs r = getr regs0 r) ->
YK0s.ret_ok (getr regs0 1) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + MC_EPI)) memc (seg_rom SEGS)) mdc)
(apost_base SEGS B MIX_CALL_STK [] regs0 ly S W mem0 md0 EV_MIX_CALL (mc_Q ly S W mem0 (spZ regs0) res)).
Proof.
intros W ly S mem0 md0 regs0 regs memc mdc res HI H2 H8 Hres HK0 Hra.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HI as (HJ & HLOW & HSV).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold MIX_CALL_STK, ESTACK in Hslo, Hstk0, Hbot, Hpres.
remember (Eimg (Ereg regs (mc_epi_extra regs0))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (mc_epi_extra regs0)) E) by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EN : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> ew E k = getr regs r).
{ intros k r Hk Hk32. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (EX : forall j, (j < 12)%nat -> ew E (32 + j) = nth j (mc_epi_extra regs0) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = w64 (spZ regs0 - 96)) by (rewrite (EN 2%nat 2%bv eq_refl) by lia; exact H2).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 96) by (rewrite E2; apply unsigned_lit_small; lia).
pose proof HSV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12).
assert (CK : forall (j : nat) (r : bv 5) off, (j < 12)%nat -> nth j (mc_epi_extra regs0) (Z_to_bv 64 0) = getr regs0 r ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs0 - 96 + off) 8 (bv_unsigned (getr regs0 r)) ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) memc) (spZ regs0 - 96) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hj Hn Hv. apply (chunk_ok_val SEGS E _ _ off 8 _ (bv_unsigned (getr regs0 r)));
  [cbn [sv_denot]; rewrite (EX j Hj), Hn, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity | apply (bv_unsigned_in_range 64) | zside | exact Hv]. }
assert (HS : st_ok_pi SEGS VAL E ss_epi (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + MC_EPI)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, mc_epi_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (CK 11%nat 26%bv 0); [lia | reflexivity | replace (spZ regs0 - 96 + 0) with (spZ regs0 - 96) by lia; exact S12].
  + apply (CK 10%nat 25%bv 8); [lia | reflexivity | replace (spZ regs0 - 96 + 8) with (spZ regs0 - 88) by lia; exact S11].
  + apply (CK 9%nat 24%bv 16); [lia | reflexivity | replace (spZ regs0 - 96 + 16) with (spZ regs0 - 80) by lia; exact S10].
  + apply (CK 8%nat 23%bv 24); [lia | reflexivity | replace (spZ regs0 - 96 + 24) with (spZ regs0 - 72) by lia; exact S9].
  + apply (CK 7%nat 22%bv 32); [lia | reflexivity | replace (spZ regs0 - 96 + 32) with (spZ regs0 - 64) by lia; exact S8].
  + apply (CK 6%nat 21%bv 40); [lia | reflexivity | replace (spZ regs0 - 96 + 40) with (spZ regs0 - 56) by lia; exact S7].
  + apply (CK 5%nat 20%bv 48); [lia | reflexivity | replace (spZ regs0 - 96 + 48) with (spZ regs0 - 48) by lia; exact S6].
  + apply (CK 4%nat 19%bv 56); [lia | reflexivity | replace (spZ regs0 - 96 + 56) with (spZ regs0 - 40) by lia; exact S5].
  + apply (CK 3%nat 18%bv 64); [lia | reflexivity | replace (spZ regs0 - 96 + 64) with (spZ regs0 - 32) by lia; exact S4].
  + apply (CK 2%nat 9%bv 72); [lia | reflexivity | replace (spZ regs0 - 96 + 72) with (spZ regs0 - 24) by lia; exact S3].
  + apply (CK 1%nat 8%bv 80); [lia | reflexivity | replace (spZ regs0 - 96 + 80) with (spZ regs0 - 16) by lia; exact S2].
  + apply (CK 0%nat 1%bv 88); [lia | reflexivity | replace (spZ regs0 - 96 + 88) with (spZ regs0 - 8) by lia; exact S1].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16.
  assert (Hm16 : (spZ regs0 - 96) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
  revert Hslo Hshi H47 Hceil C1 Hstk0 Hm16. clear. intros. repeat match goal with |- _ /\ _ => split end; lia. }
clear HE.
assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W) memc)) by constructor.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
assert (EV : forall j r, (j < 12)%nat -> nth j (mc_epi_extra regs0) (Z_to_bv 64 0) = getr regs0 r -> ew E (32 + j) = getr regs0 r).
{ intros j r Hj Hn. rewrite (EX j Hj). exact Hn. }
pose proof (EV 0%nat 1%bv ltac:(lia) eq_refl) as X32. pose proof (EV 1%nat 8%bv ltac:(lia) eq_refl) as X33.
pose proof (EV 2%nat 9%bv ltac:(lia) eq_refl) as X34. pose proof (EV 3%nat 18%bv ltac:(lia) eq_refl) as X35.
pose proof (EV 4%nat 19%bv ltac:(lia) eq_refl) as X36. pose proof (EV 5%nat 20%bv ltac:(lia) eq_refl) as X37.
pose proof (EV 6%nat 21%bv ltac:(lia) eq_refl) as X38. pose proof (EV 7%nat 22%bv ltac:(lia) eq_refl) as X39.
pose proof (EV 8%nat 23%bv ltac:(lia) eq_refl) as X40. pose proof (EV 9%nat 24%bv ltac:(lia) eq_refl) as X41.
pose proof (EV 10%nat 25%bv ltac:(lia) eq_refl) as X42. pose proof (EV 11%nat 26%bv ltac:(lia) eq_refl) as X43.
cbn [Nat.add] in X32, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43.
assert (F : forall r, In r CALLEE_SAVED -> getr (ms_regs ms) r = getr regs0 r).
{ intros r Hr. cbv [CALLEE_SAVED In] in Hr.
  repeat (destruct Hr as [<- | Hr];
  [ lazymatch goal with |- getr _ ?rr = _ => let H := fresh "H" in prreg HS rr H; rewrite H end;
    first [ rewrite Usp; replace (spZ regs0 - 96 + 96) with (spZ regs0) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
          | exact X33 | exact X34 | exact X35 | exact X36 | exact X37 | exact X38 | exact X39 | exact X40
          | exact X41 | exact X42 | exact X43
          | lazymatch goal with |- ew E ?k = getr regs0 ?rr => rewrite (EN k rr eq_refl) by lia; apply HK0; cbv; tauto end ]
  | ]); destruct Hr. }
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split; [cbn [ms_regs]; rewrite R1, X32, Hra; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
split; [apply aregs_preserved_of_list; exact F|].
split; [cbn [ms_regs]; rewrite R10, (EN 8%nat 8%bv eq_refl) by lia; exact H8|]. split; [reflexivity|]. split; [reflexivity|].
apply (mc_kept_out ly S W mem0 md0 regs0 _ _ (mc_inv_run ly S W mem0 md0 regs0 memc mdc (ms_mem ms) _ E _ HI HJ HFr ltac:(vm_compute; reflexivity))).
Qed.

Definition mixf (g : Z) (s : list byte) : Z := mix g (s ++ [Z_to_bv 8 0]).

(* back from strlen at 0x8ae78: s0 := basis when 0, a1 := len + 1, a0 := s1, into the byte loop *)
Definition ss_len : sstate := mkSS MC_LEN sr_atoms [] None
(mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (9%nat, PTR 4); (10%nat, mkAF 0 (LMAX + 1) 0); (18%nat, mkAF SB SB 0)] [] []).

Lemma mc_len : forall W ly S mem0 md0 regs0 regs memc mdc p s pk g,
mc_inv ly S W mem0 md0 regs0 memc mdc ->
In (p, pk) (ablocks B ly S) -> Z.of_nat (length s) + 1 <= pk -> Z.of_nat (length s) <= LMAX + 1 ->
astr_atR (rdW W mem0) p s ->
getr regs 2 = w64 (spZ regs0 - 96) -> getr regs 18 = w64 SB -> getr regs 19 = w64 FNV_P -> getr regs 22 = w64 FNV_B0 ->
getr regs 26 = w64 1 ->
getr regs 10 = w64 (Z.of_nat (length s)) -> getr regs 9 = w64 p -> getr regs 8 = w64 g -> 0 <= g < 2 ^ 64 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + MC_LEN)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + MC_INC)) mem' (seg_rom SEGS)) md' /\
mc_inv ly S W mem0 md0 regs0 mem' md' /\
(forall r, In r MC_KEPT -> getr regs' r = getr regs r) /\
getr regs' 8 = w64 (mixf g s)).
Proof.
intros W ly S mem0 md0 regs0 regs memc mdc p s pk g HI Hpin Hpk HL HSTR H2 H18 H19 H22 H26 H10 H9 H8 Hg.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HI as (HJ & HLOW & HSV).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold MIX_CALL_STK, ESTACK in Hslo, Hstk0, Hbot.
destruct (al_blocks _ _ LAWS ly S W memc mdc p pk HAR Hpin) as (Hp16 & Hp4096 & Hpceil & Hp_ia & Hppres & _).
assert (Hrq : req_size pk = pk) by (unfold req_size; destruct (Z.eqb_spec pk 0); lia).
remember (Eimg (Ereg regs [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EN : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> (k0 < 32)%nat -> ew E k0 = getr regs r).
{ intros k0 r Hk0 Hk32. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk0. }
assert (E2 : ew E 2 = w64 (spZ regs0 - 96)) by (rewrite (EN 2%nat 2%bv eq_refl) by lia; exact H2).
assert (E8 : ew E 8 = w64 g) by (rewrite (EN 8%nat 8%bv eq_refl) by lia; exact H8).
assert (E9 : ew E 9 = w64 p) by (rewrite (EN 9%nat 9%bv eq_refl) by lia; exact H9).
assert (E10 : ew E 10 = w64 (Z.of_nat (length s))) by (rewrite (EN 10%nat 10%bv eq_refl) by lia; exact H10).
assert (E18 : ew E 18 = w64 SB) by (rewrite (EN 18%nat 18%bv eq_refl) by lia; exact H18).
assert (E22 : ew E 22 = w64 FNV_B0) by (rewrite (EN 22%nat 22%bv eq_refl) by lia; exact H22).
assert (HS : st_ok_pi SEGS VAL E ss_len (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + MC_LEN)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_len. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint]. exact I.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite E2, E9, E10, E18. unfold w64. rewrite !unsigned_lit_small by (unfold SB, LMAX in *; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (Hm16 : (spZ regs0 - 96) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
  revert Hslo Hshi H47 Hceil C1 Hstk0 Hm16 Hp16 Hp4096 Hpceil Hrq Hpk HL. clear. unfold SB, LMAX. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
clear HE.
assert (SHOK : sh_ok SEGS mc_bBx [] E (mrestrict (w_H W) memc)) by constructor.
set (gg := if g =? 0 then FNV_B0 else g).
assert (Hgg : 0 <= gg < 2 ^ 64) by (subst gg; destruct (g =? 0); unfold FNV_B0; lia).
assert (Hmix : mixf g s = fnv gg (s ++ [Z_to_bv 8 0])) by reflexivity.
assert (Hlen : Z.of_nat (length (s ++ [Z_to_bv 8 0])) = Z.of_nat (length s) + 1) by (rewrite length_app; cbn [length]; lia).
assert (Hbytes : abytes_atR (rdW W mem0) p (s ++ [Z_to_bv 8 0])) by exact (proj1 HSTR).
psrr_branch_tok RUN BR HS SHOK Bspan.
all: rewrite branch_ne_U in Hc; unfold U in Hc; cbn [sv_denot] in Hc; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E8 in Hc;
  unfold w64 in Hc; rewrite !unsigned_lit_small in Hc by lia.
all: paj_run_to_tok RUNTO HS HJ SHOK Bspan MC_BL; [awr_ok_tac|].
all: pose proof (mc_inv_run ly S W mem0 md0 regs0 memc mdc (ms_mem ms) _ E [] HI HJ HFr ltac:(vm_compute; reflexivity)) as HI1.
all: clear HF HFr HG.
all: lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => assert (HAE2 : env_agree 32 (Ereg regs []) Ecur) by (env_agree_chain HAE) end.
all: pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ MC_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK.
all: prreg HS (8%bv : bv 5) R8; prreg HS (9%bv : bv 5) R9; prreg HS (10%bv : bv 5) R10; prreg HS (11%bv : bv 5) R11.
all: assert (R8g : getr (ms_regs ms) 8 = w64 gg) by
  (rewrite R8; subst gg; destruct (Z.eqb_spec g 0); cbn [negb] in Hc; first [discriminate | exact E8 | exact E22]).
all: pmkst HS.
all: eapply SRr_mono; [eapply (mc_bytes (Datatypes.S (length s)) W ly S mem0 md0 regs0 (ms_regs ms) (ms_mem ms) _ p
    (s ++ [Z_to_bv 8 0]) 0 gg (p, pk));
  [ rewrite Hlen; lia | lia | lia | exact HI1 | exact Hpin | reflexivity | cbn [snd]; rewrite Hlen; lia | exact Hbytes
  | rewrite (HK 2%bv ltac:(cbv; tauto)); exact H2
  | rewrite (HK 18%bv ltac:(cbv; tauto)); exact H18
  | rewrite (HK 19%bv ltac:(cbv; tauto)); exact H19
  | rewrite (HK 26%bv ltac:(cbv; tauto)); exact H26
  | rewrite R10, E9; unfold w64; f_equal; lia
  | rewrite R9, E9; unfold w64; f_equal; lia
  | rewrite R11, E10; unfold w64; rewrite unsigned_lit_small by (unfold LMAX in *; lia); f_equal; lia
  | rewrite R8g; reflexivity
  | exact Hgg ] |].
all: cbv beta; intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HI3 & HK3 & H83).
all: split; [reflexivity|]; exists regs3, mem3, md3; split; [reflexivity|]; split; [exact HI3|]; split;
  [intros r Hr; rewrite (HK3 r Hr); exact (HK r Hr) | rewrite H83, Hmix; reflexivity].
Qed.

Lemma preserved_at : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. specialize (H (bv_unsigned r) Hr). rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.

(* the INT_MAX and slot-overflow checks of the argument loop: 0x8ae88 compares a with s9 = 0x7fffffff,
   0x8ae54 compares s7 = ~(c + 8) with 8 a *)
Definition MC_NOTC (c : Z) : Z := 2 ^ 64 - 1 - (c + 8).
Lemma mc_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (Z.ones 64) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx.
assert (H1 : 2 ^ 64 - 1 - x = (Z.lnot x) mod 2 ^ 64).
{ unfold Z.lnot. apply Z.mod_unique with (q := -1); lia. }
rewrite H1. apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec.
destruct (Z.lt_ge_cases i 64) as [Hlt | Hge].
- rewrite Z.mod_pow2_bits_low, Z.lnot_spec, Z.ones_spec_low by lia. destruct (Z.testbit x i); reflexivity.
- rewrite Z.mod_pow2_bits_high, Z.ones_spec_high by lia.
  assert (Hb : Z.testbit x i = false).
  { rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
  rewrite Hb. reflexivity.
Qed.
(* s7 := ~s5 at 0x8ae40 *)
Lemma mc_not_word : forall (E : env) c, 0 <= c + 8 < 2 ^ 64 ->
alu64 ALU_XOR (Z_to_bv 64 (c + 8)) (Z_to_bv 64 (-1)) = w64 (MC_NOTC c).
Proof.
intros E c Hc. unfold w64, MC_NOTC.
change (alu64 ALU_XOR (Z_to_bv 64 (c + 8)) (Z_to_bv 64 (-1))) with (sv_denot E (SAlu ALU_XOR (SLit (c + 8)) (SLit (-1)))).
apply U_den; [|lia].
rewrite U_SAlu, !U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small (c + 8)) by lia. replace ((-1) mod 2 ^ 64) with (Z.ones 64) by reflexivity.
rewrite mc_lxor_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma slot_addr_word : forall (E : env) a c, 0 <= a <= 5 -> 0 <= c < 2 ^ 40 ->
alu64 ALU_ADD (alu64 ALU_ADD (alu64 ALU_SLL (w64 a) (Z_to_bv 64 3)) (Z_to_bv 64 8)) (w64 (c + 8)) = w64 (c + 8 + 8 * (a + 1)).
Proof.
intros E a c Ha Hc.
change (alu64 ALU_ADD (alu64 ALU_ADD (alu64 ALU_SLL (w64 a) (Z_to_bv 64 3)) (Z_to_bv 64 8)) (w64 (c + 8)))
with (sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SLit a) (SLit 3)) (SLit 8)) (SLit (c + 8)))).
apply U_den; [|lia].
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_lit by lia. change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia.
unfold zcanon, M64.
rewrite (Z.mod_small (a * 2 ^ 3) (2 ^ 64)) by lia. rewrite (Z.mod_small (a * 2 ^ 3 + 8) (2 ^ 64)) by lia.
rewrite (Z.mod_small (a * 2 ^ 3 + 8 + (c + 8)) (2 ^ 64)) by lia. lia.
Qed.
Definition MC_KEPTI : list (bv 5) := [2; 3; 4; 8; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition ss_inc : sstate := mkSS MC_INC sr_atoms [] None
(mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (20%nat, mkAF 0 5 0); (21%nat, mkAF (A_G_REC + 8) (A_REC_SPILL + 8) 0);
          (23%nat, mkAF (MC_NOTC A_REC_SPILL) (MC_NOTC A_G_REC) 0); (24%nat, mkAF 1 6 0); (25%nat, mkAF 0x7fffffff 0x7fffffff 0)] [] []).

Lemma mc_inc : forall W ly S mem0 md0 regs0 regs memc mdc (a na c : Z) (Q : world SEGS -> config -> Prop),
mc_inv ly S W mem0 md0 regs0 memc mdc ->
0 <= a < na -> na <= 6 -> A_G_REC <= c <= A_REC_SPILL ->
getr regs 2 = w64 (spZ regs0 - 96) -> getr regs 20 = w64 a -> getr regs 21 = w64 (c + 8) ->
getr regs 23 = w64 (MC_NOTC c) -> getr regs 24 = w64 na -> getr regs 25 = w64 0x7fffffff ->
(a + 1 < na -> forall regs' memc' mdc', mc_inv ly S W mem0 md0 regs0 memc' mdc' ->
  getr regs' 20 = w64 (a + 1) -> getr regs' 10 = w64 (c + 8 + 8 * (a + 1)) ->
  (forall r, In r MC_KEPTI -> getr regs' r = getr regs r) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + MC_A)) memc' (seg_rom SEGS)) mdc') Q) ->
(a + 1 = na -> forall regs' memc' mdc', mc_inv ly S W mem0 md0 regs0 memc' mdc' ->
  (forall r, In r MC_KEPTI -> getr regs' r = getr regs r) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + MC_EPI)) memc' (seg_rom SEGS)) mdc') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + MC_INC)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros W ly S mem0 md0 regs0 regs memc mdc a na c Q HI Ha Hna Hcb H2 H20 H21 H23 H24 H25 HNEXT HLAST.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HI as (HJ & HLOW & HSV).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold MIX_CALL_STK, ESTACK in Hslo, Hstk0, Hbot. unfold A_G_REC, A_REC_SPILL in Hcb.
remember (Eimg (Ereg regs [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EN : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> (k0 < 32)%nat -> ew E k0 = getr regs r).
{ intros k0 r Hk0 Hk32. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk0. }
assert (E2 : ew E 2 = w64 (spZ regs0 - 96)) by (rewrite (EN 2%nat 2%bv eq_refl) by lia; exact H2).
assert (E20 : ew E 20 = w64 a) by (rewrite (EN 20%nat 20%bv eq_refl) by lia; exact H20).
assert (E21 : ew E 21 = w64 (c + 8)) by (rewrite (EN 21%nat 21%bv eq_refl) by lia; exact H21).
assert (E23 : ew E 23 = w64 (MC_NOTC c)) by (rewrite (EN 23%nat 23%bv eq_refl) by lia; exact H23).
assert (E24 : ew E 24 = w64 na) by (rewrite (EN 24%nat 24%bv eq_refl) by lia; exact H24).
assert (E25 : ew E 25 = w64 0x7fffffff) by (rewrite (EN 25%nat 25%bv eq_refl) by lia; exact H25).
assert (HS : st_ok_pi SEGS VAL E ss_inc (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + MC_INC)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_inc. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint]. exact I.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E20, E21, E23, E24, E25. unfold w64, MC_NOTC, A_G_REC, A_REC_SPILL. rewrite !unsigned_lit_small by lia.
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (Hm16 : (spZ regs0 - 96) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
  revert Hslo Hshi H47 Hceil C1 Hstk0 Hm16 Ha Hna Hcb. clear. intros. repeat match goal with |- _ /\ _ => split end; lia. }
clear HE.
assert (SHOK : sh_ok SEGS mc_bBx [] E (mrestrict (w_H W) memc)) by constructor.
paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac|].
pose proof (mc_inv_run ly S W mem0 md0 regs0 memc mdc (ms_mem ms) _ E [] HI HJ HFr ltac:(vm_compute; reflexivity)) as HI1.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
all: rewrite branch_eq_U, (U_atom_off E 20 a 1 E20), (U_atom E 24 na E24) in Hc by lia.
- assert (Heq : a + 1 = na) by (destruct (Z.eqb_spec (a + 1) na); [lia | discriminate]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MC_EPI; [awr_ok_tac|].
  pose proof (mc_inv_run ly S W mem0 md0 regs0 (ms_mem ms) _ (ms_mem ms0) _ _ _ HI1 HJ HFr ltac:(vm_compute; reflexivity)) as HI2.
  clear HI1 HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => assert (HAE2 : env_agree 32 (Ereg regs []) Ecur) by (env_agree_chain HAE) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ MC_KEPTI HS HAE2 ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  pmkst HS.
  exact (HLAST Heq (ms_regs ms0) (ms_mem ms0) _ HI2 HK).
- assert (Hlt : a + 1 < na) by (destruct (Z.eqb_spec (a + 1) na); [discriminate | lia]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MC_A; [awr_ok_tac|].
  pose proof (mc_inv_run ly S W mem0 md0 regs0 (ms_mem ms) _ (ms_mem ms0) _ _ _ HI1 HJ HFr ltac:(vm_compute; reflexivity)) as HI2.
  clear HI1 HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => assert (HAE2 : env_agree 32 (Ereg regs []) Ecur) by (env_agree_chain HAE) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ MC_KEPTI HS HAE2 ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) R10. prreg HS (20%bv : bv 5) R20.
  assert (R10' : getr (ms_regs ms0) 10 = w64 (c + 8 + 8 * (a + 1))).
  { rewrite R10, E20, E21. apply (slot_addr_word E a c); unfold A_G_REC, A_REC_SPILL in *; lia. }
  assert (R20' : getr (ms_regs ms0) 20 = w64 (a + 1)) by (rewrite R20, E20; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  pmkst HS.
  exact (HNEXT Hlt (ms_regs ms0) (ms_mem ms0) _ HI2 R20' R10' HK).
Qed.

(* the argument loop at 0x8ae5c, a0 = &c->args[a] *)
Definition mc_a_region : YP09.region := YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition mc_a_facts : facts :=
mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF A_G_REC (A_REC_SPILL + SC_SIZE) 3); (18%nat, mkAF SB SB 0); (32%nat, PTR 4)] [] [].
Definition ss_a : sstate := mkSS MC_A sr_atoms [mc_a_region] None mc_a_facts.
Definition MC_KEPTA : list (bv 5) := [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma mc_args : forall (k : nat) W ly S mem0 md0 regs0 regs memc mdc c e P (a g res : Z),
Z.of_nat k = Z.of_nat (length (snd e)) - a -> 0 <= a -> (1 <= k)%nat ->
mc_inv ly S W mem0 md0 regs0 memc mdc ->
mc_slot c -> acall_at (ablocks B ly S) (rdW W mem0) c e P ->
rt_rom_view SEGS B W mem0 ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 3 = w64 (as_gp B) -> getr regs0 4 = w64 (as_tp B) ->
getr regs 2 = w64 (spZ regs0 - 96) -> (forall r, In r MC_K0 -> getr regs r = getr regs0 r) ->
getr regs 18 = w64 SB -> getr regs 19 = w64 FNV_P -> getr regs 20 = w64 a -> getr regs 21 = w64 (c + 8) ->
getr regs 22 = w64 FNV_B0 -> getr regs 23 = w64 (MC_NOTC c) -> getr regs 24 = w64 (Z.of_nat (length (snd e))) ->
getr regs 25 = w64 0x7fffffff -> getr regs 26 = w64 1 -> getr regs 10 = w64 (c + 8 + 8 * a) ->
getr regs 8 = w64 g -> 0 <= g < 2 ^ 64 ->
res = fold_left mixf (skipn (Z.to_nat a) (snd e)) g ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + MC_A)) memc (seg_rom SEGS)) mdc)
(apost_base SEGS B MIX_CALL_STK [] regs0 ly S W mem0 md0 EV_MIX_CALL (mc_Q ly S W mem0 (spZ regs0) res)).
Proof.
induction k as [|k IH]; intros W ly S mem0 md0 regs0 regs memc mdc c e P a g res Hk Ha0 Hk1 HI Hc HCA HROM Hra0 Hgp0 Htp0
H2 HK0 H18 H19 H20 H21 H22 H23 H24 H25 H26 H10 H8 Hg Hres; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HI as (HJ & HLOW & HSV).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold MIX_CALL_STK, ESTACK in Hslo, Hstk0, Hbot.
pose proof (mc_slot_range c Hc) as (Hc1 & Hc2 & Hc8 & _).
unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE in Hc1, Hc2.
pose proof HCA as (Hfn & Hna6 & HlenP & Mfn & Mna & HND & HARG).
set (na := Z.of_nat (length (snd e))) in *.
assert (Ha : (Z.to_nat a < length (snd e))%nat) by lia.
destruct (nth_error (snd e) (Z.to_nat a)) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
destruct (nth_error P (Z.to_nat a)) as [[p pk]|] eqn:HPa; [|apply nth_error_None in HPa; lia].
destruct (HARG (Z.to_nat a) s (p, pk) Hs HPa) as (Mq & Hp0 & Hpin & Hpk & HSTR0). cbn [fst snd] in Mq, Hp0, Hpk.
destruct (al_blocks _ _ LAWS ly S W memc mdc p pk HAR Hpin) as (Hp16 & Hp4096 & Hpceil & Hp_ia & Hppres & _).
assert (Hrq : req_size pk = pk) by (unfold req_size; destruct (Z.eqb_spec pk 0); lia).
set (q := c + 8 + 8 * a) in *.
assert (Hq : q = c + CALL_OFF_ARGS + 8 * Z.of_nat (Z.to_nat a)) by (subst q; unfold CALL_OFF_ARGS; lia).
assert (Rq : aval_mem (rdW W memc) q 8 p).
{ intros i Hi. rewrite (HLOW (q + Z.of_nat i)) by (subst q; lia). rewrite Hq. exact (Mq i Hi). }
assert (Hna : 0 <= na <= 6) by (subst na; lia).
remember (Eimg (Ereg regs [Z_to_bv 64 p])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 p]) E) by (rewrite HE; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EN : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> (k0 < 32)%nat -> ew E k0 = getr regs r).
{ intros k0 r Hk0 Hk32. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk0. }
assert (E2 : ew E 2 = w64 (spZ regs0 - 96)) by (rewrite (EN 2%nat 2%bv eq_refl) by lia; exact H2).
assert (E10 : ew E 10 = w64 q) by (rewrite (EN 10%nat 10%bv eq_refl) by lia; exact H10).
assert (E18 : ew E 18 = w64 SB) by (rewrite (EN 18%nat 18%bv eq_refl) by lia; exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HS : st_ok_pi SEGS VAL E ss_a (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + MC_A)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_a. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, mc_a_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E10. unfold w64. rewrite unsigned_lit_small by (subst q; lia).
  split; [subst q; lia|]. split; [subst q; lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside |].
  rewrite Z.add_0_r. apply (CmdRecRest.val_mem_of_aval SEGS). exact Rq.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [mc_a_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite E2, E10, E18, E32. unfold w64. rewrite !unsigned_lit_small by (subst q; unfold SB; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (Hm16 : (spZ regs0 - 96) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
  assert (Hq8 : q mod 8 = 0) by (subst q; rewrite <- Z.add_assoc, Z.add_mod, Hc8 by lia; rewrite (Z.add_mod 8 (8 * a)) by lia;
    rewrite (Z.mul_comm 8 a), Z_mod_mult; reflexivity).
  assert (Hp16' : p mod 16 = 0) by exact Hp16.
  unfold A_G_REC, A_REC_SPILL, SC_SIZE.
  subst q. revert Hslo Hshi H47 Hceil C1 Hstk0 Hm16 Hq8 Hp16' Hp4096 Hpceil Hrq Hpk Hc1 Hc2 Ha0 Hna Hk. clear. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
clear HE.
assert (SHOK : sh_ok SEGS mc_bBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HBx : U E mc_bBx = SHADOW_OFF) by (unfold mc_bBx; rewrite (U_atom E 18 SB E18) by (unfold SB; lia); reflexivity).
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem mkst]. apply (mc_obl_rd E W memc mc_bBx (SOff 10 0) q 8 HBx); [apply U_atom; [exact E10 | subst q; lia]|].
  apply (mc_rec_addr ly S W memc mdc q 8 HAR). subst q. replace (c + 8 + 8 * a) with (c + (8 + 8 * a)) by lia.
  apply mc_slot_sub; [exact Hc | lia | unfold CALL_SIZE; lia]. }
{ awr_ok_tac. }
pose proof (mc_inv_run ly S W mem0 md0 regs0 memc mdc (ms_mem ms) _ E [mc_a_region] HI HJ HFr ltac:(vm_compute; reflexivity)) as HI1.
clear HF HFr HG.
pose proof HI1 as (_ & HLOW1 & HSV1).
pose proof (proj1 HJ) as HAR1.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite E32 in R10. rewrite E2 in R2.
rewrite (EN 3%nat 3%bv eq_refl), (HK0 3%bv ltac:(cbv; tauto)), Hgp0 in R3 by lia.
rewrite (EN 4%nat 4%bv eq_refl), (HK0 4%bv ltac:(cbv; tauto)), Htp0 in R4 by lia.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs0 + -96) by (unfold spZ at 1; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hraw : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hlen0 : Z.of_nat (length s) + 1 <= pk) by lia.
lazymatch type of HS with st_ok _ ?Ecur _ _ => assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 p]) Ecur) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs _ MC_KEPTA HS HAEc ltac:(vm_compute; reflexivity)) as KA. cbn [ms_regs restrict] in KA.
prreg HS (9%bv : bv 5) R9. rewrite E32 in R9.
pmkst HS.
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low ENV ESTACK (fun _ => False) (SIGMA CS___interceptor_trampoline_strlen)
    W (ms_regs ms) (ms_mem ms) MIX_CALL_STK (spZ regs0) [] ly S W mem0 md0 [] ly S _ 0 (-96) (getr (ms_regs ms) 1)
    (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 (astr_len s)) HJ).
  1: exact Hsp1. 1: reflexivity. 1: lia. 1: unfold ESTACK; lia. 1: unfold MIX_CALL_STK, ESTACK; lia. 1: reflexivity. 1: intros a' [].
  eapply (ASTRLEN fx ly S W (ms_regs ms) (ms_mem ms) _ p s).
  - eapply (ecall_pre_stk_at SEGS B ESTACK MIX_CALL_STK (spZ regs0) [] ly S W mem0 md0 [] ly S W (ms_mem ms) _ 0 (ms_regs ms) (-96) HJ);
    [exact Hsp1 | reflexivity | lia | lia | unfold MIX_CALL_STK, ESTACK; lia | exact Hraw | exact R3 | exact R4].
  - exact R10.
  - lia.
  - apply astr_atR_view. destruct HSTR0 as [HS1 HS2]. split; [|exact HS2].
    intros i Hi. rewrite (HLOW1 (p + Z.of_nat i)); [exact (HS1 i Hi)|].
    rewrite length_app in Hi. cbn [length] in Hi. lia.
  - apply (aread_ok_of_block SEGS B LAWS ESTACK ly S W (ms_regs ms) (ms_mem ms) _ p pk p (astr_len s + 1) HAR1 Hpin);
    unfold astr_len; [lia | lia | lia | rewrite Hsp1; unfold ESTACK; lia].
  - apply (cmd_heap_tail_vis SEGS B LAWS HB ly S W (ms_mem ms) _ p pk (p + astr_len s) HAR1 Hpin). unfold astr_len. rewrite Hrq. lia.
  - exact (rt_rom_view_low W mem0 (ms_mem ms) HLOW1 HROM). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha2 & Hfr2).
rewrite R1.
assert (HI2 : mc_inv ly S W mem0 md0 regs0 mem2 md2).
{ split; [exact HJ2|]. unfold ESTACK in Hfr2. split.
  - apply (mc_low_kept W mem0 (ms_mem ms) mem2); [|exact HLOW1]. intros a' Ha'. apply Hfr2; [lia | lia | intros []].
  - apply (mc_saved_kept W (ms_mem ms) mem2); [|exact HSV1]. intros a' Ha'. apply Hfr2; [lia | lia | intros []]. }
assert (P2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r)
  by (intros r Hr; apply (preserved_at _ _ r HP2 Hr)).
assert (CH2 : forall r, In r MC_KEPT -> getr regs2 r = getr regs r).
{ intros r Hr. cbv [MC_KEPT In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [rewrite P2 by callee_ok; apply KA; cbv; tauto|]). destruct Hr. }
assert (H82 : getr regs2 8 = w64 g) by (rewrite P2 by callee_ok; rewrite KA by (cbv; tauto); exact H8).
assert (H92 : getr regs2 9 = w64 p) by (rewrite P2 by callee_ok; exact R9).
eapply SRr_bind.
{ eapply (mc_len W ly S mem0 md0 regs0 regs2 mem2 md2 p s pk g HI2 Hpin Hlen0 ltac:(unfold LMAX in *; lia) HSTR0);
  [ rewrite (CH2 2%bv) by (cbv; tauto); exact H2
  | rewrite (CH2 18%bv) by (cbv; tauto); exact H18
  | rewrite (CH2 19%bv) by (cbv; tauto); exact H19
  | rewrite (CH2 22%bv) by (cbv; tauto); exact H22
  | rewrite (CH2 26%bv) by (cbv; tauto); exact H26
  | exact Ha2 | exact H92 | exact H82 | exact Hg ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HI3 & HK3 & H83).
assert (CH3 : forall r, In r MC_KEPT -> getr regs3 r = getr regs r) by (intros r Hr; rewrite (HK3 r Hr); exact (CH2 r Hr)).
assert (Hmr : 0 <= mixf g s < 2 ^ 64) by (unfold mixf, mix; apply fnv_range; destruct (g =? 0); unfold FNV_B0; lia).
assert (Hsk : skipn (Z.to_nat a) (snd e) = s :: skipn (Datatypes.S (Z.to_nat a)) (snd e)).
{ clear -Hs. revert Hs. generalize (Z.to_nat a) as n. generalize (snd e) as l.
  induction l as [|x l IHl]; intros [|n] Hn; cbn in Hn; try discriminate.
  - injection Hn as ->. reflexivity.
  - cbn [skipn]. apply IHl. exact Hn. }
assert (Hres1 : res = fold_left mixf (skipn (Z.to_nat (a + 1)) (snd e)) (mixf g s)).
{ rewrite Hres, Hsk. cbn [fold_left]. f_equal. f_equal. lia. }
apply (mc_inc W ly S mem0 md0 regs0 regs3 mem3 md3 a na c _ HI3);
  [ lia | lia | unfold A_G_REC, A_REC_SPILL; lia
  | rewrite (CH3 2%bv) by (cbv; tauto); exact H2
  | rewrite (CH3 20%bv) by (cbv; tauto); exact H20
  | rewrite (CH3 21%bv) by (cbv; tauto); exact H21
  | rewrite (CH3 23%bv) by (cbv; tauto); exact H23
  | rewrite (CH3 24%bv) by (cbv; tauto); exact H24
  | rewrite (CH3 25%bv) by (cbv; tauto); exact H25 | | ].
- intros Hlt regs' memc' mdc' HI' H20' H10' HK'.
  assert (CK : forall r, In r MC_KEPT -> In r MC_KEPTI -> getr regs' r = getr regs r)
    by (intros r Hr Hr'; rewrite (HK' r Hr'); exact (CH3 r Hr)).
  apply (IH W ly S mem0 md0 regs0 regs' memc' mdc' c e P (a + 1) (mixf g s) res);
  [ lia | lia | lia | exact HI' | exact Hc | exact HCA | exact HROM | exact Hra0 | exact Hgp0 | exact Htp0
  | rewrite CK by (cbv; tauto); exact H2
  | intros r Hr; rewrite CK by (cbv in Hr |- *; tauto); apply HK0; exact Hr
  | rewrite CK by (cbv; tauto); exact H18
  | rewrite CK by (cbv; tauto); exact H19
  | exact H20'
  | rewrite CK by (cbv; tauto); exact H21
  | rewrite CK by (cbv; tauto); exact H22
  | rewrite CK by (cbv; tauto); exact H23
  | rewrite CK by (cbv; tauto); exact H24
  | rewrite CK by (cbv; tauto); exact H25
  | rewrite CK by (cbv; tauto); exact H26
  | exact H10'
  | rewrite (HK' 8%bv) by (cbv; tauto); exact H83
  | exact Hmr | exact Hres1 ].
- intros Heq regs' memc' mdc' HI' HK'.
  assert (CK : forall r, In r MC_KEPT -> In r MC_KEPTI -> getr regs' r = getr regs r)
    by (intros r Hr Hr'; rewrite (HK' r Hr'); exact (CH3 r Hr)).
  assert (Hres2 : res = mixf g s).
  { rewrite Hres1. replace (Z.to_nat (a + 1)) with (length (snd e)) by (subst na; lia). rewrite skipn_all. reflexivity. }
  rewrite Hres2.
  apply (mc_epi W ly S mem0 md0 regs0 regs' memc' mdc' (mixf g s) HI');
  [ rewrite CK by (cbv; tauto); exact H2
  | rewrite (HK' 8%bv) by (cbv; tauto); exact H83
  | exact Hmr
  | intros r Hr; rewrite CK by (cbv in Hr |- *; tauto); apply HK0; exact Hr
  | exact Hra0 ].
Qed.

Definition Fz (g b : Z) : Z := (Z.lxor g b * FNV_P) mod 2 ^ 64.
Lemma mix_le32 : forall h fn, 0 <= fn < REC_FN_COUNT ->
mix h (le32 fn) = Fz (Fz (Fz (Fz (if h =? 0 then FNV_B0 else h) (le_byte fn 4 0)) (le_byte fn 4 1)) (le_byte fn 4 2)) (le_byte fn 4 3).
Proof.
intros h fn Hfn. unfold mix. generalize (if h =? 0 then FNV_B0 else h) as g. intro g. unfold REC_FN_COUNT in Hfn.
assert (Hc : fn = 0 \/ fn = 1 \/ fn = 2 \/ fn = 3 \/ fn = 4 \/ fn = 5 \/ fn = 6 \/ fn = 7 \/ fn = 8 \/ fn = 9 \/ fn = 10 \/
  fn = 11 \/ fn = 12 \/ fn = 13 \/ fn = 14 \/ fn = 15 \/ fn = 16 \/ fn = 17 \/ fn = 18 \/ fn = 19 \/ fn = 20 \/ fn = 21 \/
  fn = 22 \/ fn = 23 \/ fn = 24 \/ fn = 25) by lia.
repeat match goal with H0 : _ \/ _ |- _ => destruct H0 end; subst fn; reflexivity.
Qed.
Lemma fnv_word_P : forall (E : env) g b, 0 <= g < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
mul_div M_MUL (alu64 ALU_XOR (Z_to_bv 64 g) (Z_to_bv 64 b)) (Z_to_bv 64 1099511628211) = Z_to_bv 64 (Fz g b).
Proof. intros E g b Hg Hb. exact (fnv_word E g b Hg Hb). Qed.
Lemma Fz_range : forall g b, 0 <= Fz g b < 2 ^ 64.
Proof. intros. unfold Fz. apply Z.mod_pos_bound. lia. Qed.

Lemma mc_low_frame : forall E rs (W : world SEGS) m0 m m',
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
(forall a, 0 <= a < alloc_ceiling -> ~ in_wrange E rs a) -> mc_low W m0 m -> mc_low W m0 m'.
Proof.
intros E rs W m0 m m' Hf Hw Hl a Ha. pose proof asan_consts as (C1 & _).
rewrite <- (Hl a Ha). unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact (Hw a Ha).
Qed.
Ltac nowin_tac Usp :=
let a0 := fresh "a" in let Ha0 := fresh "Ha" in let r0 := fresh "r" in let Hr0 := fresh "Hr" in let Hra0 := fresh "Hra" in
intros a0 Ha0 (r0 & Hr0 & Hra0); cbn in Hr0;
repeat (destruct Hr0 as [<- | Hr0]; [cbv [stack_region got_regionP bcell_regionP mc_fnv_region mc_c_region] in Hra0;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Hra0; try rewrite Usp in Hra0; lia|]);
destruct Hr0.
Definition mc_stack_after : YP09.region := YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0
[YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
 YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
 YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Lemma mc_saved_of_stack : forall E (W : world SEGS) m regs extra,
region_ok SEGS E (mrestrict (w_H W) m) mc_stack_after -> bv_unsigned (ew E 2) = spZ regs ->
env_agree 32 (Ereg regs extra) E -> mc_saved W m (spZ regs) regs.
Proof.
intros E W m regs extra HR Hb HA.
assert (V : forall (k : nat) (r : bv 5) off, Z.of_nat k = bv_unsigned r -> (k < 32)%nat ->
  In (YP09.mkChunk off (CVal 8 (SOff k 0))) (YP09.r_chunks mc_stack_after) ->
  val_mem SEGS (mrestrict (w_H W) m) (spZ regs + off) 8 (bv_unsigned (getr regs r))).
{ intros k r off Hk Hk32 Hin.
  pose proof (field_of_region_any E _ 2%nat (spZ regs) _ _ _ _ _ off 8 (SOff k 0) HR Hb Hin ltac:(lia)) as Hv.
  cbn [sv_denot] in Hv. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hv.
  rewrite (proj1 HA k Hk32), (ew_Ereg_nat regs extra k r Hk) in Hv.
  rewrite Z.mod_small in Hv by (pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia). exact Hv. }
unfold mc_saved.
assert (V' : forall (k : nat) (r : bv 5) off, Z.of_nat k = bv_unsigned r -> (k < 32)%nat ->
  In (YP09.mkChunk off (CVal 8 (SOff k 0))) (YP09.r_chunks mc_stack_after) ->
  val_mem SEGS (mrestrict (w_H W) m) (spZ regs - - off) 8 (bv_unsigned (getr regs r))).
{ intros k r off Hk Hk32 Hin. replace (spZ regs - - off) with (spZ regs + off) by lia. exact (V k r off Hk Hk32 Hin). }
Ltac mcm := cbn [mc_stack_after YP09.r_chunks]; repeat (first [left; reflexivity | right]).
split; [exact (V' 1%nat 1%bv (-8) eq_refl ltac:(lia) ltac:(mcm))|].
split; [exact (V' 8%nat 8%bv (-16) eq_refl ltac:(lia) ltac:(mcm))|].
split; [exact (V' 9%nat 9%bv (-24) eq_refl ltac:(lia) ltac:(mcm))|].
split; [exact (V' 18%nat 18%bv (-32) eq_refl ltac:(lia) ltac:(mcm))|].
split; [exact (V' 19%nat 19%bv (-40) eq_refl ltac:(lia) ltac:(mcm))|].
split; [exact (V' 20%nat 20%bv (-48) eq_refl ltac:(lia) ltac:(mcm))|].
split; [exact (V' 21%nat 21%bv (-56) eq_refl ltac:(lia) ltac:(mcm))|].
split; [exact (V' 22%nat 22%bv (-64) eq_refl ltac:(lia) ltac:(mcm))|].
split; [exact (V' 23%nat 23%bv (-72) eq_refl ltac:(lia) ltac:(mcm))|].
split; [exact (V' 24%nat 24%bv (-80) eq_refl ltac:(lia) ltac:(mcm))|].
split; [exact (V' 25%nat 25%bv (-88) eq_refl ltac:(lia) ltac:(mcm))|].
exact (V' 26%nat 26%bv (-96) eq_refl ltac:(lia) ltac:(mcm)).
Qed.

Lemma bv_lts_0_small : forall n, 0 <= n <= 6 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 n) = (0 <? n).
Proof.
intros n Hn. assert (Hc : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6) by lia.
repeat match goal with H0 : _ \/ _ |- _ => destruct H0 end; subst n; vm_compute; reflexivity.
Qed.

(* the slot-overflow trap 0x8ae54 at a = 0: s7 < 0 (unsigned) never holds *)
Lemma mc_ltu0 : forall E a, branch_taken BC_LTU (sv_denot E a) (sv_denot E (SLit 0)) = false.
Proof.
intros E a. rewrite branch_ltu_U, U_lit by lia. apply Z.ltb_ge. unfold U. apply (bv_unsigned_in_range 64).
Qed.
(* s8 := (- (0 < nargs)) & nargs at 0x8ae44: nargs itself once nargs > 0 *)
Lemma mc_s8 : forall na, 0 < na <= 6 ->
alu64 ALU_AND (alu64 ALU_SUB (Z_to_bv 64 0) (alu64 ALU_SLT (Z_to_bv 64 0) (Z_to_bv 64 na))) (Z_to_bv 64 na) = w64 na.
Proof.
intros na Hn. assert (Hc : na = 1 \/ na = 2 \/ na = 3 \/ na = 4 \/ na = 5 \/ na = 6) by lia.
repeat match goal with H0 : _ \/ _ |- _ => destruct H0 end; subst na; apply bv_eq; vm_compute; reflexivity.
Qed.

Ltac mc_low_step Usp HLo HLn HF HFr HG :=
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HLn : mc_low _ _ m1) by (apply (mc_low_frame _ _ _ _ m0 m1 HFr); [nowin_tac Usp | exact HLo]) end;
clear HLo HF HFr HG.

Theorem mc_core : forall ly S W regs mem md h c e P,
afn_pre_na SEGS B MIX_CALL_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 h -> 0 <= h < 2 ^ 64 -> getr regs 11 = w64 c -> mc_slot c ->
acall_at (ablocks B ly S) (rdW W mem) c e P -> abytes_atR (rdW W mem) 0x10330 RO_lit_10330 ->
SRr SEGS W (cfg_at SEGS (BASE + AF_mix_call) regs mem md)
(apost_base SEGS B MIX_CALL_STK [] regs ly S W mem md EV_MIX_CALL (mc_Q ly S W mem (spZ regs) (mixcall h (fst e) (snd e)))).
Proof.
intros ly S W regs mem md h c e P HPRE HARO H10 Hh H11 Hslot HCA HRO.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (mc_entry W ly S regs mem md h c e P HPRE H10 Hh H11 Hslot HCA HRO) as HS.
pose proof (ajournal_init_na SEGS B MIX_CALL_STK [] ly S W regs mem md HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold MIX_CALL_STK, ESTACK in Hslo, Hstk0, Hbot.
pose proof (mc_rom_view W mem HARO) as HROMV.
pose proof (mc_slot_range c Hslot) as (Hs1 & Hs2 & Hs8 & _).
unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE in Hs1, Hs2.
pose proof HCA as (Hfn & Hna6 & HlenP & Mfn & Mna & _).
set (fn := fst e) in *. set (na := Z.of_nat (length (snd e))) in *.
remember (Eimg (Ereg regs (mc_extra0 fn na))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (mc_extra0 fn na)) E) by (rewrite HE; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EN : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> (k0 < 32)%nat -> ew E k0 = getr regs r).
{ intros k0 r Hk0 Hk32. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk0. }
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (mc_extra0 fn na) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (le_byte fn 4 0)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (le_byte fn 4 1)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (le_byte fn 4 2)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 (le_byte fn 4 3)) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 na) by exact (EX 5%nat ltac:(lia)).
assert (E10 : ew E 10 = w64 h) by (rewrite (EN 10%nat 10%bv eq_refl) by lia; exact H10).
assert (E11 : ew E 11 = w64 c) by (rewrite (EN 11%nat 11%bv eq_refl) by lia; exact H11).
assert (E2 : ew E 2 = getr regs 2) by exact (EN 2%nat 2%bv eq_refl ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
assert (SHOK : sh_ok SEGS mc_Bx [] E (mrestrict (w_H W) mem)) by constructor.
assert (HBx : U E mc_Bx = SHADOW_OFF) by (unfold mc_Bx; rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
unfold cfg_at. change (w64 (BASE + AF_mix_call)) with (Z_to_bv 64 (BASE + AF_mix_call)).
(* 0x8ad54 .. 0x8adac: the frame; the traps 0x8ad88 (c = NULL) and 0x8ad94 (c mod 8) are decided by atom 11's fact *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; try exact Usp. }
pose proof (proj1 HJ) as HAR1.
(* the load1 / load4 checks on c->fn and c->nargs: the slot is addressable (report paths 0x8ae08, 0x8af2c) *)
assert (OBL : forall k n, 0 <= k -> 0 <= n -> k + n <= 8 -> range_addressable (rd_of SEGS (mrestrict (w_H W) (ms_mem ms))) (U E mc_Bx) (U E (SOff 11 k)) n).
{ intros k n Hk Hn Hkn. apply (mc_obl_rd E W (ms_mem ms) mc_Bx (SOff 11 k) (c + k) n HBx); [apply U_atom_off; [exact E11 | lia | lia]|].
  apply (mc_rec_addr ly S W (ms_mem ms) _ (c + k) n HAR1). apply mc_slot_sub; [exact Hslot | lia | unfold CALL_SIZE; lia]. }
assert (HL1 : mc_low W mem (ms_mem ms)) by (apply (mc_low_frame _ _ W mem mem (ms_mem ms) HFr); [nowin_tac Usp | intros a0 Ha0; reflexivity]).
clear HF HFr HG.
(* 0x8adac: the digest h, or the basis when h = 0 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
(* 0x8adb0 .. 0x8ae24: c->fn's 4 bytes (each trap 0x8adcc decided by atom 11's range), c->nargs *)
all: paj_run_tok RUN HS HJ SHOK Bspan.
all: try (apply OBL; lia).
all: try (awr_ok_tac; try exact Usp; fail).
all: mc_low_step Usp HL1 HL2 HF HFr HG.
(* 0x8ae24: blez nargs *)
all: psrr_branch_tok RUN BR HS SHOK Bspan.
all: rewrite branch_ne_U, (U_atom E 10 h E10), U_lit in Hc by lia.
all: cbn [sv_denot ew ewset Nat.eqb branch_taken] in Hc0; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E37 in Hc0.
all: rewrite (bv_lts_0_small na) in Hc0 by lia.
all: first
  [ assert (Hna0 : na = 0) by (destruct (Z.ltb_spec 0 na); cbn [negb] in Hc0; [discriminate | lia]);
    paj_run_to_tok RUNTO HS HJ SHOK Bspan MC_EPI
  | assert (Hna0 : 0 < na) by (destruct (Z.ltb_spec 0 na); cbn [negb] in Hc0; [lia | discriminate]);
    paj_run_to_tok RUNTO HS HJ SHOK Bspan MC_A ].
all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => awr_ok_tac; try (cbn [ew ewset Nat.eqb]; exact Usp) end).
all: mc_low_step Usp HL2 HL3 HF HFr HG.
(* nargs > 0: the run stops at the slot-overflow trap 0x8ae54 (a = 0): s7 < 0 never holds (mc_ltu0) *)
all: try (lazymatch goal with Hna0 : 0 < _ |- _ => idtac end;
  psrr_branch_tok RUN BR HS SHOK Bspan;
  [ exfalso; match goal with Hx : branch_taken BC_LTU _ _ = true |- _ => rewrite mc_ltu0 in Hx; discriminate end
  | paj_run_to_tok RUNTO HS HJ SHOK Bspan MC_A;
    [ awr_ok_tac; try (cbn [ew ewset Nat.eqb]; exact Usp)
    | mc_low_step Usp HL3 HL4 HF HFr HG; rename HL4 into HL3 ] ]).
all: lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
all: lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => assert (HAE2 : env_agree 32 (Ereg regs (mc_extra0 fn na)) Ecur) by (env_agree_chain HAE) end.
all: pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as HR0; cbn [ms_mem restrict] in HR0.
all: assert (HSV : mc_saved W (ms_mem msF) (spZ regs) regs) by
  (apply (mc_saved_of_stack _ W (ms_mem msF) regs (mc_extra0 fn na) HR0); [cbn [ew ewset Nat.eqb]; exact Usp | exact HAE2]).
all: lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
  assert (HI : mc_inv ly S W mem md regs (ms_mem msF) mdx) by (split; [exact HJ | split; [exact HL3 | exact HSV]]) end.
all: pose proof (le_byte_range fn 4 0) as LB0; pose proof (le_byte_range fn 4 1) as LB1;
  pose proof (le_byte_range fn 4 2) as LB2; pose proof (le_byte_range fn 4 3) as LB3.
all: prreg HS (8%bv : bv 5) R8; prreg HS (2%bv : bv 5) R2.
all: assert (HG8 : getr (ms_regs msF) 8 = w64 (mix h (le32 fn))) by
  (rewrite R8, (mix_le32 h fn Hfn); rewrite ?E10, E33, E34, E35, E36; unfold w64;
   destruct (Z.eqb_spec h 0) as [Hh0 | Hh0]; cbn [negb] in Hc; try discriminate;
   repeat rewrite (fnv_word_P E) by (first [apply Fz_range | unfold FNV_B0 in *; lia]); reflexivity).
all: assert (HG2 : getr (ms_regs msF) 2 = w64 (spZ regs - 96)) by (rewrite R2, Usp; unfold w64; f_equal; lia).
all: assert (Hmr : 0 <= mix h (le32 fn) < 2 ^ 64) by (unfold mix; apply fnv_range; destruct (h =? 0); unfold FNV_B0; lia).
all: pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ MC_K0 HS HAE2 ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK.
all: pmkst HS.
all: first
  [ assert (Hnil : snd e = []) by (destruct (snd e); [reflexivity | subst na; cbn [length] in Hna0; lia]);
    rewrite Hnil;
    exact (mc_epi W ly S mem md regs (ms_regs msF) (ms_mem msF) _ (mix h (le32 fn)) HI HG2 HG8 Hmr HK Hra)
  | idtac ].
all: prreg HS (10%bv : bv 5) R10; prreg HS (18%bv : bv 5) R18; prreg HS (19%bv : bv 5) R19; prreg HS (20%bv : bv 5) R20;
  prreg HS (21%bv : bv 5) R21; prreg HS (22%bv : bv 5) R22; prreg HS (23%bv : bv 5) R23; prreg HS (24%bv : bv 5) R24;
  prreg HS (25%bv : bv 5) R25; prreg HS (26%bv : bv 5) R26.
all: assert (Uc : bv_unsigned (ew E 11) = c) by (rewrite E11; apply unsigned_lit_small; lia).
all: eapply (mc_args (Z.to_nat na) W ly S mem md regs (ms_regs msF) (ms_mem msF) _ c e P 0 (mix h (le32 fn)) (mixcall h fn (snd e)));
  [ subst na; lia | lia | lia | exact HI | exact Hslot | exact HCA | exact HROMV | exact Hra | exact Hgp | exact Htp
  | exact HG2 | exact HK
  | rewrite R18, E32; reflexivity
  | rewrite R19; reflexivity
  | rewrite R20; reflexivity
  | rewrite R21, Uc; reflexivity
  | rewrite R22; reflexivity
  | rewrite R23, Uc; apply (mc_not_word E); lia
  | rewrite R24, E37; apply mc_s8; lia
  | rewrite R25; reflexivity
  | rewrite R26; reflexivity
  | rewrite R10; rewrite ?Uc; unfold w64; f_equal; lia
  | exact HG8 | exact Hmr | reflexivity ].
Qed.

(* the statement, with the allocator state unchanged and the memory outside the call's stack window kept in its
   post (what answer's walk needs after the call) *)
Theorem tmix_call_spec_keep :
forall ly S W (regs : bvmap 5 word) mem md (h c : Z) (e : rcall) (P : list (Z * Z)),
afn_pre_na SEGS B MIX_CALL_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 h -> 0 <= h < 2 ^ 64 ->
getr regs 11 = w64 c ->
((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) ->
acall_at (ablocks B ly S) (rdW W mem) c e P ->
cmd_ro_ok (rdW W mem) ->
st_nev S + EV_MIX_CALL <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_mix_call) regs mem md)
(apost_base SEGS B MIX_CALL_STK [] regs ly S W mem md EV_MIX_CALL
(fun ly' S' W' regs' mem' md' =>
getr regs' 10 = w64 (mixcall h (fst e) (snd e)) /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
ly' = ly /\ S' = S /\ kept_out (rdW W mem) (rdW W' mem') (spZ regs - MIX_CALL_STK) (spZ regs))).
Proof.
intros ly S W regs mem md h c e P HPRE HARO H10 Hh H11 Hslot HCA HRO _.
eapply SRr_mono; [exact (mc_core ly S W regs mem md h c e P HPRE HARO H10 Hh H11 Hslot HCA (proj1 (proj1 HRO)))|].
cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ & HP & (HQ & -> & -> & HK)).
exists ly, S, regs', mem', md'. split; [reflexivity|]. split; [exact HJ|]. split; [exact HP|].
split; [exact HQ|]. split; [apply Permutation_refl|]. split; [reflexivity|]. split; [reflexivity | exact HK].
Qed.

Theorem tmix_call_spec_holds : tmix_call_spec B MT.
Proof.
intros ly S W regs mem md h c e P HPRE HARO H10 Hh H11 Hslot HCA HRO HEV.
eapply SRr_mono; [exact (tmix_call_spec_keep ly S W regs mem md h c e P HPRE HARO H10 Hh H11 Hslot HCA HRO HEV)|].
cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ & HP & (HQ & HPm & Hly & HSS & _)).
exists ly', S', regs', mem', md'. split; [reflexivity|]. split; [exact HJ|]. split; [exact HP|].
split; [exact HQ|]. split; [exact HPm|]. split; [exact Hly | exact HSS].
Qed.

End e.
End f.
End d.

Check tmix_call_spec_holds.
Print Assumptions tmix_call_spec_holds.
