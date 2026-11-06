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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/mix_call.v, with its module paths, module names and numbers changed; 841 of its 1027 lines of code are new or changed and 1053 lines of the source are left out. *)
(* The ASan walk of name_ok on fuzz_segconf image A (entry BASE + AF_name_ok = 0x89d58): `name_ok_walk` proves
   name_ok_contract (lib/A/Prog/name_ok_c.v) at image A's numbers, over the Pa engine of the listing seg_listing,
   from the contract of its one callee, musl's isalnum (the interceptor layer's interface row 9). Plan:
   provenance/evidence/listing-plans/plan-name_ok.md.

   Labels (offsets from BASE = 0x84d34):
     NK_B 0x5060 (0x89d94) after the inline check of s[0]: lbu s5,0(a0); beqz s5 -> NK_Z
     NK_L 0x5088 (0x89dbc) loop head: zext.b a0,s5; jal isalnum
     NK_R 0x5090 (0x89dc4) back from isalnum: bnez a0 -> NK_N; the '-'..'_' guard and the mask bit -> NK_X
     NK_N 0x50a8 (0x89ddc) the inline check of s[k+1] (address s0), lbu s5,0(s2); s0++, s2++; bnez s5 -> NK_L
     NK_X 0x50e8 (0x89e1c) epilogue: ra, s0-s5 back from the frame; ret
   At NK_L: s0 = s2 = s + k + 1, s1 = the shadow base, s3 = 50, s4 = 2^50 + 2^13 + 3, s5 = s[k] <> 0,
   sp = sp0 - 64, the frame holds ra, s0-s5 at sp0 - 8 .. sp0 - 56.

   Walked: 58 of the 61 instructions. The three left are the two error arms of the inline checks (`mv a0,s0` and
   the call of errpath_load1 at 0x89e08 / 0x89e0c, and the call at 0x89e48) -- their branch is never taken, because
   name_ok_pre's sa_addr makes the shadow byte of every byte of the string say "addressable".

   Inputs this text closes against: the contracts at the contracts commit 6f783602b5e3 (G4 FINAL;
   name_ok_c.v), the listing at the listing commit 61d5dd44f17, the kit at the kit commit 68ab01587fc,
   the core at the core commit 677577a4a73e, row 9's text at the interceptor-layer commit ab5c95b8897a
   (lib/A/Rt/RtSeg.v) and the unit's numbers at the close commit 2723a39411ca (SegInstA.STK_name_ok,
   RLO_A, RHI_A). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegSyms SegList SegPa SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaSB PaArt SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec isalnum_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import name_ok_lem name_ok_c SegInstA.

Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma nk_b2z_eq : forall b : bool, seg_spec.b2z b = Z.b2z b.
Proof. intros [|]; reflexivity. Qed.
Lemma nk_set_fs_id : forall S : astate, S = set_fs (st_fs S) S.
Proof. intros [a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12]. reflexivity. Qed.

Definition NK_B : Z := 0x5060.
Definition NK_L : Z := 0x5088.
Definition NK_R : Z := 0x5090.
Definition NK_N : Z := 0x50a8.
Definition NK_X : Z := 0x50e8.
(* the registers no stretch of name_ok writes: gp, tp, s6-s11 *)
Definition NK_K0 : list (bv 5) := [3; 4; 22; 23; 24; 25; 26; 27]%bv.

Lemma nk_aview_byte : forall segs H mem a v, aview segs H mem a = Some v -> 0 <= v < 256.
Proof.
intros segs H mem a v E. unfold aview in E.
destruct (mbyte segs (mrestrict H mem) a) as [b|]; [|discriminate]. cbn in E. injection E as <-.
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma nk_U_den : forall (E : env) v z, U E v = z -> 0 <= z < 2 ^ 64 -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z Hu Hz. unfold U in Hu. rewrite <- Hu. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* `zext.b a0,s5` (andi a0,s5,255) on a byte value *)
Lemma nk_zext_byte : forall (E : env) c, 0 <= c < 256 ->
alu64 ALU_AND (Z_to_bv 64 c) (Z_to_bv 64 255) = Z_to_bv 64 c.
Proof.
intros E c Hc.
change (alu64 ALU_AND (Z_to_bv 64 c) (Z_to_bv 64 255))
  with (sv_denot E (SAlu ALU_AND (SLit c) (SLit 255))).
apply nk_U_den; [|lia]. rewrite U_and_lit by lia. rewrite U_lit by lia.
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. apply Z.mod_small. lia.
Qed.

Lemma nk_mbyte_of_aview : forall segs H mem a z, aview segs H mem a = Some z -> 0 <= z < 256 ->
mbyte segs (mrestrict H mem) a = Some (Z_to_bv 8 z).
Proof.
intros segs H mem a z Ha Hz. unfold aview in Ha. destruct (mbyte segs (mrestrict H mem) a) as [b|] eqn:Hb; [|discriminate].
cbn in Ha. injection Ha as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma nk_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the shadow byte of an address below 2^47 lies below alloc_ceiling *)
Lemma nk_shadow_low : forall x, 0 <= x <= 2 ^ 47 -> 0 <= SHADOW_OFF + x / 8 < alloc_ceiling.
Proof using rc.
intros x Hx. pose proof asan_consts as (C1 & _).
assert (H1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (H2 : x / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
change (2 ^ 47 / 8) with 17592186044416 in H2. unfold SHADOW_OFF. lia.
Qed.

Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the shape the engine leaves an inline check's obligation in *)
Lemma nk_obl_rd : forall E (W : world SEGS) m bx x a n, U E bx = SHADOW_OFF -> U E x = a ->
range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n ->
range_addressable (rd_of SEGS (mrestrict (w_H W) m)) (U E bx) (U E x) n.
Proof. intros E W m bx x a n Hb Hx Hr. rewrite Hb, Hx. exact Hr. Qed.

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
(* the stack this call needs, from the unit's instantiation file: name_ok's own 64-byte frame and, below it, the
   window musl's isalnum asks for (SegInstA.STK_name_ok = 64 + ESTACK = 4160) *)
Let STK : Z := STK_name_ok.
Let HSTK : 64 <= STK := ltac:(unfold STK, STK_name_ok, ESTACK; lia).
Let HSTKE : 64 + ESTACK <= STK := ltac:(unfold STK, STK_name_ok; lia).

Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

(* the string at s, as the walk uses it: its bytes and NUL at the entry, no NUL inside, its shadow addressable,
   its bytes below 2^47 and outside this call's stack window (every arm of the contract's sa_dst gives this) *)
Definition nk_str (W : world SEGS) (m0 : word -> option byte) (sp0 s : Z) (nm : list Z) : Prop :=
(forall i, (i <= length nm)%nat -> aview SEGS (w_H W) m0 (s + Z.of_nat i) = Some (nth i (nm ++ [0]) 0)) /\
~ In 0 nm /\ range_addressable (aview SEGS (w_H W) m0) SHADOW_OFF s (Z.of_nat (length nm) + 1) /\
4096 <= s /\ s + Z.of_nat (length nm) + 1 <= 2 ^ 47 - 1 /\
(s + Z.of_nat (length nm) + 1 <= sp0 - STK \/ sp0 <= s).

(* the memory below alloc_ceiling is the entry's (the heap, the side-stack frames, the image, every shadow byte) *)
Definition nk_low (W : world SEGS) (m0 m : word -> option byte) : Prop :=
forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m0 a.
(* the seven registers the prologue saved, in the frame of 64 bytes below sp0 *)
Definition nk_saved (W : world SEGS) (m : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 8) 8 (bv_unsigned (getr regs0 1)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 32) 8 (bv_unsigned (getr regs0 18)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 40) 8 (bv_unsigned (getr regs0 19)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 48) 8 (bv_unsigned (getr regs0 20)) /\
val_mem SEGS (mrestrict (w_H W) m) (sp0 - 56) 8 (bv_unsigned (getr regs0 21)).

Definition nk_inv (ly : alayout) (S : astate) (W : world SEGS) (mem0 : word -> option byte) (md0 : Model)
(regs0 : bvmap 5 word) (m : word -> option byte) (md : Model) : Prop :=
ajournal SEGS B STK (spZ regs0) [] ly S W mem0 md0 [] ly S W m md 0 /\
nk_low W mem0 m /\ nk_saved W m (spZ regs0) regs0.

(* outside this call's stack window the memory is the entry's: below alloc_ceiling by nk_low, above it by the
   journal (the footprint is empty) *)
Lemma nk_kept : forall ly S W mem0 md0 regs0 m md a, nk_inv ly S W mem0 md0 regs0 m md ->
0 <= a < 2 ^ 64 -> ~ (spZ regs0 - STK <= a < spZ regs0) ->
aview SEGS (w_H W) m a = aview SEGS (w_H W) mem0 a.
Proof using.
intros ly S W mem0 md0 regs0 m md a (HJ & HL & _) Ha Hw.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
destruct (Z_lt_le_dec a alloc_ceiling) as [Hlo | Hge]; [exact (HL a ltac:(lia))|].
apply F1; [lia | exact Hw | apply inFP_nil].
Qed.

Lemma nk_str_low : forall ly S W mem0 md0 regs0 m md sp0 s nm i,
nk_inv ly S W mem0 md0 regs0 m md -> sp0 = spZ regs0 -> nk_str W mem0 sp0 s nm -> (i <= length nm)%nat ->
aview SEGS (w_H W) m (s + Z.of_nat i) = Some (nth i (nm ++ [0]) 0).
Proof using.
intros ly S W mem0 md0 regs0 m md sp0 s nm i HI Hsp (HB & _ & _ & H4 & H47 & HW) Hi.
rewrite (nk_kept ly S W mem0 md0 regs0 m md (s + Z.of_nat i) HI ltac:(lia) ltac:(subst sp0; lia)).
exact (HB i Hi).
Qed.

Lemma nk_str_addr : forall ly S W mem0 md0 regs0 m md sp0 s nm i,
nk_inv ly S W mem0 md0 regs0 m md -> sp0 = spZ regs0 -> nk_str W mem0 sp0 s nm -> (i <= length nm)%nat ->
range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (s + Z.of_nat i) 1.
Proof using.
intros ly S W mem0 md0 regs0 m md sp0 s nm i (HJ & HL & HS) Hsp (_ & _ & HR & H4 & H47 & _) Hi.
apply (range_addressable_agree (aview SEGS (w_H W) mem0)).
- intros x Hx. apply HL. unfold shadow_of_addr. apply nk_shadow_low. lia.
- apply (range_addressable_sub _ _ s (Z.of_nat (length nm) + 1)); [exact HR | lia | lia].
Qed.

Lemma nk_str_byte : forall W m0 sp0 s nm i, nk_str W m0 sp0 s nm -> (i < length nm)%nat -> 0 < nth i nm 0 < 256.
Proof using.
intros W m0 sp0 s nm i (HB & HN & _) Hi. pose proof (HB i ltac:(lia)) as E.
rewrite nk_nth_app in E by exact Hi. pose proof (nk_aview_byte _ _ _ _ _ E) as R.
assert (nth i nm 0 <> 0) by (intros Z0; apply HN; rewrite <- Z0; apply nth_In; exact Hi). lia.
Qed.

(* what the call leaves: the answer in a0, the layout and the allocator state as they were, and every byte
   outside its own stack window as it was (the contract's sa_kept, whose write set is empty) *)
Definition nk_keptQ (W : world SEGS) (mem0 : word -> option byte) (regs0 : bvmap 5 word)
(W' : world SEGS) (mem' : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - STK <= a < spZ regs0) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem0 a.
Definition nk_Q (ly : alayout) (S : astate) (W : world SEGS) (mem0 : word -> option byte)
(regs0 : bvmap 5 word) (res : Z) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' _ =>
getr regs' 10 = w64 res /\ ly' = ly /\ S' = S /\ nk_keptQ W mem0 regs0 W' mem'.
Definition nk_post (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS) (mem0 : word -> option byte)
(md0 : Model) (res : Z) : world SEGS -> config -> Prop :=
apost_base SEGS B STK [] regs0 ly S W mem0 md0 0 (nk_Q ly S W mem0 regs0 res).

(* the registers at NK_L / NK_R / NK_N: p = s + k + 1 in s0 and s2, c = s[k] in s5 *)
Definition nk_regsL (regs0 regs : bvmap 5 word) (p c : Z) : Prop :=
getr regs 2 = w64 (spZ regs0 - 64) /\ getr regs 9 = w64 SB /\ getr regs 19 = w64 50 /\
getr regs 20 = w64 NK_MASK /\ getr regs 8 = w64 p /\ getr regs 18 = w64 p /\ getr regs 21 = w64 c /\
(forall r, In r NK_K0 -> getr regs r = getr regs0 r).

Lemma nk_frame_nowin : forall E rs (m m' : word -> option byte),
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' -> forall x, m' x = m x.
Proof using.
intros E rs m m' Hw Hf x. apply Hf. intros (r & Hr & Ha).
pose proof (proj1 (forallb_forall _ _) Hw r Hr) as H. apply Z.leb_le in H. lia.
Qed.
Lemma nk_aview_nowin : forall E rs H m m',
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs (mrestrict H m) (mrestrict H m') ->
forall a, aview SEGS H m' a = aview SEGS H m a.
Proof using.
intros E rs H m m' Hw Hf a. unfold aview, mbyte. rewrite (nk_frame_nowin E rs _ _ Hw Hf). reflexivity.
Qed.
Lemma nk_mbyte_eq : forall H m m' a, aview SEGS H m' a = aview SEGS H m a ->
mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof using.
intros H m m' a Ha. unfold aview in Ha.
destruct (mbyte SEGS (mrestrict H m') a) as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|]; cbn in Ha;
try discriminate; [|reflexivity]. injection Ha as Ha. f_equal. apply bv_eq. exact Ha.
Qed.
Lemma nk_val_mem_kept : forall H m m' a n v,
(forall k, (k < n)%nat -> aview SEGS H m' (a + Z.of_nat k) = aview SEGS H m (a + Z.of_nat k)) ->
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof using. intros H m m' a n v Hk Hv k Hlt. rewrite (nk_mbyte_eq H m m' _ (Hk k Hlt)). exact (Hv k Hlt). Qed.
Lemma nk_saved_kept : forall (W : world SEGS) m m' sp0 regs0,
(forall a, sp0 - 64 <= a < sp0 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
nk_saved W m sp0 regs0 -> nk_saved W m' sp0 regs0.
Proof using.
intros W m m' sp0 regs0 Hk (S1 & S2 & S3 & S4 & S5 & S6 & S7).
repeat split; (eapply nk_val_mem_kept; [|eassumption]); intros k Hk'; apply Hk; lia.
Qed.
Lemma nk_low_kept : forall (W : world SEGS) m0 m m',
(forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
nk_low W m0 m -> nk_low W m0 m'.
Proof using. intros W m0 m m' Hk Hl a Ha. rewrite (Hk a Ha). exact (Hl a Ha). Qed.
(* a run over regions with no write window keeps the invariant *)
Lemma nk_inv_run : forall ly S W mem0 md0 regs0 m md m' md' E rs,
nk_inv ly S W mem0 md0 regs0 m md ->
ajournal SEGS B STK (spZ regs0) [] ly S W mem0 md0 [] ly S W m' md' 0 ->
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
nk_inv ly S W mem0 md0 regs0 m' md'.
Proof using.
intros ly S W mem0 md0 regs0 m md m' md' E rs (_ & HL & HSV) HJ Hf Hw.
pose proof (nk_aview_nowin E rs (w_H W) m m' Hw Hf) as HA.
split; [exact HJ|]. split; [apply (nk_low_kept W mem0 m m'); [intros; apply HA | exact HL]|].
apply (nk_saved_kept W m m'); [intros; apply HA | exact HSV].
Qed.

Lemma nk_callee_saved_in : forall r, acallee_saved r -> In (Z_to_bv 5 r) CALLEE_SAVED.
Proof using.
intros r Hr. unfold acallee_saved in Hr.
assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia. clear Hr.
destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
cbv [CALLEE_SAVED In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
Lemma nk_aregs_preserved_of_list : forall regs regs', (forall r, In r CALLEE_SAVED -> getr regs' r = getr regs r) ->
aregs_preserved regs regs'.
Proof using. intros regs regs' H r Hr. apply H. apply nk_callee_saved_in. exact Hr. Qed.

(* the frame after the prologue: ra, s0-s5 at sp0 - 8 .. sp0 - 56 *)
Definition nk_stack_after : YP09.region := YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0
[YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
 YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Lemma nk_saved_of_stack : forall E (W : world SEGS) m regs extra,
region_ok SEGS E (mrestrict (w_H W) m) nk_stack_after -> bv_unsigned (ew E 2) = spZ regs ->
env_agree 32 (Ereg regs extra) E -> nk_saved W m (spZ regs) regs.
Proof using.
intros E W m regs extra HR Hb HA.
assert (V : forall (k : nat) (r : bv 5) off, Z.of_nat k = bv_unsigned r -> (k < 32)%nat ->
  In (YP09.mkChunk off (CVal 8 (SOff k 0))) (YP09.r_chunks nk_stack_after) ->
  val_mem SEGS (mrestrict (w_H W) m) (spZ regs - - off) 8 (bv_unsigned (getr regs r))).
{ intros k r off Hk Hk32 Hin.
  pose proof (field_of_region_any E _ 2%nat (spZ regs) _ _ _ _ _ off 8 (SOff k 0) HR Hb Hin ltac:(lia)) as Hv.
  cbn [sv_denot] in Hv. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hv.
  rewrite (proj1 HA k Hk32), (ew_Ereg_nat regs extra k r Hk) in Hv.
  rewrite Z.mod_small in Hv by (pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hr;
    change (bv_modulus 64) with (2 ^ 64) in Hr; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia).
  replace (spZ regs - - off) with (spZ regs + off) by lia. exact Hv. }
Ltac nkm := cbn [nk_stack_after YP09.r_chunks]; repeat (first [left; reflexivity | right]).
unfold nk_saved.
split; [exact (V 1%nat 1%bv (-8) eq_refl ltac:(lia) ltac:(nkm))|].
split; [exact (V 8%nat 8%bv (-16) eq_refl ltac:(lia) ltac:(nkm))|].
split; [exact (V 9%nat 9%bv (-24) eq_refl ltac:(lia) ltac:(nkm))|].
split; [exact (V 18%nat 18%bv (-32) eq_refl ltac:(lia) ltac:(nkm))|].
split; [exact (V 19%nat 19%bv (-40) eq_refl ltac:(lia) ltac:(nkm))|].
split; [exact (V 20%nat 20%bv (-48) eq_refl ltac:(lia) ltac:(nkm))|].
exact (V 21%nat 21%bv (-56) eq_refl ltac:(lia) ltac:(nkm)).
Qed.

(* a run whose only write window is the frame keeps every byte below alloc_ceiling *)
Lemma nk_low_frame : forall E rs (W : world SEGS) m0 m m',
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
(forall a, 0 <= a < alloc_ceiling -> ~ in_wrange E rs a) -> nk_low W m0 m -> nk_low W m0 m'.
Proof using.
intros E rs W m0 m m' Hf Hw Hl a Ha.
rewrite <- (Hl a Ha). unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
pose proof asan_consts as (C1 & _). rewrite unsigned_lit_small by lia. exact (Hw a Ha).
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* NK_X, the epilogue at 0x89e1c *)
Definition nk_epi_region : YP09.region := YP09.mkRegion (Some 2%nat) 0 64 0 0
[YP09.mkChunk 8 (CVal 8 (SOff 38 0)); YP09.mkChunk 16 (CVal 8 (SOff 37 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0));
 YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 34 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0));
 YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition ss_nk_epi : sstate := mkSS NK_X sr_atoms [nk_epi_region] None (mkFacts [(2%nat, mkAF (2^46) (2^47) 4)] [] []).
Definition nk_epi_extra (regs0 : bvmap 5 word) : list word := map (getr regs0) [1; 8; 9; 18; 19; 20; 21]%bv.

Lemma nk_epi : forall W ly S mem0 md0 regs0 regs memc mdc res,
nk_inv ly S W mem0 md0 regs0 memc mdc ->
getr regs 2 = w64 (spZ regs0 - 64) -> getr regs 10 = w64 res -> 0 <= res < 2 ^ 64 ->
(forall r, In r NK_K0 -> getr regs r = getr regs0 r) ->
YK0s.ret_ok (getr regs0 1) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + NK_X)) memc (seg_rom SEGS)) mdc)
(nk_post regs0 ly S W mem0 md0 res).
Proof using LAWS HSTK.
intros W ly S mem0 md0 regs0 regs memc mdc res HI H2 H10 Hres HK0 Hra.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HI as (HJ & HLOW & HSV).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
remember (Eimg (Ereg regs (nk_epi_extra regs0))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (nk_epi_extra regs0)) E) by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EN : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> ew E k = getr regs r).
{ intros k r Hk Hk32. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (EX : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (nk_epi_extra regs0) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = w64 (spZ regs0 - 64)) by (rewrite (EN 2%nat 2%bv eq_refl) by lia; exact H2).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 64) by (rewrite E2; apply unsigned_lit_small; lia).
pose proof HSV as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
assert (CK : forall (j : nat) (r : bv 5) off, (j < 7)%nat -> nth j (nk_epi_extra regs0) (Z_to_bv 64 0) = getr regs0 r ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs0 - 64 + off) 8 (bv_unsigned (getr regs0 r)) ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) memc) (spZ regs0 - 64) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hj Hn Hv. apply (chunk_ok_val SEGS E _ _ off 8 _ (bv_unsigned (getr regs0 r)));
  [cbn [sv_denot]; rewrite (EX j Hj), Hn, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity | apply (bv_unsigned_in_range 64) | zside | exact Hv]. }
assert (HS : st_ok_pi SEGS VAL E ss_nk_epi (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + NK_X)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_nk_epi. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, nk_epi_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (CK 6%nat 21%bv 8); [lia | reflexivity | replace (spZ regs0 - 64 + 8) with (spZ regs0 - 56) by lia; exact S7].
  + apply (CK 5%nat 20%bv 16); [lia | reflexivity | replace (spZ regs0 - 64 + 16) with (spZ regs0 - 48) by lia; exact S6].
  + apply (CK 4%nat 19%bv 24); [lia | reflexivity | replace (spZ regs0 - 64 + 24) with (spZ regs0 - 40) by lia; exact S5].
  + apply (CK 3%nat 18%bv 32); [lia | reflexivity | replace (spZ regs0 - 64 + 32) with (spZ regs0 - 32) by lia; exact S4].
  + apply (CK 2%nat 9%bv 40); [lia | reflexivity | replace (spZ regs0 - 64 + 40) with (spZ regs0 - 24) by lia; exact S3].
  + apply (CK 1%nat 8%bv 48); [lia | reflexivity | replace (spZ regs0 - 64 + 48) with (spZ regs0 - 16) by lia; exact S2].
  + apply (CK 0%nat 1%bv 56); [lia | reflexivity | replace (spZ regs0 - 64 + 56) with (spZ regs0 - 8) by lia; exact S1].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16.
  assert (Hm16 : (spZ regs0 - 64) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
  revert Hslo Hshi H47 Hceil C1 Hstk0 Hm16 HSTK. clear. intros. repeat match goal with |- _ /\ _ => split end; lia. }
clear HE.
assert (SHOK : sh_ok SEGS (SOff 9 0) [] E (mrestrict (w_H W) memc)) by constructor.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
assert (EV : forall j r, (j < 7)%nat -> nth j (nk_epi_extra regs0) (Z_to_bv 64 0) = getr regs0 r -> ew E (32 + j) = getr regs0 r).
{ intros j r Hj Hn. rewrite (EX j Hj). exact Hn. }
pose proof (EV 0%nat 1%bv ltac:(lia) eq_refl) as X32. pose proof (EV 1%nat 8%bv ltac:(lia) eq_refl) as X33.
pose proof (EV 2%nat 9%bv ltac:(lia) eq_refl) as X34. pose proof (EV 3%nat 18%bv ltac:(lia) eq_refl) as X35.
pose proof (EV 4%nat 19%bv ltac:(lia) eq_refl) as X36. pose proof (EV 5%nat 20%bv ltac:(lia) eq_refl) as X37.
pose proof (EV 6%nat 21%bv ltac:(lia) eq_refl) as X38. cbn [Nat.add] in X32, X33, X34, X35, X36, X37, X38.
assert (F : forall r, In r CALLEE_SAVED -> getr (ms_regs ms) r = getr regs0 r).
{ intros r Hr. cbv [CALLEE_SAVED In] in Hr.
  repeat (destruct Hr as [<- | Hr];
  [ lazymatch goal with |- getr _ ?rr = _ => let H := fresh "H" in prreg HS rr H; rewrite H end;
    first [ rewrite Usp; replace (spZ regs0 - 64 + 64) with (spZ regs0) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
          | exact X33 | exact X34 | exact X35 | exact X36 | exact X37 | exact X38
          | lazymatch goal with |- ew E ?k = getr regs0 ?rr => rewrite (EN k rr eq_refl) by lia; apply HK0; cbv; tauto end ]
  | ]); destruct Hr. }
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold nk_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split; [cbn [ms_regs]; rewrite R1, X32, Hra; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
split; [apply nk_aregs_preserved_of_list; exact F|].
split; [cbn [ms_regs]; rewrite R10, (EN 10%nat 10%bv eq_refl) by lia; exact H10|].
split; [reflexivity|]. split; [reflexivity|].
intros a Ha Hw.
apply (nk_kept ly S W mem0 md0 regs0 (ms_mem ms) _ a
  (nk_inv_run ly S W mem0 md0 regs0 memc mdc (ms_mem ms) _ E [nk_epi_region] HI HJ HFr
     ltac:(vm_compute; reflexivity)) Ha Hw).
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* NK_N, 0x89ddc: the inline check of s[k+1] at s0, lbu s5,0(s2), s0++, s2++, bnez s5 -> NK_L; at the NUL:
   a0 := 1, j NK_X *)
Definition nk_n_region : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition ss_nk_n : sstate := mkSS NK_N sr_atoms [nk_n_region] None
(mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 4096 (2^47 - 1) 0); (9%nat, mkAF SB SB 0);
          (18%nat, mkAF 4096 (2^47 - 1) 0); (32%nat, mkAF 0 255 0)] [] []).
Definition NK_KN : list (bv 5) := [2; 3; 4; 9; 19; 20; 22; 23; 24; 25; 26; 27]%bv.

Lemma nk_next : forall (nm : list Z) W ly S mem0 md0 regs0 regs memc mdc s k (c : Z),
nk_inv ly S W mem0 md0 regs0 memc mdc -> YK0s.ret_ok (getr regs0 1) ->
nk_str W mem0 (spZ regs0) s nm -> (k < length nm)%nat ->
nk_regsL regs0 regs (s + Z.of_nat k + 1) c ->
SegModel.name_ok nm = forallb nk_ch (skipn (Datatypes.S k) nm) ->
((Datatypes.S k < length nm)%nat -> SegModel.name_ok nm = forallb nk_ch (skipn (Datatypes.S k) nm) ->
  forall regs' memc' mdc', nk_inv ly S W mem0 md0 regs0 memc' mdc' ->
  nk_regsL regs0 regs' (s + Z.of_nat (Datatypes.S k) + 1) (nth (Datatypes.S k) nm 0) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + NK_L)) memc' (seg_rom SEGS)) mdc')
    (nk_post regs0 ly S W mem0 md0 (Z.b2z (SegModel.name_ok nm)))) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + NK_N)) memc (seg_rom SEGS)) mdc)
(nk_post regs0 ly S W mem0 md0 (Z.b2z (SegModel.name_ok nm))).
Proof using LAWS HSTK.
intros nm W ly S mem0 md0 regs0 regs memc mdc s k c HI Hra HSTR Hk
  (H2 & H9 & H19 & H20 & H8 & H18 & H21 & HK0) HM HNEXT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HI as (HJ & HLOW & HSV).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HSTR as (HB0 & HNZ & HRA & Hs4 & Hs47 & HWIN).
set (n := length nm) in *.
set (p := s + Z.of_nat k + 1) in *.
set (b := nth (Datatypes.S k) (nm ++ [0]) 0).
assert (Rb : aview SEGS (w_H W) memc p = Some b).
{ subst p b. replace (s + Z.of_nat k + 1) with (s + Z.of_nat (Datatypes.S k)) by lia.
  apply (nk_str_low ly S W mem0 md0 regs0 memc mdc (spZ regs0) s nm (Datatypes.S k) HI eq_refl HSTR ltac:(lia)). }
pose proof (nk_aview_byte _ _ _ _ _ Rb) as Hb.
remember (Eimg (Ereg regs [Z_to_bv 64 b])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 b]) E) by (rewrite HE; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EN : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> (k0 < 32)%nat -> ew E k0 = getr regs r).
{ intros k0 r Hk0 Hk32. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk0. }
assert (E2 : ew E 2 = w64 (spZ regs0 - 64)) by (rewrite (EN 2%nat 2%bv eq_refl) by lia; exact H2).
assert (E8 : ew E 8 = w64 p) by (rewrite (EN 8%nat 8%bv eq_refl) by lia; exact H8).
assert (E9 : ew E 9 = w64 SB) by (rewrite (EN 9%nat 9%bv eq_refl) by lia; exact H9).
assert (E18 : ew E 18 = w64 p) by (rewrite (EN 18%nat 18%bv eq_refl) by lia; exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 b) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HS : st_ok_pi SEGS VAL E ss_nk_n (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + NK_N)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_nk_n. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, nk_n_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E18. unfold w64. rewrite unsigned_lit_small by (subst p; lia).
  split; [subst p; lia|]. split; [subst p; lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ p 0 1 (SOff 32 0) b); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  intros k0 Hk0. replace k0 with 0%nat by lia. rewrite !Z.add_0_r. rewrite nk_le_byte1 by exact Hb.
  apply nk_mbyte_of_aview; [exact Rb | exact Hb].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E8, E9, E18, E32. unfold w64. rewrite !unsigned_lit_small by (unfold SB; subst p; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (Hm16 : (spZ regs0 - 64) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
  subst p. revert Hslo Hshi H47 Hceil C1 Hstk0 Hm16 Hs4 Hs47 Hb HSTK. clear - Hk. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
clear HE.
assert (SHOK : sh_ok SEGS (SOff 9 0) [] E (mrestrict (w_H W) memc)) by constructor.
assert (HBx : U E (SOff 9 0) = SHADOW_OFF) by (rewrite (U_atom E 9 SB E9) by (unfold SB; lia); reflexivity).
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem mkst]. apply (nk_obl_rd E W memc (SOff 9 0) (SOff 8 0) p 1 HBx);
    [apply U_atom; [exact E8 | subst p; lia]|].
  pose proof (nk_str_addr ly S W mem0 md0 regs0 memc mdc (spZ regs0) s nm (Datatypes.S k) HI eq_refl HSTR ltac:(lia)) as R.
  replace (s + Z.of_nat (Datatypes.S k)) with p in R by (subst p; lia). exact R. }
{ awr_ok_tac. }
pose proof (nk_inv_run ly S W mem0 md0 regs0 memc mdc (ms_mem ms) _ E [nk_n_region] HI HJ HFr ltac:(vm_compute; reflexivity)) as HI1.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s[k + 1] <> 0: the loop goes on *)
  rewrite branch_ne_U in Hc. unfold U in Hc. cbn [sv_denot ew ewset Nat.eqb] in Hc.
  rewrite E32 in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc.
  rewrite !unsigned_lit_small in Hc by lia.
  assert (Hb0 : b <> 0) by (destruct (Z.eqb_spec b 0); [discriminate | assumption]).
  assert (Hlt : (Datatypes.S k < n)%nat).
  { destruct (Nat.eq_dec (Datatypes.S k) n) as [Ei|Ei]; [|lia]. exfalso. apply Hb0. subst b.
    apply (proj2 (nk_nth_zero nm (Datatypes.S k) HNZ ltac:(lia))). exact Ei. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan NK_L.
  { awr_ok_tac. }
  pose proof (nk_inv_run ly S W mem0 md0 regs0 (ms_mem ms) _ (ms_mem ms0) _ _ _ HI1 HJ HFr ltac:(vm_compute; reflexivity)) as HI2.
  clear HI1 HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 b]) Ecur) by (env_agree_chain HAE) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ NK_KN HS HAE2 ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (8%bv : bv 5) R8. prreg HS (18%bv : bv 5) R18. prreg HS (21%bv : bv 5) R21.
  rewrite E8 in R8. rewrite E18 in R18. rewrite E32 in R21. unfold w64 in R8, R18.
  rewrite unsigned_lit_small in R8, R18 by (subst p; lia).
  pmkst HS.
  apply (HNEXT Hlt HM _ _ _ HI2).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  + rewrite (HK 2%bv) by (cbv; tauto). exact H2.
  + rewrite (HK 9%bv) by (cbv; tauto). exact H9.
  + rewrite (HK 19%bv) by (cbv; tauto). exact H19.
  + rewrite (HK 20%bv) by (cbv; tauto). exact H20.
  + rewrite R8. unfold w64. f_equal. subst p. lia.
  + rewrite R18. unfold w64. f_equal. subst p. lia.
  + rewrite R21. unfold w64. f_equal. subst b. apply nk_nth_app. exact Hlt.
  + intros r Hr. rewrite (HK r) by (cbv in Hr |- *; tauto). apply HK0. exact Hr.
- (* s[k + 1] = 0: every byte passed, a0 := 1 *)
  rewrite branch_ne_U in Hc. unfold U in Hc. cbn [sv_denot ew ewset Nat.eqb] in Hc.
  rewrite E32 in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc.
  rewrite !unsigned_lit_small in Hc by lia.
  assert (Hb0 : b = 0) by (destruct (Z.eqb_spec b 0); [assumption | discriminate]).
  assert (Hend : Datatypes.S k = n) by (apply (proj1 (nk_nth_zero nm (Datatypes.S k) HNZ ltac:(lia))); exact Hb0).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan NK_X.
  { awr_ok_tac. }
  pose proof (nk_inv_run ly S W mem0 md0 regs0 (ms_mem ms) _ (ms_mem ms0) _ _ _ HI1 HJ HFr ltac:(vm_compute; reflexivity)) as HI2.
  clear HI1 HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 b]) Ecur) by (env_agree_chain HAE) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ NK_KN HS HAE2 ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) R10.
  pmkst HS.
  assert (Hok : SegModel.name_ok nm = true) by (apply (nk_done nm (Datatypes.S k)); [lia | exact HM]).
  rewrite Hok. cbn [Z.b2z].
  apply (nk_epi W ly S mem0 md0 regs0 _ _ _ 1 HI2).
  + rewrite (HK 2%bv) by (cbv; tauto). exact H2.
  + rewrite R10. reflexivity.
  + lia.
  + intros r Hr. rewrite (HK r) by (cbv in Hr |- *; tauto). apply HK0. exact Hr.
  + exact Hra.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* NK_R, 0x89dc4, back from isalnum with a0 = r *)
Definition ss_nk_r : sstate := mkSS NK_R sr_atoms [] None
(mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 4096 (2^47 - 1) 0); (9%nat, mkAF SB SB 0);
          (18%nat, mkAF 4096 (2^47 - 1) 0); (19%nat, mkAF 50 50 0); (20%nat, mkAF NK_MASK NK_MASK 0);
          (21%nat, mkAF 1 255 0)] [] []).
Definition NK_KR : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma nk_after : forall (nm : list Z) W ly S mem0 md0 regs0 regs memc mdc s k (r : Z),
nk_inv ly S W mem0 md0 regs0 memc mdc -> YK0s.ret_ok (getr regs0 1) ->
nk_str W mem0 (spZ regs0) s nm -> (k < length nm)%nat ->
nk_regsL regs0 regs (s + Z.of_nat k + 1) (nth k nm 0) ->
getr regs 10 = w64 r -> 0 <= r < 2 ^ 64 -> (r <> 0 <-> SegModel.isalnum (nth k nm 0) = true) ->
SegModel.name_ok nm = forallb nk_ch (skipn k nm) ->
((Datatypes.S k < length nm)%nat -> SegModel.name_ok nm = forallb nk_ch (skipn (Datatypes.S k) nm) ->
  forall regs' memc' mdc', nk_inv ly S W mem0 md0 regs0 memc' mdc' ->
  nk_regsL regs0 regs' (s + Z.of_nat (Datatypes.S k) + 1) (nth (Datatypes.S k) nm 0) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + NK_L)) memc' (seg_rom SEGS)) mdc')
    (nk_post regs0 ly S W mem0 md0 (Z.b2z (SegModel.name_ok nm)))) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + NK_R)) memc (seg_rom SEGS)) mdc)
(nk_post regs0 ly S W mem0 md0 (Z.b2z (SegModel.name_ok nm))).
Proof using LAWS HSTK.
intros nm W ly S mem0 md0 regs0 regs memc mdc s k r HI Hra HSTR Hk HRL H10 Hr HAL HM HNEXT.
pose proof HRL as (H2 & H9 & H19 & H20 & H8 & H18 & H21 & HK0).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HI as (HJ & HLOW & HSV).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HSTR as (HB0 & HNZ & HRA & Hs4 & Hs47 & HWIN).
set (n := length nm) in *. set (c := nth k nm 0) in *. set (p := s + Z.of_nat k + 1) in *.
pose proof (nk_str_byte W mem0 (spZ regs0) s nm k HSTR Hk) as Hc.
assert (Ek : nth_error nm k = Some c) by (apply nk_nth_error; exact Hk).
remember (Eimg (Ereg regs [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EN : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> (k0 < 32)%nat -> ew E k0 = getr regs r0).
{ intros k0 r0 Hk0 Hk32. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk0. }
assert (E2 : ew E 2 = w64 (spZ regs0 - 64)) by (rewrite (EN 2%nat 2%bv eq_refl) by lia; exact H2).
assert (E8 : ew E 8 = w64 p) by (rewrite (EN 8%nat 8%bv eq_refl) by lia; exact H8).
assert (E9 : ew E 9 = w64 SB) by (rewrite (EN 9%nat 9%bv eq_refl) by lia; exact H9).
assert (E10 : ew E 10 = w64 r) by (rewrite (EN 10%nat 10%bv eq_refl) by lia; exact H10).
assert (E18 : ew E 18 = w64 p) by (rewrite (EN 18%nat 18%bv eq_refl) by lia; exact H18).
assert (E19 : ew E 19 = w64 50) by (rewrite (EN 19%nat 19%bv eq_refl) by lia; exact H19).
assert (E20 : ew E 20 = w64 NK_MASK) by (rewrite (EN 20%nat 20%bv eq_refl) by lia; exact H20).
assert (E21 : ew E 21 = w64 c) by (rewrite (EN 21%nat 21%bv eq_refl) by lia; exact H21).
assert (HS : st_ok_pi SEGS VAL E ss_nk_r (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + NK_R)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_nk_r. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint]. exact I.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E8, E9, E18, E19, E20, E21. unfold w64, NK_MASK. rewrite !unsigned_lit_small by (unfold SB; subst p; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (Hm16 : (spZ regs0 - 64) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
  subst p. revert Hslo Hshi H47 Hceil C1 Hstk0 Hm16 Hs4 Hs47 Hc HSTK. clear - Hk. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
clear HE.
assert (SHOK : sh_ok SEGS (SOff 9 0) [] E (mrestrict (w_H W) memc)) by constructor.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a0 <> 0: c is alphanumeric *)
  rewrite branch_ne_U, (U_atom E 10 r E10), U_lit in Hc0 by lia.
  assert (Hr0 : r <> 0) by (destruct (Z.eqb_spec r 0); [discriminate | assumption]).
  assert (HOK : nk_ch c = true) by (apply nk_ch_alnum; apply HAL; exact Hr0).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan NK_N.
  { awr_ok_tac. }
  pose proof (nk_inv_run ly S W mem0 md0 regs0 memc mdc (ms_mem ms) _ E [] HI HJ HFr ltac:(vm_compute; reflexivity)) as HI1.
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => assert (HAE2 : env_agree 32 (Ereg regs []) Ecur) by (env_agree_chain HAE) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ NK_KR HS HAE2 ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  pmkst HS.
  apply (nk_next nm W ly S mem0 md0 regs0 _ _ _ s k c HI1 Hra HSTR Hk).
  + refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); try (rewrite HK by (cbv; tauto); assumption).
    intros r0 Hr0'. rewrite HK by (cbv in Hr0' |- *; tauto). apply HK0. exact Hr0'.
  + exact (nk_step_ok nm k c Ek HM HOK).
  + exact HNEXT.
- (* a0 = 0: c is not alphanumeric *)
  rewrite branch_ne_U, (U_atom E 10 r E10), U_lit in Hc0 by lia.
  assert (Hr0 : r = 0) by (destruct (Z.eqb_spec r 0); [assumption | discriminate]).
  assert (HNA : SegModel.isalnum c = false)
    by (apply not_true_is_false; intros EA; exact (proj2 HAL EA Hr0)).
  assert (NC : nk_ch c = nk_sp c) by (apply nk_ch_sp; exact HNA).
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac. }
  pose proof (nk_inv_run ly S W mem0 md0 regs0 memc mdc (ms_mem ms) _ E [] HI HJ HFr ltac:(vm_compute; reflexivity)) as HI1.
  clear HF HFr HG.
  assert (HU21 : U E (SOff 21 (-45)) = (c - 45) mod 2 ^ 64).
  { rewrite U_SOff, E21. unfold w64. rewrite unsigned_lit_small by lia. unfold zcanon, M64. f_equal; lia. }
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* (c - 45) above 50 unsigned: c is outside '-' .. '_', the answer is 0 *)
    rewrite branch_ltu_U, (U_atom E 19 50 E19), HU21 in Hc1 by lia.
    assert (Hout : 50 < (c - 45) mod 2 ^ 64) by (apply Z.ltb_lt; exact Hc1).
    pose proof (nk_rng_out c ltac:(lia) Hout) as Ho.
    assert (HNOK : nk_ch c = false) by (rewrite NC; apply nk_sp_out; exact Ho).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan NK_X.
    { awr_ok_tac. }
    pose proof (nk_inv_run ly S W mem0 md0 regs0 (ms_mem ms) _ (ms_mem ms0) _ _ _ HI1 HJ HFr ltac:(vm_compute; reflexivity)) as HI2.
    clear HI1 HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => assert (HAE2 : env_agree 32 (Ereg regs []) Ecur) by (env_agree_chain HAE) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ (10%bv :: 2%bv :: NK_K0) HS HAE2 ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
    pmkst HS.
    rewrite (nk_step_fail nm k c Ek HM HNOK). cbn [Z.b2z].
    apply (nk_epi W ly S mem0 md0 regs0 _ _ _ 0 HI2).
    * rewrite (HK 2%bv) by (cbv; tauto). exact H2.
    * rewrite (HK 10%bv) by (cbv; tauto). rewrite H10, Hr0. reflexivity.
    * lia.
    * intros r0 Hr0'. rewrite (HK r0) by (cbv in Hr0' |- *; tauto). apply HK0. exact Hr0'.
    * exact Hra.
  + (* 45 <= c <= 95: the mask bit *)
    rewrite branch_ltu_U, (U_atom E 19 50 E19), HU21 in Hc1 by lia.
    assert (Hin : (c - 45) mod 2 ^ 64 <= 50) by (apply Z.ltb_ge; exact Hc1).
    pose proof (nk_rng_in c ltac:(lia) Hin) as Hi.
    (* the shift the mask takes: the `srl` masks its amount to 6 bits, and c - 45 is at most 50 *)
    assert (Hsh : zcanon (Z.shiftr NK_MASK (Z.land (c - 45) 63)) = Z.shiftr NK_MASK (c - 45)).
    { replace (Z.land (c - 45) 63) with (c - 45)
        by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
      assert (Hp : 1 <= 2 ^ (c - 45)) by (change 1 with (2 ^ 0) at 1; apply Z.pow_le_mono_r; lia).
      unfold zcanon, M64. apply Z.mod_small. rewrite Z.shiftr_div_pow2 by lia.
      split; [apply Z.div_pos; [unfold NK_MASK; lia | lia]|].
      apply Z.le_lt_trans with NK_MASK; [apply Z.div_le_upper_bound; [lia|] | unfold NK_MASK; lia].
      unfold NK_MASK. nia. }
    paj_run_tok RUN HS HJ SHOK Bspan.
    { awr_ok_tac. }
    pose proof (nk_inv_run ly S W mem0 md0 regs0 (ms_mem ms) _ (ms_mem ms0) _ _ _ HI1 HJ HFr ltac:(vm_compute; reflexivity)) as HI2.
    clear HI1 HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* bit clear: c is not one of "-.:_", the answer is 0 *)
      rewrite branch_eq_U, U_and_lit, U_SAlu in Hc2 by lia. cbn [zalu_raw] in Hc2.
      rewrite (U_atom E 20 NK_MASK E20), HU21, (Z.mod_small (c - 45) (2 ^ 64)), Hsh, (U_lit E 0) in Hc2
        by (unfold NK_MASK; lia).
      assert (Hbit : Z.land (Z.shiftr NK_MASK (c - 45)) 1 = 0) by (apply Z.eqb_eq; exact Hc2).
      assert (HNOK : nk_ch c = false) by (rewrite NC; apply (proj1 (nk_bit_z c Hi)); exact Hbit).
      paj_run_to_tok RUNTO HS HJ SHOK Bspan NK_X.
      { awr_ok_tac. }
      pose proof (nk_inv_run ly S W mem0 md0 regs0 (ms_mem ms0) _ (ms_mem ms1) _ _ _ HI2 HJ HFr ltac:(vm_compute; reflexivity)) as HI3.
      clear HI2 HF HFr HG.
      lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => assert (HAE2 : env_agree 32 (Ereg regs []) Ecur) by (env_agree_chain HAE) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ (10%bv :: 2%bv :: NK_K0) HS HAE2 ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
      pmkst HS.
      rewrite (nk_step_fail nm k c Ek HM HNOK). cbn [Z.b2z].
      apply (nk_epi W ly S mem0 md0 regs0 _ _ _ 0 HI3).
      -- rewrite (HK 2%bv) by (cbv; tauto). exact H2.
      -- rewrite (HK 10%bv) by (cbv; tauto). rewrite H10, Hr0. reflexivity.
      -- lia.
      -- intros r0 Hr0'. rewrite (HK r0) by (cbv in Hr0' |- *; tauto). apply HK0. exact Hr0'.
      -- exact Hra.
    * (* bit set: c is one of "-.:_" *)
      rewrite branch_eq_U, U_and_lit, U_SAlu in Hc2 by lia. cbn [zalu_raw] in Hc2.
      rewrite (U_atom E 20 NK_MASK E20), HU21, (Z.mod_small (c - 45) (2 ^ 64)), Hsh, (U_lit E 0) in Hc2
        by (unfold NK_MASK; lia).
      assert (Hbit : Z.land (Z.shiftr NK_MASK (c - 45)) 1 <> 0) by (apply Z.eqb_neq; exact Hc2).
      assert (HOK : nk_ch c = true).
      { rewrite NC. destruct (nk_sp c) eqn:ES; [reflexivity|]. exfalso. apply Hbit. apply (proj2 (nk_bit_z c Hi)). exact ES. }
      paj_run_to_tok RUNTO HS HJ SHOK Bspan NK_N.
      { awr_ok_tac. }
      pose proof (nk_inv_run ly S W mem0 md0 regs0 (ms_mem ms0) _ (ms_mem ms1) _ _ _ HI2 HJ HFr ltac:(vm_compute; reflexivity)) as HI3.
      clear HI2 HF HFr HG.
      lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => assert (HAE2 : env_agree 32 (Ereg regs []) Ecur) by (env_agree_chain HAE) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ NK_KR HS HAE2 ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
      pmkst HS.
      apply (nk_next nm W ly S mem0 md0 regs0 _ _ _ s k c HI3 Hra HSTR Hk).
      -- refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); try (rewrite HK by (cbv; tauto); assumption).
         intros r0 Hr0'. rewrite HK by (cbv in Hr0' |- *; tauto). apply HK0. exact Hr0'.
      -- exact (nk_step_ok nm k c Ek HM HOK).
      -- exact HNEXT.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* NK_B, 0x89d94: lbu s5,0(a0) (the byte the first inline check guards); beqz s5 -> 0x89e18 (a0 := 0, NK_X) *)
Definition nk_b_region : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition ss_nk_b : sstate := mkSS NK_B sr_atoms [nk_b_region] None
(mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF SB SB 0); (10%nat, mkAF 4096 (2^47 - 1) 0);
          (32%nat, mkAF 0 255 0)] [] []).
Definition NK_KB : list (bv 5) := [2; 3; 4; 9; 22; 23; 24; 25; 26; 27]%bv.

Lemma nk_b : forall (nm : list Z) W ly S mem0 md0 regs0 regs memc mdc s,
nk_inv ly S W mem0 md0 regs0 memc mdc -> YK0s.ret_ok (getr regs0 1) ->
nk_str W mem0 (spZ regs0) s nm ->
getr regs 2 = w64 (spZ regs0 - 64) -> getr regs 9 = w64 SB -> getr regs 10 = w64 s ->
(forall r, In r NK_K0 -> getr regs r = getr regs0 r) ->
((0 < length nm)%nat -> forall regs' memc' mdc', nk_inv ly S W mem0 md0 regs0 memc' mdc' ->
  nk_regsL regs0 regs' (s + 1) (nth 0 nm 0) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + NK_L)) memc' (seg_rom SEGS)) mdc')
    (nk_post regs0 ly S W mem0 md0 (Z.b2z (SegModel.name_ok nm)))) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + NK_B)) memc (seg_rom SEGS)) mdc)
(nk_post regs0 ly S W mem0 md0 (Z.b2z (SegModel.name_ok nm))).
Proof using LAWS HSTK.
intros nm W ly S mem0 md0 regs0 regs memc mdc s HI Hra HSTR H2 H9 H10 HK0 HNEXT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HI as (HJ & HLOW & HSV).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HSTR as (HB0 & HNZ & HRA & Hs4 & Hs47 & HWIN).
set (b := nth 0 (nm ++ [0]) 0).
assert (Rb : aview SEGS (w_H W) memc s = Some b).
{ subst b. replace s with (s + Z.of_nat 0) at 1 by lia.
  apply (nk_str_low ly S W mem0 md0 regs0 memc mdc (spZ regs0) s nm 0 HI eq_refl HSTR ltac:(lia)). }
pose proof (nk_aview_byte _ _ _ _ _ Rb) as Hb.
remember (Eimg (Ereg regs [Z_to_bv 64 b])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 b]) E) by (rewrite HE; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EN : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> (k0 < 32)%nat -> ew E k0 = getr regs r).
{ intros k0 r Hk0 Hk32. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk0. }
assert (E2 : ew E 2 = w64 (spZ regs0 - 64)) by (rewrite (EN 2%nat 2%bv eq_refl) by lia; exact H2).
assert (E9 : ew E 9 = w64 SB) by (rewrite (EN 9%nat 9%bv eq_refl) by lia; exact H9).
assert (E10 : ew E 10 = w64 s) by (rewrite (EN 10%nat 10%bv eq_refl) by lia; exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 b) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HS : st_ok_pi SEGS VAL E ss_nk_b (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + NK_B)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_nk_b. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, nk_b_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E10. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ s 0 1 (SOff 32 0) b); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  intros k0 Hk0. replace k0 with 0%nat by lia. rewrite !Z.add_0_r. rewrite nk_le_byte1 by exact Hb.
  apply nk_mbyte_of_aview; [exact Rb | exact Hb].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E9, E10, E32. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (Hm16 : (spZ regs0 - 64) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
  revert Hslo Hshi H47 Hceil C1 Hstk0 Hm16 Hs4 Hs47 Hb HSTK. clear. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
clear HE.
assert (SHOK : sh_ok SEGS (SOff 9 0) [] E (mrestrict (w_H W) memc)) by constructor.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
pose proof (nk_inv_run ly S W mem0 md0 regs0 memc mdc (ms_mem ms) _ E [nk_b_region] HI HJ HFr ltac:(vm_compute; reflexivity)) as HI1.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s[0] = 0: the empty string, the answer is 0 *)
  rewrite branch_eq_U in Hc. unfold U in Hc. cbn [sv_denot ew ewset Nat.eqb] in Hc.
  rewrite E32 in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc.
  rewrite !unsigned_lit_small in Hc by lia.
  assert (Hb0 : b = 0) by (destruct (Z.eqb_spec b 0); [assumption | discriminate]).
  assert (Hnil : nm = []).
  { apply length_zero_iff_nil. symmetry. apply (proj1 (nk_nth_zero nm 0 HNZ ltac:(lia))). exact Hb0. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan NK_X.
  { awr_ok_tac. }
  pose proof (nk_inv_run ly S W mem0 md0 regs0 (ms_mem ms) _ (ms_mem ms0) _ _ _ HI1 HJ HFr ltac:(vm_compute; reflexivity)) as HI2.
  clear HI1 HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 b]) Ecur) by (env_agree_chain HAE) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ NK_KB HS HAE2 ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) R10.
  pmkst HS.
  rewrite Hnil. rewrite nk_name_ok_nil. cbn [Z.b2z].
  apply (nk_epi W ly S mem0 md0 regs0 _ _ _ 0 HI2).
  + rewrite (HK 2%bv) by (cbv; tauto). exact H2.
  + rewrite R10. reflexivity.
  + lia.
  + intros r Hr. rewrite (HK r) by (cbv in Hr |- *; tauto). apply HK0. exact Hr.
  + exact Hra.
- (* s[0] <> 0: the loop is entered *)
  rewrite branch_eq_U in Hc. unfold U in Hc. cbn [sv_denot ew ewset Nat.eqb] in Hc.
  rewrite E32 in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc.
  rewrite !unsigned_lit_small in Hc by lia.
  assert (Hb0 : b <> 0) by (destruct (Z.eqb_spec b 0); [discriminate | assumption]).
  assert (Hlt : (0 < length nm)%nat).
  { destruct (Nat.eq_dec 0 (length nm)) as [Ei|Ei]; [|lia]. exfalso. apply Hb0. subst b.
    apply (proj2 (nk_nth_zero nm 0 HNZ ltac:(lia))). exact Ei. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan NK_L.
  { awr_ok_tac. }
  pose proof (nk_inv_run ly S W mem0 md0 regs0 (ms_mem ms) _ (ms_mem ms0) _ _ _ HI1 HJ HFr ltac:(vm_compute; reflexivity)) as HI2.
  clear HI1 HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 b]) Ecur) by (env_agree_chain HAE) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ NK_KB HS HAE2 ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (8%bv : bv 5) R8. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
  prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21.
  rewrite E10 in R8, R18. rewrite E32 in R21. unfold w64 in R8, R18.
  rewrite unsigned_lit_small in R8, R18 by lia.
  pmkst HS.
  apply (HNEXT Hlt _ _ _ HI2).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  + rewrite (HK 2%bv) by (cbv; tauto). exact H2.
  + rewrite (HK 9%bv) by (cbv; tauto). exact H9.
  + rewrite R19. reflexivity.
  + rewrite R20. reflexivity.
  + rewrite R8. unfold w64. f_equal; lia.
  + rewrite R18. unfold w64. f_equal; lia.
  + rewrite R21. subst b. rewrite nk_nth_app by exact Hlt. reflexivity.
  + intros r Hr. rewrite (HK r) by (cbv in Hr |- *; tauto). apply HK0. exact Hr.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* the entry 0x89d58 .. NK_B: the prologue's seven stores, the shadow base through the GOT word and the cell,
   and the first inline check *)
Definition nk_regions0 : smem := [stack_region 64; got_regionP; bcell_regionP 32].
Definition nk_facts0 : facts :=
mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 (2^47 - 1) 0); (32%nat, mkAF SB SB 0)] [] [].
Definition ss_nk0 : sstate := mkSS AF_name_ok sr_atoms nk_regions0 None nk_facts0.

Lemma nk_head : forall W ly S regs mem md ch s nm,
afn_pre SEGS B STK ly S W regs mem md ch ->
getr regs 10 = w64 s -> nk_str W mem (spZ regs) s nm ->
((0 < length nm)%nat -> forall regs' memc' mdc', nk_inv ly S W mem md regs memc' mdc' ->
  nk_regsL regs regs' (s + 1) (nth 0 nm 0) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + NK_L)) memc' (seg_rom SEGS)) mdc')
    (nk_post regs ly S W mem md (Z.b2z (SegModel.name_ok nm)))) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_name_ok) regs mem md)
(nk_post regs ly S W mem md (Z.b2z (SegModel.name_ok nm))).
Proof using LAWS TL HSTK.
intros W ly S regs mem md ch s nm HPRE H10 HSTR HNEXT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HSTR as (HB0 & HNZ & HRA & Hs4 & Hs47 & HWIN).
pose proof (ajournal_init SEGS B STK [] ly S W regs mem md ch HPRE) as HJ.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 12 ltac:(lia)) as HcellR.
unfold kImgEnd in HgotR, HcellR.
pose proof (pal_got_cell B TL) as HgcD.
remember (Eimg (Ereg regs [Z_to_bv 64 SB])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) E) by (rewrite HE; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EN : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> (k0 < 32)%nat -> ew E k0 = getr regs r).
{ intros k0 r Hk0 Hk32. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk0. }
assert (E2 : ew E 2 = getr regs 2) by exact (EN 2%nat 2%bv eq_refl ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E10 : ew E 10 = w64 s) by (rewrite (EN 10%nat 10%bv eq_refl) by lia; exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (HS : st_ok_pi SEGS VAL E ss_nk0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_name_ok)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_nk0. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold nk_regions0, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    pose proof (pa_val_range (A_OBJ 12)) as HV12.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents.
  unfold nk_regions0, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 Hstk0 HgotR HcellR HgcD HSTK. unfold kImgEnd. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [nk_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E10, E32. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil C1 Hstk0 Hal16 Hs4 Hs47 HSTK. clear. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
clear HE.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) mem)) by constructor.
assert (HBx : U E (SOff 32 0) = SHADOW_OFF) by (rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
unfold cfg_at. change (w64 (BASE + AF_name_ok)) with (Z_to_bv 64 (BASE + AF_name_ok)).
paj_run_to_tok RUNTO HS HJ SHOK Bspan NK_B.
{ cbn [ms_mem mkst]. apply (nk_obl_rd E W mem (SOff 32 0) (SOff 10 0) s 1 HBx);
    [apply U_atom; [exact E10 | lia]|].
  apply (range_addressable_sub _ _ s (Z.of_nat (length nm) + 1)); [exact HRA | lia | lia]. }
{ unfold ss_nk0, nk_regions0; cbn [ss_mem].
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ =>
  assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) Ecur) by (env_agree_chain HAE) end.
assert (HSV : nk_saved W (ms_mem ms) (spZ regs) regs)
  by (apply (nk_saved_of_stack _ W (ms_mem ms) regs [Z_to_bv 64 SB] HR0);
      [cbn [ew ewset Nat.eqb]; exact Usp | exact HAE2]).
assert (HLOW : nk_low W mem (ms_mem ms)).
{ apply (nk_low_frame _ _ W mem mem (ms_mem ms) HFr); [|intros a0 Ha0; reflexivity].
  intros a0 Ha0 (r0 & Hr0 & Hra0). cbn in Hr0.
  repeat (destruct Hr0 as [<- | Hr0];
    [ cbv [stack_region got_regionP bcell_regionP] in Hra0;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra0; try rewrite Usp in Hra0; lia |]).
  destruct Hr0. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ NK_K0 HS HAE2 ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (2%bv : bv 5) R2. prreg HS (9%bv : bv 5) R9. prreg HS (10%bv : bv 5) R10.
assert (HG2 : getr (ms_regs ms) 2 = w64 (spZ regs - 64)) by (rewrite R2, Usp; unfold w64; f_equal; lia).
assert (HG9 : getr (ms_regs ms) 9 = w64 SB)
  by (rewrite R9; rewrite ?E32; unfold w64;
      first [reflexivity | rewrite unsigned_lit_small by (unfold SB; lia); f_equal; lia]).
assert (HG10 : getr (ms_regs ms) 10 = w64 s) by (rewrite R10; rewrite ?E10; reflexivity).
pmkst HS.
apply (nk_b nm W ly S mem md regs (ms_regs ms) (ms_mem ms) _ s);
  [ split; [exact HJ | split; [exact HLOW | exact HSV]]
  | exact Hra | exact HSTR | exact HG2 | exact HG9 | exact HG10 | exact HK | exact HNEXT ].
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The contract of the callee: the interceptor layer's interface row 9, musl's isalnum at image A 0x901a0 (a direct call, not
   intercepted; a 28-byte leaf that touches no stack and no memory), at the listing's call target
   `pa_sigma SS_isalnum`. Its text is lib/A/Rt/RtSeg.v's (the interceptor-layer commit ab5c95b8897a). *)
Hypothesis ISALNUM : forall fx0 : YK11.FPState, @RtSeg.aisalnum_realizes fx0 rc SEGS B (SIGMA SS_isalnum).

(* NK_L, 0x89dbc: zext.b a0,s5; jal isalnum; the answer comes back at NK_R *)
Definition ss_nk_l : sstate := mkSS NK_L sr_atoms [] None
(mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 4096 (2^47 - 1) 0); (9%nat, mkAF SB SB 0);
          (18%nat, mkAF 4096 (2^47 - 1) 0); (19%nat, mkAF 50 50 0); (20%nat, mkAF NK_MASK NK_MASK 0);
          (21%nat, mkAF 1 255 0)] [] []).

Lemma nk_loop : forall (j : nat) (nm : list Z) W ly S mem0 md0 regs0 regs memc mdc s k,
(k + j = length nm)%nat -> (0 < j)%nat ->
nk_inv ly S W mem0 md0 regs0 memc mdc -> YK0s.ret_ok (getr regs0 1) ->
getr regs0 3 = w64 (as_gp B) -> getr regs0 4 = w64 (as_tp B) ->
nk_str W mem0 (spZ regs0) s nm ->
nk_regsL regs0 regs (s + Z.of_nat k + 1) (nth k nm 0) ->
SegModel.name_ok nm = forallb nk_ch (skipn k nm) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + NK_L)) memc (seg_rom SEGS)) mdc)
(nk_post regs0 ly S W mem0 md0 (Z.b2z (SegModel.name_ok nm))).
Proof using LAWS TL HSTK HSTKE ISALNUM.
induction j as [|j IH]; intros nm W ly S mem0 md0 regs0 regs memc mdc s k Hkj Hj HI Hra Hgp0 Htp0 HSTR HRL HM;
[lia|].
pose proof HRL as (H2 & H9 & H19 & H20 & H8 & H18 & H21 & HK0).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HI as (HJ & HLOW & HSV).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HSTR as (HB0 & HNZ & HRA & Hs4 & Hs47 & HWIN).
assert (HSTKn : STK = 4160) by (unfold STK, STK_name_ok, ESTACK; reflexivity).
assert (Hk : (k < length nm)%nat) by lia.
set (c := nth k nm 0) in *. set (p := s + Z.of_nat k + 1) in *.
pose proof (nk_str_byte W mem0 (spZ regs0) s nm k HSTR Hk) as Hc.
remember (Eimg (Ereg regs [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EN : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> (k0 < 32)%nat -> ew E k0 = getr regs r0).
{ intros k0 r0 Hk0 Hk32. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk0. }
assert (E2 : ew E 2 = w64 (spZ regs0 - 64)) by (rewrite (EN 2%nat 2%bv eq_refl) by lia; exact H2).
assert (E8 : ew E 8 = w64 p) by (rewrite (EN 8%nat 8%bv eq_refl) by lia; exact H8).
assert (E9 : ew E 9 = w64 SB) by (rewrite (EN 9%nat 9%bv eq_refl) by lia; exact H9).
assert (E18 : ew E 18 = w64 p) by (rewrite (EN 18%nat 18%bv eq_refl) by lia; exact H18).
assert (E19 : ew E 19 = w64 50) by (rewrite (EN 19%nat 19%bv eq_refl) by lia; exact H19).
assert (E20 : ew E 20 = w64 NK_MASK) by (rewrite (EN 20%nat 20%bv eq_refl) by lia; exact H20).
assert (E21 : ew E 21 = w64 c) by (rewrite (EN 21%nat 21%bv eq_refl) by lia; exact H21).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 64) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ss_nk_l (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + NK_L)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_nk_l. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint]. exact I.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E8, E9, E18, E19, E20, E21. unfold w64, NK_MASK. rewrite !unsigned_lit_small by (unfold SB; subst p; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (Hm16 : (spZ regs0 - 64) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
  subst p. revert Hslo Hshi H47 Hceil C1 Hstk0 Hm16 Hs4 Hs47 Hc HSTK HSTKE. clear - Hk. unfold SB, ESTACK. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
clear HE.
assert (SHOK : sh_ok SEGS (SOff 9 0) [] E (mrestrict (w_H W) memc)) by constructor.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
pose proof (nk_inv_run ly S W mem0 md0 regs0 memc mdc (ms_mem ms) _ E [] HI HJ HFr ltac:(vm_compute; reflexivity)) as HI1.
clear HF HFr HG.
pose proof HI1 as (_ & HLOW1 & HSV1).
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (10%bv : bv 5) R10.
rewrite E2 in R2.
rewrite (EN 3%nat 3%bv eq_refl), (HK0 3%bv ltac:(cbv; tauto)), Hgp0 in R3 by lia.
rewrite (EN 4%nat 4%bv eq_refl), (HK0 4%bv ltac:(cbv; tauto)), Htp0 in R4 by lia.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs0 + -64)
  by (unfold spZ at 1; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hraw : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite R1; apply ret_ok_codeptr_v; [unfold NK_R; lia | reflexivity]).
assert (R10c : getr (ms_regs ms) 10 = w64 c).
{ rewrite R10, ?E21. unfold w64. apply (nk_zext_byte E c). lia. }
lazymatch type of HS with st_ok _ ?Ecur _ _ => assert (HAEc : env_agree 32 (Ereg regs []) Ecur) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs _ NK_KR HS HAEc ltac:(vm_compute; reflexivity)) as KA.
cbn [ms_regs restrict] in KA.
pmkst HS.
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) ESTACK (fun _ => False) (SIGMA SS_isalnum)
    W (ms_regs ms) (ms_mem ms) STK (spZ regs0) [] ly S W mem0 md0 [] ly S _ 0 (-64) (getr (ms_regs ms) 1)
    (fun regs' (_ : word -> option byte) => getr regs' 10 <> w64 0 <-> RtSeg.alnum_b c = true) HJ).
  1: exact Hsp1. 1: reflexivity. 1: lia. 1: unfold ESTACK; lia. 1: unfold ESTACK; lia. 1: reflexivity.
  1: intros a' [].
  eapply (ISALNUM _ ly S W (ms_regs ms) (ms_mem ms) _ c).
  - eapply (ecall_pre_stk_at SEGS B ESTACK STK (spZ regs0) [] ly S W mem0 md0 [] ly S W (ms_mem ms) _ 0
      (ms_regs ms) (-64) HJ);
    [exact Hsp1 | reflexivity | lia | lia | unfold ESTACK; lia | exact Hraw | exact R3 | exact R4].
  - exact R10c.
  - lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha2 & Hfr2).
rewrite R1.
assert (HI2 : nk_inv ly S W mem0 md0 regs0 mem2 md2).
{ split; [exact HJ2|]. unfold ESTACK in Hfr2. split.
  - apply (nk_low_kept W mem0 (ms_mem ms) mem2); [|exact HLOW1].
    intros a' Ha'. apply Hfr2; [lia | lia | intros []].
  - apply (nk_saved_kept W (ms_mem ms) mem2); [|exact HSV1].
    intros a' Ha'. apply Hfr2; [lia | lia | intros []]. }
assert (P2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r).
{ intros r Hr. specialize (HP2 (bv_unsigned r) Hr). rewrite !Z_to_bv_bv_unsigned in HP2. exact HP2. }
assert (CH2 : forall r, In r NK_KR -> getr regs2 r = getr regs r).
{ intros r Hr. cbv [NK_KR In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ rewrite P2 by (unfold acallee_saved;
        match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
          change (bv_unsigned x) with v end; lia);
      apply KA; cbv; tauto |]). destruct Hr. }
set (r2 := bv_unsigned (getr regs2 10)).
assert (Hr2 : getr regs2 10 = w64 r2) by (subst r2; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Hr2r : 0 <= r2 < 2 ^ 64) by (subst r2; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Hq;
  change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (HAL : r2 <> 0 <-> SegModel.isalnum c = true).
{ change (RtSeg.alnum_b c) with (isalnum_c.alnum_b c) in Ha2.
  rewrite <- (SegBridge.bridge_isalnum c ltac:(lia)). split.
  - intros Hne. apply Ha2. rewrite Hr2. unfold w64. intros Heq.
    apply Hne. apply (f_equal bv_unsigned) in Heq. rewrite !unsigned_lit_small in Heq by lia. exact Heq.
  - intros Hal Hz. apply (proj2 Ha2 Hal). rewrite Hr2, Hz. reflexivity. }
apply (nk_after nm W ly S mem0 md0 regs0 regs2 mem2 md2 s k r2 HI2 Hra HSTR Hk);
  [ refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))) | exact Hr2 | exact Hr2r | exact HAL
  | exact HM | ].
- rewrite CH2 by (cbv; tauto). exact H2.
- rewrite CH2 by (cbv; tauto). exact H9.
- rewrite CH2 by (cbv; tauto). exact H19.
- rewrite CH2 by (cbv; tauto). exact H20.
- rewrite CH2 by (cbv; tauto). exact H8.
- rewrite CH2 by (cbv; tauto). exact H18.
- rewrite CH2 by (cbv; tauto). exact H21.
- intros r0 Hr0. rewrite CH2 by (cbv in Hr0 |- *; tauto). apply HK0. exact Hr0.
- (* the byte passed: the next turn of the loop, by the induction hypothesis at k + 1 *)
  intros Hlt Hinv regs' memc' mdc' HI' HRL'.
  apply (IH nm W ly S mem0 md0 regs0 regs' memc' mdc' s (Datatypes.S k));
  [ lia | lia | exact HI' | exact Hra | exact Hgp0 | exact Htp0 | exact HSTR | exact HRL' | exact Hinv ].
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* the contract's premises, in the walk's terms *)
Lemma nk_pre_str : forall ly S W regs mem md s nm,
AR SEGS B ly S W mem md -> astk_ok STK ly (spZ regs) ->
name_ok_pre SEGS B ly S W mem regs s nm ->
nk_str W mem (spZ regs) s nm.
Proof using LAWS HSTK.
intros ly S W regs mem md s nm HAR Hstk (Hs0 & (HZS & HNZ) & HAD & HDST).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HAD as (Hq0 & Hq63 & Hmr & HRA & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hup : s + Z.of_nat (length nm) + 1 <= 2 ^ 47 - 1).
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr. lia. }
assert (Hlo : 4096 <= s /\ (s + Z.of_nat (length nm) + 1 <= spZ regs - STK \/ spZ regs <= s)).
{ destruct HDST as [((cid & pos & Hin & Hfa & Hfb) & _) | [((b0 & m0 & Hin & Hb0 & Hb1) & _) | (Hd1 & Hd2 & _)]].
  - destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf4 & Hfc & _). split; [lia | left; lia].
  - destruct (al_blocks _ _ LAWS ly S W mem md b0 m0 HAR Hin) as (_ & Hp4 & Hpc & _).
    pose proof (req_size_pos0 m0) as Hrq. unfold req_size in *. split; [lia|]. left.
    destruct (Z.eqb_spec m0 0); lia.
  - split; [lia | right; lia]. }
split; [|split; [exact HNZ | split; [exact HRA | split; [lia | split; [exact Hup | exact (proj2 Hlo)]]]]].
intros i Hi. apply HZS. rewrite length_app. cbn [length]. lia.
Qed.

Theorem name_ok_walk : name_ok_contract SEGS B (BASE + AF_name_ok) STK RLO_A RHI_A.
Proof using LAWS TL HSTK HSTKE ISALNUM.
unfold name_ok_contract.
intros ly S W regs mem md ch s nm HPRE HROD H10 Hs64 HPRES HEV.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (nk_pre_str ly S W regs mem md s nm HAR Hstk HPRES) as HSTR.

pose proof HSTR as (HB0 & HNZ & HRA & Hs4 & Hs47 & HWIN).
eapply SRr_mono.
- apply (nk_head W ly S regs mem md ch s nm HPRE H10 HSTR).
  intros Hlt regs' memc' mdc' HI' HRL'.
  apply (nk_loop (length nm) nm W ly S mem md regs regs' memc' mdc' s 0);
  [ lia | lia | exact HI' | exact Hra | exact Hgp | exact Htp | exact HSTR | | ].
  + change (s + Z.of_nat 0 + 1) with (s + 0 + 1). replace (s + 0 + 1) with (s + 1) by lia. exact HRL'.
  + apply nk_start; [intros Enil; rewrite Enil in Hlt; cbn [length] in Hlt; lia | exact HNZ].
- cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ & HP & (HQ & -> & -> & HKEPT)).
  exists ly, S, regs', mem', md'. split; [reflexivity|]. split; [exact HJ|]. split; [exact HP|].
  split; [rewrite nk_b2z_eq; exact HQ|].
  split; [intros a Ha Hw _; exact (HKEPT a Ha Hw)|].
  split; [apply Permutation_refl|]. split; [reflexivity | exists (st_fs S); apply nk_set_fs_id].
Qed.

End e.
End f.
End d.
