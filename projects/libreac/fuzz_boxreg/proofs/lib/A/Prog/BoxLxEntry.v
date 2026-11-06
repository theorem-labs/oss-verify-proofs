(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 1683 of its 1823 lines of code are new or changed and 4913 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaRun PaShadow PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC1g YC1h YC4b YC85 BoxFrame BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxDefs BoxLxSeat ReacBoxregInit Check.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_entry reac_boxreg_init_c BoxregInit Boxreg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The entry phase of the ASan-build walk of fuzz_boxreg's LLVMFuzzerTestOneInput (fuzz_boxreg.asan 0x7ff4c, image A),
   0x7ff4c .. 0x801ec, in the PA engine: gb_entry : gb_from B MT POST (GI_J 0) -> gb_start B MT POST
   (BoxLxDefs.v vocabulary). The phase's own cuts EA (0x7ffc0), EM (0x80118), EI (0x80178) and EC (0x801a4) split it
   into five steps:
   - 0x7ff4c .. 0x7ffc0 (gb_entry_a): the prologue (saves, s0 = sp0, the realigned sp1), the GOT loads of the shadow
     offset and of the use-after-return flag (1: AR's constant cell), the call of __asan_stack_malloc_3 (0x1a0);
   - 0x7ffc0 .. 0x80118 (gb_entry_m): F <> 0 skips the machine-stack frame, the frame's header and its 52 shadow
     bytes (GSH_J), n >> 26 = 0 (n < 2^26), the cursor slots;
   - 0x80118 .. 0x80178 (gb_entry_i): malloc(288) (the NULL branch 0x8011c is refuted by 4096 <= r), the fabric byte
     (n = 0: 0; else its shadow test 0x8014c passes: p is a heap block), the spills of F and F + 64;
   - 0x80178 .. 0x801a4 (gb_entry_c): reac_boxreg_init (r, (int8_t) b), the clamp of the fabric (0x80188);
   - 0x801a4 .. 0x801ec (gb_entry_j): check (r, fabric), the loop's set-up stores (slots 0x10 .. 0x60), s5 = 0. *)

(* ---- the pcs of the entry phase's own cuts (offsets from 0x7ff4c) ---- *)
Definition GE_A : Z := 0x74.    (* 0x7ffc0, back from __asan_stack_malloc_3      *)
Definition GE_M : Z := 0x1cc.   (* 0x80118, jal __wrap_malloc (0x120)           *)
Definition GE_I : Z := 0x22c.   (* 0x80178, jal reac_boxreg_init (r, fabric_in) *)
Definition GE_C : Z := 0x258.   (* 0x801a4, jal check (r, fabric)               *)

Definition SBe : Z := 0x7fff8000.
Definition Bxe : sv := SOff 32 0.
Definition Bspane : Z * Z := (SBe, SBe + 2 ^ 44 - 1).
(* The shadow band of a run that checks no shadow byte and writes the frame's shadow: empty. *)
Definition Bspan0 : Z * Z := (0, 0).

Lemma eb_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma eb_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite eb_land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma eb_rdword_chunk : forall {segs : list Segment} E (H : word -> bool) m n b cs lo hi wlo whi od e,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 8 e)) cs ->
  rdword (aview segs H m) (b + od) = Some (bv_unsigned (sv_denot E e)).
Proof.
intros segs E H m n b cs lo hi wlo whi od e HR Hb Hin.
pose proof (field_of_region_any E _ n b cs lo hi wlo whi od 8%N e HR Hb Hin ltac:(cbn; lia)) as Hv.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Hv. rewrite Z.mod_small in Hv by apply u64_range.
exact (rdword_of_val_mem segs H m _ _ Hv (u64_range _)).
Qed.


(* The first byte of the input, the fabric fuzz_in reads (0 for an empty input), and the cursor after it. *)
Definition eb_b (pl : list byte) : Z := match pl with [] => 0 | x :: _ => bv_unsigned x end.


(* The fabric the harness checks the table against (fuzz_boxreg.c:200), and the table reac_boxreg_init leaves. *)
Definition eb_fab (pl : list byte) : Z :=
  reac_boxreg_init_c.clamp40 (LLVMFuzzerTestOneInput_entry.en_sx (eb_b pl)).
Definition eb_bs (pl : list byte) : list byte := reac_boxreg_init_c.init_bytes (eb_fab pl).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

(* The symbolic state at the first slot: the machine stack's 256 bytes below the caller's sp (the frame the
   prologue stores into), and the GOT words and runtime cells of the shadow base and of the use-after-return flag.
   Atom 32 is SHADOW_OFF, 33 the realigned stack pointer, 34 the use-after-return flag's cell. *)
Definition ss_e0 : sstate :=
  mkSS GP_entry sr_atoms [stack_region 256; got_regionP; bcell_regionP 32; uar_got_regionP 34; uar_cell_regionP 34] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SBe SBe 0); (33%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).


Definition eb_pos (cx : bcx) : Z := if c_n cx =? 0 then 0 else 1.

Definition R2_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 0x98 0 0x98
    [YP09.mkChunk 0x80 (CVal 8 (SOff 22 0)); YP09.mkChunk 0x28 (CVal 8 (SOff 22 0));
     YP09.mkChunk 0x88 (CVal 8 (SOff 20 0)); YP09.mkChunk 0x90 (CVal 8 (SOff 21 0))].
Definition R2_in : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition ss_e2_0 : sstate :=
  mkSS 0x1d0 sr_atoms [R2_sp] None
    (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF 4096 140737479966720 4); (18%nat, mkAF SBe SBe 0);
              (21%nat, mkAF 0 0 0); (32%nat, mkAF SBe SBe 0)] [] []).
Definition ss_e2_1 : sstate :=
  mkSS 0x1d0 sr_atoms [R2_sp; R2_in] None
    (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF 4096 140737479966720 4); (18%nat, mkAF SBe SBe 0);
              (20%nat, mkAF 4096 140737479966720 4); (21%nat, mkAF 1 (2 ^ 26 - 1) 0); (32%nat, mkAF SBe SBe 0)] [] []).
Definition Bx18 : sv := SOff 18 0.


Definition R3_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 0x98 0 0x98
    [YP09.mkChunk 0x80 (CVal 8 (SOff 22 0)); YP09.mkChunk 0x28 (CVal 8 (SOff 22 0));
     YP09.mkChunk 0x18 (CVal 8 (SOff 22 0)); YP09.mkChunk 0x78 (CVal 8 (SOff 22 64));
     YP09.mkChunk 0x88 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x90 (CVal 8 (SOff 34 0))].
Definition ss_e3 : sstate :=
  mkSS 0x230 sr_atoms [R3_sp] None (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SBe SBe 0)] [] []).


(* The machine frame's slots at the call of check: atom 33 = F, 34 = the input cursor, 35 = the bytes left. *)
Definition R4_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 0x98 0 0x98
    [YP09.mkChunk 0x18 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x28 (CVal 8 (SOff 33 0));
     YP09.mkChunk 0x70 (CVal 8 (SOff 33 32)); YP09.mkChunk 0x78 (CVal 8 (SOff 33 64));
     YP09.mkChunk 0x80 (CVal 8 (SOff 33 0));
     YP09.mkChunk 0x88 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x90 (CVal 8 (SOff 35 0))].
Definition ss_e4 : sstate :=
  mkSS 0x25c sr_atoms [R4_sp] None
    (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF SBe SBe 0); (20%nat, mkAF 4096 140737479966720 4);
              (32%nat, mkAF SBe SBe 0)] [] []).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the cuts of the entry phase ---- *)
Definition eb_mach (pc : Z) (ms3 : machine_state) : Prop :=
  ms_pc_val ms3 = w64 (BASE + pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr.

(* 0x7ffc0: the frame on the side stack is taken (a0), nothing else is done to it. *)
Definition EA (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  eb_mach GE_A ms3 /\
  getr (ms_regs ms3) 2 = w64 (c_sp1 cx) /\ getr (ms_regs ms3) 8 = w64 (spZ (c_regs cx)) /\
  getr (ms_regs ms3) 9 = w64 (c_sp1 cx) /\
  getr (ms_regs ms3) 3 = getr (c_regs cx) 3 /\ getr (ms_regs ms3) 4 = getr (c_regs cx) 4 /\
  getr (ms_regs ms3) 18 = w64 SHADOW_OFF /\ getr (ms_regs ms3) 20 = w64 (c_p cx) /\
  getr (ms_regs ms3) 21 = w64 (c_n cx) /\ getr (ms_regs ms3) 10 = w64 (gF cx fp) /\
  gsaved cx W3 ms3 /\
  zero_shadow (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (gF cx fp) (fs_frame_bytes GB_CID) /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + fs_frame_bytes GB_CID - 8) = Some (gFL cx fp) /\
  k <= 0 /\ acc <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx).

(* 0x80118: the frame's header and its 52 shadow bytes are written (GSH_J), the input is shorter than 2^26, slots 0x80
   and 0x28 hold F, slots 0x88 and 0x90 the input cursor; a0 = 0x120 for the malloc wrapper. *)
Definition EM (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  eb_mach GE_M ms3 /\ gregs cx fp ms3 /\ gsaved cx W3 ms3 /\ gshadow cx fp W3 ms3 GSH_J /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + fs_frame_bytes GB_CID - 8) = Some (gFL cx fp) /\
  getr (ms_regs ms3) 20 = w64 (c_p cx) /\ getr (ms_regs ms3) 21 = w64 (c_n cx) /\
  getr (ms_regs ms3) 22 = w64 (gF cx fp) /\ getr (ms_regs ms3) 10 = w64 288 /\
  gslot cx W3 ms3 0x80 (gF cx fp) /\ gslot cx W3 ms3 0x28 (gF cx fp) /\ gcursor cx W3 ms3 0 /\
  k <= 0 /\ acc <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx).

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib (PI := PI) B.
Hypothesis TLF : PALibF (PI := PI) B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM3 : astack_malloc_realizes SEGS B 3.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis TINIT : treac_boxreg_init_spec (PI := PI) B.
Hypothesis TCHECK : tcheck_spec (PI := PI) B.
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
(* the image's ZERO (A_OBJ 6, check's operand) and musl memchr's constant words: read-only image bytes *)
Hypothesis HZB : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 6)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis HZ1 : IMG_LO + 64 <= VAL (A_OBJ 6).
Hypothesis HZ2 : VAL (A_OBJ 6) + 6 + 64 <= IMG_HI.
Hypothesis HMCH : SnprintfDef.asn_rom_bytes SEGS B MCH_LO MCH_CONSTS.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* The machine stack pointer the call starts from and the realigned one (andi sp,sp,-32 at 0x7ff8c). *)
Lemma eb_sp : forall cx, gb_base B MT cx ->
  spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + 32768 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 272 <= c_sp1 cx <= spZ (c_regs cx) - 256 /\ c_sp1 cx mod 32 = 0.
Proof.
intros cx HB.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
unfold GB_STK in *.
pose proof (Z.div_mod (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hmp.
pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)) as Hd16.
rewrite Hsp1. split; [exact Hal16|]. split; [lia|]. split; [lia|]. split; [lia|].
rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

(* The prologue's saves (0x7ff54 .. 0x7ff84): ra at sp - 8, s0, s1, s2 .. s11 at sp - 16 - 8j, as (offset, entry
   register) pairs. *)
Definition EB_SAVED : list (Z * nat) :=
  [(-8, 1%nat); (-16, 8%nat); (-24, 9%nat); (-32, 18%nat); (-40, 19%nat); (-48, 20%nat); (-56, 21%nat);
   (-64, 22%nat); (-72, 23%nat); (-80, 24%nat); (-88, 25%nat); (-96, 26%nat); (-104, 27%nat)].

(* The saved words, read from a region over the machine stack at the caller's sp (atom 2) that holds them. *)
Lemma eb_gsaved_of : forall cx (W : world SEGS) ms E cs lo hi wlo whi,
  YP09.region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 2) = spZ (c_regs cx) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (c_regs cx) r) ->
  (forall od n, In (od, n) EB_SAVED -> In (YP09.mkChunk od (CVal 8 (SOff n 0))) cs) ->
  gsaved cx W ms.
Proof.
intros cx W ms E cs lo hi wlo whi HR Hb EE Hin.
assert (RD : forall od (n : nat) (r : bv 5), In (od, n) EB_SAVED -> Z.of_nat n = bv_unsigned r ->
  rdword (aview SEGS (w_H W) (ms_mem ms)) (spZ (c_regs cx) + od) = Some (bv_unsigned (getr (c_regs cx) r))).
{ intros od n r H1 H2. rewrite (eb_rdword_chunk E (w_H W) (ms_mem ms) 2 _ cs lo hi wlo whi od (SOff n 0) HR Hb (Hin od n H1)).
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE n r H2). reflexivity. }
split.
- replace (spZ (c_regs cx) - 8) with (spZ (c_regs cx) + -8) by lia.
  exact (RD (-8) 1%nat 1%bv ltac:(cbn [EB_SAVED In]; tauto) eq_refl).
- intros j Hj.
  assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11)
    by lia.
  repeat (destruct Hc as [-> | Hc]; [
    lazymatch goal with |- rdword _ (_ - 16 - 8 * ?jj) = Some (bv_unsigned (getr _ ?rr)) =>
      let od := eval vm_compute in (-16 - 8 * jj) in
      let rz := eval vm_compute in (bv_unsigned rr) in
      let n := eval vm_compute in (Z.to_nat rz) in
      replace (spZ (c_regs cx) - 16 - 8 * jj) with (spZ (c_regs cx) + od) by lia;
      exact (RD od n rr ltac:(cbn [EB_SAVED In]; tauto) eq_refl) end |]).
  subst j.
  lazymatch goal with |- rdword _ (_ - 16 - 8 * ?jj) = Some (bv_unsigned (getr _ ?rr)) =>
    let od := eval vm_compute in (-16 - 8 * jj) in
    let rz := eval vm_compute in (bv_unsigned rr) in
    let n := eval vm_compute in (Z.to_nat rz) in
    replace (spZ (c_regs cx) - 16 - 8 * jj) with (spZ (c_regs cx) + od) by lia;
    exact (RD od n rr ltac:(cbn [EB_SAVED In]; tauto) eq_refl) end.
Qed.

(* The saved words survive a step that keeps the 104 bytes below the caller's sp. *)
Lemma eb_gsaved_tr : forall cx (W W' : world SEGS) ms ms',
  (forall a, spZ (c_regs cx) - 104 <= a < spZ (c_regs cx) ->
     aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  gsaved cx W ms -> gsaved cx W' ms'.
Proof.
intros cx W W' ms ms' HK (Hra & Hsj). split.
- rewrite (rdword_ext (aview SEGS (w_H W) (ms_mem ms))); [exact Hra|]. intros i Hi. apply HK. lia.
- intros j Hj. rewrite (rdword_ext (aview SEGS (w_H W) (ms_mem ms))); [exact (Hsj j Hj)|]. intros i Hi. apply HK. lia.
Qed.

Lemma eb_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia]. apply Z.mod_divide; [lia|].
destruct Ha as [x Hx]. destruct Hb as [y Hy]. exists (2 * x - y). lia.
Qed.

Theorem gb_entry_a : forall POST, gb_from B MT POST EA -> gb_start B MT POST.
Proof.
intros POST HNEXT cx HB.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
pose proof HB as (HPRE & Hp & Hn & Hpn & HIN & Hfr0 & Hev & Hlive & HRO & Hsp1 & HE0 & HE02 & HE032 & HMOK & HTR & HNEED).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (eb_sp cx HB) as (Hs16 & Hslo' & Hshi' & Hs1 & Hs132).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
pose proof (pa_obj_img 0 ltac:(lia)) as Ho0. pose proof (pa_obj_img 1 ltac:(lia)) as Ho1.
pose proof (pa_obj_img 12 ltac:(lia)) as Ho12.
assert (HIMG : IMG_TOP < alloc_ceiling) by lia.
remember (Eimg (Ereg (c_regs cx) [Z_to_bv 64 SBe; Z_to_bv 64 (c_sp1 cx); Z_to_bv 64 (as_uar_cell B)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (c_regs cx) r)
  by (intros n r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E32 : ew E 32 = Z_to_bv 64 SBe) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (c_sp1 cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (EA0 : forall i, (i < 14)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
  by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ (c_regs cx)) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (BV : forall i, (i < 14)%nat -> YP09.base_val E (Some (A_OBJ i)) = VAL (A_OBJ i))
  by (intros i Hi; cbn [YP09.base_val]; rewrite (EA0 i Hi); apply unsigned_lit_small; apply pa_val_range).
assert (BU : YP09.base_val E (Some 34%nat) = as_uar_cell B)
  by (cbn [YP09.base_val]; rewrite E34; apply unsigned_lit_small; lia).
assert (BS : YP09.base_val E (Some 2%nat) = spZ (c_regs cx)) by (cbn [YP09.base_val]; exact Usp).
(* the seat *)
assert (HS : st_ok_pi SEGS VAL E ss_e0
  (restrict (w_H (c_W cx)) (mkst (c_regs cx) (Z_to_bv 64 (BASE + GP_entry)) (c_mem cx) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_e0. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite BS. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold GB_STK; lia.
    + rewrite (BV 1%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite (EA0 12%nat ltac:(lia)), Z.add_0_r, unsigned_lit_small by apply pa_val_range; reflexivity
        | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (c_W cx)) (c_mem cx) _ _ Kgot).
    + rewrite (BV 12%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by (unfold SBe; lia); reflexivity
        | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (c_W cx)) (c_mem cx) _ _ Kcell).
    + rewrite (BV 0%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff 34 0) (as_uar_cell B));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, unsigned_lit_small by lia; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (c_W cx)) (c_mem cx) _ _ Kguar).
    + rewrite BU. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H (c_W cx)) (c_mem cx) _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite BS, BU, (BV 0%nat ltac:(lia)), (BV 1%nat ltac:(lia)), (BV 12%nat ltac:(lia)).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, E33, !unsigned_lit_small by (unfold SBe; lia).
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r. unfold SBe.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok SEGS Bxe [] E (mrestrict (w_H (c_W cx)) (c_mem cx))) by constructor.
clear HE.
pose proof (ajournal_init SEGS B GB_STK [] _ _ _ _ _ _ _ HPRE) as HJ.
unfold GP_entry. change (w64 (BASE + 0)) with (Z_to_bv 64 (BASE + 0)).
(* 0x7ff4c .. 0x7ff8c: the frame, the saves, s0 = sp, the realignment *)
paj_run_to_tok RUNTO HS HJ SHOK Bspane 0x44; [awr_ok_tac; exact Usp |].
(* sp := the realigned stack pointer, atom 33 *)
lazymatch goal with HSx : st_ok_pi _ _ ?Ev ?ss (restrict ?Hh ?msx) |- _ =>
  assert (R2 : getr (ms_regs (restrict Hh msx)) 2 = sv_denot Ev (SOff 33 0));
  [ cbn [restrict ms_regs]; rewrite (st_ok_pi_restrict_reg Hh Ev ss msx 2%bv HSx);
    let e := eval vm_compute in (sr_get (ss_regs ss) 2%bv) in change (sr_get (ss_regs ss) 2%bv) with e;
    rewrite (eb_denot_and_m32 Ev 2 (spZ (c_regs cx)) (-256)) by
      first [ rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned | lia ];
    cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned, Hsp1; reflexivity
  | pose proof (st_ok_pi_set_reg Ev ss (restrict Hh msx) 2%bv (SOff 33 0) HSx ltac:(discriminate) R2) as HS2;
    clear HSx R2; rename HS2 into HS ]
end.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* 0x7ff90 .. 0x7ffbc: s1, the GOT loads, the use-after-return flag (1), a0 = 0x1a0, jal __asan_stack_malloc_3 *)
paj_run_tok RUN HS HJ SHOK Bspane; [awr_ok_tac; exact Usp |].
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21.
(* the saved words, from the stack region *)
lazymatch type of HS with st_ok _ _ ?ssc _ =>
  let r0 := eval vm_compute in (nth_error (ss_mem ssc) 0) in
  lazymatch r0 with Some ?rr => pose proof (st_ok_region_nth E ssc _ 0 rr HS eq_refl) as HR0 end end.
cbn [restrict ms_mem] in HR0.
assert (GSV0 : gsaved cx (c_W cx) ms0).
{ eapply eb_gsaved_of; [exact HR0 | exact Usp | exact EE |].
  intros od n Hin. cbn [EB_SAVED In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; cbn [In]; repeat (first [left; reflexivity | right]) |]).
  destruct Hin. }
clear HR0.
(* __asan_stack_malloc_3 (0x1a0): the frame F of class 3 *)
rewrite (palf_sm3 B TLF).
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 3 ASM3 ltac:(lia)
    (c_W cx) (ms_regs ms0) (ms_mem ms0) GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) []
    (c_ly cx) (c_S cx) _ 0 (c_sp1 cx - spZ (c_regs cx)) _ HJ).
  - unfold spZ at 1. rewrite Q2, E33, unsigned_lit_small by lia. lia.
  - apply eb_mod16; [exact Hs132 | exact Hs16].
  - lia.
  - unfold ESTACK, GB_STK. lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Hfr0. vm_compute. reflexivity. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2
  & Hbb2 & Hz & Hflag & HK & HJ1 & (f & ES2)).
assert (KP : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms0) r).
{ intros r Hr. pose proof (HP2 (bv_unsigned r) Hr) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
apply (HNEXT cx pos 0 0 (c_ly cx) S2 (c_W cx) (mkst regs2 (Z_to_bv 64 (BASE + 116)) mem2 (seg_rom SEGS)) md2 HB HJ2).
- rewrite Hfrs2, Hfr0. reflexivity.
- rewrite ES2. apply (mo_le_set_fs_r MT MTF). apply (mo_le_refl MT MTL).
- unfold EA, eb_mach. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst].
  split; [split; [unfold GE_A, w64; reflexivity|]; repeat split; reflexivity|].
  split; [rewrite (KP 2%bv ltac:(change (bv_unsigned (2%bv : bv 5)) with 2; unfold acallee_saved; lia)); rewrite Q2, E33; reflexivity|].
  split; [rewrite (KP 8%bv ltac:(change (bv_unsigned (8%bv : bv 5)) with 8; unfold acallee_saved; lia)); rewrite Q8, (EE 2%nat 2%bv eq_refl); unfold w64, spZ;
          symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite (KP 9%bv ltac:(change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; lia)); rewrite Q9, E33; reflexivity|].
  split; [rewrite (KP 3%bv ltac:(change (bv_unsigned (3%bv : bv 5)) with 3; unfold acallee_saved; lia)); rewrite Q3, (EE 3%nat 3%bv eq_refl); reflexivity|].
  split; [rewrite (KP 4%bv ltac:(change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; lia)); rewrite Q4, (EE 4%nat 4%bv eq_refl); reflexivity|].
  split; [rewrite (KP 18%bv ltac:(change (bv_unsigned (18%bv : bv 5)) with 18; unfold acallee_saved; lia)); rewrite Q18, E32; reflexivity|].
  split; [rewrite (KP 20%bv ltac:(change (bv_unsigned (20%bv : bv 5)) with 20; unfold acallee_saved; lia)); rewrite Q20, (EE 10%nat 10%bv eq_refl); exact Hp|].
  split; [rewrite (KP 21%bv ltac:(change (bv_unsigned (21%bv : bv 5)) with 21; unfold acallee_saved; lia)); rewrite Q21, (EE 11%nat 11%bv eq_refl); exact Hn|].
  split; [exact Ha0|].
  split.
  { apply (eb_gsaved_tr cx (c_W cx) (c_W cx) ms0); [|exact GSV0].
    intros a Ha. cbn [ms_mem mkst]. destruct HK as (K1 & _). apply K1; unfold ESTACK, GB_STK in *; lia. }
  split; [exact Hz|]. split; [exact Hflag|].
  split; [lia|]. split; [lia|]. exact Eab.
Qed.

(* ---- the facts of the frame on the side stack, at any state of the body ---- *)
Lemma eb_F : forall cx fp k ly3 S3 W3 mem3 md3,
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 mem3 md3 k ->
  frames S3 = [(GB_CID, fp)] ->
  frame_addr ly3 GB_CID fp = gF cx fp /\ flag_addr ly3 GB_CID fp = gFL cx fp /\
  4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512 /\ gF cx fp mod 64 = 0 /\
  gSH cx fp = SHADOW_OFF + gF cx fp / 8 /\
  (forall a, gF cx fp <= a < gF cx fp + 512 -> apresent (w_H W3) mem3 a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H W3) mem3 (gSH cx fp + i)).
Proof.
intros cx fp k ly3 S3 W3 mem3 md3 HB HJ HFR.
pose proof HB as ((HAR0 & _) & _).
pose proof HJ as (HAR3 & Hly3 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (EF : frame_addr ly3 GB_CID fp = gF cx fp) by (unfold gF; apply Efa).
assert (EFL : flag_addr ly3 GB_CID fp = gFL cx fp).
{ pose proof (Efa 0 0) as E00. unfold frame_addr in E00. unfold gFL, flag_addr. lia. }
pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ GB_CID fp HAR3 Hfin) as (HF0 & HFc & HFia).
pose proof (frame_al64 SEGS B _ _ _ _ _ GB_CID fp HAR3 Hfin) as (H64 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ GB_CID fp HAR3 Hfin) as (_ & _ & HFp & HFs).
assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
rewrite EF, Hfb in *.
split; [reflexivity|]. split; [exact EFL|]. split; [lia|]. split; [lia|]. split; [exact HFia|]. split; [exact H64|].
split; [reflexivity|]. split.
- intros a Ha. exact (proj1 (HFp a Ha)).
- intros i Hi. change (512 / 8) with 64 in HFs. exact (proj1 (HFs i Hi)).
Qed.

(* The right to write depends only on the regions' windows. *)
Definition eb_wsk (r : YP09.region) : option nat * Z * Z := (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r).
Lemma eb_awr_skel : forall E rs rs' STK sp0 FP bl0 blc ly own,
  map eb_wsk rs' = map eb_wsk rs -> awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E rs' STK sp0 FP bl0 blc ly own.
Proof.
intros E rs rs' STK sp0 FP bl0 blc ly own Hm H a (r' & Hin & Ha). apply H. clear H.
revert rs Hm. induction rs' as [|x rs' IH]; intros [|y rs] Hm; try discriminate Hm; [destruct Hin|].
cbn [map] in Hm. unfold eb_wsk at 1 3 in Hm. injection Hm as E1 E2 E3 Hm. destruct Hin as [<- | Hin].
- exists y. split; [left; reflexivity|]. rewrite <- E1, <- E2, <- E3. exact Ha.
- destruct (IH Hin rs Hm) as (r & Hr & Hb). exists r. split; [right; exact Hr | exact Hb].
Qed.

(* The right to write a window of the frame on the side stack, and of its shadow. *)
Lemma eb_awr_frame : forall E rs STK sp0 FP bl0 blc ly3 own fp cx (n : nat) lo hi wlo whi cs,
  In (GB_CID, fp) own -> frame_addr ly3 GB_CID fp = gF cx fp ->
  bv_unsigned (ew E n) = gF cx fp -> 0 <= wlo -> whi <= 512 ->
  awr_ok E rs STK sp0 FP bl0 blc ly3 own ->
  awr_ok E (YP09.mkRegion (Some n) lo hi wlo whi cs :: rs) STK sp0 FP bl0 blc ly3 own.
Proof.
intros E rs STK sp0 FP bl0 blc ly3 own fp cx n lo hi wlo whi cs Hin EF Hn Hlo Hhi H.
apply (awr_ok_cons_gen E _ rs STK sp0 FP bl0 blc ly3 own n (gF cx fp)); [reflexivity | exact Hn | | exact H].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists GB_CID, fp. split; [exact Hin|].
left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes GB_CID) with 512. lia.
Qed.
Lemma eb_awr_fshadow : forall E rs STK sp0 FP bl0 blc ly3 own fp cx (n : nat) lo hi wlo whi cs,
  In (GB_CID, fp) own -> frame_addr ly3 GB_CID fp = gF cx fp ->
  bv_unsigned (ew E n) = gSH cx fp -> 0 <= wlo -> whi <= 64 ->
  awr_ok E rs STK sp0 FP bl0 blc ly3 own ->
  awr_ok E (YP09.mkRegion (Some n) lo hi wlo whi cs :: rs) STK sp0 FP bl0 blc ly3 own.
Proof.
intros E rs STK sp0 FP bl0 blc ly3 own fp cx n lo hi wlo whi cs Hin EF Hn Hlo Hhi H.
apply (awr_ok_cons_gen E _ rs STK sp0 FP bl0 blc ly3 own n (gSH cx fp)); [reflexivity | exact Hn | | exact H].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists GB_CID, fp. split; [exact Hin|].
right. unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes GB_CID / 8) with 64.
unfold gSH, shadow_of_addr, shadow_addr in *. lia.
Qed.

(* The windows a run may write, by skeleton, and what a run keeps outside them. *)
Lemma eb_inw_skel : forall E rs rs' a, map eb_wsk rs' = map eb_wsk rs -> in_wrange E rs' a -> in_wrange E rs a.
Proof.
intros E rs rs' a Hm (r' & Hin & Ha).
revert rs Hm. induction rs' as [|x rs' IH]; intros [|y rs] Hm; try discriminate Hm; [destruct Hin|].
cbn [map] in Hm. unfold eb_wsk at 1 3 in Hm. injection Hm as E1 E2 E3 Hm. destruct Hin as [<- | Hin].
- exists y. split; [left; reflexivity|]. rewrite <- E1, <- E2, <- E3. exact Ha.
- destruct (IH Hin rs Hm) as (r & Hr & Hb). exists r. split; [right; exact Hr | exact Hb].
Qed.
Lemma eb_keep_step : forall E rs0 rs (H : word -> bool) m0 m1 m2,
  map eb_wsk rs = map eb_wsk rs0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs0 a -> aview SEGS H m1 a = aview SEGS H m0 a) ->
  frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs0 a -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
intros E rs0 rs H m0 m1 m2 Hm K HF a Ha Hn. rewrite <- (K a Ha Hn).
unfold aview, YP09.mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. intros Hw. exact (Hn (eb_inw_skel E rs0 rs a Hm Hw)).
Qed.

(* The machine part of a cut, from the engine's state. *)
Lemma eb_mach_of : forall E ss (H : word -> bool) ms,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> ss_resv ss = None -> eb_mach (ss_pc ss) ms.
Proof.
intros E ss H ms HS Hrv. rewrite (st_ok_pi_restrict_mkst H E ss ms HS Hrv). unfold eb_mach. cbn.
repeat split; reflexivity.
Qed.

(* The frame's 52 shadow bytes, read from a region over them whose chunks hold GSH_J. *)
Lemma eb_gshadow_of : forall cx fp (W : world SEGS) ms E n lo hi wlo whi cs,
  YP09.region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = gSH cx fp ->
  (forall i, (i < 52)%nat -> exists z, In (YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit z))) cs /\
     bv_unsigned (Z_to_bv 64 z) mod 256 = nth i GSH_J 0) ->
  gshadow cx fp W ms GSH_J.
Proof.
intros cx fp W ms E n lo hi wlo whi cs HR Hb Hc i Hi. change (length GSH_J) with 52%nat in Hi.
destruct (Hc i Hi) as (z & Hin & Hz).
pose proof (field_of_region_any E _ n _ cs lo hi wlo whi (Z.of_nat i) 1%N (SLit z) HR Hb Hin ltac:(cbn; lia)) as Hv.
cbn [sv_denot] in Hv. change (2 ^ (8 * Z.of_N 1)) with 256 in Hv. rewrite Hz in Hv.
apply (aview_of_val_mem1 SEGS (w_H W) (ms_mem ms)); [exact Hv|].
rewrite <- Hz. apply Z.mod_pos_bound. lia.
Qed.

Lemma eb_srl26 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 26 ->
  U E (SAlu ALU_SRL (SOff n 0) (SLit 26)) = 0.
Proof.
intros E n v Hn Hv. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 26) 63) with 26.
rewrite (U_atom E n v Hn) by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

(* A machine state of a cut, as the engine's start state. *)
Lemma eb_ms : forall pc (H : word -> bool) ms, eb_mach pc ms ->
  restrict H ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (mrestrict H (ms_mem ms)) (seg_rom SEGS).
Proof.
intros pc H [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0] (Hpc & Hresv & Hpend & Hrom & Hfregs & Hfcsr).
cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in *. subst. reflexivity.
Qed.

(* ---- 0x7ffc0 .. 0x80118: the frame's header, its shadow, the size test, the cursor slots ---- *)
Definition R1_sp : YP09.region := YP09.mkRegion (Some 9%nat) 0 0x98 0 0x98 [].
Definition R1_F : YP09.region := YP09.mkRegion (Some 10%nat) 0 512 0 24 [].
Definition R1_SH : YP09.region := YP09.mkRegion (Some 33%nat) 0 64 0 52 [].
Definition ss_e1 : sstate :=
  mkSS GE_A sr_atoms [R1_sp; R1_F; R1_SH] None
    (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF 4096 140737479966720 6); (32%nat, mkAF SBe SBe 0);
              (33%nat, mkAF (SBe + 512) (SBe + 17592186044416) 3)] [] []).

(* After a run: the bytes outside the windows of ss_e1 are those of the cut's memory. *)
Local Ltac e1_keep KP :=
  lazymatch goal with
  | HFx : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      lazymatch type of KP with forall a, _ -> ~ in_wrange ?E0 ?rs0 a -> aview _ ?H0 m1 a = aview _ _ ?m0 a =>
        let KP2 := fresh "KP" in
        let Hm := fresh "Hm" in
        assert (Hm : map eb_wsk rs = map eb_wsk rs0) by (vm_compute; reflexivity);
        pose proof (eb_keep_step E0 rs0 rs H0 m0 m1 m2 Hm KP HFx) as KP2;
        clear KP Hm; rename KP2 into KP end
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Theorem gb_entry_m : forall POST, gb_from B MT POST EM -> gb_from B MT POST EA.
Proof.
intros POST HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
destruct HI as (HM & G2 & G8 & G9 & G3 & G4 & G18 & G20 & G21 & G10 & GSV & HZ & HFL & Hk & Hacc & HAB).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (eb_sp cx HB) as (Hs16 & Hslo' & Hshi' & Hs1 & Hs132).
pose proof (eb_F cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ HFR) as (EF & EFL & HF0 & HFc & HFia & HF64 & HSHeq & HFp & HFs).
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
assert (Hd512 : 512 <= gF cx fp / 8) by (apply Z.div_le_lower_bound; lia).
remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 SBe; Z_to_bv 64 (gSH cx fp)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
  by (intros n r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E32 : ew E 32 = Z_to_bv 64 SBe) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (gSH cx fp)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = gF cx fp) by (rewrite (EE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = gSH cx fp) by (rewrite E33; apply unsigned_lit_small; rewrite HSHeq; unfold SHADOW_OFF; lia).
assert (HS : st_ok_pi SEGS VAL E ss_e1 (restrict (w_H W3) ms3)).
{ rewrite (eb_ms GE_A (w_H W3) ms3 HM). unfold ss_e1. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold R1_sp, R1_F, R1_SH.
    repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold GB_STK; lia.
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HFp. lia.
    + rewrite U33. split; [rewrite HSHeq; unfold SHADOW_OFF; lia|]. split; [rewrite HSHeq; unfold SHADOW_OFF; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HFs. lia.
  - apply pairwise_disjoint_of_extents.
    unfold R1_sp, R1_F, R1_SH, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
    rewrite U9, U10, U33, HSHeq.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
    repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U10, U33, E32, unsigned_lit_small by (unfold SBe; lia).
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
    rewrite HSHeq. unfold SBe, SHADOW_OFF.
    assert (Hm8 : (2147450880 + gF cx fp / 8) mod 8 = 0).
    { pose proof (Z.div_mod (gF cx fp) 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
      replace (64 * (gF cx fp / 64)) with ((8 * (gF cx fp / 64)) * 8) by lia. rewrite Z.div_mul by lia.
      replace (2147450880 + 8 * (gF cx fp / 64)) with ((268431360 + gF cx fp / 64) * 8) by lia. apply Z_mod_mult. }
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok SEGS Bxe [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HE.
assert (AWR : awr_ok E (ss_mem ss_e1) GB_STK (spZ (c_regs cx)) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3
  [(GB_CID, fp)]).
{ unfold ss_e1, R1_sp, R1_F, R1_SH. cbn [ss_mem].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
    [reflexivity | rewrite U9; lia | cbn; unfold GB_STK; lia | cbn; lia |].
  apply (eb_awr_frame E _ _ _ _ _ _ _ _ fp cx 10%nat); [left; reflexivity | exact EF | exact U10 | cbn; lia | cbn; lia |].
  apply (eb_awr_fshadow E _ _ _ _ _ _ _ _ fp cx 33%nat); [left; reflexivity | exact EF | exact U33 | cbn; lia | cbn; lia |].
  apply awr_ok_nil. }
assert (KP0 : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E (ss_mem ss_e1) a ->
  aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H W3) (ms_mem ms3) a) by reflexivity.
paj_run_to_tok RUNTO HS HJ SHOK Bspan0 0xdc; [exact AWR |].
e1_keep KP0.
(* s8 := the frame's shadow, atom 33 *)
lazymatch goal with HSx : st_ok_pi _ _ ?Ev ?ss (restrict ?Hh ?msx) |- _ =>
  assert (R24 : getr (ms_regs (restrict Hh msx)) 24 = sv_denot Ev (SOff 33 0));
  [ cbn [restrict ms_regs]; rewrite (st_ok_pi_restrict_reg Hh Ev ss msx 24%bv HSx);
    let e := eval vm_compute in (sr_get (ss_regs ss) 24%bv) in change (sr_get (ss_regs ss) 24%bv) with e;
    apply (shadow_decl_ok Ev 10 18 33 (gF cx fp) SHADOW_OFF);
    [ rewrite (EE 10%nat 10%bv eq_refl), G10; reflexivity | lia | rewrite (EE 18%nat 18%bv eq_refl), G18; reflexivity
    | rewrite E33, HSHeq; reflexivity ]
  | pose proof (st_ok_pi_set_reg Ev ss (restrict Hh msx) 24%bv (SOff 33 0) HSx ltac:(discriminate) R24) as HS2;
    clear HSx R24; rename HS2 into HS ]
end.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
paj_run_tok RUN HS HJ SHOK Bspan0; [apply (eb_awr_skel E (ss_mem ss_e1)); [vm_compute; reflexivity | exact AWR] |].
e1_keep KP0.
(* 0x80104: bnez (n >> 26); the input is shorter than 2^26 *)
assert (Hn26 : 0 <= c_n cx < 2 ^ 26).
{ pose proof HB as (_ & _ & _ & Hpn & _). unfold c_n in *. destruct Hpn as [(Hn0 & _) | (Hn0 & _)]; lia. }
psrr_branch_tok RUN BR HS SHOK Bspan0.
{ exfalso. rewrite branch_ne_U, (eb_srl26 E 21 (c_n cx)), U_SLit in Hc
    by first [rewrite (EE 21%nat 21%bv eq_refl), G21; reflexivity | lia].
  cbn in Hc. discriminate Hc. }
paj_run_to_tok RUNTO HS HJ SHOK Bspan0 GE_M; [apply (eb_awr_skel E (ss_mem ss_e1)); [vm_compute; reflexivity | exact AWR] |].
e1_keep KP0.
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => rename msx into msM; rename HSx into HSM end.
lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename HJx into HJM end.
(* the regions at 0x80118 *)
lazymatch type of HSM with st_ok_pi _ _ _ ?ssM _ =>
  let r0 := eval vm_compute in (nth_error (ss_mem ssM) 0) in
  let r2 := eval vm_compute in (nth_error (ss_mem ssM) 2) in
  lazymatch r0 with Some ?rr0 => pose proof (st_ok_pi_region_nth E ssM _ 0 rr0 HSM eq_refl) as HR0 end;
  lazymatch r2 with Some ?rr2 => pose proof (st_ok_pi_region_nth E ssM _ 2 rr2 HSM eq_refl) as HR2 end end.
cbn [restrict ms_mem] in HR0, HR2.
(* what the runs kept: the saved words and the frame's flag word *)
assert (OUT : forall a, 0 <= a < 2 ^ 64 ->
  ~ (c_sp1 cx <= a < c_sp1 cx + 0x98) -> ~ (gF cx fp <= a < gF cx fp + 24) -> ~ (gSH cx fp <= a < gSH cx fp + 52) ->
  aview SEGS (w_H W3) (ms_mem msM) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha N1 N2 N3. apply KP0; [exact Ha|].
  intros (r & Hr & Hb). unfold ss_e1, R1_sp, R1_F, R1_SH in Hr. cbn [ss_mem In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb;
    rewrite ?U9, ?U10, ?U33 in Hb; lia |]).
  destruct Hr. }
apply (HNEXT cx fp k acc ly3 S3 W3 msM _ HB HJM HFR HMO).
pose proof (eb_mach_of E _ (w_H W3) msM HSM eq_refl) as HMM. cbn [ss_pc] in HMM.
prreg HSM (2%bv : bv 5) Q2. prreg HSM (3%bv : bv 5) Q3. prreg HSM (4%bv : bv 5) Q4. prreg HSM (8%bv : bv 5) Q8.
prreg HSM (9%bv : bv 5) Q9. prreg HSM (10%bv : bv 5) Q10. prreg HSM (18%bv : bv 5) Q18. prreg HSM (20%bv : bv 5) Q20.
prreg HSM (21%bv : bv 5) Q21. prreg HSM (22%bv : bv 5) Q22. prreg HSM (24%bv : bv 5) Q24.
unfold EM, gregs.
split; [exact HMM|].
split.
{ split; [rewrite Q2, (EE 2%nat 2%bv eq_refl); exact G2|].
  split; [rewrite Q8, (EE 8%nat 8%bv eq_refl); exact G8|].
  split; [rewrite Q9, (EE 9%nat 9%bv eq_refl); exact G9|].
  split; [rewrite Q3, (EE 3%nat 3%bv eq_refl); exact G3|].
  split; [rewrite Q4, (EE 4%nat 4%bv eq_refl); exact G4|].
  split; [rewrite Q18, (EE 18%nat 18%bv eq_refl); exact G18|].
  rewrite Q24, E33. reflexivity. }
split.
{ apply (eb_gsaved_tr cx W3 W3 ms3 msM); [|exact GSV].
  intros a Ha. apply OUT; [lia | lia | lia |]. rewrite HSHeq. unfold SHADOW_OFF. lia. }
split.
{ apply (eb_gshadow_of cx fp W3 msM E 33 _ _ _ _ _ HR2 U33).
  intros i Hi.
  do 52 (destruct i as [|i]; [eexists; split; [cbn [In]; repeat (first [left; reflexivity | right]) | vm_compute; reflexivity] |]).
  lia. }
split.
{ rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3))); [exact HFL|].
  intros i Hi. change (fs_frame_bytes GB_CID) with 512. apply OUT; [lia | lia | lia |].
  rewrite HSHeq. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in HFia.
  pose proof (Z.mul_div_le (gF cx fp) 8 ltac:(lia)). unfold SHADOW_OFF. lia. }
split; [rewrite Q20, (EE 20%nat 20%bv eq_refl); exact G20|].
split; [rewrite Q21, (EE 21%nat 21%bv eq_refl); exact G21|].
split; [rewrite Q22, (EE 10%nat 10%bv eq_refl); exact G10|].
split; [rewrite Q10; reflexivity|].
assert (RD : forall od (n : nat) (r : bv 5) v,
  In (YP09.mkChunk od (CVal 8 (SOff n 0)))
    [YP09.mkChunk 144 (CVal 8 (SOff 21 0)); YP09.mkChunk 136 (CVal 8 (SOff 20 0));
     YP09.mkChunk 40 (CVal 8 (SOff 10 0)); YP09.mkChunk 128 (CVal 8 (SOff 10 0))] ->
  Z.of_nat n = bv_unsigned r -> getr (ms_regs ms3) r = w64 v -> 0 <= v < 2 ^ 64 ->
  gslot cx W3 msM od v).
{ intros od n r v Hin Hn0 Hr Hv. unfold gslot.
  rewrite (eb_rdword_chunk E (w_H W3) (ms_mem msM) 9 _ _ _ _ _ _ od (SOff n 0) HR0 U9 Hin).
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE n r Hn0), Hr. unfold w64.
  rewrite unsigned_lit_small by exact Hv. reflexivity. }
pose proof HB as (_ & _ & _ & Hpn & _).
assert (Hpr : 0 <= c_p cx < 2 ^ 64).
{ destruct Hpn as [(_ & ->) | (_ & Hin0)]; [unfold GB_EMPTY; lia|].
  pose proof HB as ((HAR0 & _) & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin0) as (_ & H4096 & Hce & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. lia. }
split; [exact (RD 128 10%nat 10%bv (gF cx fp) ltac:(cbn [In]; tauto) eq_refl G10 ltac:(lia))|].
split; [exact (RD 40 10%nat 10%bv (gF cx fp) ltac:(cbn [In]; tauto) eq_refl G10 ltac:(lia))|].
split.
{ unfold gcursor. split; [lia|]. rewrite Z.add_0_r, Z.sub_0_r.
  split; [exact (RD 136 20%nat 20%bv (c_p cx) ltac:(cbn [In]; tauto) eq_refl G20 Hpr)|].
  exact (RD 144 21%nat 21%bv (c_n cx) ltac:(cbn [In]; tauto) eq_refl G21 ltac:(lia)). }
split; [exact Hk|]. split; [exact Hacc|]. exact HAB.
Qed.

(* 0x80178: the registry r is allocated (s4, a0), the fabric byte b is read (s3) and sign-extended (s9, a1),
   slots 0x18 / 0x78 hold F / F + 64 (prev), the cursor has moved past b. *)
Definition EI (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists r,
  eb_mach GE_I ms3 /\ gregs cx fp ms3 /\ gsaved cx W3 ms3 /\ gshadow cx fp W3 ms3 GSH_J /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + fs_frame_bytes GB_CID - 8) = Some (gFL cx fp) /\
  k <= 1 /\ acc <= mo_malloc MT 288 /\ gblk1 B cx ly3 S3 r /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 10 = w64 r /\ getr (ms_regs ms3) 22 = w64 (gF cx fp) /\
  getr (ms_regs ms3) 19 = w64 (eb_b (c_pl cx)) /\
  getr (ms_regs ms3) 25 = w64 (LLVMFuzzerTestOneInput_entry.en_sx (eb_b (c_pl cx))) /\
  getr (ms_regs ms3) 11 = w64 (LLVMFuzzerTestOneInput_entry.en_sx (eb_b (c_pl cx))) /\
  gslot cx W3 ms3 0x80 (gF cx fp) /\ gslot cx W3 ms3 0x28 (gF cx fp) /\
  gslot cx W3 ms3 0x18 (gF cx fp) /\ gslot cx W3 ms3 0x78 (gF cx fp + GO_PREV) /\
  gcursor cx W3 ms3 (eb_pos cx).


(* The call chain at the realigned stack pointer, through the layout of a later state. *)
Lemma eb_achain_ly : forall cx ly3 S3 W3 mem md own k sp',
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    own ly3 S3 W3 mem md k ->
  rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  sp' + 16 <= spZ (c_regs cx) ->
  achain ly3 (aview SEGS (w_H W3) mem) sp' (spZ (c_regs cx)) (gch cx).
Proof.
intros cx ly3 S3 W3 mem md own k sp' HB HJ H8 H16 Hsp.
pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop).
eapply gb_achain;
  first [ exact HB | exact H8 | exact H16 | exact Hsp | (intros a Ha; apply F1; unfold GB_STK in *; lia) ].
Qed.

Lemma eb_gsaved_s0 : forall cx W ms, gsaved cx W ms ->
  rdword (aview SEGS (w_H W) (ms_mem ms)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)).
Proof.
intros cx W ms [_ H]. specialize (H 0 ltac:(lia)). rewrite Z.mul_0_r, Z.sub_0_r in H. rewrite H.
unfold s0Z. do 3 f_equal; apply bv_eq; reflexivity.
Qed.

(* A spill slot, read back from a region over the realigned stack pointer (atom 9). *)
Lemma eb_slot_of : forall cx (W : world SEGS) ms E cs lo hi wlo whi off (n : nat) c v,
  YP09.region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 9) = c_sp1 cx ->
  In (YP09.mkChunk off (CVal 8 (SOff n c))) cs ->
  ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  gslot cx W ms off (v + c).
Proof.
intros cx W ms E cs lo hi wlo whi off n c v HR Hb Hin Hn Hv Hc. unfold gslot.
rewrite (eb_rdword_chunk E (w_H W) (ms_mem ms) 9 _ cs lo hi wlo whi off (SOff n c) HR Hb Hin).
f_equal. exact (U_atom_off E n v c Hn Hv Hc).
Qed.

(* The byte the code reads with lbu, zero-extended. *)
Lemma eb_zext8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  sv_denot E (SExt false 8 (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv. rewrite denot_lit_U. f_equal.
rewrite U_zext, (U_atom_off E n v 0 Hn) by lia. rewrite Z.add_0_r.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hv.
Qed.

(* (int8_t) b, as `slli 56; srai 56` leave it. *)
Lemma eb_sext8 : forall E x b, U E x = b -> 0 <= b < 256 ->
  sv_denot E (SAlu ALU_SRA (SAlu ALU_SLL x (SLit 56)) (SLit 56)) =
  Z_to_bv 64 (LLVMFuzzerTestOneInput_entry.en_sx b).
Proof.
intros E x b Hx Hb. rewrite denot_lit_U. apply bv_eq. rewrite !Z_to_bv_unsigned.
rewrite !U_SAlu, Hx, !U_SLit. cbn [zalu_raw].
change (Z.land (zcanon 56) 63) with 56.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
unfold zcanon, M64, bv_swrap, bv_wrap, LLVMFuzzerTestOneInput_entry.en_sx.
change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
rewrite (Z.mod_small (b * 2 ^ 56)) by lia.
destruct (Z.ltb_spec b 128) as [Hl | Hl].
- rewrite (Z.mod_small (b * 2 ^ 56 + 2 ^ 63)) by lia.
  replace (b * 2 ^ 56 + 2 ^ 63 - 2 ^ 63) with (b * 2 ^ 56) by lia. rewrite Z.div_mul by lia.
  rewrite Z.mod_mod by lia. reflexivity.
- replace ((b * 2 ^ 56 + 2 ^ 63) mod 2 ^ 64) with (b * 2 ^ 56 + 2 ^ 63 - 2 ^ 64)
    by (apply (Z.mod_unique _ _ 1); lia).
  replace (b * 2 ^ 56 + 2 ^ 63 - 2 ^ 64 - 2 ^ 63) with ((b - 256) * 2 ^ 56) by lia.
  rewrite Z.div_mul by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma eb_add0 : forall E x, sv_denot E (SAlu ALU_ADD x (SLit 0)) = sv_denot E x.
Proof.
intros E x. rewrite (denot_lit_U E (SAlu ALU_ADD x (SLit 0))), U_SAlu, U_SLit. cbn [zalu_raw].
change (zcanon 0) with 0. rewrite Z.add_0_r. unfold zcanon. rewrite Z.mod_small by apply U_range.
symmetry. apply denot_lit_U.
Qed.

Lemma eb_frame_nil : forall E (H : word -> bool) m1 m2, frame_of E [] (mrestrict H m1) (mrestrict H m2) ->
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m2 a = aview SEGS H m1 a.
Proof.
intros E H m1 m2 HF a Ha. unfold aview, YP09.mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & [] & _).
Qed.

Local Ltac e2_keep KP :=
  lazymatch goal with
  | HFx : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      lazymatch type of KP with forall a, _ -> ~ in_wrange ?E0 ?rs0 a -> aview _ ?H0 m1 a = aview _ _ ?m0 a =>
        let KP2 := fresh "KP" in
        let Hm := fresh "Hm" in
        assert (Hm : map eb_wsk rs = map eb_wsk rs0) by (vm_compute; reflexivity);
        pose proof (eb_keep_step E0 rs0 rs H0 m0 m1 m2 Hm KP HFx) as KP2;
        clear KP Hm; rename KP2 into KP end
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Theorem gb_entry_i : forall POST, gb_from B MT POST EI -> gb_from B MT POST EM.
Proof.
intros POST HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
destruct HI as (HM & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & GSV & GSH & HFL & G20 & G21 & G22 & G10 & S80 & S28 & SCUR
  & Hk & Hacc & HAB).
pose proof HB as (HPRE & Hp & Hn & Hpn & HIN & Hfr0 & Hev & Hlive & HRO & Hsp1 & HE0 & HE02 & HE032 & HMOK & HTR & HNEED).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (eb_sp cx HB) as (Hs16 & Hslo' & Hshi' & Hs1 & Hs132).
pose proof (eb_F cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ HFR) as (EF & EFL & HF0 & HFc & HFia & HF64 & HSHeq & HFp & HFs).
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & HJpres & _).
(* 0x80118: jal __wrap_malloc (a0 = 0x120) *)
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
  by (intros n r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (HS : st_ok_pi SEGS VAL E (mkSS GE_M sr_atoms [] None (mkFacts [] [] [])) (restrict (w_H W3) ms3)).
{ rewrite (eb_ms GE_M (w_H W3) ms3 HM). apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS Bxe [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HE.
paj_run_tok RUN HS HJ SHOK Bspan0; [apply awr_ok_nil |].
lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into ms1 end.
lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (eb_frame_nil _ _ _ _ HFx) as M1 end.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24.
assert (GSV1 : gsaved cx W3 ms1) by (apply (eb_gsaved_tr cx W3 W3 ms3 ms1); [intros a Ha; apply M1; lia | exact GSV]).
assert (Usp1 : spZ (ms_regs ms1) = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)))
  by (unfold spZ at 1; rewrite Q2, (EE 2%nat 2%bv eq_refl), G2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms1)) (c_sp1 cx) (spZ (c_regs cx)) (gch cx))
  by (apply (eb_achain_ly cx ly3 S3 W3 (ms_mem ms1) _ [(GB_CID, fp)] k (c_sp1 cx) HB HJ (proj1 GSV1)
        (eb_gsaved_s0 cx W3 ms1 GSV1)); lia).
rewrite (pal_malloc B TL).
eapply SRr_bind.
{ eapply (AMALLOC4 W3 (ms_regs ms1) (ms_mem ms1) GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k 288 (c_sp1 cx - spZ (c_regs cx))
    (Z_to_bv 64 (BASE + 0x1d0)) (gch cx) HJ).
  - rewrite Q10, (EE 10%nat 10%bv eq_refl). exact G10.
  - unfold MALLOC_MAX. lia.
  - rewrite (blocks_bytes_bsum B ly3 S3), HAB, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
    unfold GB_LIVE, LIVE_MAX in *. lia.
  - exact Usp1.
  - apply eb_mod16; [exact Hs132 | exact Hs16].
  - lia.
  - unfold ASTACK, GB_STK. lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl), G3. exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl), G4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold GB_EV, EV_MAX in *. lia.
  - apply (achain_chain_pre ly3 _ (c_sp1 cx) (spZ (c_regs cx)) (gch cx) (ms_regs ms1) HCH).
    + rewrite Usp1. lia.
    + unfold s0Z. rewrite Q8, (EE 8%nat 8%bv eq_refl), G8. unfold w64. apply unsigned_lit_small. lia.
    + unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - apply HTR. left. split; [reflexivity|]. unfold raZ. rewrite Q1, unsigned_lit_small by lia.
    replace (BASE + 0x1d0 - BASE) with 0x1d0 by lia. unfold GB_MSITES. cbn [In]. auto.
  - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_malloc MT 288) MTL HMOK HMO).
    + apply (mo_malloc_nonneg MT MTL). lia.
    + pose proof (mo_free_nonneg MT MTL). pose proof (mo_malloc_nonneg MT MTL 48 ltac:(lia)).
      unfold GB_NEED, GB_A in HNEED. lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & r & -> & HJ2 & HP2 & Ha02 & Hfrs2 & Hr4096 & Eab2 & HK2 & MLE2).
assert (KP2 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs2 r0 = getr (ms_regs ms1) r0).
{ intros r0 Hr0. pose proof (HP2 (bv_unsigned r0) Hr0) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
assert (R2 : getr regs2 2 = w64 (c_sp1 cx)) by (rewrite (KP2 2%bv ltac:(change (bv_unsigned (2%bv : bv 5)) with 2; unfold acallee_saved; lia)), Q2, (EE 2%nat 2%bv eq_refl); exact G2).
assert (R3 : getr regs2 3 = getr (c_regs cx) 3) by (rewrite (KP2 3%bv ltac:(change (bv_unsigned (3%bv : bv 5)) with 3; unfold acallee_saved; lia)), Q3, (EE 3%nat 3%bv eq_refl); exact G3).
assert (R4 : getr regs2 4 = getr (c_regs cx) 4) by (rewrite (KP2 4%bv ltac:(change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; lia)), Q4, (EE 4%nat 4%bv eq_refl); exact G4).
assert (R8 : getr regs2 8 = w64 (spZ (c_regs cx))) by (rewrite (KP2 8%bv ltac:(change (bv_unsigned (8%bv : bv 5)) with 8; unfold acallee_saved; lia)), Q8, (EE 8%nat 8%bv eq_refl); exact G8).
assert (R9 : getr regs2 9 = w64 (c_sp1 cx)) by (rewrite (KP2 9%bv ltac:(change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; lia)), Q9, (EE 9%nat 9%bv eq_refl); exact G9).
assert (R18 : getr regs2 18 = w64 SHADOW_OFF) by (rewrite (KP2 18%bv ltac:(change (bv_unsigned (18%bv : bv 5)) with 18; unfold acallee_saved; lia)), Q18, (EE 18%nat 18%bv eq_refl); exact G18).
assert (R20 : getr regs2 20 = w64 (c_p cx)) by (rewrite (KP2 20%bv ltac:(change (bv_unsigned (20%bv : bv 5)) with 20; unfold acallee_saved; lia)), Q20, (EE 20%nat 20%bv eq_refl); exact G20).
assert (R21 : getr regs2 21 = w64 (c_n cx)) by (rewrite (KP2 21%bv ltac:(change (bv_unsigned (21%bv : bv 5)) with 21; unfold acallee_saved; lia)), Q21, (EE 21%nat 21%bv eq_refl); exact G21).
assert (R22 : getr regs2 22 = w64 (gF cx fp)) by (rewrite (KP2 22%bv ltac:(change (bv_unsigned (22%bv : bv 5)) with 22; unfold acallee_saved; lia)), Q22, (EE 22%nat 22%bv eq_refl); exact G22).
assert (R24 : getr regs2 24 = w64 (gSH cx fp)) by (rewrite (KP2 24%bv ltac:(change (bv_unsigned (24%bv : bv 5)) with 24; unfold acallee_saved; lia)), Q24, (EE 24%nat 24%bv eq_refl); exact G24).
clear Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q18 Q20 Q21 Q22 Q24 KP2 HP2.
assert (MK : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. destruct HK2 as (K1 & _). rewrite K1 by (unfold ASTACK in *; lia). apply M1; lia. }
assert (SL : forall off v, 0 <= off <= 0x90 -> gslot cx W3 ms3 off v ->
  rdword (aview SEGS (w_H W2) mem2) (c_sp1 cx + off) = Some v).
{ intros off v Ho Hs. unfold gslot in Hs. rewrite <- Hs. apply rdword_ext. intros i Hi. apply MK. lia. }
destruct SCUR as (_ & S88 & S90). rewrite Z.add_0_r in S88. rewrite Z.sub_0_r in S90.
pose proof (proj1 HJ2) as HAR2.
assert (Hrin : In (r, 288) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 288 HAR2 Hrin) as (Hr16 & _ & Hrce & Hrapp & _).
change (req_size 288) with 288 in Hrce, Hrapp.
remember (Eimg (Ereg regs2 [Z_to_bv 64 SBe; Z_to_bv 64 (eb_b (c_pl cx))])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E2 n = getr regs2 r0)
  by (intros n r0 Hn0; subst E2; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (F32 : ew E2 32 = Z_to_bv 64 SBe) by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (F33 : ew E2 33 = Z_to_bv 64 (eb_b (c_pl cx))) by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (U9 : bv_unsigned (ew E2 9) = c_sp1 cx) by (rewrite (EE2 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E2 10) = r) by (rewrite (EE2 10%nat 10%bv eq_refl), Ha02; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E2 18) = SHADOW_OFF) by (rewrite (EE2 18%nat 18%bv eq_refl), R18; reflexivity).
assert (U21 : bv_unsigned (ew E2 21) = c_n cx).
{ rewrite (EE2 21%nat 21%bv eq_refl), R21. apply unsigned_lit_small. pose proof HB as (_ & _ & _ & Hpn' & _).
  unfold c_n in *. destruct Hpn' as [(H0 & _) | (H0 & _)]; lia. }
assert (Hb256 : 0 <= eb_b (c_pl cx) < 256) by (unfold eb_b; destruct (c_pl cx); [lia | apply u8_range]).
assert (SPC : forall off (n : nat) (r0 : bv 5) v, Z.of_nat n = bv_unsigned r0 -> getr regs2 r0 = w64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS (w_H W2) mem2) (c_sp1 cx + off) = Some v ->
  YP09.chunk_ok SEGS E2 (mrestrict (w_H W2) mem2) (c_sp1 cx) (YP09.mkChunk off (CVal 8 (SOff n 0)))).
{ intros off n r0 v Hn0 Hr0 Hv Hrd.
  apply (chunk_ok_val SEGS E2 _ (c_sp1 cx) off 8 (SOff n 0) v); [| zside | zside |].
  - cbn [sv_denot]. rewrite (EE2 n r0 Hn0), Hr0, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity.
  - exact (val_mem_of_rdword SEGS (w_H W2) mem2 _ _ Hrd). }
assert (HFR2 : frames S2 = [(GB_CID, fp)]) by (rewrite Hfrs2; exact HFR).
assert (Hpr : 0 <= c_p cx < 2 ^ 64).
{ destruct Hpn as [(_ & ->) | (Hn0 & Hin0)]; [unfold GB_EMPTY; lia|].
  pose proof HB as ((HAR0 & _) & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin0) as (_ & H4096 & Hce & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. lia. }
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _ & _ & F2' & _ & _ & _ & HJpres2 & _).
assert (Rsp2 : YP09.region_ok SEGS E2 (mrestrict (w_H W2) mem2) R2_sp).
{ unfold R2_sp, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). apply HJpres2. unfold GB_STK; lia.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (SPC 0x80 22%nat 22%bv (gF cx fp) eq_refl R22 ltac:(lia)). apply SL; [lia | exact S80].
    + apply (SPC 0x28 22%nat 22%bv (gF cx fp) eq_refl R22 ltac:(lia)). apply SL; [lia | exact S28].
    + apply (SPC 0x88 20%nat 20%bv (c_p cx) eq_refl R20 Hpr). apply SL; [lia | exact S88].
    + apply (SPC 0x90 21%nat 21%bv (c_n cx) eq_refl R21 ltac:(lia)). apply SL; [lia | exact S90]. }
assert (AWR2 : forall rs, map eb_wsk rs = map eb_wsk [R2_sp] ->
  awr_ok E2 rs GB_STK (spZ (c_regs cx)) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly2 S2) ly2 [(GB_CID, fp)]).
{ intros rs Hm. apply (eb_awr_skel E2 [R2_sp] rs _ _ _ _ _ _ _ Hm).
  unfold R2_sp.
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
    [reflexivity | rewrite U9; lia | cbn; unfold GB_STK; lia | cbn; lia |].
  apply awr_ok_nil. }
assert (AWR2' : forall rs, map eb_wsk rs = map eb_wsk [R2_sp; R2_in] ->
  awr_ok E2 rs GB_STK (spZ (c_regs cx)) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly2 S2) ly2 [(GB_CID, fp)]).
{ intros rs Hm. apply (eb_awr_skel E2 [R2_sp; R2_in] rs _ _ _ _ _ _ _ Hm).
  unfold R2_sp, R2_in.
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
    [reflexivity | rewrite U9; lia | cbn; unfold GB_STK; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
(* the frame and its shadow, kept by the malloc wrapper *)
pose proof (eb_F cx fp (k + 1) ly2 S2 W2 mem2 md2 HB HJ2 HFR2) as (EF2 & _).
assert (MF : forall a, (gF cx fp <= a < gF cx fp + 512 \/ gSH cx fp <= a < gSH cx fp + 64) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha.
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 r 288 GB_CID fp HAR2 Hrin
    ltac:(rewrite HFR2; left; reflexivity)) as DSF.
  rewrite EF2 in DSF. unfold zdisjoint in DSF. cbn [fst snd] in DSF.
  change (req_size 288) with 288 in DSF. change (fs_frame_bytes GB_CID) with 512 in DSF.
  pose proof (Z.mul_div_le (gF cx fp) 8 ltac:(lia)) as D8.
  assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  destruct HK2 as (_ & _ & _ & K4 & _).
  rewrite (K4 GB_CID fp a ltac:(rewrite HFR; left; reflexivity)).
  - apply M1. rewrite HSHeq in Ha. unfold SHADOW_OFF in Ha. lia.
  - destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF.
    + change (fs_frame_bytes GB_CID) with 512. lia.
    + unfold shadow_addr. change (fs_frame_bytes GB_CID / 8) with 64. rewrite HSHeq in Ha. lia.
  - cbv beta. change (req_size 288) with 288. rewrite HSHeq in Ha.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
destruct (Z.eq_dec (c_n cx) 0) as [Hn0 | Hn0].
- (* the empty input: s3 = 0 *)
  assert (HS2 : st_ok_pi SEGS VAL E2 ss_e2_0 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1d0)) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_e2_0. apply pa_entry_st_ok_full.
    - subst E2. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [exact Rsp2 | apply Forall_nil].
    - apply pairwise_disjoint_of_extents. cbn. repeat split.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U10, U18, U21, F32, unsigned_lit_small by (unfold SBe; lia).
      change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite Z.pow_0_r, !Z.mod_1_r. unfold SBe, SHADOW_OFF.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  assert (SHOK2 : sh_ok SEGS Bx18 [] E2 (mrestrict (w_H W2) mem2)) by constructor.
  clear HE2.
  assert (KP0 : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E2 (ss_mem ss_e2_0) a ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W2) mem2 a) by reflexivity.
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 Bspane GE_I; [apply AWR2; vm_compute; reflexivity |].
  e2_keep KP0.
  (* 0x80128: beqz s5 (n = 0) *)
  psrr_branch_tok RUN BR HS2 SHOK2 Bspane.
  2: { exfalso. rewrite branch_eq_U, (U_atom E2 21 (c_n cx)), U_SLit in Hc
         by first [rewrite (EE2 21%nat 21%bv eq_refl), R21; reflexivity | lia].
       rewrite Hn0 in Hc. cbn in Hc. discriminate Hc. }
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 Bspane GE_I; [apply AWR2; vm_compute; reflexivity |].
  e2_keep KP0.
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => rename msx into ms5; rename HSx into HS5 end.
  assert (OUT5 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx <= a < c_sp1 cx + 0x98) ->
    aview SEGS (w_H W2) (ms_mem ms5) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hna. apply KP0; [exact Ha|]. intros (rr & Hr & Hbb). unfold ss_e2_0, R2_sp in Hr. cbn [ss_mem In] in Hr.
    destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hbb. rewrite U9 in Hbb. lia. }
  lazymatch type of HS5 with st_ok_pi _ _ _ ?ssF _ =>
    let r0 := eval vm_compute in (nth_error (ss_mem ssF) 0) in
    lazymatch r0 with Some ?rr0 => pose proof (st_ok_pi_region_nth E2 ssF _ 0 rr0 HS5 eq_refl) as HR0 end end.
  cbn [restrict ms_mem] in HR0.
  apply (HNEXT cx fp (k + 1) (acc + mo_malloc MT 288) ly2 S2 W2 ms5 _ HB HJ2 HFR2
    (mle_station MT (c_S cx) S3 S2 acc (mo_malloc MT 288) MTL HMO MLE2)).
  exists r.
  pose proof (eb_mach_of E2 _ (w_H W2) ms5 HS5 eq_refl) as HM5. cbn [ss_pc] in HM5.
  prreg HS5 (2%bv : bv 5) T2. prreg HS5 (3%bv : bv 5) T3. prreg HS5 (4%bv : bv 5) T4. prreg HS5 (8%bv : bv 5) T8.
  prreg HS5 (9%bv : bv 5) T9. prreg HS5 (10%bv : bv 5) T10. prreg HS5 (11%bv : bv 5) T11. prreg HS5 (18%bv : bv 5) T18.
  prreg HS5 (19%bv : bv 5) T19. prreg HS5 (20%bv : bv 5) T20. prreg HS5 (22%bv : bv 5) T22. prreg HS5 (24%bv : bv 5) T24.
  prreg HS5 (25%bv : bv 5) T25.
  assert (Eb0 : eb_b (c_pl cx) = 0) by (unfold c_n in Hn0; destruct (c_pl cx); [reflexivity | cbn in Hn0; lia]).
  assert (Epos : eb_pos cx = 0) by (unfold eb_pos; rewrite Hn0; reflexivity).
  rewrite Epos, Eb0. change (LLVMFuzzerTestOneInput_entry.en_sx 0) with 0.
  split; [exact HM5|].
  split.
  { unfold gregs.
    split; [rewrite T2, (EE2 2%nat 2%bv eq_refl); exact R2|].
    split; [rewrite T8, (EE2 8%nat 8%bv eq_refl); exact R8|].
    split; [rewrite T9, (EE2 9%nat 9%bv eq_refl); exact R9|].
    split; [rewrite T3, (EE2 3%nat 3%bv eq_refl); exact R3|].
    split; [rewrite T4, (EE2 4%nat 4%bv eq_refl); exact R4|].
    split; [rewrite T18, (EE2 18%nat 18%bv eq_refl); exact R18|].
    rewrite T24, (EE2 24%nat 24%bv eq_refl); exact R24. }
  pose proof (Z.mul_div_le (gF cx fp) 8 ltac:(lia)) as D8.
  assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  split.
  { apply (eb_gsaved_tr cx W3 W2 ms3 ms5); [|exact GSV].
    intros a Ha. rewrite OUT5 by lia. apply MK. lia. }
  split.
  { intros i Hi. change (length GSH_J) with 52%nat in Hi. rewrite OUT5, MF.
    - exact (GSH i ltac:(change (length GSH_J) with 52%nat; lia)).
    - right. rewrite HSHeq. unfold SHADOW_OFF. lia.
    - rewrite HSHeq. unfold SHADOW_OFF. lia.
    - rewrite HSHeq. unfold SHADOW_OFF. lia. }
  split.
  { rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3))); [exact HFL|].
    intros i Hi. change (fs_frame_bytes GB_CID) with 512. rewrite OUT5, MF; [reflexivity | left | |]; lia. }
  split; [lia|]. split; [lia|].
  split; [unfold gblk1; rewrite Eab2, HAB; reflexivity|].
  split; [rewrite T20, (EE2 10%nat 10%bv eq_refl); exact Ha02|].
  split; [rewrite T10, (EE2 10%nat 10%bv eq_refl); exact Ha02|].
  split; [rewrite T22, (EE2 22%nat 22%bv eq_refl); exact R22|].
  split; [rewrite T19; reflexivity|].
  split; [rewrite T25; reflexivity|].
  split; [rewrite T11; reflexivity|].
  assert (EF22 : ew E2 22 = w64 (gF cx fp)) by (rewrite (EE2 22%nat 22%bv eq_refl); exact R22).
  assert (EP20 : ew E2 20 = w64 (c_p cx)) by (rewrite (EE2 20%nat 20%bv eq_refl); exact R20).
  assert (EN21 : ew E2 21 = w64 (c_n cx)) by (rewrite (EE2 21%nat 21%bv eq_refl); exact R21).
  split; [pose proof (eb_slot_of cx W2 ms5 E2 _ _ _ _ _ 0x80 22 0 (gF cx fp) HR0 U9
            ltac:(cbn [In]; tauto) EF22 ltac:(lia) ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X|].
  split; [pose proof (eb_slot_of cx W2 ms5 E2 _ _ _ _ _ 0x28 22 0 (gF cx fp) HR0 U9
            ltac:(cbn [In]; tauto) EF22 ltac:(lia) ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X|].
  split; [pose proof (eb_slot_of cx W2 ms5 E2 _ _ _ _ _ 0x18 22 0 (gF cx fp) HR0 U9
            ltac:(cbn [In]; tauto) EF22 ltac:(lia) ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X|].
  split; [exact (eb_slot_of cx W2 ms5 E2 _ _ _ _ _ 0x78 22 64 (gF cx fp) HR0 U9
            ltac:(cbn [In]; tauto) EF22 ltac:(lia) ltac:(lia))|].
  unfold gcursor. split; [lia|]. rewrite Z.add_0_r, Z.sub_0_r.
  split; [pose proof (eb_slot_of cx W2 ms5 E2 _ _ _ _ _ 0x88 20 0 (c_p cx) HR0 U9
            ltac:(cbn [In]; tauto) EP20 Hpr ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X|].
  pose proof (eb_slot_of cx W2 ms5 E2 _ _ _ _ _ 0x90 21 0 (c_n cx) HR0 U9
    ltac:(cbn [In]; tauto) EN21 ltac:(lia) ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X.
- (* a nonempty input: b, its first byte, after its shadow test *)
  assert (Hn1 : 0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))
    by (destruct Hpn as [(H0 & _) | H1]; [lia | exact H1]).
  destruct Hn1 as (Hn1 & HinP).
  pose proof HB as ((HAR0 & _) & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 HinP) as (Hp16 & Hp4096 & Hpce & Hpapp & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
  assert (HinP2 : In (c_p cx, c_n cx) (ablocks B ly2 S2)) by (rewrite Eab2, HAB; apply in_or_app; left; exact HinP).
  assert (U20 : bv_unsigned (ew E2 20) = c_p cx) by (rewrite (EE2 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
  assert (HB0 : aview SEGS (w_H W2) mem2 (c_p cx) = Some (eb_b (c_pl cx))).
  { replace (c_p cx) with (c_p cx + 0) by lia.
    rewrite (F2' (c_p cx) (c_n cx) 0 HinP HinP2 ltac:(lia) (inFP_nil _)).
    unfold c_n in Hn1. destruct (c_pl cx) as [|b0 pl0] eqn:Epl; [cbn in Hn1; lia|].
    destruct (HIN 0%nat ltac:(cbn; lia)) as [Hv Hr]. cbn [nth map] in Hv, Hr.
    apply (aview_of_val_mem1 SEGS (w_H (c_W cx)) (c_mem cx)); [exact Hv | exact Hr]. }
  assert (HS2 : st_ok_pi SEGS VAL E2 ss_e2_1 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1d0)) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_e2_1. apply pa_entry_st_ok_full.
    - subst E2. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [exact Rsp2|]. apply Forall_cons; [|apply Forall_nil].
      unfold R2_in, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val]. rewrite U20.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E2 _ (c_p cx) 0 1 (SOff 33 0) (eb_b (c_pl cx)));
        [cbn [sv_denot]; rewrite F33, Z.add_0_r, unsigned_lit_small by lia; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (proj1 (val_mem1_of_aview SEGS (w_H W2) mem2 _ _ HB0)).
    - apply pairwise_disjoint_of_extents. unfold R2_sp, R2_in, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U9, U20.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U10, U18, U20, U21, F32, unsigned_lit_small by (unfold SBe; lia).
      change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite Z.pow_0_r, !Z.mod_1_r. unfold SBe, SHADOW_OFF.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  assert (UB : U E2 Bx18 = SHADOW_OFF) by (unfold Bx18; apply (U_atom E2 18 SHADOW_OFF); [rewrite (EE2 18%nat 18%bv eq_refl), R18; reflexivity | unfold SHADOW_OFF; lia]).
  assert (UP : U E2 (SOff 20 0) = c_p cx) by (apply (U_atom E2 20 (c_p cx)); [rewrite (EE2 20%nat 20%bv eq_refl), R20; reflexivity | lia]).
  assert (RAP : range_addressable (rd_of SEGS (mrestrict (w_H W2) mem2)) SHADOW_OFF (c_p cx) 1).
  { rewrite <- (aview_rd_of SEGS).
    exact (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 (c_p cx) (c_n cx) (c_p cx) 1 HAR2 HinP2 ltac:(lia) ltac:(lia)). }
  assert (SHOK2 : sh_ok SEGS Bx18 [mkSHE 20 0 1] E2 (mrestrict (w_H W2) mem2)).
  { apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    rewrite UB, UP, Z.add_0_r. split; [exact RAP|].
    intros a Ha. change (Z.min 0 1) with 0 in Ha. change (Z.max 0 1) with 1 in Ha.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
  clear HE2.
  assert (KP0 : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E2 (ss_mem ss_e2_1) a ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W2) mem2 a) by reflexivity.
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 Bspane GE_I; [apply AWR2'; vm_compute; reflexivity |].
  e2_keep KP0.
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => rename msx into ms5; rename HSx into HS5 end.
  assert (OUT5 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx <= a < c_sp1 cx + 0x98) ->
    aview SEGS (w_H W2) (ms_mem ms5) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hna. apply KP0; [exact Ha|]. intros (rr & Hr & Hbb). unfold ss_e2_1, R2_sp, R2_in in Hr.
    cbn [ss_mem In] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hbb;
      rewrite ?U9 in Hbb; lia. }
  lazymatch type of HS5 with st_ok_pi _ _ ?E5 _ _ => set (E5x := E5) in HS5 end.
  assert (A5 : forall n, (n < 512)%nat -> ew E5x n = ew E2 n) by (intros n Hn5; unfold E5x; rewrite !ew_ewset_other by lia; reflexivity).
  lazymatch type of HS5 with st_ok_pi _ _ _ ?ssF _ =>
    let r0 := eval vm_compute in (nth_error (ss_mem ssF) 0) in
    lazymatch r0 with Some ?rr0 => pose proof (st_ok_pi_region_nth E5x ssF _ 0 rr0 HS5 eq_refl) as HR0 end end.
  cbn [restrict ms_mem] in HR0.
  apply (HNEXT cx fp (k + 1) (acc + mo_malloc MT 288) ly2 S2 W2 ms5 _ HB HJ2 HFR2
    (mle_station MT (c_S cx) S3 S2 acc (mo_malloc MT 288) MTL HMO MLE2)).
  exists r.
  pose proof (eb_mach_of E5x _ (w_H W2) ms5 HS5 eq_refl) as HM5. cbn [ss_pc] in HM5.
  assert (TR : forall (rg : bv 5), getr (ms_regs ms5) rg = sv_denot E5x (sr_get (ss_regs _) rg))
    by (intros rg; exact (st_ok_pi_restrict_reg (w_H W2) E5x _ ms5 rg HS5)).
  assert (AT : forall (n : nat) (rg : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rg ->
    sv_denot E5x (SOff n 0) = getr regs2 rg).
  { intros n rg Hn5 Hnr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, A5 by lia. exact (EE2 n rg Hnr). }
  lazymatch type of HS5 with st_ok_pi _ _ _ ?ssF _ =>
    let rgv r := eval vm_compute in (sr_get (ss_regs ssF) r) in
    let e2 := rgv (2%bv : bv 5) in let e3 := rgv (3%bv : bv 5) in let e4 := rgv (4%bv : bv 5) in let e8 := rgv (8%bv : bv 5) in let e9 := rgv (9%bv : bv 5) in
    let e10 := rgv (10%bv : bv 5) in let e11 := rgv (11%bv : bv 5) in let e18 := rgv (18%bv : bv 5) in let e19 := rgv (19%bv : bv 5) in
    let e20 := rgv (20%bv : bv 5) in let e22 := rgv (22%bv : bv 5) in let e24 := rgv (24%bv : bv 5) in let e25 := rgv (25%bv : bv 5) in
    pose proof (TR (2%bv : bv 5)) as T2; change (sr_get (ss_regs ssF) (2%bv : bv 5)) with e2 in T2;
    pose proof (TR (3%bv : bv 5)) as T3; change (sr_get (ss_regs ssF) (3%bv : bv 5)) with e3 in T3;
    pose proof (TR (4%bv : bv 5)) as T4; change (sr_get (ss_regs ssF) (4%bv : bv 5)) with e4 in T4;
    pose proof (TR (8%bv : bv 5)) as T8; change (sr_get (ss_regs ssF) (8%bv : bv 5)) with e8 in T8;
    pose proof (TR (9%bv : bv 5)) as T9; change (sr_get (ss_regs ssF) (9%bv : bv 5)) with e9 in T9;
    pose proof (TR (10%bv : bv 5)) as T10; change (sr_get (ss_regs ssF) (10%bv : bv 5)) with e10 in T10;
    pose proof (TR (11%bv : bv 5)) as T11; change (sr_get (ss_regs ssF) (11%bv : bv 5)) with e11 in T11;
    pose proof (TR (18%bv : bv 5)) as T18; change (sr_get (ss_regs ssF) (18%bv : bv 5)) with e18 in T18;
    pose proof (TR (19%bv : bv 5)) as T19; change (sr_get (ss_regs ssF) (19%bv : bv 5)) with e19 in T19;
    pose proof (TR (20%bv : bv 5)) as T20; change (sr_get (ss_regs ssF) (20%bv : bv 5)) with e20 in T20;
    pose proof (TR (22%bv : bv 5)) as T22; change (sr_get (ss_regs ssF) (22%bv : bv 5)) with e22 in T22;
    pose proof (TR (24%bv : bv 5)) as T24; change (sr_get (ss_regs ssF) (24%bv : bv 5)) with e24 in T24;
    pose proof (TR (25%bv : bv 5)) as T25; change (sr_get (ss_regs ssF) (25%bv : bv 5)) with e25 in T25
  end.
  clear TR.
  assert (Epos : eb_pos cx = 1) by (unfold eb_pos; rewrite (proj2 (Z.eqb_neq _ _) Hn0); reflexivity).
  assert (F33' : ew E5x 33 = Z_to_bv 64 (eb_b (c_pl cx))) by (rewrite A5 by lia; exact F33).
  assert (Z19 : sv_denot E5x (SExt false 8 (SOff 33 0)) = Z_to_bv 64 (eb_b (c_pl cx)))
    by exact (eb_zext8 E5x 33 _ F33' Hb256).
  assert (U19 : U E5x (SExt false 8 (SOff 33 0)) = eb_b (c_pl cx))
    by (unfold U; rewrite Z19; apply unsigned_lit_small; lia).
  rewrite Epos.
  split; [exact HM5|].
  split.
  { unfold gregs.
    split; [rewrite T2, (AT 2%nat 2%bv) by (reflexivity || lia); exact R2|].
    split; [rewrite T8, (AT 8%nat 8%bv) by (reflexivity || lia); exact R8|].
    split; [rewrite T9, (AT 9%nat 9%bv) by (reflexivity || lia); exact R9|].
    split; [rewrite T3, (AT 3%nat 3%bv) by (reflexivity || lia); exact R3|].
    split; [rewrite T4, (AT 4%nat 4%bv) by (reflexivity || lia); exact R4|].
    split; [rewrite T18, (AT 18%nat 18%bv) by (reflexivity || lia); exact R18|].
    rewrite T24, (AT 24%nat 24%bv) by (reflexivity || lia); exact R24. }
  pose proof (Z.mul_div_le (gF cx fp) 8 ltac:(lia)) as D8.
  assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  split.
  { apply (eb_gsaved_tr cx W3 W2 ms3 ms5); [|exact GSV].
    intros a Ha. rewrite OUT5 by lia. apply MK. lia. }
  split.
  { intros i Hi. change (length GSH_J) with 52%nat in Hi. rewrite OUT5, MF.
    - exact (GSH i ltac:(change (length GSH_J) with 52%nat; lia)).
    - right. rewrite HSHeq. unfold SHADOW_OFF. lia.
    - rewrite HSHeq. unfold SHADOW_OFF. lia.
    - rewrite HSHeq. unfold SHADOW_OFF. lia. }
  split.
  { rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3))); [exact HFL|].
    intros i Hi. change (fs_frame_bytes GB_CID) with 512. rewrite OUT5, MF; [reflexivity | left | |]; lia. }
  split; [lia|]. split; [lia|].
  split; [unfold gblk1; rewrite Eab2, HAB; reflexivity|].
  split; [rewrite T20, (AT 10%nat 10%bv) by (reflexivity || lia); exact Ha02|].
  split; [rewrite T10, (AT 10%nat 10%bv) by (reflexivity || lia); exact Ha02|].
  split; [rewrite T22, (AT 22%nat 22%bv) by (reflexivity || lia); exact R22|].
  split; [rewrite T19, Z19; reflexivity|].
  split; [rewrite T25, (eb_sext8 E5x _ _ U19 Hb256); reflexivity|].
  split; [rewrite T11, eb_add0, (eb_sext8 E5x _ _ U19 Hb256); reflexivity|].
  assert (U9' : bv_unsigned (ew E5x 9) = c_sp1 cx) by (rewrite A5 by lia; exact U9).
  assert (EF22 : ew E5x 22 = w64 (gF cx fp)) by (rewrite A5, (EE2 22%nat 22%bv eq_refl) by lia; exact R22).
  assert (EP20 : ew E5x 20 = w64 (c_p cx)) by (rewrite A5, (EE2 20%nat 20%bv eq_refl) by lia; exact R20).
  assert (EN21 : ew E5x 21 = w64 (c_n cx)) by (rewrite A5, (EE2 21%nat 21%bv eq_refl) by lia; exact R21).
  split; [pose proof (eb_slot_of cx W2 ms5 E5x _ _ _ _ _ 0x80 22 0 (gF cx fp) HR0 U9'
            ltac:(cbn [In]; tauto) EF22 ltac:(lia) ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X|].
  split; [pose proof (eb_slot_of cx W2 ms5 E5x _ _ _ _ _ 0x28 22 0 (gF cx fp) HR0 U9'
            ltac:(cbn [In]; tauto) EF22 ltac:(lia) ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X|].
  split; [pose proof (eb_slot_of cx W2 ms5 E5x _ _ _ _ _ 0x18 22 0 (gF cx fp) HR0 U9'
            ltac:(cbn [In]; tauto) EF22 ltac:(lia) ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X|].
  split; [exact (eb_slot_of cx W2 ms5 E5x _ _ _ _ _ 0x78 22 64 (gF cx fp) HR0 U9'
            ltac:(cbn [In]; tauto) EF22 ltac:(lia) ltac:(lia))|].
  unfold gcursor. split; [lia|].
  split; [exact (eb_slot_of cx W2 ms5 E5x _ _ _ _ _ 0x88 20 1 (c_p cx) HR0 U9'
            ltac:(cbn [In]; tauto) EP20 Hpr ltac:(lia))|].
  replace (c_n cx - 1) with (c_n cx + -1) by lia.
  exact (eb_slot_of cx W2 ms5 E5x _ _ _ _ _ 0x90 21 (-1) (c_n cx) HR0 U9'
    ltac:(cbn [In]; tauto) EN21 ltac:(lia) ltac:(lia)).
Qed.

(* 0x801a4: the table r holds the bytes reac_boxreg_init left, the fabric is clamped (s9, a1), the frame's slots of
   gb_body are written (0x70 = mac); check (r, fabric) is called next. *)
Definition EC (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists r,
  gb_body cx fp GE_C W3 ms3 GSH_J /\ k <= 1 /\ acc <= mo_malloc MT 288 /\ gblk1 B cx ly3 S3 r /\
  greg B ly3 S3 W3 ms3 r (eb_bs (c_pl cx)) /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 10 = w64 r /\
  getr (ms_regs ms3) 25 = w64 (eb_fab (c_pl cx)) /\ getr (ms_regs ms3) 11 = w64 (eb_fab (c_pl cx)) /\
  gcursor cx W3 ms3 (eb_pos cx).


(* The caller's input, as any journal from the call's start keeps it while its block stays allocated. *)
Lemma eb_input : forall cx own ly3 S3 W3 mem3 md3 k, gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  (forall p n, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> In (p, n) (ablocks B ly3 S3)) ->
  garr8 SEGS (mrestrict (w_H W3) mem3) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)).
Proof.
intros cx own ly3 S3 W3 mem3 md3 k HB HJ Hbl.
pose proof HB as (_ & _ & _ & Hpn & HIN & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
destruct Hpn as [(Hn0 & _) | (Hn0 & Hin)].
- unfold c_n in Hn0. destruct (c_pl cx); [apply garr8_nil | cbn in Hn0; lia].
- apply (garr8_frame SEGS _ _ _ _ HIN). intros a Ha. rewrite length_map in Ha.
  apply (mbyte_of_aview SEGS). pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. unfold c_n in *.
  replace a with (c_p cx + (a - c_p cx)) by lia.
  apply (F2 (c_p cx) (c_n cx) (a - c_p cx) Hin (Hbl _ _ Hin)); [unfold c_n; lia | apply inFP_nil].
Qed.

(* The clamp's branch (bltu at 0x80188): (b - 1) & 0xff < 40 exactly when 1 <= b <= 40. *)
Lemma eb_ltu_fab : forall E b, ew E 19 = w64 b -> 0 <= b < 256 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_AND (SOff 19 (-1)) (SLit 255))) (sv_denot E (SLit 40)) =
  ((1 <=? b) && (b <=? 40)).
Proof.
intros E b Hb Hr. rewrite branch_ltu_U, U_and_lit, (U_lit E 40) by lia.
destruct (Z.eq_dec b 0) as [-> | Hb0].
- rewrite U_SOff, Hb. vm_compute. reflexivity.
- rewrite (U_atom_off E 19 b (-1) Hb) by lia. change 255 with (Z.ones 8). rewrite Z.land_ones, Z.mod_small by lia.
  apply eq_true_iff_eq. rewrite andb_true_iff, Z.ltb_lt, !Z.leb_le. lia.
Qed.

Theorem gb_entry_c : forall POST, gb_from B MT POST EC -> gb_from B MT POST EI.
Proof.
intros POST HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
destruct HI as (r & HM & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & GSV & GSH & HFL & Hk & Hacc & HBLK & G20 & G10 & G22
  & G19 & G25 & G11 & S80 & S28 & S18 & S78 & SCUR).
pose proof HB as (HPRE & Hp & Hn & Hpn & HIN & Hfr0 & Hev & Hlive & HRO & Hsp1 & HE0 & HE02 & HE032 & HMOK & HTR & HNEED).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (eb_sp cx HB) as (Hs16 & Hslo' & Hshi' & Hs1 & Hs132).
pose proof (eb_F cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ HFR) as (EF & EFL & HF0 & HFc & HFia & HF64 & HSHeq & HFp & HFs).
pose proof HJ as (HAR3 & _).
assert (Hrin : In (r, REG_SIZE) (ablocks B ly3 S3)) by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 Hrin) as (Hr16 & Hr4096 & Hrce & Hrapp & _).
change (req_size REG_SIZE) with 288 in Hrce, Hrapp.
assert (Hb256 : 0 <= eb_b (c_pl cx) < 256) by (unfold eb_b; destruct (c_pl cx); [lia | apply u8_range]).
(* 0x80178: jal reac_boxreg_init (r, (int8_t) b) *)
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr (ms_regs ms3) r0)
  by (intros n r0 Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (HS : st_ok_pi SEGS VAL E (mkSS GE_I sr_atoms [] None (mkFacts [] [] [])) (restrict (w_H W3) ms3)).
{ rewrite (eb_ms GE_I (w_H W3) ms3 HM). apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS Bxe [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HE.
paj_run_tok RUN HS HJ SHOK Bspan0; [apply awr_ok_nil |].
lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into ms1 end.
lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (eb_frame_nil _ _ _ _ HFx) as M1 end.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
assert (GSV1 : gsaved cx W3 ms1) by (apply (eb_gsaved_tr cx W3 W3 ms3 ms1); [intros a Ha; apply M1; lia | exact GSV]).
assert (Qsp : spZ (ms_regs ms1) = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)))
  by (unfold spZ at 1; rewrite Q2, (EE 2%nat 2%bv eq_refl), G2; unfold w64; rewrite unsigned_lit_small by lia; lia).
rewrite (pa_sigma_reac_boxreg_init (PI := PI)).
set (c := LLVMFuzzerTestOneInput_entry.en_sx (eb_b (c_pl cx))).
assert (Hcr : -128 <= c < 128) by (unfold c, LLVMFuzzerTestOneInput_entry.en_sx; destruct (Z.ltb_spec (eb_b (c_pl cx)) 128); lia).
assert (Hcw : bv_swrap 32 c = c) by (apply bv_swrap_small; change (bv_half_modulus 32) with 2147483648; lia).
eapply SRr_bind.
{ eapply (cl_callS B LAWS W3 (ms_regs ms1) (ms_mem ms1) _ GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k REAC_BOXREG_INIT_STK [(r, r + REG_SIZE)] 0
    (c_sp1 cx - spZ (c_regs cx)) (getr (ms_regs ms1) 1) (gch cx)
    (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ W2 = W3 /\
       Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) /\
       (forall i, 0 <= i < REG_SIZE -> aview SEGS (w_H W2) mem2 (r + i) =
          Some (bv_unsigned (nth (Z.to_nat i) (reac_boxreg_init_c.init_bytes (reac_boxreg_init_c.clamp40 (bv_swrap 32 c)))
            (Z_to_bv 8 0))))) HJ Qsp).
  - apply eb_mod16; [exact Hs132 | exact Hs16].
  - lia.
  - unfold REAC_BOXREG_INIT_STK, ESTACK. lia.
  - unfold REAC_BOXREG_INIT_STK, ESTACK, GB_STK. lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl), G3. exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl), G4. exact Htp.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
    unfold s0Z at 1. rewrite Q8, (EE 8%nat 8%bv eq_refl), G8. unfold w64. rewrite unsigned_lit_small by lia.
    exact (eb_achain_ly cx ly3 S3 W3 (ms_mem ms1) _ [(GB_CID, fp)] k (c_sp1 cx) HB HJ (proj1 GSV1)
      (eb_gsaved_s0 cx W3 ms1 GSV1) ltac:(lia)).
  - intros HPRE1.
    exact (TINIT ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ (gch cx) r c HPRE1
      ltac:(rewrite Q10, (EE 10%nat 10%bv eq_refl); exact G10) ltac:(rewrite Q11, (EE 11%nat 11%bv eq_refl); exact G11) Hrin).
  - intros a Ha. right. unfold inFP in Ha. destruct Ha as (rg & [<- | []] & Hrg). cbn [fst snd] in Hrg.
    exists r, REG_SIZE. split; [exact Hrin|]. split; [|change (req_size REG_SIZE) with 288; unfold REG_SIZE in Hrg; lia].
    intros Hin0. unfold gblk1 in HBLK. apply in_split in Hin0 as (l1 & l2 & El).
    pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (r, REG_SIZE) (r, REG_SIZE) l1 l2 [] HAR3
      ltac:(rewrite HBLK, El, <- app_assoc; reflexivity)) as D.
    unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size REG_SIZE) with 288 in D. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (-> & -> & -> & _ & Hbytes)).
rewrite Hcw in Hbytes. rewrite Z.add_0_r in HJ2.
assert (KP3 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs2 r0 = getr (ms_regs ms1) r0).
{ intros r0 Hr0. pose proof (HP2 (bv_unsigned r0) Hr0) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
assert (R2 : getr regs2 2 = w64 (c_sp1 cx)) by (rewrite (KP3 2%bv ltac:(change (bv_unsigned (2%bv : bv 5)) with 2; unfold acallee_saved; lia)), Q2, (EE 2%nat 2%bv eq_refl); exact G2).
assert (R3 : getr regs2 3 = getr (c_regs cx) 3) by (rewrite (KP3 3%bv ltac:(change (bv_unsigned (3%bv : bv 5)) with 3; unfold acallee_saved; lia)), Q3, (EE 3%nat 3%bv eq_refl); exact G3).
assert (R4 : getr regs2 4 = getr (c_regs cx) 4) by (rewrite (KP3 4%bv ltac:(change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; lia)), Q4, (EE 4%nat 4%bv eq_refl); exact G4).
assert (R8 : getr regs2 8 = w64 (spZ (c_regs cx))) by (rewrite (KP3 8%bv ltac:(change (bv_unsigned (8%bv : bv 5)) with 8; unfold acallee_saved; lia)), Q8, (EE 8%nat 8%bv eq_refl); exact G8).
assert (R9 : getr regs2 9 = w64 (c_sp1 cx)) by (rewrite (KP3 9%bv ltac:(change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; lia)), Q9, (EE 9%nat 9%bv eq_refl); exact G9).
assert (R18 : getr regs2 18 = w64 SHADOW_OFF) by (rewrite (KP3 18%bv ltac:(change (bv_unsigned (18%bv : bv 5)) with 18; unfold acallee_saved; lia)), Q18, (EE 18%nat 18%bv eq_refl); exact G18).
assert (R19 : getr regs2 19 = w64 (eb_b (c_pl cx))) by (rewrite (KP3 19%bv ltac:(change (bv_unsigned (19%bv : bv 5)) with 19; unfold acallee_saved; lia)), Q19, (EE 19%nat 19%bv eq_refl); exact G19).
assert (R20 : getr regs2 20 = w64 r) by (rewrite (KP3 20%bv ltac:(change (bv_unsigned (20%bv : bv 5)) with 20; unfold acallee_saved; lia)), Q20, (EE 20%nat 20%bv eq_refl); exact G20).
assert (R22 : getr regs2 22 = w64 (gF cx fp)) by (rewrite (KP3 22%bv ltac:(change (bv_unsigned (22%bv : bv 5)) with 22; unfold acallee_saved; lia)), Q22, (EE 22%nat 22%bv eq_refl); exact G22).
assert (R24 : getr regs2 24 = w64 (gSH cx fp)) by (rewrite (KP3 24%bv ltac:(change (bv_unsigned (24%bv : bv 5)) with 24; unfold acallee_saved; lia)), Q24, (EE 24%nat 24%bv eq_refl); exact G24).
assert (R25 : getr regs2 25 = w64 c) by (rewrite (KP3 25%bv ltac:(change (bv_unsigned (25%bv : bv 5)) with 25; unfold acallee_saved; lia)), Q25, (EE 25%nat 25%bv eq_refl); exact G25).
clear KP3 HP2.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K1c & _ & _ & K4c & _).
assert (MK3 : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite K1c by (unfold REAC_BOXREG_INIT_STK, ESTACK in *; lia). apply M1; lia. }
pose proof (Z.mul_div_le (gF cx fp) 8 ltac:(lia)) as D8.
assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
assert (MF3 : forall a, (gF cx fp <= a < gF cx fp + 512 \/ gSH cx fp <= a < gSH cx fp + 64) ->
  aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha.
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r REG_SIZE GB_CID fp HAR3 Hrin
    ltac:(rewrite HFR; left; reflexivity)) as DSF.
  rewrite EF in DSF. unfold zdisjoint in DSF. cbn [fst snd] in DSF.
  change (req_size REG_SIZE) with 288 in DSF. change (fs_frame_bytes GB_CID) with 512 in DSF.
  rewrite (K4c GB_CID fp a ltac:(rewrite HFR; left; reflexivity)).
  - apply M1. rewrite HSHeq in Ha. unfold SHADOW_OFF in Ha. lia.
  - destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF.
    + change (fs_frame_bytes GB_CID) with 512. lia.
    + unfold shadow_addr. change (fs_frame_bytes GB_CID / 8) with 64. rewrite HSHeq in Ha. lia.
  - intros (rg & [<- | []] & Hrg). cbn [fst snd] in Hrg. unfold REG_SIZE in Hrg. rewrite HSHeq in Ha.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (SL : forall off v, 0 <= off <= 0x90 -> gslot cx W3 ms3 off v ->
  rdword (aview SEGS (w_H W3) mem2) (c_sp1 cx + off) = Some v).
{ intros off v Ho Hs. unfold gslot in Hs. rewrite <- Hs. apply rdword_ext. intros i Hi. apply MK3. lia. }
destruct SCUR as (Hpos & S88 & S90).
assert (Hpr : 0 <= c_p cx /\ c_p cx + c_n cx < 2 ^ 47).
{ destruct Hpn as [(Hn0 & ->) | (Hn0 & Hin0)]; [unfold GB_EMPTY; lia|].
  pose proof HB as ((HAR0 & _) & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin0) as (_ & H4096 & Hce & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. lia. }
assert (Hnr : 0 <= c_n cx < 2 ^ 26) by (destruct Hpn as [(H0 & _) | (H0 & _)]; lia).
remember (Eimg (Ereg regs2 [Z_to_bv 64 SBe; Z_to_bv 64 (c_p cx + eb_pos cx); Z_to_bv 64 (c_n cx - eb_pos cx)])) as E3 eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; apply Eimg_env).
assert (EE3 : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E3 n = getr regs2 r0)
  by (intros n r0 Hn0; subst E3; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (F32 : ew E3 32 = Z_to_bv 64 SBe) by (subst E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (F33 : ew E3 33 = w64 (c_p cx + eb_pos cx)) by (subst E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (F34 : ew E3 34 = w64 (c_n cx - eb_pos cx)) by (subst E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (U9 : bv_unsigned (ew E3 9) = c_sp1 cx) by (rewrite (EE3 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (F22 : ew E3 22 = w64 (gF cx fp)) by (rewrite (EE3 22%nat 22%bv eq_refl); exact R22).
assert (SPC : forall off (n : nat) c0 v, ew E3 n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c0 < 2 ^ 64 ->
  rdword (aview SEGS (w_H W3) mem2) (c_sp1 cx + off) = Some (v + c0) ->
  YP09.chunk_ok SEGS E3 (mrestrict (w_H W3) mem2) (c_sp1 cx) (YP09.mkChunk off (CVal 8 (SOff n c0)))).
{ intros off n c0 v Hn0 Hv Hvc Hrd.
  apply (chunk_ok_val SEGS E3 _ (c_sp1 cx) off 8 (SOff n c0) (v + c0)); [| zside | zside |].
  - rewrite denot_lit_U. f_equal. exact (U_atom_off E3 n v c0 Hn0 Hv Hvc).
  - exact (val_mem_of_rdword SEGS (w_H W3) mem2 _ _ Hrd). }
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
assert (HS3 : st_ok_pi SEGS VAL E3 ss_e3 (restrict (w_H W3) (mkst regs2 (getr (ms_regs ms1) 1) mem2 (seg_rom SEGS)))).
{ rewrite Q1, restrict_mkst_fx. unfold ss_e3. apply pa_entry_st_ok_full.
  - subst E3. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold R3_sp, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split.
    + intros o Ho. apply (apresent_writable SEGS). apply HJpres2. unfold GB_STK; lia.
    + repeat apply Forall_cons; try apply Forall_nil.
      * apply (SPC 0x80 22%nat 0 (gF cx fp) F22); [lia | lia | rewrite Z.add_0_r; apply SL; [lia | exact S80]].
      * apply (SPC 0x28 22%nat 0 (gF cx fp) F22); [lia | lia | rewrite Z.add_0_r; apply SL; [lia | exact S28]].
      * apply (SPC 0x18 22%nat 0 (gF cx fp) F22); [lia | lia | rewrite Z.add_0_r; apply SL; [lia | exact S18]].
      * apply (SPC 0x78 22%nat 64 (gF cx fp) F22); [lia | lia | apply SL; [lia | exact S78]].
      * apply (SPC 0x88 33%nat 0 (c_p cx + eb_pos cx) F33); [lia | lia | rewrite Z.add_0_r; apply SL; [lia | exact S88]].
      * apply (SPC 0x90 34%nat 0 (c_n cx - eb_pos cx) F34); [lia | lia | rewrite Z.add_0_r; apply SL; [lia | exact S90]].
  - apply pairwise_disjoint_of_extents. cbn. repeat split.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, F32, unsigned_lit_small by (unfold SBe; lia).
    change (2 ^ 5) with 32. rewrite Z.pow_0_r, !Z.mod_1_r. unfold SBe.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK3 : sh_ok SEGS Bxe [] E3 (mrestrict (w_H W3) mem2)) by constructor.
assert (AWR3 : forall rs, map eb_wsk rs = map eb_wsk [R3_sp] ->
  awr_ok E3 rs GB_STK (spZ (c_regs cx)) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(GB_CID, fp)]).
{ intros rs Hm. apply (eb_awr_skel E3 [R3_sp] rs _ _ _ _ _ _ _ Hm).
  unfold R3_sp.
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
    [reflexivity | rewrite U9; lia | cbn; unfold GB_STK; lia | cbn; lia |].
  apply awr_ok_nil. }
assert (KP0 : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E3 (ss_mem ss_e3) a ->
  aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem2 a) by reflexivity.
clear HE3.
paj_run_tok RUN HS3 HJ2 SHOK3 Bspan0; [apply AWR3; vm_compute; reflexivity |].
e2_keep KP0.
(* 0x80188: bltu ((b - 1) & 0xff, 40): the fabric is b when 1 <= b <= 40, else 40 *)
assert (F19 : ew E3 19 = w64 (eb_b (c_pl cx))) by (rewrite (EE3 19%nat 19%bv eq_refl); exact R19).
psrr_branch_tok RUN BR HS3 SHOK3 Bspan0; rewrite (eb_ltu_fab E3 _ F19 Hb256) in Hc.
- (* 1 <= b <= 40: s9 stays (int8_t) b *)
  apply andb_true_iff in Hc. destruct Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  assert (Efab : eb_fab (c_pl cx) = c).
  { unfold eb_fab, c. rewrite (LLVMFuzzerTestOneInput_entry.en_clamp_in (eb_b (c_pl cx)) ltac:(lia)).
    unfold LLVMFuzzerTestOneInput_entry.en_sx. rewrite (proj2 (Z.ltb_lt _ 128)) by lia. reflexivity. }
  paj_run_to_tok RUNTO HS3 HJ2 SHOK3 Bspan0 GE_C; [apply AWR3; vm_compute; reflexivity |].
  e2_keep KP0.
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => rename msx into ms5; rename HSx into HS5 end.
  prreg HS5 (25%bv : bv 5) T25. prreg HS5 (11%bv : bv 5) T11.
  assert (FAB25 : getr (ms_regs ms5) 25 = w64 (eb_fab (c_pl cx))) by (rewrite T25, (EE3 25%nat 25%bv eq_refl), Efab; exact R25).
  assert (FAB11 : getr (ms_regs ms5) 11 = w64 (eb_fab (c_pl cx))) by (rewrite T11, (EE3 25%nat 25%bv eq_refl), Efab; exact R25).
  clear T25 T11.
  assert (OUT5 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx <= a < c_sp1 cx + 0x98) ->
    aview SEGS (w_H W3) (ms_mem ms5) a = aview SEGS (w_H W3) mem2 a).
  { intros a Ha Hna. apply KP0; [exact Ha|]. intros (rr & Hr & Hbb). unfold ss_e3, R3_sp in Hr. cbn [ss_mem In] in Hr.
    destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hbb. rewrite U9 in Hbb. lia. }
  lazymatch type of HS5 with st_ok_pi _ _ _ ?ssF _ =>
    let r0 := eval vm_compute in (nth_error (ss_mem ssF) 0) in
    lazymatch r0 with Some ?rr0 => pose proof (st_ok_pi_region_nth E3 ssF _ 0 rr0 HS5 eq_refl) as HR0 end end.
  cbn [restrict ms_mem] in HR0.
  apply (HNEXT cx fp k acc ly3 S3 W3 ms5 _ HB HJ2 HFR HMO).
  exists r.
  pose proof (eb_mach_of E3 _ (w_H W3) ms5 HS5 eq_refl) as (HP5 & HV5 & HC5 & HO5 & HF5 & HX5). cbn [ss_pc] in HP5.
  prreg HS5 (2%bv : bv 5) T2. prreg HS5 (3%bv : bv 5) T3. prreg HS5 (4%bv : bv 5) T4. prreg HS5 (8%bv : bv 5) T8.
  prreg HS5 (9%bv : bv 5) T9. prreg HS5 (10%bv : bv 5) T10. prreg HS5 (18%bv : bv 5) T18.
  prreg HS5 (20%bv : bv 5) T20. prreg HS5 (24%bv : bv 5) T24.
  assert (SLOT : forall off (n : nat) c0 v, In (YP09.mkChunk off (CVal 8 (SOff n c0)))
      [YP09.mkChunk 0x70 (CVal 8 (SOff 22 32)); YP09.mkChunk 0x80 (CVal 8 (SOff 22 0));
       YP09.mkChunk 0x28 (CVal 8 (SOff 22 0)); YP09.mkChunk 0x18 (CVal 8 (SOff 22 0));
       YP09.mkChunk 0x78 (CVal 8 (SOff 22 64)); YP09.mkChunk 0x88 (CVal 8 (SOff 33 0));
       YP09.mkChunk 0x90 (CVal 8 (SOff 34 0))] ->
    ew E3 n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c0 < 2 ^ 64 -> gslot cx W3 ms5 off (v + c0)).
  { intros off n c0 v Hin Hn5 Hv Hvc. eapply (eb_slot_of cx W3 ms5 E3 _ _ _ _ _ off n c0 v HR0 U9); [|exact Hn5 | exact Hv | exact Hvc].
    revert Hin. clear. intros Hin. cbn [In] in Hin |- *.
    repeat (destruct Hin as [Hin | Hin]; [rewrite <- Hin; repeat (first [left; reflexivity | right]) |]). destruct Hin. }
  split.
  { unfold gb_body.
    split; [exact HP5|]. split; [exact HV5|]. split; [exact HC5|]. split; [exact HO5|]. split; [exact HF5|].
    split; [exact HX5|].
    split.
    { unfold gregs.
      split; [rewrite T2, (EE3 2%nat 2%bv eq_refl); exact R2|].
      split; [rewrite T8, (EE3 8%nat 8%bv eq_refl); exact R8|].
      split; [rewrite T9, (EE3 9%nat 9%bv eq_refl); exact R9|].
      split; [rewrite T3, (EE3 3%nat 3%bv eq_refl); exact R3|].
      split; [rewrite T4, (EE3 4%nat 4%bv eq_refl); exact R4|].
      split; [rewrite T18, (EE3 18%nat 18%bv eq_refl); exact R18|].
      rewrite T24, (EE3 24%nat 24%bv eq_refl); exact R24. }
    split.
    { apply (eb_gsaved_tr cx W3 W3 ms3 ms5); [|exact GSV].
      intros a Ha. rewrite OUT5 by lia. apply MK3. lia. }
    split.
    { intros i Hi. change (length GSH_J) with 52%nat in Hi. rewrite OUT5, MF3.
      - exact (GSH i ltac:(change (length GSH_J) with 52%nat; lia)).
      - right. rewrite HSHeq. unfold SHADOW_OFF. lia.
      - rewrite HSHeq. unfold SHADOW_OFF. lia.
      - rewrite HSHeq. unfold SHADOW_OFF. lia. }
    split; [reflexivity|].
    split.
    { rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3))); [exact HFL|].
      intros i Hi. change (fs_frame_bytes GB_CID) with 512. rewrite OUT5, MF3; [reflexivity | left | |]; lia. }
    split.
    { unfold gslots_fr, GO_MAC, GO_PREV.
      split; [pose proof (SLOT 0x18 22%nat 0 (gF cx fp) ltac:(cbn [In]; tauto) F22 ltac:(lia) ltac:(lia)) as X;
              rewrite Z.add_0_r in X; exact X|].
      split; [pose proof (SLOT 0x28 22%nat 0 (gF cx fp) ltac:(cbn [In]; tauto) F22 ltac:(lia) ltac:(lia)) as X;
              rewrite Z.add_0_r in X; exact X|].
      split; [exact (SLOT 0x70 22%nat 32 (gF cx fp) ltac:(cbn [In]; tauto) F22 ltac:(lia) ltac:(lia))|].
      split; [exact (SLOT 0x78 22%nat 64 (gF cx fp) ltac:(cbn [In]; tauto) F22 ltac:(lia) ltac:(lia))|].
      pose proof (SLOT 0x80 22%nat 0 (gF cx fp) ltac:(cbn [In]; tauto) F22 ltac:(lia) ltac:(lia)) as X;
        rewrite Z.add_0_r in X; exact X. }
    apply (eb_input cx _ ly3 S3 W3 (ms_mem ms5) _ k HB HJ2).
    intros p0 n0 Hp0. unfold gblk1 in HBLK. rewrite HBLK. apply in_or_app. left. exact Hp0. }
  split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split.
  { split; [exact Hrin|]. split; [unfold eb_bs; apply BoxregInit.init_bytes_length|].
    intros i Hi. rewrite OUT5 by (unfold REG_SIZE in Hi; lia). exact (Hbytes i Hi). }
  split; [rewrite T20, (EE3 20%nat 20%bv eq_refl); exact R20|].
  split; [rewrite T10, (EE3 20%nat 20%bv eq_refl); exact R20|].
  split; [exact FAB25|]. split; [exact FAB11|].
  unfold gcursor. split; [exact Hpos|].
  split; [pose proof (SLOT 0x88 33%nat 0 (c_p cx + eb_pos cx) ltac:(cbn [In]; tauto) F33 ltac:(lia) ltac:(lia)) as X;
          rewrite Z.add_0_r in X; exact X|].
  pose proof (SLOT 0x90 34%nat 0 (c_n cx - eb_pos cx) ltac:(cbn [In]; tauto) F34 ltac:(lia) ltac:(lia)) as X;
    rewrite Z.add_0_r in X; exact X.

- (* otherwise: s9 = 40 *)
  assert (Efab : eb_fab (c_pl cx) = 40).
  { unfold eb_fab. apply (LLVMFuzzerTestOneInput_entry.en_clamp_out (eb_b (c_pl cx))); [lia|].
    intros Hin. rewrite (proj2 (Z.leb_le 1 _)), (proj2 (Z.leb_le _ 40)) in Hc by lia. discriminate Hc. }
  paj_run_to_tok RUNTO HS3 HJ2 SHOK3 Bspan0 GE_C; [apply AWR3; vm_compute; reflexivity |].
  e2_keep KP0.
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => rename msx into ms5; rename HSx into HS5 end.
  prreg HS5 (25%bv : bv 5) T25. prreg HS5 (11%bv : bv 5) T11.
  assert (FAB25 : getr (ms_regs ms5) 25 = w64 (eb_fab (c_pl cx))) by (rewrite T25, Efab; reflexivity).
  assert (FAB11 : getr (ms_regs ms5) 11 = w64 (eb_fab (c_pl cx))) by (rewrite T11, Efab; reflexivity).
  clear T25 T11.
  assert (OUT5 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx <= a < c_sp1 cx + 0x98) ->
    aview SEGS (w_H W3) (ms_mem ms5) a = aview SEGS (w_H W3) mem2 a).
  { intros a Ha Hna. apply KP0; [exact Ha|]. intros (rr & Hr & Hbb). unfold ss_e3, R3_sp in Hr. cbn [ss_mem In] in Hr.
    destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hbb. rewrite U9 in Hbb. lia. }
  lazymatch type of HS5 with st_ok_pi _ _ _ ?ssF _ =>
    let r0 := eval vm_compute in (nth_error (ss_mem ssF) 0) in
    lazymatch r0 with Some ?rr0 => pose proof (st_ok_pi_region_nth E3 ssF _ 0 rr0 HS5 eq_refl) as HR0 end end.
  cbn [restrict ms_mem] in HR0.
  apply (HNEXT cx fp k acc ly3 S3 W3 ms5 _ HB HJ2 HFR HMO).
  exists r.
  pose proof (eb_mach_of E3 _ (w_H W3) ms5 HS5 eq_refl) as (HP5 & HV5 & HC5 & HO5 & HF5 & HX5). cbn [ss_pc] in HP5.
  prreg HS5 (2%bv : bv 5) T2. prreg HS5 (3%bv : bv 5) T3. prreg HS5 (4%bv : bv 5) T4. prreg HS5 (8%bv : bv 5) T8.
  prreg HS5 (9%bv : bv 5) T9. prreg HS5 (10%bv : bv 5) T10. prreg HS5 (18%bv : bv 5) T18.
  prreg HS5 (20%bv : bv 5) T20. prreg HS5 (24%bv : bv 5) T24.
  assert (SLOT : forall off (n : nat) c0 v, In (YP09.mkChunk off (CVal 8 (SOff n c0)))
      [YP09.mkChunk 0x70 (CVal 8 (SOff 22 32)); YP09.mkChunk 0x80 (CVal 8 (SOff 22 0));
       YP09.mkChunk 0x28 (CVal 8 (SOff 22 0)); YP09.mkChunk 0x18 (CVal 8 (SOff 22 0));
       YP09.mkChunk 0x78 (CVal 8 (SOff 22 64)); YP09.mkChunk 0x88 (CVal 8 (SOff 33 0));
       YP09.mkChunk 0x90 (CVal 8 (SOff 34 0))] ->
    ew E3 n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c0 < 2 ^ 64 -> gslot cx W3 ms5 off (v + c0)).
  { intros off n c0 v Hin Hn5 Hv Hvc. eapply (eb_slot_of cx W3 ms5 E3 _ _ _ _ _ off n c0 v HR0 U9); [|exact Hn5 | exact Hv | exact Hvc].
    revert Hin. clear. intros Hin. cbn [In] in Hin |- *.
    repeat (destruct Hin as [Hin | Hin]; [rewrite <- Hin; repeat (first [left; reflexivity | right]) |]). destruct Hin. }
  split.
  { unfold gb_body.
    split; [exact HP5|]. split; [exact HV5|]. split; [exact HC5|]. split; [exact HO5|]. split; [exact HF5|].
    split; [exact HX5|].
    split.
    { unfold gregs.
      split; [rewrite T2, (EE3 2%nat 2%bv eq_refl); exact R2|].
      split; [rewrite T8, (EE3 8%nat 8%bv eq_refl); exact R8|].
      split; [rewrite T9, (EE3 9%nat 9%bv eq_refl); exact R9|].
      split; [rewrite T3, (EE3 3%nat 3%bv eq_refl); exact R3|].
      split; [rewrite T4, (EE3 4%nat 4%bv eq_refl); exact R4|].
      split; [rewrite T18, (EE3 18%nat 18%bv eq_refl); exact R18|].
      rewrite T24, (EE3 24%nat 24%bv eq_refl); exact R24. }
    split.
    { apply (eb_gsaved_tr cx W3 W3 ms3 ms5); [|exact GSV].
      intros a Ha. rewrite OUT5 by lia. apply MK3. lia. }
    split.
    { intros i Hi. change (length GSH_J) with 52%nat in Hi. rewrite OUT5, MF3.
      - exact (GSH i ltac:(change (length GSH_J) with 52%nat; lia)).
      - right. rewrite HSHeq. unfold SHADOW_OFF. lia.
      - rewrite HSHeq. unfold SHADOW_OFF. lia.
      - rewrite HSHeq. unfold SHADOW_OFF. lia. }
    split; [reflexivity|].
    split.
    { rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3))); [exact HFL|].
      intros i Hi. change (fs_frame_bytes GB_CID) with 512. rewrite OUT5, MF3; [reflexivity | left | |]; lia. }
    split.
    { unfold gslots_fr, GO_MAC, GO_PREV.
      split; [pose proof (SLOT 0x18 22%nat 0 (gF cx fp) ltac:(cbn [In]; tauto) F22 ltac:(lia) ltac:(lia)) as X;
              rewrite Z.add_0_r in X; exact X|].
      split; [pose proof (SLOT 0x28 22%nat 0 (gF cx fp) ltac:(cbn [In]; tauto) F22 ltac:(lia) ltac:(lia)) as X;
              rewrite Z.add_0_r in X; exact X|].
      split; [exact (SLOT 0x70 22%nat 32 (gF cx fp) ltac:(cbn [In]; tauto) F22 ltac:(lia) ltac:(lia))|].
      split; [exact (SLOT 0x78 22%nat 64 (gF cx fp) ltac:(cbn [In]; tauto) F22 ltac:(lia) ltac:(lia))|].
      pose proof (SLOT 0x80 22%nat 0 (gF cx fp) ltac:(cbn [In]; tauto) F22 ltac:(lia) ltac:(lia)) as X;
        rewrite Z.add_0_r in X; exact X. }
    apply (eb_input cx _ ly3 S3 W3 (ms_mem ms5) _ k HB HJ2).
    intros p0 n0 Hp0. unfold gblk1 in HBLK. rewrite HBLK. apply in_or_app. left. exact Hp0. }
  split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split.
  { split; [exact Hrin|]. split; [unfold eb_bs; apply BoxregInit.init_bytes_length|].
    intros i Hi. rewrite OUT5 by (unfold REG_SIZE in Hi; lia). exact (Hbytes i Hi). }
  split; [rewrite T20, (EE3 20%nat 20%bv eq_refl); exact R20|].
  split; [rewrite T10, (EE3 20%nat 20%bv eq_refl); exact R20|].
  split; [exact FAB25|]. split; [exact FAB11|].
  unfold gcursor. split; [exact Hpos|].
  split; [pose proof (SLOT 0x88 33%nat 0 (c_p cx + eb_pos cx) ltac:(cbn [In]; tauto) F33 ltac:(lia) ltac:(lia)) as X;
          rewrite Z.add_0_r in X; exact X|].
  pose proof (SLOT 0x90 34%nat 0 (c_n cx - eb_pos cx) ltac:(cbn [In]; tauto) F34 ltac:(lia) ltac:(lia)) as X;
    rewrite Z.add_0_r in X; exact X.
Qed.
(* The chunk a slot is read from, in a region's concrete chunk list. *)
Local Ltac inch := cbn [In]; repeat (first [left; reflexivity | right]).


(* The read-only view of the entry, kept by a journal of this call (its footprint is empty, so the sink's head is
   not in it). *)
Lemma eb_arodata : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem').
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (fp_spares_closed [] a sink_closed_nil)].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
exact (pa_relro_img a Hgot).
Qed.

(* A spill slot, read back from any chunk of a region over the realigned stack pointer (atom 9). *)
Lemma eb_slot_U : forall cx (W : world SEGS) ms E cs lo hi wlo whi off e v,
  YP09.region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 9) = c_sp1 cx -> In (YP09.mkChunk off (CVal 8 e)) cs -> U E e = v ->
  gslot cx W ms off v.
Proof.
intros cx W ms E cs lo hi wlo whi off e v HR Hb Hin Hv. unfold gslot.
rewrite (eb_rdword_chunk E (w_H W) (ms_mem ms) 9 _ cs lo hi wlo whi off e HR Hb Hin). rewrite <- Hv. reflexivity.
Qed.

(* The shadow addresses the loop's set-up computes (0x801bc .. 0x801dc), in both operand orders. *)
Lemma eb_shadow_U : forall E r c, ew E 20 = w64 r -> ew E 18 = w64 SHADOW_OFF -> 0 <= r -> 0 <= c -> r + c < 2 ^ 47 ->
  U E (SAlu ALU_ADD (SOff 18 0) (SAlu ALU_SRL (SOff 20 c) (SLit 3))) = shadow_of_addr SHADOW_OFF (r + c) /\
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 c) (SLit 3)) (SOff 18 0)) = shadow_of_addr SHADOW_OFF (r + c).
Proof.
intros E r c H20 H18 Hr Hc Hrc.
assert (Hd0 : 0 <= (r + c) / 8) by (apply Z.div_pos; lia).
assert (Hd1 : (r + c) / 8 <= r + c) by (apply Z.div_le_upper_bound; lia).
assert (U20 : U E (SOff 20 c) = r + c) by (apply (U_atom_off E 20 r c H20); lia).
assert (U18 : U E (SOff 18 0) = SHADOW_OFF) by (apply (U_atom E 18 SHADOW_OFF H18); unfold SHADOW_OFF; lia).
assert (US : U E (SAlu ALU_SRL (SOff 20 c) (SLit 3)) = (r + c) / 8).
{ rewrite U_SAlu, U_SLit, U20. cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. apply zcanon_id. unfold M64. change (2 ^ 3) with 8. lia. }
unfold shadow_of_addr, SHADOW_OFF in *. split.
- rewrite U_SAlu, U18, US. cbn [zalu_raw]. rewrite zcanon_id; [lia | unfold M64; lia].
- rewrite U_SAlu, U18, US. cbn [zalu_raw]. rewrite zcanon_id; [lia | unfold M64; lia].
Qed.

Theorem gb_entry_j : forall POST, gb_from B MT POST (GI_J B MT 0) -> gb_from B MT POST EC.
Proof.
intros POST HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
destruct HI as (r & (HPC & HRV & HSV & HROM & HFG & HFC & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & GSV & GSH & HLSH & HFL
  & (S18 & S28 & S70 & S78 & S80) & HINP) & Hk & Hacc & HBLK & HREG & G20 & G10 & G25 & G11 & SCUR).
pose proof HB as (HPRE & Hp & Hn & Hpn & HIN & Hfr0 & Hev & Hlive & HRO & Hsp1 & HE0 & HE02 & HE032 & HMOK & HTR & HNEED).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (eb_sp cx HB) as (Hs16 & Hslo' & Hshi' & Hs1 & Hs132).
pose proof (eb_F cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ HFR) as (EF & EFL & HF0 & HFc & HFia & HF64 & HSHeq & HFp & HFs).
pose proof HJ as (HAR3 & _).
assert (HM : eb_mach GE_C ms3) by (repeat split; assumption).
destruct HREG as (Hrin & Hlen & Hbytes).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 Hrin) as (Hr16 & Hr4096 & Hrce & Hrapp & _).
change (req_size REG_SIZE) with 288 in Hrce, Hrapp.
pose proof (BoxregInit.init_bytes_inv (LLVMFuzzerTestOneInput_entry.en_sx (eb_b (c_pl cx)))) as (HINV & _ & HFAB).
fold (eb_fab (c_pl cx)) in HINV, HFAB. fold (eb_bs (c_pl cx)) in HINV, HFAB.
pose proof (BoxregInit.clamp40_range (LLVMFuzzerTestOneInput_entry.en_sx (eb_b (c_pl cx)))) as Hfr.
fold (eb_fab (c_pl cx)) in Hfr.
(* 0x801a4: jal check (r, fabric) *)
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr (ms_regs ms3) r0)
  by (intros n r0 Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (HS : st_ok_pi SEGS VAL E (mkSS GE_C sr_atoms [] None (mkFacts [] [] [])) (restrict (w_H W3) ms3)).
{ rewrite (eb_ms GE_C (w_H W3) ms3 HM). apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS Bxe [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HE.
paj_run_tok RUN HS HJ SHOK Bspan0; [apply awr_ok_nil |].
lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into ms1 end.
lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (eb_frame_nil _ _ _ _ HFx) as M1 end.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
assert (GSV1 : gsaved cx W3 ms1) by (apply (eb_gsaved_tr cx W3 W3 ms3 ms1); [intros a Ha; apply M1; lia | exact GSV]).
assert (Qsp : spZ (ms_regs ms1) = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)))
  by (unfold spZ at 1; rewrite Q2, (EE 2%nat 2%bv eq_refl), G2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (HRO1 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms1)))
  by exact (eb_arodata _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO).
assert (Hbytes1 : forall i, 0 <= i < REG_SIZE -> aview SEGS (w_H W3) (ms_mem ms1) (r + i) =
  Some (bv_unsigned (nth (Z.to_nat i) (eb_bs (c_pl cx)) (Z_to_bv 8 0))))
  by (intros i Hi; rewrite M1 by (unfold REG_SIZE in Hi; lia); exact (Hbytes i Hi)).
rewrite (pa_sigma_check (PI := PI)).
eapply SRr_bind.
{ eapply (cl_callS B LAWS W3 (ms_regs ms1) (ms_mem ms1) _ GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k CHECK_STK [] 0
    (c_sp1 cx - spZ (c_regs cx)) (getr (ms_regs ms1) 1) (gch cx)
    (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ W2 = W3 /\
       Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) /\
       (forall i, 0 <= i < REG_SIZE -> aview SEGS (w_H W2) mem2 (r + i) =
          Some (bv_unsigned (nth (Z.to_nat i) (eb_bs (c_pl cx)) (Z_to_bv 8 0))))) HJ Qsp).
  - apply eb_mod16; [exact Hs132 | exact Hs16].
  - lia.
  - unfold CHECK_STK, ESTACK. lia.
  - unfold CHECK_STK, ESTACK, GB_STK. lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl), G3. exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl), G4. exact Htp.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
    unfold s0Z at 1. rewrite Q8, (EE 8%nat 8%bv eq_refl), G8. unfold w64. rewrite unsigned_lit_small by lia.
    exact (eb_achain_ly cx ly3 S3 W3 (ms_mem ms1) _ [(GB_CID, fp)] k (c_sp1 cx) HB HJ (proj1 GSV1)
      (eb_gsaved_s0 cx W3 ms1 GSV1) ltac:(lia)).
  - intros HPRE1.
    exact (TCHECK ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ (gch cx) r (eb_fab (c_pl cx)) (eb_bs (c_pl cx)) BX_G HPRE1 HRO1
      ltac:(rewrite Q10, (EE 10%nat 10%bv eq_refl); exact G10) ltac:(rewrite Q11, (EE 11%nat 11%bv eq_refl); exact G11)
      Hrin Hbytes1 (proj1 HINV) HFAB HISV HGLOB HZB ltac:(left; reflexivity) HZ1 HZ2 HMCH).
  - intros a (rg & [] & _). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (-> & -> & -> & _ & Hbytes2)).
rewrite Z.add_0_r in HJ2.
assert (KP3 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs2 r0 = getr (ms_regs ms1) r0).
{ intros r0 Hr0. pose proof (HP2 (bv_unsigned r0) Hr0) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
assert (R2 : getr regs2 2 = w64 (c_sp1 cx)) by (rewrite (KP3 2%bv ltac:(change (bv_unsigned (2%bv : bv 5)) with 2; unfold acallee_saved; lia)), Q2, (EE 2%nat 2%bv eq_refl); exact G2).
assert (R3 : getr regs2 3 = getr (c_regs cx) 3) by (rewrite (KP3 3%bv ltac:(change (bv_unsigned (3%bv : bv 5)) with 3; unfold acallee_saved; lia)), Q3, (EE 3%nat 3%bv eq_refl); exact G3).
assert (R4 : getr regs2 4 = getr (c_regs cx) 4) by (rewrite (KP3 4%bv ltac:(change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; lia)), Q4, (EE 4%nat 4%bv eq_refl); exact G4).
assert (R8 : getr regs2 8 = w64 (spZ (c_regs cx))) by (rewrite (KP3 8%bv ltac:(change (bv_unsigned (8%bv : bv 5)) with 8; unfold acallee_saved; lia)), Q8, (EE 8%nat 8%bv eq_refl); exact G8).
assert (R9 : getr regs2 9 = w64 (c_sp1 cx)) by (rewrite (KP3 9%bv ltac:(change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; lia)), Q9, (EE 9%nat 9%bv eq_refl); exact G9).
assert (R18 : getr regs2 18 = w64 SHADOW_OFF) by (rewrite (KP3 18%bv ltac:(change (bv_unsigned (18%bv : bv 5)) with 18; unfold acallee_saved; lia)), Q18, (EE 18%nat 18%bv eq_refl); exact G18).
assert (R20 : getr regs2 20 = w64 r) by (rewrite (KP3 20%bv ltac:(change (bv_unsigned (20%bv : bv 5)) with 20; unfold acallee_saved; lia)), Q20, (EE 20%nat 20%bv eq_refl); exact G20).
assert (R24 : getr regs2 24 = w64 (gSH cx fp)) by (rewrite (KP3 24%bv ltac:(change (bv_unsigned (24%bv : bv 5)) with 24; unfold acallee_saved; lia)), Q24, (EE 24%nat 24%bv eq_refl); exact G24).
assert (R25 : getr regs2 25 = w64 (eb_fab (c_pl cx))) by (rewrite (KP3 25%bv ltac:(change (bv_unsigned (25%bv : bv 5)) with 25; unfold acallee_saved; lia)), Q25, (EE 25%nat 25%bv eq_refl); exact G25).
clear KP3 HP2.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K1c & _ & _ & K4c & _).
assert (MK3 : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite K1c by (unfold CHECK_STK, ESTACK in *; lia). apply M1; lia. }
pose proof (Z.mul_div_le (gF cx fp) 8 ltac:(lia)) as D8.
assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
assert (MF3 : forall a, (gF cx fp <= a < gF cx fp + 512 \/ gSH cx fp <= a < gSH cx fp + 64) ->
  aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha.
  rewrite (K4c GB_CID fp a ltac:(rewrite HFR; left; reflexivity)).
  - apply M1. rewrite HSHeq in Ha. unfold SHADOW_OFF in Ha. lia.
  - destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF.
    + change (fs_frame_bytes GB_CID) with 512. lia.
    + unfold shadow_addr. change (fs_frame_bytes GB_CID / 8) with 64. rewrite HSHeq in Ha. lia.
  - intros (rg & [] & _). }
assert (SL : forall off v, 0 <= off <= 0x90 -> gslot cx W3 ms3 off v ->
  rdword (aview SEGS (w_H W3) mem2) (c_sp1 cx + off) = Some v).
{ intros off v Ho Hs. unfold gslot in Hs. rewrite <- Hs. apply rdword_ext. intros i Hi. apply MK3. lia. }
destruct SCUR as (Hpos & S88 & S90).
assert (Hpr : 0 <= c_p cx /\ c_p cx + c_n cx < 2 ^ 47).
{ destruct Hpn as [(Hn0 & ->) | (Hn0 & Hin0)]; [unfold GB_EMPTY; lia|].
  pose proof HB as ((HAR0 & _) & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin0) as (_ & H4096 & Hce & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. lia. }
assert (Hnr : 0 <= c_n cx < 2 ^ 26) by (destruct Hpn as [(H0 & _) | (H0 & _)]; lia).
remember (Eimg (Ereg regs2 [Z_to_bv 64 SBe; Z_to_bv 64 (gF cx fp); Z_to_bv 64 (c_p cx + eb_pos cx);
  Z_to_bv 64 (c_n cx - eb_pos cx)])) as E3 eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; apply Eimg_env).
assert (EE3 : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E3 n = getr regs2 r0)
  by (intros n r0 Hn0; subst E3; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (F32 : ew E3 32 = Z_to_bv 64 SBe) by (subst E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (F33 : ew E3 33 = w64 (gF cx fp)) by (subst E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (F34 : ew E3 34 = w64 (c_p cx + eb_pos cx)) by (subst E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (F35 : ew E3 35 = w64 (c_n cx - eb_pos cx)) by (subst E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
assert (U9 : bv_unsigned (ew E3 9) = c_sp1 cx) by (rewrite (EE3 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E3 18) = SHADOW_OFF) by (rewrite (EE3 18%nat 18%bv eq_refl), R18; reflexivity).
assert (U20 : bv_unsigned (ew E3 20) = r) by (rewrite (EE3 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (SPC : forall off (n : nat) c0 v, ew E3 n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c0 < 2 ^ 64 ->
  rdword (aview SEGS (w_H W3) mem2) (c_sp1 cx + off) = Some (v + c0) ->
  YP09.chunk_ok SEGS E3 (mrestrict (w_H W3) mem2) (c_sp1 cx) (YP09.mkChunk off (CVal 8 (SOff n c0)))).
{ intros off n c0 v Hn0 Hv Hvc Hrd.
  apply (chunk_ok_val SEGS E3 _ (c_sp1 cx) off 8 (SOff n c0) (v + c0)); [| zside | zside |].
  - rewrite denot_lit_U. f_equal. exact (U_atom_off E3 n v c0 Hn0 Hv Hvc).
  - exact (val_mem_of_rdword SEGS (w_H W3) mem2 _ _ Hrd). }
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
assert (HS3 : st_ok_pi SEGS VAL E3 ss_e4 (restrict (w_H W3) (mkst regs2 (getr (ms_regs ms1) 1) mem2 (seg_rom SEGS)))).
{ rewrite Q1, restrict_mkst_fx. unfold ss_e4. apply pa_entry_st_ok_full.
  - subst E3. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold R4_sp, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split.
    + intros o Ho. apply (apresent_writable SEGS). apply HJpres2. unfold GB_STK; lia.
    + repeat apply Forall_cons; try apply Forall_nil.
      * apply (SPC 0x18 33%nat 0 (gF cx fp) F33); [lia | lia | rewrite Z.add_0_r; apply SL; [lia | exact S18]].
      * apply (SPC 0x28 33%nat 0 (gF cx fp) F33); [lia | lia | rewrite Z.add_0_r; apply SL; [lia | exact S28]].
      * apply (SPC 0x70 33%nat 32 (gF cx fp) F33); [lia | lia | apply SL; [lia | exact S70]].
      * apply (SPC 0x78 33%nat 64 (gF cx fp) F33); [lia | lia | apply SL; [lia | exact S78]].
      * apply (SPC 0x80 33%nat 0 (gF cx fp) F33); [lia | lia | rewrite Z.add_0_r; apply SL; [lia | exact S80]].
      * apply (SPC 0x88 34%nat 0 (c_p cx + eb_pos cx) F34); [lia | lia | rewrite Z.add_0_r; apply SL; [lia | exact S88]].
      * apply (SPC 0x90 35%nat 0 (c_n cx - eb_pos cx) F35); [lia | lia | rewrite Z.add_0_r; apply SL; [lia | exact S90]].
  - apply pairwise_disjoint_of_extents. cbn. repeat split.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U18, U20, F32, unsigned_lit_small by (unfold SBe; lia).
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite Z.pow_0_r, !Z.mod_1_r. unfold SBe, SHADOW_OFF.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK3 : sh_ok SEGS Bxe [] E3 (mrestrict (w_H W3) mem2)) by constructor.
assert (AWR3 : forall rs, map eb_wsk rs = map eb_wsk [R4_sp] ->
  awr_ok E3 rs GB_STK (spZ (c_regs cx)) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(GB_CID, fp)]).
{ intros rs Hm. apply (eb_awr_skel E3 [R4_sp] rs _ _ _ _ _ _ _ Hm).
  unfold R4_sp.
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
    [reflexivity | rewrite U9; lia | cbn; unfold GB_STK; lia | cbn; lia |].
  apply awr_ok_nil. }
assert (KP0 : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E3 (ss_mem ss_e4) a ->
  aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem2 a) by reflexivity.
clear HE3.
paj_run_to_tok RUNTO HS3 HJ2 SHOK3 Bspan0 GP_J; [apply AWR3; vm_compute; reflexivity |].
e2_keep KP0.
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => rename msx into ms5; rename HSx into HS5 end.
assert (OUT5 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx <= a < c_sp1 cx + 0x98) ->
  aview SEGS (w_H W3) (ms_mem ms5) a = aview SEGS (w_H W3) mem2 a).
{ intros a Ha Hna. apply KP0; [exact Ha|]. intros (rr & Hr & Hbb). unfold ss_e4, R4_sp in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hbb. rewrite U9 in Hbb. lia. }
lazymatch type of HS5 with st_ok_pi _ _ _ ?ssF _ =>
  let r0 := eval vm_compute in (nth_error (ss_mem ssF) 0) in
  lazymatch r0 with Some ?rr0 => pose proof (st_ok_pi_region_nth E3 ssF _ 0 rr0 HS5 eq_refl) as HR0 end end.
cbn [restrict ms_mem] in HR0.
apply (HNEXT cx fp k acc ly3 S3 W3 ms5 _ HB HJ2 HFR HMO).
exists r, (eb_bs (c_pl cx)), (eb_pos cx).
pose proof (eb_mach_of E3 _ (w_H W3) ms5 HS5 eq_refl) as (HP5 & HV5 & HC5 & HO5 & HF5 & HX5). cbn [ss_pc] in HP5.
prreg HS5 (2%bv : bv 5) T2. prreg HS5 (3%bv : bv 5) T3. prreg HS5 (4%bv : bv 5) T4. prreg HS5 (8%bv : bv 5) T8.
prreg HS5 (9%bv : bv 5) T9. prreg HS5 (18%bv : bv 5) T18. prreg HS5 (20%bv : bv 5) T20. prreg HS5 (21%bv : bv 5) T21.
prreg HS5 (24%bv : bv 5) T24. prreg HS5 (25%bv : bv 5) T25.
assert (F20 : ew E3 20 = w64 r) by (rewrite (EE3 20%nat 20%bv eq_refl); exact R20).
assert (F18 : ew E3 18 = w64 SHADOW_OFF) by (rewrite (EE3 18%nat 18%bv eq_refl); exact R18).
assert (F25 : ew E3 25 = w64 (eb_fab (c_pl cx))) by (rewrite (EE3 25%nat 25%bv eq_refl); exact R25).
pose proof (eb_shadow_U E3 r 8 F20 F18 ltac:(lia) ltac:(lia) ltac:(lia)) as (SH8 & _).
pose proof (eb_shadow_U E3 r 280 F20 F18 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & SH280).
split.
{ unfold gb_body.
  split; [exact HP5|]. split; [exact HV5|]. split; [exact HC5|]. split; [exact HO5|]. split; [exact HF5|].
  split; [exact HX5|].
  split.
  { unfold gregs.
    split; [rewrite T2, (EE3 2%nat 2%bv eq_refl); exact R2|].
    split; [rewrite T8, (EE3 8%nat 8%bv eq_refl); exact R8|].
    split; [rewrite T9, (EE3 9%nat 9%bv eq_refl); exact R9|].
    split; [rewrite T3, (EE3 3%nat 3%bv eq_refl); exact R3|].
    split; [rewrite T4, (EE3 4%nat 4%bv eq_refl); exact R4|].
    split; [rewrite T18, (EE3 18%nat 18%bv eq_refl); exact R18|].
    rewrite T24, (EE3 24%nat 24%bv eq_refl); exact R24. }
  split.
  { apply (eb_gsaved_tr cx W3 W3 ms3 ms5); [|exact GSV].
    intros a Ha. rewrite OUT5 by lia. apply MK3. lia. }
  split.
  { intros i Hi. change (length GSH_J) with 52%nat in Hi. rewrite OUT5, MF3.
    - exact (GSH i ltac:(change (length GSH_J) with 52%nat; lia)).
    - right. rewrite HSHeq. unfold SHADOW_OFF. lia.
    - rewrite HSHeq. unfold SHADOW_OFF. lia.
    - rewrite HSHeq. unfold SHADOW_OFF. lia. }
  split; [exact HLSH|].
  split.
  { rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3))); [exact HFL|].
    intros i Hi. change (fs_frame_bytes GB_CID) with 512. rewrite OUT5, MF3; [reflexivity | left | |]; lia. }
  split.
  { unfold gslots_fr, GO_MAC, GO_PREV.
    split; [apply (eb_slot_U cx W3 ms5 E3 _ _ _ _ _ 0x18 (SOff 33 0) _ HR0 U9); [inch | apply (U_atom E3 33 _ F33); lia]|].
    split; [apply (eb_slot_U cx W3 ms5 E3 _ _ _ _ _ 0x28 (SOff 33 0) _ HR0 U9); [inch | apply (U_atom E3 33 _ F33); lia]|].
    split; [apply (eb_slot_U cx W3 ms5 E3 _ _ _ _ _ 0x70 (SOff 33 32) _ HR0 U9); [inch | apply (U_atom_off E3 33 _ 32 F33); lia]|].
    split; [apply (eb_slot_U cx W3 ms5 E3 _ _ _ _ _ 0x78 (SOff 33 64) _ HR0 U9); [inch | apply (U_atom_off E3 33 _ 64 F33); lia]|].
    apply (eb_slot_U cx W3 ms5 E3 _ _ _ _ _ 0x80 (SOff 33 0) _ HR0 U9); [inch | apply (U_atom E3 33 _ F33); lia]. }
  apply (eb_input cx _ ly3 S3 W3 (ms_mem ms5) _ k HB HJ2).
  intros p0 n0 Hp0. unfold gblk1 in HBLK. rewrite HBLK. apply in_or_app. left. exact Hp0. }
split; [lia|]. split; [lia|]. split; [unfold GB_A; lia|].
split; [exact HBLK|].
split.
{ split; [exact Hrin|]. split; [unfold eb_bs; apply BoxregInit.init_bytes_length|].
  intros i Hi. rewrite OUT5 by (unfold REG_SIZE in Hi; lia). exact (Hbytes2 i Hi). }
split; [exact HINV|].
split; [rewrite T20; exact F20|].
split; [rewrite T21; reflexivity|].
split; [rewrite T25, F25, HFAB; reflexivity|].
split.
{ unfold gslots_r, GO_PREV. rewrite HFAB.
  split; [apply (eb_slot_U cx W3 ms5 E3 _ _ _ _ _ 0x10 (SLit 3) _ HR0 U9); [inch | rewrite U_SLit; reflexivity]|].
  split; [apply (eb_slot_U cx W3 ms5 E3 _ _ _ _ _ 0x20 (SOff 33 76) _ HR0 U9);
          [inch | rewrite (U_atom_off E3 33 (gF cx fp) 76 F33) by lia; lia]|].
  split; [apply (eb_slot_U cx W3 ms5 E3 _ _ _ _ _ 0x38 _ _ HR0 U9 ltac:(inch) SH8)|].
  split; [apply (eb_slot_U cx W3 ms5 E3 _ _ _ _ _ 0x40 (SOff 20 280) _ HR0 U9); [inch | apply (U_atom_off E3 20 _ 280 F20); lia]|].
  split; [apply (eb_slot_U cx W3 ms5 E3 _ _ _ _ _ 0x50 (SOff 25 0) _ HR0 U9); [inch | apply (U_atom E3 25 _ F25); lia]|].
  apply (eb_slot_U cx W3 ms5 E3 _ _ _ _ _ 0x60 _ _ HR0 U9 ltac:(inch) SH280). }
unfold gcursor. split; [exact Hpos|].
split; [apply (eb_slot_U cx W3 ms5 E3 _ _ _ _ _ 0x88 (SOff 34 0) _ HR0 U9); [inch | apply (U_atom E3 34 _ F34); lia]|].
apply (eb_slot_U cx W3 ms5 E3 _ _ _ _ _ 0x90 (SOff 35 0) _ HR0 U9); [inch | apply (U_atom E3 35 _ F35); lia].
Qed.

(* ---- the phase: 0x7ff4c .. 0x801ec ---- *)
Theorem gb_entry : forall POST, gb_from B MT POST (GI_J B MT 0) -> gb_start B MT POST.
Proof.
intros POST H. exact (gb_entry_a POST (gb_entry_m POST (gb_entry_i POST (gb_entry_c POST (gb_entry_j POST H))))).
Qed.
End c.
End b.
End a.
