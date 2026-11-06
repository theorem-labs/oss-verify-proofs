(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (G-BRA, B top_x row 21 RA_x): image B's relay_add (fuzz_reply.asan-ubsan
   0x82af4 .. 0x82ca0) over a generic allocator relation ARx in the ROOM form.

   pb_relay_add_x : ra_spec_x B PST ARx MT RP G RG CTX A_relay_addP (lib/B/W_contract_x.v Section w5) is ra_all_x
   (lib/B/W_relay_add_cut_x.v) over the four segments: ENT (W_relay_add_ent_x.v pb_rb_ent_x), HELD
   (W_relay_add_held_x.v pb_rb_held_x: the realloc under the room rule), APP (W_relay_add_app_x.v pb_rb_app_x) and TAIL
   (W_relay_add_tail_x.v pb_rb_tail_x: unlock, wake's wk_spec_x with its seat fact, the epilogue).  Its Section
   hypotheses are the union of the segments'.  The B top's instance is lib/B/W_relay_add_fr_x.v fr_relay_add_x. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal W_sites W_rep W_img W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_kit_x W_sites_x W_frame_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_wake_c W_wake_c_x W_relay_add_cut W_relay_add_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_relay_add_ent_x W_relay_add_held_x W_relay_add_app_x W_relay_add_tail_x.
(* route R: SRrG / wle' (YA0nH) and relay_add's contract at R (W_contract_srlf_xR.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_srlf_xR.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable RG : rep_globals.
Variable CTX : list (list Z).
Context {hl : Z}.
(* the generic relation's laws (ENT, HELD, APP, TAIL), its empty head set (APP: the table block's shadow) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
(* relay_add's globals: owned by no allocator, writable, off .rodata; g_wake[1] an image byte nobody owns, not errno *)
Hypothesis HG : gx_ok SEGS B (RA_G RG).
Hypothesis HWK : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HNROM : forall a, inG (RA_G RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (RA_G RG).
(* wake's fake frame costs nothing (TAIL): a set_fs costs nothing (KF-COUNT #4's text) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* placement (W_relay_add_cut.v Section fr decides them at the pin) *)
Hypothesis HV3 : VAL (A_OBJ 3) = rg_lock RG.
Hypothesis HV4 : VAL (A_OBJ 4) = rg_nsrc RG.
Hypothesis HV5 : VAL (A_OBJ 5) = rg_src RG.
Hypothesis HV13 : VAL (A_OBJ 13) = rg_capsrc RG.
Hypothesis HH28 : VAL (A_HI 28) + RA_HI_NSRC = rg_nsrc RG.
Hypothesis HH29 : VAL (A_HI 29) + RA_HI_CAPSRC = rg_capsrc RG.
Hypothesis HH30 : VAL (A_HI 30) + RA_HI_SRC = rg_src RG.
Hypothesis HRGA : ra_aligned RG.
Hypothesis HRGP : ra_apart (ra_cells RG).
Hypothesis HMMAX : ATABLE < MMAX.
(* no image byte is a program static the journal exempts (HELD, TAIL; trivial at PST = []) *)
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
(* the image cover and the live blocks' sizes (APP) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the callees *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX (SIGMA WS_realloc).
Hypothesis AMEMSET : aintrin_realizes_x SEGS B ARx OSet (SIGMA WS_asan_memset).
Hypothesis WAKE : wk_spec_x B PST ARx RG (BASE + AF_fr_wake).

Theorem pb_relay_add_x : ra_spec_x B PST ARx MT RP G RG CTX A_relay_addP.
Proof.
apply ra_all_x.
- exact (W_relay_add_ent_x.pb_rb_ent_x B PST ARx MT RP G RG CTX LAWS TL MTL HG HWK HNROM HV3 HRGA HRGP ALOCK).
- exact (W_relay_add_held_x.pb_rb_held_x B PST ARx MT RP MMAX G RG CTX LAWS TL MTL HG HWK HNROM HROMO
    HV4 HV5 HV13 HH28 HH29 HH30 HRGP HMMAX AREALLOC HPST).
- exact (W_relay_add_app_x.pb_rb_app_x B PST ARx MT RP G RG CTX LAWS TL HG HWK HNROM HV4 HV5 HH28 HH30 HRGP AMEMSET
    HP0 IMGC BLKN).
- exact (W_relay_add_tail_x.pb_rb_tail_x B PST ARx MT RP G RG CTX LAWS TL MTL HG HWK HNROM MO_FR HV3 HRGA HRGP
    AUNLOCK WAKE HPST).
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): relay_add at a world relation R, ra_all_xR (W_relay_add_cut_x.v Section cR) over
   the four segments' R forms (each segment file's Section cR).  The realloc (HELD) takes its R rule with RO
   from ARx and the hull admission from the meter (HA_ra; at the top HAD := cf_hull_adm, and the top
   discharges HA_ra from the meter); the strict pb_relay_add_x above is unchanged. *)
Section cR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Variable HAD : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis HA_ra : forall lyc Sc regsT ch p n, 1 <= n -> mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HAD lyc Sc regsT ch p n.
Hypothesis AREALLOC_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HAD CTX R (SIGMA WS_realloc).
Theorem pb_relay_add_xR : ra_spec_xR B PST ARx R MT RP G RG CTX A_relay_addP.
Proof.
apply ra_all_xR.
- eapply W_relay_add_ent_x.pb_rb_ent_xR; eassumption.
- eapply W_relay_add_held_x.pb_rb_held_xR with (R := R) (RO := RO) (HAD := HAD); eassumption.
- eapply W_relay_add_app_x.pb_rb_app_xR; eassumption.
- eapply W_relay_add_tail_x.pb_rb_tail_xR; eassumption.
Qed.
End cR.
End c.
End b.
End a.
