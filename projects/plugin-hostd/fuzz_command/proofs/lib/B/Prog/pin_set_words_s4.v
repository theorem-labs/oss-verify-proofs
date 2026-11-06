(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: chain_words' walk on the ASan build of plugin-hostd/fuzz_command, segment S1
   (chain_words_d.v cw_S1P): from the entry (0x8dfd4) through __asan_stack_malloc_3 (0x8e044) to the refusal cut KR
   (0x8e278) or the first-check cut KC (0x8e1ec). In the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v (entry,
   aj_stack_malloc_atS, re-seat) with the entry seed of lib/A/Prog/numberE.v: a run to the call, the call, a re-seat
   that keeps the three stack regions and adds the frame (the call's a0) and its shadow (the alias of
   (s8 >> 3) + s7), a plain run through the 88 shadow stores to the branch on ntok < 3, and the cut facts (cw_pc)
   read back from the symbolic state at the cut. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_s1.v, with its module paths and module names changed; 430 of its 477 lines of code are new or changed and 519 lines of the source are left out. *)
(* The segment interface of the walk of pin_set_words on the ASan+UBSan build of plugin-hostd/fuzz_command (image B,
   fuzz_command.asan-ubsan, entry 0x8e17c), on the B statement lib/B/Prog/pin_set_words_c.v (a working branch
   357b1f0783f: apost_baseF post, rounding-mode-0 pre, per-event meter), in the form of a Theorem Labs lane's A walk
   (lib/A/Prog/pin_set_words_s4.v on a working branch): a context record for the statement's
   binders, its premises as a record, the post, and the cut points stated over the machine state; each segment file
   seeds its own symbolic state.

     H   0x8e17c .. 0x8e228 (MID)   the arity test, strlen(line), tok[3] and the inlined strcmp(tok[3], "-")
     M   0x8e228 .. 0x8e284 (JOIN)  ntok = 4, or ntok = 5 with tok[4] and strncmp(tok[4], "verdict=", 8)
     Ta  0x8e284 .. 0x8e2dc (K2)    tok[1], tok[2] and the call of pins_set
     Tb  0x8e2dc .. ret             rc <> 0, or rc = 0 and lv2_refusals_forget(NULL); the epilogue

   B's code is A's with the roles of s1 and s2 swapped (A: s2 = tok[3], s1 = the result; B: s1 = tok[3], s2 = the
   result) and nine UBSan checks, each branching to the `unimp` at 0x8e310 (B-PREP.md, pin_set_words section 3):
   0x8e1cc/0x8e1d8 (H), 0x8e234/0x8e240/0x8e27c (M), 0x8e288/0x8e294/0x8e2ac/0x8e2b8 (Ta). The checks on tok
   (tok + 8k wraps, tok + 8k misaligned) are decided by the symbolic run from the atom fact on tok (in
   [4096, 0x7fffff800000], 8-aligned); the check on tok[4] + 8 (0x8e27c) from tok[4]'s block (atoks_atA).

   At MID and JOIN the layout, the allocator state and the world are the entry's (the strlen and strncmp entries
   keep them, PaArt.v aj_art_at) and the memory outside the stack window is the entry's (kept_out). At K2 the
   journal has gone through pins_set and pins_set's post holds. pins_set reaches the printf wrappers, so it returns
   at an FP state fx1 related to the entry's by apost_baseF's two FP clauses (the kit's fxrel, lib/B/Prog/PaFx.v;
   the call through PaFx.v's cl_callS_pgF): the walk from K2 on is proved at the ambient FP state (from_K2) and
   applied at fx1; psw_post_lift takes its post back to the entry's.

   A later part seeds its symbolic state by psw_seedJ: the registers at the cut point are the atoms 0..31 (sp = the
   entry sp - 48, s0 = tok, s4 = the shadow base), the frame [sp, sp + 48) is one READ-ONLY region that holds the six
   words the prologue saved (atoms 32..37: the entry's ra, s0, s1, s2, s3, s4), and atoms 38..40 are tok[1], tok[2],
   tok[4] (psw_add_tok adds their one-chunk regions over s0). No part after H writes memory itself, so a run there
   keeps every byte (psw_frame_same). psw_leaf_post closes a path at the `ret`.

   Per-binary facts used here: HB (the record, lib/B/YF0m.v; CmdRecBase.v's cmd_aread_ok_chk then gives the shadow
   of the literal "verdict=" at 0x22900, CmdRecImg.v's cmd_heap_tail_vis a heap word's tail) and MTL (the meter
   laws). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain PaCallPg PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pin_set_words_s1 pin_set_words_s2 pin_set_words_s3.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pins_set_c lv2_refusals_forget_c pin_set_words_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the cut points (B listing offsets; entry BASE + AF_pin_set_words = 0x8e17c) *)
Definition PSW_MID : Z := AF_pin_set_words + 0xac.    (* 0x8e228  li a0,5 : the ntok = 5 test *)
Definition PSW_JOIN : Z := AF_pin_set_words + 0x108.  (* 0x8e284  li a0,-9 : both verdict arms join *)
Definition PSW_K2 : Z := AF_pin_set_words + 0x160.    (* 0x8e2dc  mv s2,a0 : pins_set has returned *)

(* the symbolic state a later part starts from *)
Definition psw_frameJ : YP09.region := YP09.mkRegion (Some 2%nat) 0 48 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 37 0)); YP09.mkChunk 8 (CVal 8 (SOff 36 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
 YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0)); YP09.mkChunk 40 (CVal 8 (SOff 32 0))].
Definition psw_factsJ : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 4096 0x7fffff800000 3); (20%nat, mkAF SB SB 0)] [] [].
Definition ss_pswJ (pc : Z) : sstate := mkSS pc sr_atoms [psw_frameJ] None psw_factsJ.
Definition psw_extraJ (regs : bvmap 5 word) (p1 p2 p4 : Z) : list word :=
[getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; Z_to_bv 64 p1; Z_to_bv 64 p2; Z_to_bv 64 p4].
(* the shadow base atom of a later part, its span, and a token-array word as a one-chunk read-only region over s0 *)
Definition BxJ : sv := SOff 20 0.
Definition RBspanJ : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition psw_tokJ (i : Z) (atom : nat) : YP09.region :=
YP09.mkRegion (Some 8%nat) (8 * i) (8 * i + 8) (8 * i) (8 * i) [YP09.mkChunk (8 * i) (CVal 8 (SOff atom 0))].
(* the callee-saved registers and ra after the epilogue of a later part *)
Definition psw_leaf_sv : list (Z * sv) :=
[(1, SOff 32 0); (2, SOff 2 48); (3, SOff 3 0); (4, SOff 4 0); (8, SOff 33 0); (9, SOff 34 0); (18, SOff 35 0);
 (19, SOff 36 0); (20, SOff 37 0); (21, SOff 21 0); (22, SOff 22 0); (23, SOff 23 0); (24, SOff 24 0);
 (25, SOff 25 0); (26, SOff 26 0); (27, SOff 27 0)].
(* a symbolic memory none of whose regions is writable *)
Definition psw_ro_regions (rs : smem) : bool := forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs.

(* a byte of a block's footprint lies in one of the blocks *)
Lemma psw_inFP_blocks : forall (O : list (Z * Z)) a, inFP (ablocks_fp O) a ->
  exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a (r & Hr & Ha). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & Heq & Hin).
subst r. cbn [fst snd] in Ha. exists p, n. split; [exact Hin | exact Ha].
Qed.
Lemma psw_denot_SOff : forall E n k, sv_denot E (SOff n k) = Z_to_bv 64 (bv_unsigned (ew E n) + k).
Proof. reflexivity. Qed.

Ltac psw_in := cbn [psw_leaf_sv In]; repeat (first [left; reflexivity | right]).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition EJ (regs1 regs : bvmap 5 word) (p1 p2 p4 : Z) : env :=
Eimg (L := cmd_listing) (PI := PI) (Ereg regs1 (psw_extraJ regs p1 p2 p4)).

(* the six words the prologue saved below the entry sp (sd ra,40(sp) .. sd s4,0(sp) after addi sp,sp,-48) *)
Definition psw_saved (regs : bvmap 5 word) (rd : reader) : Prop :=
aval_mem rd (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) /\
aval_mem rd (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
aval_mem rd (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
aval_mem rd (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
aval_mem rd (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
aval_mem rd (spZ regs - 48) 8 (bv_unsigned (getr regs 20)).

(* the statement's binders *)
Record pswx : Type := mkPSWX {
  x_ly : alayout; x_S : astate; x_W : world SEGS; x_regs : bvmap 5 word; x_mem : word -> option byte; x_md : Model;
  x_ch : list (Z * Z * Z); x_line : Z; x_nl : Z; x_tok : Z; x_ntok : Z; x_cb : Z; x_ncb : Z; x_T : list byte;
  x_ptrs : list Z; x_tks : list (list byte); x_R : rstate; x_O : list (Z * Z) }.
Definition psw_sp0 (c : pswx) : Z := spZ (x_regs c).
Definition psw_FP (c : pswx) : list (Z * Z) := PIN_SET_WORDS_PG ++ ablocks_fp (x_O c).

Lemma psw_val_mem_of_aval : forall H mem a n v,
aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk).
unfold aview, rd_of in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; [|cbn [option_map] in Hv; discriminate].
cbn [option_map] in Hv. injection Hv as Hv.
f_equal.
first [ rewrite <- Hv
| change (YG0f.le_byte v n k) with (YO0f.le_byte v n k); rewrite <- Hv
| change (YO0f.le_byte v n k) with (YG0f.le_byte v n k); rewrite <- Hv ].
symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* a run over a symbolic memory with no writable region changes no byte *)
Lemma psw_frame_same : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> psw_ro_regions rs = true ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hf Hro a Ha. apply (aview_eq_of SEGS). apply Hf.
intros (r & Hin & Hr). unfold psw_ro_regions in Hro. rewrite forallb_forall in Hro.
specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

(* the seed of a later part: the state at a cut point pc *)
Lemma psw_seedJ : forall ly (W : world SEGS) (m : word -> option byte) (regs regs1 : bvmap 5 word) (pc tok p1 p2 p4 : Z),
astk_ok PIN_SET_WORDS_STK ly (spZ regs) ->
psw_saved regs (rdW W m) ->
getr regs1 2 = w64 (spZ regs - 48) -> getr regs1 8 = w64 tok -> getr regs1 20 = w64 SB ->
4096 <= tok < 0x7fffff800000 -> tok mod 8 = 0 ->
0 <= p1 < 2 ^ 64 -> 0 <= p2 < 2 ^ 64 -> 0 <= p4 < 2 ^ 64 ->
st_ok_pi SEGS VAL (EJ regs1 regs p1 p2 p4) (ss_pswJ pc)
(restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))).
Proof.
intros ly W m regs regs1 pc tok p1 p2 p4 Hstk HSV Q2 Q8 Q20 Htok Htok8 R1 R2 R4.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK48 : 48 + 2 * ESTACK <= PIN_SET_WORDS_STK).
{ unfold PIN_SET_WORDS_STK. pose proof (Z.le_max_l (2 * ESTACK) (Z.max PINS_SET_STK LV2_REFUSALS_FORGET_STK)). lia. }
assert (HES : ESTACK = 4096) by reflexivity.
destruct HSV as (S1 & S8 & S9 & S18 & S19 & S20).
set (sp0 := spZ regs) in *.
set (E := EJ regs1 regs p1 p2 p4).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. subst E. unfold EJ. apply ew_Eimg_Ereg_nat. exact Hn. }
assert (ES : forall j, (j < 9)%nat -> ew E (32 + j) = nth j (psw_extraJ regs p1 p2 p4) (Z_to_bv 64 0))
by (intros j Hj; subst E; unfold EJ; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 48).
{ rewrite (EE 2%nat 2%bv eq_refl), Q2. unfold w64. apply unsigned_lit_small. lia. }
assert (Utok : bv_unsigned (ew E 8) = tok) by (rewrite (EE 8%nat 8%bv eq_refl), Q8; unfold w64; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E 20) = SB) by (rewrite (EE 20%nat 20%bv eq_refl), Q20; unfold w64, SB; apply unsigned_lit_small; lia).
assert (CK : forall (j : nat) (r : bv 5) off, (j < 6)%nat ->
  ew E (32 + j) = getr regs r -> aval_mem (rdW W m) (sp0 - 48 + off) 8 (bv_unsigned (getr regs r)) ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) m) (sp0 - 48) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hj Hew Hv. apply (chunk_ok_val SEGS E _ (sp0 - 48) off 8 (SOff (32 + j) 0) (bv_unsigned (getr regs r))).
  - cbn [sv_denot]. rewrite Hew, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia.
  - exact (psw_val_mem_of_aval _ _ _ _ _ Hv). }
rewrite restrict_mkst_fx. unfold ss_pswJ. apply pa_entry_st_ok_full.
- subst E. unfold EJ. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold psw_frameJ. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (CK 5%nat 20%bv); [lia | apply (ES 5%nat ltac:(lia)) |]. replace (sp0 - 48 + 0) with (sp0 - 48) by lia. exact S20.
  + apply (CK 4%nat 19%bv); [lia | apply (ES 4%nat ltac:(lia)) |]. replace (sp0 - 48 + 8) with (sp0 - 40) by lia. exact S19.
  + apply (CK 3%nat 18%bv); [lia | apply (ES 3%nat ltac:(lia)) |]. replace (sp0 - 48 + 16) with (sp0 - 32) by lia. exact S18.
  + apply (CK 2%nat 9%bv); [lia | apply (ES 2%nat ltac:(lia)) |]. replace (sp0 - 48 + 24) with (sp0 - 24) by lia. exact S9.
  + apply (CK 1%nat 8%bv); [lia | apply (ES 1%nat ltac:(lia)) |]. replace (sp0 - 48 + 32) with (sp0 - 16) by lia. exact S8.
  + apply (CK 0%nat 1%bv); [lia | apply (ES 0%nat ltac:(lia)) |]. replace (sp0 - 48 + 40) with (sp0 - 8) by lia. exact S1.
- cbn. tauto.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok psw_factsJ].
  split; [|split; [|split; [|exact I]]]; unfold afact_ok; cbn [af_lo af_hi af_al2];
  rewrite ?Usp, ?Utok, ?USB; change (2 ^ 4) with 16; change (2 ^ 3) with 8; rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  + split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
  + lia.
  + unfold SB. lia.
Qed.

(* one more token-array word as a read-only region over s0 *)
Lemma psw_add_tok : forall E ss ms (i : Z) (atom : nat) tok v,
st_ok_pi SEGS VAL E ss ms -> region_wf (psw_tokJ i atom) = true ->
bv_unsigned (ew E 8) = tok -> ew E atom = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
0 <= i -> 0 <= tok -> tok + 8 * i + 8 <= 2 ^ 64 ->
val_mem SEGS (ms_mem ms) (tok + 8 * i) 8 v ->
all_disjoint E (psw_tokJ i atom) (ss_mem ss) ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (psw_tokJ i atom :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms i atom tok v HS Hwf Htok Hat Hv Hi Ht Hr Hm Hd.
apply st_ok_pi_add_region; [exact HS | exact Hwf | | exact Hd].
unfold region_ok, psw_tokJ. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Htok. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ tok (8 * i) 8 (SOff atom 0) v); [| lia | lia | exact Hm].
cbn [sv_denot]. rewrite Hat, Z.add_0_r. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* the shadow entry of the load8 checks of a later part: [tok, tok + hi) of the token array, over s0 *)
Lemma psw_shokJ : forall (W : world SEGS) mem (E : env) tok ntok hi,
U E BxJ = SHADOW_OFF -> U E (SOff 8 0) = tok ->
range_addressable (rdW W mem) SHADOW_OFF tok (8 * ntok) -> 0 <= hi <= 8 * ntok ->
in_app tok (8 * ntok) -> 0 <= tok ->
sh_ok SEGS BxJ [mkSHE 8 0 hi] E (mrestrict (w_H W) mem).
Proof.
intros W mem E tok ntok hi HBx HTok Hra Hhi Happ Htok0.
unfold sh_ok. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E BxJ 8%nat tok (8 * ntok) tok 0 hi);
[exact Hra | exact HBx | exact HTok | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF.
unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. destruct (Z.min_spec 0 hi), (Z.max_spec 0 hi); lia.
Qed.

(* ra and the callee-saved registers after the epilogue of a later part *)
Lemma psw_aregs_leaf : forall (regs regs1 : bvmap 5 word) p1 p2 p4 E ss (H : word -> bool) ms,
st_ok_pi SEGS VAL E ss (restrict H ms) -> env_agree 41 (EJ regs1 regs p1 p2 p4) E ->
forallb (fun p => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 (fst p))) (snd p)) psw_leaf_sv = true ->
getr regs1 2 = w64 (spZ regs - 48) -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
(forall r, 21 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) -> 48 <= spZ regs ->
getr (ms_regs ms) 1 = getr regs 1 /\ aregs_preserved regs (ms_regs ms).
Proof.
intros regs regs1 p1 p2 p4 E ss H ms HS [HA _] Hb Q2 Q3 Q4 Qhi Hsp.
assert (G : forall z s, In (z, s) psw_leaf_sv -> getr (ms_regs ms) (Z_to_bv 5 z) = sv_denot E s).
{ intros z s Hin. rewrite (st_ok_pi_restrict_reg H E ss ms _ HS).
  rewrite forallb_forall in Hb. specialize (Hb _ Hin). cbn [fst snd] in Hb. apply sv_eqb_eq in Hb. rewrite Hb. reflexivity. }
assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn Hr. rewrite HA by lia. unfold EJ. apply ew_Eimg_Ereg_nat. exact Hr. }
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (psw_extraJ regs p1 p2 p4) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HA by lia. unfold EJ. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (SV : forall n (w : word), ew E n = w -> sv_denot E (SOff n 0) = w).
{ intros n w Hw. rewrite psw_denot_SOff, Hw, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
(* a literal register name and its Z_to_bv form name the same register *)
assert (LT : forall (b : bv 5) z, bv_unsigned b = z -> Z_to_bv 5 z = b).
{ intros b z Hbz. apply bv_eq. rewrite <- Hbz, Z_to_bv_unsigned. unfold bv_wrap.
  apply Z.mod_small. exact (bv_unsigned_in_range 5 b). }
split.
{ transitivity (getr (ms_regs ms) (Z_to_bv 5 1)); [rewrite (LT 1%bv 1 eq_refl); reflexivity|].
  rewrite (G 1 (SOff 32 0) ltac:(psw_in)). apply SV. exact (EX 0%nat ltac:(lia)). }
intros r Hr. unfold acallee_saved in Hr.
destruct Hr as [->|[->|[->|[->|[->|Hr]]]]];
[| | | | | destruct (Z_lt_le_dec r 21) as [Hlt|Hge];
  [assert (Hc3 : r = 18 \/ r = 19 \/ r = 20) by lia; destruct Hc3 as [->|[->| ->]] |]].
- rewrite (G 2 (SOff 2 48) ltac:(psw_in)), (LT 2%bv 2 eq_refl). rewrite psw_denot_SOff.
  rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl), Q2. unfold w64. rewrite unsigned_lit_small.
  + replace (spZ regs - 48 + 48) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  + pose proof (bv_unsigned_in_range 64 (getr regs 2)) as R. change (bv_modulus 64) with (2 ^ 64) in R. unfold spZ in *. lia.
- rewrite (G 3 (SOff 3 0) ltac:(psw_in)), (LT 3%bv 3 eq_refl). apply SV. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl). exact Q3.
- rewrite (G 4 (SOff 4 0) ltac:(psw_in)), (LT 4%bv 4 eq_refl). apply SV. rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl). exact Q4.
- rewrite (G 8 (SOff 33 0) ltac:(psw_in)), (LT 8%bv 8 eq_refl). apply SV. exact (EX 1%nat ltac:(lia)).
- rewrite (G 9 (SOff 34 0) ltac:(psw_in)), (LT 9%bv 9 eq_refl). apply SV. exact (EX 2%nat ltac:(lia)).
- rewrite (G 18 (SOff 35 0) ltac:(psw_in)), (LT 18%bv 18 eq_refl). apply SV. exact (EX 3%nat ltac:(lia)).
- rewrite (G 19 (SOff 36 0) ltac:(psw_in)), (LT 19%bv 19 eq_refl). apply SV. exact (EX 4%nat ltac:(lia)).
- rewrite (G 20 (SOff 37 0) ltac:(psw_in)), (LT 20%bv 20 eq_refl). apply SV. exact (EX 5%nat ltac:(lia)).
- assert (Hrr : 21 <= r <= 27) by lia.
  assert (Hc : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  assert (Hin : In (r, SOff (Z.to_nat r) 0) psw_leaf_sv).
  { destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]]; psw_in. }
  rewrite (G r _ Hin). apply SV. rewrite (EL (Z.to_nat r) (Z_to_bv 5 r)); [exact (Qhi r Hrr) | lia |].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* tpin_set_words_spec's premises (pin_set_words_c.v:118-143) but the rounding-mode one, over the context; the
   rounding mode (:120) is passed apart, to the segment that calls pins_set, so that the record holds at every FP
   state *)
Record psw_pre (c : pswx) : Prop := mkPswPre {
  pp_afn : afn_pre SEGS B PIN_SET_WORDS_STK (x_ly c) (x_S c) (x_W c) (x_regs c) (x_mem c) (x_md c) (x_ch c);
  pp_rod : arodata_okP SEGS RLO RHI B (rdW (x_W c) (x_mem c));
  pp_a0 : getr (x_regs c) 10 = w64 (x_line c);
  pp_line64 : 0 <= x_line c < 2 ^ 64;
  pp_a1 : getr (x_regs c) 11 = w64 (x_tok c);
  pp_tok64 : 0 <= x_tok c < 2 ^ 64;
  pp_a2 : getr (x_regs c) 12 = w64 (x_ntok c);
  pp_lb : In (x_line c, x_nl c) (ablocks B (x_ly c) (x_S c));
  pp_lO : ~ In (x_line c, x_nl c) (x_O c);
  pp_lT : astr_atR (rdW (x_W c) (x_mem c)) (x_line c) (x_T c);
  pp_lN : Z.of_nat (length (x_T c)) + 1 <= x_nl c;
  pp_tokobj : afobj SEGS B (x_ly c) (x_S c) (x_W c) (x_mem c) (x_tok c) (8 * x_ntok c);
  pp_toks : atoks_atA (rdW (x_W c) (x_mem c)) (x_tok c) (x_ptrs c) (x_tks c) (x_cb c) (x_ncb c);
  pp_cb : In (x_cb c, x_ncb c) (ablocks B (x_ly c) (x_S c));
  pp_cbO : ~ In (x_cb c, x_ncb c) (x_O c);
  pp_ntok : x_ntok c = Z.of_nat (length (x_tks c));
  pp_ntokr : 1 <= x_ntok c <= 64;
  pp_verb : nth_error (x_tks c) 0 = Some Verbs.Lit.verb_pin_set;
  pp_rec : rec_repA B (x_ly c) (x_S c) (rdW (x_W c) (x_mem c)) (x_R c) (x_O c);
  pp_refuse : r_refuse (x_R c) <> 0 -> declared (r_code (x_R c)) = true;
  pp_calls : (length (r_calls (x_R c)) + 2 <= 16)%nat;
  pp_ro : cmd_ro_ok (rdW (x_W c) (x_mem c));
  pp_vobjs : cmd_val_objs;
  pp_frames : Z.of_nat (length (frames (x_S c))) <= 5;
  pp_nev : st_nev (x_S c) + EV_PIN_SET_WORDS (x_R c) (x_T c) (tl (x_tks c)) <= EV_MAX;
  pp_live : blocks_bytes (x_S c) + LIVE_PIN_SET_WORDS <= LIVE_MAX;
  pp_meter : mo_ok MT (x_S c) (XM_PIN_SET_WORDS MT (x_R c) (x_T c) (tl (x_tks c))) }.

(* tpin_set_words_spec's post (pin_set_words_c.v:147-157), verbatim over the context *)
Definition psw_Q (c : pswx) : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 let '(R', r) := VerbsRun.pin_set_run (x_R c) (x_T c) (tl (x_tks c)) in
 exists O' : list (Z * Z),
 getr regs' 10 = w64 r /\ -2 ^ 31 <= r < 2 ^ 31 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn (ablocks B (x_ly c) (x_S c)) -> ~ In pn (x_O c) -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B (x_ly c) (x_S c)) /\ ~ In pn (x_O c)) \/ In pn O') /\
 (forall pn, In pn O' -> In pn (x_O c) \/ ~ In pn (ablocks B (x_ly c) (x_S c))) /\
 blocks_bytes S' <= blocks_bytes (x_S c) + LIVE_PIN_SET_WORDS /\
 mo_le MT (x_S c) S' (XM_PIN_SET_WORDS MT (x_R c) (x_T c) (tl (x_tks c))).
Definition psw_post (c : pswx) : world SEGS -> config -> Prop :=
apost_baseF SEGS B PIN_SET_WORDS_STK (psw_FP c) (x_regs c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
 (EV_PIN_SET_WORDS (x_R c) (x_T c) (tl (x_tks c))) (psw_Q c).

(* the part of the MID and JOIN cuts that both share: the journal from the entry (layout, allocator state and
   world unchanged, no event), the memory outside the stack window unchanged, the saved words, and the registers
   the rest of the walk reads or hands back *)
Record psw_cut (c : pswx) (regs1 : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (p3 : Z) : Prop := mkPswCut {
  ct_j : ajournal SEGS B PIN_SET_WORDS_STK (psw_sp0 c) (psw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [] (x_ly c) (x_S c) (x_W c) memc mdc 0;
  ct_kept : kept_out (rdW (x_W c) (x_mem c)) (rdW (x_W c) memc) (psw_sp0 c - PIN_SET_WORDS_STK) (psw_sp0 c);
  ct_saved : psw_saved (x_regs c) (rdW (x_W c) memc);
  ct_sp : getr regs1 2 = w64 (psw_sp0 c - 48);
  ct_gp : getr regs1 3 = getr (x_regs c) 3;
  ct_tp : getr regs1 4 = getr (x_regs c) 4;
  ct_s0 : getr regs1 8 = w64 (x_tok c);
  ct_s1 : getr regs1 9 = w64 p3;
  ct_s4 : getr regs1 20 = w64 SB;
  ct_hi : forall r, 21 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr (x_regs c) (Z_to_bv 5 r) }.

(* MID (0x8e228): ntok is 4 or 5, strlen(line) <= 4096, tok[3] is not "-"; s2 = -902, s3 = ntok *)
Definition INV_MID (c : pswx) (regs1 : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
exists p3 w3, psw_cut c regs1 memc mdc p3 /\
getr regs1 18 = w64 Verbs.err_invalid_operation /\ getr regs1 19 = w64 (x_ntok c) /\
Z.land (x_ntok c) (-2) = 4 /\
nth_error (x_ptrs c) 3 = Some p3 /\ nth_error (x_tks c) 3 = Some w3 /\
Z.of_nat (length (x_T c)) <= Verbs.line_max /\ Verbs.list_eqb w3 Verbs.Lit.word_layout_unknown = false.

(* JOIN (0x8e284): every check passed; a3 holds the verdict pointer: 0, or tok[4] + 8 when tok[4] starts with
   "verdict=" *)
Definition INV_JOIN (c : pswx) (regs1 : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
exists p1 p2 p3 (u f l : list byte) (v : option (list byte)) vptr,
psw_cut c regs1 memc mdc p3 /\ getr regs1 13 = w64 vptr /\
nth_error (x_ptrs c) 1 = Some p1 /\ nth_error (x_ptrs c) 2 = Some p2 /\ nth_error (x_ptrs c) 3 = Some p3 /\
nth_error (x_tks c) 1 = Some u /\ nth_error (x_tks c) 2 = Some f /\ nth_error (x_tks c) 3 = Some l /\
Verbs.pin_set_words_m (x_T c) (tl (x_tks c)) = Verbs.SPinSet u f l v /\
((v = None /\ vptr = 0) \/
 (exists p4 w4, nth_error (x_ptrs c) 4 = Some p4 /\ nth_error (x_tks c) 4 = Some w4 /\ (8 <= length w4)%nat /\
   v = Some (skipn 8 w4) /\ vptr = p4 + 8)).

(* K2 (0x8e2dc): pins_set has returned rc in a0; the journal from the entry has gone through it, and its post holds
   (pins_set_c.v:128-143) of the state at the call, whose layout, allocator state and blocks are the entry's *)
Definition INV_K2 (c : pswx) (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) (md2 : Model) : Prop :=
exists (u f l : list byte) (v : option (list byte)) (R1 : rstate) (r : Z) (O1 : list (Z * Z)),
ajournal SEGS B PIN_SET_WORDS_STK (psw_sp0 c) (psw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
  [] ly2 S2 W2 mem2 md2 (EV_PINS_SET (x_R c)) /\
psw_saved (x_regs c) (rdW W2 mem2) /\
getr regs2 2 = w64 (psw_sp0 c - 48) /\ getr regs2 3 = getr (x_regs c) 3 /\ getr regs2 4 = getr (x_regs c) 4 /\
getr regs2 8 = w64 (x_tok c) /\ getr regs2 20 = w64 SB /\
(forall r, 21 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr (x_regs c) (Z_to_bv 5 r)) /\
getr regs2 10 = w64 r /\
Verbs.pin_set_words_m (x_T c) (tl (x_tks c)) = Verbs.SPinSet u f l v /\
(length u <= 8192)%nat /\ (length f <= 8192)%nat /\ (length l <= 8192)%nat /\
(forall x, v = Some x -> (length x <= 8192)%nat) /\
pins_set_m (x_R c) (Some u) (Some f) (Some l) v = (R1, r) /\ -2 ^ 31 <= r < 2 ^ 31 /\
rec_repA B ly2 S2 (rdW W2 mem2) R1 O1 /\
(forall pn, In pn O1 -> In pn (x_O c) \/ ~ In pn (ablocks B (x_ly c) (x_S c))) /\
(forall pn, In pn (ablocks B (x_ly c) (x_S c)) -> ~ In pn (x_O c) -> In pn (ablocks B ly2 S2)) /\
(forall pn, In pn (ablocks B ly2 S2) -> (In pn (ablocks B (x_ly c) (x_S c)) /\ ~ In pn (x_O c)) \/ In pn O1) /\
blocks_bytes S2 <= blocks_bytes (x_S c) + LIVE_PINS_SET (x_R c) (Some u) (Some f) (Some l) v /\
mo_le MT (x_S c) S2 (XM_PINS_SET MT (x_R c) (Some u) (Some f) (Some l) v).

(* "from this cut point the walk reaches the post" *)
Definition from_MID (c : pswx) : Prop :=
forall regs1 memc mdc, INV_MID c regs1 memc mdc ->
SRr SEGS (x_W c) (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + PSW_MID)) memc (seg_rom SEGS)) mdc) (psw_post c).
Definition from_JOIN (c : pswx) : Prop :=
forall regs1 memc mdc, INV_JOIN c regs1 memc mdc ->
SRr SEGS (x_W c) (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + PSW_JOIN)) memc (seg_rom SEGS)) mdc) (psw_post c).
(* from K2 at the ambient FP state: Tb proves it in a closed section, the walk applies it at the FP state fx1
   pins_set returns (psw_post_lift at the end of this file) *)
Definition from_K2 (c : pswx) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2, INV_K2 c ly2 S2 W2 regs2 mem2 md2 ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + PSW_K2)) mem2 (seg_rom SEGS)) md2) (psw_post c).

(* the post at the `ret`, from the journal, the registers and the post's own facts, with the ambient FP state as
   apost_baseF's fx' (no printf-reaching call on the path, or the walk is at the FP state the last one returned).
   A path ends with
     eapply (paj_ret_at (L := cmd_listing) (PI := PI) _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
     intros mat'; apply (psw_leaf_post ...)
   and then proves psw_Q at the materialized model (psw_Q does not read the model). *)
Lemma psw_leaf_post : forall c (W' : world SEGS) (regs' : bvmap 5 word) mem' md' ly' S' k,
YK0s.ret_ok (getr (x_regs c) 1) ->
getr regs' 1 = getr (x_regs c) 1 -> aregs_preserved (x_regs c) regs' ->
ajournal SEGS B PIN_SET_WORDS_STK (psw_sp0 c) (psw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
  [] ly' S' W' mem' md' k ->
k <= EV_PIN_SET_WORDS (x_R c) (x_T c) (tl (x_tks c)) ->
forall mat', psw_Q c ly' S' W' regs' mem' (with_vm_backing (m_vm_lazy md') mat' md') ->
psw_post c W' (mkCfg (mkst regs' (v_jalr (getr regs' 1) 0) mem' (seg_rom SEGS)) (with_vm_backing (m_vm_lazy md') mat' md')).
Proof.
intros c W' regs' mem' md' ly' S' k Hra H1 HP HJ Hk mat' HQ.
unfold psw_post, apost_baseF.
exists fx, ly', S', regs', mem', (with_vm_backing (m_vm_lazy md') mat' md').
split; [rewrite H1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [intros k0 _; reflexivity|]. split; [left; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); eapply ajournal_mono_k; [exact HJ | exact Hk]|].
split; [exact HP | exact HQ].
Qed.

(* the read-only image words a Theorem Labs lane's entries read, at a state whose memory is the entry's below the window *)
Lemma psw_rom_kept : forall (W : world SEGS) mem memc lo hi,
arodata_okP SEGS RLO RHI B (rdW W mem) -> kept_out (rdW W mem) (rdW W memc) lo hi -> 0x606000 <= lo ->
rt_rom_view SEGS B W memc.
Proof.
intros W mem memc lo hi HRO HK Hlo a Ha Ho He.
assert (Himg : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
pose proof (pa_img_range a Himg) as Hr.
rewrite (HK a) by lia. apply HRO; [left; exact Ha | exact Ho | exact He].
Qed.

Section mt.
Hypothesis MTL : ameter_laws MT.
(* a refusal's post: the recorder, the blocks and the meter as at the entry, a0 = -902 *)
Lemma psw_Q_reject : forall c (regs' : bvmap 5 word) mem' md',
psw_pre c ->
Verbs.pin_set_words_m (x_T c) (tl (x_tks c)) = Verbs.reject ->
kept_out (rdW (x_W c) (x_mem c)) (rdW (x_W c) mem') (psw_sp0 c - PIN_SET_WORDS_STK) (psw_sp0 c) ->
getr regs' 10 = w64 Verbs.err_invalid_operation ->
psw_Q c (x_ly c) (x_S c) (x_W c) regs' mem' md'.
Proof.
intros c regs' mem' md' HP Hm KEEP H10.
pose proof (pp_afn c HP) as HPRE. pose proof (pp_rec c HP) as HREC.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HEV0 : EV_PIN_SET_WORDS (x_R c) (x_T c) (tl (x_tks c)) = 0) by (unfold EV_PIN_SET_WORDS; rewrite Hm; reflexivity).
unfold psw_Q. rewrite (psw_run_reject (x_R c) (x_T c) (tl (x_tks c)) Hm). exists (x_O c).
split; [exact H10|].
split; [unfold Verbs.err_invalid_operation; lia|].
split.
{ apply (rec_repA_kept B (x_ly c) (x_S c) _ (x_ly c) (x_S c) _ (x_R c) (x_O c) HREC).
  - intros pn Hin. exact (rec_repA_in_blocks B _ _ _ _ _ pn HREC Hin).
  - intros a [Ha | [Ha | Ha]].
    + apply KEEP; unfold psw_sp0, A_G_REC, REC_SIZE in *; lia.
    + apply KEEP; unfold psw_sp0, A_REC_SPILL, SC_SIZE in *; lia.
    + destruct (psw_inFP_blocks (x_O c) a Ha) as (p & n & Hpn & Hr).
      pose proof (rec_repA_in_blocks B (x_ly c) (x_S c) _ (x_R c) (x_O c) (p, n) HREC Hpn) as Hin.
      destruct (al_blocks SEGS B LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hn).
      apply KEEP; unfold psw_sp0 in *; lia. }
split; [intros pn Hpn _; exact Hpn|].
split; [intros pn Hpn;
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) pn (x_O c)) as [Hio|Hio];
  [right; exact Hio | left; split; [exact Hpn | exact Hio]]|].
split; [intros pn Hpn; left; exact Hpn|].
split; [unfold LIVE_PIN_SET_WORDS, PIN_SET_WORDS_MALLOCS, PIN_SET_WORDS_REQ; lia|].
apply (mle_weaken MT (x_S c) (x_S c) 0); [exact MTL | apply (mle_start MT (x_S c) MTL) |].
unfold XM_PIN_SET_WORDS. rewrite HEV0. lia.
Qed.
End mt.

Section rd.
(* the per-binary record (lib/B/YF0m.v), for CmdRecBase.v's cmd_aread_ok_chk and CmdRecImg.v's cmd_heap_tail_vis *)
Hypothesis HB : CmdBSyms B.

(* a string inside a live block, as a Theorem Labs lane's string entries ask it at a call: the entry state's bytes, read at a
   state whose memory is the entry's below the window and that satisfies AR *)
Lemma psw_blk_ready : forall ly S (W : world SEGS) mem memc md stk lo hi (regsT : bvmap 5 word) p s b k,
AR SEGS B ly S W memc md ->
kept_out (rdW W mem) (rdW W memc) lo hi -> alloc_ceiling <= lo -> lo <= spZ regsT - stk -> lo < 2 ^ 64 ->
In (b, k) (ablocks B ly S) -> b <= p -> p + Z.of_nat (length s) + 1 <= b + k ->
astr_atR (rdW W mem) p s ->
0 < p /\ astr_at SEGS W memc p s /\ aread_ok SEGS stk W regsT memc p (astr_len s + 1) /\
atail_vis SEGS W memc (p + astr_len s).
Proof.
intros ly S W mem memc md stk lo hi regsT p s b k HAR HK Hce Hlo Hlo64 Hin Hb He Hs.
destruct (al_blocks SEGS B LAWS ly S W memc md b k HAR Hin) as (_ & Hb4096 & Hbceil & _).
pose proof (psw3_req_ge k) as Hreq.
unfold astr_len.
split; [lia|].
split; [apply astr_atR_view; apply (astr_atR_kept _ _ lo hi p s HK Hs); lia|].
split; [apply (aread_ok_of_block SEGS B LAWS stk ly S W regsT memc md b k p (Z.of_nat (length s) + 1));
  [exact HAR | exact Hin | lia | lia | lia | lia]|].
apply (cmd_heap_tail_vis SEGS B LAWS HB ly S W memc md b k); [exact HAR | exact Hin | lia].
Qed.

Lemma psw_verdict_chk : cmd_addr_b 0x22900 8 = true /\ cmd_hull_b 0x22900 8 = true.
Proof. split; vm_compute; reflexivity. Qed.
Lemma psw_verdict_end : In (0x22900 + 8) cmd_ro_ends.
Proof. apply In_of_existsb. vm_compute. reflexivity. Qed.

(* the literal "verdict=" (.str.28, 0x22900, RO_lit_22900), as the strncmp entry asks it at a call *)
Lemma psw_verdict_ready : forall ly S (W : world SEGS) mem memc md stk lo hi (regsT : bvmap 5 word),
AR SEGS B ly S W memc md -> cmd_ro_ok (rdW W mem) ->
kept_out (rdW W mem) (rdW W memc) lo hi -> 0x606000 <= lo -> lo <= spZ regsT - stk -> lo < 2 ^ 64 ->
0 < 0x22900 /\ astr_at SEGS W memc 0x22900 Verbs.Lit.word_verdict /\
aread_ok SEGS stk W regsT memc 0x22900 (Z.min 8 (astr_len Verbs.Lit.word_verdict + 1)) /\
atail_vis SEGS W memc (0x22900 + astr_len Verbs.Lit.word_verdict).
Proof.
intros ly S W mem memc md stk lo hi regsT HAR HRO HK Hlo Hsp Hlo64.
pose proof (cmd_ro_ok_kept _ _ lo hi HK HRO Hlo Hlo64) as [HBy HT].
unfold cmd_ro_bytes in HBy.
assert (HV : abytes_atR (rdW W memc) 0x22900 RO_lit_22900).
{ repeat match type of HBy with _ /\ _ => let H := fresh "Hb" in destruct HBy as [H HBy] end.
  match goal with H : abytes_atR _ 0x22900 _ |- _ => exact H end. }
rewrite psw_verdict_lit in HV.
assert (HL : astr_len Verbs.Lit.word_verdict = 8) by reflexivity.
rewrite HL. change (Z.min 8 (8 + 1)) with 8.
destruct psw_verdict_chk as [C1 C2].
destruct (cmd_aread_ok_chk SEGS B LAWS HB ly S W memc md 0x22900 8 HAR C1 C2) as [RA HV2].
split; [lia|].
split.
{ split; [apply abytes_atR_view; exact HV|].
  intros Hin. assert (Hnz := psw_verdict_nz). rewrite Forall_forall in Hnz. specialize (Hnz _ Hin). vm_compute in Hnz.
  exact (Hnz eq_refl). }
split.
{ unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
  - intros a Ha. split.
    + replace a with (0x22900 + Z.of_nat (Z.to_nat (a - 0x22900))) by lia.
      rewrite (HV (Z.to_nat (a - 0x22900))) by (rewrite length_app, psw_verdict_len; cbn [length]; lia). discriminate.
    + unfold ascratch_stk. lia.
  - split; [unfold amem_range, kLowMemEnd; left; lia|]. split; [exact RA | intros _; exact HV2]. }
intros a Ha. apply (HT (0x22900 + 8) psw_verdict_end a Ha).
Qed.
End rd.

End e.
End f.
End d.

(* the post proved at the FP state fx1 a call returned (from_K2 applied at fx1) is the post at the entry's *)
Section lift. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing}.
Lemma psw_post_lift : forall (fx fx1 : YK11.FPState) B MT c (W0 : world (@pa_segs _ cmd_listing PI)) cfg,
  fxrel fx fx1 ->
  SRr (@pa_segs _ cmd_listing PI) W0 cfg (psw_post (fx := fx1) (rc := rc) (SK := SK) (PI := PI) B MT c) ->
  SRr (@pa_segs _ cmd_listing PI) W0 cfg (psw_post (fx := fx) (rc := rc) (SK := SK) (PI := PI) B MT c).
Proof.
intros fx fx1 B MT c W0 cfg H01 H. eapply SRr_mono; [exact H|].
intros W' c' _ (fx2 & ly' & S' & regs' & mem' & md' & Hc & Hf1 & Hf2 & HJ & HP & HQ).
destruct (fxrel_trans fx fx1 fx2 H01 (conj Hf1 Hf2)) as [G1 G2].
exists fx2, ly', S', regs', mem', md'. split; [exact Hc|]. split; [exact G1|]. split; [exact G2|].
split; [exact HJ|]. split; [exact HP | exact HQ].
Qed.
End lift.
