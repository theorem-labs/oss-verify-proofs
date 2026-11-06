(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_pool_config (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_sup_pool_config = 0x8bed0, 127 instructions): it proves a Theorem Labs lane's
   `tsup_pool_config_spec` (lib/B/Prog/sup_pool_config_c.v, a working branch 707acd856cb; the same text as at
   f490061c104) in the form of
   cgif_file_fuzzer's per-function walks: afn_pre at the entry, the symbolic executor over the position-abstract
   listing up to each call, the runtime's rules at the runtime calls (__asan_stack_malloc_0, the snprintf wrapper,
   the frame's release by its flag byte), the callee contracts record_c, arg_s_c, rec_shape_of_c and answer_c at the
   program calls (through cl_callS_wide / cl_callS_na), the return through paj_ret_at, and apost_base at the end.

   It is the B re-walk of the A walk lib/A/Prog/sup_pool_config.v (a working branch c4f188792bb),
   whose B code differs: B calls record() and arg_s() where A inlined record() and called xstrdup, and B inlines
   arg_i, so this function owns arg_i's class-0 side-stack frame (64 bytes, b = frame + 32) and its snprintf. The
   frame code (prologue, realignment `andi sp,sp,-32`, __asan_stack_malloc_0, header and shadow f1 f1 f1 f1 | f8 f8 |
   f3 f3, b unpoisoned around the snprintf and the second arg_s, the release through the flag byte) is arg_i's ASan
   walk's (lib/A/Prog/arg_i.v, a working branch 12dc52bfe84) and answer_code's ASan walk's
   (lib/A/Prog/answer_code.v, a working branch 2ba4488ce71); the B kit usage is socket_send's B walk
   (lib/B/Prog/socket_send.v, a working branch a470f91dbfb).

   Report and trap edges: none. The function has no `jal __asan_report_*`, no `unimp`, no UBSan handler call
   (capstone over the pin's .symtab, gen/traps.B.summary row `sup_pool_config 0`). Its branches: 0x8bf30 `beqz a2`
   on the use-after-return flag, read through the GOT word 0xa5fa8 at the record's const cell 0xb0c40 (= 1, lib/B/YF0m.v
   z4 (ANum 0xb0c40) 0x1, AR's const-cell law al_const; the executor decides it not taken); 0x8bf4c `bnez s2` and
   0x8c040 `beqz s2` on the side-stack frame (nonzero, __asan_stack_malloc_0's post; decided by the frame atom's
   fact), so the real-stack fallback 0x8bf50-0x8bf68 with its page probe and the real-stack release 0x8c074-0x8c090
   are not reached. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_pool_config.v, with its module paths and module names changed; 234 of its 315 lines of code are new or changed and 1983 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s10k.v, with its module paths and module names changed; 170 of its 217 lines of code are new or changed and 268 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the shared
   vocabulary of segment B8b of reac_segconf_parse_file's walk (lib/B/Prog/pf_pieces.v's S_B8b): the walk-internal
   cut JOIN, the listing offsets the segment names, and the geometry of the cut facts every sub-walk of the segment
   uses. The B8b segment lane of the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B8b; statement text and closed arithmetic only, no instruction
   is walked here). Reuse search and CONFIRM: the rule-24 lookup record. ADAPTED from
   a working branch's lib/A/Prog/pf_a8b_d.v (an image-A segment lane, the A twin's JOIN cut) and
   a working branch's lib/A/Prog/pf_a2_g.v (pa2_geo), re-derived on image B's code.

   THE CODE OF B8b (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s; 98 instructions: 0x88e4c-0x88f54 and the
   cold 0x89090-0x890b4, 0x890c0-0x890f8, 0x892cc-0x892d8, 0x892dc-0x892f4):
     PROV2 0x88e4c jal wrapper_snprintf (ret 0x88e50); 0x88e50 j 0x88600 (TAIL)
     NEW   0x88e54 lb a0,0(a3) (a3 = sh(&c->n)), bnez -> 0x890c0 (B#35 slow arm: ld a1,88(s1); andi; addi 3;
           blt a1,a0 -> 0x88e5c; j 0x892dc errpath_store4)
           0x88e5c addi a0,a2,1; ld a1,88(s1) (&c->n); 0x88e64 sw a0,0(a1) (c->n = n + 1)
           0x88e68 bltu s3,a2 -> 0x891c8 (T32: s3 = 32 < n)
           0x88e6c li a0,356; mul a0,a2,a0; ld a1,56(s1) (~c); 0x88e78 bltu a1,a0 -> 0x891c8 (T33: c + 356 n wraps)
           0x88e7c ld a1,200(s1) (c); add s3,a1,a0 (s3 = &seg[n]); li a2,356; mv a0,s3; li a1,0
           0x88e90 jal checked_memset (ret 0x88e94)
           0x88e94 auipc/addi a2 = "%s" (0x21340); li a1,16; mv a0,s3; mv a3,s7; 0x88ea8 jal wrapper_snprintf
           (ret 0x88eac); 0x88eac j 0x88efc
     FOUND 0x88eb0 srli a0,s7,3; add a0,a0,s4; lb a0,0(a0) (shadow of &seg[i].seen_gen); ld a2,24(s1)
           (sh(&c->gen)); 0x88ec0 bnez a0 -> 0x890d4 (B#36 slow arm: andi a1,s7,7; addi 3; blt a1,a0 -> 0x88ec4;
           j 0x892e4 errpath_load4)
           0x88ec4 lb a1,0(a2); mv a3,s3; lw a0,352(s3) (seen_gen); 0x88ed0 bnez a1 -> 0x890e4 (B#37 slow arm:
           ld a2,32(s1); andi; addi 3; blt a2,a1 -> 0x88ed4; j 0x892ec errpath_load4)
           0x88ed4 ld a1,32(s1); lw a1,0(a1) (c->gen); ld s7,192(s1) (the name); 0x88ee0 bne a0,a1 -> 0x88f00
           0x88ee4 auipc/addi a2 = F_twice (0x21620); ld a0,200(s1); mv a1,s6; mv a3,s7; 0x88ef8 jal refuse
           (ret 0x88efc)
     J0    0x88efc mv a3,s3
     JOIN  0x88f00 sd a3,192(s1) (cur); andi a0,a3,3; 0x88f08 bnez -> 0x891c8 (T34: cur not 4-aligned)
           0x88f0c ld a0,24(s1); lb a0,0(a0); 0x88f14 bnez -> 0x89090 (B#38 slow arm: ld a1,32(s1); andi; addi 3;
           blt a1,a0 -> 0x88f18; j 0x892cc errpath_load4)
           0x88f18 ld a0,192(s1); addi a0,a0,352; srli a1,a0,3; add a1,a1,s4; lb a2,0(a1); ld a1,32(s1);
           lw a1,0(a1) (c->gen); 0x88f34 bnez a2 -> 0x890a4 (B#39 slow arm: andi a3,a0,7; addi 3; blt a3,a2 ->
           0x88f38; j 0x892d4 errpath_store4)
           0x88f38 sw a1,0(a0) (cur->seen_gen = c->gen); auipc/addi a2 = "%s"; li a1,16; ld a0,64(s1) (cur_name);
           mv a3,s7; 0x88f50 j 0x88e4c (PROV2's call with cur_name's arguments, then TAIL)
   Traps (the `unimp` 0x891c8): T32 0x88e68 (INV_NEW's n < 32, s3 = 32), T33 0x88e78 (c + 356 n < 2 ^ 64 by pf_obj's
   sa_addr c SEG_C_SIZE), T34 0x88f08 (cur = c + 356 i, c mod 16 = 0 by pf_tf). Checks: B#35 store4 c->n, B#36 load4
   seg[i].seen_gen, B#37 load4 c->gen, B#38 load4 c->gen, B#39 store4 cur->seen_gen; each address lies in the
   block c, which pf_obj's sa_addr c SEG_C_SIZE makes addressable. Calls: snprintf 0x88e4c (PROV2's and JOIN's
   arguments), checked_memset 0x88e90, snprintf 0x88ea8, refuse 0x88ef8.

   THE CUT. NEW and FOUND both reach 0x88f00, which this file cuts as PF_B8B_JOIN: FOUND's `bne a0,a1,0x88f00` arm
   jumps straight to it with a3 = s3 (0x88ec8), and NEW's `j 0x88efc` and the return of FOUND's F_twice refuse call
   reach it after the one `mv a3,s3` of 0x88efc. JOIN's own work is the slot store, T34, the seen_gen store (B#38,
   B#39) and the cur_name snprintf at 0x88e4c, then TAIL. JOIN is taken at EVERY FP state (HA_B8B_JOIN): NEW reaches
   it after snprintf, FOUND after refuse. Its counters' room is the room after the line (pf_next), the room FOUND's
   refusal leaves (pfA_facts.pf_cnt_refuse) and the NEW path's (pf_cnt_mono).

   POSITIONAL NAMES: none is carried from an A table; every offset below is checked against B's seg_text by
   pb8b_offs (computation). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstB pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The listing offsets of the segment (BASE + AF_reac_segconf_parse_file = 0x87e38) *)
Definition PF_B8B_JOIN : Z := AF_reac_segconf_parse_file + 0x10c8.        (* 0x88f00 *)
Definition PF_B8B_J0 : Z := AF_reac_segconf_parse_file + 0x10c4.          (* 0x88efc, mv a3,s3 *)
(* the call returns inside the segment *)
Definition PF_B8B_RET_SNPC : Z := AF_reac_segconf_parse_file + 0x1018.    (* 0x88e50, after the snprintf at 0x88e4c *)
Definition PF_B8B_RET_MEMSET : Z := AF_reac_segconf_parse_file + 0x105c.  (* 0x88e94 *)
Definition PF_B8B_RET_SNPN : Z := AF_reac_segconf_parse_file + 0x1074.    (* 0x88eac *)
Definition PF_B8B_RET_REFUSE : Z := AF_reac_segconf_parse_file + 0x10c4.  (* 0x88efc *)
(* the call instructions *)
Definition PF_B8B_MEMSET : Z := AF_reac_segconf_parse_file + 0x1058.      (* 0x88e90 *)
Definition PF_B8B_SNPN : Z := AF_reac_segconf_parse_file + 0x1070.        (* 0x88ea8 *)
Definition PF_B8B_REFUSE : Z := AF_reac_segconf_parse_file + 0x10c0.      (* 0x88ef8 *)
(* the UBSan trap target, the `unimp` *)
Definition PF_B8B_UNIMP : Z := AF_reac_segconf_parse_file + 0x1390.       (* 0x891c8 *)
Lemma pb8b_offs :
  seg_text + PF_B8B_JOIN = 0x88f00 /\ seg_text + PF_B8B_J0 = 0x88efc /\
  seg_text + PF_B8B_RET_SNPC = 0x88e50 /\ seg_text + PF_B8B_RET_MEMSET = 0x88e94 /\
  seg_text + PF_B8B_RET_SNPN = 0x88eac /\ seg_text + PF_B8B_RET_REFUSE = 0x88efc /\
  seg_text + PF_B8B_MEMSET = 0x88e90 /\ seg_text + PF_B8B_SNPN = 0x88ea8 /\ seg_text + PF_B8B_REFUSE = 0x88ef8 /\
  seg_text + PF_B8B_UNIMP = 0x891c8 /\ seg_text + PF_PROV2 = 0x88e4c /\ seg_text + PF_NEW = 0x88e54 /\
  seg_text + PF_FOUND = 0x88eb0 /\ seg_text + PF_TAIL = 0x88600.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ================================ small arithmetic and register tools ================================ *)
Lemma pb8b_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma pb8b_round32 : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= x - x mod 32 <= x /\ (x - x mod 32) mod 32 = 0 /\ (x - x mod 32) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (E : x - x mod 32 = 32 * (x / 32)) by lia. rewrite E.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma pb8b_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma pb8b_den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma pb8b_zrange : forall (f : Z -> bool) lo (n : nat),
  forallb (fun k => f (lo + Z.of_nat k)) (seq 0 n) = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
intros f lo n H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)).
replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in H by lia. exact H.
Qed.
(* a register of a pf_rg list *)
Lemma pb8b_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma pb8b_rg_bv : forall rX L r v (b : bv 5), pf_rg rX L -> In (r, v) L -> bv_unsigned b = r -> getr rX b = w64 v.
Proof. intros rX L r v b H Hin Hb. rewrite <- (Z_to_bv_bv_unsigned 5 b), Hb. exact (pb8b_rg rX L r v H Hin). Qed.
Lemma pb8b_rg_sub : forall rX L L', pf_rg rX L -> (forall x, In x L' -> In x L) -> pf_rg rX L'.
Proof. intros rX L L' H Hs. unfold pf_rg in *. rewrite Forall_forall in *. intros x Hx. exact (H x (Hs x Hx)). Qed.
Lemma pb8b_rg_app : forall rX L L', pf_rg rX L -> pf_rg rX L' -> pf_rg rX (L ++ L').
Proof. intros rX L L' H H'. unfold pf_rg in *. apply Forall_app. split; assumption. Qed.
Ltac pb8b_in := cbn [In app]; repeat first [left; reflexivity | right].

(* ================================ the block c ================================ *)
(* c->seg[i] for i < 32 lies below c->n; the struct's other fields lie above it *)
Lemma pb8b_seg_in : forall c i off len, (i < 32)%nat -> 0 <= off -> 0 <= len -> off + len <= 356 ->
  c <= seg_spec.rseg_addr c i + off /\ seg_spec.rseg_addr c i + off + len <= c + seg_spec.RC_N.
Proof.
intros c i off len Hi Ho Hl Hol. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RC_N.
assert (Z.of_nat i <= 31) by lia. lia.
Qed.
(* the struct's field offsets as numbers *)
Lemma pb8b_rc_vals : seg_spec.RC_N = 0x2c80 /\ seg_spec.RC_GEN = 0x40e0 /\ seg_spec.RC_READING = 0x4080 /\
  seg_spec.RS_SEEN_GEN = 0x160 /\ seg_spec.RS_IGNORE_FILE = 0x100 /\ seg_spec.RSEG_SIZE = 356 /\
  seg_spec.SEG_C_SIZE = 16616.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* &c->seg[i] is 4-aligned when c is 16-aligned (T34) *)
Lemma pb8b_seg_al4 : forall c i, c mod 16 = 0 -> (seg_spec.rseg_addr c i) mod 4 = 0.
Proof.
intros c i Hc. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE.
apply Z.mod_divide in Hc as [q Hq]; [|lia]. rewrite Hq.
replace (q * 16 + 356 * Z.of_nat i) with ((4 * q + 89 * Z.of_nat i) * 4) by lia. apply Z_mod_mult.
Qed.
(* a byte of parse_file's footprint lies in the block *)
Lemma pb8b_fp_in : forall c a, inFP (seg_spec.RC_PARSE_W c) a -> c <= a < c + seg_spec.SEG_C_SIZE.
Proof.
intros c a (r & Hr & Ha). unfold seg_spec.RC_PARSE_W in Hr.
unfold seg_spec.SEG_C_SIZE, seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING,
  seg_spec.RC_GEN in *.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
(* the segment's writes into the block (c->n, c->seg[i], c->seg[gi].ignore_file, c->reading's neighbours are not
   written) are parse_file's footprint: its first range [c, c + RC_N + 4) *)
Lemma pb8b_fp_block : forall c a, c <= a -> a < c + seg_spec.RC_N + 4 -> inFP (seg_spec.RC_PARSE_W c) a.
Proof.
intros c a H1 H2. exists (c, c + seg_spec.RC_N + 4). split; [left; reflexivity | cbn [fst snd]; lia].
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* No Section hypothesis here: a definition of this file must not pick one up, so that every sub-walk of the
   segment keeps its own callee list. Section c below adds only the ambient FP state. *)
Section c. Context {fx : YK11.FPState}.
(* JOIN (0x88f00): the shared tail of NEW and FOUND. c holds cf (the record after seg_get and, on FOUND's path,
   after the F_twice refusal), entry i is the header's, the name is still in buf at np = s7 (INV_NEW's s7 on the
   NEW path; FOUND's reload from slot 0xc0 at 0x88edc), a3 = s3 = &c->seg[i] (0x88ec8 on FOUND's `bne` arm, 0x88efc
   otherwise). The counters have the room after the line. cur_name still holds nm (its 16 bytes are readable, which
   the snprintf of cur_name keeps past the new NUL). *)
Definition INV_B8B_JOIN (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (np : Z) (name : list Z) (i : nat) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn (pf_next (p_s v) o) (p_s v))) /\
  sa_str (rdW Wc memc) np name /\ pf_inb (pf_F v pos + PF_O_BUF) np name /\ (1 <= length name <= 15)%nat /\
  (i < length (rc_seg cf))%nat /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(19, seg_spec.rseg_addr (p_c v) i); (13, seg_spec.rseg_addr (p_c v) i); (23, np)]).
Definition H_B8B_JOIN (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i,
  INV_B8B_JOIN n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_B8B_JOIN) rX memc mdc)
    (pf_postm B v (r_upd cf i (rs_with_gen (rc_gen cf)), Some i, snprintf_s 16 F_s [AS name]) o ln).
End c.
Definition HA_B8B_JOIN (n : nat) : Prop := forall f1 : YK11.FPState, H_B8B_JOIN (fx := f1) n.

(* ================================ the geometry at a cut ================================ *)
Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the numbers of the frame and the stack at every cut from FTAKEN on (afn_pre's astk_ok at STK_reac_segconf_parse_file
   = 12832, the realigned s1 = (sp0 - 0x160) & -32 of 0x87e38 / 0x87e78, the journal's class-5 frame) *)
Definition pb8b_geoP (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + 12832 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\ pf_s1 v mod 16 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  (pf_F v pos + 2048 <= 0x7fff7000 \/ 0x10007fff8000 <= pf_F v pos) /\
  (forall a, 0x10000 <= a < kImgEnd -> ~ (pf_F v pos <= a < pf_F v pos + 2048)).
Lemma pb8b_geo : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  pb8b_geoP v pos /\ In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = pf_F v pos /\
  frames Sc = (5, pos) :: frames (p_S v) /\ AR SEGS B lyc Sc Wc memc mdc.
Proof.
intros v pos lyc Sc Wc rX memc mdc HCX HFI.
destruct HCX as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in Hslo.
destruct HFI as (HJ & Hly & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (H32 & Happ & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (Hf0 & Hfc & _).
pose proof HAR as (_ & LG & _).
pose proof (pa_img_cover lyc Sc mdc LG) as [IC1 IC2].
assert (EF : frame_addr lyc 5 pos = pf_F v pos) by (subst lyc; reflexivity).
pose proof asan_consts as (C1 & _).
change (fs_frame_bytes 5) with 2048 in Hfc, Happ.
rewrite EF in H32, Happ, Hf0, Hfc.
change (spZ (p_regs v)) with (pf_sp0 v) in Hal, Hslo, Hshi.
assert (Hsp : 0 <= pf_sp0 v) by lia.
pose proof (pb8b_round32 (pf_sp0 v - 352) ltac:(lia) ltac:(apply pb8b_m16; [exact Hal | reflexivity])) as (R1 & R2 & R3).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
split; [|split; [exact Hin | split; [exact EF | split; [exact Hfrs | exact HAR]]]].
unfold pb8b_geoP, pf_s1.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact R2|]. split; [exact R3|].
split; [lia|]. split; [lia|]. split; [exact H32|]. split; [lia|].
intros a Ha Hf. rewrite <- EF in Hf.
destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR
  ltac:(right; left; exists 5, pos; split; [exact Hin | change (fs_frame_bytes 5) with 2048; exact Hf])) as (Hz & _).
apply Hz. unfold in_zr. unfold kImgEnd in *. lia.
Qed.
(* the frame's shadow SH = SHADOW_OFF + F / 8, in the high shadow band below kHighMemBeg *)
Lemma pb8b_SHb : forall v pos, pb8b_geoP v pos ->
  pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\ 0x7fff8000 + 512 <= pf_SH v pos /\
  pf_SH v pos + 256 <= 0x10007fff8000 /\ pf_F v pos = 8 * (pf_F v pos / 8).
Proof.
intros v pos (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
unfold pf_SH, shadow_addr, SHADOW_OFF. lia.
Qed.
(* the block c from the cut facts: c is 16-aligned and not 0 (pf_tf), a live heap block below the allocator's
   ceiling (pf_obj's sa_heap), addressable (pf_obj's sa_addr), apart from the class-5 frame *)
Lemma pb8b_cblk : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  pf_obj B v lyc Sc (rdW Wc memc) ->
  p_c v <> 0 /\ p_c v mod 16 = 0 /\ 4096 <= p_c v /\ p_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling /\
  sa_addr (rdW Wc memc) (p_c v) seg_spec.SEG_C_SIZE /\ sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE /\
  (p_c v + seg_spec.SEG_C_SIZE <= pf_F v pos \/ pf_F v pos + 2048 <= p_c v).
Proof.
intros v pos lyc Sc Wc rX memc mdc HCX HFI HOBJ.
destruct (pb8b_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
pose proof HFI as (_ & _ & _ & _ & _ & _ & _ & HTF & _).
destruct HTF as (Hc0 & Hc16 & _).
destruct HOBJ as (_ & _ & _ & Ac & Hc & _).
destruct Hc as (b & m & Hinb & Hb & Hm).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hinb) as (_ & H4 & Hcl & _ & _ & _ & Hm0).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
pose proof asan_consts as (C1 & _).
assert (Hapart : p_c v + seg_spec.SEG_C_SIZE <= pf_F v pos \/ pf_F v pos + 2048 <= p_c v).
{ pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hinb Hin) as Hap.
  rewrite EF in Hap. change (fs_frame_bytes 5) with 2048 in Hap. unfold zdisjoint in Hap. cbn [fst snd] in Hap.
  unfold seg_spec.SEG_C_SIZE in *. lia. }
split; [exact Hc0|]. split; [exact Hc16|]. split; [unfold seg_spec.SEG_C_SIZE in *; lia|].
split; [unfold seg_spec.SEG_C_SIZE in *; lia|]. split; [exact Ac|].
split; [exists b, m; split; [exact Hinb | lia]|]. exact Hapart.
Qed.
End x.
End e.
End f.
End d.
