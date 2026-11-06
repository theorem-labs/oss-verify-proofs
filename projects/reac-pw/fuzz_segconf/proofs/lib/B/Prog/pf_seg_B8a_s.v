(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 298 of its 352 lines of code are new or changed and 399 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the seeds of segment B8a of
   reac_segconf_parse_file's walk (lib/B/Prog/pf_pieces.v S_B8a). The B8a segment lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: symbolic-state seeds, no instruction walked).
   A seed is the symbolic state the token executor starts from, proved to describe the machine state of a cut:
     b8_seed_seg   at SEG 0x88ca0: every register its own atom; the extra atoms 32 = c, 33 = ~c, 34 = c->n,
                   35 = c->overflow; the slots s1 + 0x00 .. 0x58 B8a reads (0x2c80, &seg[0].seen_gen,
                   &c->overflow, ~c, (c + 0x2c80) >> 3, &c->n: PF_SL's) with the writable window
                   s1 + 0x60 .. 0x78, the slots s1 + 0xc0 (writable) and 0xc8 (c, pf_fi's), and c's two counters
                   c->n (0x2c80) and c->overflow (0x34d0).
     b8_seed_loop  at the loop head 0x88cf0 and at strcmp's return 0x88d08 (one lemma, pc a parameter): the extra
                   atoms 32 .. 38 = c, ~c, n, c->overflow, sh(&c->n), 356 n, the name; the slots 0x28, 0x38 (PF_SL)
                   and 0x60, 0x68, 0x70, 0xc0 (written by B8a before the loop), c->overflow; no window.
     b8_wovf       c->overflow writable (the bound path's region, 0x88d4c .. 0x88d54).
   The shadow knowledge of every seed is c's whole block ([c, c + 16616) addressable: pf_obj's sa_addr c), so the
   token executor folds B8a's two inline checks, c->n's (B#29, lb 0x88ca8) and c->overflow's (B#30, lb 0x88d44):
   their slow paths 0x8907c .. 0x8908c / 0x89104 .. 0x89110 and error calls 0x892c4 / 0x892c8 / 0x89110 are not
   reached. Its shadow base is s4's atom (x20 = SHADOW_OFF, pf_fi). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaSB PaLibG PaLibF PaLibH PaCall
PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B8a_k pf_seg_B8a_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The symbolic states *)
Definition b8_Bx : sv := SOff 20 0.
Definition b8_SH : list shent := [mkSHE 32 0 16616].
Definition PF_LOOP : Z := AF_reac_segconf_parse_file + 0xeb8.   (* 0x88cf0, `beqz s11` (T28) *)
Definition PF_RET : Z := AF_reac_segconf_parse_file + 0xed0.    (* 0x88d08, strcmp's return, `beqz a0` *)
Definition b8_F (nlo : Z) : facts := mkFacts
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF SB SB 0); (32%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 4);
   (34%nat, mkAF nlo 32 0)] [] [].
Definition b8_R0 : YP09.region := YP09.mkRegion (Some 9%nat) 0 0x78 0x60 0x78
  [YP09.mkChunk 0x00 (CVal 8 (SLit 0x2c80)); YP09.mkChunk 0x08 (CVal 8 (SOff 32 0x160));
   YP09.mkChunk 0x28 (CVal 8 (SOff 32 0x34d0)); YP09.mkChunk 0x38 (CVal 8 (SOff 33 0));
   YP09.mkChunk 0x50 (CVal 8 (SAlu ALU_SRL (SOff 32 0x2c80) (SLit 3)));
   YP09.mkChunk 0x58 (CVal 8 (SOff 32 0x2c80))].
Definition b8_R1 : YP09.region := YP09.mkRegion (Some 9%nat) 0xc0 0xd0 0xc0 0xc8
  [YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0))].
Definition b8_R2 : YP09.region := YP09.mkRegion (Some 32%nat) 0x2c80 0x34d4 0 0
  [YP09.mkChunk 0x2c80 (CVal 4 (SOff 34 0)); YP09.mkChunk 0x34d0 (CVal 4 (SOff 35 0))].
Definition b8_ss_seg : sstate := mkSS PF_SEG sr_atoms [b8_R0; b8_R1; b8_R2] None (b8_F 0).
Definition b8_L0 : YP09.region := YP09.mkRegion (Some 9%nat) 0x28 0x78 0 0
  [YP09.mkChunk 0x28 (CVal 8 (SOff 32 0x34d0)); YP09.mkChunk 0x38 (CVal 8 (SOff 33 0));
   YP09.mkChunk 0x60 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x68 (CVal 8 (SOff 34 0));
   YP09.mkChunk 0x70 (CVal 8 (SOff 37 0))].
Definition b8_L1 : YP09.region := YP09.mkRegion (Some 9%nat) 0xc0 0xc8 0 0
  [YP09.mkChunk 0xc0 (CVal 8 (SOff 38 0))].
Definition b8_L2 : YP09.region := YP09.mkRegion (Some 32%nat) 0x34d0 0x34d4 0 0
  [YP09.mkChunk 0x34d0 (CVal 4 (SOff 35 0))].
Definition b8_L2w : YP09.region := YP09.mkRegion (Some 32%nat) 0x34d0 0x34d4 0x34d0 0x34d4
  [YP09.mkChunk 0x34d0 (CVal 4 (SOff 35 0))].
Definition b8_ss_loop (pc : Z) : sstate := mkSS pc sr_atoms [b8_L0; b8_L1; b8_L2] None (b8_F 1).

(** ** Small facts *)
Lemma b8_den_of_U : forall E e v, U E e = v -> 0 <= v < 2 ^ 64 -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H Hv. apply bv_eq. unfold U in H. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma b8_val_mem_of_sa : forall segs H mem a n v, sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
(* `sgtz a0,a2; neg a0,a0; and a0,a0,a2; li a1,356; mul a0,a0,a1` (0x88cc8 .. 0x88cdc) on n in [1, 32] *)
Lemma b8_n356_raw : forall n, 1 <= n <= 32 ->
  zcanon (zmd_raw 64 M_MUL (zcanon (zalu_raw 63 64 ALU_AND (zcanon (zalu_raw 63 64 ALU_SUB (zcanon 0)
    (zcanon (zalu_raw 63 64 ALU_SLT (zcanon 0) n)))) n)) (zcanon 356)) = 356 * n.
Proof.
intros n Hn. destruct (Z_of_nat_complete n ltac:(lia)) as [k ->]. assert (Hk : (k <= 32)%nat) by lia.
do 33 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma b8_U_n356 : forall E n, U E (SOff 34 0) = n -> 1 <= n <= 32 ->
  U E (SMd M_MUL (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 34 0))) (SOff 34 0)) (SLit 356))
  = 356 * n.
Proof. intros E n H Hn. rewrite U_SMd, !U_SAlu, !U_SLit, H. apply b8_n356_raw. exact Hn. Qed.
Lemma b8_U_sh : forall E c, ew E 32 = w64 c -> ew E 20 = w64 SHADOW_OFF -> 0 <= c -> c + 0x2c80 < 2 ^ 47 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 0x2c80) (SLit 3)) (SOff 20 0)) = shadow_addr (c + seg_spec.RC_N).
Proof.
intros E c H32 H20 H0 H1. rewrite U_SAlu, U_srl3, !U_SOff, H32, H20. unfold w64.
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia). unfold shadow_addr, seg_spec.RC_N, SHADOW_OFF, zcanon, M64.
cbn [zalu_raw]. rewrite (Z.mod_small (c + 11392)) by lia. rewrite (Z.mod_small (2147450880 + 0)) by lia.
pose proof (Z.div_pos (c + 11392) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_upper_bound (c + 11392) 8 (c + 11392) ltac:(lia) ltac:(lia)).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma b8_U_srl : forall E c, ew E 32 = w64 c -> 0 <= c -> c + 0x2c80 < 2 ^ 47 ->
  sv_denot E (SAlu ALU_SRL (SOff 32 0x2c80) (SLit 3)) = Z_to_bv 64 ((c + seg_spec.RC_N) / 8).
Proof.
intros E c H32 H0 H1. pose proof (Z.div_pos (c + 11392) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_upper_bound (c + 11392) 8 (c + 11392) ltac:(lia) ltac:(lia)).
apply b8_den_of_U; [|unfold seg_spec.RC_N; lia].
rewrite U_srl3, U_SOff, H32. unfold w64. rewrite unsigned_lit_small by lia.
unfold zcanon, M64, seg_spec.RC_N. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma b8_den_off : forall E n x k, ew E n = w64 x -> 0 <= x + k < 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
  sv_denot E (SOff n k) = Z_to_bv 64 (x + k).
Proof.
intros E n x k H H1 H2. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma b8_chunk8 : forall E (Wc : world SEGS) memc base off e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (rdW Wc memc) (base + off) = Some v -> YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E Wc memc base off e v He Hv Hw.
apply (chunk_ok_val SEGS E _ base off 8 e v He); [change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv | cbn; lia |].
exact (val_mem_of_rdword SEGS _ _ _ _ Hw).
Qed.
Lemma b8_chunk4 : forall E (Wc : world SEGS) memc base off e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  sa_val (rdW Wc memc) (base + off) 4 v -> YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) base (YP09.mkChunk off (CVal 4 e)).
Proof.
intros E Wc memc base off e v He Hv Hw.
apply (chunk_ok_val SEGS E _ base off 4 e v He); [change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact Hv | cbn; lia |].
exact (b8_val_mem_of_sa SEGS _ _ _ _ _ Hw).
Qed.
Lemma b8_rg_get : forall rX L r x, pf_rg rX L -> In (r, x) L -> getr rX (Z_to_bv 5 r) = w64 x.
Proof. intros rX L r x H Hin. exact (proj1 (Forall_forall _ _) H (r, x) Hin). Qed.
Lemma b8_sl_get : forall rd b L off x, pf_sl rd b L -> In (off, x) L -> rdword rd (b + off) = Some x.
Proof. intros rd b L off x H Hin. exact (proj1 (Forall_forall _ _) H (off, x) Hin). Qed.

(* the shadow knowledge of a seed: c's block *)
Lemma b8_shok : forall v pos lyc Sc Wc rX memc mdc sc E, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ew E 32 = w64 (p_c v) -> ew E 20 = w64 SHADOW_OFF ->
  sh_ok SEGS b8_Bx b8_SH E (mrestrict (w_H Wc) memc).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc E HB E32 E20.
destruct (b8_c_blk B v pos lyc Sc Wc rX memc mdc sc HB) as (bc & mc & _ & Hc1 & Hc2 & Hc4 & Hc3 & Happ & _).
pose proof HB as (_ & _ & (_ & _ & _ & HCA & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold seg_spec.SEG_C_SIZE in *.
unfold sh_ok, b8_SH. apply Forall_cons; [|apply Forall_nil].
apply (shent_ok_of_range SEGS (w_H Wc) memc E b8_Bx 32%nat (p_c v) 16616 (p_c v) 0 16616).
- destruct HCA as (_ & _ & _ & HRA & _). exact HRA.
- unfold b8_Bx. apply U_atom; [exact E20 | unfold SHADOW_OFF; lia].
- apply U_atom; [exact E32 | lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* the SEG seed *)
Definition b8_Eseg (rX : bvmap 5 word) (v : pfv) (cf : rconf) : env :=
  Eimg (Ereg rX [w64 (p_c v); w64 (pf_nt (p_c v)); w64 (Z.of_nat (length (rc_seg cf))); w64 (rc_overflow cf)]).
Lemma b8_seed_seg : forall v pos lyc Sc Wc rX memc mdc sc cf, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  sa_rconf (rdW Wc memc) (p_c v) cf ->
  st_ok_pi SEGS VAL (b8_Eseg rX v cf) b8_ss_seg (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_SEG)) memc (seg_rom SEGS))) /\
  sh_ok SEGS b8_Bx b8_SH (b8_Eseg rX v cf) (mrestrict (w_H Wc) memc).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc cf HB HRC.
destruct (b8_geo B v pos lyc Sc Wc rX memc mdc sc HB) as (HAR & Hly & Hin & G).
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof HB as (_ & HFI & _ & HSL & _).
destruct HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & HC8 & HRG).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct (b8_c_blk B v pos lyc Sc Wc rX memc mdc sc HB) as (bc & mc & Hbc & Hc1 & Hc2 & Hc4 & Hc3 & Happ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR Hbc) as (_ & _ & _ & _ & Hbpres & _).
pose proof (b8_rconf_n _ _ _ HRC) as (VN & L32). pose proof (b8_rconf_ov _ _ _ HRC) as (VO & RO).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pf_B_values as (_ & _ & _ & _ & _ & _ & _ & SPF & _). rewrite SPF in G1.
assert (HC16 : p_c v mod 16 = 0) by (pose proof HB as (HCX & _); exact (proj2 (b8_cx B v HCX))).
unfold seg_spec.SEG_C_SIZE in *.
set (E := b8_Eseg rX v cf).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; unfold b8_Eseg; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg rX [w64 (p_c v); w64 (pf_nt (p_c v));
  w64 (Z.of_nat (length (rc_seg cf))); w64 (rc_overflow cf)]) k) by (intros k Hk; subst E; unfold b8_Eseg; apply Eimg_low; exact Hk).
assert (E32 : ew E 32 = w64 (p_c v)) by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 (pf_nt (p_c v))) by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew E 34 = w64 (Z.of_nat (length (rc_seg cf)))) by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (E35 : ew E 35 = w64 (rc_overflow cf)) by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 3)).
clear EX.
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b8_rg_get rX _ 9 _ HRG); cbn; tauto).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (b8_rg_get rX _ 20 _ HRG); cbn; tauto).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E20 : ew E 20 = w64 SHADOW_OFF) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (U32 : bv_unsigned (ew E 32) = p_c v) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (SL : forall off x, In (off, x) (PF_SL v pos) -> rdword (rdW Wc memc) (pf_s1 v + off) = Some x)
  by (intros off x Hin'; exact (b8_sl_get _ _ _ off x HSL Hin')).
split; [|exact (b8_shok v pos lyc Sc Wc rX memc mdc sc E HB E32 E20)].
rewrite restrict_mkst_fx. unfold b8_ss_seg. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b8_R0, b8_R1, b8_R2.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split.
    { intros off Hoff. apply (apresent_writable SEGS). apply Hpres. rewrite SPF. lia. }
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (b8_chunk8 E Wc memc (pf_s1 v) 0x00 (SLit 0x2c80) 0x2c80); [reflexivity | lia | apply SL; cbn; tauto].
    * apply (b8_chunk8 E Wc memc (pf_s1 v) 0x08 _ (p_c v + seg_spec.RS_SEEN_GEN));
        [apply b8_den_off; [exact E32 | unfold seg_spec.RS_SEEN_GEN; lia | lia] | unfold seg_spec.RS_SEEN_GEN; lia | apply SL; cbn; tauto].
    * apply (b8_chunk8 E Wc memc (pf_s1 v) 0x28 _ (p_c v + seg_spec.RC_OVERFLOW));
        [apply b8_den_off; [exact E32 | unfold seg_spec.RC_OVERFLOW; lia | lia] | unfold seg_spec.RC_OVERFLOW; lia | apply SL; cbn; tauto].
    * apply (b8_chunk8 E Wc memc (pf_s1 v) 0x38 _ (pf_nt (p_c v)));
        [apply (b8_den_off E 33 _ 0) in E33; [rewrite Z.add_0_r in E33; exact E33 | unfold pf_nt; lia | unfold pf_nt; lia]
        | unfold pf_nt; lia | apply SL; cbn; tauto].
    * apply (b8_chunk8 E Wc memc (pf_s1 v) 0x50 _ ((p_c v + seg_spec.RC_N) / 8));
        [apply b8_U_srl; [exact E32 | lia | lia] | | apply SL; cbn; tauto].
      pose proof (Z.div_pos (p_c v + seg_spec.RC_N) 8 ltac:(unfold seg_spec.RC_N; lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (p_c v + seg_spec.RC_N) 8 (p_c v + seg_spec.RC_N) ltac:(lia) ltac:(unfold seg_spec.RC_N; lia)).
      unfold seg_spec.RC_N in *; lia.
    * apply (b8_chunk8 E Wc memc (pf_s1 v) 0x58 _ (p_c v + seg_spec.RC_N));
        [apply b8_den_off; [exact E32 | unfold seg_spec.RC_N; lia | lia] | unfold seg_spec.RC_N; lia | apply SL; cbn; tauto].
  + rewrite U9. split; [lia|]. split; [lia|]. split.
    { intros off Hoff. apply (apresent_writable SEGS). apply Hpres. rewrite SPF. lia. }
    repeat apply Forall_cons; try apply Forall_nil.
    apply (b8_chunk8 E Wc memc (pf_s1 v) 0xc8 _ (p_c v));
      [apply (b8_den_off E 32 _ 0) in E32; [rewrite Z.add_0_r in E32; exact E32 | lia | lia] | lia |].
    exact (b8_sl_get _ _ _ 0xc8 (p_c v) HC8 ltac:(cbn; tauto)).
  + rewrite U32. split; [lia|]. split; [lia|]. split; [intros off Hoff; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (b8_chunk4 E Wc memc (p_c v) 0x2c80 _ (Z.of_nat (length (rc_seg cf))));
        [apply (b8_den_off E 34 _ 0) in E34; [rewrite Z.add_0_r in E34; exact E34 | lia | lia] | lia | exact VN].
    * apply (b8_chunk4 E Wc memc (p_c v) 0x34d0 _ (rc_overflow cf));
        [apply (b8_den_off E 35 _ 0) in E35; [rewrite Z.add_0_r in E35; exact E35 | lia | lia] | lia | exact VO].
- apply pairwise_disjoint_of_extents. unfold extent_of_region, b8_R0, b8_R1, b8_R2.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [b8_F f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, E20, U32, E34. unfold w64. rewrite !unsigned_lit_small by (unfold SB, SHADOW_OFF; lia).
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
  repeat split; try lia; assumption.
Qed.

(* the loop seed, at the loop head and at strcmp's return *)
Definition b8_Eloop (rY : bvmap 5 word) (v : pfv) (cf : rconf) (np : Z) : env :=
  Eimg (Ereg rY [w64 (p_c v); w64 (pf_nt (p_c v)); w64 (Z.of_nat (length (rc_seg cf))); w64 (rc_overflow cf);
                 w64 (shadow_addr (p_c v + seg_spec.RC_N)); w64 (356 * Z.of_nat (length (rc_seg cf))); w64 np]).
Definition b8_SLx (v : pfv) (cf : rconf) (np : Z) : list (Z * Z) :=
  [(0x60, shadow_addr (p_c v + seg_spec.RC_N)); (0x68, Z.of_nat (length (rc_seg cf)));
   (0x70, 356 * Z.of_nat (length (rc_seg cf))); (0xc0, np)].
Lemma b8_seed_loop : forall pc v pos lyc Sc Wc rY memY mdY sc cf np, pf_base B v pos lyc Sc Wc rY memY mdY sc ->
  sa_rconf (rdW Wc memY) (p_c v) cf -> (1 <= length (rc_seg cf))%nat ->
  pf_sl (rdW Wc memY) (pf_s1 v) (b8_SLx v cf np) -> 0 <= np < 2 ^ 64 ->
  st_ok_pi SEGS VAL (b8_Eloop rY v cf np) (b8_ss_loop pc)
    (restrict (w_H Wc) (mkst rY (Z_to_bv 64 (BASE + pc)) memY (seg_rom SEGS))) /\
  sh_ok SEGS b8_Bx b8_SH (b8_Eloop rY v cf np) (mrestrict (w_H Wc) memY).
Proof.
intros pc v pos lyc Sc Wc rY memY mdY sc cf np HB HRC HN1 HSX Hnp.
destruct (b8_geo B v pos lyc Sc Wc rY memY mdY sc HB) as (HAR & Hly & Hin & G).
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof HB as (_ & HFI & _ & HSL & _).
destruct HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & HC8 & HRG).
destruct (b8_c_blk B v pos lyc Sc Wc rY memY mdY sc HB) as (bc & mc & Hbc & Hc1 & Hc2 & Hc4 & Hc3 & Happ & _).
pose proof (b8_rconf_n _ _ _ HRC) as (VN & L32). pose proof (b8_rconf_ov _ _ _ HRC) as (VO & RO).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pf_B_values as (_ & _ & _ & _ & _ & _ & _ & SPF & _). rewrite SPF in G1.
unfold seg_spec.SEG_C_SIZE in *.
set (E := b8_Eloop rY v cf np).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rY r)
  by (intros n r Hn; subst E; unfold b8_Eloop; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg rY [w64 (p_c v); w64 (pf_nt (p_c v));
  w64 (Z.of_nat (length (rc_seg cf))); w64 (rc_overflow cf); w64 (shadow_addr (p_c v + seg_spec.RC_N));
  w64 (356 * Z.of_nat (length (rc_seg cf))); w64 np]) k) by (intros k Hk; subst E; unfold b8_Eloop; apply Eimg_low; exact Hk).
assert (E32 : ew E 32 = w64 (p_c v)) by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 0)).
assert (E33 : ew E 33 = w64 (pf_nt (p_c v))) by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 1)).
assert (E34 : ew E 34 = w64 (Z.of_nat (length (rc_seg cf)))) by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 2)).
assert (E35 : ew E 35 = w64 (rc_overflow cf)) by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 3)).
assert (E36 : ew E 36 = w64 (shadow_addr (p_c v + seg_spec.RC_N))) by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 4)).
assert (E37 : ew E 37 = w64 (356 * Z.of_nat (length (rc_seg cf)))) by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 5)).
assert (E38 : ew E 38 = w64 np) by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 6)).
clear EX.
assert (R9 : getr rY (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b8_rg_get rY _ 9 _ HRG); cbn; tauto).
assert (R20 : getr rY (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (b8_rg_get rY _ 20 _ HRG); cbn; tauto).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E20 : ew E 20 = w64 SHADOW_OFF) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (U32 : bv_unsigned (ew E 32) = p_c v) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (SL : forall off x, In (off, x) (PF_SL v pos) -> rdword (rdW Wc memY) (pf_s1 v + off) = Some x)
  by (intros off x Hin'; exact (b8_sl_get _ _ _ off x HSL Hin')).
assert (SX : forall off x, In (off, x) (b8_SLx v cf np) -> rdword (rdW Wc memY) (pf_s1 v + off) = Some x)
  by (intros off x Hin'; exact (b8_sl_get _ _ _ off x HSX Hin')).
assert (Hsh : 0 <= shadow_addr (p_c v + seg_spec.RC_N) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF, seg_spec.RC_N. pose proof (Z.div_pos (p_c v + 11392) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (p_c v + 11392) 8 (p_c v + 11392) ltac:(lia) ltac:(lia)). lia. }
split; [|exact (b8_shok v pos lyc Sc Wc rY memY mdY sc E HB E32 E20)].
rewrite restrict_mkst_fx. unfold b8_ss_loop. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b8_L0, b8_L1, b8_L2.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros off Hoff; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (b8_chunk8 E Wc memY (pf_s1 v) 0x28 _ (p_c v + seg_spec.RC_OVERFLOW));
        [apply b8_den_off; [exact E32 | unfold seg_spec.RC_OVERFLOW; lia | lia] | unfold seg_spec.RC_OVERFLOW; lia | apply SL; cbn; tauto].
    * apply (b8_chunk8 E Wc memY (pf_s1 v) 0x38 _ (pf_nt (p_c v)));
        [apply (b8_den_off E 33 _ 0) in E33; [rewrite Z.add_0_r in E33; exact E33 | unfold pf_nt; lia | unfold pf_nt; lia]
        | unfold pf_nt; lia | apply SL; cbn; tauto].
    * apply (b8_chunk8 E Wc memY (pf_s1 v) 0x60 _ (shadow_addr (p_c v + seg_spec.RC_N)));
        [apply (b8_den_off E 36 _ 0) in E36; [rewrite Z.add_0_r in E36; exact E36 | lia | lia] | lia | apply SX; cbn; tauto].
    * apply (b8_chunk8 E Wc memY (pf_s1 v) 0x68 _ (Z.of_nat (length (rc_seg cf))));
        [apply (b8_den_off E 34 _ 0) in E34; [rewrite Z.add_0_r in E34; exact E34 | lia | lia] | lia | apply SX; cbn; tauto].
    * apply (b8_chunk8 E Wc memY (pf_s1 v) 0x70 _ (356 * Z.of_nat (length (rc_seg cf))));
        [apply (b8_den_off E 37 _ 0) in E37; [rewrite Z.add_0_r in E37; exact E37 | lia | lia] | lia | apply SX; cbn; tauto].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros off Hoff; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (b8_chunk8 E Wc memY (pf_s1 v) 0xc0 _ np);
      [apply (b8_den_off E 38 _ 0) in E38; [rewrite Z.add_0_r in E38; exact E38 | lia | lia] | lia | apply SX; cbn; tauto].
  + rewrite U32. split; [lia|]. split; [lia|]. split; [intros off Hoff; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (b8_chunk4 E Wc memY (p_c v) 0x34d0 _ (rc_overflow cf));
      [apply (b8_den_off E 35 _ 0) in E35; [rewrite Z.add_0_r in E35; exact E35 | lia | lia] | lia | exact VO].
- apply pairwise_disjoint_of_extents. unfold extent_of_region, b8_L0, b8_L1, b8_L2.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [b8_F f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  assert (HC16 : p_c v mod 16 = 0) by (pose proof HB as (HCX & _); exact (proj2 (b8_cx B v HCX))).
  rewrite U9, E20, U32, E34. unfold w64. rewrite !unsigned_lit_small by (unfold SB, SHADOW_OFF; lia).
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
  repeat split; try lia; assumption.
Qed.

(* c->overflow writable: the bound path's region, put in place of the state's regions after `blt` 0x88d38 *)
Lemma b8_l2w_ok : forall v pos lyc Sc Wc rY memY mdY sc cf E, pf_base B v pos lyc Sc Wc rY memY mdY sc ->
  sa_rconf (rdW Wc memY) (p_c v) cf -> ew E 32 = w64 (p_c v) -> ew E 35 = w64 (rc_overflow cf) ->
  region_ok SEGS E (mrestrict (w_H Wc) memY) b8_L2w.
Proof.
intros v pos lyc Sc Wc rY memY mdY sc cf E HB HRC E32 E35.
destruct (b8_geo B v pos lyc Sc Wc rY memY mdY sc HB) as (HAR & _ & _ & _).
destruct (b8_c_blk B v pos lyc Sc Wc rY memY mdY sc HB) as (bc & mc & Hbc & Hc1 & Hc2 & Hc4 & Hc3 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR Hbc) as (_ & _ & _ & _ & Hbpres & _).
pose proof (b8_rconf_ov _ _ _ HRC) as (VO & RO).
pose proof asan_consts as (C1 & _). unfold seg_spec.SEG_C_SIZE in *.
assert (U32 : bv_unsigned (ew E 32) = p_c v) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
unfold region_ok, b8_L2w. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U32. split; [lia|]. split; [lia|]. split.
- intros off Hoff. apply (apresent_writable SEGS). assert (Hr : bc <= p_c v + off < bc + req_size mc) by lia.
  exact (proj1 (Hbpres _ Hr)).
- repeat apply Forall_cons; try apply Forall_nil.
  apply (b8_chunk4 E Wc memY (p_c v) 0x34d0 _ (rc_overflow cf));
    [apply (b8_den_off E 35 _ 0) in E35; [rewrite Z.add_0_r in E35; exact E35 | lia | lia] | lia | exact VO].
Qed.
Lemma b8_swap_ok : forall E ss ms r,
  st_ok_pi SEGS VAL E ss ms -> YP09.region_wf r = true -> region_ok SEGS E (ms_mem ms) r ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) [r] (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r HS Hwf Hr.
pose proof (st_ok_pi_submem E ss ms [] HS (submem_nil _) eq_refl) as HS0.
exact (st_ok_pi_add_region E _ ms r HS0 Hwf Hr I).
Qed.
End e.
End f.
End d.
