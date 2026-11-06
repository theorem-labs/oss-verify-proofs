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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 819 of its 869 lines of code are new or changed and 403 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): stretch D of segment A9 of reac_segconf_parse_file's walk,
   K5 0x8814c -> REF3 (cur = NULL), ROLE, MODEL, IGN or K9 (lib/A/Prog/pf_a9_d.v SA9_D). Part of
   segment A9's proof, by the G3 walk owner, 2026-10-30.

   proves no function (kind: segment lemma of reac_segconf_parse_file's image-A walk, one stretch of segment A9;
   the whole function's rule-24 line, its pasted released-proof index output and the G3 walk owner's CONFIRM of
   2026-10-30T15:42:08Z are in the unit's internal record, commit dfb49d6ad789,
   path records/segp/g3-lookup.md, reuse verdict none:
   written new)

   THE CODE (the excerpt reac_segconf_parse_file.fuzz_segconf.asan.s in records/segp/dis/ at that commit;
   reac_segconf.c:224-292), 40 instructions:
     0x8814c K5  beqz s4, 0x881bc                       cur = NULL?
     0x88150 C1  a1 = 0x21760 "role" (listing object 43), a0 = s7 = key, jal 0x43a1c (strcasecmp trampoline)
     0x88160 R1  beqz a0, 0x881d4 = ROLE
     0x88164 C2  a1 = 0x21800 "model" (44) ...      0x88174 R2  beqz a0, 0x8826c = MODEL
     0x88178 C3  a1 = 0x218e0 "ignore" (45) ...     0x88188 R3  beqz a0, 0x88364 = IGN
     0x8818c C4  a1 = 0x21960 "knock" (46) ...      0x8819c R4  beqz a0, 0x884f8
     0x881a0     a2 = 0x21a40 F_nokey (47), a0 = s8 = c, a1 = s10 = lineno, ld a3, 0x50(s1) (cur_name), a4 = s7 = key;
                 j 0x88510 = K9
     0x884f8     a2 = 0x21980 F_knock (61), a0 = s8, a1 = s10, ld a3, 0x50(s1), a4 = s9 = val; falls into K9
     0x881bc     a2 = 0x21700 F_outside (48), a0 = s8, a1 = s10, a3 = s7 = key; j 0x87e74 = REF3

   THE WALK: one lemma per mini-cut, each from a fresh seed (s4_seed: every register its own atom, the spill slot
   s1 + 0x50 as the one read-only region, its value F + 0x20 as atom 32; the shape of segment A7's pf_a7_q.v a7_seed,
   7831f455a1ce) and the token executor with the empty shadow list (no inline check in the stretch):
     s4_K5  branch on s4 (psrr_branch_tok): 0 is cur = None (pf_a9_f.v a9_cur_ptr_eq0), run to REF3 and H_REF3 with
            pf_ref3's F_outside disjunct and a9_rkey_outs; else cur = Some gi, run to C1;
     s4_C1 .. s4_C4  run to the jal, then s4_call;
     s4_R1 .. s4_R3  branch on a0 (psrr_branch_tok on the fresh atom a0, s4_br_eq0 = trim_s.v tr_br_eq0's form):
            0 is strcasecmp = 0 (s4_cmp_true), run to ROLE / MODEL / IGN and H_ROLE / H_MODEL / H_IGN with INV_KV
            (s4_kv_of); else run to the next C;
     s4_R4  branch on a0: run to K9 on each arm and from_K9 with INV_K9 (s4_k9_of), r_key by a9_rkey_knock /
            a9_rkey_nokey.
   s4_call is ONE strcasecmp call: PaArt.v aj_art_at with RtSeg row 10 (ASTRCASECMP) at o = s1 - sp0 and window
   2 * ESTACK. Its premises: ecall_pre_stk by PaArt.v ecall_pre_stk_at; the key in buf (s4_addr_buf: buf is in
   scope at PF_SC_LINE, pf_a9_f.v a9_buf_addr / a9_buf_hull); the literal from pf_obj's sa_lit (sa_pinned at the
   call's state, the image range; S_role, S_model, S_ignore, S_knock, F_outside, F_knock and F_nokey are all texts
   of reac_segconf_parse_file_c.v's PARSE_FILE_LITS); rt_rom_view by pf_a5_k.v a5_rom. Row 10's post fixes only
   whether a0 is 0; s4_res turns its `map lc` equality into SegModel.strcasecmp = 0 (pf_a9_f.v a9_strcasecmp_iff).
   THE TRANSPORT (s4_move) across a run that writes nothing and across the call (art_post with E = fun _ => False,
   so every byte outside [s1 - 2 ESTACK, s1) is kept): pf_base by segment A5's pf_a5_k.v a5_move0 (no Section
   hypothesis), pf_st / slot 0xb0 / the frame shadow by a5_keep_st / a5_keep_slot / a5_keep_fsh, the two buf
   strings by the keep clause (buf lies below alloc_ceiling), the window's bytes stay visible by the journal.
   No trim or refuse call is in this stretch (its exit K9 is before the jal), so it has no rule-1j-bis site lemma.

   SECTION HYPOTHESES: TL (PALib: the errno cell aj_art_at needs), OBJ (seg_val_objs: the seven literal atoms),
   ASTRCASECMP. SIGP is not used (no program call) and VRO is not used (a5_move0 and a5_rom need none). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_d pf_a5_k pf_a9_d pf_a9_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= pure helpers ======================= *)
(* a reader of the ASan view depends on the address only modulo 2 ^ 64 (lib/A/Rt/RtPFupoison.v aview_mod) *)
Lemma s4_aview_mod : forall segs H mem a, aview segs H mem a = aview segs H mem (a mod 2 ^ 64).
Proof.
intros segs H mem a. assert (E : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity. }
unfold aview, mbyte. rewrite E. reflexivity.
Qed.

(* every byte of a C string and its NUL is mapped (segment A7's pf_a7_r.v a7_str_some, ebe0b30cca65) *)
Lemma s4_str_some : forall (rd : reader) p s a, sa_str rd p s -> p <= a <= p + Z.of_nat (length s) ->
  rd a <> None.
Proof.
intros rd p s a [[Hz _] _] Ha.
assert (Hi : (Z.to_nat (a - p) < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
pose proof (Hz _ Hi) as E. rewrite Z2Nat.id in E by lia.
replace (p + (a - p)) with a in E by lia. rewrite E. discriminate.
Qed.

(* `beqz r` on an atom whose value is the word w (trim_s.v tr_br_eq0's form, for any word) *)
Lemma s4_br_eq0 : forall E n (w : word) b, ew E n = w ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> (bv_unsigned w =? 0) = b.
Proof.
intros E n w b H Hc. pose proof (bv_unsigned_in_range 64 w) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
assert (Hw : ew E n = Z_to_bv 64 (bv_unsigned w)) by (rewrite H; symmetry; apply Z_to_bv_bv_unsigned).
rewrite branch_eq_U, (U_atom E n (bv_unsigned w) Hw Hr), U_lit in Hc by lia. exact Hc.
Qed.

(* the strcasecmp answer read off a0 after the branch *)
Lemma s4_cmp_true : forall (w : word) (P : Prop), (w = w64 0 <-> P) -> (bv_unsigned w =? 0) = true -> P.
Proof.
intros w P HP H. apply HP. apply Z.eqb_eq in H.
rewrite <- (Z_to_bv_bv_unsigned 64 w), H. reflexivity.
Qed.
Lemma s4_cmp_false : forall (w : word) (P : Prop), (w = w64 0 <-> P) -> (bv_unsigned w =? 0) = false -> ~ P.
Proof.
intros w P HP H HPp. apply HP in HPp. rewrite HPp in H. unfold w64 in H.
rewrite unsigned_lit_small in H by lia. discriminate.
Qed.

(* RtSeg row 10's answer as SegModel's (both strings NUL-free; pf_a9_f.v a9_strcasecmp_iff) *)
Lemma s4_res : forall (w : word) (key lit : list Z), ~ In 0 key -> ~ In 0 lit ->
  seg_spec.zs (seg_spec.zb key) = key -> seg_spec.zs (seg_spec.zb lit) = lit ->
  (w = w64 0 <-> map RtSeg.lc (map (fun b : byte => bv_unsigned b) (seg_spec.zb key) ++ [0]) =
                 map RtSeg.lc (map (fun b : byte => bv_unsigned b) (seg_spec.zb lit) ++ [0])) ->
  (w = w64 0 <-> SegModel.strcasecmp key lit = 0).
Proof.
intros w key lit Hk Hl Zk Zl H.
change (map (fun b : byte => bv_unsigned b) (seg_spec.zb key)) with (seg_spec.zs (seg_spec.zb key)) in H.
change (map (fun b : byte => bv_unsigned b) (seg_spec.zb lit)) with (seg_spec.zs (seg_spec.zb lit)) in H.
rewrite Zk, Zl in H. rewrite <- (a9_strcasecmp_iff key lit Hk Hl). exact H.
Qed.

(* the registers A9's stretch keeps from K5 on: sp, gp, tp, s0, s1, s2 .. s11 *)
Definition S4_REGS : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Ltac s4_inregs := unfold S4_REGS; cbn [In]; repeat (first [left; reflexivity | right]).
Lemma s4_rg_move : forall rX rX' L, (forall r, In r S4_REGS -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  Forall (fun rv => In (fst rv) S4_REGS) L -> pf_rg rX L -> pf_rg rX' L.
Proof.
intros rX rX' L HR HL H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HR (fst rv) (HL rv Hin)). exact (H rv Hin).
Qed.
Lemma s4_S4_cs : forall r, In r S4_REGS -> acallee_saved r.
Proof. intros r Hr. unfold S4_REGS in Hr. cbn [In] in Hr. unfold acallee_saved. lia. Qed.
Lemma s4_fs_self : forall S : astate, exists f, S = set_fs f S.
Proof. intros S. exists (st_fs S). destruct S; reflexivity. Qed.

(* the pcs of the stretch, as listing offsets (BASE + <offset>; AF_reac_segconf_parse_file = 0x87a78) *)
Definition A9_C1 : Z := AF_reac_segconf_parse_file + 0x6d8.   (* 0x88150: a1 = "role", the first call *)
Definition A9_R1 : Z := AF_reac_segconf_parse_file + 0x6e8.   (* 0x88160: its return, beqz a0 -> ROLE *)
Definition A9_C2 : Z := AF_reac_segconf_parse_file + 0x6ec.   (* 0x88164: "model" *)
Definition A9_R2 : Z := AF_reac_segconf_parse_file + 0x6fc.   (* 0x88174: beqz a0 -> MODEL *)
Definition A9_C3 : Z := AF_reac_segconf_parse_file + 0x700.   (* 0x88178: "ignore" *)
Definition A9_R3 : Z := AF_reac_segconf_parse_file + 0x710.   (* 0x88188: beqz a0 -> IGN *)
Definition A9_C4 : Z := AF_reac_segconf_parse_file + 0x714.   (* 0x8818c: "knock" *)
Definition A9_R4 : Z := AF_reac_segconf_parse_file + 0x724.   (* 0x8819c: beqz a0 -> 0x884f8 (F_knock), else F_nokey *)

(* THE SYMBOLIC STATE at a pc of the stretch (the shape of segment A7's pf_a7_q.v a7_seed, 7831f455a1ce, cut down to
   what this stretch reads): every register its own atom (sr_atoms), the extra atom 32 = cur_name's address
   F + 0x20, and ONE read-only region, the spill slot s1 + 0x50 holding atom 32: the only memory word the stretch
   reads (`ld a3, 0x50(s1)` at 0x881b0 and 0x88508), from pf_base's pf_sl (PF_SL's (0x50, F + PF_O_CN)). The facts
   are pf_a7_q.v's for atoms 2, 8, 9 (sp, s0 = sp0, s1) and 22 (s6 = the shadow base). The stretch makes no inline
   check and writes nothing, so the token runs take the empty shadow list and no window is writable. *)
Definition s4_slot_r : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x50 0x58 0 0 [YP09.mkChunk 0x50 (CVal 8 (SOff 32 0))].
Definition s4_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
            (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF SB SB 0) ] [] [].
Definition s4_ss (pc : Z) : sstate := mkSS pc sr_atoms [s4_slot_r] None s4_facts.
Definition s4_Bx : sv := SOff 22 0.

(* trim_k.v tr_ag32 *)
Lemma s4_ag32 : forall (regs1 : bvmap 5 word) extra E0 E (k : nat), (32 <= k)%nat ->
  env_agree 32 (Ereg regs1 extra) E0 -> env_agree k E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E k Hk H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.

Ltac s4_inl := unfold PF_RL, PF_RM; cbn [app In]; repeat (first [left; reflexivity | right]).
Ltac s4_inlits := unfold PARSE_FILE_LITS; apply in_or_app; left; cbn [In];
  repeat (first [left; reflexivity | right]).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma s4_K5_regs : forall v pos o ln a b c,
  Forall (fun rv => In (fst rv) S4_REGS) (PF_RL v pos ++ PF_RM v o ln ++ [(20, a); (23, b); (25, c)]).
Proof.
intros. unfold PF_RL, PF_RM. cbn [app].
repeat (apply Forall_cons; [cbn [fst]; s4_inregs|]). apply Forall_nil.
Qed.
Lemma s4_FI_regs : forall B v, Forall (fun rv => In (fst rv) S4_REGS) (a5_FI B v).
Proof.
intros. unfold a5_FI. repeat (apply Forall_cons; [cbn [fst]; s4_inregs|]). apply Forall_nil.
Qed.

(* the seed's environment: the registers rX and atom 32 = F + PF_O_CN *)
Definition s4_E (rX : bvmap 5 word) (x : a9x) : env :=
  Eimg (Ereg rX [Z_to_bv 64 (pf_F (y_v x) (y_pos x) + PF_O_CN)]).

(* the registers a run leaves as their own atoms keep the seed's values (segment A7's pf_a7_q.v a7_regs_kept): after
   a run that stops at a pc (st_ok_pi) and after one that stops at a call (st_ok of the trampoline) *)
Lemma s4_kept_pi : forall E ss (H : word -> bool) ms rX extra,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> env_agree 32 (Ereg rX extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    (map (Z_to_bv 5) S4_REGS) = true ->
  forall k, In k S4_REGS -> getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k).
Proof.
intros E ss H ms rX extra HS HA Hl k Hk.
exact (regs_kept_of_st_ok_pi E ss (restrict H ms) rX extra (map (Z_to_bv 5) S4_REGS) HS HA Hl (Z_to_bv 5 k)
  (in_map _ _ _ Hk)).
Qed.
Lemma s4_kept_ok : forall E ss (H : word -> bool) ms rX extra,
  st_ok SEGS E ss (restrict H ms) -> env_agree 32 (Ereg rX extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    (map (Z_to_bv 5) S4_REGS) = true ->
  forall k, In k S4_REGS -> getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k).
Proof.
intros E ss H ms rX extra HS HA Hl k Hk.
exact (regs_kept_of_st_ok SEGS E ss (restrict H ms) rX extra (map (Z_to_bv 5) S4_REGS) HS HA Hl (Z_to_bv 5 k)
  (in_map _ _ _ Hk)).
Qed.

(* SegABase's sa_str (list Z) as the runtime rows state a string (segment A7's pf_a7_r.v a7_astr_of_sa) *)
Lemma s4_astr_of_sa : forall (W : world SEGS) mem q l,
  sa_str (rdW W mem) q l ->
  astr_at SEGS W mem q (seg_spec.zb l) /\ astr_len (seg_spec.zb l) = Z.of_nat (length l) /\
  seg_spec.zs (seg_spec.zb l) = l /\ atail_vis SEGS W mem (q + astr_len (seg_spec.zb l)).
Proof.
intros W mem q l [Hz Ht].
destruct (sa_strz_bytes SEGS (w_H W) mem q l Hz) as (Hb & Hn & Hzs).
assert (HR : astr_atR (rdW W mem) q (seg_spec.zb l)) by (split; [exact Hb | exact Hn]).
assert (HL : astr_len (seg_spec.zb l) = Z.of_nat (length l))
  by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
split; [apply astr_atR_view; exact HR|]. split; [exact HL|]. split; [exact Hzs|].
rewrite HL. exact Ht.
Qed.

(* a range the walk's memory holds, as aread_ok (segment A7's pf_a7_r.v a7_read_ok_of_addr) *)
Lemma s4_read_ok_of_addr : forall (W : world SEGS) regs mem stk q n,
  sa_addr (rdW W mem) q n -> 0 <= n < 2 ^ 32 ->
  (forall a, q <= a < q + n -> rdW W mem a <> None) -> q + n <= spZ regs - stk ->
  aread_ok SEGS stk W regs mem q n.
Proof.
intros W regs mem stk q n (A0 & A1 & A2 & A3 & A4) Hn Hm Hw.
split; [exact A0|]. split; [exact A1|]. split; [exact Hn|].
split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
intros a Ha. split; [exact (Hm a Ha)|]. unfold ascratch_stk. lia.
Qed.

(* a range of buf is addressable with its shadow mapped: buf is in scope at every cut of A9 (PF_SC_LINE);
   pf_a9_f.v's a9_buf_addr / a9_buf_hull for the shadow, the frame's application range for amem_range *)
Lemma s4_addr_buf : forall (rd : reader) v pos q n, a5_G v pos -> pf_fsh rd (pf_SH v pos) PF_SC_LINE ->
  pf_F v pos + PF_O_BUF <= q -> 0 <= n -> q + n <= pf_F v pos + PF_O_BUF + 512 -> sa_addr rd q n.
Proof.
intros rd v pos q n G HF Hq Hn Hqn.
pose proof G as (_ & _ & _ & _ & _ & G6 & G7 & G8 & G9 & G10 & _).
pose proof alloc_ceiling_lt as HC.
unfold PF_O_BUF in Hq, Hqn.
assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
split; [lia|]. split; [lia|].
split.
{ apply amem_range_high; [lia| |lia].
  destruct G9 as [_ [Hlo | [Hhi1 Hhi2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
  [left; lia | right; lia]. }
split.
- exact (a9_buf_addr rd (pf_SH v pos) (pf_F v pos) q n HF eq_refl HF8 ltac:(lia) ltac:(lia) ltac:(lia) Hn).
- intros Hn0.
  exact (a9_buf_hull rd (pf_SH v pos) (pf_F v pos) q n HF eq_refl HF8 ltac:(lia) ltac:(lia) ltac:(lia) Hn0).
Qed.

Section e.
Variable B : asyms.
(* the image's runtime record (the strcasecmp step needs its errno cell, pal_env) *)
Hypothesis TL : PALib B.
(* the listing objects: the auipc / addi pairs of the four literals and the two formats *)
Hypothesis OBJ : seg_val_objs (PI := PI).
(* the interceptor owner's accepted RtSeg row 10, at the listing's strcasecmp trampoline (image A 0x43a1c) *)
Hypothesis ASTRCASECMP : forall fx0 : YK11.FPState,
  @RtSeg.astrcasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcasecmp).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* a C string of buf after a step that keeps every byte off the window [s1 - 2 ESTACK, s1) *)
Lemma s4_keep_inbuf : forall x (Wc : world SEGS) memc memc' q s, a5_G (y_v x) (y_pos x) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 (y_v x) - 2 * ESTACK <= a < pf_s1 (y_v x)) -> rdW Wc memc' a = rdW Wc memc a) ->
  a9_inbuf (rdW Wc memc) x q s -> a9_inbuf (rdW Wc memc') x q s.
Proof.
intros x Wc memc memc' q s G HK (((Hz & Hn) & Ht) & Hb1 & Hb2).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof alloc_ceiling_lt as HC.
unfold ESTACK in HK. unfold a9_buf, PF_O_BUF in Hb1, Hb2.
split; [|split; [exact Hb1 | exact Hb2]].
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite HK; [exact (Hz i Hi) | lia | lia].
- intros y Hy. pose proof (Z.mod_pos_bound (q + Z.of_nat (length s)) 8 ltac:(lia)).
  rewrite HK; [exact (Ht y Hy) | lia | lia].
Qed.

(* the cut K5's facts at a later state of the same call frame: a run that writes nothing, or the strcasecmp
   call, which writes only its window below s1 (art_post with E = fun _ => False). pf_base by segment A5's
   pf_a5_k.v a5_move0 (no Section hypothesis), the rest by a5_keep_st / a5_keep_slot / a5_keep_fsh. *)
Lemma s4_move : forall n x ei kp vp lyc Sc Wc rX memc mdc rX' memc' mdc',
  INV_K5 B n x ei kp vp lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 (y_v x) - 2 * ESTACK <= a < pf_s1 (y_v x)) -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall r, In r S4_REGS -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  INV_K5 B n x ei kp vp lyc Sc Wc rX' memc' mdc'.
Proof.
intros n x ei kp vp lyc Sc Wc rX memc mdc rX' memc' mdc' (HC & HSTR & HKEY & HVAL & HRG) HJ' HKP HR.
destruct HC as (HB & HM & HS & HL & HLT & HD0 & HDL).
destruct (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof (a5_text B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & Hc).
assert (KW : forall sl shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx (y_v x) (y_pos x) sl shw a ->
  rdW Wc memc' a = rdW Wc memc a).
{ intros sl shw a Ha Hw. apply HKP; [exact Ha|]. intros Hw'. apply Hw. unfold a5_Wrx. left.
  rewrite SPF in G1 |- *. unfold ESTACK in Hw'. lia. }
assert (HVIS : forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None).
{ intros a Ha. pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  rewrite s4_aview_mod in Ha |- *.
  pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as M.
  rewrite SPF in G1, Hpres. unfold ESTACK in HKP.
  destruct (Z_lt_le_dec (a mod 2 ^ 64) (pf_s1 (y_v x) - 2 * 4096)) as [H1 | H1];
    [|destruct (Z_lt_le_dec (a mod 2 ^ 64) (pf_s1 (y_v x))) as [H2 | H2]].
  - rewrite HKP; [exact Ha | exact M | lia].
  - apply (aview_some_of_apresent SEGS). apply Hpres. lia.
  - rewrite HKP; [exact Ha | exact M | lia]. }
assert (HRG' : pf_rg rX' (PF_RL (y_v x) (y_pos x) ++ PF_RM (y_v x) (y_o x) (y_ln x) ++
                          [(20, a9_cp x); (23, kp); (25, vp)]))
  by exact (s4_rg_move rX rX' _ HR (s4_K5_regs _ _ _ _ _ _ _) HRG).
assert (HFI' : pf_rg rX' (a5_FI B (y_v x)))
  by exact (s4_rg_move rX rX' _ HR (s4_FI_regs B (y_v x)) (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB)).
assert (HB' : pf_base B (y_v x) (y_pos x) lyc Sc Wc rX' memc' mdc' PF_SC_LINE).
{ apply (a5_move0 B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc rX' memc' mdc' PF_SC_LINE HB HJ'
    (s4_fs_self Sc) (Permutation_refl _) (KW true true) HVIS HFI').
  destruct HB as (_ & _ & _ & _ & HFSH).
  exact (a5_keep_fsh (y_v x) (y_pos x) _ _ true PF_SC_LINE G (KW true false) HFSH). }
split; [|split; [exact HSTR | split; [exact (s4_keep_inbuf x Wc memc memc' kp _ G HKP HKEY) |
  split; [exact (s4_keep_inbuf x Wc memc memc' vp _ G HKP HVAL) | exact HRG']]]].
split; [exact HB'|]. split; [exact HM|].
split; [exact (a5_keep_st B (y_v x) (y_pos x) lyc Sc Wc memc mdc Wc memc' G HAR Hin Hly (KW true true) _ _ _ _ Hc HS)|].
split; [exact (a5_keep_slot (y_v x) (y_pos x) _ _ true _ G (KW false true) HL)|].
split; [exact HLT|]. split; [exact HD0 | exact HDL].
Qed.

(* ======================= one strcasecmp call ======================= *)
(* From the trampoline (the run stopped at `jal 0x43a1c` with a0 = kp, a1 = a literal of PARSE_FILE_LITS and
   ra = BASE + ret): PaArt.v's aj_art_at with RtSeg row 10 (ASTRCASECMP), then K5's facts again at the return
   (s4_move) and the answer as SegModel's (s4_res). The premises: ecall_pre_stk by PaArt.v ecall_pre_stk_at at
   o = s1 - sp0; the key in buf (s4_addr_buf: buf in scope); the literal by pf_obj's sa_lit (sa_pinned at this
   state, the image range); rt_rom_view by pf_a5_k.v a5_rom. *)
Lemma s4_call : forall n x ei kp vp lyc Sc Wc rT memT mdT lit (ret : Z) Q,
  INV_K5 B n x ei kp vp lyc Sc Wc rT memT mdT ->
  In lit PARSE_FILE_LITS ->
  getr rT 10 = w64 kp -> getr rT 11 = w64 (seg_litA_rc lit) -> getr rT 1 = Z_to_bv 64 (BASE + ret) ->
  0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall rX2 mem2 md2, INV_K5 B n x ei kp vp lyc Sc Wc rX2 mem2 md2 ->
     (getr rX2 10 = w64 0 <-> SegModel.strcasecmp (a9_key x ei) lit = 0) ->
     SRr SEGS Wc (mkCfg (mkst rX2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst rT (Z_to_bv 64 (SIG SS___interceptor_trampoline_strcasecmp)) memT (seg_rom SEGS)) mdT) Q.
Proof.
intros n x ei kp vp lyc Sc Wc rT memT mdT lit ret Q HINV Hlit H10 H11 H1 Hret Hret2 HCONT.
pose proof HINV as (HC & HSTR & HKEY & HVAL & HRG).
pose proof HC as (HB & HM & HS & HL & HLT & HD0 & HDL).
destruct (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as HCL.
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (_ & (HJ & _) & HOBJ & _ & HFSH).
assert (E2 : Z_to_bv 5 2 = (2%bv : bv 5)) by (apply bv_eq; reflexivity).
assert (E3 : Z_to_bv 5 3 = (3%bv : bv 5)) by (apply bv_eq; reflexivity).
assert (E4 : Z_to_bv 5 4 = (4%bv : bv 5)) by (apply bv_eq; reflexivity).
assert (R2 : getr rT (Z_to_bv 5 2) = w64 (pf_s1 (y_v x)))
  by (eapply a5_rg_get; [exact HFI | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]).
assert (R3 : getr rT (Z_to_bv 5 3) = w64 (as_gp B))
  by (eapply a5_rg_get; [exact HFI | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]).
assert (R4 : getr rT (Z_to_bv 5 4) = w64 (as_tp B))
  by (eapply a5_rg_get; [exact HFI | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]).
rewrite E2 in R2. rewrite E3 in R3. rewrite E4 in R4.
assert (Hsp : spZ rT = pf_s1 (y_v x)) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Ho16 : (pf_s1 (y_v x) - pf_sp0 (y_v x)) mod 16 = 0).
{ pose proof (Z.div_mod (pf_s1 (y_v x)) 32 ltac:(lia)) as D1.
  pose proof (Z.div_mod (pf_sp0 (y_v x)) 16 ltac:(lia)) as D2.
  replace (pf_s1 (y_v x) - pf_sp0 (y_v x))
    with ((2 * (pf_s1 (y_v x) / 32) - pf_sp0 (y_v x) / 16) * 16) by lia.
  apply Z_mod_mult. }
assert (Hra : YK0s.ret_ok (getr rT 1)) by (rewrite H1; apply ret_ok_codeptr_v; [lia | exact Hret2]).
(* the key in buf *)
pose proof HKEY as (HKs & HKb1 & HKb2). unfold a9_buf, PF_O_BUF in HKb1, HKb2.
destruct (s4_astr_of_sa Wc memT kp (a9_key x ei) HKs) as (HKA & HKL & HKZ & HKT).
assert (HKn : ~ In 0 (a9_key x ei)) by exact (proj2 (proj1 HKs)).
(* the literal *)
pose proof HOBJ as (_ & _ & _ & _ & _ & _ & HLITS & _).
destruct (HLITS lit Hlit) as (Hl0 & Hls & Hlp & Hlr & Hli).
destruct (s4_astr_of_sa Wc memT _ lit Hls) as (HLA & HLL & HLZ & HLT0).
assert (HLn : ~ In 0 lit) by exact (proj2 (proj1 Hls)).
pose proof (Hlp lyc Sc Wc memT mdT HAR) as HLP.
pose proof (proj1 (Hli (seg_litA_rc lit + Z.of_nat (length lit)) ltac:(lia))) as Himg.
pose proof (pa_img_range _ Himg) as Hrg. unfold kImgEnd in Hrg.
(* the call *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False)
    (SIG SS___interceptor_trampoline_strcasecmp) Wc rT memT STK_reac_segconf_parse_file (pf_sp0 (y_v x))
    (seg_spec.RC_PARSE_W (p_c (y_v x))) (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x))
    (p_md (y_v x)) [(5, y_pos x)] lyc Sc mdT 0 (pf_s1 (y_v x) - pf_sp0 (y_v x)) (getr rT 1) _ HJ
    ltac:(rewrite Hsp; lia) Ho16 ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite SPF; unfold ESTACK; lia)
    eq_refl (fun a (H : False) => False_ind _ H)).
  apply (ASTRCASECMP fx lyc Sc Wc rT memT mdT kp (seg_litA_rc lit) (seg_spec.zb (a9_key x ei)) (seg_spec.zb lit)).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) STK_reac_segconf_parse_file (pf_sp0 (y_v x))
      (seg_spec.RC_PARSE_W (p_c (y_v x))) (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x))
      (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memT mdT 0 rT (pf_s1 (y_v x) - pf_sp0 (y_v x)) HJ
      ltac:(rewrite Hsp; lia) Ho16 ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite SPF; unfold ESTACK; lia)
      Hra R3 R4).
  - exact H10.
  - exact H11.
  - lia.
  - exact Hl0.
  - exact HKA.
  - exact HLA.
  - rewrite HKL. apply s4_read_ok_of_addr.
    + apply (s4_addr_buf _ (y_v x) (y_pos x)); [exact G | exact HFSH | unfold PF_O_BUF; lia | lia |
        unfold PF_O_BUF; lia].
    + lia.
    + intros a Ha. apply (s4_str_some _ kp (a9_key x ei) a HKs). lia.
    + rewrite Hsp. unfold ESTACK. lia.
  - rewrite HKL. apply amem_range_high; [lia| |lia].
    destruct G9 as [_ [Hlo | [Hhi1 Hhi2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
    [left; lia | right; lia].
  - rewrite HLL. apply s4_read_ok_of_addr.
    + exact HLP.
    + lia.
    + intros a Ha. apply (s4_str_some _ _ lit a Hls). lia.
    + rewrite Hsp. unfold ESTACK. lia.
  - rewrite HLL. unfold amem_range. left. rewrite C5. lia.
  - exact HKT.
  - exact HLT0.
  - exact (a5_rom B _ _ _ _ _ _ _ _ _ HB). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ & HK2).
rewrite H1.
apply HCONT.
- apply (s4_move n x ei kp vp lyc Sc Wc rT memT mdT regs2 mem2 md2 HINV HJ2).
  + intros a Ha Hn. apply HK2; [exact Ha | lia | intros Hf; exact Hf].
  + intros r Hr. apply HP2. exact (s4_S4_cs r Hr).
- exact (s4_res (getr regs2 10) (a9_key x ei) lit HKn HLn HKZ HLZ HQ).
Qed.

(* ======================= the walk ======================= *)
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* a listing object's atom is the literal's address (reac_segconf_parse.v lbl_atom) *)
Lemma s4_lit_atom : forall E (k i : nat) s, img_env VAL A_LIM E -> k = A_OBJ i ->
  (i < length seg_objs)%nat -> nth i seg_objs 0 = seg_litA_rc s -> (A_TEXT <= k < A_LIM)%nat ->
  ew E k = w64 (seg_litA_rc s).
Proof.
intros E k i s HE Hk Hi Hn Hr. rewrite (img_env_atomP E k HE Hr). subst k.
rewrite (OBJ i Hi), Hn. reflexivity.
Qed.

(* cur at K5: c is a live block (c > 0), cur is an entry of the table (at most 32 of 356 bytes in c) *)
Lemma s4_cp_rng : forall n x ei kp vp lyc Sc Wc rX memc mdc, INV_K5 B n x ei kp vp lyc Sc Wc rX memc mdc ->
  0 < p_c (y_v x) /\ pf_cur_ok (y_cf x) (y_cur x) /\ 0 <= a9_cp x < 2 ^ 64.
Proof.
intros n x ei kp vp lyc Sc Wc rX memc mdc ((HB & _ & HS & _) & _).
destruct (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & _ & _ & _ & _).
pose proof (a5_text B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & Hc).
pose proof HB as (_ & _ & (_ & _ & _ & (C0 & C1 & _) & _) & _).
destruct Hc as (b & m & Hb & H1 & H2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & _).
destruct HS as ((bs & _ & Henc) & Hok & _).
destruct Henc as (_ & Hlen32 & _).
unfold seg_spec.SEG_C_SIZE in C1.
unfold a9_cp, pf_cur_ptr. split; [lia|]. split; [exact Hok|].
destruct (y_cur x) as [i|]; [|lia].
unfold pf_cur_ok in Hok. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE. lia.
Qed.

(* the seed at a pc of the stretch, from K5's facts *)
Lemma s4_seed : forall n x ei kp vp lyc Sc (Wc : world SEGS) rX memc mdc (pc : Z),
  INV_K5 B n x ei kp vp lyc Sc Wc rX memc mdc ->
  st_ok_pi SEGS VAL (s4_E rX x) (s4_ss pc)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros n x ei kp vp lyc Sc Wc rX memc mdc pc ((HB & _) & _).
destruct (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G & _).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HRG.
destruct HB as (_ & _ & _ & HSL & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
assert (R2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 (y_v x)))
  by (eapply a5_rg_get; [exact HRG | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]).
assert (R8 : getr rX (Z_to_bv 5 8) = w64 (pf_sp0 (y_v x)))
  by (eapply a5_rg_get; [exact HRG | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 (y_v x)))
  by (eapply a5_rg_get; [exact HRG | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF)
  by (eapply a5_rg_get; [exact HRG | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]).
assert (H50 : rdword (rdW Wc memc) (pf_s1 (y_v x) + 0x50) = Some (pf_F (y_v x) (y_pos x) + PF_O_CN)).
{ exact (proj1 (Forall_forall _ _) HSL (0x50, pf_F (y_v x) (y_pos x) + PF_O_CN)
    ltac:(unfold PF_SL; cbn [In]; repeat (first [left; reflexivity | right]))). }
assert (E32 : ew (s4_E rX x) 32 = Z_to_bv 64 (pf_F (y_v x) (y_pos x) + PF_O_CN)).
{ unfold s4_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra rX _ 0). }
set (sp0 := pf_sp0 (y_v x)) in *. set (s1 := pf_s1 (y_v x)) in *. set (F := pf_F (y_v x) (y_pos x)) in *.
unfold PF_O_CN in *.
assert (U2 : bv_unsigned (ew (s4_E rX x) 2) = s1).
{ unfold s4_E. rewrite (ew_Eimg_Ereg_nat rX _ 2 (Z_to_bv 5 2) eq_refl), R2. unfold w64.
  apply unsigned_lit_small. lia. }
assert (U8 : bv_unsigned (ew (s4_E rX x) 8) = sp0).
{ unfold s4_E. rewrite (ew_Eimg_Ereg_nat rX _ 8 (Z_to_bv 5 8) eq_refl), R8. unfold w64.
  apply unsigned_lit_small. lia. }
assert (U9 : bv_unsigned (ew (s4_E rX x) 9) = s1).
{ unfold s4_E. rewrite (ew_Eimg_Ereg_nat rX _ 9 (Z_to_bv 5 9) eq_refl), R9. unfold w64.
  apply unsigned_lit_small. lia. }
assert (U22 : bv_unsigned (ew (s4_E rX x) 22) = SB).
{ unfold s4_E. rewrite (ew_Eimg_Ereg_nat rX _ 22 (Z_to_bv 5 22) eq_refl), R22. unfold w64, SB, SHADOW_OFF.
  apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold s4_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok, s4_slot_r.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS _ _ s1 0x50 8%N (SOff 32 0) (F + 32)).
  + cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  + lia.
  + exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ H50).
- unfold s4_slot_r. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
- split; [|split; exact I].
  cbn [s4_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U8, U9, U22.
  try change (2 ^ 5) with 32. try change (2 ^ 4) with 16.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  rewrite G3, G5. unfold SB. repeat split; lia.
Qed.

Ltac s4_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* after a run that writes nothing (trim_s.v ta_after): the environment agrees with E0 below k (HAE), the memory is
   the seed's (KM), every byte present at the seed is present (KP) *)
Ltac s4_after_core E0 HAE KM KP En msn :=
  lazymatch goal with
  | HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem msn)) |- _ =>
    lazymatch type of HAE with env_agree ?k _ _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in let KPn := fresh "KPn" in
    assert (HAEn : env_agree k E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H _) (ms_mem msn) a = aview SEGS (w_H _) _ a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          rewrite (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (fun _ => False) HFr);
          [ exact (KM a Ha)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
            destruct Hin
          | exact Ha | tauto ]);
    assert (KPn : forall a, apresent (w_H _) _ a -> apresent (w_H _) (ms_mem msn) a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (apresent_grows _ _ _ a HG (KP a Ha)));
    clear HFr HG HAE KM KP; rename HAEn into HAE; rename KMn into KM; rename KPn into KP;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
    end
  end.
Ltac s4_after E0 HAE KM KP :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn) |- _ => s4_after_core E0 HAE KM KP En msn
  | HS : st_ok _ ?En _ (restrict _ ?msn) |- _ => s4_after_core E0 HAE KM KP En msn
  end.
(* the seed at the cut (rX, memc) and the facts the runs below read of its environment *)
Ltac s4_prep HS HEI HA0 EE E32 E0 SHOK HAE KM KP rX x memc Wc :=
  assert (HEI : img_env VAL A_LIM (s4_E rX x)) by (unfold s4_E; apply Eimg_env);
  assert (HA0 : env_agree 32 (Ereg rX [Z_to_bv 64 (pf_F (y_v x) (y_pos x) + PF_O_CN)]) (s4_E rX x))
    by (split; [intros ? ?; unfold s4_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
  assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (s4_E rX x) k = getr rX r)
    by (intros ? ? ?; unfold s4_E; apply ew_Eimg_Ereg_nat; assumption);
  assert (E32 : ew (s4_E rX x) 32 = Z_to_bv 64 (pf_F (y_v x) (y_pos x) + PF_O_CN))
    by (unfold s4_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0));
  revert HS HEI HA0 EE E32; generalize (s4_E rX x) as E0; intros E0 HS HEI HA0 EE E32;
  assert (SHOK : sh_ok SEGS s4_Bx [] E0 (mrestrict (w_H Wc) memc)) by constructor;
  pose proof (env_agree_refl 33 E0) as HAE;
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity);
  assert (KP : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc a) by (intros; assumption).

(* the exits' cut predicates from K5's facts at the exit state *)
Lemma s4_ref3_of : forall n x ei kp vp lyc Sc Wc rY memY mdY,
  INV_K5 B n x ei kp vp lyc Sc Wc rY memY mdY -> y_cur x = None ->
  getr rY (Z_to_bv 5 10) = w64 (p_c (y_v x)) -> getr rY (Z_to_bv 5 11) = w64 (y_ln x + 1) ->
  getr rY (Z_to_bv 5 12) = w64 (seg_litA_rc F_outside) -> getr rY (Z_to_bv 5 13) = w64 kp ->
  INV_REF3 B n (y_v x) (y_pos x) lyc Sc Wc rY memY mdY (y_cf x) None (y_nm x) (y_o x) (y_ln x) (y_d x)
    F_outside (seg_litA_rc F_outside) [AS (a9_key x ei)] kp.
Proof.
intros n x ei kp vp lyc Sc Wc rY memY mdY ((HB & HM & HS & _) & _ & (HKs & HKb) & _ & HRG) Hcur H10 H11 H12 H13.
pose proof (a5_rg_get _ _ 20 (a9_cp x) HRG ltac:(s4_inl)) as H20.
unfold a9_cp in H20. rewrite Hcur in HS, H20.
apply a5_rg_app in HRG as [HRL HRG]. apply a5_rg_app in HRG as [HRM _].
split; [exact HB|]. split; [exact HM|]. split; [exact HS|].
split.
- right. exists (a9_key x ei). split; [right; split; reflexivity|]. split; [reflexivity|].
  split; [exact HKs | exact HKb].
- apply a5_rg_app. split; [exact HRL|]. apply a5_rg_app. split; [exact HRM|]. unfold pf_rg.
  apply Forall_cons; [exact H20|]. apply Forall_cons; [exact H10|]. apply Forall_cons; [exact H11|].
  apply Forall_cons; [exact H12|]. apply Forall_cons; [exact H13|]. apply Forall_nil.
Qed.

Lemma s4_kv_of : forall n x ei kp vp gi lyc Sc Wc rY memY mdY,
  INV_K5 B n x ei kp vp lyc Sc Wc rY memY mdY -> y_cur x = Some gi ->
  INV_KV B n (y_v x) (y_pos x) lyc Sc Wc rY memY mdY (y_cf x) (y_nm x) (y_o x) (y_ln x) (y_d x) gi kp vp
    (a9_key x ei) (a9_val x ei).
Proof.
intros n x ei kp vp gi lyc Sc Wc rY memY mdY ((HB & HM & HS & HL & _) & HSTR & (HKs & HKb) & (HVs & HVb) & HRG) Hcur.
unfold a9_cp in HL, HRG. rewrite Hcur in HS, HL, HRG.
split; [exact HB|]. split; [exact HM|]. split; [exact HS|].
split; [|split; [exact HL | exact HRG]].
split; [exists ei; split; [exact HSTR | split; reflexivity]|].
split; [exact HKs|]. split; [exact HKb|]. split; [exact HVs | exact HVb].
Qed.

Lemma s4_k9_of : forall n x ei kp vp gi f fa wp w lyc Sc Wc rY memY mdY,
  INV_K5 B n x ei kp vp lyc Sc Wc rY memY mdY -> y_cur x = Some gi ->
  a9_arg2 x ei f fa w -> a9_inbuf (rdW Wc memY) x wp w ->
  r_key (y_cf x) (y_cur x) (y_nm x) (y_ln x + 1) (a9_line x)
    = (refuse (y_cf x) (y_ln x + 1) f [AS (y_nm x); AS w], y_cur x, y_nm x) ->
  getr rY (Z_to_bv 5 10) = w64 (p_c (y_v x)) -> getr rY (Z_to_bv 5 11) = w64 (y_ln x + 1) ->
  getr rY (Z_to_bv 5 12) = w64 fa -> getr rY (Z_to_bv 5 13) = w64 (pf_F (y_v x) (y_pos x) + PF_O_CN) ->
  getr rY (Z_to_bv 5 14) = w64 wp ->
  INV_K9 B n x ei gi f fa wp w lyc Sc Wc rY memY mdY.
Proof.
intros n x ei kp vp gi f fa wp w lyc Sc Wc rY memY mdY (HC & HSTR & _ & _ & HRG) Hcur Harg Hw Hrk
  H10 H11 H12 H13 H14.
pose proof (a5_rg_get _ _ 20 (a9_cp x) HRG ltac:(s4_inl)) as H20.
apply a5_rg_app in HRG as [HRL HRG]. apply a5_rg_app in HRG as [HRM _].
split; [exact HC|]. split; [exact Hcur|]. split; [exact HSTR|]. split; [exact Harg|].
split; [exact Hw|]. split; [exact Hrk|].
apply a5_rg_app. split; [exact HRL|]. apply a5_rg_app. split; [exact HRM|]. unfold pf_rg.
apply Forall_cons; [exact H20|]. apply Forall_cons; [exact H10|]. apply Forall_cons; [exact H11|].
apply Forall_cons; [exact H12|]. apply Forall_cons; [exact H13|]. apply Forall_cons; [exact H14|].
apply Forall_nil.
Qed.

(* ---- K5 0x8814c: beqz s4. Taken (cur = NULL): 0x881bc-0x881d0 set a0 = c, a1 = lineno, a2 = F_outside,
   a3 = key and jump to REF3 (r_key's F_outside step, pf_a9_f.v a9_rkey_outs). Not taken: the first call. ---- *)
Lemma s4_K5 : forall n x ei kp vp lyc Sc Wc rX memc mdc,
  HA_REF3 B n ->
  (forall gi rX1 mem1 md1, y_cur x = Some gi -> INV_K5 B n x ei kp vp lyc Sc Wc rX1 mem1 md1 ->
     SRr SEGS Wc (cfg_at SEGS (BASE + A9_C1) rX1 mem1 md1) (a9_goal B x)) ->
  INV_K5 B n x ei kp vp lyc Sc Wc rX memc mdc ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A9_K5) rX memc mdc) (a9_goal B x).
Proof.
intros n x ei kp vp lyc Sc Wc rX memc mdc HREF3 HC1 HINV.
pose proof HINV as (HC & HSTR & HKEY & HVAL & HRG).
pose proof HC as (HB & _). pose proof HB as (_ & (HJ & _) & _).
destruct (s4_cp_rng n x ei kp vp lyc Sc Wc rX memc mdc HINV) as (Hc0 & Hok & Hcp).
pose proof (a5_rg_get _ _ 20 (a9_cp x) HRG ltac:(s4_inl)) as R20.
pose proof (s4_seed n x ei kp vp lyc Sc Wc rX memc mdc A9_K5 HINV) as HS.
s4_prep HS HEI HA0 EE E32 E0 SHOK HAE KM KP rX x memc Wc.
unfold cfg_at, w64.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s4 = 0: cur = NULL *)
  pose proof (s4_br_eq0 _ 20 _ _ (EE 20%nat (Z_to_bv 5 20) eq_refl) Hc) as L0. clear Hc.
  rewrite R20 in L0. unfold w64 in L0. rewrite unsigned_lit_small in L0 by lia. apply Z.eqb_eq in L0.
  assert (Hcur : y_cur x = None) by exact (proj1 (a9_cur_ptr_eq0 (p_c (y_v x)) (y_cf x) (y_cur x) Hc0 Hok) L0).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_REF3. { s4_awr. }
  s4_after E0 HAE KM KP.
  pose proof (s4_kept_pi _ _ _ _ rX _ HS (s4_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  pose proof (s4_move n x ei kp vp lyc Sc Wc rX memc mdc _ _ mdv HINV HJ (fun a Ha _ => KM a Ha) HK) as HINV'.
  prreg HS (Z_to_bv 5 10) N10. prreg HS (Z_to_bv 5 11) N11. prreg HS (Z_to_bv 5 12) N12. prreg HS (Z_to_bv 5 13) N13.
  rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl), (a5_rg_get _ _ 24 (p_c (y_v x)) HRG ltac:(s4_inl)) in N10.
  rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), (a5_rg_get _ _ 26 (y_ln x + 1) HRG ltac:(s4_inl)) in N11.
  rewrite (s4_lit_atom E0 289 48 F_outside HEI eq_refl ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(unfold A_TEXT, A_LIM; lia)) in N12.
  rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), (a5_rg_get _ _ 23 kp HRG ltac:(s4_inl)) in N13.
  pmkst HS.
  unfold a9_goal. rewrite Hcur, (a9_rkey_outs _ _ _ _ ei HSTR).
  exact (HREF3 fx (y_v x) (y_pos x) lyc Sc Wc _ _ mdv (y_cf x) None (y_nm x) (y_o x) (y_ln x) (y_d x)
    F_outside (seg_litA_rc F_outside) [AS (a9_key x ei)] kp
    (s4_ref3_of n x ei kp vp lyc Sc Wc _ _ mdv HINV' Hcur N10 N11 N12 N13)).
- (* s4 <> 0: cur = Some gi, on to the first strcasecmp *)
  pose proof (s4_br_eq0 _ 20 _ _ (EE 20%nat (Z_to_bv 5 20) eq_refl) Hc) as L0. clear Hc.
  rewrite R20 in L0. unfold w64 in L0. rewrite unsigned_lit_small in L0 by lia. apply Z.eqb_neq in L0.
  assert (Hcur' : exists gi, y_cur x = Some gi).
  { destruct (y_cur x) as [gi|] eqn:Hcur; [exists gi; reflexivity|].
    exfalso. apply L0. unfold a9_cp. rewrite Hcur. reflexivity. }
  destruct Hcur' as (gi & Hcur).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A9_C1. { s4_awr. }
  s4_after E0 HAE KM KP.
  pose proof (s4_kept_pi _ _ _ _ rX _ HS (s4_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  pose proof (s4_move n x ei kp vp lyc Sc Wc rX memc mdc _ _ mdv HINV HJ (fun a Ha _ => KM a Ha) HK) as HINV'.
  pmkst HS.
  exact (HC1 gi _ _ mdv Hcur HINV').
Qed.

(* ---- C1 0x88150: a1 = "role" (listing object 43), a0 = s7 = key, jal strcasecmp; the call by s4_call ---- *)
Lemma s4_C1 : forall n x ei kp vp lyc Sc Wc rX memc mdc,
  (forall rX2 mem2 md2, INV_K5 B n x ei kp vp lyc Sc Wc rX2 mem2 md2 ->
     (getr rX2 10 = w64 0 <-> SegModel.strcasecmp (a9_key x ei) S_role = 0) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + A9_R1) rX2 mem2 md2) (a9_goal B x)) ->
  INV_K5 B n x ei kp vp lyc Sc Wc rX memc mdc ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A9_C1) rX memc mdc) (a9_goal B x).
Proof.
intros n x ei kp vp lyc Sc Wc rX memc mdc HR HINV.
pose proof HINV as (HC & HSTR & HKEY & HVAL & HRG).
pose proof HC as (HB & _). pose proof HB as (_ & (HJ & _) & _).
pose proof (s4_seed n x ei kp vp lyc Sc Wc rX memc mdc A9_C1 HINV) as HS.
s4_prep HS HEI HA0 EE E32 E0 SHOK HAE KM KP rX x memc Wc.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK Bspan. { s4_awr. }
s4_after E0 HAE KM KP.
pose proof (s4_kept_ok _ _ _ _ rX _ HS (s4_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
pose proof (s4_move n x ei kp vp lyc Sc Wc rX memc mdc _ _ mdv HINV HJ (fun a Ha _ => KM a Ha) HK) as HINV'.
prreg HS (1%bv : bv 5) N1. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), (a5_rg_get _ _ 23 kp HRG ltac:(s4_inl)) in N10.
rewrite (s4_lit_atom E0 284 43 S_role HEI eq_refl ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(unfold A_TEXT, A_LIM; lia)) in N11.
pmkst HS.
eapply (s4_call n x ei kp vp lyc Sc Wc _ _ mdv S_role _ _ HINV' ltac:(s4_inlits) N10 N11 N1); [lia | reflexivity |].
intros rX2 mem2 md2 HINV2 HRES. exact (HR rX2 mem2 md2 HINV2 HRES).
Qed.

(* ---- R1 0x88160: beqz a0. Taken: strcasecmp key "role" = 0, ROLE. Not taken: the second call. ---- *)
Lemma s4_R1 : forall n x ei kp vp gi lyc Sc Wc rX memc mdc,
  HA_ROLE B n ->
  (SegModel.strcasecmp (a9_key x ei) S_role <> 0 ->
   forall rX1 mem1 md1, INV_K5 B n x ei kp vp lyc Sc Wc rX1 mem1 md1 ->
     SRr SEGS Wc (cfg_at SEGS (BASE + A9_C2) rX1 mem1 md1) (a9_goal B x)) ->
  y_cur x = Some gi ->
  INV_K5 B n x ei kp vp lyc Sc Wc rX memc mdc ->
  (getr rX 10 = w64 0 <-> SegModel.strcasecmp (a9_key x ei) S_role = 0) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A9_R1) rX memc mdc) (a9_goal B x).
Proof.
intros n x ei kp vp gi lyc Sc Wc rX memc mdc HROLE HC2 Hcur HINV HRES.
pose proof HINV as (HC & HSTR & HKEY & HVAL & HRG).
pose proof HC as (HB & _). pose proof HB as (_ & (HJ & _) & _).
pose proof (s4_seed n x ei kp vp lyc Sc Wc rX memc mdc A9_R1 HINV) as HS.
s4_prep HS HEI HA0 EE E32 E0 SHOK HAE KM KP rX x memc Wc.
unfold cfg_at, w64.
psrr_branch_tok RUN BR HS SHOK Bspan.
- pose proof (s4_cmp_true _ _ HRES (s4_br_eq0 _ 10 _ _ (EE 10%nat (10%bv : bv 5) eq_refl) Hc)) as Hr. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_ROLE. { s4_awr. }
  s4_after E0 HAE KM KP.
  pose proof (s4_kept_pi _ _ _ _ rX _ HS (s4_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  pose proof (s4_move n x ei kp vp lyc Sc Wc rX memc mdc _ _ mdv HINV HJ (fun a Ha _ => KM a Ha) HK) as HINV'.
  pmkst HS.
  unfold a9_goal. rewrite Hcur.
  exact (HROLE fx (y_v x) (y_pos x) lyc Sc Wc _ _ mdv (y_cf x) (y_nm x) (y_o x) (y_ln x) (y_d x) gi kp vp
    (a9_key x ei) (a9_val x ei) (s4_kv_of n x ei kp vp gi lyc Sc Wc _ _ mdv HINV' Hcur) Hr).
- pose proof (s4_cmp_false _ _ HRES (s4_br_eq0 _ 10 _ _ (EE 10%nat (10%bv : bv 5) eq_refl) Hc)) as Hr. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A9_C2. { s4_awr. }
  s4_after E0 HAE KM KP.
  pose proof (s4_kept_pi _ _ _ _ rX _ HS (s4_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  pose proof (s4_move n x ei kp vp lyc Sc Wc rX memc mdc _ _ mdv HINV HJ (fun a Ha _ => KM a Ha) HK) as HINV'.
  pmkst HS.
  exact (HC2 Hr _ _ mdv HINV').
Qed.

(* ---- C2 0x88164: a1 = "model" (listing object 44) ---- *)
Lemma s4_C2 : forall n x ei kp vp lyc Sc Wc rX memc mdc,
  (forall rX2 mem2 md2, INV_K5 B n x ei kp vp lyc Sc Wc rX2 mem2 md2 ->
     (getr rX2 10 = w64 0 <-> SegModel.strcasecmp (a9_key x ei) S_model = 0) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + A9_R2) rX2 mem2 md2) (a9_goal B x)) ->
  INV_K5 B n x ei kp vp lyc Sc Wc rX memc mdc ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A9_C2) rX memc mdc) (a9_goal B x).
Proof.
intros n x ei kp vp lyc Sc Wc rX memc mdc HR HINV.
pose proof HINV as (HC & HSTR & HKEY & HVAL & HRG).
pose proof HC as (HB & _). pose proof HB as (_ & (HJ & _) & _).
pose proof (s4_seed n x ei kp vp lyc Sc Wc rX memc mdc A9_C2 HINV) as HS.
s4_prep HS HEI HA0 EE E32 E0 SHOK HAE KM KP rX x memc Wc.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK Bspan. { s4_awr. }
s4_after E0 HAE KM KP.
pose proof (s4_kept_ok _ _ _ _ rX _ HS (s4_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
pose proof (s4_move n x ei kp vp lyc Sc Wc rX memc mdc _ _ mdv HINV HJ (fun a Ha _ => KM a Ha) HK) as HINV'.
prreg HS (1%bv : bv 5) N1. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), (a5_rg_get _ _ 23 kp HRG ltac:(s4_inl)) in N10.
rewrite (s4_lit_atom E0 285 44 S_model HEI eq_refl ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(unfold A_TEXT, A_LIM; lia)) in N11.
pmkst HS.
eapply (s4_call n x ei kp vp lyc Sc Wc _ _ mdv S_model _ _ HINV' ltac:(s4_inlits) N10 N11 N1); [lia | reflexivity |].
intros rX2 mem2 md2 HINV2 HRES. exact (HR rX2 mem2 md2 HINV2 HRES).
Qed.

(* ---- R2 0x88174: beqz a0. Taken: "model" (and not "role"), MODEL. Not taken: the third call. ---- *)
Lemma s4_R2 : forall n x ei kp vp gi lyc Sc Wc rX memc mdc,
  HA_MODEL B n ->
  SegModel.strcasecmp (a9_key x ei) S_role <> 0 ->
  (SegModel.strcasecmp (a9_key x ei) S_model <> 0 ->
   forall rX1 mem1 md1, INV_K5 B n x ei kp vp lyc Sc Wc rX1 mem1 md1 ->
     SRr SEGS Wc (cfg_at SEGS (BASE + A9_C3) rX1 mem1 md1) (a9_goal B x)) ->
  y_cur x = Some gi ->
  INV_K5 B n x ei kp vp lyc Sc Wc rX memc mdc ->
  (getr rX 10 = w64 0 <-> SegModel.strcasecmp (a9_key x ei) S_model = 0) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A9_R2) rX memc mdc) (a9_goal B x).
Proof.
intros n x ei kp vp gi lyc Sc Wc rX memc mdc HMODEL N1 HC3 Hcur HINV HRES.
pose proof HINV as (HC & HSTR & HKEY & HVAL & HRG).
pose proof HC as (HB & _). pose proof HB as (_ & (HJ & _) & _).
pose proof (s4_seed n x ei kp vp lyc Sc Wc rX memc mdc A9_R2 HINV) as HS.
s4_prep HS HEI HA0 EE E32 E0 SHOK HAE KM KP rX x memc Wc.
unfold cfg_at, w64.
psrr_branch_tok RUN BR HS SHOK Bspan.
- pose proof (s4_cmp_true _ _ HRES (s4_br_eq0 _ 10 _ _ (EE 10%nat (10%bv : bv 5) eq_refl) Hc)) as Hr. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_MODEL. { s4_awr. }
  s4_after E0 HAE KM KP.
  pose proof (s4_kept_pi _ _ _ _ rX _ HS (s4_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  pose proof (s4_move n x ei kp vp lyc Sc Wc rX memc mdc _ _ mdv HINV HJ (fun a Ha _ => KM a Ha) HK) as HINV'.
  pmkst HS.
  unfold a9_goal. rewrite Hcur.
  exact (HMODEL fx (y_v x) (y_pos x) lyc Sc Wc _ _ mdv (y_cf x) (y_nm x) (y_o x) (y_ln x) (y_d x) gi kp vp
    (a9_key x ei) (a9_val x ei) (s4_kv_of n x ei kp vp gi lyc Sc Wc _ _ mdv HINV' Hcur) N1 Hr).
- pose proof (s4_cmp_false _ _ HRES (s4_br_eq0 _ 10 _ _ (EE 10%nat (10%bv : bv 5) eq_refl) Hc)) as Hr. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A9_C3. { s4_awr. }
  s4_after E0 HAE KM KP.
  pose proof (s4_kept_pi _ _ _ _ rX _ HS (s4_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  pose proof (s4_move n x ei kp vp lyc Sc Wc rX memc mdc _ _ mdv HINV HJ (fun a Ha _ => KM a Ha) HK) as HINV'.
  pmkst HS.
  exact (HC3 Hr _ _ mdv HINV').
Qed.

(* ---- C3 0x88178: a1 = "ignore" (listing object 45) ---- *)
Lemma s4_C3 : forall n x ei kp vp lyc Sc Wc rX memc mdc,
  (forall rX2 mem2 md2, INV_K5 B n x ei kp vp lyc Sc Wc rX2 mem2 md2 ->
     (getr rX2 10 = w64 0 <-> SegModel.strcasecmp (a9_key x ei) S_ignore = 0) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + A9_R3) rX2 mem2 md2) (a9_goal B x)) ->
  INV_K5 B n x ei kp vp lyc Sc Wc rX memc mdc ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A9_C3) rX memc mdc) (a9_goal B x).
Proof.
intros n x ei kp vp lyc Sc Wc rX memc mdc HR HINV.
pose proof HINV as (HC & HSTR & HKEY & HVAL & HRG).
pose proof HC as (HB & _). pose proof HB as (_ & (HJ & _) & _).
pose proof (s4_seed n x ei kp vp lyc Sc Wc rX memc mdc A9_C3 HINV) as HS.
s4_prep HS HEI HA0 EE E32 E0 SHOK HAE KM KP rX x memc Wc.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK Bspan. { s4_awr. }
s4_after E0 HAE KM KP.
pose proof (s4_kept_ok _ _ _ _ rX _ HS (s4_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
pose proof (s4_move n x ei kp vp lyc Sc Wc rX memc mdc _ _ mdv HINV HJ (fun a Ha _ => KM a Ha) HK) as HINV'.
prreg HS (1%bv : bv 5) N1. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), (a5_rg_get _ _ 23 kp HRG ltac:(s4_inl)) in N10.
rewrite (s4_lit_atom E0 286 45 S_ignore HEI eq_refl ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(unfold A_TEXT, A_LIM; lia)) in N11.
pmkst HS.
eapply (s4_call n x ei kp vp lyc Sc Wc _ _ mdv S_ignore _ _ HINV' ltac:(s4_inlits) N10 N11 N1); [lia | reflexivity |].
intros rX2 mem2 md2 HINV2 HRES. exact (HR rX2 mem2 md2 HINV2 HRES).
Qed.

(* ---- R3 0x88188: beqz a0. Taken: "ignore" (and neither "role" nor "model"), IGN. Not taken: the fourth call. ---- *)
Lemma s4_R3 : forall n x ei kp vp gi lyc Sc Wc rX memc mdc,
  HA_IGN B n ->
  SegModel.strcasecmp (a9_key x ei) S_role <> 0 -> SegModel.strcasecmp (a9_key x ei) S_model <> 0 ->
  (SegModel.strcasecmp (a9_key x ei) S_ignore <> 0 ->
   forall rX1 mem1 md1, INV_K5 B n x ei kp vp lyc Sc Wc rX1 mem1 md1 ->
     SRr SEGS Wc (cfg_at SEGS (BASE + A9_C4) rX1 mem1 md1) (a9_goal B x)) ->
  y_cur x = Some gi ->
  INV_K5 B n x ei kp vp lyc Sc Wc rX memc mdc ->
  (getr rX 10 = w64 0 <-> SegModel.strcasecmp (a9_key x ei) S_ignore = 0) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A9_R3) rX memc mdc) (a9_goal B x).
Proof.
intros n x ei kp vp gi lyc Sc Wc rX memc mdc HIGN N1 N2 HC4 Hcur HINV HRES.
pose proof HINV as (HC & HSTR & HKEY & HVAL & HRG).
pose proof HC as (HB & _). pose proof HB as (_ & (HJ & _) & _).
pose proof (s4_seed n x ei kp vp lyc Sc Wc rX memc mdc A9_R3 HINV) as HS.
s4_prep HS HEI HA0 EE E32 E0 SHOK HAE KM KP rX x memc Wc.
unfold cfg_at, w64.
psrr_branch_tok RUN BR HS SHOK Bspan.
- pose proof (s4_cmp_true _ _ HRES (s4_br_eq0 _ 10 _ _ (EE 10%nat (10%bv : bv 5) eq_refl) Hc)) as Hr. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_IGN. { s4_awr. }
  s4_after E0 HAE KM KP.
  pose proof (s4_kept_pi _ _ _ _ rX _ HS (s4_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  pose proof (s4_move n x ei kp vp lyc Sc Wc rX memc mdc _ _ mdv HINV HJ (fun a Ha _ => KM a Ha) HK) as HINV'.
  pmkst HS.
  unfold a9_goal. rewrite Hcur.
  exact (HIGN fx (y_v x) (y_pos x) lyc Sc Wc _ _ mdv (y_cf x) (y_nm x) (y_o x) (y_ln x) (y_d x) gi kp vp
    (a9_key x ei) (a9_val x ei) (s4_kv_of n x ei kp vp gi lyc Sc Wc _ _ mdv HINV' Hcur) N1 N2 Hr).
- pose proof (s4_cmp_false _ _ HRES (s4_br_eq0 _ 10 _ _ (EE 10%nat (10%bv : bv 5) eq_refl) Hc)) as Hr. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A9_C4. { s4_awr. }
  s4_after E0 HAE KM KP.
  pose proof (s4_kept_pi _ _ _ _ rX _ HS (s4_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  pose proof (s4_move n x ei kp vp lyc Sc Wc rX memc mdc _ _ mdv HINV HJ (fun a Ha _ => KM a Ha) HK) as HINV'.
  pmkst HS.
  exact (HC4 Hr _ _ mdv HINV').
Qed.

(* ---- C4 0x8818c: a1 = "knock" (listing object 46) ---- *)
Lemma s4_C4 : forall n x ei kp vp lyc Sc Wc rX memc mdc,
  (forall rX2 mem2 md2, INV_K5 B n x ei kp vp lyc Sc Wc rX2 mem2 md2 ->
     (getr rX2 10 = w64 0 <-> SegModel.strcasecmp (a9_key x ei) S_knock = 0) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + A9_R4) rX2 mem2 md2) (a9_goal B x)) ->
  INV_K5 B n x ei kp vp lyc Sc Wc rX memc mdc ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A9_C4) rX memc mdc) (a9_goal B x).
Proof.
intros n x ei kp vp lyc Sc Wc rX memc mdc HR HINV.
pose proof HINV as (HC & HSTR & HKEY & HVAL & HRG).
pose proof HC as (HB & _). pose proof HB as (_ & (HJ & _) & _).
pose proof (s4_seed n x ei kp vp lyc Sc Wc rX memc mdc A9_C4 HINV) as HS.
s4_prep HS HEI HA0 EE E32 E0 SHOK HAE KM KP rX x memc Wc.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK Bspan. { s4_awr. }
s4_after E0 HAE KM KP.
pose proof (s4_kept_ok _ _ _ _ rX _ HS (s4_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
pose proof (s4_move n x ei kp vp lyc Sc Wc rX memc mdc _ _ mdv HINV HJ (fun a Ha _ => KM a Ha) HK) as HINV'.
prreg HS (1%bv : bv 5) N1. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), (a5_rg_get _ _ 23 kp HRG ltac:(s4_inl)) in N10.
rewrite (s4_lit_atom E0 287 46 S_knock HEI eq_refl ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(unfold A_TEXT, A_LIM; lia)) in N11.
pmkst HS.
eapply (s4_call n x ei kp vp lyc Sc Wc _ _ mdv S_knock _ _ HINV' ltac:(s4_inlits) N10 N11 N1); [lia | reflexivity |].
intros rX2 mem2 md2 HINV2 HRES. exact (HR rX2 mem2 md2 HINV2 HRES).
Qed.

(* ---- R4 0x8819c: beqz a0. Taken ("knock"): 0x884f8-0x8850c set a2 = F_knock, a3 = slot 0x50 = cur_name,
   a4 = s9 = val and fall into K9. Not taken: 0x881a0-0x881b8 set a2 = F_nokey, a3 = cur_name, a4 = s7 = key
   and jump to K9. a0 = s8 = c and a1 = s10 = lineno on both (pf_a9_f.v a9_rkey_knock / a9_rkey_nokey). ---- *)
Lemma s4_R4 : forall n x ei kp vp gi lyc Sc Wc rX memc mdc,
  from_K9 B n -> y_cur x = Some gi ->
  SegModel.strcasecmp (a9_key x ei) S_role <> 0 -> SegModel.strcasecmp (a9_key x ei) S_model <> 0 ->
  SegModel.strcasecmp (a9_key x ei) S_ignore <> 0 ->
  INV_K5 B n x ei kp vp lyc Sc Wc rX memc mdc ->
  (getr rX 10 = w64 0 <-> SegModel.strcasecmp (a9_key x ei) S_knock = 0) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A9_R4) rX memc mdc) (a9_goal B x).
Proof.
intros n x ei kp vp gi lyc Sc Wc rX memc mdc HK9 Hcur N1 N2 N3 HINV HRES.
pose proof HINV as (HC & HSTR & HKEY & HVAL & HRG).
pose proof HC as (HB & _). pose proof HB as (_ & (HJ & _) & _).
pose proof (s4_seed n x ei kp vp lyc Sc Wc rX memc mdc A9_R4 HINV) as HS.
s4_prep HS HEI HA0 EE E32 E0 SHOK HAE KM KP rX x memc Wc.
unfold cfg_at, w64.
psrr_branch_tok RUN BR HS SHOK Bspan.
- pose proof (s4_cmp_true _ _ HRES (s4_br_eq0 _ 10 _ _ (EE 10%nat (10%bv : bv 5) eq_refl) Hc)) as Hr. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A9_K9. { s4_awr. }
  s4_after E0 HAE KM KP.
  pose proof (s4_kept_pi _ _ _ _ rX _ HS (s4_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  pose proof (s4_move n x ei kp vp lyc Sc Wc rX memc mdc _ _ mdv HINV HJ (fun a Ha _ => KM a Ha) HK) as HINV'.
  prreg HS (Z_to_bv 5 10) N10. prreg HS (Z_to_bv 5 11) N11. prreg HS (Z_to_bv 5 12) N12.
  prreg HS (Z_to_bv 5 13) N13. prreg HS (Z_to_bv 5 14) N14.
  rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl), (a5_rg_get _ _ 24 (p_c (y_v x)) HRG ltac:(s4_inl)) in N10.
  rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), (a5_rg_get _ _ 26 (y_ln x + 1) HRG ltac:(s4_inl)) in N11.
  rewrite (s4_lit_atom E0 302 61 F_knock HEI eq_refl ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(unfold A_TEXT, A_LIM; lia)) in N12.
  rewrite E32 in N13.
  rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl), (a5_rg_get _ _ 25 vp HRG ltac:(s4_inl)) in N14.
  pose proof HINV' as (_ & _ & _ & HVAL' & _).
  pmkst HS.
  exact (HK9 x ei gi F_knock (seg_litA_rc F_knock) vp (a9_val x ei) lyc Sc Wc _ _ mdv
    (s4_k9_of n x ei kp vp gi F_knock (seg_litA_rc F_knock) vp (a9_val x ei) lyc Sc Wc _ _ mdv HINV' Hcur
      (or_introl (conj eq_refl (conj eq_refl eq_refl))) HVAL'
      ltac:(rewrite Hcur; exact (a9_rkey_knock _ _ _ _ _ ei HSTR N1 N2 N3 Hr))
      N10 N11 N12 N13 N14)).
- pose proof (s4_cmp_false _ _ HRES (s4_br_eq0 _ 10 _ _ (EE 10%nat (10%bv : bv 5) eq_refl) Hc)) as Hr. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A9_K9. { s4_awr. }
  s4_after E0 HAE KM KP.
  pose proof (s4_kept_pi _ _ _ _ rX _ HS (s4_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  pose proof (s4_move n x ei kp vp lyc Sc Wc rX memc mdc _ _ mdv HINV HJ (fun a Ha _ => KM a Ha) HK) as HINV'.
  prreg HS (Z_to_bv 5 10) N10. prreg HS (Z_to_bv 5 11) N11. prreg HS (Z_to_bv 5 12) N12.
  prreg HS (Z_to_bv 5 13) N13. prreg HS (Z_to_bv 5 14) N14.
  rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl), (a5_rg_get _ _ 24 (p_c (y_v x)) HRG ltac:(s4_inl)) in N10.
  rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), (a5_rg_get _ _ 26 (y_ln x + 1) HRG ltac:(s4_inl)) in N11.
  rewrite (s4_lit_atom E0 288 47 F_nokey HEI eq_refl ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(unfold A_TEXT, A_LIM; lia)) in N12.
  rewrite E32 in N13.
  rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), (a5_rg_get _ _ 23 kp HRG ltac:(s4_inl)) in N14.
  pose proof HINV' as (_ & _ & HKEY' & _ & _).
  pmkst HS.
  exact (HK9 x ei gi F_nokey (seg_litA_rc F_nokey) kp (a9_key x ei) lyc Sc Wc _ _ mdv
    (s4_k9_of n x ei kp vp gi F_nokey (seg_litA_rc F_nokey) kp (a9_key x ei) lyc Sc Wc _ _ mdv HINV' Hcur
      (or_intror (conj eq_refl (conj eq_refl eq_refl))) HKEY'
      ltac:(rewrite Hcur; exact (a9_rkey_nokey _ _ _ _ _ ei HSTR N1 N2 N3 Hr))
      N10 N11 N12 N13 N14)).
Qed.

(* ======================= the stretch ======================= *)
Lemma a9_sD : SA9_D B.
Proof.
unfold SA9_D. intros n HREF3 HROLE HMODEL HIGN HK9.
unfold from_K5, a9_from. intros x ei kp vp lyc Sc Wc rX memc mdc HINV.
apply (s4_K5 n x ei kp vp lyc Sc Wc rX memc mdc HREF3); [|exact HINV].
intros gi rX1 mem1 md1 Hcur HINV1.
apply (s4_C1 n x ei kp vp lyc Sc Wc rX1 mem1 md1); [|exact HINV1].
intros rX2 mem2 md2 HINV2 HR1.
apply (s4_R1 n x ei kp vp gi lyc Sc Wc rX2 mem2 md2 HROLE); [| exact Hcur | exact HINV2 | exact HR1].
intros N1 rX3 mem3 md3 HINV3.
apply (s4_C2 n x ei kp vp lyc Sc Wc rX3 mem3 md3); [|exact HINV3].
intros rX4 mem4 md4 HINV4 HR2.
apply (s4_R2 n x ei kp vp gi lyc Sc Wc rX4 mem4 md4 HMODEL N1); [| exact Hcur | exact HINV4 | exact HR2].
intros N2 rX5 mem5 md5 HINV5.
apply (s4_C3 n x ei kp vp lyc Sc Wc rX5 mem5 md5); [|exact HINV5].
intros rX6 mem6 md6 HINV6 HR3.
apply (s4_R3 n x ei kp vp gi lyc Sc Wc rX6 mem6 md6 HIGN N1 N2); [| exact Hcur | exact HINV6 | exact HR3].
intros N3 rX7 mem7 md7 HINV7.
apply (s4_C4 n x ei kp vp lyc Sc Wc rX7 mem7 md7); [|exact HINV7].
intros rX8 mem8 md8 HINV8 HR4.
exact (s4_R4 n x ei kp vp gi lyc Sc Wc rX8 mem8 md8 HK9 Hcur N1 N2 N3 HINV8 HR4).
Qed.

End e.
End f.
End d.
