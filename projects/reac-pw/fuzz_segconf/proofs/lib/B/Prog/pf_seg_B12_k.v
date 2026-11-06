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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 566 of its 615 lines of code are new or changed and 404 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the kit of segment B12 of
   reac_segconf_parse_file's walk (the ignore key, reac_segconf.c:271-280 with parse_bool R:88-99 inlined; cut IGN
   0x887e0 -> KREF 0x889a0 (bad ignore) or PROV2 0x88e4c; statement S_B12 of lib/B/Prog/pf_pieces.v). The B12 segment lane
   of the image-B G3 walk owner, 2026-10-30. proves no function (kind: segment kit). ADAPTED from a working branch
   (lib/A/Prog/pf_a12_pure.v, pf_a12_keep.v: the spine and the keep across a call) and the unit owner's UBSan piece walk
   lib/U/Prog/pf_p8.v (the six tests and the trap T31), re-derived on image B's code
   (the neutral excerpt reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s).

   THE CODE (101 instructions: 0x887e0-0x888b8, 0x88df0-0x88e48, and the cold check arms 0x89044-0x89060,
   0x89070-0x89078, 0x890b4-0x890bc, 0x890f8-0x89100, 0x892ac-0x892b0, 0x892bc-0x892c0, 0x892d8, 0x892f4):
     IGN 0x887e0  a1 = "yes" (0x21b80, listing object 50), s7 = val (slot 0x70), strcasecmp (0x887f0), s3 = 1,
                  `beqz a0` -> 0x88df4 (b = 1)
         0x887fc  a1 = "true" (object 51), strcasecmp (0x88808), `beqz a0` -> 0x88df4
         0x88810  check B#22 (load1 val[0]; slow arm 0x89070), a3 = cur (slot 0xc0), a4 = val, s7 = val[0],
                  `bne s7,'1'` -> 0x88850; check B#23 (load1 val[1]; slow arm 0x890b4), `beqz val[1]` -> 0x88df8
     NO  0x88850  a1 = "no" (object 52), s3 = val, strcasecmp (0x88860), `beqz a0` -> 0x88df0 (b = 0);
                  a1 = "false" (object 53), strcasecmp (0x88874), `beqz a0` -> 0x88df0;
         0x8887c  a4 = val (slot 0x70), `bne s7,'0'` -> BAD; check B#24 (load1 val[1]; slow arm 0x890f8),
                  `beqz val[1]` -> 0x88df0
     BAD 0x888a4  a2 = F_badignore (0x21900, object 54), a0 = c (slot 0xc8), a1 = s6, a3 = cur_name (slot 0x40),
                  `j` KREF 0x889a0
     0x88df0 s3 = 0; 0x88df4 a3 = cur (slot 0xc0);
     STORE 0x88df8  T31 `andi a0,a3,3; bnez a0` -> unimp 0x891c8 (not taken: cur = c + 356 gi, c mod 16 = 0);
                  check B#33 (store4 cur + 24; slow arm 0x89044), `sw s3,24(a3)` (ignore = b); check B#34 (store4
                  cur + 28; slow arm 0x89054), `sw 1,28(a3)` (ignore_set = 1); a0 = cur + 0x100, a2 = "%s"
                  (object 35), a1 = 96, a3 = c->reading (slot 0x48); falls into PROV2 0x88e4c.
   UBSan trap sites: T31 only (0x88dfc). Inline checks: B#22, B#23, B#24 (load1, val in buf), B#33, B#34 (store4,
   cur in the block c). Calls: strcasecmp x4 (the listing's trampoline, RtSeg.astrcasecmp_realizes).

   THE PIECES (each re-seeds a symbolic state at its cut and runs the token executor over the listing):
     pf_seg_B12_s.v STORE 0x88df8 -> PROV2;  pf_seg_B12_b.v BAD 0x888a4 -> KREF (both over the keep family
     pf_seg_B12_x.v);  pf_seg_B12_n.v NO 0x88850, R3 0x88864, R4 0x88878;  pf_seg_B12_e.v IGN, R1 0x887f4,
     R2 0x8880c;  pf_seg_B12.v S_B12_holds.
   Every internal cut carries b12_ent (the cut IGN's state INV_KV at the entry memory memc, H_IGN's key tests and
   the exits' HA_KREF / HA_PROV2) and b12_mid (the journal at the current memory, every byte outside the
   strcasecmp windows [s1 - 2 * ESTACK, s1) as at IGN, the registers B12_KEPT as at IGN). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require pf_p8_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module P8 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.pf_p8_lemmas.

(** ** The cut points of the segment, as listing offsets (BASE + AF_reac_segconf_parse_file = 0x87e38) *)
Definition B12_R1 : Z := AF_reac_segconf_parse_file + 0x9bc.     (* 0x887f4 after strcasecmp "yes" *)
Definition B12_R2 : Z := AF_reac_segconf_parse_file + 0x9d4.     (* 0x8880c after strcasecmp "true" *)
Definition B12_NO : Z := AF_reac_segconf_parse_file + 0xa18.     (* 0x88850 the "no" arm *)
Definition B12_R3 : Z := AF_reac_segconf_parse_file + 0xa2c.     (* 0x88864 after strcasecmp "no" *)
Definition B12_R4 : Z := AF_reac_segconf_parse_file + 0xa40.     (* 0x88878 after strcasecmp "false" *)
Definition B12_BAD : Z := AF_reac_segconf_parse_file + 0xa6c.    (* 0x888a4 the bad ignore's arguments *)
Definition B12_STORE : Z := AF_reac_segconf_parse_file + 0xfc0.  (* 0x88df8 T31, the two stores *)
Lemma b12_pcs :
  seg_text + PF_IGN = 0x887e0 /\ seg_text + B12_R1 = 0x887f4 /\ seg_text + B12_R2 = 0x8880c /\
  seg_text + B12_NO = 0x88850 /\ seg_text + B12_R3 = 0x88864 /\ seg_text + B12_R4 = 0x88878 /\
  seg_text + B12_BAD = 0x888a4 /\ seg_text + B12_STORE = 0x88df8 /\ seg_text + PF_KREF = 0x889a0 /\
  seg_text + PF_PROV2 = 0x88e4c.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* the literals the segment forms (listing objects 50 .. 54 and 35, B's SegAddr) and their image-B addresses *)
Lemma b12_lits :
  seg_litA_rc S_yes = 0x21b80 /\ seg_litA_rc S_true = 0x21ba0 /\ seg_litA_rc S_no = 0x21bc0 /\
  seg_litA_rc S_false = 0x21be0 /\ seg_litA_rc F_badignore = 0x21900 /\ seg_litA_rc F_s = 0x21340 /\
  nth 50 seg_objs 0 = 0x21b80 /\ nth 51 seg_objs 0 = 0x21ba0 /\ nth 52 seg_objs 0 = 0x21bc0 /\
  nth 53 seg_objs 0 = 0x21be0 /\ nth 54 seg_objs 0 = 0x21900 /\ nth 35 seg_objs 0 = 0x21340 /\
  (54 < length seg_objs)%nat.
Proof. vm_compute. repeat split; first [reflexivity | lia]. Qed.

(* the four parse_bool literals are parse_file's *)
Definition B12_LITS : list (list Z) := [S_yes; S_true; S_no; S_false].
Lemma b12_lits_in : forall x, In x B12_LITS -> In x PARSE_FILE_LITS.
Proof.
intros x Hx. unfold B12_LITS in Hx. cbn [In] in Hx. unfold PARSE_FILE_LITS.
apply in_or_app. left.
repeat (destruct Hx as [<- | Hx]; [cbn [In]; repeat first [left; reflexivity | right] |]). destruct Hx.
Qed.

(** ** strcasecmp's answer as SegModel's *)
(* sanitizer_common's ToLower (RtSeg.lc) is SegModel.tolower on a byte *)
Lemma b12_lc_tolower : forall c, 0 <= c < 256 -> RtSeg.lc c = SegModel.tolower c.
Proof.
intros c Hc.
assert (H : forallb (fun z => Z.eqb (RtSeg.lc z) (SegModel.tolower z)) (map Z.of_nat (seq 0 256)) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in H. apply Z.eqb_eq. apply H. apply in_map_iff. exists (Z.to_nat c).
split; [lia|]. apply in_seq. lia.
Qed.

Lemma b12_lits_vals : forall x, In x B12_LITS -> P8.p8_byte_vals x.
Proof.
intros x Hx. unfold B12_LITS in Hx. cbn [In] in Hx.
repeat (destruct Hx as [<- | Hx]; [apply P8.p8_bv_lit; vm_compute; reflexivity |]). destruct Hx.
Qed.

(* the interceptor's answer over (zb val, zb lit) is SegModel.strcasecmp val lit = 0 *)
Lemma b12_sc : forall val lit, P8.p8_byte_vals val -> P8.p8_byte_vals lit ->
  (map RtSeg.lc (map (fun b : byte => bv_unsigned b) (seg_spec.zb val) ++ [0]) =
   map RtSeg.lc (map (fun b : byte => bv_unsigned b) (seg_spec.zb lit) ++ [0]) <->
   SegModel.strcasecmp val lit = 0).
Proof.
intros val lit Hv Hl.
assert (ZV : map (fun b : byte => bv_unsigned b) (seg_spec.zb val) = val).
{ unfold seg_spec.zb. rewrite map_map. rewrite <- (map_id val) at 2. apply map_ext_in.
  intros a Ha. pose proof (Hv a Ha). rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  replace (2 ^ Z.of_N 8) with 256 by reflexivity. lia. }
assert (ZL : map (fun b : byte => bv_unsigned b) (seg_spec.zb lit) = lit).
{ unfold seg_spec.zb. rewrite map_map. rewrite <- (map_id lit) at 2. apply map_ext_in.
  intros a Ha. pose proof (Hl a Ha). rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  replace (2 ^ Z.of_N 8) with 256 by reflexivity. lia. }
rewrite ZV, ZL, !map_app. cbn [map].
split.
- intros H. apply app_inj_tail in H as [H _].
  apply (P8.p8_sc_zero RtSeg.lc b12_lc_tolower val lit Hv Hl). exact H.
- intros H. f_equal. apply (P8.p8_sc_zero RtSeg.lc b12_lc_tolower val lit Hv Hl). exact H.
Qed.

(* the registers the segment never writes (the strcasecmp calls preserve them): sp, gp, tp, s0, s1, s2, s4, s5, s6,
   s9, s10 -- pf_fi's and PF_RL / PF_RM's *)
Definition B12_KEPT : list Z := [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(** ** The entry bundle: the variables of H_IGN *)
Record b12e := mkB12 {
  e_n : nat; e_v : pfv (PI := PI); e_pos : Z; e_ly : alayout; e_S : astate; e_W : world SEGS;
  e_rX : bvmap 5 word; e_mem : word -> option byte; e_md : Model; e_cf : rconf; e_nm : list Z; e_o : nat;
  e_ln : Z; e_d : list (list Z); e_gi : nat; e_kp : Z; e_vp : Z; e_key : list Z; e_val : list Z }.

Section e.
Variable B : asyms.

(* the cut IGN's state, H_IGN's key tests, and the two exit cuts *)
Definition b12_ent (e : b12e) : Prop :=
  INV_KV B (e_n e) (e_v e) (e_pos e) (e_ly e) (e_S e) (e_W e) (e_rX e) (e_mem e) (e_md e) (e_cf e) (e_nm e)
    (e_o e) (e_ln e) (e_d e) (e_gi e) (e_kp e) (e_vp e) (e_key e) (e_val e) /\
  SegModel.strcasecmp (e_key e) S_role <> 0 /\ SegModel.strcasecmp (e_key e) S_model <> 0 /\
  SegModel.strcasecmp (e_key e) S_ignore = 0 /\
  HA_KREF B (e_n e) /\ HA_PROV2 B (e_n e).

(* the post every internal cut reaches: H_IGN's *)
Definition b12_post (e : b12e) : world SEGS -> config -> Prop :=
  pf_postm B (e_v e)
    (r_key (e_cf e) (Some (e_gi e)) (e_nm e) (e_ln e + 1) (pf_tline (p_s (e_v e)) (e_o e))) (e_o e) (e_ln e).

(* the state at an internal cut: the journal from the contract's entry at the current memory, every byte outside the
   strcasecmp windows as at IGN, and the registers the segment does not write as at IGN *)
Definition b12_mid (e : b12e) (regs1 : bvmap 5 word) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (e_v e)) (seg_spec.RC_PARSE_W (p_c (e_v e)))
    (p_ly (e_v e)) (p_S (e_v e)) (p_W (e_v e)) (p_mem (e_v e)) (p_md (e_v e)) [(5, e_pos e)]
    (e_ly e) (e_S e) (e_W e) memc1 mdc1 0 /\
  kept_out (rdW (e_W e) (e_mem e)) (rdW (e_W e) memc1) (pf_s1 (e_v e) - 2 * ESTACK) (pf_s1 (e_v e)) /\
  (forall r, In r B12_KEPT -> getr regs1 (Z_to_bv 5 r) = getr (e_rX e) (Z_to_bv 5 r)).

Definition b12_at (e : b12e) (regs1 : bvmap 5 word) (memc1 : word -> option byte) (mdc1 : Model) (pc : Z) : Prop :=
  SRr SEGS (e_W e) (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc1 (seg_rom SEGS)) mdc1) (b12_post e).

(** ** The internal cut statements *)
Definition b12_cur (e : b12e) : Z := seg_spec.rseg_addr (p_c (e_v e)) (e_gi e).

(* STORE 0x88df8: b is parse_bool val's answer, s3 = b, a3 = cur *)
Definition B12_STORE_stmt : Prop :=
  forall e b regs1 memc1 mdc1, b12_ent e -> b12_mid e regs1 memc1 mdc1 ->
  parse_bool (e_val e) = Some b -> getr regs1 19 = w64 (seg_spec.b2z b) -> getr regs1 13 = w64 (b12_cur e) ->
  b12_at e regs1 memc1 mdc1 B12_STORE.

(* BAD 0x888a4: parse_bool val = None, a4 = val *)
Definition B12_BAD_stmt : Prop :=
  forall e regs1 memc1 mdc1, b12_ent e -> b12_mid e regs1 memc1 mdc1 ->
  parse_bool (e_val e) = None -> getr regs1 14 = w64 (e_vp e) ->
  b12_at e regs1 memc1 mdc1 B12_BAD.

(* R4 0x88878 (after strcasecmp "false"): the first five tests failed or are in a0; s7 = val[0] *)
Definition B12_R4_stmt : Prop :=
  forall e regs1 memc1 mdc1, b12_ent e -> b12_mid e regs1 memc1 mdc1 ->
  SegModel.strcasecmp (e_val e) S_yes <> 0 -> SegModel.strcasecmp (e_val e) S_true <> 0 ->
  strcmp (e_val e) [49] <> 0 -> SegModel.strcasecmp (e_val e) S_no <> 0 ->
  (getr regs1 10 = w64 0 <-> SegModel.strcasecmp (e_val e) S_false = 0) ->
  getr regs1 23 = w64 (nth 0 (e_val e) 0) ->
  b12_at e regs1 memc1 mdc1 B12_R4.

(* R3 0x88864 (after strcasecmp "no"): s3 = val, s7 = val[0] *)
Definition B12_R3_stmt : Prop :=
  forall e regs1 memc1 mdc1, b12_ent e -> b12_mid e regs1 memc1 mdc1 ->
  SegModel.strcasecmp (e_val e) S_yes <> 0 -> SegModel.strcasecmp (e_val e) S_true <> 0 ->
  strcmp (e_val e) [49] <> 0 ->
  (getr regs1 10 = w64 0 <-> SegModel.strcasecmp (e_val e) S_no = 0) ->
  getr regs1 19 = w64 (e_vp e) -> getr regs1 23 = w64 (nth 0 (e_val e) 0) ->
  b12_at e regs1 memc1 mdc1 B12_R3.

(* NO 0x88850: the yes / true / "1" tests failed; a4 = val, s7 = val[0] *)
Definition B12_NO_stmt : Prop :=
  forall e regs1 memc1 mdc1, b12_ent e -> b12_mid e regs1 memc1 mdc1 ->
  SegModel.strcasecmp (e_val e) S_yes <> 0 -> SegModel.strcasecmp (e_val e) S_true <> 0 ->
  strcmp (e_val e) [49] <> 0 ->
  getr regs1 14 = w64 (e_vp e) -> getr regs1 23 = w64 (nth 0 (e_val e) 0) ->
  b12_at e regs1 memc1 mdc1 B12_NO.

(* R2 0x8880c (after strcasecmp "true"): s3 = 1, s7 = val *)
Definition B12_R2_stmt : Prop :=
  forall e regs1 memc1 mdc1, b12_ent e -> b12_mid e regs1 memc1 mdc1 ->
  SegModel.strcasecmp (e_val e) S_yes <> 0 ->
  (getr regs1 10 = w64 0 <-> SegModel.strcasecmp (e_val e) S_true = 0) ->
  getr regs1 19 = w64 1 -> getr regs1 23 = w64 (e_vp e) ->
  b12_at e regs1 memc1 mdc1 B12_R2.

(* R1 0x887f4 (after strcasecmp "yes"): s7 = val *)
Definition B12_R1_stmt : Prop :=
  forall e regs1 memc1 mdc1, b12_ent e -> b12_mid e regs1 memc1 mdc1 ->
  (getr regs1 10 = w64 0 <-> SegModel.strcasecmp (e_val e) S_yes = 0) ->
  getr regs1 23 = w64 (e_vp e) ->
  b12_at e regs1 memc1 mdc1 B12_R1.

(** ** What H_IGN's premises give *)
(* the spine: r_key's ignore branch is parse_bool's answer *)
Lemma b12_spine : forall e, b12_ent e ->
  r_key (e_cf e) (Some (e_gi e)) (e_nm e) (e_ln e + 1) (pf_tline (p_s (e_v e)) (e_o e)) =
  match parse_bool (e_val e) with
  | None => (refuse (e_cf e) (e_ln e + 1) F_badignore [AS (e_nm e); AS (e_val e)], Some (e_gi e), e_nm e)
  | Some b => (pf_prov_fin (PIgn b) (e_cf e) (e_gi e), Some (e_gi e), e_nm e)
  end.
Proof.
intros [n v pos ly S W rX mem md cf nm o ln d gi kp vp key val] (HI & H1 & H2 & H3 & _). cbn in *.
destruct HI as (_ & _ & _ & HKV & _).
destruct HKV as ((ei & Hs & Hk & Hv) & _).
exact (P8.p8_spine cf gi nm (ln + 1) (pf_tline (p_s v) o) ei key val Hs Hk Hv H1 H2 H3).
Qed.

(** ** Where the cut's objects lie (the A lane's a12_geo, at image B: s1 = (sp0 - 0x160) & -32, STK 12832) *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Definition b12_G (e : b12e) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  In (5, e_pos e) (frames (e_S e)) /\ frame_addr (e_ly e) 5 (e_pos e) = pf_F (e_v e) (e_pos e) /\
  e_ly e = p_ly (e_v e) /\
  4096 <= pf_F (e_v e) (e_pos e) /\ pf_F (e_v e) (e_pos e) + 2048 <= alloc_ceiling /\
  pf_F (e_v e) (e_pos e) mod 64 = 0 /\ in_app (pf_F (e_v e) (e_pos e)) 2048 /\
  4096 <= p_c (e_v e) /\ p_c (e_v e) + seg_spec.SEG_C_SIZE <= alloc_ceiling /\ p_c (e_v e) mod 16 = 0 /\
  sa_heap B (e_ly e) (e_S e) (p_c (e_v e)) seg_spec.SEG_C_SIZE /\
  (e_gi e < 32)%nat /\ (e_gi e < length (rc_seg (e_cf e)))%nat /\
  alloc_ceiling + 2 * ESTACK <= pf_s1 (e_v e) /\ pf_s1 (e_v e) + 0x160 <= pf_sp0 (e_v e) /\
  pf_sp0 (e_v e) <= 2 ^ 47 /\ pf_s1 (e_v e) mod 32 = 0 /\ pf_sp0 (e_v e) mod 16 = 0 /\
  pf_F (e_v e) (e_pos e) + PF_O_BUF <= e_vp e /\
  e_vp e + Z.of_nat (length (e_val e)) < pf_F (e_v e) (e_pos e) + PF_O_BUF + 512 /\
  AR SEGS B (e_ly e) (e_S e) (e_W e) memc1 mdc1 /\ pf_sp0 (e_v e) <= pf_s1 (e_v e) + 0x180.

Lemma b12_geo : forall e regs1 memc1 mdc1, b12_ent e -> b12_mid e regs1 memc1 mdc1 -> b12_G e memc1 mdc1.
Proof.
intros [n v pos ly S W rX mem md cf nm o ln d gi kp vp key val] regs1 memc1 mdc1 (HI & _) (HJ & _ & _).
unfold b12_G. cbn [e_n e_v e_pos e_ly e_S e_W e_rX e_mem e_md e_cf e_nm e_o e_ln e_d e_gi e_kp e_vp e_key e_val] in *.
destruct HI as ((HCX & HFI & HOBJ & HSL & HSH) & HMID & HST & HKV & HSL70 & HRG).
destruct HFI as (HJ0 & Hly & HSc & HPm & HSAV & HFL & HFRM & HTF & HSLc & HRG0).
subst ly.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in Hslo.
assert (Hin : In (5, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS (p_ly v) S W memc1 mdc1 5 pos HAR Hin) as (HF1 & HF2 & HFa).
destruct (frame_al64 SEGS B (p_ly v) S W memc1 mdc1 5 pos HAR Hin) as (HF64 & _).
change (fs_frame_bytes 5) with 2048 in HF2, HFa.
destruct HTF as (Hc0 & Hc16 & _).
pose proof HOBJ as (_ & _ & _ & _ & HHc & _).
destruct HHc as (bq & mq & Hinq & Hbq1 & Hbq2).
destruct (al_blocks _ _ LAWS (p_ly v) S W memc1 mdc1 bq mq HAR Hinq) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hqm).
pose proof (req_size_pos mq ltac:(lia)) as [_ Hrq].
destruct HST as ((bs & _ & Henc) & Hcur & _ & _ & _).
destruct Henc as (_ & Hn32 & _).
cbn [pf_cur_ok] in Hcur.
destruct HKV as (_ & _ & _ & _ & (Hv1 & Hv2)).
pose proof (Z.mod_pos_bound (pf_sp0 v - 0x160) 32 ltac:(lia)) as Hm32.
assert (ES : ESTACK = 4096) by reflexivity.
unfold pf_s1, pf_F, PF_O_BUF in *.
refine (conj Hin (conj eq_refl (conj eq_refl (conj HF1 (conj HF2 (conj HF64 (conj HFa _))))))).
split; [lia|]. split; [unfold seg_spec.SEG_C_SIZE in *; lia|]. split; [exact Hc16|].
split; [exists bq, mq; split; [exact Hinq | split; assumption]|].
split; [lia|]. split; [exact Hcur|].
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
split; [exact Hal16|]. split; [exact Hv1|]. split; [exact Hv2|]. split; [exact HAR | lia].
Qed.

(* every byte below s1 - 2 * ESTACK or at or above s1 reads at the current memory as at IGN *)
Lemma b12_kept : forall e regs1 memc1 mdc1 a, b12_ent e -> b12_mid e regs1 memc1 mdc1 ->
  0 <= a < 2 ^ 64 -> (a < pf_s1 (e_v e) - 2 * ESTACK \/ pf_s1 (e_v e) <= a) ->
  rdW (e_W e) memc1 a = rdW (e_W e) (e_mem e) a.
Proof.
intros e regs1 memc1 mdc1 a HE HM Ha Hw. destruct HM as (_ & HK & _).
apply HK; [exact Ha | lia].
Qed.
Lemma b12_kept_word : forall e regs1 memc1 mdc1 a v, b12_ent e -> b12_mid e regs1 memc1 mdc1 ->
  0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= pf_s1 (e_v e) - 2 * ESTACK \/ pf_s1 (e_v e) <= a) ->
  rdword (rdW (e_W e) (e_mem e)) a = Some v -> rdword (rdW (e_W e) memc1) a = Some v.
Proof.
intros e regs1 memc1 mdc1 a v HE HM Ha Ha8 Hw H. rewrite (rdword_ext (rdW (e_W e) (e_mem e)) (rdW (e_W e) memc1));
  [exact H|]. intros k Hk. apply (b12_kept e regs1 memc1 mdc1); [exact HE | exact HM | lia | lia].
Qed.

(* the five slots the segment reads, at the current memory *)
Lemma b12_slots : forall e regs1 memc1 mdc1, b12_ent e -> b12_mid e regs1 memc1 mdc1 ->
  let v := e_v e in let s1 := pf_s1 v in let W := e_W e in
  rdword (rdW W memc1) (s1 + 0x40) = Some (pf_F v (e_pos e) + PF_O_CN) /\
  rdword (rdW W memc1) (s1 + 0x48) = Some (p_c v + seg_spec.RC_READING) /\
  rdword (rdW W memc1) (s1 + 0x70) = Some (e_vp e) /\
  rdword (rdW W memc1) (s1 + 0xc0) = Some (b12_cur e) /\
  rdword (rdW W memc1) (s1 + 0xc8) = Some (p_c v).
Proof.
intros e regs1 memc1 mdc1 HE HM. pose proof (b12_geo e regs1 memc1 mdc1 HE HM) as G.
pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs1a & Hs1b & Hsp47 & _).
pose proof HE as (HI & _). destruct HI as ((_ & HFI & _ & HSL & _) & _ & HST & _ & HSL70 & _).
destruct HFI as (_ & _ & _ & _ & _ & _ & _ & _ & HSLc & _).
destruct HST as (_ & _ & _ & _ & H0xc0).
cbv zeta. pose proof alloc_ceiling_value as (Hac & _). assert (ES : ESTACK = 4096) by reflexivity.
assert (KW : forall off w, 0 <= off <= 0xd8 -> rdword (rdW (e_W e) (e_mem e)) (pf_s1 (e_v e) + off) = Some w ->
  rdword (rdW (e_W e) memc1) (pf_s1 (e_v e) + off) = Some w).
{ intros off w Hoff H. apply (b12_kept_word e regs1 memc1 mdc1 _ w HE HM); [lia | lia | right; lia | exact H]. }
unfold pf_sl, PF_SL in HSL. rewrite Forall_forall in HSL.
unfold pf_sl in HSL70, HSLc. rewrite Forall_forall in HSL70, HSLc.
split; [apply KW; [lia | exact (HSL (0x40, _) ltac:(cbn [In]; tauto))]|].
split; [apply KW; [lia | exact (HSL (0x48, _) ltac:(cbn [In]; tauto))]|].
split; [apply KW; [lia | exact (HSL70 (0x70, _) ltac:(cbn [In]; tauto))]|].
split; [apply KW; [lia | exact H0xc0]|].
apply KW; [lia | exact (HSLc (0xc8, _) ltac:(cbn [In]; tauto))].
Qed.

(* val's bytes and its NUL at the current memory; val has no NUL *)
Lemma b12_valbytes : forall e regs1 memc1 mdc1, b12_ent e -> b12_mid e regs1 memc1 mdc1 ->
  (forall i, (i <= length (e_val e))%nat ->
     rdW (e_W e) memc1 (e_vp e + Z.of_nat i) = Some (nth i (e_val e) 0)) /\
  ~ In 0 (e_val e) /\ P8.p8_byte_vals (e_val e) /\
  sa_tail (rdW (e_W e) memc1) (e_vp e + Z.of_nat (length (e_val e))).
Proof.
intros e regs1 memc1 mdc1 HE HM. pose proof (b12_geo e regs1 memc1 mdc1 HE HM) as G.
pose proof G as (_ & _ & _ & HF1 & HF2 & HF64 & _ & _ & _ & _ & _ & _ & _ & Hs1a & Hs1b & Hsp47 & _ & _ & Hv1 & Hv2 & _).
pose proof HE as (HI & _). destruct HI as (_ & _ & _ & HKV & _).
destruct HKV as (_ & _ & _ & ((HZ & NZ) & HT) & _).
assert (ES : ESTACK = 4096) by reflexivity.
unfold PF_O_BUF in *.
assert (VB : forall i, (i <= length (e_val e))%nat ->
  rdW (e_W e) memc1 (e_vp e + Z.of_nat i) = Some (nth i (e_val e) 0)).
{ intros i Hi. rewrite (b12_kept e regs1 memc1 mdc1) by (first [exact HE | exact HM | lia]).
  rewrite (HZ i) by (rewrite length_app; cbn [length]; lia).
  destruct (Nat.lt_ge_cases i (length (e_val e))) as [Hl|Hg].
  - rewrite app_nth1 by exact Hl. reflexivity.
  - assert (i = length (e_val e)) as -> by lia. rewrite app_nth2, Nat.sub_diag by lia. cbn [nth].
    rewrite nth_overflow by lia. reflexivity. }
split; [exact VB|]. split; [exact NZ|]. split.
- intros x Hx. pose proof (In_nth _ _ 0 Hx) as (i & Hi & Hxi).
  pose proof (VB i ltac:(lia)) as V. rewrite Hxi in V.
  destruct (aview_byte SEGS (w_H (e_W e)) memc1 _ x V) as (_ & _ & _ & Hr).
  split; [|lia]. destruct (Z.eq_dec x 0) as [->|Hne]; [exfalso; exact (NZ Hx) | lia].
- intros x Hx. pose proof (Z.mod_pos_bound (e_vp e + Z.of_nat (length (e_val e))) 8 ltac:(lia)).
  rewrite (b12_kept e regs1 memc1 mdc1) by (first [exact HE | exact HM | lia]). exact (HT x Hx).
Qed.

(* buf's shadow, at the current memory: every cell of buf is 0 (PF_SC_LINE), so a range in buf is addressable and
   its shadow hull is mapped *)
Lemma b12_buf_shadow : forall e regs1 memc1 mdc1 x n, b12_ent e -> b12_mid e regs1 memc1 mdc1 ->
  pf_F (e_v e) (e_pos e) + PF_O_BUF <= x -> x + n <= pf_F (e_v e) (e_pos e) + PF_O_BUF + 512 -> 0 < n ->
  range_addressable (rdW (e_W e) memc1) SHADOW_OFF x n /\ shadow_hull_vis (rdW (e_W e) memc1) x n.
Proof.
intros e regs1 memc1 mdc1 x n HE HM Hx1 Hx2 Hn. pose proof (b12_geo e regs1 memc1 mdc1 HE HM) as G.
pose proof G as (_ & _ & _ & HF1 & HF2 & HF64 & _ & _ & _ & _ & _ & _ & _ & Hs1a & Hs1b & Hsp47 & _).
pose proof HE as (HI & _). destruct HI as ((_ & _ & _ & _ & HSH) & _).
set (F := pf_F (e_v e) (e_pos e)) in *.
assert (ES : ESTACK = 4096) by reflexivity.
pose proof alloc_ceiling_value as (Hac & _).
assert (HSHv : pf_SH (e_v e) (e_pos e) = SHADOW_OFF + F / 8) by reflexivity.
assert (F8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)); assert (F mod 8 = 0) by
  (apply Z.mod_divide in HF64 as [q Hq]; [|lia]; rewrite Hq; replace (q * 64) with ((8 * q) * 8) by lia;
   apply Z_mod_mult); lia).
(* a frame shadow cell at the current memory *)
assert (CELL : forall i, 0 <= i < 144 -> rdW (e_W e) memc1 (SHADOW_OFF + F / 8 + i) = Some (pf_shb PF_SC_LINE i)).
{ intros i Hi. rewrite (b12_kept e regs1 memc1 mdc1) by (first [exact HE | exact HM | unfold SHADOW_OFF; lia]).
  rewrite <- HSHv. exact (HSH i Hi). }
assert (BUF0 : forall i, 8 <= i < 72 -> pf_shb PF_SC_LINE i = 0).
{ intros i Hi. unfold pf_shb, PF_SC_LINE. cbn [sc_cn sc_buf sc_low sc_l146 sc_known].
  replace (i <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i <? 6) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i <? 72) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
unfold PF_O_BUF in *. split.
- intros y Hy. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. replace (SHADOW_OFF + y / 8) with (SHADOW_OFF + F / 8 + (y / 8 - F / 8)) by lia.
  assert (Hq : 8 <= y / 8 - F / 8 < 72).
  { split.
    - apply (Z.le_trans _ ((F + 64) / 8 - F / 8)); [|apply Z.sub_le_mono_r, Z.div_le_mono; lia].
      replace (F + 64) with ((F / 8 + 8) * 8) by lia. rewrite Z.div_mul by lia. lia.
    - apply (Z.le_lt_trans _ ((F + 575) / 8 - F / 8)); [apply Z.sub_le_mono_r, Z.div_le_mono; lia|].
      replace (F + 575) with ((F / 8 + 71) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
  rewrite CELL by lia. rewrite BUF0 by lia. reflexivity.
- intros s Hs. unfold shadow_addr in Hs.
  assert (H1 : F / 8 + 8 <= x / 8).
  { replace (F / 8 + 8) with ((F + 64) / 8) by (replace (F + 64) with ((F / 8 + 8) * 8) by lia;
      rewrite Z.div_mul by lia; reflexivity). apply Z.div_le_mono; lia. }
  assert (H2 : (x + n - 1) / 8 <= F / 8 + 71).
  { replace (F / 8 + 71) with ((F + 575) / 8) by (replace (F + 575) with ((F / 8 + 71) * 8 + 7) by lia;
      rewrite Z.div_add_l by lia; change (7 / 8) with 0; lia). apply Z.div_le_mono; lia. }
  assert (SO8 : SHADOW_OFF = 8 * (SHADOW_OFF / 8)) by reflexivity.
  assert (HF8 : (F / 8) mod 8 = 0).
  { apply Z.mod_divide in HF64 as [q Hq]; [|lia]. rewrite Hq. replace (q * 64) with ((q * 8) * 8) by lia.
    rewrite Z.div_mul by lia. apply Z_mod_mult. }
  assert (LO : SHADOW_OFF + F / 8 <= (SHADOW_OFF + x / 8) / 8 * 8).
  { pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M1.
    assert (E1 : (SHADOW_OFF + x / 8) mod 8 = (x / 8 - F / 8) mod 8).
    { replace (SHADOW_OFF + x / 8) with ((x / 8 - F / 8) + (SHADOW_OFF / 8 + F / 8 / 8) * 8)
        by (pose proof (Z.div_mod (F / 8) 8 ltac:(lia)); lia).
      apply Z_mod_plus_full. }
    pose proof (Z.mod_le (x / 8 - F / 8) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (HI : SHADOW_OFF + (x + n - 1) / 8 < SHADOW_OFF + F / 8 + 72) by lia.
  assert (HI2 : (SHADOW_OFF + (x + n - 1) / 8) / 8 * 8 + 8 <= SHADOW_OFF + F / 8 + 72).
  { pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M2.
    assert (E2 : (SHADOW_OFF + F / 8 + 72) mod 8 = 0).
    { replace (SHADOW_OFF + F / 8 + 72) with ((SHADOW_OFF / 8 + F / 8 / 8 + 9) * 8)
        by (pose proof (Z.div_mod (F / 8) 8 ltac:(lia)); lia). apply Z_mod_mult. }
    pose proof (Z.div_mod (SHADOW_OFF + F / 8 + 72) 8 ltac:(lia)). lia. }
  replace s with (SHADOW_OFF + F / 8 + (s - (SHADOW_OFF + F / 8))) by lia.
  rewrite CELL by lia. discriminate.
Qed.

(** ** Small tools *)
Lemma b12_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v ->
  getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b12_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
(* a register the segment keeps, at an internal cut: its value at IGN *)
Lemma b12_kreg : forall e regs1 memc1 mdc1 r v, b12_ent e -> b12_mid e regs1 memc1 mdc1 -> In r B12_KEPT ->
  In (r, v) ([(2, pf_s1 (e_v e)); (3, as_gp B); (4, as_tp B); (8, pf_sp0 (e_v e)); (9, pf_s1 (e_v e));
              (20, SHADOW_OFF)] ++ PF_RL (e_v e) (e_pos e) ++ PF_RM (e_v e) (e_o e) (e_ln e)) ->
  getr regs1 (Z_to_bv 5 r) = w64 v.
Proof.
intros e regs1 memc1 mdc1 r v (HI & _) (_ & _ & HR) Hk Hin. rewrite (HR r Hk).
destruct HI as ((_ & HFI & _) & _ & _ & _ & _ & HRG). destruct HFI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
apply in_app_or in Hin as [Hin | Hin]; [exact (b12_rg _ _ _ _ HRG0 Hin) | exact (b12_rg _ _ _ _ HRG Hin)].
Qed.
(* a C string with no NUL, as the runtime contracts state one *)
Lemma b12_astr : forall (rd : reader) p s, (forall i, (i <= length s)%nat -> rd (p + Z.of_nat i) = Some (nth i s 0)) ->
  P8.p8_byte_vals s -> astr_atR rd p (seg_spec.zb s).
Proof.
intros rd p s HV HB. unfold seg_spec.zb. split.
- intros i Hi. rewrite length_app, length_map in Hi. cbn [length] in Hi. rewrite (HV i) by lia.
  destruct (Nat.lt_ge_cases i (length s)) as [Hl | Hg].
  + rewrite app_nth1 by (rewrite length_map; exact Hl). rewrite map_nth.
    pose proof (HB (nth i s 0) (nth_In s 0 Hl)) as Hr.
    rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. unfold bv_modulus.
    replace (2 ^ Z.of_N 8) with 256 by reflexivity. lia.
  + assert (i = length s) as -> by lia. rewrite app_nth2 by (rewrite length_map; lia).
    rewrite length_map, Nat.sub_diag. cbn [nth]. rewrite nth_overflow by lia. reflexivity.
- intros Hin. apply in_map_iff in Hin as (x & Hx & Hin). pose proof (HB x Hin) as Hr.
  apply (f_equal bv_unsigned) in Hx. rewrite !Z_to_bv_unsigned in Hx. unfold bv_wrap, bv_modulus in Hx.
  replace (2 ^ Z.of_N 8) with 256 in Hx by reflexivity. rewrite !Z.mod_small in Hx by lia. lia.
Qed.
Lemma b12_lits_len : forall x, In x B12_LITS -> (length x <= 5)%nat.
Proof.
intros x Hx. unfold B12_LITS in Hx. cbn [In] in Hx.
repeat (destruct Hx as [<- | Hx]; [vm_compute; lia |]). destruct Hx.
Qed.

(** ** One strcasecmp call (0x887f0, 0x88808, 0x88860, 0x88874): a0 = val, a1 = one of the four literals, the
    return to BASE + ret. RtSeg.astrcasecmp_realizes, stepped by PaArt.aj_art_at (window 2 * ESTACK below
    sp = s1); the internal cut's state holds after it, and a0 is SegModel.strcasecmp's answer. *)
Section c.
Hypothesis TL : PALib B.
Hypothesis ASCMP : forall fx0 : YK11.FPState,
  @RtSeg.astrcasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcasecmp).
Let errno_low := pal_env B TL.

Lemma b12_call : forall e regs1 memc1 mdc1 lit ret Q,
  b12_ent e -> b12_mid e regs1 memc1 mdc1 -> In lit B12_LITS ->
  getr regs1 10 = w64 (e_vp e) -> getr regs1 11 = w64 (seg_litA_rc lit) ->
  getr regs1 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall regs2 mem2 md2, b12_mid e regs2 mem2 md2 -> aregs_preserved regs1 regs2 ->
     (getr regs2 10 = w64 0 <-> SegModel.strcasecmp (e_val e) lit = 0) ->
     SRr SEGS (e_W e) (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS (e_W e) (mkCfg (mkst regs1 (Z_to_bv 64 (SIG SS___interceptor_trampoline_strcasecmp)) memc1
    (seg_rom SEGS)) mdc1) Q.
Proof.
intros e regs1 memc1 mdc1 lit ret Q HE HM Hlit R10 R11 R1 Hret Hret2 K.
pose proof (b12_geo e regs1 memc1 mdc1 HE HM) as G.
destruct G as (Hin & EF & Hly & HF1 & HF2 & HF64 & HFa & Hc1 & Hc2 & Hc16 & Hheap & Hgi32 & Hgi & Hs1a & Hs1b
  & Hsp47 & Hs1m & Hsp16 & Hv1 & Hv2 & HAR & Hs1c).
destruct (b12_valbytes e regs1 memc1 mdc1 HE HM) as (VB & NZ & BV & VT).
pose proof HM as (HJ & HKm & HR).
pose proof HE as (HI & _). destruct HI as ((HCX & HFI & HOBJ & HSL & HSH) & _).
pose proof HOBJ as (_ & _ & _ & _ & _ & _ & HLIT & HROD & _).
pose proof (HLIT lit (b12_lits_in lit Hlit)) as (HL0 & HLS & HLP & HLR & HLI).
pose proof (b12_lits_len lit Hlit) as HLlen. pose proof (b12_lits_vals lit Hlit) as HLB.
set (L := seg_litA_rc lit) in *.
pose proof alloc_ceiling_value as (Hac & _). assert (ES : ESTACK = 4096) by reflexivity.
pose proof STK_values as (_ & _ & _ & ESTK & _).
(* the literal lies in the image, below alloc_ceiling *)
assert (HLimg : 0x10000 <= L /\ L + Z.of_nat (length lit) + 1 <= kImgEnd).
{ destruct (HLI L ltac:(lia)) as (H1 & _). destruct (HLI (L + Z.of_nat (length lit)) ltac:(lia)) as (H2 & _).
  pose proof (pa_img_range L H1). pose proof (pa_img_range _ H2). lia. }
unfold kImgEnd in HLimg.
(* registers at the call *)
assert (R2 : getr regs1 2 = w64 (pf_s1 (e_v e)))
  by (apply (b12_bvr _ _ 2); [reflexivity | apply (b12_kreg e regs1 memc1 mdc1 2 _ HE HM); unfold B12_KEPT; cbn [In app]; tauto]).
assert (R3 : getr regs1 3 = w64 (as_gp B))
  by (apply (b12_bvr _ _ 3); [reflexivity | apply (b12_kreg e regs1 memc1 mdc1 3 _ HE HM); unfold B12_KEPT; cbn [In app]; tauto]).
assert (R4 : getr regs1 4 = w64 (as_tp B))
  by (apply (b12_bvr _ _ 4); [reflexivity | apply (b12_kreg e regs1 memc1 mdc1 4 _ HE HM); unfold B12_KEPT; cbn [In app]; tauto]).
assert (Hsp : spZ regs1 = pf_sp0 (e_v e) + (pf_s1 (e_v e) - pf_sp0 (e_v e))).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Ho16 : (pf_s1 (e_v e) - pf_sp0 (e_v e)) mod 16 = 0).
{ rewrite Zminus_mod. replace (pf_s1 (e_v e) mod 16) with 0; [rewrite Hsp16; reflexivity|].
  apply Z.mod_divide in Hs1m as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((2 * q) * 16) by lia.
  symmetry. apply Z_mod_mult. }
assert (HraT : YK0s.ret_ok (getr regs1 1)) by (rewrite R1; apply ret_ok_codeptr_v; lia).
(* the bytes of the literal at the current memory *)
destruct HLS as ((HLZ & HLNZ) & _).
assert (LB : forall i, (i <= length lit)%nat -> rdW (e_W e) memc1 (L + Z.of_nat i) = Some (nth i lit 0)).
{ intros i Hi. rewrite (b12_kept e regs1 memc1 mdc1) by (first [exact HE | exact HM | lia]).
  rewrite (HLZ i) by (rewrite length_app; cbn [length]; lia).
  destruct (Nat.lt_ge_cases i (length lit)) as [Hl|Hg].
  - rewrite app_nth1 by exact Hl. reflexivity.
  - assert (i = length lit) as -> by lia. rewrite app_nth2, Nat.sub_diag by lia. cbn [nth].
    rewrite nth_overflow by lia. reflexivity. }
(* the literal's shadow at the current allocator state *)
pose proof (HLP (e_ly e) (e_S e) (e_W e) memc1 mdc1 HAR) as (_ & _ & HLam & HLra & HLhv).
(* val's shadow *)
destruct (b12_buf_shadow e regs1 memc1 mdc1 (e_vp e) (Z.of_nat (length (e_val e)) + 1) HE HM ltac:(lia)
  ltac:(lia) ltac:(lia)) as (HVra & HVhv).
unfold PF_O_BUF in *.
assert (AMV : forall n, Z.of_nat (length (e_val e)) + 1 <= n <= Z.of_nat (length (e_val e)) + 8 -> amem_range (e_vp e) n).
{ intros n Hn. unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia. }
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
    (SIG SS___interceptor_trampoline_strcasecmp) (e_W e) regs1 memc1 STK_reac_segconf_parse_file (pf_sp0 (e_v e))
    (seg_spec.RC_PARSE_W (p_c (e_v e))) (p_ly (e_v e)) (p_S (e_v e)) (p_W (e_v e)) (p_mem (e_v e)) (p_md (e_v e)) [(5, e_pos e)] (e_ly e) (e_S e)
    mdc1 0 (pf_s1 (e_v e) - pf_sp0 (e_v e)) (Z_to_bv 64 (BASE + ret)) _ HJ Hsp Ho16 ltac:(lia) ltac:(lia)
    ltac:(rewrite ESTK, ES; lia) R1 (fun a (H : False) => False_ind _ H)).
  apply (ASCMP fx (e_ly e) (e_S e) (e_W e) regs1 memc1 mdc1 (e_vp e) L (seg_spec.zb (e_val e))
    (seg_spec.zb lit)).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) STK_reac_segconf_parse_file (pf_sp0 (e_v e))
      (seg_spec.RC_PARSE_W (p_c (e_v e))) (p_ly (e_v e)) (p_S (e_v e)) (p_W (e_v e)) (p_mem (e_v e)) (p_md (e_v e)) [(5, e_pos e)] (e_ly e)
      (e_S e) (e_W e) memc1 mdc1 0 regs1 (pf_s1 (e_v e) - pf_sp0 (e_v e)) HJ Hsp Ho16 ltac:(lia) ltac:(lia)
      ltac:(rewrite ESTK, ES; lia) HraT R3 R4).
  - exact R10.
  - exact R11.
  - lia.
  - exact HL0.
  - apply astr_atR_view. exact (b12_astr _ _ _ VB BV).
  - apply astr_atR_view. exact (b12_astr _ _ _ LB HLB).
  - unfold astr_len, seg_spec.zb. rewrite length_map.
    split; [lia|]. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - replace a with (e_vp e + Z.of_nat (Z.to_nat (a - e_vp e))) by lia. rewrite VB by lia. discriminate.
      - unfold ascratch_stk. rewrite Hsp. lia. }
    split; [apply AMV; lia|]. split; [exact HVra | intros _; exact HVhv].
  - unfold astr_len, seg_spec.zb. rewrite length_map. apply AMV. lia.
  - unfold astr_len, seg_spec.zb. rewrite length_map.
    split; [lia|]. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - replace a with (L + Z.of_nat (Z.to_nat (a - L))) by lia. rewrite LB by lia. discriminate.
      - unfold ascratch_stk. rewrite Hsp. lia. }
    split; [exact HLam|]. split; [exact HLra | exact HLhv].
  - unfold astr_len, seg_spec.zb, amem_range, kLowMemEnd. rewrite length_map. left. lia.
  - unfold astr_len, seg_spec.zb. rewrite length_map. exact VT.
  - unfold astr_len, seg_spec.zb. rewrite length_map. exact (sa_tail_of_romtail SEGS _ _ _ HLR).
  - intros a (sg & Hsg & Hw & Hr) Ho He.
    pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hr))) as Hia. unfold kImgEnd in Hia.
    rewrite (b12_kept e regs1 memc1 mdc1) by (first [exact HE | exact HM | lia]).
    exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ & HK2).
apply K.
- split; [exact HJ2|]. split.
  + intros a Ha Hn. rewrite (HK2 a Ha) by (first [tauto | lia]). exact (HKm a Ha Hn).
  + intros r Hr. rewrite HP2; [exact (HR r Hr)|].
    unfold B12_KEPT in Hr. cbn [In] in Hr. unfold acallee_saved. lia.
- exact HP2.
- rewrite HQ. exact (b12_sc (e_val e) lit BV HLB).
Qed.
End c.

(** ** The seed at an internal cut (every register its own atom). Regions: the slots s1 + 0x40 .. 0xd0 on s1's
    atom 9 (read only: 0x40 cur_name, 0x48 c->reading, 0x70 val, 0xc0 cur, 0xc8 c as the extra atoms 35, 36, 32, 34,
    33) and val's first two bytes on atom 32 (read only: atoms 37 = val[0] and 38 = the byte after it). Facts: s4
    (atom 20) is the shadow base, val and cur are pointers (cur 4-aligned), the two bytes are bytes. *)
Definition b12_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 0x40 0xd0 0 0
      [YP09.mkChunk 0x40 (CVal 8 (SOff 35 0)); YP09.mkChunk 0x48 (CVal 8 (SOff 36 0));
       YP09.mkChunk 0x70 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xc0 (CVal 8 (SOff 34 0));
       YP09.mkChunk 0xc8 (CVal 8 (SOff 33 0))];
    YP09.mkRegion (Some 32%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0)); YP09.mkChunk 1 (CVal 1 (SOff 38 0))] ].
Definition b12_facts : facts :=
  mkFacts [(20%nat, mkAF SB SB 0); (32%nat, mkAF 4096 (2 ^ 47 - 64) 0); (34%nat, mkAF 4096 (2 ^ 47 - 64) 2);
           (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0)] [] [].
Definition b12_ss (pc : Z) : sstate := mkSS pc sr_atoms b12_regions None b12_facts.
Definition b12_xs (e : b12e) (b1 : Z) : list word :=
  [w64 (e_vp e); w64 (p_c (e_v e)); w64 (b12_cur e); w64 (pf_F (e_v e) (e_pos e) + PF_O_CN);
   w64 (p_c (e_v e) + seg_spec.RC_READING); w64 (nth 0 (e_val e) 0); w64 b1].
Definition b12_E (regs1 : bvmap 5 word) (e : b12e) (b1 : Z) : env := Eimg (Ereg regs1 (b12_xs e b1)).
Definition b12_Bx : sv := SOff 20 0.

(* the byte after val[0] exists (it is in the class-5 frame) *)
Lemma b12_b1 : forall e regs1 memc1 mdc1, b12_ent e -> b12_mid e regs1 memc1 mdc1 ->
  exists b1, rdW (e_W e) memc1 (e_vp e + 1) = Some b1 /\ 0 <= b1 < 256.
Proof.
intros e regs1 memc1 mdc1 HE HM. pose proof (b12_geo e regs1 memc1 mdc1 HE HM) as G.
destruct G as (Hin & EF & Hly & HF1 & HF2 & HF64 & HFa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv1 & Hv2 & HAR & _).
destruct (al_frames _ _ LAWS (e_ly e) (e_S e) (e_W e) memc1 mdc1 5 (e_pos e) HAR Hin) as (_ & _ & Hfp & _).
rewrite EF in Hfp. change (fs_frame_bytes 5) with 2048 in Hfp. unfold PF_O_BUF in *.
pose proof (aview_some_of_apresent SEGS (w_H (e_W e)) memc1 (e_vp e + 1) (proj1 (Hfp (e_vp e + 1) ltac:(lia)))) as Hs.
destruct (rdW (e_W e) memc1 (e_vp e + 1)) as [b1|] eqn:Eb; [|exfalso; exact (Hs eq_refl)].
exists b1. split; [reflexivity|]. destruct (aview_byte SEGS (w_H (e_W e)) memc1 _ b1 Eb) as (_ & _ & _ & Hr). exact Hr.
Qed.

(* a one-byte chunk holding the byte the reader has *)
Lemma b12_chunk1 : forall E (H : word -> bool) mem base off n c,
  ew E n = Z_to_bv 64 c -> 0 <= c < 256 -> aview SEGS H mem (base + off) = Some c ->
  YP09.chunk_ok SEGS E (mrestrict H mem) base (YP09.mkChunk off (CVal 1 (SOff n 0))).
Proof.
intros E H mem base off n c En Hc Hv.
unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
destruct (aview_byte SEGS H mem _ c Hv) as (b & Hb & Hv' & _). exists b. split.
- cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite En.
  rewrite !Z.add_0_r, (unsigned_lit_small c), (unsigned_lit_small c) by lia. change (8 * 0) with 0.
  rewrite Z.shiftr_0_r. subst c. apply Z_to_bv_bv_unsigned.
- rewrite !Z.add_0_r. exact Hb.
Qed.

Lemma b12_seed : forall e regs1 memc1 mdc1 pc b1, b12_ent e -> b12_mid e regs1 memc1 mdc1 ->
  rdW (e_W e) memc1 (e_vp e + 1) = Some b1 -> 0 <= b1 < 256 ->
  st_ok_pi SEGS VAL (b12_E regs1 e b1) (b12_ss pc)
    (restrict (w_H (e_W e)) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc1 (seg_rom SEGS))).
Proof.
intros e regs1 memc1 mdc1 pc b1 HE HM Hb1 Hb1r.
pose proof (b12_geo e regs1 memc1 mdc1 HE HM) as G.
destruct G as (Hin & EF & Hly & HF1 & HF2 & HF64 & HFa & Hc1 & Hc2 & Hc16 & Hheap & Hgi32 & Hgi & Hs1a & Hs1b
  & Hsp47 & Hs1m & Hsp16 & Hv1 & Hv2 & HAR & Hs1c).
destruct (b12_slots e regs1 memc1 mdc1 HE HM) as (S40 & S48 & S70 & SC0 & SC8).
destruct (b12_valbytes e regs1 memc1 mdc1 HE HM) as (VB & NZ & BV & VT).
pose proof alloc_ceiling_value as (Hac & _). assert (ES : ESTACK = 4096) by reflexivity.
assert (R9 : getr regs1 (Z_to_bv 5 9) = w64 (pf_s1 (e_v e)))
  by (apply (b12_kreg e regs1 memc1 mdc1 9 _ HE HM); unfold B12_KEPT; cbn [In app]; tauto).
assert (R20 : getr regs1 (Z_to_bv 5 20) = w64 SHADOW_OFF)
  by (apply (b12_kreg e regs1 memc1 mdc1 20 _ HE HM); unfold B12_KEPT; cbn [In app]; tauto).
set (E := b12_E regs1 e b1).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold b12_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (b12_xs e b1) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold b12_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38.
cbn [Nat.add nth b12_xs] in E32, E33, E34, E35, E36, E37, E38. clear EX.
assert (E9 : ew E 9 = w64 (pf_s1 (e_v e))) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl); exact R9).
assert (E20 : ew E 20 = w64 SHADOW_OFF) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (Hcur : b12_cur e = p_c (e_v e) + 356 * Z.of_nat (e_gi e)) by reflexivity.
assert (V0 : rdW (e_W e) memc1 (e_vp e + 0) = Some (nth 0 (e_val e) 0)) by exact (VB 0%nat ltac:(lia)).
destruct (aview_byte SEGS (w_H (e_W e)) memc1 _ _ V0) as (_ & _ & _ & Hb0r).
unfold PF_O_BUF, PF_O_CN, seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *.
rewrite restrict_mkst_fx. unfold b12_ss. apply pa_entry_st_ok_full.
- subst E. unfold b12_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b12_regions. constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor.
    * apply (chunk_ok_val SEGS E _ (pf_s1 (e_v e)) 0x40 8 (SOff 35 0) (pf_F (e_v e) (e_pos e) + 32));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | lia | lia | exact (val_mem_of_rdword SEGS (w_H (e_W e)) memc1 _ _ S40)].
    * apply (chunk_ok_val SEGS E _ (pf_s1 (e_v e)) 0x48 8 (SOff 36 0) (p_c (e_v e) + 16512));
        [cbn [sv_denot]; rewrite E36, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | lia | lia | exact (val_mem_of_rdword SEGS (w_H (e_W e)) memc1 _ _ S48)].
    * apply (chunk_ok_val SEGS E _ (pf_s1 (e_v e)) 0x70 8 (SOff 32 0) (e_vp e));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | lia | lia | exact (val_mem_of_rdword SEGS (w_H (e_W e)) memc1 _ _ S70)].
    * apply (chunk_ok_val SEGS E _ (pf_s1 (e_v e)) 0xc0 8 (SOff 34 0) (b12_cur e));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | lia | lia | exact (val_mem_of_rdword SEGS (w_H (e_W e)) memc1 _ _ SC0)].
    * apply (chunk_ok_val SEGS E _ (pf_s1 (e_v e)) 0xc8 8 (SOff 33 0) (p_c (e_v e)));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | lia | lia | exact (val_mem_of_rdword SEGS (w_H (e_W e)) memc1 _ _ SC8)].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * exact (b12_chunk1 E (w_H (e_W e)) memc1 (e_vp e) 0 37 (nth 0 (e_val e) 0) E37 Hb0r V0).
    * exact (b12_chunk1 E (w_H (e_W e)) memc1 (e_vp e) 1 38 b1 E38 Hb1r Hb1).
- unfold b12_regions. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite E9, E32. unfold w64. rewrite !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I].
  cbn [b12_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E20, E32, E34, E37, E38. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (C4 : b12_cur e mod 4 = 0).
  { rewrite Hcur. apply Z.mod_divide in Hc16 as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 16 + 356 * Z.of_nat (e_gi e)) with ((4 * q + 89 * Z.of_nat (e_gi e)) * 4) by lia. apply Z_mod_mult. }
  rewrite C4. unfold SB, SHADOW_OFF. repeat split; lia.
Qed.

End e.
End f.
End d.
