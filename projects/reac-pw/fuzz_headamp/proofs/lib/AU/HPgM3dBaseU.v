(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheck.v (ck_entry, the code table ck_tbl / ck_wx / ck_segs_low) and
   lib/A/RPgCheckStr.v (rl_cstr_kept) at 77f59d02b01 for the MATCH HALF of reac-pw/fuzz_role's image-A segment M02:
   the half's code table, the entry state of a run that starts at one of its cuts (the registers, the real frame at
   s1 and the role cell as regions), the stack facts of lib/A/RPgSeg.v's rs_pre, the seam between RPgSeg's rs_core and
   lib/A/RPgCSpec.v's callee contracts (rl_pre before a call, rl_post after it), and the strings and cells the callees
   read, carried from the segment's start to a cut (rl_cstr_kept with two worlds and the half's write set). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b01 (the entry-state
   helpers ck_sr / regs_ok_override / ck_regs_ok / ck_entry, the run and keep tactics and ck_kept_run) and
   proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v and RPgM02KeyBase.v at 7e8cf15c304 (the half's code table and
   engine base, the real-frame and entry regions with their region_ok lemmas, the shadow entry of a value
   dispatch, the address arithmetic of &ent[v] and the sign-extension language) for reac-pw/fuzz_headamp image A:
   the ck_ / m2_ / m2k_ prefixes are renamed hv_, every address is headamp's own, role's role cell and strcmp
   wrapper are dropped, and headamp's three value arms (Bool, Int, Float) with its frame cells R+0x88, R+0x90 and
   R+0x98 take the place of role's two arms. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM3dBase.v, with its module paths, module names and addresses changed; 294 of its 424 lines of code are new or changed and 387 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM3bBase.v at 42ff422eb80 (the cut-list
   reading and keeping hb_at_get .. hb_at_app, the cut base under a register change hb_base3_regs, the block post hb_post /
   hb_post_intro, hb_denot0, hb_slot_chunk and the run tactics) and proofs/reac-pw/fuzz_headamp/lib/A/HPgM3dBase.v
   at 936ee3e8fbe (the sign-extension and the value language, hv_kept_run, the stack facts, the split of the piece
   into lanes) restated for image B over lib/AU/HPgSeg.v and HPgSegM.v (hsu_at, hqu_base3, the hqu_cut_ cuts) and image B's
   segments lib/AU/Img0U.v rsegs; the prefixes hb_ / hv_ -> hvu_; image B's code, cuts and lanes are new. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): THE SHARED LAYER of the walk of the piece value of segment M03 of
   LLVMFuzzerTestOneInput (0x80c40), lib/AU/HPgSegM.v hqu_piece_M3d_value_stmt (VAL 0x83490 -> CELL 0x836e4 /
   RF 0x836a0). No instruction is walked here. Proves no function (kind: segment lemma).

   THE PIECE (fuzz_headamp.c:139-143 with pod.h:98-122 and pod_nearest pod.h:152-171 inlined):
     0x83490 .. 0x8349c  the two UBSan checks of &pp->ent[v]: `bgeu s2,33` (the index) and `bltu R+0xf0,s8` (the
                         pointer sum against the one's complement of &ent[0]); both go to `unimp` 0x83a14
     0x834a0 .. 0x834b8  a0 := (R+0xf8) + s8 = &ent[v].type, its instrumented check (slow 0x837ac), `lw a1`
     0x834bc .. 0x834d4  `beq a1,6` -> Float 0x83578 (FA), `beq a1,4` -> Int 0x83524, `bne a1,2` -> RF
     Bool  0x834d8 .. 0x83520  size (check, slow 0x837bc; < 4 -> RF), body (check, slow 0x8381c), `snez s2`,
                               `j` CELL: a Bool value is 0 or 1 and every param's top value is at least 1
     Int   0x83524 .. 0x83574  size (check 0x837cc; < 4 -> RF), `sd a6,0x90(s1)`, body (check 0x8382c),
                               `bltu s2,0x100` -> TAIL 0x83694, else RF
     Float 0x83578 .. 0x83690  size (check 0x837dc; < 4 -> RF), `sd a6,0x90(s1)`, body (check 0x8383c),
                               `flw fs0,0(s8)`, `feq.s` (NaN -> RF by 0x83664), `fmv.s fa0,fs0`, __extendsftf2,
                               `flt.s` against fs1 = -1.0f and fs2 = 256.0f (-> RF by 0x83664), the float-cast
                               check `flt.s fs0,fs3` (fs3 = 2^63) and __gttf2(d, R+0xb8 / R+0xb0) (both to `unimp`),
                               then at CV 0x83608 `fcvt.l.s s2,fs0,rtz`, __floatditf, __subtf3, __getf2 against
                               0.5L (R+0xa8), __lttf2 against -0.5L (R+0xa0), the overflow checks of t + 1
                               (`blt` 0x83678) and t - 1 (`bge` 0x8365c), t5 / t6 reloaded from R+0x110 / R+0x108,
                               a5 := 5 and `bltu 0xff,s2` -> RF, else TAIL
     Tail  0x83694 .. 0x8369c  `sext.w a0,s2`, a6 := R+0x90, `bgeu s7,a0` -> CELL (s7 = the param's top value),
                               else RF (0x836a0) with a5 = 5.
   Every instrumented check of the piece reads the shadow of a 4-byte field of &ent[v] (type at +0, size at +4,
   the body word at +8), inside the first block pp; every slow block is inside the code table and is never
   entered (the block's shadow bytes there are 0).

   THE LANES. The piece is split at three pcs of its own: FA 0x83578 (the Float arm's first instruction), CV
   0x83608 (the Float arm after both float-cast checks, at `fcvt.l.s`) and TAIL 0x83694 (where the Int and the
   Float arms meet). hvu_piece_disp_stmt (VAL -> FA / TAIL / CELL / RF), hvu_piece_flt_stmt (FA -> CV / RF),
   hvu_piece_cv_stmt (CV -> TAIL / RF) and hvu_piece_tail_stmt (TAIL -> CELL / RF) give hqu_piece_M3d_value_stmt by
   hvu_value_of_lanes, which walks no instruction.

   WHAT THIS FILE GIVES besides: the code table hvu_tbl (240 words from 0x83490: the piece, the refusal fold and
   cell entry, and the slow blocks 0x837ac .. 0x8384c), the shadow base HVU_Bx = s11 (atom 27), the reading and
   keeping of a cut's (location, value) list (hsu_at), the cut base under a register change, the block post of a
   run that stores into the real-frame cells only, the value language (sign extension, sext.w) and the facts of
   the segment's start that every lane needs. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09 YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec Require SoftFloat.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require C_extendsftf2.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgM3dVal.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps HPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module SF := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec.SoftFloat.

(* ===================================== the pcs ===================================== *)
Definition HVU_FA : Z := 0x83578.    (* the Float arm's first instruction, `add a1,a3,s8` *)
Definition HVU_CV : Z := 0x83608.    (* `fcvt.l.s s2,fs0,rtz`, after both float-cast checks *)
Definition HVU_TAIL : Z := 0x83694.  (* `sext.w a0,s2`: the Int and Float arms meet *)
Definition HVU_INT : Z := 0x83524.   (* the Int arm *)
Definition HVU_BOOL : Z := 0x834d8.  (* the Bool arm *)
Definition HVU_RFL : Z := 0x83664.   (* the Float arm's refusal: t5 / t6 reloaded, a5 := 5, `j` RF *)

(* ===================================== the image ===================================== *)
(* the 240 4-byte words 0x83490 .. 0x8384c: the piece's own code, the refusal fold, the cell entry and the slow
   blocks of its seven instrumented checks *)
Definition HVU_N : nat := 240.
Definition hvu_tbl : ctable := Eval vm_compute in (build_table rsegs HQU_VAL HVU_N TEmpty).
Lemma hvu_tbl_eq : hvu_tbl = build_table rsegs HQU_VAL HVU_N TEmpty.
Proof. vm_cast_no_check (eq_refl hvu_tbl). Qed.
Lemma hvu_tbl_ok : table_ok rsegs hvu_tbl.
Proof. rewrite hvu_tbl_eq. apply build_table_ok0. unfold HQU_VAL. lia. Qed.

(* the shadow base: the code adds s11 (atom 27) to every shadow index *)
Definition HVU_Bx : sv := SOff 27 0.
Definition HVU_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* ===================================== the cut lists (hsu_at) ===================================== *)
Lemma hvu_at_get : forall H mem regs e L r v, hsu_at rsegs H mem regs e L -> In (LReg r, v) L ->
getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HL Hin. unfold hsu_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.
Lemma hvu_at_cell : forall H mem regs e L b o v, hsu_at rsegs H mem regs e L -> In (LCell b o, v) L ->
val_mem rsegs (mrestrict H mem) (hd_xv e b + o) 8 (v mod 2 ^ 64).
Proof. intros H mem regs e L b o v HL Hin. unfold hsu_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.
Lemma hvu_at_sub : forall H mem regs e L L', hsu_at rsegs H mem regs e L -> (forall x, In x L' -> In x L) ->
hsu_at rsegs H mem regs e L'.
Proof.
intros H mem regs e L L' HL Hs. unfold hsu_at in *. rewrite Forall_forall in *. intros x Hx. exact (HL x (Hs x Hx)).
Qed.
Definition hvu_locb (kept : list (bv 5)) (f : hd_loc * Z) : bool :=
match fst f with LReg r => existsb (fun c => bv_eqb c (Z_to_bv 5 r)) kept | LCell _ _ => true end.
Lemma hvu_at_keep : forall H mem regs e L, hsu_at rsegs H mem regs e L ->
forall regs' (kept : list (bv 5)),
(forall r, In r kept -> getr regs' r = getr regs r) -> forallb (hvu_locb kept) L = true ->
hsu_at rsegs H mem regs' e L.
Proof.
intros H mem regs e L HL regs' kept Hk Hb. unfold hsu_at in *. rewrite Forall_forall in *.
intros [[r|b o] v] Hx. 2:{ exact (HL _ Hx). }
pose proof (HL _ Hx) as Hv. cbn [hd_at fst snd] in Hv |- *.
pose proof (proj1 (forallb_forall _ _) Hb _ Hx) as Hl. unfold hvu_locb in Hl. cbn [fst] in Hl.
apply existsb_exists in Hl as (c & Hc & Hcb). apply bv_eqb_eq in Hcb. subst c.
rewrite (Hk _ Hc). exact Hv.
Qed.
Lemma hvu_at_app : forall H mem regs e L1 L2,
hsu_at rsegs H mem regs e (L1 ++ L2) <-> hsu_at rsegs H mem regs e L1 /\ hsu_at rsegs H mem regs e L2.
Proof. intros H mem regs e L1 L2. unfold hsu_at. apply Forall_app. Qed.
(* the facts of a list hold at a state whose registers agree on the list's registers and whose bytes agree on the
   list's cells *)
Lemma hvu_at_cons : forall H mem regs e l v L, hd_at rsegs H mem regs e l v -> hsu_at rsegs H mem regs e L ->
hsu_at rsegs H mem regs e ((l, v) :: L).
Proof. intros H mem regs e l v L H1 H2. unfold hsu_at in *. apply Forall_cons; [exact H1 | exact H2]. Qed.

(* membership in M03's concrete lists of facts *)
Ltac hvu_unf := unfold hqu_L_seg, hqu_L_frame, hqu_L_loopc, hqu_L_t56, hqu_L_body.
Ltac hvu_in := hvu_unf; cbv zeta; cbn [In app]; repeat (first [left; reflexivity | right]).
Ltac hvu_sub HL :=
apply (hvu_at_sub _ _ _ _ _ _ HL);
let y := fresh "y" in let Hy := fresh "Hy" in
intros y Hy; hvu_unf; cbv zeta in Hy |- *; cbn [In app] in Hy |- *;
repeat (destruct Hy as [<-|Hy]; [repeat (first [left; reflexivity | right]) |]); destruct Hy.
Ltac hvu_kin := apply in_map; cbn [In]; lia.

(* ===================================== the value language ===================================== *)
Lemma hvu_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* the 64-bit word an `lw` of a 32-bit pattern leaves (lib/A/HPgM3dVal.v hvm_sx, definitionally the same term) *)
Lemma hvu_U_sext32 : forall E (n : nat) (v : Z),
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  U E (SExt true 32 (SOff n 0)) = hvm_sx v.
Proof.
intros E n v H Hv. unfold hvm_sx.
rewrite U_SExt, (U_atom E n v H ltac:(lia)).
cbn [Z.of_N].
rewrite (Z.mod_small v (2 ^ 32)) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap.
change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
destruct (Z.ltb_spec v (2 ^ 31)) as [Hl|Hl]; cbv beta iota.
- rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia.
  rewrite Z.mod_small by lia. lia.
- replace ((v + 2 ^ 31) mod 2 ^ 32) with (v + 2 ^ 31 - 2 ^ 32)
    by (apply (Z.mod_unique _ _ 1); lia).
  symmetry. apply (Z.mod_unique _ _ (-1)); lia.
Qed.

(* `sext.w a0,s2` on a value that already fits in 31 bits *)
Lemma hvu_U_sextw : forall E (a : sv) (v : Z), U E a = v -> 0 <= v < 2 ^ 31 ->
  U E (SAluw ALU_ADD a (SLit 0)) = v.
Proof.
intros E a v H Hv.
rewrite U_of_S, S_SAluw, H, U_SLit.
change (zcanon 0 mod 2 ^ 32) with 0.
rewrite (Z.mod_small v (2 ^ 32)) by lia.
cbn [zalu_raw]. rewrite Z.add_0_r.
rewrite swrap32_id by lia.
apply wrap64_id. unfold M64. lia.
Qed.

Lemma hvu_denot_of_U : forall E (a : sv) (v : Z), U E a = v -> sv_denot E a = Z_to_bv 64 v.
Proof. intros E a v H. rewrite (denot_lit_U E a), H. reflexivity. Qed.

(* an 8-byte real-frame cell as a region chunk over an extra atom *)
Lemma hvu_slot_chunk : forall {fx : YK11.FPState} E H mem R o v (n : nat), ew E n = Z_to_bv 64 v ->
val_mem rsegs (mrestrict H mem) (R + o) 8 (v mod 2 ^ 64) ->
YP09.chunk_ok rsegs E (mrestrict H mem) R (YP09.mkChunk o (CVal 8 (SOff n 0))).
Proof.
intros fx E H mem R o v n Hn Hv.
apply (chunk_ok_val rsegs E _ R o 8 (SOff n 0) (v mod 2 ^ 64)); [| | lia | exact Hv].
- rewrite hvu_denot0, Hn. symmetry. apply HPgSteps.Z_to_bv_mod64.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
Qed.

(* the unsigned branches of the piece, on values below 2^63 *)
Lemma hvu_bltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
branch_taken BC_LTU (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. rewrite YO0c.branch_ltu, !unsigned_lit_small by lia. reflexivity. Qed.
Lemma hvu_bgeu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
branch_taken BC_GEU (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a <? b).
Proof. intros a b Ha Hb. rewrite YO0c.branch_geu, !unsigned_lit_small by lia. reflexivity. Qed.

(* ===================================== the block post ===================================== *)
Section bp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
(* the state at a block's end pc, for a block whose stores lie in the real frame's cells Wr: the world as at the
   block's start, the journal to the new store, the I/O state, the kept registers, R, and every byte outside Wr
   as at the block's start *)
Definition hvu_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (pc : Z) (kept : list (bv 5))
(Wr : Z -> Prop) (R : bvmap 5 word -> (word -> option byte) -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
(forall r, In r kept -> getr regs2 r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) /\
R regs2 mem2.

Lemma hvu_post_intro : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept Wr
(R : bvmap 5 word -> (word -> option byte) -> Prop) E' ss' ms md',
st_ok rsegs E' ss' (restrict (w_H W) ms) -> ss_resv ss' = None -> ss_pc ss' = pc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md' k -> same_io mdc md' ->
(forall r, In r kept -> getr (ms_regs ms) r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
R (ms_regs ms) (ms_mem ms) ->
hvu_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept Wr R W (mkCfg ms md').
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept Wr R E' ss' ms md' HS Hrv Hpc HJ Hio Hk HW HR.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), md'.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E' ss' ms HS Hrv) at 1; rewrite Hpc; reflexivity|].
split; [exact HJ|]. split; [exact Hio|]. split; [exact Hk|]. split; [exact HW | exact HR].
Qed.

(* the state at a block's end pc, for a block that stores nothing: the world, the journal and the memory as at
   the block's start, the I/O state, the kept registers, and R *)
Definition hvu_post0 (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (pc : Z) (kept : list (bv 5))
(R : bvmap 5 word -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 pc) memc (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md2 k /\ same_io mdc md2 /\
(forall r, In r kept -> getr regs2 r = getr regs r) /\ R regs2.

Lemma hvu_post0_intro : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept
(R : bvmap 5 word -> Prop) E' ss' ms md',
st_ok rsegs E' ss' (restrict (w_H W) ms) -> ss_resv ss' = None -> ss_pc ss' = pc -> ms_mem ms = memc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md' k -> same_io mdc md' ->
(forall r, In r kept -> getr (ms_regs ms) r = getr regs r) -> R (ms_regs ms) ->
hvu_post0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept R W (mkCfg ms md').
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept R E' ss' ms md' HS Hrv Hpc Hm HJ Hio Hk HR.
split; [reflexivity|]. exists (ms_regs ms), md'.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E' ss' ms HS Hrv) at 1; rewrite Hpc, Hm; reflexivity|].
split; [exact HJ|]. split; [exact Hio|]. split; [exact Hk | exact HR].
Qed.
End bp.

(* ===================================== the run tactics ===================================== *)
Ltac hvu_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply HPgSteps.same_io_wvb]; kio] in kio.
(* the symbolic value of register r in the engine's last state, as a closed term *)
Ltac hvu_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.
(* the registers of a kept list keep their value *)
Ltac hvu_kept kept :=
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HAE : env_agree 32 (Ereg ?rg ?ex0) _ |- _ =>
  intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E' ss' (restrict _ ms) rg ex0 kept HS HAE
    ltac:(vm_compute; reflexivity) r Hr) end.
(* the runs over hvu_tbl, with the shadow span Bsp: HVU_Bspan for a run with instrumented checks (shadow base
   HVU_Bx = s11), HPgSteps.RTBspan for a run with none (HPgSteps.RTBx, the kit's token base atom 32) *)
Ltac hvu_run Bsp awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok hvu_tbl_ok HS HJ SHOK Bsp; [awr | ] end.
Ltac hvu_run_to Bsp awr stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok hvu_tbl_ok HS HJ SHOK Bsp stop; [awr | ] end.
Ltac hvu_branch Bsp Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok hvu_tbl_ok HS SH Bsp end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* the memory after a run over read-only regions is the memory at the block's start *)
Ltac hvu_mem :=
lazymatch goal with HF : frame_of ?E0 ?rs0 ?m0 (ms_mem ?ms1) |- _ =>
  let H := fresh "HMn" in
  pose proof (frame_of_read_only E0 rs0 m0 (ms_mem ms1) eq_refl HF) as H;
  first [ match goal with HM0 : ms_mem ?ms0 = _ |- _ =>
            lazymatch ms0 with ms1 => fail | _ => rewrite HM0 in H; clear HM0 end end
        | idtac ];
  let HM := fresh "HM" in rename H into HM end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the post of a no-store block's arm, after hvu_mem *)
Ltac hvu_post0_tac B kept :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms), HM : ms_mem ?ms = _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  rewrite HM in HJ;
  eapply (hvu_post0_intro B); [exact HS | reflexivity | reflexivity | exact HM | exact HJ | hvu_io | hvu_kept kept | ] end.

(* a run keeps every byte outside the zone its write windows lie in *)
Lemma hvu_kept_run : forall {fx : YK11.FPState} (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros fx Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha.
intros X. exact (Hz (HW a X)).
Qed.

(* ===================================== the segment's facts ===================================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma hvu_start_wf : forall (cx : hsu_scx rsegs) r ev, @hqu_start_M03 fx rc SK rsegs B cx r ev -> Model.pod_rec_wf r.
Proof. intros cx r ev HS. pose proof HS as (_ & _ & Hw & _). exact Hw. Qed.
Lemma hvu_start_pre : forall (cx : hsu_scx rsegs) r ev, @hqu_start_M03 fx rc SK rsegs B cx r ev ->
hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B).
Proof. intros cx r ev HS. exact (proj1 HS). Qed.

(* the stack facts of hsu_pre, as the engine's entry state, its write obligation and the calls need them *)
Lemma hvu_stack : forall (cx : hsu_scx rsegs) (sh : list Z), hsu_pre rsegs B headamp_himg_B cx sh ->
spZ (x_regs rsegs cx) = e_R (x_e rsegs cx) /\ e_R (x_e rsegs cx) mod 32 = 0 /\
e_R (x_e rsegs cx) + 0x220 <= x_sp0 rsegs cx /\
x_sp0 rsegs cx - x_STK rsegs cx <= e_R (x_e rsegs cx) - T_SEG_STK /\
alloc_ceiling <= e_R (x_e rsegs cx) - T_SEG_STK /\
2 ^ 46 <= e_R (x_e rsegs cx) <= 2 ^ 47 /\ x_sp0 rsegs cx <= 2 ^ 47 /\
st_nev (x_S rsegs cx) + x_k rsegs cx <= EV_MAX /\
getr (x_regs rsegs cx) 2 = w64 (e_R (x_e rsegs cx)) /\
getr (x_regs rsegs cx) 3 = w64 (as_gp B) /\ getr (x_regs rsegs cx) 4 = w64 (as_tp B).
Proof using.
intros cx sh Hpre.
unfold hsu_pre, hd_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & Hal & Hrsz & Hwin & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
cbn [hi_rsz headamp_himg_B] in Hrsz.
rewrite HS in Hrsz.
unfold T_SEG_STK, ASTACK in *.
assert (HR : spZ (x_regs rsegs cx) = e_R (x_e rsegs cx))
  by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; lia).
split; [exact HR|]. split; [exact Hal|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [exact Hev|]. split; [exact H2|].
split; [exact H3 | exact H4].
Qed.

(* the first block and the frame for locals: where they lie *)
Lemma hvu_apart : forall (cx : hsu_scx rsegs) (sh : list Z), hsu_pre rsegs B headamp_himg_B cx sh ->
In (e_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) /\
e_pp (x_e rsegs cx) mod 16 = 0 /\
4096 <= e_pp (x_e rsegs cx) /\ e_pp (x_e rsegs cx) + Layout.PP_SIZE <= alloc_ceiling /\
(e_pp (x_e rsegs cx) + Layout.PP_SIZE <= kLowShadowBeg \/ kHighMemBeg <= e_pp (x_e rsegs cx)) /\
4096 <= e_F (x_e rsegs cx) /\ e_F (x_e rsegs cx) + 1024 <= alloc_ceiling /\
e_F (x_e rsegs cx) mod 32 = 0 /\
In (4, x_pos rsegs cx) (x_own rsegs cx).
Proof using.
intros cx sh Hpre.
pose proof Hpre as Hpre'. unfold hsu_pre, hd_seg_pre in Hpre'.
destruct Hpre' as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfb).
destruct Hfb as (Hp0 & Hppin & _).
cbn [hi_cid headamp_himg_B] in Hown, HF.
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hin : In (4, x_pos rsegs cx) (frames (x_Sc rsegs cx)))
  by (rewrite Hfr; apply in_or_app; left; exact Hown).
destruct (al_blocks _ _ (AR_laws_ok rsegs B) _ _ _ _ _ _ _ HAR Hppin) as (Hal & Hpp0 & Hppc & Happ & _).
assert (Hreq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
rewrite Hreq in Hppc, Happ.
destruct (al_frames _ _ (AR_laws_ok rsegs B) _ _ _ _ _ _ _ HAR Hin) as (H32 & Fapp & _).
destruct (al_sep _ _ (AR_laws_ok rsegs B) _ _ _ _ _ HAR) as (_ & Hsep).
pose proof (proj1 (Forall_forall _ _) Hsep _ Hin) as (HF0 & HFc).
cbn [fst snd] in HF0, HFc.
change (fs_frame_bytes 4) with 1024 in HF0, HFc.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
destruct Happ as (_ & Happ').
rewrite HF.
split; [exact Hppin|]. split; [exact Hal|]. split; [exact Hpp0|]. split; [exact Hppc|].
split; [destruct Happ' as [H|[H _]]; [left; exact H | right; exact H]|].
split; [exact HF0|]. split; [exact HFc|]. split; [exact H32 | exact Hown].
Qed.

(* the cut base at a state that differs from a cut's in its registers and its I/O-equal model *)
Lemma hvu_base3_regs : forall (cx : hsu_scx rsegs) (fx2 : YK11.FPState) r sh ly2 S2 W2 regs2 mem2 md2 regs3 md3,
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem2 md3 (x_k rsegs cx) ->
same_io md2 md3 ->
(forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs3 mem2 md3.
Proof.
intros cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 regs3 md3 (Hcore & Hrest) HJ3 Hio3 H234'.
split; [|exact Hrest].
unfold hsu_core, hsu_mid in Hcore |- *.
destruct Hcore as (_ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
split; [exact HJ3|].
split; [intros q Hq; rewrite (H234' q Hq); exact (H234 q Hq)|].
split; [exact Hfr|]. split; [exact Hperm|]. split; [exact (same_io_trans _ _ _ Hio Hio3)|].
split; [exact Hmo | exact Hkeep].
Qed.

End c.

(* ===================================== the three cuts inside the piece ===================================== *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* the address of the value entry ent[m + 1] (its type field) inside the first block *)
Definition hvu_entA (cx : hsu_scx rsegs) (m : nat) : Z :=
e_pp (x_e rsegs cx) + Layout.OFF_ENT + Layout.ENT_SIZE * (Z.of_nat m + 1).
(* the binary128 value __extendsftf2 makes of the binary32 b *)
Definition hvu_d (b : Z) : Z := C_extendsftf2.f128_of_f32 b.

(* FA 0x83578: the type is Float; a0 = &ent[m + 1], a3 = &ent[0].size (R+0x100), s8 = 104 (m + 1), a6 = the
   param, s7 = its top value, s5 = the channel, a5 = OUT_OF_RANGE, t5 / t6 the params-struct word and its shadow
   address (the size test's refusal goes to RF before any call) *)
Definition hvu_cut_FA (cx : hsu_scx rsegs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (v : Model.ent) (ch p : Z) (cs : list cell) (keys rf : Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
@hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx rsegs cx W2 mem2 regs2
  (hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx ++ hqu_L_t56 rsegs cx ++ hqu_L_body rsegs cx (Z.of_nat m + 2) ++
   [(LReg 10, hvu_entA cx m); (LReg 13, e_pp (x_e rsegs cx) + Layout.OFF_ENT + 4);
    (LReg 24, Layout.ENT_SIZE * (Z.of_nat m + 1));
    (LReg 16, p); (LReg 23, hvm_top p); (LReg 21, ch); (LReg 15, Headamp.REFUSE_OUT_OF_RANGE)]) /\
hqu_fs fx2 9 HQU_F32_M1 /\ hqu_fs fx2 18 HQU_F32_256 /\ hqu_fs fx2 19 HQU_F32_2P63 /\
hqu_live rsegs cx r /\ (at0 <= m)%nat /\
Headamp.expect_key (skipn (length Headamp.HA_PREFIX) k) = Headamp.KCell ch p /\
Model.e_type v = Model.POD_FLOAT /\
hqu_pair_inv rsegs cx r m k v cs keys rf /\
Z.of_nat (length cs) <= keys /\
hqu_x_at rsegs cx W2 mem2 cs (keys + 1) rf.

(* CV 0x83608: the float f = b (fs0) is neither NaN nor outside [-1, 256]; d = hvu_d b is in s8 (low word) and
   R+0x88 (high word); R+0x90 = the param, s7 = its top value, s5 = the channel. t5 / t6 are NOT carried: the two
   calls before this pc may have changed them, and both exits reload them from R+0x110 / R+0x108. *)
Definition hvu_cut_CV (cx : hsu_scx rsegs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (v : Model.ent) (ch p b : Z) (cs : list cell) (keys rf : Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
@hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx rsegs cx W2 mem2 regs2
  (hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx ++ hqu_L_body rsegs cx (Z.of_nat m + 2) ++
   [(LReg 24, SF.lo64 (hvu_d b)); (LCell XR 0x88, SF.hi64 (hvu_d b)); (LCell XR 0x90, p);
    (LReg 23, hvm_top p); (LReg 21, ch)]) /\
hqu_fs fx2 8 b /\
hqu_fs fx2 9 HQU_F32_M1 /\ hqu_fs fx2 18 HQU_F32_256 /\ hqu_fs fx2 19 HQU_F32_2P63 /\
hqu_live rsegs cx r /\ (at0 <= m)%nat /\
Headamp.expect_key (skipn (length Headamp.HA_PREFIX) k) = Headamp.KCell ch p /\
Model.e_type v = Model.POD_FLOAT /\ 4 <= Model.e_size v /\ b = Cursor.rd32 (Model.e_body v) /\
fst (Fpu.fp_eq Fpu.fmt_single b b) = true /\ fst (Fpu.fp_lt Fpu.fmt_single b 0xbf800000) = false /\
fst (Fpu.fp_lt Fpu.fmt_single 0x43800000 b) = false /\
hqu_pair_inv rsegs cx r m k v cs keys rf /\
Z.of_nat (length cs) <= keys /\
hqu_x_at rsegs cx W2 mem2 cs (keys + 1) rf.

(* TAIL 0x83694: the value val is read, 0 <= val <= 255; s2 = val, R+0x90 = the param, s7 = its top value,
   s5 = the channel, a5 = OUT_OF_RANGE, t5 / t6 as at VAL *)
Definition hvu_cut_TAIL (cx : hsu_scx rsegs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (v : Model.ent) (ch p val : Z) (cs : list cell) (keys rf : Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
@hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx rsegs cx W2 mem2 regs2
  (hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx ++ hqu_L_t56 rsegs cx ++ hqu_L_body rsegs cx (Z.of_nat m + 2) ++
   [(LReg 18, val); (LCell XR 0x90, p); (LReg 23, hvm_top p); (LReg 21, ch);
    (LReg 15, Headamp.REFUSE_OUT_OF_RANGE)]) /\
hqu_fs fx2 9 HQU_F32_M1 /\ hqu_fs fx2 18 HQU_F32_256 /\ hqu_fs fx2 19 HQU_F32_2P63 /\
hqu_live rsegs cx r /\ (at0 <= m)%nat /\
Headamp.expect_key (skipn (length Headamp.HA_PREFIX) k) = Headamp.KCell ch p /\
Headamp.cell_value v = val /\ 0 <= val <= 255 /\
hqu_pair_inv rsegs cx r m k v cs keys rf /\
Z.of_nat (length cs) <= keys /\
hqu_x_at rsegs cx W2 mem2 cs (keys + 1) rf.

(* the continuations of the three cuts *)
Definition hvu_from_FA (cx : hsu_scx rsegs) (r : Model.pod_rec)
(POST : world rsegs -> config -> Prop) (at0 m : nat) : Prop :=
forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 k v ch p cs keys rf,
hvu_cut_FA cx fx2 r at0 m k v ch p cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVU_FA regs2 mem2 md2) POST.
Definition hvu_from_CV (cx : hsu_scx rsegs) (r : Model.pod_rec)
(POST : world rsegs -> config -> Prop) (at0 m : nat) : Prop :=
forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 k v ch p b cs keys rf,
hvu_cut_CV cx fx2 r at0 m k v ch p b cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVU_CV regs2 mem2 md2) POST.
Definition hvu_from_TAIL (cx : hsu_scx rsegs) (r : Model.pod_rec)
(POST : world rsegs -> config -> Prop) (at0 m : nat) : Prop :=
forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 k v ch p val cs keys rf,
hvu_cut_TAIL cx fx2 r at0 m k v ch p val cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVU_TAIL regs2 mem2 md2) POST.

(* ===================================== the four lanes of the piece ===================================== *)
(* VAL 0x83490 -> FA / TAIL / CELL / RF: the two index checks, the entry's type, the Bool arm and the Int arm *)
Definition hvu_piece_disp_stmt : Prop :=
forall cx POST r ev at0 m,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_from_CELL fx rc SK rsegs B MT cx r POST at0 m ->
@hqu_from_RF fx rc SK rsegs B MT cx r POST at0 m ->
hvu_from_TAIL cx r POST at0 m ->
hvu_from_FA cx r POST at0 m ->
@hqu_from_VAL fx rc SK rsegs B MT cx r POST at0 m.
(* FA 0x83578 -> CV / RF: the size test, the body, the NaN and range tests, __extendsftf2 and the two
   float-cast checks *)
Definition hvu_piece_flt_stmt : Prop :=
forall cx POST r ev at0 m,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_from_RF fx rc SK rsegs B MT cx r POST at0 m ->
hvu_from_CV cx r POST at0 m ->
hvu_from_FA cx r POST at0 m.
(* CV 0x83608 -> TAIL / RF: fcvt.l.s, __floatditf, __subtf3, __getf2, __lttf2, the rounding and its two overflow
   checks, and the range test against 255 *)
Definition hvu_piece_cv_stmt : Prop :=
forall cx POST r ev at0 m,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_from_RF fx rc SK rsegs B MT cx r POST at0 m ->
hvu_from_TAIL cx r POST at0 m ->
hvu_from_CV cx r POST at0 m.
(* TAIL 0x83694 -> CELL / RF: the range test against the param's top value *)
Definition hvu_piece_tail_stmt : Prop :=
forall cx POST r ev at0 m,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_from_CELL fx rc SK rsegs B MT cx r POST at0 m ->
@hqu_from_RF fx rc SK rsegs B MT cx r POST at0 m ->
hvu_from_TAIL cx r POST at0 m.

(* the piece from its four lanes: no instruction is walked here *)
Theorem hvu_value_of_lanes :
hvu_piece_disp_stmt -> hvu_piece_flt_stmt -> hvu_piece_cv_stmt -> hvu_piece_tail_stmt ->
@hqu_piece_M3d_value_stmt fx rc SK rsegs B MT.
Proof.
intros PD PF PC PT. unfold hqu_piece_M3d_value_stmt. intros cx POST r ev at0 m HS HCELL HRF.
assert (HT : hvu_from_TAIL cx r POST at0 m) by exact (PT cx POST r ev at0 m HS HCELL HRF).
assert (HC : hvu_from_CV cx r POST at0 m) by exact (PC cx POST r ev at0 m HS HRF HT).
assert (HF : hvu_from_FA cx r POST at0 m) by exact (PF cx POST r ev at0 m HS HRF HC).
exact (PD cx POST r ev at0 m HS HCELL HRF HT HF).
Qed.

End d.

Print Assumptions hvu_tbl_ok.
Print Assumptions hvu_at_keep.
Print Assumptions hvu_U_sext32.
Print Assumptions hvu_U_sextw.
Print Assumptions hvu_post_intro.
Print Assumptions hvu_kept_run.
Print Assumptions hvu_stack.
Print Assumptions hvu_apart.
Print Assumptions hvu_base3_regs.
Print Assumptions hvu_value_of_lanes.
