(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgSlots.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632 for fuzz_qdisc's image A) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks reac_role_cfg_changes 0x82ec8 against lib/A/RPgCSpec.v's rl_cfg_changes_specX on the concrete image lib/A/Img0.v rsegs; the plain walk it replaces is lib/Prog/reac_role_cfg_changes.v (snez of the xor). The leaf's post is RPgCSpec's rl_post (the float state fx kept, no extra bytes E); the table is this file's cfg_tbl over the two cfg functions; qdisc's region of the divisor constant, its arithmetic lemmas and its three branches are dropped. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v, with its module paths and module names changed; 498 of its 543 lines of code are new or changed and 105 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the code table, entry and leaf forms of lib/A/RPgCfgChanges.v (cfg_tbl, cfg_wx,
   cfg_segs_low, kept_run, the cfg_run / cfg_keep / cfg_branch / cfg_leaf tactics) for reac_role_prop_parse; the cut
   states, the context record and the segment statements below are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseBase.v at d428443238a; for image B
   (fuzz_role.asan-ubsan): the image is lib/AU/Img0.v's; the image constants, the cut pcs and the code table are image
   B's; role_B_dcs has five cells (image B adds its float-cast checks' bounds); kept_run and same_io_wvb (of
   lib/A/RPgCfgChanges.v) are copied here; L1 keeps P + 8 in a1, L2 keeps the key slot in a1 (image B keeps the answer
   in a0); LB is at image B's 1-byte check, with a0 = the last body byte and a1 = P + c + 8; T has the flag v in a1;
   pre_q derives 0 < Q from rl_wcell and the caller's journal (image B tests Q against 0 before the store). *)
(* reac_role_prop_parse 0x83130 (1428 bytes, 357 instructions, all 4 bytes) of reac-pw/fuzz_role's ASan image B
   (fuzz_role.asan-ubsan, pinned sha256 b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; unstripped
   twin dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, the same loaded bytes): the vocabulary its
   walk files share. The walk proves lib/A/RPgCSpec.v's rl_parse_specX A_PARSE A_KEY role_B_dcs; it is cut at fixed
   pcs into segments, each walked by the engine of lib/Reusable (st_ok, aj_run_tok) from an entry state made of the
   cut's facts:

     E1 0x83130 (entry)      -> ret -1 (a0 = 0) | H
     E2 H  0x83178           -> ret -1 / ret 0 (header checks) | L1 (r = 16)
     F  L1 0x83204 (find)    -> ret 0 | L1 (next property) | L2 (the params Struct, first child, no key)
     L  L2 0x83300 (foreach) -> ret 0 | L2 (next child, no key) | LB | the strcmp call, then K
     LB LB 0x8338c           -> ret 0 | L2 (next child, key or no key)
     K  K  0x833bc           -> ret 0 / ret -1 | L2 (next child, no key) | T (Int value) | FV (Float value)
     FV FV 0x83524 (float)   -> ret -1 | T (at the float state the double steps leave)
     T  T  0x83488 (flag)    -> ret -1 | store of the role at Q, ret 1

   The pcs and the live values at each cut are read from the code (the pinned file's listing):
   - prologue 0x83130 .. 0x83158: sp -= 0x60, ra / s0 / s1 / s2 .. s8 to sp + 0x58, 0x50, 0x48, 0x40 .. 0x10 (SAVED),
     0x8315c beqz a0 -> 0x83594 (a0 = -1, the shared epilogue 0x83598 .. 0x835c4);
   - 0x83160 mv s0,a1 (Q); 0x83164 andi a1,a0,3 + 0x83168 bnez a1 -> 0x835c8 (P & 3); 0x8316c auipc a1,0x18 +
     0x83170 ld a1,-0x69c(a1) reads the .got word 0x9aad0 (as_got_shadow: it holds 0xa3678, the shadow-offset cell
     as_shadow_cell); 0x83174 ld s3,0(a1) = SHADOW_OFF; H is 0x83178, the first instrumented check (of a0 = P);
   - L1 0x83204 (li a0,0, the find loop's head): a1 = P + 8, a2 = P + r, a4 = S - 16, a5 = P + S - 8, a6 = 0x80001;
     the loop's back edge is 0x83260 bnez (r' & 3) -> 0x831e8 (a0 = 0, ret 0), else 0x83264 j L1; at the property
     found, 0x8328c andi a1,a2,3 + 0x83290 bnez a1 -> 0x835c8 ((P + r) & 3);
   - L2 0x83300 (li a0,0, the foreach head): a1 = 0 or the pending key P + ck + 8, s1 = P + c, s2 = 0x215e0 (the
     literal "reac.cfg.role", .str.4), s4 = 8, s5 = P + r + 16, s6 = P + r + 8 + VS, s7 = VS - 8 (VS the value size
     of the property at r); 0x83310 beqz s1 -> 0x835c8 (P + c = 0); the back edge is 0x833e4 bnez (c' & 3) ->
     0x831e8 (ret 0), else 0x833e8 j L2;
   - 0x8336c .. 0x83388, before LB: a1 = P + c + 8, a0 = a1 + sext32 (CS - 1) (CS the String child's size);
     0x83378 bltu a0,a1 -> 0x835c8 (the sum wraps); 0x8337c .. 0x83388 beqz ((a1 <> 0) xor (a0 = 0)) -> 0x835c8;
   - LB 0x8338c: the 1-byte check of the String child's last body byte a0 = P + c + 8 + CS - 1, with a1 = P + c + 8
     and s8 = ((P + c) >> 3) + SHADOW_OFF (the shadow address of s1, computed at 0x83314 and read again at 0x833c4);
     0x8339c .. 0x833a8 set a1 = P + c + 8 when that byte is 0 and a1 = 0 else (no branch), 0x833ac j 0x833c4;
   - the strcmp call 0x833b8 jal 0x41b68 (a0 = P + ck + 8, a1 = s2), K 0x833bc its return (a0 = strcmp's result);
   - FV 0x83524: after the Float child's 4 body bytes were put together and stored at sp + 8 (0x83520 sw), with
     a2 = 0x10518 (auipc 0x83518; fld fa4,-0x198(a2) reads 0x10380); 0x83524 .. 0x83590 are the double steps of the
     inlined reac_float_nearest: 0x83540 beqz -> 0x83594 (ret -1), 0x83550 beqz -> 0x83594 (ret -1), the cast
     bounds 0x83558 fld 0x103f8 + 0x83560 beqz -> 0x835c8 and 0x83568 fld 0x10358 + 0x83570 beqz -> 0x835c8,
     0x83574 fcvt.l.d, 0x83580 beqz -> T, 0x83584 addi a0,a1,-1 + 0x83588 bge a0,a1 -> 0x835c8, 0x8358c mv a1,a0,
     0x83590 j 0x83488;
   - T 0x83488: a1 = the value v (the Int child's 4 bytes sign-extended, or the Float path's integer); 0x83488 sext.w
     a2,a1, 0x83490 beq a2,1 -> 0x8349c, 0x83498 bnez a2 -> 0x83598 (a0 = -1); 0x8349c beqz s0 -> 0x835c8 (Q = 0),
     0x834a0 andi a0,s0,3 + 0x834a4 bnez a0 -> 0x835c8 (Q & 3); v in {0, 1} is stored at Q (0x834b8 sw, after its
     instrumented check) and 1 is returned.
   The ten branches to the `unimp` 0x835c8 (0x83168, 0x83290, 0x83310, 0x83378, 0x83388, 0x8349c, 0x834a4, 0x83560,
   0x83570, 0x83588) are not taken on any walk: each segment shows its own. No numeral of another image occurs here. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o YA0d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Cursor Model Accessors Spa Nearest Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require reac_role_prop_parse.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec RPgStrcmp.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= the image ======================================= *)
Definition A_PARSE : Z := 0x83130.
Definition N_PARSE : nat := 357.
Definition A_STRCMP : Z := 0x41b68.
Definition A_GOT_SH : Z := 0x9aad0.
Definition A_SH_CELL : Z := 0xa3678.
Definition A_KEY : Z := 0x215e0.
(* the five doubles the float path loads (fld at 0x83528, 0x83530, 0x83548, 0x83558, 0x83568): 0.5, -2^31, 2^31,
   -(2^63 + 2^11), 2^63; the last two are the bounds of image B's float-cast checks *)
Definition role_B_dcs : list (Z * Z) :=
[(0x10380, 0x3fe0000000000000); (0x103e8, 0xc1e0000000000000); (0x10330, 0x41e0000000000000);
 (0x103f8, 0xc3e0000000000001); (0x10358, 0x43e0000000000000)].
Definition PC_H : Z := 0x83178.
Definition PC_L1 : Z := 0x83204.
Definition PC_L2 : Z := 0x83300.
Definition PC_LB : Z := 0x8338c.
Definition PC_CALL : Z := 0x833b8.
Definition PC_K : Z := 0x833bc.
Definition PC_FV : Z := 0x83524.
Definition PC_T : Z := 0x83488.
(* the branch target of the ten trap branches: the `unimp` *)
Definition PC_TRAP : Z := 0x835c8.
Definition FRAME : Z := 0x60.
(* the auipc value 0x83518 + (0xfff8d << 12) mod 2^64 that the float path's first fld adds -0x198 to *)
Definition A_FV_A2 : Z := 0x10518.

(* the image's bytes at the cells above: role_B_dcs's doubles, the .got word A_GOT_SH (it holds A_SH_CELL) and the
   literal at A_KEY ("reac.cfg.role" and its NUL), read from rsegs *)
Definition img_le_ok (a v : Z) (n : nat) : bool :=
forallb (fun i => match img_byte rsegs (a + Z.of_nat i) with
                  | Some b => bv_unsigned b =? Z.land (Z.shiftr v (8 * Z.of_nat i)) 255
                  | None => false end) (seq 0 n).
Lemma role_B_dcs_img : forallb (fun c => img_le_ok (fst c) (snd c) 8) role_B_dcs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma got_sh_img : img_le_ok A_GOT_SH A_SH_CELL 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma key_img : forallb (fun i => match img_byte rsegs (A_KEY + Z.of_nat i) with
  | Some b => bv_unsigned b =? nth i (map (fun c : byte => bv_unsigned c) Role.ROLE_KEY ++ [0]) 0 | None => false end)
  (seq 0 (S (length Role.ROLE_KEY))) = true.
Proof. vm_compute. reflexivity. Qed.

Definition parse_tbl : ctable := Eval vm_compute in (build_table rsegs A_PARSE N_PARSE TEmpty).
Lemma parse_tbl_eq : parse_tbl = build_table rsegs A_PARSE N_PARSE TEmpty.
Proof. vm_cast_no_check (eq_refl parse_tbl). Qed.
Lemma parse_tbl_ok : table_ok rsegs parse_tbl.
Proof. rewrite parse_tbl_eq. apply build_table_ok0. unfold A_PARSE. lia. Qed.
Lemma parse_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma parse_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.

(* [lib/A/RPgCfgChanges.v same_io_wvb, kept_run] *)
Lemma same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
(* a run keeps every byte outside the zone its write windows lie in [fuzz_qdisc QPgSlots.v kept_run] *)
Lemma kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.

(* the shadow base: env slot 32 holds it, register s3 (atom 19) holds it from H on *)
Definition SBr : Z := 0x7fff8000.
Definition RTBspan : Z * Z := (SBr, SBr + 2 ^ 44 - 1).
Definition PBx : sv := SOff 19 0.

(* ======================================= the model ======================================= *)
Abbreviation walk_res := reac_role_prop_parse.walk_res.
Definition bvals (l : list byte) : list Z := map (fun b : byte => bv_unsigned b) l.
(* the answer from the find loop's position: the property found and its value *)
Definition l1_res (bs : list byte) (o : option Z) : option Role.role * Z :=
match o with
| Some r => if Spa.is_struct_at bs (r + 8) then walk_res bs (r + 16) (Spa.u32_at bs (r + 8)) (r + 16) (length bs) None
            else (None, 0)
| None => (None, 0)
end.
(* the key slot of the foreach loop: None, or the String child at ck whose text waits for its value *)
Definition l2_key (bs : list byte) (ko : option Z) : option (list byte) :=
match ko with None => None | Some ck => Spa.spa_get_string (Spa.child_at bs ck) end.

(* ======================================= one call ======================================= *)
(* The quantities rl_parse_specX fixes for one call (non-NULL argument): the caller's journal, the call's registers,
   the pod at P with its bytes bs, the role cell Q. *)
Record pctx := PCtx {
x_STK : Z; x_sp0 : Z; x_FP : list (Z * Z); x_ly : alayout; x_S : astate; x_W0 : world rsegs;
x_mem0 : word -> option byte; x_md0 : Model; x_own : list (Z * Z);
x_lyc : alayout; x_Sc : astate; x_W : world rsegs; x_memc : word -> option byte; x_mdc : Model; x_k : Z;
x_regs : bvmap 5 word; x_P : Z; x_Q : Z; x_bs : list byte }.
Definition x_sp (x : pctx) : Z := spZ (x_regs x).
Definition x_F (x : pctx) : Z := x_sp x - FRAME.
Definition x_len (x : pctx) : Z := Z.of_nat (length (x_bs x)).
Definition x_SZ (x : pctx) : Z := Spa.u32_at (x_bs x) 0.
Definition x_res (x : pctx) : option Role.role * Z := Role.parse_model (x_bs x).
(* the ten words the prologue saves: (offset from F, register) *)
Definition SAVED : list (Z * Z) :=
[(0x58, 1); (0x50, 8); (0x48, 9); (0x40, 18); (0x38, 19); (0x30, 20); (0x28, 21); (0x20, 22); (0x18, 23); (0x10, 24)].
Definition saved_vals (regs : bvmap 5 word) : list word := map (fun c => getr regs (Z_to_bv 5 (snd c))) SAVED.
(* the env of a segment that starts at a cut: slots 0 .. 31 the registers there, 32 the shadow base, 33 .. 42 the
   ten saved words (SAVED's order), 43 .. the segment's own values *)
Definition cut_env (x : pctx) (regs2 : bvmap 5 word) (L : list word) : env :=
Ereg regs2 (w64 SBr :: saved_vals (x_regs x) ++ L).
(* the frame [F, F + 0x60) as a region at sp (atom 2) after the prologue: the saved words as chunks of atoms 33 .. 42,
   and cs below them (the float path's 4-byte temp at 8) *)
Definition saved_chunks : list YP09.chunk :=
[YP09.mkChunk 0x10 (CVal 8 (SOff 42 0)); YP09.mkChunk 0x18 (CVal 8 (SOff 41 0)); YP09.mkChunk 0x20 (CVal 8 (SOff 40 0));
 YP09.mkChunk 0x28 (CVal 8 (SOff 39 0)); YP09.mkChunk 0x30 (CVal 8 (SOff 38 0)); YP09.mkChunk 0x38 (CVal 8 (SOff 37 0));
 YP09.mkChunk 0x40 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x48 (CVal 8 (SOff 35 0)); YP09.mkChunk 0x50 (CVal 8 (SOff 34 0));
 YP09.mkChunk 0x58 (CVal 8 (SOff 33 0))].
Definition frame_region (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 FRAME 0 FRAME (cs ++ saved_chunks).
(* what the epilogue leaves in each callee-saved register: the saved word (atoms 33 .. 42), sp + 0x60, or the
   register as it was at the cut *)
Definition leaf_sr : list (Z * sv) :=
[(1, SOff 33 0); (8, SOff 34 0); (9, SOff 35 0); (18, SOff 36 0); (19, SOff 37 0); (20, SOff 38 0); (21, SOff 39 0);
 (22, SOff 40 0); (23, SOff 41 0); (24, SOff 42 0); (2, SOff 2 FRAME); (3, SOff 3 0); (4, SOff 4 0);
 (25, SOff 25 0); (26, SOff 26 0); (27, SOff 27 0)].
Definition leaf_sr_ok (sr : list sv) : bool :=
forallb (fun p => sv_eqb (sr_get sr (Z_to_bv 5 (fst p))) (snd p)) leaf_sr.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* the call's post-condition (rl_parse_specX's), for a NULL (null = true) or non-NULL argument *)
Definition PPOST (x : pctx) (null : bool) : world rsegs -> config -> Prop :=
rl_post rsegs B MT (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x) (x_k x)
T_parse_STK (x_regs x) (x_lyc x) (x_Sc x) (x_W x) (x_memc x) (x_mdc x)
(rl_fxk [13; 14; 15] fx)
(fun a => fst (rl_parse_res null (x_bs x)) <> None /\ x_Q x <= a < x_Q x + 4)
(fun W2 regs2 mem2 =>
getr regs2 10 = w64 (snd (rl_parse_res null (x_bs x))) /\
match fst (rl_parse_res null (x_bs x)) with
| Some r => val_mem rsegs (mrestrict (w_H W2) mem2) (x_Q x) 4 (Role.role_z r)
| None => True
end).

(* rl_parse_specX's premises for one call *)
Definition call_ok (x : pctx) (null : bool) : Prop :=
rl_pre rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x) (x_k x)
T_parse_STK (x_regs x) (x_lyc x) (x_Sc x) (x_W x) (x_memc x) (x_mdc x) /\
getr (x_regs x) 10 = w64 (if null then 0 else x_P x) /\ getr (x_regs x) 11 = w64 (x_Q x) /\
(null = false ->
 0 < x_P x /\ x_P x mod 16 = 0 /\ 8 <= x_len x /\ x_SZ x = x_len x - 8 /\ x_P x + x_len x <= 2 ^ 63 /\
 garr8 rsegs (mrestrict (w_H (x_W x)) (x_memc x)) (x_P x) (bvals (x_bs x)) /\
 range_addressable (aview rsegs (w_H (x_W x)) (x_memc x)) SHADOW_OFF (x_P x) (x_len x) /\
 shadow_hull_vis (aview rsegs (w_H (x_W x)) (x_memc x)) (x_P x) (x_len x) /\
 amem_range (x_P x) (x_len x) /\
 (x_P x + x_len x <= x_sp x - T_parse_STK \/ x_sp x <= x_P x)) /\
rl_wcell (x_STK x) (x_sp0 x) (x_lyc x) (x_own x) (x_sp x) T_parse_STK (x_Q x) 4 /\ x_Q x mod 4 = 0 /\
range_addressable (aview rsegs (w_H (x_W x)) (x_memc x)) SHADOW_OFF (x_Q x) 4 /\
rl_cstr rsegs (w_H (x_W x)) (x_memc x) A_KEY (bvals Role.ROLE_KEY) /\
rl_ro_cells rsegs (w_H (x_W x)) (x_memc x) role_B_dcs /\
YK0o.frm_zero (@fp_csr fx).
Definition pre_ok (x : pctx) : Prop := call_ok x false.

(* ---------------------------------- the facts every cut carries ---------------------------------- *)
(* the caller's journal at the cut (same layout, state and world as at the call), the model's I/O as at the call,
   every byte outside the callee's stack [sp - T_parse_STK, sp) as at the call, the ten saved words in the frame,
   sp = F, gp / tp / s9 .. s11 as at the call, s0 = Q and s3 = SHADOW_OFF *)
Definition FI (x : pctx) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
ajournal rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x)
(x_lyc x) (x_Sc x) (x_W x) mem2 md2 (x_k x) /\
same_io (x_mdc x) md2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) ->
 aview rsegs (w_H (x_W x)) mem2 a = aview rsegs (w_H (x_W x)) (x_memc x) a) /\
Forall (fun c => val_mem rsegs (mrestrict (w_H (x_W x)) mem2) (x_F x + fst c) 8
 (bv_unsigned (getr (x_regs x) (Z_to_bv 5 (snd c))))) SAVED /\
getr regs2 2 = w64 (x_F x) /\
(forall r, r = 3 \/ r = 4 \/ r = 25 \/ r = 26 \/ r = 27 -> getr regs2 (Z_to_bv 5 r) = getr (x_regs x) (Z_to_bv 5 r)) /\
getr regs2 8 = w64 (x_Q x) /\ getr regs2 19 = w64 SHADOW_OFF.

(* ---------------------------------- the cuts ---------------------------------- *)
Definition H_at (x : pctx) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
FI x regs2 mem2 md2 /\ getr regs2 10 = w64 (x_P x).

(* the find loop at the property offset r (canonical fuel: one more than the bytes left) *)
Definition L1_at (x : pctx) (r : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
FI x regs2 mem2 md2 /\
getr regs2 11 = w64 (x_P x + 8) /\ getr regs2 12 = w64 (x_P x + r) /\ getr regs2 14 = w64 (x_SZ x - 16) /\
getr regs2 15 = w64 (x_P x + x_SZ x - 8) /\ getr regs2 16 = w64 0x80001 /\
Spa.is_object_type (x_bs x) Model.POD_OBJECT_PROPS = true /\ 16 <= x_SZ x /\
16 <= r <= x_len x + 7 /\ r mod 4 = 0 /\
x_res x = l1_res (x_bs x) (Spa.find_prop (x_bs x) (x_SZ x) Model.POD_PROP_PARAMS r (S (Z.to_nat (8 + x_SZ x - r)))).

(* the property at r whose value is the Struct the foreach walks: body r + 16, size VS = u32 at r + 8 *)
Definition struct_ok (x : pctx) (r : Z) : Prop :=
16 <= r /\ r mod 4 = 0 /\ Spa.is_struct_at (x_bs x) (r + 8) = true /\ 8 <= Spa.u32_at (x_bs x) (r + 8) /\
r + 16 + Spa.u32_at (x_bs x) (r + 8) <= x_len x.
(* the registers the foreach keeps from its setup (0x832dc .. 0x832fc) *)
Definition l2_regs (x : pctx) (r c : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 9 = w64 (x_P x + c) /\ getr regs2 18 = w64 A_KEY /\ getr regs2 20 = w64 8 /\
getr regs2 21 = w64 (x_P x + r + 16) /\ getr regs2 22 = w64 (x_P x + r + 8 + Spa.u32_at (x_bs x) (r + 8)) /\
getr regs2 23 = w64 (Spa.u32_at (x_bs x) (r + 8) - 8).
(* a pending key: the String child at ck lies in the pod *)
Definition key_ok (x : pctx) (ck : Z) : Prop :=
0 <= ck /\ ck + 8 + Spa.u32_at (x_bs x) ck <= x_len x /\ Spa.spa_get_string (Spa.child_at (x_bs x) ck) <> None.
Definition l2_fuel (x : pctx) (r c : Z) : nat := S (Z.to_nat (r + 16 + Spa.u32_at (x_bs x) (r + 8) - c)).

Definition L2_at (x : pctx) (r c : Z) (ko : option Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
FI x regs2 mem2 md2 /\ l2_regs x r c regs2 /\
getr regs2 11 = w64 (match ko with None => 0 | Some ck => x_P x + ck + 8 end) /\
struct_ok x r /\ r + 16 <= c <= r + 16 + Spa.u32_at (x_bs x) (r + 8) + 7 /\ c mod 4 = 0 /\
(forall ck, ko = Some ck -> key_ok x ck) /\
x_res x = walk_res (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8)) c (l2_fuel x r c) (l2_key (x_bs x) ko).

(* the child at c lies inside the Struct body (the foreach's bounds tests passed) *)
Definition child_in (x : pctx) (r c : Z) : Prop :=
Spa.pod_is_inside (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8)) c = true.
Definition s8_val (x : pctx) (c : Z) : Z := Z.shiftr (x_P x + c) 3 + SHADOW_OFF.

(* the String child at c: its last body byte's instrumented check (a0), the child's body (a1); the key slot was
   empty *)
Definition LB_at (x : pctx) (r c : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
FI x regs2 mem2 md2 /\ l2_regs x r c regs2 /\ getr regs2 24 = w64 (s8_val x c) /\
getr regs2 11 = w64 (x_P x + c + 8) /\ getr regs2 10 = w64 (x_P x + c + 8 + Spa.u32_at (x_bs x) c - 1) /\
struct_ok x r /\ r + 16 <= c /\ c mod 4 = 0 /\ child_in x r c /\
1 <= Spa.u32_at (x_bs x) c < Spa.SPA_POD_MAX_SIZE /\ Spa.u32_at (x_bs x) (c + 4) = Model.POD_STRING /\
x_res x = walk_res (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8)) c (l2_fuel x r c) None.

(* after strcmp returned rv for the key of the child at ck, at the child c *)
Definition K_at (x : pctx) (r c ck rv : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
FI x regs2 mem2 md2 /\ l2_regs x r c regs2 /\ getr regs2 24 = w64 (s8_val x c) /\ getr regs2 10 = w64 rv /\
struct_ok x r /\ r + 16 <= c /\ c mod 4 = 0 /\ child_in x r c /\ key_ok x ck /\
-1 <= rv <= 1 /\ (rv = 0 <-> l2_key (x_bs x) (Some ck) = Some Role.ROLE_KEY) /\
x_res x = walk_res (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8)) c (l2_fuel x r c) (l2_key (x_bs x) (Some ck)).

(* the Float value's bits b at F + 8 *)
Definition FV_at (x : pctx) (b : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
FI x regs2 mem2 md2 /\ val_mem rsegs (mrestrict (w_H (x_W x)) mem2) (x_F x + 8) 4 b /\ getr regs2 12 = w64 A_FV_A2 /\
0 <= b < 2 ^ 32 /\
x_res x = match Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX with
          | Some m => Role.flag_rc m | None => (None, -1) end.

(* the flag v in a1, at the float state fx2 the path to T left *)
Definition T_at (x : pctx) (v : Z) (fx2 : YK11.FPState) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
FI x regs2 mem2 md2 /\ getr regs2 11 = w64 v /\ - 2 ^ 31 <= v < 2 ^ 31 /\ rl_fxk [13; 14; 15] fx fx2 /\
x_res x = Role.flag_rc v.

(* ---------------------------------- what reaching a cut means ---------------------------------- *)
Definition H_ok (x : pctx) : Prop := forall regs2 mem2 md2,
H_at x regs2 mem2 md2 -> SRr rsegs (x_W x) (cfg_at rsegs PC_H regs2 mem2 md2) (PPOST x false).
Definition L1_ok (x : pctx) (r : Z) : Prop := forall regs2 mem2 md2,
L1_at x r regs2 mem2 md2 -> SRr rsegs (x_W x) (cfg_at rsegs PC_L1 regs2 mem2 md2) (PPOST x false).
Definition L2_ok (x : pctx) (r c : Z) (ko : option Z) : Prop := forall regs2 mem2 md2,
L2_at x r c ko regs2 mem2 md2 -> SRr rsegs (x_W x) (cfg_at rsegs PC_L2 regs2 mem2 md2) (PPOST x false).
Definition LB_ok (x : pctx) (r c : Z) : Prop := forall regs2 mem2 md2,
LB_at x r c regs2 mem2 md2 -> SRr rsegs (x_W x) (cfg_at rsegs PC_LB regs2 mem2 md2) (PPOST x false).
Definition K_ok (x : pctx) (r c ck rv : Z) : Prop := forall regs2 mem2 md2,
K_at x r c ck rv regs2 mem2 md2 -> SRr rsegs (x_W x) (cfg_at rsegs PC_K regs2 mem2 md2) (PPOST x false).
Definition FV_ok (x : pctx) (b : Z) : Prop := forall regs2 mem2 md2,
FV_at x b regs2 mem2 md2 -> SRr rsegs (x_W x) (cfg_at rsegs PC_FV regs2 mem2 md2) (PPOST x false).
Definition T_ok (x : pctx) (v : Z) : Prop := forall (fx2 : YK11.FPState) regs2 mem2 md2,
T_at x v fx2 regs2 mem2 md2 -> SRr rsegs (x_W x) (cfg_at (fx := fx2) rsegs PC_T regs2 mem2 md2) (PPOST x false).

(* ---------------------------------- the segment statements ---------------------------------- *)
(* each walk file proves one of these under the Section hypotheses LAWS, MTL, HGOT, HCELL (and STRCMP for L);
   lib/AU/RPgParse.v composes them *)
Definition segE1_stmt : Prop := forall x null, call_ok x null -> (null = false -> H_ok x) ->
SRr rsegs (x_W x) (cfg_at rsegs A_PARSE (x_regs x) (x_memc x) (x_mdc x)) (PPOST x null).
Definition segE2_stmt : Prop := forall x, pre_ok x -> (forall r, L1_ok x r) -> H_ok x.
Definition segF_stmt : Prop := forall x r, pre_ok x ->
(forall r', r < r' <= x_len x + 7 -> L1_ok x r') -> (forall r0 c ko, L2_ok x r0 c ko) -> L1_ok x r.
Definition segL_stmt : Prop := forall x r c ko, pre_ok x ->
(forall c' ko', c < c' <= r + 16 + Spa.u32_at (x_bs x) (r + 8) + 7 -> L2_ok x r c' ko') ->
LB_ok x r c -> (forall ck rv, K_ok x r c ck rv) -> L2_ok x r c ko.
Definition segLB_stmt : Prop := forall x r c, pre_ok x ->
(forall c' ko', c < c' <= r + 16 + Spa.u32_at (x_bs x) (r + 8) + 7 -> L2_ok x r c' ko') -> LB_ok x r c.
Definition segK_stmt : Prop := forall x r c ck rv, pre_ok x ->
(forall c' ko', c < c' <= r + 16 + Spa.u32_at (x_bs x) (r + 8) + 7 -> L2_ok x r c' ko') ->
(forall v, T_ok x v) -> (forall b, FV_ok x b) -> K_ok x r c ck rv.
Definition segFV_stmt : Prop := forall x b, pre_ok x -> (forall v, T_ok x v) -> FV_ok x b.
Definition segT_stmt : Prop := forall x v, pre_ok x -> T_ok x v.

(* ======================================= shared lemmas ======================================= *)
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma pre_ok_call : forall x, pre_ok x -> call_ok x false.
Proof. intros x H. exact H. Qed.

(* the pod facts of a non-NULL call *)
Lemma pre_pod : forall x, pre_ok x ->
0 < x_P x /\ x_P x mod 16 = 0 /\ 8 <= x_len x /\ x_SZ x = x_len x - 8 /\ x_P x + x_len x <= 2 ^ 63 /\
garr8 rsegs (mrestrict (w_H (x_W x)) (x_memc x)) (x_P x) (bvals (x_bs x)) /\
range_addressable (aview rsegs (w_H (x_W x)) (x_memc x)) SHADOW_OFF (x_P x) (x_len x) /\
shadow_hull_vis (aview rsegs (w_H (x_W x)) (x_memc x)) (x_P x) (x_len x) /\
amem_range (x_P x) (x_len x) /\
(x_P x + x_len x <= x_sp x - T_parse_STK \/ x_sp x <= x_P x).
Proof. intros x (_ & _ & _ & Hpod & _). exact (Hpod eq_refl). Qed.

(* the stack the callee uses lies above the allocator's ceiling, so above every shadow byte of application memory
   and above the image *)
Lemma pre_stack : forall x, pre_ok x ->
alloc_ceiling <= x_sp x - T_parse_STK /\ x_sp x <= x_sp0 x /\ x_sp0 x <= 2 ^ 47 /\ x_sp x mod 16 = 0 /\
x_sp0 x - x_STK x <= x_sp x - T_parse_STK.
Proof.
intros x ((HJ & _ & _ & _ & _ & Hal & Hlo & Hhi & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _). unfold x_sp. lia.
Qed.

(* Q is positive and 4-aligned: rl_wcell puts its 4 bytes in the caller's stack window (above the allocator's
   ceiling, astk_ok) or in a side-stack frame the caller holds (at 4096 or above, the frames law's in_app) *)
Lemma pre_q : forall x, pre_ok x -> 0 < x_Q x /\ x_Q x mod 4 = 0.
Proof.
intros x ((HJ & _) & _ & _ & _ & HWC & HQ4 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
split; [|exact HQ4].
destruct HWC as [[Hw | (cid & pos & Hown & Hcid & Hf1 & Hf2)] _].
- lia.
- assert (Hin : In (cid, pos) (frames (x_Sc x))) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hin) as (_ & Happ & _).
  unfold in_app in Happ. lia.
Qed.

(* a byte the callee's stack does not hold *)
Lemma kept_view : forall x regs2 mem2 md2 a, FI x regs2 mem2 md2 -> 0 <= a < 2 ^ 64 ->
~ (x_sp x - T_parse_STK <= a < x_sp x) ->
aview rsegs (w_H (x_W x)) mem2 a = aview rsegs (w_H (x_W x)) (x_memc x) a.
Proof. intros x regs2 mem2 md2 a (_ & _ & HK & _) Ha Hn. exact (HK a Ha Hn). Qed.

Lemma mbyte_of_kept : forall (H : word -> bool) (m m' : word -> option byte) a, 0 <= a < 2 ^ 64 ->
aview rsegs H m' a = aview rsegs H m a -> mbyte rsegs (mrestrict H m') a = mbyte rsegs (mrestrict H m) a.
Proof. intros H m m' a Ha E. apply (mbyte_of_aview rsegs). exact E. Qed.

(* the shadow address of an application byte lies below the allocator's ceiling *)
Lemma shadow_below_ceiling : forall a, 0 <= a < kHighMemEnd -> SHADOW_OFF + a / 8 + 8 <= alloc_ceiling.
Proof.
intros a Ha. assert (a / 8 <= 0x100000000000) by (apply Z.div_le_upper_bound; unfold kHighMemEnd in Ha; lia).
pose proof alloc_ceiling_value as [[Hc1 Hc2] _]. unfold SHADOW_OFF. lia.
Qed.

Lemma amem_range_bounds : forall p n, 0 <= p -> 0 < n -> amem_range p n -> p + n < kHighMemEnd.
Proof. intros p n Hp Hn [H|[H1 H2]]; pose proof asan_consts as (C1 & C2 & C3 & C4 & C5); unfold kLowMemEnd, kHighMemEnd in *; lia. Qed.

(* the pod, its shadow and its hull are as at the call at every cut *)
Lemma pod_at_cut : forall x regs2 mem2 md2, pre_ok x -> FI x regs2 mem2 md2 ->
garr8 rsegs (mrestrict (w_H (x_W x)) mem2) (x_P x) (bvals (x_bs x)) /\
range_addressable (aview rsegs (w_H (x_W x)) mem2) SHADOW_OFF (x_P x) (x_len x) /\
shadow_hull_vis (aview rsegs (w_H (x_W x)) mem2) (x_P x) (x_len x).
Proof.
intros x regs2 mem2 md2 Hpre HFI.
pose proof (pre_pod x Hpre) as (HP0 & _ & Hl8 & _ & HP63 & HG & HRA & HHV & HAM & HDJ).
pose proof (pre_stack x Hpre) as (Hceil & Hsp & H47 & _ & _).
pose proof (amem_range_bounds (x_P x) (x_len x) ltac:(lia) ltac:(lia) HAM) as Hhm.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KS : forall s, 0 <= s < alloc_ceiling -> aview rsegs (w_H (x_W x)) mem2 s = aview rsegs (w_H (x_W x)) (x_memc x) s).
{ intros s Hs. apply (kept_view x regs2 mem2 md2 s HFI); [pose proof alloc_ceiling_lt; lia | lia]. }
split; [|split].
- intros j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
  intros kk Hkk. assert (kk = 0%nat) as -> by lia. specialize (Hv 0%nat ltac:(lia)).
  rewrite <- Hv. apply mbyte_of_kept; [unfold bvals in Hj; rewrite length_map in Hj; unfold x_len in *; lia|].
  apply (kept_view x regs2 mem2 md2 _ HFI); unfold bvals in Hj; rewrite length_map in Hj; unfold x_len in *;
  [lia | destruct HDJ; lia].
- intros a Ha. destruct (HRA a Ha) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. apply KS. unfold shadow_of_addr. pose proof (shadow_below_ceiling a ltac:(lia)).
  assert (0 <= a / 8) by (apply Z.div_pos; lia). unfold SHADOW_OFF in *. lia.
- intros s Hs Hn. apply (HHV s Hs). rewrite <- (KS s); [exact Hn|].
  set (Y := x_P x + x_len x - 1) in *.
  pose proof (shadow_below_ceiling Y ltac:(subst Y; lia)) as M.
  assert (0 <= shadow_addr (x_P x)) by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (x_P x) 8 ltac:(lia) ltac:(lia)); lia).
  pose proof (Z.mul_div_le (shadow_addr Y) 8 ltac:(lia)) as M2.
  assert (0 <= shadow_addr (x_P x) / 8) by (apply Z.div_pos; lia).
  unfold shadow_addr in *. lia.
Qed.

(* ---------------------------------- the pod's bytes ---------------------------------- *)
Lemma nth_error_le_bytes : forall n z k, (k < n)%nat ->
nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.
Lemma nth_error_firstn_lt : forall {A} (l : list A) n i, (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
intros A l. induction l as [|a l IH]; intros n i Hi.
- destruct n; destruct i; reflexivity.
- destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth_error]. apply IH. lia.
Qed.
Lemma nth_error_skipn_add : forall {A} (l : list A) m i, nth_error (skipn m l) i = nth_error l (m + i).
Proof.
intros A l m. revert l. induction m as [|m IH]; intros l i; [reflexivity|].
destruct l as [|a l]; [destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

(* the u32 at offset o of the pod, read in any memory that holds the pod *)
Lemma pod_u32 : forall x (m : word -> option byte) o,
garr8 rsegs m (x_P x) (bvals (x_bs x)) -> 0 <= o -> o + 4 <= x_len x ->
val_mem rsegs m (x_P x + o) 4 (Spa.u32_at (x_bs x) o).
Proof.
intros x m o HG Ho Ho4 kk Hkk.
assert (Hj : (Z.to_nat o + kk < length (bvals (x_bs x)))%nat) by (unfold bvals, x_len in *; rewrite length_map; lia).
pose proof (garr8_mbyte rsegs m (x_P x) (bvals (x_bs x)) _ HG Hj) as Hm.
replace (x_P x + Z.of_nat (Z.to_nat o + kk)) with (x_P x + o + Z.of_nat kk) in Hm by lia.
rewrite Hm. f_equal.
set (l := firstn 4 (skipn (Z.to_nat o) (x_bs x))).
assert (Hl : length l = 4%nat) by (subst l; rewrite length_firstn, length_skipn; unfold x_len in *; lia).
pose proof (Cursor.rd32_range (skipn (Z.to_nat o) (x_bs x))) as Hr.
change (Spa.u32_at (x_bs x) o) with (bytes_le_to_Z l). change (Cursor.rd32 (skipn (Z.to_nat o) (x_bs x))) with (bytes_le_to_Z l) in Hr.
rewrite le_byte_small by (cbn; lia).
assert (E1 : nth_error l kk = Some (Z_to_bv 8 (Z.shiftr (bytes_le_to_Z l) (8 * Z.of_nat kk)))).
{ rewrite <- (YA0d.Z_to_le_bytes_to_Z l) at 1. rewrite Hl. apply nth_error_le_bytes. exact Hkk. }
assert (E2 : nth_error l kk = nth_error (x_bs x) (Z.to_nat o + kk)).
{ subst l. rewrite nth_error_firstn_lt by exact Hkk. apply nth_error_skipn_add. }
rewrite E2 in E1.
assert (E3 : nth_error (bvals (x_bs x)) (Z.to_nat o + kk) = Some (bv_unsigned (Z_to_bv 8 (Z.shiftr (bytes_le_to_Z l) (8 * Z.of_nat kk))))).
{ unfold bvals. rewrite nth_error_map, E1. reflexivity. }
rewrite (nth_error_nth _ _ 0 E3). apply Z_to_bv_bv_unsigned.
Qed.

(* the byte at offset o of the pod *)
Lemma pod_u8 : forall x (m : word -> option byte) o,
garr8 rsegs m (x_P x) (bvals (x_bs x)) -> 0 <= o -> o < x_len x ->
val_mem rsegs m (x_P x + o) 1 (nth (Z.to_nat o) (bvals (x_bs x)) 0) /\ 0 <= nth (Z.to_nat o) (bvals (x_bs x)) 0 < 256.
Proof.
intros x m o HG Ho Hlt. apply garr8_nthZ; [exact HG | exact Ho |]. unfold bvals, x_len in *. rewrite length_map. lia.
Qed.

Lemma u32_at_range : forall bs o, 0 <= Spa.u32_at bs o < 2 ^ 32.
Proof. intros bs o. apply Cursor.rd32_range. Qed.

(* an instrumented check of the bytes [P + o + lo, P + o + hi) inside the pod passes: the shadow entry of the atom
   m that holds P + o *)
Lemma shent_pod : forall x regs2 mem2 md2 E Bx (m : nat) o lo hi, pre_ok x -> FI x regs2 mem2 md2 ->
U E Bx = SHADOW_OFF -> U E (SOff m 0) = x_P x + o -> 0 <= o + lo -> o + hi <= x_len x -> lo < hi ->
shent_ok rsegs Bx E (mrestrict (w_H (x_W x)) mem2) (mkSHE m lo hi).
Proof.
intros x regs2 mem2 md2 E Bx m o lo hi Hpre HFI HB Hm H1 H2 H3.
pose proof (pod_at_cut x regs2 mem2 md2 Hpre HFI) as (_ & HRA & _).
pose proof (pre_pod x Hpre) as (HP0 & _ & Hl8 & _ & HP63 & _ & _ & _ & HAM & _).
apply (shent_ok_of_range rsegs (w_H (x_W x)) mem2 E Bx m (x_P x) (x_len x) (x_P x + o) lo hi HRA HB Hm); [lia | lia |].
intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia.
destruct HAM as [HL | [HH1 HH2]];
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5); unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *; lia.
Qed.

(* ---------------------------------- the frame ---------------------------------- *)
Lemma saved_nth : forall x j, (j < 10)%nat ->
nth j (saved_vals (x_regs x)) (Z_to_bv 64 0) = getr (x_regs x) (Z_to_bv 5 (snd (nth j SAVED (0, 0)))).
Proof.
intros x j Hj. unfold saved_vals.
do 10 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

Lemma cut_env_saved : forall x regs2 L j, (j < 10)%nat ->
ew (cut_env x regs2 L) (33 + j) = getr (x_regs x) (Z_to_bv 5 (snd (nth j SAVED (0, 0)))).
Proof.
intros x regs2 L j Hj. unfold cut_env.
replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra. cbn [nth].
rewrite app_nth1 by (unfold saved_vals; rewrite length_map; cbn; lia).
apply saved_nth. exact Hj.
Qed.

Lemma cut_env_reg : forall x regs2 L (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
ew (cut_env x regs2 L) n = getr regs2 r.
Proof. intros x regs2 L n r H. unfold cut_env. apply ew_Ereg_nat. exact H. Qed.

Lemma cut_env_sb : forall x regs2 L, ew (cut_env x regs2 L) 32 = w64 SBr.
Proof. intros x regs2 L. unfold cut_env. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.

Lemma cut_env_seg : forall x regs2 L j,
ew (cut_env x regs2 L) (43 + j) = nth j L (Z_to_bv 64 0).
Proof.
intros x regs2 L j. unfold cut_env.
replace (43 + j)%nat with (32 + S (10 + j))%nat by lia. rewrite ew_Ereg_extra.
cbn [nth]. rewrite app_nth2 by (unfold saved_vals; rewrite length_map; cbn; lia).
unfold saved_vals. rewrite length_map. cbn [length SAVED]. f_equal. lia.
Qed.

Lemma sv_denot_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* the frame region holds the saved words: from FI, at a segment's entry *)
Lemma frame_region_ok : forall x regs2 mem2 md2 L (cs : list YP09.chunk),
FI x regs2 mem2 md2 -> pre_ok x ->
Forall (YP09.chunk_ok rsegs (cut_env x regs2 L) (mrestrict (w_H (x_W x)) mem2) (x_F x)) cs ->
region_ok rsegs (cut_env x regs2 L) (mrestrict (w_H (x_W x)) mem2) (frame_region cs).
Proof.
intros x regs2 mem2 md2 L cs HFI Hpre Hcs.
pose proof (pre_stack x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin). pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
destruct HFI as (HJ & _ & _ & HSV & H2 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hb : base_val (cut_env x regs2 L) (Some 2%nat) = x_F x).
{ cbn [base_val]. rewrite (cut_env_reg x regs2 L 2 2%bv eq_refl), H2. unfold w64.
  rewrite unsigned_lit_small; [reflexivity|]. unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *. lia. }
unfold region_ok, frame_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite Hb.
split; [unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia|].
split; [unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia|]. split.
- intros o Ho. apply (apresent_writable rsegs). apply Hpres.
  unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia.
- apply Forall_app. split; [exact Hcs|].
  unfold SAVED in HSV.
  inversion HSV as [|c1 l1 V1 HSV1]; subst. inversion HSV1 as [|c2 l2 V2 HSV2]; subst.
  inversion HSV2 as [|c3 l3 V3 HSV3]; subst. inversion HSV3 as [|c4 l4 V4 HSV4]; subst.
  inversion HSV4 as [|c5 l5 V5 HSV5]; subst. inversion HSV5 as [|c6 l6 V6 HSV6]; subst.
  inversion HSV6 as [|c7 l7 V7 HSV7]; subst. inversion HSV7 as [|c8 l8 V8 HSV8]; subst.
  inversion HSV8 as [|c9 l9 V9 HSV9]; subst. inversion HSV9 as [|c10 l10 V10 _]; subst.
  cbn [fst snd] in V1, V2, V3, V4, V5, V6, V7, V8, V9, V10.
  unfold saved_chunks. repeat apply Forall_cons; try apply Forall_nil;
  match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
    let j := eval vm_compute in (n - 33)%nat in
    apply (chunk_ok_val rsegs _ _ _ off 8 (SOff n 0) (bv_unsigned (getr (x_regs x) (Z_to_bv 5 (snd (nth j SAVED (0, 0)))))));
    [ rewrite sv_denot_SOff0; change n with (33 + j)%nat; rewrite cut_env_saved by lia; symmetry; apply Z_to_bv_bv_unsigned
    | apply bv_unsigned_in_range | lia | cbn [nth snd N.to_nat Pos.to_nat]; assumption ] end.
Qed.

(* the frame's saved words, read back from a segment's final state, for the next cut's FI *)
Definition saved_idx (r : Z) : nat :=
if r =? 1 then 0 else if r =? 8 then 1 else if r =? 9 then 2 else if r =? 18 then 3 else if r =? 19 then 4 else
if r =? 20 then 5 else if r =? 21 then 6 else if r =? 22 then 7 else if r =? 23 then 8 else 9.
Lemma saved_of_frame_region : forall x E (m : word -> option byte) (cs : list YP09.chunk),
region_ok rsegs E m (frame_region cs) ->
base_val E (Some 2%nat) = x_F x ->
(forall j, (j < 10)%nat -> ew E (33 + j) = getr (x_regs x) (Z_to_bv 5 (snd (nth j SAVED (0, 0))))) ->
Forall (fun c => val_mem rsegs m (x_F x + fst c) 8 (bv_unsigned (getr (x_regs x) (Z_to_bv 5 (snd c))))) SAVED.
Proof.
intros x E m cs HR Hb HE.
unfold region_ok, frame_region in HR. cbn [YP09.r_base YP09.r_chunks] in HR. rewrite Hb in HR.
destruct HR as (_ & _ & _ & HC). apply Forall_app in HC as [_ HC]. unfold saved_chunks in HC.
assert (HC' : forall off n, In (YP09.mkChunk off (CVal 8 (SOff n 0))) saved_chunks ->
  YP09.chunk_ok rsegs E m (x_F x) (YP09.mkChunk off (CVal 8 (SOff n 0)))).
{ intros off n Hin. eapply Forall_forall; [exact HC | exact Hin]. }
unfold SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
match goal with |- val_mem _ _ (_ + ?off) 8 (bv_unsigned (getr _ (Z_to_bv 5 ?r))) =>
  let j := eval vm_compute in (saved_idx r) in
  let n := eval vm_compute in (33 + j)%nat in
  apply (val_of_chunk_ok rsegs E m (x_F x) off 8 (SOff n 0) _ (HC' off n ltac:(unfold saved_chunks; cbn; tauto)));
  [ rewrite sv_denot_SOff0; change n with (33 + j)%nat; rewrite (HE j ltac:(lia)); cbn [nth snd]; symmetry; apply Z_to_bv_bv_unsigned
  | apply bv_unsigned_in_range | lia ] end.
Qed.

(* ---------------------------------- the leaf ---------------------------------- *)
(* the registers after the epilogue: every callee-saved one as at the call, ra too *)
Lemma leaf_regs : forall x regs2 L E ss ms (H : word -> bool), pre_ok x ->
st_ok rsegs E ss (restrict H ms) ->
(forall n, (n < 43)%nat -> ew E n = ew (cut_env x regs2 L) n) ->
leaf_sr_ok (ss_regs ss) = true ->
getr regs2 2 = w64 (x_F x) ->
(forall r, r = 3 \/ r = 4 \/ r = 25 \/ r = 26 \/ r = 27 -> getr regs2 (Z_to_bv 5 r) = getr (x_regs x) (Z_to_bv 5 r)) ->
aregs_preserved (x_regs x) (ms_regs ms) /\ getr (ms_regs ms) 1 = getr (x_regs x) 1.
Proof.
intros x regs2 L E ss ms H Hpre HS HE Hok H2 Hcs.
pose proof (pre_stack x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin). pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (G : forall p, In p leaf_sr -> getr (ms_regs ms) (Z_to_bv 5 (fst p)) = sv_denot E (snd p)).
{ intros p Hp. rewrite (st_ok_restrict_reg rsegs H E ss ms _ HS). apply sv_eqb_denot.
  unfold leaf_sr_ok in Hok. exact (proj1 (forallb_forall _ _) Hok p Hp). }
assert (Gs : forall n r, In (r, SOff n 0) leaf_sr -> (n < 43)%nat ->
  getr (ms_regs ms) (Z_to_bv 5 r) = ew (cut_env x regs2 L) n).
{ intros n r Hp Hn. pose proof (G _ Hp) as Gp. cbn [fst snd] in Gp. rewrite Gp, sv_denot_SOff0. apply HE. exact Hn. }
assert (Gv : forall j r, (j < 10)%nat -> In (r, SOff (33 + j) 0) leaf_sr -> snd (nth j SAVED (0, 0)) = r ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr (x_regs x) (Z_to_bv 5 r)).
{ intros j r Hj Hp Hr. rewrite (Gs _ r Hp) by lia. rewrite cut_env_saved by exact Hj. rewrite Hr. reflexivity. }
assert (Gc : forall r, (r = 3 \/ r = 4 \/ r = 25 \/ r = 26 \/ r = 27) -> In (r, SOff (Z.to_nat r) 0) leaf_sr ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr (x_regs x) (Z_to_bv 5 r)).
{ intros r Hr Hp. rewrite (Gs _ r Hp) by (destruct Hr as [-> | [-> | [-> | [-> | ->]]]]; cbn; lia).
  rewrite (cut_env_reg x regs2 L (Z.to_nat r) (Z_to_bv 5 r)) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; destruct Hr as [-> | [-> | [-> | [-> | ->]]]]; reflexivity).
  exact (Hcs r Hr). }
assert (Hsp2 : getr (ms_regs ms) (Z_to_bv 5 2) = getr (x_regs x) (Z_to_bv 5 2)).
{ pose proof (G (2, SOff 2 FRAME) ltac:(cbn; tauto)) as Gp. cbn [fst snd] in Gp. rewrite Gp. cbn [sv_denot].
  rewrite (HE 2%nat ltac:(lia)), (cut_env_reg x regs2 L 2 2%bv eq_refl), H2. unfold w64.
  rewrite unsigned_lit_small by (unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia).
  unfold x_F, x_sp, FRAME. replace (spZ (x_regs x) - 96 + 96) with (spZ (x_regs x)) by lia.
  unfold spZ. apply Z_to_bv_bv_unsigned. }
split.
- intros r Hr. unfold acallee_saved in Hr.
  assert (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
          r = 24 \/ r = 25 \/ r = 26 \/ r = 27) as Hr' by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + exact Hsp2.
  + apply Gc; [tauto | cbn; tauto].
  + apply Gc; [tauto | cbn; tauto].
  + apply (Gv 1%nat); [lia | cbn; tauto | reflexivity].
  + apply (Gv 2%nat); [lia | cbn; tauto | reflexivity].
  + apply (Gv 3%nat); [lia | cbn; tauto | reflexivity].
  + apply (Gv 4%nat); [lia | cbn; tauto | reflexivity].
  + apply (Gv 5%nat); [lia | cbn; tauto | reflexivity].
  + apply (Gv 6%nat); [lia | cbn; tauto | reflexivity].
  + apply (Gv 7%nat); [lia | cbn; tauto | reflexivity].
  + apply (Gv 8%nat); [lia | cbn; tauto | reflexivity].
  + apply (Gv 9%nat); [lia | cbn; tauto | reflexivity].
  + apply Gc; [tauto | cbn; tauto].
  + apply Gc; [tauto | cbn; tauto].
  + apply Gc; [tauto | cbn; tauto].
- replace (1%bv : bv 5) with (Z_to_bv 5 1) by (apply bv_eq; reflexivity). apply (Gv 0%nat); [lia | cbn; tauto | reflexivity].
Qed.

(* the call's post-condition from the final state's facts *)
Lemma ppost_intro : forall x null (fx2 : YK11.FPState) regsF memF md2,
ajournal rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x)
(x_lyc x) (x_Sc x) (x_W x) memF md2 (x_k x) ->
same_io (x_mdc x) md2 ->
aregs_preserved (x_regs x) regsF ->
rl_fxk [13; 14; 15] fx fx2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) ->
 ~ (fst (rl_parse_res null (x_bs x)) <> None /\ x_Q x <= a < x_Q x + 4) ->
 aview rsegs (w_H (x_W x)) memF a = aview rsegs (w_H (x_W x)) (x_memc x) a) ->
getr regsF 10 = w64 (snd (rl_parse_res null (x_bs x))) ->
match fst (rl_parse_res null (x_bs x)) with
| Some r => val_mem rsegs (mrestrict (w_H (x_W x)) memF) (x_Q x) 4 (Role.role_z r)
| None => True end ->
PPOST x null (x_W x) (mkCfg (@mkst fx2 regsF (getr (x_regs x) 1) memF (seg_rom rsegs)) md2).
Proof.
intros x null fx2 regsF memF md2 HJ Hio Hpr Hfx HK H10 HR.
unfold PPOST, rl_post. exists fx2, (x_lyc x), (x_Sc x), regsF, memF, md2.
split; [reflexivity|]. split; [exact Hfx|]. split; [exact HJ|]. split; [exact Hpr|].
split; [reflexivity|]. split; [apply Permutation_refl|]. split; [exact Hio|].
split; [exact (mo_le_refl MT MTL (x_Sc x))|]. split; [exact HK|]. split; [exact H10 | exact HR].
Qed.

(* every segment before the float path runs at fx itself *)
Lemma rl_fxk_refl : forall ks, YK0o.frm_zero (@fp_csr fx) -> rl_fxk ks fx fx.
Proof. intros ks H. split; [intros; reflexivity | exact H]. Qed.
End b.
