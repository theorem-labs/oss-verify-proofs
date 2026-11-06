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
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): THE SHARED LAYER of the walk of the piece value_nearest of segment M03 of
   LLVMFuzzerTestOneInput (0x80bc0), which lib/A/HPgM3dDisp.v (the value dispatch and the Bool and Int arms),
   lib/A/HPgM3dFlt.v (the Float arm with its five soft-float calls) and lib/A/HPgM3dA.v (the assembly into
   lib/A/HPgSegM.v's hq_piece_M3d_value_stmt) Require. No instruction is walked here.
   Proves no function (kind: segment lemma).

   THE PIECE. From VAL 0x83364 (lib/A/HPgSegM.v's HQ_VAL: the pair's key is a cell address ch / p, and the value
   entry is ent[m + 1]) to one of three cuts: CELL 0x83548 (the value is in range), RFA 0x83454 and RF 0x83460
   (the refusal fold). It is fuzz_headamp.c:140-141 with pod.h:94-122 and pod_nearest pod.h:152-171 inlined:
     0x83364 .. 0x83374  a0 := &ent[v] = t6 + 104 v, v = s4 (`li a0,0xd; slli a0,0x23; slli s4,0x20; mulhu; add`)
     0x83378 .. 0x83388  the instrumented check of a0 and `lw a1,0(a0)` = ent[v].type
     0x83390 / 0x83398 / 0x833a0   `beq a1,6` -> Float 0x83430, `beq a1,4` -> Int 0x833e8, `bne a1,2` -> RF
                         (each after its `li a2,c` at 0x8338c / 0x83394 / 0x8339c)
     Bool  0x833a4 .. 0x833e4  `sd a3,0x98(s1)`, size (< 4 -> RF), body word, `snez s4,a0`, `j` CELL
     Int   0x833e8 .. 0x8342c  the same, size (< 4 -> RFA), body word, `bgeu s4,0x100` -> RFA, `j` 0x83534
     Float 0x83430 .. 0x83530  size (< 4 -> RFA), `flw fs0`, the three binary32 tests against fs1 = -1.0f and
                               fs2 = 256.0f, the five soft-float calls and `bltu 0xff,s4` -> RFA
     Tail  0x83534 .. 0x83544  `sext.w a0,s4`, t2 / t6 reloaded from R+0xe0 / R+0xd8, t3 := 5,
                               `bltu s2,a0` -> RF (s2 is the param's top value), else CELL.
   The seven instrumented checks (0x83384, 0x833b8, 0x833d8, 0x833fc, 0x8341c, 0x83444, 0x834a0) are 4-byte loads
   inside [&ent[v], &ent[v] + 16), which lies in the first block; ONE shadow entry over the entry's own atom
   covers all seven, so the engine reads shadow 0 and every `bnez` is decided not taken. Their slow blocks
   (0x835f4, 0x83604, 0x83614, 0x83624, 0x83664, 0x83674, 0x83684) are inside the code table and are never
   entered.

   WHAT THIS FILE GIVES. The code table hv_tbl (204 words from 0x83364) and the engine's shadow base HV_Bx = the
   register s7; the entry state of a run that starts at one of the piece's pcs (hv_entry, with the overrides, the
   regions and the facts as arguments); the two regions the piece reads and writes (hv_frame at s1 = R, hv_ent at
   a0 = &ent[v]) with their region_ok lemmas; the facts hv_facts / hv_facts10; the shadow entry hv_SH; the run,
   branch and keep tactics; the address arithmetic of &ent[v] and the two sign extensions; and the stack and
   apartness facts of lib/A/HPgSeg.v's hs_pre that every arm needs. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09 YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgCalls HPgSeg HPgSegM HPgM3dVal.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== the pcs of the piece ===================================== *)
Definition HV_VAL : Z := 0x83364.    (* HPgSegM.HQ_VAL: the piece's first pc *)
Definition HV_TYL : Z := 0x83388.    (* `lw a1,0(a0)` = ent[v].type, after its check *)
Definition HV_TY6 : Z := 0x8338c.    (* `li a2,6` then `beq a1,a2` (0x83390) -> the Float arm *)
Definition HV_TY4 : Z := 0x83394.    (* `li a2,4` then `beq a1,a2` -> the Int arm *)
Definition HV_TY2 : Z := 0x8339c.    (* `li a2,2` then `bne a1,a2` -> RF *)
Definition HV_BOOL : Z := 0x833a4.   (* the Bool arm *)
Definition HV_INT : Z := 0x833e8.    (* the Int arm *)
Definition HV_FLT : Z := 0x83430.    (* the Float arm *)
Definition HV_FBODY : Z := 0x83490.  (* the Float arm's body check, after the size test *)
Definition HV_FLW : Z := 0x834a4.    (* `flw fs0,0(a0)` *)
Definition HV_FEQ : Z := 0x834a8.    (* `feq.s a0,fs0,fs0` *)
Definition HV_FLT1 : Z := 0x834b0.   (* `flt.s a0,fs0,fs1` *)
Definition HV_FLT2 : Z := 0x834b8.   (* `flt.s a0,fs2,fs0` *)
Definition HV_FMV : Z := 0x834c0.    (* `fmv.s fa0,fs0` *)
Definition HV_EXT : Z := 0x834c4.    (* `jal __extendsftf2` *)
Definition HV_EXTR : Z := 0x834c8.   (* its return address *)
Definition HV_CVT : Z := 0x834d0.    (* `fcvt.l.s s4,fs0,rtz` *)
Definition HV_FD : Z := 0x834d8.     (* `jal __floatditf` *)
Definition HV_FDR : Z := 0x834dc.
Definition HV_SUB : Z := 0x834ec.    (* `jal __subtf3` *)
Definition HV_SUBR : Z := 0x834f0.
Definition HV_GE : Z := 0x83500.     (* `jal __getf2` *)
Definition HV_GER : Z := 0x83504.
Definition HV_LT : Z := 0x83518.     (* `jal __lttf2` *)
Definition HV_LTR : Z := 0x8351c.
Definition HV_UP : Z := 0x83528.     (* `addi s4,s4,1` *)
Definition HV_JOIN : Z := 0x8352c.   (* `li a0,0xff` *)
Definition HV_TAIL : Z := 0x83534.   (* `sext.w a0,s4`: the Int and Float arms meet *)
Definition HV_RFA : Z := 0x83454.    (* HPgSegM.HQ_RFA *)
Definition HV_RF : Z := 0x83460.     (* HPgSegM.HQ_RF *)
Definition HV_CELL : Z := 0x83548.   (* HPgSegM.HQ_CELL *)
(* the real-frame cells the piece reads and writes *)
Definition HV_C_MHALF : Z := 0xa8.   (* the high word of -0.5L *)
Definition HV_C_HALF : Z := 0xb0.    (* the high word of 0.5L *)
Definition HV_C_ENT0 : Z := 0xd8.    (* &ent[0] = pp + 0x4014 *)
Definition HV_C_NENT : Z := 0xe0.    (* n_ent *)
Definition HV_C_HI : Z := 0x88.      (* the high word of d / frac *)
Definition HV_C_LO : Z := 0x90.      (* its low word *)
Definition HV_C_PARAM : Z := 0x98.   (* the param p *)

Lemma hv_pcs_himg : HV_VAL = HQ_VAL /\ HV_RFA = HQ_RFA /\ HV_RF = HQ_RF /\ HV_CELL = HQ_CELL.
Proof. repeat split; reflexivity. Qed.

(* ===================================== the image ===================================== *)
(* the 204 4-byte words 0x83364 .. 0x83690: the piece's own code, the two exits, the Tail, and the seven slow
   blocks of its instrumented checks *)
Definition HV_N : nat := 204.
Definition hv_tbl : ctable := Eval vm_compute in (build_table rsegs HV_VAL HV_N TEmpty).
Lemma hv_tbl_eq : hv_tbl = build_table rsegs HV_VAL HV_N TEmpty.
Proof. vm_cast_no_check (eq_refl hv_tbl). Qed.
Lemma hv_tbl_ok : table_ok rsegs hv_tbl.
Proof. rewrite hv_tbl_eq. apply build_table_ok0. unfold HV_VAL. lia. Qed.
Lemma hv_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma hv_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.

(* the shadow base: the code adds s7 (atom 23) to every shadow index *)
Definition HV_SB : Z := SHADOW_OFF.
Definition HV_Bx : sv := SOff 23 0.
Definition HV_Bspan : Z * Z := (HV_SB, HV_SB + 2 ^ 44 - 1).

(* ===================================== the entry state ===================================== *)
(* an override of a register by a value it already has keeps regs_ok *)
Lemma hv_regs_ok_override : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> r <> 0%bv -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hb0.
{ exfalso. apply Hr0. unfold bv_eqb in Hb0. apply Z.eqb_eq in Hb0. apply bv_eq. exact Hb0. }
specialize (Hr r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.

Definition hv_sr (ov : list (bv 5 * sv)) : list sv :=
  fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.

Lemma hv_regs_ok : forall regs extra (ov : list (bv 5 * sv)),
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs extra) (snd p) = getr regs (fst p)) ov ->
regs_ok (Ereg regs extra) (hv_sr ov) regs.
Proof.
intros regs extra ov Hov. unfold hv_sr.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
apply IH. apply hv_regs_ok_override; assumption. }
apply G. apply regs_ok_Ereg.
Qed.

Lemma hv_lit : forall E v, sv_denot E (SLit v) = w64 v.
Proof. intros E v. reflexivity. Qed.

Lemma hv_atom : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
sv_denot (Ereg regs extra) (SOff n 0) = getr regs r.
Proof.
intros regs extra n r Hn. apply bv_eq. rewrite denot_SOff, (ew_Ereg_nat regs extra n r Hn), Z.add_0_r.
apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs r)) as Hb.
change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the entry state of a run of this piece at pc: the registers as atoms with the overrides ov (register, value it
   already has), the regions rs, the facts G *)
Lemma hv_entry : forall pc ov rs G (W : world rsegs) regs2 extra mem2,
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs2 extra) (snd p) = getr regs2 (fst p)) ov ->
regions_wf rs = true ->
Forall (region_ok rsegs (Ereg regs2 extra) (mrestrict (w_H W) mem2)) rs ->
pairwise_disjoint (Ereg regs2 extra) rs ->
facts_ok (Ereg regs2 extra) G ->
st_ok rsegs (Ereg regs2 extra) (mkSS pc (hv_sr ov) rs None G)
(restrict (w_H W) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom rsegs))).
Proof.
intros pc ov rs G W regs2 extra mem2 Hov Hwf Hrs Hpd HG.
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); try assumption. apply hv_regs_ok. exact Hov.
Qed.

End b.

(* ===================================== the regions ===================================== *)
(* the real frame at s1 = R (atom 9): [R + lo, R + hi) known, [R + wlo, R + whi) writable, the chunks cs *)
Definition hv_frame (lo hi wlo whi : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 9%nat) lo hi wlo whi cs.
(* the value entry at a0 = &ent[v] (atom 10): its type, its size and the first four bytes of its body *)
Definition hv_ent (t s bw : sv) : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 16 0 0
  [YP09.mkChunk 0 (CVal 4 t); YP09.mkChunk 4 (CVal 4 s); YP09.mkChunk 8 (CVal 4 bw)].

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma hv_frame_ok : forall E (W : world rsegs) mem2 R STK sp0 lo hi wlo whi cs,
bv_unsigned (ew E 9) = R -> 0 <= R + lo -> R + hi <= 2 ^ 64 ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) mem2 a) ->
(wlo < whi -> sp0 - STK <= R + wlo /\ R + whi <= sp0) ->
Forall (YP09.chunk_ok rsegs E (mrestrict (w_H W) mem2) R) cs ->
region_ok rsegs E (mrestrict (w_H W) mem2) (hv_frame lo hi wlo whi cs).
Proof.
intros E W mem2 R STK sp0 lo hi wlo whi cs H9 Hlo Hhi Hpres Hwin Hcs.
apply (hm_rw_region rsegs E (w_H W) mem2 9 R lo hi wlo whi cs H9 Hlo Hhi); [|exact Hcs].
intros o Ho. apply Hpres. destruct (Hwin ltac:(lia)). lia.
Qed.

Lemma hv_ent_ok : forall E (W : world rsegs) mem2 a (t s bw : sv) (tv sv_ bv_ : Z),
bv_unsigned (ew E 10) = a -> 0 <= a -> a + 16 <= 2 ^ 64 ->
sv_denot E t = Z_to_bv 64 tv -> 0 <= tv < 2 ^ 32 ->
sv_denot E s = Z_to_bv 64 sv_ -> 0 <= sv_ < 2 ^ 32 ->
sv_denot E bw = Z_to_bv 64 bv_ -> 0 <= bv_ < 2 ^ 32 ->
val_mem rsegs (mrestrict (w_H W) mem2) a 4 tv ->
val_mem rsegs (mrestrict (w_H W) mem2) (a + 4) 4 sv_ ->
val_mem rsegs (mrestrict (w_H W) mem2) (a + 8) 4 bv_ ->
region_ok rsegs E (mrestrict (w_H W) mem2) (hv_ent t s bw).
Proof.
intros E W mem2 a t s bw tv sv_ bv_ H10 Ha0 Ha1 Dt Ht Ds Hs Db Hb Vt Vs Vb.
apply (hm_ro_region rsegs E (w_H W) mem2 10 a 0 16); [exact H10 | lia | lia |].
apply Forall_cons;
[ eapply (chunk_ok_val rsegs E _ a 0 4 t tv Dt); [lia | cbn; lia | rewrite Z.add_0_r; exact Vt]|].
apply Forall_cons;
[ eapply (chunk_ok_val rsegs E _ a 4 4 s sv_ Ds); [lia | cbn; lia | exact Vs]|].
apply Forall_cons;
[ eapply (chunk_ok_val rsegs E _ a 8 4 bw bv_ Db); [lia | cbn; lia | exact Vb]|].
apply Forall_nil.
Qed.

End r.

(* ===================================== the facts and the shadow entry ===================================== *)
(* atom 9 is s1 = R, atom 23 is s7 = the runtime's shadow offset, atom 10 is a0 = &ent[v] *)
Definition hv_facts : facts :=
mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition hv_facts10 : facts :=
mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
          (10%nat, mkAF 4096 0x7fffff800000 0) ] [] [].
(* the seven checks of this piece read shadow bytes of [&ent[v], &ent[v] + 16) *)
Definition hv_SH : list shent := [ mkSHE 10 0 16 ].

Lemma hv_facts_ok : forall E R,
bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
bv_unsigned (ew E 23) = SHADOW_OFF -> facts_ok E hv_facts.
Proof.
intros E R H9 HR Hal H23. split; [|split; [exact I | exact I]].
cbn [hv_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H9, H23. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
repeat split; try lia.
all: try apply Z.mod_1_r.
Qed.

Lemma hv_facts10_ok : forall E R a,
bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
bv_unsigned (ew E 23) = SHADOW_OFF ->
bv_unsigned (ew E 10) = a -> 4096 <= a <= 0x7fffff800000 -> facts_ok E hv_facts10.
Proof.
intros E R a H9 HR Hal H23 H10 Ha. split; [|split; [exact I | exact I]].
cbn [hv_facts10 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H9, H23, H10. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
repeat split; try lia.
all: try apply Z.mod_1_r.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma hv_sh_ok : forall (W : world rsegs) mem E a,
U E HV_Bx = SHADOW_OFF -> U E (SOff 10 0) = a ->
range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a 16 ->
(a + 16 <= kLowShadowBeg \/ kHighMemBeg <= a) ->
sh_ok rsegs HV_Bx hv_SH E (mrestrict (w_H W) mem).
Proof.
intros W mem E a HB H10 Hra Happ. apply Forall_cons; [|apply Forall_nil].
apply (YCbq.shent_ok_of_range rsegs (w_H W) mem E HV_Bx 10 a 16 a 0 16 Hra HB H10 ltac:(lia) ltac:(lia)).
intros x Hx. cbn [Z.min Z.max] in Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

End s.

(* ===================================== the value language ===================================== *)
(* 0x83364 .. 0x83374 `li a0,0xd; slli a0,a0,35; slli s4,s4,32; mulhu a0,s4,a0; add a0,t6,a0`:
   mulhu((i * 2^32) mod 2^64, 13 * 2^35) = 104 i for 0 <= i <= 32, since (i 2^32)(13 2^35) = 104 i 2^64. *)
Lemma hv_denot_a0 : forall E (n p : nat) (i b : Z),
  ew E n = Z_to_bv 64 i -> 0 <= i <= 32 ->
  ew E p = Z_to_bv 64 b -> 0 <= b -> b + 104 * i < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff p 0)
                (SMd M_MULHU (SAlu ALU_SLL (SOff n 0) (SLit 32)) (SLit 446676598784)))
  = Z_to_bv 64 (b + 104 * i).
Proof.
intros E n p i b Hn Hi Hp Hb Hs.
rewrite (denot_lit_U E). apply (f_equal (Z_to_bv 64)).
rewrite ?U_SAlu, ?U_SMd, ?U_SAlu, ?U_SOff, ?U_SLit, Hn, Hp, !Z.add_0_r.
rewrite !unsigned_lit_small by lia.
cbn [zalu_raw zmd_raw Z.of_N].
change (zcanon 32) with 32. change (zcanon 446676598784) with 446676598784.
change (Z.land 32 63) with 32.
rewrite (zcanon_id i), (zcanon_id b) by (unfold M64; lia).
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296.
rewrite (zcanon_id (i * 4294967296)) by (unfold M64; lia).
rewrite Z.shiftr_div_pow2 by lia.
replace (i * 4294967296 * 446676598784) with (104 * i * 2 ^ 64)
  by (change (2 ^ 64) with 18446744073709551616; lia).
rewrite Z.div_mul by (change (2 ^ 64) with 18446744073709551616; lia).
rewrite (zcanon_id (104 * i)) by (unfold M64; lia).
apply zcanon_id. unfold M64. lia.
Qed.

Lemma hv_U_a0 : forall E (n p : nat) (i b : Z),
  ew E n = Z_to_bv 64 i -> 0 <= i <= 32 ->
  ew E p = Z_to_bv 64 b -> 0 <= b -> b + 104 * i < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff p 0)
        (SMd M_MULHU (SAlu ALU_SLL (SOff n 0) (SLit 32)) (SLit 446676598784)))
  = b + 104 * i.
Proof.
intros E n p i b Hn Hi Hp Hb Hs. unfold U.
rewrite (hv_denot_a0 E n p i b Hn Hi Hp Hb Hs).
apply unsigned_lit_small. lia.
Qed.

(* the 64-bit word an `lw` of a 32-bit pattern leaves (lib/A/HPgM3dVal.v states it as hvm_sx, definitionally the
   same term) *)
Lemma hv_U_sext32 : forall E (n : nat) (v : Z),
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  U E (SExt true 32 (SOff n 0)) = (if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32)).
Proof.
intros E n v H Hv.
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

(* the `sext.w a0,s4` of the Tail, on a value that already fits in 31 bits *)
Lemma hv_U_sextw : forall E (a : sv) (v : Z), U E a = v -> 0 <= v < 2 ^ 31 ->
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

Lemma hv_denot_of_U : forall E (a : sv) (v : Z), U E a = v -> sv_denot E a = Z_to_bv 64 v.
Proof. intros E a v H. rewrite (denot_lit_U E a), H. reflexivity. Qed.

Lemma hv_U_atom : forall E (n : nat) (v : Z), ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  U E (SOff n 0) = v.
Proof. exact U_atom. Qed.

(* ===================================== the run, branch and keep tactics ===================================== *)
(* the write-range obligation: read-only regions, and the real frame (atom 9 = R) whose write window lies in the
   journal's stack window [sp0 - STK, sp0); E9 : bv_unsigned (ew E 9) = R, with the two window facts in context *)
Ltac hv_awr :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
repeat first
[ apply awr_ok_nil
| (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|])
| lazymatch goal with E9 : bv_unsigned (ew E 9) = ?R |- _ =>
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
  [reflexivity | rewrite E9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] end ]
end.

Ltac hv_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok hv_tbl_ok HS HJ SHOK HV_Bspan; [awr | ] end.
Ltac hv_run_to awr stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok hv_tbl_ok HS HJ SHOK HV_Bspan stop; [awr | ] end.
Ltac hv_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok hv_tbl_ok HS SH HV_Bspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.

(* a run keeps every byte outside the zone its write windows lie in *)
Lemma hv_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha.
intros X. exact (Hz (HW a X)).
Qed.

(* every write window of a state of this piece lies in [R + 0x88, R + 0xa0) *)
Ltac hv_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
   first [ lazymatch goal with E9 : bv_unsigned (ew _ 9) = _ |- _ => rewrite E9 in Hb end; lia | lia ] | ]);
destruct Hr.

Ltac hv_keep kwr :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _),
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (hv_kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by kwr end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Lemma hv_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.

(* ===================================== the segment's own facts ===================================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* the stack facts of hs_pre, as the engine's entry state and its write obligation need them *)
Lemma hv_stack : forall (cx : hs_scx rsegs) (sh : list Z), hs_pre rsegs B cx sh ->
spZ (x_regs rsegs cx) = e_R (x_e rsegs cx) /\ e_R (x_e rsegs cx) mod 32 = 0 /\
e_R (x_e rsegs cx) + 0x1e0 <= x_sp0 rsegs cx /\
x_sp0 rsegs cx - x_STK rsegs cx <= e_R (x_e rsegs cx) - T_SEG_STK /\
alloc_ceiling <= e_R (x_e rsegs cx) - T_SEG_STK /\
2 ^ 46 <= e_R (x_e rsegs cx) <= 2 ^ 47 /\ x_sp0 rsegs cx <= 2 ^ 47 /\
st_nev (x_S rsegs cx) + x_k rsegs cx <= EV_MAX /\
getr (x_regs rsegs cx) 2 = w64 (e_R (x_e rsegs cx)) /\
getr (x_regs rsegs cx) 3 = w64 (as_gp B) /\ getr (x_regs rsegs cx) 4 = w64 (as_tp B).
Proof using.
intros cx sh Hpre.
unfold hs_pre, hd_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & Hal & Hrsz & Hwin & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
cbn [hi_rsz headamp_himg_A] in Hrsz.
rewrite HS in Hrsz.
unfold T_SEG_STK, ASTACK in *.
assert (HR : spZ (x_regs rsegs cx) = e_R (x_e rsegs cx))
  by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; lia).
split; [exact HR|]. split; [exact Hal|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [exact Hev|]. split; [exact H2|].
split; [exact H3 | exact H4].
Qed.

(* the first block, the frame for locals and the entry the piece reads: where they lie *)
Lemma hv_apart : forall (cx : hs_scx rsegs) (sh : list Z), hs_pre rsegs B cx sh ->
In (e_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) /\
4096 <= e_pp (x_e rsegs cx) /\ e_pp (x_e rsegs cx) + Layout.PP_SIZE <= alloc_ceiling /\
(e_pp (x_e rsegs cx) + Layout.PP_SIZE <= kLowShadowBeg \/ kHighMemBeg <= e_pp (x_e rsegs cx)) /\
4096 <= e_F (x_e rsegs cx) /\ e_F (x_e rsegs cx) + 1024 <= alloc_ceiling /\
e_F (x_e rsegs cx) mod 32 = 0 /\
In (4, x_pos rsegs cx) (x_own rsegs cx).
Proof using.
intros cx sh Hpre.
pose proof Hpre as Hpre'. unfold hs_pre, hd_seg_pre in Hpre'.
destruct Hpre' as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfb).
destruct Hfb as (Hp0 & Hppin & _).
cbn [hi_cid headamp_himg_A] in Hown, HF.
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hin : In (4, x_pos rsegs cx) (frames (x_Sc rsegs cx)))
  by (rewrite Hfr; apply in_or_app; left; exact Hown).
destruct (al_blocks _ _ (AR_laws_ok rsegs B) _ _ _ _ _ _ _ HAR Hppin) as (_ & Hpp0 & Hppc & Happ & _).
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
split; [exact Hppin|]. split; [exact Hpp0|]. split; [exact Hppc|].
split; [destruct Happ' as [H|[H _]]; [left; exact H | right; exact H]|].
split; [exact HF0|]. split; [exact HFc|]. split; [exact H32 | exact Hown].
Qed.

(* a block of the segment's own state lies below the allocator's ceiling (YG0d AR_blocks_law) *)
Lemma hv_blk_low : forall (cx : hs_scx rsegs) (sh : list Z) (p n : Z), hs_pre rsegs B cx sh ->
In (p, n) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling.
Proof using.
intros cx sh p n Hpre Hin.
pose proof Hpre as Hpre'. unfold hs_pre, hd_seg_pre in Hpre'.
destruct Hpre' as (HJ & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ (AR_laws_ok rsegs B) _ _ _ _ _ _ _ HAR Hin) as (Hnz & H0 & Hc & _).
split; [exact Hnz|]. split; [exact H0 | exact Hc].
Qed.

(* ===================================== what a run of this piece may write =====================================
   the soft-float callees' stack below R and the three real-frame cells R+0x88, R+0x90 and R+0x98 *)
Definition hv_wz (cx : hs_scx rsegs) (a : Z) : Prop :=
(e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) \/
(e_R (x_e rsegs cx) + HV_C_HI <= a < e_R (x_e rsegs cx) + 0xa0).

Lemma hv_wz_low : forall (cx : hs_scx rsegs) (sh : list Z), hs_pre rsegs B cx sh ->
forall a, 0 <= a < alloc_ceiling -> ~ hv_wz cx a.
Proof using.
intros cx sh Hpre a Ha.
destruct (hv_stack cx sh Hpre) as (_ & _ & _ & _ & Hceil & _).
unfold hv_wz, HV_C_HI, T_SEG_STK, ASTACK in *. lia.
Qed.

(* the errno cell lies in the image, far below the allocator's ceiling *)
Lemma hv_errno_low : api_env rsegs B -> forall i, 0 <= i < 4 -> 0 <= as_errno B + i < alloc_ceiling.
Proof using.
intros HE i Hi. destruct HE as ((H0 & H1) & _ & _).
pose proof asan_consts as (C1 & _).
unfold kLowMemEnd in H1. lia.
Qed.

(* ===================================== a cut's value facts, across a run or a call ===================================== *)
Lemma hv_at_kept : forall (cx : hs_scx rsegs) (W2 W3 : world rsegs) mem2 mem3 regs2 regs3 (Wr : Z -> Prop) L,
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
aregs_preserved regs2 regs3 ->
Forall (fun f : hd_loc * Z => match fst f with
        | LReg r => acallee_saved r
        | LCell b o => forall i, 0 <= i < 8 ->
            0 <= hd_xv (x_e rsegs cx) b + o + i < 2 ^ 64 /\ ~ Wr (hd_xv (x_e rsegs cx) b + o + i)
        end) L ->
hs_at_cx rsegs cx W2 mem2 regs2 L -> hs_at_cx rsegs cx W3 mem3 regs3 L.
Proof using.
intros cx W2 W3 mem2 mem3 regs2 regs3 Wr L HK Hpres HL HAT.
unfold hs_at_cx, hs_at in HAT |- *.
apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W3) mem3 regs2 regs3 (x_e rsegs cx) L HAT).
intros f Hf.
apply (hm_keeps_call rsegs Wr 0 0 (w_H W2) mem2 (w_H W3) mem3 regs2 regs3 (x_e rsegs cx) (fst f));
[intros a Ha _ Hw; exact (HK a Ha Hw) | exact Hpres |].
pose proof (proj1 (Forall_forall _ _) HL f Hf) as Hm. cbv beta in Hm.
destruct (fst f) as [rr|b o]; [exact Hm|].
intros i Hi. destruct (Hm i Hi) as (H1 & H2). split; [exact H1|]. split; [lia | exact H2].
Qed.

(* ===================================== the two cuts inside the piece =====================================
   The piece is split into three lanes at two pcs of its own: FA 0x83430, the Float arm's first instruction, and
   TAIL 0x83534, where the Int and the Float arms meet. The Bool arm reaches HPgSegM's CELL straight from
   0x833e4 (a Bool value is 0 or 1 and every param's top value is at least 1, so the code elides the range
   test), and the three HPgSegM cuts CELL, RF and RFA are the piece's own exits. *)
(* the address of the value entry ent[m + 1] inside the first block *)
Definition hv_entA (cx : hs_scx rsegs) (m : nat) : Z :=
e_pp (x_e rsegs cx) + HQ_ENT0 + 104 * (Z.of_nat m + 1).

(* FA 0x83430: the type is Float; a0 = &ent[v], a3 = the param p, s2 = its top value, R+0xa0 = the channel.
   t2, t6, t3 and s4 are NOT carried: the Float arm neither reads them nor leaves to a cut that asks for them
   (its only exits are RFA 0x83454 and TAIL 0x83534). *)
Definition hv_cut_FA (cx : hs_scx rsegs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (v : Model.ent) (ch p : Z) (cs : list cell) (keys rf : Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
@hq_base3 fx rc SK rsegs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx rsegs cx W2 mem2 regs2
  (hq_L_seg rsegs cx ++ hq_L_loopc rsegs cx ++ hq_L_body rsegs cx r ++
   [(LReg 10, hv_entA cx m); (LReg 13, p); (LReg 18, hvm_top p);
    (LReg 21, Z.of_nat m + 2); (LCell XR 0xa0, ch)]) /\
hq_fs fx2 9 HQ_F32_M1 /\ hq_fs fx2 18 HQ_F32_256 /\
hq_live rsegs cx r /\ (at0 <= m)%nat /\
Headamp.expect_key (skipn (length Headamp.HA_PREFIX) k) = Headamp.KCell ch p /\
Model.e_type v = Model.POD_FLOAT /\
hq_pair_inv rsegs cx r m k v cs keys rf /\
Z.of_nat (length cs) <= keys /\
hq_x_at rsegs cx W2 mem2 cs (keys + 1) rf /\
val_mem rsegs (mrestrict (w_H W2) mem2) (hv_entA cx m + 4) 4 (Model.e_size v) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (hv_entA cx m + 8) 4 (Cursor.rd32 (Model.e_body v)) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (hv_entA cx m) 16.

(* TAIL 0x83534: the value val is read, 0 <= val <= 255; s2 = the param's top value, R+0x98 = the param,
   R+0xa0 = the channel. The Tail runs `sext.w a0,s4`, reloads t2 and t6, sets t3 to OUT_OF_RANGE and tests
   top < val. *)
Definition hv_cut_TAIL (cx : hs_scx rsegs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (v : Model.ent) (ch p val : Z) (cs : list cell) (keys rf : Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
@hq_base3 fx rc SK rsegs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx rsegs cx W2 mem2 regs2
  (hq_L_seg rsegs cx ++ hq_L_loopc rsegs cx ++ hq_L_body rsegs cx r ++
   [(LReg 18, hvm_top p); (LReg 20, val); (LReg 21, Z.of_nat m + 2);
    (LCell XR 0x98, p); (LCell XR 0xa0, ch)]) /\
hq_fs fx2 9 HQ_F32_M1 /\ hq_fs fx2 18 HQ_F32_256 /\
hq_live rsegs cx r /\ (at0 <= m)%nat /\
Headamp.expect_key (skipn (length Headamp.HA_PREFIX) k) = Headamp.KCell ch p /\
Headamp.cell_value v = val /\ 0 <= val <= 255 /\
hq_pair_inv rsegs cx r m k v cs keys rf /\
Z.of_nat (length cs) <= keys /\
hq_x_at rsegs cx W2 mem2 cs (keys + 1) rf.

(* the continuations of the two cuts *)
Definition hv_from_FA (cx : hs_scx rsegs) (r : Model.pod_rec)
(POST : world rsegs -> config -> Prop) (at0 m : nat) : Prop :=
forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 k v ch p cs keys rf,
hv_cut_FA cx fx2 r at0 m k v ch p cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr rsegs W2 (@cfg_at fx2 rsegs HV_FLT regs2 mem2 md2) POST.

Definition hv_from_TAIL (cx : hs_scx rsegs) (r : Model.pod_rec)
(POST : world rsegs -> config -> Prop) (at0 m : nat) : Prop :=
forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 k v ch p val cs keys rf,
hv_cut_TAIL cx fx2 r at0 m k v ch p val cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr rsegs W2 (@cfg_at fx2 rsegs HV_TAIL regs2 mem2 md2) POST.

(* ===================================== the three lanes of the piece =====================================
   HPgM3dDisp.v proves the first, HPgM3dFlt.v the second, HPgM3dA.v the third and the assembly into
   HPgSegM.v's hq_piece_M3d_value_stmt. *)
(* VAL 0x83364 -> FA / TAIL / CELL / RF / RFA: the entry's address and type, the Bool arm and the Int arm. *)
Definition hv_piece_disp_stmt : Prop :=
forall cx POST r ev at0 m,
hq_start_M03 rsegs B cx r ev ->
hq_from_CELL rsegs B MT cx r POST at0 m ->
hq_from_RF rsegs B MT cx r POST at0 m ->
hq_from_RFA rsegs B MT cx r POST at0 m ->
hv_from_TAIL cx r POST at0 m ->
hv_from_FA cx r POST at0 m ->
hq_from_VAL rsegs B MT cx r POST at0 m.
(* FA 0x83430 -> TAIL / RFA: the size test, the three binary32 tests and the five soft-float calls. *)
Definition hv_piece_flt_stmt : Prop :=
forall cx POST r ev at0 m,
hq_start_M03 rsegs B cx r ev ->
hq_from_RFA rsegs B MT cx r POST at0 m ->
hv_from_TAIL cx r POST at0 m ->
hv_from_FA cx r POST at0 m.
(* TAIL 0x83534 -> CELL / RF: the range test against the param's top value. *)
Definition hv_piece_tail_stmt : Prop :=
forall cx POST r ev at0 m,
hq_start_M03 rsegs B cx r ev ->
hq_from_CELL rsegs B MT cx r POST at0 m ->
hq_from_RF rsegs B MT cx r POST at0 m ->
hv_from_TAIL cx r POST at0 m.

End c.

Print Assumptions hv_tbl_ok.
Print Assumptions hv_entry.
Print Assumptions hv_frame_ok.
Print Assumptions hv_ent_ok.
Print Assumptions hv_facts10_ok.
Print Assumptions hv_sh_ok.
Print Assumptions hv_U_a0.
Print Assumptions hv_U_sext32.
Print Assumptions hv_U_sextw.
Print Assumptions hv_kept_run.
Print Assumptions hv_stack.
Print Assumptions hv_apart.
