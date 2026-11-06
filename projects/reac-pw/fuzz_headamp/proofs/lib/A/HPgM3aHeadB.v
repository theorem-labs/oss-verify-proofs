(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths, module names, addresses and numbers changed; 1222 of its 1367 lines of code are new or changed and 869 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the block lemmas of the
   head of the checking segment M03 of LLVMFuzzerTestOneInput (lib/A/HPgSegM.v hq_piece_M3a_head_stmt, from C5
   0x82e98 to X 0x82f30 / FIRST 0x83724). lib/A/HPgM3aHead.v assembles them into the piece. Proves no function
   (kind: segment lemma).

   THE CODE (C5 0x82e98 .. 0x82f2c; fuzz_headamp.c:330-338)
     0x82e98  beqz a0,0x83848      out is not NULL: decided by a0's atom fact (out >= 4096)
     0x82e9c  mv s8,a0; addi s10,s10,0x180 (res = F + 0x180); a1 = 0xa5; 0x82ea8 sd s11,0x118(s1) (3 cap + 3)
     0x82eac  a2 = s11; 0x82eb0 jal __asan_memset (0x521a8): out[0 .. 3 cap + 3) := 0xa5
     0x82eb4  a0 = 4; 0x82eb8 sb zero,0x30(s3); 0x82ebc sb a0,0x31(s3) (res's two granules into scope)
     0x82ec0  a1 = 0x5a, a2 = 12, a0 = res; 0x82ecc jal __asan_memset: res[0 .. 12) := 0x5a
     0x82ed0  ld a0,0x40(s1) (the null flag); a0 = (null - 1) & s9; 0x82edc sd a0,0x110(s1)
     0x82ee0  a1 = out, a2 = cap, a3 = res; 0x82eec jal reac_headamp_prop_parse_result (0x845b4)
     0x82ef0  s11 = rc; a0 = out + 3 cap; 0x82ef8 jal check_no_overrun (0x83e3c)
     0x82efc  a0 = rc, a1 = cap, a2 = res; 0x82f08 jal check_count (0x83ee8)
     0x82f0c  a0 = out, a1 = rc; 0x82f14 jal check_cells_valid (0x83f7c)
     0x82f18  srli / add / lb: the shadow byte of pp->corrupt (an instrumented 4-byte check, slow block 0x83874)
     0x82f28  lw a0,0(s2) (pp->corrupt); 0x82f2c bnez a0 -> FIRST 0x83724; else X 0x82f30.
   The walk is seven engine runs (lib/Reusable: st_ok, aj_run_to / aj_run_tok) cut at the six calls: the two
   memsets are the runtime's __asan_memset (YG0d.aintrin_realizes at any float state, the Section hypothesis
   AMEMSET, through lib/A/HPgIntrin.v hd_memset_at), the parse is lib/A/HPgCSpec.v's hd_parse_result_specX (PARSE,
   at the read-only range 0 .. 0) and the three checks are its check texts at the parse's float state (CK_NO,
   CK_COUNT, CK_CV). ERRNO (the errno cell lies in the image) puts errno apart from the heap blocks, ERRNO_RW (it
   lies in no read-only segment) keeps rom_view across the parse's errno write, and MTL (the meter's laws) chains
   the four callees' meter steps. Every byte the head writes lies in the out block, res and its two shadow
   granules, the real-frame cells [R + 0x110, R + 0x120), the errno cell or the callees' stack [R - T_SEG_STK, R),
   all inside HPgSegM.hq_E3 or the callees' stack. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgMem HPgSteps HPgCalls HPgIntrin HPgSiteA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== the code table ============================== *)
(* the 38 words 0x82e98 .. 0x82f2c and the three words 0x83874 .. 0x8387c of the slow block of the check at
   0x82f24 (`andi`, `addi`, `blt` back to 0x82f28) *)
Definition MH_PC0 : Z := 0x82e98.
Definition MH_SLOW : Z := 0x83874.
Definition mh_tbl : ctable := build_table rsegs MH_SLOW 3 (build_table rsegs MH_PC0 38 TEmpty).
Lemma mh_tbl_ok : table_ok rsegs mh_tbl.
Proof. apply build_table_ok; [unfold MH_SLOW; lia|]. apply build_table_ok0. unfold MH_PC0. lia. Qed.
(* the return addresses of the six calls *)
Definition MH_A1 : Z := 0x82eb4.
Definition MH_B1 : Z := 0x82ed0.
Definition MH_F1 : Z := 0x82f18.
Definition MHCEIL : Z := 0x7fffff800000.
(* the shadow base of the last run: s7's own atom (x23); its one shadow entry is pp->corrupt's granule at s2 (x18) *)
Definition MHBx : sv := SOff 23 0.
Definition MHspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition MHSH : list shent := [mkSHE 18 0 8].

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
(* res's two granules are the only difference between the prologue's shadow pattern and C6's *)
Lemma mh_shB_shA : forall j, (j < 80)%nat -> j <> 48%nat -> j <> 49%nat ->
nth j headamp_A_shB 0 = nth j headamp_A_shA 0.
Proof.
intros j Hj H48 H49.
do 80 (destruct j as [|j]; [first [reflexivity | exfalso; lia] |]). lia.
Qed.
Lemma mh_shB_48 : nth 48 headamp_A_shB 0 = 0 /\ nth 49 headamp_A_shB 0 = 4 /\ length headamp_A_shB = 80%nat /\
length headamp_A_shA = 80%nat.
Proof. vm_compute. repeat split. Qed.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* a register named by Z_to_bv 5 n is the register named by the numeral n *)
Lemma mh_getr_z : forall (regs : bvmap 5 word) (r : bv 5) n, bv_unsigned r = n -> getr regs (Z_to_bv 5 n) = getr regs r.
Proof.
intros regs r n H. f_equal. apply bv_eq. subst n. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
pose proof (u5_range r). change (bv_modulus 5) with 32. lia.
Qed.

(* the null flag's selection `addi a0,a0,-1; and a0,a0,s9`: pod when the flag is 0, else NULL *)
Lemma mh_sel : forall nl pod, 0 <= nl <= 1 -> 0 <= pod < 2 ^ 64 ->
zcanon (Z.land (zcanon (nl + zcanon (-1))) pod) = if nl =? 0 then pod else 0.
Proof.
intros nl pod Hn Hp. destruct (Z.eqb_spec nl 0) as [->|Hne].
- change (zcanon (0 + zcanon (-1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  unfold zcanon, M64. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
- assert (nl = 1) as -> by lia. change (zcanon (1 + zcanon (-1))) with 0. rewrite Z.land_0_l. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a register the run left as its own atom holds its value at the run's start *)
Lemma mh_reg_atom : forall (fx' : YK11.FPState) E ss ms (H : word -> bool) regs extra (r : bv 5),
@st_ok rsegs fx' E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs r.
Proof.
intros fx' E ss ms H regs extra r HS [HA _] Hr.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite HA by (pose proof (u5_range r); lia). apply ew_Ereg_reg.
Qed.
(* a register the run left as an atom of the entry env holds that atom's register *)
Lemma mh_reg_is : forall (fx' : YK11.FPState) E ss ms (H : word -> bool) regs extra (r r' : bv 5) n,
@st_ok rsegs fx' E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
sr_get (ss_regs ss) r = SOff n 0 -> Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs r'.
Proof.
intros fx' E ss ms H regs extra r r' n HS [HA _] Hr Hn.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite HA by (pose proof (u5_range r'); lia). apply ew_Ereg_nat. exact Hn.
Qed.
(* a region of the state after a run, read back [fuzz_role lib/A/RPgCheckStr.v st_ok_region_nth, field_of_region] *)
Lemma mh_region_nth : forall (fx' : YK11.FPState) (H : word -> bool) E ss ms i r,
@st_ok rsegs fx' E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
region_ok rsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros fx' H E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma mh_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.
(* a byte a block or a frame holds is present, so it reads as something *)
Lemma mh_aview_some : forall (H : word -> bool) (m : word -> option byte) a, apresent H m a -> aview rsegs H m a <> None.
Proof.
intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
(* a run left every byte outside its regions' write windows as it was *)
Lemma mh_frame_kept : forall E rs (H : word -> bool) (m m' : word -> option byte) (P : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall a, 0 <= a < 2 ^ 64 -> in_wrange E rs a -> P a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' P HF HP a Ha Hn. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. intros Hw. exact (Hn (HP a Ha Hw)).
Qed.

(* the engine's value of `ld a0,0x40(s1); addi a0,a0,-1; and a0,a0,s9` with the null flag as the extra atom 32 *)
Lemma mh_sel_sv : forall E nl pod, ew E 32 = Z_to_bv 64 nl -> ew E 25 = Z_to_bv 64 pod -> 0 <= nl <= 1 ->
0 <= pod < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff 32 (-1)) (SOff 25 0)) = Z_to_bv 64 (if nl =? 0 then pod else 0).
Proof.
intros E nl pod H32 H25 Hn Hp. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 25 pod H25 Hp).
assert (HU : U E (SOff 32 (-1)) = zcanon (nl + zcanon (-1))).
{ unfold U, zcanon, M64. cbn [sv_denot]. rewrite H32, (unsigned_lit_small nl) by lia. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Zplus_mod_idemp_r. reflexivity. }
rewrite HU. apply mh_sel; lia.
Qed.

Section s.
Variable B : asyms.
Variable MT : ameter_ops.

(* ================= the start state at C5 (HPgSegM.hq_start_M03), unfolded into the facts the walk uses ================= *)
Record mh_f (cx : hs_scx rsegs) (r : Model.pod_rec) (ev : Z) : Prop := MHF {
f_pre : hs_pre rsegs B cx (hi_shA headamp_himg_A);
f_J : ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) (x_k cx);
f_nev : st_nev (x_S cx) + x_k cx <= EV_MAX;
f_r2 : getr (x_regs cx) 2 = w64 (e_R (x_e cx));
f_r3 : getr (x_regs cx) 3 = w64 (as_gp B);
f_r4 : getr (x_regs cx) 4 = w64 (as_tp B);
f_S : e_S (x_e cx) = x_sp0 cx;
f_R32 : e_R (x_e cx) mod 32 = 0;
f_RS : e_R (x_e cx) + 0x1e0 <= e_S (x_e cx);
f_STK : x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK;
f_own : In (4, x_pos cx) (x_own cx);
f_F : e_F (x_e cx) = frame_addr (x_lyc cx) 4 (x_pos cx);
f_fsh : hd_fsh rsegs (w_H (x_W cx)) (x_memc cx) (e_F (x_e cx)) headamp_A_shA;
f_cap : 0 <= e_cap (x_e cx) <= 9;
f_null : 0 <= e_null (x_e cx) <= 1;
f_rom : rom_view rsegs (x_W cx) (x_memc cx);
f_ppf : hd_fresh_block (ablocks B (x_ly cx) (x_S cx)) (ablocks B (x_lyc cx) (x_Sc cx)) (e_pp (x_e cx)) Layout.PP_SIZE;
f_a10 : getr (x_regs cx) (Z_to_bv 5 10) = w64 (e_out (x_e cx));
f_s0 : getr (x_regs cx) (Z_to_bv 5 8) = w64 (e_S (x_e cx));
f_s1 : getr (x_regs cx) (Z_to_bv 5 9) = w64 (e_R (x_e cx));
f_s2 : getr (x_regs cx) (Z_to_bv 5 18) = w64 (e_pp (x_e cx) + 0x4d18);
f_s3 : getr (x_regs cx) (Z_to_bv 5 19) = w64 (shadow_addr (e_F (x_e cx)));
f_s4 : getr (x_regs cx) (Z_to_bv 5 20) = w64 (3 * e_cap (x_e cx));
f_s5 : getr (x_regs cx) (Z_to_bv 5 21) = w64 (e_pp (x_e cx) + 0x4000);
f_s6 : getr (x_regs cx) (Z_to_bv 5 22) = w64 (e_cap (x_e cx));
f_s7 : getr (x_regs cx) (Z_to_bv 5 23) = w64 SHADOW_OFF;
f_s9 : getr (x_regs cx) (Z_to_bv 5 25) = w64 (e_pod (x_e cx));
f_s10 : getr (x_regs cx) (Z_to_bv 5 26) = w64 (e_F (x_e cx) + 0);
f_s11 : getr (x_regs cx) (Z_to_bv 5 27) = w64 (3 * e_cap (x_e cx) + 3);
f_c20 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x20) 8 ((e_F (x_e cx) + 0) mod 2 ^ 64);
f_c40 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x40) 8 (e_null (x_e cx) mod 2 ^ 64);
f_c60 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x60) 8 ((e_F (x_e cx) + 0) mod 2 ^ 64);
f_c90 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x90) 8
  (Z.shiftr (e_pp (x_e cx) + 0x4d14) 3 mod 2 ^ 64);
f_ca0 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0xa0) 8
  ((e_pp (x_e cx) + 0x4d14) mod 2 ^ 64);
f_cf0 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0xf0) 8 ((e_pp (x_e cx) + 0) mod 2 ^ 64);
f_wf : Model.pod_rec_wf r;
f_len : e_len (x_e cx) = Z.of_nat (length (Model.buf r));
f_pp : garr8 rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_pp (x_e cx)) (hd_zbytes (Layout.pp_bytes r));
f_pod : garr8 rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_pod (x_e cx)) (hd_zbytes (Model.buf r));
f_podf : hd_fresh_block (ablocks B (x_ly cx) (x_S cx)) (ablocks B (x_lyc cx) (x_Sc cx)) (e_pod (x_e cx)) (e_len (x_e cx));
f_outf : hd_fresh_block (ablocks B (x_ly cx) (x_S cx)) (ablocks B (x_lyc cx) (x_Sc cx)) (e_out (x_e cx))
  (3 * (e_cap (x_e cx) + 1));
f_dj : e_pod (x_e cx) + e_len (x_e cx) <= e_out (x_e cx) \/ e_out (x_e cx) + 3 * (e_cap (x_e cx) + 1) <= e_pod (x_e cx);
f_rc : e_rc (x_e cx) = ans_rc (Headamp.parse_props (hd_props (e_null (x_e cx)) (Model.buf r)) (e_cap (x_e cx)));
f_ev : rd32 (aview rsegs (w_H (x_W cx)) (x_memc cx)) (as_errno B) ev;
f_frm : YK0o.frm_zero (@fp_csr fx) }.

Lemma mh_f_of : forall cx r ev,
hs_pre rsegs B cx (hi_shA headamp_himg_A) ->
hd_cut rsegs (w_H (x_W cx)) (x_memc cx) (x_regs cx) (x_e cx) (hi_L5 headamp_himg_A) ->
Model.pod_rec_wf r -> e_len (x_e cx) = Z.of_nat (length (Model.buf r)) ->
garr8 rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_pp (x_e cx)) (hd_zbytes (Layout.pp_bytes r)) ->
garr8 rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_pod (x_e cx)) (hd_zbytes (Model.buf r)) ->
hd_fresh_block (ablocks B (x_ly cx) (x_S cx)) (ablocks B (x_lyc cx) (x_Sc cx)) (e_pod (x_e cx)) (e_len (x_e cx)) ->
hd_fresh_block (ablocks B (x_ly cx) (x_S cx)) (ablocks B (x_lyc cx) (x_Sc cx)) (e_out (x_e cx))
  (3 * (e_cap (x_e cx) + 1)) ->
(e_pod (x_e cx) + e_len (x_e cx) <= e_out (x_e cx) \/ e_out (x_e cx) + 3 * (e_cap (x_e cx) + 1) <= e_pod (x_e cx)) ->
e_rc (x_e cx) = ans_rc (Headamp.parse_props (hd_props (e_null (x_e cx)) (Model.buf r)) (e_cap (x_e cx))) ->
rd32 (aview rsegs (w_H (x_W cx)) (x_memc cx)) (as_errno B) ev ->
YK0o.frm_zero (@fp_csr fx) ->
mh_f cx r ev.
Proof.
intros cx r ev HP HL Hwf Hlen Hpp Hpod Hpodf Houtf Hdj Hrc Hev Hfrm.
pose proof HP as HP0.
destruct HP as (HJ & Hnev & H2 & H3 & H4 & HS & HR32 & HRS & HSTK & Hown & HF & Hfsh & Hcap & Hnull & _ & _ & _ & _ &
  _ & _ & Hrom & Hppf).
unfold hd_cut in HL. cbn [hi_L5 headamp_himg_A] in HL. unfold headamp_A_L45 in HL.
repeat rewrite Forall_cons_iff in HL.
destruct HL as (A10 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & A26 & A27 & C20 & C40 & C60 & C90 & Ca0 &
  Cf0 & _).
cbn [fst snd hd_at hd_xv] in A10, A8, A9, A18, A19, A20, A21, A22, A23, A25, A26, A27, C20, C40, C60, C90, Ca0, Cf0.
cbn [hi_cid hi_rsz hi_shA headamp_himg_A] in *.
constructor; assumption.
Qed.

(* the bounds the walk uses, from C5's journal and the allocator's block and frame laws *)
Lemma mh_bounds : forall cx r ev, mh_f cx r ev ->
let e := x_e cx in
e_out e mod 16 = 0 /\ 4096 <= e_out e /\ e_out e + 3 * (e_cap e + 1) <= alloc_ceiling /\
in_app (e_out e) (3 * (e_cap e + 1)) /\
e_pod e mod 16 = 0 /\ 4096 <= e_pod e /\ e_pod e + e_len e <= alloc_ceiling /\ in_app (e_pod e) (e_len e) /\
8 <= e_len e /\
e_pp e mod 16 = 0 /\ 4096 <= e_pp e /\ e_pp e + 19744 <= alloc_ceiling /\ in_app (e_pp e) 19744 /\
e_F e mod 32 = 0 /\ 4096 <= e_F e /\ e_F e + 1024 <= alloc_ceiling /\ in_app (e_F e) 1024 /\
alloc_ceiling + T_SEG_STK <= e_R e /\ e_R e + 0x1e0 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\
x_sp0 cx - x_STK cx <= e_R e - T_SEG_STK /\ 0x7fff7f800000 <= alloc_ceiling <= MHCEIL.
Proof.
intros cx r ev HC e. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (f_J cx r ev HC) as HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (f_outf cx r ev HC) as (_ & Hoin & _).
destruct (f_podf cx r ev HC) as (_ & Hpin & _).
destruct (f_ppf cx r ev HC) as (_ & Hppin & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hoin) as (Om16 & O4096 & Oc & Oapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin) as (Qm16 & Q4096 & Qc & Qapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hppin) as (Pm16 & P4096 & Pc & Papp & _).
assert (Hfin : In (4, x_pos cx) (frames (x_Sc cx)))
  by (rewrite Hfrs; apply in_or_app; left; exact (f_own cx r ev HC)).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (Fm32 & _).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hfin) as (F4096 & Fc & Fapp).
pose proof asan_consts as ((Ca1 & Ca2) & _).
change (fs_frame_bytes 4) with 1024 in Fapp, Fc.
rewrite <- (f_F cx r ev HC) in Fm32, Fapp, F4096, Fc.
pose proof (f_RS cx r ev HC) as HRS. pose proof (f_S cx r ev HC) as HS. pose proof (f_STK cx r ev HC) as HSTK.
pose proof (Spa.buf_header r (f_wf cx r ev HC)) as (_ & _ & _ & Hblen).
pose proof (f_len cx r ev HC) as Hlen.
pose proof (f_cap cx r ev HC) as Hcap.
assert (Hrqo : req_size (3 * (e_cap (x_e cx) + 1)) = 3 * (e_cap (x_e cx) + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap (x_e cx) + 1)) 0); lia).
assert (Hrqp : req_size (e_len (x_e cx)) = e_len (x_e cx))
  by (unfold req_size; destruct (Z.eqb_spec (e_len (x_e cx)) 0); lia).
rewrite Hrqo in Oc, Oapp. rewrite Hrqp in Qc, Qapp.
replace (req_size Layout.PP_SIZE) with 19744 in Pc, Papp by reflexivity.
unfold MHCEIL, T_SEG_STK, ASTACK in *. subst e. rewrite HS in HRS.
repeat (first [assumption | split]); lia.
Qed.

(* =================== Section hypotheses: the runtime's __asan_memset, at any float state =================== *)
Hypothesis AMEMSET : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs B OSet A_ASAN_MEMSET.

(* ===================== block A: C5 0x82e98 .. the first memset's return 0x82eb4 ===================== *)
Definition mh_rA : YP09.region := YP09.mkRegion (Some 9%nat) 0x118 0x120 0x118 0x120 [].

(* what C5 becomes after memset(out, 0xa5, 3 cap + 3): out holds the guard byte, R + 0x118 holds 3 cap + 3, s8 =
   out, s10 = res, the other callee-saved registers their C5 values, every byte outside out, R + 0x118 and the
   callee's stack [R - ESTACK, R) as at C5 *)
Definition mh_A_post (cx : hs_scx rsegs) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) mem1 md1 (x_k cx) /\
same_io (x_mdc cx) md1 /\
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27] ->
 getr regs1 (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)) /\
getr regs1 (Z_to_bv 5 24) = w64 (e_out (x_e cx)) /\
getr regs1 (Z_to_bv 5 26) = w64 (e_F (x_e cx) + 0x180) /\
val_mem rsegs (mrestrict (w_H (x_W cx)) mem1) (e_R (x_e cx) + 0x118) 8 ((3 * e_cap (x_e cx) + 3) mod 2 ^ 64) /\
(forall i, 0 <= i < 3 * e_cap (x_e cx) + 3 -> aview rsegs (w_H (x_W cx)) mem1 (e_out (x_e cx) + i) = Some 165) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_out (x_e cx) <= a < e_out (x_e cx) + 3 * e_cap (x_e cx) + 3) ->
 ~ (e_R (x_e cx) + 0x118 <= a < e_R (x_e cx) + 0x120) -> ~ (e_R (x_e cx) - ESTACK <= a < e_R (x_e cx)) ->
 aview rsegs (w_H (x_W cx)) mem1 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).

Lemma mh_A : forall cx r ev (Q : world rsegs -> config -> Prop),
mh_f cx r ev ->
(forall regs1 mem1 md1, mh_A_post cx regs1 mem1 md1 -> SRr rsegs (x_W cx) (cfg_at rsegs MH_A1 regs1 mem1 md1) Q) ->
SRr rsegs (x_W cx) (cfg_at rsegs (hi_c5 headamp_himg_A) (x_regs cx) (x_memc cx) (x_mdc cx)) Q.
Proof using AMEMSET.
intros cx r ev Q HC K.
pose proof (mh_bounds cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
destruct HC as [_ HJ Hnev H2 H3 H4 HeS HR32 _ _ Hown HeF Hfsh Hcap Hnull Hrom Hppf
  A10 A8 A9 A18 A19 A20 A21 A22 A23 A25 A26 A27 C20 C40 C60 C90 Ca0 Cf0
  Hwf Hlen Hpp Hpod Hpodf Houtf Hdj Hrc Hev Hfrm].
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
set (out := e_out e) in *. set (cap := e_cap e) in *. set (R := e_R e) in *. set (F := e_F e) in *.
unfold MHCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
assert (E9 : bv_unsigned (ew (Ereg regs []) 9) = R).
{ rewrite (ew_Ereg_nat regs [] 9 (Z_to_bv 5 9) eq_refl), A9. unfold w64. apply unsigned_lit_small. lia. }
assert (HS : st_ok rsegs (Ereg regs []) (mkSS 0x82e98 sr_atoms [mh_rA] None
  (mkFacts [(10%nat, mkAF 4096 MHCEIL 4)] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82e98) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold mh_rA.
    apply (hm_rw_region rsegs (Ereg regs []) (w_H W) memc 9 R 0x118 0x120 0x118 0x120 [] E9); [lia | lia | | apply Forall_nil].
    intros o Ho. apply Hstkp. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite (ew_Ereg_nat regs [] 10 (Z_to_bv 5 10) eq_refl), A10. unfold w64.
    rewrite unsigned_lit_small by (unfold MHCEIL; lia). change (2 ^ 4) with 16. unfold MHCEIL. lia. }
unfold cfg_at. cbn [hi_c5 headamp_himg_A]. change (w64 0x82e98) with (Z_to_bv 64 0x82e98).
aj_run_to mh_tbl_ok HS HJ 0x521a8.
{ eapply awr_ok_cons_gen; [reflexivity | exact E9 | | apply awr_ok_nil].
  intros a Ha. cbn [mh_rA YP09.r_wlo YP09.r_whi] in Ha. left. lia. }
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
rreg HS (Z_to_bv 5 1) Ra1. rreg HS (Z_to_bv 5 11) Ra11.
assert (Ra10 : getr (ms_regs ms) (Z_to_bv 5 10) = getr regs (Z_to_bv 5 10))
  by (eapply (mh_reg_is _ _ _ ms (w_H W) regs [] _ _ 10 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Ra12 : getr (ms_regs ms) (Z_to_bv 5 12) = getr regs (Z_to_bv 5 27))
  by (eapply (mh_reg_is _ _ _ ms (w_H W) regs [] _ _ 27 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Ra24 : getr (ms_regs ms) (Z_to_bv 5 24) = getr regs (Z_to_bv 5 10))
  by (eapply (mh_reg_is _ _ _ ms (w_H W) regs [] _ _ 10 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Ra26 : getr (ms_regs ms) (Z_to_bv 5 26) = w64 (F + 0x180)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 26)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 26)) with v end.
  cbn [sv_denot]. rewrite (ew_Ereg_nat regs [] 26 (Z_to_bv 5 26) eq_refl), A26. unfold w64.
  rewrite unsigned_lit_small by lia. f_equal. lia. }
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r0 Hr. eapply (mh_reg_atom _ _ _ ms (w_H W) regs [] (Z_to_bv 5 r0) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
(* R + 0x118 after the store *)
assert (H118 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x118) 8 ((3 * cap + 3) mod 2 ^ 64)).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch rr with Some ?rg =>
      assert (Hr : nth_error (ss_mem ss) 0 = Some rg) by (vm_compute; reflexivity);
      pose proof (mh_region_nth _ _ _ _ _ 0 _ HS Hr) as Hreg end end.
  rewrite Z.mod_small by lia.
  exact (mh_field _ _ _ _ _ _ _ _ _ 0x118 8 (SOff 27 0) (3 * cap + 3) Hreg E9 ltac:(cbn; tauto)
    ltac:(cbn [sv_denot]; rewrite (ew_Ereg_nat regs [] 27 (Z_to_bv 5 27) eq_refl), A27; unfold w64;
          rewrite unsigned_lit_small by lia; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x118 <= a < R + 0x120) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ apply (mh_frame_kept _ _ _ _ _ _ HFr). intros a Ha Hw.
  destruct Hw as (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [mh_rA YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E9 in Hr. exact Hr. }
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
assert (HAR : AR rsegs B lyc Sc W (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc)) by exact (proj1 HJ).
assert (E2 : getr (ms_regs ms) (2%bv : bv 5) = getr regs (2%bv : bv 5))
  by (eapply (mh_reg_atom _ _ _ ms (w_H W) regs [] _ HS HAE); vm_compute; reflexivity).
assert (E3 : getr (ms_regs ms) (3%bv : bv 5) = getr regs (3%bv : bv 5))
  by (eapply (mh_reg_atom _ _ _ ms (w_H W) regs [] _ HS HAE); vm_compute; reflexivity).
assert (E4 : getr (ms_regs ms) (4%bv : bv 5) = getr regs (4%bv : bv 5))
  by (eapply (mh_reg_atom _ _ _ ms (w_H W) regs [] _ HS HAE); vm_compute; reflexivity).
assert (Hsp : spZ (ms_regs ms) = sp0 + (R - sp0)).
{ unfold spZ. rewrite E2, H2. unfold w64. rewrite unsigned_lit_small; [ring | lia]. }
destruct Houtf as (Hout0 & Hoin & Honew).
assert (Hrqo : req_size (3 * (cap + 1)) = 3 * (cap + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (cap + 1)) 0); lia).
destruct (hm_blk_ra rsegs B lyc Sc W (ms_mem ms) _ out (3 * (cap + 1)) out (3 * cap + 3) HAR Hoin ltac:(lia)
  ltac:(rewrite Hrqo; lia)) as (Hrao & Hhullo).
eapply SRr_bind.
{ eapply (hd_memset_at B (AMEMSET fx) W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    out 165 (3 * cap + 3) (R - sp0) (Z_to_bv 64 MH_A1) HJ).
  - rewrite <- (mh_getr_z (ms_regs ms) 10 10 eq_refl), Ra10. exact A10.
  - rewrite <- (mh_getr_z (ms_regs ms) 11 11 eq_refl), Ra11. reflexivity.
  - rewrite <- (mh_getr_z (ms_regs ms) 12 12 eq_refl), Ra12. exact A27.
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - assert (HR16 : R mod 16 = 0)
      by (rewrite <- (Z.mod_mod_divide R 32 16) by (exists 2; reflexivity); rewrite HR32; reflexivity).
    rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite E3. exact H3.
  - rewrite E4. exact H4.
  - rewrite <- (mh_getr_z (ms_regs ms) 1 1 eq_refl). exact Ra1.
  - vm_compute. reflexivity.
  - intros a Ha. split.
    + replace a with (out + (a - out)) by lia.
      apply (hd_fresh_awr_n STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own out (3 * (cap + 1)) Hoin Honew);
        lia.
    + unfold ESTACK. lia.
  - eapply amem_range_of_block; [exact LAWS | exact HAR | exact Hoin | lia | rewrite Hrqo; lia].
  - exact Hrao.
  - exact Hhullo. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & Hpres2 & Ha02 & Hset & Hkeep & Hgrow).
apply K. unfold mh_A_post.
cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_k x_regs x_lyc x_Sc x_W x_memc x_mdc x_e].
fold out cap R F.
split; [exact HJ2|].
split; [eapply same_io_trans; [apply same_io_wvb | exact Hio2]|].
split.
{ intros r0 Hr. rewrite (Hpres2 r0) by (cbn [In] in Hr; unfold acallee_saved; lia). apply Rk. exact Hr. }
split.
{ rewrite (Hpres2 24) by (unfold acallee_saved; lia). rewrite Ra24. exact A10. }
split.
{ rewrite (Hpres2 26) by (unfold acallee_saved; lia). exact Ra26. }
split.
{ eapply (hd_val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms) mem2); [|exact H118].
  intros i Hi. apply Hkeep; [lia | lia | unfold ESTACK; lia]. }
split.
{ intros i Hi. rewrite (Hset i Hi). reflexivity. }
intros a Ha Ho H1 Hs. rewrite Hkeep; [| exact Ha | lia | replace (sp0 + (R - sp0)) with R by ring; exact Hs].
apply KA; [exact Ha | exact H1].
Qed.

(* ===================== block B: 0x82eb4 .. the second memset's return 0x82ed0 ===================== *)
(* res's 12 bytes have their shadow hull inside the frame's 128 shadow bytes *)
Lemma mh_res_hull : forall (H : word -> bool) (m : word -> option byte) F, F = 8 * (F / 8) ->
(forall i, 0 <= i < 128 -> aview rsegs H m (shadow_addr F + i) <> None) ->
shadow_hull_vis (aview rsegs H m) (F + 0x180) 12.
Proof.
intros H m F F8 Hp s Hs. unfold shadow_addr in *. set (q := F / 8) in *.
replace (F + 0x180) with ((q + 48) * 8) in Hs by lia.
replace ((q + 48) * 8 + 12 - 1) with ((q + 49) * 8 + 3) in Hs by lia.
rewrite Z.div_mul in Hs by lia. rewrite Z.div_add_l in Hs by lia. change (3 / 8) with 0 in Hs.
pose proof (Z.div_mod (SHADOW_OFF + (q + 48)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (q + 48)) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (q + 49 + 0)) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (q + 49 + 0)) 8 ltac:(lia)) as M2.
replace s with (SHADOW_OFF + q + (s - (SHADOW_OFF + q))) by lia.
apply Hp. lia.
Qed.

Definition mh_B_post (cx : hs_scx rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) mem2 md2 (x_k cx) /\
same_io (x_mdc cx) md2 /\
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27] ->
 getr regs2 (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)) /\
getr regs2 (Z_to_bv 5 24) = w64 (e_out (x_e cx)) /\
getr regs2 (Z_to_bv 5 26) = w64 (e_F (x_e cx) + 0x180) /\
val_mem rsegs (mrestrict (w_H (x_W cx)) mem2) (e_R (x_e cx) + 0x118) 8 ((3 * e_cap (x_e cx) + 3) mod 2 ^ 64) /\
(forall i, 0 <= i < 3 * e_cap (x_e cx) + 3 -> aview rsegs (w_H (x_W cx)) mem2 (e_out (x_e cx) + i) = Some 165) /\
hd_fsh rsegs (w_H (x_W cx)) mem2 (e_F (x_e cx)) headamp_A_shB /\
(forall i, 0 <= i < 12 -> aview rsegs (w_H (x_W cx)) mem2 (e_F (x_e cx) + 0x180 + i) = Some 90) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_out (x_e cx) <= a < e_out (x_e cx) + 3 * e_cap (x_e cx) + 3) ->
 ~ (e_R (x_e cx) + 0x118 <= a < e_R (x_e cx) + 0x120) ->
 ~ (shadow_addr (e_F (x_e cx)) + 0x30 <= a < shadow_addr (e_F (x_e cx)) + 0x32) ->
 ~ (e_F (x_e cx) + 0x180 <= a < e_F (x_e cx) + 0x18c) -> ~ (e_R (x_e cx) - ESTACK <= a < e_R (x_e cx)) ->
 aview rsegs (w_H (x_W cx)) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).

Lemma mh_B : forall cx r ev regs1 mem1 md1 (Q : world rsegs -> config -> Prop),
mh_f cx r ev -> mh_A_post cx regs1 mem1 md1 ->
(forall regs2 mem2 md2, mh_B_post cx regs2 mem2 md2 -> SRr rsegs (x_W cx) (cfg_at rsegs MH_B1 regs2 mem2 md2) Q) ->
SRr rsegs (x_W cx) (cfg_at rsegs MH_A1 regs1 mem1 md1) Q.
Proof using AMEMSET.
intros cx r ev regs1 mem1 md1 Q HC HA K.
pose proof (mh_bounds cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
destruct HA as (HJ & Hio1 & Rk1 & R24 & R26 & H118 & Hout & KA).
destruct HC as [_ _ Hnev H2 H3 H4 HeS HR32 _ _ Hown HeF Hfsh Hcap Hnull Hrom Hppf
  A10 A8 A9 A18 A19 A20 A21 A22 A23 A25 A26 A27 C20 C40 C60 C90 Ca0 Cf0
  Hwf Hlen Hpp Hpod Hpodf Houtf Hdj Hrc Hev Hfrm].
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
set (out := e_out e) in *. set (cap := e_cap e) in *. set (R := e_R e) in *. set (F := e_F e) in *.
unfold MHCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (F8 : F = 8 * (F / 8)).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as D.
  assert (F mod 8 = 0) by (rewrite <- (Z.mod_mod_divide F 32 8) by (exists 4; reflexivity); rewrite Fm32; reflexivity).
  lia. }
assert (F8m : F mod 8 = 0) by (rewrite F8, Z.mul_comm; apply Z.mod_mul; lia).
assert (Hfq : 0 <= F / 8) by lia.
assert (Happ : forall a, (out <= a < out + 3 * cap + 3) \/ (F <= a < F + 1024) ->
  ~ (shadow_addr F <= a < shadow_addr F + 128)).
{ intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Oapp, Fapp. unfold shadow_addr, SHADOW_OFF.
  lia. }
pose proof HJ as (HAR1 & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
assert (E19 : ew (Ereg regs1 []) 19 = Z_to_bv 64 (shadow_addr F)).
{ rewrite (ew_Ereg_nat regs1 _ 19 (Z_to_bv 5 19) eq_refl), (Rk1 19 ltac:(cbn; tauto)). exact A19. }
assert (E19u : bv_unsigned (ew (Ereg regs1 []) 19) = shadow_addr F).
{ rewrite E19. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR1 Hfin) as (_ & _ & _ & HFsh1).
rewrite <- HeF in HFsh1. change (fs_frame_bytes 4 / 8) with 128 in HFsh1.
assert (HS : st_ok rsegs (Ereg regs1 []) (fsh_ss 0x82eb4 0x30 0x32)
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 0x82eb4) mem1 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19u.
    split; [unfold shadow_addr, SHADOW_OFF; lia|]. split; [unfold shadow_addr, SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh1 o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at, MH_A1. change (w64 0x82eb4) with (Z_to_bv 64 0x82eb4).
aj_run_to mh_tbl_ok HS HJ 0x521a8.
{ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat 4 pos);
  [ reflexivity | rewrite E19u, HeF; reflexivity | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; change (fs_frame_bytes 4 / 8) with 128; lia
  | apply awr_ok_nil ]. }
assert (HAE : env_agree 32 (Ereg regs1 []) (Ereg regs1 [])) by apply env_agree_refl.
rreg HS (Z_to_bv 5 1) Ra1. rreg HS (Z_to_bv 5 11) Ra11. rreg HS (Z_to_bv 5 12) Ra12.
assert (Ra10 : getr (ms_regs ms) (Z_to_bv 5 10) = getr regs1 (Z_to_bv 5 26))
  by (eapply (mh_reg_is _ _ _ ms (w_H W) regs1 [] _ _ 26 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r0 Hr. eapply (mh_reg_atom _ _ _ ms (w_H W) regs1 [] (Z_to_bv 5 r0) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
(* the two shadow bytes after the stores *)
assert (Hs48 : aview rsegs (w_H W) (ms_mem ms) (shadow_addr F + 48) = Some 0 /\
  aview rsegs (w_H W) (ms_mem ms) (shadow_addr F + 49) = Some 4).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch rr with Some ?rg =>
      assert (Hr : nth_error (ss_mem ss) 0 = Some rg) by (vm_compute; reflexivity);
      pose proof (mh_region_nth _ _ _ _ _ 0 _ HS Hr) as Hreg end end.
  destruct Hreg as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19u in Hch.
  unfold aview. split.
  + apply (fsh_byte_of_region _ _ _ _ _ 0 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia].
  + apply (fsh_byte_of_region _ _ _ _ _ 4 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia]. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 0x30 <= a < shadow_addr F + 0x32) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem1 a).
{ apply (mh_frame_kept _ _ _ _ _ _ HFr). intros a Ha Hw.
  destruct Hw as (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [fsh_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E19u in Hr. exact Hr. }
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
assert (HAR : AR rsegs B lyc Sc W (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1)) by exact (proj1 HJ).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (_ & _ & HFb & HFsh).
rewrite <- HeF in HFsh, HFb. change (fs_frame_bytes 4 / 8) with 128 in HFsh. change (fs_frame_bytes 4) with 1024 in HFb.
(* the frame's shadow at the call: the prologue's with res's two granules in scope *)
assert (Hfsh1 : hd_fsh rsegs (w_H W) mem1 F headamp_A_shA).
{ apply (hm_fsh_kept rsegs (w_H W) memc (w_H W) mem1 F headamp_A_shA Hfsh).
  intros i Hi. change (length headamp_A_shA) with 80%nat in Hi. cbn in Hi.
  apply KA; [unfold shadow_addr, SHADOW_OFF; lia | | | unfold ESTACK; unfold shadow_addr, SHADOW_OFF; lia].
  - intros Ho. apply (Happ (shadow_addr F + i)); [left; exact Ho | lia].
  - unfold shadow_addr, SHADOW_OFF. lia. }
assert (HfshP : hd_fsh rsegs (w_H W) (ms_mem ms) F headamp_A_shB).
{ intros i Hi. destruct mh_shB_48 as (S48 & S49 & SlB & SlA). rewrite SlB in Hi. change (Z.of_nat 80) with 80 in Hi.
  destruct (Z.eq_dec i 48) as [->|N48]; [rewrite (proj1 Hs48); change (Z.to_nat 48) with 48%nat; rewrite S48; reflexivity|].
  destruct (Z.eq_dec i 49) as [->|N49]; [rewrite (proj2 Hs48); change (Z.to_nat 49) with 49%nat; rewrite S49; reflexivity|].
  rewrite KB by (unfold shadow_addr, SHADOW_OFF; lia).
  rewrite (Hfsh1 i ltac:(rewrite SlA; lia)).
  rewrite mh_shB_shA; [reflexivity | lia | lia | lia]. }
pose proof headamp_A_shB_facts as (Bl & B48 & B49). cbn [hi_shB headamp_himg_A] in Bl, B48, B49.
assert (E2 : getr (ms_regs ms) (2%bv : bv 5) = getr regs1 (2%bv : bv 5))
  by (eapply (mh_reg_atom _ _ _ ms (w_H W) regs1 [] _ HS HAE); vm_compute; reflexivity).
assert (E3 : getr (ms_regs ms) (3%bv : bv 5) = getr regs1 (3%bv : bv 5))
  by (eapply (mh_reg_atom _ _ _ ms (w_H W) regs1 [] _ HS HAE); vm_compute; reflexivity).
assert (E4 : getr (ms_regs ms) (4%bv : bv 5) = getr regs1 (4%bv : bv 5))
  by (eapply (mh_reg_atom _ _ _ ms (w_H W) regs1 [] _ HS HAE); vm_compute; reflexivity).
assert (Hsp : spZ (ms_regs ms) = sp0 + (R - sp0)).
{ unfold spZ. rewrite E2. rewrite <- (mh_getr_z regs1 2 2 eq_refl), (Rk1 2 ltac:(cbn; tauto)),
    (mh_getr_z regs 2 2 eq_refl), H2.
  unfold w64. rewrite unsigned_lit_small; [ring | lia]. }
assert (HR16 : R mod 16 = 0)
  by (rewrite <- (Z.mod_mod_divide R 32 16) by (exists 2; reflexivity); rewrite HR32; reflexivity).
eapply SRr_bind.
{ eapply (hd_memset_at B (AMEMSET fx) W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    (F + 0x180) 90 12 (R - sp0) (Z_to_bv 64 MH_B1) HJ).
  - rewrite <- (mh_getr_z (ms_regs ms) 10 10 eq_refl), Ra10. exact R26.
  - rewrite <- (mh_getr_z (ms_regs ms) 11 11 eq_refl), Ra11. reflexivity.
  - rewrite <- (mh_getr_z (ms_regs ms) 12 12 eq_refl), Ra12. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite E3, <- (mh_getr_z regs1 3 3 eq_refl), (Rk1 3 ltac:(cbn; tauto)), (mh_getr_z regs 3 3 eq_refl). exact H3.
  - rewrite E4, <- (mh_getr_z regs1 4 4 eq_refl), (Rk1 4 ltac:(cbn; tauto)), (mh_getr_z regs 4 4 eq_refl). exact H4.
  - rewrite <- (mh_getr_z (ms_regs ms) 1 1 eq_refl). exact Ra1.
  - vm_compute. reflexivity.
  - intros a Ha. split.
    + right. right. right. exists 4, pos. split; [exact Hown|]. left. unfold in_zr. cbn [fst snd].
      rewrite <- HeF. change (fs_frame_bytes 4) with 1024. lia.
    + unfold ESTACK. lia.
  - unfold in_app, amem_range, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia.
  - apply (hd_res_addressable rsegs (w_H W) (ms_mem ms) F headamp_A_shB HfshP F8m Bl B48 B49); lia.
  - intros _. apply (mh_res_hull (w_H W) (ms_mem ms) F F8). intros i Hi. apply mh_aview_some. exact (proj1 (HFsh i Hi)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & Hpres2 & Ha02 & Hset & Hkeep & Hgrow).
replace (sp0 + (R - sp0)) with R in Hkeep by ring.
apply K. unfold mh_B_post.
cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_k x_regs x_lyc x_Sc x_W x_memc x_mdc x_e].
fold out cap R F.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x180 <= a < F + 0x180 + 12) -> ~ (R - ESTACK <= a < R) ->
  ~ (shadow_addr F + 0x30 <= a < shadow_addr F + 0x32) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) mem1 a).
{ intros a Ha H1 H2' H3'. rewrite Hkeep; [| exact Ha | exact H1 | exact H2']. apply KB; [exact Ha | exact H3']. }
split; [exact HJ2|].
split; [eapply same_io_trans; [exact Hio1|]; eapply same_io_trans; [apply same_io_wvb | exact Hio2]|].
split.
{ intros r0 Hr. rewrite (Hpres2 r0) by (cbn [In] in Hr; unfold acallee_saved; lia).
  rewrite Rk by (cbn [In] in Hr |- *; tauto). apply Rk1. exact Hr. }
split.
{ rewrite (Hpres2 24) by (unfold acallee_saved; lia). rewrite Rk by (cbn; tauto). exact R24. }
split.
{ rewrite (Hpres2 26) by (unfold acallee_saved; lia). rewrite Rk by (cbn; tauto). exact R26. }
split.
{ eapply (hd_val_mem_kept rsegs (w_H W) (w_H W) mem1 mem2); [|exact H118].
  intros i Hi. apply KM; [lia | lia | unfold ESTACK; lia | unfold shadow_addr, SHADOW_OFF; lia]. }
split.
{ intros i Hi. rewrite KM; [exact (Hout i Hi) | lia | | unfold ESTACK; lia |].
  - pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR (proj1 (proj2 Houtf)) Hfin) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- HeF in Hz. change (fs_frame_bytes 4) with 1024 in Hz.
    replace (req_size (3 * (cap + 1))) with (3 * (cap + 1)) in Hz
      by (unfold req_size; destruct (Z.eqb_spec (3 * (cap + 1)) 0); lia).
    lia.
  - intros Hs. apply (Happ (out + i)); [left; lia | lia]. }
split.
{ apply (hm_fsh_kept rsegs (w_H W) (ms_mem ms) (w_H W) mem2 F headamp_A_shB HfshP).
  intros i Hi. rewrite Bl in Hi. cbn in Hi. apply Hkeep; [unfold shadow_addr, SHADOW_OFF; lia | | unfold ESTACK; unfold shadow_addr, SHADOW_OFF; lia].
  intros Hr. apply (Happ (F + 0x180 + (shadow_addr F + i - (F + 0x180)))); [right; lia | lia]. }
split.
{ intros i Hi. rewrite (Hset i Hi). reflexivity. }
intros a Ha Ho H1 Hsh Hres Hs. rewrite KM; [| exact Ha | lia | exact Hs | exact Hsh].
apply KA; [exact Ha | exact Ho | exact H1 | exact Hs].
Qed.

(* ===================== block C: 0x82ed0 .. the parse's return 0x82ef0 ===================== *)
Hypothesis ERRNO : api_env rsegs B.
Hypothesis ERRNO_RW : forall a, as_errno B <= a < as_errno B + 4 -> ~ in_rom rsegs a.
Hypothesis MTL : ameter_laws MT.
Hypothesis PARSE : hd_parse_result_specX rsegs B MT A_PARSE_RESULT 0 0
  (hi_akey headamp_himg_A) (hi_aph headamp_himg_A) (hi_apad headamp_himg_A) (hi_asens headamp_himg_A)
  (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A) (hi_dcs headamp_himg_A).

(* the segment's start state read at the read-only range 0 .. 0 (the parse's contract is used there) *)
Lemma mh_pre00 : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc sh RLO RHI e pos,
hd_seg_pre rsegs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_A sh RLO RHI e pos ->
hd_seg_pre rsegs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_A sh 0 0 e pos.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc sh RLO RHI e pos
  (HJ & Hnev & H2 & H3 & H4 & HS & HR32 & HRS & HSTK & Hown & HF & Hfsh & Hcap & Hnull & Haro & Hg & Hrz & Hst &
   Hce & Hgd & Hrom & Hppf).
repeat (split; [assumption|]).
split; [|repeat (split; [assumption|]); assumption].
intros a Hro Ho He. apply Haro; [|exact Ho | exact He].
destruct Hro as [Hs|Hr]; [left; exact Hs | lia].
Qed.

(* the ranges the head writes besides out and errno lie in the image's third range list *)
Lemma mh_inw3 : forall e a,
(e_R e + 0x110 <= a < e_R e + 0x120) \/ (shadow_addr (e_F e) + 0x30 <= a < shadow_addr (e_F e) + 0x32) \/
(e_F e + 0x180 <= a < e_F e + 0x18c) -> hd_inw e (hi_w3 headamp_himg_A) a.
Proof.
intros e a Ha. unfold hd_inw. cbn [hi_w3 headamp_himg_A].
destruct Ha as [Ha|[Ha|Ha]].
- apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd hd_xv]. lia.
- apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd hd_xv]. lia.
- apply Exists_cons_hd. cbn [fst snd hd_xv]. lia.
Qed.

(* the parse's answer, and every byte the head writes *)
Definition mh_ans (cx : hs_scx rsegs) (r : Model.pod_rec) : answer :=
  Headamp.parse_props (hd_props (e_null (x_e cx)) (Model.buf r)) (e_cap (x_e cx)).
Definition mh_W (cx : hs_scx rsegs) (a : Z) : Prop :=
(e_out (x_e cx) <= a < e_out (x_e cx) + 3 * (e_cap (x_e cx) + 1)) \/
(e_R (x_e cx) + 0x110 <= a < e_R (x_e cx) + 0x120) \/
(shadow_addr (e_F (x_e cx)) + 0x30 <= a < shadow_addr (e_F (x_e cx)) + 0x32) \/
(e_F (x_e cx) + 0x180 <= a < e_F (x_e cx) + 0x18c) \/
(as_errno B <= a < as_errno B + 4).
Lemma mh_W_E3 : forall cx a, mh_W cx a ->
hd_inw (x_e cx) (hi_w3 headamp_himg_A) a \/
(e_out (x_e cx) <= a < e_out (x_e cx) + 3 * (e_cap (x_e cx) + 1)) \/ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx a [H|[H|[H|[H|H]]]].
- right. left. exact H.
- left. apply mh_inw3. left. exact H.
- left. apply mh_inw3. right. left. exact H.
- left. apply mh_inw3. right. right. exact H.
- right. right. exact H.
Qed.

(* a state after the parse: the parse's post, the frame's shadow with res in scope, out holding the parse's cells
   and the guard cell, res holding the parse's result, the two real-frame cells, every byte outside mh_W and the
   callees' stack as at C5 *)
Definition mh_P (cx : hs_scx rsegs) (r : Model.pod_rec) (fx2 : YK11.FPState) ly2 S2 (W2 : world rsegs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hd_fxk [14; 15] fx fx2 /\
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) ly2 S2 W2 mem md (x_k cx) /\
frames S2 = frames (x_Sc cx) /\ Permutation (ablocks B ly2 S2) (ablocks B (x_lyc cx) (x_Sc cx)) /\
same_io (x_mdc cx) md /\ mo_le MT (x_Sc cx) S2 0 /\
(forall r0, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25] ->
 getr regs (Z_to_bv 5 r0) = getr (x_regs cx) (Z_to_bv 5 r0)) /\
getr regs (Z_to_bv 5 24) = w64 (e_out (x_e cx)) /\
getr regs (Z_to_bv 5 26) = w64 (e_F (x_e cx) + 0x180) /\
val_mem rsegs (mrestrict (w_H W2) mem) (e_R (x_e cx) + 0x110) 8 (hd_xv (x_e cx) XProps mod 2 ^ 64) /\
val_mem rsegs (mrestrict (w_H W2) mem) (e_R (x_e cx) + 0x118) 8 ((3 * e_cap (x_e cx) + 3) mod 2 ^ 64) /\
hd_fsh rsegs (w_H W2) mem (e_F (x_e cx)) headamp_A_shB /\
garr8 rsegs (mrestrict (w_H W2) mem) (e_out (x_e cx)) (hd_zbytes (ha_cells_bytes (ans_cells (mh_ans cx r)))) /\
garr8 rsegs (mrestrict (w_H W2) mem) (e_out (x_e cx) + 3 * e_cap (x_e cx)) (hd_zbytes (repeat GUARD_BYTE 3)) /\
garr8 rsegs (mrestrict (w_H W2) mem) (e_F (x_e cx) + 0x180) (hd_zbytes (ans_res_bytes (mh_ans cx r))) /\
(exists ev', rd32 (aview rsegs (w_H W2) mem) (as_errno B) ev') /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) -> ~ mh_W cx a ->
 aview rsegs (w_H W2) mem a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).

Definition mh_rC0 : YP09.region := YP09.mkRegion (Some 9%nat) 0x40 0x48 0 0 [YP09.mkChunk 0x40 (CVal 8 (SOff 32 0))].
Definition mh_rC1 : YP09.region := YP09.mkRegion (Some 9%nat) 0x110 0x118 0x110 0x118 [].

Lemma mh_C : forall cx r ev regs2 mem2 md2 (Q : world rsegs -> config -> Prop),
mh_f cx r ev -> mh_B_post cx regs2 mem2 md2 ->
(forall (fx2 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3, mh_P cx r fx2 ly3 S3 W3 regs3 mem3 md3 ->
 getr regs3 (Z_to_bv 5 10) = w64 (ans_rc (mh_ans cx r)) ->
 getr regs3 (Z_to_bv 5 27) = getr (x_regs cx) (Z_to_bv 5 27) ->
 SRr rsegs W3 (@cfg_at fx2 rsegs RA_PARSE_RESULT regs3 mem3 md3) Q) ->
SRr rsegs (x_W cx) (cfg_at rsegs MH_B1 regs2 mem2 md2) Q.
Proof using ERRNO PARSE.
intros cx r ev regs2 mem2 md2 Q HC HB K.
pose proof (mh_bounds cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
destruct HB as (HJ & Hio2 & Rk2 & R24 & R26 & H118 & Hout & Hfsh2 & Hres & KB).
destruct HC as [Hpre HJ0 Hnev H2 H3 H4 HeS HR32 _ _ Hown HeF Hfsh Hcap Hnull Hrom Hppf
  A10 A8 A9 A18 A19 A20 A21 A22 A23 A25 A26 A27 C20 C40 C60 C90 Ca0 Cf0
  Hwf Hlen Hpp Hpod Hpodf Houtf Hdj Hrc Hev Hfrm].
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
unfold mh_ans in *. cbn [x_e] in *.
set (out := e_out e) in *. set (cap := e_cap e) in *. set (R := e_R e) in *. set (F := e_F e) in *.
set (pod := e_pod e) in *. set (nl := e_null e) in *.
unfold MHCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (F8 : F = 8 * (F / 8)).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as D.
  assert (F mod 8 = 0) by (rewrite <- (Z.mod_mod_divide F 32 8) by (exists 4; reflexivity); rewrite Fm32; reflexivity).
  lia. }
assert (HR16 : R mod 16 = 0)
  by (rewrite <- (Z.mod_mod_divide R 32 16) by (exists 2; reflexivity); rewrite HR32; reflexivity).
pose proof HJ as (HAR2 & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
assert (Hfin : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
(* the env of the run: the null flag as the extra atom 32 *)
set (E := Ereg regs2 [w64 nl]).
assert (E9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), (Rk2 9 ltac:(cbn; tauto)), A9.
  unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 nl) by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E25 : ew E 25 = Z_to_bv 64 pod)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 25 (Z_to_bv 5 25) eq_refl), (Rk2 25 ltac:(cbn; tauto)); exact A25).
assert (H40 : val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x40) 8 nl).
{ rewrite (Z.mod_small nl) in C40 by lia.
  eapply (hd_val_mem_kept rsegs (w_H W) (w_H W) memc mem2); [|exact C40].
  intros i Hi. apply KB; [lia | | lia | | | unfold ESTACK; lia].
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Oapp. lia.
  - unfold shadow_addr, SHADOW_OFF. lia.
  - lia. }
assert (HS : st_ok rsegs E (mkSS 0x82ed0 sr_atoms [mh_rC0; mh_rC1] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x82ed0) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold mh_rC0. apply (hm_ro_region rsegs E (w_H W) mem2 9 R 0x40 0x48 _ E9); [lia | lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ R 0x40 8 (SOff 32 0) nl).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
      * cbn. lia.
      * cbn. lia.
      * exact H40.
    + unfold mh_rC1. apply (hm_rw_region rsegs E (w_H W) mem2 9 R 0x110 0x118 0x110 0x118 [] E9);
        [lia | lia | | apply Forall_nil].
      intros o Ho. apply Hstkp. lia.
  - cbn [pairwise_disjoint all_disjoint mh_rC0 mh_rC1 extent_disjoint YP09.r_base YP09.r_lo YP09.r_hi base_val].
    unfold extent_disjoint, mh_rC0, mh_rC1. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    fold E. rewrite E9. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
unfold cfg_at, MH_B1. change (w64 0x82ed0) with (Z_to_bv 64 0x82ed0).
aj_run_to mh_tbl_ok HS HJ 0x845b4.
{ apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact E9 | | apply awr_ok_nil].
  intros a Ha. cbn [mh_rC1 YP09.r_wlo YP09.r_whi] in Ha. left. lia. }
assert (HAE : env_agree 32 (Ereg regs2 [w64 nl]) E) by (subst E; apply env_agree_refl).
rreg HS (Z_to_bv 5 1) Ra1.
(* the parse's first argument: (null - 1) & pod *)
assert (Ra10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (if nl =? 0 then pod else 0)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 10)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 10)) with v end.
  apply mh_sel_sv; [exact E32 | exact E25 | lia | lia]. }
assert (Ra11 : getr (ms_regs ms) (Z_to_bv 5 11) = getr regs2 (Z_to_bv 5 24))
  by (eapply (mh_reg_is _ _ _ ms (w_H W) regs2 _ _ _ 24 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Ra12 : getr (ms_regs ms) (Z_to_bv 5 12) = getr regs2 (Z_to_bv 5 22))
  by (eapply (mh_reg_is _ _ _ ms (w_H W) regs2 _ _ _ 22 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Ra13 : getr (ms_regs ms) (Z_to_bv 5 13) = getr regs2 (Z_to_bv 5 26))
  by (eapply (mh_reg_is _ _ _ ms (w_H W) regs2 _ _ _ 26 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rk : forall r0, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r0) = getr regs2 (Z_to_bv 5 r0)).
{ intros r0 Hr. eapply (mh_reg_atom _ _ _ ms (w_H W) regs2 _ (Z_to_bv 5 r0) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
assert (Rx : forall r0, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r0) = getr regs (Z_to_bv 5 r0)).
{ intros r0 Hr. rewrite Rk by (cbn [In] in Hr |- *; tauto). apply Rk2. exact Hr. }
(* R + 0x110 after the store *)
assert (H110 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x110) 8 (if nl =? 0 then pod else 0)).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ss) 1) in
    lazymatch rr with Some ?rg =>
      assert (Hr : nth_error (ss_mem ss) 1 = Some rg) by (vm_compute; reflexivity);
      pose proof (mh_region_nth _ _ _ _ _ 1 _ HS Hr) as Hreg end end.
  exact (mh_field _ _ _ _ _ _ _ _ _ 0x110 8 _ _ Hreg E9 ltac:(cbn; tauto)
    ltac:(apply mh_sel_sv; [exact E32 | exact E25 | lia | lia])
    ltac:(cbn; destruct (nl =? 0); lia) ltac:(cbn; lia)). }
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x110 <= a < R + 0x118) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem2 a).
{ apply (mh_frame_kept _ _ _ _ _ _ HFr). intros a Ha Hw.
  destruct Hw as (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[<-|[]]].
  - cbn [mh_rC0 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia.
  - cbn [mh_rC1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. fold E in Hr. rewrite E9 in Hr. exact Hr. }
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
(* separations *)
destruct Houtf as (Hout0 & Hoin & Honew).
assert (Hrqo : req_size (3 * (cap + 1)) = 3 * (cap + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (cap + 1)) 0); lia).
pose proof HJ0 as (HAR0 & _).
assert (Herr : forall a, out <= a < out + 3 * (cap + 1) -> ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha He. destruct ERRNO as (_ & HAi & _).
  assert (Hcin : exists p n, In (p, n) (ablocks B lyc Sc) /\ p <= a < p + req_size n)
    by (exists out, (3 * (cap + 1)); split; [exact Hoin | rewrite Hrqo; lia]).
  destruct (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR0 (or_introl Hcin)) as (_ & Hni).
  exact (Hni (HAi a He)). }
assert (Hferr : forall a, F <= a < F + 1024 -> ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha He. destruct ERRNO as (_ & HAi & _).
  assert (Hcin : exists cid pos0, In (cid, pos0) (frames Sc) /\
    frame_addr lyc cid pos0 <= a < frame_addr lyc cid pos0 + fs_frame_bytes cid)
    by (exists 4, pos; rewrite <- HeF; change (fs_frame_bytes 4) with 1024; split; [exact Hfin | lia]).
  destruct (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR0 (or_intror (or_introl Hcin))) as (_ & Hni).
  exact (Hni (HAi a He)). }
assert (Hel : as_errno B + 4 <= kLowMemEnd) by (destruct ERRNO as ((_ & Hl) & _); exact Hl).
assert (Hel0 : 0 <= as_errno B) by (destruct ERRNO as ((Hl & _) & _); exact Hl).
unfold kLowMemEnd in Hel.
assert (Hsep : out + 3 * (cap + 1) <= F \/ F + 1024 <= out).
{ pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR0 Hoin Hfin) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- HeF, Hrqo in Hz. change (fs_frame_bytes 4) with 1024 in Hz.
  exact Hz. }
assert (Happ : forall a, (out <= a < out + 3 * cap + 3) \/ (F <= a < F + 1024) ->
  ~ (shadow_addr F <= a < shadow_addr F + 128)).
{ intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Oapp, Fapp. unfold shadow_addr, SHADOW_OFF.
  lia. }
pose proof (Headamp.parse_props_total (hd_props nl (Model.buf r)) cap ltac:(lia)) as Hok.
apply answer_ok_parts in Hok as (Hcase & _).
assert (Hlc : Z.of_nat (length (ans_cells (Headamp.parse_props (hd_props nl (Model.buf r)) cap))) <= cap)
  by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
clear Hcase.
(* the call: hc_core, the parse's premises; MD is the model the run left *)
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (MD := d) in * end.
assert (HCc : hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W (ms_mem ms) MD (ms_regs ms) R).
{ split; [exact HJ|]. split; [exact Hnev|].
  split; [rewrite <- (mh_getr_z (ms_regs ms) 2 2 eq_refl), (Rx 2 ltac:(cbn; tauto)), (mh_getr_z regs 2 2 eq_refl); exact H2|].
  split; [rewrite <- (mh_getr_z (ms_regs ms) 3 3 eq_refl), (Rx 3 ltac:(cbn; tauto)), (mh_getr_z regs 3 3 eq_refl); exact H3|].
  split; [rewrite <- (mh_getr_z (ms_regs ms) 4 4 eq_refl), (Rx 4 ltac:(cbn; tauto)), (mh_getr_z regs 4 4 eq_refl); exact H4|].
  split; [exact HR16|]. unfold T_SEG_STK, ASTACK. split; lia. }
assert (HRa : getr (ms_regs ms) 1 = w64 RA_PARSE_RESULT)
  by (rewrite <- (mh_getr_z (ms_regs ms) 1 1 eq_refl); exact Ra1).
pose proof (hc_pre rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W (ms_mem ms) MD (ms_regs ms) R RA_PARSE_RESULT
  T_parse_STK HCc HRa ltac:(unfold RA_PARSE_RESULT; lia) ltac:(reflexivity)
  ltac:(unfold T_parse_STK, T_PARSE_FRAME, ESTACK, T_SEG_STK, ASTACK; lia)) as HP.
assert (HM : hd_kept rsegs e (hi_w3 headamp_himg_A) W memc W (ms_mem ms)).
{ intros a Ha Hb Hn. fold R in Hb. fold out cap in Hn.
  rewrite KC; [| exact Ha | intros H; apply Hn; left; apply mh_inw3; left; fold R; lia].
  apply KB; [exact Ha | intros H; apply Hn; right; lia | intros H; apply Hn; left; apply mh_inw3; left; fold R; lia
    | intros H; apply Hn; left; apply mh_inw3; right; left; fold F; lia
    | intros H; apply Hn; left; apply mh_inw3; right; right; fold F; lia
    | intros H; apply Hb; unfold T_SEG_STK, ASTACK; unfold ESTACK in H; lia]. }
assert (Hsh : hd_fsh rsegs (w_H W) (ms_mem ms) F (hi_shB headamp_himg_A)).
{ cbn [hi_shB headamp_himg_A]. apply (hm_fsh_kept rsegs (w_H W) mem2 (w_H W) (ms_mem ms) F headamp_A_shB Hfsh2).
  intros i Hi. change (length headamp_A_shB) with 80%nat in Hi. cbn in Hi.
  apply KC; unfold shadow_addr, SHADOW_OFF; lia. }
pose proof (headamp_A_site_parse_args rsegs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0 0 e pos ev r
  k (ms_regs ms) lyc Sc W (ms_mem ms) _ headamp_A_segs_low ltac:(intros a Ha; lia) ERRNO headamp_A_img_bytes_rsegs
  (mh_pre00 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre) Hwf Hlen Hpod Hpodf (conj Hout0 (conj Hoin Honew)) Hdj Hev
  Hfrm HP (Permutation_refl _) HM Hsh) as HARGS.
eapply (hc_parse_result_call rsegs B MT 0 0 _ _ _ _ _ _ _ PARSE Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W (ms_mem ms)
  _ (ms_regs ms) R nl pod out (F + 0x180) cap ev (Model.buf r) HCc HRa ltac:(lia)).
- rewrite <- (mh_getr_z (ms_regs ms) 10 10 eq_refl). exact Ra10.
- rewrite <- (mh_getr_z (ms_regs ms) 11 11 eq_refl), Ra11. exact R24.
- rewrite <- (mh_getr_z (ms_regs ms) 12 12 eq_refl), Ra12, (Rk2 22 ltac:(cbn; tauto)). exact A22.
- rewrite <- (mh_getr_z (ms_regs ms) 13 13 eq_refl), Ra13. exact R26.
- exact HARGS.
- intros W3 fx2 ly3 S3 regs3 mem3 md3 Hle Hfx HC3 Hpres Hfr3 Hperm3 Hio3 Hmo3 Hkeep3 H10' HO HRs Hev'.
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (R - T_parse_STK <= a < R) ->
    ~ (out <= a < out + 3 * (cap + 1)) -> ~ (F + 0x180 <= a < F + 0x18c) -> ~ (as_errno B <= a < as_errno B + 4) ->
    aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W) (ms_mem ms) a).
  { intros a Ha H1 H2' H3' H4'. apply Hkeep3; [exact Ha | exact H1|].
    intros [HE|[HE|HE]]; [apply H2'; lia | apply H3'; lia | exact (H4' HE)]. }
  assert (Hpst : T_parse_STK <= 16384) by (unfold T_parse_STK, T_PARSE_FRAME, ESTACK; lia).
  apply (K fx2 ly3 S3 W3 regs3 mem3 md3).
  + unfold mh_P, mh_W, mh_ans.
    cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_k x_regs x_lyc x_Sc x_W x_memc x_mdc x_e].
    fold out cap R F pod nl.
    split; [exact Hfx|].
    split; [exact (proj1 HC3)|].
    split; [exact Hfr3|]. split; [exact Hperm3|].
    split; [eapply same_io_trans; [exact Hio2|]; eapply same_io_trans; [apply same_io_wvb | exact Hio3]|].
    split; [exact Hmo3|].
    split.
    { intros r0 Hr. rewrite (Hpres r0) by (cbn [In] in Hr; unfold acallee_saved; lia).
      apply Rx. cbn [In] in Hr |- *; tauto. }
    split.
    { rewrite (Hpres 24) by (unfold acallee_saved; lia). rewrite Rk by (cbn; tauto). exact R24. }
    split.
    { rewrite (Hpres 26) by (unfold acallee_saved; lia). rewrite Rk by (cbn; tauto). exact R26. }
    split.
    { cbn [hd_xv]. fold nl pod. rewrite Z.mod_small by (destruct (nl =? 0); lia).
      eapply (hd_val_mem_kept rsegs (w_H W) (w_H W3) (ms_mem ms) mem3); [|exact H110].
      intros i Hi. apply KP; lia. }
    split.
    { eapply (hd_val_mem_kept rsegs (w_H W) (w_H W3) mem2 mem3); [|exact H118].
      intros i Hi. rewrite KP by lia. apply KC; lia. }
    split.
    { apply (hm_fsh_kept rsegs (w_H W) mem2 (w_H W3) mem3 F headamp_A_shB Hfsh2).
      intros i Hi. change (length headamp_A_shB) with 80%nat in Hi. cbn in Hi.
      rewrite KP; [apply KC; unfold shadow_addr, SHADOW_OFF; lia | unfold shadow_addr, SHADOW_OFF; lia
        | unfold shadow_addr, SHADOW_OFF; lia | | | unfold shadow_addr, SHADOW_OFF; lia].
      - intros Ho. apply (Happ (shadow_addr F + i)); [left; lia | lia].
      - intros Ho. apply (Happ (shadow_addr F + i)); [right; lia | lia]. }
    split; [exact HO|].
    split.
    { intros j Hj.
      assert (Hj3 : (j < 3)%nat) by (unfold hd_zbytes in Hj; rewrite length_map, repeat_length in Hj; exact Hj).
      rewrite hd_nth_guard by exact Hj3. change (bv_unsigned GUARD_BYTE) with 165.
      split; [|lia].
      refine (proj1 (hm_aview_val1 rsegs (w_H W3) mem3 _ 165 _)).
      rewrite Hkeep3; [| lia | lia |].
      + rewrite KC by lia. replace (out + 3 * cap + Z.of_nat j) with (out + (3 * cap + Z.of_nat j)) by ring.
        apply Hout. lia.
      + intros [HE|[HE|HE]]; [lia | lia | eapply Herr; [|exact HE]; lia]. }
    split; [apply HRs; lia|].
    split; [exact Hev'|].
    intros a Ha Hb Hn.
    rewrite KP; [| exact Ha | unfold T_SEG_STK, ASTACK in Hb; lia | intros H; apply Hn; left; exact H
      | intros H; apply Hn; right; right; right; left; exact H | intros H; apply Hn; right; right; right; right; exact H].
    rewrite KC; [| exact Ha | intros H; apply Hn; right; left; lia].
    apply KB; [exact Ha | intros H; apply Hn; left; lia | intros H; apply Hn; right; left; lia
      | intros H; apply Hn; right; right; left; exact H | intros H; apply Hn; right; right; right; left; exact H
      | intros H; apply Hb; unfold T_SEG_STK, ASTACK; unfold ESTACK in H; lia].
  + exact H10'.
  + rewrite (Hpres 27) by (unfold acallee_saved; lia). apply Rx. cbn; tauto.
Qed.

(* ===================== after the parse: a run that writes nothing, and a check call ===================== *)
Lemma mh_lc : forall cx r ev, mh_f cx r ev -> Z.of_nat (length (ans_cells (mh_ans cx r))) <= e_cap (x_e cx).
Proof.
intros cx r ev HC. pose proof (f_cap _ _ _ HC) as Hcap. unfold mh_ans.
pose proof (Headamp.parse_props_total (hd_props (e_null (x_e cx)) (Model.buf r)) (e_cap (x_e cx)) ltac:(lia)) as Hok.
apply answer_ok_parts in Hok as (Hcase & _).
destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia].
Qed.

(* a run with no region left every byte as it was *)
Lemma mh_frame_nil : forall E (H : word -> bool) (m m' : word -> option byte),
frame_of E [] (mrestrict H m) (mrestrict H m') -> forall a, aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E H m m' HF a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (rg & Hin & _). destruct Hin.
Qed.
(* a run whose one region writes nothing left every byte as it was *)
Lemma mh_frame_ro : forall E rg (H : word -> bool) (m m' : word -> option byte),
YP09.r_whi rg <= YP09.r_wlo rg ->
frame_of E [rg] (mrestrict H m) (mrestrict H m') -> forall a, aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rg H m m' Hw HF a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (rg' & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]]. lia.
Qed.

Lemma mh_P_run : forall cx r (fx2 : YK11.FPState) ly2 S2 W2 regs mem md regsT memT mdT,
mh_P cx r fx2 ly2 S2 W2 regs mem md ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) ly2 S2 W2 memT mdT (x_k cx) ->
(forall a, aview rsegs (w_H W2) memT a = aview rsegs (w_H W2) mem a) ->
(forall r0, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26] ->
 getr regsT (Z_to_bv 5 r0) = getr regs (Z_to_bv 5 r0)) ->
same_io md mdT ->
mh_P cx r fx2 ly2 S2 W2 regsT memT mdT.
Proof.
intros cx r fx2 ly2 S2 W2 regs mem md regsT memT mdT HP HJT K Rk Hio'.
destruct HP as (Hfx & _ & Hfr & Hperm & Hio & Hmo & Rk0 & R24 & R26 & H110 & H118 & Hfsh & Hcells & Hguard & Hres & Hev
  & KP).
split; [exact Hfx|]. split; [exact HJT|]. split; [exact Hfr|]. split; [exact Hperm|].
split; [eapply same_io_trans; [exact Hio | exact Hio']|]. split; [exact Hmo|].
split; [intros r0 Hr; rewrite Rk by (cbn [In] in Hr |- *; tauto); exact (Rk0 r0 Hr)|].
split; [rewrite Rk by (cbn; tauto); exact R24|].
split; [rewrite Rk by (cbn; tauto); exact R26|].
split; [eapply hd_val_mem_kept; [|exact H110]; intros i _; apply K|].
split; [eapply hd_val_mem_kept; [|exact H118]; intros i _; apply K|].
split; [apply (hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh); intros i _; apply K|].
split; [eapply hd_garr8_kept; [|exact Hcells]; intros j _; apply K|].
split; [eapply hd_garr8_kept; [|exact Hguard]; intros j _; apply K|].
split; [eapply hd_garr8_kept; [|exact Hres]; intros j _; apply K|].
split; [destruct Hev as (ev' & Hev'); exists ev'; intros kk Hkk; rewrite K; exact (Hev' kk Hkk)|].
intros a Ha Hb Hn. rewrite K. exact (KP a Ha Hb Hn).
Qed.

Lemma mh_P_call : forall cx r ev (fx2 : YK11.FPState) ly2 S2 W2 regs mem md ly4 S4 W4 regs4 mem4 md4,
mh_f cx r ev -> mh_P cx r fx2 ly2 S2 W2 regs mem md ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) ly4 S4 W4 mem4 md4 (x_k cx) ->
aregs_preserved regs regs4 -> frames S4 = frames S2 -> Permutation (ablocks B ly4 S4) (ablocks B ly2 S2) ->
same_io md md4 -> mo_le MT S2 S4 0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (e_R (x_e cx) - T_check_STK <= x < e_R (x_e cx)) ->
 aview rsegs (w_H W4) mem4 x = aview rsegs (w_H W2) mem x) ->
mh_P cx r fx2 ly4 S4 W4 regs4 mem4 md4.
Proof using ERRNO MTL.
intros cx r ev fx2 ly2 S2 W2 regs mem md ly4 S4 W4 regs4 mem4 md4 HC HP HJ4 Hpres Hfr4 Hperm4 Hio4 Hmo4 Hk4.
pose proof (mh_bounds cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (mh_lc cx r ev HC) as Hlc. pose proof (f_cap _ _ _ HC) as Hcap.
destruct HP as (Hfx & _ & Hfr & Hperm & Hio & Hmo & Rk0 & R24 & R26 & H110 & H118 & Hfsh & Hcells & Hguard & Hres & Hev
  & KP).
assert (Hel : as_errno B + 4 <= kLowMemEnd) by (destruct ERRNO as ((_ & Hl) & _); exact Hl).
assert (Hel0 : 0 <= as_errno B) by (destruct ERRNO as ((Hl & _) & _); exact Hl).
unfold kLowMemEnd in Hel.
set (out := e_out (x_e cx)) in *. set (cap := e_cap (x_e cx)) in *. set (R := e_R (x_e cx)) in *.
set (F := e_F (x_e cx)) in *.
unfold MHCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
assert (F8 : F = 8 * (F / 8)).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as D.
  assert (F mod 8 = 0) by (rewrite <- (Z.mod_mod_divide F 32 8) by (exists 4; reflexivity); rewrite Fm32; reflexivity).
  lia. }
assert (K4 : forall x, 0 <= x < R - 32 \/ R <= x < 2 ^ 64 -> aview rsegs (w_H W4) mem4 x = aview rsegs (w_H W2) mem x)
  by (intros x Hx; apply Hk4; unfold T_check_STK; lia).
split; [exact Hfx|]. split; [exact HJ4|]. split; [rewrite Hfr4; exact Hfr|].
split; [eapply Permutation_trans; [exact Hperm4 | exact Hperm]|].
split; [eapply same_io_trans; [exact Hio | exact Hio4]|].
split; [exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo Hmo4)|].
split; [intros r0 Hr; rewrite (Hpres r0) by (cbn [In] in Hr; unfold acallee_saved; lia); exact (Rk0 r0 Hr)|].
split; [rewrite (Hpres 24) by (unfold acallee_saved; lia); exact R24|].
split; [rewrite (Hpres 26) by (unfold acallee_saved; lia); exact R26|].
split; [eapply hd_val_mem_kept; [|exact H110]; intros i Hi; apply K4; lia|].
split; [eapply hd_val_mem_kept; [|exact H118]; intros i Hi; apply K4; lia|].
split; [apply (hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh); intros i Hi; change (length headamp_A_shB) with 80%nat in Hi;
  apply K4; unfold shadow_addr, SHADOW_OFF; lia|].
split.
{ eapply hd_garr8_kept; [|exact Hcells]. intros j Hj. unfold hd_zbytes in Hj.
  rewrite length_map, length_ha_cells_bytes in Hj. apply K4. lia. }
split.
{ eapply hd_garr8_kept; [|exact Hguard]. intros j Hj. unfold hd_zbytes in Hj.
  rewrite length_map, repeat_length in Hj. apply K4. lia. }
split.
{ eapply hd_garr8_kept; [|exact Hres]. intros j Hj. unfold hd_zbytes, ans_res_bytes in Hj.
  rewrite length_map, length_ha_res_bytes in Hj. apply K4. lia. }
split; [destruct Hev as (ev' & Hev'); exists ev'; intros kk Hkk; rewrite K4 by lia; exact (Hev' kk Hkk)|].
intros a Ha Hb Hn. rewrite K4 by (unfold T_SEG_STK, ASTACK in Hb; lia). exact (KP a Ha Hb Hn).
Qed.

(* the frame of facts a check call asks, at a state of the walk after the parse *)
Lemma mh_core : forall cx r ev (fx2 : YK11.FPState) ly2 S2 W2 regs mem md,
mh_f cx r ev -> mh_P cx r fx2 ly2 S2 W2 regs mem md ->
hc_core rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_k cx) ly2 S2 W2 mem md regs (e_R (x_e cx)).
Proof.
intros cx r ev fx2 ly2 S2 W2 regs mem md HC HP.
pose proof (mh_bounds cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
destruct HP as (_ & HJ & _ & _ & _ & _ & Rk0 & _).
split; [exact HJ|]. split; [exact (f_nev _ _ _ HC)|].
split; [rewrite <- (mh_getr_z regs 2 2 eq_refl), (Rk0 2 ltac:(cbn; tauto)), (mh_getr_z _ 2 2 eq_refl); exact (f_r2 _ _ _ HC)|].
split; [rewrite <- (mh_getr_z regs 3 3 eq_refl), (Rk0 3 ltac:(cbn; tauto)), (mh_getr_z _ 3 3 eq_refl); exact (f_r3 _ _ _ HC)|].
split; [rewrite <- (mh_getr_z regs 4 4 eq_refl), (Rk0 4 ltac:(cbn; tauto)), (mh_getr_z _ 4 4 eq_refl); exact (f_r4 _ _ _ HC)|].
split; [rewrite <- (Z.mod_mod_divide _ 32 16) by (exists 2; reflexivity); rewrite (f_R32 _ _ _ HC); reflexivity|].
split; [exact HSTK | lia].
Qed.

(* =================== the three checks, at the parse's float state =================== *)
Hypothesis CK_NO : forall fx' : YK11.FPState, hd_check_no_overrun_specX (fx := fx') rsegs B MT A_CK_NO_OVERRUN.
Hypothesis CK_COUNT : forall fx' : YK11.FPState, hd_check_count_specX (fx := fx') rsegs B MT A_CK_COUNT.
Hypothesis CK_CV : forall fx' : YK11.FPState, hd_check_cells_valid_specX (fx := fx') rsegs B MT A_CK_CELLS_VALID.

(* ===================== block D: 0x82ef0 .. check_no_overrun's return 0x82efc ===================== *)
Lemma mh_D : forall cx r ev (fx2 : YK11.FPState) ly2 S2 W2 regs mem md (Q : world rsegs -> config -> Prop),
mh_f cx r ev -> mh_P cx r fx2 ly2 S2 W2 regs mem md ->
getr regs (Z_to_bv 5 10) = w64 (ans_rc (mh_ans cx r)) ->
(forall ly4 S4 W4 regs4 mem4 md4, mh_P cx r fx2 ly4 S4 W4 regs4 mem4 md4 ->
 getr regs4 (Z_to_bv 5 27) = w64 (ans_rc (mh_ans cx r)) ->
 SRr rsegs W4 (@cfg_at fx2 rsegs RA_CK_NO_OVERRUN regs4 mem4 md4) Q) ->
SRr rsegs W2 (@cfg_at fx2 rsegs RA_PARSE_RESULT regs mem md) Q.
Proof using ERRNO MTL CK_NO.
intros cx r ev fx2 ly2 S2 W2 regs mem md Q HC HP H10 K.
pose proof (mh_bounds cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
unfold MHCEIL in Hceil.
pose proof (mh_core cx r ev fx2 ly2 S2 W2 regs mem md HC HP) as HC2.
pose proof HP as (_ & HJ & _ & Hperm & _ & _ & Rk0 & R24 & _ & _ & _ & _ & _ & Hguard & _).
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (f_cap _ _ _ HC) as Hcap.
set (out := e_out (x_e cx)) in *. set (cap := e_cap (x_e cx)) in *. set (R := e_R (x_e cx)) in *.
assert (HS : st_ok rsegs (Ereg regs []) (mkSS 0x82ef0 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 0x82ef0) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
unfold cfg_at, RA_PARSE_RESULT. change (w64 0x82ef0) with (Z_to_bv 64 0x82ef0).
aj_run_to mh_tbl_ok HS HJ 0x83e3c.
{ apply awr_ok_nil. }
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
rreg HS (Z_to_bv 5 1) Ra1.
assert (Ra10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (out + 3 * cap)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 10)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 10)) with v end.
  rewrite denot_lit_U. unfold w64. f_equal. rewrite ?U_SAlu, ?U_SLit. cbn [zalu_raw].
  rewrite (U_atom _ 24 out), (U_atom _ 20 (3 * cap)).
  - unfold zcanon, M64. rewrite Z.mod_small by lia. ring.
  - rewrite (ew_Ereg_nat regs _ 20 (Z_to_bv 5 20) eq_refl), (Rk0 20 ltac:(cbn; tauto)). exact (f_s4 _ _ _ HC).
  - lia.
  - rewrite (ew_Ereg_nat regs _ 24 (Z_to_bv 5 24) eq_refl). exact R24.
  - lia. }
assert (Ra27 : getr (ms_regs ms) (Z_to_bv 5 27) = getr regs (Z_to_bv 5 10))
  by (eapply (mh_reg_is _ _ _ ms (w_H W2) regs [] _ _ 10 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rk : forall r0, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26] ->
  getr (ms_regs ms) (Z_to_bv 5 r0) = getr regs (Z_to_bv 5 r0)).
{ intros r0 Hr. eapply (mh_reg_atom _ _ _ ms (w_H W2) regs [] (Z_to_bv 5 r0) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
pose proof (mh_frame_nil _ _ _ _ HFr) as KD.
pose proof (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (MD := d) in * end.
assert (HPr : mh_P cx r fx2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) MD)
  by (apply (mh_P_run cx r fx2 ly2 S2 W2 regs mem md _ _ _ HP HJ KD Rk); subst MD; apply same_io_wvb).
pose proof (mh_core cx r ev fx2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) MD HC HPr) as HCc.
assert (HRa : getr (ms_regs ms) 1 = w64 RA_CK_NO_OVERRUN)
  by (rewrite <- (mh_getr_z (ms_regs ms) 1 1 eq_refl); exact Ra1).
pose proof (hc_pre rsegs B _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem ms) MD (ms_regs ms) R RA_CK_NO_OVERRUN
  T_check_STK HCc HRa ltac:(unfold RA_CK_NO_OVERRUN; lia) ltac:(reflexivity)
  ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia)) as HPc.
destruct (f_outf _ _ _ HC) as (_ & Hoin & _).
assert (Hoin2 : In (out, 3 * (cap + 1)) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Hoin).
assert (Hrqo : req_size (3 * (cap + 1)) = 3 * (cap + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (cap + 1)) 0); lia).
pose proof (headamp_A_site_block rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPc Hoin2) as (_ & _ & _ & _ & _ & Hra).
rewrite Hrqo in Hra.
eapply (hc_check_no_overrun_call (fx := fx2) rsegs B MT (CK_NO fx2) Q _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem ms) MD
  (ms_regs ms) R (out + 3 * cap) HCc HRa).
- rewrite <- (mh_getr_z (ms_regs ms) 10 10 eq_refl). exact Ra10.
- eapply hd_garr8_kept; [|exact Hguard]. intros j _. apply KD.
- exact (proj1 (Hra (out + 3 * cap) 3 ltac:(lia) ltac:(lia))).
- exact (proj2 (Hra (out + 3 * cap) 3 ltac:(lia) ltac:(lia))).
- eapply (headamp_A_site_block_app rsegs B); [exact HPc | exact Hoin2 | lia | lia | rewrite Hrqo; lia].
- intros W4 ly4 S4 regs4 mem4 md4 Hle HC4 Hpres4 Hfr4 Hperm4 Hio4 Hmo4 Hk4.
  apply (K ly4 S4 W4 regs4 mem4 md4).
  + exact (mh_P_call cx r ev fx2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) MD ly4 S4 W4 regs4 mem4 md4 HC HPr (proj1 HC4)
      Hpres4 Hfr4 Hperm4 Hio4 Hmo4 Hk4).
  + rewrite (Hpres4 27) by (unfold acallee_saved; lia). rewrite Ra27. exact H10.
Qed.

(* ===================== block E: 0x82efc .. check_count's return 0x82f0c ===================== *)
Lemma mh_E : forall cx r ev (fx2 : YK11.FPState) ly2 S2 W2 regs mem md (Q : world rsegs -> config -> Prop),
mh_f cx r ev -> mh_P cx r fx2 ly2 S2 W2 regs mem md ->
getr regs (Z_to_bv 5 27) = w64 (ans_rc (mh_ans cx r)) ->
(forall ly4 S4 W4 regs4 mem4 md4, mh_P cx r fx2 ly4 S4 W4 regs4 mem4 md4 ->
 getr regs4 (Z_to_bv 5 27) = w64 (ans_rc (mh_ans cx r)) ->
 SRr rsegs W4 (@cfg_at fx2 rsegs RA_CK_COUNT regs4 mem4 md4) Q) ->
SRr rsegs W2 (@cfg_at fx2 rsegs RA_CK_NO_OVERRUN regs mem md) Q.
Proof using ERRNO MTL CK_COUNT.
intros cx r ev fx2 ly2 S2 W2 regs mem md Q HC HP H27 K.
pose proof (mh_bounds cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
unfold MHCEIL in Hceil.
pose proof HP as (_ & HJ & _ & Hperm & _ & _ & Rk0 & R24 & R26 & _ & _ & Hfsh & _ & _ & Hres & _).
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (f_cap _ _ _ HC) as Hcap.
set (R := e_R (x_e cx)) in *.
assert (HS : st_ok rsegs (Ereg regs []) (mkSS 0x82efc sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 0x82efc) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
unfold cfg_at, RA_CK_NO_OVERRUN. change (w64 0x82efc) with (Z_to_bv 64 0x82efc).
aj_run_to mh_tbl_ok HS HJ 0x83ee8.
{ apply awr_ok_nil. }
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
rreg HS (Z_to_bv 5 1) Ra1.
assert (Ra10 : getr (ms_regs ms) (Z_to_bv 5 10) = getr regs (Z_to_bv 5 27))
  by (eapply (mh_reg_is _ _ _ ms (w_H W2) regs [] _ _ 27 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Ra11 : getr (ms_regs ms) (Z_to_bv 5 11) = getr regs (Z_to_bv 5 22))
  by (eapply (mh_reg_is _ _ _ ms (w_H W2) regs [] _ _ 22 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Ra12 : getr (ms_regs ms) (Z_to_bv 5 12) = getr regs (Z_to_bv 5 26))
  by (eapply (mh_reg_is _ _ _ ms (w_H W2) regs [] _ _ 26 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rk : forall r0, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r0) = getr regs (Z_to_bv 5 r0)).
{ intros r0 Hr. eapply (mh_reg_atom _ _ _ ms (w_H W2) regs [] (Z_to_bv 5 r0) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
pose proof (mh_frame_nil _ _ _ _ HFr) as KD.
pose proof (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (MD := d) in * end.
assert (HPr : mh_P cx r fx2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) MD).
{ apply (mh_P_run cx r fx2 ly2 S2 W2 regs mem md _ _ _ HP HJ KD); [|subst MD; apply same_io_wvb].
  intros r0 Hr. apply Rk. cbn [In] in Hr |- *; tauto. }
pose proof (mh_core cx r ev fx2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) MD HC HPr) as HCc.
assert (HRa : getr (ms_regs ms) 1 = w64 RA_CK_COUNT)
  by (rewrite <- (mh_getr_z (ms_regs ms) 1 1 eq_refl); exact Ra1).
pose proof (hc_pre rsegs B _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem ms) MD (ms_regs ms) R RA_CK_COUNT
  T_check_STK HCc HRa ltac:(unfold RA_CK_COUNT; lia) ltac:(reflexivity)
  ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia)) as HPc.
assert (HF2 : e_F (x_e cx) = frame_addr ly2 (hi_cid headamp_himg_A) (x_pos cx)).
{ rewrite (f_F _ _ _ HC). cbn [hi_cid headamp_himg_A]. symmetry.
  eapply (headamp_A_site_frame_at rsegs B); [exact (f_J _ _ _ HC) | exact HJ]. }
pose proof (headamp_A_site_count rsegs B _ _ _ _ _ _ _ _ _ _ (ms_regs ms) ly2 S2 W2 (ms_mem ms) MD (x_e cx) (x_pos cx) r
  (mh_ans cx r) HPc (f_own _ _ _ HC) HF2
  ltac:(cbn [hi_shB headamp_himg_A]; apply (hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh); intros i _; apply KD)
  (f_wf _ _ _ HC) Hcap eq_refl
  ltac:(eapply hd_garr8_kept; [|exact Hres]; intros j _; apply KD)) as (Hrc1 & Hcap31 & Hres3).
eapply (hc_check_count_call (fx := fx2) rsegs B MT (CK_COUNT fx2) Q _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem ms) MD
  (ms_regs ms) R (ans_rc (mh_ans cx r)) (e_cap (x_e cx)) (ans_keys (mh_ans cx r)) (e_F (x_e cx) + 0x180) HCc HRa).
- rewrite <- (mh_getr_z (ms_regs ms) 10 10 eq_refl), Ra10. exact H27.
- rewrite <- (mh_getr_z (ms_regs ms) 11 11 eq_refl), Ra11, (Rk0 22 ltac:(cbn; tauto)). exact (f_s6 _ _ _ HC).
- rewrite <- (mh_getr_z (ms_regs ms) 12 12 eq_refl), Ra12. exact R26.
- exact Hrc1.
- exact Hcap31.
- exact Hres3.
- intros W4 ly4 S4 regs4 mem4 md4 Hle HC4 Hpres4 Hfr4 Hperm4 Hio4 Hmo4 Hk4.
  apply (K ly4 S4 W4 regs4 mem4 md4).
  + exact (mh_P_call cx r ev fx2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) MD ly4 S4 W4 regs4 mem4 md4 HC HPr (proj1 HC4)
      Hpres4 Hfr4 Hperm4 Hio4 Hmo4 Hk4).
  + rewrite (Hpres4 27) by (unfold acallee_saved; lia). rewrite Rk by (cbn; tauto). exact H27.
Qed.

(* ===================== block F: 0x82f0c .. check_cells_valid's return 0x82f18 ===================== *)
Lemma mh_F : forall cx r ev (fx2 : YK11.FPState) ly2 S2 W2 regs mem md (Q : world rsegs -> config -> Prop),
mh_f cx r ev -> mh_P cx r fx2 ly2 S2 W2 regs mem md ->
getr regs (Z_to_bv 5 27) = w64 (ans_rc (mh_ans cx r)) ->
(forall ly4 S4 W4 regs4 mem4 md4, mh_P cx r fx2 ly4 S4 W4 regs4 mem4 md4 ->
 getr regs4 (Z_to_bv 5 27) = w64 (ans_rc (mh_ans cx r)) ->
 SRr rsegs W4 (@cfg_at fx2 rsegs MH_F1 regs4 mem4 md4) Q) ->
SRr rsegs W2 (@cfg_at fx2 rsegs RA_CK_COUNT regs mem md) Q.
Proof using ERRNO MTL CK_CV.
intros cx r ev fx2 ly2 S2 W2 regs mem md Q HC HP H27 K.
pose proof (mh_bounds cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
unfold MHCEIL in Hceil.
pose proof HP as (_ & HJ & _ & Hperm & _ & _ & Rk0 & R24 & R26 & _ & _ & _ & Hcells & _ & _ & _).
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (f_cap _ _ _ HC) as Hcap.
set (R := e_R (x_e cx)) in *.
assert (HS : st_ok rsegs (Ereg regs []) (mkSS 0x82f0c sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 0x82f0c) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
unfold cfg_at, RA_CK_COUNT. change (w64 0x82f0c) with (Z_to_bv 64 0x82f0c).
aj_run_to mh_tbl_ok HS HJ 0x83f7c.
{ apply awr_ok_nil. }
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
rreg HS (Z_to_bv 5 1) Ra1.
assert (Ra10 : getr (ms_regs ms) (Z_to_bv 5 10) = getr regs (Z_to_bv 5 24))
  by (eapply (mh_reg_is _ _ _ ms (w_H W2) regs [] _ _ 24 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Ra11 : getr (ms_regs ms) (Z_to_bv 5 11) = getr regs (Z_to_bv 5 27))
  by (eapply (mh_reg_is _ _ _ ms (w_H W2) regs [] _ _ 27 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rk : forall r0, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r0) = getr regs (Z_to_bv 5 r0)).
{ intros r0 Hr. eapply (mh_reg_atom _ _ _ ms (w_H W2) regs [] (Z_to_bv 5 r0) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
pose proof (mh_frame_nil _ _ _ _ HFr) as KD.
pose proof (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (MD := d) in * end.
assert (HPr : mh_P cx r fx2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) MD).
{ apply (mh_P_run cx r fx2 ly2 S2 W2 regs mem md _ _ _ HP HJ KD); [|subst MD; apply same_io_wvb].
  intros r0 Hr. apply Rk. cbn [In] in Hr |- *; tauto. }
pose proof (mh_core cx r ev fx2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) MD HC HPr) as HCc.
assert (HRa : getr (ms_regs ms) 1 = w64 RA_CK_CELLS_VALID)
  by (rewrite <- (mh_getr_z (ms_regs ms) 1 1 eq_refl); exact Ra1).
pose proof (hc_pre rsegs B _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem ms) MD (ms_regs ms) R RA_CK_CELLS_VALID
  T_check_STK HCc HRa ltac:(unfold RA_CK_CELLS_VALID; lia) ltac:(reflexivity)
  ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia)) as HPc.
destruct (f_outf _ _ _ HC) as (_ & Hoin & _).
assert (Hoin2 : In (e_out (x_e cx), 3 * (e_cap (x_e cx) + 1)) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm) Hoin).
pose proof (headamp_A_site_cells_valid rsegs B _ _ _ _ _ _ _ _ _ _ (ms_regs ms) ly2 S2 W2 (ms_mem ms) MD (x_e cx)
  (hd_props (e_null (x_e cx)) (Model.buf r)) (mh_ans cx r) HPc Hoin2 Hcap eq_refl
  ltac:(eapply hd_garr8_kept; [|exact Hcells]; intros j _; apply KD)) as (Hrc31 & Hcv).
eapply (hc_check_cells_valid_call (fx := fx2) rsegs B MT (CK_CV fx2) Q _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem ms) MD
  (ms_regs ms) R (ans_rc (mh_ans cx r)) (e_out (x_e cx)) (ans_cells (mh_ans cx r)) HCc HRa).
- rewrite <- (mh_getr_z (ms_regs ms) 10 10 eq_refl), Ra10. exact R24.
- rewrite <- (mh_getr_z (ms_regs ms) 11 11 eq_refl), Ra11. exact H27.
- exact Hrc31.
- exact Hcv.
- intros W4 ly4 S4 regs4 mem4 md4 Hle HC4 Hpres4 Hfr4 Hperm4 Hio4 Hmo4 Hk4.
  apply (K ly4 S4 W4 regs4 mem4 md4).
  + exact (mh_P_call cx r ev fx2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) MD ly4 S4 W4 regs4 mem4 md4 HC HPr (proj1 HC4)
      Hpres4 Hfr4 Hperm4 Hio4 Hmo4 Hk4).
  + rewrite (Hpres4 27) by (unfold acallee_saved; lia). rewrite Rk by (cbn; tauto). exact H27.
Qed.

(* ===================== block G: 0x82f18 .. X 0x82f30 / FIRST 0x83724 ===================== *)
(* the entry state of the last run: pp->corrupt's 4 bytes at s2 as the closed value c, s7 = the shadow offset and
   s2 = pp + 0x4d18 as atom facts *)
Definition mh_rG (c : Z) : YP09.region := YP09.mkRegion (Some 18%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit c))].
Definition mh_factsG : facts := mkFacts [(23%nat, mkAF 0x7fff8000 0x7fff8000 0); (18%nat, mkAF 4096 MHCEIL 3)] [] [].

Lemma mh_G : forall cx r ev (fx2 : YK11.FPState) ly2 S2 W2 regs mem md (Q : world rsegs -> config -> Prop),
mh_f cx r ev -> mh_P cx r fx2 ly2 S2 W2 regs mem md ->
getr regs (Z_to_bv 5 27) = w64 (ans_rc (mh_ans cx r)) ->
(forall regsF memF mdF, Model.corrupt r = false -> mh_P cx r fx2 ly2 S2 W2 regsF memF mdF ->
 getr regsF (Z_to_bv 5 27) = w64 (ans_rc (mh_ans cx r)) ->
 SRr rsegs W2 (@cfg_at fx2 rsegs 0x82f30 regsF memF mdF) Q) ->
(forall regsF memF mdF, mh_P cx r fx2 ly2 S2 W2 regsF memF mdF ->
 getr regsF (Z_to_bv 5 27) = w64 (ans_rc (mh_ans cx r)) ->
 SRr rsegs W2 (@cfg_at fx2 rsegs 0x83724 regsF memF mdF) Q) ->
SRr rsegs W2 (@cfg_at fx2 rsegs MH_F1 regs mem md) Q.
Proof using ERRNO.
intros cx r ev fx2 ly2 S2 W2 regs mem md Q HC HP H27 HX HFIRST.
pose proof (mh_bounds cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
unfold MHCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
pose proof HP as (_ & HJ & _ & Hperm & _ & _ & Rk0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & KP).
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (f_cap _ _ _ HC) as Hcap. pose proof (f_wf _ _ _ HC) as Hwf.
pose proof (f_J _ _ _ HC) as HJ0. pose proof HJ0 as (HAR0 & _ & _ & _ & _ & Hfrs & _).
destruct (f_outf _ _ _ HC) as (_ & Hoin & _).
destruct (f_ppf _ _ _ HC) as (_ & Hppin & _).
assert (Hfin : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact (f_own _ _ _ HC)).
assert (Hel : as_errno B + 4 <= kLowMemEnd) by (destruct ERRNO as ((_ & Hl) & _); exact Hl).
unfold kLowMemEnd in Hel.
set (pp := e_pp (x_e cx)) in *. set (out := e_out (x_e cx)) in *. set (cap := e_cap (x_e cx)) in *.
set (R := e_R (x_e cx)) in *. set (F := e_F (x_e cx)) in *.
assert (F8 : F = 8 * (F / 8)).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as D.
  assert (F mod 8 = 0) by (rewrite <- (Z.mod_mod_divide F 32 8) by (exists 4; reflexivity); rewrite Fm32; reflexivity).
  lia. }
(* the record's facts pp's image needs *)
pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & Hbl).
destruct (Model.ents_wf r Hwf) as (He & Hew).
assert (Hb : Z.of_nat (length (Model.buf r)) <= Layout.POD_BUF_MAX) by (unfold Layout.POD_BUF_MAX; lia).
assert (Hs : Forall (fun e => (length (Model.e_body e) <= 96)%nat) (Model.ents r)).
{ rewrite Forall_forall in Hew |- *. intros x Hx. destruct (Hew x Hx) as (_ & Hb' & Hsz). rewrite Hb'. lia. }
assert (Hplen : Z.of_nat (length (Layout.pp_bytes r)) = Layout.PP_SIZE)
  by (unfold Layout.pp_bytes; apply Layout.length_pp_image; [exact Hb | exact He | exact Hs]).
(* pp's bytes at the run's start: outside every byte the head writes *)
assert (Hpo : pp + 19744 <= out \/ out + 3 * (cap + 1) <= pp).
{ assert (Hne : (pp, Layout.PP_SIZE) <> (out, 3 * (cap + 1))) by (intros Heq; injection Heq as _ Hl; unfold Layout.PP_SIZE in Hl; lia).
  pose proof (sep_blocks rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR0 Hppin Hoin Hne) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz.
  replace (req_size (3 * (cap + 1))) with (3 * (cap + 1)) in Hz
    by (unfold req_size; destruct (Z.eqb_spec (3 * (cap + 1)) 0); lia).
  change (req_size Layout.PP_SIZE) with 19744 in Hz. exact Hz. }
assert (Hpf : pp + 19744 <= F \/ F + 1024 <= pp).
{ pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR0 Hppin Hfin) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- (f_F _ _ _ HC) in Hz. fold F in Hz.
  change (req_size Layout.PP_SIZE) with 19744 in Hz. change (fs_frame_bytes 4) with 1024 in Hz. exact Hz. }
assert (Hpe : forall a, pp <= a < pp + 19744 -> ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha He'. destruct ERRNO as (_ & HAi & _).
  assert (Hcin : exists p n, In (p, n) (ablocks B (x_lyc cx) (x_Sc cx)) /\ p <= a < p + req_size n)
    by (exists pp, Layout.PP_SIZE; split; [exact Hppin | change (req_size Layout.PP_SIZE) with 19744; lia]).
  destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR0 (or_introl Hcin)) as (_ & Hni).
  exact (Hni (HAi a He')). }
assert (Hpp2 : garr8 rsegs (mrestrict (w_H W2) mem) pp (hd_zbytes (Layout.pp_bytes r))).
{ eapply hd_garr8_kept; [|exact (f_pp _ _ _ HC)]. intros j Hj.
  unfold hd_zbytes in Hj. rewrite length_map in Hj. unfold Layout.PP_SIZE in Hplen. fold pp.
  apply KP; [lia | unfold T_SEG_STK, ASTACK; lia |].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Papp.
  intros [Hw|[Hw|[Hw|[Hw|Hw]]]]; fold out cap R F in Hw.
  - lia.
  - lia.
  - unfold shadow_addr, SHADOW_OFF in Hw. lia.
  - lia.
  - eapply Hpe; [|exact Hw]. lia. }
pose proof (hm_pp_corrupt rsegs (Model.buf r) (Model.is_props r) (Model.has_params r) (Model.params_struct r)
  (Model.ents r) (Model.corrupt r) Hb He Hs (w_H W2) mem pp Hpp2) as Hcor.
change Layout.OFF_CORRUPT with 0x4d18 in Hcor.
(* the entry state and the shadow entry of the check *)
assert (H18 : getr regs (Z_to_bv 5 18) = w64 (pp + 0x4d18)) by (rewrite (Rk0 18 ltac:(cbn; tauto)); exact (f_s2 _ _ _ HC)).
assert (H23 : getr regs (Z_to_bv 5 23) = w64 SHADOW_OFF) by (rewrite (Rk0 23 ltac:(cbn; tauto)); exact (f_s7 _ _ _ HC)).
assert (E18 : bv_unsigned (ew (Ereg regs []) 18) = pp + 0x4d18).
{ rewrite (ew_Ereg_nat regs _ 18 (Z_to_bv 5 18) eq_refl), H18. unfold w64. apply unsigned_lit_small. lia. }
assert (E23 : bv_unsigned (ew (Ereg regs []) 23) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs _ 23 (Z_to_bv 5 23) eq_refl), H23. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (Hppin2 : In (pp, Layout.PP_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Hppin).
destruct (hm_blk_ra rsegs B ly2 S2 W2 mem md pp Layout.PP_SIZE (pp + 0x4d18) 8 (proj1 HJ) Hppin2 ltac:(lia)
  ltac:(change (req_size Layout.PP_SIZE) with 19744; lia)) as (Hra & _).
assert (SHOK : sh_ok rsegs MHBx MHSH (Ereg regs []) (mrestrict (w_H W2) mem)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range rsegs (w_H W2) mem (Ereg regs []) MHBx 18 (pp + 0x4d18) 8 (pp + 0x4d18) 0 8 Hra).
  - apply (U_atom _ 23 SHADOW_OFF); [rewrite (ew_Ereg_nat regs _ 23 (Z_to_bv 5 23) eq_refl); exact H23 | unfold SHADOW_OFF; lia].
  - apply (U_atom _ 18 (pp + 0x4d18)); [rewrite (ew_Ereg_nat regs _ 18 (Z_to_bv 5 18) eq_refl); exact H18 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn in Hx. unfold SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Papp. lia. }
assert (HS : st_ok rsegs (Ereg regs []) (mkSS 0x82f18 sr_atoms [mh_rG (Z.b2z (Model.corrupt r))] None mh_factsG)
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 0x82f18) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold mh_rG.
    apply (hm_ro_region rsegs _ (w_H W2) mem 18 (pp + 0x4d18) 0 4); [exact E18 | lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ (pp + 0x4d18) 0 4 (SLit (Z.b2z (Model.corrupt r))) (Z.b2z (Model.corrupt r)));
      [reflexivity | cbn; destruct (Model.corrupt r); cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Hcor.
  - cbn. tauto.
  - unfold facts_ok, mh_factsG. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite E18, E23. unfold SHADOW_OFF, MHCEIL in *.
    change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
    assert (H8p : pp mod 8 = 0)
      by (rewrite <- (Z.mod_mod_divide pp 16 8) by (exists 2; reflexivity); rewrite Pm16; reflexivity).
    assert (H8 : (pp + 0x4d18) mod 8 = 0) by (rewrite Zplus_mod, H8p; reflexivity).
    repeat split; lia. }
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
unfold cfg_at, MH_F1. change (w64 0x82f18) with (Z_to_bv 64 0x82f18).
destruct (Model.corrupt r) eqn:Hc.
- (* pp->corrupt = 1: to FIRST *)
  aj_run_tok mh_tbl_ok HS HJ SHOK MHspan.
  { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  pose proof (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems. rewrite Ems.
  assert (Rk : forall r0, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r0) = getr regs (Z_to_bv 5 r0)).
  { intros r0 Hr. eapply (mh_reg_atom _ _ _ ms (w_H W2) regs [] (Z_to_bv 5 r0) HS HAE).
    cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
  apply (HFIRST (ms_regs ms) (ms_mem ms) _).
  + apply (mh_P_run cx r fx2 ly2 S2 W2 regs mem md _ _ _ HP HJ
      (mh_frame_ro _ (mh_rG (Z.b2z true)) _ _ _ ltac:(cbn; lia) HFr)); [|apply same_io_wvb].
    intros r0 Hr. apply Rk. cbn [In] in Hr |- *; tauto.
  + rewrite Rk by (cbn; tauto). exact H27.
- (* pp->corrupt = 0: to X *)
  aj_run_tok mh_tbl_ok HS HJ SHOK MHspan.
  { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  pose proof (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems. rewrite Ems.
  assert (Rk : forall r0, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r0) = getr regs (Z_to_bv 5 r0)).
  { intros r0 Hr. eapply (mh_reg_atom _ _ _ ms (w_H W2) regs [] (Z_to_bv 5 r0) HS HAE).
    cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
  apply (HX (ms_regs ms) (ms_mem ms) _ eq_refl).
  + apply (mh_P_run cx r fx2 ly2 S2 W2 regs mem md _ _ _ HP HJ
      (mh_frame_ro _ (mh_rG (Z.b2z false)) _ _ _ ltac:(cbn; lia) HFr)); [|apply same_io_wvb].
    intros r0 Hr. apply Rk. cbn [In] in Hr |- *; tauto.
  + rewrite Rk by (cbn; tauto). exact H27.
Qed.

End s.
End b.
