(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths, module names, addresses and numbers changed; 807 of its 943 lines of code are new or changed and 878 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the block lemmas of the
   head of the checking segment M03 of LLVMFuzzerTestOneInput (lib/AU/HPgSegM.v hqu_piece_M3a_head_stmt, from C5
   0x82f38 to X 0x82fdc / FIRST 0x838e4) up to the parse's return; lib/AU/HPgBM3aHead.v walks the rest and
   assembles the piece. Proves function LLVMFuzzerTestOneInput (this piece of its walk).

   THE CODE (C5 0x82f38 .. 0x82fd8; fuzz_headamp.c:330-338)
     0x82f38  beqz a0,0x83a08      out is not NULL: decided by a0's atom fact (out >= 4096)
     0x82f3c  s6 = out; a2 = s5 (3 cap + 3); s5 = R+0x48 (F); s10 = F + 0x2a0 (res); a1 = 0xa5;
     0x82f50  sd a2,0x150(s1); 0x82f54 jal __asan_memset (0x52228): out[0 .. 3 cap + 3) := 0xa5
     0x82f58  a0 = 4; 0x82f5c sb zero,0x54(s3); 0x82f60 sb a0,0x55(s3) (res's two granules into scope)
     0x82f64  a1 = 0x5a, a2 = 12, a0 = res; 0x82f70 jal __asan_memset: res[0 .. 12) := 0x5a
     0x82f74  a0 = neg(s7) & s9 (pod when the null flag is 0, else 0); 0x82f78 sd s9,0x158(s1);
     0x82f80  sd a0,0x140(s1); a1 = out, a2 = cap, a3 = res; 0x82f90 jal reac_headamp_prop_parse_result (0x849ac)
     0x82f94  not a1,s6; 0x82f98 bltu a1,s2 -> 0x83a14 (unimp): not taken, out + 3 cap < 2 ^ 64 (an assumed
              condition of the run, HPgSegM.hqu_t_ptr); s9 = rc; a0 = out + 3 cap; 0x82fa4 jal check_no_overrun
     0x82fa8  a0 = rc, a1 = cap, a2 = res; 0x82fb4 jal check_count (0x83f2c)
     0x82fb8  a0 = out, a1 = rc; 0x82fc0 jal check_cells_valid (0x83fcc)
     0x82fc4  srli / add / lb: the shadow byte of pp->corrupt (an instrumented 4-byte check, slow block 0x83a3c)
     0x82fd4  lw a0,0(s8) (pp->corrupt); 0x82fd8 bnez a0 -> FIRST 0x838e4; else X 0x82fdc.
   The walk is seven engine runs (lib/Reusable: st_ok, aj_run_to / aj_run_tok) cut at the six calls: the two
   memsets are the runtime's __asan_memset (YG0d.aintrin_realizes at any float state, the Section hypothesis
   AMEMSET, through lib/AU/HPgIntrinU.v hdu_memset_at), the parse is lib/A/HPgCSpec.v's hd_parse_result_specX
   (PARSE, at the read-only range 0 .. 0) and the three checks are its check texts at the parse's float state
   (CK_NO, CK_COUNT, CK_CV), each through lib/A/HPgCalls.v's adapters, with lib/AU/HPgSiteB.v's call-site lemmas
   for their premises. ERRNO (the errno cell lies in the image) puts errno apart from the heap blocks, ERRNO_RW (it
   lies in no read-only segment) keeps rom_view across the parse's errno write, and MTL (the meter's laws) chains
   the four callees' meter steps. Every byte the head writes lies in the out block, res and its two shadow
   granules, the real-frame cells R + 0x140, R + 0x150 and R + 0x158, the errno cell or the callees' stack
   [R - T_SEG_STK, R),
   all inside HPgSegM.hqu_E3 or the callees' stack. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgCalls HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgMem HPgSteps HPgIntrinU HPgSiteB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== the code table ============================== *)
(* the 41 words 0x82f38 .. 0x82fd8 and the three words 0x83a3c .. 0x83a44 of the slow block of the check at
   0x82fd0 (`andi`, `addi`, `blt` back to 0x82fd4); X 0x82fdc and FIRST 0x838e4 lie outside it *)
Definition MB_PC0 : Z := 0x82f38.
Definition MB_SLOW : Z := 0x83a3c.
Definition mb_tbl : ctable := build_table rsegs MB_SLOW 3 (build_table rsegs MB_PC0 41 TEmpty).
Lemma mb_tbl_ok : table_ok rsegs mb_tbl.
Proof. apply build_table_ok; [unfold MB_SLOW; lia|]. apply build_table_ok0. unfold MB_PC0. lia. Qed.
(* the return addresses of the six calls *)
Definition MB_A1 : Z := 0x82f58.
Definition MB_B1 : Z := 0x82f74.
Definition MB_C1 : Z := 0x82f94.
Definition MB_D1 : Z := 0x82fa8.
Definition MB_E1 : Z := 0x82fb8.
Definition MB_F1 : Z := 0x82fc4.
Definition MBCEIL : Z := 0x7fffff800000.
(* the shadow base of the last run: s11's own atom (x27); its one shadow entry is pp->corrupt's granule at s8 (x24) *)
Definition MBBx : sv := SOff 27 0.
Definition MBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition MBSH : list shent := [mkSHE 24 0 8].

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* a register named by Z_to_bv 5 n is the register named by the numeral n *)
Lemma mb_getr_z : forall (regs : bvmap 5 word) (r : bv 5) n, bv_unsigned r = n -> getr regs (Z_to_bv 5 n) = getr regs r.
Proof.
intros regs r n H. f_equal. apply bv_eq. subst n. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
pose proof (u5_range r). change (bv_modulus 5) with 32. lia.
Qed.

(* `neg a0,s7; and a0,a0,s9` with s7 = 1 - null: pod when the flag is 0, else NULL *)
Lemma mb_sel : forall nl pod, 0 <= nl <= 1 -> 0 <= pod < 2 ^ 64 ->
zcanon (Z.land (zcanon (zcanon 0 - (1 - nl))) pod) = if nl =? 0 then pod else 0.
Proof.
intros nl pod Hn Hp. destruct (Z.eqb_spec nl 0) as [->|Hne].
- change (zcanon (zcanon 0 - (1 - 0))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  unfold zcanon, M64. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
- assert (nl = 1) as -> by lia. change (zcanon (zcanon 0 - (1 - 1))) with 0. rewrite Z.land_0_l. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a register the run left as its own atom holds its value at the run's start *)
Lemma mb_reg_atom : forall (fx' : YK11.FPState) E ss ms (H : word -> bool) regs extra (r : bv 5),
@st_ok rsegs fx' E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs r.
Proof.
intros fx' E ss ms H regs extra r HS [HA _] Hr.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite HA by (pose proof (u5_range r); lia). apply ew_Ereg_reg.
Qed.
(* a register the run left as an atom of the entry env holds that atom's register *)
Lemma mb_reg_is : forall (fx' : YK11.FPState) E ss ms (H : word -> bool) regs extra (r r' : bv 5) n,
@st_ok rsegs fx' E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
sr_get (ss_regs ss) r = SOff n 0 -> Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs r'.
Proof.
intros fx' E ss ms H regs extra r r' n HS [HA _] Hr Hn.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite HA by (pose proof (u5_range r'); lia). apply ew_Ereg_nat. exact Hn.
Qed.
(* a region of the state after a run, read back *)
Lemma mb_region_nth : forall (fx' : YK11.FPState) (H : word -> bool) E ss ms i r,
@st_ok rsegs fx' E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
region_ok rsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros fx' H E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma mb_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
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
Lemma mb_aview_some : forall (H : word -> bool) (m : word -> option byte) a, apresent H m a -> aview rsegs H m a <> None.
Proof.
intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
(* a run left every byte outside its regions' write windows as it was *)
Lemma mb_frame_kept : forall E rs (H : word -> bool) (m m' : word -> option byte) (P : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall a, 0 <= a < 2 ^ 64 -> in_wrange E rs a -> P a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' P HF HP a Ha Hn. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. intros Hw. exact (Hn (HP a Ha Hw)).
Qed.

Section s.
Variable B : asyms.
Variable MT : ameter_ops.

(* ================= the start state at C5 (HPgSegM.hqu_start_M03), unfolded into the facts the walk uses ================= *)
Record mb_f (cx : hsu_scx rsegs) (r : Model.pod_rec) (ev : Z) : Prop := MBF {
f_pre : hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B);
f_J : ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) (x_k cx);
f_nev : st_nev (x_S cx) + x_k cx <= EV_MAX;
f_r2 : getr (x_regs cx) 2 = w64 (e_R (x_e cx));
f_r3 : getr (x_regs cx) 3 = w64 (as_gp B);
f_r4 : getr (x_regs cx) 4 = w64 (as_tp B);
f_S : e_S (x_e cx) = x_sp0 cx;
f_R32 : e_R (x_e cx) mod 32 = 0;
f_RS : e_R (x_e cx) + 0x220 <= e_S (x_e cx);
f_STK : x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK;
f_own : In (4, x_pos cx) (x_own cx);
f_F : e_F (x_e cx) = frame_addr (x_lyc cx) 4 (x_pos cx);
f_fsh : hd_fsh rsegs (w_H (x_W cx)) (x_memc cx) (e_F (x_e cx)) headamp_B_shA;
f_cap : 0 <= e_cap (x_e cx) <= 9;
f_null : 0 <= e_null (x_e cx) <= 1;
f_rom : rom_view rsegs (x_W cx) (x_memc cx);
f_ppf : hd_fresh_block (ablocks B (x_ly cx) (x_S cx)) (ablocks B (x_lyc cx) (x_Sc cx)) (e_pp (x_e cx)) Layout.PP_SIZE;
f_a10 : getr (x_regs cx) (Z_to_bv 5 10) = w64 (e_out (x_e cx));
f_s0 : getr (x_regs cx) (Z_to_bv 5 8) = w64 (e_S (x_e cx));
f_s1 : getr (x_regs cx) (Z_to_bv 5 9) = w64 (e_R (x_e cx));
f_s2 : getr (x_regs cx) (Z_to_bv 5 18) = w64 (3 * e_cap (x_e cx));
f_s3 : getr (x_regs cx) (Z_to_bv 5 19) = w64 (shadow_addr (e_F (x_e cx)));
f_s4 : getr (x_regs cx) (Z_to_bv 5 20) = w64 (e_cap (x_e cx));
f_s5 : getr (x_regs cx) (Z_to_bv 5 21) = w64 (3 * e_cap (x_e cx) + 3);
f_s7 : getr (x_regs cx) (Z_to_bv 5 23) = w64 (1 - e_null (x_e cx));
f_s8 : getr (x_regs cx) (Z_to_bv 5 24) = w64 (e_pp (x_e cx) + 0x4d18);
f_s9 : getr (x_regs cx) (Z_to_bv 5 25) = w64 (e_pod (x_e cx));
f_s11 : getr (x_regs cx) (Z_to_bv 5 27) = w64 SHADOW_OFF;
f_c8 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x8) 8
  ((e_pp (x_e cx) + 0x4008) mod 2 ^ 64);
f_c18 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x18) 8 ((e_F (x_e cx) + 0) mod 2 ^ 64);
f_c48 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x48) 8 ((e_F (x_e cx) + 0) mod 2 ^ 64);
f_ce0 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0xe0) 8
  (Z.shiftr (e_pp (x_e cx) + 0x4d14) 3 mod 2 ^ 64);
f_c108 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x108) 8 ((-16381) mod 2 ^ 64);
f_c120 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x120) 8
  ((e_pp (x_e cx) + 0x4d14) mod 2 ^ 64);
f_c148 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x148) 8 ((e_pp (x_e cx) + 0) mod 2 ^ 64);
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

Lemma mb_f_of : forall cx r ev, hqu_start_M03 rsegs B cx r ev -> mb_f cx r ev.
Proof.
intros cx r ev HS0.
destruct HS0 as (HP & HL & Hwf & Hlen & Hpp & Hpod & Hpodf & _ & _ & _ & _ & Houtf & _ & Hdj & Hrc & Hev & Hfrm).
pose proof HP as HP0.
destruct HP as (HJ & Hnev & H2 & H3 & H4 & HS & HR32 & HRS & HSTK & Hown & HF & Hfsh & Hcap & Hnull & _ & _ & _ & _ &
  _ & _ & Hrom & Hppf).
unfold hd_cut in HL. cbn [hi_L5 headamp_himg_B] in HL. unfold headamp_B_L45 in HL.
repeat rewrite Forall_cons_iff in HL.
destruct HL as (A10 & A8 & A9 & A18 & A19 & A20 & A21 & A23 & A24 & A25 & A27 & C8 & C18 & C48 & Ce0 & C108 & C120 &
  C148 & _).
cbn [fst snd hd_at hd_xv] in A10, A8, A9, A18, A19, A20, A21, A23, A24, A25, A27, C8, C18, C48, Ce0, C108, C120, C148.
cbn [hi_cid hi_rsz hi_shA headamp_himg_B] in *.
constructor; assumption.
Qed.

(* the bounds the walk uses, from C5's journal and the allocator's block and frame laws *)
Lemma mb_bounds : forall cx r ev, mb_f cx r ev ->
let e := x_e cx in
e_out e mod 16 = 0 /\ 4096 <= e_out e /\ e_out e + 3 * (e_cap e + 1) <= alloc_ceiling /\
in_app (e_out e) (3 * (e_cap e + 1)) /\
e_pod e mod 16 = 0 /\ 4096 <= e_pod e /\ e_pod e + e_len e <= alloc_ceiling /\ in_app (e_pod e) (e_len e) /\
8 <= e_len e /\
e_pp e mod 16 = 0 /\ 4096 <= e_pp e /\ e_pp e + 19744 <= alloc_ceiling /\ in_app (e_pp e) 19744 /\
e_F e mod 32 = 0 /\ 4096 <= e_F e /\ e_F e + 1024 <= alloc_ceiling /\ in_app (e_F e) 1024 /\
alloc_ceiling + T_SEG_STK <= e_R e /\ e_R e + 0x220 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\
x_sp0 cx - x_STK cx <= e_R e - T_SEG_STK /\ 0x7fff7f800000 <= alloc_ceiling <= MBCEIL.
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
unfold MBCEIL, T_SEG_STK, ASTACK in *. subst e. rewrite HS in HRS.
repeat (first [assumption | split]); lia.
Qed.

(* =================== Section hypotheses: the runtime's __asan_memset, at any float state =================== *)
Hypothesis AMEMSET : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs B OSet B_ASAN_MEMSET.

(* ===================== block A: C5 0x82f38 .. the first memset's return 0x82f58 ===================== *)
Definition mb_rA48 : YP09.region := YP09.mkRegion (Some 9%nat) 0x48 0x50 0 0 [YP09.mkChunk 0x48 (CVal 8 (SOff 32 0))].
Definition mb_rA150 : YP09.region := YP09.mkRegion (Some 9%nat) 0x150 0x158 0x150 0x158 [].

(* what C5 becomes after memset(out, 0xa5, 3 cap + 3): out holds the guard byte, R + 0x150 holds 3 cap + 3, s5 =
   F, s6 = out, s10 = res, the other callee-saved registers their C5 values, every byte outside out, R + 0x150 and
   the callee's stack [R - ESTACK, R) as at C5 *)
Definition mb_A_post (cx : hsu_scx rsegs) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) mem1 md1 (x_k cx) /\
same_io (x_mdc cx) md1 /\
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 27] ->
 getr regs1 (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)) /\
getr regs1 (Z_to_bv 5 21) = w64 (e_F (x_e cx)) /\
getr regs1 (Z_to_bv 5 22) = w64 (e_out (x_e cx)) /\
getr regs1 (Z_to_bv 5 26) = w64 (e_F (x_e cx) + 0x2a0) /\
val_mem rsegs (mrestrict (w_H (x_W cx)) mem1) (e_R (x_e cx) + 0x150) 8 ((3 * e_cap (x_e cx) + 3) mod 2 ^ 64) /\
(forall i, 0 <= i < 3 * e_cap (x_e cx) + 3 -> aview rsegs (w_H (x_W cx)) mem1 (e_out (x_e cx) + i) = Some 165) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_out (x_e cx) <= a < e_out (x_e cx) + 3 * e_cap (x_e cx) + 3) ->
 ~ (e_R (x_e cx) + 0x150 <= a < e_R (x_e cx) + 0x158) -> ~ (e_R (x_e cx) - ESTACK <= a < e_R (x_e cx)) ->
 aview rsegs (w_H (x_W cx)) mem1 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).

Lemma mb_A : forall cx r ev (Q : world rsegs -> config -> Prop),
mb_f cx r ev ->
(forall regs1 mem1 md1, mb_A_post cx regs1 mem1 md1 -> SRr rsegs (x_W cx) (cfg_at rsegs MB_A1 regs1 mem1 md1) Q) ->
SRr rsegs (x_W cx) (cfg_at rsegs (hi_c5 headamp_himg_B) (x_regs cx) (x_memc cx) (x_mdc cx)) Q.
Proof using AMEMSET.
intros cx r ev Q HC K.
pose proof (mb_bounds cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
destruct HC as [_ HJ Hnev H2 H3 H4 HeS HR32 _ _ Hown HeF Hfsh Hcap Hnull Hrom Hppf
  A10 A8 A9 A18 A19 A20 A21 A23 A24 A25 A27 C8 C18 C48 Ce0 C108 C120 C148
  Hwf Hlen Hpp Hpod Hpodf Houtf Hdj Hrc Hev Hfrm].
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
set (out := e_out e) in *. set (cap := e_cap e) in *. set (R := e_R e) in *. set (F := e_F e) in *.
unfold MBCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
set (E := Ereg regs [w64 F]).
assert (E9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl), A9. unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (HS : st_ok rsegs E (mkSS 0x82f38 sr_atoms [mb_rA48; mb_rA150] None
  (mkFacts [(10%nat, mkAF 4096 MBCEIL 4)] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82f38) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold mb_rA48. apply (hm_ro_region rsegs E (w_H W) memc 9 R 0x48 0x50 _ E9); [lia | lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ R 0x48 8 (SOff 32 0) F).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
      * cbn. lia.
      * cbn. lia.
      * rewrite Z.add_0_r, Z.mod_small in C48 by lia. exact C48.
    + unfold mb_rA150. apply (hm_rw_region rsegs E (w_H W) memc 9 R 0x150 0x158 0x150 0x158 [] E9);
        [lia | lia | | apply Forall_nil].
      intros o Ho. apply Hstkp. lia.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, mb_rA48, mb_rA150.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite E9. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    subst E. rewrite (ew_Ereg_nat regs _ 10 (Z_to_bv 5 10) eq_refl), A10. unfold w64.
    rewrite unsigned_lit_small by (unfold MBCEIL; lia). change (2 ^ 4) with 16. unfold MBCEIL. lia. }
unfold cfg_at. cbn [hi_c5 headamp_himg_B]. change (w64 0x82f38) with (Z_to_bv 64 0x82f38).
aj_run_to mb_tbl_ok HS HJ 0x52228.
{ apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact E9 | | apply awr_ok_nil].
  intros a Ha. cbn [mb_rA150 YP09.r_wlo YP09.r_whi] in Ha. left. lia. }
assert (HAE : env_agree 32 (Ereg regs [w64 F]) E) by (subst E; apply env_agree_refl).
rreg HS (Z_to_bv 5 1) Ra1. rreg HS (Z_to_bv 5 11) Ra11.
assert (Ra10 : getr (ms_regs ms) (Z_to_bv 5 10) = getr regs (Z_to_bv 5 10))
  by (eapply (mb_reg_is _ _ _ ms (w_H W) regs _ _ _ 10 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Ra12 : getr (ms_regs ms) (Z_to_bv 5 12) = getr regs (Z_to_bv 5 21))
  by (eapply (mb_reg_is _ _ _ ms (w_H W) regs _ _ _ 21 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Ra22 : getr (ms_regs ms) (Z_to_bv 5 22) = getr regs (Z_to_bv 5 10))
  by (eapply (mb_reg_is _ _ _ ms (w_H W) regs _ _ _ 10 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Ra21 : getr (ms_regs ms) (Z_to_bv 5 21) = w64 F).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 21)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 21)) with v end.
  cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
assert (Ra26 : getr (ms_regs ms) (Z_to_bv 5 26) = w64 (F + 0x2a0)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 26)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 26)) with v end.
  cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. }
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r0 Hr. eapply (mb_reg_atom _ _ _ ms (w_H W) regs _ (Z_to_bv 5 r0) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
(* R + 0x150 after the store *)
assert (H150 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x150) 8 ((3 * cap + 3) mod 2 ^ 64)).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ss) 1) in
    lazymatch rr with Some ?rg =>
      assert (Hr : nth_error (ss_mem ss) 1 = Some rg) by (vm_compute; reflexivity);
      pose proof (mb_region_nth _ _ _ _ _ 1 _ HS Hr) as Hreg end end.
  rewrite Z.mod_small by lia.
  exact (mb_field _ _ _ _ _ _ _ _ _ 0x150 8 (SOff 21 0) (3 * cap + 3) Hreg E9 ltac:(cbn; tauto)
    ltac:(cbn [sv_denot]; subst E; rewrite (ew_Ereg_nat regs _ 21 (Z_to_bv 5 21) eq_refl), A21; unfold w64;
          rewrite unsigned_lit_small by lia; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x150 <= a < R + 0x158) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ apply (mb_frame_kept _ _ _ _ _ _ HFr). intros a Ha Hw.
  destruct Hw as (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[<-|[]]];
  cbn [mb_rA48 mb_rA150 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite E9 in Hr; lia. }
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
assert (HAR : AR rsegs B lyc Sc W (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc)) by exact (proj1 HJ).
assert (E2 : getr (ms_regs ms) (2%bv : bv 5) = getr regs (2%bv : bv 5))
  by (eapply (mb_reg_atom _ _ _ ms (w_H W) regs _ _ HS HAE); vm_compute; reflexivity).
assert (E3 : getr (ms_regs ms) (3%bv : bv 5) = getr regs (3%bv : bv 5))
  by (eapply (mb_reg_atom _ _ _ ms (w_H W) regs _ _ HS HAE); vm_compute; reflexivity).
assert (E4 : getr (ms_regs ms) (4%bv : bv 5) = getr regs (4%bv : bv 5))
  by (eapply (mb_reg_atom _ _ _ ms (w_H W) regs _ _ HS HAE); vm_compute; reflexivity).
assert (Hsp : spZ (ms_regs ms) = sp0 + (R - sp0)).
{ unfold spZ. rewrite E2, H2. unfold w64. rewrite unsigned_lit_small; [ring | lia]. }
destruct Houtf as (Hout0 & Hoin & Honew).
assert (Hrqo : req_size (3 * (cap + 1)) = 3 * (cap + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (cap + 1)) 0); lia).
destruct (hm_blk_ra rsegs B lyc Sc W (ms_mem ms) _ out (3 * (cap + 1)) out (3 * cap + 3) HAR Hoin ltac:(lia)
  ltac:(rewrite Hrqo; lia)) as (Hrao & Hhullo).
assert (HR16 : R mod 16 = 0)
  by (rewrite <- (Z.mod_mod_divide R 32 16) by (exists 2; reflexivity); rewrite HR32; reflexivity).
eapply SRr_bind.
{ eapply (hdu_memset_at B (AMEMSET fx) W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    out 165 (3 * cap + 3) (R - sp0) (Z_to_bv 64 MB_A1) HJ).
  - rewrite <- (mb_getr_z (ms_regs ms) 10 10 eq_refl), Ra10. exact A10.
  - rewrite <- (mb_getr_z (ms_regs ms) 11 11 eq_refl), Ra11. reflexivity.
  - rewrite <- (mb_getr_z (ms_regs ms) 12 12 eq_refl), Ra12. exact A21.
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite E3. exact H3.
  - rewrite E4. exact H4.
  - rewrite <- (mb_getr_z (ms_regs ms) 1 1 eq_refl). exact Ra1.
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
apply K. unfold mb_A_post.
cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_k x_regs x_lyc x_Sc x_W x_memc x_mdc x_e].
fold out cap R F.
split; [exact HJ2|].
split; [eapply same_io_trans; [apply same_io_wvb | exact Hio2]|].
split.
{ intros r0 Hr. rewrite (Hpres2 r0) by (cbn [In] in Hr; unfold acallee_saved; lia). apply Rk. exact Hr. }
split.
{ rewrite (Hpres2 21) by (unfold acallee_saved; lia). exact Ra21. }
split.
{ rewrite (Hpres2 22) by (unfold acallee_saved; lia). rewrite Ra22. exact A10. }
split.
{ rewrite (Hpres2 26) by (unfold acallee_saved; lia). exact Ra26. }
split.
{ eapply (hd_val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms) mem2); [|exact H150].
  intros i Hi. apply Hkeep; [lia | lia | unfold ESTACK; lia]. }
split.
{ intros i Hi. rewrite (Hset i Hi). reflexivity. }
intros a Ha Ho H1 Hs. rewrite Hkeep; [| exact Ha | lia | replace (sp0 + (R - sp0)) with R by ring; exact Hs].
apply KA; [exact Ha | exact H1].
Qed.

(* ===================== block B: 0x82f58 .. the second memset's return 0x82f74 ===================== *)
(* outside res's two granules headamp_B_shB is headamp_B_shA *)
Lemma mb_shB_nth : forall i, (i < 116)%nat -> i <> 84%nat -> i <> 85%nat ->
nth i headamp_B_shB 0 = nth i headamp_B_shA 0.
Proof.
intros i Hi H84 H85.
assert (E : forallb (fun j => (j =? 84)%nat || (j =? 85)%nat || Z.eqb (nth j headamp_B_shB 0) (nth j headamp_B_shA 0))
  (seq 0 116) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in E. specialize (E i ltac:(apply in_seq; lia)).
apply orb_prop in E as [E|E]; [apply orb_prop in E as [E|E]; apply Nat.eqb_eq in E; lia|].
apply Z.eqb_eq. exact E.
Qed.

(* res's 12 bytes have their shadow hull inside the frame's 128 shadow bytes *)
Lemma mb_res_hull : forall (H : word -> bool) (m : word -> option byte) F, F = 8 * (F / 8) ->
(forall i, 0 <= i < 128 -> aview rsegs H m (shadow_addr F + i) <> None) ->
shadow_hull_vis (aview rsegs H m) (F + 0x2a0) 12.
Proof.
intros H m F F8 Hp s Hs. unfold shadow_addr in *. set (q := F / 8) in *.
replace (F + 0x2a0) with ((q + 84) * 8) in Hs by lia.
replace ((q + 84) * 8 + 12 - 1) with ((q + 85) * 8 + 3) in Hs by lia.
rewrite Z.div_mul in Hs by lia. rewrite Z.div_add_l in Hs by lia. change (3 / 8) with 0 in Hs.
pose proof (Z.div_mod (SHADOW_OFF + (q + 84)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (q + 84)) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (q + 85 + 0)) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (q + 85 + 0)) 8 ltac:(lia)) as M2.
replace s with (SHADOW_OFF + q + (s - (SHADOW_OFF + q))) by lia.
apply Hp. lia.
Qed.

Definition mb_B_post (cx : hsu_scx rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) mem2 md2 (x_k cx) /\
same_io (x_mdc cx) md2 /\
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 27] ->
 getr regs2 (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)) /\
getr regs2 (Z_to_bv 5 21) = w64 (e_F (x_e cx)) /\
getr regs2 (Z_to_bv 5 22) = w64 (e_out (x_e cx)) /\
getr regs2 (Z_to_bv 5 26) = w64 (e_F (x_e cx) + 0x2a0) /\
val_mem rsegs (mrestrict (w_H (x_W cx)) mem2) (e_R (x_e cx) + 0x150) 8 ((3 * e_cap (x_e cx) + 3) mod 2 ^ 64) /\
(forall i, 0 <= i < 3 * e_cap (x_e cx) + 3 -> aview rsegs (w_H (x_W cx)) mem2 (e_out (x_e cx) + i) = Some 165) /\
hd_fsh rsegs (w_H (x_W cx)) mem2 (e_F (x_e cx)) headamp_B_shB /\
(forall i, 0 <= i < 12 -> aview rsegs (w_H (x_W cx)) mem2 (e_F (x_e cx) + 0x2a0 + i) = Some 90) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_out (x_e cx) <= a < e_out (x_e cx) + 3 * e_cap (x_e cx) + 3) ->
 ~ (e_R (x_e cx) + 0x150 <= a < e_R (x_e cx) + 0x158) ->
 ~ (shadow_addr (e_F (x_e cx)) + 84 <= a < shadow_addr (e_F (x_e cx)) + 86) ->
 ~ (e_F (x_e cx) + 0x2a0 <= a < e_F (x_e cx) + 0x2ac) -> ~ (e_R (x_e cx) - ESTACK <= a < e_R (x_e cx)) ->
 aview rsegs (w_H (x_W cx)) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).

Lemma mb_B : forall cx r ev regs1 mem1 md1 (Q : world rsegs -> config -> Prop),
mb_f cx r ev -> mb_A_post cx regs1 mem1 md1 ->
(forall regs2 mem2 md2, mb_B_post cx regs2 mem2 md2 -> SRr rsegs (x_W cx) (cfg_at rsegs MB_B1 regs2 mem2 md2) Q) ->
SRr rsegs (x_W cx) (cfg_at rsegs MB_A1 regs1 mem1 md1) Q.
Proof using AMEMSET.
intros cx r ev regs1 mem1 md1 Q HC HA K.
pose proof (mb_bounds cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
destruct HA as (HJ & Hio1 & Rk1 & R21 & R22 & R26 & H150 & Hout & KA).
destruct HC as [_ _ Hnev H2 H3 H4 HeS HR32 _ _ Hown HeF Hfsh Hcap Hnull Hrom Hppf
  A10 A8 A9 A18 A19 A20 A21 A23 A24 A25 A27 C8 C18 C48 Ce0 C108 C120 C148
  Hwf Hlen Hpp Hpod Hpodf Houtf Hdj Hrc Hev Hfrm].
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
set (out := e_out e) in *. set (cap := e_cap e) in *. set (R := e_R e) in *. set (F := e_F e) in *.
unfold MBCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
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
assert (HS : st_ok rsegs (Ereg regs1 []) (fsh_ss 0x82f58 84 86)
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 0x82f58) mem1 (seg_rom rsegs)))).
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
unfold cfg_at, MB_A1. change (w64 0x82f58) with (Z_to_bv 64 0x82f58).
aj_run_to mb_tbl_ok HS HJ 0x52228.
{ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat 4 pos);
  [ reflexivity | rewrite E19u, HeF; reflexivity | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; change (fs_frame_bytes 4 / 8) with 128; lia
  | apply awr_ok_nil ]. }
assert (HAE : env_agree 32 (Ereg regs1 []) (Ereg regs1 [])) by apply env_agree_refl.
rreg HS (Z_to_bv 5 1) Ra1. rreg HS (Z_to_bv 5 11) Ra11. rreg HS (Z_to_bv 5 12) Ra12.
assert (Ra10 : getr (ms_regs ms) (Z_to_bv 5 10) = getr regs1 (Z_to_bv 5 26))
  by (eapply (mb_reg_is _ _ _ ms (w_H W) regs1 [] _ _ 26 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r0 Hr. eapply (mb_reg_atom _ _ _ ms (w_H W) regs1 [] (Z_to_bv 5 r0) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
(* the two shadow bytes after the stores *)
assert (Hs84 : aview rsegs (w_H W) (ms_mem ms) (shadow_addr F + 84) = Some 0 /\
  aview rsegs (w_H W) (ms_mem ms) (shadow_addr F + 85) = Some 4).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch rr with Some ?rg =>
      assert (Hr : nth_error (ss_mem ss) 0 = Some rg) by (vm_compute; reflexivity);
      pose proof (mb_region_nth _ _ _ _ _ 0 _ HS Hr) as Hreg end end.
  destruct Hreg as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19u in Hch.
  unfold aview. split.
  + apply (fsh_byte_of_region _ _ _ _ _ 0 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia].
  + apply (fsh_byte_of_region _ _ _ _ _ 4 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia]. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 84 <= a < shadow_addr F + 86) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem1 a).
{ apply (mb_frame_kept _ _ _ _ _ _ HFr). intros a Ha Hw.
  destruct Hw as (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [fsh_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E19u in Hr. exact Hr. }
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
assert (HAR : AR rsegs B lyc Sc W (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1)) by exact (proj1 HJ).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (_ & _ & HFb & HFsh).
rewrite <- HeF in HFsh, HFb. change (fs_frame_bytes 4 / 8) with 128 in HFsh. change (fs_frame_bytes 4) with 1024 in HFb.
(* the frame's shadow at the call: the prologue's with res's two granules in scope *)
assert (Hfsh1 : hd_fsh rsegs (w_H W) mem1 F headamp_B_shA).
{ apply (hm_fsh_kept rsegs (w_H W) memc (w_H W) mem1 F headamp_B_shA Hfsh).
  intros i Hi. change (length headamp_B_shA) with 116%nat in Hi. change (Z.of_nat 116) with 116 in Hi.
  apply KA; [unfold shadow_addr, SHADOW_OFF; lia | | | unfold ESTACK; unfold shadow_addr, SHADOW_OFF; lia].
  - intros Ho. apply (Happ (shadow_addr F + i)); [left; exact Ho | lia].
  - unfold shadow_addr, SHADOW_OFF. lia. }
assert (HfshP : hd_fsh rsegs (w_H W) (ms_mem ms) F headamp_B_shB).
{ intros i Hi. change (length headamp_B_shB) with 116%nat in Hi. change (Z.of_nat 116) with 116 in Hi.
  destruct (Z.eq_dec i 84) as [->|H84]; [rewrite (proj1 Hs84); reflexivity|].
  destruct (Z.eq_dec i 85) as [->|H85]; [rewrite (proj2 Hs84); reflexivity|].
  rewrite KB by (unfold shadow_addr, SHADOW_OFF; lia).
  rewrite (Hfsh1 i) by (change (length headamp_B_shA) with 116%nat; lia).
  rewrite mb_shB_nth by lia. reflexivity. }
pose proof headamp_B_sh_len as (_ & Bl).
pose proof headamp_B_shB_res as (B84 & B85 & _).
assert (E2 : getr (ms_regs ms) (2%bv : bv 5) = getr regs1 (2%bv : bv 5))
  by (eapply (mb_reg_atom _ _ _ ms (w_H W) regs1 [] _ HS HAE); vm_compute; reflexivity).
assert (E3 : getr (ms_regs ms) (3%bv : bv 5) = getr regs1 (3%bv : bv 5))
  by (eapply (mb_reg_atom _ _ _ ms (w_H W) regs1 [] _ HS HAE); vm_compute; reflexivity).
assert (E4 : getr (ms_regs ms) (4%bv : bv 5) = getr regs1 (4%bv : bv 5))
  by (eapply (mb_reg_atom _ _ _ ms (w_H W) regs1 [] _ HS HAE); vm_compute; reflexivity).
assert (Hsp : spZ (ms_regs ms) = sp0 + (R - sp0)).
{ unfold spZ. rewrite E2. rewrite <- (mb_getr_z regs1 2 2 eq_refl), (Rk1 2 ltac:(cbn; tauto)),
    (mb_getr_z regs 2 2 eq_refl), H2.
  unfold w64. rewrite unsigned_lit_small; [ring | lia]. }
assert (HR16 : R mod 16 = 0)
  by (rewrite <- (Z.mod_mod_divide R 32 16) by (exists 2; reflexivity); rewrite HR32; reflexivity).
eapply SRr_bind.
{ eapply (hdu_memset_at B (AMEMSET fx) W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    (F + 0x2a0) 90 12 (R - sp0) (Z_to_bv 64 MB_B1) HJ).
  - rewrite <- (mb_getr_z (ms_regs ms) 10 10 eq_refl), Ra10. exact R26.
  - rewrite <- (mb_getr_z (ms_regs ms) 11 11 eq_refl), Ra11. reflexivity.
  - rewrite <- (mb_getr_z (ms_regs ms) 12 12 eq_refl), Ra12. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite E3, <- (mb_getr_z regs1 3 3 eq_refl), (Rk1 3 ltac:(cbn; tauto)), (mb_getr_z regs 3 3 eq_refl). exact H3.
  - rewrite E4, <- (mb_getr_z regs1 4 4 eq_refl), (Rk1 4 ltac:(cbn; tauto)), (mb_getr_z regs 4 4 eq_refl). exact H4.
  - rewrite <- (mb_getr_z (ms_regs ms) 1 1 eq_refl). exact Ra1.
  - vm_compute. reflexivity.
  - intros a Ha. split.
    + right. right. right. exists 4, pos. split; [exact Hown|]. left. unfold in_zr. cbn [fst snd].
      rewrite <- HeF. change (fs_frame_bytes 4) with 1024. lia.
    + unfold ESTACK. lia.
  - unfold in_app, amem_range, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia.
  - apply (hd_res_addressableB rsegs (w_H W) (ms_mem ms) F headamp_B_shB HfshP F8m Bl B84 B85); lia.
  - intros _. apply (mb_res_hull (w_H W) (ms_mem ms) F F8). intros i Hi. apply mb_aview_some. exact (proj1 (HFsh i Hi)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & Hpres2 & Ha02 & Hset & Hkeep & Hgrow).
replace (sp0 + (R - sp0)) with R in Hkeep by ring.
apply K. unfold mb_B_post.
cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_k x_regs x_lyc x_Sc x_W x_memc x_mdc x_e].
fold out cap R F.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x2a0 <= a < F + 0x2a0 + 12) -> ~ (R - ESTACK <= a < R) ->
  ~ (shadow_addr F + 84 <= a < shadow_addr F + 86) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) mem1 a).
{ intros a Ha H1 H2' H3'. rewrite Hkeep; [| exact Ha | exact H1 | exact H2']. apply KB; [exact Ha | exact H3']. }
split; [exact HJ2|].
split; [eapply same_io_trans; [exact Hio1|]; eapply same_io_trans; [apply same_io_wvb | exact Hio2]|].
split.
{ intros r0 Hr. rewrite (Hpres2 r0) by (cbn [In] in Hr; unfold acallee_saved; lia).
  rewrite Rk by (cbn [In] in Hr |- *; tauto). apply Rk1. exact Hr. }
split.
{ rewrite (Hpres2 21) by (unfold acallee_saved; lia). rewrite Rk by (cbn; tauto). exact R21. }
split.
{ rewrite (Hpres2 22) by (unfold acallee_saved; lia). rewrite Rk by (cbn; tauto). exact R22. }
split.
{ rewrite (Hpres2 26) by (unfold acallee_saved; lia). rewrite Rk by (cbn; tauto). exact R26. }
split.
{ eapply (hd_val_mem_kept rsegs (w_H W) (w_H W) mem1 mem2); [|exact H150].
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
{ apply (hm_fsh_kept rsegs (w_H W) (ms_mem ms) (w_H W) mem2 F headamp_B_shB HfshP).
  intros i Hi. rewrite Bl in Hi. change (Z.of_nat 116) with 116 in Hi.
  apply Hkeep; [unfold shadow_addr, SHADOW_OFF; lia | | unfold ESTACK; unfold shadow_addr, SHADOW_OFF; lia].
  intros Hr. apply (Happ (F + 0x2a0 + (shadow_addr F + i - (F + 0x2a0)))); [right; lia | lia]. }
split.
{ intros i Hi. rewrite (Hset i Hi). reflexivity. }
intros a Ha Ho H1 Hsh Hres Hs. rewrite KM; [| exact Ha | lia | exact Hs | exact Hsh].
apply KA; [exact Ha | exact Ho | exact H1 | exact Hs].
Qed.

(* ===================== what the head writes, and the state after the parse ===================== *)
(* the bytes the head writes, besides the callees' stack: the out block, the real-frame cells R + 0x140, R + 0x150
   and R + 0x158,
   res's two shadow granules, res and the errno cell (each inside HPgSegM.hqu_E3) *)
Definition mb_Z (e : hd_env) (a : Z) : Prop :=
(e_out e <= a < e_out e + 3 * (e_cap e + 1)) \/
((e_R e + 0x140 <= a < e_R e + 0x148) \/ (e_R e + 0x150 <= a < e_R e + 0x160)) \/
(shadow_addr (e_F e) + 84 <= a < shadow_addr (e_F e) + 86) \/ (e_F e + 0x2a0 <= a < e_F e + 0x2ac) \/
(as_errno B <= a < as_errno B + 4).
(* the parse's answer *)
Definition mb_ans (cx : hsu_scx rsegs) (r : Model.pod_rec) : answer :=
Headamp.parse_props (hd_props (e_null (x_e cx)) (Model.buf r)) (e_cap (x_e cx)).

(* the state from the parse's return to the corrupt test: the harness's journal, the twelve callee-saved values
   (s9 = v9: the pod before 0x82f9c, rc after it), every byte outside the callees' stack and mb_Z as at C5, the
   three real-frame cells written so far, the frame's shadow with res in scope, out's guard cell, the parse's
   cells and res, and the errno cell readable. No float state: the run's own is named by the cut it reaches. *)
Definition mb_mid (cx : hsu_scx rsegs) (r : Model.pod_rec) (v9 : Z) ly2 S2 (W2 : world rsegs)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
hc_core rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  (x_k cx) ly2 S2 W2 mem2 md2 regs2 (e_R (x_e cx)) /\
frames S2 = frames (x_Sc cx) /\ Permutation (ablocks B ly2 S2) (ablocks B (x_lyc cx) (x_Sc cx)) /\
same_io (x_mdc cx) md2 /\ mo_le MT (x_Sc cx) S2 0 /\
getr regs2 (Z_to_bv 5 8) = w64 (e_S (x_e cx)) /\
getr regs2 (Z_to_bv 5 9) = w64 (e_R (x_e cx)) /\
getr regs2 (Z_to_bv 5 18) = w64 (3 * e_cap (x_e cx)) /\
getr regs2 (Z_to_bv 5 19) = w64 (shadow_addr (e_F (x_e cx))) /\
getr regs2 (Z_to_bv 5 20) = w64 (e_cap (x_e cx)) /\
getr regs2 (Z_to_bv 5 21) = w64 (e_F (x_e cx)) /\
getr regs2 (Z_to_bv 5 22) = w64 (e_out (x_e cx)) /\
getr regs2 (Z_to_bv 5 23) = w64 (1 - e_null (x_e cx)) /\
getr regs2 (Z_to_bv 5 24) = w64 (e_pp (x_e cx) + 0x4d18) /\
getr regs2 (Z_to_bv 5 25) = w64 v9 /\
getr regs2 (Z_to_bv 5 26) = w64 (e_F (x_e cx) + 0x2a0) /\
getr regs2 (Z_to_bv 5 27) = w64 SHADOW_OFF /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) -> ~ mb_Z (x_e cx) a ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x140) 8 (hd_xv (x_e cx) XProps mod 2 ^ 64) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x150) 8 ((3 * e_cap (x_e cx) + 3) mod 2 ^ 64) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x158) 8 (e_pod (x_e cx) mod 2 ^ 64) /\
hd_fsh rsegs (w_H W2) mem2 (e_F (x_e cx)) headamp_B_shB /\
garr8 rsegs (mrestrict (w_H W2) mem2) (e_out (x_e cx) + 3 * e_cap (x_e cx)) (hd_zbytes (repeat GUARD_BYTE 3)) /\
garr8 rsegs (mrestrict (w_H W2) mem2) (e_out (x_e cx)) (hd_zbytes (ha_cells_bytes (ans_cells (mb_ans cx r)))) /\
garr8 rsegs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0x2a0) (hd_zbytes (ans_res_bytes (mb_ans cx r))) /\
(exists ev', rd32 (aview rsegs (w_H W2) mem2) (as_errno B) ev').

(* a range of image B's third write list *)
Lemma mb_inw : forall e a,
(e_F e + 0x2a0 <= a < e_F e + 0x348) \/ (shadow_addr (e_F e) + 0x54 <= a < shadow_addr (e_F e) + 0x69) \/
(e_R e <= a < e_R e + 0x160) -> hd_inw e (hi_w3 headamp_himg_B) a.
Proof.
intros e a H. unfold hd_inw. cbn [hi_w3 headamp_himg_B].
destruct H as [H|[H|H]];
  [apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd];
  cbn [hd_xv fst snd]; lia.
Qed.

(* the parse writes at most cap cells *)
Lemma mb_cells_le : forall props cap, 0 <= cap <= 9 ->
Z.of_nat (length (ans_cells (Headamp.parse_props props cap))) <= cap.
Proof.
intros props cap Hcap.
pose proof (Headamp.parse_props_total props cap ltac:(lia)) as Hok.
apply answer_ok_parts in Hok as (Hcase & _).
destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia].
Qed.

(* the blocks and the frame for locals of C5, apart; the errno cell in the image, the blocks not *)
Lemma mb_seps : forall cx r ev, api_env rsegs B -> mb_f cx r ev ->
let e := x_e cx in
(e_out e + 3 * (e_cap e + 1) <= e_F e \/ e_F e + 1024 <= e_out e) /\
(e_pp e + 19744 <= e_F e \/ e_F e + 1024 <= e_pp e) /\
(e_pod e + e_len e <= e_F e \/ e_F e + 1024 <= e_pod e) /\
(e_pp e + 19744 <= e_out e \/ e_out e + 3 * (e_cap e + 1) <= e_pp e) /\
(forall a, e_out e <= a < e_out e + 3 * (e_cap e + 1) -> ~ in_img rsegs a) /\
(forall a, e_pp e <= a < e_pp e + 19744 -> ~ in_img rsegs a) /\
(forall a, e_pod e <= a < e_pod e + e_len e -> ~ in_img rsegs a) /\
(forall a, e_F e <= a < e_F e + 1024 -> ~ in_img rsegs a) /\
0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd /\
(forall a, as_errno B <= a < as_errno B + 4 -> in_img rsegs a).
Proof.
intros cx r ev HAPI HC. cbv zeta. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (mb_bounds cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (f_J cx r ev HC) as HJ. pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
destruct (f_outf cx r ev HC) as (_ & Hoin & _).
destruct (f_podf cx r ev HC) as (_ & Hpin & _).
destruct (f_ppf cx r ev HC) as (_ & Hppin & _).
assert (Hfin : In (4, x_pos cx) (frames (x_Sc cx)))
  by (rewrite Hfrs; apply in_or_app; left; exact (f_own cx r ev HC)).
pose proof (f_F cx r ev HC) as HeF. pose proof (f_cap cx r ev HC) as Hcap.
clear HC. destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
assert (Hrqo : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
assert (Hrqp : req_size (e_len e) = e_len e) by (unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia).
assert (Hrqq : req_size Layout.PP_SIZE = 19744) by reflexivity.
pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hoin Hfin) as Z1.
pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hppin Hfin) as Z2.
pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hpin Hfin) as Z3.
assert (Hne : (e_pp e, Layout.PP_SIZE) <> (e_out e, 3 * (e_cap e + 1))).
{ intros Heq. injection Heq as _ Hl. unfold Layout.PP_SIZE in Hl. lia. }
pose proof (sep_blocks rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hppin Hoin Hne) as Z4.
unfold zdisjoint in Z1, Z2, Z3, Z4. cbn [fst snd] in Z1, Z2, Z3, Z4.
rewrite <- HeF in Z1, Z2, Z3. change (fs_frame_bytes 4) with 1024 in Z1, Z2, Z3.
rewrite Hrqo in Z1, Z4. rewrite Hrqp in Z3. rewrite Hrqq in Z2, Z4.
destruct HAPI as ((Ee0 & Ee4) & Eimg & _).
split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|].
split; [intros a Ha; apply (hd_block_not_img rsegs B _ _ _ _ _ _ _ a HAR Hoin); rewrite Hrqo; exact Ha|].
split; [intros a Ha; apply (hd_block_not_img rsegs B _ _ _ _ _ _ _ a HAR Hppin); rewrite Hrqq; exact Ha|].
split; [intros a Ha; apply (hd_block_not_img rsegs B _ _ _ _ _ _ _ a HAR Hpin); rewrite Hrqp; exact Ha|].
split.
{ intros a Ha. refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR _)).
  right. left. exists 4, pos. split; [exact Hfin|]. rewrite <- HeF. change (fs_frame_bytes 4) with 1024. exact Ha. }
split; [exact Ee0|]. split; [exact Ee4 | exact Eimg].
Qed.

(* hd_seg_pre at the read-only range 0 .. 0: the parse is called with it (its relro hypothesis is then empty) *)
Lemma mb_pre00 : forall cx, hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) ->
hd_seg_pre rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  (x_k cx) (x_regs cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) headamp_himg_B (hi_shA headamp_himg_B)
  0 0 (x_e cx) (x_pos cx).
Proof.
intros cx HP.
destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & Haro & H16 & H17 & H18 &
  H19 & H20 & H21 & H22).
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
  (conj H13 (conj H14 (conj _ (conj H16 (conj H17 (conj H18 (conj H19 (conj H20 (conj H21 H22))))))))))))))))))))).
intros a Hro Ho He. apply Haro; [|exact Ho | exact He].
destruct Hro as [Hr|Hr]; [left; exact Hr | lia].
Qed.

(* =================== Section hypotheses of the parse =================== *)
Hypothesis MTL : ameter_laws MT.
(* the parse's contract at image B's entry, at the extra read-only range 0 .. 0 (every read-only segment is still
   in hd_parse_args' arodata_okP; the walk derives hd_seg_pre at 0 .. 0 from the segment's own, mb_pre00) *)
Hypothesis PARSE : hd_parse_result_specX rsegs B MT 0x849ac 0 0 0x214a0 0x214c0 0x214e0 0x21500
  0x9d478 0x5f8210 headamp_B_dcs.
Hypothesis ERRNO : api_env rsegs B.

(* ===================== block C: 0x82f74 .. the parse's return 0x82f94 ===================== *)
Definition mb_rC1 : YP09.region := YP09.mkRegion (Some 9%nat) 0x140 0x148 0x140 0x148 [].
Definition mb_rC2 : YP09.region := YP09.mkRegion (Some 9%nat) 0x158 0x160 0x158 0x160 [].

Lemma mb_C : forall cx r ev regs2 mem2 md2 (Q : world rsegs -> config -> Prop),
mb_f cx r ev -> mb_B_post cx regs2 mem2 md2 ->
(forall (fx2 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3, hd_fxk [14; 15] fx fx2 ->
 mb_mid cx r (e_pod (x_e cx)) ly3 S3 W3 regs3 mem3 md3 -> getr regs3 (Z_to_bv 5 10) = w64 (e_rc (x_e cx)) ->
 SRr rsegs W3 (@cfg_at fx2 rsegs MB_C1 regs3 mem3 md3) Q) ->
SRr rsegs (x_W cx) (cfg_at rsegs MB_B1 regs2 mem2 md2) Q.
Proof using PARSE ERRNO.
intros cx r ev regs2 mem2 md2 Q HC HB K.
pose proof (mb_bounds cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (mb_seps cx r ev ERRNO HC) as (Z1 & Z2 & Z3 & Z4 & NIo & NIp & NIq & NIf & Ee0 & Ee4 & Eimg).
pose proof (mb_pre00 cx (f_pre cx r ev HC)) as HP00.
destruct HB as (HJ & Hio2 & Rk2 & R21 & R22 & R26 & H150 & Hout & Hfsh2 & Hres & KB).
destruct HC as [_ _ Hnev H2 H3 H4 HeS HR32 _ _ Hown HeF Hfsh Hcap Hnull Hrom Hppf
  A10 A8 A9 A18 A19 A20 A21 A23 A24 A25 A27 C8 C18 C48 Ce0 C108 C120 C148
  Hwf Hlen Hpp Hpod Hpodf Houtf Hdj Hrc Hev Hfrm].
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
unfold mb_ans. cbn [x_e].
set (out := e_out e) in *. set (cap := e_cap e) in *. set (R := e_R e) in *. set (F := e_F e) in *.
set (pod := e_pod e) in *. set (nl := e_null e) in *.
unfold MBCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
unfold kLowMemEnd in Ee4.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
assert (Hfq : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (F8 : F = 8 * (F / 8)).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as D.
  assert (F mod 8 = 0) by (rewrite <- (Z.mod_mod_divide F 32 8) by (exists 4; reflexivity); rewrite Fm32; reflexivity).
  lia. }
set (E := Ereg regs2 []).
assert (E9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), (Rk2 9 ltac:(cbn; tauto)), A9.
  unfold w64. apply unsigned_lit_small. lia. }
assert (E23 : ew E 23 = Z_to_bv 64 (1 - nl))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl), (Rk2 23 ltac:(cbn; tauto)); exact A23).
assert (E25 : ew E 25 = Z_to_bv 64 pod)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 25 (Z_to_bv 5 25) eq_refl), (Rk2 25 ltac:(cbn; tauto)); exact A25).
assert (HUa0 : U E (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff 23 0)) (SOff 25 0)) = hd_xv e XProps).
{ cbn [hd_xv]. fold pod nl. rewrite !U_SAlu, !U_SLit. cbn [zalu_raw].
  rewrite (U_atom E 23 (1 - nl) E23 ltac:(lia)), (U_atom E 25 pod E25 ltac:(lia)).
  apply mb_sel; lia. }
assert (HS : st_ok rsegs E (mkSS 0x82f74 sr_atoms [mb_rC1; mb_rC2] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x82f74) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold mb_rC1. apply (hm_rw_region rsegs E (w_H W) mem2 9 R 0x140 0x148 0x140 0x148 [] E9);
        [lia | lia | | apply Forall_nil].
      intros o Ho. apply Hstkp. lia.
    + unfold mb_rC2. apply (hm_rw_region rsegs E (w_H W) mem2 9 R 0x158 0x160 0x158 0x160 [] E9);
        [lia | lia | | apply Forall_nil].
      intros o Ho. apply Hstkp. lia.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, mb_rC1, mb_rC2.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite E9. repeat split; lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at, MB_B1. change (w64 0x82f74) with (Z_to_bv 64 0x82f74).
aj_run_to mb_tbl_ok HS HJ 0x849ac.
{ eapply awr_ok_cons_gen; [reflexivity | exact E9 | |].
  { intros a Ha. cbn [mb_rC1 YP09.r_wlo YP09.r_whi] in Ha. left. lia. }
  eapply awr_ok_cons_gen; [reflexivity | exact E9 | | apply awr_ok_nil].
  intros a Ha. cbn [mb_rC2 YP09.r_wlo YP09.r_whi] in Ha. left. lia. }
assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl).
rreg HS (Z_to_bv 5 1) Rc1.
assert (Hpv : 0 <= hd_xv e XProps < 2 ^ 64) by (cbn [hd_xv]; fold pod nl; destruct (nl =? 0); lia).
assert (Rc10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (hd_xv e XProps)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 10)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 10)) with v end.
  rewrite denot_lit_U, HUa0. reflexivity. }
assert (Rc11 : getr (ms_regs ms) (Z_to_bv 5 11) = getr regs2 (Z_to_bv 5 22))
  by (eapply (mb_reg_is _ _ _ ms (w_H W) regs2 [] _ _ 22 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rc12 : getr (ms_regs ms) (Z_to_bv 5 12) = getr regs2 (Z_to_bv 5 20))
  by (eapply (mb_reg_is _ _ _ ms (w_H W) regs2 [] _ _ 20 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rc13 : getr (ms_regs ms) (Z_to_bv 5 13) = getr regs2 (Z_to_bv 5 26))
  by (eapply (mb_reg_is _ _ _ ms (w_H W) regs2 [] _ _ 26 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros r0 Hr. eapply (mb_reg_atom _ _ _ ms (w_H W) regs2 [] (Z_to_bv 5 r0) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
(* the two cells the run stores *)
assert (H140 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x140) 8 (hd_xv e XProps mod 2 ^ 64)).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch rr with Some ?rg =>
      assert (Hr : nth_error (ss_mem ss) 0 = Some rg) by (vm_compute; reflexivity);
      pose proof (mb_region_nth _ _ _ _ _ 0 _ HS Hr) as Hreg end end.
  rewrite Z.mod_small by exact Hpv.
  exact (mb_field _ _ _ _ _ _ _ _ _ 0x140 8 _ (hd_xv e XProps) Hreg E9 ltac:(cbn; tauto)
    ltac:(rewrite denot_lit_U, HUa0; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hpv) ltac:(cbn; lia)). }
assert (H158 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x158) 8 (pod mod 2 ^ 64)).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ss) 1) in
    lazymatch rr with Some ?rg =>
      assert (Hr : nth_error (ss_mem ss) 1 = Some rg) by (vm_compute; reflexivity);
      pose proof (mb_region_nth _ _ _ _ _ 1 _ HS Hr) as Hreg end end.
  rewrite Z.mod_small by lia.
  exact (mb_field _ _ _ _ _ _ _ _ _ 0x158 8 (SOff 25 0) pod Hreg E9 ltac:(cbn; tauto)
    ltac:(cbn [sv_denot]; rewrite E25, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (KC0 : forall a, 0 <= a < 2 ^ 64 -> ~ ((R + 0x140 <= a < R + 0x148) \/ (R + 0x158 <= a < R + 0x160)) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem2 a).
{ apply (mb_frame_kept _ _ _ _ _ _ HFr). intros a Ha Hw.
  destruct Hw as (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[<-|[]]];
  cbn [mb_rC1 mb_rC2 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite E9 in Hr; lia. }
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x140 <= a < R + 0x148) -> ~ (R + 0x158 <= a < R + 0x160) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem2 a)
  by (intros a Ha H1 H2'; apply KC0; [exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2' Hx)]]).
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
set (md2' := with_vm_backing (m_vm_lazy md2) mat md2) in *.
assert (E2 : getr (ms_regs ms) 2 = w64 R).
{ rewrite <- (mb_getr_z (ms_regs ms) 2 2 eq_refl), (Rk 2 ltac:(cbn; tauto)), (Rk2 2 ltac:(cbn; tauto)),
    (mb_getr_z regs 2 2 eq_refl). exact H2. }
assert (E3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ rewrite <- (mb_getr_z (ms_regs ms) 3 3 eq_refl), (Rk 3 ltac:(cbn; tauto)), (Rk2 3 ltac:(cbn; tauto)),
    (mb_getr_z regs 3 3 eq_refl). exact H3. }
assert (E4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ rewrite <- (mb_getr_z (ms_regs ms) 4 4 eq_refl), (Rk 4 ltac:(cbn; tauto)), (Rk2 4 ltac:(cbn; tauto)),
    (mb_getr_z regs 4 4 eq_refl). exact H4. }
assert (HR16 : R mod 16 = 0)
  by (rewrite <- (Z.mod_mod_divide R 32 16) by (exists 2; reflexivity); rewrite HR32; reflexivity).
assert (HCORE : hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W (ms_mem ms) md2' (ms_regs ms) R).
{ split; [exact HJ|]. split; [exact Hnev|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
  split; [exact HR16|]. unfold T_SEG_STK, ASTACK. split; lia. }
(* the memory at the call, against C5 *)
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (R - T_SEG_STK <= a < R) ->
  ~ (out <= a < out + 3 * (cap + 1)) -> ~ ((R + 0x140 <= a < R + 0x148) \/ (R + 0x150 <= a < R + 0x160)) ->
  ~ (shadow_addr F + 84 <= a < shadow_addr F + 86) -> ~ (F + 0x2a0 <= a < F + 0x2ac) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha Hs Ho HRc Hsh Hrs. unfold T_SEG_STK, ASTACK in Hs.
  rewrite KC by lia. apply KB; [exact Ha | lia | lia | exact Hsh | exact Hrs | unfold ESTACK; lia]. }
assert (HKEPT : hd_kept rsegs e (hi_w3 headamp_himg_B) W memc W (ms_mem ms)).
{ intros a Ha Hs Hn. apply KP; [exact Ha | exact Hs | | | |];
  intros Hx; apply Hn; [right; exact Hx | left; apply mb_inw; right; right; fold R; lia
  | left; apply mb_inw; right; left; fold F; lia | left; apply mb_inw; left; fold F; lia]. }
assert (HfshC : hd_fsh rsegs (w_H W) (ms_mem ms) F headamp_B_shB).
{ apply (hm_fsh_kept rsegs (w_H W) mem2 (w_H W) (ms_mem ms) F headamp_B_shB Hfsh2).
  intros i Hi. change (length headamp_B_shB) with 116%nat in Hi. change (Z.of_nat 116) with 116 in Hi.
  apply KC; unfold shadow_addr, SHADOW_OFF; lia. }
(* the parse's arguments, at the call (the call-site lemma of lib/AU/HPgSiteB.v) *)
assert (HARGS : forall HP : hd_pre rsegs B STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK (ms_regs ms) lyc Sc W
  (ms_mem ms) md2',
  hd_parse_args rsegs B STK sp0 ly S lyc Sc W (ms_mem ms) own (ms_regs ms) 0 0
  0x214a0 0x214c0 0x214e0 0x21500 0x9d478 0x5f8210 headamp_B_dcs nl pod out (F + 0x2a0) cap ev (Model.buf r)).
{ intros HP.
  exact (headamp_B_site_parse_args rsegs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0 0 e pos ev r
    k (ms_regs ms) lyc Sc W (ms_mem ms) md2' Hsegs (fun a (Ha : 0 <= a < 0) => False_ind _ (ltac:(lia) : False))
    ERRNO headamp_B_img_bytes_rsegs HP00 Hwf Hlen Hpod Hpodf Houtf Hdj Hev Hfrm HP (Permutation_refl _) HKEPT HfshC). }
pose proof (mb_cells_le (hd_props nl (Model.buf r)) cap Hcap) as Hlc.
eapply (hc_parse_k_call rsegs B MT 0x849ac MB_C1 out (F + 0x2a0)
  (Headamp.parse_props (hd_props nl (Model.buf r)) cap) Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W (ms_mem ms)
  md2' (ms_regs ms) R HCORE).
- rewrite <- (mb_getr_z (ms_regs ms) 1 1 eq_refl). exact Rc1.
- unfold MB_C1. lia.
- reflexivity.
- intros HP.
  apply (PARSE STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md2' k (ms_regs ms) nl pod out (F + 0x2a0)
    cap ev (Model.buf r) HP Hnull).
  + rewrite <- (mb_getr_z (ms_regs ms) 10 10 eq_refl). exact Rc10.
  + rewrite <- (mb_getr_z (ms_regs ms) 11 11 eq_refl), Rc11. exact R22.
  + rewrite <- (mb_getr_z (ms_regs ms) 12 12 eq_refl), Rc12, (Rk2 20 ltac:(cbn; tauto)). exact A20.
  + rewrite <- (mb_getr_z (ms_regs ms) 13 13 eq_refl), Rc13. exact R26.
  + exact (HARGS HP).
- intros W3 fx2 ly3 S3 regs3 mem3 md3 Hle Hfx HC3 Hpres Hfr Hperm Hio Hmo Hkeep H10 HO HRs Hev3.
  assert (KQ : forall a, 0 <= a < 2 ^ 64 -> ~ (R - T_parse_STK <= a < R) ->
    ~ (out <= a < out + 3 * (cap + 1)) -> ~ (F + 0x2a0 <= a < F + 0x2ac) -> ~ (as_errno B <= a < as_errno B + 4) ->
    aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W) (ms_mem ms) a).
  { intros a Ha Hs Ho Hr' He'. apply Hkeep; [exact Ha | exact Hs |].
    intros [Hx|[Hx|Hx]]; [apply Ho; lia | apply Hr'; lia | exact (He' Hx)]. }
  assert (Hpst : T_parse_STK = 12576) by reflexivity.
  apply (K fx2 ly3 S3 W3 regs3 mem3 md3 Hfx).
  + unfold mb_mid.
    cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_k x_regs x_lyc x_Sc x_W x_memc x_mdc x_e].
    unfold mb_ans. cbn [x_e]. fold out cap R F pod nl.
    split; [exact HC3|]. split; [exact Hfr|]. split; [exact Hperm|].
    split; [eapply same_io_trans; [exact Hio2|]; eapply same_io_trans; [apply same_io_wvb | exact Hio]|].
    split; [exact Hmo|].
    split; [rewrite (Hpres 8), (Rk 8), (Rk2 8) by first [unfold acallee_saved; lia | cbn [In]; tauto]; exact A8|].
    split; [rewrite (Hpres 9), (Rk 9), (Rk2 9) by first [unfold acallee_saved; lia | cbn [In]; tauto]; exact A9|].
    split; [rewrite (Hpres 18), (Rk 18), (Rk2 18) by first [unfold acallee_saved; lia | cbn [In]; tauto]; exact A18|].
    split; [rewrite (Hpres 19), (Rk 19), (Rk2 19) by first [unfold acallee_saved; lia | cbn [In]; tauto]; exact A19|].
    split; [rewrite (Hpres 20), (Rk 20), (Rk2 20) by first [unfold acallee_saved; lia | cbn [In]; tauto]; exact A20|].
    split; [rewrite (Hpres 21), (Rk 21) by first [unfold acallee_saved; lia | cbn [In]; tauto]; exact R21|].
    split; [rewrite (Hpres 22), (Rk 22) by first [unfold acallee_saved; lia | cbn [In]; tauto]; exact R22|].
    split; [rewrite (Hpres 23), (Rk 23), (Rk2 23) by first [unfold acallee_saved; lia | cbn [In]; tauto]; exact A23|].
    split; [rewrite (Hpres 24), (Rk 24), (Rk2 24) by first [unfold acallee_saved; lia | cbn [In]; tauto]; exact A24|].
    split; [rewrite (Hpres 25), (Rk 25), (Rk2 25) by first [unfold acallee_saved; lia | cbn [In]; tauto]; exact A25|].
    split; [rewrite (Hpres 26), (Rk 26) by first [unfold acallee_saved; lia | cbn [In]; tauto]; exact R26|].
    split; [rewrite (Hpres 27), (Rk 27), (Rk2 27) by first [unfold acallee_saved; lia | cbn [In]; tauto]; exact A27|].
    split.
    { intros a Ha Hs Hz. unfold mb_Z in Hz. cbn [x_e] in Hz. fold out cap R F in Hz.
      unfold T_SEG_STK, ASTACK in Hs.
      rewrite KQ; [| exact Ha | lia | intros Hx; apply Hz; left; exact Hx | intros Hx; apply Hz; right; right; right; left; exact Hx
        | intros Hx; apply Hz; right; right; right; right; exact Hx].
      apply KP; [exact Ha | unfold T_SEG_STK, ASTACK; lia | intros Hx; apply Hz; left; exact Hx
        | intros Hx; apply Hz; right; left; exact Hx | intros Hx; apply Hz; right; right; left; exact Hx
        | intros Hx; apply Hz; right; right; right; left; exact Hx]. }
    split.
    { eapply (hd_val_mem_kept rsegs (w_H W) (w_H W3) (ms_mem ms) mem3); [|exact H140].
      intros i Hi. apply KQ; lia. }
    split.
    { eapply (hd_val_mem_kept rsegs (w_H W) (w_H W3) mem2 mem3); [|exact H150].
      intros i Hi. rewrite KQ by lia. apply KC; lia. }
    split.
    { eapply (hd_val_mem_kept rsegs (w_H W) (w_H W3) (ms_mem ms) mem3); [|exact H158].
      intros i Hi. apply KQ; lia. }
    split.
    { apply (hm_fsh_kept rsegs (w_H W) (ms_mem ms) (w_H W3) mem3 F headamp_B_shB HfshC).
      intros i Hi. change (length headamp_B_shB) with 116%nat in Hi. change (Z.of_nat 116) with 116 in Hi.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Oapp, Fapp.
      apply KQ; unfold shadow_addr, SHADOW_OFF; lia. }
    split.
    { replace (hd_zbytes (repeat GUARD_BYTE 3)) with [165; 165; 165] by (vm_compute; reflexivity).
      intros j Hj. cbn [length] in Hj.
      assert (Hn : nth j [165; 165; 165] 0 = 165) by (destruct j as [|[|[|j]]]; [reflexivity | reflexivity | reflexivity | lia]).
      rewrite Hn. apply hm_aview_val1.
      assert (Hnot : ~ in_img rsegs (out + 3 * cap + Z.of_nat j)) by (apply NIo; lia).
      rewrite Hkeep; [| lia | lia |].
      2: { intros [Hx|[Hx|Hx]]; [lia | lia | exact (Hnot (Eimg _ Hx))]. }
      rewrite KC by lia. replace (out + 3 * cap + Z.of_nat j) with (out + (3 * cap + Z.of_nat j)) by lia.
      apply Hout. lia. }
    split; [exact HO|].
    split; [apply HRs; lia | exact Hev3].
  + rewrite (mb_getr_z regs3 10 10 eq_refl), Hrc. exact H10.
Qed.

End s.
End b.
