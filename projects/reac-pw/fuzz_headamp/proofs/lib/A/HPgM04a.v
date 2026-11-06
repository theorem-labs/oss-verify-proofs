(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b for
   reac-pw/fuzz_headamp image A: its start-fact record hd_c3 / hd_c3_of, its bounds lemma hd_bounds and its walk hd_A
   (a nonzero test of a block, a register move, a zero test of the length, the __asan_memcpy, its return) restated for
   headamp's segment M04a (C7 0x83744 -> C8 0x83764) as h4a_c7 / h4a_c7_of / h4a_bounds / h4a_copy over HPgSeg.hs_scx,
   with headamp's registers and real-frame cells; its helpers hd_getr_z, hd_reg_atom, hd_aview_some and hd_frame_ro
   taken renamed (h4a_); role's own memcpy step replaced by the shared lib/A/HPgIntrin.v hd_memcpy_at; the arm with
   no copy (h4a_zero), the extra-atom register lemma h4a_reg_at and the post construction h4a_close are new; role's
   parse step, .rodata zone and string lemmas are not taken (M04a calls no parse). *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the segment M04a of
   LLVMFuzzerTestOneInput (0x80bc0), the copy of the parse's cells into the first block. It proves
   lib/A/HPgCSpec.v headamp_first_contract at image A's record HPgImgA.headamp_himg_A. Proves no function (kind:
   segment lemma).

   THE CODE (C7 0x83744 to C8 0x83764; fuzz.h:78, the harness's fuzz_dup of out)
     0x83744  beqz a0,0x83848      a0 = first, not NULL (hd_fresh_block): decided by a0's atom fact (first >= 4096)
     0x83748  mv s2,a0
     0x8374c  ld s10,0x60(s1)      R+0x60 holds F (HPgImgA's C7 list): a plain load of a real-frame cell
     0x83750  beqz s5,0x83764      s5 = 3 max(rc, 0): rc <= 0 goes straight to C8 (the first block holds no cell);
                                   else decided by s5's atom fact (3 <= 3 rc <= 27)
     0x83754  a0 = s2 = first, a1 = s8 = out, a2 = s5; 0x83760 jal __asan_memcpy (0x51d0c), ra = C8 = 0x83764.
   The walk is one engine run (lib/Reusable: st_ok, entry_st_ok_full, aj_run_to) over the table of these eight
   words, cut at the call; the call is HPgIntrin.hd_memcpy_at over the runtime's __asan_memcpy (YG0d.aintrin_realizes
   at 0x51d0c, the Section hypothesis AMEMCPY). Its premises: the first block is fresh (HPgBase.hd_fresh_awr_n), both
   blocks live, apart (YCbq.sep_blocks) and below the allocator's ceiling, their shadow and its hull from AR
   (HPgMem.hm_blk_ra); the source's 3 rc bytes lie inside out's 3 (cap + 1) (rc <= cap). Every byte M04a writes lies
   in the first block's 3 max(rc, 0) bytes or in the callee's stack [R - ESTACK, R); the cut facts of C8 (R+0x20,
   R+0xf0, R+0x110, R+0x118 and the callee-saved registers) and the frame's shadow lie outside both.
   The segment post's meter clause (HPgCSpec.hd_seg_post, mo_le MT Sc S2 0) is met at S2 = Sc, by the meter's laws:
   the Section hypothesis MTL (ameter_laws MT, the form lib/A/HPgSteps.v takes; the harness's meter ameter_triv has
   them by YCbp.ameter_triv_laws). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgSteps HPgCalls HPgIntrin.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== the code table ============================== *)
(* the eight words 0x83744 .. 0x83760: every run of M04a leaves them at the memcpy's entry or at C8 *)
Definition H4A_PC0 : Z := 0x83744.
Definition h4a_tbl : ctable := build_table rsegs H4A_PC0 8 TEmpty.
Lemma h4a_tbl_ok : table_ok rsegs h4a_tbl.
Proof. apply build_table_ok0. unfold H4A_PC0. lia. Qed.
(* C8, the memcpy's return address *)
Definition H4A_C8 : Z := 0x83764.
(* the real-frame cell R + 0x60, which holds F at C7: a read-only region at s1's atom (x9), its 8 bytes the extra atom
   32 of the run's env *)
Definition h4a_r60 : YP09.region := YP09.mkRegion (Some 9%nat) 0x60 0x68 0 0 [YP09.mkChunk 0x60 (CVal 8 (SOff 32 0))].

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* a register named by Z_to_bv 5 n (HPgBase's cut lists) is the register named by the numeral n *)
Lemma h4a_getr_z : forall (regs : bvmap 5 word) (r : bv 5) n, bv_unsigned r = n -> getr regs (Z_to_bv 5 n) = getr regs r.
Proof.
intros regs r n H. f_equal. apply bv_eq. subst n. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
pose proof (u5_range r). change (bv_modulus 5) with 32. lia.
Qed.

(* the first block's request: 1 for rc <= 0, else 3 rc *)
Lemma h4a_N1 : forall e, hd_xv e XRc3NZ = if 3 * Z.max (e_rc e) 0 =? 0 then 1 else 3 * Z.max (e_rc e) 0.
Proof. intros e. cbn [hd_xv]. destruct (Z.eqb_spec (3 * Z.max (e_rc e) 0) 0); lia. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a register the run left as its own atom holds its value at the run's start *)
Lemma h4a_reg_atom : forall (fx' : YK11.FPState) E ss ms (H : word -> bool) regs extra (r : bv 5),
@st_ok rsegs fx' E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs r.
Proof.
intros fx' E ss ms H regs extra r HS [HA _] Hr.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite HA by (pose proof (u5_range r); lia). apply ew_Ereg_reg.
Qed.
(* a register the run left as an atom n of its env holds that atom's word *)
Lemma h4a_reg_at : forall (fx' : YK11.FPState) E ss ms (H : word -> bool) (r : bv 5) n v,
@st_ok rsegs fx' E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = v -> getr (ms_regs ms) r = v.
Proof.
intros fx' E ss ms H r n v HS Hr Hv.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
exact Hv.
Qed.
(* a byte a block holds is present *)
Lemma h4a_aview_some : forall (H : word -> bool) (m : word -> option byte) a, apresent H m a -> aview rsegs H m a <> None.
Proof.
intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
(* a run whose one region writes nothing left every byte as it was *)
Lemma h4a_frame_ro : forall E (H : word -> bool) (m m' : word -> option byte),
frame_of E [h4a_r60] (mrestrict H m) (mrestrict H m') -> forall a, aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E H m m' HF a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]]. unfold h4a_r60 in Hr. cbn in Hr. lia.
Qed.

Section s.
Variable B : asyms.
Variable MT : ameter_ops.
(* the runtime's __asan_memcpy (YG0d.AsanAPI's aa_asan_memcpy at image A's pc_asan_memcpy, the target of the
   `jal` at 0x83760) *)
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy 0x51d0c.
(* the meter's laws: M04a's post keeps the state's meter (mo_le MT Sc Sc 0, YC5d.mo_le_refl) *)
Hypothesis MTL : ameter_laws MT.

(* ================= the start state at C7 (headamp_first_contract's premises), unfolded ================= *)
Record h4a_c7 (cx : hs_scx rsegs) (cs : list Headamp.cell) : Prop := H4AC7 {
c7_J : ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) (x_k cx);
c7_core : hc_core rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_k cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) (x_regs cx) (e_R (x_e cx));
c7_own : In (4, x_pos cx) (x_own cx);
c7_F : e_F (x_e cx) = frame_addr (x_lyc cx) 4 (x_pos cx);
c7_fsh : hd_fsh rsegs (w_H (x_W cx)) (x_memc cx) (e_F (x_e cx)) headamp_A_shB;
c7_cap : 0 <= e_cap (x_e cx) <= 9;
c7_a0 : getr (x_regs cx) (Z_to_bv 5 10) = w64 (e_first (x_e cx));
c7_s0 : getr (x_regs cx) (Z_to_bv 5 8) = w64 (e_S (x_e cx));
c7_s1 : getr (x_regs cx) (Z_to_bv 5 9) = w64 (e_R (x_e cx));
c7_s3 : getr (x_regs cx) (Z_to_bv 5 19) = w64 (shadow_addr (e_F (x_e cx)));
c7_s5 : getr (x_regs cx) (Z_to_bv 5 21) = w64 (3 * Z.max (e_rc (x_e cx)) 0);
c7_s6 : getr (x_regs cx) (Z_to_bv 5 22) = w64 (e_cap (x_e cx));
c7_s8 : getr (x_regs cx) (Z_to_bv 5 24) = w64 (e_out (x_e cx));
c7_s9 : getr (x_regs cx) (Z_to_bv 5 25) = w64 (e_pod (x_e cx));
c7_s11 : getr (x_regs cx) (Z_to_bv 5 27) = w64 (e_rc (x_e cx));
c7_c20 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x20) 8 ((e_F (x_e cx) + 0) mod 2 ^ 64);
c7_c60 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x60) 8 ((e_F (x_e cx) + 0) mod 2 ^ 64);
c7_cf0 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0xf0) 8 ((e_pp (x_e cx) + 0) mod 2 ^ 64);
c7_c110 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x110) 8
  ((if e_null (x_e cx) =? 0 then e_pod (x_e cx) else 0) mod 2 ^ 64);
c7_c118 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x118) 8
  ((3 * e_cap (x_e cx) + 3) mod 2 ^ 64);
c7_rc : -1 <= e_rc (x_e cx) <= e_cap (x_e cx);
c7_cs : Z.of_nat (length cs) = Z.max (e_rc (x_e cx)) 0;
c7_out : garr8 rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_out (x_e cx)) (hd_zbytes (ha_cells_bytes cs));
c7_outin : In (e_out (x_e cx), 3 * (e_cap (x_e cx) + 1)) (ablocks B (x_lyc cx) (x_Sc cx));
c7_firstin : In (e_first (x_e cx), hd_xv (x_e cx) XRc3NZ) (ablocks B (x_lyc cx) (x_Sc cx));
c7_firstnew : ~ In (e_first (x_e cx), hd_xv (x_e cx) XRc3NZ) (ablocks B (x_ly cx) (x_S cx)) }.

Lemma h4a_c7_of : forall (cx : hs_scx rsegs) cs,
hs_pre rsegs B cx (hi_shB headamp_himg_A) ->
hd_cut rsegs (w_H (x_W cx)) (x_memc cx) (x_regs cx) (x_e cx) (hi_L7 headamp_himg_A) ->
-1 <= e_rc (x_e cx) <= e_cap (x_e cx) -> Z.of_nat (length cs) = Z.max (e_rc (x_e cx)) 0 ->
garr8 rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_out (x_e cx)) (hd_zbytes (ha_cells_bytes cs)) ->
hd_fresh_block (ablocks B (x_ly cx) (x_S cx)) (ablocks B (x_lyc cx) (x_Sc cx)) (e_out (x_e cx))
  (3 * (e_cap (x_e cx) + 1)) ->
hd_fresh_block (ablocks B (x_ly cx) (x_S cx)) (ablocks B (x_lyc cx) (x_Sc cx)) (e_first (x_e cx))
  (hd_xv (x_e cx) XRc3NZ) ->
h4a_c7 cx cs.
Proof.
intros cx cs HP HL7 Hrc Hcs Hout (_ & Hoin & _) (_ & Hfin & Hfnew).
unfold hs_pre in HP.
pose proof (hc_core_of_seg_pre_A rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) as HCo.
destruct HP as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HeF & Hfsh & Hcap & _ & _ & _ & _ & _ & _ & _ & _ & _).
unfold hd_cut in HL7. cbn [hi_L7 headamp_himg_A] in HL7. unfold headamp_A_L67 in HL7.
repeat rewrite Forall_cons_iff in HL7.
destruct HL7 as (A10 & A8 & A9 & A19 & A21 & A22 & A24 & A25 & A27 & C20 & C60 & Cf0 & C110 & C118 & _).
cbn [fst snd hd_at hd_xv] in A10, A8, A9, A19, A21, A22, A24, A25, A27, C20, C60, Cf0, C110, C118.
cbn [hi_cid hi_shB headamp_himg_A] in Hown, HeF, Hfsh.
constructor; assumption.
Qed.

(* the bounds the walk uses, from C7's journal and the allocator's block and frame laws *)
Lemma h4a_bounds : forall cx cs, h4a_c7 cx cs ->
1 <= hd_xv (x_e cx) XRc3NZ <= 3 * e_cap (x_e cx) + 1 /\
3 * Z.max (e_rc (x_e cx)) 0 <= hd_xv (x_e cx) XRc3NZ /\
req_size (hd_xv (x_e cx) XRc3NZ) = hd_xv (x_e cx) XRc3NZ /\
req_size (3 * (e_cap (x_e cx) + 1)) = 3 * (e_cap (x_e cx) + 1) /\
4096 <= e_first (x_e cx) /\ e_first (x_e cx) + hd_xv (x_e cx) XRc3NZ <= alloc_ceiling /\
in_app (e_first (x_e cx)) (hd_xv (x_e cx) XRc3NZ) /\
4096 <= e_out (x_e cx) /\ e_out (x_e cx) + 3 * (e_cap (x_e cx) + 1) <= alloc_ceiling /\
4096 <= e_F (x_e cx) /\ e_F (x_e cx) + 1024 <= alloc_ceiling /\
alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ e_R (x_e cx) <= 2 ^ 47 /\ spZ (x_regs cx) = e_R (x_e cx) /\
CEIL_MIN <= alloc_ceiling <= CEIL_MAX /\
(e_first (x_e cx) + hd_xv (x_e cx) XRc3NZ <= e_out (x_e cx) \/
 e_out (x_e cx) + 3 * (e_cap (x_e cx) + 1) <= e_first (x_e cx)).
Proof.
intros cx cs HC.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HC as [HJ HCo Hown HeF _ Hcap _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrc _ _ Hoin Hfin _].
pose proof HJ as (HAR & _).
assert (HN : 1 <= hd_xv (x_e cx) XRc3NZ <= 3 * e_cap (x_e cx) + 1 /\
  3 * Z.max (e_rc (x_e cx)) 0 <= hd_xv (x_e cx) XRc3NZ).
{ rewrite h4a_N1. destruct (Z.eqb_spec (3 * Z.max (e_rc (x_e cx)) 0) 0); lia. }
assert (HqN : req_size (hd_xv (x_e cx) XRc3NZ) = hd_xv (x_e cx) XRc3NZ).
{ unfold req_size. destruct (Z.eqb_spec (hd_xv (x_e cx) XRc3NZ) 0); lia. }
assert (HqO : req_size (3 * (e_cap (x_e cx) + 1)) = 3 * (e_cap (x_e cx) + 1)).
{ unfold req_size. destruct (Z.eqb_spec (3 * (e_cap (x_e cx) + 1)) 0); lia. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (_ & P4096 & Pc & Papp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hoin) as (_ & O4096 & Oc & _).
rewrite HqN in Pc, Papp. rewrite HqO in Oc.
pose proof (hc_frm_low rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hown) as (F4096 & Fc).
rewrite <- HeF in F4096, Fc. rewrite hc_fb in Fc. unfold HC_FB in Fc.
pose proof (hc_core_R rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCo) as (HR & HR47 & Hsp).
pose proof alloc_ceiling_value as (Hceil & _).
assert (Hne : (e_first (x_e cx), hd_xv (x_e cx) XRc3NZ) <> (e_out (x_e cx), 3 * (e_cap (x_e cx) + 1))).
{ intros Heq. apply (f_equal snd) in Heq. cbn [snd] in Heq. lia. }
pose proof (sep_blocks rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hfin Hoin Hne) as Hdj.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite HqN, HqO in Hdj.
destruct HN as (HN1 & HN2).
repeat (split; [assumption|]). exact Hdj.
Qed.

(* ===================== the post at C8, from what either arm leaves ===================== *)
Definition h4a_post (cx : hs_scx rsegs) (cs : list Headamp.cell) : world rsegs -> config -> Prop :=
hd_seg_post rsegs B MT (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_k cx) (x_regs cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) (hi_c8 headamp_himg_A)
  (fun f => f = fx)
  (fun a => hd_inw (x_e cx) (hi_w4 headamp_himg_A) a \/
            e_first (x_e cx) <= a < e_first (x_e cx) + hd_xv (x_e cx) XRc3NZ)
  (fun W2 regs2 mem2 =>
   hd_cut rsegs (w_H W2) mem2 regs2 (x_e cx) (hi_L8 headamp_himg_A) /\
   hd_fsh rsegs (w_H W2) mem2 (e_F (x_e cx)) (hi_shB headamp_himg_A) /\
   garr8 rsegs (mrestrict (w_H W2) mem2) (e_first (x_e cx)) (hd_zbytes (ha_cells_bytes cs))).

(* at C8: the journal at C7's blocks and frames, the I/O state as at C7, sp / gp / tp and the cut's callee-saved
   registers as at C7, s2 = first, s10 = F, every byte outside the first block's 3 max(rc, 0) bytes and the callee's
   stack as at C7, and the first block holding the cells *)
Lemma h4a_close : forall cx cs regs2 mem2 md2,
h4a_c7 cx cs ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) mem2 md2 (x_k cx) ->
same_io (x_mdc cx) md2 ->
(forall r, In r [2; 3; 4; 8; 9; 19; 22; 24; 25; 27] -> getr regs2 (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)) ->
getr regs2 (Z_to_bv 5 18) = w64 (e_first (x_e cx)) ->
getr regs2 (Z_to_bv 5 26) = w64 (e_F (x_e cx)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_first (x_e cx) <= a < e_first (x_e cx) + 3 * Z.max (e_rc (x_e cx)) 0) ->
 ~ (e_R (x_e cx) - ESTACK <= a < e_R (x_e cx)) ->
 aview rsegs (w_H (x_W cx)) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a) ->
garr8 rsegs (mrestrict (w_H (x_W cx)) mem2) (e_first (x_e cx)) (hd_zbytes (ha_cells_bytes cs)) ->
SRr rsegs (x_W cx) (mkCfg (mkst regs2 (w64 H4A_C8) mem2 (seg_rom rsegs)) md2) (h4a_post cx cs).
Proof using MTL.
intros cx cs regs2 mem2 md2 HC HJ2 Hio2 Rk R18 R26 Hkeep Hfirst.
pose proof (h4a_bounds cx cs HC) as (HN1 & HN2 & HqN & HqO & P4096 & Pc & Papp & O4096 & Oc & F4096 & Fc &
  HRlo & HR47 & Hsp & Hceil & Hdj).
pose proof HC as [HJ HCo Hown HeF Hfsh Hcap A10 A8 A9 A19 A21 A22 A24 A25 A27 C20 C60 Cf0 C110 C118
  Hrc Hcs Hout Hoin Hfin Hfnew].
clear Hdj.
unfold T_SEG_STK, ASTACK in HRlo.
apply SRr_ret. unfold h4a_post, hd_seg_post. cbv beta.
exists fx, (x_lyc cx), (x_Sc cx), regs2, mem2, md2.
split; [reflexivity|].
split; [reflexivity|].
split; [exact HJ2|].
split; [intros r Hr; apply Rk; cbn [In]; lia|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [exact Hio2|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a Ha Hs He. rewrite Hsp in Hs. unfold T_SEG_STK, ASTACK in Hs.
  apply Hkeep; [exact Ha | | unfold ESTACK; lia].
  intros Hf. apply He. right. lia. }
cbn [hi_L8 hi_shB headamp_himg_A].
assert (KC : forall o v, 0 <= o -> o + 8 <= 0x120 ->
  val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + o) 8 v ->
  val_mem rsegs (mrestrict (w_H (x_W cx)) mem2) (e_R (x_e cx) + o) 8 v).
{ intros o v Ho1 Ho2 Hv. eapply (val_mem_kept rsegs); [|exact Hv]. intros kk Hkk. cbn in Hkk.
  apply Hkeep; unfold ESTACK; lia. }
split.
{ unfold hd_cut.
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; rewrite Rk by (cbn [In]; lia); exact A8|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; rewrite Rk by (cbn [In]; lia); exact A9|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; exact R18|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; rewrite Rk by (cbn [In]; lia); exact A19|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; rewrite Rk by (cbn [In]; lia); exact A22|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; rewrite Rk by (cbn [In]; lia); exact A24|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; rewrite Rk by (cbn [In]; lia); exact A25|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; rewrite Z.add_0_r; exact R26|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; rewrite Rk by (cbn [In]; lia); exact A27|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; apply KC; [lia | lia | exact C20]|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; apply KC; [lia | lia | exact Cf0]|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; apply KC; [lia | lia | exact C110]|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; apply KC; [lia | lia | exact C118]|].
  apply Forall_nil. }
split; [|exact Hfirst].
apply (hm_fsh_kept rsegs (w_H (x_W cx)) (x_memc cx) (w_H (x_W cx)) mem2 (e_F (x_e cx)) headamp_A_shB Hfsh).
intros i Hi.
assert (Hl : Z.of_nat (length headamp_A_shB) = 80) by (vm_compute; reflexivity).
rewrite Hl in Hi.
assert (HF8a : 512 <= e_F (x_e cx) / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8b : e_F (x_e cx) / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Papp.
apply Hkeep; unfold shadow_addr, SHADOW_OFF, ESTACK; lia.
Qed.

(* the run's env: the registers at C7 and F, the word R + 0x60 holds, as the extra atom 32 *)
Lemma h4a_atoms : forall cx cs, h4a_c7 cx cs ->
bv_unsigned (ew (Ereg (x_regs cx) [w64 (e_F (x_e cx))]) 9) = e_R (x_e cx) /\
bv_unsigned (ew (Ereg (x_regs cx) [w64 (e_F (x_e cx))]) 10) = e_first (x_e cx) /\
bv_unsigned (ew (Ereg (x_regs cx) [w64 (e_F (x_e cx))]) 21) = 3 * Z.max (e_rc (x_e cx)) 0 /\
ew (Ereg (x_regs cx) [w64 (e_F (x_e cx))]) 32 = w64 (e_F (x_e cx)).
Proof.
intros cx cs HC.
pose proof (h4a_bounds cx cs HC) as (HN1 & HN2 & _ & _ & P4096 & Pc & _ & _ & _ & F4096 & Fc &
  HRlo & HR47 & _ & Hceil & _).
pose proof HC as [_ _ _ _ _ Hcap A10 _ A9 _ A21 _ _ _ _ _ _ _ _ _ Hrc _ _ _ _ _].
unfold T_SEG_STK, ASTACK in HRlo.
split; [|split; [|split]].
- rewrite (ew_Ereg_nat (x_regs cx) _ 9 (Z_to_bv 5 9) eq_refl), A9. unfold w64. apply unsigned_lit_small. lia.
- rewrite (ew_Ereg_nat (x_regs cx) _ 10 (Z_to_bv 5 10) eq_refl), A10. unfold w64. apply unsigned_lit_small. lia.
- rewrite (ew_Ereg_nat (x_regs cx) _ 21 (Z_to_bv 5 21) eq_refl), A21. unfold w64. apply unsigned_lit_small. lia.
- change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* the region of R + 0x60 at C7 *)
Lemma h4a_r60_ok : forall cx cs, h4a_c7 cx cs ->
region_ok rsegs (Ereg (x_regs cx) [w64 (e_F (x_e cx))]) (mrestrict (w_H (x_W cx)) (x_memc cx)) h4a_r60.
Proof.
intros cx cs HC.
pose proof (h4a_bounds cx cs HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F4096 & Fc & HRlo & HR47 & _ & Hceil & _).
pose proof (h4a_atoms cx cs HC) as (E9 & _ & _ & E32).
pose proof HC as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C60 _ _ _ _ _ _ _ _ _].
unfold T_SEG_STK, ASTACK in HRlo.
unfold h4a_r60.
apply (hm_ro_region rsegs _ (w_H (x_W cx)) (x_memc cx) 9 (e_R (x_e cx)) 0x60 0x68 _ E9); [lia | lia |].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val rsegs _ _ (e_R (x_e cx)) 0x60 8 (SOff 32 0) (e_F (x_e cx))).
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
- cbn. lia.
- cbn. lia.
- rewrite Z.add_0_r, Z.mod_small in C60 by lia. exact C60.
Qed.

(* ===================== rc <= 0: no copy, straight to C8 ===================== *)
Lemma h4a_zero : forall cx cs, h4a_c7 cx cs -> e_rc (x_e cx) <= 0 ->
SRr rsegs (x_W cx) (cfg_at rsegs (hi_c7 headamp_himg_A) (x_regs cx) (x_memc cx) (x_mdc cx)) (h4a_post cx cs).
Proof using MTL.
intros cx cs HC Hle.
pose proof (h4a_bounds cx cs HC) as (HN1 & HN2 & HqN & HqO & P4096 & Pc & _ & O4096 & Oc & F4096 & Fc &
  HRlo & HR47 & Hsp & Hceil & _).
pose proof (h4a_atoms cx cs HC) as (E9 & E10 & E21 & E32).
pose proof (h4a_r60_ok cx cs HC) as Hr60.
pose proof HC as [HJ HCo Hown HeF Hfsh Hcap A10 A8 A9 A19 A21 A22 A24 A25 A27 C20 C60 Cf0 C110 C118
  Hrc Hcs Hout Hoin Hfin Hfnew].
assert (Hm : Z.max (e_rc (x_e cx)) 0 = 0) by lia.
rewrite Hm in A21.
assert (Hcs0 : cs = []) by (destruct cs as [|c cs']; [reflexivity | cbn [length] in Hcs; lia]).
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (HS : st_ok rsegs (Ereg (x_regs cx) [w64 (e_F (x_e cx))])
  (mkSS 0x83744 (sr_set sr_atoms (Z_to_bv 5 21) (SLit 0)) [h4a_r60] None
    (mkFacts [(10%nat, mkAF 4096 CEIL_MAX 0)] [] []))
  (restrict (w_H (x_W cx)) (mkst (x_regs cx) (Z_to_bv 64 0x83744) (x_memc cx) (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_pin; [apply regs_ok_Ereg | |].
    + intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
    + rewrite A21. reflexivity.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact Hr60 | apply Forall_nil].
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite E10. rewrite ?Z.pow_0_r, ?Z.mod_1_r. repeat split; lia. }
unfold cfg_at, w64. cbn [hi_c7 headamp_himg_A].
aj_run_to h4a_tbl_ok HS HJ H4A_C8.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [unfold h4a_r60; cbn; lia | apply awr_ok_nil]. }
pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
pose proof (h4a_frame_ro _ _ _ _ HFr) as KA.
assert (HAE : env_agree 32 (Ereg (x_regs cx) [w64 (e_F (x_e cx))]) (Ereg (x_regs cx) [w64 (e_F (x_e cx))]))
  by apply env_agree_refl.
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 19; 22; 24; 25; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)).
{ intros r Hr. eapply (h4a_reg_atom _ _ _ ms (w_H (x_W cx)) (x_regs cx) _ (Z_to_bv 5 r) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
assert (R18 : getr (ms_regs ms) (Z_to_bv 5 18) = w64 (e_first (x_e cx))).
{ rewrite <- A10. apply (h4a_reg_at _ _ _ ms (w_H (x_W cx)) (Z_to_bv 5 18) 10%nat _ HS);
    [vm_compute; reflexivity | apply ew_Ereg_nat; reflexivity]. }
assert (R26 : getr (ms_regs ms) (Z_to_bv 5 26) = w64 (e_F (x_e cx))).
{ apply (h4a_reg_at _ _ _ ms (w_H (x_W cx)) (Z_to_bv 5 26) 32%nat _ HS); [vm_compute; reflexivity | exact E32]. }
apply (h4a_close cx cs (ms_regs ms) (ms_mem ms) _ HC HJ).
- apply same_io_wvb.
- exact Rk.
- exact R18.
- exact R26.
- intros a _ _ _. exact (KA a).
- rewrite Hcs0. unfold garr8. intros j Hj. cbn in Hj. lia.
Qed.

(* ===================== rc > 0: the copy of 3 rc bytes of out into first ===================== *)
Lemma h4a_copy : forall cx cs, h4a_c7 cx cs -> 0 < e_rc (x_e cx) ->
SRr rsegs (x_W cx) (cfg_at rsegs (hi_c7 headamp_himg_A) (x_regs cx) (x_memc cx) (x_mdc cx)) (h4a_post cx cs).
Proof using AMEMCPY MTL.
intros cx cs HC Hgt.
pose proof (h4a_bounds cx cs HC) as (HN1 & HN2 & HqN & HqO & P4096 & Pc & Papp & O4096 & Oc & F4096 & Fc &
  HRlo & HR47 & Hsp & Hceil & Hdj).
pose proof (h4a_atoms cx cs HC) as (E9 & E10 & E21 & E32).
pose proof (h4a_r60_ok cx cs HC) as Hr60.
pose proof HC as [HJ HCo Hown HeF Hfsh Hcap A10 A8 A9 A19 A21 A22 A24 A25 A27 C20 C60 Cf0 C110 C118
  Hrc Hcs Hout Hoin Hfin Hfnew].
clear Papp.
assert (Hm : Z.max (e_rc (x_e cx)) 0 = e_rc (x_e cx)) by lia.
rewrite Hm in A21, E21, HN2.
assert (HN : hd_xv (x_e cx) XRc3NZ = 3 * e_rc (x_e cx)).
{ rewrite h4a_N1, Hm. destruct (Z.eqb_spec (3 * e_rc (x_e cx)) 0); lia. }
pose proof HCo as (_ & _ & H2 & H3 & H4 & HR16 & Hwin & HRs).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hs16 & _) & _).
unfold T_SEG_STK, ASTACK in HRlo, Hwin.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (HS : st_ok rsegs (Ereg (x_regs cx) [w64 (e_F (x_e cx))])
  (mkSS 0x83744 sr_atoms [h4a_r60] None
    (mkFacts [(10%nat, mkAF 4096 CEIL_MAX 0); (21%nat, mkAF 3 27 0)] [] []))
  (restrict (w_H (x_W cx)) (mkst (x_regs cx) (Z_to_bv 64 0x83744) (x_memc cx) (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact Hr60 | apply Forall_nil].
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite E10, E21. rewrite ?Z.pow_0_r, ?Z.mod_1_r. repeat split; lia. }
unfold cfg_at, w64. cbn [hi_c7 headamp_himg_A].
aj_run_to h4a_tbl_ok HS HJ A_ASAN_MEMCPY.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [unfold h4a_r60; cbn; lia | apply awr_ok_nil]. }
pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
pose proof (h4a_frame_ro _ _ _ _ HFr) as KA.
assert (HAE : env_agree 32 (Ereg (x_regs cx) [w64 (e_F (x_e cx))]) (Ereg (x_regs cx) [w64 (e_F (x_e cx))]))
  by apply env_agree_refl.
(* the registers at the call *)
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 10; 19; 21; 22; 24; 25; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)).
{ intros r Hr. eapply (h4a_reg_atom _ _ _ ms (w_H (x_W cx)) (x_regs cx) _ (Z_to_bv 5 r) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
assert (R1 : getr (ms_regs ms) 1 = w64 H4A_C8).
{ rewrite (st_ok_restrict_reg rsegs (w_H (x_W cx)) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (1%bv : bv 5)) in
    change (sr_get (ss_regs ss) (1%bv : bv 5)) with v end. reflexivity. }
assert (R11 : getr (ms_regs ms) (Z_to_bv 5 11) = getr (x_regs cx) (Z_to_bv 5 24)).
{ apply (h4a_reg_at _ _ _ ms (w_H (x_W cx)) (Z_to_bv 5 11) 24%nat _ HS);
    [vm_compute; reflexivity | apply ew_Ereg_nat; reflexivity]. }
assert (R12 : getr (ms_regs ms) (Z_to_bv 5 12) = getr (x_regs cx) (Z_to_bv 5 21)).
{ apply (h4a_reg_at _ _ _ ms (w_H (x_W cx)) (Z_to_bv 5 12) 21%nat _ HS);
    [vm_compute; reflexivity | apply ew_Ereg_nat; reflexivity]. }
assert (R18 : getr (ms_regs ms) (Z_to_bv 5 18) = w64 (e_first (x_e cx))).
{ rewrite <- A10. apply (h4a_reg_at _ _ _ ms (w_H (x_W cx)) (Z_to_bv 5 18) 10%nat _ HS);
    [vm_compute; reflexivity | apply ew_Ereg_nat; reflexivity]. }
assert (R26 : getr (ms_regs ms) (Z_to_bv 5 26) = w64 (e_F (x_e cx))).
{ apply (h4a_reg_at _ _ _ ms (w_H (x_W cx)) (Z_to_bv 5 26) 32%nat _ HS); [vm_compute; reflexivity | exact E32]. }
assert (Hsp1 : spZ (ms_regs ms) = x_sp0 cx + (e_R (x_e cx) - x_sp0 cx)).
{ unfold spZ. rewrite <- (h4a_getr_z (ms_regs ms) 2 2 eq_refl), (Rk 2 ltac:(cbn [In]; lia)),
    (h4a_getr_z (x_regs cx) 2 2 eq_refl), H2.
  unfold w64. rewrite unsigned_lit_small by lia. ring. }
(* the two blocks at the call *)
pose proof (proj1 HJ) as HAR.
destruct (hm_blk_ra rsegs B _ _ _ _ _ (e_first (x_e cx)) (hd_xv (x_e cx) XRc3NZ) (e_first (x_e cx))
  (3 * e_rc (x_e cx)) HAR Hfin ltac:(lia) ltac:(rewrite HqN; lia)) as (Hrad & Hhd).
destruct (hm_blk_ra rsegs B _ _ _ _ _ (e_out (x_e cx)) (3 * (e_cap (x_e cx) + 1)) (e_out (x_e cx))
  (3 * e_rc (x_e cx)) HAR Hoin ltac:(lia) ltac:(rewrite HqO; lia)) as (Hrax & Hhx).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hoin) as (_ & _ & _ & _ & Opres & _).
rewrite HqO in Opres.
eapply SRr_bind.
{ eapply (hd_memcpy_at B AMEMCPY (x_W cx) (ms_regs ms) (ms_mem ms) (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx)
    (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_lyc cx) (x_Sc cx) _ (x_k cx)
    (e_first (x_e cx)) (e_out (x_e cx)) (3 * e_rc (x_e cx)) (e_R (x_e cx) - x_sp0 cx) (w64 H4A_C8) HJ).
  - rewrite <- (h4a_getr_z (ms_regs ms) 10 10 eq_refl), (Rk 10 ltac:(cbn [In]; lia)). exact A10.
  - rewrite <- (h4a_getr_z (ms_regs ms) 11 11 eq_refl), R11. exact A24.
  - rewrite <- (h4a_getr_z (ms_regs ms) 12 12 eq_refl), R12. exact A21.
  - lia.
  - lia.
  - lia.
  - exact Hsp1.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite <- (h4a_getr_z (ms_regs ms) 3 3 eq_refl), (Rk 3 ltac:(cbn [In]; lia)), (h4a_getr_z (x_regs cx) 3 3 eq_refl).
    exact H3.
  - rewrite <- (h4a_getr_z (ms_regs ms) 4 4 eq_refl), (Rk 4 ltac:(cbn [In]; lia)), (h4a_getr_z (x_regs cx) 4 4 eq_refl).
    exact H4.
  - exact R1.
  - apply hc_ret_ok; [unfold H4A_C8; lia | reflexivity].
  - intros a Ha. split.
    + replace a with (e_first (x_e cx) + (a - e_first (x_e cx))) by lia.
      apply (hd_fresh_awr_n (x_STK cx) (x_sp0 cx) (x_FP cx) (ablocks B (x_ly cx) (x_S cx)) (ablocks B (x_lyc cx) (x_Sc cx))
        (x_lyc cx) (x_own cx) (e_first (x_e cx)) (hd_xv (x_e cx) XRc3NZ) Hfin Hfnew); lia.
    + unfold ESTACK. lia.
  - eapply amem_range_of_block; [exact LAWS | exact HAR | exact Hfin | lia | rewrite HqN; lia].
  - exact Hrad.
  - exact Hhd.
  - lia.
  - lia.
  - intros a Ha. split.
    + apply h4a_aview_some. exact (proj1 (Opres a ltac:(lia))).
    + rewrite Hsp1. unfold ESTACK. lia.
  - lia.
  - eapply amem_range_of_block; [exact LAWS | exact HAR | exact Hoin | lia | rewrite HqO; lia].
  - exact Hrax.
  - exact Hhx. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & Hpres2 & Ha02 & Hcpy & Hkeep & Hgrow).
apply (h4a_close cx cs regs2 mem2 md2 HC HJ2).
- eapply same_io_trans; [apply same_io_wvb | exact Hio2].
- intros r Hr. rewrite (Hpres2 r) by (cbn [In] in Hr; unfold acallee_saved; lia). apply Rk. cbn [In] in Hr |- *. lia.
- rewrite (Hpres2 18) by (unfold acallee_saved; lia). exact R18.
- rewrite (Hpres2 26) by (unfold acallee_saved; lia). exact R26.
- intros a Ha Hf Hs. rewrite Hm in Hf. rewrite (Hkeep a Ha); [exact (KA a) | exact Hf | unfold ESTACK in *; lia].
- pose proof (length_ha_cells_bytes cs) as Hlc.
  apply (proj1 (hm_bytes_zbytes rsegs _ _ _ _)).
  apply (hm_memcpy_bytes rsegs (w_H (x_W cx)) (x_memc cx) (w_H (x_W cx)) mem2 (e_out (x_e cx)) (e_first (x_e cx))
    (ha_cells_bytes cs)).
  + apply (proj2 (hm_bytes_zbytes rsegs _ _ _ _)). exact Hout.
  + intros i Hi. rewrite Hlc in Hi. rewrite (Hcpy i ltac:(lia)). apply KA.
Qed.

(* ===================== the contract ===================== *)
Theorem headamp_A_first_holds : forall RLO RHI : Z, headamp_first_contract rsegs B MT headamp_himg_A RLO RHI.
Proof using AMEMCPY MTL.
intros RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs e pos cs
  HP HL7 Hrc Hcs Hout _ Hfo Hff _.
set (cx := {| x_STK := STK; x_sp0 := sp0; x_FP := FP; x_ly := ly; x_S := S; x_W0 := W0; x_mem0 := mem0;
  x_md0 := md0; x_own := own; x_k := k; x_regs := regs; x_lyc := lyc; x_Sc := Sc; x_W := W; x_memc := memc;
  x_mdc := mdc; x_RLO := RLO; x_RHI := RHI; x_e := e; x_pos := pos |} : hs_scx rsegs).
assert (HC : h4a_c7 cx cs) by exact (h4a_c7_of cx cs HP HL7 Hrc Hcs Hout Hfo Hff).
destruct (Z_lt_le_dec 0 (e_rc e)) as [Hgt | Hle].
- exact (h4a_copy cx cs HC Hgt).
- exact (h4a_zero cx cs HC Hle).
Qed.
Print Assumptions headamp_A_first_holds.
End s.
End b.

Print Assumptions headamp_A_first_holds.
