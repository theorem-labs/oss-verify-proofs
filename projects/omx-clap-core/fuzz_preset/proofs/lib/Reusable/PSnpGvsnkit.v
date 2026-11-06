(* musl vsnprintf 0x91f0c (fm.asan) in the donor's proof form, from the contracts of __wrap_memset and
   __interceptor_vfprintf: entry at sp0 + 0x160 (s = D, n = N, fmt, ap = P), frame 0x130 with the stack protector,
   memset (sp, 0, 0xe8) through __wrap_memset 0x51a60 (ra 0x91f70), the FILE fields, the cookie {D, N - 1}, *D = 0,
   __wrap_vfprintf 0x41308 = j 0x457ec (ra 0x91fac) with the FILE at sp0 + FO, the canary check and the epilogue.
   New file. *)
(* Modified by Theorem Labs, 2026-10: the image-free half of origin/cold/port-fm-rtprintf-param 7e395de08f5
   proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGvsn.v for the snprintf chain restated over ARx (route (a),
   c-omx-hpreset 10:51Z): only the items the four roots' closure reaches, gv_zc / gv_addc (:52-54), gv_zchk / gv_vget
   (:151-159), gv_bv64_inj, gv_fld_zero, gv_fld_val, gv_region_wf_add, gv_all_disjoint_add, gv_st_ok_add (:187-256),
   with `tfibsegs` an implicit Section variable segs (no image numeral; -304 / 232 are the frame offset and size of
   musl vsnprintf's FILE, the same at every image of this code). The canary cells, the run definitions and the
   facts read off the code table are image-bearing and live in lib/A/PSnpGvsn.v. The walk of musl vsnprintf and
   avsn_ok (the HarnessDesign route) are not reached and not ported. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI00 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import PSnpGkit.
Import ListNotations.
Open Scope Z_scope.

(* ---- adding a chunk to the first region: the memset zeros as a CZero chunk ---- *)
Definition gv_zc : YP09.chunk := YP09.mkChunk (-304) (CZero 232).
Definition gv_addc (r : YP09.region) (c : YP09.chunk) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r) (c :: YP09.r_chunks r).

(* ---- reading a FILE field off the chunks: a CZero chunk covering it, or a CVal chunk at it ---- *)
Definition gv_zchk (cs : list YP09.chunk) (off n : Z) : bool :=
  match find_chunk cs off n with
  | Some c => match YP09.c_val c with CZero _ => true | _ => false end
  | None => false end.
Definition gv_vget (cs : list YP09.chunk) (off n : Z) : option sv :=
  match find_chunk cs off n with
  | Some c => if YP09.c_off c =? off then
      match YP09.c_val c with CVal w e => if Z.of_N w =? n then Some e else None | _ => None end else None
  | None => None end.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {segs : list Segment}.
Lemma gv_bv64_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit_small in E by lia. exact E.
Qed.
Lemma gv_fld_zero : forall E m base cs off (n : nat),
  Forall (YP09.chunk_ok segs E m base) cs -> gv_zchk cs off (Z.of_nat n) = true ->
  val_mem segs m (base + off) n 0.
Proof.
intros E m base cs off n Hcs Hz. unfold gv_zchk in Hz.
destruct (find_chunk cs off (Z.of_nat n)) as [c|] eqn:Ef; [|discriminate].
destruct c as [co cv]. cbn [YP09.c_val] in Hz. destruct cv as [w e| len | len | d s len]; try discriminate.
apply find_chunk_sound in Ef as (Hin & Hlo & Hhi). cbn [YP09.c_off YP09.c_len cv_len YP09.c_val] in Hlo, Hhi.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
intros k Hk. destruct (Hck (off - co + Z.of_nat k) ltac:(cbn [YP09.c_len cv_len YP09.c_val]; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. injection Hb1 as <-.
replace (base + off + Z.of_nat k) with (base + co + (off - co + Z.of_nat k)) by lia. rewrite Hb2.
f_equal. unfold YO0f.le_byte. rewrite Zmod_0_l, Z.shiftr_0_l. reflexivity.
Qed.
Lemma gv_fld_val : forall E m base cs off (n : nat) e v,
  Forall (YP09.chunk_ok segs E m base) cs -> gv_vget cs off (Z.of_nat n) = Some e -> (n <= 8)%nat ->
  bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_nat n) = v ->
  val_mem segs m (base + off) n v.
Proof.
intros E m base cs off n e v Hcs Hv Hn8 Hval. unfold gv_vget in Hv.
destruct (find_chunk cs off (Z.of_nat n)) as [c|] eqn:Ef; [|discriminate].
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in Hv.
destruct (co =? off) eqn:Ho; [|discriminate]. apply Z.eqb_eq in Ho. subst co.
destruct cv as [w e'| | |]; try discriminate.
destruct (Z.of_N w =? Z.of_nat n) eqn:Hw; [|discriminate]. apply Z.eqb_eq in Hw. injection Hv as <-.
apply find_chunk_sound in Ef as (Hin & _ & _).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
intros k Hk. destruct (Hck (Z.of_nat k) ltac:(cbn [YP09.c_len cv_len YP09.c_val]; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. injection Hb1 as <-. rewrite Hb2. f_equal.
unfold YP09.byte_of_word, YO0f.le_byte. subst v.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
change 256 with (2 ^ 8). rewrite (Z.mod_mod _ (2 ^ (8 * Z.of_nat n))) by (apply Z.pow_nonzero; lia).
rewrite (Z.mod_mod _ (2 ^ 8)) by lia.
apply Z.bits_inj'. intros i Hi. destruct (Z_lt_le_dec i 8) as [Li|Li].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* ---- adding a chunk to the first region ---- *)
Lemma gv_region_wf_add : forall r c, region_wf r = true -> chunk_inside r c = true -> region_wf (gv_addc r c) = true.
Proof.
intros [b lo hi wlo whi cs] c Hw Hc. unfold gv_addc, region_wf in *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
apply andb_true_iff in Hw as [Hw1 Hw2]. apply andb_true_iff. split; [exact Hw1|].
cbn [forallb]. apply andb_true_iff. split; [exact Hc | exact Hw2].
Qed.
Lemma gv_all_disjoint_add : forall E r c rs, all_disjoint E r rs -> all_disjoint E (gv_addc r c) rs.
Proof.
intros E r c rs. induction rs as [|x rs IH]; cbn [all_disjoint]; [tauto|].
intros [Hx Hr]. split; [exact Hx | exact (IH Hr)].
Qed.
Lemma gv_st_ok_add : forall E ss ms r rest c,
  st_ok segs E ss ms -> ss_mem ss = r :: rest -> chunk_inside r c = true ->
  YP09.chunk_ok segs E (ms_mem ms) (base_val E (YP09.r_base r)) c ->
  st_ok segs E (set_mem ss (gv_addc r c :: rest)) ms.
Proof.
intros E ss ms r rest c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm Hci Hck.
rewrite Hm in Hwf, Hok, Hpd. unfold st_ok, set_mem. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|exact H9]. split; [|split].
- cbn [regions_wf] in *. apply andb_true_iff in Hwf as [Hr Hrs]. apply andb_true_iff.
  split; [exact (gv_region_wf_add r c Hr Hci) | exact Hrs].
- apply Forall_cons; [|exact (Forall_inv_tail Hok)].
  pose proof (Forall_inv Hok) as (R1 & R2 & R3 & R4).
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. apply Forall_cons; [exact Hck | exact R4].
- cbn [pairwise_disjoint] in *. destruct Hpd as [Ha Hb]. split; [exact (gv_all_disjoint_add E r c rest Ha) | exact Hb].
Qed.
End v.
