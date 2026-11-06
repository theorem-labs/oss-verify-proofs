(* reac-pw/fuzz_headamp, build asan-ubsan (image B): the two lemmas of lib/A/Rt/WrapU.v (image A) at image B's core
   (lib/AU/YB1v tfibsegs, YE2y rodata_ok, YF0x): AR_frame_U, the frame law at unpoison U mem, and rodata_ok_U, the
   read-only cells below kHighShadowBeg read at unpoison U mem. Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
Require Import
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.YB1v
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.YF0m
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.YF0x
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.YE2y.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* every byte of every cell of l lies in [0, kHighShadowBeg) *)
Definition ro_low (l : list (Z * Z * list (Z * N * Z))) : bool :=
forallb (fun r => forallb (fun c => (0 <=? fst (fst r) + fst (fst c)) &&
  (fst (fst r) + fst (fst c) + Z.of_N (snd (fst c)) <=? kHighShadowBeg)) (snd r)) l.

Lemma icpt_rodata_low : ro_low icpt_rodata = true.
Proof. vm_compute. reflexivity. Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.

Lemma AR_frame_U : forall U ly S W mem md mem' md',
AR tfibsegs B ly S W (unpoison U mem) md ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
AR tfibsegs B ly S W (unpoison U mem') md'.
Proof.
intros U ly S W mem md mem' md' HAR HOWN HVIS E1 E2 E3 HB.
apply (al_frame _ _ LAWS ly S W (unpoison U mem) md (unpoison U mem') md' HAR); [| |exact E1|exact E2|exact E3|].
- intros a Ha Hown. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
  + apply aview_unpoison_in. exact Ei.
  + rewrite !aview_unpoison_out by exact Ei. exact (HOWN a Ha Hown).
- intros a Hv. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
  + rewrite (aview_unpoison_in tfibsegs _ U mem' mem a Ei). exact Hv.
  + rewrite aview_unpoison_out in Hv |- * by exact Ei. exact (HVIS a Hv).
- intros a Hb Hh. unfold unpoison. destruct (in_ush U (bv_unsigned (w64 a))); [reflexivity | exact (HB a Hb Hh)].
Qed.

Lemma rodata_ok_U : forall l ly S (H : word -> bool) U mem E,
rodata_chk ly l = true -> ro_low l = true ->
(forall s, in_ush U s = true -> kHighShadowBeg <= s) ->
ARm B ly S (aview tfibsegs H (unpoison U mem)) ->
Forall (region_ok tfibsegs E (mrestrict H mem)) (map ro_region l).
Proof.
intros l ly S H U mem E Hc Hlow HU HM. unfold rodata_chk in Hc. unfold ro_low in Hlow.
rewrite forallb_forall in Hc, Hlow. apply Forall_map. apply Forall_forall. intros [[base sz] cs] Hin.
specialize (Hc _ Hin). specialize (Hlow _ Hin). cbn [fst snd] in Hc, Hlow.
apply andb_prop in Hc as [Hc Hcs]. apply andb_prop in Hc as [H0 Hhi].
apply Z.leb_le in H0. apply Z.leb_le in Hhi.
unfold ro_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
rewrite forallb_forall in Hcs, Hlow. apply Forall_map. apply Forall_forall. intros [[off n] v] Hc'.
specialize (Hcs _ Hc'). specialize (Hlow _ Hc'). cbn [fst snd] in Hcs, Hlow.
apply andb_prop in Hlow as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
apply andb_prop in Hcs as [Hcs H4]. apply andb_prop in Hcs as [Hcs H3]. apply andb_prop in Hcs as [H1 H2].
apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4.
unfold ro_chunk. cbn [fst snd].
eapply (chunk_ok_val tfibsegs E _ 0 (base + off) n (SLit v) v); [reflexivity | lia | lia |].
rewrite Z.add_0_l.
apply (YF0x.val_mem_ext (mrestrict H (unpoison U mem))).
2: exact (tfib_const_lookup B TB ly S H (unpoison U mem) (base + off) (N.to_nat n) v HM (const_chk_sound _ _ _ _ H1)).
intros j Hj. apply mbyte_of_aview. symmetry. apply aview_unpoison_out.
assert (Hj' : Z.of_nat j < Z.of_N n) by lia.
destruct (in_ush U (bv_unsigned (Z_to_bv 64 (base + off + Z.of_nat j)))) eqn:Ei; [|reflexivity].
exfalso. apply HU in Ei. rewrite wz in Ei by (unfold kHighShadowBeg in *; lia). unfold kHighShadowBeg in *. lia.
Qed.
End w.

Print Assumptions AR_frame_U.
Print Assumptions rodata_ok_U.
