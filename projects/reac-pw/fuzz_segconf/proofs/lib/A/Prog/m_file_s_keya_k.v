(* m_file on fuzz_segconf.asan (image A), segment S_MF_KEYA: the KEY facts ka_ctx (m_file_s_keya_d.v) across a run
   that writes no byte (the strip loops and the joins between them read the line and write only registers): the
   symbolic run gives the journal at the new memory and keeps every byte's view (kept_of_frame over read-only
   regions), and ka_ctx follows. The readers are equal as functions (aview reads a word address, so its value at
   x is its value at x mod 2^64; functional extensionality, which lib/A/Prog/PaDenot.v and PaLibF.v import too).
   The KEYA segment lane of the G2 walk owner's G2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_keya_m m_file_s_keya_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma ka_aview_mod : forall H (m : word -> option byte) x, aview SEGS H m x = aview SEGS H m (x mod 2 ^ 64).
Proof.
intros H m x. unfold aview, mbyte.
replace (Z_to_bv 64 (x mod 2 ^ 64)) with (Z_to_bv 64 x); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma ka_rd_ext : forall H (m m' : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a) -> aview SEGS H m' = aview SEGS H m.
Proof.
intros H m m' K. apply functional_extensionality. intros x.
rewrite (ka_aview_mod H m' x), (ka_aview_mod H m x). apply K. apply Z.mod_pos_bound. lia.
Qed.
Lemma ka_val_mem_kept : forall H (m m' : word -> option byte) a n v,
aview SEGS H m' = aview SEGS H m -> val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' a n v HE Hv k Hk. specialize (Hv k Hk).
pose proof (f_equal (fun f => f (a + Z.of_nat k)) HE) as E. cbv beta in E. unfold aview in E. rewrite Hv in E.
destruct (mbyte SEGS (mrestrict H m') (a + Z.of_nat k)) as [b|]; cbn [option_map] in E; [|discriminate E].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Section e.
Variable B : asyms.

(* ka_ctx at a memory with the same view everywhere and the journal at it *)
Lemma ka_ctx_kept : forall v lyc Sc Wc memc mdc memc' mdc' pos mcc gi line p rest i j ei n,
ka_ctx B v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v)
  (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
(forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
ka_ctx B v lyc Sc Wc memc' mdc' pos mcc gi line p rest i j ei n.
Proof.
intros v lyc Sc Wc memc mdc memc' mdc' pos mcc gi line p rest i j ei n
  (CX & LS & FRM & CORE & CELLS & Hn & Hr & LOOP & HL & Hij & HjL & HSL & HMC & HFIN & NP) HJ' KM.
pose proof (ka_rd_ext (w_H Wc) memc memc' KM) as HR.
assert (VK : forall a k vv, val_mem SEGS (mrestrict (w_H Wc) memc) a k vv -> val_mem SEGS (mrestrict (w_H Wc) memc') a k vv)
  by (intros a k vv; apply (ka_val_mem_kept (w_H Wc) memc memc' a k vv HR)).
destruct CORE as (_ & HPm & VFL & VSH & VSV & V112 & MC & MA & MT).
destruct CELLS as (C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C104 & C120 & C128 & C136 & C152).
destruct LOOP as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11).
refine (conj CX (conj LS (conj FRM (conj _ (conj _ (conj Hn (conj Hr (conj _ (conj HL (conj Hij (conj HjL
  (conj HSL (conj HMC (conj HFIN (VK _ _ _ NP))))))))))))))).
- refine (conj HJ' (conj HPm (conj (VK _ _ _ VFL) (conj (fun i0 Hi0 => VK _ _ _ (VSH i0 Hi0))
    (conj (fun j0 r Hr0 => VK _ _ _ (VSV j0 r Hr0)) (conj (VK _ _ _ V112) _)))))).
  rewrite HR. exact (conj MC (conj MA MT)).
- exact (conj (VK _ _ _ C24) (conj (VK _ _ _ C32) (conj (VK _ _ _ C40) (conj (VK _ _ _ C48) (conj (VK _ _ _ C56)
    (conj (VK _ _ _ C64) (conj (VK _ _ _ C72) (conj (VK _ _ _ C80) (conj (VK _ _ _ C88) (conj (VK _ _ _ C104)
    (conj (VK _ _ _ C120) (conj (VK _ _ _ C128) (conj (VK _ _ _ C136) (VK _ _ _ C152)))))))))))))).
- unfold mf_loop. rewrite HR.
  exact (conj L1 (conj L2 (conj L3 (conj L4 (conj L5 (conj L6 (conj L7 (conj L8 (conj L9 (conj L10 L11)))))))))).
Qed.
End e.
End f.
End d.
