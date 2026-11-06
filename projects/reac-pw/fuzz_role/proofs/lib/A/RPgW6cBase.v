(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the BLOCK STATEMENTS of the
   walk piece "ent_build C" of LLVMFuzzerTestOneInput (0x7ff88), ent_build's cases 6, 7 and 8 (pod.h:340-366) from
   their switch entries to the join J 0x8165c, and the small facts their proofs share. Proves no function (kind:
   segment lemma).

   ONE STATEMENT PER CASE (w6c_case_stmt c, c = 6, 7, 8): from the case entry (w6c_pc c) with the facts the
   cut rs_cut_D gives there (w6c_ctx, w6c_in_D), the run reaches J in the state lib/A/RPgW6cTail.v's w6c_jpost
   names, with the pod Model.ent_build makes of the kind byte c and the input r after it: these three cases never
   read the kind byte beyond kind % 10, so ent_build (kind :: r) = ent_build (c :: r) (w6c_build_kind).

   THE REGISTERS AT A CASE ENTRY (rs_L_D): s1 = R, s7 = SHADOW_OFF, s8 = cur (the cursor after the kind byte),
   a4 = cur - 1 (the kind byte's address), s9 = |r|; the cells [R+0] = 0x15555556 (the `% 12u` multiplier),
   [R+0xb0] = sa (the shadow address the cases reload into s4), [R+0xc0] = F + 0xf8 (e.body), [R+0xf0] = F + 0xf0 (e),
   [R+0xf8] = |r| + 1 (what was left before the kind byte); e's 104 bytes are zero (the memset 0x80ac4) and e's
   granules are in scope (rs_PJ). The two tables the cases read are registered globals of 16 bytes (RPgImgA
   hi_globs): t at 0x210e0 (case 6) and t.9 at 0x21100 (case 8). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSteps RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgW6cTail RPgW6cEng.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition W6C_D6 : Z := 0x810a8.
Definition W6C_D7 : Z := 0x80f64.
Definition W6C_D8 : Z := 0x810f8.
Definition w6c_pc (c : Z) : Z := if c =? 6 then W6C_D6 else if c =? 7 then W6C_D7 else W6C_D8.
Definition W6C_T6 : Z := 0x210e0.
Definition W6C_T8 : Z := 0x21100.

(* the pod of one turn whose kind byte reads c *)
Definition w6c_ent (c : Z) (r : list byte) : ent * list byte := ent_build (Z_to_bv 8 c :: r).

(* cases 6, 7 and 8 read the kind byte only through kind % 10 *)
Lemma w6c_build_kind : forall rr kd r, (kd, r) = Cursor.fuzz_u8 rr -> rr <> [] -> In (kd mod 10) [6; 7; 8] ->
ent_build rr = w6c_ent (kd mod 10) r.
Proof.
intros rr kd r Hf Hne Hin. destruct rr as [|b r0]; [contradiction|].
cbn [Cursor.fuzz_u8] in Hf. injection Hf as Hkd Hr. subst r0.
unfold w6c_ent, ent_build. cbn [Cursor.fuzz_u8]. rewrite <- Hkd.
cbv [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; rewrite <- E; reflexivity.
Qed.

(* ===================== dropping a region from a symbolic state ===================== *)
Lemma w6c_regions_wf_app : forall l1 l2, regions_wf (l1 ++ l2) = regions_wf l1 && regions_wf l2.
Proof. intros l1 l2. induction l1 as [|r l1 IH]; [reflexivity|]. cbn [app regions_wf]. rewrite IH, andb_assoc. reflexivity. Qed.
Lemma w6c_all_disj_drop : forall E a l1 r l2, all_disjoint E a (l1 ++ r :: l2) -> all_disjoint E a (l1 ++ l2).
Proof.
intros E a l1 r l2. induction l1 as [|x l1 IH]; cbn [app all_disjoint]; [intros [_ H]; exact H|].
intros [H1 H2]. split; [exact H1 | exact (IH H2)].
Qed.
Lemma w6c_pw_disj_drop : forall E l1 r l2, pairwise_disjoint E (l1 ++ r :: l2) -> pairwise_disjoint E (l1 ++ l2).
Proof.
intros E l1 r l2. induction l1 as [|x l1 IH]; cbn [app pairwise_disjoint]; [intros [_ H]; exact H|].
intros [H1 H2]. split; [exact (w6c_all_disj_drop E x l1 r l2 H1) | exact (IH H2)].
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma w6c_st_ok_drop : forall E pc rg l1 r l2 resv f ms,
st_ok rsegs E (mkSS pc rg (l1 ++ r :: l2) resv f) ms -> st_ok rsegs E (mkSS pc rg (l1 ++ l2) resv f) ms.
Proof.
intros E pc rg l1 r l2 resv f ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpw) & H9).
repeat (split; [assumption|]). split; [|exact H9]. cbn [ss_mem] in *.
split; [|split].
- rewrite w6c_regions_wf_app in *. cbn [regions_wf] in Hwf.
  apply andb_true_iff in Hwf as [Ha Hb]. apply andb_true_iff in Hb as [_ Hb]. rewrite Ha, Hb. reflexivity.
- apply Forall_app in Hok as [Ha Hb]. inversion Hb; subst. apply Forall_app. split; assumption.
- exact (w6c_pw_disj_drop E l1 r l2 Hpw).
Qed.
End b.

(* ===================== e's bytes from its two header words ===================== *)
Lemma w6c_le32_val : forall v, 0 <= v < 2 ^ 32 -> Z_to_le_bytes 4 v = le32 v.
Proof. reflexivity. Qed.
Lemma w6c_e_hdr : forall H m0 m1 F ty sz,
rm_bytes rsegs H m0 (F + 0xf0) (zeros 104) ->
val_mem rsegs (mrestrict H m1) (F + 0xf0) 4 ty -> val_mem rsegs (mrestrict H m1) (F + 0xf4) 4 sz ->
(forall x, F + 0xf8 <= x < F + 0x158 -> aview rsegs H m1 x = aview rsegs H m0 x) ->
rm_bytes rsegs H m1 (F + 0xf0) (le32 ty ++ le32 sz ++ zeros 96).
Proof.
intros H m0 m1 F ty sz Z0 Vt Vs K.
apply rm_bytes_app. split; [exact (rm_bytes_of_val rsegs H m1 (F + 0xf0) 4 ty Vt)|].
rewrite length_le32. apply rm_bytes_app. split.
- replace (F + 0xf0 + Z.of_nat 4) with (F + 0xf4) by lia. exact (rm_bytes_of_val rsegs H m1 (F + 0xf4) 4 sz Vs).
- rewrite length_le32. replace (F + 0xf0 + Z.of_nat 4 + Z.of_nat 4) with (F + 0xf0 + Z.of_nat 8) by lia.
  apply (rm_bytes_kept rsegs H m0 H m1).
  + replace (zeros 96) with (rm_slice (zeros 104) 8 96) by reflexivity.
    apply (rm_bytes_slice rsegs H m0 (F + 0xf0) (zeros 104) 8 96 Z0). rewrite length_zeros. lia.
  + intros x Hx. rewrite length_zeros in Hx. apply K. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6C_CPY.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6C_SET.

(* ===================== the context and the facts at a case entry ===================== *)
Definition w6c_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
w6c_geo STK sp0 own lyc R F pos /\ rom_view rsegs W memc.

Definition w6c_in_D (W : world rsegs) (memc : word -> option byte) (regs : bvmap 5 word) (R F cur sa : Z)
(r : list byte) : Prop :=
(* registers *)
getr regs 2 = w64 R /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 9 = w64 R /\ getr regs 23 = w64 SHADOW_OFF /\
getr regs 24 = w64 cur /\ getr regs 14 = w64 (cur - 1) /\ getr regs 25 = w64 (Z.of_nat (length r)) /\
(* the real frame's cells *)
val_mem rsegs (mrestrict (w_H W) memc) (R + 0) 8 0x15555556 /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 sa /\ 0 <= sa < 2 ^ 64 /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 (F + 0xf8) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 (F + 0xf0) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (Z.of_nat (length r) + 1) /\
(* e and its granules *)
rm_bytes rsegs (w_H W) memc (F + 0xf0) (zeros 104) /\
rl_fsh rsegs (w_H W) memc F rs_PJ /\
(* the input after the kind byte *)
rm_bytes rsegs (w_H W) memc cur r /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur (Z.of_nat (length r)) /\
(0 < Z.of_nat (length r) -> shadow_hull_vis (aview rsegs (w_H W) memc) cur (Z.of_nat (length r))) /\
amem_range cur (Z.of_nat (length r)) /\ 1 <= cur /\ cur + Z.of_nat (length r) <= 2 ^ 47 - 1 /\
(forall a, cur <= a < cur + Z.of_nat (length r) ->
 ~ (R - T_SEG_STK <= a < R + 0x138) /\ ~ (F + 0x20 <= a < F + 0x180)) /\
(* the two tables, and the frame apart from them *)
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6C_T6 16 /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6C_T8 16 /\
(forall a, W6C_T6 <= a < W6C_T8 + 16 -> ~ (F <= a < F + 512)).

(* ===================== the three cases, entry -> J ===================== *)
Definition w6c_case_stmt (c : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur sa : Z) (r : list byte),
w6c_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in_D W memc regs R F cur sa r ->
SRr rsegs W (cfg_at rsegs (w6c_pc c) regs memc mdc)
(w6c_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F
 (fst (w6c_ent c r)) (cur + Z.of_nat (length r - length (snd (w6c_ent c r))))
 (Z.of_nat (length (snd (w6c_ent c r)))) sa).
Definition w6c_case6_stmt : Prop := w6c_case_stmt 6.
Definition w6c_case7_stmt : Prop := w6c_case_stmt 7.
Definition w6c_case8_stmt : Prop := w6c_case_stmt 8.

(* the frame's bytes are present: e's region and the cells' window may be written *)
Lemma w6c_present : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos,
w6c_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
(forall o, 0 <= o < 512 -> apresent (w_H W) memc (F + o)) /\
(forall a, R <= a < R + 0x1a0 -> apresent (w_H W) memc a).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos (HJ & (HR16 & HSTK & HRS & HRk & Hown & HF & HFapp & HF32) & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ (AR_laws_ok rsegs B) lyc Sc W memc mdc 3 pos HAR Hin3) as (_ & _ & HFp & _).
rewrite <- HF in HFp. change (fs_frame_bytes 3) with 512 in HFp.
split; [intros o Ho; exact (proj1 (HFp (F + o) ltac:(lia)))|]. intros a Ha. apply Hpres. unfold T_SEG_STK, ASTACK in *. lia.
Qed.
End d.
End c.
