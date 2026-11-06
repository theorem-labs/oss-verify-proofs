(* Segment F of check_text_scribble's walk in image B (fuzz_codec.asan-ubsan 0x83dbc): bs_seg_F of
   check_text_scribble_B_inv.v, one byte of the inlined fuzz_all over the record's bytes [n, 24) at 0x84098: the
   UBSan check of (ch + n) + j (0x84098, decided from the facts of a3 and a1), the instrumented check of the byte (its
   shadow entry, the record marked usable), the byte itself 0xa5 (the record holds scribble_bytes), so the abort at
   0x840b4 is not reached (a4 = 0xa5 pinned), j + 1, and 0x840bc beq a2,a1: taken to the release 0x8403c, not taken
   back to the head. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_base check_text_scribble_B_lst.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the record's bytes past the text: 0xa5 ---------------------------------------------------------------------- *)
Lemma bsf_owe_len : forall k t, length (fst (scr_owe t k)) = k.
Proof.
induction k as [|k IH]; intros t; [rewrite bs_scr_0; reflexivity|].
destruct t as [|x t']; cbn [scr_owe]; [cbn [fst]; apply repeat_length|].
destruct (x =? 0); [cbn [fst]; apply repeat_length|].
cbv iota.
match goal with |- context [if ?c then _ else _] => destruct c end.
- destruct (scr_owe (tl t') k) as [o u] eqn:E. cbn [fst length]. specialize (IH (tl t')). rewrite E in IH.
  cbn [fst] in IH. lia.
- destruct (scr_owe t' k) as [o u] eqn:E. cbn [fst length]. specialize (IH t'). rewrite E in IH. cbn [fst] in IH. lia.
Qed.
Lemma bsf_nth_repeat : forall k i (x d : Z), (i < k)%nat -> nth i (repeat x k) d = x.
Proof. induction k as [|k IH]; intros i x d Hi; [lia|]. destruct i; cbn; [reflexivity|]. apply IH. lia. Qed.
Lemma bsf_sb_nth : forall tb n j, 0 <= n <= 8 -> 0 <= j < 24 - n ->
  nth (Z.to_nat (n + j)) (scribble_bytes tb n) 0 = 165.
Proof.
intros tb n j Hn Hj. unfold scribble_bytes, owed_scribble_text_spec.
rewrite app_nth2 by (rewrite bsf_owe_len; lia). rewrite bsf_owe_len. apply bsf_nth_repeat. lia.
Qed.

(* the state at the head: the record's byte n + j at atom 33 (the extras put it there), a read-only 0xa5; s7 = SB,
   a4 = 0xa5 *)
Definition bsf_G : facts :=
  mkFacts [(32%nat, mkAF SB SB 0); (33%nat, mkAF 1 (2 ^ 47 - 2) 0); (11%nat, mkAF 0 23 0); (12%nat, mkAF 16 24 0);
           (13%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0)] []
    [(SAlu ALU_ADD (SOff 20 0) (SOff 11 0), SOff 33 0)].
Definition bsf_rec : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 165))].
Definition bsf_sr : list sv := sr_set (sr_set sr_atoms 23%bv (SOff 32 0)) 14%bv (SLit 165).

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).

Lemma bsf_state : forall (regs2 : bvmap 5 word) (W2 : world tfibsegs) mem2 c j n,
  getr regs2 23 = w64 SB -> getr regs2 14 = w64 165 -> getr regs2 20 = w64 c -> getr regs2 11 = w64 j ->
  getr regs2 12 = w64 (24 - n) -> getr regs2 13 = w64 (bnot c) ->
  1 <= c -> c + (24 - n) <= 2 ^ 47 - 1 -> 0 <= n <= 8 -> 0 <= j < 24 - n ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) (c + j) 1 165 ->
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (c + j) 1 -> amem_range (c + j) 1 ->
  st_ok tfibsegs (Ereg regs2 (cw_extra [c + j])) (mkSS PC_F bsf_sr [bsf_rec] None bsf_G)
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_F) mem2 (seg_rom tfibsegs))) /\
  sh_ok tfibsegs CW_Bx [mkSHE 33 0 1] (Ereg regs2 (cw_extra [c + j])) (mrestrict (w_H W2) mem2).
Proof.
intros regs2 W2 mem2 c j n R23 R14 R20 R11 R12 R13 Hc0 Hc1 Hn Hj V Hra Ham.
set (E := Ereg regs2 (cw_extra [c + j])).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 (c + j)) by (subst E; exact (cw_ew_x regs2 [c + j] 0)).
assert (E20 : ew E 20 = Z_to_bv 64 c) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E11 : ew E 11 = Z_to_bv 64 j) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E12 : ew E 12 = Z_to_bv 64 (24 - n)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (E13 : ew E 13 = Z_to_bv 64 (bnot c)) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (U32 : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (U33 : bv_unsigned (ew E 33) = c + j) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = j) by (rewrite E11; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = 24 - n) by (rewrite E12; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew E 13) = bnot c) by (rewrite E13; apply unsigned_lit_small; unfold bnot; lia).
split.
- rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs2 (cw_extra [c + j])) with E.
  + unfold bsf_sr. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx0; discriminate Hx0 |]
      | intros Hx0; discriminate Hx0 |].
    all: first [ rewrite R23, sv_denot_SOff0, E32; reflexivity | rewrite R14; reflexivity ].
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, bsf_rec. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U33. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs E _ (c + j) 0 1 (SLit 165) 165); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact V.
  + apply pairwise_disjoint_of_extents. unfold bsf_rec, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + split; [|split; [exact I|]].
    * unfold bsf_G. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U32, U33, U11, U12, U13. rewrite Z.pow_0_r, !Z.mod_1_r.
      unfold bnot, SB. repeat (split; [repeat split; lia|]). exact I.
    * unfold bsf_G. cbn [f_alias alias_ok]. split; [|exact I].
      rewrite (bsl_den_add E 20 11 c j 0 E20 E11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)), Z.add_0_r.
      cbn [sv_denot]. rewrite U33, Z.add_0_r. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  exact (cw_shent_ra W2 mem2 E 33 (c + j) 1 Hra Ham ltac:(lia) ltac:(lia) ltac:(lia) E33 E32).
Qed.

Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem bs_f_holds : bs_seg_F B MT.
Proof.
unfold bs_seg_F. intros g pos fuel W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (j & R11 & R20 & R12 & R13 & R14 & Hj & Hfuel & Hrec).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R18 & R24 & R22 & R23 & R25 & R19 & R21 & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & (Hch0 & Hchn & _ & _ & _ & _ & Hcham & _) & _ & _ & _ & Hn & _).
specialize (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as (_ & Hchra & _).
assert (Hlen : bs_ch g + 24 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemEnd in Hcham; lia).
assert (V : val_mem tfibsegs (mrestrict (w_H W2) mem2) (bs_ch g + bs_n g + j) 1 165).
{ destruct (Hrec (Z.to_nat (bs_n g + j))) as (Vb & _).
  - unfold scribble_bytes, owed_scribble_text_spec. rewrite length_app, repeat_length, bsf_owe_len. lia.
  - rewrite bsf_sb_nth in Vb by lia. rewrite Z2Nat.id in Vb by lia. replace (bs_ch g + bs_n g + j) with
      (bs_ch g + (bs_n g + j)) by lia. exact Vb. }
assert (Hra : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (bs_ch g + bs_n g + j) 1)
  by (intros a Ha; apply Hchra; lia).
assert (Ham : amem_range (bs_ch g + bs_n g + j) 1)
  by (unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia).
destruct (bsf_state regs2 W2 mem2 (bs_ch g + bs_n g) j (bs_n g) R23 R14 R20 R11 R12 R13 ltac:(lia) ltac:(lia) Hn Hj
  V Hra Ham) as (HS & SHOK).
remember (Ereg regs2 (cw_extra [bs_ch g + bs_n g + j])) as E eqn:HEE.
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E11 : ew E 11 = w64 j) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E12 : ew E 12 = w64 (24 - bs_n g)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (E13 : ew E 13 = w64 (bnot (bs_ch g + bs_n g))) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E20 : ew E 20 = w64 (bs_ch g + bs_n g)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E23 : ew E 32 = getr regs2 23) by (subst E; rewrite cw_ew_SB; exact (eq_sym R23)).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem2 a) by (intros; assumption).
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 PC_F) with (Z_to_bv 64 PC_F).
pose proof (bs_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ0) as (_ & _ & _ & HF0 & HFc & _).
pose proof alloc_ceiling_val as Hac.
cw_run_to ltac:(cbn [ss_mem]; repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]) 0x840b0.
ctk_keep cw_kwr_ro.
cw_run_to ltac:(cbn [ss_mem]; repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]) 0x84098.
ctk_keep cw_kwr_ro.
cw_branch Hc1.
all: lazymatch type of Hc1 with context [sv_denot ?Ev _] =>
  rewrite branch_eq_U, (U_atom Ev 12 (24 - bs_n g) ltac:(ewpeel; exact E12) ltac:(lia)),
    (U_atom_off Ev 11 j 1 ltac:(ewpeel; exact E11) ltac:(lia) ltac:(lia)) in Hc1 end.
- (* the last byte: to the release *)
  apply Z.eqb_eq in Hc1.
  cw_run_to ltac:(cbn [ss_mem]; repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]) 0x8403c.
  ctk_keep cw_kwr_ro.
  apply SRr_ret. cbv beta. right.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
    apply (bs_cut_close B MT LAWS g pos PC_R (P_R g pos) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni
      Hio Hmo HC HJ);
    [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
    | bs_rfin | bs_rfin
    | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | ] end.
  apply (bs_garr8_kept (w_H W2) (w_H W2) mem2 _); [|exact Hrec].
  intros a Ha. apply KE; [|tauto]. unfold scribble_bytes, owed_scribble_text_spec in Ha. rewrite length_app, repeat_length, bsf_owe_len in Ha. lia.
- (* back to the head *)
  apply Z.eqb_neq in Hc1.
  cw_run_to ltac:(cbn [ss_mem]; repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]) 0x84098.
  ctk_keep cw_kwr_ro.
  apply SRr_ret. cbv beta. left.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
    apply (bs_cut_close B MT LAWS g pos PC_F (P_F g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni
      Hio Hmo HC HJ);
    [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
    | bs_rfin | bs_rfin
    | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | ] end.
  exists (j + 1).
  split; [rv; ewpeel; rewrite E11; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
  split; [lia|]. split; [lia|].
  apply (bs_garr8_kept (w_H W2) (w_H W2) mem2 _); [|exact Hrec].
  intros a Ha. apply KE; [|tauto]. unfold scribble_bytes, owed_scribble_text_spec in Ha. rewrite length_app, repeat_length, bsf_owe_len in Ha. lia.
Qed.
End s.
