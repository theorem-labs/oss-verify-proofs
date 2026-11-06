(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bC5.v at f3898085bda (the tail run of
   ent_build's case 5 and the chaining of its head, its __asan_memcpy call and its tail) for reac-pw/fuzz_headamp's
   image B: image B's own code and registers, its pointer-overflow test before the NUL store (decided from atom 34's
   interval), the call step cb_memcpy_at of lib/AU/HPgCaseB.v at __asan_memcpy 0x51d8c, the block post of
   lib/AU/HPgSteps.v (hdu_blk_postE) and the join's post pieces of lib/AU/HPgCaseBJ.v (cj_wr, cj_J_R). *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded bytes there equal the pin's):
   the block lemma hw6b_c5 of lib/AU/HPgW6bBase.v, case 5 of ent_build's `switch (kind % 10)` (pod.h:336-337,
   ent_text pod.h:209-219) inside LLVMFuzzerTestOneInput (0x80c40), from the case entry 0x81e6c to the join
   J 0x82618. Proves no function (kind: segment lemma).

   THE TAIL (0x81ec8 .. J; registers as the head leaves them: s1 = R, s2 = the memcpy source, s4 = n, s5 = F + 0x218
   = &e62.body, s7 = the kind byte sign-extended, s10 = what was left after the count byte):
     0x81ec8  mv a0,s4; bltz s7 -> 0x81ee8                 kind & 0x80: no NUL
     0x81ed0  ld a0,0xe8(s1) / bgeu a0,s4 -> 0x81edc       the NUL's pointer-overflow test (else `unimp` 0x83a14)
     0x81edc  add a1,s5,s4; a0 := s4 + 1; sb zero,0(a1)    the NUL at e62.body + n (no instrumented check)
     0x81ee8  a3 := s2 + s4; t1 := s10 - s4; s4 := [R+0x130] (= &e62); sw 8,0(s4); sw a0,4(s4);
              s7 := [R+0x148] (= pp); j 0x82614, which loads s2 := [R+0x138] (= pp + 0x4000) and falls into J.
   The real-frame cells the tail reads: [R+0xe8] (the complement the test compares against), [R+0x130], [R+0x138],
   [R+0x148]; the bytes it writes: e62.type and e62.size at F+0x210, and the NUL at F + 0x218 + n. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgSteps HPgCaseBJ.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgCaseB HPgW6bBase HPgW6bC5a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== the tail's entry state ========================================
   [R+0xe8] = atom 34, [R+0x130] = F + 0x210, [R+0x138] = pp + 0x4000, [R+0x148] = pp, read only; e62.type and
   e62.size at F + 0x210, written; the byte e62.body + n, zero, written. s5 + s4 is atom 35 by an alias fact. *)
Definition hc5_tR : YP09.region := YP09.mkRegion (Some 9%nat) 0xe8 0x150 0 0
  [YP09.mkChunk 0xe8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x130 (CVal 8 (SOff 32 0x210));
   YP09.mkChunk 0x138 (CVal 8 (SOff 33 0x4000)); YP09.mkChunk 0x148 (CVal 8 (SOff 33 0))].
Definition hc5_tE : YP09.region := YP09.mkRegion (Some 32%nat) 0x210 0x218 0x210 0x218 [].
Definition hc5_tN : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 1 [YP09.mkChunk 0 (CZero 1)].
Definition hc5_tfacts : facts :=
  mkFacts [(20%nat, mkAF 0 31 0); (34%nat, mkAF HB_E8LO HB_E8HI 0)] []
          [(SAlu ALU_ADD (SOff 21 0) (SOff 20 0), SOff 35 0)].
Definition ss_c5T : sstate := mkSS HC5_RET sr_atoms [hc5_tR; hc5_tE; hc5_tN] None hc5_tfacts.
Definition hc5_textra (F pp e8 nul : Z) : list word :=
  [Z_to_bv 64 F; Z_to_bv 64 pp; Z_to_bv 64 e8; Z_to_bv 64 nul].
(* the tail's write set: e62.type / e62.size and the NUL byte *)
Definition hc5_TWr (F n : Z) : Z -> Prop :=
  fun a => (F + 0x210 <= a < F + 0x218) \/ (F + 0x218 + n <= a < F + 0x218 + n + 1).
Definition hc5_tclob : list (bv 5) := [6; 10; 11; 13; 18; 20; 23]%bv.

(* the leaf of a tail run: the engine's last state at the join gives the block post *)
Ltac hc5_tleaf HAE KE MTLh :=
  apply SRr_ret; unfold hdu_blk_postE; do 5 eexists;
  lazymatch goal with
  | HS : st_ok _ _ _ (restrict (w_H ?Wx) _) |- _ =>
    split; [rewrite (st_ok_restrict_mkst rsegs (w_H Wx) _ _ _ HS eq_refl) at 1; reflexivity|];
    lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => split; [exact HJx|] end;
    split; [eapply (regs_kept_of_st_ok rsegs _ _ _ _ _ (w_H Wx) hc5_tclob);
            [exact HS | env_agree_chain HAE | vm_compute; reflexivity]|];
    split; [reflexivity|]; split; [apply Permutation_refl|]; split; [cb_kio|];
    split; [apply mo_le_refl; exact MTLh|]; split; [exact KE|]
  end.

(* every nonzero register outside hw6b_clob is callee-saved (checked over the 31 registers) *)
Definition hc5_cs_b (z : Z) : bool :=
  (z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)).
Lemma hc5_cs_check :
  forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) hw6b_clob || hc5_cs_b (bv_unsigned r)) nz_regs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hc5_cs : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hw6b_clob -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) hc5_cs_check r (in_nz_regs r Hr0)) as Hq. cbv beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply Hn. apply existsb_exists in Hq as (c0 & Hc & Hb). apply bv_eqb_eq in Hb. subst c0. exact Hc.
- unfold hc5_cs_b in Hq. unfold acallee_saved.
  repeat rewrite orb_true_iff in Hq. rewrite andb_true_iff, ?Z.eqb_eq, ?Z.leb_le in Hq. lia.
Qed.
Lemma hc5_reg_cs : forall (regs1 regs2 : bvmap 5 word) (r : bv 5), aregs_preserved regs1 regs2 ->
  acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs1 r.
Proof. intros regs1 regs2 r HP Hr. pose proof (HP _ Hr) as X. rewrite !Z_to_bv_bv_unsigned in X. exact X. Qed.
(* the two memory facts of a kept range, with the world free on each side *)
Lemma hc5_hullk : forall (H H' : word -> bool) m m' x n,
  shadow_hull_vis (aview rsegs H m) x n ->
  (forall a, cb_hull x n a -> aview rsegs H' m' a = aview rsegs H m a) ->
  shadow_hull_vis (aview rsegs H' m') x n.
Proof. intros H H' m m' x n HV HK s Hs. rewrite HK by exact Hs. exact (HV s Hs). Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma hc5_T_wr : forall E rs F n, YP09.skeleton rs = YP09.skeleton [hc5_tR; hc5_tE; hc5_tN] ->
  bv_unsigned (ew E 32) = F -> bv_unsigned (ew E 35) = F + 0x218 + n ->
  forall a, in_wrange E rs a -> hc5_TWr F n a.
Proof.
intros E rs F n Hsk H32 H35 a Ha. apply (in_wrange_skeleton E rs _ a Hsk) in Ha.
destruct Ha as (r & Hin & Ha). unfold hc5_TWr. cbn [In] in Hin.
repeat destruct Hin as [<-|Hin]; try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hc5_tR hc5_tE hc5_tN] in Ha; rewrite ?H32, ?H35 in Ha; lia.
Qed.
Section d0.
Variable B : asyms.
Lemma hc5_T_awr : forall E rs STK sp0 FP bl0 blc lyc own F pos n,
  YP09.skeleton rs = YP09.skeleton [hc5_tR; hc5_tE; hc5_tN] ->
  bv_unsigned (ew E 32) = F -> bv_unsigned (ew E 35) = F + 0x218 + n -> 0 <= n <= 31 ->
  In (4, pos) own -> F = frame_addr lyc 4 pos ->
  awr_ok E rs STK sp0 FP bl0 blc lyc own.
Proof.
intros E rs STK sp0 FP bl0 blc lyc own F pos n Hsk H32 H35 Hn Hown HF a Ha.
apply (in_wrange_skeleton E rs _ a Hsk) in Ha.
destruct Ha as (r & Hin & Ha). unfold awr_byte. cbn [In] in Hin.
repeat destruct Hin as [<-|Hin]; try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hc5_tR hc5_tE hc5_tN] in Ha; rewrite ?H32, ?H35 in Ha;
  first [ lia
        | right; right; right; exists 4, pos; split; [exact Hown|]; left;
          unfold in_zr; cbn [fst snd]; rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia ].
Qed.
End d0.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis MCPY : aintrin_realizes rsegs B OCpy HB_MEMCPY.

(* ======================================== the tail: 0x81ec8 .. J ======================================== *)
Lemma hc5_tail : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pos src lf pp kd n : Z) (p : list byte),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  R + 0x220 <= sp0 -> sp0 - STK <= R - 16384 -> In (4, pos) own -> F = frame_addr lyc 4 pos ->
  4096 <= F -> F + 1024 <= alloc_ceiling -> alloc_ceiling + 16384 <= R -> R + 0x220 <= 2 ^ 47 ->
  n = Z.of_nat (length p) -> (length p <= 31)%nat ->
  getr regs 9 = w64 R -> getr regs 18 = w64 src -> getr regs 20 = w64 n -> getr regs 21 = w64 (F + 0x218) ->
  getr regs 23 = w64 (hc5_kds kd) -> getr regs 26 = w64 lf ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 ((- (F + 0x219)) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
  0 <= kd < 256 -> 0 <= pp -> pp + 0x4000 < 2 ^ 64 -> 0 <= src -> src + n < 2 ^ 64 -> n <= lf < 2 ^ 64 ->
  hm_bytes rsegs (w_H W) memc (F + 0x218) p ->
  (forall i, 0 <= i < 96 - n -> aview rsegs (w_H W) memc (F + 0x218 + n + i) = Some 0) ->
  (forall o, 0 <= o < 1024 -> apresent (w_H W) memc (F + o)) ->
  SRr rsegs W (cfg_at rsegs HC5_RET regs memc mdc)
  (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc HB_J hc5_tclob (hc5_TWr F n)
    (fun W2 regs2 mem2 => getr regs2 13 = w64 (src + n) /\ getr regs2 6 = w64 (lf - n) /\
       getr regs2 18 = w64 (pp + 0x4000) /\ getr regs2 20 = w64 (F + 0x210) /\ getr regs2 23 = w64 pp /\
       hm_bytes rsegs (w_H W2) mem2 (F + 0x210)
         (le32 8 ++ le32 (n + (if Z.testbit kd 7 then 0 else 1)) ++ p ++ zeros (96 - length p)))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos src lf pp kd n p
  HJ HRsp HspR Hown HF HF4 HFc HRc HRb2 Hneq Hpl H9 H18 H20 H21 H23 H26 Ve8 V130 V138 V148
  Hkd Hpp Hppb Hsrc Hsrcn Hlf Bp Hz Hpres.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (@asan_consts rc) as (Hac & _).
pose proof (hb_e8_range F HF4 HFc) as He8.
assert (Hn : 0 <= n <= 31) by lia.
set (e8 := (- (F + 0x219)) mod 2 ^ 64) in *.
remember (Ereg regs (hc5_textra F pp e8 (F + 0x218 + n))) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (hc5_textra F pp e8 (F + 0x218 + n))) E) by (subst E; apply env_agree_refl).
assert (U9 : bv_unsigned (ew E 9) = R) by (subst E; exact (hb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
assert (E18 : ew E 18 = Z_to_bv 64 src) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E20 : ew E 20 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E21 : ew E 21 = Z_to_bv 64 (F + 0x218))
  by (subst E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E23 : ew E 23 = Z_to_bv 64 (hc5_kds kd))
  by (subst E; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (E26 : ew E 26 = Z_to_bv 64 lf) by (subst E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 e8) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (F + 0x218 + n)) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (U20 : bv_unsigned (ew E 20) = n) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = e8)
  by (rewrite E34; apply unsigned_lit_small; unfold HB_E8LO, HB_E8HI in He8; lia).
assert (U35 : bv_unsigned (ew E 35) = F + 0x218 + n) by (rewrite E35; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E ss_c5T (restrict (w_H W) (mkst regs (Z_to_bv 64 HC5_RET) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_c5T. rewrite HE. apply (entry_st_ok_full rsegs); try rewrite <- HE.
  - rewrite HE. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold hc5_tR. apply (hm_ro_region rsegs _ _ _ 9%nat R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * apply (chunk_ok_val rsegs _ _ _ _ _ _ e8);
          [apply hc5_den0; [exact E34 | unfold HB_E8LO, HB_E8HI in He8; lia]
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold HB_E8LO, HB_E8HI in He8; lia | cbn; lia | exact Ve8].
      * apply (chunk_ok_val rsegs _ _ _ _ _ _ (F + 0x210));
          [apply hc5_den_off; [exact E32 | lia | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
          | exact V130].
      * apply (chunk_ok_val rsegs _ _ _ _ _ _ (pp + 0x4000));
          [apply hc5_den_off; [exact E33 | lia | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
          | exact V138].
      * apply (chunk_ok_val rsegs _ _ _ _ _ _ pp);
          [apply hc5_den0; [exact E33 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V148].
    + unfold hc5_tE. apply (hm_rw_region rsegs _ _ _ 32%nat F); [exact U32 | lia | lia | | apply Forall_nil].
      intros o Ho. apply Hpres. lia.
    + unfold hc5_tN. apply (hm_rw_region rsegs _ _ _ 35%nat (F + 0x218 + n)); [exact U35 | lia | lia | |].
      * intros o Ho. replace (F + 0x218 + n + o) with (F + (0x218 + n + o)) by lia. apply Hpres. lia.
      * apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi.
        apply (hm_aview_mbyte rsegs). replace (F + 0x218 + n + 0 + i) with (F + 0x218 + n + 0) by lia.
        exact (Hz 0 ltac:(lia)).
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val hc5_tR hc5_tE hc5_tN]. rewrite U9, U32, U35.
    repeat split; lia.
  - unfold facts_ok. cbn [hc5_tfacts f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U34.
      unfold HB_E8LO, HB_E8HI in He8 |- *.
      repeat split; try lia; (change (2 ^ 0) with 1; apply Z.mod_1_r).
    + split; [|exact I].
      rewrite (hc5_den_add E 21 20 (F + 0x218) n E21 E20) by lia.
      rewrite (hc5_den0 E 35 _ E35) by lia. reflexivity. }
clear HE.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ hc5_TWr F n a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by reflexivity.
unfold cfg_at. change (w64 HC5_RET) with (Z_to_bv 64 HC5_RET).
(* 0x81ec8 .. the `bltz s7` at 0x81ecc *)
aj_run_to hb_tbl_ok HS HJ HB_J.
{ apply (hc5_T_awr _ _ _ _ _ _ _ _ _ F pos n); [vm_compute; reflexivity | exact U32 | exact U35 | lia
    | exact Hown | exact HF]. }
hc5_keep (hc5_TWr F n) ltac:(apply (hc5_T_wr _ _ F n); [vm_compute; reflexivity
  | rewrite ?ew_ewset_other by lia; exact U32 | rewrite ?ew_ewset_other by lia; exact U35]).
srr_branch_with hb_tbl_ok HS.
{ (* kind & 0x80: no NUL, e62.size = n *)
  rewrite (hc5_bltz E kd E23 Hkd) in Hc.
  aj_run_to hb_tbl_ok HS HJ HB_J.
  { apply (hc5_T_awr _ _ _ _ _ _ _ _ _ F pos n); [vm_compute; reflexivity | exact U32 | exact U35 | lia
      | exact Hown | exact HF]. }
  hc5_keep (hc5_TWr F n) ltac:(apply (hc5_T_wr _ _ F n); [vm_compute; reflexivity
    | rewrite ?ew_ewset_other by lia; exact U32 | rewrite ?ew_ewset_other by lia; exact U35]).
  hc5_tleaf HAE KE MTL.
  cbv beta. rewrite Hc.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  { hc5_reg HS (13%bv : bv 5). unfold w64. apply hc5_den_add; [exact E18 | exact E20 | lia | lia | lia]. }
  { hc5_reg HS (6%bv : bv 5). unfold w64. apply hc5_den_sub; [exact E20 | exact E26 | lia | lia]. }
  { hc5_reg HS (18%bv : bv 5). unfold w64. apply hc5_den_off; [exact E33 | lia | lia]. }
  { hc5_reg HS (20%bv : bv 5). unfold w64. apply hc5_den_off; [exact E32 | lia | lia]. }
  { hc5_reg HS (23%bv : bv 5). unfold w64. apply hc5_den0; [exact E33 | lia]. }
  hc5_rnth HS 1%nat Hr1. hc5_rnth HS 2%nat Hr2. rewrite Z.add_0_r.
  apply (hc5_e_bytes _ _ F p n n); [exact Hneq | lia | | | |].
  { pose proof (hb_chunk_val _ _ _ 0x210 4 (SLit 8) 8 Hr1 ltac:(hc5_in)
      (hc5_den_lit _ 8 ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
    cbn [YP09.r_base base_val] in V. rewrite U32 in V. exact V. }
  { pose proof (hb_chunk_val _ _ _ 0x214 4 (SOff 20 0) n Hr1 ltac:(hc5_in)
      (hc5_den0 _ 20 n E20 ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
    cbn [YP09.r_base base_val] in V. rewrite U32 in V. exact V. }
  { apply (hm_bytes_kept rsegs (w_H W) memc); [exact Bp|]. intros x Hx. apply KE; [lia|].
    unfold hc5_TWr. lia. }
  { intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
    - pose proof (hb_chunk_zero _ _ _ 0 1 Hr2 ltac:(hc5_in) 0 ltac:(lia)) as Z0.
      cbn [YP09.r_base base_val] in Z0. rewrite U35 in Z0.
      apply hc5_aview0. replace (F + 0x218 + n + 0) with (F + 0x218 + n + 0 + 0) by lia. exact Z0.
    - rewrite KE by (unfold hc5_TWr; lia). exact (Hz i Hi). } }
(* the NUL at e62.body + n, e62.size = n + 1 *)
rewrite (hc5_bltz E kd E23 Hkd) in Hc.
aj_run_to hb_tbl_ok HS HJ HB_J.
{ apply (hc5_T_awr _ _ _ _ _ _ _ _ _ F pos n); [vm_compute; reflexivity | exact U32 | exact U35 | lia
    | exact Hown | exact HF]. }
hc5_keep (hc5_TWr F n) ltac:(apply (hc5_T_wr _ _ F n); [vm_compute; reflexivity
  | rewrite ?ew_ewset_other by lia; exact U32 | rewrite ?ew_ewset_other by lia; exact U35]).
hc5_tleaf HAE KE MTL.
cbv beta. rewrite Hc.
refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
{ hc5_reg HS (13%bv : bv 5). unfold w64. apply hc5_den_add; [exact E18 | exact E20 | lia | lia | lia]. }
{ hc5_reg HS (6%bv : bv 5). unfold w64. apply hc5_den_sub; [exact E20 | exact E26 | lia | lia]. }
{ hc5_reg HS (18%bv : bv 5). unfold w64. apply hc5_den_off; [exact E33 | lia | lia]. }
{ hc5_reg HS (20%bv : bv 5). unfold w64. apply hc5_den_off; [exact E32 | lia | lia]. }
{ hc5_reg HS (23%bv : bv 5). unfold w64. apply hc5_den0; [exact E33 | lia]. }
hc5_rnth HS 1%nat Hr1. hc5_rnth HS 2%nat Hr2.
apply (hc5_e_bytes _ _ F p n (n + 1)); [exact Hneq | lia | | | |].
{ pose proof (hb_chunk_val _ _ _ 0x210 4 (SLit 8) 8 Hr1 ltac:(hc5_in)
    (hc5_den_lit _ 8 ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  cbn [YP09.r_base base_val] in V. rewrite U32 in V. exact V. }
{ pose proof (hb_chunk_val _ _ _ 0x214 4 (SOff 20 1) (n + 1) Hr1 ltac:(hc5_in)
    (hc5_den_off _ 20 n 1 E20 ltac:(lia) ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  cbn [YP09.r_base base_val] in V. rewrite U32 in V. exact V. }
{ apply (hm_bytes_kept rsegs (w_H W) memc); [exact Bp|]. intros x Hx. apply KE; [lia|].
  unfold hc5_TWr. lia. }
{ intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
  - pose proof (hb_chunk_val _ _ _ 0 1 (SLit 0) 0 Hr2 ltac:(hc5_in)
      (hc5_den_lit _ 0 ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
    cbn [YP09.r_base base_val] in V. rewrite U35 in V. rewrite Z.add_0_r in V.
    apply (hm_val1_aview rsegs); [replace (F + 0x218 + n + 0) with (F + 0x218 + n) by lia; exact V | lia].
  - rewrite KE by (unfold hc5_TWr; lia). exact (Hz i Hi). }
Qed.

(* ======================================== the block lemma ======================================== *)
Theorem hw6b_c5 : hw6b_c5_stmt B MT.
Proof.
unfold hw6b_c5_stmt, hw6b_case_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp b r Hctx Hkd5 Hin _.
cbv beta in Hkd5.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof (hc5_head B MT MTL STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp
  (bv_unsigned b) r Hctx Hkd5 Hin) as HH.
destruct Hctx as (HJ & HR32 & HRsp & HspR & Hown & HF & Hrom).
destruct Hin as (H2 & H3 & H4 & H9 & H27 & H18 & H17 & H6 & H20 & H16 & H13 & V40 & Ve8 & V118 & V130 & V138 & V148 &
  (Hkd0 & Hkd1) & Hpp & Hppc & HF4 & HFc & HF32 & HRc & Hpres & Ez & Hrae & Hhe & Hc1 & Hwin & Hhin & Hdis).
destruct Hwin as (Hg & Hrain & Hc0 & Hcr & Ham & Hdr).
specialize (H13 ltac:(lia)).
pose proof HJ as (HAR & Hly0 & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres2 & Hstk & _).
pose proof Hstk as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _). clear Hstk.
pose proof (@asan_consts rc) as (Hac & _).
unfold T_SEG_STK, ASTACK in HspR, HRc, Hdr.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & HFapp & _ & _).
rewrite <- HF in HFapp. change (fs_frame_bytes 4) with 1024 in HFapp.
assert (HFlo : F + 1024 <= 0x7fff7000 \/ (0x10007fff8000 <= F /\ F + 1024 <= alloc_ceiling)).
{ pose proof HFapp as X. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in X. lia. }
assert (HRb1 : alloc_ceiling <= R) by lia.
assert (HRb2 : R + 0x220 <= 2 ^ 47) by lia.
assert (HR16 : R mod 16 = 0).
{ pose proof (Z.div_mod R 32 ltac:(lia)) as Em. rewrite HR32, Z.add_0_r in Em. rewrite Em.
  replace (32 * (R / 32)) with (2 * (R / 32) * 16) by ring. apply Z.mod_mul. lia. }
assert (Hcb : c + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (pose proof Ham as X; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in X; lia).
assert (Hppb : pp + 0x4000 < 2 ^ 64) by (unfold Layout.PP_SIZE in Hppc; lia).
remember (hc5_src c r) as src eqn:Hsrc_eq. remember (hc5_n r) as n eqn:Hn_eq. remember (hc5_left r) as lf eqn:Hlf_eq.
destruct (hc5_bounds c r) as (Bs1 & Bs2 & Bs3 & Bs4 & Bs5 & Bs6 & Bs7).
rewrite <- Hsrc_eq in Bs1, Bs2, Bs5. rewrite <- Hn_eq in Bs2, Bs3, Bs4, Bs7. rewrite <- Hlf_eq in Bs4, Bs5.
(* the shadow band lies apart from every byte the block writes *)
assert (Hband : forall a, 0x7fff8000 <= a < 0x10007fff8000 ->
  ~ hc5_HWr R F a /\ ~ (R - ESTACK <= a < R) /\ ~ (F + 0x218 <= a < F + 0x218 + n) /\ ~ hc5_TWr F n a).
{ intros a Ha. unfold hc5_HWr, hc5_TWr, ESTACK. lia. }
(* every byte the block writes lies in the join's write set *)
assert (Hwr : forall a, hc5_HWr R F a \/ (R - ESTACK <= a < R) \/ hc5_TWr F n a \/ (F + 0x218 <= a < F + 0x218 + n) ->
  cj_wr R F hw6b_ws a).
{ intros a Hx. unfold cj_wr, hw6b_ws, HSU_E62, T_SEG_STK, ASTACK, ESTACK in *. unfold hc5_HWr, hc5_TWr in Hx.
  destruct Hx as [[X|[X|X]]|[X|[[X|X]|X]]].
  - right; left; apply Exists_cons_hd; lia.
  - right; left; apply Exists_cons_tl; apply Exists_cons_hd; lia.
  - right; right; lia.
  - left; lia.
  - right; right; lia.
  - right; right; lia.
  - right; right; lia. }
assert (Hpin : hm_bytes rsegs (w_H W) memc src (hc5_p r)).
{ rewrite Hsrc_eq. exact (hc5_input_bytes (w_H W) memc c r Hg). }
(* ---- 0x81e6c .. the call ---- *)
eapply SRr_bind; [exact HH|]. clear HH.
intros W1 c1 Hw1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hk1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 & HR1).
destruct HR1 as (R1 & R10 & R11 & R12 & R18 & R20 & R21 & R23 & R26 & Rez).
rewrite <- Hsrc_eq in R11, R18. rewrite <- Hn_eq in R12, R20. rewrite <- Hlf_eq in R26.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ hc5_HWr R F a -> aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a)
  by exact Hm1.
clear Hm1.
assert (Hin1 : forall x, c <= x < c + Z.of_nat (length r) -> ~ hc5_HWr R F x).
{ intros x Hx. pose proof (Hdr x Hx). pose proof (Hdis x Hx). unfold hc5_HWr. lia. }
assert (Hp1' : hm_bytes rsegs (w_H W1) mem1 src (hc5_p r)).
{ apply (hm_bytes_kept rsegs (w_H W) memc); [exact Hpin|]. intros x Hx. rewrite <- Bs7 in Hx.
  apply K1; [lia | apply Hin1; lia]. }
assert (Hsp1 : getr regs1 2 = w64 R).
{ transitivity (getr regs 2); [apply Hk1; [apply cb_nz; reflexivity | apply cb_notin; reflexivity]|]. exact H2. }
assert (Hgp1 : getr regs1 3 = w64 (as_gp B)).
{ transitivity (getr regs 3); [apply Hk1; [apply cb_nz; reflexivity | apply cb_notin; reflexivity]|]. exact H3. }
assert (Htp1 : getr regs1 4 = w64 (as_tp B)).
{ transitivity (getr regs 4); [apply Hk1; [apply cb_nz; reflexivity | apply cb_notin; reflexivity]|]. exact H4. }
pose proof HJ1 as (_ & Hly1 & _).
assert (HF1 : F = frame_addr ly1 4 pos).
{ rewrite (cj_frame_addr_le _ ly ly1 4 pos Hly1), HF. exact (cj_frame_addr_le _ ly lyc 4 pos Hly0). }
(* ---- __asan_memcpy(e62.body, src, n) ---- *)
eapply SRr_bind.
{ apply (cb_memcpy_at B HB_MEMCPY MCPY W1 regs1 mem1 STK sp0 FP ly S W0 mem0 md0 own ly1 S1 md1 k
    (F + 0x218) src n (R - sp0) (w64 HC5_RET) HJ1 R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite Hsp1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, HR16, Hsp0al. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - exact Hgp1.
  - exact Htp1.
  - exact R1.
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha. split.
    + unfold awr_byte. right; right; right. exists 4, pos. split; [exact Hown|]. left.
      unfold in_zr. cbn [fst snd]. rewrite <- HF1. change (fs_frame_bytes 4) with 1024. lia.
    + unfold ESTACK. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - apply (hm_ra_kept rsegs (w_H W) memc); [apply (ra_sub _ _ (F + 0x210) 104); [exact Hrae | lia | lia]|].
    intros x Hx. pose proof (hc5_band_ra x ltac:(lia)) as Hb.
    apply K1; [lia | exact (proj1 (Hband _ Hb))].
  - intros Hn0. apply (hc5_hullk (w_H W) (w_H W1) memc mem1);
      [apply (hm_hull_sub _ (F + 0x210) 104); [exact Hhe | lia | lia | lia]|].
    intros a Ha. pose proof (hc5_band_hull (F + 0x218) n a ltac:(lia) ltac:(lia) Hn0 Ha) as Hb.
    apply K1; [lia | exact (proj1 (Hband a Hb))].
  - lia.
  - lia.
  - intros a Ha. split.
    + rewrite Bs7 in Ha.
      pose proof (proj1 (hm_bytes_aview rsegs (w_H W1) mem1 src (hc5_p r)) Hp1' (Z.to_nat (a - src))
        ltac:(lia)) as A.
      rewrite Z2Nat.id in A by lia. replace (src + (a - src)) with a in A by lia. rewrite A. discriminate.
    + unfold spZ. rewrite Hsp1. unfold w64. rewrite unsigned_lit_small by lia. unfold ESTACK.
      pose proof (Hdr a ltac:(lia)). lia.
  - destruct (Z_le_gt_dec n 0) as [Hn0|Hn0]; [lia|].
    destruct (Z_le_gt_dec (F + 0x218 + n) src) as [X|X]; [left; exact X|].
    destruct (Z_le_gt_dec (src + n) (F + 0x218)) as [Y|Y]; [right; exact Y|].
    exfalso. apply (Hdis (Z.max src (F + 0x218))); lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham |- *. lia.
  - apply (hm_ra_kept rsegs (w_H W) memc); [apply (ra_sub _ _ c (Z.of_nat (length r))); [exact Hrain | lia | lia]|].
    intros x Hx. pose proof (hc5_band_ra x ltac:(lia)) as Hb.
    apply K1; [lia | exact (proj1 (Hband _ Hb))].
  - intros Hn0. apply (hc5_hullk (w_H W) (w_H W1) memc mem1).
    + apply (hm_hull_sub _ c (Z.of_nat (length r))); [apply Hhin; lia | lia | lia | lia].
    + intros a Ha. pose proof (hc5_band_hull src n a ltac:(lia) ltac:(lia) Hn0 Ha) as Hb.
      apply K1; [lia | exact (proj1 (Hband a Hb))]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & HP2 & _ & HD2 & HK2 & Hpr2).
replace (sp0 + (R - sp0)) with R in HK2 by lia.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ hc5_HWr R F a -> ~ (F + 0x218 <= a < F + 0x218 + n) ->
  ~ (R - ESTACK <= a < R) -> aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha X1 X2 X3. rewrite (HK2 a Ha X2 X3). exact (K1 a Ha X1). }
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & Hfrs2 & _).
assert (Hin4' : In (4, pos) (frames S1)) by (rewrite Hfrs2; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS ly1 S1 W1 mem2 md2 4 pos HAR2 Hin4') as (_ & _ & HFpres2 & _).
rewrite <- HF1 in HFpres2. change (fs_frame_bytes 4) with 1024 in HFpres2.
(* ---- 0x81ec8 .. J ---- *)
eapply SRr_mono.
{ apply (hc5_tail STK sp0 FP ly S W0 mem0 md0 own k ly1 S1 W1 mem2 md2 regs2 R F pos src lf pp
    (bv_unsigned b) n (hc5_p r) HJ2 HRsp ltac:(lia) Hown HF1 HF4 HFc ltac:(lia) HRb2 Bs7 Bs6).
  - transitivity (getr regs1 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia))|].
    transitivity (getr regs 9); [apply Hk1; [apply cb_nz; reflexivity | apply cb_notin; reflexivity]|]. exact H9.
  - transitivity (getr regs1 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact R18].
  - transitivity (getr regs1 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20].
  - transitivity (getr regs1 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact R21].
  - transitivity (getr regs1 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact R23].
  - transitivity (getr regs1 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact R26].
  - apply (hc5_val_kept (w_H W) (w_H W1) memc mem2 _ _ _ Ve8). intros i Hi. apply K2; [lia | unfold hc5_HWr; lia
      | lia | unfold ESTACK; lia].
  - apply (hc5_val_kept (w_H W) (w_H W1) memc mem2 _ _ _ V130). intros i Hi. apply K2; [lia | unfold hc5_HWr; lia
      | lia | unfold ESTACK; lia].
  - apply (hc5_val_kept (w_H W) (w_H W1) memc mem2 _ _ _ V138). intros i Hi. apply K2; [lia | unfold hc5_HWr; lia
      | lia | unfold ESTACK; lia].
  - apply (hc5_val_kept (w_H W) (w_H W1) memc mem2 _ _ _ V148). intros i Hi. apply K2; [lia | unfold hc5_HWr; lia
      | lia | unfold ESTACK; lia].
  - lia.
  - lia.
  - exact Hppb.
  - lia.
  - lia.
  - lia.
  - apply (hm_memcpy_bytes rsegs (w_H W1) mem1 (w_H W1) mem2 src); [exact Hp1'|]. intros i Hi. apply HD2. lia.
  - intros i Hi.
    rewrite (HK2 (F + 0x218 + n + i) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia)).
    apply hc5_aview0. replace (F + 0x218 + n + i) with (F + 0x210 + (8 + n + i)) by lia. apply Rez. lia.
  - intros o Ho. exact (proj1 (HFpres2 (F + o) ltac:(lia))). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hk3 & Hf3 & Hp3 & Hio3 & Hmo3 & Hm3 & HR3).
destruct HR3 as (T13 & T6 & T18 & T20 & T23 & Te).
exists ly3, S3, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|].
split.
{ intros rr Hr0 Hnc.
  rewrite (Hk3 rr Hr0 ltac:(intros X; apply Hnc; cbv [In hc5_tclob hw6b_clob] in X |- *; tauto)).
  rewrite (hc5_reg_cs regs1 regs2 rr HP2 (hc5_cs rr Hr0 Hnc)).
  apply Hk1; [exact Hr0 | intros X; apply Hnc; cbv [In hc5_clob hw6b_clob] in X |- *; tauto]. }
split; [rewrite Hf3; exact Hf1|].
split; [eapply Permutation_trans; [exact Hp3 | exact Hp1]|].
split; [eapply same_io_trans; [exact Hio1 | eapply same_io_trans; [exact Hio2 | exact Hio3]]|].
split; [exact (mle_station MT Sc S1 S3 0 0 MTL Hmo1 Hmo3)|].
split.
{ intros a Ha Hw.
  rewrite (Hm3 a Ha ltac:(intros X; apply Hw; apply Hwr; right; right; left; exact X)).
  rewrite (HK2 a Ha ltac:(intros X; apply Hw; apply Hwr; right; right; right; exact X)
                ltac:(intros X; apply Hw; apply Hwr; right; left; exact X)).
  apply K1; [exact Ha | intros X; apply Hw; apply Hwr; left; exact X]. }
(* ---- the state at J: the pod of Model.ent_build ---- *)
unfold cj_J_R. rewrite (hc5_model b r Hkd5). cbn [fst snd]. rewrite hc5_skip_len, <- Hn_eq, <- Hlf_eq.
split; [rewrite T13; unfold w64; f_equal; lia|].
split; [exact T6|].
split; [unfold Layout.OFF_LEN; exact T18|].
split; [unfold HSU_E62; exact T20|].
split; [exact T23|].
unfold HSU_E62. rewrite hc5_ent_mem by lia. rewrite <- Bs7.
revert Te. destruct (Z.testbit (bv_unsigned b) 7); intros Te; exact Te.
Qed.

End d.
End b.

Print Assumptions hc5_tail.
Print Assumptions hw6b_c5.
