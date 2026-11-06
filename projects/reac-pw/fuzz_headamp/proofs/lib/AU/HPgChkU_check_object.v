(* check_object 0x840c0 of fuzz_headamp.asan-ubsan (image B; unstripped sha256
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff; the pinned 53edda9bdeeb has the same loaded
   bytes except .note.gnu.build-id), the image-B walk against lib/A/HPgCSpec.v's hd_check_object_specX on lib/AU/Img0U.v rsegs. Proves function
   check_object (written new as the twin of lib/A/HPgChk_check_object.v; the plumbing is lib/A/HPgChkBase.v and
   lib/AU/HPgChkBaseU.v).
   THE CODE (64 words, 0x840c0 .. 0x841bc; fuzz_headamp.c:221-237): image A's 59 words (lib/A/HPgChk_check_object.v)
   at new addresses with the .got word 0x9c7f0, and two UBSan alignment checks to the trap `unimp` 0x84174:
   x's at entry, 0x840c8 `andi a3,a2,3; bnez a3`, and res's on the rc = -1 path, 0x84108 `andi a0,a1,3; bnez a0`.
   The engine decides both: the atoms of x and res carry the facts x mod 4 = 0 and res mod 4 = 0 (the contract's
   premises), so each `andi` is 0 and each `bnez` is not taken. The rest is image A's: rc = -1 decides every
   branch (res->refusal at res + 8 passes on its slow arm 0x841b0); rc <> -1 splits 0x840fc `beq a4,a2` and
   0x84104 `bne a0,a2` and refutes one side of each; `ret` 0x84168; the abort path 0x8416c is never stepped. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgChkBaseU.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgChkBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition B_CHECK_OBJECT : Z := 0x840c0.
(* the 64 words of image B from 0x840c0 *)
Definition obu_tbl : ctable := build_table rsegs B_CHECK_OBJECT 64 TEmpty.
Lemma obu_tbl_ok : table_ok rsegs obu_tbl.
Proof. apply build_table_ok0. unfold B_CHECK_OBJECT. lia. Qed.

(* rc = -1: a0 the literal -1; x->rc (env slot 12) the literal 0xffffffff; res (env slot 11) twelve zero bytes *)
Definition obu_ov1 : list (bv 5 * sv) := [((10%bv : bv 5), SLit (-1))].
Definition obu_rs1 : smem :=
[hc_data 12 0 4 [YP09.mkChunk 0 (CVal 4 (SLit (2 ^ 32 - 1)))]; hc_data 11 0 12 [YP09.mkChunk 0 (CZero 12)]].
Definition obu_fs1 : list (nat * afact) := [hc_pfact 11 2; hc_pfact 12 2].
Definition obu_SH1 : list shent := [mkSHE 12 0 4; mkSHE 11 0 12].
(* rc <> -1: x->rc the atom of env slot 33 *)
Definition obu_rs0 : smem := [hc_data 12 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))]].
Definition obu_fs0 : list (nat * afact) := [hc_pfact 12 2; (33%nat, mkAF 0 (2 ^ 32 - 2) 0)].
Definition obu_SH0 : list shent := [mkSHE 12 0 4].
Lemma obu_res_nth : forall j, (j < 12)%nat -> nth j (hd_zbytes (ha_res_bytes 0 0 0)) 0 = 0.
Proof. intros j Hj. do 12 (destruct j as [|j]; [reflexivity|]). lia. Qed.
Lemma obu_res_len : length (hd_zbytes (ha_res_bytes 0 0 0)) = 12%nat.
Proof. reflexivity. Qed.

(* the two values the engine leaves symbolic at 0x840fc when rc <> -1: seqz (rc + 1) is 0, and
   sltiu (sext32 x->rc) (-1) is 1 (x->rc mod 2^32 is not 0xffffffff) *)
Lemma obu_zcanon_neg : forall z, - 2 ^ 64 <= z < 0 -> zcanon z = z + 2 ^ 64.
Proof.
intros z Hz. unfold zcanon, M64. rewrite <- (Z.mod_add z 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma obu_wrap_neg : forall rcc, - 2 ^ 64 <= rcc < 0 -> bv_unsigned (Z_to_bv 64 rcc) = rcc + 2 ^ 64.
Proof. intros rcc H. rewrite Z_to_bv_unsigned. change (bv_wrap 64 rcc) with (zcanon rcc). apply obu_zcanon_neg. lia. Qed.
Lemma obu_seqz : forall E rcc, ew E 10 = Z_to_bv 64 rcc -> - 2 ^ 31 <= rcc < 2 ^ 31 -> rcc <> -1 ->
U E (SAlu ALU_SLTU (SOff 10 1) (SLit 1)) = 0.
Proof.
intros E rcc H Hr Hn. rewrite U_SAlu, U_SOff, U_SLit, H. cbn [zalu_raw].
rewrite (zcanon_id 1) by (unfold M64; lia).
destruct (Z_lt_le_dec rcc 0) as [Hl | Hl].
- rewrite obu_wrap_neg by lia. rewrite (zcanon_id (rcc + 2 ^ 64 + 1)) by (unfold M64; lia).
  destruct (Z.ltb_spec (rcc + 2 ^ 64 + 1) 1); [lia | reflexivity].
- rewrite unsigned_lit_small by lia. rewrite (zcanon_id (rcc + 1)) by (unfold M64; lia).
  destruct (Z.ltb_spec (rcc + 1) 1); [lia | reflexivity].
Qed.
Lemma obu_sext : forall E xm, ew E 33 = Z_to_bv 64 xm -> 0 <= xm <= 2 ^ 32 - 2 ->
U E (SExt true 32 (SOff 33 0)) = if xm <? 2 ^ 31 then xm else xm - 2 ^ 32 + 2 ^ 64.
Proof.
intros E xm H Hx. rewrite U_SExt, U_SOff, H, unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite (zcanon_id xm) by (unfold M64; lia). change (Z.of_N 32) with 32. rewrite (Z.mod_small xm (2 ^ 32)) by lia.
destruct (Z_lt_le_dec xm (2 ^ 31)) as [Hl | Hl].
- rewrite (proj2 (Z.ltb_lt xm (2 ^ 31)) Hl). rewrite swrap32_id by lia. apply zcanon_id. unfold M64. lia.
- rewrite (proj2 (Z.ltb_ge xm (2 ^ 31)) Hl).
  assert (Hs : bv_swrap 32 xm = xm - 2 ^ 32).
  { transitivity (bv_swrap 32 (xm - 2 ^ 32)); [|apply swrap32_id; lia].
    rewrite <- (bv_swrap_wrap' 32 xm), <- (bv_swrap_wrap' 32 (xm - 2 ^ 32)). f_equal.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
    replace (xm - 2 ^ 32) with (xm + (-1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. reflexivity. }
  rewrite Hs. apply obu_zcanon_neg. lia.
Qed.
Lemma obu_sltiu : forall E xm, ew E 33 = Z_to_bv 64 xm -> 0 <= xm <= 2 ^ 32 - 2 ->
U E (SAlu ALU_SLTU (SExt true 32 (SOff 33 0)) (SLit (-1))) = 1.
Proof.
intros E xm H Hx. rewrite U_SAlu, U_SLit, (obu_sext E xm H Hx), (obu_zcanon_neg (-1)) by lia. cbn [zalu_raw].
destruct (Z_lt_le_dec xm (2 ^ 31)) as [Hl | Hl].
- rewrite (proj2 (Z.ltb_lt xm (2 ^ 31)) Hl). destruct (Z.ltb_spec xm (-1 + 2 ^ 64)); [|lia].
  apply zcanon_id. unfold M64. lia.
- rewrite (proj2 (Z.ltb_ge xm (2 ^ 31)) Hl). destruct (Z.ltb_spec (xm - 2 ^ 32 + 2 ^ 64) (-1 + 2 ^ 64)); [|lia].
  apply zcanon_id. unfold M64. lia.
Qed.
(* the `bne a0,a2` at 0x84104 with a2 = -1 (the engine's literal 2^64 - 1) *)
Lemma obu_ne : forall E rcc, ew E 10 = Z_to_bv 64 rcc -> - 2 ^ 31 <= rcc < 2 ^ 31 -> rcc <> -1 ->
(U E (SOff 10 0) =? U E (SLit 18446744073709551615)) = false.
Proof.
intros E rcc H Hr Hn. rewrite U_SOff, U_SLit, H. rewrite (zcanon_id 18446744073709551615) by (unfold M64; lia).
rewrite Z.add_0_r.
destruct (Z_lt_le_dec rcc 0) as [Hl | Hl].
- rewrite obu_wrap_neg by lia. rewrite (zcanon_id (rcc + 2 ^ 64)) by (unfold M64; lia). apply Z.eqb_neq. lia.
- rewrite unsigned_lit_small by lia. rewrite (zcanon_id rcc) by (unfold M64; lia). apply Z.eqb_neq. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis HBgot : as_got_shadow B = HCU_GOT_SH.
Hypothesis HBcell : as_shadow_cell B = HCU_SH_CELL.

Theorem hd_check_object_B : hd_check_object_specX rsegs B MT B_CHECK_OBJECT.
Proof using MTL HBgot HBcell.
unfold hd_check_object_specX, hd_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rcc xrc r x
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H11 H12 Hrc Hxrc Hiff Vx Shx Ofx (Appx & Imgx) Hx4 Hres.
hcu_prelude.
destruct (hc_app_fact x 4 Appx ltac:(lia)) as (Hx0 & Hx1 & Hx2).
destruct (hcu_app_apart x 4 Imgx ltac:(lia)) as [Dxg Dxc].
unfold ASAN_CEIL in *.
unfold cfg_at. change (w64 B_CHECK_OBJECT) with (Z_to_bv 64 B_CHECK_OBJECT).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
destruct (Z.eq_dec rcc (-1)) as [Hm1 | Hn1].
- (* rc = -1, x->rc = -1 *)
  assert (Hx1' : xrc = -1) by (apply Hiff; exact Hm1).
  destruct (Hres Hm1) as (Hr4 & Gr & Shr & Ofr & (Appr & Imgr) & Hap). clear Hres.
  subst rcc xrc. change ((-1) mod 2 ^ 32) with (2 ^ 32 - 1) in Vx.
  destruct (hc_app_fact r 12 Appr ltac:(lia)) as (Hp0 & Hp1 & Hp2).
  destruct (hcu_app_apart r 12 Imgr ltac:(lia)) as [Drg Drc].
  unfold ASAN_CEIL in *.
  assert (Usp : bv_unsigned (ew (Ereg regs (hc_extra [])) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  pose proof (hc_E32 regs []) as E32.
  assert (E1 : ew (Ereg regs (hc_extra [])) 1 = getr regs 1) by exact (ew_Ereg_nat regs _ 1 1%bv eq_refl).
  assert (U11 : bv_unsigned (ew (Ereg regs (hc_extra [])) 11) = r)
  by (apply (hc_Ereg_ptr regs _ 11 11%bv r eq_refl H11); unfold HC_PHI in *; lia).
  assert (U12 : bv_unsigned (ew (Ereg regs (hc_extra [])) 12) = x)
  by (apply (hc_Ereg_ptr regs _ 12 12%bv x eq_refl H12); unfold HC_PHI in *; lia).
  assert (HS : st_ok rsegs (Ereg regs (hc_extra [])) (ss_hcu B_CHECK_OBJECT obu_ov1 obu_rs1 obu_fs1)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 B_CHECK_OBJECT) memc (seg_rom rsegs)))).
  { apply (hcu_entry B_CHECK_OBJECT obu_ov1 [] obu_rs1 obu_fs1 W regs memc ltac:(unfold B_CHECK_OBJECT; lia)); try assumption.
    - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [apply hc_nz; vm_compute; discriminate|].
      rewrite hc_lit. symmetry. exact H10.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (hc_data_ok _ _ 12 x 0 4 _ U12); [lia | unfold HC_PHI in *; lia |].
        apply Forall_cons; [|apply Forall_nil].
        apply (hc_chunk4 _ _ x 0 (SLit (2 ^ 32 - 1)) (2 ^ 32 - 1) eq_refl); [lia | rewrite Z.add_0_r; exact Vx].
      + apply (hc_data_ok _ _ 11 r 0 12 _ U11); [lia | unfold HC_PHI in *; lia |].
        apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi.
        destruct (Gr (Z.to_nat i) ltac:(rewrite obu_res_len; lia)) as [Gv _].
        rewrite (obu_res_nth (Z.to_nat i) ltac:(lia)) in Gv. rewrite Z2Nat.id in Gv by lia.
        specialize (Gv 0%nat ltac:(lia)). rewrite Z.add_0_r in Gv |- *. exact Gv.
    - unfold hcu_base_regions, obu_rs1, hc_stack_region, hcu_got_region, hcu_cell_region, hc_data, extent_of_region.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U11, U12.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold HCU_GOT_SH, HCU_SH_CELL in *. repeat split; lia.
    - cbn [atoms_ok obu_fs1 hc_pfact]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U11, U12, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite Z.pow_0_r, !Z.mod_1_r.
      unfold hc_SB, SHADOW_OFF, HC_PHI in *. repeat split; lia. }
  assert (SHOK : sh_ok rsegs hc_Bx obu_SH1 (Ereg regs (hc_extra [])) (mrestrict (w_H W) memc)).
  { unfold sh_ok, obu_SH1. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (hc_shent (w_H W) memc _ 12 x 0 4); [rewrite Z.add_0_r; exact Shx | rewrite Z.add_0_r; exact Appx | exact E32 | exact U12 | lia].
    - apply (hc_shent (w_H W) memc _ 11 r 0 12); [rewrite Z.add_0_r; exact Shr | rewrite Z.add_0_r; exact Appr | exact E32 | exact U11 | lia]. }
  remember (Ereg regs (hc_extra [])) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (hc_extra [])) E) by (subst E; apply env_agree_refl).
  clear HE. rename Usp into B2.
  (* 0x840c0 .. 0x8415c: every branch decided (the two alignment tests too); stop at 0x84168 ret *)
  hc_run obu_tbl_ok. hc_keep.
  hc_leaf obu_tbl_ok.
- (* rc <> -1, x->rc <> -1 *)
  assert (Hxn : xrc <> -1) by (intros Hq; apply Hn1; apply Hiff; exact Hq). clear Hres.
  assert (Hxv : 0 <= xrc mod 2 ^ 32 <= 2 ^ 32 - 2).
  { clear - Hxn Hxrc. pose proof (Z.mod_pos_bound xrc (2 ^ 32) ltac:(lia)) as Hb.
    pose proof (Z.div_mod xrc (2 ^ 32) ltac:(lia)) as Hd.
    remember (xrc / 2 ^ 32) as q eqn:Hq. remember (xrc mod 2 ^ 32) as m eqn:Hm. clear Hq Hm. lia. }
  assert (Usp : bv_unsigned (ew (Ereg regs (hc_extra [xrc mod 2 ^ 32])) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  pose proof (hc_E32 regs [xrc mod 2 ^ 32]) as E32.
  assert (E1 : ew (Ereg regs (hc_extra [xrc mod 2 ^ 32])) 1 = getr regs 1) by exact (ew_Ereg_nat regs _ 1 1%bv eq_refl).
  assert (E10 : ew (Ereg regs (hc_extra [xrc mod 2 ^ 32])) 10 = Z_to_bv 64 rcc) by exact (hc_ew regs _ 10 10%bv rcc eq_refl H10).
  pose proof (hc_E33 regs (xrc mod 2 ^ 32) []) as E33.
  assert (U33 : bv_unsigned (ew (Ereg regs (hc_extra [xrc mod 2 ^ 32])) 33) = xrc mod 2 ^ 32)
  by (rewrite E33; apply unsigned_lit_small; lia).
  assert (U12 : bv_unsigned (ew (Ereg regs (hc_extra [xrc mod 2 ^ 32])) 12) = x)
  by (apply (hc_Ereg_ptr regs _ 12 12%bv x eq_refl H12); unfold HC_PHI in *; lia).
  assert (HS : st_ok rsegs (Ereg regs (hc_extra [xrc mod 2 ^ 32])) (ss_hcu B_CHECK_OBJECT [] obu_rs0 obu_fs0)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 B_CHECK_OBJECT) memc (seg_rom rsegs)))).
  { apply (hcu_entry B_CHECK_OBJECT [] [xrc mod 2 ^ 32] obu_rs0 obu_fs0 W regs memc ltac:(unfold B_CHECK_OBJECT; lia)
      (Forall_nil _)); try assumption.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      apply (hc_data_ok _ _ 12 x 0 4 _ U12); [lia | unfold HC_PHI in *; lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (hc_chunk4 _ _ x 0 (SOff 33 0) (xrc mod 2 ^ 32)); [apply hc_denot_atom; [exact E33 | lia] | lia |].
      rewrite Z.add_0_r. exact Vx.
    - unfold hcu_base_regions, obu_rs0, hc_stack_region, hcu_got_region, hcu_cell_region, hc_data, extent_of_region.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U12.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold HCU_GOT_SH, HCU_SH_CELL in *. repeat split; lia.
    - cbn [atoms_ok obu_fs0 hc_pfact]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U12, U33, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite Z.pow_0_r, !Z.mod_1_r.
      unfold hc_SB, SHADOW_OFF, HC_PHI in *. repeat split; lia. }
  assert (SHOK : sh_ok rsegs hc_Bx obu_SH0 (Ereg regs (hc_extra [xrc mod 2 ^ 32])) (mrestrict (w_H W) memc)).
  { unfold sh_ok, obu_SH0. apply Forall_cons; [|apply Forall_nil].
    apply (hc_shent (w_H W) memc _ 12 x 0 4); [rewrite Z.add_0_r; exact Shx | rewrite Z.add_0_r; exact Appx | exact E32 | exact U12 | lia]. }
  remember (Ereg regs (hc_extra [xrc mod 2 ^ 32])) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (hc_extra [xrc mod 2 ^ 32])) E) by (subst E; apply env_agree_refl).
  clear HE. rename Usp into B2.
  (* 0x840c0 .. 0x840f8 (x's alignment test decided), stop at 0x840fc beq a4,a2 *)
  hc_run obu_tbl_ok. hc_keep.
  hc_branch obu_tbl_ok.
  + (* taken: seqz (rc + 1) = sltiu (sext32 x->rc) (-1), i.e. 0 = 1 *)
    exfalso. lazymatch goal with Hb : branch_taken _ (sv_denot ?Ex _) _ = true |- _ =>
      rename Hb into Ht;
      assert (F10 : ew Ex 10 = Z_to_bv 64 rcc) by (cbn [ew ewset Nat.eqb]; exact E10);
      assert (F33 : ew Ex 33 = Z_to_bv 64 (xrc mod 2 ^ 32)) by (cbn [ew ewset Nat.eqb]; exact E33) end.
    rewrite branch_eq_U, (obu_seqz _ rcc F10 Hrc Hn1), (obu_sltiu _ (xrc mod 2 ^ 32) F33 Hxv) in Ht. discriminate Ht.
  + (* not taken: 0x84100 addi a2,zero,-1, stop at 0x84104 bne a0,a2 *)
    hc_run obu_tbl_ok. hc_keep.
    hc_branch obu_tbl_ok.
    * (* taken: rc <> -1, to the epilogue; stop at 0x84168 ret *)
      hc_run obu_tbl_ok. hc_keep.
      hc_leaf obu_tbl_ok.
    * (* not taken: rc = -1, against rc <> -1 *)
      exfalso. lazymatch goal with Hb : branch_taken BC_NE (sv_denot ?Ex _) _ = false |- _ =>
        rename Hb into Ht;
        assert (F10 : ew Ex 10 = Z_to_bv 64 rcc) by (cbn [ew ewset Nat.eqb]; exact E10) end.
      rewrite branch_ne_U, (obu_ne _ rcc F10 Hrc Hn1) in Ht. discriminate Ht.
Qed.
End c.

Print Assumptions hd_check_object_B.
