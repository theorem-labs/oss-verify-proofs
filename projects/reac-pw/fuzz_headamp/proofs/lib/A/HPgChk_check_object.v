(* check_object 0x8405c of fuzz_headamp.asan (unstripped sha256
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a; the pinned f3e0669d2819 has the same loaded
   bytes except .note.gnu.build-id), the image-A walk against lib/A/HPgCSpec.v's hd_check_object_specX. Proves function check_object (written
   new; the plumbing is lib/A/HPgChkBase.v).

   THE CODE (59 words, fuzz_headamp.c:221-237):
     0x8405c addi sp,sp,-0x10; sd ra,8(sp); 0x84064 auipc a3,0x18; ld a3,0x30c(a3) (the .got word 0x9c370);
     ld a3,0(a3) (the shadow-offset cell); srli / add / 0x84078 lb a4 / 0x8407c bnez a4 (slow arm 0x84100);
     0x84080 lw a2,0(a2) (x->rc); addi a4,a0,1; seqz a4,a4 (rc = -1); 0x8408c sltiu a2,a2,-1 (x->rc <> -1);
     0x84090 beq a4,a2,0x840f8 (the two disagree); 0x84094 addi a2,zero,-1; 0x84098 bne a0,a2,0x840ec (rc <> -1:
     to the epilogue); then for res, res + 4, res + 8: srli / add / lb / bnez (slow arms 0x84114, 0x84128, 0x84138),
     lw (0x840ac, 0x840c8, 0x840e4), bnez to 0x840f8 (the word is not 0);
     0x840ec ld ra,8(sp); addi sp,sp,0x10; 0x840f4 ret; 0x840f8 jal __asan_handle_no_return; jal abort.
   The only store is `sd ra,8(sp)` into the save slot [sp - 16, sp).
   THE TWO CASES, by rc = -1 (the contract makes x->rc = -1 exactly then):
   rc = -1: a0 is the literal -1; x->rc is the literal 0xffffffff (one region at x, env slot 12) and res's 12 bytes
   are zero (one region at res, env slot 11, the contract's garr8 of ha_res_bytes 0 0 0; the two regions apart by
   the contract). The engine decides every branch: 0x84090 and 0x84098 not taken, and each word of res is 0, so no
   `bnez` at 0x840b0 / 0x840cc / 0x840e8 is taken. res->refusal at res + 8 has shadow 0x04: its check passes on the
   slow arm 0x84138, which the token engine follows to the load as the fast one (the shadow entry [res, res + 12)).
   rc <> -1: a0 is an atom and x->rc the atom of env slot 33 (x->rc mod 2^32, not 0xffffffff); the engine splits
   0x84090 and 0x84098: the taken side of the first (seqz (rc + 1) = (sext x->rc <u -1), i.e. 0 = 1) and the
   not-taken side of the second (rc = -1) are refuted; the other sides run to the `ret`; res is not read.
   The jal at 0x840f8 is never stepped; no report call is reached (the shadow entries cover every checked word). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgChkBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition A_CHECK_OBJECT : Z := 0x8405c.
(* the 59 words 0x8405c .. 0x84144 *)
Definition ob_tbl : ctable := build_table rsegs A_CHECK_OBJECT 59 TEmpty.
Lemma ob_tbl_ok : table_ok rsegs ob_tbl.
Proof. apply build_table_ok0. unfold A_CHECK_OBJECT. lia. Qed.

(* rc = -1: a0 the literal -1; x->rc (env slot 12) the literal 0xffffffff; res (env slot 11) twelve zero bytes *)
Definition ob_ov1 : list (bv 5 * sv) := [((10%bv : bv 5), SLit (-1))].
Definition ob_rs1 : smem :=
[hc_data 12 0 4 [YP09.mkChunk 0 (CVal 4 (SLit (2 ^ 32 - 1)))]; hc_data 11 0 12 [YP09.mkChunk 0 (CZero 12)]].
Definition ob_fs1 : list (nat * afact) := [hc_pfact 11 2; hc_pfact 12 2].
Definition ob_SH1 : list shent := [mkSHE 12 0 4; mkSHE 11 0 12].
(* rc <> -1: x->rc the atom of env slot 33 *)
Definition ob_rs0 : smem := [hc_data 12 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))]].
Definition ob_fs0 : list (nat * afact) := [hc_pfact 12 2; (33%nat, mkAF 0 (2 ^ 32 - 2) 0)].
Definition ob_SH0 : list shent := [mkSHE 12 0 4].
Lemma ob_res_nth : forall j, (j < 12)%nat -> nth j (hd_zbytes (ha_res_bytes 0 0 0)) 0 = 0.
Proof. intros j Hj. do 12 (destruct j as [|j]; [reflexivity|]). lia. Qed.
Lemma ob_res_len : length (hd_zbytes (ha_res_bytes 0 0 0)) = 12%nat.
Proof. reflexivity. Qed.

(* the two values the engine leaves symbolic at 0x84090 when rc <> -1: seqz (rc + 1) is 0, and
   sltiu (sext32 x->rc) (-1) is 1 (x->rc mod 2^32 is not 0xffffffff) *)
Lemma ob_zcanon_neg : forall z, - 2 ^ 64 <= z < 0 -> zcanon z = z + 2 ^ 64.
Proof.
intros z Hz. unfold zcanon, M64. rewrite <- (Z.mod_add z 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma ob_wrap_neg : forall rcc, - 2 ^ 64 <= rcc < 0 -> bv_unsigned (Z_to_bv 64 rcc) = rcc + 2 ^ 64.
Proof. intros rcc H. rewrite Z_to_bv_unsigned. change (bv_wrap 64 rcc) with (zcanon rcc). apply ob_zcanon_neg. lia. Qed.
Lemma ob_seqz : forall E rcc, ew E 10 = Z_to_bv 64 rcc -> - 2 ^ 31 <= rcc < 2 ^ 31 -> rcc <> -1 ->
U E (SAlu ALU_SLTU (SOff 10 1) (SLit 1)) = 0.
Proof.
intros E rcc H Hr Hn. rewrite U_SAlu, U_SOff, U_SLit, H. cbn [zalu_raw].
rewrite (zcanon_id 1) by (unfold M64; lia).
destruct (Z_lt_le_dec rcc 0) as [Hl | Hl].
- rewrite ob_wrap_neg by lia. rewrite (zcanon_id (rcc + 2 ^ 64 + 1)) by (unfold M64; lia).
  destruct (Z.ltb_spec (rcc + 2 ^ 64 + 1) 1); [lia | reflexivity].
- rewrite unsigned_lit_small by lia. rewrite (zcanon_id (rcc + 1)) by (unfold M64; lia).
  destruct (Z.ltb_spec (rcc + 1) 1); [lia | reflexivity].
Qed.
Lemma ob_sext : forall E xm, ew E 33 = Z_to_bv 64 xm -> 0 <= xm <= 2 ^ 32 - 2 ->
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
  rewrite Hs. apply ob_zcanon_neg. lia.
Qed.
Lemma ob_sltiu : forall E xm, ew E 33 = Z_to_bv 64 xm -> 0 <= xm <= 2 ^ 32 - 2 ->
U E (SAlu ALU_SLTU (SExt true 32 (SOff 33 0)) (SLit (-1))) = 1.
Proof.
intros E xm H Hx. rewrite U_SAlu, U_SLit, (ob_sext E xm H Hx), (ob_zcanon_neg (-1)) by lia. cbn [zalu_raw].
destruct (Z_lt_le_dec xm (2 ^ 31)) as [Hl | Hl].
- rewrite (proj2 (Z.ltb_lt xm (2 ^ 31)) Hl). destruct (Z.ltb_spec xm (-1 + 2 ^ 64)); [|lia].
  apply zcanon_id. unfold M64. lia.
- rewrite (proj2 (Z.ltb_ge xm (2 ^ 31)) Hl). destruct (Z.ltb_spec (xm - 2 ^ 32 + 2 ^ 64) (-1 + 2 ^ 64)); [|lia].
  apply zcanon_id. unfold M64. lia.
Qed.
(* the `bne a0,a2` at 0x84098 with a2 = -1 (the engine's literal 2^64 - 1) *)
Lemma ob_ne : forall E rcc, ew E 10 = Z_to_bv 64 rcc -> - 2 ^ 31 <= rcc < 2 ^ 31 -> rcc <> -1 ->
(U E (SOff 10 0) =? U E (SLit 18446744073709551615)) = false.
Proof.
intros E rcc H Hr Hn. rewrite U_SOff, U_SLit, H. rewrite (zcanon_id 18446744073709551615) by (unfold M64; lia).
rewrite Z.add_0_r.
destruct (Z_lt_le_dec rcc 0) as [Hl | Hl].
- rewrite ob_wrap_neg by lia. rewrite (zcanon_id (rcc + 2 ^ 64)) by (unfold M64; lia). apply Z.eqb_neq. lia.
- rewrite unsigned_lit_small by lia. rewrite (zcanon_id rcc) by (unfold M64; lia). apply Z.eqb_neq. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis HBgot : as_got_shadow B = HC_GOT_SH.
Hypothesis HBcell : as_shadow_cell B = HC_SH_CELL.

Theorem hd_check_object_A : hd_check_object_specX rsegs B MT A_CHECK_OBJECT.
Proof using MTL HBgot HBcell.
unfold hd_check_object_specX, hd_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rcc xrc r x
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H11 H12 Hrc Hxrc Hiff Vx Shx Ofx (Appx & Imgx) Hx4 Hres.
hc_prelude.
destruct (hc_app_fact x 4 Appx ltac:(lia)) as (Hx0 & Hx1 & Hx2).
destruct (hc_app_apart x 4 Imgx ltac:(lia)) as [Dxg Dxc].
unfold ASAN_CEIL in *.
unfold cfg_at. change (w64 A_CHECK_OBJECT) with (Z_to_bv 64 A_CHECK_OBJECT).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
destruct (Z.eq_dec rcc (-1)) as [Hm1 | Hn1].
- (* rc = -1, x->rc = -1 *)
  assert (Hx1' : xrc = -1) by (apply Hiff; exact Hm1).
  destruct (Hres Hm1) as (Hr4 & Gr & Shr & Ofr & (Appr & Imgr) & Hap). clear Hres.
  subst rcc xrc. change ((-1) mod 2 ^ 32) with (2 ^ 32 - 1) in Vx.
  destruct (hc_app_fact r 12 Appr ltac:(lia)) as (Hp0 & Hp1 & Hp2).
  destruct (hc_app_apart r 12 Imgr ltac:(lia)) as [Drg Drc].
  unfold ASAN_CEIL in *.
  assert (Usp : bv_unsigned (ew (Ereg regs (hc_extra [])) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  pose proof (hc_E32 regs []) as E32.
  assert (E1 : ew (Ereg regs (hc_extra [])) 1 = getr regs 1) by exact (ew_Ereg_nat regs _ 1 1%bv eq_refl).
  assert (U11 : bv_unsigned (ew (Ereg regs (hc_extra [])) 11) = r)
  by (apply (hc_Ereg_ptr regs _ 11 11%bv r eq_refl H11); unfold HC_PHI in *; lia).
  assert (U12 : bv_unsigned (ew (Ereg regs (hc_extra [])) 12) = x)
  by (apply (hc_Ereg_ptr regs _ 12 12%bv x eq_refl H12); unfold HC_PHI in *; lia).
  assert (HS : st_ok rsegs (Ereg regs (hc_extra [])) (ss_hc A_CHECK_OBJECT ob_ov1 ob_rs1 ob_fs1)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_CHECK_OBJECT) memc (seg_rom rsegs)))).
  { apply (hc_entry A_CHECK_OBJECT ob_ov1 [] ob_rs1 ob_fs1 W regs memc ltac:(unfold A_CHECK_OBJECT; lia)); try assumption.
    - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [apply hc_nz; vm_compute; discriminate|].
      rewrite hc_lit. symmetry. exact H10.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (hc_data_ok _ _ 12 x 0 4 _ U12); [lia | unfold HC_PHI in *; lia |].
        apply Forall_cons; [|apply Forall_nil].
        apply (hc_chunk4 _ _ x 0 (SLit (2 ^ 32 - 1)) (2 ^ 32 - 1) eq_refl); [lia | rewrite Z.add_0_r; exact Vx].
      + apply (hc_data_ok _ _ 11 r 0 12 _ U11); [lia | unfold HC_PHI in *; lia |].
        apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi.
        destruct (Gr (Z.to_nat i) ltac:(rewrite ob_res_len; lia)) as [Gv _].
        rewrite (ob_res_nth (Z.to_nat i) ltac:(lia)) in Gv. rewrite Z2Nat.id in Gv by lia.
        specialize (Gv 0%nat ltac:(lia)). rewrite Z.add_0_r in Gv |- *. exact Gv.
    - unfold hc_base_regions, ob_rs1, hc_stack_region, hc_got_region, hc_cell_region, hc_data, extent_of_region.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U11, U12.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold HC_GOT_SH, HC_SH_CELL in *. repeat split; lia.
    - cbn [atoms_ok ob_fs1 hc_pfact]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U11, U12, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite Z.pow_0_r, !Z.mod_1_r.
      unfold hc_SB, SHADOW_OFF, HC_PHI in *. repeat split; lia. }
  assert (SHOK : sh_ok rsegs hc_Bx ob_SH1 (Ereg regs (hc_extra [])) (mrestrict (w_H W) memc)).
  { unfold sh_ok, ob_SH1. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (hc_shent (w_H W) memc _ 12 x 0 4); [rewrite Z.add_0_r; exact Shx | rewrite Z.add_0_r; exact Appx | exact E32 | exact U12 | lia].
    - apply (hc_shent (w_H W) memc _ 11 r 0 12); [rewrite Z.add_0_r; exact Shr | rewrite Z.add_0_r; exact Appr | exact E32 | exact U11 | lia]. }
  remember (Ereg regs (hc_extra [])) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (hc_extra [])) E) by (subst E; apply env_agree_refl).
  clear HE. rename Usp into B2.
  (* 0x8405c .. 0x840e8: every branch decided; stop at 0x840f4 ret *)
  hc_run ob_tbl_ok. hc_keep.
  hc_leaf ob_tbl_ok.
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
  assert (HS : st_ok rsegs (Ereg regs (hc_extra [xrc mod 2 ^ 32])) (ss_hc A_CHECK_OBJECT [] ob_rs0 ob_fs0)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_CHECK_OBJECT) memc (seg_rom rsegs)))).
  { apply (hc_entry A_CHECK_OBJECT [] [xrc mod 2 ^ 32] ob_rs0 ob_fs0 W regs memc ltac:(unfold A_CHECK_OBJECT; lia)
      (Forall_nil _)); try assumption.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      apply (hc_data_ok _ _ 12 x 0 4 _ U12); [lia | unfold HC_PHI in *; lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (hc_chunk4 _ _ x 0 (SOff 33 0) (xrc mod 2 ^ 32)); [apply hc_denot_atom; [exact E33 | lia] | lia |].
      rewrite Z.add_0_r. exact Vx.
    - unfold hc_base_regions, ob_rs0, hc_stack_region, hc_got_region, hc_cell_region, hc_data, extent_of_region.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U12.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold HC_GOT_SH, HC_SH_CELL in *. repeat split; lia.
    - cbn [atoms_ok ob_fs0 hc_pfact]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U12, U33, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite Z.pow_0_r, !Z.mod_1_r.
      unfold hc_SB, SHADOW_OFF, HC_PHI in *. repeat split; lia. }
  assert (SHOK : sh_ok rsegs hc_Bx ob_SH0 (Ereg regs (hc_extra [xrc mod 2 ^ 32])) (mrestrict (w_H W) memc)).
  { unfold sh_ok, ob_SH0. apply Forall_cons; [|apply Forall_nil].
    apply (hc_shent (w_H W) memc _ 12 x 0 4); [rewrite Z.add_0_r; exact Shx | rewrite Z.add_0_r; exact Appx | exact E32 | exact U12 | lia]. }
  remember (Ereg regs (hc_extra [xrc mod 2 ^ 32])) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (hc_extra [xrc mod 2 ^ 32])) E) by (subst E; apply env_agree_refl).
  clear HE. rename Usp into B2.
  (* 0x8405c .. 0x8408c, stop at 0x84090 beq a4,a2 *)
  hc_run ob_tbl_ok. hc_keep.
  hc_branch ob_tbl_ok.
  + (* taken: seqz (rc + 1) = sltiu (sext32 x->rc) (-1), i.e. 0 = 1 *)
    exfalso. lazymatch goal with Hb : branch_taken _ (sv_denot ?Ex _) _ = true |- _ =>
      rename Hb into Ht;
      assert (F10 : ew Ex 10 = Z_to_bv 64 rcc) by (cbn [ew ewset Nat.eqb]; exact E10);
      assert (F33 : ew Ex 33 = Z_to_bv 64 (xrc mod 2 ^ 32)) by (cbn [ew ewset Nat.eqb]; exact E33) end.
    rewrite branch_eq_U, (ob_seqz _ rcc F10 Hrc Hn1), (ob_sltiu _ (xrc mod 2 ^ 32) F33 Hxv) in Ht. discriminate Ht.
  + (* not taken: 0x84094 addi a2,zero,-1, stop at 0x84098 bne a0,a2 *)
    hc_run ob_tbl_ok. hc_keep.
    hc_branch ob_tbl_ok.
    * (* taken: rc <> -1, to the epilogue; stop at 0x840f4 ret *)
      hc_run ob_tbl_ok. hc_keep.
      hc_leaf ob_tbl_ok.
    * (* not taken: rc = -1, against rc <> -1 *)
      exfalso. lazymatch goal with Hb : branch_taken BC_NE (sv_denot ?Ex _) _ = false |- _ =>
        rename Hb into Ht;
        assert (F10 : ew Ex 10 = Z_to_bv 64 rcc) by (cbn [ew ewset Nat.eqb]; exact E10) end.
      rewrite branch_ne_U, (ob_ne _ rcc F10 Hrc Hn1) in Ht. discriminate Ht.
Qed.
End c.

Print Assumptions hd_check_object_A.
