(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_slow_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_PUTSHORTMSB : Z := 0x18614.

Definition putmsb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (X : deflate_state) (b : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(dl_As L, dl_As L + 212); (dl_Ab L, dl_Ab L + DS_PEND)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ DREP m' L (putShortMSB X b).

(* [comment removed for export] *)
Lemma mod_mod_le : forall x j k, 0 <= j <= k -> (x mod 2^k) mod 2^j = x mod 2^j.
Proof.
  intros x j k Hjk. replace (2^k) with (2^j * 2^(k-j)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm (2^j)), Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.
Lemma msb_b1 : forall b bb, 0 <= b < 2^32 -> bb mod 2^32 = b ->
  bv_unsigned (wz (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bb mod 18446744073709551616)) 8))) mod 2^8 = wrap8 (Z.shiftr b 8) mod 2^8.
Proof.
  intros b bb Hb Hbb. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. change 18446744073709551616 with (2^64). change 4294967296 with (2^32).
  rewrite mod_mod_le by lia. rewrite Hbb.
  assert (RS : 0 <= Z.shiftr b 8 < 2^24) by (rewrite Z.shiftr_div_pow2 by lia; change (2^8) with 256; change (2^24) with 16777216; Z.div_mod_to_equations; lia).
  rewrite bv_swrap32_id by lia. rewrite unsigned_lit by lia. rewrite wrap8_mod, Z.mod_mod by lia. reflexivity.
Qed.
Lemma msb_b0 : forall b bb, 0 <= b < 2^32 -> bb mod 2^32 = b -> bv_unsigned (wz bb) mod 2^8 = wrap8 (Z.land b 255) mod 2^8.
Proof.
  intros b bb Hb Hbb. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. unfold wrap8.
  change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. rewrite !Z.mod_mod by lia.
  rewrite <- Hbb. change 18446744073709551616 with (2^64). rewrite !mod_mod_le by lia. reflexivity.
Qed.

Lemma putShortMSB_spec : forall (L : dlay) (X : deflate_state) (b bb lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L X -> mem_inv usegs m -> dlay_below L lo (bv_unsigned sp) -> lo <= bv_unsigned sp ->
  0 <= ds_pending X -> ds_pending X + 2 <= 65536 -> 0 <= b < 2^32 -> bb mod 2^32 = b ->
  a0 = wz (dl_As L) -> a1 = wz bb ->
  evt usegs (putmsb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L X b m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_PUTSHORTMSB) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros DR MI BEL LOSP RP0 RP2 Rb Rbb -> ->. unfold Z_PUTSHORTMSB. below_open BEL.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY].
  open_A GA. open_pend Gpend. pose proof (ln_pend _ LENS) as Lpend.
  lay_open LAY. pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs. pose proof (lo_b _ LAY) as BKb. unfold blk_ok in BKb.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ab L, dl_Ab L + 65536)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. al8 (dl_As L). gF.
  zs. zs. zstep. zstep. zs. gF. zstep. zstep. zstep. gX. gF.
  zstep.
  pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_pending X) (wrap8 (Z.shiftr b 8)) ltac:(exact (msb_b1 b bb Rb Rbb)).
  zs. zs. zstep. zstep. zs. gF. zstep. zstep. zstep. gX. gF.
  pb_store Gpend (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 (Z.shiftr b 8))) 65536 (dl_Ab L) (ds_pending X + 1) (wrap8 (Z.land b 255)) ltac:(exact (msb_b0 b bb Rb Rbb)).
  zstep. name_mem mB.
  tr_groups MU WM.
  apply evt_done. unfold putmsb_post. do 15 eexists. exists mB.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split.
  - unfold putShortMSB, put_byte. dsred. exact ZS.
  - unfold putShortMSB, put_byte.
    constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| unfold dpend; dsred; exact Gpend| close_lens_set LENS | exact LAY].
Qed.
