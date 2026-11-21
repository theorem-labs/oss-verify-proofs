(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_init Z_tr_cb3 Z_tr_cb4 Z_tr_fbtail Z_tr_fb1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition tfb_ssite_post (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp t0 t1 t2 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 wbb m',
    ms' = MS (tfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b67c) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16.

Lemma tfb_ssite : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  0 <= last <= 1 -> 0 <= BV <= 16 -> 0 <= PD -> (13 < BV -> PD + 2 <= 65536) ->
  evt psegs (tfb_ssite_post L s sp last len bufp (sbF_PB PB PD BB BV (2 + last) 3) (sbF_PD PD BV 3) (sbF_BB BB BV (2 + last) 3) (sbF_BV BV 3)
                ra gp tp t0 t1 t2 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 (wz BV) a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b57c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HBB MI LAY Rl RBV RPD ROOM. unfold tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. reg_as (last + 2) (2 + last). zstep. br_cases K.
  -
    zs2. zs2. zs2. sb_or w LO BB (rewrite lo16_sx16; exact HBB).
    zs2. zs2. zs2.
    apply evt_done. unfold tfb_ssite_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 7 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend| exact LO].
  -
    zs2. zs2. zs2. zs2. zs2. sb_or w LO BB (rewrite lo16_sx16; exact HBB).
    sbf_b0 L Gpend PB PD (nbv BB BV (2 + last)) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV (2 + last)) LO.
    zs2. zs2. zs2. zs2. zs2. rewrite (Z.mod_small (2 + last) 65536) by lia.
    zs2. rewrite srlw_val16 by lia.
    zs2. zs2. zs2. zs2. reg_as (BV + -13) (BV + 3 - 16).
    apply evt_done. unfold tfb_ssite_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 7 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.

Lemma send_bits_flat : forall X V l, send_bits X V l = upd4 X (sbF_PB (ds_pending_buf X) (ds_pending X) (ds_bi_buf X) (ds_bi_valid X) V l) (sbF_PD (ds_pending X) (ds_bi_valid X) l)
                                                        (sbF_BB (ds_bi_buf X) (ds_bi_valid X) V l) (sbF_BV (ds_bi_valid X) l).
Proof. intros. rewrite <- (upd4_self X) at 1. apply send_bits_sbF. Qed.

Lemma BINV_init_block : forall P Y, BINV P Y -> BINV P (init_block Y).
Proof. intros P Y H. eapply BINV_bits4; [|exact H]. apply (k_init_block _ _ _ keeps_bits4 eq_refl). Qed.
Lemma strm_init_block : forall Y, ds_strm (init_block Y) = ds_strm Y.
Proof. intros. apply (k_init_block _ _ _ keeps_strm eq_refl). Qed.

Lemma tfb_arm_static : forall (L : dlay) (X Rfin : deflate_state) (c : cstrm) (last len bufp lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X -> dzs m L c -> ds_strm X = c -> mem_inv psegs m ->
  munch (tfW L lo sp) m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk psegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> dlay_below L lo (bv_unsigned sp) ->
  BINV 65536 X -> RefFlushBlk13.stat_ok 65536 last X ->
  RefFlushBlk13.post_ok 65536 last (compress_block (send_bits X (2 + last) 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl) ->
  0 <= last <= 1 ->
  Rfin = tfb_fin last (compress_block (send_bits X (2 + last) 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 (wz (ds_bi_valid X)) a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b57c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL BI (ROOM & CBOK & Rsn & Rlb) (BIY & ROOMY) Rl ER.
  unfold Z_TRFB_STACK in LO. pose proof BI as (RBV & RBB & RPD).
  pose proof BEL as BEL0. below_open BEL0.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  pose proof (munch_refl (Wem L) m) as MUw. pose proof (wmono_refl psegs m) as WMw.
  open_DST ST. pose proof (ln_pend _ LENS) as LNP.
  pose proof (EM_of_groups _ _ _ GA GD Gpend LNP) as EMH.
  unfold sb_room, Buf_size in ROOM.
  call (tfb_ssite L X sp last len bufp (ds_pending_buf X) (ds_pending X) (ds_bi_buf X) (ds_bi_valid X) (wz (ds_bi_buf X))).
  1:{ exact EMH. } 1:{ apply lo16_unsigned_wz. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ lia. } 1:{ intros; apply ROOM; lia. }
  match goal with H : EM ?mm _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof H as EMf end.
  match goal with HB : bv_unsigned ?wb mod _ = ?bb mod _ |- _ => lazymatch type of EMf with EM _ _ _ _ _ wb _ =>
    destruct (EM_to_groups _ _ _ _ _ _ _ bb _ EMf (le2_wz_mod _ _ HB) eq_refl) as (HA & HD & HP) end end.
  clear GA GD Gpend EMH. tr_groups MUw WMw. clear MUw WMw.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (ST1 : DST mm L (send_bits X (2 + last) 3)) by
      (rewrite send_bits_flat; cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY; close_lens_sbF LENS) end.
  clear HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead EMf.
  unfold tfR. do 6 zs2. name_mem m1.
  pose proof (munch_refl (tfWz L lo sp) m1) as MUz. pose proof (wmono_refl psegs m1) as WMz.
  call (compress_block_spec L (send_bits X (2 + last) 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl Z_STATIC_LTREE Z_STATIC_DTREE lo).
  1:{ exact ST1. } 1:{ eassumption. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ eapply ct_readable_ro; [apply rod_static_ltree| lia]. } 1:{ eapply ct_readable_ro; [apply rod_static_dtree| lia]. }
  1:{ unfold Z_STATIC_LTREE; lia. } 1:{ unfold Z_STATIC_LTREE; lia. } 1:{ unfold Z_STATIC_DTREE; lia. } 1:{ unfold Z_STATIC_DTREE; lia. }
  1:{ intros i _. pose proof (TreesTab.static_ltree_fc_bound i). lia. } 1:{ intros i _. pose proof (TreesTab.static_dtree_fc_bound i). lia. }
  1:{ exact CBOK. } 1:{ rewrite send_bits_flat, upd4_lit_bufsize. lia. } 1:{ rewrite send_bits_flat, upd4_sym_next. lia. } 1:{ rewrite send_bits_flat, upd4_sym_next. lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST1. name_mem m2.
  remember (compress_block (send_bits X (2 + last) 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl) as Y eqn:EY.
  assert (ESY : ds_strm Y = c).
  { rewrite EY, (k_compress_block _ _ _ keeps_strm eq_refl), (k_send_bits _ _ _ keeps_strm eq_refl). exact ESTRM. }
  zs2. zs2.
  pose proof (munch_refl (tfWz L lo sp) m2) as MUz. pose proof (wmono_refl psegs m2) as WMz.
  call (init_block_spec L Y).
  1:{ eassumption. } 1:{ eassumption. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite ESP in *.
  zstep.
  name_mem m3.
  br_cases_s K.
  - eapply (tfb_finish L (init_block Y) Rfin c last lo 0x1b92c m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
  - zs2. eapply (tfb_finish L (init_block Y) Rfin c last lo 0x1b9a0 m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
Qed.
