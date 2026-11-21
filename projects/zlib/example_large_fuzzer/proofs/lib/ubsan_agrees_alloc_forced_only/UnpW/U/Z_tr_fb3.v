(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_cb4 Z_tr_cb5 Z_tr_windup Z_tr_init Z_tr_stored Z_tr_fb1 Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel TreesTab CompressModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Lemma tfb_arm_stored : forall (L : dlay) (X Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X -> dzs m L c -> ds_strm X = c -> mem_inv usegs m ->
  munch (tfW L lo sp) m0 m -> wmono usegs m0 m ->
  rw_cells usegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk usegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> dlay_below L lo (bv_unsigned sp) ->
  BINV 65536 X -> RefFlushBlk13.sto_ok 65536 X buf len last -> RefFlushBlk13.post_ok 65536 last (tr_stored_block X buf len last) ->
  fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  Rfin = tfb_fin last (tr_stored_block X buf len last) ->
  evt usegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (utfR L sp last len (buf_ptr L buf) ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c6b4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL BI (ROOM & NN) (BIY & ROOMY) BOK Rlen Rl ER.
  unfold Z_TRFB_STACK in LO.
  pose proof BEL as BEL0. below_open BEL0.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  assert (LAY : dlay_ok L) by (destruct ST; assumption).
  unfold utfR. do 5 zs2. name_mem m1.
  pose proof (munch_refl (tfWz L lo sp) m1) as MUz. pose proof (wmono_refl usegs m1) as WMz.
  call (tr_stored_block_spec L X buf len last lo).
  1:{ exact ST. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ exact BI. } 1:{ exact ROOM. } 1:{ exact NN. } 1:{ exact BOK. } 1:{ exact Rlen. } 1:{ exact Rl. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST. name_mem m2.
  remember (tr_stored_block X buf len last) as Y eqn:EY.
  assert (ESY : ds_strm Y = c).
  { rewrite EY, (k_tr_stored_block _ _ _ keeps_strm eq_refl). exact ESTRM. }
  zs2. zs2.
  pose proof (munch_refl (tfWz L lo sp) m2) as MUz. pose proof (wmono_refl usegs m2) as WMz.
  call (init_block_spec L Y).
  1:{ eassumption. } 1:{ eassumption. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite ESP in *.
  zstep. name_mem m3.
  br_cases_s K.
  - eapply (tfb_finish L (init_block Y) Rfin c last lo TF_FIN0 m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
  - eapply (tfb_finish L (init_block Y) Rfin c last lo TF_FINW m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
Qed.
