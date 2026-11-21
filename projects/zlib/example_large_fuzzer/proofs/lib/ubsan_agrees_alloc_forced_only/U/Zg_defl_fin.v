(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_defl_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_kit Z_putmsb Z_flushpend Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate SendModel FillWinModel DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section FING.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HTFB : tr_flush_bits_stmt.

(* [comment removed for export] *)
Lemma defl_fing : forall (Q : machine_state -> Prop) (X : deflate_state),
  (flush = 0 \/ flush = 4 \/ flush = 5) -> - 2 <= ds_wrap X <= 2 -> ds_wrap X <> 2 ->
  (flush = 4 -> 0 < ds_wrap X ->
   0 <= ds_pending X /\ ds_pending X + 4 <= 65536 /\ 0 <= cs_adler (ds_strm X) < 2^64 /\ ds_lit_bufsize X = 16384
   /\ 0 <= cs_avail_out (ds_strm X) < 2^31 /\ fp_ok (put_adler X)
   /\ ds_wrap (flush_pending (put_adler X)) = ds_wrap X /\ 0 <= ds_pending (flush_pending (put_adler X)) < 2^64
   /\ Box (length (cs_out_rev (ds_strm (flush_pending (put_adler X)))) <= length rest0)%nat) ->
  (flush <> 4 -> DKE L rest0 lo r F fc me Q (wz 0) X) ->
  (flush = 4 -> ds_wrap X <= 0 -> DKE L rest0 lo r F fc me Q (wz 1) X) ->
  (flush = 4 -> 0 < ds_wrap X -> ds_pending (flush_pending (put_adler X)) = 0 ->
   DKE L rest0 lo r F fc me Q (wz 1) (set_wrap (flush_pending (put_adler X)) (- ds_wrap (flush_pending (put_adler X))))) ->
  (flush = 4 -> 0 < ds_wrap X -> ds_pending (flush_pending (put_adler X)) <> 0 ->
   DKE L rest0 lo r F fc me Q (wz 0) (set_wrap (flush_pending (put_adler X)) (- ds_wrap (flush_pending (put_adler X))))) ->
  DKS L flush rest0 lo r F fc me Q 0x18228 X.
Proof.
  intros Q X HFL RW W2 TRL KOK KEND KT1 KT0. unfold DKS. intros until m'. intros DI.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold deflR. unfold DKE, Z_DEFL_EPI in KOK, KEND, KT1, KT0.
  zs. zstep. if_cases KF; zify_cond KF; rewrite ?unsigned_lit in KF by lia.
  - (* [comment removed for export] *)
    assert (F4 : flush = 4) by lia. specialize (KEND F4). specialize (KT1 F4). specialize (KT0 F4). specialize (TRL F4). clear KOK KF.
    pose proof DI as DI0. destruct DI as (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
    pose proof DR as DR0. destruct DR as [ZS ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY1]. open_zs ZS. open_A GA.
    lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
    unfold defl_frame in FR. unfold defl_W in MU.
    assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
    assert (HW : ds_wrap X = -2 \/ ds_wrap X = -1 \/ ds_wrap X = 0 \/ ds_wrap X = 1) by lia.
    assert (RWs : - 2^31 <= ds_wrap X < 2^31) by lia.
    zs.
    destruct HW as [EW|[EW|[EW|EW]]]; rewrite EW; zstep; closed_br.
    1,2,3: zs; zstep; eapply (KEND ltac:(lia)); exact DI0.
    assert (WP : 0 < ds_wrap X) by lia. specialize (KT1 WP). specialize (KT0 WP). destruct (TRL WP) as (RP0 & RP4 & RAD & LBS & RAO & FPOK & EWR & RPF & ROOMF).
    clear KEND TRL.
    pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ab L, dl_Ab L + 65536)] m') as MUf. pose proof (wmono_refl usegs m') as WMf.
    (* [comment removed for export] *)
    zs. zs. zstep. closed_br. zstep. zstep. zs. zstep.
    clear GA ZS.
    assert (X1F : forall Y b, ds_pending (putShortMSB Y b) = ds_pending Y + 1 + 1 /\ ds_strm (putShortMSB Y b) = ds_strm Y
                              /\ ds_lit_bufsize (putShortMSB Y b) = ds_lit_bufsize Y /\ ds_wrap (putShortMSB Y b) = ds_wrap Y).
    { intros Y b. unfold putShortMSB, put_byte. dsred. repeat split; reflexivity. }
    call (putShortMSB_spec L X (wrap32 (Z.shiftr (cs_adler (ds_strm X)) 16)) (bv_swrap 32 (Z.shiftr (cs_adler (ds_strm X)) 16 + 0)) lo).
    1:{ exact DR0. } 1:{ exact MI. } 1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ lia. } 1:{ lia. }
    1:{ apply wrap32_range. } 1:{ rewrite swrap32_mod32, Z.add_0_r, wrap32_mod. reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
    name_mem mB.
    lazymatch goal with H : DREP mB L _ |- _ => rename H into DR1 end.
    lazymatch goal with H : mem_inv usegs mB |- _ => rename H into MI1 end.
    remember (putShortMSB X (wrap32 (Z.shiftr (cs_adler (ds_strm X)) 16))) as X1 eqn:EX1.
    destruct (X1F X (wrap32 (Z.shiftr (cs_adler (ds_strm X)) 16))) as (P1 & T1 & B1 & W1). rewrite <- EX1 in P1, T1, B1, W1.
    pose proof DR1 as DR1'. destruct DR1' as [ZS1 _]. open_zs ZS1. rewrite T1 in ZS1.
    (* [comment removed for export] *)
    rd_lo2 ZS1 96%nat. zstep. zs. zstep. unfold zx16. clear ZS1 RD.
    call (putShortMSB_spec L X1 (Z.land (cs_adler (ds_strm X)) 65535) (bv_unsigned (wz (cs_adler (ds_strm X))) mod 2^16) lo).
    1:{ exact DR1. } 1:{ exact MI1. } 1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ lia. } 1:{ lia. }
    1:{ change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (cs_adler (ds_strm X)) (2^16) ltac:(lia)). lia. }
    1:{ rewrite unsigned_lit by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
        apply Z.mod_small. pose proof (Z.mod_pos_bound (cs_adler (ds_strm X)) (2^16) ltac:(lia)). lia. }
    1:{ reflexivity. } 1:{ reflexivity. }
    name_mem mB2.
    lazymatch goal with H : DREP mB2 L _ |- _ => rename H into DR2 end.
    lazymatch goal with H : mem_inv usegs mB2 |- _ => rename H into MI2 end.
    assert (EPA : putShortMSB X1 (Z.land (cs_adler (ds_strm X)) 65535) = put_adler X) by (rewrite EX1; reflexivity).
    rewrite EPA in DR2.
    destruct (X1F X1 (Z.land (cs_adler (ds_strm X)) 65535)) as (P2 & T2 & B2 & Wr2). rewrite EPA in P2, T2, B2, Wr2.
    assert (DOUT2 : dout mB2 L rest0 (ds_strm (put_adler X))).
    { rewrite T2, T1. apply (dout_munch _ m' mB2 L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia. }
    clear MUf WMf DR0 DR1 EX1 X1F.
    (* [comment removed for export] *)
    zs. zstep.
    call (flush_pending_spec HTFB L (put_adler X) rest0 (zlength inp) lo).
    1:{ exact DR2. } 1:{ exact DOUT2. } 1:{ exact MI2. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
    1:{ exact IO. } 1:{ exact FPOK. } 1:{ rewrite B2, B1, LBS. reflexivity. }
    1:{ rewrite T2, T1. exact RAO. } 1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. }
    name_mem mD.
    lazymatch goal with H : stk usegs mD _ _ |- _ => rewrite ?ESP in H; rename H into STKF end.
    lazymatch goal with H : DREP mD L _ |- _ => rename H into DRF end.
    lazymatch goal with H : dout mD L _ _ |- _ => rename H into DOF end.
    lazymatch goal with H : mem_inv usegs mD |- _ => rename H into MIF end.
    clear P2 T2 B2 Wr2 P1 T1 B1 W1 EPA DR2 DOUT2.
    revert DRF DOF EWR RPF ROOMF KT1 KT0. generalize (flush_pending (put_adler X)). intros s2 DRF DOF EWR RPF ROOMF KT1 KT0.
    (* [comment removed for export] *)
    destruct DRF as [ZSF STF]. destruct STF as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENSF LAYF]. open_A GA.
    pose proof (munch_refl [(dl_As L, dl_As L + 212)] mD) as MUf. pose proof (wmono_refl usegs mD) as WMf.
    assert (RW2 : - 2^31 <= ds_wrap s2 < 2^31) by lia.
    zs. rewrite EWR, EW. zstep. closed_br. zs. zs. name_mem mE.
    tr_groups MUf WMf.
    assert (DIE : DINV L rest0 lo r me (set_wrap s2 (- ds_wrap s2)) mE).
    { split; [split|].
      - exact ZSF.
      - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSF | exact LAYF].
      - split; [dsred; apply (dout_munch _ mD mE L rest0 _ DOF ROOMF MUf WMf); cbn [disjoint_from]; slia|].
        split; [exact ROOMF|]. split; [eexists; exact FR|]. split; [exact STKF|]. split; [exact MU|]. split; [exact WM| eassumption]. }
    (* [comment removed for export] *)
    zs.
    destruct (Z.eq_dec (ds_pending s2) 0) as [P0|PN].
    + rewrite P0. zstep. change (Z.b2z (0 <? 1)) with 1. zstep. eapply (KT1 P0). exact DIE.
    + zstep. replace (ds_pending s2 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). change (Z.b2z false) with 0.
      zstep. eapply (KT0 PN). exact DIE.
  - zs. zstep. eapply (KOK ltac:(lia)). exact DI.
Qed.
End FING.
