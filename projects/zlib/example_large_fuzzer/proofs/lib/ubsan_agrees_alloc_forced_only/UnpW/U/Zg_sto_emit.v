(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Zg_sto_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Z_tr_emit Z_ukit Z_flushpend Zg_defl_iface Zg_sto_kit Zg_sto_head.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk SendModel FillWinModel TrSmallModel DeflateSafe. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast1. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored2 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_STO_COPY : Z := 0x188b8.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dlay_below_lower : forall L lo hi hi', dlay_below L lo hi -> hi' <= hi -> dlay_below L lo hi'.
Proof. intros L lo hi hi' H Hle. unfold dlay_below in *. lia. Qed.

(* [comment removed for export] *)
Lemma patb0 : forall len, bv_unsigned (wz len) mod 2^8 = wrap8 len mod 2^8.
Proof. intros len. rewrite lo8_unsigned_wz. bits8. Qed.
Lemma patb1 : forall len, 0 <= len -> bv_unsigned (wz (Z.shiftr len 8)) mod 2^8 = wrap8 (Z.shiftr len 8) mod 2^8.
Proof. intros len H. rewrite lo8_unsigned_wz. bits8. Qed.
Lemma patb2 : forall len, 0 <= len -> bv_unsigned (wz (Z.lxor len 18446744073709551615)) mod 2^8 = wrap8 (Z.lnot len) mod 2^8.
Proof. intros len H. rewrite lo8_unsigned_wz. change 18446744073709551615 with (Z.ones 64). bits8. Qed.

(* [comment removed for export] *)
Lemma patb1w : forall len, 0 <= len < 2^16 -> wz (bv_swrap 32 (Z.shiftr (bv_wrap 32 len) 8)) = wz (Z.shiftr len 8).
Proof.
  intros len H. rewrite (bv_wrap_small 32 len) by (unfold bv_modulus; cbn; lia).
  assert (R : 0 <= Z.shiftr len 8 < 2^24).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite bv_swrap32_id by lia. reflexivity.
Qed.
Lemma patb3w : forall len, 0 <= len < 2^16 ->
  bv_unsigned (wz (bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.lxor len 18446744073709551615)) 8))) mod 2^8 = wrap8 (Z.shiftr (wrap32 (Z.lnot len)) 8) mod 2^8.
Proof.
  intros len H.
  assert (R1 : 0 <= bv_wrap 32 (Z.lxor len 18446744073709551615) < 2^32) by (unfold bv_wrap; apply Z.mod_pos_bound; reflexivity).
  assert (R : 0 <= Z.shiftr (bv_wrap 32 (Z.lxor len 18446744073709551615)) 8 < 2^24).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite bv_swrap32_id by lia. rewrite lo8_unsigned_wz. unfold bv_wrap, wrap32. change (bv_modulus 32) with (2^32).
  change 18446744073709551615 with (Z.ones 64). change 4294967295 with (Z.ones 32). bits8.
Qed.

(* [comment removed for export] *)
Lemma lastv_mach : forall flush len v, 0 <= flush <= 5 -> 0 <= len < 2^16 -> 0 <= v < 2^32 ->
  Z.b2z (Z.lor (Z.lxor flush 4) (Z.lxor len ((bv_swrap 32 v) mod 18446744073709551616)) <? 1) = (if (flush =? 4) && (len =? v) then 1 else 0).
Proof.
  intros flush len v Hf Hl Hv.
  set (u := bv_swrap 32 v mod 18446744073709551616).
  assert (Hu : 0 <= u /\ (u = len <-> v = len)).
  { subst u. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.div].
    change (4294967296 / 2) with 2147483648. change (2^32) with 4294967296 in Hv. change (2^16) with 65536 in Hl.
    Z.div_mod_to_equations. lia. }
  clearbody u. destruct Hu as [Hu0 Huv].
  assert (N1' : 0 <= Z.lxor flush 4) by (apply (proj2 (Z.lxor_nonneg flush 4)); lia).
  assert (N2' : 0 <= Z.lxor len u) by (apply (proj2 (Z.lxor_nonneg len u)); lia).
  assert (N3 : 0 <= Z.lor (Z.lxor flush 4) (Z.lxor len u)) by (apply (proj2 (Z.lor_nonneg _ _)); split; assumption).
  destruct (Z.ltb_spec (Z.lor (Z.lxor flush 4) (Z.lxor len u)) 1) as [LT|GE].
  - assert (E0 : Z.lor (Z.lxor flush 4) (Z.lxor len u) = 0) by lia.
    apply Z.lor_eq_0_iff in E0. destruct E0 as [E1 E2]. apply (proj1 (Z.lxor_eq_0_iff _ _)) in E1. apply (proj1 (Z.lxor_eq_0_iff _ _)) in E2.
    replace (flush =? 4) with true by (symmetry; apply Z.eqb_eq; exact E1).
    replace (len =? v) with true by (symmetry; apply Z.eqb_eq; symmetry; apply Huv; symmetry; exact E2). reflexivity.
  - destruct (Z.eqb_spec flush 4) as [EF|NF]; [|reflexivity]. destruct (Z.eqb_spec len v) as [EL|NL]; [|reflexivity].
    exfalso. rewrite EF in GE. assert (Eu : u = len) by (apply (proj2 Huv); symmetry; exact EL). rewrite Eu in GE.
    rewrite !Z.lxor_nilpotent in GE. change (Z.lor 0 0) with 0 in GE. lia.
Qed.

(* [comment removed for export] *)
Lemma fp_ok_of_so : forall s, ds_lit_bufsize s = 16384 -> so_fp_ok 65536 s -> fp_ok s.
Proof.
  intros s LBS [BI H]. cbv zeta in H. unfold fp_ok. rewrite LBS. change (16384 * 4) with 65536. split; [exact BI|]. cbv zeta. lia.
Qed.

(* [comment removed for export] *)
Ltac pb_store' ARR A idx v RNG := lazymatch type of ARR with u8arr _ _ _ (av8 ?a ?n) => pb_store ARR a n A idx v RNG end.

Section EMIT.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.
Hypothesis HFL : 0 <= flush <= 5.
Hypothesis HTSB : tr_stored_block_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.

(* [comment removed for export] *)
Definition KCOPY (Q : machine_state -> Prop) (X X4 : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 : word) (m' : mem),
    STOINV L flush rest0 lo r me X4 m' ->
    evt usegs Q (MS (stoR L flush ai0 (sb_lastv X flush) r y1 y5 y6 y7 (wz (ds_strstart X - ds_block_start X)) y10 y11 y12 y13 y14 y15 y16 y17 (wz (sb_len X)) y20 y28 y29 y30 y31)
                    F (wz Z_STO_COPY) fc None m' (seg_rom usegs)).

Variables (Q : machine_state -> Prop) (X : deflate_state).
Hypothesis RBV : 0 <= ds_bi_valid X <= 16.
Hypothesis RAO : 0 <= cs_avail_out (ds_strm X) < 2^31.
Hypothesis RAI : 0 <= cs_avail_in (ds_strm X) < 2^31.
Hypothesis RBS : 0 <= ds_block_start X <= ds_strstart X.
Hypothesis RSTR : ds_strstart X <= 65536.
Hypothesis LBS : ds_lit_bufsize X = 16384.
Hypothesis HH : sb_hdr X <= cs_avail_out (ds_strm X).
Hypothesis EOK : so_emit_ok X flush.
Hypothesis RM4 : Box (length (cs_out_rev (ds_strm (st_emit1 X flush))) <= length rest0)%nat.
Hypothesis KC : KCOPY Q X (st_emit1 X flush).

Let v := ds_strstart X - ds_block_start X + cs_avail_in (ds_strm X).

Lemma sto_emit : KEMIT L flush ai0 rest0 lo r F fc me Q X.
Proof using v KC RM4 EOK HH LBS RSTR RBS RAI RAO HTFB HTSB HFL CTX inp.
  unfold KEMIT. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & FR & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_EMIT, stoR.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'.
  pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (sb_len_range X ltac:(lia) HH) as (RL1 & RL2 & RL3).
  (* [comment removed for export] *)
  destruct EOK as (BI0 & RP1 & FPOK). rewrite LBS in BI0, RP1, FPOK. change (16384 * 4) with 65536 in BI0, RP1, FPOK.
  remember (sb_lastv X flush) as last eqn:Elast.
  pose proof (sb_lastv_range X flush) as Rlast. rewrite <- Elast in Rlast.
  assert (Elv : last = (if (flush =? 4) && (sb_len X =? v) then 1 else 0)).
  { rewrite Elast. unfold sb_lastv, Z_FINISH. rewrite (sb_left_eq' X RBS RSTR). subst v. rewrite wrap32_mod, Z.mod_small by lia. reflexivity. }
  (* [comment removed for export] *)
  zstep. fold v. replace (Z.land (if flush =? 4 then 1 else 0) (if sb_len X =? v then 1 else 0)) with last by (rewrite Elv; destruct (flush =? 4), (sb_len X =? v); reflexivity).
  (* [comment removed for export] *)
  do 4 zstep.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -112)) = bv_unsigned (r_sp r) + -112) by (apply unsigned_lit; lia).
  unfold sto_W, slow_W in MU.
  unfold dout in DOUT. pose proof (outv_length rest0 (ds_strm X) (unbox _ RM)) as OL. open_zs ZS.
  zstep. call (HTSB L X None 0 last lo).
  1:{ exact ST. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. eapply dlay_below_lower; [exact BEL| lia]. }
  1:{ exact BI0. } 1:{ lia. } 1:{ intros C; exfalso; apply C; reflexivity. } 1:{ exact I. } 1:{ lia. } 1:{ exact Rlast. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem m1. rewrite ESP in PC. rename PC into STK1. clear ST.
  (* [comment removed for export] *)
  assert (HX1 : exists X1, X1 = tr_stored_block X None 0 last) by (eexists; reflexivity). destruct HX1 as [X1 EX1].
  pose proof (sb_keep X None 0 last) as KK. cbv zeta in KK. rewrite <- EX1 in KK, RP1, FPOK, POST. destruct KK as (K1s & K1w & K1ws & K1hs & K1lbs & K1bs & K1str).
  open_DST POST. open_A GA. open_pend Gpend. pose proof (ln_pend _ LENS) as LNP.
  pose proof (munch_refl [(dl_Ab L, dl_Ab L + 65536)] m1) as MUf. pose proof (wmono_refl usegs m1) as WMf.
  (* [comment removed for export] *)
  do 4 zstep. gF. do 3 zstep. gX. gF.
  pb_store' Gpend (dl_Ab L) (ds_pending X1 - 4) (wrap8 (sb_len X)) ltac:(apply patb0).
  do 4 zstep. gF. do 3 zstep. gX. gF. zstep. rewrite (patb1w (sb_len X)) by lia.
  pb_store' Gpend (dl_Ab L) (ds_pending X1 - 3) (wrap8 (Z.shiftr (sb_len X) 8)) ltac:(apply patb1; lia).
  do 4 zstep. gF. do 3 zstep. gX. gF. zstep.
  pb_store' Gpend (dl_Ab L) (ds_pending X1 - 2) (wrap8 (Z.lnot (sb_len X))) ltac:(apply patb2; lia).
  do 4 zstep. gF. do 3 zstep. gX. gF. zstep.
  pb_store' Gpend (dl_Ab L) (ds_pending X1 - 1) (wrap8 (Z.shiftr (wrap32 (Z.lnot (sb_len X))) 8)) ltac:(apply patb3w; lia).
  name_mem mB.
  (* [comment removed for export] *)
  assert (EA4 : exists X2, X2 = sb_patch X1 (sb_len X)) by (eexists; reflexivity). destruct EA4 as [X2 EX2].
  pose proof (sb_patch_keep X1 (sb_len X)) as KK. rewrite <- EX2 in KK. destruct KK as (K2s & K2w & K2ws & K2hs & K2lbs & K2bs & K2str & K2p & K2wr & K2bv).
  rewrite <- EX2 in FPOK.
  tr_groups MUf WMf.
  assert (ST2 : DST mB L X2).
  { rewrite EX2. unfold sb_patch. cbv zeta.
    destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
    constructor; [exists hA1, hA2, hA3, hA4, hA5; exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| | exact LAY].
    constructor; [exact l1| exact l2| exact l3| exact l4| exact l5| exact l6| exact l7| exact l8| exact l9| exact l10| exact l11| exact l12| ].
    dsred. rewrite !arr_len_set. exact LNP. }
  assert (ES : ds_strm X2 = ds_strm X) by (rewrite K2s; exact K1s).
  assert (EF : st_emit1 X flush = flush_pending X2) by (unfold st_emit1; rewrite <- Elast, <- EX1, <- EX2; reflexivity).
  rewrite EF in RM4. unfold KCOPY in KC. rewrite EF in KC.
  (* [comment removed for export] *)
  zstep.
  clear GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf WMf LENS LNP GA.
  assert (DR2 : DREP mB L X2) by (split; [exists zp1, zp2, zp3, zresv; rewrite ES; exact ZS| exact ST2]).
  assert (OUT2 : dout mB L rest0 (ds_strm X2)) by (unfold dout; rewrite ES; exact DOUT).
  assert (FP2 : fp_ok X2) by (apply fp_ok_of_so; [rewrite K2lbs, K1lbs; exact LBS| exact FPOK]).
  clear ZS ST2 DOUT.
  zstep. call (flush_pending_spec HTFB L X2 rest0 (zlength inp) lo).
  1:{ exact DR2. } 1:{ exact OUT2. } 1:{ eassumption. } 1:{ rewrite ESP. exact STK1. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. eapply dlay_below_lower; [exact BEL| lia]. }
  1:{ exact IO. } 1:{ exact FP2. } 1:{ rewrite K2lbs, K1lbs, LBS. reflexivity. } 1:{ rewrite ES. exact RAO. } 1:{ exact (unbox _ RM4). } 1:{ reflexivity. }
  name_mem m2. rewrite ESP in PC. rename PC into STK2.
  subst last. eapply KC.
  split; [exact PC0|]. split; [exact POST|]. split; [exact RM4|]. split; [exact FR|]. split; [exact STK2|].
  split; [exact MU|]. split; [exact WM| exact MI].
Qed.
End EMIT.
