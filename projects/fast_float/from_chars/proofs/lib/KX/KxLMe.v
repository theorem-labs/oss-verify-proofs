(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxFrame FxCall FxRgs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_app2 A_rt_stmt A_rt_lemmas A_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn M4A_lm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4A_lm.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun KxTac KxRt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require Import AsanImgScan AsanImg.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxLMn.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require KxSM5 KxSF5 KxMcpyA KxMcpyB KxMsx.
From OSSVerify.Proofs.fast_float.from_chars.lib.LM Require LmThmFp.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxFn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma fr_diff : forall a b lo hi, 0 <= a < two64 -> 0 <= b < two64 ->
  ((b <= a /\ lo <= a - b <= hi) \/ (a < b /\ lo <= a - b + two64 <= hi)) -> lo <= (a - b) mod two64 <= hi.
Proof.
  intros a b lo hi Ha Hb [[H1 H2]|[H1 H2]].
  - rewrite Z.mod_small by lia. exact H2.
  - assert (Hm : (a - b) mod two64 = a - b + two64) by (symmetry; apply Z.mod_unique with (q := -1); unfold two64 in *; lia).
    rewrite Hm. exact H2.
Qed.

(* [comment removed for export] *)
Lemma fr_any : forall z lo hi, -two64 <= z < two64 ->
  ((0 <= z /\ lo <= z <= hi) \/ (z < 0 /\ lo <= z + two64 <= hi)) -> lo <= z mod two64 <= hi.
Proof.
  intros z lo hi Hz [[H1 H2]|[H1 H2]].
  - rewrite Z.mod_small by lia. exact H2.
  - assert (Hm : z mod two64 = z + two64) by (symmetry; apply Z.mod_unique with (q := -1); unfold two64 in *; lia).
    rewrite Hm. exact H2.
Qed.
Ltac frange := apply fr_any; unfold two64 in *; lia.

(* [comment removed for export] *)
Lemma sc_c0all : scan byte_ok c0 64 0x0 0x2e000 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_c2all : scan byte_ok c2 64 0x0 0x5000 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma rom_ok0 : forall x, 0x10000 <= x < 0x3e000 -> seg_rom ASEGS (Z_to_bv 64 x) <> None.
Proof.
  intros x Hx. rewrite rom0 by lia.
  destruct (byte_ok_some c0 _ (scan_at byte_ok c0 0x0 0x2e000 0x10000 x sc_c0all ltac:(cbn [Z.of_N]; lia))) as [b Hb]. rewrite Hb. discriminate.
Qed.
Lemma rom_ok2 : forall x, 0xd9000 <= x < 0xde000 -> seg_rom ASEGS (Z_to_bv 64 x) <> None.
Proof.
  intros x Hx. rewrite rom2 by lia.
  destruct (byte_ok_some c2 _ (scan_at byte_ok c2 0x0 0x5000 0xd9000 x sc_c2all ltac:(cbn [Z.of_N]; lia))) as [b Hb]. rewrite Hb. discriminate.
Qed.
Lemma sc_d3all : scan byte_ok c3 64 0x0 0x3700 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma rom_ok3a : forall x, 0xde000 <= x < 0xe1700 -> seg_rom ASEGS (Z_to_bv 64 x) <> None.
Proof.
  intros x Hx. rewrite rom3 by lia.
  destruct (byte_ok_some c3 _ (scan_at byte_ok c3 0x0 0x3700 0xde000 x sc_d3all ltac:(cbn [Z.of_N]; lia))) as [b Hb]. rewrite Hb. discriminate.
Qed.
Lemma rom_ok3z : forall x, 0xe1700 <= x < 0x168000 -> seg_rom ASEGS (Z_to_bv 64 x) <> None.
Proof.
  intros x Hx. rewrite rom3 by lia.
  rewrite (byte_z_zero c3 _ (scan_at byte_z c3 0x3700 0x86900 0xde000 x sc_3 ltac:(cbn [Z.of_N]; lia))). discriminate.
Qed.
Lemma rom_ok3w : forall x, 0x174000 <= x < 0x177000 -> seg_rom ASEGS (Z_to_bv 64 x) <> None.
Proof.
  intros x Hx. rewrite rom3 by lia.
  rewrite (byte_z_zero c3 _ (scan_at byte_z c3 0x96000 0x3000 0xde000 x sc_4 ltac:(cbn [Z.of_N]; lia))). discriminate.
Qed.
Lemma rom_ok3y : forall x, 0x617410 <= x < 0x63a000 -> seg_rom ASEGS (Z_to_bv 64 x) <> None.
Proof.
  intros x Hx. rewrite rom3 by lia.
  rewrite (byte_z_zero c3 _ (scan_at byte_z c3 0x539410 0x22bf0 0xde000 x sc_9 ltac:(cbn [Z.of_N]; lia))). discriminate.
Qed.
Lemma rd1_of_rom : forall m (x : word), seg_rom ASEGS x <> None -> rd1 ASEGS m x <> None.
Proof. intros m x H. unfold rd1. destruct (m x); [discriminate | exact H]. Qed.

Lemma rg_ok_ro_p : forall E m A n, pristine m A (A + n) -> 0 <= A -> A + n < two64 -> 0 < n ->
  (forall x, A <= x < A + n -> seg_rom ASEGS (Z_to_bv 64 x) <> None) -> rg_ok ASEGS E m (RGz (lconst A) n RO TEmpty).
Proof.
  intros E m A n HP H0 H1 Hn Hs. unfold rg_ok. rewrite rsz_RGz by (unfold two64 in *; lia). cbn [RGz rg_base rg_kind rg_cont].
  rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64 in *; lia).
  split; [lia|]. split; [unfold two64 in *; lia|]. split.
  - intros i Hi. split; [exact (proj2 (proj2 HP) (A + i) ltac:(lia)) | exact (Hs (A + i) ltac:(lia))].
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

(* [comment removed for export] *)
Definition RGSe : list region :=
  [ RGz (laddc SP (-2528)) 2528 RW TEmpty;
    RG XA (lconst 496) RW TEmpty;
    track (RG (laddc XA 496) (lconst 2) RW TEmpty) 0 [BV LEN 0; BV LEN 1];
    track (RG XS (lconst 63) FxCore.RT TEmpty) 0 (List.repeat (BK 0) 63);
    RG (laddc XS (-8)) (lconst 8) FxCore.RT TEmpty;
    RG (laddc XS 63) (lconst 8) FxCore.RT TEmpty;
    RGz (lconst 0x10000) 0x2e000 RO TEmpty;
    track (RG (lconst (SHB + 0x4a68)) (lconst 32) FxCore.RT TEmpty) 0 (List.repeat (BK 0) 32);
    track (RGz (fsc 40) 8 RW TEmpty) 0 (bv8 H5);
    RG (fsc FL5) P5 RZ TEmpty;
    RG FLB5 (lconst 1) RZ TEmpty;
    RG (ladd (fsc (FL5 + 1)) P5) (laddc (lscale (-1) P5) 511) RZ TEmpty;
    RG SLOT5 (lconst 2048) RW TEmpty;
    RG (laddc SHSLOT5 (-8)) (lconst 8) FxCore.RT TEmpty;
    RG SHSLOT5 (lconst 256) RW TEmpty;
    fs_hdr_c; sb_uar_t ] ++ rt_rgs_t ++ relro_rgs.
Lemma RGSe_eq : LM_RGS = RGSe. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition iv_disj (a b : Z * Z) : Prop := fst a + snd a <= fst b \/ fst b + snd b <= fst a.
Fixpoint pw_disj (l : list (Z * Z)) : Prop := match l with [] => True | iv :: l' => Forall (iv_disj iv) l' /\ pw_disj l' end.
Lemma rgs_disj_of_ivs : forall E rgs ivs,
  Forall2 (fun R iv => bv_unsigned (lden E (rg_base R)) = fst iv /\ rsz E R = snd iv) rgs ivs -> pw_disj ivs -> rgs_disj E rgs.
Proof.
  intros E rgs ivs H. induction H as [|R iv rs ivs' [Hb Hs] H IH]; intros Hp; [exact I|].
  cbn [pw_disj] in Hp. destruct Hp as (Hf & Hp). cbn [rgs_disj]. split; [|exact (IH Hp)].
  clear IH Hp. induction H as [|R' iv' rs' ivs'' [Hb' Hs'] H' IH']; [constructor|].
  apply Forall_cons_iff in Hf as (Hd & Hf). constructor; [|exact (IH' Hf)].
  unfold rg_disj. rewrite Hb, Hs, Hb', Hs'. exact Hd.
Qed.

(* [comment removed for export] *)
Lemma lme_c1 : forall c, (c = 0 \/ c = 16) -> kfrag_ok_fp ASEGS (LM_P0 c) (LM_TAIL_Q c) 0x973c8.
Proof.
  intros c [->| ->].
  - exact (LmThmFp.lm_c1_fp_0 KxSM5.sm5_kfn_fp KxMcpyA.mca_kfn_fp KxMcpyB.mcb_kfn_fp KxMsx.msx_kfn_fp).
  - exact (LmThmFp.lm_c1_fp_16 KxSM5.sm5_kfn_fp KxMcpyA.mca_kfn_fp KxMcpyB.mcb_kfn_fp KxMsx.msx_kfn_fp).
Qed.
Lemma lme_c2 : forall c, (c = 0 \/ c = 16) -> fn_ok_fp ASEGS (LM_EPI_P0 c) (LM_Q c) [0x976b0].
Proof. intros c [->| ->]; [exact (LmThmFp.lm_c2_fp_0 KxSF5.sf5_kfn_fp) | exact (LmThmFp.lm_c2_fp_16 KxSF5.sf5_kfn_fp)]. Qed.

(* [comment removed for export] *)
Lemma mrd_ext : forall (mm mm' : word -> option byte) a, mm' a = mm a -> mrd ASEGS mm' a = mrd ASEGS mm a.
Proof. intros mm mm' a H. unfold mrd. rewrite H. reflexivity. Qed.
Lemma wview_ext : forall (mm mm' : word -> option byte) a, mm' a = mm a -> wview ASEGS mm' a = wview ASEGS mm a.
Proof. intros mm mm' a H. unfold RiscvSemantics.wview. rewrite H. reflexivity. Qed.
Lemma bytes_at_ext_mem : forall mm mm' A bs, bytes_at ASEGS mm A bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mm' (wa (A + i)) = mm (wa (A + i))) -> bytes_at ASEGS mm' A bs.
Proof.
  intros mm mm' A bs (B1 & B2 & B) H. split; [exact B1|]. split; [exact B2|]. intros i Hi.
  rewrite (mrd_ext mm mm' _ (H (Z.of_nat i) ltac:(lia))). exact (B i Hi).
Qed.
Lemma wr_at_ext_mem : forall mm mm' A n, wr_at ASEGS mm A n ->
  (forall i, 0 <= i < n -> mm' (wa (A + i)) = mm (wa (A + i))) -> wr_at ASEGS mm' A n.
Proof.
  intros mm mm' A n (W1 & W2 & W) H. split; [exact W1|]. split; [exact W2|]. intros i Hi.
  rewrite (wview_ext mm mm' _ (H i Hi)). exact (W i Hi).
Qed.
Lemma u64arr_ext_mem : forall mm mm' A ws, u64arr ASEGS mm A ws ->
  (forall i, 0 <= i < 8 * Z.of_nat (length ws) -> mm' (wa (A + i)) = mm (wa (A + i))) -> u64arr ASEGS mm' A ws.
Proof.
  intros mm mm' A ws (B & W) H. split.
  - apply (bytes_at_ext_mem mm mm' A _ B). intros i Hi. rewrite u64s_length in Hi. apply H. lia.
  - exact (wr_at_ext_mem mm mm' A _ W H).
Qed.
Lemma ro_cells_ext_mem : forall mm mm' A cs, ro_cells ASEGS mm A cs ->
  (forall i, 0 <= i < Z.of_nat (length (cells_bytes cs)) -> mm' (wa (A + i)) = mm (wa (A + i))) -> ro_cells ASEGS mm' A cs.
Proof. intros mm mm' A cs (Hw & B) H. split; [exact Hw | exact (bytes_at_ext_mem mm mm' A _ B H)]. Qed.

Lemma in_some_iv : forall (W : list ivl) x, ~ Frame.outside W x -> exists lo hi, In (lo, hi) W /\ lo <= x < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn [Frame.outside] in H; [exfalso; exact (H I)|].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - exists lo, hi. split; [left; reflexivity | lia].
  - destruct (IH x ltac:(intros Ho; apply H; split; [lia | exact Ho])) as (lo' & hi' & Hin & Hr). exists lo', hi'. split; [right; exact Hin | exact Hr].
  - destruct (IH x ltac:(intros Ho; apply H; split; [lia | exact Ho])) as (lo' & hi' & Hin & Hr). exists lo', hi'. split; [right; exact Hin | exact Hr].
Qed.

Lemma outside_dec : forall (W : list ivl) x, Frame.outside W x \/ ~ Frame.outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [Frame.outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros (_ & H'); exact (H H')].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - right. intros (H3 & _). apply H3. lia.
  - left. split; [lia | exact H].
  - left. split; [lia | exact H].
Qed.

Section LME.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ws : list word) (len : Z) (v : rt_vals) (h5 : word) (fb : byte).
Local Notation A := (bv_unsigned a0).
Local Notation FS := (rt_FS v).
Local Notation SPv := (bv_unsigned sp).
(* [comment removed for export] *)
Hypothesis ST : stk ASEGS m (SPv - 2528) SPv.
Hypothesis AL : SPv mod 16 = 0.
Hypothesis SPLO : IMG_END <= SPv - 2528.
Hypothesis PR : pristine m IMG_LO ROD_HI.
Hypothesis LIMBS : u64arr ASEGS m A ws.
Hypothesis L62 : length ws = 62%nat.
Hypothesis LENC : rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 len)].
Hypothesis Hlen : 0 <= len <= 62.
Hypothesis A8 : A mod 8 = 0.
Hypothesis CAP : len + 5 <= LM_T.
Hypothesis SEP : A + 498 <= SPv - 2528 \/ SPv <= A.
Hypothesis TP : tp = Z_to_bv 64 TPV.
Hypothesis Ha1 : a1 = Z_to_bv 64 A_LARGE_POW5.
Hypothesis Ha2 : a2 = Z_to_bv 64 5.
Hypothesis PRG : pristine m RELRO_LO RELRO_HI.
Hypothesis PRT : pristine m REALTAB_LO REALTAB_HI.
Hypothesis RTH : RT m v.
Hypothesis FK : fk5_inv m FS h5.
Hypothesis KSP : KHI <= SPv - 2528.
Hypothesis KSP2 : SPv <= KTOP.
Hypothesis KA0 : app2r A (A + 504).
Hypothesis KA1 : A + 504 <= KTOP.
Hypothesis SFS : FS + FSSIZE <= SPv - 2528.
Hypothesis SEPF : FS + 4231168 <= A /\ A + 632 <= FS + FK5_LO.
Hypothesis RD1 : rt_disj v (SPv - 2528) SPv.
Hypothesis RD2 : rt_disj v A (A + 498).
Hypothesis RD3 : rt_disj v FS (FS + FSSIZE).
Hypothesis SHX : shz ASEGS m (ASAN_B + A / 8) 63.
Hypothesis SHT : shz ASEGS m POW5TAB_SH POW5TAB_SHN.
Hypothesis RBX : rdbl ASEGS m (ASAN_B + A / 8 - 8) 79.
Hypothesis RBF : rdbl ASEGS m (ASAN_B + FS / 8 + FK_SH_LO) FK_SH_N.
Hypothesis RTX0 : RTX v fc.
Hypothesis RAE : bv_unsigned ra mod 2 = 0.
(* [comment removed for export] *)
Hypothesis Hfb : ro_cells ASEGS m 1534321 [C1 fb] /\ bv_unsigned fb <> 0.

(* [comment removed for export] *)
Definition E : valu := fun x =>
  match x with
  | 4%positive => sp
  | 5%positive => ra
  | 10%positive => Z_to_bv 64 (FS / 4096)
  | 13%positive => h5
  | 14%positive => Z_to_bv 64 (bv_unsigned h5 mod 512)
  | 15%positive => Z_to_bv 64 (rt_ctx v)
  | 16%positive => Z_to_bv 64 (rt_thr v)
  | 17%positive => Z_to_bv 64 (rt_blk v)
  | 18%positive => Z_to_bv 64 (rt_beg v)
  | 19%positive => Z_to_bv 64 (rt_tlsb v)
  | 20%positive => Z_to_bv 64 (rt_tlse v)
  | 21%positive => Z_to_bv 64 (bv_unsigned fb)
  | 30%positive => Z_to_bv 64 (A / 8)
  | 31%positive => Z_to_bv 64 len
  | 103%positive => gp
  | 105%positive => t0
  | 106%positive => t1
  | 107%positive => t2
  | 108%positive => s0
  | 109%positive => s1
  | 113%positive => a3
  | 114%positive => a4
  | 115%positive => a5
  | 116%positive => a6
  | 117%positive => a7
  | 118%positive => s2
  | 119%positive => s3
  | 120%positive => s4
  | 121%positive => s5
  | 122%positive => s6
  | 123%positive => s7
  | 124%positive => s8
  | 125%positive => s9
  | 126%positive => s10
  | 127%positive => s11
  | 128%positive => t3
  | 129%positive => t4
  | 130%positive => t5
  | 131%positive => t6
  | _ => Z_to_bv 64 0
  end.
#[using="Type"] Lemma HE4 : E 4%positive = sp. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE5 : E 5%positive = ra. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE10 : E 10%positive = Z_to_bv 64 (FS / 4096). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE13 : E 13%positive = h5. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE14 : E 14%positive = Z_to_bv 64 (bv_unsigned h5 mod 512). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE15 : E 15%positive = Z_to_bv 64 (rt_ctx v). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE16 : E 16%positive = Z_to_bv 64 (rt_thr v). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE17 : E 17%positive = Z_to_bv 64 (rt_blk v). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE18 : E 18%positive = Z_to_bv 64 (rt_beg v). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE19 : E 19%positive = Z_to_bv 64 (rt_tlsb v). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE20 : E 20%positive = Z_to_bv 64 (rt_tlse v). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE21 : E 21%positive = Z_to_bv 64 (bv_unsigned fb). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE30 : E 30%positive = Z_to_bv 64 (A / 8). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE31 : E 31%positive = Z_to_bv 64 len. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE103 : E 103%positive = gp. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE105 : E 105%positive = t0. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE106 : E 106%positive = t1. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE107 : E 107%positive = t2. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE108 : E 108%positive = s0. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE109 : E 109%positive = s1. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE113 : E 113%positive = a3. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE114 : E 114%positive = a4. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE115 : E 115%positive = a5. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE116 : E 116%positive = a6. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE117 : E 117%positive = a7. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE118 : E 118%positive = s2. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE119 : E 119%positive = s3. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE120 : E 120%positive = s4. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE121 : E 121%positive = s5. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE122 : E 122%positive = s6. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE123 : E 123%positive = s7. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE124 : E 124%positive = s8. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE125 : E 125%positive = s9. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE126 : E 126%positive = s10. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE127 : E 127%positive = s11. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE128 : E 128%positive = t3. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE129 : E 129%positive = t4. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE130 : E 130%positive = t5. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma HE131 : E 131%positive = t6. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

(* [comment removed for export] *)
#[using="ra sp a0 fc m ws L62 RTH RTX0"] Lemma lme_rt :
  app2r FS (FS + 11571200) /\ FS + 11571200 <= KTOP /\ FS mod 4096 = 0 /\
  rt_app (rt_ctx v) 160 /\ rt_ctx v + 160 <= KTOP /\ rt_app (rt_thr v) 80 /\ rt_thr v + 80 <= KTOP /\
  rt_app (rt_blk v) 32 /\ rt_blk v + 32 <= KTOP /\ 0 < rt_beg v < two64 /\
  6529024 <= rt_ctx v /\ 4096 <= rt_thr v /\ 4096 <= rt_blk v /\ rt_ctx v mod 8 = 0 /\ rt_thr v mod 8 = 0 /\ rt_blk v mod 8 = 0.
Proof. LiaFast.lf_pins (fun (ra sp a0 fc m ws L62 RTH RTX0 : LiaFast.U) => LiaFast.u0).
  pose proof RTH as R. unfold RT in R.
  destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hbeg & _ & _ & _ & _ & F1 & F2 & F3 & C1 & C2 & T1 & T2 & B1 & B2)).
  destruct RTX0 as ((X1 & X2 & X3 & X4 & X5 & X6) & _).
  unfold two64, KTOP in *. repeat split; try assumption; lia.
Qed.

#[using="fc m ws L62 Hlen RTH RTX0 Hfb"] Lemma vz_vals :
  vz E 4 = SPv /\ vz E 5 = bv_unsigned ra /\ vz E 10 = FS / 4096 /\ vz E 13 = bv_unsigned h5 /\ vz E 14 = bv_unsigned h5 mod 512 /\
  vz E 15 = rt_ctx v /\ vz E 16 = rt_thr v /\ vz E 17 = rt_blk v /\ vz E 18 = rt_beg v /\ vz E 21 = bv_unsigned fb /\
  vz E 30 = A / 8 /\ vz E 31 = len.
Proof. LiaFast.lf_pins (fun (fc m ws L62 Hlen RTH RTX0 Hfb : LiaFast.U) => LiaFast.u0).
  pose proof lme_rt as (Fa & Fk & Fm & Ca & Ck & Ta & Tk & Ba & Bk & Hbeg & _).
  pose proof (bv_unsigned_in_range _ h5) as Bh. pose proof (bv_unsigned_in_range _ fb) as Bf. pose proof (bv_unsigned_in_range _ a0) as Ba0.
  unfold bv_modulus in Bh, Bf, Ba0. change (2 ^ Z.of_N 64) with two64 in Bh, Ba0. change (2 ^ Z.of_N 8) with 256 in Bf.
  pose proof (Z.mod_pos_bound (bv_unsigned h5) 512 ltac:(lia)) as Mh.
  assert (Dfs : 0 <= FS / 4096 < two64) by (unfold app2r in Fa; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; unfold two64; lia).
  assert (Da : 0 <= A / 8 < two64) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; unfold two64 in *; lia).
  unfold vz. rewrite HE4, HE5, HE10, HE13, HE14, HE15, HE16, HE17, HE18, HE21, HE30, HE31, !u_Z_to_bv.
  unfold app2r, rt_app in *. unfold two64 in *.
  unfold KTOP, KHI in *. repeat split; try reflexivity; apply Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
Ltac fnorm :=
  cbn [fact_ok]; lnorm_s; rewrite ?u_Z_to_bv;
  repeat match goal with |- context [bv_unsigned (E ?x)] => change (bv_unsigned (E x)) with (vz E x) end;
  pose proof vz_vals as (V4 & V5 & V10 & V13 & V14 & V15 & V16 & V17 & V18 & V21 & V30 & V31);
  rewrite ?V4, ?V5, ?V10, ?V13, ?V14, ?V15, ?V16, ?V17, ?V18, ?V21, ?V30, ?V31;
  clear V4 V5 V10 V13 V14 V15 V16 V17 V18 V21 V30 V31.


Ltac facts_pre :=
  pose proof lme_rt as (Fa & Fk & Fm & Ca & Ck & Ta & Tk & Ba & Bk & Hbeg & Cl & Tl & Bl & Cm & Tm & Bm);
  pose proof (bv_unsigned_in_range _ sp) as Bsp; pose proof (bv_unsigned_in_range _ ra) as Bra;
  pose proof (bv_unsigned_in_range _ h5) as Bh; pose proof (bv_unsigned_in_range _ fb) as Bf; pose proof (bv_unsigned_in_range _ a0) as Ba0;
  unfold bv_modulus in Bsp, Bra, Bh, Bf, Ba0; change (2 ^ Z.of_N 64) with two64 in Bsp, Bra, Bh, Ba0; change (2 ^ Z.of_N 8) with 256 in Bf;
  pose proof (Z.mod_pos_bound (bv_unsigned h5) 512 ltac:(lia)) as Mh; pose proof (Z.div_mod (bv_unsigned h5) 512 ltac:(lia)) as Dh;
  assert (EF : FS = 4096 * (FS / 4096)) by (pose proof (Z.div_mod FS 4096 ltac:(lia)); lia);
  assert (EA : A = 8 * (A / 8)) by (pose proof (Z.div_mod A 8 ltac:(lia)); lia);
  destruct Hfb as (_ & Hfb0); destruct SEPF as (SEPF1 & SEPF2);
  unfold rt_disj in RD1, RD3; destruct RD1 as (R1c & R1t & R1b); destruct RD3 as (R3c & R3t & R3b);
  unfold app2r, rt_app in *.
Ltac facts_post :=
  change (2 ^ 1) with 2; change (2 ^ 3) with 8; change (2 ^ 5) with 32; change (2 ^ 9) with 512;
  change (IMG_END / 4096) with 1594; change ((KTOP - 0xb09000) / 4096) with 34359735543;
  unfold IMG_END, KTOP, KHI, SH_LO in *.

#[using="fc m ws L62 Hlen A8 CAP RTH KSP KSP2 SFS SEPF RD1 RD3 RTX0 RAE Hfb"] Lemma lme_facts_0 : SPv mod 32 = 0 -> Forall (fact_ok E) (LM_F 0).
Proof. LiaFast.lf_pins (fun (fc m ws L62 Hlen A8 CAP RTH KSP KSP2 SFS SEPF RD1 RD3 RTX0 RAE Hfb : LiaFast.U) => LiaFast.u0).
  intros Hcl. facts_pre.
  unfold LM_F, fks5_facts, rt_facts, two_class, two_class4k; cbn [app List.flat_map List.map].
  repeat apply Forall_cons; try apply Forall_nil; fnorm; facts_post.
  - (* [comment removed for export] *) exact Hcl.
  - (* [comment removed for export] *) clear -KSP KSP2 Bsp; rewrite Z.mod_small by (unfold two64 in *; lia); lia.
  - (* [comment removed for export] *) exact RAE.
  - (* [comment removed for export] *) clear -Hlen CAP; lia.
  - (* [comment removed for export] *) clear -EF EA SEPF1 SEPF2 Fa Fk; unfold two64 in *; rewrite Z.mod_small by lia; lia.
  - (* [comment removed for export] *) clear -EF EA SEPF1 SEPF2 Fa Fk; unfold two64 in *; rewrite Z.mod_small by lia; lia.
  - (* [comment removed for export] *) clear -EF SFS KSP KSP2 Fa Fk Bsp; unfold two64 in *; rewrite Z.mod_small by lia; lia.
  - (* [comment removed for export] *) clear -Mh; lia.
  - (* [comment removed for export] *) clear -Mh Dh Bh; rewrite (Z.mod_small _ two64) by (unfold two64 in *; lia); match goal with |- ?z mod 512 = 0 => replace z with ((bv_unsigned h5 / 512) * 512) by lia end; apply Z_mod_mult.
  - (* [comment removed for export] *) clear -EF Fa Fk; lia.
  - (* [comment removed for export] *) clear -Fa Fk EF; frange.
  - (* [comment removed for export] *) clear -Cl Ck; lia.
  - (* [comment removed for export] *) clear -Ca Ck Cl; frange.
  - (* [comment removed for export] *) clear -Tl Tk; lia.
  - (* [comment removed for export] *) clear -Ta Tk Tl; frange.
  - (* [comment removed for export] *) clear -Bl Bk; lia.
  - (* [comment removed for export] *) clear -Ba Bk Bl; frange.
  - (* [comment removed for export] *) clear -Hbeg; unfold two64 in *; lia.
  - (* [comment removed for export] *) clear -Bf Hfb0; lia.
  - (* [comment removed for export] *) exact Cm.
  - (* [comment removed for export] *) exact Tm.
  - (* [comment removed for export] *) exact Bm.
  - (* [comment removed for export] *) clear -R3c Cl Ck Fa Fk EF; frange.
  - (* [comment removed for export] *) clear -R3t Tl Tk Fa Fk EF; frange.
  - (* [comment removed for export] *) clear -R3b Bl Bk Fa Fk EF; frange.
  - (* [comment removed for export] *) clear -R1c Cl Ck Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1t Tl Tk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1b Bl Bk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1c Cl Ck Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1c Cl Ck Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1c Cl Ck Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1c Cl Ck Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1t Tl Tk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1t Tl Tk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1t Tl Tk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1t Tl Tk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1b Bl Bk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1b Bl Bk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1b Bl Bk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1b Bl Bk Bsp KSP; frange.
Qed.

#[using="fc m ws L62 Hlen A8 CAP RTH KSP KSP2 SFS SEPF RD1 RD3 RTX0 RAE Hfb"] Lemma lme_facts_16 : SPv mod 32 = 16 -> Forall (fact_ok E) (LM_F 16).
Proof. LiaFast.lf_pins (fun (fc m ws L62 Hlen A8 CAP RTH KSP KSP2 SFS SEPF RD1 RD3 RTX0 RAE Hfb : LiaFast.U) => LiaFast.u0).
  intros Hcl. facts_pre.
  unfold LM_F, fks5_facts, rt_facts, two_class, two_class4k; cbn [app List.flat_map List.map].
  repeat apply Forall_cons; try apply Forall_nil; fnorm; facts_post.
  - (* [comment removed for export] *) exact Hcl.
  - (* [comment removed for export] *) clear -KSP KSP2 Bsp; rewrite Z.mod_small by (unfold two64 in *; lia); lia.
  - (* [comment removed for export] *) exact RAE.
  - (* [comment removed for export] *) clear -Hlen CAP; lia.
  - (* [comment removed for export] *) clear -EF EA SEPF1 SEPF2 Fa Fk; unfold two64 in *; rewrite Z.mod_small by lia; lia.
  - (* [comment removed for export] *) clear -EF EA SEPF1 SEPF2 Fa Fk; unfold two64 in *; rewrite Z.mod_small by lia; lia.
  - (* [comment removed for export] *) clear -EF SFS KSP KSP2 Fa Fk Bsp; unfold two64 in *; rewrite Z.mod_small by lia; lia.
  - (* [comment removed for export] *) clear -Mh; lia.
  - (* [comment removed for export] *) clear -Mh Dh Bh; rewrite (Z.mod_small _ two64) by (unfold two64 in *; lia); match goal with |- ?z mod 512 = 0 => replace z with ((bv_unsigned h5 / 512) * 512) by lia end; apply Z_mod_mult.
  - (* [comment removed for export] *) clear -EF Fa Fk; lia.
  - (* [comment removed for export] *) clear -Fa Fk EF; frange.
  - (* [comment removed for export] *) clear -Cl Ck; lia.
  - (* [comment removed for export] *) clear -Ca Ck Cl; frange.
  - (* [comment removed for export] *) clear -Tl Tk; lia.
  - (* [comment removed for export] *) clear -Ta Tk Tl; frange.
  - (* [comment removed for export] *) clear -Bl Bk; lia.
  - (* [comment removed for export] *) clear -Ba Bk Bl; frange.
  - (* [comment removed for export] *) clear -Hbeg; unfold two64 in *; lia.
  - (* [comment removed for export] *) clear -Bf Hfb0; lia.
  - (* [comment removed for export] *) exact Cm.
  - (* [comment removed for export] *) exact Tm.
  - (* [comment removed for export] *) exact Bm.
  - (* [comment removed for export] *) clear -R3c Cl Ck Fa Fk EF; frange.
  - (* [comment removed for export] *) clear -R3t Tl Tk Fa Fk EF; frange.
  - (* [comment removed for export] *) clear -R3b Bl Bk Fa Fk EF; frange.
  - (* [comment removed for export] *) clear -R1c Cl Ck Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1t Tl Tk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1b Bl Bk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1c Cl Ck Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1c Cl Ck Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1c Cl Ck Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1c Cl Ck Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1t Tl Tk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1t Tl Tk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1t Tl Tk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1t Tl Tk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1b Bl Bk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1b Bl Bk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1b Bl Bk Bsp KSP; frange.
  - (* [comment removed for export] *) clear -R1b Bl Bk Bsp KSP; frange.
Qed.

#[using="fc m ws AL L62 Hlen A8 CAP RTH KSP KSP2 SFS SEPF RD1 RD3 RTX0 RAE Hfb"] Lemma lme_facts : forall c, bv_unsigned sp mod 32 = c -> Forall (fact_ok E) (LM_F c).
Proof. LiaFast.lf_pins (fun (fc m ws AL L62 Hlen A8 CAP RTH KSP KSP2 SFS SEPF RD1 RD3 RTX0 RAE Hfb : LiaFast.U) => LiaFast.u0).
  intros c Hcl. assert (Hcc : c = 0 \/ c = 16) by (rewrite <- Hcl; clear -AL; Z.div_mod_to_equations; lia).
  destruct Hcc as [->| ->]; [exact (lme_facts_0 Hcl) | exact (lme_facts_16 Hcl)].
Qed.

(* [comment removed for export] *)
Ltac bvc := lnorm_s; rewrite ?u_Z_to_bv;
  repeat match goal with |- context [bv_unsigned (E ?x)] => change (bv_unsigned (E x)) with (vz E x) end;
  pose proof vz_vals as (V4 & V5 & V10 & V13 & V14 & V15 & V16 & V17 & V18 & V21 & V30 & V31);
  rewrite ?V4, ?V5, ?V10, ?V13, ?V14, ?V15, ?V16, ?V17, ?V18, ?V21, ?V30, ?V31;
  clear V4 V5 V10 V13 V14 V15 V16 V17 V18 V21 V30 V31.

(* [comment removed for export] *)
#[using="ra fc m ws L62 A8 RTH KSP KSP2 SFS SEPF RTX0"] Lemma lme_pl :
  KHI <= SPv - 2528 /\ SPv <= KTOP /\ 6529024 <= FS /\ FS + 11571200 <= SPv - 2528 /\ FS mod 4096 = 0 /\
  FS + 4231168 <= A /\ A + 632 <= FS + 5279744 /\ A mod 8 = 0 /\ 0 <= bv_unsigned h5 mod 512 < 512.
Proof. LiaFast.lf_pins (fun (ra fc m ws L62 A8 RTH KSP KSP2 SFS SEPF RTX0 : LiaFast.U) => LiaFast.u0).
  pose proof lme_rt as (Fa & _ & Fm & _).
  pose proof (Z.mod_pos_bound (bv_unsigned h5) 512 ltac:(lia)) as Mh.
  destruct SEPF as (S1 & S2). unfold app2r in Fa. repeat split; try assumption; lia.
Qed.

#[using="fc m ws L62 Hlen A8 SEP RTH KSP KSP2 KA1 SFS SEPF RTX0 Hfb"] Lemma lme_bases :
  bv_unsigned (lden E (laddc SP (-2528))) = SPv - 2528 /\
  bv_unsigned (lden E XA) = A /\
  bv_unsigned (lden E (laddc XA 496)) = A + 496 /\
  bv_unsigned (lden E XS) = ASAN_B + A / 8 /\
  bv_unsigned (lden E (laddc XS (-8))) = ASAN_B + A / 8 - 8 /\
  bv_unsigned (lden E (laddc XS 63)) = ASAN_B + A / 8 + 63 /\
  bv_unsigned (lden E (fsc 40)) = FS + 40 /\
  bv_unsigned (lden E (fsc FL5)) = FS + 35840 /\
  bv_unsigned (lden E FLB5) = FS + 35840 + bv_unsigned h5 mod 512 /\
  bv_unsigned (lden E (ladd (fsc (FL5 + 1)) P5)) = FS + 35841 + bv_unsigned h5 mod 512 /\
  bv_unsigned (lden E SLOT5) = FS + 5279744 + 2048 * (bv_unsigned h5 mod 512) /\
  bv_unsigned (lden E (laddc SHSLOT5 (-8))) = ASAN_B + FS / 8 + 659968 + 256 * (bv_unsigned h5 mod 512) - 8 /\
  bv_unsigned (lden E SHSLOT5) = ASAN_B + FS / 8 + 659968 + 256 * (bv_unsigned h5 mod 512) /\
  bv_unsigned (lden E (fsc 88)) = FS + 88.
Proof. LiaFast.lf_pins (fun (fc m ws L62 Hlen A8 SEP RTH KSP KSP2 KA1 SFS SEPF RTX0 Hfb : LiaFast.U) => LiaFast.u0).
  pose proof lme_pl as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  assert (EF : FS = 4096 * (FS / 4096)) by (pose proof (Z.div_mod FS 4096 ltac:(lia)); lia).
  assert (EF8 : FS / 8 = 512 * (FS / 4096)) by (rewrite EF at 1; replace (4096 * (FS / 4096)) with ((512 * (FS / 4096)) * 8) by ring; apply Z.div_mul; lia).
  assert (EA : A = 8 * (A / 8)) by (pose proof (Z.div_mod A 8 ltac:(lia)); lia).
  unfold KHI, KTOP in *.
  repeat split; bvc; rewrite ?EF8; rewrite Z.mod_small by (unfold two64; lia); lia.
Qed.

#[using="fc m ws L62 Hlen RTH RTX0 Hfb"] Lemma lme_bases2 : bv_unsigned (lden E (laddc CTX 152)) = rt_ctx v + 152 /\ bv_unsigned (lden E (laddc THR 48)) = rt_thr v + 48 /\
  bv_unsigned (lden E (laddc BLK 24)) = rt_blk v + 24.
Proof. LiaFast.lf_pins (fun (fc m ws L62 Hlen RTH RTX0 Hfb : LiaFast.U) => LiaFast.u0).
  pose proof vz_vals as (_ & _ & _ & _ & _ & V15 & V16 & V17 & _). pose proof lme_rt as (_ & _ & _ & _ & Ck & _ & Tk & _ & Bk & _).
  unfold vz in V15, V16, V17. unfold KTOP in *.
  rewrite (u_ctx152 E ltac:(rewrite V15; lia)), (u_thr48 E ltac:(rewrite V16; lia)), (u_blk24 E ltac:(rewrite V17; lia)), V15, V16, V17.
  repeat split.
Qed.

#[using="fc m ws L62 Hlen A8 RTH KSP KSP2 SFS SEPF RTX0 Hfb"] Lemma lden_FS : lden E OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_tmpl.FS = Z_to_bv 64 (rt_FS v).
Proof. LiaFast.lf_pins (fun (fc m ws L62 Hlen A8 RTH KSP KSP2 SFS SEPF RTX0 Hfb : LiaFast.U) => LiaFast.u0).
  pose proof vz_vals as (_ & _ & V10 & _).
  pose proof lme_pl as (_ & _ & Q3 & _ & Q5 & _).
  lnorm. f_equal. rewrite V10. pose proof (Z.div_mod (rt_FS v) 4096 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cells_bytes_at : forall A cs, ro_cells ASEGS m A cs -> bytes_at ASEGS m A (cells_bytes cs).
Proof. LiaFast.lf_pins LiaFast.u0. intros A cs (_ & B). exact B. Qed.
#[using="Type"] Lemma rw_cells_bytes_at : forall A cs, rw_cells ASEGS m A cs -> bytes_at ASEGS m A (cells_bytes cs).
Proof. LiaFast.lf_pins LiaFast.u0. intros A cs ((_ & B) & _). exact B. Qed.

Ltac rszc := unfold rsz; cbn [rg_size track RGz]; rewrite ?lden_lconst, ?u_Z_to_bv, ?Z.mod_small by (unfold two64; lia);
  first [ lia | (apply Z.leb_le; vm_compute; reflexivity) ].

(* [comment removed for export] *)
Ltac img_rt R0 A n lo hi :=
  apply (rg_ok_rt_of_rd ASEGS E m R0 A n); [reflexivity | reflexivity | cbn [rg_base RGz]; rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia); reflexivity
                                      | unfold rsz; cbn [rg_size RGz]; rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia); reflexivity
                                      | lia | unfold two64; lia
                                      | intros i Hi; rewrite <- rd1_mrd; apply rd1_of_rom; first [apply rom_ok3z; lia | apply rom_ok3y; lia | apply rom_ok3a; lia | apply rom_ok3w; lia] ].

#[using="fc ws ST PR LIMBS L62 LENC Hlen A8 SEP PRG PRT RTH FK KSP KSP2 KA1 SFS SEPF SHX SHT RBX RBF RTX0 Hfb"] Lemma lme_rgs : Forall (rg_ok ASEGS E m) RGSe.
Proof. LiaFast.lf_pins (fun (fc ws ST PR LIMBS L62 LENC Hlen A8 SEP PRG PRT RTH FK KSP KSP2 KA1 SFS SEPF SHX SHT RBX RBF RTX0 Hfb : LiaFast.U) => LiaFast.u0).
  pose proof lme_pl as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  pose proof lme_bases as (B0 & B1 & B2 & B3 & B4 & B5 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15).
  pose proof lme_bases2 as (B25 & B26 & B27).
  pose proof RTH as RTq. unfold RT in RTq.
  destruct RTq as (K1 & K2 & K3 & K4 & K5 & _ & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & _).
  destruct FK as (FK0 & FK1 & FK2 & FK3 & FK4).
  pose proof (bv_unsigned_in_range _ a0) as Ba0. unfold bv_modulus in Ba0. change (2 ^ Z.of_N 64) with two64 in Ba0.
  pose proof lme_rt as (_ & _ & _ & _ & Ck & _ & Tk & _ & Bk & _ & Cl & Tl & Bl & _).
  set (p := bv_unsigned h5 mod 512) in *.
  unfold RGSe, rt_rgs_t, relro_rgs, fs_hdr_c, sb_uar_t. cbn [app].
  unfold KHI, KTOP in *.
  repeat apply Forall_cons; try apply Forall_nil.
  - (* [comment removed for export] *)
    apply (rg_ok_of_stk ASEGS E m _ (SPv - 2528) SPv); [reflexivity | reflexivity | exact B0 | | lia | exact ST].
    rewrite rsz_RGz by (unfold two64; lia). lia.
  - (* [comment removed for export] *)
    apply (rg_ok_of_u64arr ASEGS E m _ A ws); [reflexivity | reflexivity | exact B1 | | exact LIMBS].
    unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). rewrite L62. reflexivity.
  - (* [comment removed for export] *)
    apply track_of_bytes_at; [ | lia | cbn [length]; unfold rsz; cbn [rg_size]; rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia); lia | ].
    + apply (rg_ok_of_rw_cells ASEGS E m _ (A + 496) [C2 (Z_to_bv 64 len)]); [reflexivity | reflexivity | exact B2 | | exact LENC].
      unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). reflexivity.
    + cbn [rg_base]. rewrite B2, Z.add_0_r. apply (bytes_at_ext ASEGS _ _ _ _ (rw_cells_bytes_at _ _ LENC)).
      cbn [cells_bytes cbytes List.map bden]. rewrite app_nil_r. unfold le2. cbn [Z_to_le_bytes].
      change (lden E LEN) with (lden E (lvar 31)). rewrite lden_lvar, HE31, Z.shiftr_0_r. reflexivity.
  - (* [comment removed for export] *)
    destruct SHX as (_ & SX).
    apply track_of_bytes_at; [ | lia | cbn; unfold rsz; cbn [rg_size]; rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia); lia | ].
    + apply (rg_ok_rt_of_bytes_at ASEGS E m _ (ASAN_B + A / 8) (zeros 63)); [reflexivity | reflexivity | exact B3 | | exact SX].
      unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). reflexivity.
    + cbn [rg_base]. rewrite B3, Z.add_0_r, map_repeat. exact SX.
  - (* [comment removed for export] *)
    destruct RBX as (RB1 & RB2 & RB).
    apply (rg_ok_rt_of_rd ASEGS E m _ (ASAN_B + A / 8 - 8) 8); [reflexivity | reflexivity | exact B4 | | lia | unfold two64; lia | ].
    + unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). reflexivity.
    + intros i Hi. destruct (RB i ltac:(lia)) as (b & Hb). rewrite Hb. discriminate.
  - (* [comment removed for export] *)
    destruct RBX as (RB1 & RB2 & RB).
    apply (rg_ok_rt_of_rd ASEGS E m _ (ASAN_B + A / 8 + 63) 8); [reflexivity | reflexivity | exact B5 | | lia | unfold two64; lia | ].
    + unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). reflexivity.
    + intros i Hi. destruct (RB (71 + i) ltac:(lia)) as (b & Hb). replace (ASAN_B + A / 8 - 8 + (71 + i)) with (ASAN_B + A / 8 + 63 + i) in Hb by ring.
      rewrite Hb. discriminate.
  - (* [comment removed for export] *)
    apply rg_ok_ro_p; [exact PR | lia | unfold two64; lia | lia | intros x Hx; apply rom_ok0; lia].
  - (* [comment removed for export] *)
    destruct SHT as (_ & ST7).
    apply track_of_bytes_at; [ | lia | cbn; unfold rsz; cbn [rg_size]; rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia); lia | ].
    + apply (rg_ok_rt_of_bytes_at ASEGS E m _ POW5TAB_SH (zeros 32)); [reflexivity | reflexivity | | | exact ST7].
      * cbn [rg_base]. rewrite lden_lconst. reflexivity.
      * unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). reflexivity.
    + cbn [rg_base]. rewrite lden_lconst. change (bv_unsigned (Z_to_bv 64 (SHB + 0x4a68)) + 0) with 2147469928. rewrite map_repeat. exact ST7.
  - (* [comment removed for export] *)
    apply track_of_bytes_at; [ | lia | rszc | ].
    + apply (rg_ok_of_rw_cells ASEGS E m _ (FS + 40) [C8 h5]); [reflexivity | reflexivity | exact B8 | | exact FK1].
      rewrite rsz_RGz by (unfold two64; lia). reflexivity.
    + cbn [rg_base RGz]. rewrite B8, Z.add_0_r. unfold bv8. rewrite map_bden_bv8. change (lden E H5) with (lden E (lvar 13)). rewrite lden_lvar, HE13.
      apply (bytes_at_ext ASEGS _ _ _ _ (rw_cells_bytes_at _ _ FK1)). cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
  - (* [comment removed for export] *)
    destruct FK2 as ((FB1 & FB2 & FBy) & (FW1 & FW2 & FW)). rewrite zeros_length in FB2, FW2, FBy, FW.
    apply (rg_ok_rz_of ASEGS E m _ (FS + 35840) p); [reflexivity | reflexivity | exact B9 | | lia | unfold two64; lia | ].
    + unfold rsz. cbn [rg_size]. change (lden E P5) with (lden E (lvar 14)). rewrite lden_lvar, HE14, u_Z_to_bv, Z.mod_small by (unfold two64; lia). reflexivity.
    + intros i Hi. split; [|exact (FW i ltac:(lia))]. pose proof (FBy (Z.to_nat i) ltac:(lia)) as X.
      rewrite Z2Nat.id in X by lia. rewrite X. unfold zeros. rewrite nth_error_repeat by lia. reflexivity.
  - (* [comment removed for export] *)
    destruct FK2 as ((FB1 & FB2 & FBy) & (FW1 & FW2 & FW)). rewrite zeros_length in FB2, FW2, FBy, FW.
    apply (rg_ok_rz_of ASEGS E m _ (FS + 35840 + p) 1); [reflexivity | reflexivity | exact B10 | | lia | unfold two64; lia | ].
    + unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). reflexivity.
    + intros i Hi. split; [|replace (FS + 35840 + p + i) with (FS + 35840 + (p + i)) by ring; exact (FW (p + i) ltac:(lia))].
      pose proof (FBy (Z.to_nat (p + i)) ltac:(lia)) as X.
      rewrite Z2Nat.id in X by lia. replace (FS + 35840 + p + i) with (FS + 35840 + (p + i)) by ring. rewrite X. unfold zeros. rewrite nth_error_repeat by lia. reflexivity.
  - (* [comment removed for export] *)
    destruct FK2 as ((FB1 & FB2 & FBy) & (FW1 & FW2 & FW)). rewrite zeros_length in FB2, FW2, FBy, FW.
    apply (rg_ok_rz_of ASEGS E m _ (FS + 35841 + p) (511 - p)); [reflexivity | reflexivity | exact B11 | | lia | unfold two64; lia | ].
    + unfold rsz. cbn [rg_size]. bvc. rewrite Z.mod_small by (unfold two64; lia). lia.
    + intros i Hi. split; [|replace (FS + 35841 + p + i) with (FS + 35840 + (p + 1 + i)) by ring; exact (FW (p + 1 + i) ltac:(lia))].
      pose proof (FBy (Z.to_nat (p + 1 + i)) ltac:(lia)) as X.
      rewrite Z2Nat.id in X by lia. replace (FS + 35841 + p + i) with (FS + 35840 + (p + 1 + i)) by ring. rewrite X. unfold zeros. rewrite nth_error_repeat by lia. reflexivity.
  - (* [comment removed for export] *)
    apply (rg_ok_of_stk ASEGS E m _ (FS + 5279744 + 2048 * p) (FS + 5279744 + 2048 * p + 2048)); [reflexivity | reflexivity | exact B12 | | lia | ].
    + unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). lia.
    + destruct (stk_split ASEGS _ _ (FS + 5279744 + 2048 * p) _ FK3 ltac:(lia)) as (_ & S1).
      destruct (stk_split ASEGS _ _ (FS + 5279744 + 2048 * p + 2048) _ S1 ltac:(lia)) as (S2 & _). exact S2.
  - (* [comment removed for export] *)
    destruct RBF as (RF1 & RF2 & RF).
    apply (rg_ok_rt_of_rd ASEGS E m _ (ASAN_B + FS / 8 + 659968 + 256 * p - 8) 8); [reflexivity | reflexivity | exact B13 | | lia | unfold two64 in *; lia | ].
    + unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). reflexivity.
    + intros i Hi. destruct (RF (262136 + 256 * p + i) ltac:(lia)) as (b & Hb).
      replace (ASAN_B + FS / 8 + FK_SH_LO + (262136 + 256 * p + i)) with (ASAN_B + FS / 8 + 659968 + 256 * p - 8 + i) in Hb by ring.
      rewrite Hb. discriminate.
  - (* [comment removed for export] *)
    apply (rg_ok_of_stk ASEGS E m _ (ASAN_B + FS / 8 + 659968 + 256 * p) (ASAN_B + FS / 8 + 659968 + 256 * p + 256)); [reflexivity | reflexivity | exact B14 | | lia | ].
    + unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). lia.
    + destruct (stk_split ASEGS _ _ (ASAN_B + FS / 8 + 659968 + 256 * p) _ FK4 ltac:(lia)) as (_ & S1).
      destruct (stk_split ASEGS _ _ (ASAN_B + FS / 8 + 659968 + 256 * p + 256) _ S1 ltac:(lia)) as (S2 & _). exact S2.
  - (* [comment removed for export] *)
    unfold fs_cells_ok in FK0.
    apply track_of_bytes_at; [ | lia | rszc | ].
    + apply (rg_ok_rt_of_bytes_at ASEGS E m _ (FS + 88) (cells_bytes [C8 (Z_to_bv 64 20); C1 (Z_to_bv 8 0)])); [reflexivity | reflexivity | exact B15 | | exact (cells_bytes_at _ _ FK0)].
      rewrite rsz_RGz by (unfold two64; lia). reflexivity.
    + cbn [rg_base RGz]. rewrite B15, Z.add_0_r. apply (bytes_at_ext ASEGS _ _ _ _ (cells_bytes_at _ _ FK0)). apply bytes_eqb_eq. vm_compute. reflexivity.
  - (* [comment removed for export] *)
    apply track_of_bytes_at; [ img_rt (RGz (lconst 0xe4db8) 12 FxCore.RT TEmpty) 0xe4db8 12 0 0 | lia | rszc | ].
    cbn [rg_base RGz]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). rewrite Z.add_0_r.
    apply (bytes_at_ext ASEGS _ _ _ _ (cells_bytes_at _ _ K1)). apply bytes_eqb_eq. vm_compute. reflexivity.
  - (* [comment removed for export] *)
    change (RG (lconst 0xe4620) (lconst 8) FxCore.RT (put_bytes (put_bytes TEmpty 0 [BK 1]) 4 (bkn 4 0))) with
           (track (track (RGz (lconst 0xe4620) 8 FxCore.RT TEmpty) 0 [BK 1]) 4 (bkn 4 0)).
    apply track_of_bytes_at; [ apply track_of_bytes_at; [ img_rt (RGz (lconst 0xe4620) 8 FxCore.RT TEmpty) 0xe4620 8 0 0 | lia | rszc | ] | lia | rszc | ].
    + cbn [rg_base RGz]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). rewrite Z.add_0_r.
      apply (bytes_at_ext ASEGS _ _ _ _ (cells_bytes_at _ _ K2)). apply bytes_eqb_eq. vm_compute. reflexivity.
    + cbn [rg_base RGz track]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia).
      apply (bytes_at_ext ASEGS _ _ _ _ (cells_bytes_at _ _ K3)). apply bytes_eqb_eq. vm_compute. reflexivity.
  - (* [comment removed for export] *)
    apply track_of_bytes_at; [ img_rt (RGz (lconst 0xe5a98) 2 FxCore.RT TEmpty) 0xe5a98 2 0 0 | lia | rszc | ].
    cbn [rg_base RGz]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). rewrite Z.add_0_r.
    apply (bytes_at_ext ASEGS _ _ _ _ (cells_bytes_at _ _ K4)). apply bytes_eqb_eq. vm_compute. reflexivity.
  - (* [comment removed for export] *)
    apply track_of_bytes_at; [ img_rt (RGz (lconst 0xe5aa0) 24 FxCore.RT TEmpty) 0xe5aa0 24 0 0 | lia | rszc | ].
    cbn [rg_base RGz]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). rewrite Z.add_0_r.
    apply (bytes_at_ext ASEGS _ _ _ _ (cells_bytes_at _ _ K5)). apply bytes_eqb_eq. vm_compute. reflexivity.
  - (* [comment removed for export] *)
    apply track_of_bytes_at; [ img_rt (RGz (lconst 0x174858) 4 FxCore.RT TEmpty) 0x174858 4 0 0 | lia | rszc | ].
    cbn [rg_base RGz]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). rewrite Z.add_0_r.
    apply (bytes_at_ext ASEGS _ _ _ _ (cells_bytes_at _ _ K7)). apply bytes_eqb_eq. vm_compute. reflexivity.
  - (* [comment removed for export] *)
    destruct Hfb as (Hfb1 & _).
    apply track_of_bytes_at; [ img_rt (RGz (lconst 0x176971) 1 FxCore.RT TEmpty) 0x176971 1 0 0 | lia | rszc | ].
    cbn [rg_base RGz]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). rewrite Z.add_0_r.
    apply (bytes_at_ext ASEGS _ _ _ _ (cells_bytes_at _ _ Hfb1)). cbn [cells_bytes cbytes List.map bden app].
    change (lden E FB) with (lden E (lvar 21)). rewrite lden_lvar, HE21, Z.shiftr_0_r, u_Z_to_bv.
    pose proof (bv_unsigned_in_range _ fb) as Bf. unfold bv_modulus in Bf. change (2 ^ Z.of_N 8) with 256 in Bf.
    rewrite Z.mod_small by (unfold two64; lia). f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity.
  - (* [comment removed for export] *)
    apply track_of_bytes_at; [ img_rt (RGz (lconst 0x617f28) 8 FxCore.RT TEmpty) 0x617f28 8 0 0 | lia | rszc | ].
    cbn [rg_base RGz]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). rewrite Z.add_0_r.
    apply (bytes_at_ext ASEGS _ _ _ _ (cells_bytes_at _ _ K8)). apply bytes_eqb_eq. vm_compute. reflexivity.
  - (* [comment removed for export] *)
    apply track_of_bytes_at; [ apply track_of_bytes_at; [ apply track_of_bytes_at; [ apply track_of_bytes_at;
      [ img_rt (RGz (lconst 0x617f78) 56 FxCore.RT TEmpty) 0x617f78 56 0 0 | lia | rszc | ]
      | lia | rszc | ] | lia | rszc | ]
      | lia | rszc | ].
    + cbn [rg_base RGz track]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). rewrite Z.add_0_r.
      pose proof (cells_bytes_at _ _ K9) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. apply bytes_at_app in X as (X1 & _).
      apply (bytes_at_ext ASEGS _ _ _ _ X1). apply bytes_eqb_eq. vm_compute. reflexivity.
    + cbn [rg_base RGz track]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia).
      pose proof (cells_bytes_at _ _ K9) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. apply bytes_at_app in X as (_ & X2).
      rewrite length_le8 in X2. unfold bv8. rewrite map_bden_bv8, lden_FS. exact X2.
    + cbn [rg_base RGz track]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia).
      pose proof (cells_bytes_at _ _ K10) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X.
      unfold bv8. rewrite map_bden_bv8. change (lden E BLK) with (lden E (lvar 17)). rewrite lden_lvar, HE17. exact X.
    + cbn [rg_base RGz track]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia).
      apply (bytes_at_ext ASEGS _ _ _ _ (cells_bytes_at _ _ K11)). apply bytes_eqb_eq. vm_compute. reflexivity.
  - (* [comment removed for export] *)
    apply track_of_bytes_at; [ img_rt (RGz (lconst 0x639328) 8 FxCore.RT TEmpty) 0x639328 8 0 0 | lia | rszc | ].
    cbn [rg_base RGz]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). rewrite Z.add_0_r.
    pose proof (cells_bytes_at _ _ K12) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X.
    unfold bv8. rewrite map_bden_bv8. change (lden E CTX) with (lden E (lvar 15)). rewrite lden_lvar, HE15. exact X.
  - (* [comment removed for export] *)
    pose proof (cells_bytes_at _ _ K13) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X.
    apply track_of_bytes_at; [ | lia | rszc | ].
    + apply (rg_ok_rt_of_bytes_at ASEGS E m _ (rt_ctx v + 152) (le8 (Z_to_bv 64 (rt_thr v)))); [reflexivity | reflexivity | exact B25 | | exact X].
      rewrite rsz_RGz by (unfold two64; lia). rewrite length_le8. reflexivity.
    + cbn [rg_base RGz]. rewrite B25, Z.add_0_r.
      unfold bv8. rewrite map_bden_bv8. change (lden E THR) with (lden E (lvar 16)). rewrite lden_lvar, HE16. exact X.
  - (* [comment removed for export] *)
    pose proof (cells_bytes_at _ _ K14) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X.
    apply track_of_bytes_at; [ | lia | rszc | ].
    + apply (rg_ok_rt_of_bytes_at ASEGS E m _ (rt_thr v + 48) (le8 (Z_to_bv 64 (rt_tlsb v)) ++ le8 (Z_to_bv 64 (rt_tlse v)))); [reflexivity | reflexivity | exact B26 | | exact X].
      rewrite rsz_RGz by (unfold two64; lia). rewrite length_app, !length_le8. reflexivity.
    + cbn [rg_base RGz]. rewrite B26, Z.add_0_r. rewrite List.map_app.
      unfold bv8. rewrite !map_bden_bv8. change (lden E TLSB) with (lden E (lvar 19)). change (lden E TLSE) with (lden E (lvar 20)).
      rewrite !lden_lvar, HE19, HE20. exact X.
  - (* [comment removed for export] *)
    pose proof (cells_bytes_at _ _ K15) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X.
    apply track_of_bytes_at; [ | lia | rszc | ].
    + apply (rg_ok_rt_of_bytes_at ASEGS E m _ (rt_blk v + 24) (le8 (Z_to_bv 64 (rt_beg v)))); [reflexivity | reflexivity | exact B27 | | exact X].
      rewrite rsz_RGz by (unfold two64; lia). rewrite length_le8. reflexivity.
    + cbn [rg_base RGz]. rewrite B27, Z.add_0_r.
      unfold bv8. rewrite map_bden_bv8. change (lden E BEG) with (lden E (lvar 18)). rewrite lden_lvar, HE18. exact X.
  - (* [comment removed for export] *)
    apply rg_ok_ro_p; [exact PRG | lia | unfold two64; lia | lia | intros x Hx; apply rom_ok2; lia].
  - (* [comment removed for export] *)
    apply rg_ok_ro_p; [exact PRT | lia | unfold two64; lia | lia | intros x Hx; apply rom_ok3a; lia].
Qed.
(* [comment removed for export] *)
Ltac drop_unrel x := lazymatch goal with |- context [x] => idtac | _ => repeat match goal with H : context [x] |- _ => clear H end end.

(* [comment removed for export] *)
Ltac in_ivs := cbn [RT_IMG_IVS In]; repeat first [left; reflexivity | right].
Ltac img_disj HIt HIb :=
  let X := fresh "X" in
  match goal with
  | |- (?b + ?n <= _ \/ _ <= ?b) => first [ (pose proof (HIt b n ltac:(in_ivs)) as X; clear -X; lia) | (pose proof (HIb b n ltac:(in_ivs)) as X; clear -X; lia) ]
  | |- (_ <= ?b \/ ?b + ?n <= _) => first [ (pose proof (HIt b n ltac:(in_ivs)) as X; clear -X; lia) | (pose proof (HIb b n ltac:(in_ivs)) as X; clear -X; lia) ]
  end.
#[using="fc m ws L62 Hlen A8 SEP RTH KSP KSP2 KA0 KA1 SFS SEPF RD1 RD2 RD3 RTX0 Hfb"] Lemma lme_disj : rgs_disj E RGSe.
Proof. LiaFast.lf_pins (fun (fc m ws L62 Hlen A8 SEP RTH KSP KSP2 KA0 KA1 SFS SEPF RD1 RD2 RD3 RTX0 Hfb : LiaFast.U) => LiaFast.u0).
  pose proof lme_pl as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  pose proof lme_bases as (B0 & B1 & B2 & B3 & B4 & B5 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15).
  pose proof lme_bases2 as (B25 & B26 & B27).
  assert (S9 : bv_unsigned (lden E P5) = bv_unsigned h5 mod 512).
  { change (lden E P5) with (lden E (lvar 14)). rewrite lden_lvar, HE14, u_Z_to_bv, Z.mod_small by (unfold two64; lia). reflexivity. }
  assert (S11 : bv_unsigned (lden E (laddc (lscale (-1) P5) 511)) = 511 - bv_unsigned h5 mod 512).
  { bvc. rewrite Z.mod_small by (unfold two64; lia). lia. }
  apply (rgs_disj_of_ivs E RGSe
    [ (SPv - 2528, 2528); (A, 496); (A + 496, 2); (ASAN_B + A / 8, 63); (ASAN_B + A / 8 - 8, 8); (ASAN_B + A / 8 + 63, 8);
      (0x10000, 0x2e000); (SHB + 0x4a68, 32); (FS + 40, 8); (FS + 35840, bv_unsigned h5 mod 512); (FS + 35840 + bv_unsigned h5 mod 512, 1);
      (FS + 35841 + bv_unsigned h5 mod 512, 511 - bv_unsigned h5 mod 512); (FS + 5279744 + 2048 * (bv_unsigned h5 mod 512), 2048);
      (ASAN_B + FS / 8 + 659968 + 256 * (bv_unsigned h5 mod 512) - 8, 8); (ASAN_B + FS / 8 + 659968 + 256 * (bv_unsigned h5 mod 512), 256);
      (FS + 88, 9); (0xe4db8, 12); (0xe4620, 8); (0xe5a98, 2); (0xe5aa0, 24); (0x174858, 4); (0x176971, 1); (0x617f28, 8);
      (0x617f78, 56); (0x639328, 8); (rt_ctx v + 152, 8); (rt_thr v + 48, 16); (rt_blk v + 24, 8); (0xd9000, 0x5000); (0xde9d0, 0x188) ]).
  - unfold RGSe, rt_rgs_t, relro_rgs, fs_hdr_c, sb_uar_t. cbn [app].
    repeat apply Forall2_cons; try apply Forall2_nil; cbn [fst snd]; unfold rsz; cbn [rg_base rg_size track RGz].
    all: rewrite ?B0, ?B1, ?B2, ?B3, ?B4, ?B5, ?B8, ?B9, ?B10, ?B11, ?B12, ?B13, ?B14, ?B15, ?B25, ?B26, ?B27, ?S9, ?S11.
    all: rewrite ?lden_lconst, ?u_Z_to_bv.
    all: split; try reflexivity.
  - pose proof lme_rt as (Fa & Fk & _ & Ca & Ck & Ta & Tk & Ba & Bk & _ & Cl & Tl & Bl & _).
    destruct RTX0 as (_ & _ & D12 & D13 & D23 & HIt & HIb).
    unfold rt_disj in RD1, RD2, RD3. destruct RD1 as (R1c & R1t & R1b). destruct RD2 as (R2c & R2t & R2b). destruct RD3 as (R3c & R3t & R3b).
    assert (EA8 : A = 8 * (A / 8)) by (clear -Q8; pose proof (Z.div_mod A 8 ltac:(lia)); lia).
    assert (EF8 : FS = 8 * (FS / 8)) by (clear -Q5; pose proof (Z.div_mod FS 4096 ltac:(lia)); pose proof (Z.div_mod FS 8 ltac:(lia)); lia).
    clear ST PR LIMBS LENC TP PRG PRT RTH FK SHX SHT RBX RBF RAE Hfb SEP SEPF
          B0 B1 B2 B3 B4 B5 B8 B9 B10 B11 B12 B13 B14 B15 B25 B26 B27 S9 S11 Q5 Q8.
    remember (A / 8) as x8 eqn:Hx8. remember (FS / 8) as f8 eqn:Hf8. rewrite EA8 in *. rewrite EF8 in *. clear Hx8 Hf8 EA8 EF8.
    remember (bv_unsigned h5 mod 512) as p eqn:Hp. clear Hp.
    remember (rt_ctx v) as ctx eqn:Hctx. remember (rt_thr v) as thr eqn:Hthr. remember (rt_blk v) as blk eqn:Hblk. clear Hctx Hthr Hblk.
    remember SPv as sq eqn:Hsq. clear Hsq.
    unfold app2r, rt_app, KHI, KTOP, SHB in *.
    (* [comment removed for export] *)
    assert (X1 : 10629120 <= 8 * x8 /\ 8 * x8 + 504 <= 2 ^ 47) by (clear -Q3 Q6 KA1; lia).
    assert (X2 : 8 * x8 + 632 <= sq - 2528) by (clear -Q4 Q7; lia).
    assert (X3 : 6529024 <= 8 * f8 /\ 8 * f8 + 11571200 <= 2 ^ 47) by (clear -Q3 Q4 Q2; lia).
    cbn [pw_disj]. repeat split; repeat apply Forall_cons; try apply Forall_nil; unfold iv_disj; cbn [fst snd].
    all: drop_unrel sq; drop_unrel x8; drop_unrel f8; drop_unrel p; drop_unrel ctx; drop_unrel thr; drop_unrel blk.
    all: first [ lia | img_disj HIt HIb ].
Qed.

(* [comment removed for export] *)
Definition kms0 : machine_state :=
  MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 LMUL_ENTRY) fc None m (seg_rom ASEGS).

#[using="ws L62 Hlen A8 TP Ha1 Ha2 RTH KSP KSP2 SFS SEPF RTX0 Hfb"] Lemma lme_regs : regs_ok E LM_R0 (ms_regs kms0).
Proof. LiaFast.lf_pins (fun (ws L62 Hlen A8 TP Ha1 Ha2 RTH KSP KSP2 SFS SEPF RTX0 Hfb : LiaFast.U) => LiaFast.u0).
  pose proof vz_vals as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V30 & _).
  pose proof lme_pl as (_ & _ & _ & _ & _ & _ & _ & Q8 & _).
  assert (EA : 8 * (A / 8) = A) by (clear -Q8; pose proof (Z.div_mod A 8 ltac:(lia)); lia).
  apply regs_ok_of_cases. intros n Hn. cbn [ms_regs kms0 MS].
  do 32 (destruct n as [|n];
           [ getr_mkR_norm; rget_norm; lnorm; rewrite ?HE4, ?HE5, ?HE103, ?HE105, ?HE106, ?HE107, ?HE108, ?HE109, ?HE113, ?HE114, ?HE115, ?HE116, ?HE117, ?HE118, ?HE119, ?HE120, ?HE121, ?HE122, ?HE123, ?HE124, ?HE125, ?HE126, ?HE127, ?HE128, ?HE129, ?HE130, ?HE131;
             first [ reflexivity
                   | (rewrite TP; reflexivity) | (rewrite Ha1; reflexivity) | (rewrite Ha2; reflexivity)
                   | (change (vz E 30) with (bv_unsigned (E 30%positive)); unfold vz in V30; rewrite V30, Z.add_0_r, Z.add_0_l, EA;
                      symmetry; apply Z_to_bv_bv_unsigned) ]
           |]).
  lia.
Qed.

#[using="ws ST AL PR LIMBS L62 LENC Hlen A8 CAP SEP TP Ha1 Ha2 PRG PRT RTH FK KSP KSP2 KA0 KA1 SFS SEPF RD1 RD2 RD3 SHX SHT RBX RBF RTX0 RAE Hfb"] Lemma lme_sden0 : forall c, SPv mod 32 = c -> sden0 ASEGS E (LM_P0 c) kms0.
Proof. LiaFast.lf_pins (fun (ws ST AL PR LIMBS L62 LENC Hlen A8 CAP SEP TP Ha1 Ha2 PRG PRT RTH FK KSP KSP2 KA0 KA1 SFS SEPF RD1 RD2 RD3 SHX SHT RBX RBF RTX0 RAE Hfb : LiaFast.U) => LiaFast.u0).
  intros c Hcl. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); cbn [s_pc s_regs s_rgs s_facts s_resv LM_P0 kms0 MS ms_pc_val ms_svc_pending ms_resv ms_mem ms_fcsr].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact lme_regs.
  - rewrite RGSe_eq. exact lme_rgs.
  - rewrite RGSe_eq. exact lme_disj.
  - exact (lme_facts c Hcl).
  - destruct RTX0 as (_ & Hfrm & _). exact Hfrm.
Qed.

#[using="ws ST AL PR LIMBS L62 LENC Hlen A8 CAP SEP TP Ha1 Ha2 PRG PRT RTH FK KSP KSP2 KA0 KA1 SFS SEPF RD1 RD2 RD3 SHX SHT RBX RBF RTX0 RAE Hfb"] Lemma lme_sden : forall c, SPv mod 32 = c -> sden ASEGS E (LM_P0 c) kms0.
Proof. LiaFast.lf_pins (fun (ws ST AL PR LIMBS L62 LENC Hlen A8 CAP SEP TP Ha1 Ha2 PRG PRT RTH FK KSP KSP2 KA0 KA1 SFS SEPF RD1 RD2 RD3 SHX SHT RBX RBF RTX0 RAE Hfb : LiaFast.U) => LiaFast.u0).
  intros c Hcl. apply sden0_sden; [|exact (lme_sden0 c Hcl)].
  assert (Hcc : c = 0 \/ c = 16) by (rewrite <- Hcl; clear -AL; Z.div_mod_to_equations; lia).
  destruct Hcc as [->| ->]; [exact (proj1 LM_wf) | exact (proj2 LM_wf)].
Qed.

(* [comment removed for export] *)
#[using="h5 fb ST AL PR LIMBS L62 LENC Hlen A8 CAP SEP TP Ha1 Ha2 PRG PRT RTH FK KSP KSP2 KA0 KA1 SFS SEPF RD1 RD2 RD3 SHX SHT RBX RBF RTX0 RAE Hfb"] Lemma lme_run : evt ASEGS (long_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A ws len v m) kms0.
Proof. LiaFast.lf_pins (fun (h5 fb ST AL PR LIMBS L62 LENC Hlen A8 CAP SEP TP Ha1 Ha2 PRG PRT RTH FK KSP KSP2 KA0 KA1 SFS SEPF RD1 RD2 RD3 SHX SHT RBX RBF RTX0 RAE Hfb : LiaFast.U) => LiaFast.u0).
  assert (Hcc : SPv mod 32 = 0 \/ SPv mod 32 = 16) by (clear -AL; Z.div_mod_to_equations; lia).
  set (c := SPv mod 32) in *.
  pose proof (lme_sden c eq_refl) as HD0.
  destruct (lme_c1 c Hcc E kms0 HD0) as (ms1 & E1 & HI1 & HD1 & HA1 & HFr1 & HP1).
  pose proof (fx_rom ASEGS _ _ HI1) as Hrom1. cbn [kms0 MS ms_rom] in Hrom1.
  apply (evt_msteps ASEGS _ kms0 ms1 (isteps_msteps ASEGS _ _ HI1)).
  apply (lmn_run c E1 ms1 _ Hcc HD1 Hrom1). intros ws1 l' a0' a2' a3' m2 CUR L62' BN Hl' MU WM HD2.
  destruct (lme_c2 c Hcc _ _ HD2) as (ms3 & E3 & p & HI3 & Hin & Hret & HD3 & HA3 & HFr3 & HP3).
  apply (evt_msteps ASEGS _ _ ms3 (isteps_msteps ASEGS _ _ HI3)).
  destruct Hin as [<-|[]].
  pose proof (fx_rom ASEGS _ _ HI3) as Hrom3. cbn [ms2 MS ms_rom] in Hrom3.
  destruct (sden_0 _ _ _ _ HD3) as (Hpc3 & Hsvc3 & Hresv3 & HR3 & HG3 & HD3' & HF3 & Hfrm3).
  cbn [s_pc s_regs s_rgs s_facts s_resv with_pc LM_Q] in Hpc3, Hresv3, HR3, HG3, HD3', HF3. unfold rsv_ok in Hresv3.
  assert (Heqv3 : ms_eqv ms3 (kms ASEGS ms3)).
  { pose proof (kms_eqv ASEGS ms3 Hsvc3) as X. rewrite <- Hrom3, with_rom_eta in X. exact (ms_eqv_sym _ _ X). }
  apply (evt_eqv_l ASEGS _ ms3 _ Heqv3). unfold kms, mkR_of. rewrite Hpc3, Hresv3.
  step.
  (* [comment removed for export] *)
  assert (HAE : agree 200 E E3).
  { apply (agree_trans 200 E E1 E3); [exact HA1|]. apply (agree_trans 200 E1 (KxLMn.E2 E1 l' a0' a2' a3') E3); [exact (E2_agree E1 l' a0' a2' a3')|].
    apply (agree_mono 200 240); [lia | exact HA3]. }
  assert (KR : forall k, In k [1%nat; 2%nat; 3%nat; 4%nat; 8%nat; 9%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat] ->
                 getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat k)) = getr (ms_regs kms0) (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk. rewrite (HR3 _), lme_regs. cbn in Hk.
    repeat (destruct Hk as [<-|Hk]; [rget_norm; apply (lden_agree 200); [vm_compute; reflexivity | intros x Hx; symmetry; exact (HAE x Hx)]|]). destruct Hk. }
  (* [comment removed for export] *)
  pose proof lme_pl as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  pose proof lme_bases as (B0 & B1 & B2 & B3 & B4 & B5 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15).
  set (p5 := bv_unsigned h5 mod 512) in *.
  assert (S9 : bv_unsigned (lden E P5) = p5).
  { change (lden E P5) with (lden E (lvar 14)). rewrite lden_lvar, HE14, u_Z_to_bv, Z.mod_small by (unfold two64; lia). reflexivity. }
  assert (S11 : bv_unsigned (lden E (laddc (lscale (-1) P5) 511)) = 511 - p5).
  { bvc. rewrite Z.mod_small by (unfold two64; lia). lia. }
  assert (AE2 : agree 200 E (KxLMn.E2 E1 l' a0' a2' a3')).
  { apply (agree_trans 200 E E1); [exact HA1 | exact (E2_agree E1 l' a0' a2' a3')]. }
  set (W9 := [(SPv - 2528, SPv); (A, A + 496); (A + 496, A + 498); (FS + 40, FS + 48); (FS + 35840, FS + 35840 + p5);
              (FS + 35840 + p5, FS + 35841 + p5); (FS + 35841 + p5, FS + 35841 + p5 + (511 - p5));
              (FS + 5279744 + 2048 * p5, FS + 5279744 + 2048 * p5 + 2048);
              (ASAN_B + FS / 8 + 659968 + 256 * p5, ASAN_B + FS / 8 + 659968 + 256 * p5 + 256)]).
  (* [comment removed for export] *)
  assert (WR : forall (E' : valu) rgs j R (x : word), agree 200 E E' -> In j [0%nat; 1%nat; 2%nat; 8%nat; 9%nat; 10%nat; 11%nat; 12%nat; 14%nat] ->
            nth_error rgs j = Some R -> shape rgs = shape RGSe -> forallb (bs_wf 200) rgs = true ->
            in_rg E' R x -> ~ Frame.outside W9 (bv_unsigned x)).
  { intros E' rgs j R x HAg Hj HR Hsh Hbw Hin Hout.
    assert (HR0 : nth_error (shape RGSe) j = Some (rg_base R, rg_size R)).
    { rewrite <- Hsh. unfold shape. rewrite nth_error_map, HR. reflexivity. }
    assert (Hbw' : bs_wf 200 R = true) by (rewrite forallb_forall in Hbw; exact (Hbw R (nth_error_In _ _ HR))).
    unfold bs_wf in Hbw'. apply andb_prop in Hbw' as [Hb1 Hb2].
    assert (HinE : in_rg E R x).
    { unfold in_rg, rsz in Hin |- *. rewrite (lden_agree 200 E E' _ Hb1 HAg), (lden_agree 200 E E' _ Hb2 HAg). exact Hin. }
    clear Hin HR Hsh Hbw Hb1 Hb2. unfold in_rg, rsz in HinE. cbn [Frame.outside W9] in Hout.
    cbn in Hj. repeat (destruct Hj as [<-|Hj];
      [cbn [shape List.map nth_error RGSe rg_base rg_size RGz track app rt_rgs_t relro_rgs fs_hdr_c sb_uar_t] in HR0;
       injection HR0 as Hb Hs; rewrite <- Hb, <- Hs in HinE;
       rewrite ?B0, ?B1, ?B2, ?B8, ?B9, ?B10, ?B11, ?B12, ?B14, ?S9, ?S11 in HinE;
       rewrite ?lden_lconst, ?u_Z_to_bv, ?Z.mod_small in HinE by (unfold two64; lia); lia|]).
    destruct Hj. }
  (* [comment removed for export] *)
  assert (ROm : forall y : word, (65536 <= bv_unsigned y < 253952 \/ 888832 <= bv_unsigned y < 909312 \/ 911824 <= bv_unsigned y < 912216) -> m y = None).
  { intros y Hy. destruct PR as (_ & _ & P1'). destruct PRG as (_ & _ & P2'). destruct PRT as (_ & _ & P3').
    rewrite <- (Z_to_bv_bv_unsigned y). change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)).
    destruct Hy as [Hy|[Hy|Hy]]; [exact (P1' _ Hy) | exact (P2' _ Hy) | exact (P3' _ Hy)]. }
  assert (ROt : forall (E' : valu) (lk : rkind) (up : bool) mm (y : word), Forall (rg_ok ASEGS E' mm) (LM_RGS_T c lk up) ->
            (65536 <= bv_unsigned y < 253952 \/ 888832 <= bv_unsigned y < 909312 \/ 911824 <= bv_unsigned y < 912216) -> mm y = None).
  { intros E' lk up mm y HGq Hy. unfold LM_RGS_T in HGq. rewrite Forall_app in HGq. destruct HGq as (HGq1 & HGq2).
    rewrite Forall_app in HGq2. destruct HGq2 as (_ & HGq2). rewrite Forall_app in HGq2. destruct HGq2 as (_ & HGq2).
    unfold relro_rgs in HGq2.
    destruct Hy as [Hy|[Hy|Hy]].
    - apply (ro_none ASEGS E' mm _ (RGz (lconst 0x10000) 0x2e000 RO TEmpty) y HGq1); [cbn; tauto | reflexivity |].
      unfold in_rg, rsz. cbn [RGz rg_base rg_size]. rewrite !lden_lconst, !u_Z_to_bv, !Z.mod_small by (unfold two64; lia). lia.
    - apply (ro_none ASEGS E' mm _ (RGz (lconst 0xd9000) 0x5000 RO TEmpty) y HGq2); [cbn; tauto | reflexivity |].
      unfold in_rg, rsz. cbn [RGz rg_base rg_size]. rewrite !lden_lconst, !u_Z_to_bv, !Z.mod_small by (unfold two64; lia). lia.
    - apply (ro_none ASEGS E' mm _ (RGz (lconst 0xde9d0) 0x188 RO TEmpty) y HGq2); [cbn; tauto | reflexivity |].
      unfold in_rg, rsz. cbn [RGz rg_base rg_size]. rewrite !lden_lconst, !u_Z_to_bv, !Z.mod_small by (unfold two64; lia). lia. }
  (* [comment removed for export] *)
  assert (RO3 : forall (E' : valu) (lk : rkind) (up : bool) R (y : word), lk <> RO -> In R (LM_RGS_T c lk up) -> rg_kind R = RO -> in_rg E' R y ->
            (65536 <= bv_unsigned y < 253952 \/ 888832 <= bv_unsigned y < 909312 \/ 911824 <= bv_unsigned y < 912216)).
  { intros E' lk up R y Hlk HRin Hk Hy. unfold LM_RGS_T in HRin. rewrite !in_app_iff in HRin.
    destruct HRin as [HRin|[HRin|[HRin|HRin]]].
    - destruct up; cbn [In] in HRin.
      all: repeat (destruct HRin as [<-|HRin]; [first [ (cbn in Hk; discriminate) | (cbn in Hk; exfalso; exact (Hlk Hk))
                             | (unfold in_rg, rsz in Hy; cbn [RGz rg_base rg_size] in Hy; rewrite !lden_lconst, !u_Z_to_bv, !Z.mod_small in Hy by (unfold two64; lia); lia) ]|]).
      all: destruct HRin.
    - cbn [In fks5_lm] in HRin. repeat (destruct HRin as [<-|HRin]; [cbn in Hk; discriminate|]). destruct HRin.
    - cbn [In rt_rgs_c fs_hdr_c sb_uar_c app List.map firstn skipn rt_rgs] in HRin. repeat (destruct HRin as [<-|HRin]; [cbn in Hk; discriminate|]). destruct HRin.
    - unfold relro_rgs in HRin. cbn [In] in HRin. repeat (destruct HRin as [<-|HRin]; [
                             unfold in_rg, rsz in Hy; cbn [RGz rg_base rg_size] in Hy; rewrite !lden_lconst, !u_Z_to_bv, !Z.mod_small in Hy by (unfold two64; lia); lia|]).
      destruct HRin. }
  destruct (sden_0 _ _ _ _ HD1) as (_ & _ & _ & _ & HG1 & _). cbn [s_rgs with_pc LM_TAIL_Q] in HG1.
  destruct (sden_0 _ _ _ _ HD2) as (_ & _ & _ & _ & HG2 & _). cbn [s_rgs LM_EPI_P0] in HG2.
  assert (MEM : forall x : word, Frame.outside W9 (bv_unsigned x) -> ms_mem ms3 x = m x).
  { intros x Hx.
    assert (M32 : ms_mem ms3 x = m2 x).
    { apply (frame_idx (KxLMn.E2 E1 l' a0' a2' a3') (LM_RGS_T c FxCore.RT false) [0%nat; 2%nat; 8%nat; 9%nat; 10%nat; 11%nat; 12%nat; 14%nat] m2 (ms_mem ms3) x).
      - destruct Hcc as [Hc|Hc]; rewrite Hc; vm_compute; reflexivity.
      - intros j R Hj HR Hin. apply (WR _ (LM_RGS_T c FxCore.RT false) j R x AE2 ltac:(cbn in Hj |- *; tauto) HR
                                       ltac:(destruct Hcc as [Hc|Hc]; rewrite Hc; vm_compute; reflexivity)
                                       ltac:(destruct Hcc as [Hc|Hc]; rewrite Hc; vm_compute; reflexivity) Hin Hx).
      - intros Hfr. exact (HFr3 x Hfr).
      - intros R HRin Hk Hin. pose proof (RO3 _ FxCore.RT false R x ltac:(discriminate) HRin Hk Hin) as Hr.
        split; [exact (ROt _ _ _ _ x HG2 Hr) | exact (ROt _ _ _ _ x HG3 Hr)]. }
    assert (M21 : m2 x = ms_mem ms1 x).
    { apply MU. rewrite (lden_agree 200 E1 E XA ltac:(vm_compute; reflexivity) ltac:(intros y Hy; symmetry; exact (HA1 y Hy))), B1.
      cbn [Frame.outside W9] in Hx |- *. lia. }
    assert (M10 : ms_mem ms1 x = m x).
    { apply (frame_idx E LM_RGS [0%nat; 1%nat; 2%nat; 8%nat; 9%nat; 10%nat; 11%nat; 12%nat; 14%nat] m (ms_mem ms1) x).
      - vm_compute; reflexivity.
      - intros j R Hj HR Hin. apply (WR E LM_RGS j R x (agree_refl 200 E) Hj HR ltac:(rewrite RGSe_eq; reflexivity)
                                       ltac:(vm_compute; reflexivity) Hin Hx).
      - intros Hfr. exact (HFr1 x Hfr).
      - intros R HRin Hk Hin. rewrite RGSe_eq in HRin.
        assert (Hr : 65536 <= bv_unsigned x < 253952 \/ 888832 <= bv_unsigned x < 909312 \/ 911824 <= bv_unsigned x < 912216).
        { unfold RGSe, rt_rgs_t, relro_rgs in HRin. cbn [In app] in HRin.
          repeat (destruct HRin as [<-|HRin]; [cbn in Hk; try discriminate;
                   unfold in_rg, rsz in Hin; cbn [RGz rg_base rg_size] in Hin; rewrite !lden_lconst, !u_Z_to_bv, !Z.mod_small in Hin by (unfold two64; lia); lia|]).
          destruct HRin. }
        split; [exact (ROm x Hr) | exact (ROt _ _ _ _ x HG1 Hr)]. }
    rewrite M32, M21, M10. reflexivity. }
  (* [comment removed for export] *)
  assert (FP3 : forall r, reg_get (ms_fregs ms3) r = reg_get F r).
  { intros r. destruct HP3 as (HP3r & _). destruct HP1 as (HP1r & _). rewrite HP3r. cbn [KxLMn.ms2 MS ms_fregs]. rewrite HP1r. reflexivity. }
  assert (FC3 : ms_fcsr ms3 = fc).
  { destruct HP3 as (_ & HP3c). destruct HP1 as (_ & HP1c). rewrite HP3c. cbn [KxLMn.ms2 MS ms_fcsr]. rewrite HP1c. reflexivity. }
  (* [comment removed for export] *)
  assert (NIMG : forall (mm : word -> option byte) (y : word), 6529024 <= bv_unsigned y -> wview ASEGS mm y <> None -> mm y <> None).
  { intros mm y Hy Hw. unfold RiscvSemantics.wview in Hw. destruct (mm y) as [b|]; [discriminate|].
    rewrite (find_segment_above ASEGS 6529024 (bv_unsigned y) 1 ltac:(vm_compute; reflexivity) Hy ltac:(lia)) in Hw. exact Hw. }
  (* [comment removed for export] *)
  assert (RDreg : forall j R (x : word), nth_error (LM_RGS_T c FxCore.RT true) j = Some R -> rg_kind R <> RO ->
            bv_unsigned (lden E (rg_base R)) <= bv_unsigned x < bv_unsigned (lden E (rg_base R)) + rsz E R -> 6529024 <= bv_unsigned x ->
            bs_wf 200 R = true -> ms_mem ms3 x <> None).
  { intros j R x Hj Hk Hx Himg Hbw. rewrite Forall_forall in HG3. pose proof (HG3 R (nth_error_In _ _ Hj)) as GR.
    unfold bs_wf in Hbw. apply andb_prop in Hbw as [Hb1 Hb2]. unfold rsz in Hx.
    rewrite (lden_agree 200 E E3 _ Hb1 HAE), (lden_agree 200 E E3 _ Hb2 HAE) in Hx.
    pose proof (rd_of_rg ASEGS E3 _ R (bv_unsigned x - bv_unsigned (lden E3 (rg_base R))) GR ltac:(unfold rsz; lia) Hk) as X.
    replace (bv_unsigned (lden E3 (rg_base R)) + (bv_unsigned x - bv_unsigned (lden E3 (rg_base R)))) with (bv_unsigned x) in X by ring.
    unfold wa in X. rewrite Z_to_bv_bv_unsigned in X. unfold mrd in X. intros Hm. rewrite Hm in X.
    exact (X (seg_rom_above ASEGS 6529024 x ltac:(vm_compute; reflexivity) Himg)). }
  assert (F8 : 0 <= FS / 8) by (apply Z.div_pos; lia).
  assert (W9RD : forall x : word, ~ Frame.outside W9 (bv_unsigned x) -> ms_mem ms3 x <> None).
  { intros x Hx. destruct (in_some_iv W9 (bv_unsigned x) Hx) as (lo & hi & Hin & Hr). unfold W9 in Hin. cbn [In] in Hin.
    destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]]]]]]; injection Hin as <- <-.
    - eapply (RDreg 0%nat); [reflexivity | cbn; discriminate | (unfold rsz; cbn [rg_base rg_size track RGz slot5_shadow]; rewrite ?B0, ?B1, ?B2, ?B8, ?B9, ?B10, ?B11, ?B12, ?B14, ?S9, ?S11; rewrite ?lden_lconst, ?u_Z_to_bv, ?Z.mod_small by (unfold two64; lia); lia) | unfold KHI in *; lia | vm_compute; reflexivity].
    - eapply (RDreg 1%nat); [reflexivity | cbn; discriminate | (unfold rsz; cbn [rg_base rg_size track RGz slot5_shadow]; rewrite ?B0, ?B1, ?B2, ?B8, ?B9, ?B10, ?B11, ?B12, ?B14, ?S9, ?S11; rewrite ?lden_lconst, ?u_Z_to_bv, ?Z.mod_small by (unfold two64; lia); lia) | unfold KHI in *; lia | vm_compute; reflexivity].
    - eapply (RDreg 2%nat); [reflexivity | cbn; discriminate | (unfold rsz; cbn [rg_base rg_size track RGz slot5_shadow]; rewrite ?B0, ?B1, ?B2, ?B8, ?B9, ?B10, ?B11, ?B12, ?B14, ?S9, ?S11; rewrite ?lden_lconst, ?u_Z_to_bv, ?Z.mod_small by (unfold two64; lia); lia) | unfold KHI in *; lia | vm_compute; reflexivity].
    - eapply (RDreg 8%nat); [reflexivity | cbn; discriminate | (unfold rsz; cbn [rg_base rg_size track RGz slot5_shadow]; rewrite ?B0, ?B1, ?B2, ?B8, ?B9, ?B10, ?B11, ?B12, ?B14, ?S9, ?S11; rewrite ?lden_lconst, ?u_Z_to_bv, ?Z.mod_small by (unfold two64; lia); lia) | unfold KHI in *; lia | vm_compute; reflexivity].
    - eapply (RDreg 9%nat); [reflexivity | cbn; discriminate | (unfold rsz; cbn [rg_base rg_size track RGz slot5_shadow]; rewrite ?B0, ?B1, ?B2, ?B8, ?B9, ?B10, ?B11, ?B12, ?B14, ?S9, ?S11; rewrite ?lden_lconst, ?u_Z_to_bv, ?Z.mod_small by (unfold two64; lia); lia) | unfold KHI in *; lia | vm_compute; reflexivity].
    - eapply (RDreg 10%nat); [reflexivity | cbn; discriminate | (unfold rsz; cbn [rg_base rg_size track RGz slot5_shadow]; rewrite ?B0, ?B1, ?B2, ?B8, ?B9, ?B10, ?B11, ?B12, ?B14, ?S9, ?S11; rewrite ?lden_lconst, ?u_Z_to_bv, ?Z.mod_small by (unfold two64; lia); lia) | unfold KHI in *; lia | vm_compute; reflexivity].
    - eapply (RDreg 11%nat); [reflexivity | cbn; discriminate | (unfold rsz; cbn [rg_base rg_size track RGz slot5_shadow]; rewrite ?B0, ?B1, ?B2, ?B8, ?B9, ?B10, ?B11, ?B12, ?B14, ?S9, ?S11; rewrite ?lden_lconst, ?u_Z_to_bv, ?Z.mod_small by (unfold two64; lia); lia) | unfold KHI in *; lia | vm_compute; reflexivity].
    - eapply (RDreg 12%nat); [reflexivity | cbn; discriminate | (unfold rsz; cbn [rg_base rg_size track RGz slot5_shadow]; rewrite ?B0, ?B1, ?B2, ?B8, ?B9, ?B10, ?B11, ?B12, ?B14, ?S9, ?S11; rewrite ?lden_lconst, ?u_Z_to_bv, ?Z.mod_small by (unfold two64; lia); lia) | unfold KHI in *; lia | vm_compute; reflexivity].
    - eapply (RDreg 14%nat); [reflexivity | cbn; discriminate | (unfold rsz; cbn [rg_base rg_size track RGz slot5_shadow]; rewrite ?B0, ?B1, ?B2, ?B8, ?B9, ?B10, ?B11, ?B12, ?B14, ?S9, ?S11; rewrite ?lden_lconst, ?u_Z_to_bv, ?Z.mod_small by (unfold two64; lia); lia) | unfold KHI in *; lia | vm_compute; reflexivity].
  }
  (* [comment removed for export] *)
  assert (KRv : getr (ms_regs ms3) 1 = ra /\ getr (ms_regs ms3) 2 = sp /\ getr (ms_regs ms3) 3 = gp /\ getr (ms_regs ms3) 4 = tp /\
                getr (ms_regs ms3) 8 = s0 /\ getr (ms_regs ms3) 9 = s1 /\ getr (ms_regs ms3) 18 = s2 /\ getr (ms_regs ms3) 19 = s3 /\
                getr (ms_regs ms3) 20 = s4 /\ getr (ms_regs ms3) 21 = s5 /\ getr (ms_regs ms3) 22 = s6 /\ getr (ms_regs ms3) 23 = s7 /\
                getr (ms_regs ms3) 24 = s8 /\ getr (ms_regs ms3) 25 = s9 /\ getr (ms_regs ms3) 26 = s10 /\ getr (ms_regs ms3) 27 = s11 /\
                getr (ms_regs ms3) 10 = Z_to_bv 64 1).
  { repeat split; rewrite (HR3 _); rget_norm; lnorm.
    all: first [ reflexivity | (rewrite TP; reflexivity) | (match goal with |- _ ?x = _ => rewrite <- (HAE x ltac:(lia)); reflexivity end) ]. }
  destruct KRv as (K1 & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K10).
  set (R3 := ms_regs ms3) in *.
  apply (evt_eqv_l ASEGS _ _
           (MS (mkR ra sp gp tp (getr R3 5) (getr R3 6) (getr R3 7) s0 s1 (Z_to_bv 64 1) (getr R3 11) (getr R3 12) (getr R3 13) (getr R3 14)
                    (getr R3 15) (getr R3 16) (getr R3 17) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (getr R3 28) (getr R3 29) (getr R3 30) (getr R3 31))
               F (ret_pc ra) fc None (ms_mem ms3) (seg_rom ASEGS))).
  { refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
    - intros r. destruct (reg_of_nat r) as (n & -> & Hn).
      do 32 (destruct n as [|n]; [rewrite !getr_mkR; cbn beta iota; first [reflexivity | assumption | (symmetry; assumption)] |]). lia.
    - intros r. exact (FP3 r).
    - rewrite K1. reflexivity.
    - reflexivity.
    - reflexivity.
    - exact FC3.
    - reflexivity.
    - reflexivity. }
  (* [comment removed for export] *)
  assert (GQ : forall j R, nth_error (LM_RGS_T c FxCore.RT true) j = Some R -> rg_ok ASEGS E3 (ms_mem ms3) R).
  { intros j R Hj. rewrite Forall_forall in HG3. exact (HG3 R (nth_error_In _ _ Hj)). }
  assert (BQ : forall l, lwf 200 l = true -> lden E3 l = lden E l) by (intros l Hl; symmetry; exact (lden_agree 200 E E3 l Hl HAE)).
  assert (MUNCH : munch (long_mul_W SPv A FS) m (ms_mem ms3)).
  { intros x Hx. apply MEM. unfold long_mul_W in Hx. unfold W9. cbn [Frame.outside] in Hx |- *. clear -Hx Q9. lia. }
  assert (WMONO : wmono ASEGS m (ms_mem ms3)).
  { intros x Hx. destruct (outside_dec W9 (bv_unsigned x)) as [Ho|Hi]; [rewrite (MEM x Ho); exact Hx | exact (W9RD x Hi)]. }
  assert (STK3 : stk ASEGS (ms_mem ms3) (SPv - 2528) SPv).
  { apply (stk_of_rg ASEGS E3 _ (RG (laddc SP (-2528)) (lconst 2528) RW TEmpty)); [apply (GQ 0%nat); reflexivity | left; reflexivity | | ].
    - cbn [rg_base]. rewrite (BQ (laddc SP (-2528)) ltac:(vm_compute; reflexivity)). exact B0.
    - unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). lia. }
  assert (XA1 : bv_unsigned (lden E1 XA) = A).
  { rewrite (lden_agree 200 E1 E XA ltac:(vm_compute; reflexivity) ltac:(intros y Hy; symmetry; exact (HA1 y Hy))). exact B1. }
  assert (LIMBS3 : u64arr ASEGS (ms_mem ms3) A ws1).
  { rewrite XA1 in CUR. apply (u64arr_ext_mem (ms_mem ms1) (ms_mem ms3) A ws1 CUR). rewrite L62'. intros i Hi.
    assert (Hw : bv_unsigned (wa (A + i)) = A + i) by (unfold wa; rewrite u_Z_to_bv, Z.mod_small by (clear -Hi KA1 Q6 Q3; cbn in Hi; unfold KTOP, two64 in *; lia); reflexivity).
    rewrite (HFr3 (wa (A + i))).
    - apply MU. rewrite XA1, Hw. cbn [Frame.outside]. cbn in Hi. clear -Hi. lia.
    - right. apply Exists_exists. exists (RG XA (lconst 496) FxCore.RT TEmpty). split; [|split; [reflexivity|]].
      + cbn [LM_EPI_P0 s_rgs]. unfold LM_RGS_T. apply in_or_app. left. right. left. reflexivity.
      + unfold FxStep.in_rg, rsz. cbn [rg_base rg_size]. rewrite (lden_agree 200 (KxLMn.E2 E1 l' a0' a2' a3') E XA ltac:(vm_compute; reflexivity)
                                                       ltac:(intros y Hy; symmetry; exact (AE2 y Hy))), B1, Hw.
        rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia). cbn in Hi. clear -Hi. lia. }
  assert (E3_235 : E3 235%positive = Z_to_bv 64 l').
  { rewrite <- (HA3 235%positive ltac:(cbn [s_next LM_EPI_P0]; lia)). reflexivity. }
  assert (LENC3 : rw_cells ASEGS (ms_mem ms3) (A + 496) [C2 (Z_to_bv 64 l')]).
  { pose proof (GQ 2%nat _ eq_refl) as G2q. cbn [LM_RGS_T] in G2q.
    assert (B2q : bv_unsigned (lden E3 (laddc XA 496)) = A + 496) by (rewrite (BQ (laddc XA 496) ltac:(vm_compute; reflexivity)); exact B2).
    split; [split; [cbn; tauto|] |].
    - pose proof (track_bytes_at ASEGS E3 (ms_mem ms3) _ 0 _ G2q ltac:(lia) ltac:(cbn; lia)) as X. cbn [rg_base] in X. rewrite B2q, Z.add_0_r in X.
      apply (bytes_at_ext ASEGS _ _ _ _ X). cbn [cells_bytes cbytes List.map bden]. rewrite app_nil_r. unfold le2. cbn [Z_to_le_bytes].
      change (lden E3 L0V) with (lden E3 (lvar 235)). rewrite lden_lvar, E3_235, Z.shiftr_0_r. reflexivity.
    - cbn [cells_size csize]. change (Z.of_nat (2 + 0)) with 2.
      pose proof (wr_at_of_rg ASEGS E3 _ _ _ _ (rg_ok_untrack ASEGS E3 _ _ _ _ _ _ G2q) ltac:(left; reflexivity) ltac:(cbn [rg_base]; exact B2q) eq_refl) as W.
      unfold rsz in W. cbn [rg_size] in W. rewrite lden_lconst, u_Z_to_bv, Z.mod_small in W by (unfold two64; lia). exact W. }
  assert (PR3 : pristine (ms_mem ms3) IMG_LO ROD_HI).
  { split; [lia|]. split; [lia|]. intros i Hi. apply (ROt E3 FxCore.RT true (ms_mem ms3) (wa i) HG3).
    unfold wa. rewrite u_Z_to_bv, Z.mod_small by (unfold two64; lia). lia. }
  assert (RT3 : RT (ms_mem ms3) v).
  { assert (F8h : 8 * (FS / 8) <= FS) by (apply Z.mul_div_le; lia).
    pose proof lme_rt as (_ & Fk & _). unfold KTOP in Fk.
    apply (RT_transport m (ms_mem ms3) v _ RTH MUNCH). unfold long_mul_W. solve_W_rt. }
  destruct (word_of_stk ASEGS (ms_mem ms3) (FS + 40)) as (h5' & HINT).
  { apply (stk_of_rg ASEGS E3 _ (RGz (fsc 40) 8 RW TEmpty)); [apply (GQ 8%nat); reflexivity | left; reflexivity | | ].
    - cbn [rg_base RGz]. rewrite (BQ (fsc 40) ltac:(vm_compute; reflexivity)). exact B8.
    - rewrite rsz_RGz by (unfold two64; lia). lia. }
  (* [comment removed for export] *)
  assert (HwF : forall z, 0 <= z < two64 -> bv_unsigned (wa z) = z) by (intros z Hz; unfold wa; rewrite u_Z_to_bv, Z.mod_small by exact Hz; reflexivity).
  pose proof lme_rt as (Fa & Fk & _). unfold app2r, KTOP in Fa, Fk.
  destruct FK as (FK0 & FK1 & FK2 & FK3' & FK4).
  assert (F8h : 8 * (FS / 8) <= FS) by (apply Z.mul_div_le; lia).
  assert (FSC3 : fs_cells_ok FS (ms_mem ms3)).
  { apply (ro_cells_ext_mem m (ms_mem ms3) (FS + 88) _ FK0). intros i Hi.
    change (Z.of_nat (length (cells_bytes [C8 (Z_to_bv 64 20); C1 (Z_to_bv 8 0)]))) with 9 in Hi. apply MEM.
    rewrite HwF by (clear -Hi Fa Fk; unfold two64; lia). unfold W9. cbn [Frame.outside]. clear -Hi Q9 Fa Fk Q1 Q3 Q4 Q6 Q7 F8 F8h. unfold KHI in *. lia. }
  assert (FL3 : u8arr ASEGS (ms_mem ms3) (FS + 35840) (zeros 512)).
  { pose proof (GQ 9%nat _ eq_refl) as G9q. pose proof (GQ 10%nat _ eq_refl) as G10q. pose proof (GQ 11%nat _ eq_refl) as G11q.
    assert (B9q : bv_unsigned (lden E3 (fsc FL5)) = FS + 35840) by (rewrite (BQ (fsc FL5) ltac:(vm_compute; reflexivity)); exact B9).
    assert (B10q : bv_unsigned (lden E3 FLB5) = FS + 35840 + p5) by (rewrite (BQ FLB5 ltac:(vm_compute; reflexivity)); exact B10).
    assert (B11q : bv_unsigned (lden E3 (ladd (fsc (FL5 + 1)) P5)) = FS + 35841 + p5) by (rewrite (BQ (ladd (fsc (FL5 + 1)) P5) ltac:(vm_compute; reflexivity)); exact B11).
    assert (S9q : rsz E3 (RG (fsc FL5) P5 RZ TEmpty) = p5) by (unfold rsz; cbn [rg_size]; rewrite (BQ P5 ltac:(vm_compute; reflexivity)); exact S9).
    assert (S11q : rsz E3 (RG (ladd (fsc (FL5 + 1)) P5) (laddc (lscale (-1) P5) 511) RZ TEmpty) = 511 - p5)
      by (unfold rsz; cbn [rg_size]; rewrite (BQ (laddc (lscale (-1) P5) 511) ltac:(vm_compute; reflexivity)); exact S11).
    assert (HB : forall i, 0 <= i < 512 -> mrd ASEGS (ms_mem ms3) (wa (FS + 35840 + i)) = Some (Z_to_bv 8 0) /\
                                           wview ASEGS (ms_mem ms3) (wa (FS + 35840 + i)) <> None).
    { intros i Hi. destruct (Z.ltb_spec i p5) as [H1|H1]; [|destruct (Z.eqb_spec i p5) as [H2|H2]].
      - pose proof (rz_bytes ASEGS E3 _ _ i G9q eq_refl eq_refl ltac:(rewrite S9q; lia)) as X. cbn [rg_base] in X. rewrite B9q in X. exact X.
      - subst i. pose proof (rz_bytes ASEGS E3 _ _ 0 G10q eq_refl eq_refl ltac:(unfold rsz; cbn [rg_size]; rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia); lia)) as X.
        cbn [rg_base] in X. rewrite B10q, Z.add_0_r in X. exact X.
      - pose proof (rz_bytes ASEGS E3 _ _ (i - p5 - 1) G11q eq_refl eq_refl ltac:(rewrite S11q; lia)) as X. cbn [rg_base] in X. rewrite B11q in X.
        replace (FS + 35841 + p5 + (i - p5 - 1)) with (FS + 35840 + i) in X by ring. exact X. }
    split.
    - split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
      intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi. exact (proj1 (HB (Z.of_nat i) ltac:(lia))).
    - split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
      intros i Hi. unfold zeros in Hi. rewrite repeat_length in Hi. exact (proj2 (HB i ltac:(lia))). }
  assert (STKS : stk ASEGS (ms_mem ms3) (FS + FK5_LO) (FS + FK5_HI)).
  { pose proof (GQ 12%nat _ eq_refl) as G12q.
    assert (B12q : bv_unsigned (lden E3 SLOT5) = FS + 5279744 + 2048 * p5) by (rewrite (BQ SLOT5 ltac:(vm_compute; reflexivity)); exact B12).
    destruct FK3' as (S1 & S2 & S). split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Z_le_gt_dec (FS + 5279744 + 2048 * p5) a) as [L1|L1]; [destruct (Z_lt_ge_dec a (FS + 5279744 + 2048 * p5 + 2048)) as [L2|L2]|].
    - pose proof (rdwr_of_rg ASEGS E3 _ _ (a - (FS + 5279744 + 2048 * p5)) G12q ltac:(left; reflexivity)
                    ltac:(unfold rsz; cbn [rg_size]; rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia); lia)) as (X1 & X2).
      cbn [rg_base] in X1, X2. rewrite B12q in X1, X2. replace (FS + 5279744 + 2048 * p5 + (a - (FS + 5279744 + 2048 * p5))) with a in X1, X2 by ring.
      split; [exact X2|]. destruct (mrd ASEGS (ms_mem ms3) (wa a)) as [b|]; [exists b; reflexivity | exfalso; exact (X1 eq_refl)].
    - assert (Hm : ms_mem ms3 (wa a) = m (wa a)) by (apply MEM; rewrite HwF by (clear -Ha Fa Fk; unfold two64 in *; lia); unfold W9; cbn [Frame.outside]; clear -Ha L1 L2 Q9 Fa Fk Q1 Q3 Q4 Q6 Q7 F8 F8h; unfold KHI in *; lia).
      rewrite (wview_ext m (ms_mem ms3) _ Hm), (mrd_ext m (ms_mem ms3) _ Hm). exact (S a Ha).
    - assert (Hm : ms_mem ms3 (wa a) = m (wa a)) by (apply MEM; rewrite HwF by (clear -Ha Fa Fk; unfold two64 in *; lia); unfold W9; cbn [Frame.outside]; clear -Ha L1 Q9 Fa Fk Q1 Q3 Q4 Q6 Q7 F8 F8h; unfold KHI in *; lia).
      rewrite (wview_ext m (ms_mem ms3) _ Hm), (mrd_ext m (ms_mem ms3) _ Hm). exact (S a Ha). }
  assert (STKH : stk ASEGS (ms_mem ms3) (ASAN_B + FS / 8 + FK5_SLO) (ASAN_B + FS / 8 + FK5_SHI)).
  { pose proof (GQ 14%nat _ eq_refl) as G14q.
    assert (B14q : bv_unsigned (lden E3 SHSLOT5) = ASAN_B + FS / 8 + 659968 + 256 * p5) by (rewrite (BQ SHSLOT5 ltac:(vm_compute; reflexivity)); exact B14).
    destruct FK4 as (S1 & S2 & S). split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Z_le_gt_dec (ASAN_B + FS / 8 + 659968 + 256 * p5) a) as [L1|L1]; [destruct (Z_lt_ge_dec a (ASAN_B + FS / 8 + 659968 + 256 * p5 + 256)) as [L2|L2]|].
    - pose proof (rdwr_of_rg ASEGS E3 _ _ (a - (ASAN_B + FS / 8 + 659968 + 256 * p5)) G14q ltac:(left; reflexivity)
                    ltac:(unfold rsz; cbn [rg_size slot5_shadow]; rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia); lia)) as (X1 & X2).
      cbn [rg_base slot5_shadow] in X1, X2. rewrite B14q in X1, X2.
      replace (ASAN_B + FS / 8 + 659968 + 256 * p5 + (a - (ASAN_B + FS / 8 + 659968 + 256 * p5))) with a in X1, X2 by ring.
      split; [exact X2|]. destruct (mrd ASEGS (ms_mem ms3) (wa a)) as [b|]; [exists b; reflexivity | exfalso; exact (X1 eq_refl)].
    - assert (Hm : ms_mem ms3 (wa a) = m (wa a)) by (apply MEM; rewrite HwF by (clear -Ha Fa Fk F8 F8h; unfold two64 in *; lia); unfold W9; cbn [Frame.outside]; clear -Ha L1 L2 Q9 Fa Fk Q1 Q3 Q4 Q6 Q7 F8 F8h; unfold KHI in *; lia).
      rewrite (wview_ext m (ms_mem ms3) _ Hm), (mrd_ext m (ms_mem ms3) _ Hm). exact (S a Ha).
    - assert (Hm : ms_mem ms3 (wa a) = m (wa a)) by (apply MEM; rewrite HwF by (clear -Ha Fa Fk F8 F8h; unfold two64 in *; lia); unfold W9; cbn [Frame.outside]; clear -Ha L1 Q9 Fa Fk Q1 Q3 Q4 Q6 Q7 F8 F8h; unfold KHI in *; lia).
      rewrite (wview_ext m (ms_mem ms3) _ Hm), (mrd_ext m (ms_mem ms3) _ Hm). exact (S a Ha). }
  (* [comment removed for export] *)
  pose proof (lmn_facts c E1 ms1 Hcc HD1) as (F40 & F41 & _).
  assert (E131 : bv_unsigned (E1 31%positive) = len).
  { rewrite <- (HA1 31%positive ltac:(cbn [s_next LM_P0]; lia)), HE31, u_Z_to_bv. apply Z.mod_small. unfold two64; lia. }
  apply evt_done. unfold long_mul_post.
  exists (getr R3 5), (getr R3 6), (getr R3 7), (getr R3 11), (getr R3 12), (getr R3 13), (getr R3 14), (getr R3 15), (getr R3 16), (getr R3 17),
         (getr R3 28), (getr R3 29), (getr R3 30), (getr R3 31), (ms_mem ms3), ws1, l', h5'.
  refine (conj eq_refl (conj MUNCH (conj WMONO (conj STK3 (conj LIMBS3 (conj L62' (conj LENC3 (conj _ (conj _ (conj BN (conj PR3 (conj RT3 _)))))))))))).
  - lia.
  - lia.
  - exact (conj FSC3 (conj HINT (conj FL3 (conj STKS STKH)))).
Qed.

End LME.


(* [comment removed for export] *)
Theorem long_mul_fx : long_mul_stmt.
Proof.
  unfold long_mul_stmt. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ws len v h5.
  cbv zeta. intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NORM Ha1 Ha2 CAP SEP TP PRG PRT RTH FK KSP KSP2 KA0 KA1 SFS SEPF RD1 RD2 RD3 SHX SHT RBX RBF RTX0 RAE.
  pose proof RTH as R6. unfold RT in R6. destruct R6 as (_ & _ & _ & _ & _ & (fb & Hfb1 & Hfb2) & _).
  eapply lme_run.
  all: first [ exact (conj Hfb1 Hfb2) | eassumption ].
Qed.
