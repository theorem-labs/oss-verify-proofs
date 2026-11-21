(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U Require Base.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK Require ZStep ZMem ZTac ZCall ZCallL ZArr ZArr4 IDefs ISpecs ITac.

Module T_Fast1.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInvTab.
Export OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U.Base.
Export OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.ZStep OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.ITac.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Ltac zmem_transport_loop_T_Fast2 M a bs :=
  repeat match goal with
  | H : mem_arr ?k ?segs M ?base ?n ?f |- _ =>
      first [ apply (mem_arr_frame segs k M base n f a bs) in H; [|unfold zdisj; zlen_norm; zlia]
            | idtac "WARNING: mem_arr fact dropped at store" a base; clear H ]
  | H : mem_u64 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 8;
      first [ apply (mem_u64_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u32 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 4;
      first [ apply (mem_u32_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u16 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 2;
      first [ apply (mem_u16_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u8 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 1;
      first [ apply (mem_u8_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_is ?segs M ?a' ?bs' |- _ =>
      zrng_ensure a' (Z.of_nat (length bs'));
      first [ apply (mem_is_frame segs M a bs a' bs') in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_wr ?segs M ?a' ?len |- _ =>
      apply (mem_wr_frame segs M a bs a' len) in H
  | H : rom_ok M |- _ =>
      first [ apply (rom_ok_frame M a bs) in H; [| zlia | zlen_norm; zlia | unfold ROM_LO, ROM_HI; zdisj_tac]
            | idtac "WARNING: rom_ok dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stable ?Fr ?lo ?hi |- _ =>
      first [ apply (HS M a bs) in H; [|zlia|zlen_norm; zlia]
            | idtac "WARNING: framed fact dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stable2 ?Fr _ _ _ _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; zlia]
            | idtac "WARNING: framed2 fact dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stableL ?Fr _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; in_some_tac]
            | idtac "WARNING: framedL fact dropped at store" a; clear H ]
  | H : rdn ?segs M _ _ = Some _ |- _ => clear H
  end.
Ltac zmem_transport M a bs ::=
  zxfer_pre a bs;
  zmem_transport_loop_T_Fast2 M a bs;
  zxfer_post a.

Ltac zlia_chk ::= zlia.

Definition L_FENTRY : Z := 103324.
Definition L_FHEAD : Z := 103676.
Definition L_FLOOK : Z := 103728.
Definition L_FLIT : Z := 103868.
Definition L_FLATCH : Z := 103888.
Definition L_FLENB : Z := 103904.
Definition L_FDLOOK : Z := 104040.
Definition L_FDISTB : Z := 104184.
Definition L_FWIN : Z := 104296.
Definition L_FDIRECT : Z := 104528.
Definition L_FEOB : Z := 105164.
Definition L_FBADD : Z := 105184.
Definition L_FMSG : Z := 105192.
Definition L_FEXIT : Z := 105220.
Definition L_FTOOFAR : Z := 105444.

Lemma pow2_pos : forall k, 0 <= k -> 0 < 2 ^ k.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.
Lemma pow2_le : forall a b, 0 <= a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros. apply Z.pow_le_mono_r; lia. Qed.
Lemma pow2_15 : forall k, 0 <= k <= 15 -> 1 <= 2 ^ k <= 32768.
Proof. intros k Hk. split; [pose proof (pow2_pos k ltac:(lia)); lia | change 32768 with (2 ^ 15); apply pow2_le; lia]. Qed.

Lemma mask_not_sllw : forall k, 0 <= k <= 30 ->
  Z.lxor (bv_swrap 32 (Z.shiftl (-1) (k mod 32))) (-1) = 2 ^ k - 1.
Proof.
  intros k Hk. rewrite (Z.mod_small k 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  assert (B : 1 <= 2 ^ k <= 1073741824) by (split; [pose proof (pow2_pos k ltac:(lia)); lia | change 1073741824 with (2 ^ 30); apply pow2_le; lia]).
  rewrite swrap32_small by lia. rewrite lxor_m1. lia.
Qed.

Lemma land_mask_range : forall x k, 0 <= k -> 0 <= Z.land x (2 ^ k - 1) < 2 ^ k.
Proof. intros. apply land_ones_range. assumption. Qed.
Lemma land_mask_range' : forall x k, 0 <= k -> 0 <= Z.land x (2 ^ k + -1) < 2 ^ k.
Proof. intros x k Hk. replace (2 ^ k + -1) with (2 ^ k - 1) by lia. apply land_ones_range. assumption. Qed.
Lemma land_mask_le : forall x k, 0 <= k -> 0 <= x -> Z.land x (2 ^ k - 1) <= x.
Proof.
  intros x k Hk Hx. replace (2 ^ k - 1) with (Z.ones k) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  rewrite Z.land_ones by lia. apply Z.mod_le; [lia | apply pow2_pos; lia].
Qed.

Lemma srl_hold : forall hold bits k, 0 <= hold < 2 ^ bits -> 0 <= bits <= 63 -> 0 <= k <= 63 ->
  Z.shiftr (hold mod 18446744073709551616) (k mod 64) = hold / 2 ^ k.
Proof.
  intros hold bits k Hh Hb Hk.
  assert (2 ^ bits <= 2 ^ 63) by (apply pow2_le; lia).
  rewrite (Z.mod_small k 64) by lia. rewrite Z.mod_small by (change 18446744073709551616 with (2 * 2 ^ 63); lia).
  apply Z.shiftr_div_pow2. lia.
Qed.
Lemma hold_shr_bound : forall hold bits k, 0 <= hold < 2 ^ bits -> 0 <= k <= bits ->
  0 <= hold / 2 ^ k < 2 ^ (bits - k).
Proof.
  intros hold bits k Hh Hk. pose proof (pow2_pos k ltac:(lia)).
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k + (bits - k)) with bits by lia. lia.
Qed.

Lemma shl_byte : forall b s, 0 <= b < 256 -> 0 <= s <= 63 -> Z.shiftl b (s mod 64) = b * 2 ^ s /\ 0 <= b * 2 ^ s.
Proof.
  intros b s Hb Hs. rewrite (Z.mod_small s 64) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  pose proof (pow2_pos s ltac:(lia)). split; [reflexivity | nia].
Qed.
Lemma hold_pull1 : forall hold bits b, 0 <= hold < 2 ^ bits -> 0 <= bits -> 0 <= b < 256 ->
  0 <= hold + b * 2 ^ bits < 2 ^ (bits + 8).
Proof.
  intros hold bits b Hh Hbits Hb. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  pose proof (pow2_pos bits Hbits). nia.
Qed.
Lemma hold_pull2 : forall hold bits b0 b1, 0 <= hold < 2 ^ bits -> 0 <= bits -> 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  0 <= hold + b0 * 2 ^ bits + b1 * 2 ^ (bits + 8) < 2 ^ (bits + 16).
Proof.
  intros hold bits b0 b1 Hh Hbits H0 H1.
  pose proof (hold_pull1 hold bits b0 Hh Hbits H0) as A.
  pose proof (hold_pull1 (hold + b0 * 2 ^ bits) (bits + 8) b1 A ltac:(lia) H1) as B.
  replace (bits + 8 + 8) with (bits + 16) in B by lia. lia.
Qed.
Lemma lor_16 : forall b, 0 <= b < 16 -> Z.lor b 16 = b + 16.
Proof.
  intros b Hb.
  assert (E : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11
              \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15) by lia.
  repeat (destruct E as [E|E]; [subst b; reflexivity|]). subst b; reflexivity.
Qed.
Lemma land_7_mod : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma zfupd_byte : forall (f : Z -> Z) i v lo hi,
  (forall j, lo <= j < hi -> 0 <= f j < 256) -> 0 <= v < 256 -> forall j, lo <= j < hi -> 0 <= zfupd f i v j < 256.
Proof. intros f i v lo hi Hf Hv j Hj. unfold zfupd. destruct (Z.eqb_spec j i); [lia | apply Hf; lia]. Qed.
Lemma mod_256_range : forall x, 0 <= x mod 256 < 256.
Proof. intros. apply Z.mod_pos_bound. lia. Qed.

Record fcx := FCX {
  f_u : Z; f_p : Z; f_q : Z; f_n : Z; f_ob : Z; f_osz : Z; f_w : Z;
  f_whave : Z; f_wnext : Z; f_wn : Z;
  f_lb : Z; f_db : Z; f_la : Z; f_na : Z; f_da : Z; f_nd : Z;
  f_spi : Z; f_bo : Z; f_cout0 : Z; f_W0 : Z; f_s8 : Z; f_gp : Z; f_tp : Z;
  f_zc : Z;
  f_rdL : Z -> Z; f_rdD : Z -> Z; f_fin : Z -> Z; f_fw : Z -> Z }.

Ltac fcx_cbn := cbn [f_u f_p f_q f_n f_ob f_osz f_w f_whave f_wnext f_wn f_lb f_db f_la f_na f_da f_nd
                     f_spi f_bo f_cout0 f_W0 f_s8 f_gp f_tp f_zc f_rdL f_rdD f_fin f_fw] in *.

Definition PFOLD (P : Prop) : Prop := P.

Definition fcx_ok (cx : fcx) : Prop :=
  let u := f_u cx in let p := f_p cx in let q := f_q cx in let n := f_n cx in let ob := f_ob cx in let osz := f_osz cx in
  let w := f_w cx in let whave := f_whave cx in let wnext := f_wnext cx in let wn := f_wn cx in
  let lb := f_lb cx in let db := f_db cx in let la := f_la cx in let na := f_na cx in let da := f_da cx in let nd := f_nd cx in
  let spi := f_spi cx in let bo := f_bo cx in let cout0 := f_cout0 cx in let s8v := f_s8 cx in let zc := f_zc cx in
  1024 + zc <= u /\ u + 208 <= 140737488355328 /\ spi + 224 <= u /\ u + -864 <= spi /\
  0 < p /\ p + 7176 <= zc /\
  1 <= q /\ 0 <= n /\ n < 67108864 /\ 6 <= n /\ q + n <= zc /\
  0 < ob /\ 1 <= osz /\ osz <= 262144 /\ ob + osz <= u /\ ZSEP (ob + osz <= u + -1024 \/ u + 7 <= ob) /\
  ZSEP (p + 7176 <= ob \/ ob + osz <= p) /\ ZSEP (p + 7176 <= q \/ q + n <= p) /\ ZSEP (ob + osz <= q \/ q + n <= ob) /\
  0 <= w /\ w + wn <= zc /\
  ZSEP (p + 7176 <= w \/ w + wn <= p) /\ ZSEP (w + wn <= q \/ q + n <= w) /\ ZSEP (w + wn <= ob \/ ob + osz <= w) /\
  0 < la /\ la + 4 * na <= zc /\ 0 < da /\ da + 4 * nd <= zc /\ 0 <= na /\ 0 <= nd /\
  ZSEP (la + 4 * na <= ob \/ ob + osz <= la) /\ ZSEP (la + 4 * na <= p \/ p + 1384 <= la) /\
  ZSEP (da + 4 * nd <= ob \/ ob + osz <= da) /\ ZSEP (da + 4 * nd <= p \/ p + 1384 <= da) /\
  1 <= lb /\ lb <= 15 /\ 1 <= db /\ db <= 15 /\
  tab_ok LENS (f_rdL cx) lb na = true /\ tab_ok DISTS (f_rdD cx) db nd = true /\
  0 <= whave /\ 0 <= wnext /\ whave <= wn /\ wnext <= wn /\ wn <= 32768 /\ wn <= 32768 * w /\
  0 <= bo /\ bo <= cout0 /\ 0 <= cout0 /\ cout0 <= osz /\ cout0 + 258 <= osz /\
  ZSEP (wnext = 0 \/ s8v = w + wnext) /\
  (forall i, 0 <= i < n -> 0 <= f_fin cx i < 256) /\ (forall i, 0 <= i < wn -> 0 <= f_fw cx i < 256) /\
  u mod 16 = 0 /\ p mod 16 = 0 /\ la mod 2 = 0 /\ da mod 2 = 0.

Ltac open_ok H :=
  unfold fcx_ok in H; cbv zeta in H; fcx_cbn;
  destruct H as (Cu1 & Cu2 & Cu3 & Cu4 & Cp1 & Cp2 & Cq1 & Cn1 & Cn2 & Cn3 & Cq2 &
                 Cob1 & Cosz1 & Cosz2 & Cob2 & Sobu & Spob & Spq & Sobq & Cw1 & Cw2 & Swp & Swq & Swob &
                 Cla1 & Cla2 & Cda1 & Cda2 & Cna & Cnd & Slaob & Slap & Sdaob & Sdap &
                 Clb1 & Clb2 & Cdb1 & Cdb2 & TOKL & TOKD &
                 Cwh1 & Cwn1 & Cwh2 & Cwn2 & Cwn3 & Cwn4 & Cbo1 & Cbo2 & Cco1 & Cco2 & Cco3 & Cs8 & Rfin & Rfw & Calu & Calp & Call & Cald).

Definition f_const (cx : fcx) (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kA0 = f_u cx /\ zget_l R l kA1 = f_p cx /\ zget_l R l kA2 = f_q cx + f_n cx + -5 /\
  zget_l R l kS5 = f_ob cx + f_osz cx + -257 /\
  zget_l R l kT5 = f_la cx /\ zget_l R l kT6 = f_da cx /\ zget_l R l kS4 = 2 ^ f_lb cx - 1 /\ zget_l R l kT3 = f_wnext cx /\
  zget_l R l kS8 = - f_la cx + -1 /\ zget_l R l kS9 = - f_da cx + -1 /\ zget_l R l kS10 = 1 /\
  zget_l R l kS0 = -1 /\ zget_l R l kS2 = 2 /\ zget_l R l kS3 = 63 /\ zget_l R l kA7 = 31 /\
  zget_l R l kSP = f_spi cx + -160 /\ zget_l R l kGP = f_gp cx /\ zget_l R l kTP = f_tp cx.

Ltac open_const H :=
  unfold f_const in H; fcx_cbn;
  dand H as (Ga0 & Ga1 & Ga2 & Gs5 & Gt5 & Gt6 & Gs4 & Gt3 & Gs8 & Gs9 & Gs10 & Gs0 & Gs2 & Gs3 & Ga7 & Gsp & Ggp & Gtp).
Ltac close_const := unfold f_const; fcx_cbn; split_conj; zreg.

Definition f_live {RCa1 : RunCtx}  (cx : fcx) (fo : Z -> Z) (M : mem) : Prop :=
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_u cx + -1024) 1232 /\ mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_p cx) 7176 /\ mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_ob cx) (f_osz cx) /\
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_w cx) (f_wn cx) (f_fw cx) /\
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_ob cx) (f_osz cx) fo.

Ltac open_live H :=
  unfold f_live in H; fcx_cbn;
  dand H as (Wu & Wp & Wob & Hwin & HOB).
Ltac close_live := unfold f_live; fcx_cbn; split_conj; assumption.

Definition f_ro {RCa1 : RunCtx}  (cx : fcx) (M : mem) : Prop :=
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_q cx) (f_n cx) (f_fin cx) /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_la cx) (f_na cx) (f_rdL cx) /\
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_da cx) (f_nd cx) (f_rdD cx) /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_p cx + 7160) 1 /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_spi cx + -112) (2 ^ f_db cx - 1) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_spi cx + -120) (f_w cx) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_spi cx + -128) (f_ob cx + f_bo cx) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_spi cx + -136) (f_whave cx) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_spi cx + -144) (f_p cx + 7160) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_spi cx + -152) (f_wn cx) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_spi cx + -160) (f_wn cx + f_wnext cx).

Ltac open_ro H :=
  unfold f_ro in H; fcx_cbn;
  dand H as (Hin & HtL & HtD & Hsane & Q48 & Q40 & Q32 & Q24 & Q16 & Q8 & Q0).

Definition FPW (cx : fcx) : list (Z * Z) := [(f_ob cx, f_osz cx)].
Definition FP1 (cx : fcx) : list (Z * Z) := [(f_ob cx, f_osz cx); (f_p cx + 8, 4); (f_u cx, 56); (f_p cx + 96, 12)].

Lemma f_ro_now {RCa1 : RunCtx}  : forall cx M1 M, fcx_ok cx -> f_ro cx M1 -> framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M -> f_ro cx M.
Proof.
  intros cx M1 M CX H [HA _].
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. unfold f_ro, FPW in *. fcx_cbn. pose proof two64_eq as TW64.
  dand H as (A1 & A2 & A3 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  pose proof (mem_arr_bounds _ _ _ _ _ _ A1) as B1.
  split_conj;
  first [ eapply mem_arr_magreeL; [exact HA | eassumption | cbn [disj_all]; split; [zlia | exact I]]
        | eapply mem_u64_magreeL; [exact HA | eassumption | lia | lia | cbn [disj_all]; split; [zlia | exact I]]
        | eapply mem_u32_magreeL; [exact HA | eassumption | lia | lia | cbn [disj_all]; split; [zlia | exact I]] ].
Qed.

Definition fW (cx : fcx) (ci bits co : Z) : Z := 8 * (f_n cx - ci) + bits + (f_osz cx - co).

Section K.
Context {RCa1 : RunCtx}.
Variables (cx : fcx) (M1 : mem) (MD : Model) (T : TSet).

Definition KEXIT : Prop :=
  forall (R : tree Z) (M : mem) (ci co hold bits mode : Z) (fo : Z -> Z),
    zget_l R [] kA0 = f_u cx -> zget_l R [] kA1 = f_p cx -> zget_l R [] kA2 = f_q cx + f_n cx + -5 ->
    zget_l R [] kS5 = f_ob cx + f_osz cx + -257 -> zget_l R [] kSP = f_spi cx + -160 ->
    zget_l R [] kGP = f_gp cx -> zget_l R [] kTP = f_tp cx ->
    zget_l R [] kA4 = hold -> zget_l R [] kA6 = f_q cx + ci -> zget_l R [] kS6 = f_ob cx + co -> zget_l R [] kA5 = bits ->
    0 <= ci -> ci <= f_n cx -> f_cout0 cx <= co -> co <= f_osz cx -> 0 <= bits -> bits <= 40 -> bits <= 8 * ci ->
    0 <= hold -> hold < 2 ^ bits -> fW cx ci bits co < f_W0 cx -> fW cx ci bits (f_cout0 cx) <= f_W0 cx ->
    PFOLD (mode = LEN \/ mode = TYPE \/ mode = BAD) ->
    mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_u cx + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_p cx) 7176 ->
    mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_ob cx) (f_osz cx) fo -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_p cx + 8) mode ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FP1 cx)) M ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FEXIT (zupd R []) M MD) T.

Definition KLATCH (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (ci co hold bits : Z) (fo : Z -> Z),
    f_const cx R [] ->
    zget_l R [] kA4 = hold -> zget_l R [] kA6 = f_q cx + ci -> zget_l R [] kS6 = f_ob cx + co -> zget_l R [] kA5 = bits ->
    0 <= ci -> ci <= f_n cx -> f_cout0 cx <= co -> co <= f_osz cx -> 0 <= bits -> bits <= 40 -> bits <= 8 * ci ->
    0 <= hold -> hold < 2 ^ bits -> fW cx ci bits co < B -> fW cx ci bits co < f_W0 cx -> fW cx ci bits (f_cout0 cx) <= f_W0 cx ->
    f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLATCH (zupd R []) M MD) T.
End K.


Definition f_frame {RCa1 : RunCtx}  (cx : fcx) (Rb : tree Z) (l : list (positive * Z)) (ret : Z) (M1 : mem) : Prop :=
  let sp := f_spi cx in
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (sp + -8) ret /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (sp + -16) (zget_l Rb l kS0) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (sp + -24) (zget_l Rb l kS1) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (sp + -32) (zget_l Rb l kS2) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (sp + -40) (zget_l Rb l kS3) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (sp + -48) (zget_l Rb l kS4) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (sp + -56) (zget_l Rb l kS5) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (sp + -64) (zget_l Rb l kS6) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (sp + -72) (zget_l Rb l kS7) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (sp + -80) (zget_l Rb l kS8) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (sp + -88) (zget_l Rb l kS9) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (sp + -96) (zget_l Rb l kS10) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (sp + -104) (zget_l Rb l kS11).

Definition KRET {RCa1 : RunCtx}  (cx : fcx) (Rb : tree Z) (l : list (positive * Z)) (ret : Z) (M0 : mem) (MD : Model) (T : TSet) : Prop :=
  forall (R' : tree Z) (M' : mem) (cin' cout' hold' bits' mode' : Z) (fo' : Z -> Z),
     0 <= cin' -> cin' <= f_n cx -> f_cout0 cx <= cout' -> cout' <= f_osz cx ->
     0 <= bits' -> bits' <= 7 -> 0 <= hold' -> hold' < 2 ^ bits' -> bits' <= 8 * cin' ->
     8 * (f_n cx - cin') + bits' + (f_osz cx - cout') < f_W0 cx ->
     8 * (f_n cx - cin') + bits' + (f_osz cx - f_cout0 cx) <= f_W0 cx ->
     (mode' = LEN \/ mode' = TYPE \/ mode' = BAD) ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M' (if_fp (f_u cx) (f_p cx) (f_ob cx) (f_osz cx) (f_spi cx) 160) ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (f_u cx) (f_q cx + cin') -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (f_u cx + 8) (f_n cx - cin') ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (f_u cx + 24) (f_ob cx + cout') -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (f_u cx + 32) (f_osz cx - cout') ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (f_p cx + 96) hold' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (f_p cx + 104) bits' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (f_p cx + 8) mode' ->
     mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' (f_ob cx) (f_osz cx) fo' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
     kept_eq Rb l R' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T.

Lemma mem_u64_retype {RCa1 : RunCtx}  : forall M a e e', mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a e -> e = e' -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a e'.
Proof. intros; subst; assumption. Qed.
Lemma mem_u32_retype {RCa1 : RunCtx}  : forall M a e e', mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a e -> e = e' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a e'.
Proof. intros; subst; assumption. Qed.

Ltac zswrapb :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, Z.b2z (bv_swrap 64 ?a <? bv_swrap 64 ?b)) :: _)) _ _) _ =>
      zsetreg (Z.b2z (a <? b)) ltac:(rewrite !swrap64_small by lia; reflexivity)
  | |- realizes _ (zcfg _ _ (zupd _ ((_, Z.b2z (?a <? bv_swrap 64 ?b)) :: _)) _ _) _ =>
      zsetreg (Z.b2z (a <? b)) ltac:(rewrite !swrap64_small by lia; reflexivity)
  | |- realizes _ (zcfg _ _ (zupd _ ((_, Z.b2z (bv_swrap 64 ?a <? ?b)) :: _)) _ _) _ =>
      zsetreg (Z.b2z (a <? b)) ltac:(rewrite !swrap64_small by lia; reflexivity)
  end.
Lemma m1_mod64 : (-1) mod 18446744073709551616 = 18446744073709551615.
Proof. reflexivity. Qed.

Lemma fast_exit {RCa1 : RunCtx}  : forall cx Rb l M0 M1 MD T ret,
  fcx_ok cx -> m_halted MD = None -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  zget_l Rb l kSP = f_spi cx -> zget_l Rb l kGP = f_gp cx -> zget_l Rb l kTP = f_tp cx ->
  f_frame cx Rb l ret M1 ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M1 [(f_spi cx + -160, 160)] ->
  KRET cx Rb l ret M0 MD T ->
  KEXIT cx M1 MD T.
Proof.
  intros cx Rb l M0 M1 MD T ret CX Hh Hret1 Hret2 Esp Egp Etp FR PRO K.
  intros R M ci co hold bits mode fo La0 La1 La2 Ls5 Lsp Lgp Ltp La4 La6 Ls6 La5
         Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hb3 Hh1 Hh2 HW HWI Hmode Wu Wp HOB Rfo Hm8 HAG.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. unfold KRET, f_frame, fW, FP1 in *. fcx_cbn.
  clear Spq Sobq Cw1 Cw2 Swp Swq Swob Cla1 Cla2 Cda1 Cda2 Cna Cnd Slaob Slap Sdaob Sdap Clb1 Clb2 Cdb1 Cdb2 TOKL TOKD
        Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cwn4 Cs8 Rfin Rfw Calu Calp Call Cald.
  dand FR as (F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
  zkeys. unfold L_FEXIT in *. pose proof two64_eq as TW64. pose proof m1_mod64 as Hm1.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz); (p + 8, 4); (u, 56); (p + 96, 12)] ltac:(ranges_ok_tac)) as HST.
  pose proof (Z.div_mod bits 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound bits 8 ltac:(lia)) as Hr8.
  set (b8 := bits / 8) in *. set (r8 := bits mod 8) in *.
  assert (Eb8 : b8 = bits / 8) by reflexivity. assert (Er8 : r8 = bits mod 8) by reflexivity. clearbody b8 r8.
  assert (HPb : 2 ^ bits <= 2 ^ 40) by (apply pow2_le; lia).
  pose proof (land_mask_range hold r8 ltac:(lia)) as Hmask. replace (2 ^ r8 - 1) with (2 ^ r8 + -1) in Hmask by lia.
  pose proof (pow2_15 r8 ltac:(lia)) as Hp8.
  assert (J2 : forall RX, zget RX 11 = u -> zget RX 12 = p -> zget RX 3 = spi + -160 -> zget RX 4 = vgp -> zget RX 5 = vtp ->
            zget RX 15 = hold -> zget RX 16 = bits -> zget RX 13 = osz - co ->
            forall MX, mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) MX (u + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) MX p 7176 ->
            mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) MX ob osz fo -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) MX (p + 8) mode ->
            mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) MX (u) (q + ci - b8) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) MX (u + 24) (ob + co) -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) MX (u + 8) (n - (ci - b8)) ->
            framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X [(ob, osz); (p + 8, 4); (u, 56); (p + 96, 12)]) MX ->
            realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 105352 (zupd RX []) MX MD) T).
  { intros RX G11 G12 G3 G4 G5 G15 G16 G13 MX Wu' Wp' HOB' Hm8' E8 E32 E16 HAG'.
    zstep Rfd.
    zsetreg r8 ltac:(rewrite Er8; symmetry; apply land_7_mod; lia).
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (2 ^ r8 - 1) ltac:(symmetry; apply mask_not_sllw; lia).
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zderiveL HAG' F1 G1'. zderiveL HAG' F8 G8'. zderiveL HAG' F9 G9'. zderiveL HAG' F18 G18'. zderiveL HAG' F19 G19'.
    zderiveL HAG' F20 G20'. zderiveL HAG' F21 G21'. zderiveL HAG' F22 G22'. zderiveL HAG' F23 G23'. zderiveL HAG' F24 G24'.
    zderiveL HAG' F25 G25'. zderiveL HAG' F26 G26'. zderiveL HAG' F27 G27'.
    do 13 (zstep Rfd).
    zstep Rfd.
    zret Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rr ?Mx _) _ =>
      eapply (K Rr Mx (ci - b8) co (Z.land hold (2 ^ r8 + -1)) r8 mode fo) end.
    all: try lia.
    - exact Hmode.
    - eapply mpostL_trans.
      + eapply (framed_mpostL_weaken (run_segments R_segs rc_inp rc_sp rc_mb) M0 M1); [| exact PRO]. unfold if_fp. ranges_within_tac.
      + eapply (framed_mpostL_weaken (run_segments R_segs rc_inp rc_sp rc_mb) M1); [| exact HAG']. unfold if_fp. ranges_within_tac.
    - eapply mem_u64_retype; [zfact_exact | lia].
    - eapply mem_u32_retype; [zfact_exact | lia].
    - zfact_exact.
    - zfact_exact.
    - zfact_exact.
    - zfact_exact.
    - assumption.
    - assumption.
    - exact Rfo.
    - unfold kept_eq. zkeys. split_conj; zreg. }
  assert (J1 : forall RX, zget RX 11 = u -> zget RX 12 = p -> zget RX 3 = spi + -160 -> zget RX 4 = vgp -> zget RX 5 = vtp ->
            zget RX 15 = hold -> zget RX 16 = bits -> zget RX 13 = n - (ci - b8) -> zget RX 23 = ob + co -> zget RX 22 = ob + osz + -257 ->
            forall MX, mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) MX (u + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) MX p 7176 ->
            mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) MX ob osz fo -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) MX (p + 8) mode ->
            mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) MX (u) (q + ci - b8) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) MX (u + 24) (ob + co) ->
            framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X [(ob, osz); (p + 8, 4); (u, 56); (p + 96, 12)]) MX ->
            realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 105304 (zupd RX []) MX MD) T).
  { intros RX G11 G12 G3 G4 G5 G15 G16 G13 G23 G22 MX Wu' Wp' HOB' Hm8' E8 E32 HAG'.
    zstep Rfd.
    destruct (Z_lt_dec (ob + co) (ob + osz + -257)) as [Hlt|Hge].
    - zbr Rfd false.
      zstep Rfd.
      zstep Rfd.
      zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rr ?Mx _) _ => eapply (J2 Rr) end; try zreg; try assumption.
    - zbr Rfd true.
      zstep Rfd.
      zstep Rfd.
      destruct (Z_lt_dec 0 (ob + co - (ob + osz + -257))) as [Hp|Hz].
      + zstep Rfd. zswrapb. zbool.
        zstep Rfd.
        zstep Rfd. zswrapb. zbool.
        zbr Rfd false.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rr ?Mx _) _ => eapply (J2 Rr) end; try zreg; try assumption.
      + zstep Rfd. zswrapb. zbool.
        zstep Rfd.
        zstep Rfd. zswrapb. zbool.
        zbr Rfd false.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rr ?Mx _) _ => eapply (J2 Rr) end; try zreg; try assumption. }
  clear J2.
  zrebase.
  zstep Rfd.
  zsetreg b8 ltac:(rewrite Eb8; symmetry; etransitivity; [apply srliw_small; lia | reflexivity]).
  zbr Rfd false.
  zstep Rfd. zbool.
  zstep Rfd.
  zstep Rfd.
  zsetreg 0 ltac:(symmetry; apply seqz_xor_neq; lia).
  zstep Rfd. zlit.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  destruct (Z_lt_dec (q + ci - b8) (q + n + -5)) as [Hlt|Hge].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rr ?Mx _) _ => eapply (J1 Rr) end; try zreg; try assumption.
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    destruct (Z_lt_dec 0 (q + ci - b8 - (q + n + -5))) as [Hp|Hz].
    + zstep Rfd. zswrapb. zbool.
      zstep Rfd.
      zstep Rfd. zswrapb. zbool.
      zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rr ?Mx _) _ => eapply (J1 Rr) end; try zreg; try assumption.
    + zstep Rfd. zswrapb. zbool.
      zstep Rfd.
      zstep Rfd. zswrapb. zbool.
      zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rr ?Mx _) _ => eapply (J1 Rr) end; try zreg; try assumption.
Qed.

Lemma land_le_l : forall a b, 0 <= a -> Z.land a b <= a.
Proof.
  intros a b Ha.
  assert (D : Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ D) as E. rewrite (Z.lxor_lor _ _ D), Z.lor_ldiff_and in E.
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; left; exact Ha). lia.
Qed.
Lemma land_range_r : forall a b, 0 <= b -> 0 <= Z.land a b <= b.
Proof. intros a b Hb. split; [apply Z.land_nonneg; lia | rewrite Z.land_comm; apply land_le_l; lia]. Qed.

Definition XPRE {RCa1 : RunCtx}  (cx : fcx) (M1 : mem) (R : tree Z) (l : list (positive * Z)) (M : mem)
           (ci co hold bits : Z) (fo : Z -> Z) : Prop :=
  zget_l R l kA0 = f_u cx /\ zget_l R l kA1 = f_p cx /\ zget_l R l kA2 = f_q cx + f_n cx + -5 /\
  zget_l R l kS5 = f_ob cx + f_osz cx + -257 /\ zget_l R l kSP = f_spi cx + -160 /\
  zget_l R l kGP = f_gp cx /\ zget_l R l kTP = f_tp cx /\
  zget_l R l kA4 = hold /\ zget_l R l kA6 = f_q cx + ci /\ zget_l R l kS6 = f_ob cx + co /\ zget_l R l kA5 = bits /\
  0 <= ci /\ ci <= f_n cx /\ f_cout0 cx <= co /\ co <= f_osz cx /\ 0 <= bits /\ bits <= 40 /\ bits <= 8 * ci /\
  0 <= hold /\ hold < 2 ^ bits /\ fW cx ci bits co < f_W0 cx /\ fW cx ci bits (f_cout0 cx) <= f_W0 cx /\
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_u cx + -1024) 1232 /\ mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_p cx) 7176 /\
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_ob cx) (f_osz cx) fo /\ (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) /\
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M.

Ltac open_xpre H :=
  unfold XPRE, fW, FPW in H; fcx_cbn;
  dand H as (La0 & La1 & La2 & Ls5 & Lsp & Lgp & Ltp & La4 & La6 & Ls6 & La5 &
                 Hci1 & Hci2 & Hco1 & Hco2 & Hb1 & Hb2 & Hb3 & Hh1 & Hh2 & HW & HWI & Wu & Wp & HOB & Rfo & HAG).

Definition KERR {RCa1 : RunCtx}  (cx : fcx) (M1 : mem) (MD : Model) (T : TSet) (pc : Z) : Prop :=
  forall R l M ci co hold bits fo, XPRE cx M1 R l M ci co hold bits fo -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd R l) M MD) T.

Lemma fast_msg {RCa1 : RunCtx}  : forall cx M1 MD T, fcx_ok cx -> m_halted MD = None -> KEXIT cx M1 MD T -> KERR cx M1 MD T L_FMSG.
Proof.
  intros cx M1 MD T CX Hh HEX R l M ci co hold bits fo XP.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. open_xpre XP. unfold KEXIT, FP1, fW in HEX. fcx_cbn.
  clear Spq Sobq Cw1 Cw2 Swp Swq Swob Cla1 Cla2 Cda1 Cda2 Cna Cnd Slaob Slap Sdaob Sdap Clb1 Clb2 Cdb1 Cdb2 TOKL TOKD
        Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cwn4 Cs8 Rfin Rfw Calu Calp Call Cald.
  zkeys. unfold L_FMSG, L_FEXIT in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz); (p + 8, 4); (u, 56); (p + 96, 12)] ltac:(ranges_ok_tac)) as HST.
  apply (framed_mpostL_weaken (run_segments R_segs rc_inp rc_sp rc_mb) M1 M [(ob, osz)] [(ob, osz); (p + 8, 4); (u, 56); (p + 96, 12)] ltac:(ranges_within_tac)) in HAG.
  zrebase.
  zstep Rfd.
  zstep Rfd. zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (HEX Rx Mx ci co hold bits BAD fo) end.
  all: try zreg. all: try assumption. all: try zfact_exact. all: unfold PFOLD; (first [solve [zkeep_section; tauto] | tauto]).
Qed.

Lemma fast_badd {RCa1 : RunCtx}  : forall cx M1 MD T, fcx_ok cx -> m_halted MD = None -> KEXIT cx M1 MD T -> KERR cx M1 MD T L_FBADD.
Proof.
  intros cx M1 MD T CX Hh HEX R l M ci co hold bits fo XP.
  pose proof (fast_msg cx M1 MD T CX Hh HEX) as KM. unfold KERR in KM.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_xpre XP. zkeys. unfold L_FBADD, L_FMSG in *.
  zstep Rfd. zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ => apply (KM Rx lx Mx ci co hold bits fo) end.
  unfold XPRE. fcx_cbn. split_conj; try zreg; try assumption.
Qed.

Lemma fast_toofar {RCa1 : RunCtx}  : forall cx M1 MD T, fcx_ok cx -> m_halted MD = None -> KEXIT cx M1 MD T -> KERR cx M1 MD T L_FTOOFAR.
Proof.
  intros cx M1 MD T CX Hh HEX R l M ci co hold bits fo XP.
  pose proof (fast_msg cx M1 MD T CX Hh HEX) as KM. unfold KERR in KM.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_xpre XP. zkeys. unfold L_FTOOFAR, L_FMSG in *.
  zstep Rfd. zstep Rfd. zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ => apply (KM Rx lx Mx ci co hold bits fo) end.
  unfold XPRE. fcx_cbn. split_conj; try zreg; try assumption.
Qed.

Lemma fast_eob {RCa1 : RunCtx}  : forall cx M1 MD T, fcx_ok cx -> m_halted MD = None -> KEXIT cx M1 MD T ->
  forall R l M ci co hold bits fo op,
    XPRE cx M1 R l M ci co hold bits fo -> zget_l R l kA3 = op -> 0 <= op < 256 ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FEOB (zupd R l) M MD) T.
Proof.
  intros cx M1 MD T CX Hh HEX R l M ci co hold bits fo op XP La3 Hop.
  pose proof (fast_msg cx M1 MD T CX Hh HEX) as KM. unfold KERR in KM.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. open_ok CX. open_xpre XP. unfold KEXIT, FP1, fW in HEX. fcx_cbn.
  clear Spq Sobq Cw1 Cw2 Swp Swq Swob Cla1 Cla2 Cda1 Cda2 Cna Cnd Slaob Slap Sdaob Sdap Clb1 Clb2 Cdb1 Cdb2 TOKL TOKD
        Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cwn4 Cs8 Rfin Rfw Calu Calp Call Cald.
  zkeys. unfold L_FEOB, L_FMSG, L_FEXIT in *. pose proof two64_eq as TW64.
  pose proof (land_range_r op 32 ltac:(lia)) as H32.
  zrebase.
  zstep Rfd.
  destruct (Z.eq_dec (Z.land op 32) 0) as [Z32|NZ32].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ => apply (KM Rx lx Mx ci co hold bits fo) end.
    unfold XPRE. fcx_cbn. split_conj; try zreg; try assumption.
  - zbr Rfd true.
    zstep Rfd. zstep Rfd.
    pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz); (p + 8, 4); (u, 56); (p + 96, 12)] ltac:(ranges_ok_tac)) as HST.
    apply (framed_mpostL_weaken (run_segments R_segs rc_inp rc_sp rc_mb) M1 M [(ob, osz)] [(ob, osz); (p + 8, 4); (u, 56); (p + 96, 12)] ltac:(ranges_within_tac)) in HAG.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (HEX Rx Mx ci co hold bits TYPE fo) end.
    all: try zreg. all: try assumption. all: try zfact_exact. all: unfold PFOLD; (first [solve [zkeep_section; tauto] | tauto]).
Qed.
End T_Fast1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv InflateInvTab.
Import T_Fast1.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Lemma zu_lbu_arr4_vlo {RCa1 : RunCtx}  : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word (run_segments R_segs rc_inp rc_sp rc_mb) (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M base n f -> zrd_l Rb l rs + bv_signed imm = base + 4 * i + 2 -> 0 <= i < n ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (pc + 4) (zupd Rb (wb rd (code_val (f i) mod 256) l)) M MD) T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hk.
  dand (mem_arr4_cells (run_segments R_segs rc_inp rc_sp rc_mb) M base n f i Ha Hi) as (_ & _ & H2).
  eapply zu_lbu; [exact F | exact E | exact D | exact Hh | |].
  - rewrite Heq. unfold mem_u16, mem_is in H2.
    pose proof (mem_is_firstn (run_segments R_segs rc_inp rc_sp rc_mb) M _ _ 1 H2 ltac:(cbn; lia)) as H1. cbn [firstn Z_to_le_bytes] in H1. exact H1.
  - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact Hk.
Qed.

Ltac tld4_op Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr4_op (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
Ltac tld4_bits Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr4_bits (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
Ltac tld4_val Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lhu_arr4_val (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
Ltac tld4_vlo Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr4_vlo _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
Ltac tld1 Ha i Hr :=
  lazymatch type of Ha with mem_arr 1 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr' (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | apply Hr; lia | ]); znorm end.
Ltac tld1m Ha i :=
  lazymatch type of Ha with mem_arr 1 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.

Ltac zlastval := lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ((_, ?x) :: _)) _ _) _ => x end.
Ltac kfin := try zreg; try assumption; try (split_conj; first [assumption | eassumption | zreg]); try lia.

Lemma shiftl_2 : forall x, Z.shiftl x (2 mod 64) = 4 * x.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ (2 mod 64)) with 4. lia. Qed.
Lemma shiftl_1_pow : forall k, 0 <= k -> Z.shiftl 1 k = 2 ^ k.
Proof. intros. rewrite Z.shiftl_1_l. reflexivity. Qed.


Lemma mod2_4k : forall k, (4 * k) mod 2 = 0.
Proof. intros k. replace (4 * k) with ((2 * k) * 2) by lia. apply Z_mod_mult. Qed.
Lemma mod2_add : forall a b, a mod 2 = 0 -> b mod 2 = 0 -> (a + b) mod 2 = 0.
Proof. intros a b Ha Hb. rewrite Z.add_mod, Ha, Hb by lia. reflexivity. Qed.
Ltac zmod2 := first [ assumption | apply mod2_4k | apply mod2_add; zmod2 ].
Ltac zeven := zsetreg 0 ltac:(symmetry; apply (land_mask0 _ 1); [lia | change (2 ^ 1) with 2; zmod2]).

Ltac zgetl0 := repeat match goal with H : zget_l ?R [] ?k = ?v |- _ => cbv [zget_l alookup] in H end.
Ltac zpc_norm :=
  lazymatch goal with |- realizes ?s (zcfg ?s' ?pc ?R ?M ?MD) ?T =>
    let v := eval vm_compute in pc in change (realizes s (zcfg s' v R M MD) T) end.

Lemma fast_head {RCa1 : RunCtx}  : forall cx R l M MD T (ci hold bits v4 : Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> zget_l R l kS1 = 14 ->
  zget_l R l kA4 = hold -> zget_l R l kA6 = f_q cx + ci -> zget_l R l kS6 = v4 -> zget_l R l kA5 = bits ->
  f_ro cx M ->
  0 <= ci -> ci + 6 <= f_n cx -> 0 <= bits -> bits <= 40 -> bits <= 8 * ci -> 0 <= hold -> hold < 2 ^ bits ->
  (forall R' (ci' hold' bits' : Z),
     f_const cx R' [] -> zget_l R' [] kA4 = hold' -> zget_l R' [] kA6 = f_q cx + ci' -> zget_l R' [] kS6 = v4 -> zget_l R' [] kA5 = bits' ->
     ci <= ci' -> ci' <= ci + 2 -> ci' <= f_n cx -> 15 <= bits' -> bits' <= 40 -> bits' <= 8 * ci' -> 0 <= hold' -> hold' < 2 ^ bits' ->
     8 * (f_n cx - ci') + bits' = 8 * (f_n cx - ci) + bits ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLOOK (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FHEAD (zupd R l) M MD) T.
Proof.
  intros cx R l M MD T ci hold bits v4 CX Hh HC Ls1 La4 La6 Ls6 La5 HL Hci1 Hci2 Hb1 Hb2 Hb3 Hh1 Hh2 K.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. open_const HC. open_ro HL. unfold f_const in K. fcx_cbn.
  clear HtL HtD Hsane Q48 Q40 Q32 Q24 Q16 Q8 Q0.
  clear Sobu Spob Spq Sobq Cw1 Cw2 Swp Swq Swob Slaob Slap Sdaob Sdap TOKL TOKD Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cwn4 Cbo1 Cbo2 Cco1 Cco2 Cco3 Cs8 Rfw
        Calu Calp Call Cald.
  zkeys. unfold L_FHEAD, L_FLOOK in *. pose proof two64_eq as TW64. pose proof m1_mod64 as Hm1.
  assert (HPb : 2 ^ bits <= 2 ^ 40) by (apply pow2_le; lia).
  zrebase.
  destruct (Z_lt_dec 14 bits) as [Hge|Hlt].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx ci hold bits) end.
    all: try zreg. all: try lia. all: split_conj; zreg.
  - zbr Rfd false.
    pose proof (Rfin (ci + 1) ltac:(lia)) as Rb1. pose proof (Rfin ci ltac:(lia)) as Rb0.
    zstep Rfd.
    zbr Rfd false.
    zbr Rfd false.
    tld1 Hin ci Rfin.
    tld1 Hin (ci + 1) Rfin.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (fin ci * 2 ^ bits) ltac:(symmetry; apply (proj1 (shl_byte _ bits Rb0 ltac:(lia)))).
    zstep Rfd.
    zsetreg (fin (ci + 1) * 2 ^ (bits + 8)) ltac:(symmetry; apply (proj1 (shl_byte _ (bits + 8) Rb1 ltac:(lia)))).
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (bits + 16) ltac:(symmetry; apply lor_16; lia).
    pose proof (hold_pull2 hold bits (fin ci) (fin (ci + 1)) ltac:(lia) ltac:(lia) Rb0 Rb1) as HP2.
    assert (HPb2 : 2 ^ (bits + 16) <= 2 ^ 40) by (apply pow2_le; lia).
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
      eapply (K Rx (ci + 2) (fin ci * 2 ^ bits + hold + fin (ci + 1) * 2 ^ (bits + 8)) (bits + 16)) end.
    all: try zreg. all: try lia. all: split_conj; zreg.
Qed.

Lemma fast_declen {RCa1 : RunCtx}  : forall cx R l M MD T (hold bits v3 v4 : Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> zget_l R l kA4 = hold -> zget_l R l kA6 = v3 -> zget_l R l kS6 = v4 -> zget_l R l kA5 = bits ->
  f_ro cx M ->
  15 <= bits -> bits <= 40 -> 0 <= hold -> hold < 2 ^ bits ->
  (forall R' (k hold' bits' : Z),
     f_const cx R' [] -> zget_l R' [] kA4 = hold' -> zget_l R' [] kA6 = v3 -> zget_l R' [] kS6 = v4 -> zget_l R' [] kA5 = bits' ->
     zget_l R' [] kT0 = f_la cx + 4 * k -> 0 <= k -> k < f_na cx ->
     0 <= bits' -> 1 <= bits - bits' -> bits - bits' <= 15 -> 0 <= hold' -> hold' < 2 ^ bits' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLIT (zupd R' []) M MD) T) ->
  (forall R' (k hold' bits' : Z),
     f_const cx R' [] -> zget_l R' [] kA4 = hold' -> zget_l R' [] kA6 = v3 -> zget_l R' [] kS6 = v4 -> zget_l R' [] kA5 = bits' ->
     zget_l R' [] kT0 = f_la cx + 4 * k -> zget_l R' [] kA3 = code_op (f_rdL cx k) -> 0 <= k -> k < f_na cx ->
     16 <= code_op (f_rdL cx k) -> code_op (f_rdL cx k) <= 21 -> 3 <= code_val (f_rdL cx k) ->
     code_val (f_rdL cx k) + 2 ^ (code_op (f_rdL cx k) - 16) - 1 <= 258 ->
     0 <= bits' -> 1 <= bits - bits' -> bits - bits' <= 15 -> 0 <= hold' -> hold' < 2 ^ bits' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLENB (zupd R' []) M MD) T) ->
  (forall R' (op hold' bits' : Z),
     f_const cx R' [] -> zget_l R' [] kA4 = hold' -> zget_l R' [] kA6 = v3 -> zget_l R' [] kS6 = v4 -> zget_l R' [] kA5 = bits' ->
     zget_l R' [] kA3 = op -> 0 <= op -> op < 256 ->
     0 <= bits' -> 1 <= bits - bits' -> bits - bits' <= 15 -> 0 <= hold' -> hold' < 2 ^ bits' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FEOB (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLOOK (zupd R l) M MD) T.
Proof.
  intros cx R l M MD T hold bits v3 v4 CX Hh HC La4 La6 Ls6 La5 HL Hb1 Hb2 Hh1 Hh2 KLIT KLENB KEOB.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. open_const HC. open_ro HL. unfold f_const in KLIT, KLENB, KEOB. fcx_cbn.
  clear Hin HtD Hsane Q48 Q40 Q32 Q24 Q16 Q8 Q0.
  clear Sobu Spob Spq Sobq Cw1 Cw2 Swp Swq Swob Slaob Slap Sdaob Sdap TOKD Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cwn4 Cbo1 Cbo2 Cco1 Cco2 Cco3 Cs8 Rfw Rfin
        Calu Calp Cald.
  zkeys. unfold L_FLOOK, L_FLIT, L_FLENB, L_FEOB in *. pose proof two64_eq as TW64. pose proof m1_mod64 as Hm1.
  pose proof (lnot_val_mod' la ltac:(lia)) as Hs8.
  assert (HPb : 2 ^ bits <= 2 ^ 40) by (apply pow2_le; lia). pose proof (pow2_15 lb ltac:(lia)) as HPl.
  zrebase.
  zstep Rfd.
  let x := zlastval in set (i1 := x) in *;
  pose proof (land_mask_range' hold lb ltac:(lia)) as Ri1; fold i1 in Ri1.
  clearbody i1.
  pose proof (tab_root_entry LENS rdL lb na i1 TOKL Ri1) as (Hbits1 & _ & Hext & CASES).
  pose proof (code_op_range (rdL i1)) as Rop1. pose proof (code_val_range (rdL i1)) as Rval1.
  zstep Rfd.
  zsetreg (4 * i1) ltac:(symmetry; apply shiftl_2).
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd. zbool.
  zstep Rfd. zlit.
  zbr Rfd false.
  zstep Rfd. zeven.
  zbr Rfd false.
  zbr Rfd false.
  tld4_bits HtL i1.
  zbr Rfd false.
  tld4_op HtL i1.
  zstep Rfd.
  zsetreg (hold / 2 ^ code_bits (rdL i1)) ltac:(symmetry; apply (srl_hold hold bits); lia).
  pose proof (hold_shr_bound hold bits (code_bits (rdL i1)) ltac:(lia) ltac:(lia)) as Hh'.
  tstep1 Rfd.
  Local Ltac fin := try zreg; try lia; try (split_conj; zreg).
  destruct CASES as [[NL TM] | (L1 & L2 & L3 & L4 & SUB)].
  -
    apply term_ok_LENS in TM as (Hb1' & CL).
    destruct CL as [(Hop0 & Hv) | [(Hop16 & Hv3 & Hv258 & Hop21) | (H64 & H16)]].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (KLIT Rx i1 (hold / 2 ^ code_bits (rdL i1)) (bits - code_bits (rdL i1))) end.
      all: fin.
    + pose proof (op_base_tests (code_op (rdL i1)) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
      rewrite shiftl_1_pow in Hv258 by lia.
      zbr Rfd false.
      zstep Rfd.
      zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (KLENB Rx i1 (hold / 2 ^ code_bits (rdL i1)) (bits - code_bits (rdL i1))) end.
      all: fin.
    + assert (Tnz : code_op (rdL i1) <> 0) by (intros E; rewrite E in H64; apply H64; reflexivity).
      pose proof (land_range_r (code_op (rdL i1)) 64 ltac:(lia)) as R64.
      zbr Rfd false.
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd.
      zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (KEOB Rx (code_op (rdL i1)) (hold / 2 ^ code_bits (rdL i1)) (bits - code_bits (rdL i1))) end.
      all: fin.
  -
    pose proof (op_link_tests (code_op (rdL i1)) ltac:(lia)) as (T16 & T64 & T240 & Tnz).
    pose proof (pow2_15 (code_op (rdL i1)) ltac:(lia)) as HPo.
    zbr Rfd false.
    zstep Rfd.
    zbr Rfd false.
    zstep Rfd.
    zbr Rfd false.
    tld4_val HtL i1.
    zstep Rfd.
    zsetreg (4 * code_val (rdL i1)) ltac:(symmetry; apply shiftl_2).
    zbr Rfd false.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (2 ^ code_op (rdL i1) - 1) ltac:(symmetry; apply mask_not_sllw; lia).
    zstep Rfd.
    let x := zlastval in set (j := x) in *;
    pose proof (land_mask_range' (hold / 2 ^ code_bits (rdL i1)) (code_op (rdL i1)) ltac:(lia)) as Rj; fold j in Rj.
    clearbody j.
    destruct (SUB j Rj) as [NL2 TM2]. apply term_ok_LENS in TM2 as (Hbits2 & CL2).
    pose proof (code_op_range (rdL (code_val (rdL i1) + j))) as Rop2.
    zstep Rfd.
    zsetreg (4 * j) ltac:(symmetry; apply shiftl_2).
    zstep Rfd. znot.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd. zeven.
    zbr Rfd true.
    tld4_bits HtL (code_val (rdL i1) + j).
    zbr Rfd false.
    tld4_op HtL (code_val (rdL i1) + j).
    zstep Rfd.
    zsetreg (hold / 2 ^ code_bits (rdL i1) / 2 ^ code_bits (rdL (code_val (rdL i1) + j)))
      ltac:(symmetry; apply (srl_hold _ (bits - code_bits (rdL i1))); lia).
    pose proof (hold_shr_bound (hold / 2 ^ code_bits (rdL i1)) (bits - code_bits (rdL i1))
                  (code_bits (rdL (code_val (rdL i1) + j))) ltac:(lia) ltac:(lia)) as Hh''.
    tstep1 Rfd.
    destruct CL2 as [(Hop0 & Hv) | [(Hop16 & Hv3 & Hv258 & Hop21) | (H64 & H16)]].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (KLIT Rx (code_val (rdL i1) + j) (hold / 2 ^ code_bits (rdL i1) / 2 ^ code_bits (rdL (code_val (rdL i1) + j)))
                  (bits - code_bits (rdL i1) - code_bits (rdL (code_val (rdL i1) + j)))) end.
      all: fin.
    + pose proof (op_base_tests (code_op (rdL (code_val (rdL i1) + j))) ltac:(lia)) as (U16 & U64 & U32 & U240 & U15 & Unz).
      rewrite shiftl_1_pow in Hv258 by lia.
      zbr Rfd false.
      zstep Rfd.
      zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (KLENB Rx (code_val (rdL i1) + j) (hold / 2 ^ code_bits (rdL i1) / 2 ^ code_bits (rdL (code_val (rdL i1) + j)))
                  (bits - code_bits (rdL i1) - code_bits (rdL (code_val (rdL i1) + j)))) end.
      all: fin.
    + assert (Unz : code_op (rdL (code_val (rdL i1) + j)) <> 0) by (intros E; rewrite E in H64; apply H64; reflexivity).
      pose proof (land_range_r (code_op (rdL (code_val (rdL i1) + j))) 64 ltac:(lia)) as R64.
      zbr Rfd false.
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd.
      zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (KEOB Rx (code_op (rdL (code_val (rdL i1) + j))) (hold / 2 ^ code_bits (rdL i1) / 2 ^ code_bits (rdL (code_val (rdL i1) + j)))
                  (bits - code_bits (rdL i1) - code_bits (rdL (code_val (rdL i1) + j)))) end.
      all: fin.
Qed.

Lemma fast_lit {RCa1 : RunCtx}  : forall cx M1 R l M MD T (k co v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> zget_l R l kA4 = v1 -> zget_l R l kA6 = v3 -> zget_l R l kS6 = f_ob cx + co -> zget_l R l kA5 = v7 ->
  zget_l R l kT0 = f_la cx + 4 * k -> 0 <= k -> k < f_na cx ->
  0 <= co -> co < f_osz cx ->
  f_ro cx M -> f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R' M' (fo' : Z -> Z),
     f_const cx R' [] -> zget_l R' [] kA4 = v1 -> zget_l R' [] kA6 = v3 -> zget_l R' [] kS6 = f_ob cx + co + 1 -> zget_l R' [] kA5 = v7 ->
     f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLATCH (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLIT (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T k co v1 v3 v7 fo CX Hh HC La4 La6 Ls6 La5 Lt0 Hk1 Hk2 Hco1 Hco2 HRO HL Rfo HAG K.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. open_const HC. open_ro HRO. open_live HL. unfold f_const, f_live, FPW in K |- *. fcx_cbn.
  clear Hin HtD Hsane Q48 Q40 Q32 Q24 Q16 Q8 Q0.
  clear Spq Swp Swq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cwn1 Cwn2 Cbo1 Cbo2 Cco1 Cco2 Cco3 Cs8 Rfw Rfin Calu Calp Call Cald.
  zkeys. unfold L_FLIT, L_FLATCH in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  pose proof (mod_256_range (code_val (rdL k))) as Rv.
  zrebase.
  zstep Rfd.
  zbr Rfd false.
  tld4_vlo HtL k.
  clear HtL.
  tstore_arr Rfd HOB co.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
    eapply (K Rx Mx (zfupd fo co (code_val (rdL k) mod 256))) end.
  all: try zreg. all: try assumption. all: try (split_conj; first [assumption | zreg]).
  apply (zfupd_byte fo co _ 0 osz Rfo Rv).
Qed.

Lemma fast_lenb {RCa1 : RunCtx}  : forall cx R l M MD T (k ci hold bits v4 : Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> zget_l R l kA4 = hold -> zget_l R l kA6 = f_q cx + ci -> zget_l R l kS6 = v4 -> zget_l R l kA5 = bits ->
  zget_l R l kT0 = f_la cx + 4 * k -> zget_l R l kA3 = code_op (f_rdL cx k) -> 0 <= k -> k < f_na cx ->
  16 <= code_op (f_rdL cx k) -> code_op (f_rdL cx k) <= 21 -> 3 <= code_val (f_rdL cx k) ->
  code_val (f_rdL cx k) + 2 ^ (code_op (f_rdL cx k) - 16) - 1 <= 258 ->
  f_ro cx M ->
  0 <= ci -> ci <= f_n cx -> 0 <= bits -> bits <= 40 -> bits <= 8 * ci -> 0 <= hold -> hold < 2 ^ bits ->
  33 <= 8 * (f_n cx - ci) + bits ->
  (forall R' (ci' hold' bits' len : Z),
     f_const cx R' [] -> zget_l R' [] kA4 = hold' -> zget_l R' [] kA6 = f_q cx + ci' -> zget_l R' [] kS6 = v4 -> zget_l R' [] kA5 = bits' ->
     zget_l R' [] kS11 = len -> 3 <= len -> len <= 258 ->
     ci <= ci' -> ci' <= ci + 3 -> ci' <= f_n cx -> 15 <= bits' -> bits' <= 40 -> bits' <= 8 * ci' -> 0 <= hold' -> hold' < 2 ^ bits' ->
     8 * (f_n cx - ci') + bits' <= 8 * (f_n cx - ci) + bits -> 28 <= 8 * (f_n cx - ci') + bits' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDLOOK (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLENB (zupd R l) M MD) T.
Proof.
  intros cx R l M MD T k ci hold bits v4 CX Hh HC La4 La6 Ls6 La5 Lt0 La3 Hk1 Hk2 Hop1 Hop2 Hv1 Hv2 HL
         Hci1 Hci2 Hb1 Hb2 Hb3 Hh1 Hh2 HA K.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. open_const HC. open_ro HL. unfold f_const in K. fcx_cbn.
  clear HtD Hsane Q48 Q40 Q32 Q24 Q16 Q8 Q0.
  clear Sobu Spob Spq Sobq Cw1 Cw2 Swp Swq Swob Slaob Slap Sdaob Sdap TOKL TOKD Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cwn4 Cbo1 Cbo2 Cco1 Cco2 Cco3 Cs8 Rfw
        Calu Calp Call Cald.
  zkeys. unfold L_FLENB, L_FDLOOK in *. pose proof two64_eq as TW64. pose proof m1_mod64 as Hm1.
  assert (HPb : 2 ^ bits <= 2 ^ 40) by (apply pow2_le; lia).
  set (op := code_op (rdL k)) in *.
  pose proof (op_base_tests op ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
  replace (op - 16) with (op + -16) in Hv2 by lia. replace (op - 16) with (op + -16) in T15 by lia.
  pose proof (pow2_15 (op + -16) ltac:(lia)) as HPe.
  assert (J : forall RJ (cj hj bj len : Z),
    zget RJ 11 = u -> zget RJ 12 = p -> zget RJ 13 = q + n + -5 -> zget RJ 22 = ob + osz + -257 ->
    zget RJ 31 = la -> zget RJ 32 = da -> zget RJ 21 = 2 ^ lb - 1 -> zget RJ 29 = wnext ->
    zget RJ 25 = - la + -1 -> zget RJ 26 = - da + -1 -> zget RJ 27 = 1 -> zget RJ 9 = -1 -> zget RJ 19 = 2 -> zget RJ 20 = 63 -> zget RJ 18 = 31 ->
    zget RJ 3 = spi + -160 -> zget RJ 4 = vgp -> zget RJ 5 = vtp ->
    zget RJ 15 = hj -> zget RJ 17 = q + cj -> zget RJ 23 = v4 -> zget RJ 16 = bj -> zget RJ 28 = len ->
    3 <= len -> len <= 258 -> ci <= cj -> cj <= ci + 1 -> cj <= n -> 0 <= bj -> bj <= 14 -> bj <= 8 * cj -> 0 <= hj -> hj < 2 ^ bj ->
    8 * (n - cj) + bj <= 8 * (n - ci) + bits -> 28 <= 8 * (n - cj) + bj ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 103992 (zupd RJ []) M MD) T).
  { intros RJ cj hj bj len G11 G12 G13 G22 G31 G32 G21 G29 G25 G26 G27 G9 G19 G20 G18 G3 G4 G5 G15 G17 G23 G16 G28
           Hl1 Hl2 Hcj1 Hcj2 Hcj3 Hbj1 Hbj2 Hbj3 Hhj1 Hhj2 HAj1 HAj2.
    assert (HPbj : 2 ^ bj <= 2 ^ 40) by (apply pow2_le; lia).
    pose proof (Rfin (cj + 1) ltac:(lia)) as Rb1. pose proof (Rfin cj ltac:(lia)) as Rb0.
    zstep Rfd.
    zbr Rfd false.
    zbr Rfd false.
    tld1 Hin cj Rfin.
    tld1 Hin (cj + 1) Rfin.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (fin cj * 2 ^ bj) ltac:(symmetry; apply (proj1 (shl_byte _ bj Rb0 ltac:(lia)))).
    zstep Rfd.
    zsetreg (fin (cj + 1) * 2 ^ (bj + 8)) ltac:(symmetry; apply (proj1 (shl_byte _ (bj + 8) Rb1 ltac:(lia)))).
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (bj + 16) ltac:(symmetry; apply lor_16; lia).
    pose proof (hold_pull2 hj bj (fin cj) (fin (cj + 1)) ltac:(lia) ltac:(lia) Rb0 Rb1) as HP2.
    assert (HPb2 : 2 ^ (bj + 16) <= 2 ^ 40) by (apply pow2_le; lia).
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
      eapply (K Rx (cj + 2) (fin cj * 2 ^ bj + hj + fin (cj + 1) * 2 ^ (bj + 8)) (bj + 16) len) end.
    all: kfin. }
  assert (J2 : forall RJ (cj hj bj : Z),
    zget RJ 11 = u -> zget RJ 12 = p -> zget RJ 13 = q + n + -5 -> zget RJ 22 = ob + osz + -257 ->
    zget RJ 31 = la -> zget RJ 32 = da -> zget RJ 21 = 2 ^ lb - 1 -> zget RJ 29 = wnext ->
    zget RJ 25 = - la + -1 -> zget RJ 26 = - da + -1 -> zget RJ 27 = 1 -> zget RJ 9 = -1 -> zget RJ 19 = 2 -> zget RJ 20 = 63 -> zget RJ 18 = 31 ->
    zget RJ 3 = spi + -160 -> zget RJ 4 = vgp -> zget RJ 5 = vtp ->
    zget RJ 15 = hj -> zget RJ 17 = q + cj -> zget RJ 23 = v4 -> zget RJ 16 = bj -> zget RJ 28 = code_val (rdL k) -> zget RJ 14 = op + -16 ->
    ci <= cj -> cj <= ci + 1 -> cj <= n -> op + -16 <= bj -> bj <= 40 -> bj <= 8 * cj -> 0 <= hj -> hj < 2 ^ bj ->
    8 * (n - cj) + bj = 8 * (n - ci) + bits ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 103948 (zupd RJ []) M MD) T).
  { intros RJ cj hj bj G11 G12 G13 G22 G31 G32 G21 G29 G25 G26 G27 G9 G19 G20 G18 G3 G4 G5 G15 G17 G23 G16 G28 G14
           Hcj1 Hcj2 Hcj3 Hbj1 Hbj2 Hbj3 Hhj1 Hhj2 HAj.
    assert (HPbj : 2 ^ bj <= 2 ^ 40) by (apply pow2_le; lia).
    pose proof (land_mask_range' hj (op + -16) ltac:(lia)) as Rm. pose proof (land_mask_le hj (op + -16) ltac:(lia) ltac:(lia)) as Rm2.
    replace (2 ^ (op + -16) - 1) with (2 ^ (op + -16) + -1) in Rm2 by lia.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (2 ^ (op + -16) - 1) ltac:(symmetry; apply mask_not_sllw; lia).
    zstep Rfd.
    zstep Rfd.
    zsetreg (hj / 2 ^ (op + -16)) ltac:(symmetry; apply (srl_hold hj bj); lia).
    pose proof (hold_shr_bound hj bj (op + -16) ltac:(lia) ltac:(lia)) as Hh'.
    zstep Rfd.
    tstep1 Rfd.
    destruct (Z_lt_dec 14 (bj - (op + -16))) as [Hskip|Hpull].
    - zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (K Rx cj (hj / 2 ^ (op + -16)) (bj - (op + -16)) (Z.land hj (2 ^ (op + -16) + -1) + code_val (rdL k))) end.
      all: kfin.
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (J Rx cj (hj / 2 ^ (op + -16)) (bj - (op + -16)) (Z.land hj (2 ^ (op + -16) + -1) + code_val (rdL k))) end.
      all: kfin. }
  zrebase.
  tld4_val HtL k.
  zstep Rfd.
  zsetreg (op + -16) ltac:(symmetry; exact T15).
  destruct (Z.eq_dec (op + -16) 0) as [E0|NE0].
  - zbr Rfd true.
    zstep Rfd.
    destruct (Z_lt_dec 14 bits) as [Hskip|Hpull].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx ci hold bits (code_val (rdL k))) end. all: kfin.
    + zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J Rx ci hold bits (code_val (rdL k))) end. all: kfin.
  - zbr Rfd false.
    destruct (Z_lt_dec bits (op + -16)) as [Hlt|Hge].
    + zbr Rfd false.
      pose proof (Rfin ci ltac:(lia)) as Rb0.
      zstep Rfd.
      zbr Rfd false.
      tld1 Hin ci Rfin.
      zstep Rfd.
      zstep Rfd.
      zsetreg (fin ci * 2 ^ bits) ltac:(symmetry; apply (proj1 (shl_byte _ bits Rb0 ltac:(lia)))).
      zstep Rfd.
      zstep Rfd.
      pose proof (hold_pull1 hold bits (fin ci) ltac:(lia) ltac:(lia) Rb0) as HP1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (J2 Rx (ci + 1) (fin ci * 2 ^ bits + hold) (bits + 8)) end.
      all: kfin.
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J2 Rx ci hold bits) end.
      all: kfin.
Qed.
