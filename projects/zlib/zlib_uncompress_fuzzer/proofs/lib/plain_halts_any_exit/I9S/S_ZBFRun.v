(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SBase S_Entry.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Frame Hoare.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require RefMemcpyLib FuzzMem S9MemcpyBase S9Memcpy S9AdlerBase S9AdlerIface S9Adler.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require S9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZTac ZMem ZCall ZCallL ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_It3.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZStep.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZGo11 SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout.

Module S_Fast1.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Export OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.Base.
Export OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZStep OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ITac.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Ltac zmem_transport_loop_S_ZB M a bs :=
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
  zmem_transport_loop_S_ZB M a bs;
  zxfer_post a.

Ltac zlia_chk ::= zlia.

(* the text's own labels are fields of the layout text; the old names stay, for parsing only *)
Notation L_FENTRY := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IFAST (only parsing).
Notation L_FHEAD := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FHEAD (only parsing).
Notation L_FLOOK := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FLOOK (only parsing).
Notation L_FLIT := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FLIT (only parsing).
Notation L_FLATCH := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FLATCH (only parsing).
Notation L_FLENB := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FLENB (only parsing).
Notation L_FDLOOK := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FDLOOK (only parsing).
Notation L_FDISTB := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FDISTB (only parsing).
Notation L_FWIN := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWIN (only parsing).
Notation L_FDIRECT := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FDIRECT (only parsing).
Notation L_FFROMOUT := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FFROMOUT (only parsing).
Notation L_FCOPY3 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FCOPY3 (only parsing).
Notation L_FCOPY3B := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FCOPY3B (only parsing).
Notation L_FFROMWIN := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FFROMWIN (only parsing).
Notation L_FEOB := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FEOB (only parsing).
Notation L_FBADD := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FBADD (only parsing).
Notation L_FMSG := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FMSG (only parsing).
Notation L_FEXIT := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FEXIT (only parsing).
Notation L_FTOOFAR := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FTOOFAR (only parsing).
(* the places that the hand text writes as numerals or as a place plus a distance: layout fields too *)
Notation L_FLENJ := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FLENJ (only parsing).
Notation L_FLENJ2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FLENJ2 (only parsing).
Notation L_FDISTJ := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FDISTJ (only parsing).
Notation L_FWL_WR := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_WR (only parsing).
Notation L_FWL_WR_X := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_WR_X (only parsing).
Notation L_FWL_W0 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_W0 (only parsing).
Notation L_FWL_W0_X := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_W0_X (only parsing).
Notation L_FWL_CT := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_CT (only parsing).
Notation L_FWL_CT_X := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_CT_X (only parsing).
Notation L_FWLOOP2_X := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWLOOP2_X (only parsing).
Notation L_FW0 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FW0 (only parsing).
Notation L_FCONTIG := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FCONTIG (only parsing).
Notation L_FWRAP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWRAP (only parsing).

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
Lemma land_255_id : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
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
  1024 + zc <= u /\ u + 208 <= 140737488355328 /\ spi + 224 <= u /\ u + -912 <= spi /\
  0 < p /\ p + 7176 <= zc /\
  1 <= q /\ 0 <= n /\ n < 67108864 /\ q + n <= zc /\
  0 < ob /\ 1 <= osz /\ osz <= 262144 /\ ob + osz <= u /\ ZSEP (ob + osz <= u + -1024 \/ u + 7 <= ob) /\
  ZSEP (p + 7176 <= ob \/ ob + osz <= p) /\ ZSEP (p + 7176 <= q \/ q + n <= p) /\ ZSEP (ob + osz <= q \/ q + n <= ob) /\
  0 <= w /\ w + wn <= zc /\
  ZSEP (p + 7176 <= w \/ w + wn <= p) /\ ZSEP (w + wn <= q \/ q + n <= w) /\ ZSEP (w + wn <= ob \/ ob + osz <= w) /\
  0 < la /\ la + 4 * na <= zc /\ 0 < da /\ da + 4 * nd <= zc /\ 0 <= na /\ 0 <= nd /\
  ZSEP (la + 4 * na <= ob \/ ob + osz <= la) /\ ZSEP (la + 4 * na <= p \/ p + 1384 <= la) /\
  ZSEP (da + 4 * nd <= ob \/ ob + osz <= da) /\ ZSEP (da + 4 * nd <= p \/ p + 1384 <= da) /\
  1 <= lb /\ lb <= 15 /\ 1 <= db /\ db <= 15 /\
  tab_ok LENS (f_rdL cx) lb na = true /\ tab_ok DISTS (f_rdD cx) db nd = true /\
  0 <= whave /\ 0 <= wnext /\ whave <= wn /\ wnext <= wn /\ wn <= 32768 /\
  0 <= bo /\ bo <= cout0 /\ 0 <= cout0 /\ cout0 <= osz /\
  ZSEP (wnext = 0 \/ s8v = w + wnext) /\
  (forall i, 0 <= i < n -> 0 <= f_fin cx i < 256) /\ (forall i, 0 <= i < wn -> 0 <= f_fw cx i < 256).

Ltac open_ok H :=
  unfold fcx_ok in H; cbv zeta in H; fcx_cbn;
  destruct H as (Cu1 & Cu2 & Cu3 & Cu4 & Cp1 & Cp2 & Cq1 & Cn1 & Cn2 & Cq2 &
                 Cob1 & Cosz1 & Cosz2 & Cob2 & Sobu & Spob & Spq & Sobq & Cw1 & Cw2 & Swp & Swq & Swob &
                 Cla1 & Cla2 & Cda1 & Cda2 & Cna & Cnd & Slaob & Slap & Sdaob & Sdap &
                 Clb1 & Clb2 & Cdb1 & Cdb2 & TOKL & TOKD &
                 Cwh1 & Cwn1 & Cwh2 & Cwn2 & Cwn3 & Cbo1 & Cbo2 & Cco1 & Cco2 & Cs8 & Rfin & Rfw).

(* THE LIST FORM OF THIS TEXT. A register fact is said through a list of the layout text: the list pairs a
   register with "value number i of the list of values that the statement binds" (the quantities text's
   `Q_arg`, read by `qargs`); the statement writes the values; this text names no register for them. *)
Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Notation qargs := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs (only parsing).
(* the values of the constant register map, in the layout list's order: value 0 = the stream's address; 1 = the
   state's address; 2 = the input's fast-loop end; 3 = the output's fast-loop end; 4 = the window; 5, 6 = the two
   tables; 7 = the address of the state's check field; 8 = the output's start; 9, 10 = the two root masks; 11 =
   the window's write address; 12, 13, 14 = the window's size, fill and write index; 15 = the entry stack
   pointer; 16, 17 = the two ABI pointers *)
Definition fcs (cx : fcx) : list Z :=
  [f_u cx; f_p cx; f_q cx + f_n cx + -5; f_ob cx + f_osz cx + -257; f_w cx; f_la cx; f_da cx; f_p cx + 7160;
   f_ob cx + f_bo cx; 2 ^ f_lb cx - 1; 2 ^ f_db cx - 1; f_s8 cx; f_wn cx; f_whave cx; f_wnext cx; f_spi cx;
   f_gp cx; f_tp cx].
(* the values of an exit place's register map: 0 to 3 as above; 4 = the entry stack pointer; 5, 6 = the two ABI
   pointers; 7 = the hold; 8 = the next input address; 9 = the next output address; 10 = the bit count *)
Definition fxv (cx : fcx) (ci co hold bits : Z) : list Z :=
  [f_u cx; f_p cx; f_q cx + f_n cx + -5; f_ob cx + f_osz cx + -257; f_spi cx; f_gp cx; f_tp cx;
   hold; f_q cx + ci; f_ob cx + co; bits].
(* OPENERS OF THE LIST FORM (they only unfold): the meaning of a layout list is unfolded in a hypothesis, in the
   goal, or in every hypothesis that holds one *)
Ltac zbf_in H :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd fcs fxv
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_const OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_exit OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_xpre
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_latch OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_exit0 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_entry
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_eob OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_head OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_look
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_lit OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_lenb OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_eobk
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_dlook OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_lenj OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_lenj2
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_distb OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_baddk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_directk
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wink OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_distj] in H.
Ltac zbf_goal :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd fcs fxv
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_const OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_exit OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_xpre
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_latch OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_exit0 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_entry
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_eob OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_head OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_look
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_lit OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_lenb OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_eobk
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_dlook OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_lenj OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_lenj2
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_distb OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_baddk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_directk
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wink OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_distj].
Ltac zbf_open :=
  repeat match goal with
         | HH : context [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds] |- _ => progress (zbf_in HH)
         end.

(* THE CONSTANT REGISTER MAP: the meaning of the layout's list at the context's values *)
Definition f_const (cx : fcx) (R : tree Z) (l : list (positive * Z)) : Prop :=
  Eval cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd fcs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_const] in
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs (fcs cx)) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_const.

Ltac open_const H :=
  unfold f_const in H; fcx_cbn;
  dand H as (Ga0 & Ga2 & Ga5 & Ga6 & Gs0 & Gs1 & Gs2 & Gs3 & Gs4 & Gs6 & Gs7 & Gs8 & Gt0 & Gt1 & Gt3 & Gt4 & Gt5 & Gt6 & Gsp & Ggp & Gtp).
Ltac close_const := unfold f_const; fcx_cbn; split_conj; zreg.

Definition f_live {RCa1 : RunCtx}  (cx : fcx) (fo : Z -> Z) (M : mem) : Prop :=
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_u cx + -1024) 1232 /\ mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_p cx) 7176 /\ mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_ob cx) (f_osz cx) /\
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_w cx) (f_wn cx) (f_fw cx) /\
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_ob cx) (f_osz cx) fo.

Ltac open_live H :=
  unfold f_live in H; fcx_cbn;
  dand H as (Wu & Wp & Wob & Hwin & HOB).
Ltac close_live := unfold f_live; fcx_cbn; split_conj; assumption.

(* (its fourth fact is the frame's one local slot: the meaning of the layout's frame list at the entry stack
   pointer; the value it binds is the window's size plus its write index) *)
Definition f_ro {RCa1 : RunCtx}  (cx : fcx) (M : mem) : Prop :=
  Eval cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width
            OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.fr_zbf_local] in
  (mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_q cx) (f_n cx) (f_fin cx) /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_la cx) (f_na cx) (f_rdL cx) /\
   mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_da cx) (f_nd cx) (f_rdD cx) /\
   OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds (run_segments R_segs rc_inp rc_sp rc_mb) (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs [f_wn cx + f_wnext cx]) M (f_spi cx) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.fr_zbf_local /\
   mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_p cx + 7160) 1).

Ltac open_ro H :=
  unfold f_ro in H; fcx_cbn;
  dand H as (Hin & HtL & HtD & Hsp0 & Hsane).

Definition FPW (cx : fcx) : list (Z * Z) := [(f_ob cx, f_osz cx)].
Definition FP1 (cx : fcx) : list (Z * Z) := [(f_ob cx, f_osz cx); (f_p cx + 8, 4); (f_u cx, 56); (f_p cx + 96, 12)].

Lemma f_ro_now {RCa1 : RunCtx}  : forall cx M1 M, fcx_ok cx -> f_ro cx M1 -> framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M -> f_ro cx M.
Proof.
  intros cx M1 M CX H [HA _].
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. unfold f_ro, FPW in *. fcx_cbn. pose proof two64_eq as TW64.
  dand H as (A1 & A2 & A3 & E1 & E2).
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
  Eval cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd fxv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_exit] in
  forall (R : tree Z) (M : mem) (ci co hold bits mode : Z) (fo : Z -> Z),
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs (fxv cx ci co hold bits)) R [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_exit ->
    0 <= ci -> ci <= f_n cx -> f_cout0 cx <= co -> co <= f_osz cx -> 0 <= bits -> bits <= 40 -> bits <= 8 * ci ->
    0 <= hold -> hold < 2 ^ bits -> fW cx ci bits co < f_W0 cx -> fW cx ci bits (f_cout0 cx) <= f_W0 cx ->
    PFOLD (mode = LEN \/ mode = TYPE \/ mode = BAD) ->
    mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_u cx + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_p cx) 7176 ->
    mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_ob cx) (f_osz cx) fo -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_p cx + 8) mode ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FP1 cx)) M ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FEXIT (zupd R []) M MD) T.

Definition KLATCH (B : Z) : Prop :=
  Eval cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_latch] in
  forall (R : tree Z) (M : mem) (ci co hold bits : Z) (fo : Z -> Z),
    f_const cx R [] ->
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs [hold; f_q cx + ci; f_ob cx + co; bits]) R [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_latch ->
    0 <= ci -> ci <= f_n cx -> f_cout0 cx <= co -> co <= f_osz cx -> 0 <= bits -> bits <= 40 -> bits <= 8 * ci ->
    0 <= hold -> hold < 2 ^ bits -> fW cx ci bits co < B -> fW cx ci bits co < f_W0 cx -> fW cx ci bits (f_cout0 cx) <= f_W0 cx ->
    f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLATCH (zupd R []) M MD) T.
End K.

(* THE FRAME's FOOTPRINT: its low end and its extent are the layout's two integers *)
Definition f_fp (cx : fcx) : list (Z * Z) :=
  Eval cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZBF_LO OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZBF_EXT] in
  [(f_spi cx + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZBF_LO, OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZBF_EXT)].

(* THE ENTRY FRAME: the meaning of the layout's frame list at the entry stack pointer: a slot holds the return
   address (the value bound) or the value that a register held at the function's entry (the start state) *)
Definition f_frame {RCa1 : RunCtx}  (cx : fcx) (Rb : tree Z) (l : list (positive * Z)) (ret : Z) (M1 : mem) : Prop :=
  Eval cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width
            OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval c_K fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.fr_zbf_entry] in
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds (run_segments R_segs rc_inp rc_sp rc_mb)
    (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval (ICX 0 0 0 0 0 0 0 0 0 0 (zget_l Rb l) 0) None ret) M1 (f_spi cx)
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.fr_zbf_entry.

Definition KRET {RCa1 : RunCtx}  (cx : fcx) (Rb : tree Z) (l : list (positive * Z)) (ret : Z) (M0 : mem) (MD : Model) (T : TSet) : Prop :=
  Eval cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZBF_EXT] in
  forall (R' : tree Z) (M' : mem) (cin' cout' hold' bits' mode' : Z) (fo' : Z -> Z),
     0 <= cin' -> cin' <= f_n cx -> f_cout0 cx <= cout' -> cout' <= f_osz cx ->
     0 <= bits' -> bits' <= 7 -> 0 <= hold' -> hold' < 2 ^ bits' -> bits' <= 8 * cin' ->
     8 * (f_n cx - cin') + bits' + (f_osz cx - cout') < f_W0 cx ->
     8 * (f_n cx - cin') + bits' + (f_osz cx - f_cout0 cx) <= f_W0 cx ->
     (mode' = LEN \/ mode' = TYPE \/ mode' = BAD) ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M' (if_fp (f_u cx) (f_p cx) (f_ob cx) (f_osz cx) (f_spi cx) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZBF_EXT) ->
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

(* A HINT LEMMA (the equation that a value replacement of the hand text proved in place: machine form = nicer
   form; a run's hint names the lemma) *)
Lemma srliw3_div8 : forall x, 0 <= x < 4294967296 -> bv_swrap 32 (Z.shiftr (x mod 4294967296) 3) = x / 8.
Proof. intros x Hx. rewrite srliw_small by lia. reflexivity. Qed.

Lemma fast_exit {RCa1 : RunCtx}  : forall cx Rb l M0 M1 MD T ret,
  fcx_ok cx -> m_halted MD = None -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  rholds (qargs [f_spi cx; f_gp cx; f_tp cx]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_exit0 ->
  f_frame cx Rb l ret M1 ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M1 (f_fp cx) ->
  KRET cx Rb l ret M0 MD T ->
  KEXIT cx M1 MD T.
Proof.
  intros cx Rb l M0 M1 MD T ret CX Hh Hret1 Hret2 EV FR PRO K.
  intros Rg M ci co hold bits mode fo XV
         Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hb3 Hh1 Hh2 HW HWI Hmode Wu Wp HOB Rfo Hm8 HAG. zbf_open. dand EV as (Esp & Egp & Etp). dand XV as (La0 & La2 & La5 & La6 & Lsp & Lgp & Ltp & La1 & La3 & La4 & La7).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. unfold KRET, f_frame, fW, FP1, f_fp in *. fcx_cbn.
  clear Spq Sobq Cw1 Cw2 Swp Swq Swob Cla1 Cla2 Cda1 Cda2 Cna Cnd Slaob Slap Sdaob Sdap Clb1 Clb2 Cdb1 Cdb2 TOKL TOKD
        Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cs8 Rfin Rfw.
  cbv zeta in FR. destr_conj FR.
  zkeys. unfold L_FEXIT in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz); (p + 8, 4); (u, 56); (p + 96, 12)] ltac:(ranges_ok_tac)) as HST.
  pose proof (Z.div_mod bits 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound bits 8 ltac:(lia)) as Hr8.
  assert (HPb : 2 ^ bits <= 2 ^ 40) by (apply pow2_le; lia).
  pose proof (land_mask_range hold (bits mod 8) ltac:(lia)) as Hmask. replace (2 ^ (bits mod 8) - 1) with (2 ^ (bits mod 8) + -1) in Hmask by lia.
  pose proof (pow2_15 (bits mod 8) ltac:(lia)) as Hp8.
  zrebase.
  (* every fact of the entry frame is carried to the memory in hand, before the run (the hand text derives them
     between two stretches) *)
  repeat match goal with
         | SF : mem_u64 _ M1 _ _ |- _ => let GF := fresh "GF" in zderiveL HAG SF GF; clear SF
         end.
  (* ONE RUN to the return, with THREE VALUE HINTS (the bit count's whole bytes; its bits below a byte; the
     mask of those bits) *)
  zuntil_h Rfd (first [ zhint srliw3_div8 | zhint land_7_mod | zhint mask_not_sllw ])
    (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ =>
       eapply (K RX MX (ci - bits / 8) co (Z.land hold (2 ^ (bits mod 8) + -1)) (bits mod 8) mode fo) end).
  all: try lia.
  - exact Hmode.
  -
    eapply mpostL_trans.
    + eapply (framed_mpostL_weaken (run_segments R_segs rc_inp rc_sp rc_mb) M0 M1); [| exact PRO]. unfold if_fp. ranges_within_tac.
    + eapply (framed_mpostL_weaken (run_segments R_segs rc_inp rc_sp rc_mb) M1); [| exact HAG]. unfold if_fp. ranges_within_tac.
  - eapply mem_u64_retype; [zfact_exact | lia].
  - eapply mem_u32_retype; [zfact_exact | lia].
  - zfact_exact.
  - eapply mem_u32_retype; [zfact_exact | lia].
  - zfact_exact.
  - zfact_exact.
  - assumption.
  - assumption.
  - exact Rfo.
  - unfold kept_eq. zkeys. split_conj; zreg.
Qed.


Definition f_emem {RCa1 : RunCtx}  (cx : fcx) (cin cout hold bits : Z) (fo : Z -> Z) (M : mem) : Prop :=
  let u := f_u cx in let p := f_p cx in
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u) (f_q cx + cin) /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 8) (f_n cx - cin) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 24) (f_ob cx + cout) /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 32) (f_osz cx - cout) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 56) p /\
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) (f_wn cx) /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 76) (f_whave cx) /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 80) (f_wnext cx) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) (f_w cx) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 96) hold /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 104) bits /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 120) (f_la cx) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 128) (f_da cx) /\
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 136) (f_lb cx) /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 140) (f_db cx) /\
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 7160) 1 /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 8) LEN /\
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_q cx) (f_n cx) (f_fin cx) /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_la cx) (f_na cx) (f_rdL cx) /\
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_da cx) (f_nd cx) (f_rdD cx) /\ mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_w cx) (f_wn cx) (f_fw cx) /\
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_ob cx) (f_osz cx) fo.

Lemma f_emem_magreeL {RCa1 : RunCtx}  : forall cx cin cout hold bits fo M0 M,
  fcx_ok cx -> magreeL M0 M (f_fp cx) -> f_emem cx cin cout hold bits fo M0 -> f_emem cx cin cout hold bits fo M.
Proof.
  intros cx cin cout hold bits fo M0 M CX HA H.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. unfold f_emem, f_fp in *. fcx_cbn. pose proof two64_eq as TW64.
  dand H as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & A1 & A2 & A3 & A4 & A5).
  pose proof (mem_arr_bounds _ _ _ _ _ _ A4) as Bw. pose proof (mem_arr_bounds _ _ _ _ _ _ A5) as Bob.
  split_conj;
  first [ eapply mem_u64_magreeL; [exact HA | eassumption | lia | lia | cbn [disj_all]; split; [zlia | exact I]]
        | eapply mem_u32_magreeL; [exact HA | eassumption | lia | lia | cbn [disj_all]; split; [zlia | exact I]]
        | eapply mem_arr_magreeL; [exact HA | eassumption | cbn [disj_all]; split; [zlia | exact I]] ].
Qed.

Ltac open_emem H :=
  unfold f_emem in H; cbv zeta in H; fcx_cbn;
  dand H as (E8 & E16 & E32 & E40 & E64 & P60 & P64 & P68 & P72 & P80 & P88 & P104 & P112 & P120 & P124 & Hsane & Hm8 &
                 Hin & HtL & HtD & Hwin & HOB).

Definition s8_of (w wnext : Z) : Z := Z.shiftr (Z.shiftl (wnext + -1) 32 mod 18446744073709551616) 32 + w + 1.
Lemma s8_of_eq : forall w wnext, 0 < wnext < 4294967296 -> s8_of w wnext = w + wnext.
Proof. intros w wnext H. unfold s8_of. rewrite zext32_shift by lia. lia. Qed.

Lemma fast_entry {RCa1 : RunCtx}  : forall cx Rb l M MD T (cin cout hold bits out ret : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  rholds (qargs [f_u cx; out; f_spi cx; ret; f_gp cx; f_tp cx]) Rb l
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_entry ->
  f_cout0 cx = cout -> f_bo cx = cout - (out - (f_osz cx - cout)) -> f_osz cx - cout <= out -> out <= f_osz cx ->
  f_s8 cx = s8_of (f_w cx) (f_wnext cx) ->
  0 <= cin -> cin + 6 <= f_n cx -> 0 <= cout -> cout + 258 <= f_osz cx ->
  0 <= bits -> bits <= 40 -> 0 <= hold -> hold < 2 ^ bits ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_u cx + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_p cx) 7176 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_ob cx) (f_osz cx) ->
  f_emem cx cin cout hold bits fo M ->
  (forall R M1,
     f_const cx R [] ->
     rholds (qargs [hold; f_q cx + cin; f_ob cx + cout; bits]) R [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_head ->
     f_live cx fo M1 -> f_ro cx M1 -> f_frame cx Rb l ret M1 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (f_p cx + 8) LEN ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M1 (f_fp cx) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FHEAD (zupd R []) M1 MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FENTRY (zupd Rb l) M MD) T.
Proof.
  intros cx Rb l M MD T cin cout hold bits out ret fo CX Hh EV
         Eco0 Ebo Hout1 Hout2 Es8 Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hh1 Hh2 Wu Wp Wob EM K. zbf_open. dand EV as (La0 & La1 & Lsp & Lra & Lgp & Ltp).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. open_ok CX. unfold f_frame, f_live, f_ro, f_const in K. fcx_cbn.
  clear Spq Sobq Swp Swq Swob Slaob Slap Sdaob Sdap TOKL TOKD Rfin Rfw.
  (* the continuation's frame fact, kept as a test of a memory: the first run stops where it holds *)
  lazymatch type of CX' with fcx_ok ?CC =>
    assert (FRI : forall MC : mem, f_frame CC Rb l ret MC -> True) by (intros; exact I) end.
  unfold f_frame in FRI; cbv zeta in FRI; cbn [f_spi] in FRI.
  zkeys. unfold L_FENTRY, L_FHEAD in *. pose proof two64_eq as TW64.
  assert (HPb : 2 ^ bits <= 2 ^ 40) by (apply pow2_le; lia).
  pose proof (pow2_15 lb ltac:(lia)) as HPl. pose proof (pow2_15 db ltac:(lia)) as HPd.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (f_fp (FCX u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw)) ltac:(unfold f_fp; cbn [f_spi]; ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (f_fp (FCX u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw))) M) by (apply mpostL_refl). unfold f_fp in *. fcx_cbn.
  (* the entry values that the continuation's frame fact names get names of their own (the hand text names them one by one,
     by their numbers) *)
  repeat match type of K with
         | context [zget_l Rb l ?KK] =>
             let ve := fresh "ve" in let Eve := fresh "Eve" in let Gve := fresh "Gve" in
             remember (zget_l Rb l KK) as ve eqn:Eve;
             assert (Gve : zget_l Rb l KK = ve) by (symmetry; exact Eve)
         end.
  zrebase.
  (* ONE RUN until the frame holds every entry value that the continuation's frame fact names *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ _ ?MC _) _ =>
    assert_succeeds (pose proof (FRI MC ltac:(split_conj; zfact_exact)));
    apply (f_emem_magreeL _ cin cout hold bits fo M MC CX' (proj1 HAG)) in EM end).
  clear CX' FRI. open_emem EM.
  (* ONE RUN to the loop's head, (five value equations stand before it) *)
  pose proof (zext32_shift (n - cin + -5) ltac:(zlia)) as EZ1. pose proof (zext32_shift (out - (osz - cout)) ltac:(zlia)) as EZ2. pose proof (zext32_shift (osz - cout + -257) ltac:(zlia)) as EZ3. pose proof (mask_not_sllw lb ltac:(lia)) as EM1. pose proof (mask_not_sllw db ltac:(lia)) as EM2. zuntil Rfd
    (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ => eapply (K RX MX) end).
  - split_conj; try zreg. rewrite Es8. unfold s8_of. zreg.
  - split_conj; zreg.
  - split_conj; assumption.
  - split_conj; try assumption. eapply mem_u64_retype; [zfact_exact | lia].
  - split_conj; zfact_exact.
  - exact Hm8.
  - exact HAG.
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
  Eval cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd fxv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_xpre] in
  0 <= ci /\ ci <= f_n cx /\ f_cout0 cx <= co /\ co <= f_osz cx /\ 0 <= bits /\ bits <= 40 /\ bits <= 8 * ci /\
  0 <= hold /\ hold < 2 ^ bits /\ fW cx ci bits co < f_W0 cx /\ fW cx ci bits (f_cout0 cx) <= f_W0 cx /\
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_u cx + -1024) 1232 /\ mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_p cx) 7176 /\
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_ob cx) (f_osz cx) fo /\ (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) /\
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M /\
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs (fxv cx ci co hold bits)) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_xpre.

(* (the register facts stand last in the meaning of the layout's list; the opener names them last) *)
Ltac open_xpre H :=
  unfold XPRE, fW, FPW in H; fcx_cbn;
  dand H as (Hci1 & Hci2 & Hco1 & Hco2 & Hb1 & Hb2 & Hb3 & Hh1 & Hh2 & HW & HWI & Wu & Wp & HOB & Rfo & HAG &
                 La0 & La2 & La5 & La6 & Lsp & Lgp & Ltp & La1 & La3 & La4 & La7).

Definition KERR {RCa1 : RunCtx}  (cx : fcx) (M1 : mem) (MD : Model) (T : TSet) (pc : Z) : Prop :=
  forall R l M ci co hold bits fo, XPRE cx M1 R l M ci co hold bits fo -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd R l) M MD) T.

Lemma fast_msg {RCa1 : RunCtx}  : forall cx M1 MD T, fcx_ok cx -> m_halted MD = None -> KEXIT cx M1 MD T -> KERR cx M1 MD T L_FMSG.
Proof.
  intros cx M1 MD T CX Hh HEX Rg l M ci co hold bits fo XP.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. open_xpre XP. unfold KEXIT, FP1, fW in HEX. fcx_cbn.
  clear Spq Sobq Cw1 Cw2 Swp Swq Swob Cla1 Cla2 Cda1 Cda2 Cna Cnd Slaob Slap Sdaob Sdap Clb1 Clb2 Cdb1 Cdb2 TOKL TOKD
        Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cs8 Rfin Rfw.
  zkeys. unfold L_FMSG, L_FEXIT in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz); (p + 8, 4); (u, 56); (p + 96, 12)] ltac:(ranges_ok_tac)) as HST.
  apply (framed_mpostL_weaken (run_segments R_segs rc_inp rc_sp rc_mb) M1 M [(ob, osz)] [(ob, osz); (p + 8, 4); (u, 56); (p + 96, 12)] ltac:(ranges_within_tac)) in HAG.
  zrebase.
  (* ONE RUN to the exit place *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ => eapply (HEX RX MX ci co hold bits BAD fo) end).
  all: try zreg. all: try (split_conj; zreg). all: try assumption. all: try zfact_exact. all: unfold PFOLD; (first [solve [zkeep_section; tauto] | tauto]).
Qed.

Lemma fast_badd {RCa1 : RunCtx}  : forall cx M1 MD T, fcx_ok cx -> m_halted MD = None -> KEXIT cx M1 MD T -> KERR cx M1 MD T L_FBADD.
Proof.
  intros cx M1 MD T CX Hh HEX Rg l M ci co hold bits fo XP.
  pose proof (fast_msg cx M1 MD T CX Hh HEX) as KM. unfold KERR in KM.
  pose proof XP as XP'. destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_xpre XP. zkeys. unfold L_FBADD, L_FMSG in *.
  (* ONE RUN to the message place *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RX ?LX) ?MX _) _ => apply (KM RX LX MX ci co hold bits fo) end).
  unfold XPRE. fcx_cbn. split_conj; try zreg; try assumption.
Qed.

Lemma fast_toofar {RCa1 : RunCtx}  : forall cx M1 MD T, fcx_ok cx -> m_halted MD = None -> KEXIT cx M1 MD T -> KERR cx M1 MD T L_FTOOFAR.
Proof.
  intros cx M1 MD T CX Hh HEX Rg l M ci co hold bits fo XP.
  pose proof (fast_msg cx M1 MD T CX Hh HEX) as KM. unfold KERR in KM.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_xpre XP. zkeys. unfold L_FTOOFAR, L_FMSG in *.
  (* ONE RUN to the message place *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RX ?LX) ?MX _) _ => apply (KM RX LX MX ci co hold bits fo) end).
  unfold XPRE. fcx_cbn. split_conj; try zreg; try assumption.
Qed.

Lemma fast_eob {RCa1 : RunCtx}  : forall cx M1 MD T, fcx_ok cx -> m_halted MD = None -> KEXIT cx M1 MD T ->
  forall R l M ci co hold bits fo op,
    XPRE cx M1 R l M ci co hold bits fo -> rholds (qargs [op]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_eob -> 0 <= op < 256 ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FEOB (zupd R l) M MD) T.
Proof.
  intros cx M1 MD T CX Hh HEX Rg l M ci co hold bits fo op XP Ls9 Hop. zbf_open.
  pose proof (fast_msg cx M1 MD T CX Hh HEX) as KM. unfold KERR in KM.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. open_ok CX. open_xpre XP. unfold KEXIT, FP1, fW in HEX. fcx_cbn.
  clear Spq Sobq Cw1 Cw2 Swp Swq Swob Cla1 Cla2 Cda1 Cda2 Cna Cnd Slaob Slap Sdaob Sdap Clb1 Clb2 Cdb1 Cdb2 TOKL TOKD
        Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cs8 Rfin Rfw.
  zkeys. unfold L_FEOB, L_FMSG, L_FEXIT in *. pose proof two64_eq as TW64.
  pose proof (land_range_r op 32 ltac:(lia)) as H32.
  zrebase.
  (* ONE RUN to the test of the code's kind *)
  zto_branch Rfd.
  destruct (Z.eq_dec (Z.land op 32) 0) as [Z32|NZ32].
  - (* ONE RUN to the message place *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RX ?LX) ?MX _) _ => apply (KM RX LX MX ci co hold bits fo) end).
    unfold XPRE. fcx_cbn. split_conj; try zreg; try assumption.
  - (* the two facts that the run's store needs stand before the run (the hand text states them beside the store) *)
    pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz); (p + 8, 4); (u, 56); (p + 96, 12)] ltac:(ranges_ok_tac)) as HST.
    apply (framed_mpostL_weaken (run_segments R_segs rc_inp rc_sp rc_mb) M1 M [(ob, osz)] [(ob, osz); (p + 8, 4); (u, 56); (p + 96, 12)] ltac:(ranges_within_tac)) in HAG.
    (* ONE RUN to the exit place *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ => eapply (HEX RX MX ci co hold bits TYPE fo) end).
    all: try zreg. all: try (split_conj; zreg). all: try assumption. all: try zfact_exact. all: unfold PFOLD; (first [solve [zkeep_section; tauto] | tauto]).
Qed.
End S_Fast1.

Module S_Fast2.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import S_Fast1.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* A HINT LEMMA (the equation half of the hand text's `shl_byte`; a run's hint names it) *)
Lemma shl_byte_eq : forall b s, 0 <= b < 256 -> 0 <= s <= 63 -> Z.shiftl b (s mod 64) = b * 2 ^ s.
Proof. intros b s Hb Hs. exact (proj1 (shl_byte b s Hb Hs)). Qed.

Lemma fast_head {RCa1 : RunCtx}  : forall cx R l M MD T (ci hold bits v4 : Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> rholds (qargs [hold; f_q cx + ci; v4; bits]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_head ->
  f_ro cx M ->
  0 <= ci -> ci + 6 <= f_n cx -> 0 <= bits -> bits <= 40 -> bits <= 8 * ci -> 0 <= hold -> hold < 2 ^ bits ->
  (forall R' (ci' hold' bits' : Z),
     f_const cx R' [] -> rholds (qargs [hold'; f_q cx + ci'; v4; bits']) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_look ->
     ci <= ci' -> ci' <= ci + 2 -> ci' <= f_n cx -> 15 <= bits' -> bits' <= 40 -> bits' <= 8 * ci' -> 0 <= hold' -> hold' < 2 ^ bits' ->
     8 * (f_n cx - ci') + bits' = 8 * (f_n cx - ci) + bits ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLOOK (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FHEAD (zupd R l) M MD) T.
Proof.
  intros cx Rg l M MD T ci hold bits v4 CX Hh HC HV HL Hci1 Hci2 Hb1 Hb2 Hb3 Hh1 Hh2 K. zbf_open. dand HV as (La1 & La3 & La4 & La7).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. open_const HC. open_ro HL. unfold f_const in K. fcx_cbn.
  clear HtL HtD Hsp0 Hsane.
  clear Sobu Spob Spq Sobq Cw1 Cw2 Swp Swq Swob Slaob Slap Sdaob Sdap TOKL TOKD Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cbo1 Cbo2 Cco1 Cco2 Cs8 Rfw.
  zkeys. unfold L_FHEAD, L_FLOOK in *. pose proof two64_eq as TW64.
  assert (HPb : 2 ^ bits <= 2 ^ 40) by (apply pow2_le; lia).
  zrebase.
  destruct (Z_lt_dec 14 bits) as [Hge|Hlt].
  - (* ONE RUN to the lookup place *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ => eapply (K RX ci hold bits) end).
    all: try zreg. all: try lia. all: split_conj; zreg.
  - (* the model facts stand before the run (the hand text states them between the steps) *)
    pose proof (Rfin (ci + 1) ltac:(lia)) as Rb1. pose proof (Rfin ci ltac:(lia)) as Rb0.
    pose proof (hold_pull2 hold bits (fin ci) (fin (ci + 1)) ltac:(lia) ltac:(lia) Rb0 Rb1) as HP2.
    assert (HPb2 : 2 ^ (bits + 16) <= 2 ^ 40) by (apply pow2_le; lia).
    (* THREE VALUE EQUATIONS STATED BEFORE THE RUN (the two pulled bytes, shifted; the bit count after two bytes):
       the run is plain; the closing lines' solver reads the equations *)
    pose proof (shl_byte_eq (fin (ci + 1)) (bits + 8) Rb1 ltac:(lia)) as EQ1.
    pose proof (shl_byte_eq (fin ci) bits Rb0 ltac:(lia)) as EQ0.
    pose proof (lor_16 bits ltac:(lia)) as EQ16.
    (* ONE RUN to the lookup place *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
      eapply (K RX (ci + 2) (hold + fin ci * 2 ^ bits + fin (ci + 1) * 2 ^ (bits + 8)) (bits + 16)) end).
    all: try zreg. all: try lia. all: split_conj; zreg.
Qed.


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

Lemma fast_declen {RCa1 : RunCtx}  : forall cx R l M MD T (hold bits v3 v4 : Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> rholds (qargs [hold; v3; v4; bits]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_look ->
  f_ro cx M ->
  15 <= bits -> bits <= 40 -> 0 <= hold -> hold < 2 ^ bits ->
  (forall R' (k hold' bits' : Z),
     f_const cx R' [] -> rholds (qargs [hold'; v3; v4; bits'; f_la cx + 4 * k]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_lit ->
     0 <= k -> k < f_na cx ->
     0 <= bits' -> 1 <= bits - bits' -> bits - bits' <= 15 -> 0 <= hold' -> hold' < 2 ^ bits' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLIT (zupd R' []) M MD) T) ->
  (forall R' (k hold' bits' : Z),
     f_const cx R' [] -> rholds (qargs [hold'; v3; v4; bits'; f_la cx + 4 * k; code_op (f_rdL cx k)]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_lenb ->
     0 <= k -> k < f_na cx ->
     16 <= code_op (f_rdL cx k) -> code_op (f_rdL cx k) <= 21 -> 3 <= code_val (f_rdL cx k) ->
     code_val (f_rdL cx k) + 2 ^ (code_op (f_rdL cx k) - 16) - 1 <= 258 ->
     0 <= bits' -> 1 <= bits - bits' -> bits - bits' <= 15 -> 0 <= hold' -> hold' < 2 ^ bits' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLENB (zupd R' []) M MD) T) ->
  (forall R' (op hold' bits' : Z),
     f_const cx R' [] -> rholds (qargs [hold'; v3; v4; bits'; op]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_eobk ->
     0 <= op -> op < 256 ->
     0 <= bits' -> 1 <= bits - bits' -> bits - bits' <= 15 -> 0 <= hold' -> hold' < 2 ^ bits' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FEOB (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLOOK (zupd R l) M MD) T.
Proof.
  intros cx Rg l M MD T hold bits v3 v4 CX Hh HC HV HL Hb1 Hb2 Hh1 Hh2 KLIT KLENB KEOB. zbf_open. dand HV as (La1 & La3 & La4 & La7).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. open_const HC. open_ro HL. unfold f_const in KLIT, KLENB, KEOB. fcx_cbn.
  clear Hin HtD Hsp0 Hsane.
  clear Sobu Spob Spq Sobq Cw1 Cw2 Swp Swq Swob Slaob Slap Sdaob Sdap TOKD Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cbo1 Cbo2 Cco1 Cco2 Cs8 Rfw Rfin.
  zkeys. unfold L_FLOOK, L_FLIT, L_FLENB, L_FEOB in *. pose proof two64_eq as TW64.
  assert (HPb : 2 ^ bits <= 2 ^ 40) by (apply pow2_le; lia). pose proof (pow2_15 lb ltac:(lia)) as HPl.
  (* THE ROOT INDEX GETS ITS NAME BEFORE THE RUN (the hand text names the newest value after the first step);
     the equation `Ei1` is the run's hint for it; the model facts on it stand before the run too *)
  pose (i1 := Z.land hold (2 ^ lb + -1)).
  assert (Ei1 : Z.land hold (2 ^ lb + -1) = i1) by reflexivity.
  pose proof (land_mask_range hold lb ltac:(lia)) as Ri1; replace (2 ^ lb - 1) with (2 ^ lb + -1) in Ri1 by lia; fold i1 in Ri1.
  clearbody i1.
  pose proof (tab_root_entry LENS rdL lb na i1 TOKL Ri1) as (Hbits1 & _ & Hext & CASES).
  pose proof (code_op_range (rdL i1)) as Rop1. pose proof (code_val_range (rdL i1)) as Rval1.
  pose proof (srl_hold hold bits) as SH1.
  pose proof (hold_shr_bound hold bits (code_bits (rdL i1)) ltac:(lia) ltac:(lia)) as Hh'.
  zrebase.
  (* THREE RUNS: to the load of the entry's bit count (its index is the root index), with TWO VALUE HINTS; to
     the load of its kind; to the first test, with ONE VALUE HINT (the hold shifted) *)
  zuntil_h Rfd (first [ zhint Ei1 | zhint shiftl_2 ]) (idtac; tld4_bits HtL i1).
  zuntil0 Rfd (idtac; tld4_op HtL i1).
  zto_branch_h Rfd (first [ zhint SH1 ]).
  Local Ltac fin := try zreg; try lia; try (split_conj; zreg).
  destruct CASES as [[NL TM] | (L1 & L2 & L3 & L4 & SUB)].
  -
    apply term_ok_LENS in TM as (Hb1' & CL).
    destruct CL as [(Hop0 & Hv) | [(Hop16 & Hv3 & Hv258 & Hop21) | (H64 & H16)]].
    +
      (* ONE RUN to the literal place *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
        eapply (KLIT RX i1 (hold / 2 ^ code_bits (rdL i1)) (bits - code_bits (rdL i1))) end).
      all: fin.
    +
      pose proof (op_base_tests (code_op (rdL i1)) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
      rewrite shiftl_1_pow in Hv258 by lia.
      (* ONE RUN to the length-base place, with ONE VALUE HINT (the kind's low byte) *)
      zuntil_h Rfd (first [ zhint land_255_id ])
        (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
          eapply (KLENB RX i1 (hold / 2 ^ code_bits (rdL i1)) (bits - code_bits (rdL i1))) end).
      all: fin.
    +
      assert (Tnz : code_op (rdL i1) <> 0) by (intros E; rewrite E in H64; apply H64; reflexivity).
      pose proof (land_range_r (code_op (rdL i1)) 64 ltac:(lia)) as R64.
      (* ONE RUN to the end-of-block place, with ONE VALUE HINT *)
      zuntil_h Rfd (first [ zhint land_255_id ])
        (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
          eapply (KEOB RX (code_op (rdL i1)) (hold / 2 ^ code_bits (rdL i1)) (bits - code_bits (rdL i1))) end).
      all: fin.
  -
    pose proof (op_link_tests (code_op (rdL i1)) ltac:(lia)) as (T16 & T64 & T240 & Tnz).
    pose proof (pow2_15 (code_op (rdL i1)) ltac:(lia)) as HPo.
    (* THE SECOND-LEVEL INDEX GETS ITS NAME BEFORE THE RUNS; `Ej` is the hint for it *)
    pose (j := Z.land (hold / 2 ^ code_bits (rdL i1)) (2 ^ code_op (rdL i1) + -1)).
    assert (Ej : Z.land (hold / 2 ^ code_bits (rdL i1)) (2 ^ code_op (rdL i1) + -1) = j) by reflexivity.
    pose proof (land_mask_range (hold / 2 ^ code_bits (rdL i1)) (code_op (rdL i1)) ltac:(lia)) as Rj;
    replace (2 ^ code_op (rdL i1) - 1) with (2 ^ code_op (rdL i1) + -1) in Rj by lia; fold j in Rj.
    clearbody j.
    destruct (SUB j Rj) as [NL2 TM2]. apply term_ok_LENS in TM2 as (Hbits2 & CL2).
    pose proof (code_op_range (rdL (code_val (rdL i1) + j))) as Rop2.
    pose proof (srl_hold (hold / 2 ^ code_bits (rdL i1)) (bits - code_bits (rdL i1))) as SH2.
    pose proof (hold_shr_bound (hold / 2 ^ code_bits (rdL i1)) (bits - code_bits (rdL i1))
                  (code_bits (rdL (code_val (rdL i1) + j))) ltac:(lia) ltac:(lia)) as Hh''.
    (* FOUR RUNS: to the load of the link's base index; to the load of the second entry's bit count; to the load
       of its kind; to the next test *)
    zuntil_h Rfd (first [ zhint land_255_id ]) (idtac; tld4_val HtL i1).
    zuntil_h Rfd (first [ zhint mask_not_sllw | zhint Ej | zhint shiftl_2 ])
      (idtac; tld4_bits HtL (code_val (rdL i1) + j)).
    zuntil0 Rfd (idtac; tld4_op HtL (code_val (rdL i1) + j)).
    zto_branch_h Rfd (first [ zhint SH2 ]).
    destruct CL2 as [(Hop0 & Hv) | [(Hop16 & Hv3 & Hv258 & Hop21) | (H64 & H16)]].
    +
      (* ONE RUN to the literal place *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
        eapply (KLIT RX (code_val (rdL i1) + j) (hold / 2 ^ code_bits (rdL i1) / 2 ^ code_bits (rdL (code_val (rdL i1) + j)))
                  (bits - code_bits (rdL i1) - code_bits (rdL (code_val (rdL i1) + j)))) end).
      all: fin.
    +
      pose proof (op_base_tests (code_op (rdL (code_val (rdL i1) + j))) ltac:(lia)) as (U16 & U64 & U32 & U240 & U15 & Unz).
      rewrite shiftl_1_pow in Hv258 by lia.
      (* ONE RUN to the length-base place, with ONE VALUE HINT *)
      zuntil_h Rfd (first [ zhint land_255_id ])
        (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
          eapply (KLENB RX (code_val (rdL i1) + j) (hold / 2 ^ code_bits (rdL i1) / 2 ^ code_bits (rdL (code_val (rdL i1) + j)))
                    (bits - code_bits (rdL i1) - code_bits (rdL (code_val (rdL i1) + j)))) end).
      all: fin.
    +
      assert (Unz : code_op (rdL (code_val (rdL i1) + j)) <> 0) by (intros E; rewrite E in H64; apply H64; reflexivity).
      pose proof (land_range_r (code_op (rdL (code_val (rdL i1) + j))) 64 ltac:(lia)) as R64.
      (* ONE RUN to the end-of-block place, with ONE VALUE HINT *)
      zuntil_h Rfd (first [ zhint land_255_id ])
        (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
          eapply (KEOB RX (code_op (rdL (code_val (rdL i1) + j))) (hold / 2 ^ code_bits (rdL i1) / 2 ^ code_bits (rdL (code_val (rdL i1) + j)))
                    (bits - code_bits (rdL i1) - code_bits (rdL (code_val (rdL i1) + j)))) end).
      all: fin.
Qed.


Lemma fast_lit {RCa1 : RunCtx}  : forall cx M1 R l M MD T (k co v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> rholds (qargs [v1; v3; f_ob cx + co; v7; f_la cx + 4 * k]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_lit ->
  0 <= k -> k < f_na cx ->
  0 <= co -> co < f_osz cx ->
  f_ro cx M -> f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R' M' (fo' : Z -> Z),
     f_const cx R' [] -> rholds (qargs [v1; v3; f_ob cx + co + 1; v7]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_latch ->
     f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLATCH (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLIT (zupd R l) M MD) T.
Proof.
  intros cx M1 Rg l M MD T k co v1 v3 v7 fo CX Hh HC HV Hk1 Hk2 Hco1 Hco2 HRO HL Rfo HAG K. zbf_open. dand HV as (La1 & La3 & La4 & La7 & Lt2).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. open_const HC. open_ro HRO. open_live HL. unfold f_const, f_live, FPW in K |- *. fcx_cbn.
  clear Hin HtD Hsp0 Hsane.
  clear Spq Swp Swq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cwn1 Cwn2 Cbo1 Cbo2 Cco1 Cco2 Cs8 Rfw Rfin.
  zkeys. unfold L_FLIT, L_FLATCH in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  pose proof (mod_256_range (code_val (rdL k))) as Rv.
  zrebase.
  (* THREE RUNS: to the table load (the text's own load rule, with its index); to the store into the output
     array (the kit's array store, with its index); to the latch place *)
  zuntil0 Rfd (idtac; tld4_vlo HtL k).
  clear HtL.
  zuntil0 Rfd (idtac; tstore_arr Rfd HOB co).
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ =>
    eapply (K RX MX (zfupd fo co (code_val (rdL k) mod 256))) end).
  all: try zreg. all: try assumption. all: try (split_conj; first [assumption | zreg]).
  apply (zfupd_byte fo co _ 0 osz Rfo Rv).
Qed.


Lemma fast_lenb {RCa1 : RunCtx}  : forall cx R l M MD T (k ci hold bits v4 : Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> rholds (qargs [hold; f_q cx + ci; v4; bits; f_la cx + 4 * k; code_op (f_rdL cx k)]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_lenb ->
  0 <= k -> k < f_na cx ->
  16 <= code_op (f_rdL cx k) -> code_op (f_rdL cx k) <= 21 -> 3 <= code_val (f_rdL cx k) ->
  code_val (f_rdL cx k) + 2 ^ (code_op (f_rdL cx k) - 16) - 1 <= 258 ->
  f_ro cx M ->
  0 <= ci -> ci <= f_n cx -> 0 <= bits -> bits <= 40 -> bits <= 8 * ci -> 0 <= hold -> hold < 2 ^ bits ->
  33 <= 8 * (f_n cx - ci) + bits ->
  (forall R' (ci' hold' bits' len : Z),
     f_const cx R' [] -> rholds (qargs [hold'; f_q cx + ci'; v4; bits'; len]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_dlook ->
     3 <= len -> len <= 258 ->
     ci <= ci' -> ci' <= ci + 3 -> ci' <= f_n cx -> 15 <= bits' -> bits' <= 40 -> bits' <= 8 * ci' -> 0 <= hold' -> hold' < 2 ^ bits' ->
     8 * (f_n cx - ci') + bits' <= 8 * (f_n cx - ci) + bits -> 28 <= 8 * (f_n cx - ci') + bits' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDLOOK (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLENB (zupd R l) M MD) T.
Proof.
  intros cx Rg l M MD T k ci hold bits v4 CX Hh HC HV Hk1 Hk2 Hop1 Hop2 Hv1 Hv2 HL
         Hci1 Hci2 Hb1 Hb2 Hb3 Hh1 Hh2 HA K. zbf_open. dand HV as (La1 & La3 & La4 & La7 & Lt2 & Ls9).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. open_const HC. open_ro HL. unfold f_const in K. fcx_cbn.
  clear HtD Hsp0 Hsane.
  clear Sobu Spob Spq Sobq Cw1 Cw2 Swp Swq Swob Slaob Slap Sdaob Sdap TOKL TOKD Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cbo1 Cbo2 Cco1 Cco2 Cs8 Rfw.
  zkeys. unfold L_FLENB, L_FDLOOK in *. pose proof two64_eq as TW64.
  assert (HPb : 2 ^ bits <= 2 ^ 40) by (apply pow2_le; lia).
  set (op := code_op (rdL k)) in *. set (val := code_val (rdL k)) in *.
  pose proof (op_base_tests op ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
  pose proof (pow2_15 (op - 16) ltac:(lia)) as HPe.
  (* THE FIRST JOIN PLACE INSIDE THIS LEMMA, in the list form: the constant map and the layout's list of the
     place at the values bound: 0 the hold; 1 the next input address; 2 the value bound for the output
     register; 3 the bit count; 4 the length *)
  assert (J : forall RJ (cj hj bj len : Z),
    f_const (FCX u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw) RJ [] ->
    rholds (qargs [hj; q + cj; v4; bj; len]) RJ [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_lenj ->
    3 <= len -> len <= 258 -> ci <= cj -> cj <= ci + 1 -> cj <= n -> 0 <= bj -> bj <= 40 -> bj <= 8 * cj -> 0 <= hj -> hj < 2 ^ bj ->
    8 * (n - cj) + bj <= 8 * (n - ci) + bits -> 28 <= 8 * (n - cj) + bj ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLENJ (zupd RJ []) M MD) T).
  { intros RJ cj hj bj len GC GV Hl1 Hl2 Hcj1 Hcj2 Hcj3 Hbj1 Hbj2 Hbj3 Hhj1 Hhj2 HAj1 HAj2.
    unfold f_const in GC. zbf_open. fcx_cbn. destr_conj GC. destr_conj GV. zkeys.
    repeat match goal with HH : zget_l RJ [] _ = _ |- _ => cbv [zget_l alookup] in HH end.
    assert (HPbj : 2 ^ bj <= 2 ^ 40) by (apply pow2_le; lia).
    unfold L_FLENJ.
    destruct (Z_lt_dec 14 bj) as [Hge|Hlt].
    - (* ONE RUN to the distance lookup place *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ => eapply (K RX cj hj bj len) end). all: kfin.
    - (* the model facts stand before the run *)
      pose proof (Rfin (cj + 1) ltac:(lia)) as Rb1. pose proof (Rfin cj ltac:(lia)) as Rb0.
      pose proof (hold_pull2 hj bj (fin cj) (fin (cj + 1)) ltac:(lia) ltac:(lia) Rb0 Rb1) as HP2.
      assert (HPb2 : 2 ^ (bj + 16) <= 2 ^ 40) by (apply pow2_le; lia).
      (* ONE RUN to the distance lookup place (its three value equations stand before it) *)
      pose proof (shl_byte_eq (fin (cj + 1)) (bj + 8) Rb1 ltac:(lia)) as EQ1. pose proof (shl_byte_eq (fin cj) bj Rb0 ltac:(lia)) as EQ0. pose proof (lor_16 bj ltac:(lia)) as EQ16. zuntil Rfd
        (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
          eapply (K RX (cj + 2) (hj + fin cj * 2 ^ bj + fin (cj + 1) * 2 ^ (bj + 8)) (bj + 16) len) end).
      all: kfin. }
  unfold f_const in J. zbf_in J. fcx_cbn.
  clear K.
  zrebase.
  (* TWO RUNS: the load of the length's base value (the text's own load, with its index); to the test of the
     extra bits' count (a model fact in hand names the machine form) *)
  zuntil0 Rfd (idtac; tld4_val HtL k; fold val).
  zto_branch Rfd.
  destruct (Z.eq_dec (op - 16) 0) as [E0|NE0].
  - (* ONE RUN to the join place of the length *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ => eapply (J RX ci hold bits val) end). all: kfin.
  - (* the second join place's statement, in the list form, stands before the run that takes the test's branch:
       the values: 0 the hold; 1 the next input address; 2 the value bound for the output register; 3 the bit
       count; 4 the length's base value; 5 the count of extra bits *)
    assert (J2 : forall RJ (cj hj bj : Z),
      f_const (FCX u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw) RJ [] ->
      rholds (qargs [hj; q + cj; v4; bj; val; op - 16]) RJ [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_lenj2 ->
      ci <= cj -> cj <= ci + 1 -> cj <= n -> op - 16 <= bj -> bj <= 40 -> bj <= 8 * cj -> 0 <= hj -> hj < 2 ^ bj ->
      8 * (n - cj) + bj = 8 * (n - ci) + bits ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLENJ2 (zupd RJ []) M MD) T).
    { intros RJ cj hj bj GC GV Hcj1 Hcj2 Hcj3 Hbj1 Hbj2 Hbj3 Hhj1 Hhj2 HAj.
      unfold f_const in GC. zbf_open. fcx_cbn. destr_conj GC. destr_conj GV. zkeys.
      repeat match goal with HH : zget_l RJ [] _ = _ |- _ => cbv [zget_l alookup] in HH end.
      assert (HPbj : 2 ^ bj <= 2 ^ 40) by (apply pow2_le; lia).
      pose proof (land_mask_range hj (op - 16) ltac:(lia)) as Rm. pose proof (land_mask_le hj (op - 16) ltac:(lia) ltac:(lia)) as Rm2.
      unfold L_FLENJ2.
      pose proof (srl_hold hj bj) as SHj.
      pose proof (hold_shr_bound hj bj (op - 16) ltac:(lia) ltac:(lia)) as Hh'.
      (* ONE RUN to the join place of the length, with TWO VALUE HINTS (the mask of the extra bits; the hold
         shifted) *)
      zuntil_h Rfd (first [ zhint mask_not_sllw | zhint SHj ])
        (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
          eapply (J RX cj (hj / 2 ^ (op - 16)) (bj - (op - 16)) (Z.land hj (2 ^ (op - 16) + -1) + val)) end).
      all: kfin.
      all: replace (2 ^ (op - 16) + -1) with (2 ^ (op - 16) - 1) by lia; lia. }
    unfold f_const in J2. zbf_in J2. fcx_cbn.
    destruct (Z_lt_dec bits (op - 16)) as [Hlt|Hge].
    + (* the model facts stand before the run *)
      pose proof (Rfin ci ltac:(lia)) as Rb0.
      pose proof (hold_pull1 hold bits (fin ci) ltac:(lia) ltac:(lia) Rb0) as HP1.
      (* ONE RUN to the second join place (its value equation stands before it) *)
      pose proof (shl_byte_eq (fin ci) bits Rb0 ltac:(lia)) as EQ0. zuntil Rfd
        (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
          eapply (J2 RX (ci + 1) (hold + fin ci * 2 ^ bits) (bits + 8)) end).
      all: kfin.
    + (* ONE RUN to the second join place *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ => eapply (J2 RX ci hold bits) end).
      all: kfin.
Qed.

End S_Fast2.

Module S_Fast3.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import S_Fast1 S_Fast2.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Lemma fast_decdist {RCa1 : RunCtx}  : forall cx R l M MD T (hold bits v3 v4 v27 : Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> rholds (qargs [hold; v3; v4; bits; v27]) R l
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_dlook ->
  f_ro cx M ->
  15 <= bits -> bits <= 40 -> 0 <= hold -> hold < 2 ^ bits ->
  (forall R' (k hold' bits' : Z),
     f_const cx R' [] -> rholds (qargs [hold'; v3; v4; bits'; v27; f_da cx + 4 * k; code_op (f_rdD cx k)]) R' []
     OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_distb ->
     0 <= k -> k < f_nd cx ->
     16 <= code_op (f_rdD cx k) -> code_op (f_rdD cx k) <= 29 -> 1 <= code_val (f_rdD cx k) ->
     code_val (f_rdD cx k) + 2 ^ (code_op (f_rdD cx k) - 16) - 1 <= 32768 ->
     0 <= bits' -> 1 <= bits - bits' -> bits - bits' <= 15 -> 0 <= hold' -> hold' < 2 ^ bits' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDISTB (zupd R' []) M MD) T) ->
  (forall R' (hold' bits' : Z),
     f_const cx R' [] -> rholds (qargs [hold'; v3; v4; bits']) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_baddk ->
     0 <= bits' -> 1 <= bits - bits' -> bits - bits' <= 15 -> 0 <= hold' -> hold' < 2 ^ bits' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FBADD (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDLOOK (zupd R l) M MD) T.
Proof.
  intros cx Rg l M MD T hold bits v3 v4 v27 CX Hh HC HV HL Hb1 Hb2 Hh1 Hh2 KDB KBAD. zbf_open. dand HV as (La1 & La3 & La4 & La7 & Ls10).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. open_const HC. open_ro HL. unfold f_const in KDB, KBAD. fcx_cbn.
  clear Hin HtL Hsp0 Hsane.
  clear Sobu Spob Spq Sobq Cw1 Cw2 Swp Swq Swob Slaob Slap Sdaob Sdap TOKL Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cbo1 Cbo2 Cco1 Cco2 Cs8 Rfw Rfin.
  zkeys. unfold L_FDLOOK, L_FDISTB, L_FBADD in *. pose proof two64_eq as TW64.
  assert (HPb : 2 ^ bits <= 2 ^ 40) by (apply pow2_le; lia). pose proof (pow2_15 db ltac:(lia)) as HPd.
  (* THE ROOT INDEX GETS ITS NAME BEFORE THE RUN (the hand text names the newest value after the first step);
     the equation `Ei1` is the run's hint for it; the model facts on it stand before the run too *)
  pose (i1 := Z.land hold (2 ^ db + -1)).
  assert (Ei1 : Z.land hold (2 ^ db + -1) = i1) by reflexivity.
  pose proof (land_mask_range hold db ltac:(lia)) as Ri1; replace (2 ^ db - 1) with (2 ^ db + -1) in Ri1 by lia; fold i1 in Ri1.
  clearbody i1.
  pose proof (tab_root_entry DISTS rdD db nd i1 TOKD Ri1) as (Hbits1 & _ & Hext & CASES).
  pose proof (code_op_range (rdD i1)) as Rop1. pose proof (code_val_range (rdD i1)) as Rval1.
  pose proof (srl_hold hold bits) as SH1.
  pose proof (hold_shr_bound hold bits (code_bits (rdD i1)) ltac:(lia) ltac:(lia)) as Hh'.
  zrebase.
  (* THREE RUNS: to the load of the entry's bit count (its index is the root index), with TWO VALUE HINTS; to
     the load of its kind; to the first test, with ONE VALUE HINT (the hold shifted) *)
  zuntil_h Rfd (first [ zhint Ei1 | zhint shiftl_2 ]) (idtac; tld4_bits HtD i1).
  zuntil0 Rfd (idtac; tld4_op HtD i1).
  zto_branch_h Rfd (first [ zhint SH1 ]).
  destruct CASES as [[NL TM] | (L1 & L2 & L3 & L4 & SUB)].
  -
    apply term_ok_DISTS in TM as (Hb1' & CL).
    destruct CL as [(Hop16 & Hv1 & Hv2 & Hop29) | (H64 & H16 & H32)].
    + pose proof (op_base_tests (code_op (rdD i1)) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
      rewrite shiftl_1_pow in Hv2 by lia.
      (* ONE RUN to the distance-base place *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
        eapply (KDB RX i1 (hold / 2 ^ code_bits (rdD i1)) (bits - code_bits (rdD i1))) end).
      all: kfin.
    + pose proof (land_range_r (code_op (rdD i1)) 64 ltac:(lia)) as R64.
      (* ONE RUN to the bad-distance place *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
        eapply (KBAD RX (hold / 2 ^ code_bits (rdD i1)) (bits - code_bits (rdD i1))) end).
      all: kfin.
  -
    pose proof (op_link_tests (code_op (rdD i1)) ltac:(lia)) as (T16 & T64 & T240 & Tnz).
    pose proof (pow2_15 (code_op (rdD i1)) ltac:(lia)) as HPo.
    (* THE SECOND-LEVEL INDEX GETS ITS NAME BEFORE THE RUNS; `Ej` is the hint for it *)
    pose (j := Z.land (hold / 2 ^ code_bits (rdD i1)) (2 ^ code_op (rdD i1) + -1)).
    assert (Ej : Z.land (hold / 2 ^ code_bits (rdD i1)) (2 ^ code_op (rdD i1) + -1) = j) by reflexivity.
    pose proof (land_mask_range (hold / 2 ^ code_bits (rdD i1)) (code_op (rdD i1)) ltac:(lia)) as Rj;
    replace (2 ^ code_op (rdD i1) - 1) with (2 ^ code_op (rdD i1) + -1) in Rj by lia; fold j in Rj.
    clearbody j.
    destruct (SUB j Rj) as [NL2 TM2]. apply term_ok_DISTS in TM2 as (Hbits2 & CL2).
    pose proof (code_op_range (rdD (code_val (rdD i1) + j))) as Rop2.
    pose proof (srl_hold (hold / 2 ^ code_bits (rdD i1)) (bits - code_bits (rdD i1))) as SH2.
    pose proof (hold_shr_bound (hold / 2 ^ code_bits (rdD i1)) (bits - code_bits (rdD i1))
                  (code_bits (rdD (code_val (rdD i1) + j))) ltac:(lia) ltac:(lia)) as Hh''.
    (* FOUR RUNS: to the load of the link's base index; to the load of the second entry's bit count, with THREE
       VALUE HINTS; to the load of its kind; to the next test, with ONE VALUE HINT *)
    zuntil Rfd (idtac; tld4_val HtD i1).
    zuntil_h Rfd (first [ zhint mask_not_sllw | zhint Ej | zhint shiftl_2 ])
      (idtac; tld4_bits HtD (code_val (rdD i1) + j)).
    zuntil0 Rfd (idtac; tld4_op HtD (code_val (rdD i1) + j)).
    zto_branch_h Rfd (first [ zhint SH2 ]).
    destruct CL2 as [(Hop16 & Hv1 & Hv2 & Hop29) | (H64 & H16 & H32)].
    + pose proof (op_base_tests (code_op (rdD (code_val (rdD i1) + j))) ltac:(lia)) as (U16 & U64 & U32 & U240 & U15 & Unz).
      rewrite shiftl_1_pow in Hv2 by lia.
      (* ONE RUN to the distance-base place *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
        eapply (KDB RX (code_val (rdD i1) + j) (hold / 2 ^ code_bits (rdD i1) / 2 ^ code_bits (rdD (code_val (rdD i1) + j)))
                  (bits - code_bits (rdD i1) - code_bits (rdD (code_val (rdD i1) + j)))) end).
      all: kfin.
    + pose proof (land_range_r (code_op (rdD (code_val (rdD i1) + j))) 64 ltac:(lia)) as R64.
      (* ONE RUN to the bad-distance place *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
        eapply (KBAD RX (hold / 2 ^ code_bits (rdD i1) / 2 ^ code_bits (rdD (code_val (rdD i1) + j)))
                  (bits - code_bits (rdD i1) - code_bits (rdD (code_val (rdD i1) + j)))) end).
      all: kfin.
Qed.


Lemma fast_distb {RCa1 : RunCtx}  : forall cx R l M MD T (k ci co hold bits len : Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> rholds (qargs [hold; f_q cx + ci; f_ob cx + co; bits; len; f_da cx + 4 * k; code_op (f_rdD cx k)]) R l
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_distb ->
  0 <= k -> k < f_nd cx ->
  16 <= code_op (f_rdD cx k) -> code_op (f_rdD cx k) <= 29 -> 1 <= code_val (f_rdD cx k) ->
  code_val (f_rdD cx k) + 2 ^ (code_op (f_rdD cx k) - 16) - 1 <= 32768 ->
  f_ro cx M ->
  0 <= ci -> ci <= f_n cx -> 0 <= bits -> bits <= 40 -> bits <= 8 * ci -> 0 <= hold -> hold < 2 ^ bits ->
  13 <= 8 * (f_n cx - ci) + bits ->
  f_bo cx <= co -> co <= f_osz cx ->
  (forall R' (ci' hold' bits' dist : Z),
     f_const cx R' [] -> rholds (qargs [hold'; f_q cx + ci'; f_ob cx + co; bits'; len; dist]) R' []
     OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_directk ->
     1 <= dist -> dist <= 32768 -> dist <= co - f_bo cx ->
     ci <= ci' -> ci' <= ci + 2 -> ci' <= f_n cx -> 0 <= bits' -> bits' <= 40 -> bits' <= 8 * ci' -> 0 <= hold' -> hold' < 2 ^ bits' ->
     8 * (f_n cx - ci') + bits' <= 8 * (f_n cx - ci) + bits ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDIRECT (zupd R' []) M MD) T) ->
  (forall R' (ci' hold' bits' dist : Z),
     f_const cx R' [] -> rholds (qargs [hold'; f_q cx + ci'; f_ob cx + co; bits'; len; dist]) R' []
     OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wink ->
     1 <= dist -> dist <= 32768 -> co - f_bo cx < dist ->
     ci <= ci' -> ci' <= ci + 2 -> ci' <= f_n cx -> 0 <= bits' -> bits' <= 40 -> bits' <= 8 * ci' -> 0 <= hold' -> hold' < 2 ^ bits' ->
     8 * (f_n cx - ci') + bits' <= 8 * (f_n cx - ci) + bits ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FWIN (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDISTB (zupd R l) M MD) T.
Proof.
  intros cx Rg l M MD T k ci co hold bits len CX Hh HC HV Hk1 Hk2 Hop1 Hop2 Hv1 Hv2 HL
         Hci1 Hci2 Hb1 Hb2 Hb3 Hh1 Hh2 HA Hco1 Hco2 KDIR KWIN. zbf_open. dand HV as (La1 & La3 & La4 & La7 & Ls10 & Lt2 & Ls11).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. open_const HC. open_ro HL. unfold f_const in KDIR, KWIN. fcx_cbn.
  clear HtL Hsp0 Hsane.
  clear Sobu Spob Spq Sobq Cw1 Cw2 Swp Swq Swob Slaob Slap Sdaob Sdap TOKL TOKD Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cco1 Cco2 Cs8 Rfw.
  zkeys. unfold L_FDISTB, L_FDIRECT, L_FWIN in *. pose proof two64_eq as TW64.
  assert (HPb : 2 ^ bits <= 2 ^ 40) by (apply pow2_le; lia).
  set (op := code_op (rdD k)) in *.
  pose proof (op_base_tests op ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
  replace (op - 16) with (op + -16) in Hv2 by lia. replace (op - 16) with (op + -16) in T15 by lia.
  pose proof (pow2_15 (op + -16) ltac:(lia)) as HPe.
  (* THE JOIN PLACE INSIDE THIS LEMMA, in the list form: the constant map and the layout's list of the place at
     the values bound: 0 the hold; 1 the next input address; 2 the next output address; 3 the bit count; 4 the
     length; 5 the table entry's address; 6 the count of extra bits *)
  assert (J : forall RJ (cj hj bj : Z),
    f_const (FCX u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw) RJ [] ->
    rholds (qargs [hj; q + cj; ob + co; bj; len; da + 4 * k; op + -16]) RJ [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_distj ->
    ci <= cj -> cj <= ci + 2 -> cj <= n -> op + -16 <= bj -> bj <= 40 -> bj <= 8 * cj -> 0 <= hj -> hj < 2 ^ bj ->
    8 * (n - cj) + bj = 8 * (n - ci) + bits ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDISTJ (zupd RJ []) M MD) T).
  { intros RJ cj hj bj GC GV Hcj1 Hcj2 Hcj3 Hbj1 Hbj2 Hbj3 Hhj1 Hhj2 HAj.
    unfold f_const in GC. zbf_open. fcx_cbn. destr_conj GC. destr_conj GV. zkeys.
    repeat match goal with HH : zget_l RJ [] _ = _ |- _ => cbv [zget_l alookup] in HH end.
    assert (HPbj : 2 ^ bj <= 2 ^ 40) by (apply pow2_le; lia).
    pose proof (land_mask_range' hj (op + -16) ltac:(lia)) as Rm.
    unfold L_FDISTJ.
    pose proof (srl_hold hj bj) as SHj.
    pose proof (hold_shr_bound hj bj (op + -16) ltac:(lia) ltac:(lia)) as Hh'.
    (* TWO RUNS: the load of the distance's base value (the text's own load, with its index); to the test of the
       distance against the output written, with TWO VALUE HINTS (the mask of the extra bits; the hold shifted) *)
    zuntil0 Rfd (idtac; tld4_val HtD k).
    zto_branch_h Rfd (first [ zhint mask_not_sllw | zhint SHj ]).
    destruct (Z_lt_dec (co - bo) (Z.land hj (2 ^ (op + -16) + -1) + code_val (rdD k))) as [Hw|Hd].
    - (* ONE RUN to the window place *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
        eapply (KWIN RX cj (hj / 2 ^ (op + -16)) (bj - (op + -16)) (Z.land hj (2 ^ (op + -16) + -1) + code_val (rdD k))) end).
      all: kfin.
    - (* ONE RUN to the direct-copy place *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
        eapply (KDIR RX cj (hj / 2 ^ (op + -16)) (bj - (op + -16)) (Z.land hj (2 ^ (op + -16) + -1) + code_val (rdD k))) end).
      all: kfin. }
  unfold f_const in J. zbf_in J. fcx_cbn.
  clear KDIR KWIN.
  zrebase.
  (* ONE RUN to the test of the extra bits' count (a model fact in hand names the machine form) *)
  zto_branch Rfd.
  destruct (Z_lt_dec bits (op + -16)) as [Hlt|Hge].
  - (* the model facts stand before the run *)
    pose proof (Rfin ci ltac:(lia)) as Rb0.
    pose proof (hold_pull1 hold bits (fin ci) ltac:(lia) ltac:(lia) Rb0) as HP1.
    (* ONE RUN to the second test of the bit count (its value equation stands before it) *)
    pose proof (shl_byte_eq (fin ci) bits Rb0 ltac:(lia)) as EQ0. zto_branch Rfd.
    destruct (Z_lt_dec (bits + 8) (op + -16)) as [Hlt2|Hge2].
    + (* the model facts stand before the run *)
      pose proof (Rfin (ci + 1) ltac:(lia)) as Rb1.
      pose proof (hold_pull1 (hold + fin ci * 2 ^ bits) (bits + 8) (fin (ci + 1)) HP1 ltac:(lia) Rb1) as HP2.
      replace (bits + 8 + 8) with (bits + 16) in HP2 by lia.
      assert (HPb2 : 2 ^ (bits + 16) <= 2 ^ 40) by (apply pow2_le; lia).
      (* ONE RUN to the join place (its value equation stands before it) *)
      pose proof (shl_byte_eq (fin (ci + 1)) (bits + 8) Rb1 ltac:(lia)) as EQ1. zuntil Rfd
        (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
          eapply (J RX (ci + 2) (hold + fin ci * 2 ^ bits + fin (ci + 1) * 2 ^ (bits + 8)) (bits + 16)) end).
      all: kfin.
    + (* the model fact stands before the run *)
      assert (HPb1 : 2 ^ (bits + 8) <= 2 ^ 40) by (apply pow2_le; lia).
      (* ONE RUN to the join place *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ =>
        eapply (J RX (ci + 1) (hold + fin ci * 2 ^ bits) (bits + 8)) end).
      all: kfin.
  - (* ONE RUN to the join place *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ => eapply (J RX ci hold bits) end).
    all: kfin.
Qed.

End S_Fast3.

Module S_Fast4.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import S_Fast1 S_Fast2.
Import ListNotations.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* THE PLACES OF THIS HALF ARE FIELDS OF THE LAYOUT TEXT; here they have their short names only *)
Local Notation L_FC3TA := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FC3TA (only parsing).
Local Notation L_FC3T1 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FC3T1 (only parsing).
Local Notation L_FWLOOP2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWLOOP2 (only parsing).
Local Notation L_FWL_WR := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_WR (only parsing).
Local Notation L_FWL_WR_X := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_WR_X (only parsing).
Local Notation L_FWL_W0 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_W0 (only parsing).
Local Notation L_FWL_W0_X := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_W0_X (only parsing).
Local Notation L_FWL_CT := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_CT (only parsing).
Local Notation L_FWL_CT_X := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_CT_X (only parsing).
Local Notation L_FWLOOP2_X := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWLOOP2_X (only parsing).
(* the meaning words of the list form, by their short names *)
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation qargs := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs (only parsing).

(* OPENERS OF THE LIST FORM (they only unfold): the meaning of a list of this half, in a hypothesis and in
   the goal *)
Ltac open_q H :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_cregs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_kl
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wloop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wloop_k
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wloop2
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_c3loop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_c3loop_k
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_c3tail OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_copy3w
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_fromout OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_fromwin
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_w0 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_contig
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wrap OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_win
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_toofar
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_dloop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_dloop_k
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_dtail OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_direct
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_head OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_loopx] in H.
Ltac open_q_goal :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_cregs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_kl
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wloop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wloop_k
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wloop2
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_c3loop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_c3loop_k
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_c3tail OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_copy3w
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_fromout OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_fromwin
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_w0 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_contig
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wrap OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_win
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_toofar
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_dloop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_dloop_k
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_dtail OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_direct
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_head OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_loopx].

Definition cregs (cx : fcx) (v1 v3 v7 v28 : Z) (R : tree Z) (l : list (positive * Z)) : Prop :=
  f_const cx R l /\ rholds (qargs [v1; v3; v7; v28]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_cregs.
Ltac open_cregs H := let HC := ident:(HC) in let HQ := fresh "HQc" in
  (dand H as (HC & HQ); open_const HC; open_q HQ; dand HQ as (La1 & La3 & La7 & Ls11)).

Definition KL {RCa1 : RunCtx}  (cx : fcx) (M1 : mem) (MD : Model) (T : TSet) (v1 v3 v7 v28 c : Z) : Prop :=
  forall R' M' (fo' : Z -> Z),
    cregs cx v1 v3 v7 v28 R' [] -> rholds (qargs [f_ob cx + c]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_kl ->
    f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLATCH (zupd R' []) M' MD) T.

Ltac zpc_norm :=
  lazymatch goal with |- realizes ?s (zcfg ?s' ?pc ?R ?M ?MD) ?T =>
    let v := eval vm_compute in pc in change (realizes s (zcfg s' v R M MD) T) end.

Ltac zgetl0 := repeat match goal with H : zget_l ?R [] ?k = ?v |- _ => cbv [zget_l alookup] in H end.

Ltac prep_copy CX HR HL :=
  open_ok CX; open_cregs HR; open_live HL; fcx_cbn; zkeys; pose proof two64_eq as TW64.

(* the closing word of this half's continuation premises: the list-form facts in hand and in the goal are
   opened first; then the hand text's closing word as it stands *)
Ltac kfin :=
  try assumption;
  repeat match goal with H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ |- _ => open_q H; destr_conj H end;
  try (lazymatch goal with |- context [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds] => open_q_goal end);
  try zreg; try assumption; try (split_conj; first [assumption | eassumption | zreg]); try lia.

Lemma fast_wloop {RCa1 : RunCtx}  : forall pc pcx,
  ((pc = L_FWL_WR /\ pcx = L_FWL_WR_X) \/ (pc = L_FWL_W0 /\ pcx = L_FWL_W0_X) \/
   (pc = L_FWL_CT /\ pcx = L_FWL_CT_X)) ->
  forall (N : nat) cx M1 R l M MD T (wi c m v1 v3 v7 v8 v27 v28 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 v28 R l ->
  rholds (qargs [v8; v27; f_w cx + wi; f_ob cx + c; m]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wloop ->
  1 <= m -> m <= Z.of_nat N -> 0 <= wi -> wi + m <= f_wn cx -> 0 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R' M' (fo' : Z -> Z),
     cregs cx v1 v3 v7 v28 R' [] ->
     rholds (qargs [v8; v27; f_w cx + wi + m; f_ob cx + c + m]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wloop_k ->
     f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pcx (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd R l) M MD) T.
Proof.
  intros pc pcx Hpc N. induction N as [|N IH]; intros cx M1 R l M MD T wi c m v1 v3 v7 v8 v27 v28 fo CX Hh HR HQ
    Hm1 Hm2 Hwi1 Hwi2 Hc1 Hc2 HL Rfo HAG K; [lia|].
  open_q HQ. dand HQ as (Lt2 & Ls10 & Lra & La4 & Ls9).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. prep_copy CX HR HL. unfold cregs, f_const, f_live, FPW in K, IH |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  pose proof (Rfw wi ltac:(lia)) as Rb.
  pose proof (zfupd_byte fo c (fw wi) 0 osz Rfo Rb) as Rfo'.
  destruct Hpc as [[-> ->] | [[-> ->] | [-> ->]]].
  (* each way: the array load is the first run's handed-in call; ONE RUN to the array store (the store is the
     run's handed-in call); ONE RUN to the loop's exit test; then ONE RUN to the continuation or back to the
     loop's head, where the induction hypothesis applies *)
  all: cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_WR OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_WR_X
            OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_W0 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_W0_X
            OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_CT OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_CT_X] in K, IH |- *;
    zrebase;
    zuntil0 Rfd (idtac; tld1 Hwin wi Rfw);
    zuntil Rfd (idtac; tstore_arr Rfd HOB c);
    zto_branch Rfd;
    (destruct (Z.eq_dec m 1) as [E1|N1];
     [ zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd fo c (fw wi))) end); kfin
     | zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
         eapply (IH _ M1 Rx [] Mx MD T (wi + 1) (c + 1) (m - 1) v1 v3 v7 v8 v27 v28 (zfupd fo c (fw wi)) CX' Hh) end);
       [ (fcx_cbn; kfin) .. | ] ]).
  all: intros R' M' fo' HR' HQ' HL' Rfo'' HAG'; fcx_cbn;
       lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K R' M' fo') end; kfin.
Qed.

Lemma fast_wloop2 {RCa1 : RunCtx}  : forall (N : nat) cx M1 R l M MD T (wi c v1 v3 v7 v27 v28 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 v28 R l ->
  rholds (qargs [v27; f_w cx + wi; f_ob cx + c]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wloop2 ->
  f_s8 cx = f_w cx + f_wnext cx ->
  0 <= wi -> wi < f_wnext cx -> f_wnext cx - wi <= Z.of_nat N -> 0 <= c -> c + (f_wnext cx - wi) <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R' M' (fo' : Z -> Z),
     cregs cx v1 v3 v7 v28 R' [] ->
     rholds (qargs [v27; f_w cx + f_wnext cx; f_ob cx + c + (f_wnext cx - wi)]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wloop2 ->
     f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FWLOOP2_X (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FWLOOP2 (zupd R l) M MD) T.
Proof.
  induction N as [|N IH]; intros cx M1 R l M MD T wi c v1 v3 v7 v27 v28 fo CX Hh HR HQ Es8
    Hwi1 Hwi2 HN Hc1 Hc2 HL Rfo HAG K; [lia|].
  open_q HQ. dand HQ as (Ls10 & Lt2 & La4).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. prep_copy CX HR HL. unfold cregs, f_const, f_live, FPW, L_FWLOOP2, L_FWLOOP2_X in K, IH |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  pose proof (Rfw wi ltac:(lia)) as Rb.
  zrebase.
  pose proof (zfupd_byte fo c (fw wi) 0 osz Rfo Rb) as Rfo'.
  (* the array load and the array store are the handed-in calls of two runs; ONE RUN to the loop's exit test *)
  zuntil0 Rfd (idtac; tld1 Hwin wi Rfw).
  zuntil0 Rfd (idtac; tstore_arr Rfd HOB c).
  zto_branch Rfd.
  destruct (Z.eq_dec (wi + 1) wnext) as [E1|N1].
  - (* ONE RUN to the continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd fo c (fw wi))) end); kfin.
  - (* THE BACK EDGE: ONE RUN to the loop's head, where the induction hypothesis applies *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH _ M1 Rx [] Mx MD T (wi + 1) (c + 1) v1 v3 v7 v27 v28 (zfupd fo c (fw wi)) CX' Hh) end).
    all: try (fcx_cbn; kfin).
    intros R' M' fo' HR' HQ' HL' Rfo'' HAG'; fcx_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K R' M' fo') end; kfin.
Qed.

Lemma fast_c3loop_w {RCa1 : RunCtx}  : forall (N : nat) cx M1 R l M MD T (wi c m v1 v3 v7 v28 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 v28 R l ->
  rholds (qargs [f_w cx + wi; f_ob cx + c; m]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_c3loop ->
  3 <= m -> m <= Z.of_nat N -> 0 <= wi -> wi + m <= f_wn cx -> 0 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R' M' (fo' : Z -> Z) (k : Z),
     cregs cx v1 v3 v7 v28 R' [] ->
     rholds (qargs [f_w cx + wi + k; f_w cx + wi + k; f_ob cx + c + k; f_ob cx + c + k; m - k]) R' []
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_c3loop_k ->
     3 <= k -> k <= m -> m - k <= 2 ->
     f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FC3TA (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FCOPY3B (zupd R l) M MD) T.
Proof.
  induction N as [|N IH]; intros cx M1 R l M MD T wi c m v1 v3 v7 v28 fo CX Hh HR HQ
    Hm1 Hm2 Hwi1 Hwi2 Hc1 Hc2 HL Rfo HAG K; [lia|].
  open_q HQ. dand HQ as (Lra & La4 & Ls10).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. prep_copy CX HR HL. unfold cregs, f_const, f_live, FPW, L_FCOPY3B, L_FC3TA in K, IH |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  pose proof (Rfw wi ltac:(lia)) as Rb0. pose proof (Rfw (wi + 1) ltac:(lia)) as Rb1. pose proof (Rfw (wi + 2) ltac:(lia)) as Rb2.
  zrebase.
  pose proof (zfupd_byte fo c (fw wi) 0 osz Rfo Rb0) as Rfo1.
  pose proof (zfupd_byte _ (c + 1) (fw (wi + 1)) 0 osz Rfo1 Rb1) as Rfo2.
  pose proof (zfupd_byte _ (c + 2) (fw (wi + 2)) 0 osz Rfo2 Rb2) as Rfo3.
  (* three array loads and three array stores: each is the handed-in call of a run; then ONE RUN to the
     loop's exit test *)
  zuntil0 Rfd (idtac; tld1 Hwin wi Rfw).
  zuntil0 Rfd (idtac; tstore_arr Rfd HOB c).
  zuntil0 Rfd (idtac; tld1 Hwin (wi + 1) Rfw).
  zuntil0 Rfd (idtac; tstore_arr Rfd HOB (c + 1)).
  zuntil0 Rfd (idtac; tld1 Hwin (wi + 2) Rfw).
  zuntil0 Rfd (idtac; tstore_arr Rfd HOB (c + 2)).
  zto_branch Rfd.
  destruct (Z_lt_dec 2 (m - 3)) as [Hgo|Hstop].
  - (* THE BACK EDGE: ONE RUN to the loop's head, where the induction hypothesis applies *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH _ M1 Rx [] Mx MD T (wi + 3) (c + 3) (m - 3) v1 v3 v7 v28 _ CX' Hh) end).
    all: try (fcx_cbn; kfin).
    intros R' M' fo' k HR' HQ' Hk1 Hk2 Hk3 HL' Rfo'' HAG'; fcx_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K R' M' fo' (k + 3)) end; kfin.
  - (* ONE RUN to the continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx _ 3) end); kfin.
Qed.

Lemma fast_c3loop_o {RCa1 : RunCtx}  : forall (N : nat) cx M1 R l M MD T (s c m v1 v3 v7 v28 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 v28 R l ->
  rholds (qargs [f_ob cx + s; f_ob cx + c; m]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_c3loop ->
  3 <= m -> m <= Z.of_nat N -> 0 <= s -> s + 1 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R' M' (fo' : Z -> Z) (k : Z),
     cregs cx v1 v3 v7 v28 R' [] ->
     rholds (qargs [f_ob cx + s + k; f_ob cx + s + k; f_ob cx + c + k; f_ob cx + c + k; m - k]) R' []
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_c3loop_k ->
     3 <= k -> k <= m -> m - k <= 2 ->
     f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FC3TA (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FCOPY3B (zupd R l) M MD) T.
Proof.
  induction N as [|N IH]; intros cx M1 R l M MD T s c m v1 v3 v7 v28 fo CX Hh HR HQ
    Hm1 Hm2 Hs1 Hs2 Hc2 HL Rfo HAG K; [lia|].
  open_q HQ. dand HQ as (Lra & La4 & Ls10).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. prep_copy CX HR HL. unfold cregs, f_const, f_live, FPW, L_FCOPY3B, L_FC3TA in K, IH |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  zrebase.
  pose proof (Rfo s ltac:(lia)) as Rb0.
  pose proof (zfupd_byte fo c (fo s) 0 osz Rfo Rb0) as Rfo1.
  pose proof (Rfo1 (s + 1) ltac:(lia)) as Rb1.
  pose proof (zfupd_byte _ (c + 1) _ 0 osz Rfo1 Rb1) as Rfo2.
  pose proof (Rfo2 (s + 2) ltac:(lia)) as Rb2.
  pose proof (zfupd_byte _ (c + 2) _ 0 osz Rfo2 Rb2) as Rfo3.
  (* three array loads and three array stores: each is the handed-in call of a run; then ONE RUN to the
     loop's exit test *)
  zuntil0 Rfd (idtac; tld1 HOB s Rfo).
  zuntil0 Rfd (idtac; tstore_arr Rfd HOB c).
  zuntil0 Rfd (idtac; tld1 HOB (s + 1) Rfo1).
  zuntil0 Rfd (idtac; tstore_arr Rfd HOB (c + 1)).
  zuntil0 Rfd (idtac; tld1 HOB (s + 2) Rfo2).
  zuntil0 Rfd (idtac; tstore_arr Rfd HOB (c + 2)).
  zto_branch Rfd.
  destruct (Z_lt_dec 2 (m - 3)) as [Hgo|Hstop].
  - (* THE BACK EDGE: ONE RUN to the loop's head, where the induction hypothesis applies *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH _ M1 Rx [] Mx MD T (s + 3) (c + 3) (m - 3) v1 v3 v7 v28 _ CX' Hh) end).
    all: try (fcx_cbn; kfin).
    intros R' M' fo' k HR' HQ' Hk1 Hk2 Hk3 HL' Rfo'' HAG'; fcx_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K R' M' fo' (k + 3)) end; kfin.
  - (* ONE RUN to the continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx _ 3) end); kfin.
Qed.

Lemma fast_c3tail_w {RCa1 : RunCtx}  : forall cx M1 R l M MD T (wi c m v1 v3 v7 v28 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 v28 R l ->
  rholds (qargs [f_w cx + wi; f_ob cx + c; m]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_c3tail ->
  1 <= m -> m <= 2 -> 0 <= wi -> wi + m <= f_wn cx -> 0 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 v28 (c + m) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FC3T1 (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T wi c m v1 v3 v7 v28 fo CX Hh HR HQ Hm1 Hm2 Hwi1 Hwi2 Hc1 Hc2 HL Rfo HAG K.
  open_q HQ. dand HQ as (Ls9 & Lt2 & Ls10).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. unfold KL, cregs, f_const, f_live, FPW, L_FC3T1, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  pose proof (Rfw wi ltac:(lia)) as Rb0.
  zrebase.
  pose proof (zfupd_byte fo c (fw wi) 0 osz Rfo Rb0) as Rfo1.
  (* the array load and the array store are the handed-in calls of two runs *)
  zuntil0 Rfd (idtac; tld1 Hwin wi Rfw).
  zuntil0 Rfd (idtac; tstore_arr Rfd HOB c).
  destruct (Z.eq_dec m 2) as [E2|N2].
  - pose proof (Rfw (wi + 1) ltac:(lia)) as Rb1.
    pose proof (zfupd_byte _ (c + 1) (fw (wi + 1)) 0 osz Rfo1 Rb1) as Rfo2.
    (* one more array load and array store, each the handed-in call of a run; then ONE RUN to the continuation *)
    zuntil Rfd (idtac; tld1 Hwin (wi + 1) Rfw).
    zuntil0 Rfd (idtac; tstore_arr Rfd HOB (c + 1)).
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end); kfin.
  - (* ONE RUN to the continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end); kfin.
Qed.

Lemma fast_c3tail_o {RCa1 : RunCtx}  : forall cx M1 R l M MD T (s c m v1 v3 v7 v28 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 v28 R l ->
  rholds (qargs [f_ob cx + s; f_ob cx + c; m]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_c3tail ->
  1 <= m -> m <= 2 -> 0 <= s -> s + 1 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 v28 (c + m) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FC3T1 (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T s c m v1 v3 v7 v28 fo CX Hh HR HQ Hm1 Hm2 Hs1 Hs2 Hc2 HL Rfo HAG K.
  open_q HQ. dand HQ as (Ls9 & Lt2 & Ls10).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. unfold KL, cregs, f_const, f_live, FPW, L_FC3T1, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  pose proof (Rfo s ltac:(lia)) as Rb0.
  zrebase.
  pose proof (zfupd_byte fo c (fo s) 0 osz Rfo Rb0) as Rfo1.
  (* the array load and the array store are the handed-in calls of two runs *)
  zuntil0 Rfd (idtac; tld1 HOB s Rfo).
  zuntil0 Rfd (idtac; tstore_arr Rfd HOB c).
  destruct (Z.eq_dec m 2) as [E2|N2].
  - pose proof (Rfo1 (s + 1) ltac:(lia)) as Rb1.
    pose proof (zfupd_byte _ (c + 1) _ 0 osz Rfo1 Rb1) as Rfo2.
    (* one more array load and array store, each the handed-in call of a run; then ONE RUN to the continuation *)
    zuntil Rfd (idtac; tld1 HOB (s + 1) Rfo1).
    zuntil0 Rfd (idtac; tstore_arr Rfd HOB (c + 1)).
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end); kfin.
  - (* ONE RUN to the continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end); kfin.
Qed.

End S_Fast4.

Module S_Fast5.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import S_Fast1 S_Fast2 S_Fast4.
Import ListNotations.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* THE PLACES OF THIS HALF ARE FIELDS OF THE LAYOUT TEXT; here they have their short names only *)
Local Notation L_FC3TA := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FC3TA (only parsing).
Local Notation L_FWLOOP2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWLOOP2 (only parsing).
Local Notation L_FWL_WR := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_WR (only parsing).
Local Notation L_FWL_WR_X := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_WR_X (only parsing).
Local Notation L_FWL_W0 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_W0 (only parsing).
Local Notation L_FWL_W0_X := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_W0_X (only parsing).
Local Notation L_FWL_CT := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_CT (only parsing).
Local Notation L_FWL_CT_X := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWL_CT_X (only parsing).
Local Notation L_FWLOOP2_X := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWLOOP2_X (only parsing).
Local Notation L_FW0 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FW0 (only parsing).
Local Notation L_FCONTIG := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FCONTIG (only parsing).
Local Notation L_FWRAP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FWRAP (only parsing).
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation qargs := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs (only parsing).

(* which of the three loop places a caller means: found by the labels themselves, none is written *)
Local Ltac zbf_way :=
  first [ left; split; reflexivity | right; left; split; reflexivity | right; right; split; reflexivity ].

Lemma fast_copy3_w {RCa1 : RunCtx}  : forall cx M1 R l M MD T (wi c m v1 v3 v7 v28 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 v28 R l ->
  rholds (qargs [f_w cx + wi; f_ob cx + c; m]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_copy3w ->
  0 <= m -> m <= 258 -> 0 <= wi -> wi + m <= f_wn cx -> 0 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 v28 (c + m) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FCOPY3 (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T wi c m v1 v3 v7 v28 fo CX Hh HR HQ Hm1 Hm2 Hwi1 Hwi2 Hc1 Hc2 HL Rfo HAG K.
  open_q HQ. dand HQ as (Lra & La4 & Ls10).
  pose proof CX as CX'. pose proof HR as HR'. pose proof HL as HL'.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. unfold KL, cregs, f_const, f_live, FPW, L_FCOPY3, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  clear Wu Wp Wob Hwin HOB.
  (* ONE RUN to the test of the length *)
  zto_branch Rfd.
  destruct (Z_lt_dec m 3) as [Hlt|Hge].
  - (* ONE RUN to the next test *)
    zto_branch Rfd.
    destruct (Z.eq_dec m 0) as [E0|N0].
    + (* ONE RUN to the continuation *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx fo) end); kfin.
    + (* ONE RUN to the tail's lemma *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (fast_c3tail_w _ M1 Rx lx Mx MD T wi c m v1 v3 v7 v28 fo CX' Hh) end).
      all: try (unfold cregs, f_const; fcx_cbn; kfin). all: exact K.
  - (* ONE RUN to the loop's lemma *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_c3loop_w (Z.to_nat m) _ M1 Rx lx Mx MD T wi c m v1 v3 v7 v28 fo CX' Hh) end).
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
    intros R' M' fo' k HR2 HQk Hk1 Hk2 Hk3 HL2 Rfo' HAG'. fcx_cbn. open_q HQk. dand HQk as (Lra' & Ls9' & La4' & Lt2' & Ls10').
    pose proof HR2 as HR3. dand HR2 as (HC2 & HQ2). open_q HQ2. dand HQ2 as (La1' & La3' & La7' & Ls11'). unfold f_const in HC2. fcx_cbn. destr_conj HC2.
    unfold L_FC3TA. zkeys. zgetl0.
    destruct (Z.eq_dec (m - k) 0) as [E0|N0].
    + (* ONE RUN to the continuation *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx fo') end).
      all: try (unfold cregs, f_const; fcx_cbn; kfin).
    + (* ONE RUN to the tail's lemma *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (fast_c3tail_w _ M1 Rx lx Mx MD T (wi + k) (c + k) (m - k) v1 v3 v7 v28 fo' CX' Hh) end).
      all: try (unfold cregs, f_const; fcx_cbn; kfin).
      all: replace (c + k + (m - k)) with (c + m) by lia; exact K.
Qed.

Lemma fast_copy3_o {RCa1 : RunCtx}  : forall cx M1 R l M MD T (c m v1 v3 v7 dist : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 dist R l ->
  rholds (qargs [f_ob cx + c; m]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_fromout ->
  0 <= m -> m <= 258 -> 1 <= dist -> dist <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 dist (c + m) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FFROMOUT (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T c m v1 v3 v7 dist fo CX Hh HR HQ Hm1 Hm2 Hd1 Hd2 Hc2 HL Rfo HAG K.
  open_q HQ. dand HQ as (La4 & Ls10).
  pose proof CX as CX'. pose proof HL as HL'.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. unfold KL, cregs, f_const, f_live, FPW, L_FFROMOUT, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  clear Wu Wp Wob Hwin HOB.
  (* ONE RUN to the test of the length *)
  zto_branch Rfd.
  destruct (Z_lt_dec m 3) as [Hlt|Hge].
  - (* ONE RUN to the next test *)
    zto_branch Rfd.
    destruct (Z.eq_dec m 0) as [E0|N0].
    + (* ONE RUN to the continuation *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx fo) end); kfin.
    + (* ONE RUN to the tail's lemma *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (fast_c3tail_o _ M1 Rx lx Mx MD T (c - dist) c m v1 v3 v7 dist fo CX' Hh) end).
      all: try (unfold cregs, f_const; fcx_cbn; kfin). all: exact K.
  - (* ONE RUN to the loop's lemma *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_c3loop_o (Z.to_nat m) _ M1 Rx lx Mx MD T (c - dist) c m v1 v3 v7 dist fo CX' Hh) end).
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
    intros R' M' fo' k HR2 HQk Hk1 Hk2 Hk3 HL2 Rfo' HAG'. fcx_cbn. open_q HQk. dand HQk as (Lra' & Ls9' & La4' & Lt2' & Ls10').
    pose proof HR2 as HR3. dand HR2 as (HC2 & HQ2). open_q HQ2. dand HQ2 as (La1' & La3' & La7' & Ls11'). unfold f_const in HC2. fcx_cbn. destr_conj HC2.
    unfold L_FC3TA. zkeys. zgetl0.
    destruct (Z.eq_dec (m - k) 0) as [E0|N0].
    + (* ONE RUN to the continuation *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx fo') end).
      all: try (unfold cregs, f_const; fcx_cbn; kfin).
    + (* ONE RUN to the tail's lemma *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (fast_c3tail_o _ M1 Rx lx Mx MD T (c - dist + k) (c + k) (m - k) v1 v3 v7 dist fo' CX' Hh) end).
      all: try (unfold cregs, f_const; fcx_cbn; kfin).
      all: replace (c + k + (m - k)) with (c + m) by lia; exact K.
Qed.

Lemma fast_fromwin {RCa1 : RunCtx}  : forall cx M1 R l M MD T (c m v1 v3 v7 v28 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 v28 R l ->
  rholds (qargs [f_ob cx + c; m]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_fromwin ->
  0 <= m -> m <= 258 -> m <= f_wn cx -> 0 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 v28 (c + m) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FFROMWIN (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T c m v1 v3 v7 v28 fo CX Hh HR HQ Hm1 Hm2 Hm3 Hc1 Hc2 HL Rfo HAG K.
  open_q HQ. dand HQ as (La4 & Ls10).
  pose proof CX as CX'. pose proof HL as HL'.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. unfold KL, cregs, f_const, f_live, FPW, L_FFROMWIN, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  clear Wu Wp Wob Hwin HOB.
  (* ONE RUN to the test of the length *)
  zto_branch Rfd.
  destruct (Z_lt_dec m 3) as [Hlt|Hge].
  - (* ONE RUN to the next test *)
    zto_branch Rfd.
    destruct (Z.eq_dec m 0) as [E0|N0].
    + (* ONE RUN to the continuation *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx fo) end); kfin.
    + (* ONE RUN to the tail's lemma *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (fast_c3tail_w _ M1 Rx lx Mx MD T 0 c m v1 v3 v7 v28 fo CX' Hh) end).
      all: try (unfold cregs, f_const; fcx_cbn; kfin). all: exact K.
  - (* ONE RUN to the loop's lemma *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_c3loop_w (Z.to_nat m) _ M1 Rx lx Mx MD T 0 c m v1 v3 v7 v28 fo CX' Hh) end).
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
    intros R' M' fo' k HR2 HQk Hk1 Hk2 Hk3 HL2 Rfo' HAG'. fcx_cbn. open_q HQk. dand HQk as (Lra' & Ls9' & La4' & Lt2' & Ls10').
    pose proof HR2 as HR3. dand HR2 as (HC2 & HQ2). open_q HQ2. dand HQ2 as (La1' & La3' & La7' & Ls11'). unfold f_const in HC2. fcx_cbn. destr_conj HC2.
    unfold L_FC3TA. zkeys. zgetl0.
    destruct (Z.eq_dec (m - k) 0) as [E0|N0].
    + (* ONE RUN to the continuation *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx fo') end).
      all: try (unfold cregs, f_const; fcx_cbn; kfin).
    + (* ONE RUN to the tail's lemma *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (fast_c3tail_w _ M1 Rx lx Mx MD T (0 + k) (c + k) (m - k) v1 v3 v7 v28 fo' CX' Hh) end).
      all: try (unfold cregs, f_const; fcx_cbn; kfin).
      all: replace (c + k + (m - k)) with (c + m) by lia; exact K.
Qed.

Lemma fast_w0 {RCa1 : RunCtx}  : forall cx M1 R l M MD T (co len dist op v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 dist R l ->
  rholds (qargs [f_ob cx + co; len; op]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_w0 ->
  3 <= len -> len <= 258 -> 0 <= co -> co + len <= f_osz cx -> f_bo cx <= co ->
  op = dist - (co - f_bo cx) -> 1 <= op -> op <= f_whave cx -> dist <= 32768 ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 dist (co + len) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FW0 (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T co len dist op v1 v3 v7 fo CX Hh HR HQ Hl1 Hl2 Hco1 Hco2 Hbo Hop Hop1 Hop2 Hd HL Rfo HAG K.
  open_q HQ. dand HQ as (La4 & Ls10 & Lt2).
  pose proof CX as CX'. pose proof HL as HL'.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. unfold KL, cregs, f_const, f_live, FPW, L_FLATCH, L_FW0 in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  clear Wu Wp Wob Hwin HOB.
  (* the value equation of this stretch's value replacement (the kit's own lemma): stated before the run *)
  pose proof (zext32_shift (wn - op) ltac:(lia)) as Hzx.
  (* ONE RUN to the test of the two lengths *)
  zto_branch Rfd.
  destruct (Z_lt_dec op len) as [Hlt|Hge].
  - (* ONE RUN to the loop's lemma *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_wloop L_FWL_W0 L_FWL_W0_X ltac:(zbf_way) (Z.to_nat op) _ M1 Rx lx Mx MD T (wn - op) co op v1 v3 v7 op len dist fo CX' Hh) end).
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
    intros R' M' fo' HR2 HQk HL2 Rfo' HAG'. fcx_cbn. open_q HQk. dand HQk as (Lt2' & Ls10' & Lra' & La4').
    pose proof HR2 as HR3. dand HR2 as (HC2 & HQ2). open_q HQ2. dand HQ2 as (La1' & La3' & La7' & Ls11'). unfold f_const in HC2. fcx_cbn. destr_conj HC2.
    zkeys. zgetl0. zpc_norm.
    (* ONE RUN to the next copy's lemma *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_copy3_o _ M1 Rx lx Mx MD T (co + op) (len - op) v1 v3 v7 dist fo' CX' Hh) end).
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
    all: replace (co + op + (len - op)) with (co + len) by lia; exact K.
  - (* ONE RUN to the copy's lemma *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_copy3_w _ M1 Rx lx Mx MD T (wn - op) co len v1 v3 v7 dist fo CX' Hh) end).
    all: try (unfold cregs, f_const; fcx_cbn; kfin). all: exact K.
Qed.

Lemma fast_contig {RCa1 : RunCtx}  : forall cx M1 R l M MD T (co len dist op v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 dist R l ->
  rholds (qargs [f_ob cx + co; len; op]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_contig ->
  3 <= len -> len <= 258 -> 0 <= co -> co + len <= f_osz cx -> f_bo cx <= co ->
  op = dist - (co - f_bo cx) -> 1 <= op -> op <= f_whave cx -> op <= f_wnext cx -> dist <= 32768 ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 dist (co + len) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FCONTIG (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T co len dist op v1 v3 v7 fo CX Hh HR HQ Hl1 Hl2 Hco1 Hco2 Hbo Hop Hop1 Hop2 Hop3 Hd HL Rfo HAG K.
  open_q HQ. dand HQ as (La4 & Ls10 & Lt2).
  pose proof CX as CX'. pose proof HL as HL'.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. unfold KL, cregs, f_const, f_live, FPW, L_FLATCH, L_FCONTIG in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  clear Wu Wp Wob Hwin HOB.
  (* the value equation of this stretch's value replacement (the kit's own lemma): stated before the run *)
  pose proof (zext32_shift (wnext - op) ltac:(lia)) as Hzx.
  (* ONE RUN to the test of the two lengths *)
  zto_branch Rfd.
  destruct (Z_lt_dec op len) as [Hlt|Hge].
  - (* ONE RUN to the loop's lemma *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_wloop L_FWL_CT L_FWL_CT_X ltac:(zbf_way) (Z.to_nat op) _ M1 Rx lx Mx MD T (wnext - op) co op v1 v3 v7 op len dist fo CX' Hh) end).
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
    intros R' M' fo' HR2 HQk HL2 Rfo' HAG'. fcx_cbn. open_q HQk. dand HQk as (Lt2' & Ls10' & Lra' & La4').
    pose proof HR2 as HR3. dand HR2 as (HC2 & HQ2). open_q HQ2. dand HQ2 as (La1' & La3' & La7' & Ls11'). unfold f_const in HC2. fcx_cbn. destr_conj HC2.
    zkeys. zgetl0. zpc_norm.
    (* ONE RUN to the next copy's lemma *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_copy3_o _ M1 Rx lx Mx MD T (co + op) (len - op) v1 v3 v7 dist fo' CX' Hh) end).
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
    all: replace (co + op + (len - op)) with (co + len) by lia; exact K.
  - (* ONE RUN to the copy's lemma *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_copy3_w _ M1 Rx lx Mx MD T (wnext - op) co len v1 v3 v7 dist fo CX' Hh) end).
    all: try (unfold cregs, f_const; fcx_cbn; kfin). all: exact K.
Qed.

Lemma fast_wrap {RCa1 : RunCtx}  : forall cx M1 R l M MD T (co len dist op v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 dist R l ->
  rholds (qargs [f_ob cx + co; len; op]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_wrap ->
  3 <= len -> len <= 258 -> 0 <= co -> co + len <= f_osz cx -> f_bo cx <= co ->
  op = dist - (co - f_bo cx) -> 1 <= op -> op <= f_whave cx -> 0 < f_wnext cx -> f_wnext cx < op -> dist <= 32768 ->
  f_ro cx M -> f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 dist (co + len) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FWRAP (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T co len dist op v1 v3 v7 fo CX Hh HR HQ Hl1 Hl2 Hco1 Hco2 Hbo Hop Hop1 Hop2 Hwn1 Hwn2 Hd
         HRO HL Rfo HAG K.
  open_q HQ. dand HQ as (La4 & Ls10 & Lt2).
  pose proof CX as CX'. pose proof HL as HL'.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. open_ro HRO. unfold KL, cregs, f_const, f_live, FPW, L_FLATCH, L_FWRAP in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Rfin.
  clear Wu Wp Wob Hwin HOB Hin HtL HtD Hsane.
  assert (Es8 : s8v = w + wnext) by (unfold ZSEP in Cs8; destruct Cs8; [lia | assumption]). clear Cs8.
  (* the value equation of this stretch's value replacement (the kit's own lemma): stated before the run *)
  pose proof (zext32_shift (wn + wnext - op) ltac:(lia)) as Hzx.
  (* ONE RUN to the test of the two lengths *)
  zto_branch Rfd.
  destruct (Z_lt_dec (op - wnext) len) as [Hlt|Hge].
  - (* ONE RUN to the loop's lemma *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_wloop L_FWL_WR L_FWL_WR_X ltac:(zbf_way) (Z.to_nat op) _ M1 Rx lx Mx MD T (wn + wnext - op) co (op - wnext)
                v1 v3 v7 (op - wnext) len dist fo CX' Hh) end).
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
    intros R' M' fo' HR2 HQk HL2 Rfo' HAG'. fcx_cbn. open_q HQk. dand HQk as (Lt2' & Ls10' & Lra' & La4').
    pose proof HR2 as HR3. dand HR2 as (HC2 & HQ2). open_q HQ2. dand HQ2 as (La1' & La3' & La7' & Ls11'). unfold f_const in HC2. fcx_cbn. destr_conj HC2.
    zkeys. zgetl0. zpc_norm.
    (* ONE RUN to the next test *)
    zto_branch Rfd.
    destruct (Z_le_dec (len - (op - wnext)) wnext) as [Hle|Hgt].
    + (* ONE RUN to the next copy's lemma *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (fast_fromwin _ M1 Rx lx Mx MD T (co + (op - wnext)) (len - (op - wnext)) v1 v3 v7 dist fo' CX' Hh) end).
      all: try (unfold cregs, f_const; fcx_cbn; kfin).
      all: replace (co + (op - wnext) + (len - (op - wnext))) with (co + len) by lia; exact K.
    + pose proof HL2 as HL3. unfold f_live in HL3.
      (* ONE RUN to the second loop's lemma *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (fast_wloop2 (Z.to_nat wnext) _ M1 Rx lx Mx MD T 0 (co + (op - wnext)) v1 v3 v7 (len - (op - wnext)) dist fo' CX' Hh) end).
      all: try (unfold cregs, f_const; fcx_cbn; kfin).
      intros R'' M'' fo'' HR4 HQ4 HL4 Rfo'' HAG''. fcx_cbn. open_q HQ4. dand HQ4 as (Ls10'' & Lt2'' & La4'').
      pose proof HR4 as HR5. dand HR4 as (HC4 & HQ5). open_q HQ5. dand HQ5 as (La1'' & La3'' & La7'' & Ls11''). unfold f_const in HC4. fcx_cbn. destr_conj HC4.
      unfold L_FWLOOP2_X. zkeys. zgetl0. zpc_norm.
      (* ONE RUN to the last copy's lemma *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (fast_copy3_o _ M1 Rx lx Mx MD T (co + op) (len - op) v1 v3 v7 dist fo'' CX' Hh) end).
      all: try (unfold cregs, f_const; fcx_cbn; kfin).
      all: replace (co + op + (len - op)) with (co + len) by lia; exact K.
  - (* ONE RUN to the copy's lemma *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_copy3_w _ M1 Rx lx Mx MD T (wn + wnext - op) co len v1 v3 v7 dist fo CX' Hh) end).
    all: try (unfold cregs, f_const; fcx_cbn; kfin). all: exact K.
Qed.

Lemma fast_win {RCa1 : RunCtx}  : forall cx M1 R l M MD T (co len dist v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 dist R l ->
  rholds (qargs [f_ob cx + co; len]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_win ->
  3 <= len -> len <= 258 -> 0 <= co -> co + len <= f_osz cx -> f_bo cx <= co ->
  co - f_bo cx < dist -> 1 <= dist -> dist <= 32768 ->
  f_ro cx M -> f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R', cregs cx v1 v3 v7 dist R' [] ->
     rholds (qargs [f_ob cx + co]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_toofar ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FTOOFAR (zupd R' []) M MD) T) ->
  KL cx M1 MD T v1 v3 v7 dist (co + len) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FWIN (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T co len dist v1 v3 v7 fo CX Hh HR HQ Hl1 Hl2 Hco1 Hco2 Hbo Hd0 Hd1 Hd2 HRO HL Rfo HAG KTF K.
  open_q HQ. dand HQ as (La4 & Ls10).
  pose proof CX as CX'. pose proof HL as HL'. pose proof HRO as HRO'.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. open_ro HRO. unfold KL, cregs, f_const, f_live, FPW, L_FWIN, L_FTOOFAR in K, KTF |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  clear Wu Wp Wob Hwin HOB Hin HtL HtD Hsp0.
  (* ONE RUN to the test of the distance *)
  zto_branch Rfd.
  destruct (Z_lt_dec whave (dist - (co - bo))) as [Hfar|Hok].
  - (* ONE RUN to the far place's continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KTF Rx) end).
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
  - clear Hsane KTF.
    (* ONE RUN to the next test *)
    zto_branch Rfd.
    destruct (Z.eq_dec wnext 0) as [Ew0|Nw0].
    + (* ONE RUN to the first case's lemma *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (fast_w0 _ M1 Rx lx Mx MD T co len dist (dist - (co - bo)) v1 v3 v7 fo CX' Hh) end).
      all: try (unfold cregs, f_const; fcx_cbn; kfin). all: exact K.
    + (* ONE RUN to the next test *)
      zto_branch Rfd.
      destruct (Z_le_dec (dist - (co - bo)) wnext) as [Hc|Hw].
      * (* ONE RUN to the second case's lemma *)
        zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (fast_contig _ M1 Rx lx Mx MD T co len dist (dist - (co - bo)) v1 v3 v7 fo CX' Hh) end).
        all: try (unfold cregs, f_const; fcx_cbn; kfin). all: exact K.
      * (* ONE RUN to the third case's lemma *)
        zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (fast_wrap _ M1 Rx lx Mx MD T co len dist (dist - (co - bo)) v1 v3 v7 fo CX' Hh) end).
        all: try (unfold cregs, f_const; fcx_cbn; kfin). all: try exact K. all: exact HRO'.
Qed.
End S_Fast5.

Module S_Fast6.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import S_Fast1 S_Fast2 S_Fast4.
Import ListNotations.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.


(* THE PLACES OF THIS HALF ARE FIELDS OF THE LAYOUT TEXT; here they have their short names only *)
Local Notation L_FDLOOP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FDLOOP (only parsing).
Local Notation L_FDTAIL := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FDTAIL (only parsing).
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation qargs := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs (only parsing).

Lemma fast_dloop {RCa1 : RunCtx}  : forall (N : nat) cx M1 R l M MD T (c m v1 v3 v7 dist : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 dist R l ->
  rholds (qargs [f_ob cx + c + 2; m; 1 - dist]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_dloop ->
  3 <= m -> m <= Z.of_nat N -> 1 <= dist -> dist <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R' M' (fo' : Z -> Z) (k : Z),
     cregs cx v1 v3 v7 dist R' [] ->
     rholds (qargs [f_ob cx + c + k + 2; m - k; 1 - dist]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_dloop_k ->
     3 <= k -> k <= m -> m - k <= 2 ->
     f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDTAIL (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDLOOP (zupd R l) M MD) T.
Proof.
  induction N as [|N IH]; intros cx M1 R l M MD T c m v1 v3 v7 dist fo CX Hh HR HQ
    Hm1 Hm2 Hd1 Hd2 Hc2 HL Rfo HAG K; [lia|].
  open_q HQ. dand HQ as (La4 & Ls10 & Lt2).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. prep_copy CX HR HL. unfold cregs, f_const, f_live, FPW, L_FDLOOP, L_FDTAIL in K, IH |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  zrebase.
  pose proof (Rfo (c - dist) ltac:(lia)) as Rb0.
  pose proof (zfupd_byte fo c (fo (c - dist)) 0 osz Rfo Rb0) as Rfo1.
  pose proof (Rfo1 (c + 1 - dist) ltac:(lia)) as Rb1.
  pose proof (zfupd_byte _ (c + 1) _ 0 osz Rfo1 Rb1) as Rfo2.
  pose proof (Rfo2 (c + 2 - dist) ltac:(lia)) as Rb2.
  pose proof (zfupd_byte _ (c + 2) _ 0 osz Rfo2 Rb2) as Rfo3.
  (* three array loads and three array stores: each is the handed-in call of a run; then ONE RUN to the
     loop's exit test *)
  zuntil0 Rfd (idtac; tld1 HOB (c - dist) Rfo).
  zuntil0 Rfd (idtac; tstore_arr Rfd HOB c).
  zuntil0 Rfd (idtac; tld1 HOB (c + 1 - dist) Rfo1).
  zuntil0 Rfd (idtac; tstore_arr Rfd HOB (c + 1)).
  zuntil0 Rfd (idtac; tld1 HOB (c + 2 - dist) Rfo2).
  zuntil0 Rfd (idtac; tstore_arr Rfd HOB (c + 2)).
  zto_branch Rfd.
  destruct (Z_lt_dec 2 (m - 3)) as [Hgo|Hstop].
  - (* THE BACK EDGE: ONE RUN to the loop's head, where the induction hypothesis applies *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH _ M1 Rx [] Mx MD T (c + 3) (m - 3) v1 v3 v7 dist _ CX' Hh) end).
    all: try (fcx_cbn; kfin).
    intros R' M' fo' k HR' HQ' Hk1 Hk2 Hk3 HL' Rfo'' HAG'; fcx_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K R' M' fo' (k + 3)) end; kfin.
  - (* ONE RUN to the continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx _ 3) end); kfin.
Qed.

Lemma fast_dtail {RCa1 : RunCtx}  : forall cx M1 R l M MD T (c m v1 v3 v7 dist : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 dist R l ->
  rholds (qargs [f_ob cx + c + 2; m]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_dtail ->
  0 <= m -> m <= 2 -> 1 <= dist -> dist <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 dist (c + m) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDTAIL (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T c m v1 v3 v7 dist fo CX Hh HR HQ Hm1 Hm2 Hd1 Hd2 Hc2 HL Rfo HAG K.
  open_q HQ. dand HQ as (La4 & Ls10).
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. unfold KL, cregs, f_const, f_live, FPW, L_FDTAIL, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  zrebase.
  destruct (Z.eq_dec m 0) as [E0|N0].
  - (* ONE RUN to the continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx fo) end); kfin.
  - pose proof (Rfo (c - dist) ltac:(lia)) as Rb0.
    pose proof (zfupd_byte fo c (fo (c - dist)) 0 osz Rfo Rb0) as Rfo1.
    (* the array load and the array store are the handed-in calls of two runs *)
    zuntil0 Rfd (idtac; tld1 HOB (c - dist) Rfo).
    zuntil0 Rfd (idtac; tstore_arr Rfd HOB c).
    destruct (Z.eq_dec m 2) as [E2|N2].
    + pose proof (Rfo1 (c + 1 - dist) ltac:(lia)) as Rb1.
      pose proof (zfupd_byte _ (c + 1) _ 0 osz Rfo1 Rb1) as Rfo2.
      (* the value equation of this stretch's value replacement (the kit's own lemma): stated before the run *)
      pose proof (lxor_m1 dist) as Hlx.
      (* one more array load and array store, each the handed-in call of a run; then ONE RUN to the continuation *)
      zuntil0 Rfd (idtac; tld1 HOB (c + 1 - dist) Rfo1).
      zuntil0 Rfd (idtac; tstore_arr Rfd HOB (c + 1)).
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end); kfin.
    + (* ONE RUN to the continuation *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end); kfin.
Qed.

Lemma fast_direct {RCa1 : RunCtx}  : forall cx M1 R l M MD T (co len dist v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 dist R l ->
  rholds (qargs [f_ob cx + co; len]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_direct ->
  3 <= len -> len <= 258 -> 0 <= co -> co + len <= f_osz cx ->
  1 <= dist -> dist <= co ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 dist (co + len) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDIRECT (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T co len dist v1 v3 v7 fo CX Hh HR HQ Hl1 Hl2 Hco1 Hco2 Hd1 Hd2 HL Rfo HAG K.
  open_q HQ. dand HQ as (La4 & Ls10).
  pose proof CX as CX'. pose proof HL as HL'.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. unfold KL, cregs, f_const, f_live, FPW, L_FDIRECT, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin.
  clear Wu Wp Wob Hwin HOB.
  (* ONE RUN to the loop's lemma *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (fast_dloop (Z.to_nat len) _ M1 Rx lx Mx MD T co len v1 v3 v7 dist fo CX' Hh) end).
  all: try (unfold cregs, f_const; fcx_cbn; kfin).
  intros R' M' fo' k HR2 HQk Hk1 Hk2 Hk3 HL2 Rfo' HAG'. fcx_cbn.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (fast_dtail _ M1 Rx lx Mx MD T (co + k) (len - k) v1 v3 v7 dist fo' CX' Hh) end.
  all: try (unfold cregs, f_const; fcx_cbn; kfin).
  all: replace (co + k + (len - k)) with (co + len) by lia; exact K.
Qed.
End S_Fast6.

Module S_Fast7.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import S_Fast1 S_Fast2 S_Fast3 S_Fast4 S_Fast5 S_Fast6.
Import ListNotations.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.



(* the meaning words of the list form, by their short names *)
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation qargs := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs (only parsing).
Ltac xpre_tac :=
  unfold XPRE, fW; unfold fW in *; split_conj;
  first [ assumption | zreg | lia
        | match goal with H : f_const _ _ _ |- _ => let H' := fresh in pose proof H as H'; unfold f_const in H'; destr_conj H'; first [assumption | zreg] end ].

Lemma fast_body {RCa1 : RunCtx}  : forall cx M1 R l M MD T (ci co hold bits : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> rholds (qargs [hold; f_q cx + ci; f_ob cx + co; bits]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_head ->
  0 <= ci -> ci + 6 <= f_n cx -> f_cout0 cx <= co -> co + 258 <= f_osz cx -> 0 <= bits -> bits <= 40 -> bits <= 8 * ci ->
  0 <= hold -> hold < 2 ^ bits -> fW cx ci bits co <= f_W0 cx -> fW cx ci bits (f_cout0 cx) <= f_W0 cx ->
  f_ro cx M1 -> f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KEXIT cx M1 MD T ->
  KLATCH cx M1 MD T (fW cx ci bits co) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FHEAD (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T ci co hold bits fo CX Hh HC HV0 Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hb3 Hh1 Hh2 HW HWI
         HRO1 HL Rfo HAG HEX HKL.
  pose proof (f_ro_now cx M1 M CX HRO1 HAG) as HRO.
  pose proof CX as CX'. unfold fcx_ok in CX'; cbv zeta in CX'; destr_conj CX'.
  pose proof HL as HL'. unfold f_live in HL'. dand HL' as (Wu & Wp & Wob & Hwin & HOB).
  unfold KLATCH, fW in HKL. unfold fW in HW, HWI.
  (* THE FRONT HALF's LEMMAS TAKE A PLACE's REGISTER FACTS AS ONE LIST FACT: a continuation's list fact is handed
     on as it stands where the next lemma's place has the same list; else it is opened and its parts named *)
  eapply (fast_head cx R l M MD T ci hold bits (f_ob cx + co) CX Hh HC HV0 HRO); try lia.
  intros R1 ci1 hold1 bits1 HC1 MV Hc1a Hc1b Hc1c Hb1a Hb1b Hb1c Hh1a Hh1b HA1.
  eapply (fast_declen cx R1 [] M MD T hold1 bits1 (f_q cx + ci1) (f_ob cx + co) CX Hh HC1 MV HRO); try lia.
  -
    intros R2 k hold2 bits2 HC2 NV Hk1 Hk2 Hb2a Hb2b Hb2c Hh2a Hh2b.
    eapply (fast_lit cx M1 R2 [] M MD T k co hold2 (f_q cx + ci1) bits2 fo CX Hh HC2 NV Hk1 Hk2); try lia; try assumption.
    intros R3 M3 fo3 HC3 OV HL3 Rfo3 HAG3. zbf_in OV. dand OV as (Oa1 & Oa3 & Oa4 & Oa7).
    eapply (HKL R3 M3 ci1 (co + 1) hold2 bits2 fo3); try assumption; try lia; try (split_conj; first [assumption | lia]).
  -
    intros R2 k hold2 bits2 HC2 NV Hk1 Hk2 Hop1 Hop2 Hv1 Hv2 Hb2a Hb2b Hb2c Hh2a Hh2b.
    eapply (fast_lenb cx R2 [] M MD T k ci1 hold2 bits2 (f_ob cx + co) CX Hh HC2 NV Hk1 Hk2 Hop1 Hop2 Hv1 Hv2 HRO); try lia.
    intros R3 ci3 hold3 bits3 len HC3 OV Hl1 Hl2 Hc3a Hc3b Hc3c Hb3a Hb3b Hb3c Hh3a Hh3b HA3a HA3b.
    eapply (fast_decdist cx R3 [] M MD T hold3 bits3 (f_q cx + ci3) (f_ob cx + co) len CX Hh HC3 OV HRO); try lia.
    +
      intros R4 k' hold4 bits4 HC4 PV Hk1' Hk2' Hop1' Hop2' Hv1' Hv2' Hb4a Hb4b Hb4c Hh4a Hh4b.
      eapply (fast_distb cx R4 [] M MD T k' ci3 co hold4 bits4 len CX Hh HC4 PV Hk1' Hk2' Hop1' Hop2' Hv1' Hv2' HRO); try lia.
      *
        intros R5 ci5 hold5 bits5 dist HC5 QV Hd1 Hd2 Hd3 Hc5a Hc5b Hc5c Hb5a Hb5b Hb5c Hh5a Hh5b HA5.
        zbf_in QV. dand QV as (Qa1 & Qa3 & Qa4 & Qa7 & Qs10 & Qs11).
        eapply (fast_direct cx M1 R5 [] M MD T co len dist hold5 (f_q cx + ci5) bits5 fo CX Hh); try lia; try assumption.
        { unfold cregs. kfin. } { kfin. }
        intros R6 M6 fo6 HR6 Sa4 HL6 Rfo6 HAG6. dand HR6 as (HC6 & HQ6). open_q HQ6. dand HQ6 as (Sa1 & Sa3 & Sa7 & Ss11). open_q Sa4.
        eapply (HKL R6 M6 ci5 (co + len) hold5 bits5 fo6); try assumption; try lia; try (split_conj; first [assumption | lia]).
      *
        intros R5 ci5 hold5 bits5 dist HC5 QV Hd1 Hd2 Hd3 Hc5a Hc5b Hc5c Hb5a Hb5b Hb5c Hh5a Hh5b HA5.
        zbf_in QV. dand QV as (Qa1 & Qa3 & Qa4 & Qa7 & Qs10 & Qs11).
        eapply (fast_win cx M1 R5 [] M MD T co len dist hold5 (f_q cx + ci5) bits5 fo CX Hh); try lia; try assumption.
        { unfold cregs. kfin. } { kfin. }
        {
          intros R6 HR6 Sa4. dand HR6 as (HC6 & HQ6). open_q HQ6. dand HQ6 as (Sa1 & Sa3 & Sa7 & Ss11). open_q Sa4.
          eapply (fast_toofar cx M1 MD T CX Hh HEX R6 [] M ci5 co hold5 bits5 fo). xpre_tac. }
        intros R6 M6 fo6 HR6 Sa4 HL6 Rfo6 HAG6. dand HR6 as (HC6 & HQ6). open_q HQ6. dand HQ6 as (Sa1 & Sa3 & Sa7 & Ss11). open_q Sa4.
        eapply (HKL R6 M6 ci5 (co + len) hold5 bits5 fo6); try assumption; try lia; try (split_conj; first [assumption | lia]).
    +
      intros R4 hold4 bits4 HC4 PV Hb4a Hb4b Hb4c Hh4a Hh4b.
      zbf_in PV. dand PV as (Pa1 & Pa3 & Pa4 & Pa7).
      eapply (fast_badd cx M1 MD T CX Hh HEX R4 [] M ci3 co hold4 bits4 fo). xpre_tac.
  -
    intros R2 op hold2 bits2 HC2 NV Hop1 Hop2 Hb2a Hb2b Hb2c Hh2a Hh2b.
    zbf_in NV. dand NV as (Na1 & Na3 & Na4 & Na7 & Ns9).
    eapply (fast_eob cx M1 MD T CX Hh HEX R2 [] M ci1 co hold2 bits2 fo op); [ xpre_tac | zbf_goal; exact Ns9 | lia ].
Qed.

Lemma fast_loop {RCa1 : RunCtx}  : forall (N : nat) cx M1 R l M MD T (ci co hold bits : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> rholds (qargs [hold; f_q cx + ci; f_ob cx + co; bits]) R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_head ->
  0 <= ci -> ci + 6 <= f_n cx -> f_cout0 cx <= co -> co + 258 <= f_osz cx -> 0 <= bits -> bits <= 40 -> bits <= 8 * ci ->
  0 <= hold -> hold < 2 ^ bits -> fW cx ci bits co <= f_W0 cx -> fW cx ci bits (f_cout0 cx) <= f_W0 cx -> fW cx ci bits co < Z.of_nat N ->
  f_ro cx M1 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (f_p cx + 8) LEN ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KEXIT cx M1 MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FHEAD (zupd R l) M MD) T.
Proof.
  induction N as [|N IH]; intros cx M1 R l M MD T ci co hold bits fo CX Hh HC HQ Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hb3
    Hh1 Hh2 HW HWI HWN HRO1 Hm8 HL Rfo HAG HEX; [unfold fW in HWN; lia|].
  eapply (fast_body cx M1 R l M MD T ci co hold bits fo CX Hh HC HQ); try assumption.
  intros R' M' ci' co' hold' bits' fo' HC' KV Hci1' Hci2' Hco1' Hco2' Hb1' Hb2' Hb3' Hh1' Hh2' HB' HW0' HWI' HL' Rfo' HAG'. dand KV as (Ka1 & Ka3 & Ka4 & Ka7).
  pose proof CX as CX'. unfold fcx_ok in CX'; cbv zeta in CX'; destr_conj CX'.
  pose proof HC' as HC''. unfold f_const in HC''. destr_conj HC''.
  unfold fW in *. unfold L_FLATCH, L_FHEAD in *. zkeys. zgetl0. pose proof two64_eq as TW64.
  (* the exit place: its machine facts are the layout's list at the values this proof holds *)
  assert (EXIT : forall RX, f_const cx RX [] ->
                 rholds (qargs [hold'; f_q cx + ci'; f_ob cx + co'; bits']) RX [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zbf_loopx ->
                 realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FEXIT (zupd RX []) M' MD) T).
  { intros RX GC GQ. open_q GQ. dand GQ as (G12 & G14 & G15 & G18). unfold f_const in GC. destr_conj GC.
    pose proof HL' as HL2. unfold f_live in HL2. dand HL2 as (Wu & Wp & Wob & Hwin & HOB).
    zderiveL HAG' Hm8 Hm8'.
    apply (framed_mpostL_weaken (run_segments R_segs rc_inp rc_sp rc_mb) M1 M' (FPW cx) (FP1 cx) ltac:(unfold FPW, FP1; ranges_within_tac)) in HAG'.
    unfold KEXIT, L_FEXIT in HEX. zkeys.
    eapply (HEX RX M' ci' co' hold' bits' LEN fo'); try assumption; try lia; try (split_conj; assumption). unfold PFOLD. left. reflexivity. }
  destruct (Z_lt_dec (f_q cx + ci') (f_q cx + f_n cx + -5)) as [Hin|Hnin].
  - destruct (Z_lt_dec (f_ob cx + co') (f_ob cx + f_osz cx + -257)) as [Hout|Hnout].
    + (* THE BACK EDGE: ONE RUN to the loop's head, where the induction hypothesis applies *)
      zuntil Rfd (idtac; eapply (IH cx M1 _ [] M' MD T ci' co' hold' bits' fo' CX Hh)); try assumption; try lia; kfin.
    + (* ONE RUN to the exit place *)
      zuntil Rfd (idtac; apply EXIT); kfin.
  - (* ONE RUN to the exit place *)
    zuntil Rfd (idtac; apply EXIT); kfin.
Qed.

(* THE LIST-FORM TWIN of the text's last theorem: the entry place and the frame's extent are the layout's
   fields. The hand statement, word for word, stands in the bridge text and is proved there from this one. *)
Theorem ifast_s_l {RCa1 : RunCtx}  : ifast_spec_at (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IFAST OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IF.
Proof.
  unfold ifast_spec_at. unfold OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IFAST, OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IF.
  intros Rb l M MD T u p q n ob osz w whave wnext cin cout hold bits out lb db la na da nd spi ret rhi zc rdL rdD fin fo fw.
  intros Hh La0 La1 Lsp Lra Hret1 Hret2.
  intros Cu1 Cu2 Cu3 Cu4 Cu5 Cu6 Cp1 Cp2 Cp3 Cq1 Cn1 Cn2 Cq2 Cob1 Cosz1 Cosz2 Cob2 Sobu Spob Spq Sobq Cw Swp Swq Swob
         Cla1 Cla2 Cda1 Cda2 Cla3 Cda3 Slaob Slap Sdaob Sdap Clb1 Clb2 Cdb1 Cdb2 TOKL TOKD
         Hci1 Hci2 Hci3 Hco1 Hco2 Hco3 Hb1 Hb2 Hh1 Hh2 Hb3 Hout1 Hout2 Hout3 Hwh1 Hwn1 Hw0 Hw1
         Wu Wp Wob Ww E8 E16 E32 E40 E64 P60 P64 P68 P72 P80 P88 P8 P104 P112 P120 P124 P7144 HtL HtD Hin Rfin HOB Rfo Hwin Rfw K.
  cbv [FRA STATE_SIZE WIN_SIZE] in Cu1, Cu4, Cp2, Cq2, Sobu, Spob, Spq, Cw, Swp, Swq, Swob, Cla2, Cda2, Hw1, Wu, Wp, Ww, P60, Hwin, Rfw.
  pose proof two64_eq as TW64.
  pose proof (tab_ok_root _ _ _ _ TOKL) as (_ & HnaL & _). pose proof (tab_ok_root _ _ _ _ TOKD) as (_ & HndD & _).
  pose proof (pow2_15 lb ltac:(lia)) as HPl. pose proof (pow2_15 db ltac:(lia)) as HPd.
  set (wn := if w =? 0 then 0 else 32768) in *.
  assert (Hwn : (w = 0 /\ wn = 0 /\ whave = 0 /\ wnext = 0) \/ (0 < w /\ w + 32768 <= zc /\ wn = 32768 /\ whave <= 32768 /\ wnext < 32768)).
  { idtac. subst wn. destruct (Z.eqb_spec w 0) as [E|NE].
    - left. destruct (Hw0 E). lia.
    - right. dand (Hw1 NE) as (A & B & _). destruct Cw as [|(C1 & C2 & C3)]; [lia|]. lia. }
  clear Hw0 Hw1. clearbody wn. idtac.
  set (cx := FCX u p q n ob osz w whave wnext wn lb db la na da nd spi (cout - (out - (osz - cout))) cout
                 (8 * (n - cin) + bits + (osz - cout)) (s8_of w wnext) (zget_l Rb l kGP) (zget_l Rb l kTP) zc rdL rdD fin fw).
  clear Cw.
  assert (CX : fcx_ok cx).
  { unfold fcx_ok. subst cx. cbn [f_u f_p f_q f_n f_ob f_osz f_w f_whave f_wnext f_wn f_lb f_db f_la f_na f_da f_nd
                     f_spi f_bo f_cout0 f_W0 f_s8 f_gp f_tp f_zc f_rdL f_rdD f_fin f_fw]. idtac.
    split_conj.
    all: try assumption.
    all: try lia.
    - unfold ZSEP in Swp |- *. lia.
    - unfold ZSEP in Swq |- *. lia.
    - unfold ZSEP in Swob |- *. lia.
    - unfold ZSEP. destruct (Z.eq_dec wnext 0) as [E|NE]; [left; exact E | right]. apply s8_of_eq. lia.
    - intros i Hi. apply Rfw. lia. }
  Local Ltac pj := cbn [f_u f_p f_q f_n f_ob f_osz f_w f_whave f_wnext f_wn f_lb f_db f_la f_na f_da f_nd
                        f_spi f_bo f_cout0 f_W0 f_s8 f_gp f_tp f_zc f_rdL f_rdD f_fin f_fw].
  eapply (fast_entry cx Rb l M MD T cin cout hold bits out ret fo CX Hh); try (subst cx; pj; first [assumption | reflexivity | lia | (zbf_goal; pj; split_conj; first [assumption | reflexivity])]).
  -
    unfold f_emem. subst cx. pj.
    split_conj; try assumption.
    destruct Hwn as [(Ew & Ewn & _) | (Cw1 & Cw2 & Ewn & _)].
    + rewrite Ew, Ewn. apply mem_arr_nil; [rewrite TW64; lia | lia].
    + rewrite Ewn. apply Hwin. lia.
  -
    intros R1 M1 HC1 MV HL1 HRO1 HFR Hm8 PRO. zbf_in MV. dand MV as (Ma1 & Ma3 & Ma4 & Ma7).
    eapply (fast_loop (S (Z.to_nat (8 * (n - cin) + bits + (osz - cout)))) cx M1 R1 [] M1 MD T cin cout hold bits fo CX Hh HC1 ltac:(open_q_goal; split_conj; assumption));
      try (subst cx; pj; first [assumption | lia]).
    + subst cx. unfold fW. pj. lia.
    + subst cx. unfold fW. pj. lia.
    + subst cx. unfold fW. pj. rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia.
    + apply mpostL_refl.
    + eapply (fast_exit cx Rb l M M1 MD T ret CX Hh Hret1 Hret2); try (subst cx; pj; first [assumption | reflexivity | (zbf_goal; pj; split_conj; first [assumption | reflexivity])]).
      all: unfold KRET; subst cx; pj; intros R' M' cin' cout' hold' bits' mode' fo'; intros;
           eapply (K R' M' cin' cout' hold' bits' mode' fo'); try eassumption; lia.
Qed.
End S_Fast7.
