(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contract astrcmp_realizes (lib/A/W_sites.v) proved for
   fuzz_reply.asan-ubsan's strcmp interceptor, entered at the trampoline __wrap_strcmp 0x421f0. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RT_strcmp.v at commit debcdf3fa6a, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (18 numerals; per-numeral report). *)
(* Ported from: a working branch 3210d71ee38 proofs/omx-clap-core/fuzz_state/lib/A/FSstrcmp.v (the stop
   index strcmp_k and strcmp_facts from a Theorem Labs lane's lib/A/Prog/strcmp_wrap{,_c}.v, bz_strcmp, fs_strcmp_realizesU).
   Changes: fuzz_reply.asan-ubsan's addresses (trampoline 0x421f0, ___interceptor_strcmp 0x42ac4, the
   weak hook 0x42ac0 a `ret` inside the walk, intercept_strcmp at common_flags + 0xfa = 0x138262); the premises are
   W_sites.v's astrcmp_realizes: each string is a first_byte fact over aview, its bytes the ones the donor's reader
   sees (RT_kit.mk_slack); the frame separation from ain_ok (RT_kit.off_window); region_in_mem from achecked's
   amem_range and amem_range x 8 / y 8; the checked length from kx + 1 <= 2 ^ 40; U-free; the result read back as
   the form's "a0 = 0 <-> kx = ky /\ the views agree below kx".  The interceptor compares itself and never calls
   REAL(strcmp) on this path (asan_inited = 1).  Body walk: relocated Bz I_strcmp.v istrcmp_spec with RIP =
   R_isPoisoned.rip_proof.  Named premises beyond AR_laws: RT_kit.FrShadowSyms and RT_kit.FrRtCells. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Img0.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FRsl.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.ImageA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_consts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_qck.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strcmpw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strcmp.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YK14 YP09 YP02 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
YB1v W_syms W_listing W_kit W_tbl W_place W_img W_contract W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require FRbz_bridge RT_kit RT_post YE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module NM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Module L6 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Regs6ss.
Module I0 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Img0.
Module SL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FRsl.
Module BE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Exec.
Module BM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Mem.
Module BF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Frame.
Module BMS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.MState.
Module BI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.ImageA.
Module BK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_consts.
Module BQ := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_qck.
Module BR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Module BP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_isPoisoned.
Module BS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strcmpw.
Module BSC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strcmp.
Module BC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Cells.
Module BSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Step.
Module FSB := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FRbz_bridge.
Module K := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_kit.
Module RP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_post.

(* Build identity: fuzz_reply.asan-ubsan (see RT_strlen.v), the entry the walks call as WS_strcmp is 0x421f0, and its
   word is `j 0x42ac4` (into ___interceptor_strcmp). *)
Lemma rt_strcmp_build_id :
  YE2k.A_ofl_head = 0x5fa0e8 /\ @YI16.sk_ofl_head YE2k.tfib_sink_head = 0x5fa0e8 /\
  fr_sigma WS_strcmp = 0x421f0 /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x81ea4)) = Some 0xfb010113 /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x84408)) = Some 0xec010113 /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x421f0)) = Some 0x0d50006f.
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity.
Qed.

(* ---- the stop index (a Theorem Labs lane 840c4afa7e2 lib/A/Prog/strcmp_wrap_c.v strcmp_k, strcmp_wrap.v:20-84) ---- *)
Fixpoint strcmp_k (x y : list byte) : nat :=
  match x, y with
  | a :: x', b :: y' => if bv_unsigned a =? bv_unsigned b then S (strcmp_k x' y') else O
  | _, _ => O
  end.

Lemma nth_error_firstn_lt : forall (l : list byte) j i, (i < j)%nat -> nth_error (firstn j l) i = nth_error l i.
Proof.
  induction l as [|x l IH]; intros j i Hij; [rewrite firstn_nil; destruct i; reflexivity|].
  destruct j as [|j]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma nonzero_head : forall (a : byte) l, ~ In (Z_to_bv 8 0) (a :: l) -> bv_unsigned a <> 0.
Proof.
  intros a l H E. apply H. left. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma strcmp_facts : forall sx sy, ~ In (Z_to_bv 8 0) sx -> ~ In (Z_to_bv 8 0) sy ->
  let k := strcmp_k sx sy in
  let x := nth k (sx ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) in
  let y := nth k (sy ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) in
  (k <= length sx)%nat /\ (k <= length sy)%nat /\ BS.sc_pre (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) k /\
  (bv_unsigned x <> bv_unsigned y \/ bv_unsigned x = 0) /\ (bv_unsigned x = bv_unsigned y <-> sx = sy).
Proof.
  induction sx as [|a sx IH]; intros [|b sy] NX NY; cbn [strcmp_k length app nth]; cbv zeta.
  - split; [lia|]. split; [lia|]. split; [intros j H; lia|]. split; [right; reflexivity|].
    split; intros _; reflexivity.
  - pose proof (nonzero_head b sy NY) as NB.
    split; [lia|]. split; [lia|]. split; [intros j H; lia|]. split; [right; reflexivity|].
    split; [intros E; change (bv_unsigned (Z_to_bv 8 0)) with 0 in E; lia| discriminate].
  - pose proof (nonzero_head a sx NX) as NA.
    split; [lia|]. split; [lia|]. split; [intros j H; lia|]. split; [left; exact NA|].
    split; [intros E; change (bv_unsigned (Z_to_bv 8 0)) with 0 in E; lia| discriminate].
  - pose proof (nonzero_head a sx NX) as NA.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [EQ|NE]; cbv beta iota.
    + assert (Eab : a = b) by (apply bv_eq; exact EQ). subst b.
      destruct (IH sy ltac:(intros H; apply NX; right; exact H) ltac:(intros H; apply NY; right; exact H)) as (L1 & L2 & HP & HB & HE).
      split; [lia|]. split; [lia|]. split.
      * intros [|j] Hj; [exists a; cbn; auto|]. apply (HP j). lia.
      * cbn [nth]. split; [exact HB|]. split; [intros H; f_equal; apply HE; exact H| intros H; injection H as H; apply HE; exact H].
    + split; [lia|]. split; [lia|]. split; [intros j H; lia|]. split; [left; exact NE|].
      split; [contradiction| intros H; injection H as H _; subst b; contradiction].
Qed.

Lemma cmpx_sgn : forall x y, BS.cmpx x y = Z.sgn (x - y).
Proof.
  intros x y. unfold BS.cmpx.
  destruct (Z.ltb_spec x y); [symmetry; apply Z.sgn_neg; lia|].
  destruct (Z.ltb_spec y x); [symmetry; apply Z.sgn_pos; lia|].
  symmetry. apply Z.sgn_null. lia.
Qed.

(* the bytes of a C string, as the walks read them, determine it *)
Lemma map_bv8_inj : forall l1 l2 : list Z, Forall (fun c => 0 <= c < 256) l1 -> Forall (fun c => 0 <= c < 256) l2 ->
  map (Z_to_bv 8) l1 = map (Z_to_bv 8) l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] F1 F2 E; cbn [map] in E; try discriminate; [reflexivity|].
  pose proof (f_equal (fun s => hd (Z_to_bv 8 0) s) E) as Eab. cbn [hd] in Eab.
  pose proof (f_equal (@tl _) E) as Et. cbn [tl] in Et. clear E. rename Et into E.
  inversion F1 as [|? ? Ra F1']; subst. inversion F2 as [|? ? Rb F2']; subst.
  apply (f_equal bv_unsigned) in Eab. rewrite !Z_to_bv_unsigned in Eab. unfold bv_wrap in Eab.
  change (bv_modulus 8) with 256 in Eab. rewrite !Z.mod_small in Eab by lia. subst b. f_equal. exact (IH l2 F1' F2' E).
Qed.

(* the shadow facts of a range hold of its prefixes *)
Lemma range_addressable_sub : forall rd B a n n', 0 <= n' <= n ->
  range_addressable rd B a n -> range_addressable rd B a n'.
Proof. intros rd B a n n' Hn H z Hz. apply H. lia. Qed.

Lemma hull_sub : forall rd x n n', 0 <= x -> 0 < n' <= n -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
  intros rd x n n' Hx Hn H s Hs. apply H. split; [lia|].
  assert (E : shadow_addr (x + n' - 1) <= shadow_addr (x + n - 1)).
  { unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
  assert (shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

(* the walk from the trampoline, in the Bz tree's words (I_strcmp.v istrcmp_spec, RIP met) *)
Lemma bz_strcmp : forall regs F fc m0 (p1 p2 : Z) (b1 b2 : list byte) (idx : nat) (x y : byte) (lo : Z),
  reg_get regs 10 = Z_to_bv 64 p1 -> reg_get regs 11 = Z_to_bv 64 p2 ->
  BF.stk BI.asegs m0 lo (bv_unsigned (reg_get regs 2)) -> lo <= bv_unsigned (reg_get regs 2) - 2272 ->
  BR.kHighShadowEnd < lo -> bv_unsigned (reg_get regs 2) < 2 ^ 63 ->
  BM.bytes_at BI.asegs m0 p1 b1 -> BM.bytes_at BI.asegs m0 p2 b2 -> length b1 = S idx -> length b2 = S idx ->
  BS.sc_pre b1 b2 idx -> nth_error b1 idx = Some x -> nth_error b2 idx = Some y ->
  (bv_unsigned x <> bv_unsigned y \/ bv_unsigned x = 0) ->
  p1 + (Z.of_nat idx + 1) <= 2 ^ 47 -> p2 + (Z.of_nat idx + 1) <= 2 ^ 47 ->
  (p1 + (Z.of_nat idx + 1) <= bv_unsigned (reg_get regs 2) - 2272 \/ bv_unsigned (reg_get regs 2) <= p1) ->
  (p2 + (Z.of_nat idx + 1) <= bv_unsigned (reg_get regs 2) - 2272 \/ bv_unsigned (reg_get regs 2) <= p2) ->
  BQ.chk_ok m0 p1 (Z.of_nat idx + 1) -> BQ.chk_ok m0 p2 (Z.of_nat idx + 1) -> BR.m2s_cells m0 -> BS.icells_sc m0 ->
  BSt.ro_cells BI.asegs m0 0x138262 [BC.C1 (Z_to_bv 8 1)] -> BM.mem_inv BI.asegs m0 ->
  BE.evt BI.asegs
    (BSC.istrcmp_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
       (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
       (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) F fc
       (BS.cmpx (bv_unsigned x) (bv_unsigned y)) lo m0)
    (BMS.MS (L6.mkR_of regs) F (Z_to_bv 64 0x421f0) fc None m0 (YK11.seg_rom BI.asegs)).
Proof.
  intros regs F fc m0 p1 p2 b1 b2 idx x y lo H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20
    H21 H22 H23 H24.
  change (L6.mkR_of regs) with (BF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
    (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
    (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16)
    (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
    (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28)
    (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)).
  exact (BSC.istrcmp_spec BP.rip_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F fc m0 p1 p2 b1 b2 idx x y lo H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22
    H23 H24).
Qed.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* one string: its k bytes then its NUL, as the walk's list, read from the donor's view *)
Lemma cstr_list : forall (W : world frsegs) mem x k, 0 < x -> 0 <= k -> x + k + 1 <= 2 ^ 64 ->
  first_byte frsegs W mem x (k + 1) 0 k ->
  let mR := mrestrict (w_H W) mem in
  K.mk_slack mR x (Z.to_nat k + 1) = K.mk_slack mR x (Z.to_nat k) ++ [Z_to_bv 8 0] /\
  ~ In (Z_to_bv 8 0) (K.mk_slack mR x (Z.to_nat k)) /\
  BM.bytes_at BI.asegs mR x (K.mk_slack mR x (Z.to_nat k + 1)) /\
  (forall i, 0 <= i < k -> exists b, aview frsegs (w_H W) mem (x + i) = Some b /\
     K.byte_at mR (x + i) = Z_to_bv 8 b /\ 0 < b < 256).
Proof.
  intros W mem x k Hx Hk Hxk (Hkn & Hbef & Hlast) mR.
  assert (E0 : K.byte_at mR (x + k) = Z_to_bv 8 0) by exact (proj1 (K.byte_at_view (w_H W) mem (x + k) 0 (Hlast ltac:(lia)))).
  assert (BYTES : forall i, 0 <= i < k -> exists b, aview frsegs (w_H W) mem (x + i) = Some b /\
     K.byte_at mR (x + i) = Z_to_bv 8 b /\ 0 < b < 256).
  { intros i Hi. destruct (Hbef i Hi) as (b & Hb & Hb0). exists b. split; [exact Hb|].
    destruct (K.byte_at_view (w_H W) mem (x + i) b Hb) as (Eb & Rb). split; [exact Eb | lia]. }
  assert (EL : K.mk_slack mR x (Z.to_nat k + 1) = K.mk_slack mR x (Z.to_nat k) ++ [Z_to_bv 8 0]).
  { rewrite K.mk_slack_app. f_equal. unfold K.mk_slack. cbn [seq map]. rewrite <- E0. f_equal. f_equal. lia. }
  split; [exact EL|]. split; [|split; [|exact BYTES]].
  - intros Hin. unfold K.mk_slack in Hin. apply in_map_iff in Hin as (j & Ej & Hj). apply in_seq in Hj.
    destruct (BYTES (Z.of_nat j) ltac:(lia)) as (b & _ & Eb & Rb). rewrite Eb in Ej.
    exact (K.bv8_ne0 b ltac:(lia) ltac:(lia) Ej).
  - apply K.bytes_at_mk; [lia | lia |]. intros a Ha.
    destruct (Z.eq_dec a (x + k)) as [->|N]; [rewrite (Hlast ltac:(lia)); discriminate|].
    destruct (Hbef (a - x) ltac:(lia)) as (b & Hb & _). replace (x + (a - x)) with a in Hb by lia. rewrite Hb. discriminate.
Qed.

(* the two byte lists are equal exactly when the lengths and the views agree *)
Lemma cstr_eq_iff : forall (W : world frsegs) mem x y kx ky, 0 <= kx -> 0 <= ky ->
  (forall i, 0 <= i < kx -> exists b, aview frsegs (w_H W) mem (x + i) = Some b /\
     K.byte_at (mrestrict (w_H W) mem) (x + i) = Z_to_bv 8 b /\ 0 < b < 256) ->
  (forall i, 0 <= i < ky -> exists b, aview frsegs (w_H W) mem (y + i) = Some b /\
     K.byte_at (mrestrict (w_H W) mem) (y + i) = Z_to_bv 8 b /\ 0 < b < 256) ->
  (K.mk_slack (mrestrict (w_H W) mem) x (Z.to_nat kx) = K.mk_slack (mrestrict (w_H W) mem) y (Z.to_nat ky) <->
   kx = ky /\ forall i, 0 <= i < kx -> aview frsegs (w_H W) mem (x + i) = aview frsegs (w_H W) mem (y + i)).
Proof.
  intros W mem x y kx ky Hkx Hky BX BY. set (mR := mrestrict (w_H W) mem) in *. split.
  - intros E. assert (Hl : kx = ky).
    { pose proof (f_equal (@length _) E) as L. rewrite !K.length_mk_slack in L. lia. }
    split; [exact Hl|]. intros i Hi.
    destruct (BX i Hi) as (bx & Vx & Ex & Rx). destruct (BY i ltac:(lia)) as (by' & Vy & Ey & Ry).
    pose proof (f_equal (fun l => nth_error l (Z.to_nat i)) E) as N. cbn beta in N.
    rewrite !K.nth_mk_slack in N by lia. injection N as N. rewrite !Z2Nat.id in N by lia.
    rewrite Ex, Ey in N. apply (f_equal bv_unsigned) in N. rewrite !Z_to_bv_unsigned in N. unfold bv_wrap in N.
    change (bv_modulus 8) with 256 in N. rewrite !Z.mod_small in N by lia. rewrite Vx, Vy, N. reflexivity.
  - intros (<- & HV). unfold K.mk_slack. apply map_ext_in. intros j Hj. apply in_seq in Hj.
    destruct (BX (Z.of_nat j) ltac:(lia)) as (bx & Vx & Ex & Rx).
    pose proof (HV (Z.of_nat j) ltac:(lia)) as V. rewrite Vx in V.
    destruct (K.byte_at_view (w_H W) mem (y + Z.of_nat j) bx (eq_sym V)) as (Ey & _).
    fold mR in Ey. rewrite Ex, Ey. reflexivity.
Qed.

Theorem rt_strcmp : forall B, AR_laws frsegs B -> K.FrShadowSyms B -> K.FrRtCells B ->
  astrcmp_realizes (PI := PB_fr) B (fr_sigma WS_strcmp).
Proof.
  intros B LAWS TL CELLS ly St W regs mem md x y kx ky Hpre (Hslo2 & Hpres2) Hx Hy Hx0 Hy0 Hkx0 Hky0 Hxk Hyk Hk40
    Hfbx Hfby Hainx Hainy (Hamrx & Hrax & Hhullx) (Hamry & Hray & Hhully) Hrom (Ham8x & Ham8y).
  change (@pa_segs _ fr_prog_listing PB_fr) with frsegs in *.
  change (fr_sigma WS_strcmp) with 0x421f0.
  pose proof Hpre as (HAR & Hret & Hal & Hlo1 & Hhi & HpresE & Hgp & Htp).
  pose proof (am_layout B ly St _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
  assert (HK : 2 * ESTACK = 8192) by reflexivity.
  pose proof (RP.ro_agree_of_rom_view W mem Hrom) as RO.
  pose proof (K.walk_cells B LAWS TL CELLS ly St W mem md HAR) as (M2S & _ & _ & _ & ICS & FLAG & _).
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs) by (unfold spZ; rewrite RP.getr_nz by reflexivity; reflexivity).
  assert (Ha0 : reg_get regs 10 = Z_to_bv 64 x) by (rewrite <- RP.getr_nz by reflexivity; exact Hx).
  assert (Ha1 : reg_get regs 11 = Z_to_bv 64 y) by (rewrite <- RP.getr_nz by reflexivity; exact Hy).
  assert (Hamx' : (0 <= x /\ x + kx + 1 <= 0x7fff7fff /\ x + 8 <= 0x7fff7fff) \/
                  (0x10007fff8000 <= x /\ x + kx + 1 <= 0x7fffffffffff /\ x + 8 <= 0x7fffffffffff))
    by (unfold amem_range, YG0f.kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamrx, Ham8x; lia).
  assert (Hamy' : (0 <= y /\ y + ky + 1 <= 0x7fff7fff /\ y + 8 <= 0x7fff7fff) \/
                  (0x10007fff8000 <= y /\ y + ky + 1 <= 0x7fffffffffff /\ y + 8 <= 0x7fffffffffff))
    by (unfold amem_range, YG0f.kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamry, Ham8y; lia).
  assert (Hfx : x + kx < spZ regs - 8192 \/ spZ regs <= x).
  { assert (Hw : forall a, x <= a < x + (kx + 1) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) by (intros a Ha; exact (proj2 (Hainx a Ha))).
    destruct (K.off_window (spZ regs) (2 * ESTACK) x (kx + 1) ltac:(lia) ltac:(lia) Hw) as [L|L]; [left; lia | right; exact L]. }
  assert (Hfy : y + ky < spZ regs - 8192 \/ spZ regs <= y).
  { assert (Hw : forall a, y <= a < y + (ky + 1) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) by (intros a Ha; exact (proj2 (Hainy a Ha))).
    destruct (K.off_window (spZ regs) (2 * ESTACK) y (ky + 1) ltac:(lia) ltac:(lia) Hw) as [L|L]; [left; lia | right; exact L]. }
  destruct (cstr_list W mem x kx Hx0 Hkx0 ltac:(lia) Hfbx) as (ELx & NZ1 & BYX & BX).
  destruct (cstr_list W mem y ky Hy0 Hky0 ltac:(lia) Hfby) as (ELy & NZ2 & BYY & BY).
  pose proof (cstr_eq_iff W mem x y kx ky Hkx0 Hky0 BX BY) as EQV.
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *. set (sp := spZ regs) in *.
  set (lo := sp - 2 * ESTACK).
  set (sx := K.mk_slack mR x (Z.to_nat kx)) in *. set (sy := K.mk_slack mR y (Z.to_nat ky)) in *.
  assert (Lsx : length sx = Z.to_nat kx) by (unfold sx; apply K.length_mk_slack).
  assert (Lsy : length sy = Z.to_nat ky) by (unfold sy; apply K.length_mk_slack).
  destruct (strcmp_facts sx sy NZ1 NZ2) as (KL & KR & HP & HB & HE).
  set (k := strcmp_k sx sy) in *.
  set (cx := nth k (sx ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) in *.
  set (cy := nth k (sy ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) in *.
  set (ls := firstn (S k) (sx ++ [Z_to_bv 8 0])).
  set (rs := firstn (S k) (sy ++ [Z_to_bv 8 0])).
  assert (LL : length ls = S k) by (unfold ls; apply firstn_length_le; rewrite length_app; cbn [length]; lia).
  assert (LR : length rs = S k) by (unfold rs; apply firstn_length_le; rewrite length_app; cbn [length]; lia).
  assert (EX : nth_error ls k = Some cx).
  { unfold ls. rewrite nth_error_firstn_lt by lia. apply nth_error_nth'. rewrite length_app; cbn; lia. }
  assert (EY : nth_error rs k = Some cy).
  { unfold rs. rewrite nth_error_firstn_lt by lia. apply nth_error_nth'. rewrite length_app; cbn; lia. }
  assert (HPc : BS.sc_pre ls rs k).
  { intros j Hj. destruct (HP j Hj) as (z & E1 & E2 & NZ). exists z. unfold ls, rs.
    rewrite !nth_error_firstn_lt by lia. auto. }
  (* the prefixes the interceptor reads, on the walk's memory *)
  assert (PREF : forall p kp (s : list byte), length s = Z.to_nat kp -> (k <= Z.to_nat kp)%nat -> 0 <= kp ->
    BM.bytes_at BI.asegs mR p (s ++ [Z_to_bv 8 0]) -> p + kp + 1 <= TASK_SIZE ->
    BM.bytes_at BI.asegs (NM.normalize_cj I0.rsegs mR) p (firstn (S k) (s ++ [Z_to_bv 8 0]))).
  { intros p kp s Ls Hk Hkp BYS Hp. apply (NM.bytes_at_normalize_cj_low I0.rsegs mR p _ RO).
    - rewrite firstn_length_le by (rewrite length_app; cbn; lia). lia.
    - assert (E : s ++ [Z_to_bv 8 0] = firstn (S k) (s ++ [Z_to_bv 8 0]) ++ skipn (S k) (s ++ [Z_to_bv 8 0]))
        by (rewrite firstn_skipn; reflexivity).
      rewrite E in BYS. exact (proj1 (proj1 (BM.bytes_at_app BI.asegs _ _ _ _) BYS)). }
  set (r := BS.cmpx (bv_unsigned cx) (bv_unsigned cy)).
  assert (Hr : r = -1 \/ r = 0 \/ r = 1)
    by (unfold r; rewrite cmpx_sgn; destruct (Z.sgn_spec (bv_unsigned cx - bv_unsigned cy)) as [[_ ->]|[[_ ->]|[_ ->]]]; lia).
  assert (Hr0 : r = 0 <-> sx = sy).
  { unfold r. rewrite cmpx_sgn. split.
    - intros E. apply HE. apply Z.sgn_null_iff in E. lia.
    - intros E. apply Z.sgn_null_iff. apply HE in E. lia. }
  apply (FSB.srr_of_evt K.Hwx_fr W 0x421f0 regs mem md
    (RP.walk_at (BSC.istrcmp_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
       (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
       (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) fp_regs fp_csr
       r lo (NM.normalize_cj I0.rsegs mR)) mR)).
  - refine (_ : BE.evt BI.asegs _ (RP.st_at regs fp_regs (Z_to_bv 64 0x421f0) fp_csr mR)).
    apply RP.bz_transport; [exact RO|].
    apply (bz_strcmp regs fp_regs fp_csr _ x y ls rs k cx cy lo).
    + exact Ha0.
    + exact Ha1.
    + rewrite Esp. apply RP.stk_norm_high; [unfold lo, RP.FR_IMG_TOP; lia | unfold TASK_SIZE; lia |].
      apply FSB.stk_of_apresent; [unfold lo; lia | lia | exact Hpres2].
    + rewrite Esp. unfold lo. lia.
    + unfold BR.kHighShadowEnd, lo. lia.
    + rewrite Esp. lia.
    + apply (PREF x kx sx Lsx ltac:(lia) Hkx0); [rewrite <- ELx; exact BYX | unfold TASK_SIZE; lia].
    + apply (PREF y ky sy Lsy ltac:(lia) Hky0); [rewrite <- ELy; exact BYY | unfold TASK_SIZE; lia].
    + exact LL.
    + exact LR.
    + exact HPc.
    + exact EX.
    + exact EY.
    + exact HB.
    + lia.
    + lia.
    + rewrite Esp. lia.
    + rewrite Esp. lia.
    + apply RP.chk_norm; [lia | lia | lia | lia | | |].
      * unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
      * apply (range_addressable_sub _ _ _ (kx + 1)); [lia | exact Hrax].
      * apply (hull_sub _ _ (kx + 1)); [lia | lia | exact (Hhullx ltac:(lia))].
    + apply RP.chk_norm; [lia | lia | lia | lia | | |].
      * unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
      * apply (range_addressable_sub _ _ _ (ky + 1)); [lia | exact Hray].
      * apply (hull_sub _ _ (ky + 1)); [lia | lia | exact (Hhully ltac:(lia))].
    + exact M2S.
    + exact ICS.
    + exact FLAG.
    + apply RP.bz_mem_inv_normalize.
  - intros ms' model' (c & s0 & HQ & Hrel & Hsame & Heqv) Hsbm _.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Es0 & MU & _ & _ & ST').
    subst s0. rewrite Esp in MU, ST'.
    refine (RP.aentry_post_of_walk B LAWS (2 * ESTACK) 2272 [] (fun _ => False) _ r ly St W regs mem md
      ms' model' c m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hpre Hslo2 RO ltac:(lia) _ _ _ Hrel Hsame Heqv _ ST' Hsbm _).
    + intros a Ha. inversion Ha.
    + intros a [].
    + intros a [].
    + cbn [app]. exact MU.
    + intros regs'' mem'' Hreg _. rewrite Hreg. rewrite <- EQV, <- Hr0. clearbody r. unfold w64.
      destruct Hr as [-> | [-> | ->]]; split; intros E; try reflexivity; try discriminate E;
        apply (f_equal bv_unsigned) in E; rewrite !Z_to_bv_unsigned in E; vm_compute in E; discriminate E.
Qed.

End core.
