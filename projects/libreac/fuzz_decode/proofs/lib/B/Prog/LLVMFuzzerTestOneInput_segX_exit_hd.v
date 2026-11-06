(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_cmp_tail.v, with its module paths and module names changed; 304 of its 340 lines of code are new or changed and 260 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_segX_exit_hd: the head of the image-B exit group of LLVMFuzzerTestOneInput, +0x96c .. +0xab8,
   from llvm_b_st_96c (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v) to the cut ex_ab8 (lib/B/Prog/
   LLVMFuzzerTestOneInput_segX_exit_defs.v) before free #2:
   - +0x96c .. +0xa24, the channel-count test and the frame-header check, then +0xa24 (the abort edge refuted:
     reac_upstream_decode's verdict and the header's agree) and its two continuations, all in
     lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_hd_a.v (hd_96c, hd_974, hd_A24);
   - a0 = -1: the scan loop L6 and +0xa78 .. +0xab8 (lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_loop.v ex_loop),
     over the 0xa5 fill the refused call left (llvm_b_st_96c's dec_b_filled clause);
   - a0 = 12: check_round_trip #2 (+0xaa0, lib/B/Prog/LLVMFuzzerTestOneInput_segX_crt1_calls.v c1e_crt_call), the
     stretch +0xaa4 .. +0xab4 (hd_AA4) and check_braid (+0xab4, lib/B/Prog/LLVMFuzzerTestOneInput_leafb.v
     dec_leafb_check_braid), the braid relation both read from lib/B/Prog/LLVMFuzzerTestOneInput_segX_crt1_braid.v
     c1b_braid_of_garr8 at the upstream frame (audio = s11 + 50, out = s7, ns = 12). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP09 YI00 YI04 YP0m YP0e YP03.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBList DecodeBPa DecodeBPaLib
  DecodeBAddr DecodeBImg check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs reac_upstream_channels_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_upstream_decode_c reac_decode_c check_braid_cg
  check_braid_c LeafCgKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_exit_defs
  LLVMFuzzerTestOneInput_segX_exit_loop LLVMFuzzerTestOneInput_segX_crt1_calls LLVMFuzzerTestOneInput_segX_crt1_braid
  LLVMFuzzerTestOneInput_leafb LLVMFuzzerTestOneInput_segX_up_arith LLVMFuzzerTestOneInput_segX_up_a
  LLVMFuzzerTestOneInput_segX_up_b LLVMFuzzerTestOneInput_segX_up_d LLVMFuzzerTestOneInput_segX_up_kit
  LLVMFuzzerTestOneInput_segX_exit_hd_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lib/Reusable/YM03.v:182-189 redefines lia / nia globally (context pruning and retries); this file uses the
   plain ones (YM03.v:179-180). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Open Scope Z_scope.
Module CUp := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_decode_c.
Module CDec := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_c.
Module LCheckBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_braid_cg.
Module CBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_braid_c.

Ltac xin := repeat (first [left; reflexivity | right]).

(* check_round_trip #2 runs at nch = s5 <= 40 and ns = 12, inside the slot's ceiling. *)
Lemma xh_crt_le : forall MT, ameter_laws MT -> forall r, 2 <= r <= 40 ->
  dec_crt_cost MT r 12 <= dec_crt_cost_max MT.
Proof.
intros MT MTL r Hr. unfold dec_crt_cost, dec_crt_cost_max.
pose proof (mo_malloc_mono MT MTL (4 * (r * 12)) 1920 ltac:(lia)).
pose proof (mo_malloc_mono MT MTL (8 * r) 1016 ltac:(lia)).
pose proof (mo_malloc_mono MT MTL (3 * (r * 12)) 1440 ltac:(lia)).
lia.
Qed.

Lemma xh_crt_max_nonneg : forall MT, ameter_laws MT -> 0 <= dec_crt_cost_max MT.
Proof.
intros MT MTL. unfold dec_crt_cost_max.
pose proof (mo_malloc_nonneg MT MTL 1920 ltac:(lia)). pose proof (mo_malloc_nonneg MT MTL 1016 ltac:(lia)).
pose proof (mo_malloc_nonneg MT MTL 1440 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia.
Qed.

(* A verdict of 12 comes with a channel count in [2, 40], even, and the frame 52 + 36 nch bytes long. *)
Lemma xh_ok_geom : forall res upb len body, 0 <= len < 67108864 ->
  CUp.up_ok res upb len body = true ->
  let r := upstream_result len in 2 <= r <= 40 /\ Z.even r = true /\ len = 52 + 36 * r /\ CUp.up_nch len = r.
Proof.
intros res upb len body Hlen Hok r.
assert (Hn : CUp.up_nch len = r) by (unfold r; apply up_nch_result; unfold UP_NMAX; lia).
assert (H0 : 0 <= CUp.up_nch len).
{ unfold CUp.up_ok in Hok. repeat (apply andb_prop in Hok as [Hok ?]).
  match goal with H : (0 <=? CUp.up_nch len) = true |- _ => apply Z.leb_le in H; exact H end. }
destruct (up_result_cases len ltac:(unfold UP_NMAX; lia)) as [Hm | (Hq & H2 & Hev)]; [unfold r in Hn; lia|].
fold r in Hq. rewrite <- Hq in H2, Hev.
assert (Hm36 : (len - 52) mod 36 = 0).
{ destruct (upstream_ok len) eqn:E.
  - unfold upstream_ok in E. repeat (apply andb_prop in E as [E ?]).
    match goal with H : ((len - 52) mod 36 =? 0) = true |- _ => apply Z.eqb_eq in H; exact H end.
  - unfold r, upstream_result in H2. rewrite E in H2. lia. }
pose proof (Z.div_mod (len - 52) 36 ltac:(lia)).
split; [exact H2|]. split; [exact Hev|]. split; [lia | exact Hn].
Qed.

Section hd. Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegsB0.
Local Abbreviation base cx :=
  (@dec_b_base rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx).

Lemma ex_96c_ab8 :
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B -> AR_laws segs B -> ameter_laws MT ->
  (forall fx : YK11.FPState,
     @dec_check_round_trip_cg fx rc B MT (decodeb_sigma DB_check_round_trip) (CTX_check_round_trip RA_LLVMF)) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCheckBraid.dec_check_braid_cg) fx) ->
  forall (cx : dctx) (W : world segs) (c : config),
  base cx -> dec_b_rom cx -> llvm_b_st_96c B MT cx W c -> SRr segs W c (ex_ab8 B MT cx).
Proof.
intros HC HO HE LAWS MTL HCRT HBRD cx W c HB HROM HST.
destruct HST as (fx' & ly' & S' & regs' & mem' & md' & res & upb & mode & nch & ns & -> & Hfrm & Hcore & Hperm & Hres &
  Hupb & Hmle & Hmok & Hfrs & H10 & H18 & H21 & H22 & H23 & H24 & H25 & H27 & Hmode & Hfsh & Hgarr & Hok1 & Hok0 &
  S24 & S32 & S40 & S80 & S112).
destruct (ex_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx HB)
  as (Hraok & HRA & Hgp0 & Htp0 & Hstk0 & Hch & Hpn & Hnlen & Hfrs0 & Hnev0 & Hlive0 & _ & _ & _ & Hra4).
assert (Hn : 0 <= d_n cx < 67108864) by (destruct Hpn as [[-> _] | [Hq _]]; lia).
assert (Hpay0 : 0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx)))
  by (intros Hn0; destruct Hpn as [[Hq _] | [_ Hq]]; [lia | exact Hq]).
pose proof Hcore as (HJ & Hfrs' & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & Hsaved & HF4096 & HFal & HFpres &
  HFLw & Hpay & Hgarr0).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstkz & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
set (len := dec_b_len (d_n cx)) in *.
set (r := upstream_result len) in *.
set (uo := dec_b_uolen r) in *.
set (body := d_body cx) in *.
assert (Hlen : 0 <= len < 67108864) by (unfold len, dec_b_len; lia).
assert (Hbl : Z.of_nat (length body) = len)
  by (unfold body, len; rewrite (up_body_len cx Hnlen); unfold up_len; lia).
assert (Hres_in : In (res, len) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_app_iff; right; left; reflexivity).
assert (Hupb_in : In (upb, uo) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_app_iff; right; right; left; reflexivity).
assert (Huo : 1 <= uo <= 1440) by exact (up_uo_bounds cx Hn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res len HAR Hres_in) as (_ & Hr4096 & Hrc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ upb uo HAR Hupb_in) as (_ & Hu4096 & Huc & _).
pose proof (req_size_pos len ltac:(lia)) as [Hq1 Hq2].
pose proof (xh_crt_max_nonneg MT MTL) as Hcm.
assert (Hsp1b : 70368744177664 <= d_sp1 cx <= 140737488355328 - 88) by (change (2 ^ 46) with 70368744177664 in *;
  change (2 ^ 47) with 140737488355328 in *; lia).
rewrite (@up_cfg_eq fx' rc regs' mem' md' 0x96c).
refine (@hd_96c fx' rc B LAWS W regs' mem' md' regs' res upb len body r (d_sp1 cx) _ DEC_LLVMF_STK (d_sp0 cx) []
  (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' dec_ev_96c HJ (fun x _ => eq_refl)
  Hres_in Hbl Hgarr Hlen eq_refl Hupb H10 H18 H21 H22 H27 Hs1 Hsp1b S80 _ _).
- (* a0 = -1: L6, then +0xab8 *)
  intros Hokf regsT mdT T10 T12 T13 T18 Tkeep TJ.
  assert (T23 : YK11.getr regsT 23 = w64 upb) by (rewrite (Tkeep 23%bv ltac:(xin)); exact H23).
  assert (T24 : YK11.getr regsT 24 = w64 uo) by (rewrite (Tkeep 24%bv ltac:(xin)); exact H24).
  assert (T25 : YK11.getr regsT 25 = w64 (Z.lnot upb)) by (rewrite (Tkeep 25%bv ltac:(xin)); exact H25).
  refine (@ex_loop fx' rc B LAWS W DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly' S' dec_ev_96c regsT mem' upb uo _ Hupb_in Huo _ T18 T23 T24 T25 T10 _
    (Z.to_nat (uo - 0)) 0 regsT mdT eq_refl ltac:(lia) TJ T12 T13 (fun x _ => eq_refl)).
  + intros j Hj. exact (Hok0 Hokf j Hj).
  + intros regsE mdE Ekeep EJ. apply SRr_ret.
    assert (EK : forall x, In x hd_keep -> In x ex_keepL -> YK11.getr regsE x = YK11.getr regs' x)
      by (intros x H1 H2; rewrite (Ekeep x H2); exact (Tkeep x H1)).
    exists fx', ly', S', regsE, mem', mdE, dec_ev_96c, res, upb, (dec_spent_96c MT (d_n cx)), (dec_crt_cost_max MT).
    split; [reflexivity|]. split; [exact Hfrm|].
    split.
    { apply (ex_core_kept B cx ly' S' W regs' mem' md' dec_ev_96c ly' S' W regsE mem' mdE dec_ev_96c Hcore EJ Hfrs');
        try (intros; reflexivity).
      - exact (EK 8%bv ltac:(xin) ltac:(xin)).
      - exact (EK 9%bv ltac:(xin) ltac:(xin)).
      - unfold spZ. f_equal. exact (EK 2%bv ltac:(xin) ltac:(xin)).
      - exact (EK 3%bv ltac:(xin) ltac:(xin)).
      - exact (EK 4%bv ltac:(xin) ltac:(xin)).
      - exact HFpres.
      - exact Hpay. }
    split; [unfold dec_ev_96c; lia|]. split; [exact Hperm|]. split; [exact Hmle|]. split; [exact Hcm|].
    split; [replace (mo_free MT + (mo_free MT + dec_crt_cost_max MT)) with (dec_rest_96c MT)
              by (unfold dec_rest_96c; ring); exact Hmok|].
    split; [unfold dec_spent_ae0, dec_rest_96c; lia|].
    split; [exact Hfrs|]. split; [exact Hfsh|].
    split; [exact (eq_trans (EK 23%bv ltac:(xin) ltac:(xin)) H23) | exact (eq_trans (EK 27%bv ltac:(xin) ltac:(xin)) H27)].
- (* a0 = 12: check_round_trip #2, check_braid *)
  intros Hokt regsT mdT T10 T11 T12 T13 T18 T1 Tkeep TJ.
  destruct (xh_ok_geom res upb len body Hlen Hokt) as (Hr2 & Hrev & Hlen36 & Hnch). fold r in Hr2, Hrev, Hlen36, Hnch.
  assert (Huo36 : uo = 36 * r) by (unfold uo, dec_b_uolen; replace (0 <? r) with true by (symmetry; apply Z.ltb_lt; lia);
    reflexivity).
  assert (TK : forall x, In x hd_keep -> YK11.getr regsT x = YK11.getr regs' x) by exact Tkeep.
  assert (Hsp16 : d_sp1 cx mod 16 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hsp1al; [|lia].
    destruct Hsp1al as [q Hq]. exists (2 * q). lia. }
  assert (HspT : spZ regsT = d_sp1 cx) by (unfold spZ; rewrite (TK 2%bv ltac:(xin)); exact Hsp).
  (* the frame invariant at the call *)
  assert (HcoreT : dec_b_core B cx ly' S' W regsT mem' mdT dec_ev_96c).
  { apply (ex_core_kept B cx ly' S' W regs' mem' md' dec_ev_96c ly' S' W regsT mem' mdT dec_ev_96c Hcore TJ Hfrs');
      try (intros; reflexivity).
    - exact (TK 8%bv ltac:(xin)).
    - exact (TK 9%bv ltac:(xin)).
    - unfold spZ. f_equal. exact (TK 2%bv ltac:(xin)).
    - exact (TK 3%bv ltac:(xin)).
    - exact (TK 4%bv ltac:(xin)).
    - exact HFpres.
    - exact Hpay. }
  assert (Hmem0 : up_mem cx W mem' res mode nch ns)
    by exact (conj Hfrs (conj Hmode (conj Hfsh (conj Hgarr (conj S24 (conj S32 (conj S40 (conj S80 S112)))))))).
  (* the braid relation the two leaves read *)
  assert (G2 : garr8 segs (mrestrict (w_H W) mem') upb (map (fun b : byte => bv_unsigned b) (CDec.braid_out body r 12))).
  { rewrite <- Hnch. exact (Hok1 Hokt). }
  assert (HBR : dec_crt_braid (aview segs (w_H W) mem') (res + 50) upb r 12)
    by exact (c1b_braid_of_garr8 W mem' body res upb r 12 ltac:(lia) ltac:(lia) ltac:(lia) Hgarr G2).
  (* the two words the prologue saved, read by check_round_trip's frame-pointer chain *)
  assert (R8 : rdword (aview segs (w_H W) mem') (d_sp0 cx - 8) = Some RA_LLVMF).
  { rewrite <- HRA. exact (proj1 (Forall_forall _ _) Hsaved (8, 1) ltac:(xin)). }
  assert (R16 : rdword (aview segs (w_H W) mem') (d_sp0 cx - 16) = Some (s0Z (d_regs cx))).
  { exact (proj1 (Forall_forall _ _) Hsaved (16, 8) ltac:(xin)). }
  eapply SRr_bind.
  { refine (c1e_crt_call B MT RA_LLVMF HCRT fx' (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
      [(DEC_FCLASS, d_fpos cx)] ly' S' W mem' mdT dec_ev_96c regsT (s0Z (d_regs cx)) (res + 50) upb r 12 res len upb uo
      (dec_rest_96c MT) TJ Hch R8 R16 _ _ _ _ _ T10 _ _ T13 _ _ _ _ Hfrm Hrev _ _ _ Hres_in _ _ Hupb_in _ _ HBR _ _ _ Hmok _).
    - rewrite <- HRA. exact Hra4.
    - right. unfold raZ. rewrite T1. vm_compute. reflexivity.
    - rewrite T1. apply ret_ok_codeptr_v; [change (2 ^ 40) with 1099511627776; lia | reflexivity].
    - rewrite (TK 3%bv ltac:(xin)). exact Hgp.
    - rewrite (TK 4%bv ltac:(xin)). exact Htp.
    - rewrite T11. exact H23.
    - rewrite T12. exact H21.
    - unfold s0Z. rewrite (TK 8%bv ltac:(xin)), Hs0. apply unsigned_lit_small.
      change (2 ^ 64) with 18446744073709551616. change (2 ^ 47) with 140737488355328 in H47. lia.
    - rewrite HspT. exact Hsp16.
    - rewrite HspT. lia.
    - rewrite HspT. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - eapply ex_rom_rd; [exact HO | exact HE | exact HROM | exact TJ].
    - unfold dec_ev_96c, DEC_CRT_EV, DEC_EV_LIB in *. lia.
    - rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ Hperm), !bsum_app, <- (blocks_bytes_bsum B (d_ly cx) (d_S cx)).
      cbn [bsum fold_right snd]. unfold DEC_LIVE_LIB, DEC_CRT_LIVE in *. change (2 ^ 33) with 8589934592 in *.
      change (2 ^ 13) with 8192. lia.
    - pose proof (xh_crt_le MT MTL r Hr2). pose proof (mo_free_nonneg MT MTL). unfold dec_rest_96c. lia. }
  cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfrm2 & HJ2 & HP2 & Hfr2 & Hperm2 & HKc & Hmle2).
  rewrite T1.
  pose proof (proj1 HJ2) as HAR2.
  destruct (ex_acall_keep B LAWS cx ly' S' W regsT mem' mdT dec_ev_96c W2 mem2 (spZ regsT - DEC_CRT_STK) (spZ regsT)
    (fun _ => False) HcoreT HKc ltac:(lia) ltac:(intros a _ []) ltac:(intros a _ [])) as (KS & KF & KH).
  pose proof HKc as (_ & KB & _).
  assert (K2B : forall p n i, In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
    aview segs (w_H W2) mem2 (p + i) = aview segs (w_H W) mem' (p + i))
    by (intros p n i Hpn0 Hi; exact (KB p n i Hpn0 Hi (fun H => H))).
  assert (Hcore2 : dec_b_core B cx ly2 S2 W2 regs2 mem2 md2 (dec_ev_96c + DEC_CRT_EV)).
  { apply (ex_core_kept B cx ly' S' W regsT mem' mdT dec_ev_96c ly2 S2 W2 regs2 mem2 md2 (dec_ev_96c + DEC_CRT_EV)
      HcoreT HJ2).
    - rewrite Hfr2. exact Hfrs'.
    - exact (HP2 8 ltac:(unfold acallee_saved; lia)).
    - exact (HP2 9 ltac:(unfold acallee_saved; lia)).
    - unfold spZ. exact (f_equal bv_unsigned (HP2 2 ltac:(unfold acallee_saved; lia))).
    - exact (HP2 3 ltac:(unfold acallee_saved; lia)).
    - exact (HP2 4 ltac:(unfold acallee_saved; lia)).
    - intros a Ha. apply KS. lia.
    - intros a Ha. exact (proj1 (KF a Ha)).
    - intros a Ha. exact (proj2 (KF a Ha)).
    - intros Hn0. apply (Permutation_in _ (Permutation_sym Hperm2)). exact (Hpay Hn0).
    - intros i Hi. destruct (Z.lt_ge_cases 0 (d_n cx)) as [Hn0 | Hn0]; [|lia].
      pose proof (req_size_pos (d_n cx) ltac:(lia)).
      apply (K2B (d_p cx) (d_n cx) i (Hpay Hn0)). lia. }
  assert (Hmem2 : up_mem cx W2 mem2 res mode nch ns).
  { apply (up_mem_kept B cx ly' S' W mem' mdT ly2 S2 W2 mem2 md2 res mode nch ns HC (proj1 TJ) HAR2
      (ex_rom_rd B cx _ _ _ _ _ _ _ _ HO HE HROM TJ) (ex_rom_rd B cx _ _ _ _ _ _ _ _ HO HE HROM HJ2) Hsp1r KS
      (fun a Ha => proj1 (KF a Ha)) KH); [|exact Hmem0].
    intros i Hi. apply (K2B res len i Hres_in). change (d_body cx) with body in Hi. lia. }
  assert (Hres2 : In (res, len) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm2) Hres_in).
  assert (Hupb2 : In (upb, uo) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm2) Hupb_in).
  pose proof (req_size_pos uo ltac:(lia)) as [Hu1 Hu2].
  assert (G1' : garr8 segs (mrestrict (w_H W2) mem2) res (map (fun b : byte => bv_unsigned b) body)).
  { apply (ex_garr8_kept (w_H W) (w_H W2) mem' mem2); [|exact Hgarr].
    intros i Hi. rewrite length_map in Hi. apply (K2B res len i Hres_in). lia. }
  assert (G2' : garr8 segs (mrestrict (w_H W2) mem2) upb (map (fun b : byte => bv_unsigned b) (CDec.braid_out body r 12))).
  { apply (ex_garr8_kept (w_H W) (w_H W2) mem' mem2); [|exact G2].
    intros i Hi. rewrite length_map, c1b_braid_len in Hi. apply (K2B upb uo i Hupb_in). lia. }
  assert (HBR2 : dec_crt_braid (aview segs (w_H W2) mem2) (res + 50) upb r 12)
    by exact (c1b_braid_of_garr8 W2 mem2 body res upb r 12 ltac:(lia) ltac:(lia) ltac:(lia) G1' G2').
  (* +0xaa4 .. check_braid *)
  apply (@hd_AA4 fx2 rc B LAWS W2 regs2 mem2 md2 _ DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly2 S2 (dec_ev_96c + DEC_CRT_EV) HJ2).
  intros regsB mdB B10 B11 B12 B13 B1 Bkeep HJB.
  assert (P2_2 : YK11.getr regs2 2 = YK11.getr regsT 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  assert (P2_3 : YK11.getr regs2 3 = YK11.getr regsT 3) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
  assert (P2_4 : YK11.getr regs2 4 = YK11.getr regsT 4) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
  assert (P2_18 : YK11.getr regs2 18 = YK11.getr regsT 18) by exact (HP2 18 ltac:(unfold acallee_saved; lia)).
  assert (P2_21 : YK11.getr regs2 21 = YK11.getr regsT 21) by exact (HP2 21 ltac:(unfold acallee_saved; lia)).
  assert (P2_23 : YK11.getr regs2 23 = YK11.getr regsT 23) by exact (HP2 23 ltac:(unfold acallee_saved; lia)).
  assert (P2_27 : YK11.getr regs2 27 = YK11.getr regsT 27) by exact (HP2 27 ltac:(unfold acallee_saved; lia)).
  assert (HspB : spZ regsB = d_sp1 cx).
  { unfold spZ. rewrite (Bkeep 2%bv ltac:(xin)), P2_2. fold (spZ regsT). exact HspT. }
  assert (HcoreB : dec_b_core B cx ly2 S2 W2 regsB mem2 mdB (dec_ev_96c + DEC_CRT_EV)).
  { apply (ex_core_kept B cx ly2 S2 W2 regs2 mem2 md2 (dec_ev_96c + DEC_CRT_EV) ly2 S2 W2 regsB mem2 mdB
      (dec_ev_96c + DEC_CRT_EV) Hcore2 HJB); try (intros; reflexivity).
    - rewrite Hfr2. exact Hfrs'.
    - exact (Bkeep 8%bv ltac:(xin)).
    - exact (Bkeep 9%bv ltac:(xin)).
    - unfold spZ. f_equal. exact (Bkeep 2%bv ltac:(xin)).
    - exact (Bkeep 3%bv ltac:(xin)).
    - exact (Bkeep 4%bv ltac:(xin)).
    - pose proof Hcore2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFp2 & _). exact HFp2.
    - pose proof Hcore2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpay2 & _). exact Hpay2. }
  replace (decodeb_sigma DB_check_braid) with CBraid.CHECK_BRAID by (vm_compute; reflexivity).
  eapply SRr_bind.
  { refine (dec_leafb_check_braid B LAWS HC HBRD W2 regsB mem2 DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx)
      (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly2 S2 mdB (dec_ev_96c + DEC_CRT_EV) (d_sp1 cx - d_sp0 cx) (res + 50)
      upb r 12 res len upb uo HJB _ _ _ _ _ _ _ _ _ _ _ _ _ Hres2 _ _ Hupb2 _ _ HBR2).
    - rewrite HspB. lia.
    - replace (d_sp1 cx - d_sp0 cx) with (- (d_sp0 cx - d_sp1 cx)) by ring.
      apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hsp0al; [|lia]. apply Z.mod_divide in Hsp16; [|lia].
      destruct Hsp0al as [q0 Hz0]. destruct Hsp16 as [q1 Hz1]. exists (q1 - q0). lia.
    - lia.
    - unfold ESTACK. lia.
    - rewrite B1. apply ret_ok_codeptr_v; [change (2 ^ 40) with 1099511627776; lia | reflexivity].
    - rewrite (Bkeep 3%bv ltac:(xin)), P2_3, (TK 3%bv ltac:(xin)). exact Hgp.
    - rewrite (Bkeep 4%bv ltac:(xin)), P2_4, (TK 4%bv ltac:(xin)). exact Htp.
    - rewrite B10, P2_18. exact T18.
    - rewrite B11, P2_23, (TK 23%bv ltac:(xin)). exact H23.
    - rewrite B12, P2_21, (TK 21%bv ltac:(xin)). exact H21.
    - exact B13.
    - lia.
    - lia.
    - lia.
    - rewrite Z.mul_comm. replace (r mod 2) with 0 by (symmetry; apply Z.even_spec in Hrev; destruct Hrev as [h ->];
        rewrite Z.mul_comm, Z_mod_mult; reflexivity). lia.
    - lia.
    - lia. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Heff3 & Hpres3 & _).
  destruct (up_win_kept B cx ly2 S2 W2 regsB mem2 mdB (dec_ev_96c + DEC_CRT_EV) regs3 mem3 md3 res mode nch ns
    (LeafCgKit.in_wr []) LAWS HC HO HE HROM Hnlen HcoreB HJ3 HP3) as [Hcore3 Hmem3].
  + intros a Ha Hw Hn0. apply Heff3; [exact Ha | rewrite HspB; unfold ESTACK; exact Hw | exact Hn0].
  + exact Hpres3.
  + intros a _ Ha. apply Exists_nil in Ha. exact Ha.
  + intros a _ Ha. apply Exists_nil in Ha. exact Ha.
  + intros a _ Ha. apply Exists_nil in Ha. exact Ha.
  + intros i _ Ha. apply Exists_nil in Ha. exact Ha.
  + exact Hres2.
  + intros i _ Ha. apply Exists_nil in Ha. exact Ha.
  + exact Hmem2.
  + apply SRr_ret.
    pose proof (xh_crt_le MT MTL r Hr2) as Hcl.
    pose proof (mo_free_nonneg MT MTL) as Hfn.
    exists fx2, ly2, S2, regs3, mem3, md3, (dec_ev_96c + DEC_CRT_EV), res, upb,
      (dec_spent_96c MT (d_n cx) + dec_crt_cost MT r 12), (dec_crt_cost_max MT - dec_crt_cost MT r 12).
    split; [rewrite B1; reflexivity|]. split; [exact Hfrm2|]. split; [exact Hcore3|].
    split; [unfold dec_ev_96c, DEC_CRT_EV; lia|].
    split; [exact (Permutation_trans Hperm2 Hperm)|].
    split; [exact (mle_station MT (d_S cx) S' S2 _ _ MTL Hmle Hmle2)|].
    split; [lia|].
    split; [apply (mok_station MT S' S2 (dec_rest_96c MT) (dec_crt_cost MT r 12) _ MTL Hmok Hmle2);
              unfold dec_rest_96c; lia|].
    split; [unfold dec_spent_ae0, dec_rest_96c; lia|].
    pose proof Hmem3 as (Hfrs3 & _ & Hfsh3 & _).
    split; [exact Hfrs3|]. split; [exact Hfsh3|].
    assert (P3_23 : YK11.getr regs3 23 = YK11.getr regsB 23) by exact (HP3 23 ltac:(unfold acallee_saved; lia)).
    assert (P3_27 : YK11.getr regs3 27 = YK11.getr regsB 27) by exact (HP3 27 ltac:(unfold acallee_saved; lia)).
    split.
    * rewrite P3_23, (Bkeep 23%bv ltac:(xin)), P2_23, (TK 23%bv ltac:(xin)). exact H23.
    * rewrite P3_27, (Bkeep 27%bv ltac:(xin)), P2_27, (TK 27%bv ltac:(xin)). exact H27.
Qed.
End hd.
