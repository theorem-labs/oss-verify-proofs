(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_crt1_stage: the end of image B's LLVMFuzzerTestOneInput segment crt1.
     c1s_plain: from the call of reac_decode_plain_le at +0x6ec to the segment's end state llvm_b_st_6f0
                (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), over leafb's per-leaf instance dec_leafb_plain.
   The cut points c1_pre / c1_st / c1_regs are lib/B/Prog/LLVMFuzzerTestOneInput_segX_crt1_defs.v's.
   NOTE on arithmetic: lia zifies the whole context, which is large here, so every numeric goal is closed under
   `clear - HN` with HN the one conjunction of the numbers the proof uses. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_leafb.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_crt1_cut
  LLVMFuzzerTestOneInput_segX_crt1_glue LLVMFuzzerTestOneInput_segX_crt1_defs
  LLVMFuzzerTestOneInput_segX_crt1_calls LLVMFuzzerTestOneInput_segX_crt1_geo
  LLVMFuzzerTestOneInput_segX_crt1_runs LLVMFuzzerTestOneInput_segX_crt1_fevt
  LLVMFuzzerTestOneInput_segX_crt1_braid.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import LiaTwx2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* lib/Reusable/YM03.v:182-189 redefines lia globally; the donor proofs were built under lib/Lib/LiaTwx2.v's
   (zify_prune first), which this file takes back. *)
Local Ltac Lia.lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

Section C1Stage. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable RA_LLVMF : Z.
Local Abbreviation segs := decodesegsB0.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

Hypothesis HCELLS : dec_crt_cells B.
(* The two instance facts the read-only view at the DEC_RO_RD bytes needs (c1g_mode, c1_step). *)
Hypothesis HROS : dec_ro_rd_unowned B.
Hypothesis HRNE : dec_rom_no_errno B.
Hypothesis LAWS : AR_laws segs B.

(* ---- the call of reac_decode_plain_le at +0x6ec ---- *)
Theorem c1s_plain :
  (forall fx' : YK11.FPState, @dec_leaf_wr_at rc B (@LPlainLe.dec_reac_decode_plain_le_cg) fx') ->
  forall cx (res out mode nch ns : Z) fx' ly' S' W' regs' mem' md',
  @c1_pre rc B RA_LLVMF cx ->
  @c1_st rc B MT cx res out mode nch ns dec_ev_6f0 (dec_spent_6f0 MT (d_n cx)) (dec_rest_6f0 MT)
    fx' ly' S' W' regs' mem' md' ->
  c1_regs cx res out mode nch ns regs' ->
  YK11.getr regs' 18 = w64 out ->
  YK11.getr regs' 22 = w64 (dec_b_len (d_n cx)) ->
  YK11.getr regs' 1 = w64 (DEC_A_LLVMF + 0x6f0) ->
  YK11.getr regs' 10 = w64 res -> YK11.getr regs' 11 = w64 (dec_b_len (d_n cx)) ->
  YK11.getr regs' 12 = w64 mode -> YK11.getr regs' 13 = w64 out ->
  dec_b_filled W' mem' out (dec_b_olen nch ns) ->
  SRr segs W' (@LeafCgKit.cfg_at fx' CPlain.REAC_DECODE_PLAIN_LE regs' mem' md')
    (@llvm_b_st_6f0 rc B MT cx).
Proof.
  intros LPL cx res out mode nch ns fx' ly' S' W' regs' mem' md' HPRE HST HR R18 R22 R1 R10 R11 R12 R13 HFILL.
  destruct HPRE as (Hret & Hra & Hra4 & Hgp & Htp & Hstk & Hch & Hpay & Hn1 & Hn2 & Hnev & Hlive & Hrom).
  destruct HST as (Hfrm & Hcore & HP & Hres4 & Hout4 & Hmle & Hmok & Hmem & Hs80).
  destruct HR as (R19 & R20 & R21 & R23 & R24 & R26 & R27).
  pose proof Hcore as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1al & Hgp' & Htp' & _ & _ & _ & HFpres & _ & Hpayb & Hgarr).
  pose proof (proj1 HJ) as HAR.
  pose proof (c1g_layout B LAWS cx ly' S' W' regs' mem' md' dec_ev_6f0 res out nch ns Hcore HP Hn2 Hpay) as
    (Hsp0 & Hsp1 & H47 & Hinr & Hino & Ho4096 & Hoc & Hoapp & Hr4096 & Hrc & Hro & Hpo & Hof).
  pose proof (c1g_body_len cx Hn2) as Hbl.
  pose proof (@YM05.alloc_ceiling_val rc) as HCEIL.
  destruct Hmem as (Hfrs' & Hmode & Hfsh & Hgb & S24 & S32 & S40 & S56 & S64 & S72 & S88 & S112).
  pose proof (c1g_mode B LAWS cx ly' S' W' regs' mem' md' dec_ev_6f0 mode nch ns HCELLS HROS HRNE Hrom Hcore Hmode
                Hfsh) as
    (Hm0 & Hmc & Hm4 & Hmapp & Hmvis & Hmra).
  pose proof Hmode as (_ & Hnch & Hns & V4 & V8).
  pose proof (req_size_pos (dec_b_len (d_n cx)) ltac:(clear - Hn1; unfold dec_b_len; lia)) as [Hq1 Hq2].
  assert (Hop : 0 < dec_b_olen nch ns)
    by (clear - Hnch Hns; unfold dec_b_olen; destruct ((0 <? nch) && (0 <? ns))%bool eqn:E;
        [apply andb_true_iff in E as [E1 E2]; apply Z.ltb_lt in E1; apply Z.ltb_lt in E2; nia | lia]).
  pose proof (req_size_pos (dec_b_olen nch ns) ltac:(clear - Hop; lia)) as [Hqo1 Hqo2].
  assert (Hoq : req_size (dec_b_olen nch ns) = dec_b_olen nch ns)
    by (clear - Hop; unfold req_size; destruct (dec_b_olen nch ns =? 0) eqn:E;
        [apply Z.eqb_eq in E; lia | reflexivity]).
  (* the powers lia must see as numbers, and the one conjunction every numeric goal below is closed from *)
  assert (PW : 2 ^ 64 = 18446744073709551616 /\ 2 ^ 26 = 67108864 /\ 2 ^ 47 = 140737488355328 /\
               2 ^ 32 = 4294967296)
    by (clear; repeat split; vm_compute; reflexivity).
  assert (HN : 2 ^ 64 = 18446744073709551616 /\ 2 ^ 26 = 67108864 /\ 2 ^ 47 = 140737488355328 /\
               2 ^ 32 = 4294967296 /\
               0 <= d_n cx < 2 ^ 26 /\ Z.of_nat (length (d_body cx)) = dec_b_len (d_n cx) /\
               0 < dec_b_len (d_n cx) + 1 /\ 1 <= req_size (dec_b_len (d_n cx)) /\
               dec_b_len (d_n cx) <= req_size (dec_b_len (d_n cx)) /\
               0 < dec_b_olen nch ns /\ req_size (dec_b_olen nch ns) = dec_b_olen nch ns /\
               -128 <= nch <= 127 /\ -128 <= ns <= 127 /\
               0 < mode /\ mode + 12 <= YM05.alloc_ceiling /\
               4096 <= res /\ res + req_size (dec_b_len (d_n cx)) <= YM05.alloc_ceiling /\
               4096 <= out /\ out + req_size (dec_b_olen nch ns) <= YM05.alloc_ceiling /\
               (res + req_size (dec_b_len (d_n cx)) <= out \/ out + req_size (dec_b_olen nch ns) <= res) /\
               YM05.alloc_ceiling + 32768 <= d_sp0 cx /\ d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 /\
               d_sp0 cx <= 2 ^ 47 /\ d_sp1 cx mod 32 = 0 /\ d_sp0 cx mod 16 = 0 /\
               140735332483072 <= YM05.alloc_ceiling <= 140737479966720).
  { pose proof (proj1 Hstk) as Hal0. repeat split; try assumption; try (clear - PW; lia);
      try (clear - Hn1 PW; unfold dec_b_len; lia);
      try (clear - Hsp0 PW; lia); try (clear - Hsp1 PW; lia); try (clear - H47 PW; lia);
      try (clear - Hr4096 PW; lia); try (clear - Hrc PW; lia); try (clear - Ho4096 PW; lia); try (clear - Hoc PW; lia);
      try (clear - Hro PW; lia); try (clear - HCEIL PW; lia); try (clear - Hm0 PW; lia); try (clear - Hmc PW; lia);
      try (clear - Hq1 PW; lia); try (clear - Hq2 PW; lia); try (clear - Hop PW; lia); try (clear - Hoq PW; lia);
      try (clear - Hnch PW; lia); try (clear - Hns PW; lia); try (clear - Hsp1r PW; lia); try (clear - Hsp1al PW; lia);
      try (clear - Hal0 PW; lia); try (clear - Hbl PW; lia). }
  set (len := dec_b_len (d_n cx)) in *. set (olen := dec_b_olen nch ns) in *.
  assert (HLE : CPlain.plain_ok len (d_body cx) nch ns = true -> 3 * nch * ns <= olen).
  { intros Hp. unfold olen, dec_b_olen. unfold CPlain.plain_ok in Hp. rewrite !andb_true_iff in Hp.
    destruct Hp as (((_ & P1) & P2) & _). rewrite (proj2 (andb_true_iff _ _) (conj P1 P2)).
    apply Z.ltb_lt in P1. apply Z.ltb_lt in P2. clear - P1 P2. nia. }
  (* the leaf *)
  eapply SRr_mono;
    [ eapply (dec_leafb_plain B LAWS HCELLS LPL W' regs' mem' DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx)
                (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' md' dec_ev_6f0
                (d_sp1 cx - d_sp0 cx) res len mode out nch ns olen (d_body cx) HJ)
    | ].
  - rewrite Hsp. clear - HN. lia.
  - pose proof (Z.div_mod (d_sp1 cx) 32 ltac:(lia)) as D1.
    pose proof (Z.div_mod (d_sp0 cx) 16 ltac:(lia)) as D2.
    pose proof (Z.div_mod (d_sp1 cx) 16 ltac:(lia)) as D3.
    pose proof (Z.mod_pos_bound (d_sp1 cx) 16 ltac:(lia)) as D4.
    clear - HN D1 D2 D3 D4. lia.
  - clear - HN. lia.
  - unfold ESTACK, DEC_LLVMF_STK. clear - HN. lia.
  - rewrite R1. apply YK0s.ret_ok_even. clear. vm_compute. reflexivity.
  - exact Hgp'.
  - exact Htp'.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R13.
  - clear - HN. unfold len. lia.
  - clear - HN. lia.
  - clear - HN. lia.
  - exact Hinr.
  - intros E. clear - HN E. lia.
  - exact Hgb.
  - exact Hino.
  - clear - HN. lia.
  - exact HLE.
  - intros Hp a Ha. right. right. left. exists out, olen.
    split; [exact Hino|]. split.
    + intros Hin0. apply (c1g_perm_twice B LAWS ly' S' W' mem' md' (ablocks B (d_ly cx) (d_S cx))
        ([(res, len)] ++ [(out, olen)]) (out, olen) HAR HP Hin0). right. left. reflexivity.
    + pose proof (HLE Hp) as Hle. clear - HN Ha Hle. lia.
  - exact Hmapp.
  - exact Hm4.
  - exact Hmvis.
  - exact Hmra.
  - exact V4.
  - exact V8.
  - (* the post *)
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HJ2 & HPRES & HA0 & HKEEP & HGR & HX).
    unfold llvm_b_st_6f0.
    exists fx', ly', S', regs2, mem2, md2, res, out, mode, nch, ns.
    assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - ESTACK <= a < d_sp1 cx) ->
      ~ (out <= a < out + req_size olen) -> aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a).
    { intros a Ha H1 H2. apply (HKEEP a Ha); [rewrite Hsp; exact H1|].
      intros Hw. apply H2. destruct (CPlain.plain_ok len (d_body cx) nch ns) eqn:Hpk.
      - unfold LeafCgKit.in_wr in Hw. apply Exists_exists in Hw as (r & Hin & Hr).
        cbv iota in Hin. simpl in Hin. destruct Hin as [<- | []]. cbn [fst snd] in Hr.
        pose proof (HLE eq_refl) as Hle. clear - HN Hr Hle. lia.
      - unfold LeafCgKit.in_wr in Hw. apply Exists_exists in Hw as (r & Hin & Hr).
        cbv iota in Hin. simpl in Hin. destruct Hin. }
    destruct (c1g_keep_window B LAWS cx ly' S' W' regs' mem' md' dec_ev_6f0 res out nch ns mem2
                Hcore HP Hn2 Hpay KW HGR) as (KS & KF & KH & KR & KP).
    assert (HSTEP : dec_b_core B cx ly' S' W' regs2 mem2 md2 dec_ev_6f0 /\
                    c1_mem cx W' mem2 res out mode nch ns).
    { apply (c1_step B cx ly' S' W' regs' mem' md' dec_ev_6f0 res out mode nch ns ly' S' W' regs2 mem2 md2
               dec_ev_6f0 HCELLS HROS HRNE Hrom Hcore
               (conj Hfrs' (conj Hmode (conj Hfsh (conj Hgb (conj S24 (conj S32 (conj S40 (conj S56
                  (conj S64 (conj S72 (conj S88 S112))))))))))) HJ2 Hfrs).
      - intros b Hb. exact Hb.
      - exact (eq_trans (HPRES 8 ltac:(unfold acallee_saved; clear; lia)) eq_refl).
      - exact (eq_trans (HPRES 9 ltac:(unfold acallee_saved; clear; lia)) eq_refl).
      - exact (f_equal bv_unsigned (HPRES 2 ltac:(unfold acallee_saved; clear; lia))).
      - exact (eq_trans (HPRES 3 ltac:(unfold acallee_saved; clear; lia)) eq_refl).
      - exact (eq_trans (HPRES 4 ltac:(unfold acallee_saved; clear; lia)) eq_refl).
      - intros a Ha _. apply KS. exact Ha.
      - exact KF.
      - exact KH.
      - exact KR.
      - exact KP. }
    destruct HSTEP as (Hcore2 & Hmem2).
    destruct Hmem2 as (Hfrs2 & Hmode2 & Hfsh2 & Hgb2 & S24' & S32' & S40' & S56' & S64' & S72' & S88' & S112').
    assert (S80' : dec_b_slot cx (aview segs (w_H W') mem2) 80 (res + 50)).
    { unfold dec_b_slot in *. rewrite <- Hs80. apply rdword_ext. intros j Hj. apply KS. clear - HN Hj. lia. }
    rewrite R1 in Hc2.
    split; [exact Hc2|].
    split; [exact Hfrm|].
    split; [exact Hcore2|].
    split; [exact HP|].
    split; [exact Hres4|]. split; [exact Hout4|].
    split; [exact Hmle|]. split; [exact Hmok|].
    split; [exact Hfrs2|].
    split; [exact HA0|].
    split; [exact (eq_trans (HPRES 18 ltac:(unfold acallee_saved; clear; lia)) R18)|].
    split; [exact (eq_trans (HPRES 19 ltac:(unfold acallee_saved; clear; lia)) R19)|].
    split; [exact (eq_trans (HPRES 20 ltac:(unfold acallee_saved; clear; lia)) R20)|].
    split; [exact (eq_trans (HPRES 21 ltac:(unfold acallee_saved; clear; lia)) R21)|].
    split; [exact (eq_trans (HPRES 22 ltac:(unfold acallee_saved; clear; lia)) R22)|].
    split; [exact (eq_trans (HPRES 23 ltac:(unfold acallee_saved; clear; lia)) R23)|].
    split; [exact (eq_trans (HPRES 26 ltac:(unfold acallee_saved; clear; lia)) R26)|].
    split; [exact (eq_trans (HPRES 27 ltac:(unfold acallee_saved; clear; lia)) R27)|].
    split; [exact Hmode2|].
    split; [exact Hfsh2|].
    split; [exact Hgb2|].
    split; [exact HX|].
    split.
    { intros Hp i Hi.
      assert (E : aview segs (w_H W') mem2 (out + i) = aview segs (w_H W') mem' (out + i)).
      { apply (HKEEP (out + i)); [clear - HN Hi; lia | rewrite Hsp; unfold ESTACK; clear - HN Hi; lia |].
        assert (Hp' : CPlain.plain_ok len (d_body cx) nch ns = false) by exact Hp.
        rewrite Hp'. cbv iota. intros Hw. unfold LeafCgKit.in_wr in Hw. inversion Hw. }
      rewrite E. exact (HFILL i Hi). }
    split; [exact S24'|]. split; [exact S32'|]. split; [exact S40'|]. split; [exact S56'|].
    split; [exact S64'|]. split; [exact S72'|]. split; [exact S80'|]. split; [exact S88' | exact S112'].
Qed.
(* ---- the call of __asan_memset at +0x6d4, then the run +0x6d8 .. +0x6ec ---- *)
Theorem c1k_memset :
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (decodeb_sigma DB___asan_memset)) ->
  (forall fx' : YK11.FPState, @dec_leaf_wr_at rc B (@LPlainLe.dec_reac_decode_plain_le_cg) fx') ->
  @c1_K_memset rc B MT RA_LLVMF.
Proof.
  intros AMS LPL cx res out mode nch ns fx' ly' S' W' regs' mem' md' HPRE HST HR R18 R1 R10 R11 R12.
  pose proof HPRE as (Hret & Hra & Hra4 & Hgp & Htp & Hstk & Hch & Hpay & Hn1 & Hn2 & Hnev & Hlive & Hrom).
  pose proof HST as (Hfrm & Hcore & HP & Hres4 & Hout4 & Hmle & Hmok & Hmem & Hs80).
  pose proof HR as (R19 & R20 & R21 & R23 & R24 & R26 & R27).
  pose proof Hcore as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1al & Hgp' & Htp' & _ & _ & _ & HFpres & _ & Hpayb & Hgarr).
  pose proof (proj1 HJ) as HAR.
  pose proof (c1g_layout B LAWS cx ly' S' W' regs' mem' md' dec_ev_6f0 res out nch ns Hcore HP Hn2 Hpay) as
    (Hsp0 & Hsp1 & H47 & Hinr & Hino & Ho4096 & Hoc & Hoapp & Hr4096 & Hrc & Hro & Hpo & Hof).
  pose proof (c1g_body_len cx Hn2) as Hbl.
  pose proof (@YM05.alloc_ceiling_val rc) as HCEIL.
  pose proof Hmem as (Hfrs' & Hmode & Hfsh & Hgb & S24 & S32 & S40 & S56 & S64 & S72 & S88 & S112).
  pose proof (c1g_mode B LAWS cx ly' S' W' regs' mem' md' dec_ev_6f0 mode nch ns HCELLS HROS HRNE Hrom Hcore Hmode
                Hfsh) as
    (Hm0 & Hmc & Hm4 & Hmapp & Hmvis & Hmra).
  pose proof Hmode as (_ & Hnch & Hns & V4 & V8).
  pose proof (req_size_pos (dec_b_len (d_n cx)) ltac:(clear - Hn1; unfold dec_b_len; lia)) as [Hq1 Hq2].
  assert (Hop : 0 < dec_b_olen nch ns < 2 ^ 32).
  { clear - Hnch Hns. unfold dec_b_olen. destruct ((0 <? nch) && (0 <? ns))%bool eqn:E;
    [apply andb_true_iff in E as [E1 E2]; apply Z.ltb_lt in E1; apply Z.ltb_lt in E2;
     assert (2 ^ 32 = 4294967296) by (vm_compute; reflexivity); nia
    | assert (0 < 2 ^ 32) by (vm_compute; reflexivity); lia]. }
  assert (Hoq : req_size (dec_b_olen nch ns) = dec_b_olen nch ns)
    by (clear - Hop; unfold req_size; destruct (dec_b_olen nch ns =? 0) eqn:E;
        [apply Z.eqb_eq in E; lia | reflexivity]).
  assert (PW : 2 ^ 64 = 18446744073709551616 /\ 2 ^ 26 = 67108864 /\ 2 ^ 47 = 140737488355328 /\
               2 ^ 32 = 4294967296)
    by (clear; repeat split; vm_compute; reflexivity).
  assert (HN : 2 ^ 64 = 18446744073709551616 /\ 2 ^ 26 = 67108864 /\ 2 ^ 47 = 140737488355328 /\
               2 ^ 32 = 4294967296 /\
               0 <= d_n cx < 2 ^ 26 /\ Z.of_nat (length (d_body cx)) = dec_b_len (d_n cx) /\
               1 <= req_size (dec_b_len (d_n cx)) /\
               dec_b_len (d_n cx) <= req_size (dec_b_len (d_n cx)) /\
               0 < dec_b_olen nch ns < 2 ^ 32 /\ req_size (dec_b_olen nch ns) = dec_b_olen nch ns /\
               -128 <= nch <= 127 /\ -128 <= ns <= 127 /\
               0 < mode /\ mode + 12 <= YM05.alloc_ceiling /\
               4096 <= res /\ res + req_size (dec_b_len (d_n cx)) <= YM05.alloc_ceiling /\
               4096 <= out /\ out + req_size (dec_b_olen nch ns) <= YM05.alloc_ceiling /\
               (res + req_size (dec_b_len (d_n cx)) <= out \/ out + req_size (dec_b_olen nch ns) <= res) /\
               YM05.alloc_ceiling + 32768 <= d_sp0 cx /\ d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 /\
               d_sp0 cx <= 2 ^ 47 /\ d_sp1 cx mod 32 = 0 /\ d_sp0 cx mod 16 = 0 /\
               140735332483072 <= YM05.alloc_ceiling <= 140737479966720).
  { pose proof (proj1 Hstk) as Hal0. repeat split; try assumption; try (clear - PW; lia);
      try (clear - Hn1 PW; unfold dec_b_len; lia);
      try (clear - Hsp0 PW; lia); try (clear - Hsp1 PW; lia); try (clear - H47 PW; lia);
      try (clear - Hr4096 PW; lia); try (clear - Hrc PW; lia); try (clear - Ho4096 PW; lia);
      try (clear - Hoc PW; lia); try (clear - Hro PW; lia); try (clear - HCEIL PW; lia);
      try (clear - Hm0 PW; lia); try (clear - Hmc PW; lia); try (clear - Hq1 PW; lia);
      try (clear - Hq2 PW; lia); try (clear - Hop PW; lia); try (clear - Hoq PW; lia);
      try (clear - Hnch PW; lia); try (clear - Hns PW; lia); try (clear - Hsp1r PW; lia);
      try (clear - Hsp1al PW; lia); try (clear - Hal0 PW; lia); try (clear - Hbl PW; lia). }
  assert (Hnin : ~ In (out, dec_b_olen nch ns) (ablocks B (d_ly cx) (d_S cx))).
  { intros Hin0. apply (c1g_perm_twice B LAWS ly' S' W' mem' md' (ablocks B (d_ly cx) (d_S cx))
      ([(res, dec_b_len (d_n cx))] ++ [(out, dec_b_olen nch ns)]) (out, dec_b_olen nch ns) HAR HP Hin0).
    right. left. reflexivity. }
  assert (Ho16 : d_sp1 cx - d_sp0 cx <= 0) by (clear - HN; lia).
  assert (Hoal : (d_sp1 cx - d_sp0 cx) mod 16 = 0).
  { pose proof (Z.div_mod (d_sp1 cx) 32 ltac:(lia)) as D1.
    pose proof (Z.div_mod (d_sp0 cx) 16 ltac:(lia)) as D2.
    pose proof (Z.div_mod (d_sp1 cx) 16 ltac:(lia)) as D3.
    pose proof (Z.mod_pos_bound (d_sp1 cx) 16 ltac:(lia)) as D4.
    clear - HN D1 D2 D3 D4. lia. }
  assert (Hobud : ESTACK - (d_sp1 cx - d_sp0 cx) <= DEC_LLVMF_STK)
    by (unfold ESTACK, DEC_LLVMF_STK; clear - HN; lia).
  assert (Hretm : YK0s.ret_ok (YK11.getr regs' 1))
    by (rewrite R1; apply YK0s.ret_ok_even; clear; vm_compute; reflexivity).
  (* the memset *)
  eapply SRr_bind;
    [ eapply (c1e_memset_call B LAWS AMS fx' DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
                (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' W' mem' md' dec_ev_6f0 regs'
                (d_sp1 cx - d_sp0 cx) out (dec_b_olen nch ns) (YK11.getr regs' 1)
                HJ Hino Hnin ltac:(clear - HN; lia) R10 R11 ltac:(rewrite Hoq; exact R12)
                ltac:(rewrite Hsp; clear - HN; lia) Hoal Ho16 Hobud Hgp' Htp' eq_refl Hretm)
    | ].
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPRES & HA0 & HFILL2 & HKEEP2 & HGR2).
  (* the frame at the memset's return *)
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - ESTACK <= a < d_sp1 cx) ->
    ~ (out <= a < out + req_size (dec_b_olen nch ns)) ->
    aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a).
  { intros a Ha H1 H2. apply (HKEEP2 a Ha); [exact H2|].
    unfold ESTACK in H1 |- *. clear - H1 HN. lia. }
  destruct (c1g_keep_window B LAWS cx ly' S' W' regs' mem' md' dec_ev_6f0 res out nch ns mem2
              Hcore HP Hn2 Hpay KW HGR2) as (KS & KF & KH & KR & KP).
  destruct (c1_step B cx ly' S' W' regs' mem' md' dec_ev_6f0 res out mode nch ns ly' S' W' regs2 mem2 md2
              dec_ev_6f0 HCELLS HROS HRNE Hrom Hcore
              (conj Hfrs' (conj Hmode (conj Hfsh (conj Hgb (conj S24 (conj S32 (conj S40 (conj S56
                 (conj S64 (conj S72 (conj S88 S112))))))))))) HJ2 Hfrs
              (fun b Hb => Hb)
              (eq_trans (HPRES 8 ltac:(unfold acallee_saved; clear; lia)) eq_refl)
              (eq_trans (HPRES 9 ltac:(unfold acallee_saved; clear; lia)) eq_refl)
              (f_equal bv_unsigned (HPRES 2 ltac:(unfold acallee_saved; clear; lia)))
              (eq_trans (HPRES 3 ltac:(unfold acallee_saved; clear; lia)) eq_refl)
              (eq_trans (HPRES 4 ltac:(unfold acallee_saved; clear; lia)) eq_refl)
              ltac:(intros a Ha _; apply KS; exact Ha) KF KH KR KP) as (Hcore2 & Hmem2).
  pose proof Hmem2 as (Hfrs2 & Hmode2 & Hfsh2 & Hgb2 & S24' & S32' & S40' & S56' & S64' & S72' & S88' & S112').
  assert (S80' : dec_b_slot cx (aview segs (w_H W') mem2) 80 (res + 50)).
  { unfold dec_b_slot in *. rewrite <- Hs80. apply rdword_ext. intros j Hj. apply KS. clear - HN Hj. lia. }
  assert (HST2 : @c1_st rc B MT cx res out mode nch ns dec_ev_6f0 (dec_spent_6f0 MT (d_n cx))
                   (dec_rest_6f0 MT) fx' ly' S' W' regs2 mem2 md2).
  { split; [exact Hfrm|]. split; [exact Hcore2|]. split; [exact HP|]. split; [exact Hres4|].
    split; [exact Hout4|]. split; [exact Hmle|]. split; [exact Hmok|]. split; [exact Hmem2 | exact S80']. }
  assert (HREG2 : c1_regs cx res out mode nch ns regs2).
  { split; [exact (eq_trans (HPRES 19 ltac:(unfold acallee_saved; clear; lia)) R19)|].
    split; [exact (eq_trans (HPRES 20 ltac:(unfold acallee_saved; clear; lia)) R20)|].
    split; [exact (eq_trans (HPRES 21 ltac:(unfold acallee_saved; clear; lia)) R21)|].
    split; [exact (eq_trans (HPRES 23 ltac:(unfold acallee_saved; clear; lia)) R23)|].
    split; [exact (eq_trans (HPRES 24 ltac:(unfold acallee_saved; clear; lia)) R24)|].
    split; [exact (eq_trans (HPRES 26 ltac:(unfold acallee_saved; clear; lia)) R26)
           | exact (eq_trans (HPRES 27 ltac:(unfold acallee_saved; clear; lia)) R27)]. }
  pose proof HREG2 as (R19' & R20' & R21' & R23' & R24' & R26' & R27').
  assert (R18' : YK11.getr regs2 18 = w64 out)
    by exact (eq_trans (HPRES 18 ltac:(unfold acallee_saved; clear; lia)) R18).
  assert (R9' : YK11.getr regs2 9 = w64 (d_sp1 cx))
    by exact (eq_trans (HPRES 9 ltac:(unfold acallee_saved; clear; lia)) R9).
  assert (Hsp2 : spZ regs2 = d_sp1 cx)
    by (etransitivity; [exact (f_equal bv_unsigned (HPRES 2 ltac:(unfold acallee_saved; clear; lia))) | exact Hsp]).
  (* the run +0x6d8 .. +0x6ec *)
  set (wf := CInsp.inspect_wf (dec_b_len (d_n cx)) (d_body cx)).
  set (fz := ((0 <? nch) && (0 <? ns))%bool).
  set (ft := (dec_b_prod nch ns <? 481)).
  assert (Ep : c1_pok wf fz ft = CPlain.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns)
    by exact (c1g_pok (dec_b_len (d_n cx)) (d_body cx) nch ns Hnch Hns).
  assert (G2r : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (d_sp1 cx))
    by (apply bv_eq; rewrite (MState.unsigned_lit (d_sp1 cx)) by (clear - HN; lia); exact Hsp2).
  assert (G9r : YK11.getr regs2 (Z_to_bv 5 9) = Z_to_bv 64 (d_sp1 cx)) by exact R9'.
  assert (G18r : YK11.getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 out) by exact R18'.
  assert (G19r : YK11.getr regs2 (Z_to_bv 5 19) = Z_to_bv 64 (if c1_pok wf fz ft then 1 else 0))
    by (rewrite Ep; exact R19').
  assert (G20r : YK11.getr regs2 (Z_to_bv 5 20) = Z_to_bv 64 (dec_b_len (d_n cx))) by exact R20'.
  assert (G21r : YK11.getr regs2 (Z_to_bv 5 21) = Z_to_bv 64 mode) by exact R21'.
  assert (G23r : YK11.getr regs2 (Z_to_bv 5 23) = Z_to_bv 64 nch) by exact R23'.
  assert (G24r : YK11.getr regs2 (Z_to_bv 5 24) = Z_to_bv 64 (if fz then 1 else 0)) by exact R24'.
  assert (G26r : YK11.getr regs2 (Z_to_bv 5 26) = Z_to_bv 64 (dec_b_olen nch ns)) by exact R26'.
  assert (G27r : YK11.getr regs2 (Z_to_bv 5 27) = Z_to_bv 64 res) by exact R27'.
  assert (RSTK : ExecF.rng (LeafCgKit.RNG_W (world segs) (@w_H segs) W') (d_sp1 cx + 24) 72)
    by (apply (c1e_rng_stk B cx ly' S' W' regs2 mem2 md2 dec_ev_6f0); [exact Hcore2 | unfold DEC_LLVMF_STK; clear - HN; lia | clear - HN; lia | clear; lia]).
  assert (RD24 : ov_read_bytes Img0.rsegs mem2 (Z_to_bv 64 (d_sp1 cx + 24)) 8 =
                 Some (Mem.le8 (Z_to_bv 64 (dec_b_len (d_n cx)))))
    by (apply (c1e_slot_rd8 B cx ly' S' W' regs2 mem2 md2 dec_ev_6f0); [exact Hcore2 | clear; lia | clear; lia | exact S24']).
  pose proof (c1_run_amset (LeafCgKit.RNG_W (world segs) (@w_H segs) W')
    (YK11.getr regs2 (Z_to_bv 5 3)) (YK11.getr regs2 (Z_to_bv 5 4)) (YK11.getr regs2 (Z_to_bv 5 8))
    (YK11.getr regs2 (Z_to_bv 5 25)) (@fp_regs fx') (@fp_csr fx')
    (d_sp1 cx) res out mode (dec_b_len (d_n cx)) (dec_b_olen nch ns) nch wf fz ft
    ltac:(clear - HN; unfold dec_b_len; lia) ltac:(clear - HN; lia) RSTK mem2 RD24
    (YK11.getr regs2 (Z_to_bv 5 1)) (YK11.getr regs2 (Z_to_bv 5 5)) (YK11.getr regs2 (Z_to_bv 5 6))
    (YK11.getr regs2 (Z_to_bv 5 7)) (YK11.getr regs2 (Z_to_bv 5 28)) (YK11.getr regs2 (Z_to_bv 5 29))
    (YK11.getr regs2 (Z_to_bv 5 30)) (YK11.getr regs2 (Z_to_bv 5 31))
    (YK11.getr regs2 (Z_to_bv 5 10)) (YK11.getr regs2 (Z_to_bv 5 11)) (YK11.getr regs2 (Z_to_bv 5 12))
    (YK11.getr regs2 (Z_to_bv 5 13)) (YK11.getr regs2 (Z_to_bv 5 14)) (YK11.getr regs2 (Z_to_bv 5 15))
    (YK11.getr regs2 (Z_to_bv 5 16)) (YK11.getr regs2 (Z_to_bv 5 17))
    (YK11.getr regs2 (Z_to_bv 5 22))) as HRUN.
  lazymatch type of HRUN with ExecF.evtF _ _ ?P _ =>
    assert (HRUN2 : ExecF.evtF Img0.rsegs (LeafCgKit.RNG_W (world segs) (@w_H segs) W') P
                      (@LeafCgKit.ms_of_regs fx' (DEC_A_LLVMF + 0x6d8) regs2 mem2)) end.
  { unfold LeafCgKit.ms_of_regs.
    rewrite G2r, G9r, G18r, G19r, G20r, G21r, G23r, G24r, G26r, G27r.
    replace (LeafCgKit.w64 (DEC_A_LLVMF + 1752)) with (Z_to_bv 64 (C1 1752))
      by (unfold LeafCgKit.w64; f_equal; unfold C1, DEC_A_LLVMF, DecodeBList.AF_LLVMFuzzerTestOneInput; clear; lia).
    exact HRUN. }
  clear HRUN.
  rewrite R1.
  apply (c1f_run W' regs2 mem2 md2 (DEC_A_LLVMF + 0x6d8) _ _ HRUN2).
  intros ms' md3 (ms0 & HQ & HEQ) HSBM.
  destruct HQ as (r1' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & a4' & a5' & a6' & a7' & Ems0 & Hr1').
  subst ms0.
  pose proof (@c1f_ms_shape fx' _ _ _ ms' HEQ) as Ems'.
  pose proof (fun r Hr => c1f_ms_reg _ _ _ _ _ _ _ ms' r HEQ Hr) as GEQ.
  (* the run writes nothing *)
  assert (HJ3 : @ajournal rc dec_B_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx)
                  (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' W' mem2 md3 dec_ev_6f0).
  { eapply (ajournal_exec segs B LAWS c1f_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 md3 (fun _ => False));
      [exact (proj1 Hcore2) | intros x _; reflexivity | intros x Hx; exact Hx | intros x _; reflexivity
       | exact HSBM | intros a []]. }
  assert (Q2 : YK11.getr (ms_regs ms') (Z_to_bv 5 2) = Z_to_bv 64 (d_sp1 cx))
    by exact (GEQ (Z_to_bv 5 2) eq_refl).
  assert (Q9 : YK11.getr (ms_regs ms') (Z_to_bv 5 9) = YK11.getr regs2 (Z_to_bv 5 9))
    by (etransitivity; [exact (GEQ (Z_to_bv 5 9) eq_refl) | symmetry; exact G9r]).
  assert (Qsp : spZ (ms_regs ms') = spZ regs2).
  { change (bv_unsigned (YK11.getr (ms_regs ms') (Z_to_bv 5 2)) = bv_unsigned (YK11.getr regs2 (Z_to_bv 5 2))).
    rewrite Q2, G2r. reflexivity. }
  destruct (c1_step B cx ly' S' W' regs2 mem2 md2 dec_ev_6f0 res out mode nch ns ly' S' W' (ms_regs ms') mem2 md3
              dec_ev_6f0 HCELLS HROS HRNE Hrom Hcore2 Hmem2 HJ3 Hfrs (fun b Hb => Hb)
              (GEQ (Z_to_bv 5 8) eq_refl) Q9 Qsp
              (GEQ (Z_to_bv 5 3) eq_refl) (GEQ (Z_to_bv 5 4) eq_refl)
              ltac:(intros a _ _; reflexivity)
              ltac:(intros a Ha; split; [reflexivity | exact (proj2 (KF a Ha))])
              ltac:(intros a _; reflexivity) ltac:(intros i _; reflexivity)
              ltac:(intros i _; reflexivity)) as (Hcore3 & Hmem3).
  rewrite Ems'.
  apply (c1s_plain LPL cx res out mode nch ns fx' ly' S' W' (ms_regs ms') mem2 md3 HPRE).
  - split; [exact Hfrm|]. split; [exact Hcore3|]. split; [exact HP|]. split; [exact Hres4|].
    split; [exact Hout4|]. split; [exact Hmle|]. split; [exact Hmok|]. split; [exact Hmem3|].
    unfold dec_b_slot in *. rewrite <- S80'. apply rdword_ext. intros j Hj. reflexivity.
  - split;
      [ transitivity (Z_to_bv 64 (if c1_pok wf fz ft then 1 else 0));
        [exact (GEQ (Z_to_bv 5 19) eq_refl) | rewrite Ep; reflexivity] |].
    split; [exact (GEQ (Z_to_bv 5 20) eq_refl)|]. split; [exact (GEQ (Z_to_bv 5 21) eq_refl)|].
    split; [exact (GEQ (Z_to_bv 5 23) eq_refl)|]. split; [exact (GEQ (Z_to_bv 5 24) eq_refl)|].
    split; [exact (GEQ (Z_to_bv 5 26) eq_refl) | exact (GEQ (Z_to_bv 5 27) eq_refl)].
  - exact (GEQ (Z_to_bv 5 18) eq_refl).
  - exact (GEQ (Z_to_bv 5 22) eq_refl).
  - transitivity r1'; [exact (GEQ (Z_to_bv 5 1) eq_refl)|].
    apply bv_eq. rewrite Hr1'. unfold w64.
    rewrite (MState.unsigned_lit (DEC_A_LLVMF + 1776))
      by (clear; unfold DEC_A_LLVMF, decodeb_text, DecodeBList.AF_LLVMFuzzerTestOneInput; lia).
    unfold C1, DEC_A_LLVMF, decodeb_text, DecodeBList.AF_LLVMFuzzerTestOneInput. clear. lia.
  - exact (GEQ (Z_to_bv 5 10) eq_refl).
  - exact (GEQ (Z_to_bv 5 11) eq_refl).
  - exact (GEQ (Z_to_bv 5 12) eq_refl).
  - exact (GEQ (Z_to_bv 5 13) eq_refl).
  - intros i Hi. etransitivity; [exact (HFILL2 i ltac:(rewrite Hoq; exact Hi)) | reflexivity].
Qed.
(* ---- the call of check_braid at +0x6bc, then the run +0x6c0 .. +0x6d4 ---- *)
Theorem c1k_braid :
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (decodeb_sigma DB___asan_memset)) ->
  (forall fx' : YK11.FPState, @dec_leaf_wr_at rc B (@LPlainLe.dec_reac_decode_plain_le_cg) fx') ->
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LCheckBraid.dec_check_braid_cg) fx') ->
  @c1_K_braid rc B MT RA_LLVMF.
Proof.
  intros AMS LPL LCB cx res out mode nch ns fx' ly' S' W' regs' mem' md' HPRE HST HR Hdok HBR R22b R1 R10 R11 R12 R13.
  pose proof HPRE as (Hret & Hra & Hra4 & Hgp & Htp & Hstk & Hch & Hpay & Hn1 & Hn2 & Hnev & Hlive & Hrom).
  pose proof HST as (Hfrm & Hcore & HP & Hres4 & Hout4 & Hmle & Hmok & Hmem & Hs80).
  pose proof HR as (R19 & R20 & R21 & R23 & R24 & R26 & R27).
  pose proof Hcore as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1al & Hgp' & Htp' & _ & _ & _ & HFpres & _ & Hpayb & Hgarr).
  pose proof (proj1 HJ) as HAR.
  pose proof (c1g_layout B LAWS cx ly' S' W' regs' mem' md' dec_ev_6f0 res out nch ns Hcore HP Hn2 Hpay) as
    (Hsp0 & Hsp1 & H47 & Hinr & Hino & Ho4096 & Hoc & Hoapp & Hr4096 & Hrc & Hro & Hpo & Hof).
  pose proof (c1g_body_len cx Hn2) as Hbl.
  pose proof (@YM05.alloc_ceiling_val rc) as HCEIL.
  pose proof Hmem as (Hfrs' & Hmode & Hfsh & Hgb & S24 & S32 & S40 & S56 & S64 & S72 & S88 & S112).
  pose proof Hmode as (_ & Hnch & Hns & V4 & V8).
  pose proof (c1g_mode B LAWS cx ly' S' W' regs' mem' md' dec_ev_6f0 mode nch ns HCELLS HROS HRNE Hrom Hcore Hmode
                Hfsh) as
    (Hm0 & Hmc & _ & _ & _ & _).
  (* what the decode check gives *)
  assert (HD : CInsp.inspect_wf (dec_b_len (d_n cx)) (d_body cx) = true /\ 0 < nch /\ nch mod 2 = 0 /\
               0 < ns /\ nch * ns <= 480).
  { unfold CDec.decode_ok in Hdok. rewrite !andb_true_iff in Hdok.
    destruct Hdok as ((((Hw & P1) & P2) & P3) & P4).
    apply Z.ltb_lt in P1. apply Z.eqb_eq in P2. apply Z.ltb_lt in P3. apply Z.leb_le in P4.
    exact (conj Hw (conj P1 (conj P2 (conj P3 P4)))). }
  destruct HD as (Hwf & Hn0 & Hev & Hs0 & Hprod).
  assert (Hlen1492 : dec_b_len (d_n cx) = 1492).
  { unfold CInsp.inspect_wf in Hwf. rewrite !andb_true_iff in Hwf.
    destruct Hwf as ((((He & _) & _) & _) & _). apply Z.eqb_eq in He. exact He. }
  assert (Holen : dec_b_olen nch ns = 3 * nch * ns).
  { unfold dec_b_olen.
    rewrite (proj2 (andb_true_iff _ _) (conj (proj2 (Z.ltb_lt 0 nch) Hn0) (proj2 (Z.ltb_lt 0 ns) Hs0))).
    reflexivity. }
  pose proof (req_size_pos (dec_b_len (d_n cx)) ltac:(clear - Hlen1492; lia)) as [Hq1 Hq2].
  pose proof (req_size_pos (dec_b_olen nch ns) ltac:(clear - Holen Hn0 Hs0; nia)) as [Hqo1 Hqo2].
  assert (PW : 2 ^ 64 = 18446744073709551616 /\ 2 ^ 26 = 67108864 /\ 2 ^ 47 = 140737488355328 /\
               2 ^ 32 = 4294967296)
    by (clear; repeat split; vm_compute; reflexivity).
  assert (HN : 2 ^ 64 = 18446744073709551616 /\ 2 ^ 26 = 67108864 /\ 2 ^ 47 = 140737488355328 /\
               2 ^ 32 = 4294967296 /\
               dec_b_len (d_n cx) = 1492 /\ Z.of_nat (length (d_body cx)) = 1492 /\
               1492 <= req_size (dec_b_len (d_n cx)) /\
               dec_b_olen nch ns = 3 * nch * ns /\ 3 * nch * ns <= req_size (dec_b_olen nch ns) /\
               0 < mode /\ mode + 12 <= YM05.alloc_ceiling /\
               0 < nch <= 127 /\ 0 < ns <= 127 /\ nch * ns <= 480 /\ nch mod 2 = 0 /\
               4096 <= res /\ res + req_size (dec_b_len (d_n cx)) <= YM05.alloc_ceiling /\
               4096 <= out /\ out + req_size (dec_b_olen nch ns) <= YM05.alloc_ceiling /\
               (res + req_size (dec_b_len (d_n cx)) <= out \/ out + req_size (dec_b_olen nch ns) <= res) /\
               YM05.alloc_ceiling + 32768 <= d_sp0 cx /\ d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 /\
               d_sp0 cx <= 2 ^ 47 /\ d_sp1 cx mod 32 = 0 /\ d_sp0 cx mod 16 = 0 /\
               140735332483072 <= YM05.alloc_ceiling <= 140737479966720).
  { pose proof (proj1 Hstk) as Hal0. repeat split; try assumption; try (clear - PW; lia);
      try (clear - Hlen1492 Hbl PW; lia); try (clear - Hlen1492 Hq2 PW; lia);
      try (clear - Holen Hqo2 PW; lia); try (clear - Holen PW; lia);
      try (clear - Hn0 Hnch PW; lia); try (clear - Hs0 Hns PW; lia); try (clear - Hprod PW; lia);
      try (clear - Hev PW; lia); try (clear - Hm0 PW; lia); try (clear - Hmc PW; lia);
      try (clear - Hsp0 PW; lia); try (clear - Hsp1 PW; lia); try (clear - H47 PW; lia);
      try (clear - Hr4096 PW; lia); try (clear - Hrc PW; lia); try (clear - Ho4096 PW; lia);
      try (clear - Hoc PW; lia); try (clear - Hro PW; lia); try (clear - HCEIL PW; lia);
      try (clear - Hsp1r PW; lia); try (clear - Hsp1al PW; lia); try (clear - Hal0 PW; lia). }
  assert (Ho16 : d_sp1 cx - d_sp0 cx <= 0) by (clear - HN; lia).
  assert (Hoal : (d_sp1 cx - d_sp0 cx) mod 16 = 0).
  { pose proof (Z.div_mod (d_sp1 cx) 32 ltac:(lia)) as D1.
    pose proof (Z.div_mod (d_sp0 cx) 16 ltac:(lia)) as D2.
    pose proof (Z.div_mod (d_sp1 cx) 16 ltac:(lia)) as D3.
    pose proof (Z.mod_pos_bound (d_sp1 cx) 16 ltac:(lia)) as D4.
    clear - HN D1 D2 D3 D4. lia. }
  assert (Hobud : ESTACK - (d_sp1 cx - d_sp0 cx) <= DEC_LLVMF_STK)
    by (unfold ESTACK, DEC_LLVMF_STK; clear - HN; lia).
  assert (Hretb : YK0s.ret_ok (YK11.getr regs' 1))
    by (rewrite R1; apply YK0s.ret_ok_even; clear; vm_compute; reflexivity).
  assert (HBRAID : dec_crt_braid (aview segs (w_H W') mem') (res + 50) out nch ns)
    by (apply (c1b_braid_of_garr8 W' mem' (d_body cx) res out nch ns);
        [clear - HN; lia | clear - HN; lia | clear - HN; nia | exact Hgb | exact HBR]).
  (* the leaf *)
  eapply SRr_bind;
    [ eapply (dec_leafb_check_braid B LAWS HCELLS LCB W' regs' mem' DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx)
                (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' md' dec_ev_6f0
                (d_sp1 cx - d_sp0 cx) (res + 50) out nch ns res (dec_b_len (d_n cx)) out (dec_b_olen nch ns)
                HJ ltac:(rewrite Hsp; clear - HN; lia) Hoal Ho16 Hobud Hretb Hgp' Htp' R10 R11 R12 R13
                ltac:(clear - HN; lia) ltac:(clear - HN; lia)
                Hinr ltac:(clear - HN; lia) ltac:(clear - HN; nia)
                Hino ltac:(clear - HN; lia) ltac:(clear - HN; lia) HBRAID)
    | ].
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPRES & HKEEP2 & HGR2 & _).
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - ESTACK <= a < d_sp1 cx) ->
    ~ (out <= a < out + req_size (dec_b_olen nch ns)) ->
    aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a).
  { intros a Ha H1 _. apply (HKEEP2 a Ha); [rewrite Hsp; exact H1 | intros Hw; inversion Hw]. }
  destruct (c1g_keep_window B LAWS cx ly' S' W' regs' mem' md' dec_ev_6f0 res out nch ns mem2
              Hcore HP Hn2 Hpay KW HGR2) as (KS & KF & KH & KR & KP).
  destruct (c1_step B cx ly' S' W' regs' mem' md' dec_ev_6f0 res out mode nch ns ly' S' W' regs2 mem2 md2
              dec_ev_6f0 HCELLS HROS HRNE Hrom Hcore
              (conj Hfrs' (conj Hmode (conj Hfsh (conj Hgb (conj S24 (conj S32 (conj S40 (conj S56
                 (conj S64 (conj S72 (conj S88 S112))))))))))) HJ2 Hfrs
              (fun b Hb => Hb)
              (eq_trans (HPRES 8 ltac:(unfold acallee_saved; clear; lia)) eq_refl)
              (eq_trans (HPRES 9 ltac:(unfold acallee_saved; clear; lia)) eq_refl)
              (f_equal bv_unsigned (HPRES 2 ltac:(unfold acallee_saved; clear; lia)))
              (eq_trans (HPRES 3 ltac:(unfold acallee_saved; clear; lia)) eq_refl)
              (eq_trans (HPRES 4 ltac:(unfold acallee_saved; clear; lia)) eq_refl)
              ltac:(intros a Ha _; apply KS; exact Ha) KF KH KR KP) as (Hcore2 & Hmem2).
  pose proof Hmem2 as (Hfrs2 & Hmode2 & Hfsh2 & Hgb2 & S24' & S32' & S40' & S56' & S64' & S72' & S88' & S112').
  assert (S80' : dec_b_slot cx (aview segs (w_H W') mem2) 80 (res + 50)).
  { unfold dec_b_slot in *. rewrite <- Hs80. apply rdword_ext. intros j Hj. apply KS. clear - HN Hj. lia. }
  assert (HST2 : @c1_st rc B MT cx res out mode nch ns dec_ev_6f0 (dec_spent_6f0 MT (d_n cx))
                   (dec_rest_6f0 MT) fx' ly' S' W' regs2 mem2 md2).
  { split; [exact Hfrm|]. split; [exact Hcore2|]. split; [exact HP|]. split; [exact Hres4|].
    split; [exact Hout4|]. split; [exact Hmle|]. split; [exact Hmok|]. split; [exact Hmem2 | exact S80']. }
  assert (HREG2 : c1_regs cx res out mode nch ns regs2).
  { split; [exact (eq_trans (HPRES 19 ltac:(unfold acallee_saved; clear; lia)) R19)|].
    split; [exact (eq_trans (HPRES 20 ltac:(unfold acallee_saved; clear; lia)) R20)|].
    split; [exact (eq_trans (HPRES 21 ltac:(unfold acallee_saved; clear; lia)) R21)|].
    split; [exact (eq_trans (HPRES 23 ltac:(unfold acallee_saved; clear; lia)) R23)|].
    split; [exact (eq_trans (HPRES 24 ltac:(unfold acallee_saved; clear; lia)) R24)|].
    split; [exact (eq_trans (HPRES 26 ltac:(unfold acallee_saved; clear; lia)) R26)
           | exact (eq_trans (HPRES 27 ltac:(unfold acallee_saved; clear; lia)) R27)]. }
  pose proof HREG2 as (R19' & R20' & R21' & R23' & R24' & R26' & R27').
  assert (R9' : YK11.getr regs2 9 = w64 (d_sp1 cx))
    by exact (eq_trans (HPRES 9 ltac:(unfold acallee_saved; clear; lia)) R9).
  assert (Hsp2 : spZ regs2 = d_sp1 cx)
    by (etransitivity; [exact (f_equal bv_unsigned (HPRES 2 ltac:(unfold acallee_saved; clear; lia))) | exact Hsp]).
  (* the run +0x6c0 .. +0x6d4 *)
  set (wf := CInsp.inspect_wf (dec_b_len (d_n cx)) (d_body cx)).
  set (fz := ((0 <? nch) && (0 <? ns))%bool).
  set (ft := (dec_b_prod nch ns <? 481)).
  assert (Ep : c1_pok wf fz ft = CPlain.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns)
    by exact (c1g_pok (dec_b_len (d_n cx)) (d_body cx) nch ns Hnch Hns).
  assert (G2r : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (d_sp1 cx))
    by (apply bv_eq; rewrite (MState.unsigned_lit (d_sp1 cx)) by (clear - HN; lia); exact Hsp2).
  assert (G9r : YK11.getr regs2 (Z_to_bv 5 9) = Z_to_bv 64 (d_sp1 cx)) by exact R9'.
  assert (G19r : YK11.getr regs2 (Z_to_bv 5 19) = Z_to_bv 64 (if c1_pok wf fz ft then 1 else 0))
    by (rewrite Ep; exact R19').
  assert (G20r : YK11.getr regs2 (Z_to_bv 5 20) = Z_to_bv 64 (dec_b_len (d_n cx))) by exact R20'.
  assert (G21r : YK11.getr regs2 (Z_to_bv 5 21) = Z_to_bv 64 mode) by exact R21'.
  assert (G22r : YK11.getr regs2 (Z_to_bv 5 22) = Z_to_bv 64 out)
    by exact (eq_trans (HPRES 22 ltac:(unfold acallee_saved; clear; lia)) R22b).
  assert (G23r : YK11.getr regs2 (Z_to_bv 5 23) = Z_to_bv 64 nch) by exact R23'.
  assert (G24r : YK11.getr regs2 (Z_to_bv 5 24) = Z_to_bv 64 (if fz then 1 else 0)) by exact R24'.
  assert (G26r : YK11.getr regs2 (Z_to_bv 5 26) = Z_to_bv 64 (dec_b_olen nch ns)) by exact R26'.
  assert (RSTK : ExecF.rng (LeafCgKit.RNG_W (world segs) (@w_H segs) W') (d_sp1 cx + 24) 72)
    by (apply (c1e_rng_stk B cx ly' S' W' regs2 mem2 md2 dec_ev_6f0);
        [exact Hcore2 | unfold DEC_LLVMF_STK; clear - HN; lia | clear - HN; lia | clear; lia]).
  assert (RD40 : ov_read_bytes Img0.rsegs mem2 (Z_to_bv 64 (d_sp1 cx + 40)) 8 =
                 Some (Mem.le8 (Z_to_bv 64 res)))
    by (apply (c1e_slot_rd8 B cx ly' S' W' regs2 mem2 md2 dec_ev_6f0);
        [exact Hcore2 | clear; lia | clear; lia | exact S40']).
  assert (RD88 : ov_read_bytes Img0.rsegs mem2 (Z_to_bv 64 (d_sp1 cx + 88)) 8 =
                 Some (Mem.le8 (Z_to_bv 64 out)))
    by (apply (c1e_slot_rd8 B cx ly' S' W' regs2 mem2 md2 dec_ev_6f0);
        [exact Hcore2 | clear; lia | clear; lia | exact S88']).
  pose proof (c1_run_abraid (LeafCgKit.RNG_W (world segs) (@w_H segs) W')
    (YK11.getr regs2 (Z_to_bv 5 3)) (YK11.getr regs2 (Z_to_bv 5 4)) (YK11.getr regs2 (Z_to_bv 5 8))
    (YK11.getr regs2 (Z_to_bv 5 25)) (@fp_regs fx') (@fp_csr fx')
    (d_sp1 cx) res out mode (dec_b_len (d_n cx)) (dec_b_olen nch ns) nch wf fz ft
    ltac:(clear - HN; lia) ltac:(clear - HN; lia) RSTK mem2 RD40 RD88
    (YK11.getr regs2 (Z_to_bv 5 1)) (YK11.getr regs2 (Z_to_bv 5 5)) (YK11.getr regs2 (Z_to_bv 5 6))
    (YK11.getr regs2 (Z_to_bv 5 7)) (YK11.getr regs2 (Z_to_bv 5 28)) (YK11.getr regs2 (Z_to_bv 5 29))
    (YK11.getr regs2 (Z_to_bv 5 30)) (YK11.getr regs2 (Z_to_bv 5 31))
    (YK11.getr regs2 (Z_to_bv 5 10)) (YK11.getr regs2 (Z_to_bv 5 11)) (YK11.getr regs2 (Z_to_bv 5 12))
    (YK11.getr regs2 (Z_to_bv 5 13)) (YK11.getr regs2 (Z_to_bv 5 14)) (YK11.getr regs2 (Z_to_bv 5 15))
    (YK11.getr regs2 (Z_to_bv 5 16)) (YK11.getr regs2 (Z_to_bv 5 17))
    (YK11.getr regs2 (Z_to_bv 5 18)) (YK11.getr regs2 (Z_to_bv 5 27))) as HRUN.
  lazymatch type of HRUN with ExecF.evtF _ _ ?P _ =>
    assert (HRUN2 : ExecF.evtF Img0.rsegs (LeafCgKit.RNG_W (world segs) (@w_H segs) W') P
                      (@LeafCgKit.ms_of_regs fx' (DEC_A_LLVMF + 0x6c0) regs2 mem2)) end.
  { unfold LeafCgKit.ms_of_regs.
    rewrite G2r, G9r, G19r, G20r, G21r, G22r, G23r, G24r, G26r.
    replace (LeafCgKit.w64 (DEC_A_LLVMF + 1728)) with (Z_to_bv 64 (C1 1728))
      by (unfold LeafCgKit.w64; f_equal; unfold C1, DEC_A_LLVMF, DecodeBList.AF_LLVMFuzzerTestOneInput; clear; lia).
    exact HRUN. }
  clear HRUN.
  rewrite R1.
  apply (c1f_run W' regs2 mem2 md2 (DEC_A_LLVMF + 0x6c0) _ _ HRUN2).
  intros ms' md3 (ms0 & HQ & HEQ) HSBM.
  destruct HQ as (a3' & r1' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & a4' & a5' & a6' & a7' & Ems0 & Hr1').
  subst ms0.
  pose proof (@c1f_ms_shape fx' _ _ _ ms' HEQ) as Ems'.
  pose proof (fun r Hr => c1f_ms_reg _ _ _ _ _ _ _ ms' r HEQ Hr) as GEQ.
  assert (HJ3 : @ajournal rc dec_B_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx)
                  (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' W' mem2 md3 dec_ev_6f0).
  { eapply (ajournal_exec segs B LAWS c1f_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 md3 (fun _ => False));
      [exact (proj1 Hcore2) | intros x _; reflexivity | intros x Hx; exact Hx | intros x _; reflexivity
       | exact HSBM | intros a []]. }
  assert (Q2 : YK11.getr (ms_regs ms') (Z_to_bv 5 2) = Z_to_bv 64 (d_sp1 cx))
    by exact (GEQ (Z_to_bv 5 2) eq_refl).
  assert (Q9 : YK11.getr (ms_regs ms') (Z_to_bv 5 9) = YK11.getr regs2 (Z_to_bv 5 9))
    by (etransitivity; [exact (GEQ (Z_to_bv 5 9) eq_refl) | symmetry; exact G9r]).
  assert (Qsp : spZ (ms_regs ms') = spZ regs2).
  { change (bv_unsigned (YK11.getr (ms_regs ms') (Z_to_bv 5 2)) = bv_unsigned (YK11.getr regs2 (Z_to_bv 5 2))).
    rewrite Q2, G2r. reflexivity. }
  destruct (c1_step B cx ly' S' W' regs2 mem2 md2 dec_ev_6f0 res out mode nch ns ly' S' W' (ms_regs ms') mem2 md3
              dec_ev_6f0 HCELLS HROS HRNE Hrom Hcore2 Hmem2 HJ3 Hfrs (fun b Hb => Hb)
              (GEQ (Z_to_bv 5 8) eq_refl) Q9 Qsp
              (GEQ (Z_to_bv 5 3) eq_refl) (GEQ (Z_to_bv 5 4) eq_refl)
              ltac:(intros a _ _; reflexivity)
              ltac:(intros a Ha; split; [reflexivity | exact (proj2 (KF a Ha))])
              ltac:(intros a _; reflexivity) ltac:(intros i _; reflexivity)
              ltac:(intros i _; reflexivity)) as (Hcore3 & Hmem3).
  rewrite Ems'.
  apply (c1k_memset AMS LPL cx res out mode nch ns fx' ly' S' W' (ms_regs ms') mem2 md3 HPRE).
  - split; [exact Hfrm|]. split; [exact Hcore3|]. split; [exact HP|]. split; [exact Hres4|].
    split; [exact Hout4|]. split; [exact Hmle|]. split; [exact Hmok|]. split; [exact Hmem3|].
    unfold dec_b_slot in *. rewrite <- S80'. apply rdword_ext. intros j Hj. reflexivity.
  - split;
      [ transitivity (Z_to_bv 64 (if c1_pok wf fz ft then 1 else 0));
        [exact (GEQ (Z_to_bv 5 19) eq_refl) | rewrite Ep; reflexivity] |].
    split; [exact (GEQ (Z_to_bv 5 20) eq_refl)|]. split; [exact (GEQ (Z_to_bv 5 21) eq_refl)|].
    split; [exact (GEQ (Z_to_bv 5 23) eq_refl)|]. split; [exact (GEQ (Z_to_bv 5 24) eq_refl)|].
    split; [exact (GEQ (Z_to_bv 5 26) eq_refl) | exact (GEQ (Z_to_bv 5 27) eq_refl)].
  - exact (GEQ (Z_to_bv 5 18) eq_refl).
  - transitivity r1'; [exact (GEQ (Z_to_bv 5 1) eq_refl)|].
    apply bv_eq. rewrite Hr1'. unfold w64.
    rewrite (MState.unsigned_lit (DEC_A_LLVMF + 1752))
      by (clear; unfold DEC_A_LLVMF, decodeb_text, DecodeBList.AF_LLVMFuzzerTestOneInput; lia).
    unfold C1, DEC_A_LLVMF, decodeb_text, DecodeBList.AF_LLVMFuzzerTestOneInput. clear. lia.
  - exact (GEQ (Z_to_bv 5 10) eq_refl).
  - exact (GEQ (Z_to_bv 5 11) eq_refl).
  - exact (GEQ (Z_to_bv 5 12) eq_refl).
Qed.
End C1Stage.
