(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac Frame.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState Inflate InflateSync.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout InflMem Sync6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 IRep6 InflArmLib6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import ExSmallIface FlLibStmtU.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.FMQ6 Require CallocTail6u.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition pc_isy : Z := 0x21998.
Definition pc_B : Z := 0x21a20.
Definition pc_DL : Z := 0x21ae8.
Definition pc_S1 : Z := 0x21b00.
Definition pc_K0 : Z := 0x21b38.
Definition pc_S1x : Z := 0x21b40.
Definition pc_E : Z := 0x21b48.
Definition pc_S2 : Z := 0x21b78.
Definition pc_G : Z := 0x21bc8.
Definition pc_X : Z := 0x21c8c.
Definition pc_TRAP : Z := 0x21cb0.

Section SYNCU.
  Variables (regs : bvmap 5 word) (mem : word -> option byte).
  Variables (S ZP WB : Z) (s : inflate_state) (zc : ZCall) (sp ra inp outp zcl fa ff : Z) (MA : Z -> Z).
  Local Abbreviation input := (zc_input zc).
  Local Abbreviation n := (zlength (zc_input zc)).
  Local Abbreviation RS := s6u_segs.

  Hypothesis G10 : getr regs 10 = zw ZP.
  Hypothesis G2 : getr regs 2 = zw sp.
  Hypothesis G1 : getr regs 1 = zw ra.
  Hypothesis RA : ra_ok ra.
  Hypothesis SP16 : sp mod 16 = 0.
  Hypothesis HZC : zcl + FL_FRA <= sp.
  Hypothesis SP47 : sp <= 2 ^ 47.
  Hypothesis HTOP : FL_IMG_TOP <= zcl.
  Hypothesis BOK : blocks_ok mem zcl (iblocks (IP ZP S WB)).
  Hypothesis IC : img_clear mem.
  Hypothesis STRM0 : 0 < ZP.
  Hypothesis STRM63 : ZP + 112 <= 2 ^ 63.
  Hypothesis STRM8 : ZP mod 8 = 0.
  Hypothesis INP0 : 0 < inp.
  Hypothesis SOK1 : store_ok RS mem (Z_to_bv 64 (sp - 96)) 96%nat = true.
  Hypothesis SOK2 : store_ok RS mem (Z_to_bv 64 ZP) 112%nat = true.
  Hypothesis AP : all_apart ((sp - 96, 96) :: (ZP, 112) :: (inp, n) :: iblocks (IP ZP S WB)).
  Hypothesis IMG : forall a k, In (a, k) [(sp - 96, 96); (ZP, 112); (inp, n)] -> a + k <= FL_RO_LO \/ FL_IMG_TOP <= a.
  Hypothesis B1 : inp + n < 2 ^ 63.
  Hypothesis B2 : n < 2 ^ 32.
  Hypothesis IR : ISREP6 mem S ZP WB s.
  Hypothesis HLD : holds RS mem inp input.
  Hypothesis ZS : izs_cells MA mem ZP inp n outp (zc_avail_out zc) (zc_strm zc) S fa ff.
  Hypothesis FA : fa = FL_ZCALLOC.
  Hypothesis FF : ff = FL_ZCFREE.
  Hypothesis SAFE : SSAFE6 s zc.
  Hypothesis MA0 : MA MSG_NULL = 0.

  Lemma ra_facts : 0 <= ra < 2 ^ 64 /\ ret_ok (zw ra).
  Proof using RA. destruct RA as [R1 R2]. split; [exact R1| exact (ret_ok_lit ra R1 R2)]. Qed.

  Lemma n_nonneg : 0 <= n.
  Proof using sp ZP. unfold zlength. lia. Qed.

  Lemma safe_facts : 0 <= is_bits s < 40 /\ 0 <= is_hold s < 2 ^ 64 /\ 0 <= is_have s < 2 ^ 31 /\
    - 2 ^ 31 <= is_flags s < 2 ^ 31 /\ 0 <= is_wrap s < 2 ^ 31 /\ 0 <= is_mode s < 2 ^ 31 /\
    Forall (fun b => 0 <= b < 256) input /\ n < 2 ^ 31.
  Proof using SAFE. exact (proj1 SAFE). Qed.
  (* 1.4: the reachable-state facts that make the 1.3.1 model's sync agree with 1.4's code *)
  Lemma sync14_facts : SYNC14 s.
  Proof using SAFE. exact (proj2 SAFE). Qed.

  Lemma zs_facts :
    cell RS mem (ZP + 0) 8 inp /\ cell RS mem (ZP + 8) 4 n /\ cell RS mem (ZP + 16) 8 (zs_total_in (zc_strm zc)) /\
    cell RS mem (ZP + 24) 8 outp /\ cell RS mem (ZP + 32) 4 (zc_avail_out zc) /\ cell RS mem (ZP + 40) 8 (zs_total_out (zc_strm zc)) /\
    cell RS mem (ZP + 48) 8 (MA (zs_msg (zc_strm zc))) /\ cell RS mem (ZP + 56) 8 S /\ cell RS mem (ZP + 64) 8 fa /\
    cell RS mem (ZP + 72) 8 ff /\ cell RS mem (ZP + 80) 8 0 /\ cell RS mem (ZP + 96) 8 (zs_adler (zc_strm zc)).
  Proof using ZS.
    destruct ZS as (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C96).
    unfold cell8, cell4 in *. unfold cell. rewrite Z.add_0_r. repeat split; assumption.
  Qed.

  Lemma st_facts : is6_scalars mem S (ISP ZP WB) s /\ 0 < S /\ S mod 16 = 0 /\ S + 7176 <= zcl /\
    (S + 7176 <= 0x10000 \/ FL_IMG_TOP <= S) /\ store_ok RS mem (Z_to_bv 64 S) (Z.to_nat 7176) = true.
  Proof using IR BOK.
    destruct IR as (SC & _). split; [exact SC|].
    unfold blocks_ok, iblocks in BOK. cbn [ip_p ip_w ip_strm] in BOK. apply Forall_inv in BOK. cbn [fst snd] in BOK.
    destruct BOK as (M16 & P0 & TOP & OFF & SOK). unfold FL_ISTATE_N in *. repeat split; assumption.
  Qed.

  Lemma maps : (forall x : word, S <= bv_unsigned x < S + 7176 -> mem x <> None) /\
               (forall x : word, sp - 96 <= bv_unsigned x < sp - 96 + 96 -> mem x <> None) /\
               (forall x : word, ZP <= bv_unsigned x < ZP + 112 -> mem x <> None).
  Proof using STRM8 IR IMG SOK2 SOK1 STRM63 STRM0 BOK HTOP SP47 HZC RA zcl inp ra zc s WB.
    pose proof st_facts as (_ & S0 & _ & STOP & OFF & SSOK). pose proof ra_facts as [RAB _].
    assert (KTOP : FL_IMG_TOP = 0x5f000) by reflexivity. assert (KRO : FL_RO_LO = 0x10000) by reflexivity.
    assert (KFRA : FL_FRA = 1024) by reflexivity. rewrite KTOP in OFF, HTOP. rewrite KFRA in HZC.
    split; [| split].
    - apply (FMQ6.CallocTail6u.mapped_of_store_ok6u mem S 7176); [lia| lia| lia| exact OFF| exact SSOK].
    - apply (FMQ6.CallocTail6u.mapped_of_store_ok6u mem (sp - 96) 96); [lia| lia| lia| | exact SOK1].
      specialize (IMG (sp - 96) 96 ltac:(left; reflexivity)). rewrite KTOP, KRO in IMG. exact IMG.
    - apply (FMQ6.CallocTail6u.mapped_of_store_ok6u mem ZP 112); [lia| lia| lia| | exact SOK2].
      specialize (IMG ZP 112 ltac:(right; left; reflexivity)). rewrite KTOP, KRO in IMG. exact IMG.
  Qed.

  Lemma consts : FL_ZCALLOC = 0x1a9f4 /\ FL_ZCFREE = 0x1aa04 /\ FL_FRA = 1024 /\ FL_IMG_TOP = 0x5f000 /\ FL_RO_LO = 0x10000 /\ FL_ISTATE_N = 7176 /\ FL_WIN_N = 32768.
  Proof using. repeat split. Qed.

  Local Ltac facts :=
    pose proof ra_facts as (RAB & RET); pose proof n_nonneg as N0';
    pose proof safe_facts as (Bbits & Bhold & Bhave & Bflags & Bwrap & Bmode & Bin & Bn);
    pose proof zs_facts as (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C96);
    pose proof st_facts as (SC & S0 & S16 & STOP & SOFF & SSOK); pose proof maps as (WS & WF & WZ);
    pose proof consts as (KA & KF & KFRA & KTOP & KRO & KIS & KWN);
    pose proof (is6_strm _ _ _ _ SC) as D0; pose proof (is6_mode _ _ _ _ SC) as D8; pose proof (is6_wrap _ _ _ _ SC) as D16;
    pose proof (is6_flags _ _ _ _ SC) as D24; pose proof (is6_hold _ _ _ _ SC) as D80; pose proof (is6_bits _ _ _ _ SC) as D88;
    pose proof (is6_have _ _ _ _ SC) as D140; cbn [q_strm] in D0;
    pose proof D0 as D0'; rewrite Z.add_0_r in D0'; pose proof C0 as C0'; rewrite Z.add_0_r in C0';
    rewrite KA in FA; rewrite KF in FF; rewrite KFRA in HZC; rewrite KTOP in HTOP.

  Definition FP : list (word * Z) := [(zw (sp - 96), 96); (zw ZP, 112); (zw S, 7176)].
  Definition KEEP (m : word -> option byte) : Prop :=
    cells RS m (S + 168) 2 2 320 (arr_get (is_lens s)) /\ cells RS m (S + 808) 2 2 288 (arr_get (is_work s)) /\
    cells RS m (S + 1384) 4 4 1444 (arr_get (is_codes s)) /\
    (WB <> 0 -> cells RS m WB 1 1 (arr_len (is_window s)) (arr_get (is_window s))) /\
    holds RS m inp input /\ frame_mod mem m FP /\
    (forall x : word, S <= bv_unsigned x < S + 7176 -> m x <> None) /\
    (forall x : word, sp - 96 <= bv_unsigned x < sp - 96 + 96 -> m x <> None) /\
    (forall x : word, ZP <= bv_unsigned x < ZP + 112 -> m x <> None).
  Definition ZSC (m : word -> option byte) (ni ai : Z) (z : zstrm) : Prop :=
    cell RS m (ZP + 0) 8 ni /\ cell RS m (ZP + 8) 4 ai /\ cell RS m (ZP + 16) 8 (zs_total_in z) /\
    cell RS m (ZP + 24) 8 outp /\ cell RS m (ZP + 32) 4 (zc_avail_out zc) /\ cell RS m (ZP + 40) 8 (zs_total_out z) /\
    cell RS m (ZP + 48) 8 (MA (zs_msg z)) /\ cell RS m (ZP + 56) 8 S /\ cell RS m (ZP + 64) 8 fa /\
    cell RS m (ZP + 72) 8 ff /\ cell RS m (ZP + 80) 8 0 /\ cell RS m (ZP + 96) 8 (zs_adler z).
  Definition wr_ok (b len : Z) : Prop :=
    (S + 8 <= b /\ b + len <= S + 168) \/ (S + 7160 <= b /\ b + len <= S + 7176) \/
    (sp - 96 <= b /\ b + len <= sp) \/ (ZP <= b /\ b + len <= ZP + 112).

  (* 1.4: inflateSync saves ra, s0-s5 at sp-8 .. sp-56 and reloads them at its exit *)
  Definition SV (m : word -> option byte) : Prop :=
    cell RS m (sp + -8) 8 (bv_unsigned (getr regs 1)) /\ cell RS m (sp + -16) 8 (bv_unsigned (getr regs 8)) /\
    cell RS m (sp + -24) 8 (bv_unsigned (getr regs 9)) /\ cell RS m (sp + -32) 8 (bv_unsigned (getr regs 18)) /\
    cell RS m (sp + -40) 8 (bv_unsigned (getr regs 19)) /\ cell RS m (sp + -48) 8 (bv_unsigned (getr regs 20)).
  Lemma SV_write : forall m (b : Z) bs, SV m -> 96 <= sp -> sp <= 2 ^ 47 ->
    0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 63 -> (b + Z.of_nat (length bs) <= sp - 48 \/ sp <= b) ->
    SV (wbytes m (zw b) bs).
  Proof using.
    intros m b bs H P96 P47 Hb0 Hb1 Hd. destruct H as (C1 & C2 & C3 & C4 & C5 & C6).
    clear - C1 C2 C3 C4 C5 C6 P96 P47 Hb0 Hb1 Hd.
    repeat split; (apply cell_write_other; [assumption| lia| cbn; lia| lia| lia| cbn; lia]).
  Qed.
  Definition RESTORED (R : bvmap 5 word) : Prop :=
    getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\ getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20.
  Ltac fin_one HR k := let Q := fresh "Q" in symex_reg HR (k : reg) as Q; rewrite Q; first [reflexivity | exact (Z_to_bv_bv_unsigned 64 _)].
  Ltac fin_restored HR :=
    unfold RESTORED; repeat split;
    [ fin_one HR (8%bv : reg) | fin_one HR (9%bv : reg) | fin_one HR (18%bv : reg) | fin_one HR (19%bv : reg) | fin_one HR (20%bv : reg) ].
  Ltac tcell H :=
    rewrite ?word_le_Z;
    first [ exact H
          | apply cell_write_same; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]
          | eapply cell_write_other;
            [ tcell H
            | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia
            | cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia
            | cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia ] ].
  Ltac sv_peel H := repeat (first [exact H | apply SV_write; [| lia| lia| lia| cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia]]).

  Lemma KEEP0 : KEEP mem.
  Proof using STRM8 HLD IR IMG SOK2 SOK1 STRM63 STRM0 BOK HTOP SP47 HZC RA zcl ra.
    destruct IR as (SC & L & W & C & WN & _). pose proof maps as (WS & WF & WZ).
    repeat split; try assumption. apply mem_grows_refl.
  Qed.
  Lemma ZSC0 : ZSC mem inp n (zc_strm zc).
  Proof using ZS. exact zs_facts. Qed.

  (* 1.4: inflateSync's frame is 64 bytes (`add sp,sp,-64` at 0x1eeb4), and the inflateReset it calls (0x1cc0c) pushes 32 more below it, so the stack region is [sp - 96, sp). inflateReset's zfree arm (wbits <> reqbits) and inflateSync's own (wbits = 0) are not reached: SYNC14 gives wbits = 15, and the rep's reqbits is the constant 15 *)
  Lemma layout : 0 < S /\ S + 7176 <= 2 ^ 63 /\ 96 <= sp /\ sp <= 2 ^ 47 /\ 0 < ZP /\ ZP + 112 <= 2 ^ 63 /\ 0 < inp /\ inp + n < 2 ^ 63 /\ 0 <= n /\
    apart (sp - 96) 96 ZP 112 /\ apart (sp - 96) 96 inp n /\ apart (sp - 96) 96 S 7176 /\
    apart ZP 112 inp n /\ apart ZP 112 S 7176 /\ apart inp n S 7176 /\
    (WB <> 0 -> apart (sp - 96) 96 WB 32768 /\ apart ZP 112 WB 32768 /\ apart inp n WB 32768 /\ apart S 7176 WB 32768 /\ 0 < WB /\ WB + 32768 <= 2 ^ 63).
  Proof using STRM8 IR B1 AP INP0 STRM63 STRM0 BOK HTOP SP47 HZC RA zcl ra s mem.
    pose proof st_facts as (_ & S0 & _ & STOP & _ & _). pose proof ra_facts as [RAB _]. pose proof n_nonneg as N0'.
    pose proof consts as (KA & KF & KFRA & KTOP & KRO & KIS & KWN). rewrite KFRA in HZC. rewrite KTOP in HTOP.
    unfold all_apart, apart_from_all, iblocks in AP. cbn [ip_p ip_w ip_strm] in AP. rewrite KIS, KWN in AP.
    destruct (Z.eqb_spec WB 0) as [W0|W0].
    - cbn [all_apart apart_from_all app] in AP. destruct AP as ((A1 & A2 & A3 & _) & (A4 & A5 & _) & (A6 & _) & _).
      repeat split; try assumption; try lia.
    - cbn [all_apart apart_from_all app] in AP. destruct AP as ((A1 & A2 & A3 & A7 & _) & (A4 & A5 & A8 & _) & (A6 & A9 & _) & (A10 & _) & _).
      unfold blocks_ok, iblocks in BOK. cbn [ip_p ip_w ip_strm] in BOK. replace (WB =? 0) with false in BOK by (symmetry; apply Z.eqb_neq; exact W0).
      apply Forall_inv_tail, Forall_inv in BOK. cbn [fst snd] in BOK. rewrite KWN in BOK. destruct BOK as (_ & WB0 & WTOP & _).
      repeat split; try assumption; try lia.
  Qed.

  Lemma holds_write_other : forall m (b : Z) bs, holds RS m inp input ->
    0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 63 -> (inp + n <= b \/ b + Z.of_nat (length bs) <= inp) ->
    holds RS (wbytes m (zw b) bs) inp input.
  Proof using STRM8 IR B1 AP INP0 STRM63 STRM0 BOK HTOP SP47 HZC RA zcl ra sp s WB ZP S mem.
    intros m b bs H Hb0 Hb1 Hd. pose proof layout as LY. unfold holds in *. unfold zw. rewrite rdn_wbytes_out.
    all: change (Z_to_bv 64) with zw; rewrite ?u_zw_small by lia. 1: exact H. all: rewrite ?length_map; unfold zlength in *; lia.
  Qed.

  Lemma KEEP_write : forall m (b : Z) bs, KEEP m -> wr_ok b (Z.of_nat (length bs)) -> KEEP (wbytes m (zw b) bs).
  Proof using STRM8 IR B1 AP INP0 STRM63 STRM0 BOK HTOP SP47 HZC RA zcl ra.
    intros m b bs (L & W & C & WN & HB & FM & MS & MF & MZ) OK.
    pose proof layout as (S0 & S63 & P16 & P47 & Z0 & Z63 & I0 & I63 & N0 & A1 & A2 & A3 & A4 & A5 & A6 & LW). unfold wr_ok in OK. unfold apart in *.
    destruct IR as (_ & _ & _ & _ & _ & _ & WL).
    assert (LEN : 0 <= Z.of_nat (length bs)) by lia.
    unfold KEEP. repeat match goal with |- _ /\ _ => split end.
    - apply cells_write_other; [exact L| lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 S0; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 S63; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK S0 P16 Z0; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK S63 P47 Z63 LEN; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK LEN A3 A5; lia].
    - apply cells_write_other; [exact W| lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 S0; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 S63; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK S0 P16 Z0; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK S63 P47 Z63 LEN; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK LEN A3 A5; lia].
    - apply cells_write_other; [exact C| lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 S0; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 S63; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK S0 P16 Z0; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK S63 P47 Z63 LEN; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK LEN A3 A5; lia].
    - intros W0. specialize (WN W0). specialize (LW W0). specialize (WL W0). rewrite WL in *. destruct LW as (B1' & B2' & B3' & B4' & B5' & B6').
      apply cells_write_other; [exact WN| lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 B5'; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 B6'; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK S0 P16 Z0; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK S63 P47 Z63 LEN; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK LEN B1' B2' B4'; lia].
    - apply holds_write_other; [exact HB| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK S0 P16 Z0; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK S63 P47 Z63 LEN; lia| clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK LEN A2 A4 A6; lia].
    - eapply frame_mod_trans_same; [exact FM|].
      eapply frame_mod_weaken; [| apply (frame_mod_wbytes m (zw b) bs); rewrite u_zw_small by (clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK S0 P16 Z0 S63 P47 Z63 LEN; lia); clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK S63 P47 Z63; lia].
      intros a Ha. unfold FP in Ha. cbn [outside] in Ha |- *. unfold in_rng in *.
      rewrite !u_zw_small in Ha by (clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 S0 S63 P16 P47 Z0 Z63; lia). rewrite u_zw_small by (clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 OK S0 P16 Z0 S63 P47 Z63 LEN; lia).
      split; [clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 Ha OK LEN; lia| exact I].
    - intros x Hx. apply wbytes_grows. exact (MS x Hx).
    - intros x Hx. apply wbytes_grows. exact (MF x Hx).
    - intros x Hx. apply wbytes_grows. exact (MZ x Hx).
  Qed.

  Lemma ZSC_write_other : forall m ni ai z (b : Z) bs, ZSC m ni ai z ->
    0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 63 -> (ZP + 112 <= b \/ b + Z.of_nat (length bs) <= ZP) ->
    ZSC (wbytes m (zw b) bs) ni ai z.
  Proof using STRM8 STRM63 STRM0 sp.
    intros m ni ai z b bs H Hb0 Hb1 Hd. pose proof STRM0 as Z0. pose proof STRM63 as Z63.
    destruct H as (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C96).
    repeat split; (apply cell_write_other; [assumption| lia| cbn; lia| lia| lia| cbn; lia]).
  Qed.

  Lemma is6_write_other : forall m p s1 (b : Z) bs, is6_scalars m S p s1 ->
    0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 63 -> (S + 7176 <= b \/ b + Z.of_nat (length bs) <= S) ->
    is6_scalars (wbytes m (zw b) bs) S p s1.
  Proof using STRM8 IR B1 AP INP0 STRM63 STRM0 BOK HTOP SP47 HZC RA zcl inp ra sp zc s WB ZP mem.
    intros m p s1 b bs H Hb0 Hb1 Hd. pose proof layout as (S0 & S63 & _).
    rewrite is6_scalars_isl in *.
    apply isl_scalars_frame; [exact H| lia| unfold isl_SIZE; lia| lia| lia| unfold isl_SIZE; lia].
  Qed.

  Ltac is6_peel1 :=
    lazymatch goal with
    | |- is6_scalars (wbytes _ (zw (S + 8)) _) _ _ _ => apply is6_upd_mode
    | |- is6_scalars (wbytes _ (zw (S + 12)) _) _ _ _ => apply is6_upd_last
    | |- is6_scalars (wbytes _ (zw (S + 16)) _) _ _ _ => apply is6_upd_wrap
    | |- is6_scalars (wbytes _ (zw (S + 24)) _) _ _ _ => apply is6_upd_havedict
    | |- is6_scalars (wbytes _ (zw (S + 28)) _) _ _ _ => apply is6_upd_flags
    | |- is6_scalars (wbytes _ (zw (S + 32)) _) _ _ _ => apply is6_upd_dmax
    | |- is6_scalars (wbytes _ (zw (S + 48)) _) _ _ _ => apply is6_upd_total
    | |- is6_scalars (wbytes _ (zw (S + 56)) _) _ _ _ => apply is6_upd_head
    | |- is6_scalars (wbytes _ (zw (S + 72)) _) _ _ _ => apply is6_upd_wsize
    | |- is6_scalars (wbytes _ (zw (S + 76)) _) _ _ _ => apply is6_upd_whave
    | |- is6_scalars (wbytes _ (zw (S + 80)) _) _ _ _ => apply is6_upd_wnext
    | |- is6_scalars (wbytes _ (zw (S + 96)) _) _ _ _ => apply is6_upd_hold
    | |- is6_scalars (wbytes _ (zw (S + 104)) _) _ _ _ => apply is6_upd_bits
    | |- is6_scalars (wbytes _ (zw (S + 120)) _) _ _ _ => apply is6_upd_lencode
    | |- is6_scalars (wbytes _ (zw (S + 128)) _) _ _ _ => apply is6_upd_distcode
    | |- is6_scalars (wbytes _ (zw (S + 156)) _) _ _ _ => apply is6_upd_have
    | |- is6_scalars (wbytes _ (zw (S + 160)) _) _ _ _ => apply is6_upd_next
    | |- is6_scalars (wbytes _ (zw (S + 7160)) _) _ _ _ => apply is6_upd_sane
    | |- is6_scalars (wbytes _ (zw (S + 7164)) _) _ _ _ => apply is6_upd_back
    | |- is6_scalars (wbytes _ (zw _) _) _ _ _ =>
        apply is6_write_other; [| lia| cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia]
    end.
  Ltac is6_peel H := repeat (first [exact H | is6_peel1]); try (unfold is6_SIZE; lia).
  Ltac pow8_norm := repeat match goal with |- context [2 ^ (8 * ?k)] => let e := eval vm_compute in (8 * k) in change (2 ^ (8 * k)) with (2 ^ e) end.
  Ltac keep_peel H := repeat (first [exact H | apply KEEP_write; [| unfold wr_ok; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia]]).
  Ltac zsc_peel H := repeat (first [exact H | apply ZSC_write_other; [| lia| cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia]]).

  Definition cfgA : cfg := CFG [] [] [EVar 1%nat] [pc_B] [].
  Local Ltac runA dirs R HR Hfr Hms :=
    symex s6u_segs cfgA 60%nat dirs
      [RVal (EVar 35%nat); RVal (EVar 36%nat); RVal (EVar 33%nat); RVal (EVar 32%nat); RVal (EVar 37%nat); RVal (EVar 38%nat); RVal (EVar 39%nat)]
      [(10, EVar 32%nat); (2, EVar 34%nat)]
      [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 64); (36%nat, 2 ^ 64); (37%nat, 2 ^ 31); (38%nat, 2 ^ 31); (39%nat, 40)]
      NoRegions [ZP; S; sp; fa; ff; is_mode s; n; is_bits s] NoVals F0 F0'
      (mkst regs (Z_to_bv 64 pc_isy) mem s6u_rom) R HR Hfr Hms.

  Lemma align_facts : ZP mod 2 ^ 3 = 0 /\ S mod 2 ^ 3 = 0.
  Proof using IR STRM8 BOK zcl sp s WB mem.
    pose proof st_facts as (_ & S0 & S16 & _). change (2 ^ 3) with 8.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split; [exact STRM8|]. Z.to_euclidean_division_equations. lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Local Ltac layfacts :=
    pose proof layout as (_ & S63 & P96 & P47' & _ & Z63 & _ & _ & _ & A1 & A2 & A3 & A4 & A5 & A6 & _); unfold apart in A1, A2, A3, A4, A5, A6.

  Lemma syA_ok :
    inflateStateCheck s = false -> ~ (n = 0 /\ is_bits s < 8) ->
    exists R m1, msteps RS (mkst regs (Z_to_bv 64 pc_isy) mem s6u_rom) (mkst R (Z_to_bv 64 pc_B) m1 s6u_rom)
      /\ getr R 10 = zw ZP /\ getr R 9 = zw S /\ getr R 12 = zw (is_mode s) /\ getr R 15 = zw n /\ getr R 2 = zw (sp - 64)
      /\ (forall r, reg_in r [2; 9; 11; 12; 13; 14; 15]%bv = false -> getr R r = getr regs r)
      /\ is6_scalars m1 S (ISP ZP WB) s /\ KEEP m1 /\ ZSC m1 inp n (zc_strm zc) /\ SV m1.
  Proof using STRM8 AP B1 B2 BOK FA FF G10 G2 HLD HTOP HZC IMG INP0 IR MA RA S SAFE SOK1 SOK2 SP47 STRM0 STRM63 WB ZP ZS fa ff fx inp mem outp ra regs s sp zc zcl.
    intros CHK NBUF. facts. layfacts. pose proof align_facts as [AL1 AL2]. pose proof KEEP0 as KP. pose proof ZSC0 as ZC.
    assert (MR : ~ 31 < szwrap 32 (is_mode s + -16180) mod 2 ^ 64).
    { intros X. apply (proj1 (mode_range_test _ Bmode)) in X. unfold inflateStateCheck, HEAD, SYNC in CHK. rewrite CHK in X. discriminate. }
    destruct (Z.eq_dec n 0) as [N0|N0].
    - runA [false; false; false; false; false; false; false; false; false; true] R HR Hfr Hms. all: try arm_side.
      lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => exists R, M end. split; [by_run Hms|].
      symex_reg HR (10%bv : reg) as QA10. symex_reg HR (9%bv : reg) as QA9. symex_reg HR (12%bv : reg) as QA12.
      symex_reg HR (15%bv : reg) as QA15. symex_reg HR (2%bv : reg) as QA2.
      split; [exact QA10|]. split; [exact QA9|]. split; [rewrite QA12; f_equal; lia|]. split; [rewrite QA15; f_equal; lia|]. split; [rewrite QA2; f_equal; lia|].
      split; [fr_weak Hfr|].
      split; [| split; [| split]];
      [ clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SC S0 S63 P96 P47' A3; pow8_norm; is6_peel SC
      | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 KP; keep_peel KP
      | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 ZC Z63 S0 S63 P96 P47' A1 A5; zsc_peel ZC
      | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 P96 P47'; unfold SV; repeat split; tcell I ].
    - runA [false; false; false; false; false; false; false; false; true] R HR Hfr Hms. all: try arm_side.
      lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => exists R, M end. split; [by_run Hms|].
      symex_reg HR (10%bv : reg) as QA10. symex_reg HR (9%bv : reg) as QA9. symex_reg HR (12%bv : reg) as QA12.
      symex_reg HR (15%bv : reg) as QA15. symex_reg HR (2%bv : reg) as QA2.
      split; [exact QA10|]. split; [exact QA9|]. split; [rewrite QA12; f_equal; lia|]. split; [rewrite QA15; f_equal; lia|]. split; [rewrite QA2; f_equal; lia|].
      split; [fr_weak Hfr|].
      split; [| split; [| split]];
      [ clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SC S0 S63 P96 P47' A3; pow8_norm; is6_peel SC
      | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 KP; keep_peel KP
      | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 ZC Z63 S0 S63 P96 P47' A1 A5; zsc_peel ZC
      | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 P96 P47'; unfold SV; repeat split; tcell I ].
  Qed.

  Lemma syA_buf :
    inflateStateCheck s = false -> n = 0 -> is_bits s < 8 ->
    exists R m1, msteps RS (mkst regs (Z_to_bv 64 pc_isy) mem s6u_rom) (mkst R (Z_to_bv 64 ra) m1 s6u_rom)
      /\ getr R 10 = zw Z_BUF_ERROR /\ getr R 2 = zw sp
      /\ (forall r, reg_in r [2; 10; 11; 12; 13; 14; 15]%bv = false -> getr R r = getr regs r)
      /\ RESTORED R
      /\ is6_scalars m1 S (ISP ZP WB) s /\ KEEP m1 /\ ZSC m1 inp n (zc_strm zc).
  Proof using STRM8 AP B1 B2 BOK FA FF G10 G1 G2 HLD HTOP HZC IMG INP0 IR MA RA S SAFE SOK1 SOK2 SP47 STRM0 STRM63 WB ZP ZS fa ff fx inp mem outp ra regs s sp zc zcl.
    intros CHK N0 BITS. facts. layfacts. pose proof align_facts as [AL1 AL2]. pose proof KEEP0 as KP. pose proof ZSC0 as ZC.
    assert (MR : ~ 31 < szwrap 32 (is_mode s + -16180) mod 2 ^ 64).
    { intros X. apply (proj1 (mode_range_test _ Bmode)) in X. unfold inflateStateCheck, HEAD, SYNC in CHK. rewrite CHK in X. discriminate. }
    runA [false; false; false; false; false; false; false; false; false; false] R HR Hfr Hms. all: try arm_side.
    rewrite G1 in Hms. lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => exists R, M end. split; [by_run Hms|].
    symex_reg HR (10%bv : reg) as QA10. symex_reg HR (2%bv : reg) as QA2.
    split; [rewrite QA10; reflexivity|]. split; [rewrite QA2; f_equal; lia|]. split; [fr_weak Hfr|].
    split; [fin_restored HR|].
      split; [| split];
      [ clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SC S0 S63 P96 P47' A3; pow8_norm; is6_peel SC
      | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 KP; keep_peel KP
      | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 ZC Z63 S0 S63 P96 P47' A1 A5; zsc_peel ZC ].
  Qed.

  Lemma syA_err :
    inflateStateCheck s = true ->
    exists R m1, msteps RS (mkst regs (Z_to_bv 64 pc_isy) mem s6u_rom) (mkst R (Z_to_bv 64 ra) m1 s6u_rom)
      /\ getr R 10 = zw Z_STREAM_ERROR /\ getr R 2 = zw sp
      /\ (forall r, reg_in r [2; 10; 11; 12; 13; 14; 15]%bv = false -> getr R r = getr regs r)
      /\ RESTORED R
      /\ is6_scalars m1 S (ISP ZP WB) s /\ KEEP m1 /\ ZSC m1 inp n (zc_strm zc).
  Proof using STRM8 AP B1 B2 BOK FA FF G10 G1 G2 HLD HTOP HZC IMG INP0 IR MA RA S SAFE SOK1 SOK2 SP47 STRM0 STRM63 WB ZP ZS fa ff fx inp mem outp ra regs s sp zc zcl.
    intros CHK. facts. layfacts. pose proof align_facts as [AL1 AL2]. pose proof KEEP0 as KP. pose proof ZSC0 as ZC.
    assert (MR : 31 < szwrap 32 (is_mode s + -16180) mod 2 ^ 64).
    { apply (proj2 (mode_range_test _ Bmode)). unfold inflateStateCheck, HEAD, SYNC in CHK. exact CHK. }
    runA [false; false; false; false; false; false; false; true] R HR Hfr Hms. all: try arm_side.
    rewrite G1 in Hms. lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => exists R, M end. split; [by_run Hms|].
    symex_reg HR (10%bv : reg) as QA10. symex_reg HR (2%bv : reg) as QA2.
    split; [rewrite QA10; reflexivity|]. split; [rewrite QA2; f_equal; lia|]. split; [fr_weak Hfr|].
    split; [fin_restored HR|].
      split; [| split];
      [ clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SC S0 S63 P96 P47' A3; pow8_norm; is6_peel SC
      | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 KP; keep_peel KP
      | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 ZC Z63 S0 S63 P96 P47' A1 A5; zsc_peel ZC ].
  Qed.


  Definition hold1 : Z := is_hold s / 2 ^ (is_bits s mod 8).
  Definition kq : Z := is_bits s / 8.
  Definition sB4 : inflate_state := iset_bits (iset_hold (iset_mode s SYNC) (hold1 / 2 ^ (8 * kq))) 0.
  Definition bufv (j : Z) : Z := (hold1 / 2 ^ (8 * j)) mod 256.

  Definition cfgB : cfg := CFG [] [] [EVar 1%nat] [pc_S1; pc_E] [].
  Local Ltac factsM SCm KPm ZCm :=
    pose proof ra_facts as (RAB & RET); pose proof n_nonneg as N0';
    pose proof safe_facts as (Bbits & Bhold & Bhave & Bflags & Bwrap & Bmode & Bin & Bn);
    pose proof ZCm as ZCm'; unfold ZSC in ZCm'; destruct ZCm' as (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C96);
    pose proof st_facts as (_ & S0 & S16 & STOP & SOFF & SSOK);
    pose proof KPm as KPm'; destruct KPm' as (_ & _ & _ & _ & _ & _ & WS & WF & WZ);
    pose proof SCm as SC;
    pose proof consts as (KA & KF & KFRA & KTOP & KRO & KIS & KWN);
    pose proof (is6_strm _ _ _ _ SC) as D0; pose proof (is6_mode _ _ _ _ SC) as D8; pose proof (is6_wrap _ _ _ _ SC) as D16;
    pose proof (is6_flags _ _ _ _ SC) as D24; pose proof (is6_hold _ _ _ _ SC) as D80; pose proof (is6_bits _ _ _ _ SC) as D88;
    pose proof (is6_have _ _ _ _ SC) as D140; cbn [q_strm] in D0;
    pose proof D0 as D0'; rewrite Z.add_0_r in D0'; pose proof C0 as C0'; rewrite Z.add_0_r in C0';
    rewrite KA in FA; rewrite KF in FF; rewrite KFRA in HZC; rewrite KTOP in HTOP.

  Local Ltac runB R0 m0 dirs rds R HR Hfr Hms :=
    symex s6u_segs cfgB 60%nat dirs rds
      [(10, EVar 32%nat); (9, EVar 33%nat); (2, EVar 34%nat); (12, EVar 37%nat)]
      [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 64); (36%nat, 40); (37%nat, 2 ^ 31); (38%nat, 2 ^ 31); (39%nat, 2 ^ 31)]
      NoRegions [ZP; S; sp - 64; is_hold s; is_bits s; is_mode s; n; is_have s] NoVals F0 F0'
      (mkst R0 (Z_to_bv 64 pc_B) m0 s6u_rom) R HR Hfr Hms.

  Lemma is6_state_eq : forall m p s1 s2, is6_scalars m S p s1 -> s1 = s2 -> is6_scalars m S p s2.
  Proof using. intros m p s1 s2 H E. subst s2. exact H. Qed.

  Lemma syB_drain : forall R0 m0,
    is6_scalars m0 S (ISP ZP WB) s -> KEEP m0 -> ZSC m0 inp n (zc_strm zc) -> SV m0 ->
    getr R0 10 = zw ZP -> getr R0 9 = zw S -> getr R0 2 = zw (sp - 64) -> getr R0 12 = zw (is_mode s) ->
    is_mode s <> SYNC -> 1 <= kq ->
    exists R m1, msteps RS (mkst R0 (Z_to_bv 64 pc_B) m0 s6u_rom) (mkst R (Z_to_bv 64 pc_S1) m1 s6u_rom)
      /\ getr R 10 = zw ZP /\ getr R 9 = zw S /\ getr R 2 = zw (sp - 64)
      /\ getr R 14 = zw 0 /\ getr R 11 = zw 0 /\ getr R 15 = zw (sp - 64 + 12) /\ getr R 16 = zw 4 /\ getr R 13 = zw kq /\ getr R 12 = zw (S + 156)
      /\ (forall r, reg_in r [11; 12; 13; 14; 15; 16]%bv = false -> getr R r = getr R0 r)
      /\ is6_scalars m1 S (ISP ZP WB) (iset_have sB4 0) /\ KEEP m1 /\ ZSC m1 inp n (zc_strm zc) /\ SV m1
      /\ cells RS m1 (sp - 64 + 12) 1 1 kq bufv.
  Proof using STRM8 AP B1 B2 BOK FA FF G10 G1 G2 HLD HTOP HZC IMG INP0 IR MA RA S SAFE SOK1 SOK2 SP47 STRM0 STRM63 WB ZP ZS fa ff fx inp mem outp ra regs s sp zc zcl.
    intros R0 m0 SCm KP ZC SVh Q10 Q9 Q2 Q12 NSY K1. factsM SCm KP ZC.
    pose proof (land7_m8 (is_bits s) ltac:(lia)) as [L7 L8].
    pose proof (mod8_range (is_bits s) ltac:(lia)) as [R7 DEC].
    assert (K4 : kq = 1 \/ kq = 2 \/ kq = 3 \/ kq = 4) by (unfold kq in *; apply kq_cases; lia).
    assert (H1 : zalu ALU_SRL (is_hold s) (is_bits s mod 2 ^ 3) = hold1).
    { unfold hold1. change (2 ^ 3) with 8. apply zalu_srl_small; lia. }
    layfacts.
    unfold kq in *.
    clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 Q10 Q9 Q2 Q12 D80 D88 WS WF Bbits Bhold Bmode Bn N0' Bhave STRM0 S0 S63 P96 P47' Z63 L8 K4 NSY A1 A3 A5 H1 SC KP ZC SVh DEC R7.
    destruct K4 as [K|[K|[K|K]]]; rewrite K; rewrite K in L8.
    - runB R0 m0 [false; false; true] [RVal (EVar 35%nat); RVal (EVar 36%nat)] R HR Hfr Hms. all: try arm_side.
      rewrite ?H1 in Hms; lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => exists R, M end; split; [by_run Hms|]; let Q := fresh "Q" in repeat lazymatch goal with | |- getr R ?k = _ /\ _ => split; [symex_reg HR (k : reg) as Q; rewrite ?szwrap32_small in Q by lia; rewrite Q; first [reflexivity| f_equal; lia]; clear Q|] | |- (forall r, _) /\ _ => split; [fr_weak Hfr|] end; split; [| split; [| split; [| split]]]; [ eapply is6_state_eq; [ clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SC S0 S63 P96 P47' A3; pow8_norm; is6_peel SC| ] | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 KP; keep_peel KP | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 ZC Z63 S0 S63 P96 P47' A1 A5; zsc_peel ZC | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SVh P96 P47' S0 S63 A3; sv_peel SVh | ].
      + clear - L8 K. rewrite ?iset_hb. unfold sB4, kq. rewrite K. rewrite L8. reflexivity.
      + clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 S0 S63 P96 P47' A3. intros i Hi. assert (IK : i = 0) by lia. clear Hi.
        repeat match type of IK with _ \/ _ => destruct IK as [IK|IK] end; subst i; rewrite Z.mul_1_l;
          match goal with |- cell _ _ (?b + 12 + ?i) _ _ => let k := eval vm_compute in (12 + i) in replace (b + 12 + i) with (b + k) by lia end.
        all: eapply cell_mod; [tower_cell| change (2 ^ (8 * Z.of_nat 1)) with 256; unfold bufv; pow8_norm;
                                rewrite ?Z.pow_0_r, ?Z.div_1_r; rewrite Z.mod_mod by lia; reflexivity].
    - runB R0 m0 [false; false; false; true] [RVal (EVar 35%nat); RVal (EVar 36%nat)] R HR Hfr Hms. all: try arm_side.
      rewrite ?H1 in Hms; lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => exists R, M end; split; [by_run Hms|]; let Q := fresh "Q" in repeat lazymatch goal with | |- getr R ?k = _ /\ _ => split; [symex_reg HR (k : reg) as Q; rewrite ?szwrap32_small in Q by lia; rewrite Q; first [reflexivity| f_equal; lia]; clear Q|] | |- (forall r, _) /\ _ => split; [fr_weak Hfr|] end; split; [| split; [| split; [| split]]]; [ eapply is6_state_eq; [ clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SC S0 S63 P96 P47' A3; pow8_norm; is6_peel SC| ] | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 KP; keep_peel KP | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 ZC Z63 S0 S63 P96 P47' A1 A5; zsc_peel ZC | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SVh P96 P47' S0 S63 A3; sv_peel SVh | ].
      + clear - L8 K. rewrite ?iset_hb. unfold sB4, kq. rewrite K. rewrite L8. reflexivity.
      + clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 S0 S63 P96 P47' A3. intros i Hi. assert (IK : i = 0 \/ i = 1) by lia. clear Hi.
        repeat match type of IK with _ \/ _ => destruct IK as [IK|IK] end; subst i; rewrite Z.mul_1_l;
          match goal with |- cell _ _ (?b + 12 + ?i) _ _ => let k := eval vm_compute in (12 + i) in replace (b + 12 + i) with (b + k) by lia end.
        all: eapply cell_mod; [tower_cell| change (2 ^ (8 * Z.of_nat 1)) with 256; unfold bufv; pow8_norm;
                                rewrite ?Z.pow_0_r, ?Z.div_1_r; rewrite Z.mod_mod by lia; reflexivity].
    - runB R0 m0 [false; false; false; false; true] [RVal (EVar 35%nat); RVal (EVar 36%nat)] R HR Hfr Hms. all: try arm_side.
      rewrite ?H1 in Hms; lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => exists R, M end; split; [by_run Hms|]; let Q := fresh "Q" in repeat lazymatch goal with | |- getr R ?k = _ /\ _ => split; [symex_reg HR (k : reg) as Q; rewrite ?szwrap32_small in Q by lia; rewrite Q; first [reflexivity| f_equal; lia]; clear Q|] | |- (forall r, _) /\ _ => split; [fr_weak Hfr|] end; split; [| split; [| split; [| split]]]; [ eapply is6_state_eq; [ clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SC S0 S63 P96 P47' A3; pow8_norm; is6_peel SC| ] | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 KP; keep_peel KP | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 ZC Z63 S0 S63 P96 P47' A1 A5; zsc_peel ZC | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SVh P96 P47' S0 S63 A3; sv_peel SVh | ].
      + clear - L8 K. rewrite ?iset_hb. unfold sB4, kq. rewrite K. rewrite L8. reflexivity.
      + clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 S0 S63 P96 P47' A3. intros i Hi. assert (IK : i = 0 \/ i = 1 \/ i = 2) by lia. clear Hi.
        repeat match type of IK with _ \/ _ => destruct IK as [IK|IK] end; subst i; rewrite Z.mul_1_l;
          match goal with |- cell _ _ (?b + 12 + ?i) _ _ => let k := eval vm_compute in (12 + i) in replace (b + 12 + i) with (b + k) by lia end.
        all: eapply cell_mod; [tower_cell| change (2 ^ (8 * Z.of_nat 1)) with 256; unfold bufv; pow8_norm;
                                rewrite ?Z.pow_0_r, ?Z.div_1_r; rewrite Z.mod_mod by lia; reflexivity].
    - runB R0 m0 [false; false; false; false; false; false] [RVal (EVar 35%nat); RVal (EVar 36%nat)] R HR Hfr Hms. all: try arm_side.
      rewrite ?H1 in Hms; lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => exists R, M end; split; [by_run Hms|]; let Q := fresh "Q" in repeat lazymatch goal with | |- getr R ?k = _ /\ _ => split; [symex_reg HR (k : reg) as Q; rewrite ?szwrap32_small in Q by lia; rewrite Q; first [reflexivity| f_equal; lia]; clear Q|] | |- (forall r, _) /\ _ => split; [fr_weak Hfr|] end; split; [| split; [| split; [| split]]]; [ eapply is6_state_eq; [ clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SC S0 S63 P96 P47' A3; pow8_norm; is6_peel SC| ] | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 KP; keep_peel KP | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 ZC Z63 S0 S63 P96 P47' A1 A5; zsc_peel ZC | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SVh P96 P47' S0 S63 A3; sv_peel SVh | ].
      + clear - L8 K. rewrite ?iset_hb. unfold sB4, kq. rewrite K. rewrite L8. reflexivity.
      + clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 S0 S63 P96 P47' A3. intros i Hi. assert (IK : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia. clear Hi.
        repeat match type of IK with _ \/ _ => destruct IK as [IK|IK] end; subst i; rewrite Z.mul_1_l;
          match goal with |- cell _ _ (?b + 12 + ?i) _ _ => let k := eval vm_compute in (12 + i) in replace (b + 12 + i) with (b + k) by lia end.
        all: eapply cell_mod; [tower_cell| change (2 ^ (8 * Z.of_nat 1)) with 256; unfold bufv; pow8_norm;
                                rewrite ?Z.pow_0_r, ?Z.div_1_r; rewrite Z.mod_mod by lia; reflexivity].
  Qed.

  Definition sB0 : inflate_state := iset_have (iset_bits (iset_hold (iset_mode s SYNC) hold1) 0) 0.
  Lemma syB_k0 : forall R0 m0,
    is6_scalars m0 S (ISP ZP WB) s -> KEEP m0 -> ZSC m0 inp n (zc_strm zc) -> SV m0 ->
    getr R0 10 = zw ZP -> getr R0 9 = zw S -> getr R0 2 = zw (sp - 64) -> getr R0 12 = zw (is_mode s) ->
    is_mode s <> SYNC -> kq = 0 ->
    exists R m1, msteps RS (mkst R0 (Z_to_bv 64 pc_B) m0 s6u_rom) (mkst R (Z_to_bv 64 pc_E) m1 s6u_rom)
      /\ getr R 10 = zw ZP /\ getr R 9 = zw S /\ getr R 2 = zw (sp - 64)
      /\ getr R 15 = zw n
      /\ (forall r, reg_in r [11; 12; 13; 14; 15; 16]%bv = false -> getr R r = getr R0 r)
      /\ is6_scalars m1 S (ISP ZP WB) sB0 /\ KEEP m1 /\ ZSC m1 inp n (zc_strm zc) /\ SV m1.
  Proof using STRM8 AP B1 B2 BOK FA FF G10 G1 G2 HLD HTOP HZC IMG INP0 IR MA RA S SAFE SOK1 SOK2 SP47 STRM0 STRM63 WB ZP ZS fa ff fx inp mem outp ra regs s sp zc zcl.
    intros R0 m0 SCm KP ZC SVh Q10 Q9 Q2 Q12 NSY K0. factsM SCm KP ZC.
    pose proof (land7_m8 (is_bits s) ltac:(lia)) as [L7 L8]. pose proof (mod8_range (is_bits s) ltac:(lia)) as [R7 DEC].
    assert (H1 : zalu ALU_SRL (is_hold s) (is_bits s mod 2 ^ 3) = hold1).
    { unfold hold1. change (2 ^ 3) with 8. apply zalu_srl_small; lia. }
    layfacts.
    assert (EB0 : sB0 = iset_have (iset_bits (iset_hold (iset_mode s SYNC) hold1) 0) 0) by reflexivity. rewrite EB0.
    unfold kq in *. rewrite K0 in L8. assert (B7 : is_bits s <= 7) by (clear - K0 DEC R7; rewrite K0 in DEC; lia).
    clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 Q10 Q9 Q2 Q12 D80 D88 C8 WS WF Bbits Bhold Bmode Bn N0' Bhave STRM0 S0 S63 P96 P47' Z63 L8 NSY A1 A3 A5 H1 SC KP ZC SVh B7.
    assert (L80 : Z.land (is_bits s) (-8) = 0) by lia.
    runB R0 m0 [false; true] [RVal (EVar 35%nat); RVal (EVar 36%nat); RVal (EVar 38%nat)] R HR Hfr Hms. all: try arm_side.
    rewrite ?H1, ?L80 in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => exists R, M end. split; [by_run Hms|].
    symex_reg HR (10%bv : reg) as Q10'. symex_reg HR (9%bv : reg) as Q9'. symex_reg HR (2%bv : reg) as Q2'.
    symex_reg HR (15%bv : reg) as Q15'.
    split; [exact Q10'|]. split; [exact Q9'|]. split; [exact Q2'|].
    split; [rewrite Q15'; f_equal; rewrite ?szwrap32_small by lia; lia|]. split; [fr_weak Hfr|].
    split; [| split; [| split]].
    + eapply is6_state_eq; [clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SC S0 S63 P96 P47' A3; is6_peel SC|].
      clear - L80. rewrite ?L80. destruct s; reflexivity.
    + clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 KP. keep_peel KP.
    + clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 ZC Z63 S0 S63 P96 P47' A1 A5. zsc_peel ZC.
    + clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SVh P96 P47' S0 S63 A3. sv_peel SVh.
  Qed.

  Lemma syB_sync : forall R0 m, is6_scalars m S (ISP ZP WB) s ->
    getr R0 10 = zw ZP -> getr R0 9 = zw S -> getr R0 2 = zw (sp - 64) -> getr R0 12 = zw (is_mode s) -> getr R0 15 = zw n ->
    is_mode s = SYNC ->
    exists R, msteps RS (mkst R0 (Z_to_bv 64 pc_B) m s6u_rom) (mkst R (Z_to_bv 64 pc_E) m s6u_rom)
      /\ getr R 10 = zw ZP /\ getr R 9 = zw S /\ getr R 2 = zw (sp - 64)
      /\ getr R 15 = zw n
      /\ (forall r, reg_in r [11; 13]%bv = false -> getr R r = getr R0 r).
  Proof using STRM8 AP B1 B2 BOK FA FF G10 G1 G2 HLD HTOP HZC IMG INP0 IR MA RA S SAFE SOK1 SOK2 SP47 STRM0 STRM63 WB ZP ZS fa ff fx inp mem outp ra regs s sp zc zcl.
    intros R0 m SCm Q10 Q9 Q2 Q12 Q15 SY. facts. layfacts. pose proof (is6_have _ _ _ _ SCm) as D140m.
    clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 Q10 Q9 Q2 Q12 Q15 D140m Bhave Bmode Bbits Bhold Bn N0' STRM0 Z63 P96 P47' S0 S63 SY.
    runB R0 m [true] [RVal (EVar 39%nat)] R HR Hfr Hms. all: try arm_side.
    exists R. split; [by_run Hms|].
    symex_reg HR (10%bv : reg) as Q10'. symex_reg HR (9%bv : reg) as Q9'. symex_reg HR (2%bv : reg) as Q2'.
    symex_reg HR (15%bv : reg) as Q15'.
    split; [exact Q10'|]. split; [exact Q9'|]. split; [exact Q2'|].
    split; [rewrite Q15'; exact Q15|]. fr_weak Hfr.
  Qed.

  Definition inb (j : Z) : Z := nth (Z.to_nat j) input 0.
  Lemma inb_range : forall j, 0 <= j < n -> 0 <= inb j < 256.
  Proof using STRM8 SAFE STRM0 sp s ZP.
    intros j Hj. unfold inb. pose proof safe_facts as (_ & _ & _ & _ & _ & _ & Bin & _).
    apply (Forall_nth (fun b => 0 <= b < 256) input); [exact Bin|]. unfold zlength in Hj. lia.
  Qed.
  Lemma holds_cells : forall m, holds RS m inp input -> cells RS m inp 1 1 n inb.
  Proof using STRM8 IR B1 AP INP0 STRM63 STRM0 BOK HTOP SP47 HZC RA zcl ra sp s WB ZP S mem.
    intros m H i Hi. pose proof layout as (_ & _ & _ & _ & _ & _ & I0 & I63 & _). unfold holds in H. unfold cell, inb.
    unfold zlength in *.
    pose proof (rdn_nth RS m (length input) (Z_to_bv 64 inp) _ (Z.to_nat i) H ltac:(lia)) as R1.
    rewrite <- zw_add_nat, Z2Nat.id in R1 by lia. replace (inp + 1 * i) with (inp + i) by lia. rewrite R1. f_equal.
    change (Z_to_bv 8 0) with ((fun z : Z => Z_to_bv 8 z) 0). rewrite map_nth. reflexivity.
  Qed.

  Definition cfgS2 : cfg := CFG [] [] [EVar 1%nat] [pc_S2; pc_G] [].
  Local Ltac runS2 R0 m i got dirs R HR Hfr Hms :=
    symex s6u_segs cfgS2 40%nat dirs [RVal (EVar 36%nat)]
      [(12, EVar 32%nat); (14, EVar 33%nat); (13, EVar 33%nat); (16, EVar 34%nat); (17, ELit 4); (15, EVar 37%nat); (11, EVar 35%nat)]
      [(32%nat, 2 ^ 63); (33%nat, 2 ^ 31); (34%nat, 2 ^ 31); (35%nat, 4); (36%nat, 256); (37%nat, 2 ^ 64)]
      NoRegions [inp; i; n; got; inb i; 2 ^ 64 - 1 - inp] NoVals F0 F0'
      (mkst R0 (Z_to_bv 64 pc_S2) m s6u_rom) R HR Hfr Hms.

  Local Ltac finS2 R HR Hfr Hms GOT :=
    exists R; split; [by_run Hms|];
    let Q := fresh "Q" in
    repeat lazymatch goal with
      | |- getr R ?k = _ /\ _ => split; [symex_reg HR (k : reg) as Q; rewrite ?szwrap32_small in Q by lia; rewrite Q, ?GOT; first [reflexivity| f_equal; lia]; clear Q|]
      | |- forall r, _ => fr_weak Hfr
      end.
  Lemma syS2_trip : forall R0 m i got,
    cells RS m inp 1 1 n inb ->
    getr R0 12 = zw inp -> getr R0 14 = zw i -> getr R0 13 = zw i -> getr R0 16 = zw n -> getr R0 17 = zw 4 -> getr R0 15 = zw (2 ^ 64 - 1 - inp) -> getr R0 11 = zw got ->
    0 <= i < n -> 0 <= got < 4 ->
    let got' := sync_step got (inb i) in
    let cont := (i + 1 <? n) && (got' <? 4) in
    exists R, msteps RS (mkst R0 (Z_to_bv 64 pc_S2) m s6u_rom) (mkst R (Z_to_bv 64 (if cont then pc_S2 else pc_G)) m s6u_rom)
      /\ getr R 12 = zw inp /\ getr R 14 = zw (i + 1) /\ getr R 13 = zw (i + 1) /\ getr R 16 = zw n /\ getr R 17 = zw 4 /\ getr R 15 = zw (2 ^ 64 - 1 - inp) /\ getr R 11 = zw got'
      /\ (forall r, reg_in r [5; 6; 11; 13; 14]%bv = false -> getr R r = getr R0 r).
  Proof using STRM8 SAFE IR B1 AP INP0 STRM63 STRM0 BOK HTOP SP47 HZC RA zcl ra sp s WB ZP S mem.
    intros R0 m i got HB Q14 Q16 Q15 Q17 Q5 Q6 Q11 Hi Hg. pose proof (inb_range i Hi) as Bi. pose proof inb_range as Br.
    pose proof layout as (_ & _ & _ & _ & _ & _ & I0 & I63 & N0 & _). pose proof safe_facts as (_ & _ & _ & _ & _ & _ & _ & Bn).
    clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 HB Q14 Q16 Q15 Q17 Q5 Q6 Q11 Hi Hg Bi Br I0 I63 N0 Bn.
    cbv zeta. pose proof (sync_pat_eq got Hg) as PAT. pose proof (sync_got_eq (inb i) got Bi Hg) as GOT.
    rewrite szwrap32_small in GOT by lia. unfold sync_step.
    destruct (Z.eqb_spec (inb i) (if got <? 2 then 0 else 255)) as [MT|NM].
    -
      destruct (Z.ltb_spec (i + 1) n) as [C1|C1]; [destruct (Z.ltb_spec (got + 1) 4) as [C2|C2]|]; cbn [andb].
      + runS2 R0 m i got [false; true; false; true] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
      + runS2 R0 m i got [false; true; false; false] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
      + runS2 R0 m i got [false; true; true] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
    - destruct (Z.eqb_spec (inb i) 0) as [B0|B0]; cbn [negb].
      +
        destruct (Z.ltb_spec (i + 1) n) as [C1|C1]; [destruct (Z.ltb_spec (4 - got) 4) as [C2|C2]|]; cbn [andb].
        * runS2 R0 m i got [false; false; false; true] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
        * runS2 R0 m i got [false; false; false; false] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
        * runS2 R0 m i got [false; false; true] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
      +
        destruct (Z.ltb_spec (i + 1) n) as [C1|C1]; [replace (0 <? 4) with true by reflexivity|]; cbn [andb].
        * runS2 R0 m i got [false; false; false; true] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
        * runS2 R0 m i got [false; false; true] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
  Qed.

  Lemma syS2_loop : forall cnt R0 m i got,
    cells RS m inp 1 1 n inb ->
    getr R0 12 = zw inp -> getr R0 14 = zw i -> getr R0 13 = zw i -> getr R0 16 = zw n -> getr R0 17 = zw 4 -> getr R0 15 = zw (2 ^ 64 - 1 - inp) -> getr R0 11 = zw got ->
    0 <= i < n -> 0 <= got < 4 -> (Z.to_nat (n - i) <= cnt)%nat ->
    let r := syncsearch_loop (skipn (Z.to_nat i) input) got i in
    exists R, msteps RS (mkst R0 (Z_to_bv 64 pc_S2) m s6u_rom) (mkst R (Z_to_bv 64 pc_G) m s6u_rom)
      /\ getr R 12 = zw inp /\ getr R 16 = zw n /\ getr R 11 = zw (fst r) /\ getr R 13 = zw (snd r)
      /\ (forall r, reg_in r [5; 6; 11; 13; 14]%bv = false -> getr R r = getr R0 r).
  Proof using STRM8 SAFE IR B1 AP INP0 STRM63 STRM0 BOK HTOP SP47 HZC RA zcl ra sp s WB ZP S mem.
    induction cnt as [|cnt IH]; intros R0 m i got HB Q14 Q16 Q15 Q17 Q5 Q6 Q11 Hi Hg Hc; [lia|].
    cbv zeta. pose proof (syS2_trip R0 m i got HB Q14 Q16 Q15 Q17 Q5 Q6 Q11 Hi Hg) as T. cbv zeta in T.
    destruct T as (R1 & MS1 & P14 & P16 & P15 & P17 & P5 & P6 & P11 & FR1).
    pose proof (sync_step_range got (inb i) Hg) as GR.
    assert (LEN : length input = Z.to_nat n) by (unfold zlength; lia).
    rewrite (skipn_cons_nth input (Z.to_nat i)) by lia. change (nth (Z.to_nat i) input 0) with (inb i).
    rewrite syncsearch_loop_cons by lia. replace (Datatypes.S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
    destruct ((i + 1 <? n) && (sync_step got (inb i) <? 4)) eqn:CT.
    -
      apply andb_prop in CT. destruct CT as [C1 C2]. apply Z.ltb_lt in C1. apply Z.ltb_lt in C2.
      destruct (IH R1 m (i + 1) (sync_step got (inb i)) HB P14 P16 P15 P17 P5 P6 P11 ltac:(lia) ltac:(lia) ltac:(lia))
        as (R2 & MS2 & W14 & W17 & W11 & W15 & FR2).
      exists R2. split; [eapply msteps_trans; [exact MS1| exact MS2]|].
      split; [exact W14|]. split; [exact W17|]. split; [exact W11|]. split; [exact W15|].
      intros r Hr. rewrite (FR2 r Hr). exact (FR1 r Hr).
    -
      rewrite syncsearch_loop_stop.
      2:{ apply Bool.andb_false_iff in CT. destruct CT as [C1|C2].
          - left. apply Z.ltb_ge in C1. apply skipn_all2. lia.
          - right. apply Z.ltb_ge in C2. exact C2. }
      exists R1. cbn [fst snd]. split; [exact MS1|]. split; [exact P14|]. split; [exact P17|]. split; [exact P11|]. split; [exact P15|]. exact FR1.
  Qed.

  Lemma bufv_range : forall j, 0 <= j < kq -> 0 <= bufv j < 256.
  Proof using. intros j _. unfold bufv. apply Z.mod_pos_bound. lia. Qed.

  Definition cfgS1 : cfg := CFG [] [] [EVar 1%nat] [pc_S1; pc_S1x] [].
  Local Ltac runS1 R0 m i got dirs R HR Hfr Hms :=
    symex s6u_segs cfgS1 40%nat dirs [RVal (EVar 36%nat)]
      [(15, EVar 32%nat); (14, EVar 33%nat); (13, EVar 34%nat); (16, ELit 4); (11, EVar 35%nat)]
      [(32%nat, 2 ^ 63); (33%nat, 2 ^ 31); (34%nat, 2 ^ 31); (35%nat, 4); (36%nat, 256)]
      NoRegions [sp - 64 + 12; i; kq; got; bufv i] NoVals F0 F0'
      (mkst R0 (Z_to_bv 64 pc_S1) m s6u_rom) R HR Hfr Hms.

  Lemma syS1_trip : forall R0 m i got,
    cells RS m (sp - 64 + 12) 1 1 kq bufv ->
    getr R0 15 = zw (sp - 64 + 12) -> getr R0 14 = zw i -> getr R0 13 = zw kq -> getr R0 16 = zw 4 -> getr R0 11 = zw got ->
    0 <= i < kq -> kq <= 4 -> 0 <= got < 4 ->
    let got' := sync_step got (bufv i) in
    let cont := (i + 1 <? kq) && (got' <? 4) in
    exists R, msteps RS (mkst R0 (Z_to_bv 64 pc_S1) m s6u_rom) (mkst R (Z_to_bv 64 (if cont then pc_S1 else pc_S1x)) m s6u_rom)
      /\ getr R 15 = zw (sp - 64 + 12) /\ getr R 14 = zw (i + 1) /\ getr R 13 = zw kq /\ getr R 16 = zw 4 /\ getr R 11 = zw got'
      /\ (forall r, reg_in r [5; 11; 14; 17]%bv = false -> getr R r = getr R0 r).
  Proof using STRM8 IR B1 AP INP0 STRM63 STRM0 BOK HTOP SP47 HZC RA zcl inp ra zc WB ZP S mem.
    intros R0 m i got HB Q16 Q15 Q14 Q17 Q11 Hi K4 Hg. pose proof (bufv_range i Hi) as Bi. pose proof bufv_range as Br.
    pose proof layout as (_ & _ & P16 & P47 & _).
    clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 HB Q16 Q15 Q14 Q17 Q11 Hi K4 Hg Bi Br P16 P47.
    cbv zeta. pose proof (sync_pat_eq got Hg) as PAT. pose proof (sync_got_eq (bufv i) got Bi Hg) as GOT.
    rewrite szwrap32_small in GOT by lia. unfold sync_step.
    destruct (Z.eqb_spec (bufv i) (if got <? 2 then 0 else 255)) as [MT|NM].
    - destruct (Z.ltb_spec (i + 1) kq) as [C1|C1]; [destruct (Z.ltb_spec (got + 1) 4) as [C2|C2]|]; cbn [andb].
      + runS1 R0 m i got [true; false; true] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
      + runS1 R0 m i got [true; false; false] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
      + runS1 R0 m i got [true; true] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
    - destruct (Z.eqb_spec (bufv i) 0) as [B0|B0]; cbn [negb].
      + destruct (Z.ltb_spec (i + 1) kq) as [C1|C1]; [destruct (Z.ltb_spec (4 - got) 4) as [C2|C2]|]; cbn [andb].
        * runS1 R0 m i got [false; false; true] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
        * runS1 R0 m i got [false; false; false] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
        * runS1 R0 m i got [false; true] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
      + destruct (Z.ltb_spec (i + 1) kq) as [C1|C1]; [replace (0 <? 4) with true by reflexivity|]; cbn [andb].
        * runS1 R0 m i got [false; false; true] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
        * runS1 R0 m i got [false; true] RR HRR Hfr Hms. all: try arm_side. finS2 RR HRR Hfr Hms GOT.
  Qed.

  Definition bufl : list Z := drain_bytes hold1 (Z.to_nat kq).
  Lemma bufl_facts : length bufl = Z.to_nat kq /\ (forall j, 0 <= j < kq -> nth (Z.to_nat j) bufl 0 = bufv j).
  Proof using STRM8 SAFE STRM0 sp zc ZP.
    pose proof safe_facts as (Bbits & Bhold & _). unfold bufl, bufv. split; [apply drain_bytes_length|].
    intros j Hj. rewrite drain_bytes_nth; [| unfold hold1; apply Z.div_pos; [lia| apply Z.pow_pos_nonneg; [lia| apply Z.mod_pos_bound; lia]]| lia].
    rewrite Z2Nat.id by lia. reflexivity.
  Qed.

  Lemma syS1_loop : forall cnt R0 m i got,
    cells RS m (sp - 64 + 12) 1 1 kq bufv ->
    getr R0 15 = zw (sp - 64 + 12) -> getr R0 14 = zw i -> getr R0 13 = zw kq -> getr R0 16 = zw 4 -> getr R0 11 = zw got ->
    0 <= i < kq -> kq <= 4 -> 0 <= got < 4 -> (Z.to_nat (kq - i) <= cnt)%nat ->
    let r := syncsearch_loop (skipn (Z.to_nat i) bufl) got i in
    exists R, msteps RS (mkst R0 (Z_to_bv 64 pc_S1) m s6u_rom) (mkst R (Z_to_bv 64 pc_S1x) m s6u_rom)
      /\ getr R 11 = zw (fst r) /\ getr R 14 = zw (snd r)
      /\ (forall r, reg_in r [5; 11; 14; 17]%bv = false -> getr R r = getr R0 r).
  Proof using STRM8 SAFE IR B1 AP INP0 STRM63 STRM0 BOK HTOP SP47 HZC RA zcl inp ra zc WB ZP S mem.
    induction cnt as [|cnt IH]; intros R0 m i got HB Q16 Q15 Q14 Q17 Q11 Hi K4 Hg Hc; [lia|].
    cbv zeta. pose proof (syS1_trip R0 m i got HB Q16 Q15 Q14 Q17 Q11 Hi K4 Hg) as T. cbv zeta in T.
    destruct T as (R1 & MS1 & P16 & P15 & P14 & P17 & P11 & FR1).
    pose proof (sync_step_range got (bufv i) Hg) as GR. pose proof bufl_facts as [LEN NTH].
    rewrite (skipn_cons_nth bufl (Z.to_nat i)) by lia. rewrite (NTH i) by lia.
    rewrite syncsearch_loop_cons by lia. replace (Datatypes.S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
    destruct ((i + 1 <? kq) && (sync_step got (bufv i) <? 4)) eqn:CT.
    - apply andb_prop in CT. destruct CT as [C1 C2]. apply Z.ltb_lt in C1. apply Z.ltb_lt in C2.
      destruct (IH R1 m (i + 1) (sync_step got (bufv i)) HB P16 P15 P14 P17 P11 ltac:(lia) K4 ltac:(lia) ltac:(lia))
        as (R2 & MS2 & W11 & W15 & FR2).
      exists R2. split; [eapply msteps_trans; [exact MS1| exact MS2]|].
      split; [exact W11|]. split; [exact W15|].
      intros r Hr. rewrite (FR2 r Hr). exact (FR1 r Hr).
    - rewrite syncsearch_loop_stop.
      2:{ apply Bool.andb_false_iff in CT. destruct CT as [C1|C2].
          - left. apply Z.ltb_ge in C1. apply skipn_all2. lia.
          - right. apply Z.ltb_ge in C2. exact C2. }
      exists R1. cbn [fst snd]. split; [exact MS1|]. split; [exact P11|]. split; [exact P15|]. exact FR1.
  Qed.

  Definition cfgE : cfg := CFG [] [] [EVar 1%nat] [pc_E; pc_G; pc_S2] [].

  Lemma syE1 : forall R0 m sX got,
    is6_scalars m S (ISP ZP WB) sX -> KEEP m -> ZSC m inp n (zc_strm zc) -> SV m ->
    getr R0 10 = zw ZP -> getr R0 9 = zw S -> getr R0 11 = zw got -> getr R0 12 = zw (S + 156) -> 0 <= got <= 4 ->
    exists R m1, msteps RS (mkst R0 (Z_to_bv 64 pc_S1x) m s6u_rom) (mkst R (Z_to_bv 64 pc_E) m1 s6u_rom)
      /\ getr R 10 = zw ZP /\ getr R 9 = zw S /\ getr R 11 = zw got /\ getr R 15 = zw n
      /\ (forall r, reg_in r [15]%bv = false -> getr R r = getr R0 r)
      /\ is6_scalars m1 S (ISP ZP WB) (iset_have sX got) /\ KEEP m1 /\ ZSC m1 inp n (zc_strm zc) /\ SV m1.
  Proof using STRM8 AP B1 B2 BOK FA FF G10 G1 G2 HLD HTOP HZC IMG INP0 IR MA RA S SAFE SOK1 SOK2 SP47 STRM0 STRM63 WB ZP ZS fa ff fx inp mem outp ra regs s sp zc zcl.
    intros R0 m sX got SCX KP ZC SVh Q10 Q9 Q11 Q12 Hg. factsM SCX KP ZC. layfacts.
    clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SCX KP ZC SVh Q10 Q9 Q11 Q12 Hg S0 S63 P96 P47' Z63 N0' A1 A3 A5 Bn WS WZ C8.
    symex s6u_segs cfgE 10%nat (@nil bool) [RVal (EVar 35%nat)]
      [(10, EVar 32%nat); (9, EVar 33%nat); (11, EVar 34%nat); (12, EVar 36%nat)]
      [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 5); (35%nat, 2 ^ 31); (36%nat, 2 ^ 63)]
      NoRegions [ZP; S; got; n; S + 156] NoVals F0 F0'
      (mkst R0 (Z_to_bv 64 pc_S1x) m s6u_rom) RR HRR Hfr Hms.
    all: try arm_side.
    lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => exists RR, M end. split; [by_run Hms|].
    symex_reg HRR (10%bv : reg) as P10. symex_reg HRR (9%bv : reg) as P9. symex_reg HRR (11%bv : reg) as P11. symex_reg HRR (15%bv : reg) as P15.
    split; [exact P10|]. split; [exact P9|]. split; [exact P11|]. split; [rewrite P15; rewrite ?szwrap32_small by lia; f_equal; lia|]. split; [fr_weak Hfr|].
    split; [| split; [| split]].
    - clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SCX S0 S63 P96 P47' A3. is6_peel SCX.
    - clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 KP. keep_peel KP.
    - clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 ZC Z63 S0 S63 P96 P47' A1 A5. zsc_peel ZC.
    - clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SVh P96 P47' S0 S63 A3. sv_peel SVh.
  Qed.

  Lemma zw_not : forall x, zw (Z.lxor x (-1)) = zw (2 ^ 64 - 1 - x).
  Proof using. intros x. apply zw_eqm. rewrite Z.lxor_m1_r, Z.lnot_eq_pred_opp.
    replace (2 ^ 64 - 1 - x) with ((- x - 1) + 1 * 2 ^ 64) by ring. rewrite Z.mod_add by (apply Z.pow_nonzero; lia). reflexivity. Qed.
  Local Ltac runE R0 m have dirs R HR Hfr Hms :=
    symex s6u_segs cfgE 20%nat dirs [RVal (EVar 35%nat); RVal (EVar 33%nat)]
      [(10, EVar 32%nat); (9, EVar 36%nat); (15, EVar 34%nat)]
      [(32%nat, 2 ^ 63); (33%nat, 2 ^ 31); (34%nat, 2 ^ 31); (35%nat, 2 ^ 63); (36%nat, 2 ^ 63)]
      NoRegions [ZP; have; n; inp; S] NoVals F0 F0'
      (mkst R0 (Z_to_bv 64 pc_E) m s6u_rom) R HR Hfr Hms.
  Local Ltac finE R HR Hfr Hms :=
    exists R; split; [by_run Hms|];
    let Q := fresh "Q" in
    repeat lazymatch goal with
      | |- getr R ?k = _ /\ _ => split; [symex_reg HR (k : reg) as Q; rewrite ?szwrap32_small in Q by lia; rewrite Q; first [reflexivity| f_equal; lia]; clear Q|]
      | |- (_ = false -> _) /\ _ =>
          let Q' := fresh "Q" in
          split; [first [discriminate | intros _; repeat match goal with
                         | |- getr R ?k = _ /\ _ => split; [symex_reg HR (k : reg) as Q; rewrite Q; first [reflexivity| f_equal; lia]; clear Q|]
                         | |- getr R ?k = _ => symex_reg HR (k : reg) as Q; rewrite Q; first [reflexivity| f_equal; lia| apply zw_not]
                         end]|]
      | |- forall r, _ => fr_weak Hfr
      end.

  Lemma syE : forall R0 m have,
    ZSC m inp n (zc_strm zc) ->
    getr R0 10 = zw ZP -> getr R0 9 = zw S -> cell RS m (S + 156) 4 have -> getr R0 15 = zw n -> 0 <= have < 2 ^ 31 ->
    exists R, msteps RS (mkst R0 (Z_to_bv 64 pc_E) m s6u_rom)
                        (mkst R (Z_to_bv 64 (if (n =? 0) || (3 <? have) then pc_G else pc_S2)) m s6u_rom)
      /\ getr R 10 = zw ZP /\ getr R 11 = zw have /\ getr R 12 = zw inp /\ getr R 13 = zw 0
      /\ ((n =? 0) || (3 <? have) = false -> getr R 14 = zw 0 /\ getr R 16 = zw n /\ getr R 17 = zw 4 /\ getr R 15 = zw (2 ^ 64 - 1 - inp))
      /\ (forall r, reg_in r [11; 12; 13; 14; 15; 16; 17]%bv = false -> getr R r = getr R0 r).
  Proof using STRM8 SAFE IR B1 AP INP0 STRM63 STRM0 BOK HTOP SP47 HZC RA zcl ra sp s WB mem.
    intros R0 m have ZC Q10 Q9 CH Q15 Hh.
    pose proof layout as (S0 & S63 & P16 & P47 & Z0 & Z63 & I0 & I63 & N0 & _).
    pose proof safe_facts as (_ & _ & _ & _ & _ & _ & _ & Bn).
    destruct ZC as (C0 & _). pose proof C0 as C0'. rewrite Z.add_0_r in C0'.
    clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 Q10 Q9 CH Q15 Hh S0 S63 Z0 Z63 I0 I63 N0 Bn C0 C0'.
    destruct (Z.eqb_spec n 0) as [NZ|NZ]; [| destruct (Z.ltb_spec 3 have) as [H3|H3]]; cbn [orb].
    - runE R0 m have [true] RR HRR Hfr Hms. all: try arm_side. finE RR HRR Hfr Hms.
    - runE R0 m have [false; true] RR HRR Hfr Hms. all: try arm_side. finE RR HRR Hfr Hms.
    - runE R0 m have [false; false; false] RR HRR Hfr Hms. all: try arm_side. finE RR HRR Hfr Hms.
  Qed.

  Definition cfgG : cfg := CFG [] [] [EVar 44%nat] [] [].
  Local Ltac runG R0 m sX len got dirs rds R HR Hfr Hms :=
    symex s6u_segs cfgG 200%nat dirs rds
      [(10, EVar 32%nat); (9, EVar 33%nat); (2, EVar 34%nat); (12, EVar 35%nat); (13, EVar 36%nat); (11, EVar 38%nat)]
      [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 63); (36%nat, 2 ^ 31); (37%nat, 2 ^ 31); (38%nat, 2 ^ 31);
       (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 32); (42%nat, 2 ^ 31); (43%nat, 2 ^ 31); (44%nat, 2 ^ 64); (45%nat, 2 ^ 64);
       (46%nat, 2 ^ 64); (47%nat, 2 ^ 64); (48%nat, 2 ^ 64); (49%nat, 2 ^ 64)]
      NoRegions [ZP; S; sp - 64; inp; len; n; got; zs_total_in (zc_strm zc) mod 2 ^ 64; zs_total_out (zc_strm zc) mod 2 ^ 64; is_flags s mod 2 ^ 32; is_wrap s;
                 is_mode sX; ra; bv_unsigned (getr regs 8); bv_unsigned (getr regs 9); bv_unsigned (getr regs 18); bv_unsigned (getr regs 19);
                 bv_unsigned (getr regs 20)] NoVals F0 F0'
      (mkst R0 (Z_to_bv 64 pc_G) m s6u_rom) R HR Hfr Hms.
  Local Ltac layfull :=
    pose proof layout as (S0 & S63 & P96 & P47 & Z0 & Z63 & I0 & I63 & N0 & A1 & A2 & A3 & A4 & A5 & A6 & _); unfold apart in A1, A2, A3, A4, A5, A6.

  Definition zG1 : Z -> zstrm := fun len => zs_set_total_in (wrap64 (zs_total_in (zc_strm zc) + len)) (zc_strm zc).

  Lemma syG_err : forall R0 m sX len got,
    is6_scalars m S (ISP ZP WB) sX -> KEEP m -> ZSC m inp n (zc_strm zc) -> SV m -> (is_flags sX = is_flags s) -> (is_wrap sX = is_wrap s) ->
    getr R0 10 = zw ZP -> getr R0 9 = zw S -> getr R0 2 = zw (sp - 64) -> getr R0 12 = zw inp -> getr R0 13 = zw len ->
    getr R0 11 = zw got -> getr R0 1 = getr regs 1 ->
    0 <= len <= n -> 0 <= got < 2 ^ 31 -> got <> 4 -> 0 <= is_mode sX < 2 ^ 31 ->
    exists R m1, msteps RS (mkst R0 (Z_to_bv 64 pc_G) m s6u_rom) (mkst R (Z_to_bv 64 ra) m1 s6u_rom)
      /\ getr R 10 = zw Z_DATA_ERROR /\ getr R 2 = zw sp
      /\ (forall r, reg_in r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 18; 19; 20]%bv = false -> getr R r = getr R0 r)
      /\ RESTORED R
      /\ is6_scalars m1 S (ISP ZP WB) (iset_have sX got) /\ KEEP m1 /\ ZSC m1 (inp + len) (n - len) (zG1 len).
  Proof using STRM8 SAFE ZS IR B2 B1 AP INP0 STRM63 STRM0 BOK HTOP SP47 HZC RA zcl G1 sp s regs HLD MA ra fx mem WB ZP S zc IMG SOK1 SOK2 G2 G10 FA FF outp inp fa ff.
    intros R0 m sX len got SCX KP ZC SVh EF EW Q10 Q9 Q2 Q12 Q13 Q11 Q1R Hl Hg NG4 Hmx.
    layfull.
    pose proof safe_facts as (_ & _ & _ & Bflags & Bwrap & _ & _ & Bn). pose proof ra_facts as [RAB RET].
    assert (Q1 : getr R0 1 = zw ra) by (rewrite Q1R; exact G1).
    destruct SVh as (V1 & V2 & V3 & V4 & V5 & V6). rewrite G1 in V1. rewrite u_zw_small in V1 by lia.
    replace (sp + -8) with (sp - 64 + 56) in V1 by lia. replace (sp + -16) with (sp - 64 + 48) in V2 by lia. replace (sp + -24) with (sp - 64 + 40) in V3 by lia.
    replace (sp + -32) with (sp - 64 + 32) in V4 by lia. replace (sp + -40) with (sp - 64 + 24) in V5 by lia. replace (sp + -48) with (sp - 64 + 16) in V6 by lia.
    pose proof KP as KP'. destruct KP' as (_ & _ & _ & _ & _ & _ & WS & WF & WZ).
    pose proof ZC as ZC'. destruct ZC' as (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C96).
    pose proof (Z.mod_pos_bound (zs_total_in (zc_strm zc)) (2 ^ 64) ltac:(lia)) as TIB.
    pose proof (Z.mod_pos_bound (zs_total_out (zc_strm zc)) (2 ^ 64) ltac:(lia)) as TOB.
    pose proof (Z.mod_pos_bound (is_flags s) (2 ^ 32) ltac:(lia)) as FLB.
    assert (UR1 : 0 <= bv_unsigned (getr R0 1) < 2 ^ 64) by exact (bv_unsigned_range_u64 _). assert (UR8 : 0 <= bv_unsigned (getr regs 8) < 2 ^ 64) by exact (bv_unsigned_range_u64 _). assert (UR9 : 0 <= bv_unsigned (getr regs 9) < 2 ^ 64) by exact (bv_unsigned_range_u64 _).
    assert (UR18 : 0 <= bv_unsigned (getr regs 18) < 2 ^ 64) by exact (bv_unsigned_range_u64 _). assert (UR19 : 0 <= bv_unsigned (getr regs 19) < 2 ^ 64) by exact (bv_unsigned_range_u64 _). assert (UR20 : 0 <= bv_unsigned (getr regs 20) < 2 ^ 64) by exact (bv_unsigned_range_u64 _). assert (UR21 : 0 <= bv_unsigned (getr regs 21) < 2 ^ 64) by exact (bv_unsigned_range_u64 _).
    pose proof (Z.mod_small (bv_unsigned (getr regs 8)) (2 ^ (8 * Z.of_nat 8)) ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); exact (bv_unsigned_range_u64 _))) as MS8.
    pose proof (Z.mod_small (bv_unsigned (getr regs 9)) (2 ^ (8 * Z.of_nat 8)) ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); exact (bv_unsigned_range_u64 _))) as MS9.
    pose proof (Z.mod_small (bv_unsigned (getr regs 18)) (2 ^ (8 * Z.of_nat 8)) ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); exact (bv_unsigned_range_u64 _))) as MS18.
    pose proof (Z.mod_small (bv_unsigned (getr regs 19)) (2 ^ (8 * Z.of_nat 8)) ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); exact (bv_unsigned_range_u64 _))) as MS19.
    pose proof (Z.mod_small (bv_unsigned (getr regs 20)) (2 ^ (8 * Z.of_nat 8)) ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); exact (bv_unsigned_range_u64 _))) as MS20.
    pose proof (Z.mod_small (bv_unsigned (getr regs 21)) (2 ^ (8 * Z.of_nat 8)) ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); exact (bv_unsigned_range_u64 _))) as MS21.
    destruct RA as [_ RA2].
    runG R0 m sX len got [false; false; true] [RVal (EVar 37%nat); RVal (EVar 39%nat); RVal (EVar 44%nat); RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 48%nat); RVal (EVar 49%nat)] RR HRR Hfr Hms.
    all: try arm_side.
    all: try (rewrite (land_m2_even ra) by exact RA2; reflexivity).
    all: try (rewrite (proj2 (Z.ltb_lt 0 inp)) by lia; rewrite (proj2 (Z.ltb_ge (inp + len) 1)) by lia; discriminate).
    rewrite ?szwrap32_small in Hms by lia.
    lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => exists RR, M end. split; [by_run Hms|].
    symex_reg HRR (10%bv : reg) as P10. symex_reg HRR (2%bv : reg) as P2.
    split; [rewrite P10; reflexivity|]. split; [rewrite P2; f_equal; lia|]. split; [fr_weak Hfr|].
    split; [fin_restored HRR|].
    split; [| split].
    - clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SCX S0 S63 Z0 Z63 A5. is6_peel SCX.
    - clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 KP Hl. keep_peel KP.
    - clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 Z0 Z63 S0 S63 A5 Hl I0 I63 N0 C0 C8 C16 C24 C32 C40 C48 C56 C64 C72 C80 C96 TIB. unfold ZSC, zG1.
      destruct (zc_strm zc) as [zti zto zmsg zdt zad]; cbn [zs_total_in zs_total_out zs_msg zs_adler zs_set_total_in] in *.
      rewrite Z.add_0_r. repeat match goal with |- _ /\ _ => split end.
      all: first [ tcell C0 | tcell C8 | tcell C24 | tcell C32 | tcell C40 | tcell C48 | tcell C56 | tcell C64 | tcell C72 | tcell C80 | tcell C96
                 | eapply cell_mod; [tcell C0| unfold wrap64; apply wrap64_cell] ].
  Qed.


  Definition wrG : Z := if is_flags s =? -1 then 0 else Z.land (is_wrap s) (-5).
  Definition sGf (sX : inflate_state) : inflate_state :=
    iset_flags (iset_havedict (iset_last (iset_mode (iset_next (iset_distcode (iset_lencode (iset_bits (iset_hold (iset_head (iset_dmax
      (iset_back (iset_sane (iset_wnext (iset_whave (iset_wsize (iset_total (iset_wrap (iset_have sX 4) wrG) 0) 0) 0) 0) 1) (-1))
      32768) 0) 0) 0) (CDyn 0)) (CDyn 0)) 0) TYPE) 0) 0) (is_flags sX).
  Definition zGok (len : Z) : zstrm :=
    mkZS (wrap64 (zs_total_in (zc_strm zc) + len)) (zs_total_out (zc_strm zc))
         (if wrG =? 0 then zs_adler (zc_strm zc) else Z.land wrG 1) (zs_data_type (zc_strm zc)) MSG_NULL.

  Local Ltac finG RR HRR Hfr Hms Q1 SCX KP S0 S63 Z0 Z63 A5 Hl I0 I63 N0 C24 C32 C56 C64 C72 C80 C96 FLE MA0 :=
    rewrite Q1 in Hms; rewrite ?szwrap32_small in Hms by lia; rewrite ?FLE in Hms;
    lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => exists RR, M end; split; [by_run Hms|];
    let P := fresh "P" in
    split; [symex_reg HRR (10%bv : reg) as P; rewrite P; reflexivity|];
    split; [symex_reg HRR (2%bv : reg) as P; rewrite P; f_equal; lia|];
    split; [fr_weak Hfr|];
    split; [| split];
    [ clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SCX S0 S63 Z0 Z63 A5;
      rewrite (wbytes_sd_split _ (S + 76) 0), (wbytes_sd_split _ (S + 7160) (-4294967295));
      replace (S + 76 + 4) with (S + 80) by lia; replace (S + 7160 + 4) with (S + 7164) by lia;
      replace (Z_to_le_bytes 4 (-4294967295)) with (Z_to_le_bytes 4 1) by (rewrite <- (SymExec.Z_to_le_bytes_mod 4 (-4294967295)); reflexivity);
      change (Z.shiftr (-4294967295) 32) with (-1); change (Z_to_le_bytes 4 (Z.shiftr 0 32)) with (Z_to_le_bytes 4 0);
      replace (Z_to_le_bytes 8 (S + 1384)) with (Z_to_le_bytes 8 (codeptr_addr 75438 77486 S (CDyn 0))) by (cbn [codeptr_addr]; f_equal; lia);
      change TYPE with 16191; is6_peel SCX
    | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 KP Hl; keep_peel KP
    | clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 Z0 Z63 S0 S63 A5 Hl I0 I63 N0 C24 C32 C56 C64 C72 C80 C96 MA0; unfold ZSC; cbn [zs_total_in zs_total_out zs_msg zs_adler zs_data_type];
      rewrite MA0; rewrite Z.add_0_r; repeat match goal with |- _ /\ _ => split end;
      first [ tcell C24 | tcell C32 | tcell C56 | tcell C64 | tcell C72 | tcell C80 | tcell C96
            | eapply cell_mod; [tcell C24| first [apply wrap64_cell | apply mod64_cell | rewrite mod2_land1; reflexivity]] ] ].

  Local Ltac hide_ne := repeat match goal with H : ?a <> ?b |- _ => change (@id Prop (a <> b)) in H end.
  Local Ltac unhide_ne := repeat match goal with H : @id Prop (?a <> ?b) |- _ => change (a <> b) in H end.

  Lemma syG_ok : forall R0 m sX len,
    is6_scalars m S (ISP ZP WB) sX -> KEEP m -> ZSC m inp n (zc_strm zc) -> SV m -> (is_flags sX = is_flags s) -> (is_wrap sX = is_wrap s) -> is_wbits sX = 15 ->
    getr R0 10 = zw ZP -> getr R0 9 = zw S -> getr R0 2 = zw (sp - 64) -> getr R0 12 = zw inp -> getr R0 13 = zw len ->
    getr R0 11 = zw 4 -> getr R0 1 = getr regs 1 ->
    0 <= len <= n -> 16180 <= is_mode sX <= 16211 ->
    exists R m1, msteps RS (mkst R0 (Z_to_bv 64 pc_G) m s6u_rom) (mkst R (Z_to_bv 64 ra) m1 s6u_rom)
      /\ getr R 10 = zw Z_OK /\ getr R 2 = zw sp
      /\ (forall r, reg_in r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 18; 19; 20]%bv = false -> getr R r = getr R0 r)
      /\ RESTORED R
      /\ is6_scalars m1 S (ISP ZP WB) (sGf sX) /\ KEEP m1 /\ ZSC m1 (inp + len) (n - len) (zGok len).
  Proof using STRM8 SAFE ZS IR B2 B1 AP INP0 STRM63 STRM0 BOK HTOP SP47 HZC RA zcl G1 sp s regs HLD MA ra fx mem WB ZP S zc IMG SOK1 SOK2 G2 G10 FA FF outp inp fa ff MA0.
    intros R0 m sX len SCX KP ZC SVh EF EW EWB Q10 Q9 Q2 Q12 Q13 Q11 Q1R Hl Hmd.
    layfull.
    pose proof safe_facts as (_ & _ & _ & Bflags & Bwrap & _ & _ & Bn). pose proof ra_facts as [RAB RET].
    pose proof sync14_facts as (F14 & W5 & WB15).
    assert (Q1 : getr R0 1 = zw ra) by (rewrite Q1R; exact G1).
    destruct SVh as (V1 & V2 & V3 & V4 & V5 & V6). rewrite G1 in V1. rewrite u_zw_small in V1 by lia.
    replace (sp + -8) with (sp - 64 + 56) in V1 by lia. replace (sp + -16) with (sp - 64 + 48) in V2 by lia. replace (sp + -24) with (sp - 64 + 40) in V3 by lia.
    replace (sp + -32) with (sp - 64 + 32) in V4 by lia. replace (sp + -40) with (sp - 64 + 24) in V5 by lia. replace (sp + -48) with (sp - 64 + 16) in V6 by lia.
    pose proof KP as KP'. destruct KP' as (_ & _ & _ & _ & _ & _ & WS & WF & WZ).
    pose proof ZC as ZC'. destruct ZC' as (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C96).
    pose proof (Z.mod_pos_bound (zs_total_in (zc_strm zc)) (2 ^ 64) ltac:(lia)) as TIB.
    pose proof (Z.mod_pos_bound (zs_total_out (zc_strm zc)) (2 ^ 64) ltac:(lia)) as TOB.
    pose proof (Z.mod_pos_bound (is_flags s) (2 ^ 32) ltac:(lia)) as FLB.
    pose proof (flags_test (is_flags s) Bflags) as FT.
    assert (FLE : szwrap 32 (is_flags s mod 2 ^ 32) = is_flags sX) by (rewrite EF; apply szwrap32_of_mod32; exact Bflags).
    assert (FT' : szwrap 32 (is_flags s mod 2 ^ 32) mod 2 ^ 64 <> 18446744073709551615) by (intros X; apply F14, (proj1 FT), X).
    assert (CRW : cell s6u_segs m (S + 20) 4 5) by exact (fields_nth s6u_segs m S _ _ 32 20 4%nat _ SCX eq_refl eq_refl).
    assert (CRB : cell s6u_segs m (S + 64) 4 15) by exact (fields_nth s6u_segs m S _ _ 33 64 4%nat _ SCX eq_refl eq_refl).
    pose proof (is6_flags _ _ _ _ SCX) as D24. pose proof (is6_wrap _ _ _ _ SCX) as D16. pose proof (is6_wbits _ _ _ _ SCX) as D68. rewrite EF in D24. rewrite EW in D16. rewrite EWB in D68.
    assert (UR1 : 0 <= bv_unsigned (getr R0 1) < 2 ^ 64) by exact (bv_unsigned_range_u64 _). assert (UR8 : 0 <= bv_unsigned (getr regs 8) < 2 ^ 64) by exact (bv_unsigned_range_u64 _). assert (UR9 : 0 <= bv_unsigned (getr regs 9) < 2 ^ 64) by exact (bv_unsigned_range_u64 _).
    assert (UR18 : 0 <= bv_unsigned (getr regs 18) < 2 ^ 64) by exact (bv_unsigned_range_u64 _). assert (UR19 : 0 <= bv_unsigned (getr regs 19) < 2 ^ 64) by exact (bv_unsigned_range_u64 _). assert (UR20 : 0 <= bv_unsigned (getr regs 20) < 2 ^ 64) by exact (bv_unsigned_range_u64 _). assert (UR21 : 0 <= bv_unsigned (getr regs 21) < 2 ^ 64) by exact (bv_unsigned_range_u64 _).
    pose proof (Z.mod_small (bv_unsigned (getr regs 8)) (2 ^ (8 * Z.of_nat 8)) ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); exact (bv_unsigned_range_u64 _))) as MS8.
    pose proof (Z.mod_small (bv_unsigned (getr regs 9)) (2 ^ (8 * Z.of_nat 8)) ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); exact (bv_unsigned_range_u64 _))) as MS9.
    pose proof (Z.mod_small (bv_unsigned (getr regs 18)) (2 ^ (8 * Z.of_nat 8)) ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); exact (bv_unsigned_range_u64 _))) as MS18.
    pose proof (Z.mod_small (bv_unsigned (getr regs 19)) (2 ^ (8 * Z.of_nat 8)) ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); exact (bv_unsigned_range_u64 _))) as MS19.
    pose proof (Z.mod_small (bv_unsigned (getr regs 20)) (2 ^ (8 * Z.of_nat 8)) ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); exact (bv_unsigned_range_u64 _))) as MS20.
    pose proof (Z.mod_small (bv_unsigned (getr regs 21)) (2 ^ (8 * Z.of_nat 8)) ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); exact (bv_unsigned_range_u64 _))) as MS21.
    pose proof (is6_strm _ _ _ _ SCX) as D0. cbn [q_strm] in D0. rewrite Z.add_0_r in D0. pose proof (is6_mode _ _ _ _ SCX) as D8.
    pose proof consts as (KA & KF & _). rewrite KA in FA. rewrite KF in FF. pose proof C64 as C64l. rewrite FA in C64l. pose proof C72 as C72l. rewrite FF in C72l.
    destruct RA as [_ RA2].
    assert (EPROG : sGf sX = (iset_mode (iset_wrap (iset_flags (iset_back (iset_sane (iset_head (iset_dmax (iset_flags (iset_havedict (iset_last (iset_mode (iset_distcode (iset_lencode (iset_bits (iset_hold (iset_next (iset_total (iset_wnext (iset_wrap (iset_whave (iset_wsize (iset_have sX 4) 0) 0) 5) 0) 0) 0) 0) 0) (CDyn 0)) (CDyn 0)) 16180) 0) 0) (-1)) 32768) 0) 1) (-1)) (is_flags sX)) 1) TYPE)) by (unfold sGf, wrG; replace (is_flags s =? -1) with false by (symmetry; apply Z.eqb_neq; exact F14); rewrite W5; reflexivity).
    rewrite EPROG. unfold zGok, wrG. replace (is_flags s =? -1) with false by (symmetry; apply Z.eqb_neq; exact F14). rewrite W5. change (Z.land 5 (-5)) with 1. change (1 =? 0) with false.
    pose proof align_facts as [AL1 AL2].
    runG R0 m sX len 4 [false; false; false; false; false; false; false; false; false; true; false; true; false; false; false; false; false; false; false; false; true]
      [RVal (EVar 37%nat); RVal (EVar 39%nat); RVal (EVar 41%nat); RVal (EVar 40%nat); RVal (ELit 0x1a9f4); RVal (ELit 0x1aa04); RVal (EVar 33%nat); RVal (EVar 32%nat);
       RVal (EVar 43%nat); RVal (ELit 15); RVal (ELit 15); RVal (ELit 5);
       RVal (EVar 44%nat); RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 48%nat); RVal (EVar 49%nat)] RR HRR Hfr Hms.
    all: try arm_side.
    all: try (rewrite (land_m2_even ra) by exact RA2; reflexivity).
    all: try (rewrite (proj2 (Z.ltb_lt 0 inp)) by lia; rewrite (proj2 (Z.ltb_ge (inp + len) 1)) by lia; discriminate).
    all: try (exact FT'). all: try (intros X; apply FT'; exact X). all: try (rewrite ?szwrap32_small by lia; lia). all: try discriminate. all: try exact AL2. all: try exact AL1.
    all: lazymatch goal with H : msteps _ _ _ |- _ => idtac | |- ?G => fail 1 "SIDEGOAL-FAIL:" G end.
    rewrite ?szwrap32_small in Hms by lia. rewrite ?FLE in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => exists RR, M end. split; [by_run Hms|].
    symex_reg HRR (10%bv : reg) as P10. symex_reg HRR (2%bv : reg) as P2.
    split; [rewrite P10; reflexivity|]. split; [rewrite P2; f_equal; lia|]. split; [fr_weak Hfr|].
    split; [fin_restored HRR|].
    split; [| split].
    - clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 SCX S0 S63 Z0 Z63 A3 A5 P96 P47.
      try rewrite (wbytes_sd_split _ (S + 8) 16180), (wbytes_sd_split _ (S + 24) (-4294967296)), (wbytes_sd_split _ (S + 72) 0), (wbytes_sd_split _ (S + 7160) (-4294967295)).
      replace (S + 8 + 4) with (S + 12) by lia; replace (S + 24 + 4) with (S + 28) by lia; replace (S + 72 + 4) with (S + 76) by lia; replace (S + 7160 + 4) with (S + 7164) by lia.
      replace (Z_to_le_bytes 4 (-4294967296)) with (Z_to_le_bytes 4 0) by (rewrite <- (SymExec.Z_to_le_bytes_mod 4 (-4294967296)); reflexivity).
      replace (Z_to_le_bytes 4 (-4294967295)) with (Z_to_le_bytes 4 1) by (rewrite <- (SymExec.Z_to_le_bytes_mod 4 (-4294967295)); reflexivity).
      change (Z.shiftr 16180 32) with 0; change (Z.shiftr (-4294967296) 32) with (-1); change (Z.shiftr 0 32) with 0; change (Z.shiftr (-4294967295) 32) with (-1).
      replace (Z_to_le_bytes 8 (S + 1384)) with (Z_to_le_bytes 8 (codeptr_addr 75438 77486 S (CDyn 0))) by (cbn [codeptr_addr]; f_equal; lia).
      is6_peel SCX.
    - clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 KP Hl. keep_peel KP.
    - clear - G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS FA FF SAFE MA0 Z0 Z63 S0 S63 A1 A3 A5 P96 P47 Hl I0 I63 N0 C0 C8 C16 C24 C32 C40 C48 C56 C64 C72 C80 C96 TIB. unfold ZSC, zGok.
      destruct (zc_strm zc) as [zti zto zmsg zdt zad]; cbn [zs_total_in zs_total_out zs_msg zs_adler zs_data_type] in *.
      rewrite MA0. rewrite Z.add_0_r. repeat match goal with |- _ /\ _ => split end.
      all: try first [ tcell C0 | tcell C8 | tcell C16 | tcell C24 | tcell C32 | tcell C40 | tcell C48 | tcell C56 | tcell C64 | tcell C72 | tcell C80 | tcell C96
                 | eapply cell_mod; [first [tcell C0 | tcell C8 | tcell C16 | tcell C40 | tcell C48 | tcell C96]| first [reflexivity | apply wrap64_cell | apply mod64_cell | symmetry; apply mod64_cell | rewrite mod2_land1; reflexivity | unfold wrap64; apply wrap64_cell | symmetry; unfold wrap64; apply wrap64_cell]] ].
      all: try (replace (wrap64 (zti + len)) with ((zti mod 2 ^ 64 + len) mod 2 ^ 64)
                  by (first [ unfold wrap64; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.add_mod_idemp_l by lia; reflexivity
                            | symmetry; unfold wrap64; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.add_mod_idemp_l by lia; reflexivity ]);
                tcell C16).
      all: lazymatch goal with |- ?G => fail 1 "ZSC-LEFT:" G end.
  Qed.

  Definition sFT : inflate_state := iset_have (iset_have sB4 0) (fst (syncsearch_loop bufl 0 0)).
  Definition sE : inflate_state := if is_mode s =? SYNC then s else sFT.

  Lemma kq_facts : 0 <= kq <= 4 /\ is_bits s = 8 * kq + is_bits s mod 8 /\ 0 <= is_bits s mod 8 < 8 /\
    Z.land (is_bits s) 7 = is_bits s mod 8 /\ 0 <= hold1.
  Proof using STRM8 SAFE STRM0 sp zc ZP.
    pose proof safe_facts as (Bbits & Bhold & _). pose proof (mod8_range (is_bits s) ltac:(lia)) as [R7 DEC].
    pose proof (land7_m8 (is_bits s) ltac:(lia)) as [L7 L8]. unfold kq, hold1.
    repeat split; try lia.
    all: first [ pose proof (Z.div_pos (is_bits s) 8); lia
               | destruct (Z_lt_le_dec (is_bits s) 8) as [LT|GE]; [pose proof (kq_zero (is_bits s) ltac:(lia)); lia| pose proof (kq_cases (is_bits s) ltac:(lia)); lia]
               | apply Z.div_pos; [lia|]; apply Z.pow_pos_nonneg; lia ].
  Qed.

  Lemma sE_facts : is_flags sE = is_flags s /\ is_wrap sE = is_wrap s /\ (inflateStateCheck s = false -> inflateStateCheck sE = false) /\
    is_lens sE = is_lens s /\ is_work sE = is_work s /\ is_codes sE = is_codes s /\ is_window sE = is_window s /\ is_window_blk sE = is_window_blk s /\
    (is_mode sE = is_mode s \/ is_mode sE = SYNC) /\ is_wbits sE = is_wbits s.
  Proof using.
    unfold sE, sFT, sB4. destruct (is_mode s =? SYNC); [repeat split; auto|].
    repeat split; try reflexivity. right; reflexivity.
  Qed.

  Ltac model_cbv := cbv beta iota delta [auxp iv_aux ivar_ref negb Z.eqb iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head
    iset_wbits iset_wsize iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset iset_extra iset_lencode iset_distcode
    iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have iset_next iset_lens iset_work iset_codes iset_sane iset_back iset_was is_mode is_last
    is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext is_window is_window_blk is_hold is_bits is_length
    is_offset is_extra is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back
    is_was is_self_blk zs_set_total_in zs_set_total_out zs_set_adler zs_set_msg zs_total_in zs_total_out zs_adler zs_msg zs_data_type].

  Lemma inflateSync_m_run :
    inflateStateCheck s = false -> ~ (n = 0 /\ is_bits s < 8) ->
    inflateSync_m ivar_ref s zc =
      (let '(gotf, lenf) := syncsearch_loop input (is_have sE) 0 in
       if gotf =? 4 then (sGf sE, mkZRet lenf [] (zGok lenf) Z_OK)
       else (iset_have sE gotf, mkZRet lenf [] (zG1 lenf) Z_DATA_ERROR)).
  Proof using STRM8 SAFE STRM0 sp ZP.
    intros CHK NBUF. pose proof kq_facts as (K4 & DEC & R7 & L7 & H1p). pose proof safe_facts as (Bbits & Bhold & _).
    pose proof sE_facts as (EF & EW & ECHK & _). specialize (ECHK CHK).
    unfold inflateSync_m. rewrite CHK.
    replace ((zlength input =? 0) && (is_bits s <? 8)) with false.
    2:{ symmetry. apply Bool.andb_false_iff. destruct (Z.eq_dec n 0); [right; apply Z.ltb_ge; lia| left; apply Z.eqb_neq; lia]. }
    unfold syncsearch.
    pose proof (is_upd_facts) as UF.
    match goal with |- context [if negb (is_mode s =? SYNC) then ?A else s] => assert (FIRSTEQ : A = sFT) end.
    { destruct (UF s SYNC) as (U1 & U2 & _). rewrite !U1, !U2.
      destruct (UF (iset_mode s SYNC) (Z.shiftr (is_hold s) (Z.land (is_bits s) 7))) as (_ & _ & U3 & _). rewrite !U3, !U2.
      rewrite !L7. rewrite (Z.shiftr_div_pow2 (is_hold s) (is_bits s mod 8)) by lia. fold hold1.
      set (s3 := iset_bits _ _).
      assert (B3 : is_bits s3 = 8 * Z.of_nat (Z.to_nat kq)) by (subst s3; cbn; rewrite Z2Nat.id by lia; lia).
      rewrite (sync_drain_run (Z.to_nat kq) _ s3 []); [| exact B3|].
      2:{ rewrite B3, Z2Nat.id, Z.shiftr_div_pow2 by lia. replace (8 * kq / 2 ^ 3) with kq by (change (2 ^ 3) with 8; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity). lia. }
      rewrite app_nil_l. cbv beta iota.
      assert (H3 : is_hold s3 = hold1) by reflexivity. rewrite !H3. rewrite Z2Nat.id by lia. fold bufl.
      destruct (UF (iset_bits (iset_hold s3 (Z.shiftr hold1 (8 * kq))) 0) 0) as (_ & _ & _ & _ & _ & _ & U7 & _). rewrite U7.
      destruct (syncsearch_loop bufl 0 0) as [g1 n1] eqn:SS1.
      unfold sFT. rewrite SS1. cbn [fst]. unfold sB4. subst s3. rewrite iset_hb. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
    rewrite FIRSTEQ. clear FIRSTEQ.
    replace (if negb (is_mode s =? SYNC) then sFT else s) with sE by (unfold sE; destruct (is_mode s =? SYNC); reflexivity).
    destruct (syncsearch_loop input (is_have sE) 0) as [gotf lenf].
    destruct (UF sE gotf) as (_ & _ & _ & _ & _ & _ & U7 & U8 & U9 & _). rewrite !U7, !U8, !U9.
    destruct (Z.eqb_spec gotf 4) as [G4|G4]; cbn [negb]; [| unfold zG1; reflexivity]. subst gotf.
    unfold sGf, zGok, wrG. rewrite <- !EF, <- !EW.
    destruct (Z.eqb_spec (is_flags sE) (-1)) as [F1|F1];
      [| destruct (UF sE 4) as (_ & _ & _ & _ & _ & _ & _ & _ & U9' & _);
         destruct (Z.eqb_spec (Z.land (is_wrap sE) (-5)) 0) as [W0|W0]; change (Z.lnot 4) with (-5); rewrite ?W0];
      unfold inflateReset; rewrite (proj2 (isc_upd sE 4 _ 0 0 0)), ECHK; unfold inflateResetKeep; rewrite (proj1 (isc_upd sE 4 _ 0 0 0)), ECHK;
      rewrite is_wrap_resets.
    - model_cbv. reflexivity.
    - model_cbv. reflexivity.
    - replace (Z.land (is_wrap sE) (-5) =? 0) with false by (symmetry; apply Z.eqb_neq; exact W0). cbn [negb]. model_cbv. reflexivity.
  Qed.

  Lemma izs_of_ZSC : forall m ni ai z, ZSC m ni ai z -> izs_cells MA m ZP ni ai outp (zc_avail_out zc) z S fa ff.
  Proof using.
    intros m ni ai z (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C96). rewrite Z.add_0_r in C0.
    unfold izs_cells, cell8, cell4. unfold cell in *. repeat split; assumption.
  Qed.

  Lemma ISREP6_of : forall m sX, is6_scalars m S (ISP ZP WB) sX -> KEEP m ->
    is_lens sX = is_lens s -> is_work sX = is_work s -> is_codes sX = is_codes s -> is_window sX = is_window s -> is_window_blk sX = is_window_blk s ->
    ISREP6 m S ZP WB sX /\ (WB = 0 <-> is_window_blk sX = None).
  Proof using IR.
    intros m sX SCX (L & W & C & WN & _) E1 E2 E3 E4 E5. destruct IR as (_ & _ & _ & _ & _ & IFF & WL).
    unfold ISREP6. rewrite E1, E2, E3, E4, E5.
    split; [| exact IFF]. split; [exact SCX|]. split; [exact L|]. split; [exact W|]. split; [exact C|]. split; [exact WN|]. split; [exact IFF| exact WL].
  Qed.

  Lemma frame_of_KEEP : forall m, KEEP m -> frame_mod mem m ((Z_to_bv 64 (sp - 96), 96) :: (Z_to_bv 64 ZP, 112) :: wz (iblocks (IP ZP S WB))).
  Proof using.
    intros m (_ & _ & _ & _ & _ & FM & _). eapply frame_mod_weaken; [| exact FM].
    intros a Ha. unfold FP. unfold wz, iblocks. cbn [map fst snd ip_p ip_w] in *. change zw with (Z_to_bv 64) in *.
    destruct Ha as (H1 & H2 & H3 & _). cbn. repeat split; try assumption.
  Qed.

  Lemma FL_KEEP_eq : FL_KEEP = [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
  Proof using. reflexivity. Qed.
  Definition FLK2 : list reg := [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv.
  Lemma rkeep_via2 : forall (R0 R1 R2 : bvmap 5 word) (K L : list reg),
    (forall r, In r K -> getr R1 r = getr R0 r) ->
    (forall r, reg_in r L = false -> getr R2 r = getr R1 r) ->
    forallb (fun r => negb (reg_in r L)) K = true ->
    forall r, In r K -> getr R2 r = getr R0 r.
  Proof using.
    intros R0 R1 R2 K L H1 H2 HL r Hr. rewrite <- (H1 r Hr). apply H2.
    apply forallb_forall with (x := r) in HL; [| exact Hr]. destruct (reg_in r L); [discriminate| reflexivity].
  Qed.
  Ltac rk_step FR Hfr := let H := fresh "FR" in pose proof (rkeep_via2 _ _ _ FLK2 _ FR Hfr ltac:(reflexivity)) as H; clear FR; rename H into FR.
  Lemma rkeep_final : forall R, RESTORED R -> (forall r, In r FLK2 -> getr R r = getr regs r) -> forall r, In r FL_KEEP -> getr R r = getr regs r.
  Proof using.
    intros R (H8 & H9 & H18 & H19 & H20) HK r Hr. rewrite FL_KEEP_eq in Hr. cbn in Hr.
    repeat (destruct Hr as [<-|Hr]; [first [exact H8|exact H9|exact H18|exact H19|exact H20| apply HK; unfold FLK2; cbn; repeat first [left; reflexivity | right]]|]).
    destruct Hr.
  Qed.

  Theorem inflateSync_run6u :
    HEAD <= is_mode s <= SYNC ->
    (0 <= S /\ S + FL_ISTATE_N <= 2 ^ 63 /\ 0 <= WB /\ WB + FL_WIN_N <= 2 ^ 63) ->
    let s' := fst (inflateSync_m ivar_ref s zc) in let r := snd (inflateSync_m ivar_ref s zc) in
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps RS (mkst regs (Z_to_bv 64 FL_A_ISY) mem (seg_rom RS)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RS))
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - 96), 96) :: (Z_to_bv 64 ZP, 112) :: wz (iblocks (IP ZP S WB)))
      /\ getr regs' 10 = Z_to_bv 64 (zr_rc r) /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep regs regs' FL_KEEP
      /\ zr_output r = [] /\ 0 <= zr_consumed r <= n
      /\ (ISREP6 mem' S ZP WB s' /\ HEAD <= is_mode s' <= SYNC /\ (0 <= S /\ S + FL_ISTATE_N <= 2 ^ 63 /\ 0 <= WB /\ WB + FL_WIN_N <= 2 ^ 63))
      /\ izs_cells MA mem' ZP (inp + zr_consumed r) (n - zr_consumed r) outp (zc_avail_out zc) (zr_strm r) S fa ff
      /\ (WB = 0 <-> is_window_blk s' = None).
  Proof using STRM8 MA0 SAFE FF FA ZS HLD IR B2 B1 IMG AP SOK2 SOK1 INP0 STRM63 STRM0 BOK HTOP SP47 HZC RA G1 G2 G10 zcl.
    intros MRNG IRG. pose proof n_nonneg as N0. pose proof safe_facts as (Bbits & Bhold & Bhave & Bflags & Bwrap & Bmode & Bin & Bn).
    pose proof KEEP0 as KP0. pose proof ZSC0 as ZC0. pose proof st_facts as (SC0 & _). pose proof IR as IR'. destruct IR' as (_ & _ & _ & _ & _ & IFF & _).
    assert (FR0 : forall r, In r FLK2 -> getr regs r = getr regs r) by (intros; reflexivity).
    change FL_A_ISY with pc_isy. change (seg_rom RS) with s6u_rom.
    assert (TRIV : forall R m1 rc, msteps RS (mkst regs (Z_to_bv 64 pc_isy) mem s6u_rom) (mkst R (Z_to_bv 64 ra) m1 s6u_rom) ->
      getr R 10 = zw rc -> getr R 2 = zw sp -> (forall r, reg_in r [2; 10; 11; 12; 13; 14; 15]%bv = false -> getr R r = getr regs r) -> RESTORED R ->
      is6_scalars m1 S (ISP ZP WB) s -> KEEP m1 -> ZSC m1 inp n (zc_strm zc) ->
      inflateSync_m ivar_ref s zc = (s, mkZRet 0 [] (zc_strm zc) rc) ->
      let s' := fst (inflateSync_m ivar_ref s zc) in let r := snd (inflateSync_m ivar_ref s zc) in
      exists regs' mem', msteps RS (mkst regs (Z_to_bv 64 pc_isy) mem s6u_rom) (mkst regs' (Z_to_bv 64 ra) mem' s6u_rom)
        /\ frame_mod mem mem' ((Z_to_bv 64 (sp - 96), 96) :: (Z_to_bv 64 ZP, 112) :: wz (iblocks (IP ZP S WB)))
        /\ getr regs' 10 = Z_to_bv 64 (zr_rc r) /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep regs regs' FL_KEEP
        /\ zr_output r = [] /\ 0 <= zr_consumed r <= n
        /\ (ISREP6 mem' S ZP WB s' /\ HEAD <= is_mode s' <= SYNC /\ (0 <= S /\ S + FL_ISTATE_N <= 2 ^ 63 /\ 0 <= WB /\ WB + FL_WIN_N <= 2 ^ 63))
        /\ izs_cells MA mem' ZP (inp + zr_consumed r) (n - zr_consumed r) outp (zc_avail_out zc) (zr_strm r) S fa ff
        /\ (WB = 0 <-> is_window_blk s' = None)).
    { intros R m1 rc MS Q10 Q2 Hfr RST SC1 KP1 ZC1 EQ. rewrite EQ. cbn [fst snd zr_rc zr_output zr_consumed zr_strm].
      exists R, m1. split; [exact MS|]. split; [exact (frame_of_KEEP m1 KP1)|]. split; [exact Q10|]. split; [exact Q2|].
      split; [exact (rkeep_final R RST ltac:(rk_step FR0 Hfr; exact FR0))|]. split; [reflexivity|]. split; [lia|].
      destruct (ISREP6_of m1 s SC1 KP1 eq_refl eq_refl eq_refl eq_refl eq_refl) as [IR1 IFF1].
      split; [split; [exact IR1| split; [exact MRNG| exact IRG]]|].
      split; [rewrite Z.add_0_r, Z.sub_0_r; exact (izs_of_ZSC _ _ _ _ ZC1)| exact IFF1]. }
    destruct (inflateStateCheck s) eqn:CHK.
    { destruct (syA_err CHK) as (R & m1 & MS & Q10 & Q2 & Hfr & RST & SC1 & KP1 & ZC1). apply (TRIV R m1 _ MS Q10 Q2 Hfr RST SC1 KP1 ZC1). unfold inflateSync_m. rewrite CHK. reflexivity. }
    destruct (Sumbool.sumbool_and _ _ _ _ (Z.eq_dec n 0) (Z_lt_le_dec (is_bits s) 8)) as [[NZ BL]|NB].
    { destruct (syA_buf CHK NZ BL) as (R & m1 & MS & Q10 & Q2 & Hfr & RST & SC1 & KP1 & ZC1). apply (TRIV R m1 _ MS Q10 Q2 Hfr RST SC1 KP1 ZC1). unfold inflateSync_m. rewrite CHK.
      replace ((zlength input =? 0) && (is_bits s <? 8)) with true by (symmetry; apply andb_true_intro; split; [apply Z.eqb_eq; exact NZ| apply Z.ltb_lt; exact BL]).
      reflexivity. }
    assert (NBUF : ~ (n = 0 /\ is_bits s < 8)) by (destruct NB; lia). clear NB TRIV.
    cbv zeta. rewrite (inflateSync_m_run CHK NBUF).
    destruct (syA_ok CHK NBUF) as (R1 & m1 & MS1 & A10 & A9 & A12 & A15 & A2 & Hfr1 & SC1 & KP1 & ZC1 & SV1). rk_step FR0 Hfr1.
    assert (TOE : exists R2 m2, msteps RS (mkst R1 (Z_to_bv 64 pc_B) m1 s6u_rom) (mkst R2 (Z_to_bv 64 pc_E) m2 s6u_rom)
      /\ getr R2 10 = zw ZP /\ getr R2 9 = zw S /\ getr R2 2 = zw (sp - 64) /\ getr R2 15 = zw n
      /\ (forall r, In r FLK2 -> getr R2 r = getr regs r) /\ getr R2 1 = getr regs 1
      /\ is6_scalars m2 S (ISP ZP WB) sE /\ KEEP m2 /\ ZSC m2 inp n (zc_strm zc) /\ SV m2 /\ 0 <= is_have sE < 2 ^ 31).
    { pose proof kq_facts as (K4 & DEC & R7 & L7 & H1p).
      assert (X1 : getr R1 1 = getr regs 1) by (rewrite (Hfr1 1%bv eq_refl); reflexivity).
      destruct (Z.eqb_spec (is_mode s) SYNC) as [MS|MS].
      - assert (ESE : sE = s) by (unfold sE; rewrite MS, Z.eqb_refl; reflexivity). rewrite ESE.
        destruct (syB_sync R1 m1 SC1 A10 A9 A2 A12 A15 MS) as (R2 & MS2 & Y10 & Y9 & Y2 & Y15 & Hfr2).
        exists R2, m1. split; [exact MS2|]. split; [exact Y10|]. split; [exact Y9|]. split; [exact Y2|]. split; [exact Y15|].
        split; [rk_step FR0 Hfr2; exact FR0|]. split; [rewrite (Hfr2 1%bv eq_refl); exact X1|].
        split; [exact SC1|]. split; [exact KP1|]. split; [exact ZC1|]. split; [exact SV1| exact Bhave].
      - assert (NSY : (is_mode s =? SYNC) = false) by (apply Z.eqb_neq; exact MS).
        destruct (Z.eq_dec kq 0) as [K0|K1].
        + destruct (syB_k0 R1 m1 SC1 KP1 ZC1 SV1 A10 A9 A2 A12 MS K0) as (R2 & m2 & MS2 & Y10 & Y9 & Y2 & Y15 & Hfr2 & SC2 & KP2 & ZC2 & SV2).
          assert (ESE : sE = sB0).
          { unfold sE, sFT, sB0, sB4, bufl. rewrite NSY, K0. cbn [Z.to_nat drain_bytes syncsearch_loop fst].
            rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity. }
          rewrite ESE. exists R2, m2. split; [exact MS2|]. split; [exact Y10|]. split; [exact Y9|]. split; [exact Y2|].
          split; [exact Y15|]. split; [rk_step FR0 Hfr2; exact FR0|]. split; [rewrite (Hfr2 1%bv eq_refl); exact X1|].
          split; [exact SC2|]. split; [exact KP2|]. split; [exact ZC2|]. split; [exact SV2| cbn; lia].
        + destruct (syB_drain R1 m1 SC1 KP1 ZC1 SV1 A10 A9 A2 A12 MS ltac:(lia)) as (R2 & m2 & MS2 & Y10 & Y9 & Y2 & Y14 & Y11 & Y15 & Y16 & Y13 & Y12 & Hfr2 & SC2 & KP2 & ZC2 & SV2 & BUF).
          destruct (syS1_loop 4 R2 m2 0 0 BUF Y15 Y14 Y13 Y16 Y11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (R3 & MS3 & C11 & C13 & Hfr3).
          cbn [Z.to_nat skipn] in C11, C13.
          pose proof (syncsearch_loop_bounds bufl 0 0 ltac:(lia) ltac:(lia)) as [GB _].
          set (g1 := fst (syncsearch_loop bufl 0 0)) in *.
          destruct (syE1 R3 m2 (iset_have sB4 0) g1 SC2 KP2 ZC2 SV2 ltac:(rewrite (Hfr3 10%bv eq_refl); exact Y10) ltac:(rewrite (Hfr3 9%bv eq_refl); exact Y9) C11 ltac:(rewrite (Hfr3 12%bv eq_refl); exact Y12) ltac:(lia))
            as (R4 & m4 & MS4 & D10 & D9 & D11 & D15 & Hfr4 & SC4 & KP4 & ZC4 & SV4).
          assert (ESE : sE = iset_have sB4 g1) by (unfold sE, sFT; rewrite NSY; reflexivity). rewrite ESE.
          assert (EHH : iset_have (iset_have sB4 0) g1 = iset_have sB4 g1) by (destruct sB4; reflexivity). rewrite EHH in SC4.
          exists R4, m4. split; [eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| exact MS4]]|].
          split; [exact D10|]. split; [exact D9|].
          split; [rewrite (Hfr4 2%bv eq_refl), (Hfr3 2%bv eq_refl); exact Y2|]. split; [exact D15|].
          split; [rk_step FR0 Hfr2; rk_step FR0 Hfr3; rk_step FR0 Hfr4; exact FR0|].
          split; [rewrite (Hfr4 1%bv eq_refl), (Hfr3 1%bv eq_refl), (Hfr2 1%bv eq_refl); exact X1|].
          split; [exact SC4|]. split; [exact KP4|]. split; [exact ZC4|]. split; [exact SV4| cbn; lia]. }
    clear FR0. destruct TOE as (R2 & m2 & MS2 & Y10 & Y9 & Y2 & Y15 & FR & Y1 & SCE & KPE & ZCE & SVE & HVB).
    pose proof sE_facts as (EF & EW & _ & EL & EWK & EC & EWI & EWB & EM & EWBT).
    destruct (syE R2 m2 (is_have sE) ZCE Y10 Y9 ltac:(exact (is6_have _ _ _ _ SCE)) Y15 HVB) as (R3 & MS3 & E10 & E11 & E12 & E13 & ECT & Hfr3).
    assert (TOG : exists R4, msteps RS (mkst R2 (Z_to_bv 64 pc_E) m2 s6u_rom) (mkst R4 (Z_to_bv 64 pc_G) m2 s6u_rom)
      /\ getr R4 10 = zw ZP /\ getr R4 12 = zw inp /\ getr R4 11 = zw (fst (syncsearch_loop input (is_have sE) 0))
      /\ getr R4 13 = zw (snd (syncsearch_loop input (is_have sE) 0))
      /\ (forall r, reg_in r [5; 6; 11; 12; 13; 14; 15; 16; 17]%bv = false -> getr R4 r = getr R2 r)).
    { destruct ((n =? 0) || (3 <? is_have sE)) eqn:DSP.
      - rewrite syncsearch_loop_stop.
        2:{ apply Bool.orb_true_iff in DSP. destruct DSP as [D|D]; [left| right; apply Z.ltb_lt in D; lia].
            apply Z.eqb_eq in D. unfold zlength in D. destruct (zc_input zc); [reflexivity| cbn in D; lia]. }
        cbn [fst snd]. exists R3. split; [exact MS3|]. split; [exact E10|]. split; [exact E12|]. split; [exact E11|]. split; [exact E13|]. fr_weak Hfr3.
      - apply Bool.orb_false_iff in DSP. destruct DSP as [D1 D2]. apply Z.eqb_neq in D1. apply Z.ltb_ge in D2. destruct (ECT eq_refl) as (E14 & E16 & E17 & E15).
        pose proof KPE as KPE'. destruct KPE' as (_ & _ & _ & _ & HB & _).
        destruct (syS2_loop (Datatypes.S (Z.to_nat n)) R3 m2 0 (is_have sE) (holds_cells m2 HB) E12 E14 E13 E16 E17 E15 E11 ltac:(lia) ltac:(lia) ltac:(lia))
          as (R4 & MS4 & F12 & F16 & F11 & F13 & Hfr4).
        cbn [Z.to_nat skipn] in F11, F13.
        exists R4. split; [eapply msteps_trans; [exact MS3| exact MS4]|]. split; [rewrite (Hfr4 10%bv eq_refl); exact E10|]. split; [exact F12|].
        split; [exact F11|]. split; [exact F13|].
        intros r Hr. rewrite (Hfr4 r); [apply Hfr3; eapply reg_in_sub; [| exact Hr]; reflexivity| eapply reg_in_sub; [| exact Hr]; reflexivity]. }
    destruct TOG as (R4 & MS4 & F10 & F12 & F11 & F13 & Hfr4).
    pose proof (syncsearch_loop_bounds input (is_have sE) 0 ltac:(lia) ltac:(lia)) as [GB LB].
    destruct (syncsearch_loop input (is_have sE) 0) as [gotf lenf]. cbn [fst snd] in F11, F13, GB, LB.
    cbv beta iota zeta.
    assert (X1 : getr R4 1 = getr regs 1) by (rewrite (Hfr4 1%bv eq_refl); exact Y1).
    assert (X9 : getr R4 9 = zw S) by (rewrite (Hfr4 9%bv eq_refl); exact Y9).
    assert (X2 : getr R4 2 = zw (sp - 64)) by (rewrite (Hfr4 2%bv eq_refl); exact Y2).
    pose proof sync14_facts as (_ & _ & WB15).
    assert (MODR : 16180 <= is_mode sE <= 16211) by (unfold HEAD, SYNC in *; destruct EM as [EM|EM]; lia).
    rk_step FR Hfr4.
    destruct (Z.eqb_spec gotf 4) as [G4|G4].
    - subst gotf. rewrite ?Z.eqb_refl.
      destruct (syG_ok R4 m2 sE lenf SCE KPE ZCE SVE EF EW ltac:(rewrite EWBT; exact WB15) F10 X9 X2 F12 F13 F11 X1 ltac:(lia) MODR) as (R5 & m5 & MS5 & Z10 & Z2 & Hfr5 & RST5 & SC5 & KP5 & ZC5).
      rk_step FR Hfr5.
      exists R5, m5. cbn [fst snd zr_rc zr_output zr_consumed zr_strm].
      split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS4| exact MS5]]]|].
      split; [exact (frame_of_KEEP m5 KP5)|]. split; [exact Z10|]. split; [first [exact Z2| rewrite Z2; reflexivity]|]. split; [exact (rkeep_final R5 RST5 FR)|].
      split; [reflexivity|]. split; [lia|].
      destruct (ISREP6_of m5 (sGf sE) SC5 KP5 ltac:(etransitivity; [| exact EL]; reflexivity) ltac:(etransitivity; [| exact EWK]; reflexivity)
                  ltac:(etransitivity; [| exact EC]; reflexivity) ltac:(etransitivity; [| exact EWI]; reflexivity) ltac:(etransitivity; [| exact EWB]; reflexivity)) as [IR5 IFF5].
      split; [split; [exact IR5| split; [change (is_mode (sGf sE)) with TYPE; unfold HEAD, TYPE, SYNC; lia| exact IRG]]|].
      split; [exact (izs_of_ZSC _ _ _ _ ZC5)| exact IFF5].
    - destruct (syG_err R4 m2 sE lenf gotf SCE KPE ZCE SVE EF EW F10 X9 X2 F12 F13 F11 X1 ltac:(lia) ltac:(lia) G4 ltac:(lia)) as (R5 & m5 & MS5 & Z10 & Z2 & Hfr5 & RST5 & SC5 & KP5 & ZC5).
      rk_step FR Hfr5.
      try rewrite (proj2 (Z.eqb_neq gotf 4) G4).
      exists R5, m5. cbn [fst snd zr_rc zr_output zr_consumed zr_strm].
      split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS4| exact MS5]]]|].
      split; [exact (frame_of_KEEP m5 KP5)|]. split; [exact Z10|]. split; [first [exact Z2| rewrite Z2; reflexivity]|]. split; [exact (rkeep_final R5 RST5 FR)|].
      split; [reflexivity|]. split; [lia|].
      destruct (ISREP6_of m5 (iset_have sE gotf) SC5 KP5 ltac:(etransitivity; [| exact EL]; reflexivity) ltac:(etransitivity; [| exact EWK]; reflexivity)
                  ltac:(etransitivity; [| exact EC]; reflexivity) ltac:(etransitivity; [| exact EWI]; reflexivity) ltac:(etransitivity; [| exact EWB]; reflexivity)) as [IR5 IFF5].
      split; [split; [exact IR5| split; [change (is_mode (iset_have sE gotf)) with (is_mode sE); unfold HEAD, SYNC in *; lia| exact IRG]]|].
      split; [exact (izs_of_ZSC _ _ _ _ ZC5)| exact IFF5].
  Qed.
End SYNCU.

(* 1.4 (a worker, statement from a worker's FlLibStmtU fl_isy): inflateSync's stack use is 96 bytes, its 64-byte
   frame plus inflateReset's 32-byte frame below it, which 1.4 calls (1.3.1: 16, inflateReset inlined) *)
Corollary inflateSync_fl_isyU : forall (MA : Z -> Z), MA MSG_NULL = 0 ->
  forall (regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (s : inflate_state) (zc : ZCall) (sp ra inp outp zcl fa ff : Z),
    let p := ip_p q in let strm := ip_strm q in
    let s' := fst (inflateSync_m ivar_ref s zc) in let r := snd (inflateSync_m ivar_ref s zc) in
    getr regs 10 = Z_to_bv 64 strm -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = Z_to_bv 64 ra ->
    ra_ok ra -> sp mod 16 = 0 -> zcl + FL_FRA <= sp -> sp <= 2 ^ 47 -> FL_IMG_TOP <= zcl ->
    blocks_ok mem zcl (iblocks q) -> img_clear mem -> 0 < strm -> strm + 112 <= 2 ^ 63 -> strm mod 8 = 0 -> 0 < inp ->
    store_ok s6u_segs mem (Z_to_bv 64 (sp - 96)) 96%nat = true -> store_ok s6u_segs mem (Z_to_bv 64 strm) 112%nat = true ->
    all_apart ((sp - 96, 96) :: (strm, 112) :: (inp, zlength (zc_input zc)) :: iblocks q) ->
    (forall a n, In (a, n) [(sp - 96, 96); (strm, 112); (inp, zlength (zc_input zc))] -> a + n <= FL_RO_LO \/ FL_IMG_TOP <= a) ->
    inp + zlength (zc_input zc) < 2 ^ 63 -> zlength (zc_input zc) < 2 ^ 32 ->
    (ISREP6 mem (ip_p q) (ip_strm q) (ip_w q) s /\ HEAD <= is_mode s <= SYNC /\
     (0 <= ip_p q /\ ip_p q + FL_ISTATE_N <= 2 ^ 63 /\ 0 <= ip_w q /\ ip_w q + FL_WIN_N <= 2 ^ 63)) ->
    holds s6u_segs mem inp (zc_input zc) ->
    izs_cells MA mem strm inp (zlength (zc_input zc)) outp (zc_avail_out zc) (zc_strm zc) p fa ff -> fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    SSAFE6 s zc ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps s6u_segs (mkst regs (Z_to_bv 64 FL_A_ISY) mem (seg_rom s6u_segs)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom s6u_segs))
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - 96), 96) :: (Z_to_bv 64 strm, 112) :: wz (iblocks q))
      /\ getr regs' 10 = Z_to_bv 64 (zr_rc r) /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep regs regs' FL_KEEP
      /\ zr_output r = [] /\ 0 <= zr_consumed r <= zlength (zc_input zc)
      /\ (ISREP6 mem' (ip_p q) (ip_strm q) (ip_w q) s' /\ HEAD <= is_mode s' <= SYNC /\
          (0 <= ip_p q /\ ip_p q + FL_ISTATE_N <= 2 ^ 63 /\ 0 <= ip_w q /\ ip_w q + FL_WIN_N <= 2 ^ 63))
      /\ izs_cells MA mem' strm (inp + zr_consumed r) (zlength (zc_input zc) - zr_consumed r) outp (zc_avail_out zc) (zr_strm r) p fa ff
      /\ (ip_w q = 0 <-> is_window_blk s' = None).
Proof using.
  intros MA MA0 regs mem [strm p w] s zc sp ra inp outp zcl fa ff. cbn [ip_p ip_strm ip_w].
  intros G10 G2 G1 RA SP16 HZC SP47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 (IR & MRNG & IRG) HLD ZS FA FF SAFE.
  pose proof (inflateSync_run6u regs mem p strm w s zc sp ra inp outp zcl fa ff MA) as T. cbv zeta in T |- *.
  apply T; assumption.
Qed.
End FXG.
