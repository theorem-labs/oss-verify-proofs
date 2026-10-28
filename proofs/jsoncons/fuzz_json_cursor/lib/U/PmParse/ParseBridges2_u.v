(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmCurDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSpecs_u ParseBridges_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PB2.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Definition ls_foot (a : Z) : Prop :=
  0x10000 <= a < PML.IMG_RO_HI \/ 0xd5228 <= a < 0xd5231 \/ a = 0xd5030 \/ 0xd4df8 <= a < 0xd4dfa \/ 0xd4df0 <= a < 0xd4df2 \/ 0xf6848 <= a < 0xf6848 + 544
  \/ a = 0xf6a93 \/ 0xf6b68 <= a < 0xf6b6c.
Section FrameK.
Variables (M M' : mem).
Hypothesis FRK : forall a, ls_foot a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Lemma agree_k : forall a n, (forall i, a <= i < a + n -> ls_foot i) -> L5C.agree_on M M' a n.
Proof. intros a n H i Hi. apply FRK. apply H. exact Hi. Qed.
Lemma ls_ok_keep : forall g, g <> PML.LS0 -> PML.ls_ok g M -> PML.ls_ok g M'.
Proof.
  intros g Hg (IR & H).
  assert (U8 : forall a v, ls_foot a -> 0 <= a -> a + 1 <= 2 ^ 64 -> PML.u8 M a v -> PML.u8 M' a v).
  { intros a v Hf A0 A1 Hu. apply (L5C.u8_at_agree RSEGS M M' a v); [apply agree_k; intros i Hi; replace i with a by lia; exact Hf | exact A0 | exact A1 | exact Hu]. }
  assert (U64 : forall a v, (forall i, a <= i < a + 8 -> ls_foot i) -> 0 <= a -> a + 8 <= 2 ^ 64 -> PML.u64 M a v -> PML.u64 M' a v).
  { intros a v Hf A0 A1 Hu. apply (L5C.u64_at_agree RSEGS M M' a v); [apply agree_k; exact Hf | exact A0 | exact A1 | exact Hu]. }
  assert (U32 : forall a v, (forall i, a <= i < a + 4 -> ls_foot i) -> 0 <= a -> a + 4 <= 2 ^ 64 -> PML.u32 M a v -> PML.u32 M' a v).
  { intros a v Hf A0 A1 Hu. unfold PML.u32, L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4%nat a A0 ltac:(cbn; lia)); [exact Hu|]. apply agree_k. intros i Hi. apply Hf. cbn in Hi. lia. }
  destruct H as ((Q1 & Q2) & H).
  split; [|split].
  - intros i Hi. rewrite FRK; [apply IR; exact Hi | left; exact Hi].
  - unfold PML.libc_quiet, PML.NEED_LOCKS, PML.LOCALE_LOCK in *. split; [apply U8; [unfold ls_foot; lia | lia | lia | exact Q1] | apply U32; [intros i Hi; unfold ls_foot; lia | lia | lia | exact Q2]].
  - assert (LD : PML.loc_done M -> PML.loc_done M').
    { intros (X & Y & Z). split; [apply U8; [unfold ls_foot; lia | lia | lia | exact X]|].
      split; [apply U64; [intros i Hi; unfold ls_foot; lia | lia | lia | exact Y] | apply U8; [unfold ls_foot; lia | lia | lia | exact Z]]. }
    assert (EG : forall b, PML.errcat_guard M b -> PML.errcat_guard M' b).
    { intros b (X & Y). split; apply U8; try (unfold ls_foot; lia); try lia; assumption. }
    assert (CG : forall b, PML.convcat_guard M b -> PML.convcat_guard M' b).
    { intros b (X & Y). split; apply U8; try (unfold ls_foot; lia); try lia; assumption. }
    assert (AC : forall hs, PML.atexit_cells M hs -> PML.atexit_cells M' hs).
    { intros hs. apply PML.atexit_cells_agree. intros a Ha. apply FRK. unfold ls_foot, PML.AX in *. lia. }
    destruct g; [exfalso; apply Hg; reflexivity | ..]; destruct H as (X & Y & Z & W);
      (split; [apply LD; exact X | split; [apply EG; exact Y | split; [apply CG; exact Z | apply AC; exact W]]]).
Qed.
End FrameK.

Section Frame.
Variables (F : list L5.range) (M M' : mem).
Hypothesis FR : L5.frame_but F M M'.
Hypothesis GR : mem_grows M M'.
Definition out (a n : Z) : Prop := 0 <= a /\ a + n <= 2 ^ 64 /\ forall i, a <= i < a + n -> L5.outside F i.
Lemma out_sub : forall a n a' n', out a n -> a <= a' -> a' + n' <= a + n -> out a' n'.
Proof. intros a n a' n' (H0 & H1 & H2) Ha Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H2. lia. Qed.
Lemma u64_fr : forall a v, out a 8 -> PML.u64 M a v -> PML.u64 M' a v.
Proof. intros a v (H0 & H1 & H2) H. exact (L5.u64_at_frame RSEGS M M' F a v FR H0 H1 H2 H). Qed.
Lemma u8_fr : forall a v, out a 1 -> PML.u8 M a v -> PML.u8 M' a v.
Proof. intros a v (H0 & H1 & H2) H. apply (L5.u8_at_frame RSEGS M M' F a v FR H0 H1); [apply H2; lia | exact H]. Qed.
Lemma u32_fr : forall a v, out a 4 -> PML.u32 M a v -> PML.u32 M' a v.
Proof.
  intros a v (H0 & H1 & H2) H. unfold PML.u32, L5.u32_at in *. rewrite (L5.rdn_frame RSEGS M M' F FR 4%nat a H0 ltac:(cbn; lia)); [exact H|].
  intros i Hi. apply H2. cbn in Hi. lia.
Qed.
Lemma bytes_fr : forall p bs, out p (Z.of_nat (length bs)) -> L5.bytes_at RSEGS M p bs -> L5.bytes_at RSEGS M' p bs.
Proof. intros p bs Ho H i Hi. apply u8_fr; [apply (out_sub _ _ _ _ Ho); lia | exact (H i Hi)]. Qed.
Lemma def_fr : forall a n, L5.defined M a n -> L5.defined M' a n.
Proof. intros a n H. exact (L5.defined_grows M M' a n GR H). Qed.
Lemma lstr_short_nil_fr : forall o, out o 24 -> L5.lstr_short RSEGS M o [] -> L5.lstr_short RSEGS M' o [].
Proof.
  intros o Ho (H1 & H2 & H3 & H4). cbn [length] in *. split; [exact H1|]. split; [apply u8_fr; [apply (out_sub _ _ _ _ Ho); lia | exact H2]|].
  split; [intros i Hi; cbn in Hi; lia|]. apply u8_fr; [apply (out_sub _ _ _ _ Ho); cbn; lia | exact H4].
Qed.
Lemma str_long_fr : forall o cap p s, out o 24 -> out p cap -> PML.str_at M o (PML.SLong cap p s) -> PML.str_at M' o (PML.SLong cap p s).
Proof.
  intros o cap p s Ho Hp ((B & W0 & W8 & W16 & BS & NUL) & C8 & LT). split; [|split; assumption].
  split; [exact B|]. split; [apply u64_fr; [apply (out_sub _ _ _ _ Ho); lia | exact W0]|]. split; [apply u64_fr; [apply (out_sub _ _ _ _ Ho); lia | exact W8]|].
  split; [apply u64_fr; [apply (out_sub _ _ _ _ Ho); lia | exact W16]|].
  split; [apply bytes_fr; [apply (out_sub _ _ _ _ Hp); lia | exact BS] | apply u8_fr; [apply (out_sub _ _ _ _ Hp); lia | exact NUL]].
Qed.
Lemma parser_at_fr : forall P ps, out P 272 -> out (PML.ps_bptr ps) (PML.ps_bcap ps) -> out (PML.ps_sb ps) (PML.ps_scap ps) ->
  PML.parser_at M P ps -> PML.parser_at M' P ps.
Proof.
  intros P ps HP HB HS H. unfold PML.parser_at in *.
  destruct H as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30).
  assert (O8 : forall k, 0 <= k -> k + 8 <= 272 -> out (P + k) 8) by (intros k K0 K1; apply (out_sub _ _ _ _ HP); lia).
  assert (O4 : forall k, 0 <= k -> k + 4 <= 272 -> out (P + k) 4) by (intros k K0 K1; apply (out_sub _ _ _ _ HP); lia).
  assert (O1 : forall k, 0 <= k -> k + 1 <= 272 -> out (P + k) 1) by (intros k K0 K1; apply (out_sub _ _ _ _ HP); lia).
  assert (O24 : forall k, 0 <= k -> k + 24 <= 272 -> out (P + k) 24) by (intros k K0 K1; apply (out_sub _ _ _ _ HP); lia).
  split; [apply u64_fr; [replace P with (P + 0) by lia; apply O8; lia | exact A0]|].
  split; [apply u32_fr; [apply O4; lia | exact A1]|].
  split; [apply u8_fr; [apply O1; lia | exact A2]|]. split; [apply u8_fr; [apply O1; lia | exact A3]|]. split; [apply u8_fr; [apply O1; lia | exact A4]|].
  split; [apply u8_fr; [apply O1; lia | exact A5]|]. split; [apply u8_fr; [apply O1; lia | exact A6]|]. split; [apply u8_fr; [apply O1; lia | exact A7]|].
  split; [apply u8_fr; [apply O1; lia | exact A8]|].
  split; [apply lstr_short_nil_fr; [apply O24; lia | exact A9]|]. split; [apply lstr_short_nil_fr; [apply O24; lia | exact A10]|]. split; [apply lstr_short_nil_fr; [apply O24; lia | exact A11]|].
  split; [apply u64_fr; [apply O8; lia | exact A12]|]. split; [apply u64_fr; [apply O8; lia | exact A13]|].
  split; [apply u32_fr; [apply O4; lia | exact A14]|].
  split; [destruct (PML.ps_win ps) as [[p e]|]; [destruct A15 as (X & Y & Z); split; [apply u64_fr; [apply O8; lia | exact X] | split; [apply u64_fr; [apply O8; lia | exact Y] | exact Z]]
                                                 | destruct A15 as (X & Y); split; apply u64_fr; try (apply O8; lia); assumption]|].
  split; [apply u8_fr; [apply O1; lia | exact A16]|]. split; [apply u8_fr; [apply O1; lia | exact A17]|]. split; [apply u8_fr; [apply O1; lia | exact A18]|].
  split; [apply u8_fr; [apply O1; lia | exact A19]|]. split; [apply u8_fr; [apply O1; lia | exact A20]|]. split; [apply u8_fr; [apply O1; lia | exact A21]|].
  split; [apply u32_fr; [apply O4; lia | exact A22]|].
  split; [apply str_long_fr; [apply O24; lia | exact HB | exact A23]|]. split; [exact A24|].
  split; [apply u64_fr; [apply O8; lia | exact A25]|]. split; [apply u64_fr; [apply O8; lia | exact A26]|]. split; [apply u64_fr; [apply O8; lia | exact A27]|].
  split; [apply bytes_fr; [apply (out_sub _ _ _ _ HS); lia | exact A28]|]. split; [exact A29|]. apply def_fr. exact A30.
Qed.
Lemma ec_at_fr : forall E code, out E 16 -> PML.ec_at M E code -> PML.ec_at M' E code.
Proof.
  intros E code HE (A & B & C). split; [apply u32_fr; [apply (out_sub _ _ _ _ HE); lia | exact A]|]. split; [apply def_fr; exact B|].
  destruct C as [C|[C1 C2]]; [left; exact C | right; split; [exact C1 | apply u64_fr; [apply (out_sub _ _ _ _ HE); lia | exact C2]]].
Qed.
Lemma win_ok_fr : forall LBo ps, PML.win_ok M LBo ps -> PML.win_ok M' LBo ps.
Proof. intros LBo ps H. unfold PML.win_ok in *. destruct (PML.ps_win ps) as [[p e]|]; [|exact I]. destruct H as (ch & A & B & C & D). exists ch. repeat split; try assumption. apply def_fr. exact D. Qed.

Lemma ls_ok_fr : forall g, g <> PML.LS0 -> out 0x10000 (0xf6b6c - 0x10000) -> PML.ls_ok g M -> PML.ls_ok g M'.
Proof.
  intros g Hg (_ & _ & HO) H. apply (ls_ok_keep M M'); [|exact Hg | exact H].
  intros a Ha. apply FR. unfold ls_foot, PML.IMG_RO_HI in Ha. rewrite L5.unsigned_lit by lia. apply HO. lia.
Qed.
End Frame.

Lemma kword8_elim : forall E (M : mem) a v A, kentry_ok RSEGS E M (KWord a 1 v) -> estart E a = A -> L5.u8_at RSEGS M A (uv E v).
Proof.
  intros E M a v A (_ & Hfl & Hr) Ha. unfold L5.u8_at. rewrite <- Ha, <- (CL5.adenot_start E a _ Hfl), Hr. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. reflexivity.
Qed.
Lemma kword32_elim : forall E (M : mem) a v A, kentry_ok RSEGS E M (KWord a 4 v) -> estart E a = A -> L5.u32_at RSEGS M A (uv E v).
Proof.
  intros E M a v A (_ & Hfl & Hr) Ha. unfold L5.u32_at. rewrite <- Ha, <- (CL5.adenot_start E a _ Hfl), Hr. unfold PB.uv. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma kword64_elim : forall E (M : mem) a v A, kentry_ok RSEGS E M (KWord a 8 v) -> estart E a = A -> L5.u64_at RSEGS M A (uv E v).
Proof. intros E M a v A H Ha. exact (CL5.kword64_elim RSEGS E M a v A (uv E v) H Ha eq_refl). Qed.
Lemma kword8_intro : forall E (M : mem) a v A z, estart E a = A -> 0 <= A -> A + 1 <= 2 ^ 64 -> edenot E v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  L5.u8_at RSEGS M A z -> kentry_ok RSEGS E M (KWord a 1 v).
Proof.
  intros E M a v A z Ha H0 H1 Hv Hz Hu. cbn [kentry_ok]. assert (Hfl : flat E a (Z.of_nat 1)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha, Hv. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. rewrite u64_of_Z by exact Hz. exact Hu.
Qed.

Lemma cell_exists : forall (M : mem) a (n : nat), (n <= 8)%nat -> L5.defined M a (Z.of_nat n) ->
  exists v, 0 <= v < 2 ^ 64 /\ rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof.
  intros M a n Hn Hd.
  assert (RD : forall (k : nat) b, (forall i, 0 <= i < Z.of_nat k -> M (Z_to_bv 64 (b + i)) <> None) -> exists bs, rdn RSEGS M (Z_to_bv 64 b) k = Some bs /\ length bs = k).
  { induction k as [|k IH]; intros b H; [exists []; split; reflexivity|].
    destruct (IH (b + 1)) as (bs & Hr & Hl); [intros i Hi; replace (b + 1 + i) with (b + (1 + i)) by lia; apply H; lia|].
    pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 b)) as [x|] eqn:Hb; [|contradiction].
    exists (x :: bs). cbn [rdn]. rewrite Hb, L5C.add1_lit, Hr. split; [reflexivity | cbn [length]; lia]. }
  destruct (RD n a Hd) as (bs & Hr & Hl). exists (bytes_le_to_Z bs).
  pose proof (bytes_le_to_Z_nonneg bs) as N0. pose proof (bytes_le_to_Z_bound bs) as N1. rewrite Hl in N1.
  assert (Hle : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  split; [lia|]. rewrite Hr. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; assumption.
Qed.
Lemma uv_lit : forall E z, 0 <= z < 2 ^ 64 -> uv E (ELit z) = z.
Proof. intros E z Hz. unfold PB.uv. cbn [edenot]. apply u64_of_Z. exact Hz. Qed.

Record pvals : Type := PV { pv_level : expr; pv_wend : expr; pv_wptr : expr; pv_st : expr; pv_sst : expr; pv_nst : expr; pv_more : expr; pv_done : expr; pv_size : expr }.
Definition hasw (cells : list kentry) (b : expr) (k : Z) (w : nat) (v : expr) : bool := PB.has cells (KWord (SA b k) w v).
Definition pconst_chk (cells : list kentry) (Pb : expr) : bool :=
  (hasw cells Pb 0 8 (ELit PML.VT_PARSER) && hasw cells Pb 8 4 (ELit 1024)
   && hasw cells Pb 12 1 (ELit 0) && hasw cells Pb 13 1 (ELit 1) && hasw cells Pb 14 1 (ELit 0) && hasw cells Pb 15 1 (ELit 1)
   && hasw cells Pb 16 1 (ELit 0) && hasw cells Pb 17 1 (ELit 0) && hasw cells Pb 18 1 (ELit 0)
   && hasw cells Pb 24 1 (ELit 0) && hasw cells Pb 25 1 (ELit 0) && hasw cells Pb 48 1 (ELit 0) && hasw cells Pb 49 1 (ELit 0) && hasw cells Pb 72 1 (ELit 0) && hasw cells Pb 73 1 (ELit 0)
   && hasw cells Pb 96 8 (ELit PML.VT_FUNC) && hasw cells Pb 128 8 (APC.eaddz Pb 96) && hasw cells Pb 213 1 (ELit 1) && hasw cells Pb 216 4 (ELit 0))%bool.
Definition pview (cells : list kentry) (Pb pe ce SB SLEN SCAP : expr) : option pvals :=
  match CAX.cell_at cells Pb 144 4, CAX.cell_at cells Pb 192 8, CAX.cell_at cells Pb 200 8, CAX.cell_at cells Pb 208 1, CAX.cell_at cells Pb 209 1,
        CAX.cell_at cells Pb 210 1, CAX.cell_at cells Pb 211 1, CAX.cell_at cells Pb 212 1, CAX.cell_at cells Pb 232 8 with
  | Some lvl, Some wend, Some wptr, Some st, Some sst, Some nst, Some more, Some done, Some se =>
      if (pconst_chk cells Pb && PB.str_pat cells Pb 224 pe ce se 264 67108864
          && hasw cells Pb 248 8 SB && hasw cells Pb 256 8 (APC.eadd SB SLEN) && hasw cells Pb 264 8 (APC.eadd SB SCAP)
          && PB.has cells (KBlob (SA SB 0) SLEN 0))%bool
      then Some (PV lvl wend wptr st sst nst more done se) else None
  | _, _, _, _, _, _, _, _, _ => None
  end.

Lemma cell_at_ok : forall E (M : mem) cells b k w v, know_ok RSEGS E M cells -> CAX.cell_at cells b k w = Some v -> kentry_ok RSEGS E M (KWord (SA b k) w v).
Proof.
  intros E M cells b k w v HK H. destruct (PB.cell_at_has _ _ _ _ _ H) as (b' & Hin & ->). exact (proj1 (Forall_forall _ _) HK _ Hin).
Qed.

Lemma parser_view : forall E (M : mem) cells Pb pe ce SB SLEN SCAP pv P (bm bd : bool) (stack : list Z),
  know_ok RSEGS E M cells -> pview cells Pb pe ce SB SLEN SCAP = Some pv ->
  uv E Pb = P -> 2 ^ 32 <= P -> P + 272 <= 2 ^ 63 ->
  uv E (pv_more pv) = PML.b2z bm -> uv E (pv_done pv) = PML.b2z bd ->
  eb E 0 = map (Z_to_bv 8) stack -> uv E SB + uv E SLEN < 2 ^ 64 -> uv E SB + uv E SCAP < 2 ^ 64 -> uv E SLEN <= uv E SCAP ->
  uv E (pv_wptr pv) <= uv E (pv_wend pv) ->
  L5.defined M P 272 ->
  exists buf : list Z,
    PML.parser_at M P (PML.PS (uv E (pv_st pv)) (uv E (pv_sst pv)) (uv E (pv_nst pv)) bm bd (uv E (pv_level pv)) stack (uv E SB) (uv E SCAP) (uv E ce) (uv E pe) buf
                              (Some (uv E (pv_wptr pv), uv E (pv_wend pv))))
    /\ Z.of_nat (length buf) = uv E (pv_size pv) /\ 264 <= uv E ce <= 2 ^ 27 /\ uv E ce mod 8 = 0 /\ 4096 <= uv E pe <= 2 ^ 47 /\ L5.defined M (uv E pe) (uv E ce)
    /\ Z.of_nat (length stack) = uv E SLEN.
Proof.
  intros E M cells Pb pe ce SB SLEN SCAP pv P bm bd stack HK HV HP P0 P1 Hm Hd Hst HS1 HS2 HS3 Hwin Hdef.
  unfold pview in HV.
  destruct (CAX.cell_at cells Pb 144 4) as [lvl|] eqn:C144; [|discriminate]. destruct (CAX.cell_at cells Pb 192 8) as [wend|] eqn:C192; [|discriminate].
  destruct (CAX.cell_at cells Pb 200 8) as [wptr|] eqn:C200; [|discriminate]. destruct (CAX.cell_at cells Pb 208 1) as [st|] eqn:C208; [|discriminate].
  destruct (CAX.cell_at cells Pb 209 1) as [sst|] eqn:C209; [|discriminate]. destruct (CAX.cell_at cells Pb 210 1) as [nst|] eqn:C210; [|discriminate].
  destruct (CAX.cell_at cells Pb 211 1) as [more|] eqn:C211; [|discriminate]. destruct (CAX.cell_at cells Pb 212 1) as [done|] eqn:C212; [|discriminate].
  destruct (CAX.cell_at cells Pb 232 8) as [se|] eqn:C232; [|discriminate].
  lazymatch type of HV with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection HV as <-. cbn [pv_level pv_wend pv_wptr pv_st pv_sst pv_nst pv_more pv_done pv_size] in *.
  apply andb_prop in Hb as [Hb B6]. apply andb_prop in Hb as [Hb B5]. apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2].
  assert (ES : forall k, estart E (SA Pb k) = P + k) by (intros k; unfold estart; cbn [a_base a_off]; fold (uv E Pb); rewrite HP; reflexivity).
  destruct (PB.str_view E M cells Pb 224 pe ce se 264 67108864 HK B2 ltac:(lia) ltac:(rewrite ES; lia) ltac:(rewrite ES; lia)) as (buf & Hstr & Hlen & Hcap & Hlt & Hsm & Hc8 & Hpr & Hpdef).
  rewrite ES in Hstr.
  exists buf. split; [|repeat split; try lia; try assumption].
  2: { destruct (CL5.kblob_elim RSEGS E M _ _ _ (uv E SB) stack (PB.has_ok E M _ _ HK B6)) as [_ HL]; [unfold estart; cbn [a_base a_off]; fold (uv E SB); lia | exact Hst |].
       unfold elenZ in HL. fold (uv E SLEN) in HL. lia. }
  unfold pconst_chk, hasw in B1.
  repeat (let X := fresh "K" in apply andb_prop in B1 as [B1 X]; apply (PB.has_ok E M _ _ HK) in X).
  apply (PB.has_ok E M _ _ HK) in B1.
  pose proof (fun k w v (H : kentry_ok RSEGS E M (KWord (SA Pb k) w v)) => H) as _.
  assert (U8 : forall k v z, kentry_ok RSEGS E M (KWord (SA Pb k) 1 v) -> uv E v = z -> PML.u8 M (P + k) z).
  { intros k v z H <-. apply (kword8_elim E M _ _ _ H). apply ES. }
  assert (U32 : forall k v z, kentry_ok RSEGS E M (KWord (SA Pb k) 4 v) -> uv E v = z -> PML.u32 M (P + k) z).
  { intros k v z H <-. apply (kword32_elim E M _ _ _ H). apply ES. }
  assert (U64 : forall k v z, kentry_ok RSEGS E M (KWord (SA Pb k) 8 v) -> uv E v = z -> PML.u64 M (P + k) z).
  { intros k v z H <-. apply (kword64_elim E M _ _ _ H). apply ES. }
  assert (LIT : forall z, 0 <= z < 2 ^ 64 -> uv E (ELit z) = z) by (intros; apply uv_lit; assumption).
  assert (SHORT : forall k, kentry_ok RSEGS E M (KWord (SA Pb k) 1 (ELit 0)) -> kentry_ok RSEGS E M (KWord (SA Pb (k + 1)) 1 (ELit 0)) -> L5.lstr_short RSEGS M (P + k) []).
  { intros k H1 H2. split; [cbn; lia|]. cbn [length]. split; [exact (U8 k _ 0 H1 (LIT 0 ltac:(lia)))|]. split; [intros i Hi; cbn in Hi; lia|].
    replace (P + k + 1 + Z.of_nat 0) with (P + (k + 1)) by lia. exact (U8 (k + 1) _ 0 H2 (LIT 0 ltac:(lia))). }
  pose proof (cell_at_ok E M _ _ _ _ _ HK C144) as D144. pose proof (cell_at_ok E M _ _ _ _ _ HK C192) as D192. pose proof (cell_at_ok E M _ _ _ _ _ HK C200) as D200.
  pose proof (cell_at_ok E M _ _ _ _ _ HK C208) as D208. pose proof (cell_at_ok E M _ _ _ _ _ HK C209) as D209. pose proof (cell_at_ok E M _ _ _ _ _ HK C210) as D210.
  pose proof (cell_at_ok E M _ _ _ _ _ HK C211) as D211. pose proof (cell_at_ok E M _ _ _ _ _ HK C212) as D212.
  apply (PB.has_ok E M _ _ HK) in B3, B4, B5.
  unfold PML.parser_at. cbn [PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win].
  split; [replace P with (P + 0) by lia; apply (U64 0 _ _ B1); apply LIT; unfold PML.VT_PARSER; lia|].
  split; [apply (U32 8 _ _ K16); apply LIT; lia|].
  split; [apply (U8 12 _ _ K15); apply LIT; lia|]. split; [apply (U8 13 _ _ K14); apply LIT; lia|]. split; [apply (U8 14 _ _ K13); apply LIT; lia|].
  split; [apply (U8 15 _ _ K12); apply LIT; lia|]. split; [apply (U8 16 _ _ K11); apply LIT; lia|]. split; [apply (U8 17 _ _ K10); apply LIT; lia|].
  split; [apply (U8 18 _ _ K9); apply LIT; lia|].
  split; [exact (SHORT 24 K8 K7)|]. split; [exact (SHORT 48 K6 K5)|]. split; [exact (SHORT 72 K4 K3)|].
  split; [apply (U64 96 _ _ K2); apply LIT; unfold PML.VT_FUNC; lia|].
  split; [apply (U64 128 _ _ K1); rewrite PB.uv_eaddz, HP; apply Z.mod_small; lia|].
  split; [exact (U32 144 _ _ D144 eq_refl)|].
  split; [split; [exact (U64 200 _ _ D200 eq_refl) | split; [exact (U64 192 _ _ D192 eq_refl) | exact Hwin]]|].
  split; [exact (U8 208 _ _ D208 eq_refl)|]. split; [exact (U8 209 _ _ D209 eq_refl)|]. split; [exact (U8 210 _ _ D210 eq_refl)|].
  split; [exact (U8 211 _ _ D211 Hm)|]. split; [exact (U8 212 _ _ D212 Hd)|].
  split; [apply (U8 213 _ _ K0); apply LIT; lia|]. split; [apply (U32 216 _ _ K); apply LIT; lia|].
  split; [exact Hstr|]. split; [lia|].
  split; [exact (U64 248 _ _ B3 eq_refl)|].
  destruct (CL5.kblob_elim RSEGS E M _ _ _ (uv E SB) stack (PB.has_ok E M _ _ HK B6)) as [HBS HL]; [unfold estart; cbn [a_base a_off]; fold (uv E SB); lia | exact Hst |].
  unfold elenZ in HL. fold (uv E SLEN) in HL.
  split; [apply (U64 256 _ _ B4); rewrite PB.uv_eadd, HL; apply Z.mod_small; pose proof (PB.uv_range E SB); lia|].
  split; [apply (U64 264 _ _ B5); rewrite PB.uv_eadd; apply Z.mod_small; pose proof (PB.uv_range E SB); pose proof (PB.uv_range E SCAP); lia|].
  split; [exact HBS|]. split; [lia | exact Hdef].
Qed.

Section Inst2.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable LBrest : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
Variable Cred : nat -> env -> credit -> Prop.
Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L LBrest sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Variable XI : nat -> env -> mem -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - CH.hd_scr d) (CH.hd_scr d).

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.
Abbreviation AMB3 := (CH2.amb3 L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred XI).
Abbreviation HAMB := (CH2.heap_amb L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).
Variables KXf BXf : list (Z * Z) -> Z.
Hypothesis CRED_EQ : forall i E cr, Cred i E cr <-> PPS.bufcred L cr (PB.cap_of BLS i E) (KXf (PB.tl_of BLS i E)) (BXf (PB.tl_of BLS i E)).

Variable EB : expr.
Variable EK : Z.
Hypothesis EB_frozen : APC.expr_vars_lt NF EB = true.
Variable eaddr : Z.
Hypothesis EADDR : estart E0 (SA EB EK) = eaddr.
Hypothesis EOBJ : sp0 <= eaddr /\ eaddr + 16 <= hl_sptop L /\ eaddr mod 8 = 0.
Hypothesis EDEF0 : L5.defined M0 eaddr 16.
Definition SETEC_W : list L5.range := [(eaddr, 16); (0xd4df8, 2); (0xf6848, 544)].
Hypothesis SETEC_W_in : forall w a, In w SETEC_W -> L5.in_rng w a -> exists w', In w' W /\ L5.in_rng w' a.
Hypothesis SETEC : PMS.set_ec_spec L.
Variable g0 : PML.ls_state.
Hypothesis G0 : g0 <> PML.LS0.

Definition SETEC_SCR : Z := 256.
Definition setec_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  match split_lit (nth 10 regs (ELit 0)), nth 11 regs (ELit 0) with
  | (eb, ek), ELit code =>
      if (expr_eqb eb EB && Z.eqb ek EK && Z.leb 1 code && Z.leb code 31 && CH2.blocks_eqb BLj BLi)%bool
      then CH2.custom_chk NF d SETEC_SCR 0 BLi ((eb, ek, ELit 16) :: PSU.statics_wregs) (PSU.setec_news eb ek (ELit code)) (Some (nth 10 regs (ELit 0))) c ps cj BLi
      else None
  | _, _ => None
  end.

Lemma setec_leaf_ok : forall i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther PML.PC_SET_EC) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = PML.PC_SET_EC ->
  setec_chk c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E E' R' (M M' : mem) model, env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> HAMB i E M' model -> XI i E M -> PML.ls_ok g0 M') ->
  (forall E2 (M2 : mem), PML.ls_ok (PML.regJ g0) M2 -> XI j E2 M2) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros i c k ps j cj ci IL Hret Hcj Hpc Hchk XPRE XPOST fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0.
  unfold setec_chk in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [eb ek] eqn:Hsplit.
  destruct (nth 11 (CA.ps_reglist ps) (ELit 0)) as [code| | | | | | |] eqn:Hcode; try discriminate.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B5]. apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2].
  apply expr_eqb_eq in B1. apply Z.eqb_eq in B2. apply Z.leb_le in B3, B4. apply CH2.blocks_eqb_eq in B5. subst eb ek.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              SETEC_SCR 0%nat (nth i BLS []) _ _ _ i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  set (nx := CH2.ci_nx ci) in *.
  pose proof HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  assert (Ho : estart E' (SA EB EK) = eaddr) by (rewrite (PB.estart_agree NF E0 E' EB EK HagE' EB_frozen); exact EADDR).
  destruct EOBJ as (O1 & O2 & O3). pose proof STK as (S1 & S2 & S3 & S4 & S5).
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO. pose proof LYI as [LI1 LI2]. pose proof LYE as [LE1 LE2].
  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 eaddr).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplit). f_equal. exact Ho. }
  assert (Ga1 : getr R' 11%bv = Z_to_bv 64 code).
  { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq, Hcode. reflexivity. }
  assert (HLS : PML.ls_ok g0 M') by exact (XPRE E E' R' M M' model Hag HLF HA' HXI0).
  assert (HDE : L5.defined M' eaddr 16).
  { intros q Hq. apply (Hdf (eaddr + q)); [lia | | apply EDEF0; exact Hq]. split; [right; left; split; lia | unfold in_errno; lia]. }
  rewrite Hpc, LS. destruct Hmo as (Hm1 & Hm2 & Hm3).
  apply (SETEC eaddr code (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) g0 fx' R' M' model K Hm1 Hm2 K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]|].
    split; [exact Ga0|]. split; [exact Ga1|]. split; [lia|]. split; [exact HDE|]. split; [unfold PML.obj_on_stack; lia|]. split; [exact HLS | exact G0]. }
  intros fx2 R2 M2 HFP2 (Hec & Hls2 & Ha0') HRP HFB HGR.
  set (LBk := CH2.den E' (nth i BLS []) ++ LBrest).
  assert (HHk : hi_heap HI LBk cr M' (m_vmmaps model)) by (unfold LBk; rewrite Hden; exact HH).
  pose proof (proj1 (hio_wf L SCFG HI HIok _ _ _ _ HHk)) as Hwf.
  assert (OUTF : forall a, 0 <= a < 2 ^ 64 -> L5.outside SETEC_W a -> ~ (sp0 + CH2.ci_csp ci - SETEC_SCR <= a < sp0 + CH2.ci_csp ci) -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha Hout Hns. apply HFB. rewrite L5.unsigned_lit by exact Ha. intros r [<-|Hr]; [unfold L5.in_rng; cbn [fst snd]; unfold PMS.SETEC_SCR, SETEC_SCR in *; lia | exact (Hout r Hr)]. }
  assert (HPRES : L5C.hpres L LBk (sp0 + CH2.ci_csp ci) SETEC_SCR SETEC_W M' M2).
  { apply L5C.hpres_intro.
    - intros a (K1 & K2 & K3 & K4). apply (OUTF a K1 K4). destruct K2 as [(b & Hb & Hin)|[[C1 C2]|[C1 C2]]]; [|exact C2 | lia].
      destruct (Hwf b Hb) as ((R0 & R1 & R2' & R3 & R4) & _). unfold SETEC_SCR in *. lia.
    - intros q Hq. apply HGR. destruct Hstk as (_ & _ & _ & _ & T5). apply T5. exact Hq.
    - intros a _ _ _ Hd. apply HGR. exact Hd. }
  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model [] LBk SETEC_W eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) _ HPRES).
  - intros b Hb. exact Hb.
  - intros w a Hw Hin. unfold SETEC_W in Hw. destruct Hw as [<-|[<-|[<-|[]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    + exists (EB, EK, ELit 16). split; [left; reflexivity|]. unfold CH2.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
    + exists (ELit 0, 0xd4df8, ELit 2). split; [right; left; reflexivity|]. unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0), (u64_of_Z 2) by lia. lia.
    + exists (ELit 0, 0xf6848, ELit 544). split; [right; right; left; reflexivity|]. unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0), (u64_of_Z 544) by lia. lia.
  -
    intros X HX _. fold nx. set (E2 := CH2.retEx E' nx [] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
    assert (Hest : estart E2 (SA EB EK) = eaddr) by (rewrite (PB.estart_agree NF E0 E2 EB EK HagE2 EB_frozen); exact EADDR).
    destruct Hec as (Hu32 & _ & Hcat). rewrite LS.
    destruct HX as [<-|[<-|[]]].
    + eapply PB.kword32_intro with (A := eaddr) (z := code); [exact Hest | lia | lia | reflexivity | exact Hu32].
    + destruct Hcat as [Hz|[_ Hcat]]; [lia|].
      eapply CL5.kword64_intro with (A := eaddr + 8) (z := PML.OBJ_JSON_CATEGORY); [unfold estart in *; cbn [a_base a_off] in *; lia | lia | lia | reflexivity | exact Hcat].
  -
    fold nx. set (E2 := CH2.retEx E' nx [] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (Z3 : CH2.blocks_vars_lt nx (nth i BLS []) = true).
    { unfold CH2.custom_chk in Hchk. destruct (CH2.common_chk_x _ _ _ _ _ _ _ _) as [ci0|] eqn:Hc0; [|discriminate].
      lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb2; [|discriminate] end. injection Hchk as ->.
      apply andb_prop in Hb2 as [Hb2 _]. apply andb_prop in Hb2 as [Hb2 _]. apply andb_prop in Hb2 as [_ Hb2]. exact Hb2. }
    assert (Hden2 : CH2.den E2 (nth j BLS []) = CH2.den E (nth i BLS [])).
    { rewrite B5, (CH2.den_agree nx E' E2 _ Hag2 Z3). exact Hden. }
    split; [|apply XPOST; exact Hls2].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 (PB.FLOOR L NF sp0 d STK NF32) SETEC_SCR 0%nat c ps cj ci i j E E' R' M' model E2 M2 model LBk SETEC_W cr CF HPRES).
    + intros b Hb. unfold LBk. apply in_or_app. right. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). destruct (SETEC_W_in w a Hw Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
    + apply L5C.model_but_vm_refl.
    + unfold CH2.cur. rewrite Hden2, <- Hden. fold LBk.
      apply (hio_frame L SCFG HI HIok LBk cr M' M2 _ HHk); [|intros x Hx; apply HGR; exact Hx].
      intros a Ha Hpriv. apply (OUTF a Ha).
      * intros w Hw Hin. unfold SETEC_W in Hw. destruct Hw as [<-|[<-|[<-|[]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
        -- destruct Hpriv as [(P1 & _)|P]; [lia|]. destruct (LYR a P) as [Q|Q]; lia.
        -- destruct Hpriv as [(_ & _ & P3)|P]; [apply P3; split; [rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); lia|]; intros AS; pose proof (PmLayout.ly_static L LAY a AS); lia|].
           destruct (PmLayout.ly_ro_img L LAY a P ltac:(rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); lia)) as [Q|[Q|Q]]; lia.
        -- destruct Hpriv as [(_ & _ & P3)|P]; [apply P3; split; [rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); lia|]; intros AS; pose proof (PmLayout.ly_static L LAY a AS); lia|].
           destruct (PmLayout.ly_ro_img L LAY a P ltac:(rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); lia)) as [Q|[Q|Q]]; lia.
      * intros Hin. destruct Hpriv as [(P1 & _)|P]; [unfold SETEC_SCR in *; lia|]. destruct (LYR a P) as [Q|Q]; unfold SETEC_SCR in *; lia.
    + exact Hag2.
    + apply CRED_EQ. apply CRED_EQ in HC. unfold PB.cap_of, PB.tl_of in *. rewrite Hden2. exact HC.
  Unshelve.

  cbv beta iota. fold nx. set (E2 := CH2.retEx E' nx [] R2).
  assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
  rewrite Ha0'. rewrite <- (SR.edenot_agree_AP nx E' E2 _ Hag2 (CH.nth_vars_lt nx (CA.ps_reglist ps) 10 ltac:(rewrite <- Hreq; exact V1))).
  rewrite (APS.split_lit_denot E' _ _ _ Hsplit). f_equal. symmetry. exact Ho.
Qed.

Variable PBx : expr.
Variable PKx : Z.
Hypothesis PB_frozen : APC.expr_vars_lt NF PBx = true.
Variable paddr : Z.
Hypothesis PADDR : estart E0 (SA PBx PKx) = paddr.
Variable vaddr : Z.
Hypothesis OBJS : PML.obj_on_stack L sp0 paddr 272 /\ PML.obj_on_stack L sp0 vaddr 48 /\ PML.obj_on_stack L sp0 eaddr 16 /\
                  PML.apart paddr 272 vaddr 48 /\ PML.apart paddr 272 eaddr 16 /\ PML.apart vaddr 48 eaddr 16.
Hypothesis WPAR_in : forall w a, In w (PML.W_par paddr eaddr) -> L5.in_rng w a -> exists w', In w' W /\ L5.in_rng w' a.
Variables CPC CSCR : Z.
Variable WFin : PML.pstate -> Prop.
Variable BBin : PML.pstate -> Z -> Prop.
Variable PAin : mem -> Z -> PML.pstate -> Prop.
Variable PAout : PML.pstate -> mem -> Z -> PML.pstate -> Prop.
Variable Args : bvmap 5 word -> mem -> Z -> Z -> Z -> PML.pstate -> Prop.
Variable Rel : PML.pstate -> PML.pstate -> Z -> bvmap 5 word -> Prop.
Hypothesis CALLEE : PMS.ptrans_gbk L HI WFin BBin PAin PAout CPC CSCR Args Rel.
Hypothesis PAOUT_CAP : forall pst (M : mem) P ps2, PAout pst M P ps2 -> PML.ps_bcap ps2 mod 2 = 0.
Variable Bv : Z.
Variables KXv BXv : Z.

Lemma ghost_val : forall E' nx ghosts R2 q z, nth q ghosts (Z_to_bv 64 0) = Z_to_bv 64 z -> (q < length ghosts)%nat -> 0 <= z < 2 ^ 64 ->
  bv_unsigned (ev (CH2.retEx E' nx ghosts R2) (nx + q)) = z.
Proof. intros E' nx ghosts R2 q z H Hq Hz. rewrite (CH2.retEx_ghost E' nx ghosts R2 q Hq), H. apply u64_of_Z. exact Hz. Qed.

Definition ptrans_pre (R : bvmap 5 word) (M : mem) (cr : credit) (pst : PML.pstate) : Prop :=
  Args R M paddr vaddr eaddr pst /\ PAin M paddr pst /\ WFin pst /\ PML.win_ok M LBrest pst /\ BBin pst Bv /\ PML.vis_at M vaddr /\ PML.ec_at M eaddr 0 /\
  PML.ls_ok g0 M /\ PML.pcredit_x L cr pst KXv BXv.
Definition ptrans_post (pst : PML.pstate) (R2 : bvmap 5 word) (M2 : mem) (cr2 : credit) (ps2 : PML.pstate) (code : Z) (g' : PML.ls_state) : Prop :=
  PAout pst M2 paddr ps2 /\ PMCUR.wf_c ps2 /\ PML.win_ok M2 LBrest ps2 /\ PML.buf_bound ps2 Bv /\ PML.ec_at M2 eaddr code /\ (code <> 0 -> PML.ps_more ps2 = false) /\
  PML.ls_ok g' M2 /\ (g' = g0 \/ (g' = PML.regJ g0 /\ code <> 0)) /\ PML.pcredit_x L cr2 ps2 KXv BXv /\ Rel pst ps2 code R2.

Definition ptrans_chk (ereg : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  let nx := (CC.cp_nx cj - APC.NCS - 5)%nat in
  match split_lit (nth 10 regs (ELit 0)), split_lit (nth ereg regs (ELit 0)) with
  | (pb, pk), (eb, ek) =>
      if (expr_eqb pb PBx && Z.eqb pk PKx && expr_eqb eb EB && Z.eqb ek EK && Z.leb 0 CSCR
          && CH2.blocks_eqb BLj [(EVar (nx + 1), PSU.emul2 (EVar (nx + 2))); (EVar (nx + 3), EVar (nx + 4))])%bool
      then CH2.custom_chk NF d CSCR 5 [] ((pb, pk, ELit 272) :: (eb, ek, ELit 16) :: PSU.statics_wregs) (PSU.pt_news eb ek nx) None c ps cj BLi
      else None
  end.

Lemma ptrans_leaf_ok : forall ereg i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther CPC) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = CPC ->
  ptrans_chk ereg c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E E' R' (M M' : mem) model cr,
      env_agree NF E0 E' -> APC.sr_vars_lt (CH2.ci_nx ci) (CA.ps_reglist ps) = true -> CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS - 5)%nat ->
      env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> regs_ok E' (CA.ps_reglist ps) R' -> HAMB i E M' model -> XI i E M ->
      hi_heap HI (CH2.cur LBrest BLS i E) cr M' (m_vmmaps model) -> Cred i E cr ->
      exists pst, CH2.den E' (nth i BLS []) = PML.ps_blocks pst /\ ptrans_pre R' M' cr pst /\
        forall R2 (M2 : mem) cr2 ps2 code g' E2,
          ptrans_post pst R2 M2 cr2 ps2 code g' -> env_agree (CH2.ci_nx ci) E' E2 -> bv_unsigned (ev E2 (CH2.ci_nx ci)) = code ->
          CH2.den E2 (nth j BLS []) = PML.ps_blocks ps2 ->
          L5C.hpres L LBrest (sp0 + CH2.ci_csp ci) CSCR (PML.W_par paddr eaddr) M' M2 ->
          XI j E2 M2 /\ Cred j E2 cr2) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros ereg i c k ps j cj ci IL Hret Hcj Hpc Hchk USER fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0.
  unfold ptrans_chk in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [pb pk] eqn:Hsplit.
  destruct (split_lit (nth ereg (CA.ps_reglist ps) (ELit 0))) as [eb ek] eqn:Hsplit2.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B6]. apply andb_prop in Hb as [Hb B5]. apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2].
  apply expr_eqb_eq in B1, B3. apply Z.eqb_eq in B2, B4. apply Z.leb_le in B5. apply CH2.blocks_eqb_eq in B6. subst pb pk eb ek.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              CSCR 5%nat [] _ _ None i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (Hnx : CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS - 5)%nat) by lia.
  rewrite <- Hnx in B6. set (nx := CH2.ci_nx ci) in *.
  pose proof HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  assert (Hoe : estart E' (SA EB EK) = eaddr) by (rewrite (PB.estart_agree NF E0 E' EB EK HagE' EB_frozen); exact EADDR).
  assert (Hop : estart E' (SA PBx PKx) = paddr) by (rewrite (PB.estart_agree NF E0 E' PBx PKx HagE' PB_frozen); exact PADDR).
  pose proof STK as (S1 & S2 & S3 & S4 & S5). pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.
  assert (HRL : regs_ok E' (CA.ps_reglist ps) R') by (rewrite <- Hreq; exact HR).
  destruct (USER E E' R' M M' model cr HagE' ltac:(rewrite <- Hreq; exact V1) Hnx Hag HLF HRL HA' HXI0 HH HC) as (pst & Hblk & (PA & PIN & PWF & PWIN & PBB & PVIS & PEC & PLS & PCR) & UPOST).
  destruct OBJS as (OP & OV & OE & AP1 & AP2 & AP3).
  assert (OBM : forall o n, PML.obj_on_stack L sp0 o n -> PML.obj_on_stack L (sp0 + CH2.ci_csp ci) o n) by (intros o n (X & Y & Z); repeat split; try assumption; lia).
  unfold CH2.cur in HH. rewrite <- Hden, Hblk in HH.
  rewrite Hpc, LS.
  apply (CALLEE LBrest cr (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) paddr vaddr eaddr Bv KXv BXv g0 pst fx' R' M' model K HH Hmo K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]|].
    repeat (split; [assumption|]).
    split; [apply OBM; exact OP|]. split; [apply OBM; exact OV|]. split; [apply OBM; exact OE|]. repeat split; assumption. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (ps2 & code & g' & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & -> & -> & -> & Q9 & Q10) HRP HPRES Hbv2 HH2.
  pose proof (PAOUT_CAP _ _ _ _ Q1) as Hcap2.
  set (bp := PML.ps_bptr ps2) in *. set (bc := PML.ps_bcap ps2) in *. set (sb := PML.ps_sb ps2) in *. set (sc := PML.ps_scap ps2) in *.
  assert (Hblk2 : PML.ps_blocks ps2 = [(bp, bc); (sb, sc)]) by reflexivity. rewrite Hblk2 in HH2. cbn [app] in HH2.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & _).
  destruct (Hwf2 (bp, bc) ltac:(left; reflexivity)) as ((X0 & X1 & X2 & X3 & X4) & _). destruct (Hwf2 (sb, sc) ltac:(right; left; reflexivity)) as ((Y0 & Y1 & Y2 & Y3 & Y4) & _).
  cbn [fst snd] in *.
  assert (Hcode : 0 <= code <= 31) by (destruct Q5 as (_ & _ & [Z0|[Z1 _]]); lia).
  set (ghosts := [Z_to_bv 64 code; Z_to_bv 64 bp; Z_to_bv 64 (bc / 2); Z_to_bv 64 sb; Z_to_bv 64 sc]).
  set (E2 := CH2.retEx E' nx ghosts R2).
  assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
  assert (Hh : 0 <= bc / 2 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold hl_ceil in *.
  assert (G0' : bv_unsigned (ev E2 nx) = code) by (pose proof (ghost_val E' nx ghosts R2 0 code eq_refl ltac:(cbn; lia) ltac:(lia)) as G; rewrite Nat.add_0_r in G; exact G).
  assert (G1 : bv_unsigned (ev E2 (nx + 1)) = bp) by (apply (ghost_val E' nx ghosts R2 1 bp eq_refl); [cbn; lia | lia]).
  assert (G2 : bv_unsigned (ev E2 (nx + 2)) = bc / 2) by (apply (ghost_val E' nx ghosts R2 2 (bc / 2) eq_refl); [cbn; lia | exact Hh]).
  assert (G3 : bv_unsigned (ev E2 (nx + 3)) = sb) by (apply (ghost_val E' nx ghosts R2 3 sb eq_refl); [cbn; lia | lia]).
  assert (G4 : bv_unsigned (ev E2 (nx + 4)) = sc) by (apply (ghost_val E' nx ghosts R2 4 sc eq_refl); [cbn; lia | lia]).
  assert (Hbcd : bc = 2 * (bc / 2)) by (pose proof (Z.div_mod bc 2 ltac:(lia)) as D; rewrite Hcap2 in D; lia).
  assert (Hden2 : CH2.den E2 (nth j BLS []) = PML.ps_blocks ps2).
  { rewrite B6, Hblk2. unfold CH2.den. cbn [map fst snd]. unfold PSU.emul2. fold (PB.uv E2 (APC.escale 2 (EVar (nx + 2)))). rewrite PB.uv_escale. unfold PB.uv. cbn [edenot].
    rewrite G1, G2, G3, G4, <- Hbcd, Z.mod_small by lia. reflexivity. }
  assert (HPR : L5C.hpres L LBrest (sp0 + CH2.ci_csp ci) CSCR (PML.W_par paddr eaddr) M' M2) by exact HPRES.
  destruct (UPOST R2 M2 cr' ps2 code g' E2 (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8 (conj Q9 Q10))))))))) Hag2 G0' Hden2 HPR) as [HXI2 HC2].
  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model2 ghosts LBrest (PML.W_par paddr eaddr) eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HPRES).
  - intros b Hb. exact Hb.
  - intros w a Hw Hin. unfold PML.W_par in Hw. destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    + exists (PBx, PKx, ELit 272). split; [left; reflexivity|]. unfold CH2.in_reg. rewrite Hop. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
    + exists (EB, EK, ELit 16). split; [right; left; reflexivity|]. unfold CH2.in_reg. rewrite Hoe. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
    + exists (ELit 0, 0xd4df8, ELit 2). split; [right; right; left; reflexivity|]. unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0), (u64_of_Z 2) by lia. lia.
    + exists (ELit 0, 0xf6848, ELit 544). split; [right; right; right; left; reflexivity|]. unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0), (u64_of_Z 544) by lia. lia.
  -
    intros X HX _. fold E2. rewrite <- Hnx in HX. fold nx in HX.
    assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
    assert (Hest : estart E2 (SA EB EK) = eaddr) by (rewrite (PB.estart_agree NF E0 E2 EB EK HagE2 EB_frozen); exact EADDR).
    destruct EOBJ as (O1 & O2 & O3). destruct Q5 as (Hu32 & _ & _). rewrite LS.
    destruct HX as [<-|[<-|[]]].
    + eapply PB.kword32_intro with (A := eaddr) (z := code); [exact Hest | lia | lia | | exact Hu32].
      cbn [edenot]. rewrite <- G0'. symmetry. apply Z_to_bv_bv_unsigned.
    + cbn [kentry_ok edenot]. rewrite G0'. lia.
  -
    fold E2. split; [|exact HXI2].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 (PB.FLOOR L NF sp0 d STK NF32) CSCR 5%nat c ps cj ci i j E E' R' M' model E2 M2 model2 LBrest (PML.W_par paddr eaddr) cr' CF HPRES).
    + intros b Hb. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). destruct (WPAR_in w a Hw Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
    + exact Hbv2.
    + unfold CH2.cur. rewrite Hden2, Hblk2. exact HH2.
    + exact Hag2.
    + exact HC2.
Qed.

Variable VBx : expr.
Variable VKx : Z.
Hypothesis VB_frozen : APC.expr_vars_lt NF VBx = true.
Hypothesis VADDR : estart E0 (SA VBx VKx) = vaddr.
Hypothesis WPARC_in : forall w a, In w (PMS.W_parc paddr vaddr eaddr) -> L5.in_rng w a -> exists w', In w' W /\ L5.in_rng w' a.
Hypothesis CALLEEC : PMS.ptrans_gb L HI WFin BBin PAin PAout CPC CSCR Args Rel.
Definition ptrans_postc (pst : PML.pstate) (R2 : bvmap 5 word) (M2 : mem) (cr2 : credit) (ps2 : PML.pstate) (code : Z) (g' : PML.ls_state) : Prop :=
  ptrans_post pst R2 M2 cr2 ps2 code g' /\ PMCUR.cur_post RSEGS pst ps2 code M2 vaddr.

Definition ptrans_chkc (ereg : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  let nx := (CC.cp_nx cj - APC.NCS - 5)%nat in
  match split_lit (nth 10 regs (ELit 0)), split_lit (nth ereg regs (ELit 0)) with
  | (pb, pk), (eb, ek) =>
      if (expr_eqb pb PBx && Z.eqb pk PKx && expr_eqb eb EB && Z.eqb ek EK && Z.leb 0 CSCR
          && CH2.blocks_eqb BLj [(EVar (nx + 1), PSU.emul2 (EVar (nx + 2))); (EVar (nx + 3), EVar (nx + 4))])%bool
      then CH2.custom_chk NF d CSCR 5 [] ((pb, pk, ELit 272) :: (eb, ek, ELit 16) :: (VBx, VKx + 8, ELit 40) :: PSU.statics_wregs) (PSU.pt_news eb ek nx) None c ps cj BLi
      else None
  end.

Lemma ptrans_leaf_okc : forall ereg i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther CPC) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = CPC ->
  ptrans_chkc ereg c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E E' R' (M M' : mem) model cr,
      env_agree NF E0 E' -> APC.sr_vars_lt (CH2.ci_nx ci) (CA.ps_reglist ps) = true -> CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS - 5)%nat ->
      env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> regs_ok E' (CA.ps_reglist ps) R' -> HAMB i E M' model -> XI i E M ->
      hi_heap HI (CH2.cur LBrest BLS i E) cr M' (m_vmmaps model) -> Cred i E cr ->
      exists pst, CH2.den E' (nth i BLS []) = PML.ps_blocks pst /\ ptrans_pre R' M' cr pst /\
        forall R2 (M2 : mem) cr2 ps2 code g' E2,
          ptrans_postc pst R2 M2 cr2 ps2 code g' -> env_agree (CH2.ci_nx ci) E' E2 -> bv_unsigned (ev E2 (CH2.ci_nx ci)) = code ->
          CH2.den E2 (nth j BLS []) = PML.ps_blocks ps2 ->
          L5C.hpres L LBrest (sp0 + CH2.ci_csp ci) CSCR (PMS.W_parc paddr vaddr eaddr) M' M2 ->
          XI j E2 M2 /\ Cred j E2 cr2) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros ereg i c k ps j cj ci IL Hret Hcj Hpc Hchk USER fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0.
  unfold ptrans_chkc in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [pb pk] eqn:Hsplit.
  destruct (split_lit (nth ereg (CA.ps_reglist ps) (ELit 0))) as [eb ek] eqn:Hsplit2.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B6]. apply andb_prop in Hb as [Hb B5]. apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2].
  apply expr_eqb_eq in B1, B3. apply Z.eqb_eq in B2, B4. apply Z.leb_le in B5. apply CH2.blocks_eqb_eq in B6. subst pb pk eb ek.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              CSCR 5%nat [] _ _ None i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (Hnx : CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS - 5)%nat) by lia.
  rewrite <- Hnx in B6. set (nx := CH2.ci_nx ci) in *.
  pose proof HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  assert (Hoe : estart E' (SA EB EK) = eaddr) by (rewrite (PB.estart_agree NF E0 E' EB EK HagE' EB_frozen); exact EADDR).
  assert (Hop : estart E' (SA PBx PKx) = paddr) by (rewrite (PB.estart_agree NF E0 E' PBx PKx HagE' PB_frozen); exact PADDR).
  assert (Hov : estart E' (SA VBx VKx) = vaddr) by (rewrite (PB.estart_agree NF E0 E' VBx VKx HagE' VB_frozen); exact VADDR).
  assert (Hov8 : estart E' (SA VBx (VKx + 8)) = vaddr + 8) by (unfold estart in *; cbn [a_base a_off] in *; lia).
  pose proof STK as (S1 & S2 & S3 & S4 & S5). pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.
  assert (HRL : regs_ok E' (CA.ps_reglist ps) R') by (rewrite <- Hreq; exact HR).
  destruct (USER E E' R' M M' model cr HagE' ltac:(rewrite <- Hreq; exact V1) Hnx Hag HLF HRL HA' HXI0 HH HC) as (pst & Hblk & (PA & PIN & PWF & PWIN & PBB & PVIS & PEC & PLS & PCR) & UPOST).
  destruct OBJS as (OP & OV & OE & AP1 & AP2 & AP3).
  assert (OBM : forall o n, PML.obj_on_stack L sp0 o n -> PML.obj_on_stack L (sp0 + CH2.ci_csp ci) o n) by (intros o n (X & Y & Z); repeat split; try assumption; lia).
  unfold CH2.cur in HH. rewrite <- Hden, Hblk in HH.
  rewrite Hpc, LS.
  apply (CALLEEC LBrest cr (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) paddr vaddr eaddr Bv KXv BXv g0 pst fx' R' M' model K HH Hmo K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]|].
    repeat (split; [assumption|]).
    split; [apply OBM; exact OP|]. split; [apply OBM; exact OV|]. split; [apply OBM; exact OE|]. repeat split; assumption. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (ps2 & code & g' & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & -> & -> & -> & Q9 & Q10 & Q11) HRP HPRES Hbv2 HH2.
  pose proof (PAOUT_CAP _ _ _ _ Q1) as Hcap2.
  set (bp := PML.ps_bptr ps2) in *. set (bc := PML.ps_bcap ps2) in *. set (sb := PML.ps_sb ps2) in *. set (sc := PML.ps_scap ps2) in *.
  assert (Hblk2 : PML.ps_blocks ps2 = [(bp, bc); (sb, sc)]) by reflexivity. rewrite Hblk2 in HH2. cbn [app] in HH2.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & _).
  destruct (Hwf2 (bp, bc) ltac:(left; reflexivity)) as ((X0 & X1 & X2 & X3 & X4) & _). destruct (Hwf2 (sb, sc) ltac:(right; left; reflexivity)) as ((Y0 & Y1 & Y2 & Y3 & Y4) & _).
  cbn [fst snd] in *.
  assert (Hcode : 0 <= code <= 31) by (destruct Q5 as (_ & _ & [Z0|[Z1 _]]); lia).
  set (ghosts := [Z_to_bv 64 code; Z_to_bv 64 bp; Z_to_bv 64 (bc / 2); Z_to_bv 64 sb; Z_to_bv 64 sc]).
  set (E2 := CH2.retEx E' nx ghosts R2).
  assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
  assert (Hh : 0 <= bc / 2 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold hl_ceil in *.
  assert (G0' : bv_unsigned (ev E2 nx) = code) by (pose proof (ghost_val E' nx ghosts R2 0 code eq_refl ltac:(cbn; lia) ltac:(lia)) as G; rewrite Nat.add_0_r in G; exact G).
  assert (G1 : bv_unsigned (ev E2 (nx + 1)) = bp) by (apply (ghost_val E' nx ghosts R2 1 bp eq_refl); [cbn; lia | lia]).
  assert (G2 : bv_unsigned (ev E2 (nx + 2)) = bc / 2) by (apply (ghost_val E' nx ghosts R2 2 (bc / 2) eq_refl); [cbn; lia | exact Hh]).
  assert (G3 : bv_unsigned (ev E2 (nx + 3)) = sb) by (apply (ghost_val E' nx ghosts R2 3 sb eq_refl); [cbn; lia | lia]).
  assert (G4 : bv_unsigned (ev E2 (nx + 4)) = sc) by (apply (ghost_val E' nx ghosts R2 4 sc eq_refl); [cbn; lia | lia]).
  assert (Hbcd : bc = 2 * (bc / 2)) by (pose proof (Z.div_mod bc 2 ltac:(lia)) as D; rewrite Hcap2 in D; lia).
  assert (Hden2 : CH2.den E2 (nth j BLS []) = PML.ps_blocks ps2).
  { rewrite B6, Hblk2. unfold CH2.den. cbn [map fst snd]. unfold PSU.emul2. fold (PB.uv E2 (APC.escale 2 (EVar (nx + 2)))). rewrite PB.uv_escale. unfold PB.uv. cbn [edenot].
    rewrite G1, G2, G3, G4, <- Hbcd, Z.mod_small by lia. reflexivity. }
  assert (HPR : L5C.hpres L LBrest (sp0 + CH2.ci_csp ci) CSCR (PMS.W_parc paddr vaddr eaddr) M' M2) by exact HPRES.
  destruct (UPOST R2 M2 cr' ps2 code g' E2 (conj (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8 (conj Q9 Q10))))))))) Q11) Hag2 G0' Hden2 HPR) as [HXI2 HC2].
  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model2 ghosts LBrest (PMS.W_parc paddr vaddr eaddr) eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HPRES).
  - intros b Hb. exact Hb.
  - intros w a Hw Hin. unfold PMS.W_parc, PML.W_par in Hw. cbn [app] in Hw. destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    + exists (PBx, PKx, ELit 272). split; [left; reflexivity|]. unfold CH2.in_reg. rewrite Hop. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
    + exists (EB, EK, ELit 16). split; [right; left; reflexivity|]. unfold CH2.in_reg. rewrite Hoe. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
    + exists (ELit 0, 0xd4df8, ELit 2). split; [right; right; right; left; reflexivity|]. unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0), (u64_of_Z 2) by lia. lia.
    + exists (ELit 0, 0xf6848, ELit 544). split; [right; right; right; right; left; reflexivity|]. unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0), (u64_of_Z 544) by lia. lia.
    + exists (VBx, VKx + 8, ELit 40). split; [right; right; left; reflexivity|]. unfold CH2.in_reg. rewrite Hov8. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
  -
    intros X HX _. fold E2. rewrite <- Hnx in HX. fold nx in HX.
    assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
    assert (Hest : estart E2 (SA EB EK) = eaddr) by (rewrite (PB.estart_agree NF E0 E2 EB EK HagE2 EB_frozen); exact EADDR).
    destruct EOBJ as (O1 & O2 & O3). destruct Q5 as (Hu32 & _ & _). rewrite LS.
    destruct HX as [<-|[<-|[]]].
    + eapply PB.kword32_intro with (A := eaddr) (z := code); [exact Hest | lia | lia | | exact Hu32].
      cbn [edenot]. rewrite <- G0'. symmetry. apply Z_to_bv_bv_unsigned.
    + cbn [kentry_ok edenot]. rewrite G0'. lia.
  -
    fold E2. split; [|exact HXI2].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 (PB.FLOOR L NF sp0 d STK NF32) CSCR 5%nat c ps cj ci i j E E' R' M' model E2 M2 model2 LBrest (PMS.W_parc paddr vaddr eaddr) cr' CF HPRES).
    + intros b Hb. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). destruct (WPARC_in w a Hw Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
    + exact Hbv2.
    + unfold CH2.cur. rewrite Hden2, Hblk2. exact HH2.
    + exact Hag2.
    + exact HC2.
Qed.
End Inst2.
End PB2.
