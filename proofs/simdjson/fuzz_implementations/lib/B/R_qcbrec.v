(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_poison R_deallocate R_qput R_combfree R_qdorec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma hdr_cas30 : forall b, (0 <= b < 256)%Z ->
  (Z.land (3 + 256 * b) 255 = 3 /\ Z.lxor (3 + 256 * b) 3 = 0 + 256 * b)%Z.
Proof.
  intros b Hb. split; [apply (land255_low 3 b); lia|].
  rewrite (lxor_low 3 b 3); [change (Z.lxor 3 3) with 0%Z; reflexivity| lia| lia| lia| change (Z.lxor 3 3) with 0%Z; lia].
Qed.

Definition qcb_W (M n T sp : Z) : list (Z * Z) :=
  [(M, M + 4); (shad (M + 16), shad (M + 16) + ru8 n / 8); (T + 2840, T + 2856); (sp - 112, sp)]%Z.

Definition qcbrec_post (rao sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (cache c blk : Z) (W : list (Z * Z)) (lo : Z) (P : mem -> Prop) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR rao sp gp tp t0' t1' t2' s0o s1o (Z_to_bv 64 cache) (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 blk)
                  a4' a5' a6' a7' s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 cdealloc_entry) fc None m'
             (seg_rom bsegs)
    /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ P m' /\ stk bsegs m' lo (bv_unsigned sp).

Definition qcb_after (M n b1 T rf rfd : Z) (m : mem) : Prop :=
  rw_cells bsegs m M [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)]
  /\ rw_cells bsegs m (shad (M + 16)) [CB (Z.to_nat (ru8 n / 8)) (farun (ru8 n / 8))]
  /\ rw_cells bsegs m (T + 2840) [C8 (Z_to_bv 64 (rf + 1)); C8 (Z_to_bv 64 (rfd + n))].

Lemma qcb_k1 : forall ra0 sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem)
    (rao s0o s1o s2o s3o s4o : word) (ACEIL SB c off M n b1 TCX T rf rfd cache CBP lo : Z) (shj : list byte),
  (1 <= c <= 30)%Z -> (0 <= off < 2^32)%Z -> SB_ok ACEIL SB ->
  (SB <= M)%Z -> (M + 16 + ru8 n <= SB + 2^37)%Z -> (M mod 16 = 0)%Z -> (1 <= n < 2^32)%Z -> (0 <= b1 < 256)%Z ->
  rw_cells bsegs m M [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)] ->
  rw_cells bsegs m (shad (M + 16)) [CB (Z.to_nat (ru8 n / 8)) shj] -> ps_cells m ->
  thread_cells TCX T m ->
  (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (TCX + 0xa0 <= 0x7fff8000 \/ kHighShadowEnd < TCX)%Z ->
  (TCX + 0xa0 <= 0x10000 \/ 0x6e0000 <= TCX)%Z ->
  (0 < T)%Z -> (T + 4096 <= lo)%Z -> (T + 4096 <= 0x7fff8000 \/ kHighShadowEnd < T)%Z -> (T + 4096 <= 0x10000 \/ 0x6e0000 <= T)%Z ->
  (TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
  (M + 16 <= TCX + 152 \/ TCX + 160 <= M)%Z -> (M + 16 <= T + 2840 \/ T + 2856 <= M)%Z ->
  rw_cells bsegs m (T + 2840) [C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 rfd)] ->
  rw_cells bsegs m i_spacebeg [C8 (Z_to_bv 64 SB)] -> rw_cells bsegs m CBP [C8 (Z_to_bv 64 cache)] -> (0 <= cache < 2^64)%Z ->
  (bv_unsigned sp <= CBP)%Z -> (CBP + 8 <= 2^47)%Z ->
  rw_cells bsegs m (bv_unsigned sp - 48) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  stk bsegs m lo (bv_unsigned sp - 48) -> (lo <= bv_unsigned sp - 112)%Z -> (ACEIL <= lo)%Z -> (0x10007fff8000 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (qcbrec_post rao sp gp (Z_to_bv 64 tpA) s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc cache c (SB + c * 2^32 + off)
               (qcb_W M n T (bv_unsigned sp)) lo (qcb_after M n b1 T rf rfd) m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp - 48)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 CBP) (Z_to_bv 64 M) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (SB + c * 2^32 + off)) (Z_to_bv 64 INST) (Z_to_bv 64 (2^37)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x612a4) fc None m (seg_rom bsegs)).
Proof.
  intros until shj. intros Hc Hoff HSBo HM1 HM2 HM16 Hn Hb1 HD SH PS TC HTCX0 HTCXl HTCXs HTCXi HT0 HTl HTs HTi HTX HMX HMT STS SBC CBC
    HCA HCB1 HCB2 FR ST HLO HAC HLOs HSP MI.
  pose proof HSBo as (HSB1 & HSB2 & HSB3 & HSB4). unfold kHighShadowEnd in *.
  destruct TC as [(KI & K0 & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, i_spacebeg, INST, g_instance in *.
  pose proof (ru8'_range n ltac:(lia)) as RU. change (ru8' n) with (ru8 n) in RU.
  apply box in PS. apply box in SBC. apply box in CBC. apply box in STS. apply box in TT.
  apply box in HTCXs. apply box in HTCXi. apply box in HTs. apply box in HTi. apply box in HTX. apply box in HMX. apply box in HMT.
  assert (PA : ps_args_ok (M + 16) (ru8 n)).
  { unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd. split; [split; [Z.div_mod_to_equations; lia| lia]| right; lia]. }
  pose proof (ps_shad_range _ _ PA) as (SR1 & SR2 & SR3 & SR4). unfold kHighShadowEnd in SR2.
  destruct RU as (RU1 & RU2 & RU3). apply box in RU2. apply box in SR3. apply box in HSB2. apply box in PA.
  apply box in HCA. apply box in HCB1. apply box in HCB2. apply box in Hc. apply box in Hoff.
  pose proof (munch_refl (qcb_W M n T (bv_unsigned sp)) m) as MU.
  pose proof (munch_refl [(M, M + 4); (shad (M + 16), shad (M + 16) + ru8 n / 8); (bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MUa.
  pose proof (wmono_refl bsegs m) as WM.
  unfold qcb_W in MU.
  assert (RM : (17594333495295 < M < 2^47)%Z) by lia.
  replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z in * by lia.

  zhide.
  do 4 zstep.
  do 2 zstep.
  assert (ESH : (Z.land (Z.shiftl M 3) 18446744073709551615 mod 32 = 0)%Z).
  { clear - RM HM16. unfold zal in HM16. rewrite Z.shiftl_mul_pow2 by lia. change 18446744073709551615%Z with (Z.ones 64).
    rewrite Z.land_ones by lia. rewrite (Z.mod_small (M * 2 ^ 3) (2 ^ 64)) by lia.
    change (2 ^ 3)%Z with 8%Z. Z.div_mod_to_equations; lia. }
  rewrite ESH. fold_reg 14%Z. fold_reg 13%Z.
  rewrite land_m4 by (clear - RM; lia). replace (4 * (M / 4))%Z with M by (clear - RM HM16; unfold zal in HM16; Z.div_mod_to_equations; lia).
  pose proof (hdr_cas30 b1 Hb1) as (HC1 & HC2).
  apply (hdr3_to_c4 _ _ 3 b1 [C4 (Z_to_bv 64 n)]) in HD; [| lia| lia].
  assert (AMO : amo_aligned AW (Z_to_bv 64 M) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. Z.div_mod_to_equations; lia. }
  amo_step AMO. rewrite (sx32_small_A (3 + 256 * b1)) by lia.
  zstep. rewrite ?HC1. zstep. ifF.
  do 3 zstep. rewrite ?HC1, ?HC2.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  apply (c4_to_hdr3 _ _ 0 b1 [C4 (Z_to_bv 64 n)]) in HD; [| lia| lia].
  clear ESH HC1 HC2 AMO. apply box in HM16.

  do 7 zstep.
  rewrite (Z.mod_small n 4294967296) by lia. rewrite roundup8_machine by lia. change (ru8' n) with (ru8 n).
  zstep. zstep.
  let mm := amem in
  pose proof (ps_cells_framed m mm _ (unbox _ PS) MUa WM ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)) as PSm.
  clear PS.
  sp_facts.
  call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (M + 16)%Z (ru8 n) 250 lo shj).
  all: rewrite ?Esp in *; try lia; try exact (unbox _ PA); try eassumption; try (unfold kHighShadowEnd; lia).

  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_transport bsegs _ m mm _ _ (unbox _ TT) MUa WM
                  ltac:(pose proof (unbox _ HMX); pose proof (unbox _ HTCXs); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia))
      as TTm end.
  clear TT.
  call (gcts_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  all: rewrite ?Esp in *; try lia; try eassumption.
  all: lazymatch goal with
       | |- thread_cells _ _ _ =>
           unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
           split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TTm]
       | |- evt _ _ _ => idtac
       end.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_transport bsegs _ m mm _ _ (unbox _ STS) MUa WM
                  ltac:(pose proof (unbox _ HMT); pose proof (unbox _ HTs); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia))
      as STSm;
    pose proof (munch_refl [(T + 2840, T + 2856)]%Z mm) as MUb; pose proof (wmono_refl bsegs mm) as WMb end.
  clear STS MUa. clear TTm KI K0 TS T0.
  do 8 zstep.
  apply box in HD. apply box in PC.
  do 2 zstep.
  pose proof (unbox _ Hc) as Hc'. pose proof (unbox _ Hoff) as Hoff'. pose proof (unbox _ HCA) as HCA'.
  pose proof (unbox _ HCB1) as HCB1'. pose proof (unbox _ HCB2) as HCB2'.
  zstep. ifF.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_transport bsegs _ m mm _ _ (unbox _ SBC) MU WM
                  ltac:(pose proof (unbox _ HTi); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as SBCm;
    pose proof (rw_cells_transport bsegs _ m mm _ _ (unbox _ CBC) MU WM
                  ltac:(pose proof (unbox _ HCB1); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as CBCm;
    match goal with MUb' : munch _ ?m3 mm, WMb' : wmono _ ?m3 mm |- _ =>
      pose proof (rw_cells_transport bsegs _ m3 mm _ _ (unbox _ HD) MUb' WMb'
                    ltac:(pose proof (unbox _ HMT); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as HDm;
      pose proof (rw_cells_transport bsegs _ m3 mm _ _ (unbox _ PC) MUb' WMb'
                    ltac:(pose proof (unbox _ HTs); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as PCm end end.
  clear SBC CBC HD PC MUb WMb.
  rewrite (Z.mod_small n 4294967296) in STSm by lia.
  change (1598232 + 32)%Z with i_spacebeg in SBCm.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_mono; [eapply (rtail_frag_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm (Z_to_bv 64 CBP)
                                s0o s1o s2o s3o s4o rao ACEIL SB cache c off lo); try eassumption; try lia|] end.
  - rewrite unsigned_lit by lia. exact CBCm.
  - intros ms' (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU' & WM' & MI' & ST').
    unfold qcbrec_post, cdealloc_entry. exists t0', t1', t2', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU']; intros xx _; exact I]|].
    split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [| exact ST'].
    unfold qcb_after. lazymatch goal with MU1 : munch [] ?m1 m', WM1 : wmono _ ?m1 m' |- _ =>
      split; [apply (rw_cells_transport bsegs _ m1 m' _ _ HDm MU1 WM1 I)|];
      split; [apply (rw_cells_transport bsegs _ m1 m' _ _ PCm MU1 WM1 I)|];
      replace (rfd + n)%Z with (n + rfd)%Z by lia; apply (rw_cells_transport bsegs _ m1 m' _ _ STSm MU1 WM1 I) end.
Qed.

Lemma qthread_cells_frame : forall TCX T W (m m' : mem), thread_cells TCX T m -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W img_hull_lo (img_hull_hi - img_hull_lo) -> disjoint_from W (TCX + 0x98) 8 -> thread_cells TCX T m'.
Proof.
  intros TCX T W m m' [(KI & K & TS & T0) TT] MU WM H1 H2. unfold img_hull_lo, img_hull_hi in H1.
  unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  split; [split; [| split; [| split]]|].
  - apply (rw_cells_transport bsegs W m m' _ _ KI MU WM). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (rw_cells_transport bsegs W m m' _ _ K MU WM). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (rw_cells_transport bsegs W m m' _ _ TS MU WM). cbn [cells_size csize Nat.add]. unfold tpA.
    eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (rw_cells_transport bsegs W m m' _ _ T0 MU WM). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (rw_cells_transport bsegs W m m' _ _ TT MU WM). exact H2.
Qed.

Definition qcbrec_prim_W (blk M n T sp : Z) : list (Z * Z) := (blk, blk + 8)%Z :: qcb_W M n T sp.

Lemma qcbrec_prim_spec : forall ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c idx d mu n b1 TCX T rf rfd cache CBP lo : Z) (shj : list byte),
  (1 <= c <= 30)%Z -> (0 <= idx)%Z -> (d = 0 \/ 16 <= d)%Z -> (d + 16 + ru8 n <= ClassSize c)%Z ->
  ((idx + 1) * ClassSize c <= mu <= 0xE0000000)%Z ->
  rw_cells bsegs m i_spacebeg [C8 (Z_to_bv 64 SB); C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (SB + 2^37))] ->
  rw_cells bsegs m (SB + 2^37 + 128 * c + 48) [C8 (Z_to_bv 64 mu)] -> SB_ok ACEIL SB ->
  ((SB + c * 2^32 + idx * ClassSize c + d) mod 16 = 0)%Z -> (1 <= n < 2^32)%Z -> (0 <= b1 < 256)%Z ->
  rw_cells bsegs m (SB + c * 2^32 + idx * ClassSize c + d)
    [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)] ->
  (d <> 0 -> lch m (SB + c * 2^32 + idx * ClassSize c) (SB + c * 2^32 + idx * ClassSize c + d))%Z ->
  rw_cells bsegs m (shad (SB + c * 2^32 + idx * ClassSize c + d + 16)) [CB (Z.to_nat (ru8 n / 8)) shj] -> ps_cells m ->
  thread_cells TCX T m -> tsep ACEIL SB T TCX ->
  rw_cells bsegs m (T + 2840) [C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 rfd)] ->
  rw_cells bsegs m CBP [C8 (Z_to_bv 64 cache)] -> (0 <= cache < 2^64)%Z -> (bv_unsigned sp <= CBP)%Z -> (CBP + 8 <= 2^47)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 112)%Z -> (ACEIL <= lo)%Z -> (0x10007fff8000 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  let blk := (SB + c * 2^32 + idx * ClassSize c)%Z in
  evt bsegs (qcbrec_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc cache c blk
               (qcbrec_prim_W blk (blk + d) n T (bv_unsigned sp)) lo
               (fun m' => qcb_after (blk + d) n b1 T rf rfd m' /\ (d <> 0 -> rw_cells bsegs m' blk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (blk + d))]))%Z
               m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 CBP) (Z_to_bv 64 (blk + d)) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qcbrec_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until shj. intros Hc Hidx Hd Hdn Hmu SBC RI HSBo HM16 Hn Hb1 HD LCH SH PS TC TSEP STS CBC HCA HCB1 HCB2 ST HLO HAC HLOs HSP MI blk.
  change (SB + c * 2 ^ 32 + idx * ClassSize c)%Z with blk in HM16, HD, LCH, SH.
  pose proof (ClassSize_range c ltac:(lia)) as [[HCS1 HCS2] HCS3]. apply box in HCS3.
  assert (EIDX : ((idx + 1) * ClassSize c = idx * ClassSize c + ClassSize c)%Z) by ring.
  assert (HIX : (0 <= idx * ClassSize c)%Z) by nia.
  assert (HBK : (SB + c * 2^32 <= blk /\ blk + ClassSize c <= SB + c * 2^32 + 2^32)%Z) by (unfold blk; lia).
  clear EIDX.
  pose proof TSEP as (TOK & HTCX0 & HTCXA & HTCXi & HTSB & HTCXSB & HTX & HTs & HTCXs). destruct TOK as (HT0 & HT4k & HTA & HA47 & HTi).
  apply box in HT4k. apply box in HM16.
  apply box in HTCXi. apply box in HTSB. apply box in HTCXSB. apply box in HTX. apply box in HTs. apply box in HTCXs. apply box in HTi.
  apply box in PS. apply box in TC. apply box in STS. apply box in CBC. apply box in SH.
  pose proof HSBo as (HSB1 & HSB2 & HSB3 & HSB4). apply box in HSB2. unfold kHighShadowEnd in *.
  pose proof (ru8'_range n ltac:(lia)) as (RU1 & RU2 & RU3). change (ru8' n) with (ru8 n) in RU1, RU2, RU3. apply box in RU2.
  unfold i_spacebeg, INST, g_instance, qcbrec_entry in *.
  pose proof (munch_refl [(blk, blk + 8); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU0.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MUs.
  pose proof (wmono_refl bsegs m) as WM0.
  carve_frame 48%nat ST.
  zhide.
  do 7 zstep. do 4 zstep.
  eapply evt_cut; [eapply (gbb_frag_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ ACEIL SB c idx d mu);
                   try eassumption; lia|].
  intros ms1 (a2' & a3' & a4' & a5' & a6' & a7' & E1). subst ms1.
  unfold gbb_pc1.
  change (SB + c * 2 ^ 32 + idx * ClassSize c)%Z with blk.
  remember (blk + d)%Z as M eqn:EM.
  pose proof Hd as Hd'. apply box in Hd'.
  apply or_comm in Hd.
  destruct Hd as [Hd16| Hd0];
    [
      zstep; ifF
    |
      zstep; ifT;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (LCHc : d <> 0%Z -> rw_cells bsegs mm blk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 M)]) by (intros H; congruence) end ].
    assert (Hblk8 : (blk mod 8 = 0)%Z).
    { pose proof (unbox _ HSB2) as E1. pose proof (unbox _ HCS3) as E2.
      assert (D1 : (8 | SB)%Z) by (apply (Z.divide_trans _ (2^16)); [exists 8192%Z; reflexivity| apply Z.mod_divide; [lia| exact E1]]).
      assert (D2 : (8 | ClassSize c)%Z) by (apply (Z.divide_trans _ 32); [exists 4%Z; reflexivity| apply Z.mod_divide; [lia| exact E2]]).
      apply Z.mod_divide; [lia|]. unfold blk. apply Z.divide_add_r; [apply Z.divide_add_r; [exact D1| exists (c * 2^29)%Z; ring]|].
      apply Z.divide_mul_r. exact D2. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (rw_cells_transport bsegs _ m mm _ _ (LCH ltac:(lia)) MUs WM0 ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia))
        as LCm end.
    clear MUs.
    unfold lch in LCm. try rewrite <- EM in LCm.
    zstep.
    let mm := amem in
    let bs := eval vm_compute in (option.default [] (image_bytes bsegs 0x10398 8)) in
    assert (RCM : ro_cells bsegs mm 0x10398 [CB (length bs) bs])
      by (apply ro_cells_image; [eassumption| vm_compute; reflexivity| lia| cbn; lia]).
    cbn [length] in RCM.
    zstep. fold_reg 14%Z. clear RCM.
    assert (AMOb : amo_aligned AD (Z_to_bv 64 blk) = true).
    { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. exact Hblk8. }
    unfold K_kAllocBegMagic in LCm.
    amo_step AMOb.
    zstep. first [ifF| dIf_closed].
    amo_step AMOb; try fix_lit_store.
    zstep. first [ifF| dIf_closed].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (LCHc : d <> 0%Z -> rw_cells bsegs mm blk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 M)]) by (intros _; exact LCm) end.
    clear LCm.

  all: assert (PA : ps_args_ok (M + 16) (ru8 n));
         [ unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd; try unfold zal in *; split; [split; [pose proof (unbox _ HM16); try unfold zal in *; Z.div_mod_to_equations; lia| pose proof (unbox _ RU2); lia]| right; lia]|].
  all: pose proof (ps_shad_range _ _ PA) as (SR1 & SR2 & SR3 & SR4); unfold kHighShadowEnd in SR2.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         pose proof (rw_cells_transport bsegs _ m mm _ _ (unbox _ SH) MU0 WM0
                       ltac:(cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia)) as SHm;
         pose proof (ps_cells_framed m mm _ (unbox _ PS) MU0 WM0 ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)) as PSm;
         pose proof (qthread_cells_frame _ _ _ m mm (unbox _ TC) MU0 WM0 ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)
                       ltac:(pose proof (unbox _ HTCXSB); cbn [disjoint_from]; lia)) as TCm;
         pose proof (rw_cells_transport bsegs _ m mm _ _ (unbox _ STS) MU0 WM0
                       ltac:(pose proof (unbox _ HTSB); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as STSm;
         pose proof (rw_cells_transport bsegs _ m mm _ _ (unbox _ CBC) MU0 WM0
                       ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as CBCm end.
  all: lazymatch goal with H : rw_cells bsegs ?mm ?A [C8 ?w0; C8 ?w1; C8 ?w2] |- _ =>
         pose proof (proj1 (rwc_app bsegs mm A [C8 w0] [C8 w1; C8 w2]) H) as (SB1m & _) end.
  all: change (1598232 + 32)%Z with i_spacebeg in SB1m.
  all: assert (HMX : (M + 16 <= TCX + 152 \/ TCX + 160 <= M)%Z)
         by (pose proof (unbox _ HTCXSB) as H0; pose proof (unbox _ Hd') as H1; clear - H0 H1 EM HBK Hdn RU1 Hc Hn HSB1 HIX HCS1 HCS2; lia).
  all: assert (HMT : (M + 16 <= T + 2840 \/ T + 2856 <= M)%Z)
         by (pose proof (unbox _ HTSB) as H0; pose proof (unbox _ Hd') as H1; clear - H0 H1 EM HBK Hdn RU1 Hc Hn HSB1 HIX HCS1 HCS2; lia).
  all: apply box in HMX; apply box in HMT.
  all: pose proof (unbox _ HM16) as HM16'; try rewrite <- EM in HM16'.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         eapply evt_mono; [eapply (qcb_k1 _ sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm ra s0 s1 s2 s3 s4 ACEIL SB c
                                     (idx * ClassSize c) M n b1 TCX T rf rfd cache CBP lo shj); try eassumption; try lia|] end.
  all: try (unfold kHighShadowEnd; lia).
  all: intros ms' (q0 & q1 & q2 & q4 & q5 & q6 & q7 & q3 & q8 & q9 & q10 & m' & E & MU' & WM' & MI' & P & ST').
  all: exists q0, q1, q2, q4, q5, q6, q7, q3, q8, q9, q10, m'; split; [exact E|].
  all: split; [eapply munch_trans; [eapply munch_weaken; [| exact MU0]| eapply munch_weaken; [| exact MU']];
               intros xx Hx; clear - Hx; unfold qcbrec_prim_W, qcb_W in *; cbn [outside] in *; lia|].
  all: split; [eapply wmono_trans; eassumption|]. all: split; [exact MI'|]. all: split; [| exact ST'].
  all: split; [exact P|].
  all: intros Hdnz; pose proof (unbox _ Hd') as Hdd; pose proof (unbox _ HTSB) as HTSB'.
  all: lazymatch goal with |- rw_cells _ ?m2 _ _ => match goal with MU1 : munch _ ?m1 m2, WM1 : wmono _ ?m1 m2 |- _ =>
         apply (rw_cells_transport bsegs _ m1 m2 _ _ (LCHc Hdnz) MU1 WM1) end end.
  all: unfold qcb_W; cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia.
Qed.
