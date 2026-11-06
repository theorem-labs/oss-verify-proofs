(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/RepAppPcf.v (commit eb934de95d13, blob c6159289c746) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 31 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0scf YG0qcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG06bcf YGcfTok.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK10 YK13 YK0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFff.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MemnormHitG MemnormSafepreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require RepRelcf RepRelXcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RepIFcf.

From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.

Definition st_setsize (ns : Z) (s : astate) : astate :=
  match errb_set_size ns s with IRet (_, s') => s' | _ => s end.

Lemma st_setsize_eq : forall ns s, errb_set_size ns s = IRet (tt, st_setsize ns s).
Proof. intros ns s. reflexivity. Qed.

Lemma pk_qloose_frame : forall s s', errb_frame s s' -> qloose s -> qloose s'.
Proof. intros s s' E Q. unfold errb_frame in E. rewrite E. destruct s. exact Q. Qed.

Lemma pk_WfP_cc : forall U pp cc cc' bb s, 0 <= cc' <= cc -> WfP_cf U pp cc bb s -> WfP_cf U pp cc' bb s.
Proof.
intros U pp cc cc' bb s Hc W.
pose proof (wfc_chunks_ev _ _ _ _ _ W) as E1.
pose proof (wfc_secs_ev _ _ _ _ _ W) as E2.
pose proof (wfc_slack _ _ _ _ _ W) as E3.
destruct W. constructor; try assumption; try lia.
Qed.

Lemma pk_setsize : forall (S : astate) (v : Z),
  WfP_cf (as_universe B) 0 (errb_slack S) 0 S -> 0 <= v <= cf_nob ->
  WfP_cf (as_universe B) 0 0 0 (st_setsize v S) /\ errb_frame S (st_setsize v S) /\
  find_sz (st_secs (st_setsize v S)) 0 <> None /\ errb_size_cf (st_setsize v S) = v.
Proof.
intros S v W1 Hv.
assert (W0 : WfP_cf (as_universe B) 0 0 0 S).
{ apply (pk_WfP_cc _ _ (errb_slack S) 0 _ S); [|exact W1].
  pose proof (wfc_slack _ _ _ _ _ W1) as E3. lia. }

pose proof (errb_set_size_ok (as_universe B) 0 0 0 S v true W0 Hv
  ltac:(intros Hn; pose proof (wfc_secs_ev _ _ _ _ _ W1) as X; unfold errb_slack in X; rewrite Hn in X; lia)) as HS.
destruct HS as (W' & EF & _ & _ & HF & HZ).
split; [exact W' | split; [exact EF | split; [exact HF | exact HZ]]].
Qed.

Lemma pk_aview_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros H m m' a E. unfold aview, mbyte, mrestrict. destruct (H (Z_to_bv 64 a)); [reflexivity|]. rewrite E. reflexivity.
Qed.

Lemma pk_vis_mono : forall (H : word -> bool) (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) ->
  forall a, aview tfibsegs H m a <> None -> aview tfibsegs H m' a <> None.
Proof.
intros H m m' P a V. unfold aview, mbyte, mrestrict in *.
destruct (H (Z_to_bv 64 a)) eqn:Hh; [exact V|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (P a (conj Hh (ex_intro _ b Em))) as [_ [b' Eb']]. rewrite Eb'. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact V].
Qed.

Lemma pk_held_eq : forall lk (m m' : word -> option byte) x, m' x = m x -> held_mem lk m' x = held_mem lk m x.
Proof. intros lk m m' x E. destruct lk as [l|]; cbn [held_mem]; [destruct (in8 l x); [reflexivity | exact E] | exact E]. Qed.

Lemma pk_held_pres : forall lk (H : word -> bool) (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) ->
  forall a, apresent H (held_mem lk m) a -> apresent H (held_mem lk m') a.
Proof.
intros lk H m m' P a [Hh [b Eb]]. split; [exact Hh|]. destruct lk as [l|]; cbn [held_mem] in *.
- destruct (in8 l (Z_to_bv 64 a)); [exists (Z_to_bv 8 0); reflexivity|].
  destruct (P a (conj Hh (ex_intro _ b Eb))) as [_ X]. exact X.
- destruct (P a (conj Hh (ex_intro _ b Eb))) as [_ X]. exact X.
Qed.

Lemma pk_last_cap_some : forall S, errb_mapped_cf S = true -> last_cap_idx (st_secs S) 0 None <> None.
Proof.
intros S M E. unfold errb_mapped_cf in M.
assert (G : forall l i acc, last_cap_idx l i acc = None -> acc = None /\ existsb is_errb_cap l = false).
{ induction l as [|sm t IH]; intros i acc H; cbn [last_cap_idx existsb] in *; [split; [exact H | reflexivity]|].
  destruct (is_errb_cap sm) eqn:Ec.
  - destruct (IH _ _ H) as [X _]. discriminate X.
  - cbn [orb]. exact (IH _ _ H). }
destruct (G _ _ _ E) as [_ F]. rewrite F in M. discriminate M.
Qed.

Lemma pk_xs_mapped : forall ly S, errb_mapped_cf S = true ->
  xs_cf ly S = [(YG0ncf.errb_data_cf ly S, errb_cap_cf S)].
Proof.
intros ly S M. pose proof (pk_last_cap_some S M) as N. unfold xs_cf, YG0ncf.errb_data_cf.
destruct (last_cap_idx (st_secs S) 0 None); [reflexivity | exfalso; apply N; reflexivity].
Qed.

Lemma pk_xs_place : forall ly S d c, xs_cf ly S = [(d, c)] -> xs_placed_cf ly S ->
  in_app d c /\ d + c <= alloc_ceiling /\
  zdisjoint (d, c) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\ zdisjoint (d, c) (ly_img ly) /\
  zdisjoint (d, c) (ly_prim ly, kPrimResvSize).
Proof.
intros ly S d c E P. unfold xs_placed_cf in P. rewrite E in P. apply Forall_inv in P.
destruct P as (_ & IA & CE & DJ). rewrite Forall_forall in DJ.
assert (IS : forall z, In z (static_extents ly) -> zdisjoint (d, c) z).
{ intros z Hz. apply DJ. apply in_app_iff. right. apply in_app_iff. left. exact Hz. }
split; [exact IA|]. split; [exact CE|].
split; [apply IS; unfold static_extents; apply in_app_iff; right; left; reflexivity|].
split; [apply IS; unfold static_extents; apply in_app_iff; right; right; left; reflexivity|].
apply IS. unfold static_extents, owned_extents. left. reflexivity.
Qed.

Lemma pk_layout : forall ly, layout_ok ly -> img_cover ly ->
  zdisjoint (ly_prim ly, kPrimResvSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
  zdisjoint (ly_prim ly, kPrimResvSize) (ly_img ly) /\
  zdisjoint (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (ly_img ly) /\
  fst (ly_img ly) <= TFIB_IMG_LO /\ TFIB_IMG_END <= fst (ly_img ly) + snd (ly_img ly) /\ 0 < snd (ly_img ly) /\
  ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
  kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
  kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof.
intros ly LY [I1 I2]. pose proof (lo_disj ly LY) as LD.
assert (E2 : static_extents ly = (owned_extents ly ++ [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)]) ++ [ly_img ly]).
{ unfold static_extents. rewrite <- app_assoc. reflexivity. }
split; [apply (pairwise_In zdisjoint (static_extents ly) _ _ (owned_extents ly) [_; _] eq_refl LD); [left; reflexivity | left; reflexivity]|].
split; [apply (pairwise_In zdisjoint (static_extents ly) _ _ (owned_extents ly) [_; _] eq_refl LD); [left; reflexivity | right; left; reflexivity]|].
split; [apply (pairwise_In zdisjoint (static_extents ly) _ _ _ _ E2 LD); [apply in_app_iff; right; left; reflexivity | left; reflexivity]|].
pose proof (lo_img ly LY) as (_ & IM & _). pose proof (lo_space_in ly LY) as [S1 S2].
pose proof (lo_high ly LY) as [P1 P2]. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
repeat split; assumption.
Qed.

Lemma pk_held_off : forall lk ly (m : word -> option byte) (x : word), lk_ok ly lk ->
  ~ (ly_space ly + kRegionInfoOff <= bv_unsigned x < ly_space ly + kRegionInfoOff + 4096) -> held_mem lk m x = m x.
Proof.
intros lk ly m x [->|(c & Hc & ->)] Hx; cbn [held_mem]; [reflexivity|].
destruct (in8 (region_lock_addr ly c) x) eqn:E; [|reflexivity]. exfalso.
unfold in8, region_lock_addr in E. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply Hx. lia.
Qed.

Lemma pk_cells_held : forall lk lyL ly S (H : word -> bool) (m : word -> option byte),
  lk_ok lyL lk -> layout_ok lyL -> cf_errbuf_obj = 0xaa728 ->
  (forall a, YG0ncf.errb_data_cf ly S <= a < YG0ncf.errb_data_cf ly S + errb_cap_cf S -> aview tfibsegs H (held_mem lk m) a <> None) ->
  YG0ncf.errb_cells_cf B ly S (aview tfibsegs H m) -> YG0ncf.errb_cells_cf B ly S (aview tfibsegs H (held_mem lk m)).
Proof.
intros lk lyL ly S H m LK LO EO VB C.
pose proof (lo_space_in _ LO) as [S1 S2]. pose proof (lo_high _ LO) as [H1 H2]. pose proof ASAN_CEIL_range as [CR _].
unfold YG0ncf.errb_cells_cf in *. cbv zeta in *. rewrite EO in *.
destruct C as (P0 & P16 & P32 & P40 & P48 & _ & PL & PM).
assert (CK : forall A v, 0xaa728 <= A -> A + 8 <= 0xaa728 + 56 ->
  cell_holds B ly (aview tfibsegs H m) (z8 (ANum A) v) -> cell_holds B ly (aview tfibsegs H (held_mem lk m)) (z8 (ANum A) v)).
{ intros A v HA HB Cc. apply (cell_holds_agree B ly _ _ _ Cc). intros k Hk. cbn [c_w c_at z8 c8 aeval] in Hk |- *.
  apply pk_aview_eq. apply (pk_held_off lk lyL m _ LK).
  rewrite Z_to_bv_unsigned, bv_wrap_small; [|change (bv_modulus 64) with (2 ^ 64); lia].
  unfold ASAN_CEIL, kPrimResvSize, kHighMemBeg, kRegionInfoOff, kSpaceSize in *. lia. }
split; [apply CK; [lia | lia | exact P0]|]. split; [apply CK; [lia | lia | exact P16]|].
split; [apply CK; [lia | lia | exact P32]|]. split; [apply CK; [lia | lia | exact P40]|].
split; [apply CK; [lia | lia | exact P48]|]. split; [exact VB|]. split; [exact PL | exact PM].
Qed.

Lemma pk_xs_not_owned : forall ly S S' Hp rd d c b, ARmcf B ly S Hp rd -> errb_frame S S' -> xs_cf ly S' = [(d, c)] ->
  xs_placed_cf ly S' -> d <= b < d + c -> ~ aowned B ly S b.
Proof.
intros ly S S' Hp rd d c b M EF XS XP Hb OW. pose proof (RepRelcf.rr_zf_owned B ly S Hp rd b M OW) as Z.
unfold xs_placed_cf in XP. rewrite XS in XP. apply Forall_inv in XP. destruct XP as (_ & OA & _ & OD). cbn [fst snd] in OA, OD.
pose proof (proj1 (Forall_app _ _ _) OD) as [ODc ODr]. pose proof (proj1 (Forall_app _ _ _) ODr) as [ODs _].
unfold errb_frame in EF. rewrite EF in ODc. exact (RepRelcf.rr_zf_apart ly S d c b OA ODs ODc Z Hb).
Qed.

Lemma post_keep : forall lk Hp ly S W regs mem md (s : list Z) regs' mem' mat,
  let len := Z.of_nat (length s) in
  (TfibSyms B -> pf_cells_apart_t B) -> errb_call_pre B lk Hp ly S W mem md -> errb_call_regs B APP_STK ly W regs mem ->
  errb_room_for S len -> errb_mapped_cf S = true -> errb_size_cf S + len <= errb_cap_cf S ->
  regs_preserved regs regs' ->
  (forall x : word, ~ (spZ regs - APP_STK <= bv_unsigned x < spZ regs) ->
     ~ (C_ERRBUF <= bv_unsigned x < C_ERRBUF + 56) ->
     ~ (YG0ncf.errb_data_cf ly S + errb_size_cf S <= bv_unsigned x
        < YG0ncf.errb_data_cf ly S + errb_size_cf S + len) -> mem' x = mem x) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') C_ERRBUF 8 (C_ERRBUF + 32) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (C_ERRBUF + 16) 8 0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (C_ERRBUF + 32) 8 (YG0ncf.errb_data_cf ly S) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (C_ERRBUF + 40) 8 (errb_cap_cf S) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (C_ERRBUF + 48) 8 (errb_size_cf S + len) ->
  errb_call_post B lk APP_STK len Hp ly S (st_setsize (errb_size_cf S + len) S) W regs mem md W
    (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)).
Proof.
intros lk Hp ly S W regs mem md s regs' mem' mat. cbv zeta.
intros PFA PRE REGS ROOM MAP FIT RP FR PRES V0 V16 V32 V40 V48.
destruct PRE as (EO & EX & LY & IMG & TS & TSD & ARL & XM & W1 & QL & EXH & CELLS & IMGF & HT).
destruct ARL as (LK & AR & LKV).
destruct REGS as (_ & _ & _ & _ & _ & RLO & RHI & RWIN).
pose proof ASAN_CEIL_range as [CR _].
unfold errb_room_for in ROOM. unfold APP_STK in *.
assert (Hlen : 0 <= Z.of_nat (length s)) by lia.
assert (Z0 : 0 <= errb_size_cf S) by exact (errb_size_nonneg_cf (as_universe B) 0 (errb_slack S) 0 S W1).
assert (GR : secs_errb_grow (st_secs S) (st_secs (st_setsize (errb_size_cf S + Z.of_nat (length s)) S)))
  by (apply (YGcfSecsStep.secs_errb_set_grow_ret _ S _ (st_setsize_eq _ S)); lia).
unfold YG0ncf.errb_cells_cf in CELLS. cbv zeta in CELLS. rewrite EO in CELLS.
destruct CELLS as (_ & _ & _ & _ & _ & CV & _ & CPG).
assert (XS : xs_cf ly S = [(YG0ncf.errb_data_cf ly S, errb_cap_cf S)]) by exact (pk_xs_mapped ly S MAP).
destruct (pk_xs_place ly S _ _ XS (xs_placed_of_ARcf tfibsegs B ly S Hp W _ md AR)) as (XA & XC & XSTK & XIMG & XPRIM).
destruct (pk_layout ly LY IMG) as (DPS & DPI & DSI & I1 & I2 & I3 & SP1 & SP2 & PR1 & PR2 & ST1 & ST2).
unfold zdisjoint in XSTK, XIMG, XPRIM, DPS, DPI, DSI. cbn [fst snd] in XSTK, XIMG, XPRIM, DPS, DPI, DSI.
unfold in_app in XA. unfold C_ERRBUF in *. unfold TFIB_IMG_LO, TFIB_IMG_END in I1, I2.
unfold ASAN_CEIL in *. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, kHighMemBeg, kHighMemEnd, kLowShadowBeg, kPage in *.
change (2 ^ 37) with 137438953472 in *.

destruct (pk_setsize S (errb_size_cf S + Z.of_nat (length s)) W1 ltac:(lia)) as (WF' & EFR & HFIND & ESZ).
destruct (RepRelcf.errb_rel_setsize ly S (st_setsize (errb_size_cf S + Z.of_nat (length s)) S) md
  (errb_size_cf S + Z.of_nat (length s)) (xs_placed_of_ARcf tfibsegs B ly S Hp W _ md AR) XM (st_setsize_eq _ S))
  as (XM1 & XP1 & _ & EC' & ED' & EM' & ES' & EXS & _).

set (S' := st_setsize (errb_size_cf S + Z.of_nat (length s)) S) in *.
pose proof (RepRelcf.rr_hull_ok_step S S' EFR GR HT) as HT'.

assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 512 <= a < spZ regs) -> ~ (0xaa728 <= a < 0xaa728 + 56) ->
  ~ (YG0ncf.errb_data_cf ly S + errb_size_cf S <= a
     < YG0ncf.errb_data_cf ly S + errb_size_cf S + Z.of_nat (length s)) -> mem' (w64 a) = mem (w64 a)).
{ intros a Ha N1 N2 N3. unfold w64. apply FR; rewrite unsigned_lit_small by lia; assumption. }
assert (RIK : forall a, ly_space ly + 137438953472 <= a < ly_space ly + 137438953472 + 4096 -> mem' (w64 a) = mem (w64 a)).
{ intros a Ha. apply KEEP; lia. }
assert (IMK : forall a, 0x10000 <= a < 0x600000 -> ~ (0xaa728 <= a < 0xaa728 + 56) -> mem' (w64 a) = mem (w64 a)).
{ intros a Ha Hn. apply KEEP; [lia | lia | exact Hn | lia]. }
assert (XS' : xs_cf ly S' = [(YG0ncf.errb_data_cf ly S, errb_cap_cf S)]) by (rewrite EXS; exact XS).

pose proof (YG0ncf.ARcf_errb_cells tfibsegs B ly S Hp W _ md AR) as CH.
unfold YG0ncf.errb_cells_cf in CH. cbv zeta in CH. destruct CH as (_ & _ & _ & _ & _ & CVH & _ & _).
assert (CELLSM : YG0ncf.errb_cells_cf B ly S' (aview tfibsegs (w_H W) mem')).
{ apply (RepRelcf.errb_cells_build B ly S' (w_H W) mem').
  - rewrite EO, EM', MAP. exact V0.
  - rewrite EO. exact V16.
  - rewrite EO, ED'. exact V32.
  - rewrite EO, EC'. exact V40.
  - rewrite EO, ES'. exact V48.
  - intros a Ha. rewrite ED', EC' in Ha. apply (pk_vis_mono (w_H W) mem mem' PRES). apply CV. exact Ha.
  - rewrite ES', EC'. exact FIT.
  - rewrite EC'. exact CPG. }
assert (CELLSH : YG0ncf.errb_cells_cf B ly S' (aview tfibsegs (w_H W) (held_mem lk mem'))).
{ apply (pk_cells_held lk ly ly S' (w_H W) mem' LK LY ltac:(rewrite EO; reflexivity)); [|exact CELLSM].
  intros a Ha. rewrite ED', EC' in Ha. apply (pk_vis_mono (w_H W) (held_mem lk mem) (held_mem lk mem') (pk_held_pres lk _ _ _ PRES)).
  apply CVH. exact Ha. }

assert (AR2 : ARcf tfibsegs B ly S' Hp W (held_mem lk mem') (with_vm_backing (m_vm_lazy md) mat md)).
{ apply (RepRelXcf.errb_rel_post B Hp ly S S' W (held_mem lk mem) md (held_mem lk mem') _ TS IMG ltac:(rewrite EO; reflexivity) (PFA TS)
           (RepRelcf.rr_split_secs B ly S S S' Hp W _ md EFR GR EXS EC' (RepRelcf.rr_split_of_ARcf B ly S Hp W _ md AR)) EFR WF' XP1).
  - intros a Ha OW NO. apply pk_aview_eq. apply pk_held_eq. unfold RepRelXcf.PW in NO. apply KEEP; [exact Ha | | exact NO |].
    + intros Hs. apply (RepRelcf.rr_stack_not_owned B ly S Hp _ a (proj1 AR)); [lia | exact OW].
    + intros Hb. apply (RepRelcf.errb_xs_not_aowned B Hp ly S _ a (proj1 AR));
        [rewrite XS; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact OW].
  - intros a _ _ Hv. exact (pk_vis_mono _ _ _ (pk_held_pres lk _ _ _ PRES) a Hv).
  - apply m_vmmaps_wvb.
  - apply m_vm_lazy_wvb.
  - unfold eager_used. rewrite m_vmmaps_wvb, m_vm_lazy_wvb. reflexivity.
  - intros a Hb _. apply pk_held_eq. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb.
    apply KEEP; lia.
  - exact CELLSH. }
unfold errb_call_post.
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md) mat md).
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{
  split; [exact EO|]. split; [exact EX|]. split; [exact LY|]. split; [exact IMG|]. split; [exact TS|]. split; [exact TSD|].
  split.
  { split; [exact LK|]. split; [exact AR2|]. destruct lk as [l|]; [|exact I].
    destruct LK as [LKn|(c & Hc & LKs)]; [discriminate LKn|]. injection LKs as ->. unfold region_lock_addr in *.
    apply (AF0x.val_mem_frame (w_H W) mem mem' _ 8 _); [|exact LKV].
    intros k Hk. apply RIK. unfold kRegionInfoOff. change (2 ^ 37) with 137438953472. lia. }
  split. { unfold xs_mapped_cf in *. rewrite m_vmmaps_wvb. exact XM1. }
  split. { unfold errb_slack. destruct (find_sz (st_secs S') 0) eqn:Ef; [exact WF' | exfalso; exact (HFIND eq_refl)]. }
  split. { exact (pk_qloose_frame S S' EFR QL). }
  split.
  { apply (YGcfInstBase.exh_cell_cf_frame B ly ly S S' (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) mem') EXH).
    - intros c. unfold errb_frame in EFR. rewrite EFR at 1. reflexivity.
    - intros c Hc. cbn [aoff aeval]. rewrite EX. apply pk_aview_eq. apply RIK.
      unfold kRegionInfoOff. change (2 ^ 37) with 137438953472. lia. }
  split. { exact CELLSM. }
  split; [|exact HT'].
  { destruct IMGF as [IT IC ISL IV]. destruct IV as [F1 F2 FT JS JU].
    assert (L1 : (length FMT1_BYTES <= 100)%nat) by (apply Nat.leb_le; vm_compute; reflexivity).
    assert (L2 : (length FMT2_BYTES <= 100)%nat) by (apply Nat.leb_le; vm_compute; reflexivity).
    assert (L3 : (length (str_z "AddressSanitizer" ++ [0%Z]) <= 100)%nat) by (apply Nat.leb_le; vm_compute; reflexivity).
    constructor.
    - apply (AF0x.val_mem_frame (w_H W) mem mem' _ 8 _); [|exact IT]. intros k Hk. apply IMK; unfold C_TOOLNAME; lia.
    - apply (AF0x.val_mem_frame (w_H W) mem mem' _ 8 _); [|exact IC]. intros k Hk. apply IMK; unfold C_PFCB; lia.
    - apply (AF0x.val_mem_frame (w_H W) mem mem' _ 8 _); [|exact ISL]. intros k Hk. apply IMK; unfold C_SILENT; lia.
    - constructor.
      + intros i Hi. apply (AF0x.val_mem_frame (w_H W) mem mem' _ 1 _); [|exact (F1 i Hi)]. intros k Hk. apply IMK; unfold FMT_OOM1; lia.
      + intros i Hi. apply (AF0x.val_mem_frame (w_H W) mem mem' _ 1 _); [|exact (F2 i Hi)]. intros k Hk. apply IMK; unfold FMT_OOM2; lia.
      + intros i Hi. apply (AF0x.val_mem_frame (w_H W) mem mem' _ 1 _); [|exact (FT i Hi)]. intros k Hk. apply IMK; unfold A_TOOLNAME; lia.
      + apply (AF0x.val_mem_frame (w_H W) mem mem' _ 4 _); [|exact JS]. intros k Hk. apply IMK; lia.
      + apply (AF0x.val_mem_frame (w_H W) mem mem' _ 4 _); [|exact JU]. intros k Hk. apply IMK; lia. } }
split. { rewrite ES'. lia. }
split. { apply layout_le_refl. }
split. { apply wle_refl. }
split. { intros r Hr. apply RP. exact Hr. }
split. { unfold same_io. repeat split; reflexivity. }
assert (AOXZ : forall a, 0 <= a < 2 ^ 64 -> ~ YGcfInstBase.AOX_cf B ly S a -> ~ (spZ regs - 512 <= a < spZ regs) ->
  mem' (w64 a) = mem (w64 a)).
{ intros a Ha NA NS. unfold YGcfInstBase.AOX_cf, AOXm_cf in NA. apply KEEP; [exact Ha | lia | |].
  - intros Ho. apply NA. left. apply (own_static_cf B ly S Hp _ a (proj1 AR)). rewrite (ts_owned _ TS). unfold Tfib_owned_static.
    do 3 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - intros Hb. apply NA. right. rewrite XS. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
split. { intros a Ha NA _ NS. apply pk_aview_eq. apply AOXZ; [exact Ha | exact NA | exact NS]. }
split. { intros x NA _ NS. pose proof (AOXZ (bv_unsigned x) (u64_range x) NA NS) as E.
  unfold w64 in E. rewrite Z_to_bv_bv_unsigned in E. exact E. }
split.
{ apply (MemnormT.memnorm_frame tfibsegs
    (fun a => (spZ regs - 512 <= a < spZ regs) \/ (0xaa728 <= a < 0xaa728 + 56) \/
      (YG0ncf.errb_data_cf ly S + errb_size_cf S <= a
       < YG0ncf.errb_data_cf ly S + errb_size_cf S + Z.of_nat (length s)))).
  - intros x [Hx|[Hx|Hx]].
    + apply MemnormHitG.mn_safe_high. unfold kImgEnd, TASK_SIZE. lia.
    + apply MemnormSafepreset.mn_safe_rw. unfold TASK_SIZE. lia.
    + apply (MemnormHitG.mn_safe_off ly x IMG); [lia | unfold TASK_SIZE; lia].
  - intros x Hx. apply FR; intros Hy; apply Hx; tauto. }
intros a Ha. apply PRES. apply RWIN. exact Ha.
Qed.

Lemma pk_aview_HF : forall (H H' : word -> bool) (m m' : word -> option byte) b,
  H' (Z_to_bv 64 b) = H (Z_to_bv 64 b) -> m' (Z_to_bv 64 b) = m (Z_to_bv 64 b) ->
  aview tfibsegs H' m' b = aview tfibsegs H m b.
Proof. intros H H' m m' b E1 E2. unfold aview, mbyte, mrestrict. rewrite E1, E2. reflexivity. Qed.

Lemma pk_val_mem_HF : forall (H H' : word -> bool) (m m' : word -> option byte) b (n : nat) v,
  (forall k, (k < n)%nat -> H' (Z_to_bv 64 (b + Z.of_nat k)) = H (Z_to_bv 64 (b + Z.of_nat k)) /\
     m' (Z_to_bv 64 (b + Z.of_nat k)) = m (Z_to_bv 64 (b + Z.of_nat k))) ->
  val_mem tfibsegs (mrestrict H m) b n v -> val_mem tfibsegs (mrestrict H' m') b n v.
Proof.
intros H H' m m' b n v E V k Hk. destruct (E k Hk) as [E1 E2].
unfold mbyte, mrestrict in *. rewrite E1, E2. exact (V k Hk).
Qed.

Lemma pk_apres_view : forall (H : word -> bool) (m : word -> option byte) b,
  apresent H m b -> aview tfibsegs H m b <> None.
Proof. intros H m b [Hh [bb Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

Lemma pk_aview_wrap : forall (H : word -> bool) (m : word -> option byte) b,
  aview tfibsegs H m (bv_unsigned (Z_to_bv 64 b)) = aview tfibsegs H m b.
Proof. intros H m b. unfold aview, mbyte, mrestrict. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma pk_held_apres : forall lk (H : word -> bool) (m : word -> option byte) b,
  apresent H m b -> apresent H (held_mem lk m) b.
Proof.
intros lk H m b [Hh [bb Hb]]. split; [exact Hh|]. destruct lk as [l|]; cbn [held_mem];
[destruct (in8 l (Z_to_bv 64 b)); [exists (Z_to_bv 8 0); reflexivity | exists bb; exact Hb] | exists bb; exact Hb].
Qed.

Lemma pk_obj_view : forall (W0 : world tfibsegs) (m : word -> option byte) b,
  0xaa728 <= b < 0xaa728 + 56 -> aview tfibsegs (w_H W0) m b <> None.
Proof.
intros W0 m b Hb. destruct (AFff.rw_mbyte W0 m b ltac:(lia)) as [bb Hbb].
unfold aview. rewrite Hbb. discriminate.
Qed.

Lemma pk_mapped_app : forall (S1 : astate) l n,
  st_secs S1 = l ++ [mkSec n ERRB_CAP_TAG false] -> errb_mapped_cf S1 = true.
Proof.
intros S1 l n E. unfold errb_mapped_cf. rewrite E, existsb_app.
replace (existsb is_errb_cap [mkSec n ERRB_CAP_TAG false]) with true by reflexivity. apply orb_true_r.
Qed.

Lemma pk_exh_frame : forall s s', errb_frame s s' -> forall c, exh_mem_cf s' c = exh_mem_cf s c.
Proof. intros s s' E c. unfold errb_frame in E. rewrite E at 1. reflexivity. Qed.

Lemma pk_le_facts : forall n ly ly', layout_le n ly ly' ->
  ly_space ly' = ly_space ly /\ ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly /\ ly_img ly' = ly_img ly.
Proof.
intros n ly ly' LE.
destruct LE as (_ & E2 & _ & _ & _ & _ & _ & _ & _ & E10 & E11 & _ & _ & _ & _ & E16 & _).
split; [exact E2|]. split; [exact E10|]. split; [exact E11 | exact E16].
Qed.

Lemma post_remap : forall lk Hp ly S S1 W regs mem md (s : list Z) (a : Z) (mat matF : list word)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (W' : world tfibsegs) (mdU mdF : Model),
  let len := Z.of_nat (length s) in
  let ncap := page_round_up_Z (errb_size_cf S + len) in
  mdU = YK0v.munmap_model (w64 (YG0ncf.errb_data_cf ly S)) (w64 (errb_cap_cf S))
          (Mmap.with_mmap_backing (w64 34) (w64 a) (w64 ncap)
             (YK0v.mmap_model (w64 a) (w64 ncap) (with_vm_backing (m_vm_lazy md) mat md))) ->
  mdF = with_vm_backing (m_vm_lazy mdU) matF mdU ->
  (TfibSyms B -> pf_cells_apart_t B) -> errb_call_pre B lk Hp ly S W mem md -> errb_call_regs B APP_STK ly W regs mem ->
  errb_mapped_cf S = true -> 0 < errb_cap_cf S -> errb_cap_cf S < errb_size_cf S + len ->
  errb_size_cf S + len < 2 ^ 47 -> errb_room_for S len ->
  RepRelcf.ALEDGER_X ly S md -> WfP_cf (as_universe B) 0 (errb_slack S1) 0 S1 -> errb_frame S S1 ->
  st_secs S1 = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] ->
  wle W W' -> w_A W' = w_A W ->
  (forall x : word, ~ (a <= bv_unsigned x < a + ncap) -> w_H W' x = w_H W x) ->
  YK13.grant_ok_na_pin md (w64 a) ncap = true -> 0 < a -> a + ncap < 2 ^ 64 ->
  regs_preserved regs regs' ->
  (forall x : word, ~ (spZ regs - APP_STK <= bv_unsigned x < spZ regs) ->
     ~ (C_ERRBUF <= bv_unsigned x < C_ERRBUF + 56) -> ~ (a <= bv_unsigned x < a + ncap) ->
     ~ (YG0ncf.errb_data_cf ly S <= bv_unsigned x < YG0ncf.errb_data_cf ly S + errb_cap_cf S) ->
     mem' x = mem x) ->
  (forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b ->
     ~ (YG0ncf.errb_data_cf ly S <= b < YG0ncf.errb_data_cf ly S + errb_cap_cf S) ->
     ~ (C_ERRBUF <= b < C_ERRBUF + 56) -> apresent (w_H W') mem' b) ->
  (forall b, a <= b < a + ncap -> apresent (w_H W') mem' b) ->
  val_mem tfibsegs (mrestrict (w_H W') mem') C_ERRBUF 8 (C_ERRBUF + 32) ->
  val_mem tfibsegs (mrestrict (w_H W') mem') (C_ERRBUF + 16) 8 0 ->
  val_mem tfibsegs (mrestrict (w_H W') mem') (C_ERRBUF + 32) 8 a ->
  val_mem tfibsegs (mrestrict (w_H W') mem') (C_ERRBUF + 40) 8 ncap ->
  val_mem tfibsegs (mrestrict (w_H W') mem') (C_ERRBUF + 48) 8 (errb_size_cf S + len) ->
  same_io md mdF ->
  errb_call_post B lk APP_STK len Hp ly S (st_setsize (errb_size_cf S + len) S1) W regs mem md W'
    (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) mdF).
Proof.
intros lk Hp ly S S1 W regs mem md s a mat matF regs' mem' W' mdU mdF. cbv zeta.
intros EMU EMF PFA PRE REGS MAP CAPPOS TOOSMALL SZ47 ROOM LX W1S1 EFR1 ES1
  WLE WA HHN GRANT APOS ANW RP FRM PRESA PRESN V0 V16 V32 V40 V48 SIO.
destruct PRE as (EO & EX & LY & IMG & TS & TSD & ARL & XM & W1 & QL & EXH & CELLS & IMGF & HT).
destruct ARL as (LK & AR & LKV).
destruct REGS as (_ & _ & _ & _ & _ & RLO & RHI & RWIN).
pose proof ASAN_CEIL_range as [CR _].
unfold APP_STK in *. unfold errb_room_for in ROOM.
assert (HL : 0 <= Z.of_nat (length s)) by lia.
assert (Hs0 : 0 <= errb_size_cf S) by exact (errb_size_nonneg_cf (as_universe B) 0 (errb_slack S) 0 S W1).
unfold YG0ncf.errb_cells_cf in CELLS. cbv zeta in CELLS. rewrite EO in CELLS.
destruct CELLS as (_ & _ & _ & _ & _ & CV & FIT0 & CPG).
pose proof (YK02.page_round_up_Z_bounds (errb_size_cf S + Z.of_nat (length s)) ltac:(lia)) as HNB.
pose proof (YK10.page_round_up_Z_aligned (errb_size_cf S + Z.of_nat (length s))) as HNM.
unfold page_size in HNB, HNM.
assert (GR1 : secs_errb_grow (st_secs S) (st_secs S1))
  by exact (RepRelcf.rr_secs_grow_map S S1 (page_round_up_Z (errb_size_cf S + Z.of_nat (length s))) ltac:(lia) ES1).
assert (GR2 : secs_errb_grow (st_secs S1) (st_secs (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1))).
{ apply (YGcfSecsStep.secs_errb_set_grow_ret _ S1 _ (st_setsize_eq _ S1)); [rewrite (RepRelcf.rr_size_map S S1 _ ES1)|]; lia. }
assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
assert (G' : YK13.grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) (w64 a)
               (page_round_up_Z (errb_size_cf S + Z.of_nat (length s))) = true) by exact GRANT.
destruct (RepRelcf.errb_grant_facts B Hp ly S W (held_mem lk mem) md mat a
            (page_round_up_Z (errb_size_cf S + Z.of_nat (length s))) AR XM G' Ha64 ltac:(lia) ltac:(lia))
  as (GA & GAPP & GCE & GFA).
assert (XS : xs_cf ly S = [(YG0ncf.errb_data_cf ly S, errb_cap_cf S)]) by exact (pk_xs_mapped ly S MAP).
destruct (pk_xs_place ly S _ _ XS (xs_placed_of_ARcf tfibsegs B ly S Hp W _ md AR)) as (XA & XC & XSTK & XIMG & XPRIM).
destruct (pk_layout ly LY IMG) as (DPS & DPI & DSI & I1 & I2 & I3 & SP1 & SP2 & PR1 & PR2 & ST1 & ST2).
assert (GPRIM : zdisjoint (a, page_round_up_Z (errb_size_cf S + Z.of_nat (length s))) (ly_prim ly, kPrimResvSize)).
{ apply (proj1 (Forall_forall _ _) GFA). apply in_or_app. left. unfold static_extents, owned_extents. left. reflexivity. }
assert (GSTK : zdisjoint (a, page_round_up_Z (errb_size_cf S + Z.of_nat (length s)))
                 (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)).
{ apply (proj1 (Forall_forall _ _) GFA). apply in_or_app. left. unfold static_extents.
  apply in_app_iff. right. left. reflexivity. }
assert (GIMG : zdisjoint (a, page_round_up_Z (errb_size_cf S + Z.of_nat (length s))) (ly_img ly)).
{ apply (proj1 (Forall_forall _ _) GFA). apply in_or_app. left. unfold static_extents.
  apply in_app_iff. right. right. left. reflexivity. }
assert (GBUF : zdisjoint (a, page_round_up_Z (errb_size_cf S + Z.of_nat (length s)))
                 (YG0ncf.errb_data_cf ly S, errb_cap_cf S)).
{ apply (proj1 (Forall_forall _ _) GFA). do 4 (apply in_or_app; right). rewrite XS. left. reflexivity. }
unfold zdisjoint in XSTK, XIMG, XPRIM, DPS, DPI, DSI, GPRIM, GSTK, GIMG, GBUF.
cbn [fst snd] in XSTK, XIMG, XPRIM, DPS, DPI, DSI, GPRIM, GSTK, GIMG, GBUF.

assert (GBAND : forall b, in_band_rw b -> ~ (a <= b < a + page_round_up_Z (errb_size_cf S + Z.of_nat (length s)))).
{ intros b Hb Hin. unfold in_app in GAPP. pose proof ASAN_CEIL_range as [CR' _].
  unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *. lia. }
assert (XBAND : forall b, in_band_rw b -> ~ (YG0ncf.errb_data_cf ly S <= b < YG0ncf.errb_data_cf ly S + errb_cap_cf S)).
{ intros b Hb Hin. unfold in_app in XA. pose proof ASAN_CEIL_range as [CR' _].
  unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *. lia. }
clear GSTK GBUF DPI DSI XA GAPP GA GFA.
unfold C_ERRBUF in *. unfold TFIB_IMG_LO, TFIB_IMG_END in I1, I2.
unfold ASAN_CEIL in *.
unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, kHighMemBeg, kHighMemEnd, kLowShadowBeg, kPage in *.
change (2 ^ 37) with 137438953472 in *.

assert (W0S1 : Wf_cf (as_universe B) S1).
{ apply (pk_WfP_cc _ _ (errb_slack S1) 0 _ S1); [pose proof (wfc_slack _ _ _ _ _ W1S1) as E3; lia | exact W1S1]. }

pose proof (AR_wle_cf tfibsegs B ly S Hp W W' (held_mem lk mem) md AR WLE
              ltac:(intros i Hi; rewrite WA; exact Hi) ltac:(rewrite WA; exact (proj1 (proj1 (proj2 (proj2 AR)))))) as AR'.
destruct (RepRelcf.errb_rel_remap B Hp ly S S1 W' (held_mem lk mem) md mat a
            (page_round_up_Z (errb_size_cf S + Z.of_nat (length s))) TS IMG AR' XM LX MAP ltac:(lia)
            Ha64 ltac:(lia) ltac:(unfold kPage; exact HNM) G' W0S1 EFR1 ES1)
  as (LE & LO1 & IMG1 & TSD1 & RS & LX1 & XM1 & XP1 & DAT1 & CAP1 & BUD1).
destruct (pk_le_facts _ ly _ LE) as (LSP & LLO & LHI & LIM).
pose proof (proj1 RS) as M1.
destruct (pk_setsize S1 (errb_size_cf S + Z.of_nat (length s)) W1S1 ltac:(lia))
  as (WF' & EFR2 & HFIND & ESZ).
destruct (RepRelcf.errb_rel_setsize (set_ly_sec ly (length (st_secs S)) a) S1 (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1) _
            (errb_size_cf S + Z.of_nat (length s)) XP1 XM1 (st_setsize_eq _ S1))
  as (XM2 & XP2 & _ & EC2 & ED2 & EM2 & ES2 & EXS2 & _).
pose proof (RepRelcf.rr_hull_ok_step S1 _ EFR2 GR2 (RepRelcf.rr_hull_ok_step S S1 EFR1 GR1 HT)) as HT'.
assert (MAP1 : errb_mapped_cf S1 = true) by exact (pk_mapped_app S1 _ _ ES1).
assert (XS1 : xs_cf (set_ly_sec ly (length (st_secs S)) a) (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1) = [(a, page_round_up_Z (errb_size_cf S + Z.of_nat (length s)))]).
{ rewrite (pk_xs_mapped _ _ ltac:(rewrite EM2; exact MAP1)). rewrite ED2, EC2, DAT1, CAP1. reflexivity. }
assert (XS0 : xs_cf (set_ly_sec ly (length (st_secs S)) a) S = [(YG0ncf.errb_data_cf ly S, errb_cap_cf S)]) by (rewrite (xs_cf_layout ly _ S LE); exact XS).
assert (EFR : errb_frame S (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1)) by exact (errb_frame_trans _ _ _ EFR1 EFR2).

assert (CELLSM : YG0ncf.errb_cells_cf B (set_ly_sec ly (length (st_secs S)) a) (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1) (aview tfibsegs (w_H W') mem')).
{ apply (RepRelcf.errb_cells_build B (set_ly_sec ly (length (st_secs S)) a) (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1) (w_H W') mem').
  - rewrite EO, EM2, MAP1. exact V0.
  - rewrite EO. exact V16.
  - rewrite EO, ED2, DAT1. exact V32.
  - rewrite EO, EC2, CAP1. exact V40.
  - rewrite EO, ES2. exact V48.
  - intros b Hb. rewrite ED2, EC2, DAT1, CAP1 in Hb. apply pk_apres_view. apply PRESN. exact Hb.
  - rewrite ES2, EC2, CAP1. lia.
  - rewrite EC2, CAP1. unfold kPage. exact HNM. }
assert (CELLSH : YG0ncf.errb_cells_cf B (set_ly_sec ly (length (st_secs S)) a) (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1) (aview tfibsegs (w_H W') (held_mem lk mem'))).
{ apply (pk_cells_held lk ly (set_ly_sec ly (length (st_secs S)) a) (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1) (w_H W') mem' LK LY ltac:(rewrite EO; reflexivity)); [|exact CELLSM].
  intros b Hb. rewrite ED2, EC2, DAT1, CAP1 in Hb. apply pk_apres_view. apply pk_held_apres. apply PRESN. exact Hb. }

assert (AR4 : ARcf tfibsegs B (set_ly_sec ly (length (st_secs S)) a) (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1) Hp W' (held_mem lk mem') mdF).
{ rewrite EMF, EMU.
  apply (RepRelXcf.errb_rel_post B Hp (set_ly_sec ly (length (st_secs S)) a) S (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1) W' (held_mem lk mem) _ (held_mem lk mem') _ TS IMG1
           ltac:(rewrite EO; reflexivity) (PFA TS) (RepRelcf.rr_split_secs B (set_ly_sec ly (length (st_secs S)) a) S S1 (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1) Hp W' _ _ EFR2 GR2 EXS2 EC2 RS) EFR WF' XP2).
  - intros b Hb OW NO. unfold RepRelXcf.PW in NO. apply pk_aview_eq. apply pk_held_eq.
    apply FRM; rewrite unsigned_lit_small by lia.
    + intros Hs. apply (RepRelcf.rr_stack_not_owned B (set_ly_sec ly (length (st_secs S)) a) S Hp _ b M1); [rewrite LLO, LHI; lia | exact OW].
    + exact NO.
    + intros Hn. exact (pk_xs_not_owned (set_ly_sec ly (length (st_secs S)) a) S (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1) Hp _ a _ b M1 EFR XS1 XP2 Hn OW).
    + intros Ho. apply (RepRelcf.errb_xs_not_aowned B Hp (set_ly_sec ly (length (st_secs S)) a) S _ b M1); [|exact OW].
      rewrite XS0. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ho.
  - intros b Hb64 Hxs Hv. rewrite XS0 in Hxs. apply Forall_inv in Hxs. unfold in_zr in Hxs. cbn [fst snd] in Hxs.
    destruct (Z_le_dec 0xaa728 b) as [O1|O1]; destruct (Z_lt_dec b (0xaa728 + 56)) as [O2|O2];
    try (apply (pk_obj_view W' (held_mem lk mem') b); lia);
    destruct (Z_le_dec (spZ regs - 512) b) as [K1|K1]; destruct (Z_lt_dec b (spZ regs)) as [K2|K2];
    try (apply pk_apres_view; apply pk_held_apres; apply PRESA; [lia | apply RWIN; lia | lia | lia]);
    destruct (Z_le_dec a b) as [N1|N1]; destruct (Z_lt_dec b (a + page_round_up_Z (errb_size_cf S + Z.of_nat (length s)))) as [N2|N2];
    try (apply pk_apres_view; apply pk_held_apres; apply PRESN; lia);
    (rewrite (pk_aview_eq (w_H W') (held_mem lk mem) (held_mem lk mem') b); [exact Hv|];
     apply pk_held_eq; apply FRM; rewrite unsigned_lit_small by lia; lia).
  - rewrite m_vmmaps_wvb. reflexivity.
  - rewrite m_vm_lazy_wvb. reflexivity.
  - unfold eager_used. rewrite m_vmmaps_wvb, m_vm_lazy_wvb. reflexivity.
  - intros b Hb _. assert (Hb' := Hb).
    unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb'.
    apply pk_held_eq. apply FRM; rewrite unsigned_lit_small by lia; [lia | lia | exact (GBAND b Hb) | exact (XBAND b Hb)].
  - exact CELLSH. }

assert (IMK2 : forall b, 0x10000 <= b < 0x600000 -> ~ (0xaa728 <= b < 0xaa728 + 56) ->
  w_H W' (Z_to_bv 64 b) = w_H W (Z_to_bv 64 b) /\ mem' (Z_to_bv 64 b) = mem (Z_to_bv 64 b)).
{ intros b Hb Hn. split.
  - apply HHN. rewrite unsigned_lit_small by lia. lia.
  - apply FRM; rewrite unsigned_lit_small by lia; [lia | exact Hn | lia | lia]. }
unfold errb_call_post.
exists (set_ly_sec ly (length (st_secs S)) a), regs', mem', mdF.
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ split; [exact EO|]. split; [exact EX|]. split; [exact LO1|]. split; [exact IMG1|]. split; [exact TS|].
  split; [rewrite TSD1; exact TSD|].
  split.
  { destruct LK as [LKn|(c & Hc & LKs)].
    - split; [left; exact LKn|]. split; [exact AR4|]. rewrite LKn. exact I.
    - split.
      { right. exists c. split; [exact Hc|]. rewrite LKs. unfold region_lock_addr. rewrite LSP. reflexivity. }
      split; [exact AR4|]. rewrite LKs. rewrite LKs in LKV. cbn [held_mem] in LKV |- *.
      apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 8 _); [|exact LKV].
      intros k Hk. unfold region_lock_addr in *. unfold kRegionInfoOff in *. change (2 ^ 37) with 137438953472 in *. split.
      + apply HHN. rewrite unsigned_lit_small by lia. lia.
      + apply FRM; rewrite unsigned_lit_small by lia; lia. }
  split. { unfold xs_mapped_cf in *. rewrite EMF, EMU, m_vmmaps_wvb. exact XM2. }
  split. { unfold errb_slack.
    destruct (find_sz (st_secs (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1)) 0) eqn:Ef;
    [exact WF' | exfalso; exact (HFIND eq_refl)]. }
  split. { exact (pk_qloose_frame S1 _ EFR2 (pk_qloose_frame S S1 EFR1 QL)). }
  split.
  { apply (YGcfInstBase.exh_cell_cf_frame B ly (set_ly_sec ly (length (st_secs S)) a) S
             (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1)
             (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W') mem') EXH).
    - intros c. rewrite (pk_exh_frame S1 _ EFR2 c). exact (pk_exh_frame S S1 EFR1 c).
    - intros c Hc. cbn [aoff aeval]. rewrite EX, LSP. unfold kRegionInfoOff. change (2 ^ 37) with 137438953472. apply pk_aview_HF.
      + apply HHN. rewrite unsigned_lit_small by lia. lia.
      + apply FRM; rewrite unsigned_lit_small by lia; lia. }
  split. { exact CELLSM. }
  split; [|exact HT'].
  { destruct IMGF as [IT IC ISL IV]. destruct IV as [F1 F2 FT JS JU].
    assert (L1 : (length FMT1_BYTES <= 100)%nat) by (apply Nat.leb_le; vm_compute; reflexivity).
    assert (L2 : (length FMT2_BYTES <= 100)%nat) by (apply Nat.leb_le; vm_compute; reflexivity).
    assert (L3 : (length (str_z "AddressSanitizer" ++ [0%Z]) <= 100)%nat) by (apply Nat.leb_le; vm_compute; reflexivity).
    constructor.
    - apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 8 _); [|exact IT]. intros k Hk. apply IMK2; unfold C_TOOLNAME; lia.
    - apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 8 _); [|exact IC]. intros k Hk. apply IMK2; unfold C_PFCB; lia.
    - apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 8 _); [|exact ISL]. intros k Hk. apply IMK2; unfold C_SILENT; lia.
    - constructor.
      + intros i Hi. apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 1 _); [|exact (F1 i Hi)]. intros k Hk. apply IMK2; unfold FMT_OOM1; lia.
      + intros i Hi. apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 1 _); [|exact (F2 i Hi)]. intros k Hk. apply IMK2; unfold FMT_OOM2; lia.
      + intros i Hi. apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 1 _); [|exact (FT i Hi)]. intros k Hk. apply IMK2; unfold A_TOOLNAME; lia.
      + apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 4 _); [|exact JS]. intros k Hk. apply IMK2; lia.
      + apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 4 _); [|exact JU]. intros k Hk. apply IMK2; lia. } }
split. { rewrite ES2. lia. }
split. { exact LE. }
split. { exact WLE. }
split. { intros r Hr. apply RP. exact Hr. }
split. { exact SIO. }
assert (AOXZ : forall b, 0 <= b < 2 ^ 64 -> ~ YGcfInstBase.AOX_cf B ly S b ->
  ~ YGcfInstBase.AOX_cf B (set_ly_sec ly (length (st_secs S)) a)
      (st_setsize (errb_size_cf S + Z.of_nat (length s)) S1) b ->
  ~ (spZ regs - 512 <= b < spZ regs) ->
  w_H W' (Z_to_bv 64 b) = w_H W (Z_to_bv 64 b) /\ mem' (Z_to_bv 64 b) = mem (Z_to_bv 64 b)).
{ intros b Hb NA NA' NS.
  assert (NOBJ : ~ (0xaa728 <= b < 0xaa728 + 56)).
  { intros Ho. apply NA.
    apply (RepRelcf.errb_aox_obj B Hp ly S W (held_mem lk mem) md b TS ltac:(rewrite EO; reflexivity) AR).
    rewrite EO. exact Ho. }
  assert (NBUF : ~ (YG0ncf.errb_data_cf ly S <= b < YG0ncf.errb_data_cf ly S + errb_cap_cf S)).
  { intros Ho. apply NA. unfold YGcfInstBase.AOX_cf, AOXm_cf. right. rewrite XS.
    apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ho. }
  assert (NNEW : ~ (a <= b < a + page_round_up_Z (errb_size_cf S + Z.of_nat (length s)))).
  { intros Ho. apply NA'. unfold YGcfInstBase.AOX_cf, AOXm_cf. right. rewrite XS1.
    apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ho. }
  split; [apply HHN; rewrite unsigned_lit_small by lia; exact NNEW
        | apply FRM; rewrite unsigned_lit_small by lia; assumption]. }
split. { intros b Hb NA NA' NS. destruct (AOXZ b Hb NA NA' NS) as [E1 E2]. exact (pk_aview_HF _ _ _ _ b E1 E2). }
split. { intros x NA NA' NS. destruct (AOXZ (bv_unsigned x) (u64_range x) NA NA' NS) as [_ E2].
  rewrite Z_to_bv_bv_unsigned in E2. exact E2. }
split.
{ apply (MemnormT.memnorm_frame tfibsegs
    (fun b => (spZ regs - 512 <= b < spZ regs) \/ (0xaa728 <= b < 0xaa728 + 56)
           \/ (a <= b < a + page_round_up_Z (errb_size_cf S + Z.of_nat (length s)))
           \/ (YG0ncf.errb_data_cf ly S <= b < YG0ncf.errb_data_cf ly S + errb_cap_cf S))).
  - intros x [Hx|[Hx|[Hx|Hx]]].
    + apply MemnormHitG.mn_safe_high. unfold kImgEnd, TASK_SIZE. lia.
    + apply MemnormSafepreset.mn_safe_rw. unfold TASK_SIZE. lia.
    + apply MemnormSafepreset.mn_safe_offimg; unfold TFIB_IMG_LO, TFIB_IMG_END, TASK_SIZE; lia.
    + apply MemnormSafepreset.mn_safe_offimg; unfold TFIB_IMG_LO, TFIB_IMG_END, TASK_SIZE; lia.
  - intros x Hx. apply FRM; intros Hy; apply Hx; tauto. }
intros b Hb. apply PRESA; [lia | apply RWIN; exact Hb | lia | lia].
Qed.

Lemma pk_last_cap_none : forall l i acc, existsb is_errb_cap l = false -> last_cap_idx l i acc = acc.
Proof.
induction l as [|sm t IH]; intros i acc H; [reflexivity|].
cbn [existsb last_cap_idx] in *. apply orb_false_iff in H as [H1 H2]. rewrite H1. exact (IH _ _ H2).
Qed.

Lemma pk_xs_unmapped : forall ly S, errb_mapped_cf S = false -> xs_cf ly S = [].
Proof.
intros ly S U. unfold xs_cf. rewrite (pk_last_cap_none (st_secs S) 0 None U). reflexivity.
Qed.

Lemma post_first : forall lk Hp ly S S1 W regs mem md (s : list Z) (a : Z) (mat matF : list word)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (W' : world tfibsegs) (md1 mdF : Model),
  let len := Z.of_nat (length s) in
  let ncap := page_round_up_Z 65536 in
  md1 = Mmap.with_mmap_backing (w64 34) (w64 a) (w64 ncap)
          (YK0v.mmap_model (w64 a) (w64 ncap) (with_vm_backing (m_vm_lazy md) mat md)) ->
  mdF = with_vm_backing (m_vm_lazy md1) matF md1 ->
  (TfibSyms B -> pf_cells_apart_t B) -> errb_call_pre B lk Hp ly S W mem md -> errb_call_regs B APP_STK ly W regs mem ->
  errb_mapped_cf S = false -> len <= 65536 -> errb_room_for S len ->
  RepRelcf.ALEDGER_X ly S md -> WfP_cf (as_universe B) 0 (errb_slack S1) 0 S1 -> errb_frame S S1 ->
  st_secs S1 = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] ->
  wle W W' -> w_A W' = w_A W ->
  (forall x : word, ~ (a <= bv_unsigned x < a + ncap) -> w_H W' x = w_H W x) ->
  YK13.grant_ok_na_pin md (w64 a) ncap = true -> 0 < a -> a + ncap < 2 ^ 64 ->
  regs_preserved regs regs' ->
  (forall x : word, ~ (spZ regs - APP_STK <= bv_unsigned x < spZ regs) ->
     ~ (C_ERRBUF <= bv_unsigned x < C_ERRBUF + 56) -> ~ (a <= bv_unsigned x < a + ncap) ->
     mem' x = mem x) ->
  (forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b ->
     ~ (C_ERRBUF <= b < C_ERRBUF + 56) -> apresent (w_H W') mem' b) ->
  (forall b, a <= b < a + ncap -> apresent (w_H W') mem' b) ->
  val_mem tfibsegs (mrestrict (w_H W') mem') C_ERRBUF 8 (C_ERRBUF + 32) ->
  val_mem tfibsegs (mrestrict (w_H W') mem') (C_ERRBUF + 16) 8 0 ->
  val_mem tfibsegs (mrestrict (w_H W') mem') (C_ERRBUF + 32) 8 a ->
  val_mem tfibsegs (mrestrict (w_H W') mem') (C_ERRBUF + 40) 8 ncap ->
  val_mem tfibsegs (mrestrict (w_H W') mem') (C_ERRBUF + 48) 8 len ->
  same_io md mdF ->
  errb_call_post B lk APP_STK len Hp ly S (st_setsize len S1) W regs mem md W'
    (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) mdF).
Proof.
intros lk Hp ly S S1 W regs mem md s a mat matF regs' mem' W' md1 mdF. cbv zeta.
intros EM1 EMF PFA PRE REGS UNMAP LEN65 ROOM LX W1S1 EFR1 ES1
  WLE WA HHN GRANT APOS ANW RP FRM PRESA PRESN V0 V16 V32 V40 V48 SIO.
destruct PRE as (EO & EX & LY & IMG & TS & TSD & ARL & XM & W1 & QL & EXH & CELLS & IMGF & HT).
destruct ARL as (LK & AR & LKV).
destruct REGS as (_ & _ & _ & _ & _ & RLO & RHI & RWIN).
pose proof ASAN_CEIL_range as [CR _].
unfold APP_STK in *. unfold errb_room_for in ROOM.
assert (HL : 0 <= Z.of_nat (length s)) by lia.
assert (Hs0 : 0 <= errb_size_cf S) by exact (errb_size_nonneg_cf (as_universe B) 0 (errb_slack S) 0 S W1).
assert (HN65 : page_round_up_Z 65536 = 65536) by (vm_compute; reflexivity).
pose proof (YK10.page_round_up_Z_aligned 65536) as HNM. unfold page_size in HNM.

assert (SZ0 : errb_size_cf S = 0).
{ pose proof CELLS as CE. unfold YG0ncf.errb_cells_cf in CE. cbv zeta in CE. destruct CE as (_ & _ & _ & _ & _ & _ & FIT0 & _).
  assert (CAP0 : errb_cap_cf S = 0).
  { unfold errb_mapped_cf in UNMAP. rewrite RepRelcf.rr_existsb_filter in UNMAP. unfold errb_cap_cf, errb_e.
    destruct (filter is_errb_cap (st_secs S)); [reflexivity | discriminate UNMAP]. }
  lia. }
assert (GR1 : secs_errb_grow (st_secs S) (st_secs S1)) by exact (RepRelcf.rr_secs_grow_map S S1 (page_round_up_Z 65536) ltac:(lia) ES1).
assert (GR2 : secs_errb_grow (st_secs S1) (st_secs (st_setsize (Z.of_nat (length s)) S1))).
{ apply (YGcfSecsStep.secs_errb_set_grow_ret _ S1 _ (st_setsize_eq _ S1)); [rewrite (RepRelcf.rr_size_map S S1 _ ES1)|]; lia. }
assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
assert (G' : YK13.grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) (w64 a)
               (page_round_up_Z 65536) = true) by exact GRANT.
destruct (RepRelcf.errb_grant_facts B Hp ly S W (held_mem lk mem) md mat a (page_round_up_Z 65536)
            AR XM G' Ha64 ltac:(lia) ltac:(lia)) as (GA & GAPP & GCE & GFA).
assert (XS : xs_cf ly S = []) by exact (pk_xs_unmapped ly S UNMAP).
destruct (pk_layout ly LY IMG) as (DPS & DPI & DSI & I1 & I2 & I3 & SP1 & SP2 & PR1 & PR2 & ST1 & ST2).
assert (GPRIM : zdisjoint (a, page_round_up_Z 65536) (ly_prim ly, kPrimResvSize)).
{ apply (proj1 (Forall_forall _ _) GFA). apply in_or_app. left. unfold static_extents, owned_extents. left. reflexivity. }
assert (GIMG : zdisjoint (a, page_round_up_Z 65536) (ly_img ly)).
{ apply (proj1 (Forall_forall _ _) GFA). apply in_or_app. left. unfold static_extents.
  apply in_app_iff. right. right. left. reflexivity. }
unfold zdisjoint in DPS, DPI, DSI, GPRIM, GIMG. cbn [fst snd] in DPS, DPI, DSI, GPRIM, GIMG.
assert (GBAND : forall b, in_band_rw b -> ~ (a <= b < a + page_round_up_Z 65536)).
{ intros b Hb Hin. unfold in_app in GAPP. pose proof ASAN_CEIL_range as [CR' _].
  unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *. lia. }
clear DPI DSI GAPP GA GFA.
unfold C_ERRBUF in *. unfold TFIB_IMG_LO, TFIB_IMG_END in I1, I2.
unfold ASAN_CEIL in *.
unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, kHighMemBeg, kHighMemEnd, kLowShadowBeg, kPage in *.
change (2 ^ 37) with 137438953472 in *.

assert (W0S1 : Wf_cf (as_universe B) S1).
{ apply (pk_WfP_cc _ _ (errb_slack S1) 0 _ S1); [pose proof (wfc_slack _ _ _ _ _ W1S1) as E3; lia | exact W1S1]. }

pose proof (AR_wle_cf tfibsegs B ly S Hp W W' (held_mem lk mem) md AR WLE
              ltac:(intros i Hi; rewrite WA; exact Hi) ltac:(rewrite WA; exact (proj1 (proj1 (proj2 (proj2 AR)))))) as AR'.
destruct (RepRelcf.errb_rel_map B Hp ly S S1 W' (held_mem lk mem) md mat a (page_round_up_Z 65536)
            TS IMG AR' XM LX UNMAP Ha64 ltac:(lia) ltac:(unfold kPage; exact HNM) G' W0S1 EFR1 ES1)
  as (LE & LO1 & IMG1 & TSD1 & RS & LX1 & XM1 & XP1 & DAT1 & CAP1 & BUD1).
destruct (pk_le_facts _ ly _ LE) as (LSP & LLO & LHI & LIM).
pose proof (proj1 RS) as M1.
destruct (pk_setsize S1 (Z.of_nat (length s)) W1S1 ltac:(lia)) as (WF' & EFR2 & HFIND & ESZ).
destruct (RepRelcf.errb_rel_setsize (set_ly_sec ly (length (st_secs S)) a) S1 (st_setsize (Z.of_nat (length s)) S1) _
            (Z.of_nat (length s)) XP1 XM1 (st_setsize_eq _ S1))
  as (XM2 & XP2 & _ & EC2 & ED2 & EM2 & ES2 & EXS2 & _).
pose proof (RepRelcf.rr_hull_ok_step S1 _ EFR2 GR2 (RepRelcf.rr_hull_ok_step S S1 EFR1 GR1 HT)) as HT'.
assert (MAP1 : errb_mapped_cf S1 = true) by exact (pk_mapped_app S1 _ _ ES1).
assert (XS1 : xs_cf (set_ly_sec ly (length (st_secs S)) a) (st_setsize (Z.of_nat (length s)) S1) = [(a, page_round_up_Z 65536)]).
{ rewrite (pk_xs_mapped _ _ ltac:(rewrite EM2; exact MAP1)). rewrite ED2, EC2, DAT1, CAP1. reflexivity. }
assert (XS0 : xs_cf (set_ly_sec ly (length (st_secs S)) a) S = []) by (rewrite (xs_cf_layout ly _ S LE); exact XS).
assert (EFR : errb_frame S (st_setsize (Z.of_nat (length s)) S1)) by exact (errb_frame_trans _ _ _ EFR1 EFR2).

assert (CELLSM : YG0ncf.errb_cells_cf B (set_ly_sec ly (length (st_secs S)) a) (st_setsize (Z.of_nat (length s)) S1) (aview tfibsegs (w_H W') mem')).
{ apply (RepRelcf.errb_cells_build B (set_ly_sec ly (length (st_secs S)) a) (st_setsize (Z.of_nat (length s)) S1) (w_H W') mem').
  - rewrite EO, EM2, MAP1. exact V0.
  - rewrite EO. exact V16.
  - rewrite EO, ED2, DAT1. exact V32.
  - rewrite EO, EC2, CAP1. exact V40.
  - rewrite EO, ES2. exact V48.
  - intros b Hb. rewrite ED2, EC2, DAT1, CAP1 in Hb. apply pk_apres_view. apply PRESN. exact Hb.
  - rewrite ES2, EC2, CAP1. lia.
  - rewrite EC2, CAP1. unfold kPage. exact HNM. }
assert (CELLSH : YG0ncf.errb_cells_cf B (set_ly_sec ly (length (st_secs S)) a) (st_setsize (Z.of_nat (length s)) S1) (aview tfibsegs (w_H W') (held_mem lk mem'))).
{ apply (pk_cells_held lk ly (set_ly_sec ly (length (st_secs S)) a) (st_setsize (Z.of_nat (length s)) S1) (w_H W') mem' LK LY ltac:(rewrite EO; reflexivity)); [|exact CELLSM].
  intros b Hb. rewrite ED2, EC2, DAT1, CAP1 in Hb. apply pk_apres_view. apply pk_held_apres. apply PRESN. exact Hb. }

assert (AR4 : ARcf tfibsegs B (set_ly_sec ly (length (st_secs S)) a) (st_setsize (Z.of_nat (length s)) S1) Hp W' (held_mem lk mem') mdF).
{ rewrite EMF, EM1.
  apply (RepRelXcf.errb_rel_post B Hp (set_ly_sec ly (length (st_secs S)) a) S (st_setsize (Z.of_nat (length s)) S1) W' (held_mem lk mem) _ (held_mem lk mem') _ TS IMG1
           ltac:(rewrite EO; reflexivity) (PFA TS) (RepRelcf.rr_split_secs B (set_ly_sec ly (length (st_secs S)) a) S S1 (st_setsize (Z.of_nat (length s)) S1) Hp W' _ _ EFR2 GR2 EXS2 EC2 RS) EFR WF' XP2).
  - intros b Hb OW NO. unfold RepRelXcf.PW in NO. apply pk_aview_eq. apply pk_held_eq.
    apply FRM; rewrite unsigned_lit_small by lia.
    + intros Hs. apply (RepRelcf.rr_stack_not_owned B (set_ly_sec ly (length (st_secs S)) a) S Hp _ b M1); [rewrite LLO, LHI; lia | exact OW].
    + exact NO.
    + intros Hn. exact (pk_xs_not_owned (set_ly_sec ly (length (st_secs S)) a) S (st_setsize (Z.of_nat (length s)) S1) Hp _ a _ b M1 EFR XS1 XP2 Hn OW).
  - intros b Hb64 _ Hv.
    destruct (Z_le_dec 0xaa728 b) as [O1|O1]; destruct (Z_lt_dec b (0xaa728 + 56)) as [O2|O2];
    try (apply (pk_obj_view W' (held_mem lk mem') b); lia);
    destruct (Z_le_dec (spZ regs - 512) b) as [K1|K1]; destruct (Z_lt_dec b (spZ regs)) as [K2|K2];
    try (apply pk_apres_view; apply pk_held_apres; apply PRESA; [lia | apply RWIN; lia | lia]);
    destruct (Z_le_dec a b) as [N1|N1]; destruct (Z_lt_dec b (a + page_round_up_Z 65536)) as [N2|N2];
    try (apply pk_apres_view; apply pk_held_apres; apply PRESN; lia);
    (rewrite (pk_aview_eq (w_H W') (held_mem lk mem) (held_mem lk mem') b); [exact Hv|];
     apply pk_held_eq; apply FRM; rewrite unsigned_lit_small by lia; lia).
  - rewrite m_vmmaps_wvb. reflexivity.
  - rewrite m_vm_lazy_wvb. reflexivity.
  - unfold eager_used. rewrite m_vmmaps_wvb, m_vm_lazy_wvb. reflexivity.
  - intros b Hb _. assert (Hb' := Hb).
    unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb'.
    apply pk_held_eq. apply FRM; rewrite unsigned_lit_small by lia; [lia | lia | exact (GBAND b Hb)].
  - exact CELLSH. }

assert (IMK2 : forall b, 0x10000 <= b < 0x600000 -> ~ (0xaa728 <= b < 0xaa728 + 56) ->
  w_H W' (Z_to_bv 64 b) = w_H W (Z_to_bv 64 b) /\ mem' (Z_to_bv 64 b) = mem (Z_to_bv 64 b)).
{ intros b Hb Hn. split.
  - apply HHN. rewrite unsigned_lit_small by lia. lia.
  - apply FRM; rewrite unsigned_lit_small by lia; [lia | exact Hn | lia]. }
unfold errb_call_post.
exists (set_ly_sec ly (length (st_secs S)) a), regs', mem', mdF.
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ split; [exact EO|]. split; [exact EX|]. split; [exact LO1|]. split; [exact IMG1|]. split; [exact TS|].
  split; [rewrite TSD1; exact TSD|].
  split.
  { destruct LK as [LKn|(c & Hc & LKs)].
    - split; [left; exact LKn|]. split; [exact AR4|]. rewrite LKn. exact I.
    - split.
      { right. exists c. split; [exact Hc|]. rewrite LKs. unfold region_lock_addr. rewrite LSP. reflexivity. }
      split; [exact AR4|]. rewrite LKs. rewrite LKs in LKV. cbn [held_mem] in LKV |- *.
      apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 8 _); [|exact LKV].
      intros k Hk. unfold region_lock_addr in *. unfold kRegionInfoOff in *.
      change (2 ^ 37) with 137438953472 in *. split.
      + apply HHN. rewrite unsigned_lit_small by lia. lia.
      + apply FRM; rewrite unsigned_lit_small by lia; lia. }
  split. { unfold xs_mapped_cf in *. rewrite EMF, EM1, m_vmmaps_wvb. exact XM2. }
  split. { unfold errb_slack.
    destruct (find_sz (st_secs (st_setsize (Z.of_nat (length s)) S1)) 0) eqn:Ef;
    [exact WF' | exfalso; exact (HFIND eq_refl)]. }
  split. { exact (pk_qloose_frame S1 _ EFR2 (pk_qloose_frame S S1 EFR1 QL)). }
  split.
  { apply (YGcfInstBase.exh_cell_cf_frame B ly (set_ly_sec ly (length (st_secs S)) a) S
             (st_setsize (Z.of_nat (length s)) S1)
             (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W') mem') EXH).
    - intros c. rewrite (pk_exh_frame S1 _ EFR2 c). exact (pk_exh_frame S S1 EFR1 c).
    - intros c Hc. cbn [aoff aeval]. rewrite EX, LSP. unfold kRegionInfoOff.
      change (2 ^ 37) with 137438953472. apply pk_aview_HF.
      + apply HHN. rewrite unsigned_lit_small by lia. lia.
      + apply FRM; rewrite unsigned_lit_small by lia; lia. }
  split. { exact CELLSM. }
  split; [|exact HT'].
  { destruct IMGF as [IT IC ISL IV]. destruct IV as [F1 F2 FT JS JU].
    assert (L1 : (length FMT1_BYTES <= 100)%nat) by (apply Nat.leb_le; vm_compute; reflexivity).
    assert (L2 : (length FMT2_BYTES <= 100)%nat) by (apply Nat.leb_le; vm_compute; reflexivity).
    assert (L3 : (length (str_z "AddressSanitizer" ++ [0%Z]) <= 100)%nat) by (apply Nat.leb_le; vm_compute; reflexivity).
    constructor.
    - apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 8 _); [|exact IT]. intros k Hk. apply IMK2; unfold C_TOOLNAME; lia.
    - apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 8 _); [|exact IC]. intros k Hk. apply IMK2; unfold C_PFCB; lia.
    - apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 8 _); [|exact ISL]. intros k Hk. apply IMK2; unfold C_SILENT; lia.
    - constructor.
      + intros i Hi. apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 1 _); [|exact (F1 i Hi)]. intros k Hk. apply IMK2; unfold FMT_OOM1; lia.
      + intros i Hi. apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 1 _); [|exact (F2 i Hi)]. intros k Hk. apply IMK2; unfold FMT_OOM2; lia.
      + intros i Hi. apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 1 _); [|exact (FT i Hi)]. intros k Hk. apply IMK2; unfold A_TOOLNAME; lia.
      + apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 4 _); [|exact JS]. intros k Hk. apply IMK2; lia.
      + apply (pk_val_mem_HF (w_H W) (w_H W') mem mem' _ 4 _); [|exact JU]. intros k Hk. apply IMK2; lia. } }
split. { rewrite ES2. lia. }
split. { exact LE. }
split. { exact WLE. }
split. { intros r Hr. apply RP. exact Hr. }
split. { exact SIO. }
assert (AOXZ : forall b, 0 <= b < 2 ^ 64 -> ~ YGcfInstBase.AOX_cf B ly S b ->
  ~ YGcfInstBase.AOX_cf B (set_ly_sec ly (length (st_secs S)) a) (st_setsize (Z.of_nat (length s)) S1) b ->
  ~ (spZ regs - 512 <= b < spZ regs) ->
  w_H W' (Z_to_bv 64 b) = w_H W (Z_to_bv 64 b) /\ mem' (Z_to_bv 64 b) = mem (Z_to_bv 64 b)).
{ intros b Hb NA NA' NS.
  assert (NOBJ : ~ (0xaa728 <= b < 0xaa728 + 56)).
  { intros Ho. apply NA.
    apply (RepRelcf.errb_aox_obj B Hp ly S W (held_mem lk mem) md b TS ltac:(rewrite EO; reflexivity) AR).
    rewrite EO. exact Ho. }
  assert (NNEW : ~ (a <= b < a + page_round_up_Z 65536)).
  { intros Ho. apply NA'. unfold YGcfInstBase.AOX_cf, AOXm_cf. right. rewrite XS1.
    apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ho. }
  split; [apply HHN; rewrite unsigned_lit_small by lia; exact NNEW
        | apply FRM; rewrite unsigned_lit_small by lia; assumption]. }
split. { intros b Hb NA NA' NS. destruct (AOXZ b Hb NA NA' NS) as [E1 E2]. exact (pk_aview_HF _ _ _ _ b E1 E2). }
split. { intros x NA NA' NS. destruct (AOXZ (bv_unsigned x) (u64_range x) NA NA' NS) as [_ E2].
  rewrite Z_to_bv_bv_unsigned in E2. exact E2. }
split.
{ apply (MemnormT.memnorm_frame tfibsegs
    (fun b => (spZ regs - 512 <= b < spZ regs) \/ (0xaa728 <= b < 0xaa728 + 56)
           \/ (a <= b < a + page_round_up_Z 65536))).
  - intros x [Hx|[Hx|Hx]].
    + apply MemnormHitG.mn_safe_high. unfold kImgEnd, TASK_SIZE. lia.
    + apply MemnormSafepreset.mn_safe_rw. unfold TASK_SIZE. lia.
    + apply MemnormSafepreset.mn_safe_offimg; unfold TFIB_IMG_LO, TFIB_IMG_END, TASK_SIZE; lia.
  - intros x Hx. apply FRM; intros Hy; apply Hx; tauto. }
intros b Hb. apply PRESA; [lia | apply RWIN; exact Hb | lia].
Qed.

End a.
