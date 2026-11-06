(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 662 of its 760 lines of code are new or changed and 833 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase0Kit.v, with its module names changed; 1254 of its 1367 lines of code are new or changed and 647 lines of the source are left out. *)
(* Case 1 of the switch of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput (op & 3 = 1): the zero test and the
   scan of prev's rows, three segments of BoxBLxCase1Defs.v:
   - c1_seg_zero  (C1_I2 at 0x806d4 -> C1_I3 at 0x80700): bcmp (mac, ZERO, 6) at 0x806e4 (YCbq.v aj_bcmp_at with
     lh_bcmp; ZERO is A_OBJ 4, its bytes from BLxLib's blx_rom_bytes through arodata_okP, its shadow from blx_cells
     and blx_isv), the result to sp1 + 0x60, s7 = prev->n (the frame's word at F + 344), lf = -1 to sp1 + 0x20,
     held = bind = -1;
   - c1_seg_scan0 (C1_I3 -> C1_I4 or C1_I5): `blez s7` (prev->n = 0 skips the scan), else the loop registers;
   - c1_seg_scan  (C1_I4 -> C1_I5): the loop body at 0x80718 for row j (bgez s9; the zero-MAC test; the row index
     guard bltu 4, s11 is decided by the engine, j <= 4; the pointer-overflow guard against sp1 + 0x78 is refuted:
     F + 64 + 56 j + 6 <= F + 512 <= alloc_ceiling; bcmp (prev.box[j].mac, mac, 6) at 0x80748; bgez s3; bcmp
     (prev.box[j].mac, ZERO, 6) at 0x80784; the shadow check of prev.box[j].nch (0x8078c) passes by the frame's
     LSH_iter shadow (BoxBLxSeat.v lx_shent_frame); nch compared with sp1 + 0x50), by induction on bx_n bs - j.
     The trackers move as LLVMFuzzerTestOneInput_case1.v's c1_sh / c1_su (c1_sh_keep, c1_sh_v0, c1_sh_hit,
     c1_sh_miss, c1_su_keep, c1_su_hit, c1_su_miss).
   No branch of the range reaches a report, abort or trap body: the UBSan traps (0x80fac) behind the two guards
   are refuted as above, and the shadow check is decided by the engine's token run.

   The walk does not use BoxBLxSeat.v's lx_seat (whose spill and frame regions are writable, so a run would lose
   prev and mac): each straight-line piece is seated on its own small regions (c1s_seat, through PaRun's
   pa_entry_st_ok_full on lx_env), read-only except the two slots the zero test stores (0x20, 0x60); what the cuts
   carry about memory is kept as facts (c1s_mem, c1s_mem3) across the runs (frame_of) and the calls (the bcmp
   post's keep fact). Every value the engine meets that depends on a variable is an atom of lx_env's extra list;
   the loop's index j is a numeral in each of its five cases. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase1Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregRd LLVMFuzzerTestOneInput_case1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition C1S_SB : Z := 0x7fff8000.
Definition C1S_Bx : sv := SOff LA_SB 0.
Definition C1S_SPAN : Z * Z := (C1S_SB, C1S_SB + 2 ^ 44 - 1).
Definition c1s_spill (l : list (Z * sv)) : YP09.region := YP09.mkRegion (Some LA_SP) 0 0x98 0 0 (lx_slot_chunks l).
Definition c1s_win (o : Z) : YP09.region := YP09.mkRegion (Some LA_SP) o (o + 8) o (o + 8) [].
Definition c1s_frame (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some LA_F) 0 512 0 0 cs.
Definition c1s_ss (pc : Z) (sr : list sv) (rs : YP09.smem) (G : list (nat * afact)) : sstate :=
  mkSS pc sr rs None (mkFacts (LX_AF ++ G) [] []).
Definition c1s_ov (j : Z) : list (bv 5 * sv) :=
  [((24%bv : bv 5), SLit j); ((27%bv : bv 5), SLit j); ((26%bv : bv 5), SLit (12 + 56 * j))] ++ LX_OVP.
Definition C1S_SHD : list shent := [mkSHE LA_F 64 352].

Lemma c1s_nth_le_bytes : forall m z k, (k < m)%nat ->
  nth k (Z_to_le_bytes m z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction m as [|m IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth].
  - rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma c1s_rd4_bytes : forall bs k0, length bs = 288%nat -> 0 <= k0 -> k0 + 4 <= 288 ->
  0 <= Boxreg.rd4 bs k0 ->
  forall k, (k < 4)%nat -> nth (Z.to_nat k0 + k) bs (Z_to_bv 8 0) = Z_to_bv 8 (le_byte (Boxreg.rd4 bs k0) 4 k).
Proof.
  intros bs k0 HL H0 H4 Hn k Hk.
  assert (L : length (Boxreg.bsub bs k0 4) = 4%nat) by (apply Boxreg.bsub_length; lia).
  pose proof (Boxreg.rd4_range bs k0) as Hr.
  assert (Hv : bytes_le_to_Z (Boxreg.bsub bs k0 4) = Boxreg.rd4 bs k0).
  { pose proof (Boxreg.le4_range _ L) as R. unfold Boxreg.rd4 in *.
    revert Hn R. generalize (bytes_le_to_Z (Boxreg.bsub bs k0 4)). intros v Hn R.
    unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 32) with (2 ^ 32) in *.
    change (2 ^ 32 / 2) with (2 ^ 31) in *. Z.div_mod_to_equations. lia. }
  assert (E2 : nth (Z.to_nat k0 + k) bs (Z_to_bv 8 0) = nth k (Boxreg.bsub bs k0 4) (Z_to_bv 8 0)).
  { unfold Boxreg.bsub. rewrite nth_firstn. change (Z.to_nat 4) with 4%nat.
    destruct (Nat.ltb_spec k 4); [|lia]. rewrite nth_skipn. reflexivity. }
  rewrite E2. rewrite <- (BoxregRd.le_bytes_roundtrip (Boxreg.bsub bs k0 4)). rewrite L, Hv.
  rewrite c1s_nth_le_bytes by exact Hk.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, le_byte. change (bv_modulus 8) with 256.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small (Boxreg.rd4 bs k0) (2 ^ 32)) by lia.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma c1s_rdword_keep : forall (rd rd' : reader) a v,
  (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v Hk H. rewrite (rdword_ext rd rd' a Hk). exact H. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).

Lemma c1s_prev_val_mem : forall cx fp W3 ms bs k0, lprev cx fp W3 ms bs -> length bs = 288%nat ->
  0 <= k0 -> k0 + 4 <= 288 -> 0 <= Boxreg.rd4 bs k0 ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (lF cx fp + 64 + k0) 4 (Boxreg.rd4 bs k0).
Proof.
  intros cx fp W3 ms bs k0 HP HL H0 H4 Hn kk Hkk.
  pose proof (HP (k0 + Z.of_nat kk) ltac:(unfold LX_REG; lia)) as HA. unfold lview in HA.
  destruct (aview_byte SEGS _ _ _ _ HA) as (b & Hb & Hbv & _).
  replace (lF cx fp + 64 + k0 + Z.of_nat kk) with (lF cx fp + 64 + (k0 + Z.of_nat kk)) by lia. rewrite Hb. f_equal.
  replace b with (nth (Z.to_nat (k0 + Z.of_nat kk)) bs (Z_to_bv 8 0)) by (apply bv_eq; lia).
  replace (Z.to_nat (k0 + Z.of_nat kk)) with (Z.to_nat k0 + kk)%nat by lia.
  exact (c1s_rd4_bytes bs k0 HL H0 H4 Hn kk Hkk).
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Section d.
Hypothesis HY : lx_hyps B MT.
Section e.
Variable POST : lxcx -> world SEGS -> config -> Prop.
Variable i : nat.
Variable cx : lxcx.
Variables fp k acc : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variables r fab : Z.
Variables bs M : list byte.
Variable q : nat.
Variable nch : Z.
Hypothesis HB : lx_base B MT cx.
Hypothesis HFR : frames S3 = [(LX_CID, fp)].
Hypothesis HMO : mo_le MT (lc_S cx) S3 acc.
Hypothesis Hi64 : (i < 64)%nat.
Hypothesis Hk : k <= 1 + 2 * Z.of_nat i.
Hypothesis Hacc : acc <= LX_A1 MT + Z.of_nat i * LX_AI MT.
Hypothesis HBLK : lblk B cx ly3 S3 r.
Hypothesis HINV : Boxreg.boxreg_inv bs.
Hypothesis HFAB : Boxreg.bx_fabric bs = fab.
Hypothesis HGsp : lsp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= lsp0 cx /\ lsp0 cx <= 2 ^ 47 /\
  lsp0 cx - 287 <= lsp1 cx <= lsp0 cx - 256 /\ lsp1 cx mod 32 = 0.
Hypothesis HGF : 4096 <= lF cx fp /\ lF cx fp + 512 <= alloc_ceiling /\ in_app (lF cx fp) 512 /\
  lF cx fp mod 64 = 0 /\ lSH cx fp = SHADOW_OFF + lF cx fp / 8 /\ frame_addr ly3 LX_CID fp = lF cx fp.
Hypothesis HGr : 4096 <= r /\ r + 288 <= alloc_ceiling.
Hypothesis HGin : lc_n cx = 0 \/ (0 <= lc_p cx /\ lc_p cx + lc_n cx <= alloc_ceiling).

Definition c1s_cms (m : word -> option byte) : machine_state := mkst (lc_regs cx) (Z_to_bv 64 0) m (seg_rom SEGS).

Definition c1s_regs (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lsp1 cx) /\ getr regs 8 = w64 (lsp0 cx) /\ getr regs 9 = w64 (lsp1 cx) /\
  getr regs 3 = getr (lc_regs cx) 3 /\ getr regs 4 = getr (lc_regs cx) 4 /\
  getr regs 18 = w64 SHADOW_OFF /\ getr regs 22 = w64 (lSH cx fp) /\
  getr regs 20 = w64 r /\ getr regs 21 = w64 (lF cx fp + 64).

Definition c1s_mem (m : word -> option byte) : Prop :=
  lsaved cx W3 (c1s_cms m) /\ lshadow cx fp W3 (c1s_cms m) LSH_iter /\
  rdword (aview SEGS (w_H W3) m) (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp) /\
  lslot cx W3 (c1s_cms m) 0x10 (lF cx fp) /\ lslot cx W3 (c1s_cms m) 0x18 (lF cx fp) /\
  lslot cx W3 (c1s_cms m) 0x80 (lF cx fp) /\
  garr8 SEGS (mrestrict (w_H W3) m) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)) /\
  lreg W3 (c1s_cms m) r bs /\ lprev cx fp W3 (c1s_cms m) bs /\ lcur cx W3 (c1s_cms m) q /\
  lslots_loop cx fp W3 (c1s_cms m) r fab /\ lslot cx W3 (c1s_cms m) 0x58 (Z.of_nat i) /\
  lslot cx W3 (c1s_cms m) 0x48 (Boxreg.bx_n bs) /\ c1_read cx fp W3 (c1s_cms m) M nch.

Definition c1s_mem3 (nz : Z) (m : word -> option byte) : Prop :=
  c1s_mem m /\ c1_nz cx W3 (c1s_cms m) M nz /\ lslot cx W3 (c1s_cms m) 0x20 (2 ^ 64 - 1).

Definition c1s_J (m : word -> option byte) (md : Model) : Prop :=
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 m md k.

(* The bytes the memory facts speak about, and the two slots the zero test writes. *)
Definition c1s_at (a : Z) : Prop :=
  lsp1 cx <= a < 2 ^ 64 \/ (lc_n cx <> 0 /\ lc_p cx <= a < lc_p cx + lc_n cx) \/ lF cx fp <= a < lF cx fp + 512 \/
  lSH cx fp <= a < lSH cx fp + 64 \/ r <= a < r + 288.
Definition c1s_wr (a : Z) : Prop :=
  lsp1 cx + 0x20 <= a < lsp1 cx + 0x28 \/ lsp1 cx + 0x60 <= a < lsp1 cx + 0x68.

Lemma c1s_slot_keep : forall m m' off v,
  (forall a, c1s_at a -> ~ c1s_wr a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  0 <= off -> off + 8 <= 0x98 -> (off + 8 <= 0x20 \/ 0x28 <= off) -> (off + 8 <= 0x60 \/ 0x68 <= off) ->
  lslot cx W3 (c1s_cms m) off v -> lslot cx W3 (c1s_cms m') off v.
Proof.
  intros m m' off v KP H0 H1 H2 H3 H. pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs2 & Hs32).
  unfold lslot, lview in *. cbn [c1s_cms ms_mem mkst] in *.
  eapply (c1s_rdword_keep _ _ _ v); [|exact H]. intros q0 Hq. apply KP.
  - left. lia.
  - unfold c1s_wr. lia.
Qed.

Lemma c1s_SH : lSH cx fp = SHADOW_OFF + lF cx fp / 8 /\ 0 <= lF cx fp / 8 /\ lSH cx fp + 64 <= alloc_ceiling /\
  (lF cx fp + 512 <= SHADOW_OFF \/ lSH cx fp + 64 <= lF cx fp).
Proof.
  pose proof HGF as (HF0 & HF1 & HFapp & HF64 & HSH & _). pose proof asan_consts as (C1 & _).
  assert (D0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
  assert (D1 : 8 * (lF cx fp / 8) <= lF cx fp) by (apply Z.mul_div_le; lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. rewrite HSH. unfold SHADOW_OFF in *.
  split; [reflexivity|]. split; [exact D0|].
  destruct HFapp as [_ [Hlo | [Hhi1 Hhi2]]].
  - assert (lF cx fp / 8 <= 268430848) by (apply Z.div_le_upper_bound; lia). split; [lia|]. left. lia.
  - assert (lF cx fp / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia). split; [lia|]. right. lia.
Qed.

Lemma c1s_mem_keep_w : forall m m', c1s_mem m ->
  (forall a, c1s_at a -> ~ c1s_wr a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) -> c1s_mem m'.
Proof.
  intros m m' (SV & SH & FL & S10 & S18 & S80 & GI & RG & PV & CU & SL & S58 & S48 & RD) KP.
  pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs2 & Hs32). pose proof HGF as (HF0 & HF1 & HFapp & HF64 & _).
  pose proof HGr as (Hr0 & Hr1).
  pose proof c1s_SH as (ESH & D0 & HSH1 & HSH2). pose proof asan_consts as (C1 & _).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by reflexivity.
  assert (KS : forall off v, 0 <= off -> off + 8 <= 0x98 -> (off + 8 <= 0x20 \/ 0x28 <= off) ->
    (off + 8 <= 0x60 \/ 0x68 <= off) -> lslot cx W3 (c1s_cms m) off v -> lslot cx W3 (c1s_cms m') off v)
    by (intros; eapply c1s_slot_keep; eassumption).
  unfold c1s_mem.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]].
  - destruct SV as (Sra & Sj). unfold lsaved, lview in *. cbn [c1s_cms ms_mem mkst] in *. split.
    + eapply (c1s_rdword_keep _ _ _ _); [|exact Sra]. intros q0 Hq. apply KP; [left; lia | unfold c1s_wr; lia].
    + intros j Hj. eapply (c1s_rdword_keep _ _ _ _); [|exact (Sj j Hj)]. intros q0 Hq.
      apply KP; [left; lia | unfold c1s_wr; lia].
  - intros q0 Hq. unfold lview in *. cbn [c1s_cms ms_mem mkst] in *.
    assert (Z.of_nat (length LSH_iter) = 52) by reflexivity.
    rewrite KP; [exact (SH q0 Hq)| |].
    + right; right; right; left. lia.
    + unfold c1s_wr. destruct HSH2; lia.
  - rewrite Hfb in *. eapply (c1s_rdword_keep _ _ _ _); [|exact FL]. intros q0 Hq.
    apply KP; [right; right; left; lia | unfold c1s_wr; lia].
  - apply KS; [lia | lia | lia | lia | exact S10].
  - apply KS; [lia | lia | lia | lia | exact S18].
  - apply KS; [lia | lia | lia | lia | exact S80].
  - apply (garr8_frame SEGS _ _ _ _ GI). intros a Ha. rewrite length_map in Ha. apply (mbyte_of_aview SEGS).
    destruct HGin as [Hn0 | (Hp0 & Hp1)]; [unfold lc_n in Hn0; lia|].
    apply KP; [right; left; unfold lc_n in *; split; lia | unfold c1s_wr, lc_n in *; lia].
  - intros q0 Hq. unfold lview in *. cbn [c1s_cms ms_mem mkst] in *. rewrite KP; [exact (RG q0 Hq)| |].
    + right; right; right; right. unfold LX_REG in Hq. lia.
    + unfold c1s_wr, LX_REG in *. lia.
  - intros q0 Hq. unfold lview in *. cbn [c1s_cms ms_mem mkst] in *. rewrite KP; [exact (PV q0 Hq)| |].
    + right; right; left. unfold LX_REG in Hq. lia.
    + unfold c1s_wr, LX_REG in *. lia.
  - destruct CU as (Hq & C88 & C90). split; [exact Hq|].
    split; [apply KS; [lia | lia | lia | lia | exact C88] | apply KS; [lia | lia | lia | lia | exact C90]].
  - destruct SL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
    repeat split; apply KS; first [lia | assumption].
  - apply KS; [lia | lia | lia | lia | exact S58].
  - apply KS; [lia | lia | lia | lia | exact S48].
  - destruct RD as ((HML & MC) & S50 & Hn). split; [split; [exact HML|]|].
    + intros j Hj. unfold lview in *. cbn [c1s_cms ms_mem mkst] in *. rewrite KP; [exact (MC j Hj)| |].
      * right; right; left. lia.
      * unfold c1s_wr. lia.
    + split; [apply KS; [lia | lia | lia | lia | exact S50] | exact Hn].
Qed.

Lemma c1s_mem3_keep : forall nz m m', c1s_mem3 nz m ->
  (forall a, c1s_at a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) -> c1s_mem3 nz m'.
Proof.
  intros nz m m' (HM & (S60 & Hnz) & S20) KP. pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs2 & Hs32).
  assert (KS : forall off v, 0 <= off -> off + 8 <= 0x98 ->
    lslot cx W3 (c1s_cms m) off v -> lslot cx W3 (c1s_cms m') off v).
  { intros off v H0 H1 H. unfold lslot, lview in *. cbn [c1s_cms ms_mem mkst] in *.
    eapply (c1s_rdword_keep _ _ _ v); [|exact H]. intros q0 Hq. apply KP. left. lia. }
  split; [apply (c1s_mem_keep_w m m' HM); intros a Ha _; exact (KP a Ha)|].
  split; [split; [apply KS; [lia | lia | exact S60] | exact Hnz] | apply KS; [lia | lia | exact S20]].
Qed.

Lemma c1s_body : forall pc regs m, c1s_regs regs -> c1s_mem m ->
  c1_body B MT i cx fp pc k acc ly3 S3 W3 (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS)) r fab bs q.
Proof.
  intros pc regs m (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21)
    (SV & SH & FL & S10 & S18 & S80 & GI & RG & PV & CU & SL & S58 & S48 & RD).
  unfold c1_body. split.
  { unfold lx_body. do 6 (split; [reflexivity|]).
    split; [exact (conj G2 (conj G8 (conj G9 (conj G3 (conj G4 (conj G18 G22))))))|].
    split; [exact SV|]. split; [exact SH|]. split; [exact FL|].
    split; [exact S10|]. split; [exact S18|]. split; [exact S80 | exact GI]. }
  split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|].
  split; [exact HBLK|]. split; [exact RG|]. split; [exact HINV|]. split; [exact HFAB|].
  split; [exact PV|]. split; [exact CU|]. split; [exact SL|]. split; [exact S58|]. split; [exact S48|].
  split; [exact G20 | exact G21].
Qed.

Lemma c1s_land3 : forall regs m md nz, lx_from B MT POST (C1_I3 B MT i) ->
  c1s_regs regs -> getr regs 19 = w64 (-1) -> getr regs 23 = w64 (Boxreg.bx_n bs) -> getr regs 25 = w64 (-1) ->
  c1s_mem3 nz m -> c1s_J m md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C1_P3)) m (seg_rom SEGS)) md) (POST cx).
Proof.
  intros regs m md nz HN HR R19 R23 R25 (HM & HNZ & H20) HJ.
  apply (HN cx fp k acc ly3 S3 W3 (mkst regs (Z_to_bv 64 (BASE + C1_P3)) m (seg_rom SEGS)) md HB HJ HFR HMO).
  pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RD).
  exists q, r, fab, bs, M, nch, nz.
  split; [exact (c1s_body C1_P3 regs m HR HM)|]. split; [exact RD|]. split; [exact HNZ|].
  split; [exact H20|]. split; [exact R19|]. split; [exact R23 | exact R25].
Qed.

Lemma c1s_land4 : forall regs m md nz j h u, lx_from B MT POST (C1_I4 B MT i) ->
  c1s_regs regs -> c1s_mem3 nz m -> c1s_J m md ->
  0 <= j < Boxreg.bx_n bs -> LC1.c1_sh bs M nz j h -> LC1.c1_su bs nch j u ->
  getr regs 19 = w64 u -> getr regs 23 = w64 (Boxreg.bx_n bs) -> getr regs 24 = w64 j -> getr regs 25 = w64 h ->
  getr regs 26 = w64 (12 + 56 * j) -> getr regs 27 = w64 j ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C1_P4)) m (seg_rom SEGS)) md) (POST cx).
Proof.
  intros regs m md nz j h u HN HR (HM & HNZ & H20) HJ Hj HSH HSU R19 R23 R24 R25 R26 R27.
  apply (HN cx fp k acc ly3 S3 W3 (mkst regs (Z_to_bv 64 (BASE + C1_P4)) m (seg_rom SEGS)) md HB HJ HFR HMO).
  pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RD).
  exists q, r, fab, bs, M, nch, nz, j, h, u.
  split; [exact (c1s_body C1_P4 regs m HR HM)|]. split; [exact RD|]. split; [exact HNZ|].
  split; [exact H20|]. split; [exact Hj|]. split; [exact HSH|]. split; [exact HSU|].
  split; [exact R19|]. split; [exact R23|]. split; [exact R24|]. split; [exact R25|]. split; [exact R26 | exact R27].
Qed.

Lemma c1s_land5 : forall regs m md nz h u, lx_from B MT POST (C1_I5 B MT i) ->
  c1s_regs regs -> c1s_mem3 nz m -> c1s_J m md ->
  LC1.c1_sh bs M nz (Boxreg.bx_n bs) h -> LC1.c1_su bs nch (Boxreg.bx_n bs) u ->
  getr regs 19 = w64 u -> getr regs 25 = w64 h ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C1_P5)) m (seg_rom SEGS)) md) (POST cx).
Proof.
  intros regs m md nz h u HN HR (HM & HNZ & H20) HJ HSH HSU R19 R25.
  apply (HN cx fp k acc ly3 S3 W3 (mkst regs (Z_to_bv 64 (BASE + C1_P5)) m (seg_rom SEGS)) md HB HJ HFR HMO).
  pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RD).
  exists q, r, fab, bs, M, nch, nz, h, u.
  split; [exact (c1s_body C1_P5 regs m HR HM)|]. split; [exact RD|]. split; [exact HNZ|].
  split; [exact H20|]. split; [exact HSH|]. split; [exact HSU|]. split; [exact R19 | exact R25].
Qed.

Lemma c1s_lregs : forall regs pc m, c1s_regs regs -> lregs cx fp (mkst regs pc m (seg_rom SEGS)).
Proof.
  intros regs pc m (G2 & G8 & G9 & G3 & G4 & G18 & G22 & _).
  exact (conj G2 (conj G8 (conj G9 (conj G3 (conj G4 (conj G18 G22)))))).
Qed.

Lemma c1s_envE : forall regs ex, c1s_regs regs -> lx_E cx fp (lx_env cx fp regs ex).
Proof.
  intros regs ex HR. exact (lx_env_E cx fp (mkst regs (Z_to_bv 64 0) (fun _ => None) (seg_rom SEGS)) ex
    (c1s_lregs regs _ _ HR)).
Qed.

Lemma c1s_regs_ok : forall regs ex, c1s_regs regs -> regs_ok (lx_env cx fp regs ex) (lx_sr LX_OVP) regs.
Proof.
  intros regs ex HR. apply lx_regs_ok; [apply lx_regs_ok_atoms|].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & G21).
  exact (lx_ovp_ok cx fp (mkst regs (Z_to_bv 64 0) (fun _ => None) (seg_rom SEGS)) ex (c1s_lregs regs _ _ HR) G21).
Qed.

Lemma c1s_regs_ok_l : forall regs ex j, c1s_regs regs ->
  getr regs 24 = w64 j -> getr regs 27 = w64 j -> getr regs 26 = w64 (12 + 56 * j) ->
  regs_ok (lx_env cx fp regs ex) (lx_sr (c1s_ov j)) regs.
Proof.
  intros regs ex j HR R24 R27 R26. apply lx_regs_ok; [apply lx_regs_ok_atoms|].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & G21). unfold c1s_ov. apply Forall_app. split.
  - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd sv_denot];
      [rewrite R24 | rewrite R27 | rewrite R26]; reflexivity.
  - exact (lx_ovp_ok cx fp (mkst regs (Z_to_bv 64 0) (fun _ => None) (seg_rom SEGS)) ex (c1s_lregs regs _ _ HR) G21).
Qed.

Lemma c1s_ew2 : forall regs ex, c1s_regs regs -> bv_unsigned (ew (lx_env cx fp regs ex) LA_SP) = lsp1 cx.
Proof.
  intros regs ex HR. pose proof (c1s_envE regs ex HR) as (H2 & _). pose proof HGsp as (_ & Hs0 & Hs1 & Hs2 & _).
  pose proof asan_consts as (C1 & _). rewrite H2. apply unsigned_lit_small. lia.
Qed.

Lemma c1s_ew46 : forall regs ex, ew (lx_env cx fp regs ex) LA_F = w64 (lF cx fp).
Proof. intros regs ex. exact (lx_env_x cx fp regs ex 14 ltac:(lia)). Qed.

Lemma c1s_ew32 : forall regs ex, ew (lx_env cx fp regs ex) LA_SB = w64 SHADOW_OFF.
Proof. intros regs ex. exact (lx_env_x cx fp regs ex 0 ltac:(lia)). Qed.

Lemma c1s_u46 : forall regs ex, bv_unsigned (ew (lx_env cx fp regs ex) LA_F) = lF cx fp.
Proof.
  intros regs ex. rewrite c1s_ew46. pose proof HGF as (HF0 & HF1 & _). pose proof asan_consts as (C1 & _).
  apply unsigned_lit_small. lia.
Qed.

Lemma c1s_ewex : forall regs ex j, (j < 100)%nat -> ew (lx_env cx fp regs ex) (48 + j) = nth j ex (w64 0).
Proof. intros regs ex j Hj. exact (lx_env_ex cx fp regs ex j ltac:(lia)). Qed.

Lemma c1s_spill_ok : forall regs ex m l, c1s_regs regs ->
  lx_slots cx W3 (c1s_cms m) (lx_env cx fp regs ex) l ->
  YP09.region_ok SEGS (lx_env cx fp regs ex) (mrestrict (w_H W3) m) (c1s_spill l).
Proof.
  intros regs ex m l HR HL. pose proof HGsp as (_ & Hs0 & Hs1 & Hs2 & _). pose proof asan_consts as (C1 & _).
  unfold YP09.region_ok, c1s_spill. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite (c1s_ew2 regs ex HR). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  exact (lx_slot_chunks_ok cx W3 (c1s_cms m) _ l HL).
Qed.

Lemma c1s_frame_ok : forall regs ex m cs,
  Forall (YP09.chunk_ok SEGS (lx_env cx fp regs ex) (mrestrict (w_H W3) m) (lF cx fp)) cs ->
  YP09.region_ok SEGS (lx_env cx fp regs ex) (mrestrict (w_H W3) m) (c1s_frame cs).
Proof.
  intros regs ex m cs HC. pose proof HGF as (HF0 & HF1 & _). pose proof asan_consts as (C1 & _).
  unfold YP09.region_ok, c1s_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite (c1s_u46 regs ex). split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact HC].
Qed.

Lemma c1s_win_ok : forall regs ex m md o, c1s_regs regs -> c1s_J m md -> 0 <= o -> o + 8 <= 0x98 ->
  YP09.region_ok SEGS (lx_env cx fp regs ex) (mrestrict (w_H W3) m) (c1s_win o).
Proof.
  intros regs ex m md o HR HJ H0 H1. pose proof HGsp as (_ & Hs0 & Hs1 & Hs2 & _). pose proof asan_consts as (C1 & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  unfold YP09.region_ok, c1s_win. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite (c1s_ew2 regs ex HR). split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o' Ho. apply (apresent_writable SEGS). apply HJpres. unfold LX_STK. lia.
Qed.

Lemma c1s_slot_at : forall regs ex m off n v, lslot cx W3 (c1s_cms m) off v ->
  ew (lx_env cx fp regs ex) n = w64 v -> 0 <= v < 2 ^ 64 ->
  rdword (lview W3 (c1s_cms m)) (lsp1 cx + off) = Some (bv_unsigned (sv_denot (lx_env cx fp regs ex) (SOff n 0))).
Proof.
  intros regs ex m off n v H Hn Hv. apply (lx_slot_atom cx W3 (c1s_cms m) _ off n v 0); [rewrite Z.add_0_r; exact H | exact Hn | exact Hv | lia].
Qed.

Lemma c1s_seat : forall regs m md ex pc sr rs G,
  c1s_regs regs -> c1s_J m md -> regs_ok (lx_env cx fp regs ex) sr regs ->
  YP09.regions_wf rs = true -> Forall (YP09.region_ok SEGS (lx_env cx fp regs ex) (mrestrict (w_H W3) m)) rs ->
  YP09.pairwise_disjoint (lx_env cx fp regs ex) rs -> atoms_ok (lx_env cx fp regs ex) G ->
  st_ok_pi SEGS VAL (lx_env cx fp regs ex) (c1s_ss pc sr rs G)
    (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))).
Proof.
  intros regs m md ex pc sr rs G HR HJ Hsr Hwf Hok Hd HG. rewrite restrict_mkst_fx.
  apply pa_entry_st_ok_full; [exact Hsr | exact Hwf | exact Hok | exact Hd |].
  split; [|split; exact I]. cbn [f_atoms]. apply atoms_ok_app; [|exact HG].
  exact (lx_af_ok B MT (lh_laws B MT HY) cx fp W3 (c1s_cms m) ly3 S3 md k HB HJ HFR _ (c1s_envE regs ex HR)).
Qed.

Lemma c1s_bt_ge : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. rewrite (Boxreg.lts_lit x y Hx Hy). reflexivity. Qed.

Lemma c1s_bt_lt : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. exact (Boxreg.lts_lit x y Hx Hy). Qed.

Lemma c1s_reg_run : forall regs ex E' ss ms (H : word -> bool) (rr : bv 5) (n : nat) c,
  st_ok_pi SEGS VAL E' ss (restrict H ms) ->
  (forall a, (a < 240)%nat -> ew E' a = ew (lx_env cx fp regs ex) a) ->
  sr_get (ss_regs ss) rr = SOff n c -> (n < 240)%nat ->
  getr (ms_regs ms) rr = Z_to_bv 64 (bv_unsigned (ew (lx_env cx fp regs ex) n) + c).
Proof.
  intros regs ex E' ss ms H rr n c HS HA Hr Hn.
  rewrite (st_ok_pi_restrict_reg H E' ss ms rr HS), Hr. cbn [sv_denot]. rewrite (HA n Hn). reflexivity.
Qed.

Lemma c1s_regs_run : forall regs ex E' ss ms (H : word -> bool),
  c1s_regs regs -> st_ok_pi SEGS VAL E' ss (restrict H ms) ->
  (forall a, (a < 240)%nat -> ew E' a = ew (lx_env cx fp regs ex) a) ->
  map (sr_get (ss_regs ss)) [2%bv; 8%bv; 9%bv; 3%bv; 4%bv; 18%bv; 22%bv; 20%bv; 21%bv] =
    [SOff 2 0; SOff 8 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 32 0; SOff 22 0; SOff 20 0; SOff 46 64] ->
  c1s_regs (ms_regs ms).
Proof.
  intros regs ex E' ss ms H HR HS HA Hm. cbn [map] in Hm.
  injection Hm as M2 M8 M9 M3 M4 M18 M22 M20 M21.
  pose proof HR as (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21).
  pose proof (c1s_envE regs ex HR) as (E2 & E8 & E3 & E4 & E22 & E32 & _ & E46 & _).
  assert (RR : forall (rr : bv 5) n c, sr_get (ss_regs ss) rr = SOff n c -> (n < 240)%nat ->
    getr (ms_regs ms) rr = Z_to_bv 64 (bv_unsigned (ew (lx_env cx fp regs ex) n) + c))
    by (intros rr n c Hr Hn; exact (c1s_reg_run regs ex E' ss ms H rr n c HS HA Hr Hn)).
  assert (W0 : forall w : word, Z_to_bv 64 (bv_unsigned w + 0) = w) by (intros w; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
  unfold c1s_regs.
  split; [rewrite (RR _ _ _ M2 ltac:(lia)), W0; exact E2|].
  split; [rewrite (RR _ _ _ M8 ltac:(lia)), W0; exact E8|].
  split; [rewrite (RR _ _ _ M9 ltac:(lia)), W0; exact E2|].
  split; [rewrite (RR _ _ _ M3 ltac:(lia)), W0; exact E3|].
  split; [rewrite (RR _ _ _ M4 ltac:(lia)), W0; exact E4|].
  split; [rewrite (RR _ _ _ M18 ltac:(lia)), W0; exact E32|].
  split; [rewrite (RR _ _ _ M22 ltac:(lia)), W0; exact E22|].
  split; [rewrite (RR _ _ _ M20 ltac:(lia)), W0, (lx_env_reg cx fp regs ex 20 (20%bv : bv 5)) by reflexivity; exact G20|].
  rewrite (RR _ _ _ M21 ltac:(lia)). change (ew (lx_env cx fp regs ex) 46) with (ew (lx_env cx fp regs ex) LA_F). rewrite E46. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  apply Zplus_mod_idemp_l.
Qed.

Lemma c1s_reg_keep : forall regs ex E' ss ms (H : word -> bool) (rr : bv 5) (n : nat),
  st_ok_pi SEGS VAL E' ss (restrict H ms) -> (forall a, (a < 240)%nat -> ew E' a = ew (lx_env cx fp regs ex) a) ->
  sr_get (ss_regs ss) rr = SOff n 0 -> Z.of_nat n = bv_unsigned rr -> getr (ms_regs ms) rr = getr regs rr.
Proof.
  intros regs ex E' ss ms H rr n HS HA Hr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hrr.
  change (bv_modulus 5) with 32 in Hrr.
  rewrite (c1s_reg_run regs ex E' ss ms H rr n 0 HS HA Hr ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned.
  exact (lx_env_reg cx fp regs ex n rr Hn).
Qed.

Lemma c1s_reg_lit : forall E' ss ms (H : word -> bool) (rr : bv 5) z,
  st_ok_pi SEGS VAL E' ss (restrict H ms) -> sr_get (ss_regs ss) rr = SLit z -> getr (ms_regs ms) rr = Z_to_bv 64 z.
Proof. intros E' ss ms H rr z HS Hr. rewrite (st_ok_pi_restrict_reg H E' ss ms rr HS), Hr. reflexivity. Qed.

Ltac c1s_sh0 := first [ left; split; [reflexivity | right; intros; exfalso; lia]
                      | left; split; [reflexivity | intros; exfalso; lia] ].

Ltac c1s_lit := unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity.

Lemma c1s_scan0_pt : forall regs m md nz, lx_from B MT POST (C1_I4 B MT i) -> lx_from B MT POST (C1_I5 B MT i) ->
  c1s_regs regs -> getr regs 19 = w64 (-1) -> getr regs 23 = w64 (Boxreg.bx_n bs) -> getr regs 25 = w64 (-1) ->
  c1s_mem3 nz m -> c1s_J m md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C1_P3)) m (seg_rom SEGS)) md) (POST cx).
Proof.
  intros regs m md nz HN4 HN5 HR R19 R23 R25 HM HJ.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof HINV as ((_ & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
  pose (RUNTO := paj_run_to B LAWS). pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
  pose proof (c1s_seat regs m md [] C1_P3 (lx_sr LX_OVP) [] [] HR HJ (c1s_regs_ok regs [] HR) eq_refl (Forall_nil _) I I) as HS.
  assert (HEI : img_env VAL A_LIM (lx_env cx fp regs [])) by apply lx_env_img.
  assert (SHOK : sh_ok SEGS C1S_Bx [] (lx_env cx fp regs []) (mrestrict (w_H W3) m)) by apply Forall_nil.
  assert (EF23 : ew (lx_env cx fp regs []) 23 = w64 (Boxreg.bx_n bs))
    by (rewrite (lx_env_reg cx fp regs [] 23 (23%bv : bv 5)) by reflexivity; exact R23).
  remember (lx_env cx fp regs []) as E eqn:HE.
  assert (AG : forall a, (a < 240)%nat -> ew E a = ew (lx_env cx fp regs []) a) by (intros a _; rewrite HE; reflexivity).
  unfold c1s_J in HJ. unfold c1s_ss in HS.
  psrr_branch_tok RUN BR HS SHOK C1S_SPAN;
    rewrite lx_sv_SOff0, EF23 in Hc; cbn [sv_denot] in Hc; unfold w64 in Hc; rewrite c1s_bt_ge in Hc by lia.
  - apply negb_true_iff, Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK C1S_SPAN C1_P5; [apply awr_ok_nil |].
    assert (EM : ms_mem ms = m) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity).
    pmkst HS. rewrite EM in HJ |- *.
    apply (c1s_land5 (ms_regs ms) m _ nz (-1) (-1) HN5).
    + exact (c1s_regs_run regs [] E _ ms (w_H W3) HR HS AG eq_refl).
    + exact HM.
    + exact HJ.
    + replace (Boxreg.bx_n bs) with 0 by lia. c1s_sh0.
    + replace (Boxreg.bx_n bs) with 0 by lia. c1s_sh0.
    + rewrite (c1s_reg_keep regs [] E _ ms (w_H W3) (19%bv : bv 5) 19 HS AG eq_refl eq_refl). exact R19.
    + rewrite (c1s_reg_keep regs [] E _ ms (w_H W3) (25%bv : bv 5) 25 HS AG eq_refl eq_refl). exact R25.
  - apply negb_false_iff, Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK C1S_SPAN C1_P4; [apply awr_ok_nil |].
    assert (EM : ms_mem ms = m) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity).
    pmkst HS. rewrite EM in HJ |- *.
    apply (c1s_land4 (ms_regs ms) m _ nz 0 (-1) (-1) HN4).
    + exact (c1s_regs_run regs [] E _ ms (w_H W3) HR HS AG eq_refl).
    + exact HM.
    + exact HJ.
    + lia.
    + c1s_sh0.
    + c1s_sh0.
    + rewrite (c1s_reg_lit E _ ms (w_H W3) (19%bv : bv 5) _ HS eq_refl). c1s_lit.
    + rewrite (c1s_reg_keep regs [] E _ ms (w_H W3) (23%bv : bv 5) 23 HS AG eq_refl eq_refl). exact R23.
    + rewrite (c1s_reg_lit E _ ms (w_H W3) (24%bv : bv 5) _ HS eq_refl). c1s_lit.
    + rewrite (c1s_reg_lit E _ ms (w_H W3) (25%bv : bv 5) _ HS eq_refl). c1s_lit.
    + rewrite (c1s_reg_lit E _ ms (w_H W3) (26%bv : bv 5) _ HS eq_refl). c1s_lit.
    + rewrite (c1s_reg_lit E _ ms (w_H W3) (27%bv : bv 5) _ HS eq_refl). c1s_lit.
Qed.

Definition c1s_obj (m : word -> option byte) (x : Z) : Prop :=
  0 <= x /\ x + 6 <= alloc_ceiling /\ amem_range x 6 /\
  (forall a, x <= a < x + 6 -> aview SEGS (w_H W3) m a <> None) /\
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF x 6 /\ shadow_hull_vis (aview SEGS (w_H W3) m) x 6.

Lemma c1s_bcmp : forall regsT memT mdT x y ret,
  c1s_J memT mdT ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 6 ->
  getr regsT 2 = w64 (lsp1 cx) -> getr regsT 3 = getr (lc_regs cx) 3 -> getr regsT 4 = getr (lc_regs cx) 4 ->
  getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  c1s_obj memT x -> c1s_obj memT y ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BB___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2 /\ c1s_J mem2 md2 /\
       aregs_preserved regsT regs2 /\
       (bv_unsigned (getr regs2 10) = 0 <->
          forall j, 0 <= j < 6 -> aview SEGS (w_H W3) memT (x + j) = aview SEGS (w_H W3) memT (y + j)) /\
       (forall a, c1s_at a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memT a)).
Proof.
  intros regsT memT mdT x y ret HJ H10 H11 H12 H2 H3 H4 H1 Hret0 Hret2
    (Hx0 & Hx1 & Hxm & Hxv & Hxr & Hxh) (Hy0 & Hy1 & Hym & Hyv & Hyr & Hyh).
  pose proof (lh_laws B MT HY) as LAWS. pose proof pa_segs_low as Hsegs.
  pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs2 & Hs32). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
  pose proof c1s_SH as (ESH & D0 & HSH1 & HSH2).
  pose proof HGF as (HF0 & HF1 & HFapp & HF64 & _). pose proof HGr as (Hr0 & Hr1).
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (HspT : spZ regsT = lsp0 cx + (lsp1 cx - lsp0 cx)).
  { unfold spZ. rewrite H2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (Hmod : (lsp1 cx - lsp0 cx) mod 16 = 0).
  { apply Z.mod_divide in Hs32; [|lia]. apply Z.mod_divide in Hs16; [|lia].
    destruct Hs32 as [a ->]. destruct Hs16 as [b Hb]. rewrite Hb. apply Z.mod_divide; [lia|]. exists (2 * a - b). lia. }
  eapply SRr_mono.
  { eapply (aj_bcmp_at SEGS B LAWS Hsegs _ (lh_bcmp B MT HY) W3 regsT memT LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx)
      (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 mdT k x y 6 (lsp1 cx - lsp0 cx) (Z_to_bv 64 (BASE + ret)) HJ
      H10 H11 H12 ltac:(lia) Hx0 ltac:(lia) Hy0 ltac:(lia) HspT Hmod ltac:(lia) ltac:(unfold LX_STK; lia)).
    - rewrite H3. exact Hgp.
    - rewrite H4. exact Htp.
    - exact H1.
    - exact (ret_ok_codeptr_v ret Hret0 Hret2).
    - intros a Ha. split; [exact (Hxv a Ha)|]. rewrite HspT, Hes. lia.
    - intros a Ha. split; [exact (Hyv a Ha)|]. rewrite HspT, Hes. lia.
    - intros a Ha. rewrite Hes. lia.
    - intros a Ha. rewrite Hes. lia.
    - exact Hxm.
    - exact Hym.
    - exact Hxr.
    - intros _. exact Hxh.
    - exact Hyr.
    - intros _. exact Hyh. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & _).
  split; [reflexivity|]. exists regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split.
  - rewrite Hv. rewrite <- Hcmp. split.
    + intros H0. apply bv_eq. rewrite H0. reflexivity.
    + intros ->. reflexivity.
  - intros a Ha. unfold c1s_at in Ha. rewrite Hes in Hfr.
    assert (Hag : 0 <= a < 2 ^ 64 /\ ~ (lsp0 cx + (lsp1 cx - lsp0 cx) - 2 * 4096 <= a < lsp0 cx + (lsp1 cx - lsp0 cx))).
    { clear - Ha HGin Hs0 Hs1 Hs2 C1 HF0 HF1 HSH1 Hr0 Hr1 D0 ESH. unfold lc_n, SHADOW_OFF in *.
      destruct HGin as [Hn0 | (Hp0 & Hp1)]; lia. }
    exact (Hfr a (proj1 Hag) (proj2 Hag)).
Qed.

Lemma c1s_bytes_eq : forall (l1 l2 : list byte) x y m, length l1 = 6%nat -> length l2 = 6%nat ->
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) m (x + j) = Some (bv_unsigned (nth (Z.to_nat j) l1 (Z_to_bv 8 0)))) ->
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) m (y + j) = Some (bv_unsigned (nth (Z.to_nat j) l2 (Z_to_bv 8 0)))) ->
  ((forall j, 0 <= j < 6 -> aview SEGS (w_H W3) m (x + j) = aview SEGS (w_H W3) m (y + j)) <-> l1 = l2).
Proof.
  intros l1 l2 x y m H1 H2 HXv HYv. split.
  - intros Heq. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [rewrite H1, H2; reflexivity|].
    intros kk Hkk. rewrite H1 in Hkk. pose proof (Heq (Z.of_nat kk) ltac:(lia)) as Q.
    rewrite HXv, HYv in Q by lia. rewrite Nat2Z.id in Q. injection Q as Q. apply bv_eq. exact Q.
  - intros <- j Hj. rewrite HXv, HYv by exact Hj. reflexivity.
Qed.

Lemma c1s_mac_bytes : forall bs0 j0 kk, length bs0 = 288%nat -> 0 <= j0 <= 4 -> 0 <= kk < 6 ->
  nth (Z.to_nat kk) (Boxreg.bx_mac bs0 j0) (Z_to_bv 8 0) = nth (Z.to_nat (56 * j0 + kk)) bs0 (Z_to_bv 8 0).
Proof.
  intros bs0 j0 kk HL Hj Hkk. unfold Boxreg.bx_mac, Boxreg.bsub. rewrite nth_firstn.
  destruct (Nat.ltb_spec (Z.to_nat kk) (Z.to_nat 6)); [|lia]. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma c1s_zero6_bytes : forall kk, 0 <= kk < 6 -> bv_unsigned (nth (Z.to_nat kk) Boxreg.zero6 (Z_to_bv 8 0)) = 0.
Proof.
  intros kk Hkk. assert (Hc : kk = 0 \/ kk = 1 \/ kk = 2 \/ kk = 3 \/ kk = 4 \/ kk = 5) by lia.
  destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; reflexivity.
Qed.

Lemma c1s_obj_frame : forall m md lo, c1s_J m md -> lshadow cx fp W3 (c1s_cms m) LSH_iter ->
  (lo = 32 \/ (64 <= lo /\ lo + 6 <= 352)) ->
  (forall a, lF cx fp + lo <= a < lF cx fp + lo + 6 -> aview SEGS (w_H W3) m a <> None) ->
  c1s_obj m (lF cx fp + lo).
Proof.
  intros m md lo HJ Hsh Hlo Hv. pose proof (lh_laws B MT HY) as LAWS.
  pose proof HGF as (HF0 & HF1 & HFapp & HF64 & HSH & HFA). pose proof asan_consts as (C1 & _).
  assert (Hfin : In (LX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by reflexivity.
  pose proof HJ as (HAR & _).
  unfold c1s_obj. split; [lia|]. split; [lia|].
  split; [exact (amem_range_sub_app (lF cx fp) 512 (lF cx fp + lo) 6 HFapp HF1 ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [exact Hv|]. split.
  - assert (HU32 : U (lx_env cx fp (lc_regs cx) []) (SOff LA_SB 0) = SHADOW_OFF).
    { unfold U. rewrite lx_sv_SOff0, c1s_ew32. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
    assert (HU46 : U (lx_env cx fp (lc_regs cx) []) (SOff LA_F 0) = lF cx fp).
    { unfold U. rewrite lx_sv_SOff0. apply c1s_u46. }
    destruct (lx_shent_frame B MT LAWS cx fp W3 (c1s_cms m) ly3 S3 md k HB HJ HFR (lx_env cx fp (lc_regs cx) []) lo (lo + 6)
      HU32 HU46 Hsh ltac:(lia)) as [HRA _].
    cbn [she_m she_lo she_hi] in HRA. rewrite HU32, HU46 in HRA. cbn [c1s_cms ms_mem mkst] in HRA.
    rewrite <- (aview_rd_of SEGS) in HRA. replace (lo + 6 - lo) with 6 in HRA by lia. exact HRA.
  - apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 m md LX_CID fp); [exact HAR | exact Hfin | rewrite HFA; lia | rewrite HFA, Hfb; lia | lia].
Qed.

Lemma c1s_zero_view : forall m md, c1s_J m md ->
  forall j, 0 <= j < 6 -> aview SEGS (w_H W3) m (VAL (A_OBJ 4) + j) = Some 0.
Proof.
  intros m md HJ j Hj. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof (lx_arodata_kept B LX_STK (lsp0 cx) (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)]
    ly3 S3 W3 m md k HJ HRO) as HRO3.
  pose proof (blx_rom_bytes B (lh_glob B MT HY) (4%nat, [0; 0; 0; 0; 0; 0]) ltac:(cbn; tauto)) as HZB.
  cbn [fst snd] in HZB. destruct (HZB j ltac:(cbn [length]; lia)) as (Hrom & Hown & Herr & Hb).
  rewrite (HRO3 _ (or_introl Hrom) Hown Herr), Hb.
  assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
  destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; reflexivity.
Qed.

Lemma c1s_obj_zero : forall m md, c1s_J m md -> c1s_obj m (VAL (A_OBJ 4)).
Proof.
  intros m md HJ. pose proof (lh_glob B MT HY) as GL. pose proof asan_consts as (C1 & _).
  pose proof HJ as (HAR & _).
  pose proof (blx_marg B GL (4%nat, 6) ltac:(cbn; tauto)) as (HZ1 & HZ2). cbn [fst snd] in HZ1, HZ2.
  pose proof (blx_al B GL (4%nat, 6) ltac:(cbn; tauto)) as HZal. cbn [fst] in HZal.
  unfold IMG_HI in HZ2.
  unfold c1s_obj. split; [lia|]. split; [lia|]. split; [left; unfold kLowMemEnd in *; lia|]. split.
  { intros a Ha. replace a with (VAL (A_OBJ 4) + (a - VAL (A_OBJ 4))) by lia.
    rewrite (c1s_zero_view m md HJ) by lia. discriminate. }
  split.
  - apply (block_shadow_range _ _ (VAL (A_OBJ 4)) 6); [| lia | lia].
    assert (Hal8 : VAL (A_OBJ 4) mod 8 = 0).
    { apply Z.mod_divide in HZal; [|lia]. destruct HZal as [c Hc]. rewrite Hc. apply Z.mod_divide; [lia|]. exists (4 * c). lia. }
    split; [exact Hal8|]. split; [lia|]. intros i0 Hi0. change ((6 + 7) / 8) with 1 in Hi0. assert (i0 = 0) by lia. subst i0.
    pose proof (am_const B ly3 S3 _ (proj1 HAR)) as HC. rewrite Forall_forall in HC.
    pose proof (HC (z1 (ANum (shadow_addr (VAL (A_OBJ 4)))) 6)
      (blx_cells B GL ly3 _ ltac:(cbn [lx_glob_cells flat_map LX_GLOBS fst snd]; left; reflexivity))) as Hcell.
    unfold cell_holds in Hcell. cbn [c_at c_val c_w z1 c1 aeval] in Hcell.
    specialize (Hcell 0%nat ltac:(lia)). rewrite Z.add_0_r in Hcell.
    rewrite Z.add_0_r. unfold shadow_of_addr. change (SHADOW_OFF + VAL (A_OBJ 4) / 8) with (shadow_addr (VAL (A_OBJ 4))).
    rewrite Hcell. reflexivity.
  - exact (ro_hull SEGS B ly3 S3 W3 m md (VAL (A_OBJ 4)) 6 (blx_isv B GL) HAR ltac:(lia) HZ1 HZ2).
Qed.

Lemma c1s_aview_frame : forall E rs m m' a,
  frame_of E rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') -> 0 <= a < 2 ^ 64 -> ~ YP09.in_wrange E rs a ->
  aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Proof.
  intros E rs m m' a HF Ha Hn. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

Lemma c1s_ew48 : forall regs ex, ew (lx_env cx fp regs ex) 48 = nth 0 ex (w64 0).
Proof. intros regs ex. exact (lx_env_ex cx fp regs ex 0 ltac:(lia)). Qed.
Lemma c1s_ew49 : forall regs ex, ew (lx_env cx fp regs ex) 49 = nth 1 ex (w64 0).
Proof. intros regs ex. exact (lx_env_ex cx fp regs ex 1 ltac:(lia)). Qed.
Lemma c1s_ew50 : forall regs ex, ew (lx_env cx fp regs ex) 50 = nth 2 ex (w64 0).
Proof. intros regs ex. exact (lx_env_ex cx fp regs ex 2 ltac:(lia)). Qed.
Lemma c1s_ew51 : forall regs ex, ew (lx_env cx fp regs ex) 51 = nth 3 ex (w64 0).
Proof. intros regs ex. exact (lx_env_ex cx fp regs ex 3 ltac:(lia)). Qed.

Lemma c1s_afact : forall E n v lo hi, ew E n = w64 v -> lo <= v <= hi -> 0 <= v < 2 ^ 64 -> afact_ok E n (mkAF lo hi 0).
Proof.
  intros E n v lo hi He Hv Hr. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite He. unfold w64.
  rewrite unsigned_lit_small by exact Hr. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

Lemma c1s_n_range : 0 <= Boxreg.bx_n bs <= 5.
Proof. pose proof HINV as ((_ & HB1 & _) & _). exact HB1. Qed.

Lemma c1s_len : length bs = 288%nat.
Proof. pose proof HINV as ((HL & _) & _). exact HL. Qed.

Lemma c1s_n_chunk : forall regs ex m, (nth 0 ex (w64 0)) = w64 (Boxreg.bx_n bs) -> lprev cx fp W3 (c1s_cms m) bs ->
  YP09.chunk_ok SEGS (lx_env cx fp regs ex) (mrestrict (w_H W3) m) (lF cx fp) (YP09.mkChunk 344 (CVal 4 (SOff 48 0))).
Proof.
  intros regs ex m Hex HP. pose proof c1s_n_range as Hn. pose proof c1s_len as HL.
  apply (chunk_ok_val SEGS _ _ (lF cx fp) 344 4 (SOff 48 0) (Boxreg.bx_n bs)).
  - rewrite lx_sv_SOff0, c1s_ew48, Hex. reflexivity.
  - cbn [Z.of_N]. lia.
  - cbn. lia.
  - replace (lF cx fp + 344) with (lF cx fp + 64 + 280) by lia.
    exact (c1s_prev_val_mem cx fp W3 (c1s_cms m) bs 280 HP HL ltac:(lia) ltac:(lia) (proj1 Hn)).
Qed.

Lemma c1s_regs_pres : forall regs regs', aregs_preserved regs regs' -> c1s_regs regs -> c1s_regs regs'.
Proof.
  intros regs regs' HP (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21).
  assert (K : forall (r0 : bv 5) z, r0 = Z_to_bv 5 z -> acallee_saved z -> getr regs' r0 = getr regs r0)
    by (intros r0 z -> Hz; apply HP; exact Hz).
  unfold c1s_regs.
  split; [etransitivity; [apply (K _ 2); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact G2]|].
  split; [etransitivity; [apply (K _ 8); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact G8]|].
  split; [etransitivity; [apply (K _ 9); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact G9]|].
  split; [etransitivity; [apply (K _ 3); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact G3]|].
  split; [etransitivity; [apply (K _ 4); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact G4]|].
  split; [etransitivity; [apply (K _ 18); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact G18]|].
  split; [etransitivity; [apply (K _ 22); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact G22]|].
  split; [etransitivity; [apply (K _ 20); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact G20]|].
  etransitivity; [apply (K _ 21); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact G21].
Qed.

Lemma c1s_regs_runc : forall regs ex E' ss pc ms (H : word -> bool),
  c1s_regs regs -> st_ok SEGS E' (setpc ss pc) (restrict H ms) ->
  (forall a, (a < 240)%nat -> ew E' a = ew (lx_env cx fp regs ex) a) ->
  map (sr_get (ss_regs ss)) [2%bv; 8%bv; 9%bv; 3%bv; 4%bv; 18%bv; 22%bv; 20%bv; 21%bv] =
    [SOff 2 0; SOff 8 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 32 0; SOff 22 0; SOff 20 0; SOff 46 64] ->
  c1s_regs (ms_regs ms).
Proof.
  intros regs ex E' ss pc ms H HR HS HA Hm.
  assert (HS' : st_ok_pi SEGS VAL E' (setpc ss (pc - BASE)) (restrict H ms)).
  { unfold st_ok_pi, abs_ss. unfold setpc at 2 3. cbn [ss_pc]. replace (BASE + (pc - BASE)) with pc by lia.
    exact HS. }
  exact (c1s_regs_run regs ex E' _ ms H HR HS' HA Hm).
Qed.

Lemma c1s_zero2_pt : forall regs m md, lx_from B MT POST (C1_I3 B MT i) ->
  c1s_regs regs -> c1s_mem m -> c1s_J m md ->
  (bv_unsigned (getr regs 10) = 0 <-> M = Boxreg.zero6) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x73c)) m (seg_rom SEGS)) md) (POST cx).
Proof.
  intros regs m md HN3 HR HM HJ Hv.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof c1s_n_range as Hn.
  pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs2 & Hs32). pose proof asan_consts as (C1 & _).
  pose (RUNTO := paj_run_to B LAWS).
  pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & HPV & _).
  pose proof (c1s_seat regs m md [w64 (Boxreg.bx_n bs)] 0x73c (lx_sr LX_OVP)
    [c1s_win 0x20; c1s_win 0x60; c1s_frame [YP09.mkChunk 344 (CVal 4 (SOff 48 0))]] [(48%nat, mkAF 0 5 0)]
    HR HJ (c1s_regs_ok regs _ HR) eq_refl) as HS.
  specialize (HS ltac:(repeat apply Forall_cons; try apply Forall_nil;
      [ apply (c1s_win_ok regs _ m md 0x20 HR HJ); lia
      | apply (c1s_win_ok regs _ m md 0x60 HR HJ); lia
      | apply (c1s_frame_ok regs _ m); apply Forall_cons; [|apply Forall_nil];
        exact (c1s_n_chunk regs [w64 (Boxreg.bx_n bs)] m eq_refl HPV) ])).

  assert (HD : YP09.pairwise_disjoint (lx_env cx fp regs [w64 (Boxreg.bx_n bs)])
    [c1s_win 0x20; c1s_win 0x60; c1s_frame [YP09.mkChunk 344 (CVal 4 (SOff 48 0))]]).
  { cbn [YP09.pairwise_disjoint YP09.all_disjoint]; unfold YP09.extent_disjoint;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi c1s_win c1s_frame c1s_spill YP09.base_val].
    rewrite ?(c1s_ew2 _ _ HR), ?c1s_u46. pose proof HGF as (HF0 & HF1 & _).
    repeat match goal with |- _ /\ _ => split end. all: try exact I. all: lia. }

  specialize (HS HD).
  specialize (HS (conj (c1s_afact _ 48 (Boxreg.bx_n bs) 0 5 (c1s_ew48 regs [w64 (Boxreg.bx_n bs)]) Hn ltac:(lia)) I)).
  assert (HEI : img_env VAL A_LIM (lx_env cx fp regs [w64 (Boxreg.bx_n bs)])) by apply lx_env_img.
  assert (SHOK : sh_ok SEGS C1S_Bx [] (lx_env cx fp regs [w64 (Boxreg.bx_n bs)]) (mrestrict (w_H W3) m)) by apply Forall_nil.
  assert (U2 : bv_unsigned (ew (lx_env cx fp regs [w64 (Boxreg.bx_n bs)]) LA_SP) = lsp0 cx + (lsp1 cx - lsp0 cx)) by (rewrite (c1s_ew2 regs _ HR); lia).
  remember (lx_env cx fp regs [w64 (Boxreg.bx_n bs)]) as E eqn:HE.
  assert (AG : forall a, (a < 240)%nat -> ew E a = ew (lx_env cx fp regs [w64 (Boxreg.bx_n bs)]) a) by (intros a _; rewrite HE; reflexivity).
  unfold c1s_J in HJ. unfold c1s_ss in HS.
  paj_run_to_tok RUNTO HS HJ SHOK C1S_SPAN C1_P3.
  { cbn [ss_mem].
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ LA_SP (lsp1 cx - lsp0 cx)); [reflexivity | exact U2 | cbn; unfold LX_STK; lia | cbn; lia |].
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ LA_SP (lsp1 cx - lsp0 cx)); [reflexivity | exact U2 | cbn; unfold LX_STK; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }

  assert (ATR : forall a, c1s_at a -> 0 <= a < 2 ^ 64).
  { intros a Ha. pose proof HGF as (HF0 & HF1 & _). pose proof HGr as (Hr0 & Hr1). pose proof c1s_SH as (ESH & D0 & HSH1 & HSH2).
    clear - Ha HGin Hs0 Hs1 Hs2 C1 HF0 HF1 HSH1 Hr0 Hr1 D0 ESH. unfold c1s_at, lc_n, SHADOW_OFF in *.
    destruct HGin as [Hn0 | (Hp0 & Hp1)]; lia. }
  assert (HM2 : c1s_mem (ms_mem ms)).
  { apply (c1s_mem_keep_w m (ms_mem ms) HM). intros a Ha Hw.
    apply (c1s_aview_frame E _ m (ms_mem ms) a HFr (ATR a Ha)).
    intros (rg & Hin & Hr). cbn [ss_mem In] in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi c1s_win c1s_frame YP09.base_val] in Hr;
      rewrite ?U2 in Hr; unfold c1s_wr in Hw; lia. }
  assert (U2' : bv_unsigned (ew E LA_SP) = lsp1 cx) by lia.
  assert (S60 : lslot cx W3 (c1s_cms (ms_mem ms)) 0x60 (bv_unsigned (getr regs 10))).

  { eapply (lx_word_of_ss W3 ms E _ 1 LA_SP (lsp1 cx)); [exact HS | reflexivity | exact U2' | left; reflexivity | | apply u64_range].
    rewrite lx_sv_SOff0, HE, (lx_env_reg cx fp regs _ 10 (10%bv : bv 5)) by reflexivity.
    unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (S20 : lslot cx W3 (c1s_cms (ms_mem ms)) 0x20 (2 ^ 64 - 1)).
  { eapply (lx_word_of_ss W3 ms E _ 0 LA_SP (lsp1 cx)); [exact HS | reflexivity | exact U2' | left; reflexivity | reflexivity | lia]. }
  pmkst HS.
  apply (c1s_land3 (ms_regs ms) (ms_mem ms) _ (bv_unsigned (getr regs 10)) HN3).
  - exact (c1s_regs_run regs _ E _ ms (w_H W3) HR HS AG eq_refl).
  - rewrite (c1s_reg_lit E _ ms (w_H W3) (19%bv : bv 5) _ HS eq_refl). c1s_lit.
  - rewrite (c1s_reg_run regs _ E _ ms (w_H W3) (23%bv : bv 5) 48 0 HS AG eq_refl ltac:(lia)), c1s_ew48. cbn [nth].
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (c1s_reg_lit E _ ms (w_H W3) (25%bv : bv 5) _ HS eq_refl). c1s_lit.
  - split; [exact HM2|]. split; [|exact S20]. split; [exact S60|]. split; [apply u64_range | exact Hv].
  - exact HJ.
Qed.

Lemma c1s_zero1_pt : forall regs m md, lx_from B MT POST (C1_I3 B MT i) ->
  c1s_regs regs -> c1s_mem m -> c1s_J m md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C1_P2)) m (seg_rom SEGS)) md) (POST cx).
Proof.
  intros regs m md HN3 HR HM HJ.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs2 & Hs32). pose proof asan_consts as (C1 & _).
  pose proof HGF as (HF0 & HF1 & _).
  pose (RUN := paj_run B LAWS).
  pose proof HM as (_ & HSH & _ & _ & _ & _ & _ & _ & _ & _ & HSL & _ & _ & ((HML & HMC) & _)).
  pose proof HSL as (_ & _ & _ & _ & _ & L68 & _).
  assert (HSLOT : lx_slots cx W3 (c1s_cms m) (lx_env cx fp regs []) [(0x68, SOff LA_F 32)]).
  { apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    apply (lx_slot_atom cx W3 (c1s_cms m) _ 0x68 LA_F (lF cx fp) 32 L68 (c1s_ew46 regs []) ltac:(lia) ltac:(lia)). }
  pose proof (c1s_seat regs m md [] C1_P2 (lx_sr LX_OVP) [c1s_spill [(0x68, SOff LA_F 32)]] []
    HR HJ (c1s_regs_ok regs _ HR) eq_refl (@Forall_cons _ _ _ _ (c1s_spill_ok regs [] m _ HR HSLOT) (@Forall_nil _ _))
    (conj I I) I) as HS.
  assert (HEI : img_env VAL A_LIM (lx_env cx fp regs [])) by apply lx_env_img.
  assert (SHOK : sh_ok SEGS C1S_Bx [] (lx_env cx fp regs []) (mrestrict (w_H W3) m)) by apply Forall_nil.
  remember (lx_env cx fp regs []) as E eqn:HE.
  assert (AG : forall a, (a < 240)%nat -> ew E a = ew (lx_env cx fp regs []) a) by (intros a _; rewrite HE; reflexivity).
  unfold c1s_J in HJ. unfold c1s_ss in HS.
  paj_run_tok RUN HS HJ SHOK C1S_SPAN.
  { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  assert (EM : ms_mem ms = m) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity).
  pmkst HS.

  rewrite EM in HJ |- *.
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
  prreg HS (1%bv : bv 5) Rra.
  assert (HR1 : c1s_regs (ms_regs ms)) by exact (c1s_regs_runc regs [] E _ _ ms (w_H W3) HR HS AG eq_refl).
  pose proof HR1 as (Q2 & _ & _ & Q3 & Q4 & _).
  eapply SRr_bind.
  { apply (c1s_bcmp (ms_regs ms) m _ (lF cx fp + 32) (VAL (A_OBJ 4)) 0x73c HJ).
    - rewrite Ra0, HE, c1s_u46. reflexivity.
    - rewrite Ra1. unfold w64. rewrite <- (HEI (A_OBJ 4) ltac:(cbv; lia)). rewrite Z_to_bv_bv_unsigned. reflexivity.
    - rewrite Ra2. reflexivity.
    - exact Q2.
    - exact Q3.
    - exact Q4.
    - exact Rra.
    - lia.
    - reflexivity.
    - apply (c1s_obj_frame m _ 32 HJ HSH); [left; reflexivity|]. intros a Ha.
      replace a with (lF cx fp + 32 + (a - (lF cx fp + 32))) by lia.
      unfold lview in HMC. cbn [c1s_cms ms_mem mkst] in HMC. rewrite (HMC (a - (lF cx fp + 32))) by lia. discriminate.
    - exact (c1s_obj_zero m _ HJ). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hcmp & Hkeep).
  apply (c1s_zero2_pt regs2 mem2 md2 HN3).
  - exact (c1s_regs_pres _ _ HP HR1).
  - apply (c1s_mem_keep_w m mem2 HM). intros a Ha _. exact (Hkeep a Ha).
  - exact HJ2.
  - rewrite Hcmp. apply (c1s_bytes_eq M Boxreg.zero6 (lF cx fp + 32) (VAL (A_OBJ 4)) m HML eq_refl).
    + intros j Hj. unfold lview in HMC. cbn [c1s_cms ms_mem mkst] in HMC. exact (HMC j Hj).
    + intros j Hj. rewrite (c1s_zero_view m _ HJ j Hj). rewrite c1s_zero6_bytes by exact Hj. reflexivity.
Qed.

Definition c1s_lr (j h u : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 19 = w64 u /\ getr regs 23 = w64 (Boxreg.bx_n bs) /\ getr regs 24 = w64 j /\ getr regs 25 = w64 h /\
  getr regs 26 = w64 (12 + 56 * j) /\ getr regs 27 = w64 j.

Definition c1s_at4 (nz j h u : Z) (regs : bvmap 5 word) (m : word -> option byte) (md : Model) : Prop :=
  c1s_regs regs /\ c1s_mem3 nz m /\ c1s_J m md /\ 0 <= j < Boxreg.bx_n bs /\
  LC1.c1_sh bs M nz j h /\ LC1.c1_su bs nch j u /\ c1s_lr j h u regs.

Definition c1s_next (nz j : Z) : Prop :=
  forall h' u' regs' m' md', c1s_at4 nz (j + 1) h' u' regs' m' md' ->
  SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + C1_P4)) m' (seg_rom SEGS)) md') (POST cx).

Lemma c1s_j_cases : forall j, 0 <= j < Boxreg.bx_n bs -> j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4.
Proof. intros j Hj. pose proof c1s_n_range. lia. Qed.

Lemma c1s_ew_reg : forall regs ex (n : nat) (rr : bv 5) v, Z.of_nat n = bv_unsigned rr -> getr regs rr = w64 v ->
  ew (lx_env cx fp regs ex) n = w64 v.
Proof. intros regs ex n rr v Hn H. rewrite (lx_env_reg cx fp regs ex n rr Hn). exact H. Qed.

Lemma c1s_U_reg : forall regs ex E (n : nat) (rr : bv 5) v, E = lx_env cx fp regs ex -> Z.of_nat n = bv_unsigned rr ->
  getr regs rr = w64 v -> 0 <= v < 2 ^ 64 -> U E (SOff n 0) = v.
Proof. intros regs ex E n rr v -> Hn H Hv. apply (U_atom _ n v (c1s_ew_reg regs ex n rr v Hn H) Hv). Qed.

Lemma c1s_S_reg : forall regs ex E (n : nat) (rr : bv 5) v, E = lx_env cx fp regs ex -> Z.of_nat n = bv_unsigned rr ->
  getr regs rr = w64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros regs ex E n rr v -> Hn H. rewrite lx_sv_SOff0. exact (c1s_ew_reg regs ex n rr v Hn H). Qed.

Ltac c1s_reg_solve :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E ?ss (restrict _ ?msn),
    AG : forall a, _ -> ew ?E a = ew (lx_env _ _ ?regs ?ex) a |- getr (ms_regs ?msn) ?rr = _ =>
      first [ rewrite (c1s_reg_lit E ss msn (w_H W3) rr _ HS eq_refl); first [reflexivity | c1s_lit]
            | rewrite (c1s_reg_keep regs ex E ss msn (w_H W3) rr _ HS AG eq_refl eq_refl); assumption ]
  end.

Ltac c1s_lr_solve := unfold c1s_lr; repeat match goal with |- _ /\ _ => split end; c1s_reg_solve.

Lemma c1s_call_pi : forall E' ss pc ms, st_ok SEGS E' (setpc ss pc) ms -> st_ok_pi SEGS VAL E' (setpc ss (pc - BASE)) ms.
Proof.
  intros E' ss pc ms HS. unfold st_ok_pi, abs_ss. unfold setpc at 2 3. cbn [ss_pc].
  replace (BASE + (pc - BASE)) with pc by lia. exact HS.
Qed.

Lemma c1s_reg_img : forall E' ss ms (H : word -> bool) (rr : bv 5) (a : nat),
  st_ok_pi SEGS VAL E' ss (restrict H ms) -> img_env VAL A_LIM E' -> sr_get (ss_regs ss) rr = SOff a 0 ->
  (A_TEXT <= a < A_LIM)%nat -> getr (ms_regs ms) rr = w64 (VAL a).
Proof.
  intros E' ss ms H rr a HS HEI Hr Ha. rewrite (st_ok_pi_restrict_reg H E' ss ms rr HS), Hr, lx_sv_SOff0.
  unfold w64. rewrite <- (HEI a Ha). symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma c1s_reg_code : forall E' ss ms (H : word -> bool) (rr : bv 5) kk,
  st_ok_pi SEGS VAL E' ss (restrict H ms) -> img_env VAL A_LIM E' -> sr_get (ss_regs ss) rr = SOff A_TEXT kk ->
  getr (ms_regs ms) rr = Z_to_bv 64 (BASE + kk).
Proof.
  intros E' ss ms H rr kk HS HEI Hr. rewrite (st_ok_pi_restrict_reg H E' ss ms rr HS), Hr.
  exact (codeptr_val E' kk HEI).
Qed.

Lemma c1s_lr_pres : forall j h u regs regs', aregs_preserved regs regs' -> c1s_lr j h u regs -> c1s_lr j h u regs'.
Proof.
  intros j h u regs regs' HP (R19 & R23 & R24 & R25 & R26 & R27).
  assert (K : forall (r0 : bv 5) z, r0 = Z_to_bv 5 z -> acallee_saved z -> getr regs' r0 = getr regs r0)
    by (intros r0 z -> Hz; apply HP; exact Hz).
  unfold c1s_lr.
  split; [etransitivity; [apply (K _ 19); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact R19]|].
  split; [etransitivity; [apply (K _ 23); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact R23]|].
  split; [etransitivity; [apply (K _ 24); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact R24]|].
  split; [etransitivity; [apply (K _ 25); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact R25]|].
  split; [etransitivity; [apply (K _ 26); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact R26]|].
  etransitivity; [apply (K _ 27); [apply bv_eq; reflexivity | unfold acallee_saved; lia] | exact R27].
Qed.

Lemma c1s_row_view : forall m j kk, lprev cx fp W3 (c1s_cms m) bs -> 0 <= j <= 4 -> 0 <= kk < 6 ->
  aview SEGS (w_H W3) m (lF cx fp + 64 + 56 * j + kk) =
    Some (bv_unsigned (nth (Z.to_nat kk) (Boxreg.bx_mac bs j) (Z_to_bv 8 0))).
Proof.
  intros m j kk HP Hj Hkk. pose proof c1s_len as HL.
  rewrite (c1s_mac_bytes bs j kk HL Hj Hkk).
  replace (lF cx fp + 64 + 56 * j + kk) with (lF cx fp + 64 + (56 * j + kk)) by lia.
  exact (HP (56 * j + kk) ltac:(unfold LX_REG; lia)).
Qed.

Lemma c1s_row_obj : forall m md j, c1s_J m md -> c1s_mem m -> 0 <= j <= 4 -> c1s_obj m (lF cx fp + 64 + 56 * j).
Proof.
  intros m md j HJ HM Hj. pose proof HM as (_ & HSH & _ & _ & _ & _ & _ & _ & HP & _).
  replace (lF cx fp + 64 + 56 * j) with (lF cx fp + (64 + 56 * j)) by lia.
  apply (c1s_obj_frame m md (64 + 56 * j) HJ HSH); [right; lia|].
  intros a Ha. replace a with (lF cx fp + 64 + 56 * j + (a - (lF cx fp + 64 + 56 * j))) by lia.
  rewrite (c1s_row_view m j (a - (lF cx fp + 64 + 56 * j)) HP Hj) by lia. discriminate.
Qed.

Lemma c1s_mac_obj : forall m md, c1s_J m md -> c1s_mem m -> c1s_obj m (lF cx fp + 32).
Proof.
  intros m md HJ HM. pose proof HM as (_ & HSH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ((HML & HMC) & _)).
  apply (c1s_obj_frame m md 32 HJ HSH); [left; reflexivity|]. intros a Ha.
  replace a with (lF cx fp + 32 + (a - (lF cx fp + 32))) by lia.
  unfold lview in HMC. cbn [c1s_cms ms_mem mkst] in HMC. rewrite (HMC (a - (lF cx fp + 32))) by lia. discriminate.
Qed.

Lemma c1s_row_zero : forall m md j, c1s_J m md -> c1s_mem m -> 0 <= j <= 4 ->
  ((forall jj, 0 <= jj < 6 -> aview SEGS (w_H W3) m (lF cx fp + 64 + 56 * j + jj) = aview SEGS (w_H W3) m (VAL (A_OBJ 4) + jj))
   <-> Boxreg.bx_mac bs j = Boxreg.zero6).
Proof.
  intros m md j HJ HM Hj. pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & HP & _). pose proof c1s_len as HL.
  apply (c1s_bytes_eq (Boxreg.bx_mac bs j) Boxreg.zero6 _ _ m (LC1.c1_mac_len bs j HL Hj) eq_refl).
  - intros jj Hjj. exact (c1s_row_view m j jj HP Hj Hjj).
  - intros jj Hjj. rewrite (c1s_zero_view m md HJ jj Hjj), c1s_zero6_bytes by exact Hjj. reflexivity.
Qed.

Lemma c1s_row_mac : forall m j, c1s_mem m -> 0 <= j <= 4 ->
  ((forall jj, 0 <= jj < 6 -> aview SEGS (w_H W3) m (lF cx fp + 64 + 56 * j + jj) = aview SEGS (w_H W3) m (lF cx fp + 32 + jj))
   <-> Boxreg.bx_mac bs j = M).
Proof.
  intros m j HM Hj. pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & HP & _ & _ & _ & _ & ((HML & HMC) & _)).
  pose proof c1s_len as HL.
  apply (c1s_bytes_eq (Boxreg.bx_mac bs j) M _ _ m (LC1.c1_mac_len bs j HL Hj) HML).
  - intros jj Hjj. exact (c1s_row_view m j jj HP Hj Hjj).
  - intros jj Hjj. unfold lview in HMC. cbn [c1s_cms ms_mem mkst] in HMC. exact (HMC jj Hjj).
Qed.

Lemma c1s_E : forall nz j h u regs m md, c1s_next nz j -> lx_from B MT POST (C1_I5 B MT i) ->
  c1s_regs regs -> c1s_mem3 nz m -> c1s_J m md -> 0 <= j < Boxreg.bx_n bs ->
  LC1.c1_sh bs M nz (j + 1) h -> LC1.c1_su bs nch (j + 1) u -> c1s_lr j h u regs ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x80c)) m (seg_rom SEGS)) md) (POST cx).
Proof.
  intros nz j h u regs m md HNX HN5 HR HM HJ Hj HSH HSU (R19 & R23 & R24 & R25 & R26 & R27).
  pose proof (lh_laws B MT HY) as LAWS. pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof c1s_n_range as Hn.
  pose (RUNTO := paj_run_to B LAWS). pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
  pose proof (c1s_seat regs m md [] 0x80c (lx_sr (c1s_ov j)) [] [] HR HJ (c1s_regs_ok_l regs [] j HR R24 R27 R26)
    eq_refl (Forall_nil _) I I) as HS.
  assert (HEI : img_env VAL A_LIM (lx_env cx fp regs [])) by apply lx_env_img.
  assert (SHOK : sh_ok SEGS C1S_Bx [] (lx_env cx fp regs []) (mrestrict (w_H W3) m)) by apply Forall_nil.
  remember (lx_env cx fp regs []) as E eqn:HE.
  assert (AG : forall a, (a < 240)%nat -> ew E a = ew (lx_env cx fp regs []) a) by (intros a _; rewrite HE; reflexivity).
  assert (U23 : U E (SOff 23 0) = Boxreg.bx_n bs) by (apply (c1s_U_reg regs [] E 23 (23%bv : bv 5)); [exact HE | reflexivity | exact R23 | lia]).
  unfold c1s_J in HJ. unfold c1s_ss in HS.
  destruct (c1s_j_cases j Hj) as [-> | [-> | [-> | [-> | ->]]]].

  all: paj_run_tok RUN HS HJ SHOK C1S_SPAN; [apply awr_ok_nil |].
  all: assert (EM : ms_mem ms = m) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity).
  all: subst m; clear HF HFr HG.
  all: psrr_branch_tok RUN BR HS SHOK C1S_SPAN; rewrite branch_ne_U, U23, U_lit in Hc by lia.
  all: lazymatch type of Hc with
       | negb _ = true => apply negb_true_iff, Z.eqb_neq in Hc; paj_run_to_tok RUNTO HS HJ SHOK C1S_SPAN C1_P4; [apply awr_ok_nil |]
       | negb _ = false => apply negb_false_iff, Z.eqb_eq in Hc; paj_run_to_tok RUNTO HS HJ SHOK C1S_SPAN C1_P5; [apply awr_ok_nil |]
       end.
  all: assert (EM : ms_mem ms0 = ms_mem ms) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity).
  all: clear HF HFr HG; rewrite EM in HJ; rewrite ?wvb_collapse in HJ; pmkst HS; rewrite EM.
  all: lazymatch type of Hc with
       | _ <> _ =>
         apply (HNX h u); split; [exact (c1s_regs_run regs [] E _ ms0 (w_H W3) HR HS AG eq_refl)|];
         split; [exact HM|]; split; [exact HJ|]; split; [lia|]; split; [exact HSH|]; split; [exact HSU|];
         split; [rewrite (c1s_reg_keep regs [] E _ ms0 (w_H W3) (19%bv : bv 5) 19 HS AG eq_refl eq_refl); exact R19|];
         split; [rewrite (c1s_reg_keep regs [] E _ ms0 (w_H W3) (23%bv : bv 5) 23 HS AG eq_refl eq_refl); exact R23|];
         split; [rewrite (c1s_reg_lit E _ ms0 (w_H W3) (24%bv : bv 5) _ HS eq_refl); reflexivity|];
         split; [rewrite (c1s_reg_keep regs [] E _ ms0 (w_H W3) (25%bv : bv 5) 25 HS AG eq_refl eq_refl); exact R25|];
         split; [rewrite (c1s_reg_lit E _ ms0 (w_H W3) (26%bv : bv 5) _ HS eq_refl); reflexivity|];
         rewrite (c1s_reg_lit E _ ms0 (w_H W3) (27%bv : bv 5) _ HS eq_refl); reflexivity
       | _ = _ =>
         apply (c1s_land5 (ms_regs ms0) (ms_mem ms) _ nz h u HN5);
         [ exact (c1s_regs_run regs [] E _ ms0 (w_H W3) HR HS AG eq_refl)
         | exact HM | exact HJ | rewrite Hc; exact HSH | rewrite Hc; exact HSU
         | rewrite (c1s_reg_keep regs [] E _ ms0 (w_H W3) (19%bv : bv 5) 19 HS AG eq_refl eq_refl); exact R19
         | rewrite (c1s_reg_keep regs [] E _ ms0 (w_H W3) (25%bv : bv 5) 25 HS AG eq_refl eq_refl); exact R25 ]
       end.
Qed.

Lemma c1s_D : forall nz j h u regs m md, c1s_next nz j -> lx_from B MT POST (C1_I5 B MT i) ->
  c1s_regs regs -> c1s_mem3 nz m -> c1s_J m md -> 0 <= j < Boxreg.bx_n bs ->
  LC1.c1_sh bs M nz (j + 1) h -> LC1.c1_su bs nch j u -> u = -1 -> c1s_lr j h u regs ->
  (bv_unsigned (getr regs 10) = 0 <-> Boxreg.bx_mac bs j = Boxreg.zero6) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x7dc)) m (seg_rom SEGS)) md) (POST cx).
Proof.
  intros nz j h u regs m md HNX HN5 HR HM HJ Hj HSH HSU Hu (R19 & R23 & R24 & R25 & R26 & R27) Hv.
  pose proof (lh_laws B MT HY) as LAWS. pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof c1s_n_range as Hn. pose proof c1s_len as HL.
  pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs2 & Hs32). pose proof asan_consts as (C1 & _).
  pose proof HGF as (HF0 & HF1 & _).
  pose proof HINV as ((_ & _ & HB2 & HB3 & _) & _).
  pose proof (Boxreg.B3_bounds bs j HB2 HB3 Hj) as (_ & Hnchj & _).
  pose (RUNTO := paj_run_to B LAWS). pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
  pose proof HM as ((_ & HSHW & _ & _ & _ & _ & _ & _ & HPV & _ & _ & _ & _ & (_ & S50 & Hnch)) & _).
  set (ex := [w64 nch; w64 (Boxreg.bx_nch bs j)]).
  assert (HSLOT : lx_slots cx W3 (c1s_cms m) (lx_env cx fp regs ex) [(0x50, SOff 48 0)]).
  { apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    exact (c1s_slot_at regs ex m 0x50 48 nch S50 (c1s_ew48 regs ex) ltac:(lia)). }
  assert (HCH : YP09.chunk_ok SEGS (lx_env cx fp regs ex) (mrestrict (w_H W3) m) (lF cx fp)
                  (YP09.mkChunk (76 + 56 * j) (CVal 4 (SOff 49 0)))).
  { apply (chunk_ok_val SEGS _ _ (lF cx fp) (76 + 56 * j) 4 (SOff 49 0) (Boxreg.bx_nch bs j)).
    - rewrite lx_sv_SOff0, c1s_ew49. reflexivity.
    - cbn [Z.of_N]. lia.
    - cbn. lia.
    - replace (lF cx fp + (76 + 56 * j)) with (lF cx fp + 64 + (56 * j + 12)) by lia.
      exact (c1s_prev_val_mem cx fp W3 (c1s_cms m) bs (56 * j + 12) HPV HL ltac:(lia) ltac:(lia) ltac:(unfold Boxreg.bx_nch in Hnchj; lia)). }
  assert (HD : YP09.pairwise_disjoint (lx_env cx fp regs ex)
    [c1s_spill [(0x50, SOff 48 0)]; c1s_frame [YP09.mkChunk (76 + 56 * j) (CVal 4 (SOff 49 0))]]).
  { cbn [YP09.pairwise_disjoint YP09.all_disjoint]; unfold YP09.extent_disjoint;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi c1s_win c1s_frame c1s_spill YP09.base_val].
    rewrite ?(c1s_ew2 _ _ HR), ?c1s_u46.
    repeat match goal with |- _ /\ _ => split end. all: try exact I. all: lia. }
  pose proof (c1s_seat regs m md ex 0x7dc (lx_sr (c1s_ov j))
    [c1s_spill [(0x50, SOff 48 0)]; c1s_frame [YP09.mkChunk (76 + 56 * j) (CVal 4 (SOff 49 0))]]
    [(48%nat, mkAF 0 255 0); (49%nat, mkAF 0 40 0)]
    HR HJ (c1s_regs_ok_l regs ex j HR R24 R27 R26)
    ltac:(destruct (c1s_j_cases j Hj) as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; reflexivity)
    (@Forall_cons _ _ _ _ (c1s_spill_ok regs ex m _ HR HSLOT)
      (@Forall_cons _ _ _ _ (c1s_frame_ok regs ex m _ (@Forall_cons _ _ _ _ HCH (@Forall_nil _ _))) (@Forall_nil _ _)))
    HD) as HS.
  specialize (HS (conj (c1s_afact _ 48 nch 0 255 (c1s_ew48 regs ex) ltac:(lia) ltac:(lia))
                 (conj (c1s_afact _ 49 (Boxreg.bx_nch bs j) 0 40 (c1s_ew49 regs ex) ltac:(lia) ltac:(lia)) I))).
  assert (SHOK : sh_ok SEGS C1S_Bx C1S_SHD (lx_env cx fp regs ex) (mrestrict (w_H W3) m)).
  { assert (HU32 : U (lx_env cx fp regs ex) (SOff LA_SB 0) = SHADOW_OFF).
    { unfold U. rewrite lx_sv_SOff0, c1s_ew32. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
    assert (HU46 : U (lx_env cx fp regs ex) (SOff LA_F 0) = lF cx fp).
    { unfold U. rewrite lx_sv_SOff0. apply c1s_u46. }
    apply Forall_cons; [|apply Forall_nil].
    exact (lx_shent_frame B MT LAWS cx fp W3 (c1s_cms m) ly3 S3 md k HB HJ HFR _ 64 352 HU32 HU46 HSHW ltac:(lia)). }
  assert (HEI : img_env VAL A_LIM (lx_env cx fp regs ex)) by apply lx_env_img.
  assert (U10 : U (lx_env cx fp regs ex) (SOff 10 0) = bv_unsigned (getr regs 10)).
  { unfold U. rewrite lx_sv_SOff0, (lx_env_reg cx fp regs ex 10 (10%bv : bv 5)) by reflexivity. reflexivity. }
  assert (U48 : U (lx_env cx fp regs ex) (SOff 48 0) = nch) by (apply U_atom; [exact (c1s_ew48 regs ex) | lia]).
  assert (U49 : U (lx_env cx fp regs ex) (SOff 49 0) = Boxreg.bx_nch bs j) by (apply U_atom; [exact (c1s_ew49 regs ex) | lia]).
  remember (lx_env cx fp regs ex) as E eqn:HE.
  assert (AG : forall a, (a < 240)%nat -> ew E a = ew (lx_env cx fp regs ex) a) by (intros a _; rewrite HE; reflexivity).
  unfold c1s_J in HJ. unfold c1s_ss in HS.
  destruct (c1s_j_cases j Hj) as [-> | [-> | [-> | [-> | ->]]]].

  all: subst u.
  all: psrr_branch_tok RUN BR HS SHOK C1S_SPAN; rewrite branch_ne_U, U10, U_lit in Hc by lia.
  all: lazymatch type of Hc with
       | negb _ = true => apply negb_true_iff, Z.eqb_neq in Hc; rename Hc into HcT;
           paj_run_to_tok RUNTO HS HJ SHOK C1S_SPAN 0x80c; [cbn [ss_mem add_cond]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |]
       | negb _ = false => apply negb_false_iff, Z.eqb_eq in Hc; rename Hc into HcF;
           paj_run_tok RUN HS HJ SHOK C1S_SPAN; [cbn [ss_mem add_cond]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |]
       end.
  all: assert (EM : ms_mem ms = m) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity).
  all: subst m; clear HF HFr HG; rewrite ?wvb_collapse in HJ.
  all: tryif (let x := constr:(HcT) in idtac) then
         (pmkst HS;
          apply (c1s_E nz _ h (-1) _ _ _ HNX HN5);
          [ exact (c1s_regs_run regs _ E _ ms (w_H W3) HR HS AG eq_refl) | exact HM | exact HJ | lia | exact HSH
          | apply LC1.c1_su_miss; [exact HSU | lia | intros (HZ & _); apply HcT; apply Hv; exact HZ]
          | c1s_lr_solve ])
       else idtac.
  all: psrr_branch_tok RUN BR HS SHOK C1S_SPAN; rewrite branch_eq_U, U49, U48 in Hc.
  all: lazymatch type of Hc with
       | (_ =? _) = true => apply Z.eqb_eq in Hc;
           paj_run_to_tok RUNTO HS HJ SHOK C1S_SPAN 0x80c; [cbn [ss_mem add_cond]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |];
           assert (EM2 : ms_mem ms0 = ms_mem ms) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity);
           clear HF HFr HG; rewrite EM2 in HJ; rewrite ?wvb_collapse in HJ; pmkst HS; rewrite EM2;
           lazymatch type of HNX with c1s_next _ ?jj => apply (c1s_E nz jj h jj _ _ _ HNX HN5) end;
           [ exact (c1s_regs_run regs _ E _ ms0 (w_H W3) HR HS AG eq_refl) | exact HM | exact HJ | lia | exact HSH
           | apply LC1.c1_su_hit; [exact HSU | lia | apply Hv; exact HcF | exact Hc]
           | c1s_lr_solve ]
       | (_ =? _) = false => apply Z.eqb_neq in Hc;
           paj_run_to_tok RUNTO HS HJ SHOK C1S_SPAN 0x80c; [cbn [ss_mem add_cond]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |];
           assert (EM2 : ms_mem ms0 = ms_mem ms) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity);
           clear HF HFr HG; rewrite EM2 in HJ; rewrite ?wvb_collapse in HJ; pmkst HS; rewrite EM2;
           apply (c1s_E nz _ h (-1) _ _ _ HNX HN5);
           [ exact (c1s_regs_run regs _ E _ ms0 (w_H W3) HR HS AG eq_refl) | exact HM | exact HJ | lia | exact HSH
           | apply LC1.c1_su_miss; [exact HSU | lia | intros (_ & HK); exact (Hc HK)]
           | c1s_lr_solve ]
       end.
Qed.

Lemma c1s_C : forall nz j h u regs m md, c1s_next nz j -> lx_from B MT POST (C1_I5 B MT i) ->
  c1s_regs regs -> c1s_mem3 nz m -> c1s_J m md -> 0 <= j < Boxreg.bx_n bs ->
  LC1.c1_sh bs M nz (j + 1) h -> LC1.c1_su bs nch j u -> c1s_lr j h u regs ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x7b0)) m (seg_rom SEGS)) md) (POST cx).
Proof.
  intros nz j h u regs m md HNX HN5 HR HM HJ Hj HSH HSU HLR.
  pose proof HLR as (R19 & R23 & R24 & R25 & R26 & R27).
  pose proof (lh_laws B MT HY) as LAWS. pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof c1s_n_range as Hn. pose proof c1s_len as HL.
  pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs2 & Hs32). pose proof asan_consts as (C1 & _).
  pose proof HGF as (HF0 & HF1 & _).
  pose proof (lxc1_su_bound bs nch j u HSU) as Hub.
  pose (RUNTO := paj_run_to B LAWS). pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
  pose proof HM as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSL & _) & _).
  pose proof HSL as (_ & _ & _ & _ & _ & _ & _ & L78).
  set (ex := [w64 (2 ^ 64 - 1 - (lF cx fp + 64))]).
  assert (HSLOT : lx_slots cx W3 (c1s_cms m) (lx_env cx fp regs ex) [(0x78, SOff 48 0)]).
  { apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    exact (c1s_slot_at regs ex m 0x78 48 _ L78 (c1s_ew48 regs ex) ltac:(lia)). }
  pose proof (c1s_seat regs m md ex 0x7b0 (lx_sr (c1s_ov j)) [c1s_spill [(0x78, SOff 48 0)]] []
    HR HJ (c1s_regs_ok_l regs ex j HR R24 R27 R26) eq_refl
    (@Forall_cons _ _ _ _ (c1s_spill_ok regs ex m _ HR HSLOT) (@Forall_nil _ _)) (conj I I) I) as HS.
  assert (HEI : img_env VAL A_LIM (lx_env cx fp regs ex)) by apply lx_env_img.
  assert (SHOK : sh_ok SEGS C1S_Bx [] (lx_env cx fp regs ex) (mrestrict (w_H W3) m)) by apply Forall_nil.
  assert (U48 : U (lx_env cx fp regs ex) (SOff 48 0) = 2 ^ 64 - 1 - (lF cx fp + 64)) by (apply U_atom; [exact (c1s_ew48 regs ex) | lia]).
  remember (lx_env cx fp regs ex) as E eqn:HE.
  assert (AG : forall a, (a < 240)%nat -> ew E a = ew (lx_env cx fp regs ex) a) by (intros a _; rewrite HE; reflexivity).
  assert (S19 : sv_denot E (SOff 19 0) = Z_to_bv 64 u) by exact (c1s_S_reg regs ex E 19 (19%bv : bv 5) u HE eq_refl R19).
  unfold c1s_J in HJ. unfold c1s_ss in HS.
  destruct (c1s_j_cases j Hj) as [-> | [-> | [-> | [-> | ->]]]].
  all: psrr_branch_tok RUN BR HS SHOK C1S_SPAN; rewrite S19 in Hc; cbn [sv_denot] in Hc; rewrite c1s_bt_ge in Hc by lia.
  all: lazymatch type of Hc with
       | negb _ = true => apply negb_true_iff, Z.ltb_ge in Hc; rename Hc into HcT;
           paj_run_to_tok RUNTO HS HJ SHOK C1S_SPAN 0x80c; [cbn [ss_mem add_cond]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |]
       | negb _ = false => apply negb_false_iff, Z.ltb_lt in Hc; rename Hc into HcF;
           paj_run_tok RUN HS HJ SHOK C1S_SPAN; [cbn [ss_mem add_cond]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |]
       end.
  all: assert (EM : ms_mem ms = m) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity).
  all: subst m; clear HF HFr HG; rewrite ?wvb_collapse in HJ.
  all: tryif (let x := constr:(HcT) in idtac) then
         (pmkst HS;
          apply (c1s_E nz _ h u _ _ _ HNX HN5);
          [ exact (c1s_regs_run regs _ E _ ms (w_H W3) HR HS AG eq_refl) | exact HM | exact HJ | lia | exact HSH
          | exact (LC1.c1_su_keep bs nch _ u HSU HcT)
          | c1s_lr_solve ])
       else idtac.
  all: assert (Hu1 : u = -1) by lia; subst u.
  all: psrr_branch_tok RUN BR HS SHOK C1S_SPAN; rewrite branch_ltu_U, U48, U_lit in Hc by lia.
  all: lazymatch type of Hc with
       | (_ <? _) = true => exfalso; apply Z.ltb_lt in Hc; lia
       | (_ <? _) = false => clear Hc; paj_run_tok RUN HS HJ SHOK C1S_SPAN; [cbn [ss_mem add_cond]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |]
       end.
  all: assert (EM2 : ms_mem ms0 = ms_mem ms) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity).
  all: clear HF HFr HG; rewrite EM2 in HJ; rewrite ?wvb_collapse in HJ; pmkst HS; rewrite EM2.
  all: pose proof (c1s_call_pi _ _ _ _ HS) as HS'.
  all: assert (HR1 : c1s_regs (ms_regs ms0)) by exact (c1s_regs_run regs _ E _ ms0 (w_H W3) HR HS' AG eq_refl).
  all: assert (HLR1 : c1s_lr _ h (-1) (ms_regs ms0)) by c1s_lr_solve.
  all: pose proof HR1 as (Q2 & _ & _ & Q3 & Q4 & _).

  all: lazymatch type of HLR1 with c1s_lr ?jj _ _ _ =>
       eapply SRr_bind;
       [ apply (c1s_bcmp (ms_regs ms0) (ms_mem ms) _ (lF cx fp + 64 + 56 * jj) (VAL (A_OBJ 4)) 0x7dc HJ);
         [ rewrite (c1s_reg_run regs ex E _ ms0 (w_H W3) (10%bv : bv 5) 46 _ HS' AG eq_refl ltac:(lia));
           change (ew (lx_env cx fp regs ex) 46) with (ew (lx_env cx fp regs ex) LA_F); rewrite c1s_u46; unfold w64; f_equal; lia
         | exact (c1s_reg_img E _ ms0 (w_H W3) (11%bv : bv 5) (A_OBJ 4) HS' HEI eq_refl ltac:(cbv; lia))
         | rewrite (c1s_reg_lit E _ ms0 (w_H W3) (12%bv : bv 5) _ HS' eq_refl); reflexivity
         | exact Q2 | exact Q3 | exact Q4
         | exact (c1s_reg_code E _ ms0 (w_H W3) (1%bv : bv 5) _ HS' HEI eq_refl)
         | lia | reflexivity
         | exact (c1s_row_obj _ _ jj HJ (proj1 HM) ltac:(lia))
         | exact (c1s_obj_zero _ _ HJ) ]
       | cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hcmp & Hkeep);
         apply (c1s_D nz jj h (-1) regs2 mem2 md2 HNX HN5);
         [ exact (c1s_regs_pres _ _ HP HR1) | exact (c1s_mem3_keep nz _ mem2 HM Hkeep) | exact HJ2 | exact Hj | exact HSH
         | exact HSU | reflexivity | exact (c1s_lr_pres _ _ _ _ _ HP HLR1)
         | rewrite Hcmp; exact (c1s_row_zero _ _ jj HJ (proj1 HM) ltac:(lia)) ] ]
       end.
Qed.

Lemma c1s_Bp : forall nz j h u regs m md, c1s_next nz j -> lx_from B MT POST (C1_I5 B MT i) ->
  c1s_regs regs -> c1s_mem3 nz m -> c1s_J m md -> 0 <= j < Boxreg.bx_n bs ->
  LC1.c1_sh bs M nz j h -> h = -1 -> nz <> 0 -> LC1.c1_su bs nch j u -> c1s_lr j h u regs ->
  (bv_unsigned (getr regs 10) = 0 <-> Boxreg.bx_mac bs j = M) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x7a0)) m (seg_rom SEGS)) md) (POST cx).
Proof.
  intros nz j h u regs m md HNX HN5 HR HM HJ Hj HSH Hh Hnz HSU HLR Hv. subst h.
  pose proof HLR as (R19 & R23 & R24 & R25 & R26 & R27).
  pose proof (lh_laws B MT HY) as LAWS. pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof c1s_n_range as Hn.
  pose (RUNTO := paj_run_to B LAWS). pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
  pose proof (c1s_seat regs m md [] 0x7a0 (lx_sr (c1s_ov j)) [] [] HR HJ (c1s_regs_ok_l regs [] j HR R24 R27 R26)
    eq_refl (Forall_nil _) I I) as HS.
  assert (HEI : img_env VAL A_LIM (lx_env cx fp regs [])) by apply lx_env_img.
  assert (SHOK : sh_ok SEGS C1S_Bx [] (lx_env cx fp regs []) (mrestrict (w_H W3) m)) by apply Forall_nil.
  assert (U10 : U (lx_env cx fp regs []) (SOff 10 0) = bv_unsigned (getr regs 10)).
  { unfold U. rewrite lx_sv_SOff0, (lx_env_reg cx fp regs [] 10 (10%bv : bv 5)) by reflexivity. reflexivity. }
  remember (lx_env cx fp regs []) as E eqn:HE.
  assert (AG : forall a, (a < 240)%nat -> ew E a = ew (lx_env cx fp regs []) a) by (intros a _; rewrite HE; reflexivity).
  unfold c1s_J in HJ. unfold c1s_ss in HS.
  destruct (c1s_j_cases j Hj) as [-> | [-> | [-> | [-> | ->]]]].
  all: paj_run_tok RUN HS HJ SHOK C1S_SPAN; [apply awr_ok_nil |].
  all: assert (EM : ms_mem ms = m) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity).
  all: subst m; clear HF HFr HG; rewrite ?wvb_collapse in HJ.
  all: psrr_branch_tok RUN BR HS SHOK C1S_SPAN; rewrite branch_eq_U, U10, U_lit in Hc by lia.
  all: paj_run_to_tok RUNTO HS HJ SHOK C1S_SPAN 0x7b0; [apply awr_ok_nil |].
  all: assert (EM2 : ms_mem ms0 = ms_mem ms) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity).
  all: clear HF HFr HG; rewrite EM2 in HJ; rewrite ?wvb_collapse in HJ; pmkst HS; rewrite EM2.
  all: lazymatch type of Hc with
       | (_ =? _) = true => apply Z.eqb_eq in Hc;
           lazymatch type of HNX with c1s_next _ ?jj => apply (c1s_C nz jj jj u _ _ _ HNX HN5) end;
           [ exact (c1s_regs_run regs _ E _ ms0 (w_H W3) HR HS AG eq_refl) | exact HM | exact HJ | lia
           | apply LC1.c1_sh_hit; [exact HSH | exact Hnz | lia | apply Hv; exact Hc]
           | exact HSU | c1s_lr_solve ]
       | (_ =? _) = false => apply Z.eqb_neq in Hc;
           apply (c1s_C nz _ (-1) u _ _ _ HNX HN5);
           [ exact (c1s_regs_run regs _ E _ ms0 (w_H W3) HR HS AG eq_refl) | exact HM | exact HJ | lia
           | apply LC1.c1_sh_miss; [exact HSH | lia | intros HX; apply Hc; apply Hv; exact HX]
           | exact HSU | c1s_lr_solve ]
       end.
Qed.

Lemma c1s_A : forall nz j h u regs m md, c1s_next nz j -> lx_from B MT POST (C1_I5 B MT i) ->
  c1s_at4 nz j h u regs m md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C1_P4)) m (seg_rom SEGS)) md) (POST cx).
Proof.
  intros nz j h u regs m md HNX HN5 (HR & HM & HJ & Hj & HSH & HSU & HLR).
  pose proof HLR as (R19 & R23 & R24 & R25 & R26 & R27).
  pose proof (lh_laws B MT HY) as LAWS. pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof c1s_n_range as Hn. pose proof c1s_len as HL.
  pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs2 & Hs32). pose proof asan_consts as (C1 & _).
  pose proof HGF as (HF0 & HF1 & _).
  pose proof (lxc1_sh_bound bs M nz j h HSH) as Hhb.
  pose (RUNTO := paj_run_to B LAWS). pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
  pose proof HM as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSL & _) & (S60 & Hnz0 & Hnz) & _).
  pose proof HSL as (_ & _ & _ & _ & _ & L68 & _ & L78).
  set (ex := [w64 nz; w64 (2 ^ 64 - 1 - (lF cx fp + 64))]).
  assert (HSLOT : lx_slots cx W3 (c1s_cms m) (lx_env cx fp regs ex)
                    [(0x60, SOff 48 0); (0x68, SOff LA_F 32); (0x78, SOff 49 0)]).
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
    - exact (c1s_slot_at regs ex m 0x60 48 nz S60 (c1s_ew48 regs ex) Hnz0).
    - apply (lx_slot_atom cx W3 (c1s_cms m) _ 0x68 LA_F (lF cx fp) 32 L68 (c1s_ew46 regs ex)); lia.
    - exact (c1s_slot_at regs ex m 0x78 49 _ L78 (c1s_ew49 regs ex) ltac:(lia)). }
  pose proof (c1s_seat regs m md ex C1_P4 (lx_sr (c1s_ov j))
    [c1s_spill [(0x60, SOff 48 0); (0x68, SOff LA_F 32); (0x78, SOff 49 0)]] []
    HR HJ (c1s_regs_ok_l regs ex j HR R24 R27 R26) eq_refl
    (@Forall_cons _ _ _ _ (c1s_spill_ok regs ex m _ HR HSLOT) (@Forall_nil _ _)) (conj I I) I) as HS.
  assert (HEI : img_env VAL A_LIM (lx_env cx fp regs ex)) by apply lx_env_img.
  assert (SHOK : sh_ok SEGS C1S_Bx [] (lx_env cx fp regs ex) (mrestrict (w_H W3) m)) by apply Forall_nil.
  assert (U48 : U (lx_env cx fp regs ex) (SOff 48 0) = nz) by (apply U_atom; [exact (c1s_ew48 regs ex) | lia]).
  assert (U49 : U (lx_env cx fp regs ex) (SOff 49 0) = 2 ^ 64 - 1 - (lF cx fp + 64)) by (apply U_atom; [exact (c1s_ew49 regs ex) | lia]).
  remember (lx_env cx fp regs ex) as E eqn:HE.
  assert (AG : forall a, (a < 240)%nat -> ew E a = ew (lx_env cx fp regs ex) a) by (intros a _; rewrite HE; reflexivity).
  assert (S25 : sv_denot E (SOff 25 0) = Z_to_bv 64 h) by exact (c1s_S_reg regs ex E 25 (25%bv : bv 5) h HE eq_refl R25).
  unfold c1s_J in HJ. unfold c1s_ss in HS.
  destruct (c1s_j_cases j Hj) as [-> | [-> | [-> | [-> | ->]]]].
  all: psrr_branch_tok RUN BR HS SHOK C1S_SPAN; rewrite S25 in Hc; cbn [sv_denot] in Hc; rewrite c1s_bt_ge in Hc by lia.
  all: lazymatch type of Hc with
       | negb _ = true => apply negb_true_iff, Z.ltb_ge in Hc; rename Hc into HcT;
           paj_run_to_tok RUNTO HS HJ SHOK C1S_SPAN 0x7b0; [cbn [ss_mem add_cond]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |]
       | negb _ = false => apply negb_false_iff, Z.ltb_lt in Hc; rename Hc into HcF;
           paj_run_tok RUN HS HJ SHOK C1S_SPAN; [cbn [ss_mem add_cond]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |]
       end.
  all: assert (EM : ms_mem ms = m) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity).
  all: subst m; clear HF HFr HG; rewrite ?wvb_collapse in HJ.
  all: tryif (let x := constr:(HcT) in idtac) then
         (pmkst HS;
          apply (c1s_C nz _ h u _ _ _ HNX HN5);
          [ exact (c1s_regs_run regs _ E _ ms (w_H W3) HR HS AG eq_refl) | exact HM | exact HJ | lia
          | exact (LC1.c1_sh_keep bs M nz _ h HSH HcT)
          | exact HSU | c1s_lr_solve ])
       else idtac.
  all: assert (Hh1 : h = -1) by lia; subst h.
  all: psrr_branch_tok RUN BR HS SHOK C1S_SPAN; rewrite branch_eq_U, U48, U_lit in Hc by lia.
  all: lazymatch type of Hc with
       | (_ =? _) = true => apply Z.eqb_eq in Hc; rename Hc into Hz0;
           paj_run_to_tok RUNTO HS HJ SHOK C1S_SPAN 0x7b0; [cbn [ss_mem add_cond]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |]
       | (_ =? _) = false => apply Z.eqb_neq in Hc; rename Hc into Hz1;
           paj_run_tok RUN HS HJ SHOK C1S_SPAN; [cbn [ss_mem add_cond]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |]
       end.
  all: assert (EM2 : ms_mem ms0 = ms_mem ms) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity).
  all: clear HF HFr HG; rewrite <- EM2 in HM; rewrite ?wvb_collapse in HJ.
  all: tryif (let x := constr:(Hz0) in idtac) then
         (pmkst HS;
          apply (c1s_C nz _ (-1) u _ _ _ HNX HN5);
          [ exact (c1s_regs_run regs _ E _ ms0 (w_H W3) HR HS AG eq_refl) | exact HM | exact HJ | lia
          | exact (LC1.c1_sh_v0 bs M nz _ Hz0)
          | exact HSU | c1s_lr_solve ])
       else idtac.
  all: psrr_branch_tok RUN BR HS SHOK C1S_SPAN; rewrite branch_ltu_U, U49, U_lit in Hc by lia.
  all: lazymatch type of Hc with
       | (_ <? _) = true => exfalso; apply Z.ltb_lt in Hc; lia
       | (_ <? _) = false => clear Hc; paj_run_tok RUN HS HJ SHOK C1S_SPAN; [cbn [ss_mem add_cond]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |]
       end.
  all: assert (EM3 : ms_mem ms1 = ms_mem ms0) by (apply (fun H0 => frame_of_read_only _ _ _ _ H0 HF); vm_compute; reflexivity).
  all: clear HF HFr HG; rewrite <- EM3 in HM; rewrite ?wvb_collapse in HJ; pmkst HS.
  all: pose proof (c1s_call_pi _ _ _ _ HS) as HS'.
  all: assert (HR1 : c1s_regs (ms_regs ms1)) by exact (c1s_regs_run regs _ E _ ms1 (w_H W3) HR HS' AG eq_refl).
  all: assert (HLR1 : c1s_lr _ (-1) u (ms_regs ms1)) by c1s_lr_solve.
  all: pose proof HR1 as (Q2 & _ & _ & Q3 & Q4 & _).

  all: lazymatch type of HLR1 with c1s_lr ?jj _ _ _ =>
       eapply SRr_bind;
       [ apply (c1s_bcmp (ms_regs ms1) (ms_mem ms1) _ (lF cx fp + 64 + 56 * jj) (lF cx fp + 32) 0x7a0 HJ);
         [ rewrite (c1s_reg_run regs ex E _ ms1 (w_H W3) (10%bv : bv 5) 46 _ HS' AG eq_refl ltac:(lia));
           change (ew (lx_env cx fp regs ex) 46) with (ew (lx_env cx fp regs ex) LA_F); rewrite c1s_u46; unfold w64; f_equal; lia
         | rewrite (c1s_reg_run regs ex E _ ms1 (w_H W3) (11%bv : bv 5) 46 _ HS' AG eq_refl ltac:(lia));
           change (ew (lx_env cx fp regs ex) 46) with (ew (lx_env cx fp regs ex) LA_F); rewrite c1s_u46; reflexivity
         | rewrite (c1s_reg_lit E _ ms1 (w_H W3) (12%bv : bv 5) _ HS' eq_refl); reflexivity
         | exact Q2 | exact Q3 | exact Q4
         | exact (c1s_reg_code E _ ms1 (w_H W3) (1%bv : bv 5) _ HS' HEI eq_refl)
         | lia | reflexivity
         | exact (c1s_row_obj _ _ jj HJ (proj1 HM) ltac:(lia))
         | exact (c1s_mac_obj _ _ HJ (proj1 HM)) ]
       | cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hcmp & Hkeep);
         apply (c1s_Bp nz jj (-1) u regs2 mem2 md2 HNX HN5);
         [ exact (c1s_regs_pres _ _ HP HR1) | exact (c1s_mem3_keep nz _ mem2 HM Hkeep) | exact HJ2 | exact Hj | exact HSH
         | reflexivity | exact Hz1 | exact HSU | exact (c1s_lr_pres _ _ _ _ _ HP HLR1)
         | rewrite Hcmp; exact (c1s_row_mac _ jj (proj1 HM) ltac:(lia)) ] ]
       end.
Qed.

Lemma c1s_loop : forall nz, lx_from B MT POST (C1_I5 B MT i) ->
  forall d j h u regs m md, Boxreg.bx_n bs - j = Z.of_nat d -> c1s_at4 nz j h u regs m md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C1_P4)) m (seg_rom SEGS)) md) (POST cx).
Proof.
  intros nz HN5 d. induction d as [|d IH]; intros j h u regs m md Hd HA.
  - exfalso. destruct HA as (_ & _ & _ & Hj & _). lia.
  - apply (c1s_A nz j h u regs m md); [|exact HN5|exact HA].
    intros h' u' regs' m' md' HA'. apply (IH (j + 1) h' u' regs' m' md'); [lia | exact HA'].
Qed.

End e.
End d.

Lemma c1s_geo : lx_hyps B MT -> forall cx fp ly3 S3 (W3 : world SEGS) ms3 md3 k r,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(LX_CID, fp)] -> lblk B cx ly3 S3 r ->
  (lsp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= lsp0 cx /\ lsp0 cx <= 2 ^ 47 /\
   lsp0 cx - 287 <= lsp1 cx <= lsp0 cx - 256 /\ lsp1 cx mod 32 = 0) /\
  (4096 <= lF cx fp /\ lF cx fp + 512 <= alloc_ceiling /\ in_app (lF cx fp) 512 /\
   lF cx fp mod 64 = 0 /\ lSH cx fp = SHADOW_OFF + lF cx fp / 8 /\ frame_addr ly3 LX_CID fp = lF cx fp) /\
  (4096 <= r /\ r + 288 <= alloc_ceiling) /\
  (lc_n cx = 0 \/ (0 <= lc_p cx /\ lc_p cx + lc_n cx <= alloc_ceiling)).
Proof.
  intros HY cx fp ly3 S3 W3 ms3 md3 k r HB HJ HFR HBLK.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HF1 & HFapp & _ & HF64 & HSH).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EFA.
  pose proof HJ as (HAR3 & _).
  split; [exact (lx_sp_facts B MT cx HB)|].
  split; [split; [exact HF0|]; split; [exact HF1|]; split; [exact HFapp|]; split; [exact HF64|]; split; [exact HSH | exact EFA]|].
  split.
  - assert (Hin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hin) as (_ & Hr4096 & Hrceil & _).
    change (req_size LX_REG) with 288 in Hrceil. lia.
  - pose proof HB as (HPRE & _ & _ & Hpn & _). pose proof HPRE as (HAR0 & _).
    destruct Hpn as [[Hn0 _] | (Hn & Hin)]; [left; exact Hn0 | right].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hq]. lia.
Qed.

Lemma c1s_ms_eq : forall (ms3 : machine_state) pc, ms_pc_val ms3 = w64 (BASE + pc) -> ms_resv ms3 = None ->
  ms_svc_pending ms3 = None -> ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (ms_mem ms3) (seg_rom SEGS).
Proof.
  intros ms3 pc Hpc Hresv Hsvc Hrom Hfreg Hfcsr.
  destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in *. subst. reflexivity.
Qed.

Theorem c1_seg_zero : C1_SEG_zero B MT.
Proof.
  intros HY POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
  destruct HGI as (q & r & fab & bs & M & nch & HBODY & HRD).
  destruct HBODY as (HLX & Hi64 & Hk & Hacc & HBLK & HREG & HINV & HFAB & HPV & HCUR & HSL & S58 & S48 & R20 & R21).
  pose proof HLX as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
  destruct (c1s_geo HY cx fp ly3 S3 W3 ms3 md3 k r HB HJ HFR HBLK) as (HGsp & HGF & HGr & HGin).
  rewrite (c1s_ms_eq ms3 C1_P2 Hpc Hresv Hsvc Hrom Hfreg Hfcsr).
  pose proof HREGS as (G2 & G8 & G9 & G3 & G4 & G18 & G22).
  apply (c1s_zero1_pt HY POST i cx fp k acc ly3 S3 W3 r fab bs M q nch HB HFR HMO Hi64 Hk Hacc HBLK HINV HFAB
    HGsp HGF HGr HGin (ms_regs ms3) (ms_mem ms3) md3 HNEXT).
  - exact (conj G2 (conj G8 (conj G9 (conj G3 (conj G4 (conj G18 (conj G22 (conj R20 R21)))))))).
  - exact (conj HSAVED (conj HSH (conj HFLAG (conj HS10 (conj HS18 (conj HS80 (conj HINP (conj HREG (conj HPV (conj HCUR (conj HSL (conj S58 (conj S48 HRD))))))))))))).
  - exact HJ.
Qed.

Theorem c1_seg_scan0 : C1_SEG_scan0 B MT.
Proof.
  intros HY POST i HN4 HN5 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
  destruct HGI as (q & r & fab & bs & M & nch & nz & HBODY & HRD & HNZ & H20 & R19 & R23 & R25).
  destruct HBODY as (HLX & Hi64 & Hk & Hacc & HBLK & HREG & HINV & HFAB & HPV & HCUR & HSL & S58 & S48 & R20 & R21).
  pose proof HLX as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
  destruct (c1s_geo HY cx fp ly3 S3 W3 ms3 md3 k r HB HJ HFR HBLK) as (HGsp & HGF & HGr & HGin).
  rewrite (c1s_ms_eq ms3 C1_P3 Hpc Hresv Hsvc Hrom Hfreg Hfcsr).
  pose proof HREGS as (G2 & G8 & G9 & G3 & G4 & G18 & G22).
  apply (c1s_scan0_pt HY POST i cx fp k acc ly3 S3 W3 r fab bs M q nch HB HFR HMO Hi64 Hk Hacc HBLK HINV HFAB
    HGsp HGF (ms_regs ms3) (ms_mem ms3) md3 nz HN4 HN5).
  - exact (conj G2 (conj G8 (conj G9 (conj G3 (conj G4 (conj G18 (conj G22 (conj R20 R21)))))))).
  - exact R19.
  - exact R23.
  - exact R25.
  - exact (conj (conj HSAVED (conj HSH (conj HFLAG (conj HS10 (conj HS18 (conj HS80 (conj HINP (conj HREG (conj HPV (conj HCUR (conj HSL (conj S58 (conj S48 HRD))))))))))))) (conj HNZ H20)).
  - exact HJ.
Qed.

Theorem c1_seg_scan : C1_SEG_scan B MT.
Proof.
  intros HY POST i HN5 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
  destruct HGI as (q & r & fab & bs & M & nch & nz & j & h & u & HBODY & HRD & HNZ & H20 & Hj & HSHj & HSU
    & R19 & R23 & R24 & R25 & R26 & R27).
  destruct HBODY as (HLX & Hi64 & Hk & Hacc & HBLK & HREG & HINV & HFAB & HPV & HCUR & HSL & S58 & S48 & R20 & R21).
  pose proof HLX as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
  destruct (c1s_geo HY cx fp ly3 S3 W3 ms3 md3 k r HB HJ HFR HBLK) as (HGsp & HGF & HGr & HGin).
  rewrite (c1s_ms_eq ms3 C1_P4 Hpc Hresv Hsvc Hrom Hfreg Hfcsr).
  pose proof HREGS as (G2 & G8 & G9 & G3 & G4 & G18 & G22).
  apply (c1s_loop HY POST i cx fp k acc ly3 S3 W3 r fab bs M q nch HB HFR HMO Hi64 Hk Hacc HBLK HINV HFAB
    HGsp HGF HGr HGin nz HN5 (Z.to_nat (Boxreg.bx_n bs - j)) j h u (ms_regs ms3) (ms_mem ms3) md3).
  - lia.
  - split; [exact (conj G2 (conj G8 (conj G9 (conj G3 (conj G4 (conj G18 (conj G22 (conj R20 R21))))))))|].
    split; [exact (conj (conj HSAVED (conj HSH (conj HFLAG (conj HS10 (conj HS18 (conj HS80 (conj HINP (conj HREG (conj HPV (conj HCUR (conj HSL (conj S58 (conj S48 HRD))))))))))))) (conj HNZ H20))|].
    split; [exact HJ|]. split; [exact Hj|]. split; [exact HSHj|]. split; [exact HSU|].
    exact (conj R19 (conj R23 (conj R24 (conj R25 (conj R26 R27))))).
Qed.

End c.
End b.
End a.
