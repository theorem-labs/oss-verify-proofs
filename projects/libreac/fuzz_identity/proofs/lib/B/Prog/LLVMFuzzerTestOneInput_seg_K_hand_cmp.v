(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8w.v:289-290, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_K_hand_cat.v, with its addresses changed; 437 of its 501 lines of code are new or changed and 212 lines of the source are left out. *)
(* Piece k_cmp of seg_K of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B), +0x19dc .. +0x19f8
   (fuzz_identity.asan-ubsan 0x82150 .. 0x8216c, the n_r = 0 path). The slots: 0x82150 a0 := s2 (nm),
   0x82154 a1 := s9 (SF + 528, exp_nm), 0x82158 the call of the strcmp wrapper (0x421fc, k_strcmp_at),
   0x8215c the branch to 0x82614 when a0 <> 0 (the harness's abort, not taken), 0x82160 a0 := the 8 bytes at
   s1 + 184 (dp; the machine frame has no ASan check), 0x82164 a1 := s10 (SF + 592, exp_dp), 0x82168 the strcmp
   wrapper again; the piece ends at that call's return slot 0x8216c with a0 = 0. Both compares meet at the NUL:
   with n_r = 0, KH gives the same byte list n_EXP_NM ++ [0] (n_EXP_DP ++ [0]) at the heap buffer and at the frame
   buffer, and that list has no zero byte before its end (KModel.nzb_EXP_NM, nzb_EXP_DP), so str_meet holds at
   k = its length with c1 = c2 = 0 (kcmp_meet). The branch at 0x8215c is decided by pinning a0 to the literal 0 in
   the symbolic state. The heap ranges' shadow facts come from the block lemmas, the frame ranges' from KH's
   sh_zero clauses carried by kkeep's frame clause; kkeep is composed after each wrapper call from the wrapper's
   "memory outside [sp - 2 * ESTACK, sp) kept" clause at sp = mf (kcmp_keep). No trap is on this stretch. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81 IdentBlkTail.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
check_str reac_box_catalogue reac_box_catalogue_defect.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_seg_K_hand_stmt LLVMFuzzerTestOneInput_seg_K_base.
Import ListNotations. Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number". Open Scope Z_scope.
(* YC4b turns lia's division and modulo handling off for every file that loads it; the alignment and shadow
   arithmetic of this piece needs it, so this file turns it back on (as lib/B/Prog/LLVMFuzzerTestOneInput_seg_L.v). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- the symbolic states ------------------------------------------------------------------------------------ *)
(* +0x19dc: two register moves and the call; no memory. *)
Definition kcmp_ss1 : sstate := mkSS 0x19dc sr_atoms [] None (mkFacts [] [] []).
(* +0x19e8: the machine frame's slot mf+184 (dp), read-only; atom 32 is dp. a0 is pinned to 0 afterwards. *)
Definition kcmp_rmf : YP09.region :=
  YP09.mkRegion (Some 9%nat) 184 192 184 184 [YP09.mkChunk 184 (CVal 8 (SOff 32 0))].
Definition kcmp_ss2 : sstate := mkSS 0x19e8 sr_atoms [kcmp_rmf] None (mkFacts [] [] []).

(* The callee-saved side condition of aregs_preserved, with the register literal computed. *)
Ltac kcmp_cs :=
unfold acallee_saved;
match goal with
| |- context [bv_unsigned ?x] =>
  let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v
end; clear; lia.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Section b. Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms. Variable MT : ameter_ops. Variables XM_LIB XN_LIB : Z -> Z. Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type. Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable G : list (Z * Z).
Hypothesis HPRE : KPRE B RLO RHI LLVMF_STK arodata_okS G.
Let LAWS := k_laws B RLO RHI LLVMF_STK arodata_okS G HPRE.
Let RUNP := SRr_run_pi_AJ B LAWS.  Let RUNC := SRr_run_pi_AJ_call B LAWS.
#[local] Notation KHn := (KH B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation KCn := (KC B LLVMF_STK).
#[local] Notation KGEOM := (k_geom B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS G HPRE).
#[local] Notation KVMHI := (k_vm_hi B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS G HPRE).
#[local] Notation AJn g pos ly2 S2 W2 mem md :=
  (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem md (4 * Z.of_nat (m_nrec g) + 7)).

(* ---- small helpers -------------------------------------------------------------------------------------------- *)
Lemma kcmp_pres1 : forall (r : bv 5) (regs regs' : bvmap 5 word),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros r regs regs' H Hr. specialize (H (bv_unsigned r) Hr). rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* A byte of a string that bytes_at8 places. *)
Lemma kcmp_at8 : forall (W : world SEGS) mem x (bs : list byte) j, bytes_at8 W mem x bs -> (j < length bs)%nat ->
  aview SEGS (w_H W) mem (x + Z.of_nat j) = Some (RcIdentModel.bz (RcIdentModel.nthb bs j)).
Proof.
intros W mem x bs j Hb Hj. unfold bytes_at8 in Hb.
assert (Hj' : (j < length (map (fun b : byte => bv_unsigned b) bs))%nat) by (rewrite length_map; exact Hj).
destruct (Hb j Hj') as [Hv Hr].
rewrite (aview_of_val_mem1 SEGS (w_H W) mem _ _ Hv Hr). f_equal.
unfold RcIdentModel.bz, RcIdentModel.nthb. clear. revert j.
induction bs as [|b r IH]; intros [|j]; cbn [nth map]; try reflexivity. apply IH.
Qed.

(* Two copies of one NUL-terminated string with no zero byte before its end meet at the NUL, both bytes 0. *)
Lemma kcmp_meet : forall (W : world SEGS) mem x y (l : list byte) k,
  Z.of_nat (length l) = k -> KModel.nzb l = true ->
  bytes_at8 W mem x (l ++ [RcIdentModel.zb 0]) -> bytes_at8 W mem y (l ++ [RcIdentModel.zb 0]) ->
  AStrcmpDef.str_meet SEGS W mem x y k 0 0.
Proof.
intros W mem x y l k Hk Hnz Bx By.
assert (Hlen : length (l ++ [RcIdentModel.zb 0]) = S (length l)) by (rewrite length_app; cbn [length]; lia).
unfold AStrcmpDef.str_meet. split; [clear - Hk; lia|].
split.
{ intros i Hi. exists (RcIdentModel.bz (RcIdentModel.nthb l (Z.to_nat i))).
  assert (Hj : (Z.to_nat i < length l)%nat) by (clear - Hi Hk; lia).
  assert (E : RcIdentModel.nthb (l ++ [RcIdentModel.zb 0]) (Z.to_nat i) = RcIdentModel.nthb l (Z.to_nat i))
    by (unfold RcIdentModel.nthb; apply app_nth1; exact Hj).
  replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by (clear - Hi; lia).
  replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by (clear - Hi; lia).
  rewrite (kcmp_at8 W mem x _ _ Bx) by (rewrite Hlen; clear - Hj; lia).
  rewrite (kcmp_at8 W mem y _ _ By) by (rewrite Hlen; clear - Hj; lia).
  rewrite E. split; [reflexivity|]. split; [reflexivity|].
  exact (KModel.nzb_nth l (Z.to_nat i) Hnz Hj). }
assert (E0 : RcIdentModel.bz (RcIdentModel.nthb (l ++ [RcIdentModel.zb 0]) (length l)) = 0).
{ unfold RcIdentModel.nthb. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
rewrite <- Hk.
rewrite (kcmp_at8 W mem x _ _ Bx) by (rewrite Hlen; lia).
rewrite (kcmp_at8 W mem y _ _ By) by (rewrite Hlen; lia).
rewrite E0. split; [reflexivity|]. split; [reflexivity|]. right. reflexivity.
Qed.

(* kkeep composed with a step that keeps every byte outside the wrappers' window [mf - 2 * ESTACK, mf). *)
Lemma kcmp_keep : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2, KHn g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 ->
  forall mem mem', kkeep B g pos mf ly2 S2 W2 mem2 mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
     aview SEGS (w_H W2) mem' a = aview SEGS (w_H W2) mem a) ->
  kkeep B g pos mf ly2 S2 W2 mem2 mem'.
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH mem mem' (K1 & K2 & K3) HF.
pose proof (KGEOM g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH) as
  (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & Hin4).
pose proof asan_consts as (C1 & _).
pose proof HKH as (HJ2 & _). pose proof (proj1 HJ2) as HAR2.
unfold kkeep. split; [|split].
- intros a Ha Hna.
  rewrite (HF a); [exact (K1 a Ha Hna) | clear - Ha C1; lia | clear - Hna; lia].
- intros b n i Hin Hi.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b n HAR2 Hin) as (_ & Hb4 & Hbc & _).
  rewrite (HF (b + i)); [exact (K2 b n i Hin Hi) | clear - Hi Hb4 Hbc C1; lia | unfold ESTACK; clear - Hi Hb4 Hbc G1; lia].
- intros a Hin Hnc Hns.
  assert (Ha : 0 <= a < alloc_ceiling).
  { pose proof Hin as Hin'. unfold in_zr, frame_rng in Hin'. cbn [fst snd] in Hin'. rewrite G12 in Hin'.
    change (fs_frame_bytes 4) with 1024 in Hin'. clear - Hin' G8 G9 G14 G15. lia. }
  rewrite (HF a); [exact (K3 a Hin Hnc Hns) | clear - Ha C1; lia | unfold ESTACK; clear - Ha G1; lia].
Qed.

(* A string in a live heap block, carried from the start state to a piece's state. *)
Lemma kcmp_blk : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2, KHn g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 ->
  forall memT mdT b n0 (l : list byte) k,
  AJn g pos ly2 S2 W2 memT mdT -> kkeep B g pos mf ly2 S2 W2 mem2 memT ->
  In (b, n0) (ablocks B ly2 S2) -> Z.of_nat (length l) = k -> k + 1 <= req_size n0 ->
  bytes_at8 W2 mem2 b (l ++ [RcIdentModel.zb 0]) ->
  bytes_at8 W2 memT b (l ++ [RcIdentModel.zb 0]) /\ 4096 <= b /\ b + k + 1 <= alloc_ceiling /\
  amem_range b (k + 1) /\ range_addressable (aview SEGS (w_H W2) memT) SHADOW_OFF b (k + 1) /\
  shadow_hull_vis (aview SEGS (w_H W2) memT) b (k + 1).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH memT mdT b n0 l k HJ HKP Hin Hk Hkn HB.
pose proof (proj1 HJ) as HART.
destruct (al_blocks _ _ LAWS ly2 S2 W2 memT mdT b n0 HART Hin) as (_ & Hb4 & Hbc & _).
assert (Hk0 : 0 <= k) by (clear - Hk; lia).
split.
{ unfold bytes_at8 in *. apply (k_garr8_moved (w_H W2) (w_H W2) mem2 memT _ _); [|exact HB].
  intros j Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj.
  apply (proj1 (proj2 HKP) b n0 j Hin). clear - Hj Hk Hkn. lia. }
split; [exact Hb4|]. split; [clear - Hbc Hkn; lia|].
assert (H1 : b <= b) by (clear; lia).
assert (H2 : b + (k + 1) <= b + req_size n0) by (clear - Hkn; lia).
assert (H3 : 0 < k + 1) by (clear - Hk0; lia).
split; [exact (amem_range_of_block SEGS B LAWS ly2 S2 W2 memT mdT b n0 b (k + 1) HART Hin H1 H2)|].
split; [exact (range_addressable_of_block SEGS B LAWS ly2 S2 W2 memT mdT b n0 b (k + 1) HART Hin H1 H2)|].
exact (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 memT mdT b n0 b (k + 1) HART Hin H1 H2 H3).
Qed.

(* A string in the entry's frame (outside `count`), carried from the start state to a piece's state. *)
Lemma kcmp_frm : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2, KHn g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 ->
  forall memT mdT off N (l : list byte) k,
  AJn g pos ly2 S2 W2 memT mdT -> kkeep B g pos mf ly2 S2 W2 mem2 memT ->
  0 <= off -> off mod 8 = 0 -> N mod 8 = 0 -> off + N <= 720 ->
  Z.of_nat (length l) = k -> k + 1 <= N ->
  sh_zero W2 mem2 (SFa g pos + off) N ->
  bytes_at8 W2 mem2 (SFa g pos + off) (l ++ [RcIdentModel.zb 0]) ->
  bytes_at8 W2 memT (SFa g pos + off) (l ++ [RcIdentModel.zb 0]) /\
  4096 <= SFa g pos + off /\ SFa g pos + off + k + 1 <= alloc_ceiling /\
  amem_range (SFa g pos + off) (k + 1) /\
  range_addressable (aview SEGS (w_H W2) memT) SHADOW_OFF (SFa g pos + off) (k + 1) /\
  shadow_hull_vis (aview SEGS (w_H W2) memT) (SFa g pos + off) (k + 1).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH memT mdT off N l k HJ HKP Ho0 Ho8 HN8 HoN Hk HkN HSZ HB.
pose proof (KGEOM g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH) as
  (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & Hin4).
pose proof asan_consts as (C1 & _).
pose proof (proj1 HJ) as HART.
destruct HKP as (_ & _ & K3).
assert (Hk0 : 0 <= k) by (clear - Hk; lia).
assert (HS8 : SFa g pos mod 8 = 0) by (clear - G11; lia).
assert (Hsh : forall i, shadow_of_addr SHADOW_OFF (SFa g pos + off) + i = shadow_addr (SFa g pos) + off / 8 + i).
{ intros i. rewrite (shadow_of_addr_aligned_off SHADOW_OFF (SFa g pos) off HS8). unfold shadow_of_addr.
  rewrite G13. reflexivity. }
split.
{ unfold bytes_at8 in *. apply (k_garr8_moved (w_H W2) (w_H W2) mem2 memT _ _); [|exact HB].
  intros j Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj.
  apply K3.
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite G12. change (fs_frame_bytes 4) with 1024.
    clear - Hj Hk HkN HoN Ho0. lia.
  - unfold V_cnt. clear - Hj Hk HkN HoN Ho0. lia.
  - intros Hw. apply (fshadow_not_app (SFa g pos) 128 (SFa g pos) 1024 (SFa g pos + off + j));
      [exact G8 | clear - G9 C1; lia | exact G10 | | clear - Hj Hk HkN HoN Ho0; lia].
    rewrite Hw, G13. unfold SHADOW_OFF. clear. lia. }
split; [clear - G8 Ho0; lia|].
split; [clear - G9 HoN HkN; lia|].
split.
{ apply (amem_range_sub_app (SFa g pos) 1024 (SFa g pos + off) (k + 1) G10 G9).
  - clear - Ho0. lia.
  - clear - HoN HkN. lia.
  - clear - Hk0. lia. }
split.
{ apply (range_addressable_sub (aview SEGS (w_H W2) memT) SHADOW_OFF (SFa g pos + off) N).
  - apply zero_shadow_range; [clear - HS8 Ho8; lia | exact HN8 |].
    intros i Hi. rewrite Hsh. rewrite K3.
    + rewrite <- Hsh. exact (HSZ i Hi).
    + right. unfold in_zr. cbn [fst snd]. rewrite G12. change (fs_frame_bytes 4) with 1024.
      clear - Hi Ho0 Ho8 HN8 HoN. lia.
    + intros Hc. apply (fshadow_not_app (SFa g pos) 128 (SFa g pos) 1024 (shadow_addr (SFa g pos) + off / 8 + i)).
      * exact G8.
      * clear - G9 C1. lia.
      * exact G10.
      * rewrite G13. unfold SHADOW_OFF. clear - Hi Ho0 Ho8 HN8 HoN. lia.
      * unfold V_cnt in Hc. clear - Hc. lia.
    + clear - Hi Ho0 Ho8 HN8 HoN. lia.
  - clear. lia.
  - clear - HkN. lia. }
apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 memT mdT 4 pos (SFa g pos + off) (k + 1) HART Hin4).
- rewrite G12. clear - Ho0. lia.
- rewrite G12. change (fs_frame_bytes 4) with 1024. clear - HoN HkN. lia.
- clear - Hk0. lia.
Qed.

(* One strcmp wrapper call at sp = mf on two copies of one string: a0 = 0, the journal, the registers the
   callee keeps, and every byte outside [mf - 2 * ESTACK, mf). *)
Lemma kcmp_call : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2, KHn g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 ->
  forall regsT memT mdT x y (l : list byte) k raw,
  AJn g pos ly2 S2 W2 memT mdT ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 2 = w64 mf ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  KModel.nzb l = true -> Z.of_nat (length l) = k -> k < 64 ->
  bytes_at8 W2 memT x (l ++ [RcIdentModel.zb 0]) -> bytes_at8 W2 memT y (l ++ [RcIdentModel.zb 0]) ->
  4096 <= x -> x + k + 1 <= alloc_ceiling -> 4096 <= y -> y + k + 1 <= alloc_ceiling ->
  amem_range x (k + 1) -> amem_range y (k + 1) ->
  range_addressable (aview SEGS (w_H W2) memT) SHADOW_OFF x (k + 1) ->
  shadow_hull_vis (aview SEGS (w_H W2) memT) x (k + 1) ->
  range_addressable (aview SEGS (w_H W2) memT) SHADOW_OFF y (k + 1) ->
  shadow_hull_vis (aview SEGS (w_H W2) memT) y (k + 1) ->
  SRr SEGS W2 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___interceptor_trampoline_strcmp)) memT (seg_rom SEGS)) mdT)
  (fun W' c' => W' = W2 /\ exists regs' mem' md',
    c' = mkCfg (mkst regs' raw mem' (seg_rom SEGS)) md' /\ AJn g pos ly2 S2 W2 mem' md' /\
    aregs_preserved regsT regs' /\ getr regs' 10 = w64 0 /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
      aview SEGS (w_H W2) mem' a = aview SEGS (w_H W2) memT a)).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regsT memT mdT x y l k raw HJ Hx Hy Hsp Hgp Htp Hra Hraw
  NZ Hk Hk64 Bx By Hx0 Hx1 Hy0 Hy1 Mx My Rx Vx Ry Vy.
pose proof (KGEOM g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _).
pose proof asan_consts as (C1 & _).
assert (Hmf : spZ regsT = mf).
{ unfold spZ. rewrite Hsp. apply unsigned_lit_small. clear - G1 G2 G3 C1. lia. }
assert (P1 : 0 < x) by (clear - Hx0; lia).
assert (P2 : 0 < y) by (clear - Hy0; lia).
assert (P3 : k + 1 < 2 ^ 32) by (clear - Hk64; lia).
assert (P4 : x + k + 1 <= 2 ^ 63) by (clear - Hx1 C1; lia).
assert (P5 : y + k + 1 <= 2 ^ 63) by (clear - Hy1 C1; lia).
assert (P6 : spZ regsT = e_sp0 g + (mf - e_sp0 g)) by (rewrite Hmf; clear; lia).
assert (P7 : (mf - e_sp0 g) mod 16 = 0) by (clear - G4 G6; lia).
assert (P8 : mf - e_sp0 g <= 0) by (clear - G2; lia).
assert (P9 : 2 * ESTACK - (mf - e_sp0 g) <= LLVMF_STK) by (unfold ESTACK; clear - G7; lia).
pose proof (kcmp_meet W2 memT x y l k Hk NZ Bx By) as P10.
assert (Sx : src_ok SEGS W2 regsT memT x (k + 1)).
{ intros a Ha. split.
  - replace a with (x + Z.of_nat (Z.to_nat (a - x))) by (clear - Ha; lia).
    rewrite (kcmp_at8 W2 memT x _ (Z.to_nat (a - x)) Bx); [discriminate|].
    rewrite length_app. cbn [length]. clear - Ha Hk. lia.
  - rewrite Hmf. unfold ESTACK. clear - Ha Hx1 G1. lia. }
assert (Sy : src_ok SEGS W2 regsT memT y (k + 1)).
{ intros a Ha. split.
  - replace a with (y + Z.of_nat (Z.to_nat (a - y))) by (clear - Ha; lia).
    rewrite (kcmp_at8 W2 memT y _ (Z.to_nat (a - y)) By); [discriminate|].
    rewrite length_app. cbn [length]. clear - Ha Hk. lia.
  - rewrite Hmf. unfold ESTACK. clear - Ha Hy1 G1. lia. }
assert (Wx : forall a, x <= a <= x + k ->
  ~ (e_sp0 g + (mf - e_sp0 g) - 2 * ESTACK <= a < e_sp0 g + (mf - e_sp0 g))).
{ intros a Ha. unfold ESTACK. clear - Ha Hx1 G1. lia. }
assert (Wy : forall a, y <= a <= y + k ->
  ~ (e_sp0 g + (mf - e_sp0 g) - 2 * ESTACK <= a < e_sp0 g + (mf - e_sp0 g))).
{ intros a Ha. unfold ESTACK. clear - Ha Hy1 G1. lia. }
eapply SRr_mono.
{ exact (k_strcmp_at B RLO RHI LLVMF_STK arodata_okS G HPRE W2 regsT memT LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g)
    (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 mdT (4 * Z.of_nat (m_nrec g) + 7) x y k 0 0 (mf - e_sp0 g) raw
    HJ Hx Hy P1 P2 P3 P4 P5 P6 P7 P8 P9 Hgp Htp Hra Hraw P10 Sx Sy Wx Wy Mx My Rx Vx Ry Vy). }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & HP' & Hres & Hfr & _).
split; [reflexivity|]. exists regs', mem', md'.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP'|]. split; [exact Hres|].
intros a Ha Hna. apply Hfr; [exact Ha|]. clear - Hna. lia.
Qed.

(* ---- +0x19dc .. +0x19e8: a0 := nm, a1 := exp_nm, strcmp; a0 = 0 at its return ---------------------------------- *)
Lemma kcmp_A : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2, KHn g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 ->
  forall regs mem md (Q : world SEGS -> config -> Prop),
  KCn g pos mf tk ly2 S2 W2 mem2 regs mem md -> KR g pos regs -> getr regs 18 = w64 nm ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' -> KR g pos regs' -> getr regs' 10 = w64 0 ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x19e8) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x19dc) regs mem md) Q.
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs mem md Q
  (HJ & HKP & Rsp & Rs1 & Rs0 & Rgp & Rtp & Rtk & Rsh) (R22 & R25 & R26) R18 HK.
pose proof (KGEOM g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH) as
  (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & Hin4).
pose proof asan_consts as (C1 & _).
pose proof HKH as (_ & _ & _ & _ & _ & _ & HHB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HSZn & _ & HWOK & HR0 & Hr0).
destruct (KModel.n_r0 _ Hr0) as [Hwok Hfits].
destruct (HWOK Hwok) as [BFn _].
destruct (HR0 Hr0) as (BHn & _ & _).
pose proof (KModel.nzb_EXP_NM _ Hwok) as NZ.
pose proof (SlotModel.n_ln_le _ Hwok) as Lln.
destruct (KModel.fits_unfold _ Hfits) as (Fn & _ & _).
assert (Hk : Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) = SlotModel.n_ln (e_pl g)) by reflexivity.
assert (Hinn : In (nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1) (ablocks B ly2 S2)).
{ destruct HHB as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left.
  cbn. left. reflexivity. }
pose proof (req_size_pos (Z.max (SlotModel.t_cap_name (e_pl g)) 1) ltac:(clear; lia)) as Rq.
assert (Kn1 : SlotModel.n_ln (e_pl g) + 1 <= req_size (Z.max (SlotModel.t_cap_name (e_pl g)) 1))
  by (clear - Fn Rq; lia).
assert (KnN : SlotModel.n_ln (e_pl g) + 1 <= N_nm) by (unfold N_nm; clear - Lln; lia).
assert (Kl64 : SlotModel.n_ln (e_pl g) < 64) by (clear - Lln; lia).
assert (O0 : 0 <= V_nm) by (unfold V_nm; clear; lia).
assert (O8 : V_nm mod 8 = 0) by reflexivity.
assert (N8 : N_nm mod 8 = 0) by reflexivity.
assert (ON : V_nm + N_nm <= 720) by (unfold V_nm, N_nm; clear; lia).
(* the run *)
unfold cfg_at. change (w64 (BASE + 0x19dc)) with (Z_to_bv 64 (BASE + 0x19dc)).
remember (Eimg (Ereg regs [])) as E1 eqn:HE1.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply Eimg_env).
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs r)
  by (intros n r Hn; rewrite HE1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS1 : st_ok_pi SEGS VAL E1 kcmp_ss1
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x19dc)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kcmp_ss1. apply pa_entry_st_ok_full.
  - rewrite HE1. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn [pairwise_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
paj_run_shc RUNP RUNC HS1 HJ.
{ apply awr_ok_nil. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem a).
{ intros a Ha _. apply (kept_of_frame E1 _ (w_H W2) mem (ms_mem ms) (fun _ => False) HFr); [| exact Ha | intros []].
  intros bb wlo whi aa Hin Hr. unfold kcmp_ss1, windows in Hin. cbn in Hin. destruct Hin. }
clear HF HFr HG.
pose proof (kcmp_keep g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH mem (ms_mem ms) HKP KEEP1) as HKP1.
prreg HS1 (10%bv : bv 5) R1_10. prreg HS1 (11%bv : bv 5) R1_11. prreg HS1 (1%bv : bv 5) R1_1.
prreg HS1 (2%bv : bv 5) R1_2. prreg HS1 (3%bv : bv 5) R1_3. prreg HS1 (4%bv : bv 5) R1_4.
prreg HS1 (8%bv : bv 5) R1_8. prreg HS1 (9%bv : bv 5) R1_9. prreg HS1 (21%bv : bv 5) R1_21.
prreg HS1 (22%bv : bv 5) R1_22. prreg HS1 (23%bv : bv 5) R1_23. prreg HS1 (25%bv : bv 5) R1_25.
prreg HS1 (26%bv : bv 5) R1_26.
rewrite (EE1 18%nat 18%bv eq_refl), R18 in R1_10.
rewrite (EE1 25%nat 25%bv eq_refl), R25 in R1_11.
rewrite (EE1 2%nat 2%bv eq_refl), Rsp in R1_2. rewrite (EE1 3%nat 3%bv eq_refl), Rgp in R1_3.
rewrite (EE1 4%nat 4%bv eq_refl), Rtp in R1_4. rewrite (EE1 8%nat 8%bv eq_refl), Rs0 in R1_8.
rewrite (EE1 9%nat 9%bv eq_refl), Rs1 in R1_9. rewrite (EE1 21%nat 21%bv eq_refl), Rtk in R1_21.
rewrite (EE1 22%nat 22%bv eq_refl), R22 in R1_22. rewrite (EE1 23%nat 23%bv eq_refl), Rsh in R1_23.
rewrite (EE1 25%nat 25%bv eq_refl), R25 in R1_25. rewrite (EE1 26%nat 26%bv eq_refl), R26 in R1_26.
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + 0x19e8))) by (apply ret_ok_codeptr_v; [clear; lia | reflexivity]).
destruct (kcmp_blk g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_mem ms) _ nm _ _ _ HJ HKP1 Hinn Hk Kn1 BHn)
  as (Bx & Hx0 & Hx1 & Mx & Rx & Vx).
destruct (kcmp_frm g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_mem ms) _ V_nm N_nm _ _ HJ HKP1
  O0 O8 N8 ON Hk KnN HSZn BFn) as (By & Hy0 & Hy1 & My & Ry & Vy).
pmkst HS1.
eapply SRr_bind.
{ exact (kcmp_call g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_regs ms) (ms_mem ms) _ nm (SFa g pos + V_nm)
    (SlotModel.n_EXP_NM (e_pl g)) (SlotModel.n_ln (e_pl g)) _ HJ R1_10 R1_11 R1_2 R1_3 R1_4 R1_1 Hraw
    NZ Hk Kl64 Bx By Hx0 Hx1 Hy0 Hy1 Mx My Rx Vx Ry Vy). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & A10 & HF3).
pose proof (kcmp_keep g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_mem ms) mem3 HKP1 HF3) as HKP3.
apply (HK regs3 mem3 md3).
- split; [exact HJ3|]. split; [exact HKP3|].
  split; [rewrite (kcmp_pres1 2%bv _ _ HP3) by kcmp_cs; exact R1_2|].
  split; [rewrite (kcmp_pres1 9%bv _ _ HP3) by kcmp_cs; exact R1_9|].
  split; [rewrite (kcmp_pres1 8%bv _ _ HP3) by kcmp_cs; exact R1_8|].
  split; [rewrite (kcmp_pres1 3%bv _ _ HP3) by kcmp_cs; exact R1_3|].
  split; [rewrite (kcmp_pres1 4%bv _ _ HP3) by kcmp_cs; exact R1_4|].
  split; [rewrite (kcmp_pres1 21%bv _ _ HP3) by kcmp_cs; exact R1_21|].
  rewrite (kcmp_pres1 23%bv _ _ HP3) by kcmp_cs; exact R1_23.
- split; [rewrite (kcmp_pres1 22%bv _ _ HP3) by kcmp_cs; exact R1_22|].
  split; [rewrite (kcmp_pres1 25%bv _ _ HP3) by kcmp_cs; exact R1_25|].
  rewrite (kcmp_pres1 26%bv _ _ HP3) by kcmp_cs; exact R1_26.
- exact A10.
Qed.

(* ---- +0x19e8 .. +0x19f8: the abort test (a0 = 0), a0 := dp, a1 := exp_dp, strcmp; a0 = 0 at its return -------- *)
Lemma kcmp_B : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2, KHn g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 ->
  forall regs mem md (Q : world SEGS -> config -> Prop),
  KCn g pos mf tk ly2 S2 W2 mem2 regs mem md -> KR g pos regs -> getr regs 10 = w64 0 ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' -> getr regs' 10 = w64 0 ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x19f8) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x19e8) regs mem md) Q.
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs mem md Q
  (HJ & HKP & Rsp & Rs1 & Rs0 & Rgp & Rtp & Rtk & Rsh) (R22 & R25 & R26) R10 HK.
pose proof (KGEOM g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH) as
  (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & Hin4).
pose proof asan_consts as (C1 & _).
pose proof HKH as (_ & _ & _ & _ & _ & _ & HHB & _ & _ & _ & _ & _ & _ & _ & V184 & _ & _ & _ & _ & _ & _ &
  _ & HSZd & HWOK & HR0 & Hr0).
destruct (KModel.n_r0 _ Hr0) as [Hwok Hfits].
destruct (HWOK Hwok) as [_ BFd].
destruct (HR0 Hr0) as (_ & _ & BHd).
pose proof (KModel.nzb_EXP_DP _ Hwok) as NZ.
pose proof (SlotModel.n_ld_le _ Hwok) as Lld.
destruct (KModel.fits_unfold _ Hfits) as (_ & _ & Fd).
assert (Hk : Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))) = SlotModel.n_ld (e_pl g)) by reflexivity.
assert (Hk0 : 0 <= SlotModel.n_ld (e_pl g)) by (rewrite <- Hk; clear; lia).
assert (Hind : In (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) (ablocks B ly2 S2)).
{ destruct HHB as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left.
  cbn. right. right. left. reflexivity. }
pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) ltac:(clear; lia)) as Rq.
assert (Kn1 : SlotModel.n_ld (e_pl g) + 1 <= req_size (Z.max (SlotModel.t_cap_disp (e_pl g)) 1))
  by (clear - Fd Rq; lia).
assert (KnN : SlotModel.n_ld (e_pl g) + 1 <= N_dp) by (unfold N_dp; clear - Lld; lia).
assert (Kl64 : SlotModel.n_ld (e_pl g) < 64) by (clear - Lld; lia).
assert (O0 : 0 <= V_dp) by (unfold V_dp; clear; lia).
assert (O8 : V_dp mod 8 = 0) by reflexivity.
assert (N8 : N_dp mod 8 = 0) by reflexivity.
assert (ON : V_dp + N_dp <= 720) by (unfold V_dp, N_dp; clear; lia).
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem md dp _ HAR Hind) as (_ & Hd4 & Hdc & _).
assert (Hdp64 : 0 <= dp < 2 ^ 64) by (clear - Hd4 Hdc Rq C1; lia).
assert (M184 : val_mem SEGS (rd W2 mem) (mf + 184) 8 dp).
{ apply (KVMHI g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH mem (mf + 184) 8 dp HKP).
  - clear. lia.
  - clear - G2 G3. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  - exact V184. }
(* the run *)
unfold cfg_at. change (w64 (BASE + 0x19e8)) with (Z_to_bv 64 (BASE + 0x19e8)).
remember (Eimg (Ereg regs [Z_to_bv 64 dp])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs r)
  by (intros n r Hn; rewrite HE2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E2_32 : ew E2 32 = Z_to_bv 64 dp)
  by (rewrite HE2, Eimg_low by (clear; unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U2_9 : bv_unsigned (ew E2 9) = mf).
{ rewrite (EE2 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - G1 G2 G3 C1. lia. }
assert (HS2a : st_ok_pi SEGS VAL E2 kcmp_ss2
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x19e8)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kcmp_ss2. apply pa_entry_st_ok_full.
  - rewrite HE2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold kcmp_rmf, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2_9. split; [clear - G1 C1; lia|]. split; [clear - G1 G2 G3; lia|].
    split; [intros o Ho; clear - Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E2 _ mf 184 8 (SOff 32 0) dp).
    + cbn [sv_denot]. rewrite E2_32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + clear - Hdp64. cbn. lia.
    + clear. cbn. lia.
    + exact M184.
  - cbn [pairwise_disjoint all_disjoint]. repeat match goal with |- _ /\ _ => split end; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
(* a0 = 0: pin it, so that the abort test at 0x8215c is decided *)
assert (H10' : getr (ms_regs (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x19e8)) mem (seg_rom SEGS))))
  (10%bv : bv 5) = Z_to_bv 64 0) by (cbn [restrict ms_regs mkst]; exact R10).
pose proof (st_ok_pi_pin_reg' E2 kcmp_ss2 _ (10%bv : bv 5) 0 HS2a H10' ltac:(vm_compute; reflexivity)) as HS2.
clear HS2a H10'. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts kcmp_ss2] in HS2.
paj_run_shc RUNP RUNC HS2 HJ.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [unfold kcmp_rmf; cbn; clear; lia | apply awr_ok_nil]. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem a).
{ intros a Ha _. apply (kept_of_frame E2 _ (w_H W2) mem (ms_mem ms) (fun _ => False) HFr); [| exact Ha | intros []].
  intros bb wlo whi aa Hin Hr. unfold windows, kcmp_rmf in Hin. cbn in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. clear - Hr. lia. }
clear HF HFr HG.
pose proof (kcmp_keep g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH mem (ms_mem ms) HKP KEEP2) as HKP2.
prreg HS2 (10%bv : bv 5) R2_10. prreg HS2 (11%bv : bv 5) R2_11. prreg HS2 (1%bv : bv 5) R2_1.
prreg HS2 (2%bv : bv 5) R2_2. prreg HS2 (3%bv : bv 5) R2_3. prreg HS2 (4%bv : bv 5) R2_4.
prreg HS2 (8%bv : bv 5) R2_8. prreg HS2 (9%bv : bv 5) R2_9. prreg HS2 (21%bv : bv 5) R2_21.
prreg HS2 (23%bv : bv 5) R2_23.
rewrite E2_32 in R2_10.
rewrite (EE2 26%nat 26%bv eq_refl), R26 in R2_11.
rewrite (EE2 2%nat 2%bv eq_refl), Rsp in R2_2. rewrite (EE2 3%nat 3%bv eq_refl), Rgp in R2_3.
rewrite (EE2 4%nat 4%bv eq_refl), Rtp in R2_4. rewrite (EE2 8%nat 8%bv eq_refl), Rs0 in R2_8.
rewrite (EE2 9%nat 9%bv eq_refl), Rs1 in R2_9. rewrite (EE2 21%nat 21%bv eq_refl), Rtk in R2_21.
rewrite (EE2 23%nat 23%bv eq_refl), Rsh in R2_23.
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + 0x19f8))) by (apply ret_ok_codeptr_v; [clear; lia | reflexivity]).
destruct (kcmp_blk g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_mem ms) _ dp _ _ _ HJ HKP2 Hind Hk Kn1 BHd)
  as (Bx & Hx0 & Hx1 & Mx & Rx & Vx).
destruct (kcmp_frm g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_mem ms) _ V_dp N_dp _ _ HJ HKP2
  O0 O8 N8 ON Hk KnN HSZd BFd) as (By & Hy0 & Hy1 & My & Ry & Vy).
pmkst HS2.
eapply SRr_bind.
{ exact (kcmp_call g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_regs ms) (ms_mem ms) _ dp (SFa g pos + V_dp)
    (SlotModel.n_EXP_DP (e_pl g)) (SlotModel.n_ld (e_pl g)) _ HJ R2_10 R2_11 R2_2 R2_3 R2_4 R2_1 Hraw
    NZ Hk Kl64 Bx By Hx0 Hx1 Hy0 Hy1 Mx My Rx Vx Ry Vy). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & A10 & HF3).
pose proof (kcmp_keep g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_mem ms) mem3 HKP2 HF3) as HKP3.
apply (HK regs3 mem3 md3); [|exact A10].
split; [exact HJ3|]. split; [exact HKP3|].
split; [rewrite (kcmp_pres1 2%bv _ _ HP3) by kcmp_cs; exact R2_2|].
split; [rewrite (kcmp_pres1 9%bv _ _ HP3) by kcmp_cs; exact R2_9|].
split; [rewrite (kcmp_pres1 8%bv _ _ HP3) by kcmp_cs; exact R2_8|].
split; [rewrite (kcmp_pres1 3%bv _ _ HP3) by kcmp_cs; exact R2_3|].
split; [rewrite (kcmp_pres1 4%bv _ _ HP3) by kcmp_cs; exact R2_4|].
split; [rewrite (kcmp_pres1 21%bv _ _ HP3) by kcmp_cs; exact R2_21|].
rewrite (kcmp_pres1 23%bv _ _ HP3) by kcmp_cs; exact R2_23.
Qed.

(* ---- the piece -------------------------------------------------------------------------------------------------- *)
Lemma k_cmp : k_cmp_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS G.
Proof.
intros _ g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs mem md Q HKC HKR R18 HK.
apply (kcmp_A g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs mem md Q HKC HKR R18).
intros regs' mem' md' HKC' HKR' R10'.
exact (kcmp_B g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs' mem' md' Q HKC' HKR' R10' HK).
Qed.
Check (k_cmp : k_cmp_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS G).
End c. End b. End a.
Print Assumptions k_cmp.
