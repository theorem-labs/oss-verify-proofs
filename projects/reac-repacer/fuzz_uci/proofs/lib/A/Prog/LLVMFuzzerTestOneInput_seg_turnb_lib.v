(* LLVMFuzzerTestOneInput_seg_turnb_lib: what the turn_b segment (+0x130 .. the next head, LLVMFuzzerTestOneInput_segs.v
   u_turn_b_stmt) needs apart from the runs of the Pa engine, in the form of proofs/libreac/fuzz_decode's
   LLVMFuzzerTestOneInput_seg_crt1.v c1_Bcrt (a caller-journal callee contract composed into the walk: its premises at
   the call, its post moved to the next state):
   - tb_st: the state at the two return points +0x148 (after check_no_overread) and +0x158 (after check_value);
   - the premises every call of the turn reads from the slot pre and the frame invariant u_core (the reply slice and
     its block, the read-only view, the event and live-byte budgets, the meter);
   - tb_call_cno / tb_call_cv: each callee contract (the record u_prem) applied at its call state, with its post
     moved to tb_st at the return address;
   - tb_close: the frame invariant, the meter and the results after the store of the turn's value. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YE00 YE01 YO09 YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v ACfn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require rp_uci_int_c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
  UciPSyms UciPList UciPAddr UciPPa UciPPaLib UciPImg UciCg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_lib.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require check_no_overread_cg check_value_cg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module PRc := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_uci_int_c.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. Values of the turn                                               *)
(* ------------------------------------------------------------------ *)

(* cur, the int `lw s4, 8(sp)` loads from its four bytes cu (unsigned little-endian). *)
Definition tb_cur (cu : Z) : Z := if cu <? 2 ^ 31 then cu else cu - 2 ^ 32.
Lemma tb_cur_range : forall cu, 0 <= cu < 2 ^ 32 -> INT_MIN <= tb_cur cu <= INT_MAX.
Proof. intros cu Hcu. unfold tb_cur, INT_MIN, INT_MAX. destruct (Z.ltb_spec cu (2 ^ 31)); lia. Qed.
Lemma tb_swrap : forall cu, 0 <= cu < 2 ^ 32 -> bv_swrap 32 cu = tb_cur cu.
Proof.
intros cu Hcu. unfold tb_cur, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
destruct (Z.ltb_spec cu (2 ^ 31)); cbn -[Z.add Z.mul Z.modulo Z.div Z.sub]; lia.
Qed.
Lemma tb_w64_canon : forall z, Z_to_bv 64 (zcanon z) = w64 z.
Proof.
intros z. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma tb_sext_denot : forall E (n : nat) cu, ew E n = Z_to_bv 64 cu -> 0 <= cu < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = w64 (tb_cur cu) /\
  sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 0)) = w64 (tb_cur cu).
Proof.
intros E n cu Hn Hcu.
assert (Hx : U E (SExt true 32 (SOff n 0)) = zcanon (tb_cur cu)).
{ rewrite U_SExt, (U_atom E n cu Hn) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. rewrite tb_swrap by lia. reflexivity. }
split.
- rewrite denot_lit_U, Hx. apply tb_w64_canon.
- rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Hx. change (zcanon 0) with 0. rewrite Z.add_0_r.
  rewrite tb_w64_canon. unfold w64 at 1. apply tb_w64_canon.
Qed.
(* The sum of two registers below 2 ^ 63 each. *)
Lemma tb_add_denot : forall E (a b : nat) x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
  0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = w64 (x + y).
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite (U_atom E a x Ha), (U_atom E b y Hb) by lia. apply tb_w64_canon.
Qed.
Lemma tb_soff_denot : forall E (a : nat) w, ew E a = w -> sv_denot E (SOff a 0) = w.
Proof. intros E a w Ha. cbn [sv_denot]. rewrite Ha, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* The slice of the input the turn hands to both callees. *)
Definition tb_slice (pl : list byte) (off len : Z) : list byte := firstn (Z.to_nat len) (skipn (Z.to_nat off) pl).
Lemma tb_slice_len : forall pl off len, 0 <= off -> 0 <= len -> off + len <= Z.of_nat (length pl) ->
  Z.of_nat (length (tb_slice pl off len)) = len.
Proof.
intros pl off len Ho Hl Hol. unfold tb_slice. rewrite length_firstn, length_skipn. lia.
Qed.
Lemma tb_garr8_slice : forall segs m p (pl : list byte) off len,
  garr8 segs m p (map (fun b : byte => bv_unsigned b) pl) ->
  0 <= off -> 0 <= len -> off + len <= Z.of_nat (length pl) ->
  garr8 segs m (p + off) (map (fun b : byte => bv_unsigned b) (tb_slice pl off len)).
Proof.
intros segs m p pl off len Hg Ho Hl Hol j Hj.
rewrite length_map in Hj. pose proof (tb_slice_len pl off len Ho Hl Hol) as Hsl.
assert (Hj' : (Z.to_nat off + j < length (map (fun b : byte => bv_unsigned b) pl))%nat) by (rewrite length_map; lia).
destruct (Hg _ Hj') as [Hv Hr].
assert (E : nth j (map (fun b : byte => bv_unsigned b) (tb_slice pl off len)) 0 =
            nth (Z.to_nat off + j) (map (fun b : byte => bv_unsigned b) pl) 0).
{ unfold tb_slice. rewrite <- firstn_map, <- skipn_map. rewrite nth_firstn.
  destruct (Nat.ltb_spec j (Z.to_nat len)) as [Hlt | Hge]; [|lia]. rewrite nth_skipn. reflexivity. }
rewrite E. split; [|exact Hr].
replace (p + off + Z.of_nat j) with (p + Z.of_nat (Z.to_nat off + j)) by lia. exact Hv.
Qed.

(* A stored 4-byte chunk reads back as the int whose register was stored (two's complement). *)
Lemma tb_mod_div : forall v M d, 0 < d -> 0 < M -> M mod (d * 256) = 0 -> ((v mod M) / d) mod 256 = (v / d) mod 256.
Proof.
intros v M d Hd HM HMd.
assert (EM : M = d * 256 * (M / (d * 256))) by (pose proof (Z.div_mod M (d * 256) ltac:(lia)); lia).
rewrite (Z.mod_eq v M) by lia.
set (q := M / (d * 256)) in *. set (w := v / M) in *. clearbody q w.
rewrite EM.
replace (v - d * 256 * q * w) with (v + (- (256 * q * w)) * d) by ring.
rewrite Z.div_add by lia.
replace (v / d + - (256 * q * w)) with (v / d + (- (q * w)) * 256) by ring.
apply Z.mod_add. lia.
Qed.
Lemma tb_le_byte4 : forall v k, (k < 4)%nat ->
  Z.shiftr (v mod 2 ^ 64) (8 * Z.of_nat k) mod 256 = le_byte v 4 k.
Proof.
intros v k Hk. unfold le_byte. rewrite !Z.shiftr_div_pow2 by lia. change (8 * Z.of_nat 4) with 32.
rewrite (tb_mod_div v (2 ^ 64) (2 ^ (8 * Z.of_nat k))), (tb_mod_div v (2 ^ 32) (2 ^ (8 * Z.of_nat k))); try lia;
  do 4 (destruct k as [|k]; [reflexivity|]); lia.
Qed.
Lemma tb_store_val : forall segs E m base off e v,
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v ->
  val_mem segs m (base + off) 4 v.
Proof.
intros segs E m base off e v Hc He k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn [c_len YP09.c_val cv_len]; lia)) as (b & Hb & Hm).
cbn [cbyte YP09.c_val YP09.c_off] in Hb, Hm. rewrite Hm. injection Hb as <-. f_equal.
unfold byte_of_word. rewrite He. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
rewrite (tb_le_byte4 v k Hk). unfold YO0f.le_byte, YG0f.le_byte. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma tb_rd32_of_val : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 4 v -> rd32 (aview segs H mem) a v.
Proof.
intros segs H mem a v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YO0f.le_byte, YG0f.le_byte.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* A callee-saved register through aregs_preserved. *)
Lemma tb_pres : forall regs regs2 (r : bv 5), aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) ->
  YK11.getr regs2 r = YK11.getr regs r.
Proof. intros regs regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac tb_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let x := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with x; unfold acallee_saved; lia end.
(* A register in a literal list of registers. *)
Ltac tb_in := cbn [In]; repeat (first [left; reflexivity | left; apply bv_eq; reflexivity | right]).

(* What a run whose regions are all the result word (atom 32, window [0, 4)) leaves of the memory. *)
Lemma tb_frame32 : forall E rs (m m' : word -> option byte) R,
  frame_of E rs m m' ->
  forallb (fun r => match YP09.r_base r with Some n => Nat.eqb n 32 | None => false end &&
    (YP09.r_wlo r =? 0) && (YP09.r_whi r =? 4))%bool rs = true ->
  bv_unsigned (ew E 32) = R -> forall x, ~ (R <= bv_unsigned x < R + 4) -> m' x = m x.
Proof.
intros E rs m m' R HF Hb HR x Hx. apply HF. intros (r & Hin & Ha). rewrite forallb_forall in Hb.
specialize (Hb r Hin). destruct (YP09.r_base r) as [n|] eqn:Eb; [|discriminate Hb].
rewrite !andb_true_iff in Hb. destruct Hb as ((Hn & Hlo) & Hhi).
apply Nat.eqb_eq in Hn. apply Z.eqb_eq in Hlo, Hhi. subst n.
cbn [base_val] in Ha. rewrite HR, Hlo, Hhi in Ha. lia.
Qed.

(* The saved words and the results lie above sp1: a byte the view keeps there keeps them. *)
Lemma tb_saved_kept : forall cx (r r' : reader), u_saved cx r ->
  (forall a, u_sp0 cx - 96 <= a < u_sp0 cx -> r' a = r a) -> u_saved cx r'.
Proof.
intros cx r r' Hs Hk. unfold u_saved in *. rewrite Forall_forall in *. intros o Ho.
rewrite <- (Hs o Ho). apply rdword_kept. intros k Hk8.
assert (Hf : 8 <= fst o <= 96).
{ unfold uci_saved_at in Ho. repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
apply Hk. lia.
Qed.
Lemma tb_res_kept : forall cx (r r' : reader) i vs, u_res cx r i vs ->
  (forall a, u_sp1 cx + 0x1c <= a < u_sp1 cx + 0x1c + 4 * i -> r' a = r a) -> u_res cx r' i vs.
Proof.
intros cx r r' i vs (Hl & Hf & Hw) Hk. refine (conj Hl (conj Hf _)). intros j Hj kk Hkk.
rewrite Hk by lia. exact (Hw j Hj kk Hkk).
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The states at the two return points                              *)
(* ------------------------------------------------------------------ *)

Section tb. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* The registers of the turn from +0x134 on: s0 = n, s1 = p, s2 = margin_max, s3 = len, s4 = cur, s5 = p + off,
   s6 = the shadow base, s7 = the turn, s8 = off, s9 = sp1 + 0x1c, s10 = 5. All are callee-saved. *)
Definition tb_regs (cx : ucx) (regs : bvmap 5 word) (i mm off len cur : Z) : Prop :=
  YK11.getr regs 8 = w64 (u_n cx) /\ YK11.getr regs 9 = w64 (u_p cx) /\
  YK11.getr regs 18 = w64 mm /\ (mm = U_MM0 \/ mm = U_MM1) /\
  YK11.getr regs 19 = w64 len /\ YK11.getr regs 20 = w64 cur /\ YK11.getr regs 21 = w64 (u_p cx + off) /\
  YK11.getr regs 22 = w64 SHADOW_OFF /\ YK11.getr regs 23 = w64 i /\ YK11.getr regs 24 = w64 off /\
  YK11.getr regs 25 = w64 (u_sp1 cx + 0x1c) /\ YK11.getr regs 26 = w64 5.

(* The state at pc (+0x148 or +0x158) of turn i: the frame invariant at kev events, the meter charged i turns and the
   calls of this turn so far (C len), the registers, the slice, the results of the earlier turns, and X (a0 at
   +0x158). *)
Definition tb_st (cx : ucx) (i pc kev : Z) (C : Z -> Z) (X : bvmap 5 word -> Z -> Z -> Z -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (mm off len cur : Z) (vs : list Z),
    c' = u_cfg cx pc regs' mem' md' /\
    u_core B cx ly' S' W' regs' mem' md' kev /\
    mo_le MT (u_S cx) S' (i * U_TURN_COST MT + C len) /\ mo_ok MT S' (XL (u_n cx) - (i * U_TURN_COST MT + C len)) /\
    tb_regs cx regs' i mm off len cur /\
    0 <= off /\ 0 <= len <= PR.REPLY_MAX /\ off + len <= u_n cx /\ INT_MIN <= cur <= INT_MAX /\
    u_res cx (aview segs (w_H W') mem') i vs /\
    X regs' off len cur.

Lemma tb_regs_pres : forall cx regs regs2 i mm off len cur,
  aregs_preserved regs regs2 -> tb_regs cx regs i mm off len cur -> tb_regs cx regs2 i mm off len cur.
Proof.
intros cx regs regs2 i mm off len cur HP (R8 & R9 & R18 & Hmm & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26).
unfold tb_regs.
repeat match goal with |- context [YK11.getr regs2 ?r] => rewrite (tb_pres regs regs2 r HP) by tb_cs end.
repeat split; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. What every call of the turn reads                                *)
(* ------------------------------------------------------------------ *)

Lemma tb_base : forall cx, u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx ->
  0 <= u_n cx < 2 ^ 26 /\ 0 <= u_p cx <= 2 ^ 47 /\ Z.of_nat (length (u_pl cx)) = u_n cx /\
  garr8 segs (mrestrict (w_H (u_W cx)) (u_mem cx)) (u_p cx) (map (fun b : byte => bv_unsigned b) (u_pl cx)) /\
  (0 < u_n cx -> In (u_p cx, u_n cx) (ablocks B (u_ly cx) (u_S cx))) /\
  st_nev (u_S cx) + EV_LIB <= EV_MAX /\ blocks_bytes (u_S cx) + LIVE_LIB <= LIVE_MAX /\
  arodata_okS segs B RLO RHI (aview segs (w_H (u_W cx)) (u_mem cx)).
Proof.
intros cx HP HB. pose proof (up_laws _ _ _ _ _ HP) as LAWS.
unfold u_base, tfib_lib_pre_x in HB.
destruct HB as (HAFN & Hra & H10 & H11 & Hpn & Hlen & Hgarr & Hfrs & Hnev & Hbb & Haro & _).
pose proof HAFN as (HAR & _).
assert (Hn26 : 0 <= u_n cx < 2 ^ 26) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
refine (conj Hn26 (conj _ (conj (eq_sym Hlen) (conj Hgarr (conj _ (conj Hnev (conj Hbb Haro))))))).
- destruct Hpn as [(_ & ->) | (Hn & Hin)]; [unfold A_EMPTY; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ (u_p cx) (u_n cx) HAR Hin) as (_ & Hb1 & Hb3 & _).
  pose proof (req_size_pos (u_n cx) ltac:(lia)) as Hrq. pose proof alloc_ceiling_val as Hce. lia.
- intros Hn. destruct Hpn as [(Hz & _) | (_ & Hin)]; [lia | exact Hin].
Qed.

Lemma tb_J_facts : forall cx ly' S' W mem md k,
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' W mem md k ->
  u_sp0 cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= u_sp0 cx /\ u_sp0 cx <= 2 ^ 47 /\
  (forall a, u_sp0 cx - LLVMF_STK <= a < u_sp0 cx -> apresent (w_H W) mem a).
Proof.
intros cx ly' S' W mem md k HJ.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (H16 & _ & Hceil & Hlo & Hhi & H47 & _).
refine (conj H16 (conj _ (conj _ Hpres))); lia.
Qed.

(* The slice, its length and its block, at a state of the journal: the slot pre's bytes, kept by the journal's block
   clause. *)
Lemma tb_slice_at : forall cx ly' S' W mem md k off len,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx ->
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' W mem md k ->
  Permutation (ablocks B ly' S') (ablocks B (u_ly cx) (u_S cx)) ->
  0 <= off -> 0 <= len -> off + len <= u_n cx ->
  garr8 segs (mrestrict (w_H W) mem) (u_p cx + off) (map (fun b : byte => bv_unsigned b) (tb_slice (u_pl cx) off len)) /\
  Z.of_nat (length (tb_slice (u_pl cx) off len)) = len /\
  (0 < len -> exists bA nA, In (bA, nA) (ablocks B ly' S') /\ bA <= u_p cx + off /\ u_p cx + off + len <= bA + nA).
Proof.
intros cx ly' S' W mem md k off len HP HB HJ Hperm Ho Hl Hol.
destruct (tb_base cx HP HB) as (Hn & Hp & Hlen & Hg & Hblk & _).
pose proof (tb_slice_len (u_pl cx) off len Ho Hl ltac:(lia)) as Hsl.
split; [|split; [exact Hsl|]].
- apply (garr8_kept segs (w_H (u_W cx)) (w_H W) (u_mem cx) mem).
  + intros j Hj. rewrite length_map, Hsl in Hj.
    destruct (Z.lt_ge_cases 0 (u_n cx)) as [Hn0 | Hn0]; [|lia].
    pose proof (Hblk Hn0) as Hin.
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    replace (u_p cx + off + j) with (u_p cx + (off + j)) by lia.
    apply (F2 (u_p cx) (u_n cx) (off + j) Hin).
    * apply (Permutation_in _ (Permutation_sym Hperm)). exact Hin.
    * unfold req_size. destruct (Z.eqb_spec (u_n cx) 0); lia.
    * intros (rg & [] & _).
  + apply tb_garr8_slice; [exact Hg | lia | lia | lia].
- intros Hl0. exists (u_p cx), (u_n cx). split; [|lia].
  apply (Permutation_in _ (Permutation_sym Hperm)). apply Hblk. lia.
Qed.

(* The read-only bytes the callees read: the slot pre's arodata_okS, kept by the journal's image clause. *)
Lemma tb_rom_at : forall cx ly' S' W mem md k,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx ->
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' W mem md k ->
  uci_rom_view_rd W mem.
Proof.
intros cx ly' S' W mem md k HP HB HJ a Ha.
pose proof (up_ro_unowned _ _ _ _ _ HP) as HOU. pose proof (up_rom_no_errno _ _ _ _ _ HP) as HNE.
destruct (tb_base cx HP HB) as (_ & _ & _ & _ & _ & _ & _ & Haro).
destruct (uci_ro_rd_scoped B HOU HNE a Ha) as [Ho He].
destruct (uci_ro_rd_rom_clean a Ha) as [Hrom _].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Himg : in_img segs a) by (destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
rewrite (F3 a Himg Ho He (fp_spares_closed [] a sink_closed_nil)).
apply Haro; [left; exact Hrom | exact Ho | exact He].
Qed.

(* The meter: each call costs at most its largest slice's cost, and five turns fit XL n. *)
Lemma tb_costs : ameter_laws MT -> forall len, 0 <= len <= PR.REPLY_MAX ->
  0 <= PN.uci_cno_cost MT len <= uci_cno_cost_max MT /\ 0 <= PV.uci_cv_cost MT len <= uci_cv_cost_max MT /\
  U_TURN_COST MT = uci_cno_cost_max MT + uci_cv_cost_max MT.
Proof.
intros ML len Hl. unfold uci_cno_cost_max, uci_cv_cost_max, PN.uci_cno_cost, PV.uci_cv_cost, PR.REPLY_MAX in *.
pose proof (mo_malloc_mono MT ML (len + 1) (255 + 1) ltac:(lia)).
pose proof (mo_malloc_mono MT ML (Z.max len 1) (Z.max 255 1) ltac:(lia)).
pose proof (mo_malloc_nonneg MT ML (len + 1) ltac:(lia)).
pose proof (mo_malloc_nonneg MT ML (Z.max len 1) ltac:(lia)).
pose proof (mo_free_nonneg MT ML).
split; [lia|]. split; [lia|]. reflexivity.
Qed.
Lemma tb_budget : forall cx i, u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 <= i < 5 ->
  (i + 1) * U_TURN_COST MT <= XL (u_n cx) /\ 0 <= U_TURN_COST MT.
Proof.
intros cx i HP HB Hi. pose proof (up_meter_laws _ _ _ _ _ HP) as ML.
destruct (tb_base cx HP HB) as (Hn & _).
pose proof (up_cost _ _ _ _ _ HP (u_n cx) ltac:(lia)) as Hc. unfold uci_llvmf_cost in Hc.
destruct (tb_costs ML 0 ltac:(unfold PR.REPLY_MAX; lia)) as (H1 & H2 & E).
rewrite <- E in Hc. split; [nia | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 4. A call's post moved to the frame invariant                       *)
(* ------------------------------------------------------------------ *)

Lemma tb_after_call : forall cx (W W2 : world segs) regsT memT mdT ly' S' ly2 S2 regs2 mem2 md2 k EV STKc
    i mm off len cur vs,
  u_core B cx ly' S' W regsT memT mdT k ->
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly2 S2 W2 mem2 md2 (k + EV) ->
  aregs_preserved regsT regs2 -> frames S2 = frames S' ->
  Permutation (ablocks B ly2 S2) (ablocks B ly' S') ->
  @acall_kept rc segs B ly' S' W memT W2 mem2 (spZ regsT - STKc) (spZ regsT) (fun _ => False) ->
  tb_regs cx regsT i mm off len cur -> u_res cx (aview segs (w_H W) memT) i vs -> 0 <= i <= 5 ->
  u_core B cx ly2 S2 W2 regs2 mem2 md2 (k + EV) /\ tb_regs cx regs2 i mm off len cur /\
  u_res cx (aview segs (w_H W2) mem2) i vs.
Proof.
intros cx W W2 regsT memT mdT ly' S' ly2 S2 regs2 mem2 md2 k EV STKc i mm off len cur vs
  HC HJ2 HPr Hfr2 Hperm2 HK HRg HR Hi.
destruct HC as (HJ & Hfrs & Hsp & Hgp & Htp & H27 & Hsv & Hperm).
destruct (tb_J_facts _ _ _ _ _ _ _ HJ) as (H16 & Hceil & H47 & _).
pose proof alloc_ceiling_val as Hce.
assert (KV : forall a, u_sp1 cx <= a < 2 ^ 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memT a).
{ intros a Ha. destruct HK as (K1 & _). apply K1; [unfold u_sp1, U_FRAME, LLVMF_STK in *; lia | rewrite Hsp; lia]. }
assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs2 r = YK11.getr regsT r)
  by (intros r Hr; exact (tb_pres regsT regs2 r HPr Hr)).
split; [|split].
- refine (conj HJ2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  + rewrite Hfr2. exact Hfrs.
  + unfold spZ in *. rewrite (P 2%bv ltac:(tb_cs)). exact Hsp.
  + rewrite (P 3%bv ltac:(tb_cs)). exact Hgp.
  + rewrite (P 4%bv ltac:(tb_cs)). exact Htp.
  + rewrite (P 27%bv ltac:(tb_cs)). exact H27.
  + apply (tb_saved_kept cx _ _ Hsv). intros a Ha. apply KV. unfold u_sp1, U_FRAME in *. lia.
  + exact (Permutation_trans Hperm2 Hperm).
- exact (tb_regs_pres cx regsT regs2 i mm off len cur HPr HRg).
- apply (tb_res_kept cx _ _ i vs HR). intros a Ha. apply KV. unfold u_sp1, U_FRAME in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The two calls                                                    *)
(* ------------------------------------------------------------------ *)

(* check_no_overread (p + off, len, cur) at +0x144 by u_prem's contract; its return +0x148 is tb_st. The chain is
   empty (s0 = n < alloc_ceiling), so the context is the return address alone. *)
Lemma tb_call_cno : forall cx i (W : world segs) regsT memT mdT ly' S' mm off len cur vs,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 <= i < 5 ->
  u_core B cx ly' S' W regsT memT mdT (i * U_EV_TURN) -> u_meter MT XL cx S' i ->
  YK11.getr regsT 1 = w64 (UCI_A_LLVMF + 0x148) ->
  tb_regs cx regsT i mm off len cur ->
  YK11.getr regsT 10 = w64 (u_p cx + off) -> YK11.getr regsT 11 = w64 len -> YK11.getr regsT 12 = w64 cur ->
  0 <= off -> 0 <= len <= PR.REPLY_MAX -> off + len <= u_n cx -> INT_MIN <= cur <= INT_MAX ->
  u_res cx (aview segs (w_H W) memT) i vs ->
  SRr segs W (@cfg_at (u_fx cx) segs (uci_sigma US_check_no_overread) regsT memT mdT)
    (tb_st cx i 0x148 (i * U_EV_TURN + PN.CNO_EV) (fun l => PN.uci_cno_cost MT l) (fun _ _ _ _ => True)).
Proof.
intros cx i W regsT memT mdT ly' S' mm off len cur vs HP HB Hi HC (Hle & Hmo) R1 HRg R10 R11 R12 Ho Hl Hol Hcur HR.
pose proof (up_meter_laws _ _ _ _ _ HP) as ML.
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H27 & Hsv & Hperm).
destruct (tb_base cx HP HB) as (Hn & Hp & Hlen & _ & _ & Hnev & Hbb & _).
destruct (tb_J_facts _ _ _ _ _ _ _ HJ) as (H16 & Hceil & H47 & _).
pose proof alloc_ceiling_val as Hce.
destruct (tb_slice_at cx ly' S' W memT mdT _ off len HP HB HJ Hperm Ho ltac:(lia) Hol) as (Hg & Hsl & Hblk).
pose proof (tb_rom_at cx ly' S' W memT mdT _ HP HB HJ) as Hrom.
pose proof HRg as (R8 & _).
destruct (tb_costs ML len Hl) as (Hc1 & Hc2 & ETC).
destruct (tb_budget cx i HP HB Hi) as (Hbud & HTC).
assert (Hraz : raZ regsT = UCI_A_LLVMF + 0x148)
  by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; vm_compute; split; congruence).
eapply SRr_bind.
{ refine (up_cno _ _ _ _ _ HP (u_fx cx) LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) []
    ly' S' W memT mdT (i * U_EV_TURN) regsT (u_p cx + off) len cur (XL (u_n cx) - i * U_TURN_COST MT)
    (tb_slice (u_pl cx) off len) [] HJ _ _ Hgp Htp R10 R11 R12 _ _ _ _ _ Hcur Hl Hsl Hblk Hg Hrom _ _ Hmo _).
  - rewrite R1. vm_compute. reflexivity.
  - rewrite Hraz. vm_compute. discriminate.
  - apply achain_low. unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite Hraz. unfold CTX_check_no_overread, UCI_LLVMF_RA_CNO. cbn [spine map In]. left. reflexivity.
  - rewrite Hsp. unfold u_sp1, U_FRAME. lia.
  - rewrite Hsp. unfold u_sp1, U_FRAME, PN.CNO_STK, PN.CNO_FRAME, ASTACK, LLVMF_STK. lia.
  - rewrite Hsp. unfold u_sp1, U_FRAME. lia.
  - unfold U_EV_TURN, PN.CNO_EV, PV.CV_EV, EV_LIB in *. lia.
  - rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ Hperm), <- (blocks_bytes_bsum B (u_ly cx) (u_S cx)).
    unfold PN.CNO_LIVE, PR.REPLY_MAX, LIVE_LIB, LIVE_MAX in *. lia.
  - lia. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPr & Hfr2 & Hperm2 & HK & Hmle).
apply SRr_ret.
destruct (tb_after_call cx W W2 regsT memT mdT ly' S' ly2 S2 regs2 mem2 md2 (i * U_EV_TURN) PN.CNO_EV PN.CNO_STK
  i mm off len cur vs HC HJ2 HPr Hfr2 Hperm2 HK HRg HR ltac:(lia)) as (HC2 & HRg2 & HR2).
exists ly2, S2, regs2, mem2, md2, mm, off, len, cur, vs. cbv beta.
refine (conj _ (conj HC2 (conj _ (conj _ (conj HRg2 (conj Ho (conj Hl (conj Hol (conj Hcur (conj HR2 I)))))))))).
- unfold u_cfg. rewrite R1. reflexivity.
- exact (mo_le_trans MT ML _ _ _ _ _ Hle Hmle).
- apply (mo_ok_step MT ML S' S2 (PN.uci_cno_cost MT len)); [|exact Hmle].
  replace (PN.uci_cno_cost MT len + (XL (u_n cx) - (i * U_TURN_COST MT + PN.uci_cno_cost MT len)))
    with (XL (u_n cx) - i * U_TURN_COST MT) by lia. exact Hmo.
Qed.

(* check_value (p + off, len, cur) at +0x154 by u_prem's contract; its return +0x158 is tb_st with a0 the value. *)
Lemma tb_call_cv : forall cx i (W : world segs) regsT memT mdT ly' S' mm off len cur vs,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 <= i < 5 ->
  u_core B cx ly' S' W regsT memT mdT (i * U_EV_TURN + PN.CNO_EV) ->
  mo_le MT (u_S cx) S' (i * U_TURN_COST MT + PN.uci_cno_cost MT len) ->
  mo_ok MT S' (XL (u_n cx) - (i * U_TURN_COST MT + PN.uci_cno_cost MT len)) ->
  YK11.getr regsT 1 = w64 (UCI_A_LLVMF + 0x158) ->
  tb_regs cx regsT i mm off len cur ->
  YK11.getr regsT 10 = w64 (u_p cx + off) -> YK11.getr regsT 11 = w64 len -> YK11.getr regsT 12 = w64 cur ->
  0 <= off -> 0 <= len <= PR.REPLY_MAX -> off + len <= u_n cx -> INT_MIN <= cur <= INT_MAX ->
  u_res cx (aview segs (w_H W) memT) i vs ->
  SRr segs W (@cfg_at (u_fx cx) segs (uci_sigma US_check_value) regsT memT mdT)
    (tb_st cx i 0x158 (i * U_EV_TURN + PN.CNO_EV + PV.CV_EV) (fun l => PN.uci_cno_cost MT l + PV.uci_cv_cost MT l)
       (fun regs off len cur => YK11.getr regs 10 = w64 (rp_uci_int_m (PRc.zbytes (tb_slice (u_pl cx) off len)) cur))).
Proof.
intros cx i W regsT memT mdT ly' S' mm off len cur vs HP HB Hi HC Hle Hmo R1 HRg R10 R11 R12 Ho Hl Hol Hcur HR.
pose proof (up_meter_laws _ _ _ _ _ HP) as ML.
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H27 & Hsv & Hperm).
destruct (tb_base cx HP HB) as (Hn & Hp & Hlen & _ & _ & Hnev & Hbb & _).
destruct (tb_J_facts _ _ _ _ _ _ _ HJ) as (H16 & Hceil & H47 & _).
pose proof alloc_ceiling_val as Hce.
destruct (tb_slice_at cx ly' S' W memT mdT _ off len HP HB HJ Hperm Ho ltac:(lia) Hol) as (Hg & Hsl & Hblk).
pose proof (tb_rom_at cx ly' S' W memT mdT _ HP HB HJ) as Hrom.
destruct (tb_costs ML len Hl) as (Hc1 & Hc2 & ETC).
destruct (tb_budget cx i HP HB Hi) as (Hbud & HTC).
assert (Hraz : raZ regsT = UCI_A_LLVMF + 0x158)
  by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; vm_compute; split; congruence).
eapply SRr_bind.
{ refine (up_cv _ _ _ _ _ HP (u_fx cx) LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) []
    ly' S' W memT mdT (i * U_EV_TURN + PN.CNO_EV) regsT (u_p cx + off) len cur
    (XL (u_n cx) - (i * U_TURN_COST MT + PN.uci_cno_cost MT len))
    (tb_slice (u_pl cx) off len) HJ _ _ Hgp Htp R10 R11 R12 _ _ _ Hcur Hl Hsl Hblk Hg Hrom _ _ Hmo _).
  - rewrite R1. vm_compute. reflexivity.
  - rewrite Hraz. vm_compute. discriminate.
  - rewrite Hsp. unfold u_sp1, U_FRAME. lia.
  - rewrite Hsp. unfold u_sp1, U_FRAME, PV.CV_STK, PV.CV_FRAME, ASTACK, LLVMF_STK. lia.
  - rewrite Hsp. unfold u_sp1, U_FRAME. lia.
  - unfold U_EV_TURN, PN.CNO_EV, PV.CV_EV, EV_LIB in *. lia.
  - rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ Hperm), <- (blocks_bytes_bsum B (u_ly cx) (u_S cx)).
    unfold PV.CV_LIVE, PR.REPLY_MAX, LIVE_LIB, LIVE_MAX in *. lia.
  - lia. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPr & Hfr2 & Hperm2 & HK & Hmle & R10').
apply SRr_ret.
destruct (tb_after_call cx W W2 regsT memT mdT ly' S' ly2 S2 regs2 mem2 md2 (i * U_EV_TURN + PN.CNO_EV) PV.CV_EV
  PV.CV_STK i mm off len cur vs HC HJ2 HPr Hfr2 Hperm2 HK HRg HR ltac:(lia)) as (HC2 & HRg2 & HR2).
exists ly2, S2, regs2, mem2, md2, mm, off, len, cur, vs. cbv beta.
refine (conj _ (conj HC2 (conj _ (conj _ (conj HRg2 (conj Ho (conj Hl (conj Hol (conj Hcur (conj HR2 R10')))))))))).
- unfold u_cfg. rewrite R1. reflexivity.
- apply (mo_le_mono MT ML _ _ _ _ (mo_le_trans MT ML _ _ _ _ _ Hle Hmle)). lia.
- apply (mo_ok_step MT ML S' S2 (PV.uci_cv_cost MT len)); [|exact Hmle].
  replace (PV.uci_cv_cost MT len + (XL (u_n cx) - (i * U_TURN_COST MT + (PN.uci_cno_cost MT len + PV.uci_cv_cost MT len))))
    with (XL (u_n cx) - (i * U_TURN_COST MT + PN.uci_cno_cost MT len)) by lia. exact Hmo.
Qed.

(* ------------------------------------------------------------------ *)
(* 6. Runs of the walk between the calls                               *)
(* ------------------------------------------------------------------ *)

(* A run that wrote no memory and kept sp, gp, tp and s11 keeps the frame invariant. *)
Lemma tb_core_same : forall cx ly' S' (W : world segs) regs regs' mem md md' k,
  u_core B cx ly' S' W regs mem md k ->
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' W mem md' k ->
  (forall r : bv 5, In r [2; 3; 4; 27]%bv -> YK11.getr regs' r = YK11.getr regs r) ->
  u_core B cx ly' S' W regs' mem md' k.
Proof.
intros cx ly' S' W regs regs' mem md md' k (HJ & Hfrs & Hsp & Hgp & Htp & H27 & Hsv & Hperm) HJ' KA.
refine (conj HJ' (conj Hfrs (conj _ (conj _ (conj _ (conj _ (conj Hsv Hperm))))))).
- unfold spZ in *. rewrite (KA 2%bv ltac:(tb_in)). exact Hsp.
- rewrite (KA 3%bv ltac:(tb_in)). exact Hgp.
- rewrite (KA 4%bv ltac:(tb_in)). exact Htp.
- rewrite (KA 27%bv ltac:(tb_in)). exact H27.
Qed.
Lemma tb_regs_kept : forall cx regs regs' i mm off len cur,
  tb_regs cx regs i mm off len cur ->
  (forall r : bv 5, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> YK11.getr regs' r = YK11.getr regs r) ->
  tb_regs cx regs' i mm off len cur.
Proof.
intros cx regs regs' i mm off len cur (R8 & R9 & R18 & Hmm & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26) KA.
unfold tb_regs.
repeat match goal with |- context [YK11.getr regs' ?r] => rewrite (KA r ltac:(tb_in)) end.
repeat split; assumption.
Qed.

(* After the store of the turn's value v at sp1 + 0x1c + 4 i (+0x158 .. +0x16c): the frame invariant at the events of
   i + 1 turns, the meter, the results of i + 1 turns, the registers of the next head. *)
Lemma tb_close : forall cx i (W : world segs) regs mem md ly' S' mm off len cur vs regs' mem' md' v,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 <= i < 5 ->
  u_core B cx ly' S' W regs mem md (i * U_EV_TURN + PN.CNO_EV + PV.CV_EV) ->
  mo_le MT (u_S cx) S' (i * U_TURN_COST MT + (PN.uci_cno_cost MT len + PV.uci_cv_cost MT len)) ->
  mo_ok MT S' (XL (u_n cx) - (i * U_TURN_COST MT + (PN.uci_cno_cost MT len + PV.uci_cv_cost MT len))) ->
  tb_regs cx regs i mm off len cur ->
  0 <= off -> 0 <= len <= PR.REPLY_MAX -> off + len <= u_n cx ->
  u_res cx (aview segs (w_H W) mem) i vs ->
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' W mem' md'
    (i * U_EV_TURN + PN.CNO_EV + PV.CV_EV) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (u_sp1 cx + 0x1c + 4 * i <= a < u_sp1 cx + 0x1c + 4 * i + 4) ->
     aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  rd32 (aview segs (w_H W) mem') (u_sp1 cx + 0x1c + 4 * i) v -> INT_MIN <= v <= INT_MAX ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 22; 25; 26; 27]%bv -> YK11.getr regs' r = YK11.getr regs r) ->
  YK11.getr regs' 23 = w64 (i + 1) -> YK11.getr regs' 24 = w64 (len + off) ->
  u_core B cx ly' S' W regs' mem' md' ((i + 1) * U_EV_TURN) /\ u_meter MT XL cx S' (i + 1) /\
  u_res cx (aview segs (w_H W) mem') (i + 1) (vs ++ [v]) /\
  YK11.getr regs' 8 = w64 (u_n cx) /\ YK11.getr regs' 9 = w64 (u_p cx) /\ YK11.getr regs' 18 = w64 mm /\
  (mm = U_MM0 \/ mm = U_MM1) /\ YK11.getr regs' 22 = w64 SHADOW_OFF /\ YK11.getr regs' 23 = w64 (i + 1) /\
  YK11.getr regs' 24 = w64 (len + off) /\ YK11.getr regs' 25 = w64 (u_sp1 cx + 0x1c) /\
  YK11.getr regs' 26 = w64 5 /\ 0 <= len + off <= u_n cx.
Proof.
intros cx i W regs mem md ly' S' mm off len cur vs regs' mem' md' v HP HB Hi HC Hle Hmo HRg Ho Hl Hol HR HJ' HK Hrd Hv
  KA R23' R24'.
pose proof (up_meter_laws _ _ _ _ _ HP) as ML.
destruct HC as (HJ & Hfrs & Hsp & Hgp & Htp & H27 & Hsv & Hperm).
destruct (tb_J_facts _ _ _ _ _ _ _ HJ) as (H16 & Hceil & H47 & _).
pose proof alloc_ceiling_val as Hce.
destruct HRg as (R8 & R9 & R18 & Hmm & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26).
destruct (tb_costs ML len Hl) as (Hc1 & Hc2 & ETC).
destruct (tb_budget cx i HP HB Hi) as (Hbud & HTC).
assert (Hk : (i + 1) * U_EV_TURN = i * U_EV_TURN + PN.CNO_EV + PV.CV_EV)
  by (unfold U_EV_TURN, PN.CNO_EV, PV.CV_EV; lia).
assert (KV : forall a, u_sp0 cx - 96 <= a < u_sp0 cx -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a)
  by (intros a Ha; apply HK; unfold u_sp1, U_FRAME, LLVMF_STK in *; lia).
refine (conj _ (conj _ (conj _ _))).
- rewrite Hk. refine (conj HJ' (conj Hfrs (conj _ (conj _ (conj _ (conj _ (conj _ Hperm))))))).
  + unfold spZ in *. rewrite (KA 2%bv ltac:(tb_in)). exact Hsp.
  + rewrite (KA 3%bv ltac:(tb_in)). exact Hgp.
  + rewrite (KA 4%bv ltac:(tb_in)). exact Htp.
  + rewrite (KA 27%bv ltac:(tb_in)). exact H27.
  + exact (tb_saved_kept cx _ _ Hsv KV).
- split.
  + apply (mo_le_mono MT ML _ _ _ _ Hle). lia.
  + apply (mo_ok_le MT ML _ _ _ Hmo). lia.
- destruct HR as (Hlv & Hfv & Hw). refine (conj _ (conj _ _)).
  + rewrite length_app. cbn [length]. lia.
  + apply Forall_app. split; [exact Hfv | constructor; [exact Hv | constructor]].
  + intros j Hj. destruct (Z.eq_dec j i) as [-> | Hne].
    * rewrite app_nth2 by lia. replace (Z.to_nat i - length vs)%nat with 0%nat by lia. cbn [nth]. exact Hrd.
    * rewrite app_nth1 by lia. intros kk Hkk. rewrite HK by (unfold u_sp1, U_FRAME, LLVMF_STK in *; lia).
      exact (Hw j ltac:(lia) kk Hkk).
- rewrite (KA 8%bv ltac:(tb_in)), (KA 9%bv ltac:(tb_in)), (KA 18%bv ltac:(tb_in)), (KA 22%bv ltac:(tb_in)),
    (KA 25%bv ltac:(tb_in)), (KA 26%bv ltac:(tb_in)).
  refine (conj R8 (conj R9 (conj R18 (conj Hmm (conj R22 (conj R23' (conj R24' (conj R25 (conj R26 _))))))))). lia.
Qed.
End tb.
