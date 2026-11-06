From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgWalk CPgWalkIntr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= the walk's start state ======================= *)
Definition A_SYSEX : Z := 0x848b4.
(* atoms 33 .. 33 + nn - 1 hold the payload bytes, atoms 33 + nn .. 33 + nn + 31 the 32 bytes of out before the call *)
Definition sx_bc (nn : nat) (i : Z) : YP09.chunk := YP09.mkChunk i (CVal 1 (SOff (33 + nn + Z.to_nat i) 0)).
(* out[0 .. 4) and out[nn + 4 .. 32): the bytes the call stores, each holding its byte of `before` *)
Definition sx_hd (nn : nat) : YP09.region := YP09.mkRegion (Some 14%nat) 0 4 0 4 (map (sx_bc nn) [0; 1; 2; 3]).
Definition sx_tl (nn : nat) : YP09.region :=
  YP09.mkRegion (Some 14%nat) (Z.of_nat nn + 4) 32 (Z.of_nat nn + 4) 32
    (map (sx_bc nn) (map Z.of_nat (seq (nn + 4) (28 - nn)))).
Definition sx_rs (nn : nat) : smem := [sx_hd nn; sx_tl nn].
Definition SX_OUTHI : Z := 0x7fffff800000 - 32.
Definition sx_AF (nn : nat) : list (nat * afact) :=
  [(10%nat, mkAF 0 255 0); (11%nat, mkAF 0 255 0); (13%nat, mkAF (Z.of_nat nn) (Z.of_nat nn) 0);
   (14%nat, mkAF 4096 SX_OUTHI 0)] ++
  match nn with O => [] | S _ => [(12%nat, mkAF 1 (2 ^ 47 - 1 - Z.of_nat nn) 0)] end.
Definition sx_ss (nn : nat) : sstate :=
  mkSS A_SYSEX sr_atoms (cw_regs 48 ++ sx_rs nn) None (mkFacts (cw_atoms ++ sx_AF nn) [] []).
Definition sx_SH : list shent := [mkSHE 14 0 32].
Definition sx_zone (sp out : Z) (nn : nat) (a : Z) : Prop :=
  (sp - 48 <= a < sp) \/ (out <= a < out + 4) \/ (out + Z.of_nat nn + 4 <= a < out + 32).
(* after __asan_memcpy: the call's whole window [sp - T, sp) and out[0 .. 32) *)
Definition sx_zone2 (sp out : Z) (a : Z) : Prop := (sp - (48 + 4096) <= a < sp) \/ (out <= a < out + 32).
(* the payload pl[0 .. nn), read-only, each byte its atom 33 + i *)
Definition sx_pc (i : Z) : YP09.chunk := YP09.mkChunk i (CVal 1 (SOff (33 + Z.to_nat i) 0)).
Definition sx_pl (nn : nat) : YP09.region :=
  YP09.mkRegion (Some 12%nat) 0 (Z.of_nat nn) 0 0 (map sx_pc (map Z.of_nat (seq 0 nn))).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma sx_ew_x : forall regs bs before (nn : nat) i, length bs = nn -> (i < 32)%nat ->
  ew (Ereg regs (cw_extra (bs ++ before))) (33 + nn + i) = Z_to_bv 64 (nth i before 0).
Proof.
intros regs bs before nn i Hl Hi. replace (33 + nn + i)%nat with (33 + (nn + i))%nat by lia.
rewrite cw_ew_x. rewrite app_nth2 by lia. f_equal. f_equal. lia.
Qed.
Lemma sx_chunk_ok : forall regs bs before (nn : nat) mem out i,
  length bs = nn -> garr8 tfibsegs mem out before -> length before = 32%nat -> 0 <= i < 32 ->
  YP09.chunk_ok tfibsegs (Ereg regs (cw_extra (bs ++ before))) mem out (sx_bc nn i).
Proof.
intros regs bs before nn mem out i Hl HG Hlen Hi. unfold sx_bc.
destruct (HG (Z.to_nat i) ltac:(lia)) as [Hv Hr]. rewrite Z2Nat.id in Hv by lia.
apply (chunk_ok_val tfibsegs _ _ out i 1 _ (nth (Z.to_nat i) before 0)); [| lia | lia | exact Hv].
rewrite sv_denot_SOff0. apply sx_ew_x; [exact Hl | lia].
Qed.
Lemma sx_chunks_ok : forall regs bs before (nn : nat) mem out l,
  length bs = nn -> garr8 tfibsegs mem out before -> length before = 32%nat -> Forall (fun i => 0 <= i < 32) l ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs (cw_extra (bs ++ before))) mem out) (map (sx_bc nn) l).
Proof.
intros regs bs before nn mem out l Hl HG Hlen Hi. apply Forall_map. eapply Forall_impl; [|exact Hi].
intros i Hi'. apply sx_chunk_ok; assumption.
Qed.

Lemma sx_atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
intros E l1 l2 H1 H2. induction l1 as [|[n f] l1 IH]; cbn [app atoms_ok] in *; [exact H2|].
destruct H1 as [A B']. split; [exact A | apply IH; exact B'].
Qed.
Lemma sx_ew_b : forall regs bs before j, (j < length bs)%nat ->
  ew (Ereg regs (cw_extra (bs ++ before))) (33 + j) = Z_to_bv 64 (nth j bs 0).
Proof. intros regs bs before j Hj. rewrite cw_ew_x. rewrite app_nth1 by exact Hj. reflexivity. Qed.
Lemma sx_pl_chunks_ok : forall E mem pl bs,
  (forall j, (j < length bs)%nat -> ew E (33 + j) = Z_to_bv 64 (nth j bs 0)) ->
  garr8 tfibsegs mem pl bs ->
  Forall (YP09.chunk_ok tfibsegs E mem pl) (map sx_pc (map Z.of_nat (seq 0 (length bs)))).
Proof.
intros E mem pl bs EXb HG. apply Forall_map, Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
unfold sx_pc. rewrite Nat2Z.id. destruct (HG j ltac:(lia)) as [Hv Hr].
apply (chunk_ok_val tfibsegs E mem pl (Z.of_nat j) 1 _ (nth j bs 0)); [| lia | lia | exact Hv].
rewrite sv_denot_SOff0. apply EXb. lia.
Qed.
Lemma sx_ra_keep : forall (H : word -> bool) (m m' : word -> option byte) q n,
  range_addressable (aview tfibsegs H m) SHADOW_OFF q n ->
  (forall x, q <= x < q + n -> aview tfibsegs H m' (shadow_of_addr SHADOW_OFF x) = aview tfibsegs H m (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable (aview tfibsegs H m') SHADOW_OFF q n.
Proof. intros H m m' q n HR HK x Hx. rewrite (HK x Hx). exact (HR x Hx). Qed.
Lemma sx_denot_off : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = w64 (x + c).
Proof. intros E n x c Hn Hx Hc. rewrite denot_lit_U, (U_atom_off E n x c Hn Hx Hc). reflexivity. Qed.
Lemma sx_div8 : forall x, 0 <= x -> 0 <= x / 8 /\ 8 * (x / 8) <= x.
Proof. intros x Hx. split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]. Qed.
(* the 8-byte-aligned shadow hull of a sub-range lies in the hull of the range; a kept hull stays visible *)
Lemma sx_hull_keep : forall (H : word -> bool) (m m' : word -> option byte) x n x' n',
  shadow_hull_vis (aview tfibsegs H m) x n -> 0 <= x -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
     aview tfibsegs H m' s = aview tfibsegs H m s) ->
  shadow_hull_vis (aview tfibsegs H m') x' n'.
Proof.
intros H m m' x n x' n' Hh H0 H1 H2 H3 HK s Hs.
assert (M : forall a b, 0 <= a <= b -> shadow_addr a / 8 * 8 <= shadow_addr b / 8 * 8).
{ intros a b Hab. unfold shadow_addr. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
  apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (Hs' : shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8).
{ pose proof (M x x' ltac:(lia)). pose proof (M (x' + n' - 1) (x + n - 1) ltac:(lia)). lia. }
rewrite (HK s Hs'). exact (Hh s Hs').
Qed.
(* the hull of an application range lies in the shadow band, below kHighMemBeg *)
Lemma sx_hull_band : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 - 1 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> SHADOW_OFF - 8 <= s < SHADOW_OFF + 2 ^ 44.
Proof.
intros x n s Hx Hn Hxn Hs. unfold shadow_addr, SHADOW_OFF in *.
pose proof (sx_div8 x Hx) as [A1 A2]. pose proof (sx_div8 (x + n - 1) ltac:(lia)) as [B1 B2].
pose proof (sx_div8 (2147450880 + x / 8) ltac:(lia)) as [C1 C2].
pose proof (Z.mul_succ_div_gt (2147450880 + x / 8) 8 ltac:(lia)) as C3.
pose proof (sx_div8 (2147450880 + (x + n - 1) / 8) ltac:(lia)) as [D1 D2].
assert ((x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
lia.
Qed.
Lemma sx_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) q l,
  garr8 tfibsegs (mrestrict H m) q l ->
  (forall x, q <= x < q + Z.of_nat (length l) -> aview tfibsegs H m' x = aview tfibsegs H m x) ->
  garr8 tfibsegs (mrestrict H m') q l.
Proof.
intros H m m' q l HG HK j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
apply (cw_val_mem_kept H H m m'); [|exact Hv]. intros x Hx. apply HK. lia.
Qed.
Lemma sx_img : forall a, (0x9db10 <= a < 0x9db18) \/ (0xa6478 <= a < 0xa6480) -> in_img tfibsegs a.
Proof.
intros a [Ha|Ha]; unfold in_img; eexists; split;
[right; right; left; reflexivity | | right; right; right; left; reflexivity |];
match goal with |- ?l <= a < ?l2 + ?s =>
  let l' := eval vm_compute in l in let l2' := eval vm_compute in l2 in let s' := eval vm_compute in s in
  change l with l'; change l2 with l2'; change s with s' end; lia.
Qed.
Section c.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
(* out lies off the two image cells the walk reads (a byte of a block or a live frame is no byte of the image) *)
Lemma sx_out_cells : forall lyc Sc (W : world tfibsegs) memc mdc out,
  AR tfibsegs B lyc Sc W memc mdc -> tdst_ok B lyc Sc out 32 ->
  (out + 32 <= A_GOT_shadow \/ A_GOT_shadow + 8 <= out) /\ (out + 32 <= A_shadow_glob \/ A_shadow_glob + 8 <= out).
Proof.
intros lyc Sc W memc mdc out HAR Htd. unfold A_GOT_shadow, A_shadow_glob.
split; [destruct (Z_le_gt_dec (out + 32) 0x9db10); [left; lia|]; destruct (Z_le_gt_dec (0x9db10 + 8) out); [right; lia|]
       |destruct (Z_le_gt_dec (out + 32) 0xa6478); [left; lia|]; destruct (Z_le_gt_dec (0xa6478 + 8) out); [right; lia|]];
exfalso; [apply (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc out 32 (Z.max out 0x9db10) HAR Htd); [lia|]
         |apply (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc out 32 (Z.max out 0xa6478) HAR Htd); [lia|]];
apply sx_img; lia.
Qed.
Lemma sx_entry : forall (nn : nat) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k regs
  dev fn pl out bs before,
  cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_sysex ->
  arg_zxA 8 (getr regs 10) dev -> arg_zxA 8 (getr regs 11) fn ->
  getr regs 12 = w64 pl -> ((0 < nn)%nat -> 1 <= pl <= 2 ^ 47 - 1 - Z.of_nat nn) ->
  getr regs 13 = w64 (Z.of_nat nn) -> length bs = nn -> (nn <= 24)%nat ->
  getr regs 14 = w64 out ->
  cenc_out tfibsegs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_sysex out before ->
  regions_wf (cw_regs 48 ++ sx_rs nn) = true ->
  st_ok tfibsegs (Ereg regs (cw_extra (bs ++ before))) (sx_ss nn)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_SYSEX) memc (seg_rom tfibsegs))).
Proof.
intros nn STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs dev fn pl out bs before
  HE [Hdv Hdev] [Hfv Hfn] H12 Hpl H13 Hl Hnn H14 HOUT Hwf.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_sysex HE
  ltac:(unfold T_sysex, ESTACK; lia)) as (Hceil & H47 & H46 & Hal & Hpres).
pose proof HE as ((HAR & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HOUT as ((Hq0 & Hq32 & Htd & Htw & Hra & Hhull & Ham & Hcw) & HGb & Hlenb).
pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc out 32 out HAR Htd ltac:(lia)) as [O1 _].
pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc out 32 (out + 31) HAR Htd ltac:(lia)) as [O2 _].
pose proof (sx_out_cells lyc Sc W memc mdc out HAR Htd) as [DG DC].
set (E := Ereg regs (cw_extra (bs ++ before))).
assert (U14 : bv_unsigned (ew E 14) = out).
{ subst E. rewrite (cw_ew_reg regs _ 14 14%bv eq_refl), H14. unfold w64. apply unsigned_lit_small. lia. }
assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs _ 2 2%bv eq_refl); reflexivity).
unfold T_sysex, ESTACK in *.
unfold sx_ss. apply (cw_entry B TL LAWS A_SYSEX 48 (bs ++ before) (sx_rs nn) (sx_AF nn) lyc Sc W regs memc mdc HAR).
- lia.
- lia.
- exact Hal.
- intros a Ha. apply Hpres. lia.
- exact Hwf.
- unfold sx_rs, sx_hd, sx_tl. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; fold E; rewrite U14.
  + split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs). exact (proj1 (proj2 (Htw (out + o) ltac:(lia)))).
    * apply sx_chunks_ok; [exact Hl | exact HGb | exact Hlenb |]. repeat (apply Forall_cons; [lia|]). apply Forall_nil.
  + split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs). exact (proj1 (proj2 (Htw (out + o) ltac:(lia)))).
    * apply sx_chunks_ok; [exact Hl | exact HGb | exact Hlenb |]. apply Forall_forall. intros x Hx.
      apply in_map_iff in Hx as (j & <- & Hj). apply in_seq in Hj. lia.
- apply pairwise_disjoint_of_extents.
  unfold cw_regs, sx_rs, sx_hd, sx_tl, stack_region, got_region, bcell_region, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite U2, U14.
  unfold A_GOT_shadow, A_shadow_glob in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- unfold sx_AF. apply sx_atoms_ok_app.
  + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    subst E. rewrite (cw_ew_reg regs _ 10 10%bv eq_refl), (cw_ew_reg regs _ 11 11%bv eq_refl),
      (cw_ew_reg regs _ 13 13%bv eq_refl), (cw_ew_reg regs _ 14 14%bv eq_refl), Hdev, Hfn, H13, H14.
    unfold w64. rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SX_OUTHI. repeat split; lia.
  + destruct nn as [|nn']; [exact I|]. specialize (Hpl ltac:(lia)).
    cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    subst E. rewrite (cw_ew_reg regs _ 12 12%bv eq_refl), H12.
    unfold w64. rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
Qed.
(* out unchanged: its bytes in the two regions still hold the chunks of `before`, the bytes between kept *)
Lemma sx_garr8_before : forall E (H : word -> bool) m memc out (nn : nat) before,
  (forall j, (j < 32)%nat -> ew E (33 + nn + j) = Z_to_bv 64 (nth j before 0)) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict H m) out) (map (sx_bc nn) [0; 1; 2; 3]) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict H m) out) (map (sx_bc nn) (map Z.of_nat (seq (nn + 4) (28 - nn)))) ->
  (forall a, out + 4 <= a < out + Z.of_nat nn + 4 -> aview tfibsegs H m a = aview tfibsegs H memc a) ->
  garr8 tfibsegs (mrestrict H memc) out before -> length before = 32%nat -> (nn <= 28)%nat ->
  garr8 tfibsegs (mrestrict H m) out before.
Proof.
intros E H m memc out nn before EX Fh Ft KM HG Hlen Hnn j Hj. rewrite Hlen in Hj.
destruct (HG j ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
destruct (Nat.lt_ge_cases j 4) as [J4|J4]; [|destruct (Nat.lt_ge_cases j (nn + 4)) as [J5|J5]].
- assert (Hc : YP09.chunk_ok tfibsegs E (mrestrict H m) out (sx_bc nn (Z.of_nat j))).
  { rewrite Forall_forall in Fh. apply Fh. apply in_map. cbn [In].
    destruct j as [|[|[|[|j]]]]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; [tauto | tauto | tauto | tauto | lia]. }
  unfold sx_bc in Hc. rewrite Nat2Z.id in Hc.
  apply (val_of_chunk_ok tfibsegs E _ out (Z.of_nat j) 1 _ (nth j before 0) Hc); [| lia | lia].
  rewrite sv_denot_SOff0. apply EX. lia.
- eapply (val_mem_kept tfibsegs); [| exact Hv]. intros kk Hkk. apply KM. lia.
- assert (Hc : YP09.chunk_ok tfibsegs E (mrestrict H m) out (sx_bc nn (Z.of_nat j))).
  { rewrite Forall_forall in Ft. apply Ft. apply in_map. apply in_map. apply in_seq. lia. }
  unfold sx_bc in Hc. rewrite Nat2Z.id in Hc.
  apply (val_of_chunk_ok tfibsegs E _ out (Z.of_nat j) 1 _ (nth j before 0) Hc); [| lia | lia].
  rewrite sv_denot_SOff0. apply EX. lia.
Qed.
End c.
End b.

(* ======================= sysex_spec on each path (lib/Prog/diginet_sysex_encode.v's, restated) ======================= *)
Lemma sx_spec_arg : forall dev fn l, 0x7f < dev -> sysex_spec dev fn l = (E_ARG, None).
Proof. intros dev fn l H. unfold sysex_spec. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.
Lemma sx_spec_refused : forall dev l, dev <= 0x7f -> sysex_spec dev 0x70 l = (E_REFUSED, None).
Proof. intros dev l H. unfold sysex_spec. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.
Lemma sx_spec_rfn : forall dev fn l, dev <= 0x7f -> fn <> 0x70 -> 0x7f < fn -> sysex_spec dev fn l = (E_RANGE, None).
Proof.
intros dev fn l H H0 H1. unfold sysex_spec.
rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.ltb_lt _ _) H1). reflexivity.
Qed.
Lemma sx_spec_space : forall dev fn l, dev <= 0x7f -> fn <> 0x70 -> fn <= 0x7f -> 24 < Z.of_nat (length l) + 5 ->
  sysex_spec dev fn l = (E_SPACE, None).
Proof.
intros dev fn l H H0 H1 H2. unfold sysex_spec. rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.eqb_neq _ _) H0),
  (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H2). reflexivity.
Qed.
Lemma sx_spec_rpl : forall dev fn l, dev <= 0x7f -> fn <> 0x70 -> fn <= 0x7f -> Z.of_nat (length l) + 5 <= 24 ->
  existsb (fun x => Z.testbit x 7) l = true -> sysex_spec dev fn l = (E_RANGE, None).
Proof.
intros dev fn l H H0 H1 H2 H3. unfold sysex_spec. rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.eqb_neq _ _) H0),
  (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2), H3. reflexivity.
Qed.
Lemma sx_spec_ok : forall dev fn l, dev <= 0x7f -> fn <> 0x70 -> fn <= 0x7f -> Z.of_nat (length l) + 5 <= 24 ->
  existsb (fun x => Z.testbit x 7) l = false ->
  sysex_spec dev fn l = (0, Some ([0xf0; 0x13; dev; fn] ++ l ++ [0xf7], 0, bit_or_0 ((fn =? 0x40) || (fn =? 0x30)) 1)).
Proof.
intros dev fn l H H0 H1 H2 H3. unfold sysex_spec. rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.eqb_neq _ _) H0),
  (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2), H3. reflexivity.
Qed.

(* ======================= the engine's conditions as Z facts ======================= *)
Lemma sx_br_lt0 : forall E e, branch_taken BC_LT (sv_denot E e) (sv_denot E (SLit 0)) = (2 ^ 63 <=? U E e).
Proof.
intros E e. pose proof (U_range E e) as Hr. unfold M64 in Hr.
cbn [branch_taken]. rewrite (denot_lit_U E e). cbn [sv_denot]. unfold bv_lts. rewrite !Z_to_bv_signed.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
change ((0 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63) with 0.
destruct (Z.leb_spec (2 ^ 63) (U E e)).
- replace (U E e + 2 ^ 63) with ((U E e - 2 ^ 63) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
  rewrite Z.mod_small by lia. apply Z.ltb_lt. lia.
- rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.
Lemma sx_U_sext8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  U E (SExt true 8 (SOff n 0)) = if v <? 128 then v else v + (2 ^ 64 - 2 ^ 8).
Proof.
intros E n v Hn Hv. rewrite U_SExt. cbv iota beta. rewrite (U_atom E n v Hn) by lia.
change (2 ^ Z.of_N 8) with (2 ^ 8). rewrite (Z.mod_small v) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap.
replace (bv_half_modulus 8) with (2 ^ 7) by reflexivity. replace (bv_modulus 8) with (2 ^ 8) by reflexivity.
destruct (Z.ltb_spec v 128).
- rewrite (Z.mod_small (v + 2 ^ 7)) by lia. replace (v + 2 ^ 7 - 2 ^ 7) with v by lia. apply Z.mod_small. lia.
- replace (v + 2 ^ 7) with ((v - 2 ^ 7) + 1 * 2 ^ 8) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (v - 2 ^ 7)) by lia.
  replace (v - 2 ^ 7 - 2 ^ 7) with ((v + (2 ^ 64 - 2 ^ 8)) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma sx_bit7 : forall v, 0 <= v < 256 -> Z.testbit v 7 = (128 <=? v).
Proof.
intros v Hv.
assert (C : forallb (fun x => Bool.eqb (Z.testbit x 7) (128 <=? x)) (map Z.of_nat (seq 0 256)) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in C.
specialize (C v ltac:(apply in_map_iff; exists (Z.to_nat v); split; [lia | apply in_seq; lia])).
apply Bool.eqb_prop in C. exact C.
Qed.
(* `lb` of a payload byte v, then `bltz`: taken exactly when bit 7 of v is set *)
Lemma sx_br_sext8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  branch_taken BC_LT (sv_denot E (SExt true 8 (SOff n 0))) (sv_denot E (SLit 0)) = Z.testbit v 7.
Proof.
intros E n v Hn Hv. rewrite sx_br_lt0, (sx_U_sext8 E n v Hn Hv), sx_bit7 by exact Hv.
destruct (Z.ltb_spec v 128); [destruct (Z.leb_spec (2 ^ 63) v); destruct (Z.leb_spec 128 v); first [reflexivity | lia]|].
destruct (Z.leb_spec (2 ^ 63) (v + (2 ^ 64 - 2 ^ 8))); destruct (Z.leb_spec 128 v); first [reflexivity | lia].
Qed.
Lemma sx_ex_hit : forall l i, (i < length l)%nat -> Z.testbit (nth i l 0) 7 = true ->
  existsb (fun x => Z.testbit x 7) l = true.
Proof.
intros l i Hi H. apply existsb_exists. exists (nth i l 0). split; [apply nth_In; exact Hi | exact H].
Qed.
Lemma sx_ex_none : forall l, (forall i, (i < length l)%nat -> Z.testbit (nth i l 0) 7 = false) ->
  existsb (fun x => Z.testbit x 7) l = false.
Proof.
induction l as [|x l IH]; intros H; [reflexivity|]. cbn [existsb].
pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn [nth] in H0. rewrite H0. cbn [orb].
apply IH. intros i Hi. apply (H (S i)). cbn. lia.
Qed.
(* the display byte: `addi; andi 239; seqz` of fn is 1 exactly for fn = 0x30 or 0x40 *)
Lemma sx_U_disp : forall E fn, ew E 11 = Z_to_bv 64 fn -> 0 <= fn < 256 ->
  U E (SAlu ALU_SLTU (SAlu ALU_AND (SOff 11 (-48)) (SLit 239)) (SLit 1)) = bit_or_0 ((fn =? 0x40) || (fn =? 0x30)) 1.
Proof.
intros E fn Hn Hf. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_and_lit by lia.
rewrite (cw_U_offx E 11 fn (-48) Hn ltac:(lia)). rewrite U_SLit.
assert (C : forallb (fun f => Z.eqb (zcanon (if Z.land ((f + -48) mod 2 ^ 64) 239 <? zcanon 1 then 1 else 0))
  (bit_or_0 ((f =? 0x40) || (f =? 0x30)) 1)) (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C.
specialize (C fn ltac:(apply in_map_iff; exists (Z.to_nat fn); split; [lia | apply in_seq; lia])).
apply Z.eqb_eq in C. exact C.
Qed.
(* a one-byte chunk of a region's chunk list gives the byte's view *)
Lemma sx_chunk_in : forall E (H : word -> bool) m base cs off e v,
  Forall (YP09.chunk_ok tfibsegs E (mrestrict H m) base) cs -> In (YP09.mkChunk off (CVal 1 e)) cs ->
  v = U E e mod 256 -> aview tfibsegs H m (base + off) = Some v.
Proof.
intros E H m base cs off e v HF Hin ->. rewrite Forall_forall in HF. specialize (HF _ Hin).
pose proof (val_of_chunk_any tfibsegs E (mrestrict H m) base off 1 e HF ltac:(lia)) as V.
change (2 ^ (8 * Z.of_N 1)) with 256 in V. unfold U.
apply (aview_of_val_mem1 tfibsegs H m (base + off) _ V). apply Z.mod_pos_bound. lia.
Qed.
(* the four bytes of a 4-byte zero chunk *)
Lemma sx_chunk_zero4 : forall E (H : word -> bool) m base cs off k,
  Forall (YP09.chunk_ok tfibsegs E (mrestrict H m) base) cs -> In (YP09.mkChunk off (CVal 4 (SLit 0))) cs ->
  0 <= k < 4 -> aview tfibsegs H m (base + off + k) = Some 0.
Proof.
intros E H m base cs off k HF Hin Hk. rewrite Forall_forall in HF. specialize (HF _ Hin).
destruct (HF k ltac:(cbn; lia)) as (b & Hb & Hm). cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb, Hm.
injection Hb as <-. unfold aview. rewrite Hm. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. cbn [sv_denot]. rewrite Z_to_bv_unsigned.
change (bv_wrap 64 0) with 0. rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma sx_vm1 : forall (H : word -> bool) (m : word -> option byte) a v,
  aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
destruct (aview_byte tfibsegs H m a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite !(Z.mod_small (bv_unsigned b) 256) by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma sx_U_sll56 : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 256 ->
  U E (SAlu ALU_SLL (SOff n 0) (SLit 56)) = x * 2 ^ 56.
Proof.
intros E n x Hn Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn) by lia. rewrite U_SLit.
change (Z.land (zcanon 56) 63) with 56. rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* ======================= the walk's tactics ======================= *)
(* every write window lies in the save area, out[0 .. 4) or out[nn + 4 .. 32), which the caller lets the call write *)
Ltac sx_ew_peel := repeat first [ rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia
  | match goal with Q : forall k, (k < _)%nat -> ew ?X k = ew _ k |- context [ew ?X _] => rewrite Q by lia end ].
Ltac sx_ew_peel_in H := repeat first [ rewrite ew_ewset_other in H by lia | rewrite ew_havoc_old in H by lia
  | match goal with Q : forall k, (k < _)%nat -> ew ?X k = ew _ k |- _ =>
      match type of H with context [ew X _] => rewrite Q in H by lia end end ].
(* seal the walk's env: each run extends it, and every later step that reads an atom walks the extensions. Name it
   Es, keep what the rest of the walk reads of it (env agreement with the entry env for the leaf, its first Kat atoms
   as the entry env's, ra), and forget its structure. *)
Ltac sx_seal HAE E1 Kat :=
idtac; lazymatch goal with HS : st_ok _ ?En _ _ |- _ =>
first [ is_var En |
lazymatch type of HAE with env_agree 32 ?Eb _ =>
lazymatch type of E1 with ew ?E0 1 = ?v1 =>
  let HAE2 := fresh "HAE" in let E1' := fresh "E1s" in let EQ := fresh "EQ" in let Es := fresh "Es" in
  assert (HAE2 : env_agree 32 Eb En) by (env_agree_chain HAE);
  assert (EQ : forall k, (k < Kat)%nat -> ew En k = ew E0 k)
    by (let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; sx_ew_peel; reflexivity);
  assert (E1' : ew En 1 = v1) by (rewrite (EQ 1%nat ltac:(lia)); exact E1);
  repeat match goal with
  | Q : forall k, (k < _)%nat -> ew ?X k = ew E0 k |- _ => lazymatch X with En => fail | _ => clear Q end
  | Q : ew ?X 1 = v1 |- _ => lazymatch X with En => fail | E0 => fail | _ => clear Q end
  end;
  set (Es := En) in *; clearbody Es; clear HAE; rename HAE2 into HAE
end end ] end.
Ltac sx_awr Htw B14 :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch goal with B2 : bv_unsigned (ew _ 2) = ?spv |- _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
  [reflexivity | sx_ew_peel; rewrite B2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
| eapply cw_awr_ok_cons_twr with (m := 14%nat) (n := 32);
  [reflexivity | sx_ew_peel; exact B14 | cbn; lia | cbn; lia | exact Htw |] ]
end end.
Ltac sx_kwr B14 :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
unfold sx_zone;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; sx_ew_peel_in Hb;
first [ lazymatch goal with B2 : bv_unsigned (ew _ 2) = _ |- _ => rewrite B2 in Hb end; lia
      | rewrite B14 in Hb; lia | lia ] | ]);
destruct Hr.
Ltac sx_kwr2 B14 :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
unfold sx_zone2;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; sx_ew_peel_in Hb;
first [ lazymatch goal with B2 : bv_unsigned (ew _ 2) = _ |- _ => rewrite B2 in Hb end; lia
      | rewrite B14 in Hb; lia | lia ] | ]);
destruct Hr.
Ltac sx_probe := lazymatch goal with HS : st_ok _ _ ?ss _ |- _ => let v := eval vm_compute in ss in
  lazymatch goal with SH : sh_ok _ _ ?SHl _ _ |- _ =>
  let r := eval vm_compute in (sym_runN_tok tfibsegs tfibtbl_lib (run_K 0 CW_Bx SHl v) CW_Bx CW_Bspan SHl FUEL v) in
  lazymatch r with (?st, ?rs) => let pc := eval vm_compute in (ss_pc (sh_ss st)) in
  let rg := eval vm_compute in (ss_regs (sh_ss st)) in fail 0 "PROBE" pc rs rg end end end.
Ltac sx_probe_full := lazymatch goal with HS : st_ok _ _ ?ss _ |- _ => let v := eval vm_compute in ss in fail 0 "PROBEF" v end.
(* the region at index i of the state's memory, as region_ok *)
Ltac sx_reg HS i HR :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r := eval vm_compute in (nth_error (ss_mem ssx) i) in
lazymatch r with Some ?rr => pose proof (st_ok_region_nth Ex ssx msx i rr HS ltac:(vm_compute; reflexivity)) as HR end end.
(* register r at the stop, as the engine's symbolic value *)
Ltac sx_rg HS r R :=
lazymatch type of HS with st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
assert (R : getr (ms_regs ms) r = sv_denot Ex e) by exact (st_ok_restrict_reg segs Hh Ex ss ms r HS) end.
(* the region of out (atom 14) whose window starts at lo *)
Ltac sx_reg14 HS lo HR :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let i := eval vm_compute in
  (idx_of (fun r : YP09.region => match YP09.r_base r with Some 14%nat => Z.eqb (YP09.r_lo r) lo | _ => false end) (ss_mem ssx)) in
sx_reg HS i HR end.
(* drop the .got slot and the shadow-offset cell (regions 1 and 2), keep the save area and out's two regions *)
Ltac sx_drop_gb :=
lazymatch goal with HS : st_ok _ ?Ev ?ssv ?msv |- _ =>
  let l := eval vm_compute in (ss_mem ssv) in
  let l' := eval vm_compute in (match l with r0 :: _ :: _ :: t => r0 :: t | _ => l end) in
  let HS1 := fresh "HS" in
  assert (HS1 : st_ok tfibsegs Ev (mkSS (ss_pc ssv) (ss_regs ssv) l' (ss_resv ssv) (ss_facts ssv)) msv)
  by (apply (st_ok_submem tfibsegs Ev ssv msv l' HS); [change (submem l' l); submem_to | reflexivity]);
  clear HS; rename HS1 into HS end.

(* the memory clause of a leaf before the call: what the walk kept, its write set out[0 .. 32) *)
Ltac sx_ktac HJ0 Htd B LAWS :=
idtac; lazymatch goal with KE : forall a, _ -> ~ sx_zone _ _ _ a -> _ |- _ =>
cw_kept HJ0 KE
  ltac:(let a := fresh "a" in let Ha := fresh "Ha" in let Hi := fresh "Hi" in intros a Ha Hi; unfold cenc_wr in Ha;
        exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ 32 a (proj1 HJ0) Htd Ha Hi))
  ltac:(let a := fresh "a" in let Hz := fresh "Hz" in intros a Hz; unfold sx_zone, cenc_wr, T_sysex, ESTACK in *;
        destruct Hz as [Hz|[Hz|Hz]]; [left; lia | right; lia | right; lia]) end.
(* a failing return: a0 = rc, out as before (out's two regions untouched since the entry) *)
Ltac sx_fail_res Hspec nn EX HGb Hlenb B14 :=
idtac; lazymatch type of EX with forall j, _ -> ew ?E _ = Z_to_bv 64 (nth j ?before 0) =>
lazymatch type of HGb with garr8 _ (mrestrict (w_H ?W) ?memc) ?out _ =>
lazymatch goal with KE : forall a, _ -> ~ sx_zone _ _ _ a -> _ |- _ =>
unfold cenc_res; rewrite Hspec; cbn [fst snd cmd_outZ]; split;
[ lazymatch goal with |- ?lhs = _ => lazymatch goal with R : lhs = _ |- _ => rewrite R end end;
  unfold w64; apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn [sv_denot]; rewrite ?Z_to_bv_unsigned; reflexivity
| lazymatch goal with HS : st_ok _ ?Ex _ (restrict _ ?ms) |- _ =>
  let EX' := fresh "EX" in
  assert (EX' : forall j, (j < 32)%nat -> ew Ex (33 + nn + j) = Z_to_bv 64 (nth j before 0))
    by (let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; sx_ew_peel; apply EX; exact Hj);
  let HR3 := fresh "HR" in let HR4 := fresh "HR" in sx_reg14 HS 0 HR3; sx_reg14 HS (Z.of_nat nn + 4) HR4;
  unfold region_ok in HR3, HR4; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict] in HR3, HR4;
  sx_ew_peel_in HR3; sx_ew_peel_in HR4; rewrite B14 in HR3, HR4;
  let Fh := fresh "Fh" in let Ft := fresh "Ft" in destruct HR3 as (_ & _ & _ & Fh); destruct HR4 as (_ & _ & _ & Ft);
  apply (sx_garr8_before Ex (w_H W) (ms_mem ms) memc out nn before EX' Fh Ft);
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in intros a Ha; apply KE; [lia|];
    unfold sx_zone, coff_win, T_sysex, ESTACK in *; intros [Hz|[Hz|Hz]]; lia
  | exact HGb | exact Hlenb | lia ] end ] end end end.
Ltac sx_fail_leaf Hspec nn HJ0 Htd EX HGb Hlenb B14 B LAWS :=
cw_leaf ltac:(sx_ktac (proj1 HJ0) Htd B LAWS) ltac:(sx_fail_res Hspec nn EX HGb Hlenb B14).
(* the payload byte i (atom n = 33 + i) tested by `lb; bltz`, as Z.testbit of the byte *)
Ltac sx_bit Hy n i EXb HGp :=
lazymatch type of Hy with context [sv_denot ?Ex (SExt true 8 (SOff n 0))] =>
lazymatch type of HGp with garr8 _ _ _ ?bs =>
rewrite (sx_br_sext8 Ex n (nth i bs 0) ltac:(sx_ew_peel; exact (EXb i ltac:(lia))) (proj2 (HGp i ltac:(lia)))) in Hy
end end.
(* the leaf's bytes: each byte of out from its chunk (sx_val proves the value), from the copy (KM), or zero *)
Ltac sx_val E10 E11 E13 :=
first [ reflexivity
      | lazymatch type of E11 with ew _ 11 = Z_to_bv 64 ?f =>
        lazymatch goal with |- context [U ?Ex (SAlu ALU_SLTU _ _)] =>
          unfold u8; rewrite (sx_U_disp Ex f ltac:(sx_ew_peel; exact E11) ltac:(lia)); reflexivity end end
      | rewrite U_SOff; sx_ew_peel;
        first [ rewrite E10 | rewrite E11 | rewrite E13
              | match goal with Hx : ew _ ?k = Z_to_bv 64 _ |- context [ew _ ?k] => rewrite Hx end ];
        rewrite unsigned_lit_small by lia; rewrite ?Z.add_0_r; rewrite zcanon_id by (unfold M64; lia); unfold u8;
        first [reflexivity | rewrite Z.mod_small by lia; reflexivity] ].
Ltac sx_inl := solve [cbn [In]; repeat (first [left; reflexivity | right])].
Ltac sx_byte Fh Ft KM E10 E11 E13 :=
split;
[ apply sx_vm1;
  first [ eapply sx_chunk_in; [exact Fh | sx_inl | sx_val E10 E11 E13]
        | eapply sx_chunk_in; [exact Ft | sx_inl | sx_val E10 E11 E13]
        | lazymatch goal with |- aview _ _ _ (?o + ?k) = _ =>
            first [ let i := eval vm_compute in (Z.to_nat (k - 4)) in
                    replace (o + k) with (o + 4 + Z.of_nat i) by lia; rewrite (KM i ltac:(lia)); cbn [nth]; f_equal;
                    unfold u8; rewrite Z.mod_small by lia; reflexivity
                  | replace (o + k) with (o + 28 + (k - 28)) by lia;
                    eapply sx_chunk_zero4; [exact Ft | sx_inl | lia] ] end ]
| first [lia | (unfold u8; apply Z.mod_pos_bound; lia) | (cbn; lia)] ].
Ltac sx_pose_before HGb EX j :=
lazymatch eval vm_compute in (Nat.ltb j 32) with
| true => let Hr := fresh "Rx" in let He := fresh "Ex" in
  pose proof (proj2 (HGb j ltac:(cbn [length]; lia))) as Hr; cbn [nth] in Hr;
  pose proof (EX j ltac:(lia)) as He; cbn [nth Nat.add] in He;
  sx_pose_before HGb EX (S j)
| false => idtac end.
(* the range facts of the payload bytes, 0 <= bs[j] < 256 *)
Ltac sx_pose_bs HGp j nn :=
lazymatch eval vm_compute in (Nat.ltb j nn) with
| true => let Hr := fresh "Rb" in
  pose proof (proj2 (HGp j ltac:(cbn [length]; lia))) as Hr; cbn [nth] in Hr; sx_pose_bs HGp (S j) nn
| false => idtac end.
(* a list of length nn, as nn named elements *)
Ltac sx_destr l Hl j nn :=
lazymatch eval vm_compute in (Nat.ltb j nn) with
| true => let b := fresh "b" in let t := fresh "t" in
  destruct l as [|b t]; [cbn [length] in Hl; discriminate Hl|]; sx_destr t Hl (S j) nn
| false => destruct l as [|? ?]; [|cbn [length] in Hl; discriminate Hl] end.
(* n = 0: an undecided test of a3 against zero; drop the side n = 0 refutes *)
Ltac sx_n0br E13 :=
let Hz := fresh "Hz" in
cw_branch Hz;
[ first [ exfalso; rewrite ?branch_eq_U, ?branch_ne_U in Hz;
          lazymatch type of Hz with context [U ?Ex (SOff 13 ?c)] =>
            rewrite (U_atom_off Ex 13 0 c ltac:(sx_ew_peel; exact E13) ltac:(lia) ltac:(lia)) in Hz end;
          rewrite U_lit in Hz by lia; discriminate Hz
        | clear Hz ]
| first [ exfalso; rewrite ?branch_eq_U, ?branch_ne_U in Hz;
          lazymatch type of Hz with context [U ?Ex (SOff 13 ?c)] =>
            rewrite (U_atom_off Ex 13 0 c ltac:(sx_ew_peel; exact E13) ltac:(lia) ltac:(lia)) in Hz end;
          rewrite U_lit in Hz by lia; discriminate Hz
        | clear Hz ] ].

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).
(* the contract at one payload length nn *)
Definition sx_case (nn : nat) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(dev fn pl n out : Z) (bs before : list Z),
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_sysex ->
arg_zxA 8 (getr regs 10) dev -> arg_zxA 8 (getr regs 11) fn ->
getr regs 12 = w64 pl -> getr regs 13 = w64 n -> n = Z.of_nat (length bs) -> 0 <= n <= 24 ->
getr regs 14 = w64 out ->
(0 < n -> 0 < pl /\ garr8 tfibsegs (rd W memc) pl bs /\
          crd_ok tfibsegs W memc (spZ regs) T_sysex pl n /\ (pl + n <= out \/ out + 32 <= pl)) ->
cenc_out tfibsegs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_sysex out before ->
n = Z.of_nat nn ->
SRr tfibsegs W (cfg_at tfibsegs A_SYSEX regs memc mdc)
(cdc_post tfibsegs B MT STK sp0 FP ly S W0 mem0 md0 own k regs T_sysex (cenc_wr out) lyc Sc W memc mdc
  (cenc_res tfibsegs out before (sysex_spec dev fn bs))).
End w.

(* ======================= the walk at one payload length nn ======================= *)
(* The checks before any store (device, the empty-payload test, fn = 0x70, fn bit 7, n + 5 > 24), then for
   0 < nn <= 19 the payload loop (one bit-7 test per byte), the four header stores, __asan_memcpy
   (out + 4, pl, nn), the tail stores; for nn = 0 the header and tail stores without the loop or the call. *)
Ltac sx_go nn B TL LAWS AMEMCPY :=
let z := eval vm_compute in (Z.of_nat nn) in
let cls := eval vm_compute in (if Nat.eqb nn 0 then 0%nat else if Nat.leb nn 19 then 1%nat else 2%nat) in
unfold sx_case;
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs dev fn pl n out bs before
  HE Hdev Hfn H12 H13 Hn Hn24 H14 HPL HOUT Hnn;
rewrite Hnn in H13, HPL, Hn24, Hn; clear Hnn n; change (Z.of_nat nn) with z in H13, HPL, Hn24, Hn;
pose proof Hwx_tfa as Hwx; pose proof tfib_segs_low as Hsegs;
pose proof HE as HE0;
destruct HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive);
pose proof (conj HJ I) as HJ0;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _);
pose proof Hstk as (Hsp0al & _); clear Hstk;
assert (Hl : length bs = nn) by lia;
pose proof (sx_entry B TL LAWS nn STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs dev fn pl out bs before
  HE0 Hdev Hfn H12
  ltac:(let Hc := fresh "Hc" in intros Hc; first
    [ exfalso; lia
    | destruct (HPL ltac:(lia)) as (? & _ & (_ & _ & _ & _ & _ & Ham' & _) & _);
      unfold amem_range in Ham'; pose proof asan_consts as (_ & _ & C3' & C4' & C5'); rewrite C3', C4', C5' in Ham'; lia ])
  H13 Hl ltac:(lia) H14 HOUT ltac:(vm_compute; reflexivity)) as HS;
pose proof HOUT as ((Hq0 & Hq32 & Htd & Htw & Hra32 & Hhull & Ham & Hcw) & HGb & Hlenb);
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_sysex HE0
  ltac:(unfold T_sysex, ESTACK; lia)) as (Hceil & H47 & H46 & Hal & Hpres);
unfold T_sysex, ESTACK in Hceil, H46, Hpres;
pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc out 32 out (proj1 HJ) Htd ltac:(lia)) as [O1 O1'];
pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc out 32 (out + 31) (proj1 HJ) Htd ltac:(lia)) as [O2 O2'];
unfold kLowShadowBeg in O1', O2'; rewrite C3 in O1', O2';
destruct Hdev as [Hdv Hdev]; destruct Hfn as [Hfv Hfn];
remember (Ereg regs (cw_extra (bs ++ before))) as E eqn:HE;
assert (HAE : env_agree 32 (Ereg regs (cw_extra (bs ++ before))) E) by (subst E; apply env_agree_refl);
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs _ 1 1%bv eq_refl));
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs _ 2 2%bv eq_refl); reflexivity);
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite <- B2; symmetry; apply Z_to_bv_bv_unsigned);
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (cw_ew_reg regs _ 3 3%bv eq_refl));
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (cw_ew_reg regs _ 4 4%bv eq_refl));
assert (E10 : ew E 10 = Z_to_bv 64 dev) by (subst E; rewrite (cw_ew_reg regs _ 10 10%bv eq_refl); exact Hdev);
assert (E11 : ew E 11 = Z_to_bv 64 fn) by (subst E; rewrite (cw_ew_reg regs _ 11 11%bv eq_refl); exact Hfn);
assert (E12 : ew E 12 = Z_to_bv 64 pl) by (subst E; rewrite (cw_ew_reg regs _ 12 12%bv eq_refl); exact H12);
assert (E13 : ew E 13 = Z_to_bv 64 z) by (subst E; rewrite (cw_ew_reg regs _ 13 13%bv eq_refl); exact H13);
assert (E14 : ew E 14 = Z_to_bv 64 out) by (subst E; rewrite (cw_ew_reg regs _ 14 14%bv eq_refl); exact H14);
assert (B14 : bv_unsigned (ew E 14) = out) by (rewrite E14; apply unsigned_lit_small; lia);
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB);
assert (EX : forall j, (j < 32)%nat -> ew E (33 + nn + j) = Z_to_bv 64 (nth j before 0))
  by (intros j Hj; subst E; apply sx_ew_x; [exact Hl | exact Hj]);
assert (EXb : forall j, (j < length bs)%nat -> ew E (33 + j) = Z_to_bv 64 (nth j bs 0))
  by (intros j Hj; subst E; apply sx_ew_b; exact Hj);
clear HE;
assert (SHOK : sh_ok tfibsegs CW_Bx sx_SH E (mrestrict (w_H W) memc))
  by (apply Forall_cons; [|apply Forall_nil];
      apply (cw_shent_cdst B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_sysex E 14 out 32);
      [exact (proj1 HOUT) | exact E14 | exact E32 | lia]);
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ sx_zone (spZ regs) out nn a ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity);
pose proof Hwlo as Hwlo0; unfold T_sysex, ESTACK in Hwlo, Hcw;
unfold cfg_at; change (w64 A_SYSEX) with (Z_to_bv 64 A_SYSEX);
cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14);
let Hb1 := fresh "Hb1" in let Hb2 := fresh "Hb2" in let Hb3 := fresh "Hb3" in
cw_branch Hb1;
[ (* 0x848e4 bltz: device > 0x7f, return E_ARG *)
  rewrite sx_br_lt0, (sx_U_sll56 E 10 dev E10 ltac:(lia)) in Hb1; apply Z.leb_le in Hb1;
  pose proof (sx_spec_arg dev fn bs ltac:(lia)) as Hspec;
  cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14);
  sx_fail_leaf Hspec nn HJ0 Htd EX HGb Hlenb B14 B LAWS
| rewrite sx_br_lt0, (sx_U_sll56 E 10 dev E10 ltac:(lia)) in Hb1; apply Z.leb_gt in Hb1;
  cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14);
  (* n = 0: the empty-payload test (0x848f8) branches on (pl == 0) & 0, which the engine leaves open *)
  lazymatch cls with
  | 0%nat =>
    let Hz := fresh "Hz" in
    cw_branch Hz;
    [ exfalso; rewrite branch_ne_U, U_SAlu in Hz; cbn [zalu_raw] in Hz; rewrite !U_lit in Hz by lia;
      rewrite Z.land_0_r in Hz; vm_compute in Hz; discriminate Hz
    | clear Hz ];
    cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14)
  | _ => idtac end;
  cw_branch Hb2;
  [ (* 0x84900 bne s1,0x70 taken: fn <> 0x70 *)
    rewrite branch_ne_U, (U_atom E 11 fn E11), U_lit in Hb2 by lia; apply negb_true_iff, Z.eqb_neq in Hb2;
    cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14);
    cw_branch Hb3;
    [ (* 0x84914 bltz: fn > 0x7f, return E_RANGE *)
      rewrite sx_br_lt0, (sx_U_sll56 E 11 fn E11 ltac:(lia)) in Hb3; apply Z.leb_le in Hb3;
      pose proof (sx_spec_rfn dev fn bs ltac:(lia) Hb2 ltac:(lia)) as Hspec;
      cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14);
      sx_fail_leaf Hspec nn HJ0 Htd EX HGb Hlenb B14 B LAWS
    | rewrite sx_br_lt0, (sx_U_sll56 E 11 fn E11 ltac:(lia)) in Hb3; apply Z.leb_gt in Hb3;
      lazymatch cls with
      | 2%nat =>
        (* n + 5 > 24 (0x84920): return E_SPACE *)
        pose proof (sx_spec_space dev fn bs ltac:(lia) Hb2 ltac:(lia) ltac:(rewrite Hl; cbn; lia)) as Hspec;
        cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14);
        sx_fail_leaf Hspec nn HJ0 Htd EX HGb Hlenb B14 B LAWS
      | 0%nat =>
        (* n = 0: beqz a3 to the header stores (0x84984), then the tail (0x84a60) *)
        cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14);
        sx_n0br E13;
        cw_run_to ltac:(sx_awr Htw B14) 0x84a64; cw_keep ltac:(sx_kwr B14);
        (* 0x84a64: a0 = n + out, pinned to out's atom (offset 0) *)
        let HS4 := fresh "HS4" in
        lazymatch goal with HS : st_ok _ ?Ex ?ss (restrict ?Hh ?ms) |- _ =>
          let e := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in
          pose proof (st_ok_pin_rege Ex ss (restrict Hh ms) (10%bv : bv 5) (SOff 14 z) HS ltac:(intros X; discriminate X)
            ltac:(cbn [ms_regs restrict]; rewrite (st_ok_restrict_reg tfibsegs Hh Ex ss ms (10%bv : bv 5) HS);
                  change (sr_get (ss_regs ss) (10%bv : bv 5)) with e;
                  rewrite (sx_denot_off Ex 14 out z) by (first [sx_ew_peel; exact E14 | lia]);
                  rewrite (denot_add2 Ex 13 14 z out) by (first [sx_ew_peel; first [exact E13 | exact E14] | lia]);
                  unfold w64; f_equal; lia)) as HS4 end;
        clear HS; rename HS4 into HS; norm_ss HS;
        cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14);
        let KM := fresh "KM" in
        lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
          assert (KM : forall i : nat, (i < 0)%nat ->
            aview tfibsegs (w_H W) (ms_mem ms) (out + 4 + Z.of_nat i) = Some (nth i bs 0)) by (intros; lia) end;
        cw_leaf ltac:(sx_ktac (proj1 HJ0) Htd B LAWS) ltac:(idtac);
        unfold cenc_res;
        rewrite (sx_spec_ok dev fn bs ltac:(lia) Hb2 ltac:(lia) ltac:(rewrite Hl; cbn; lia)
          (sx_ex_none bs ltac:(intros i Hi; rewrite Hl in Hi; exfalso; lia)));
        cbn [fst snd]; split;
        [ lazymatch goal with |- ?lhs = _ => lazymatch goal with R : lhs = _ |- _ => rewrite R end end; reflexivity
        | let Fh := fresh "Fh" in let Ft := fresh "Ft" in
          lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
            let HR3 := fresh "HR" in let HR4 := fresh "HR" in sx_reg14 HS 0 HR3; sx_reg14 HS (Z.of_nat nn + 4) HR4;
            unfold region_ok in HR3, HR4;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict] in HR3, HR4;
            sx_ew_peel_in HR3; sx_ew_peel_in HR4; rewrite B14 in HR3, HR4;
            destruct HR3 as (_ & _ & _ & Fh); destruct HR4 as (_ & _ & _ & Ft) end;
          sx_destr bs Hl 0%nat nn;
          do 32 (destruct before as [|?x before]; [cbn [length] in Hlenb; discriminate Hlenb|]);
          destruct before as [|? ?]; [|cbn [length] in Hlenb; discriminate Hlenb];
          sx_pose_before HGb EX 0%nat;
          unfold cmd_outZ; cbn [map app firstn skipn length le4Z Z.of_nat Pos.of_succ_nat Pos.succ];
          unfold garr8; intros j Hj; cbn [length] in Hj;
          do 32 (destruct j as [|j]; [cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; sx_byte Fh Ft KM E10 E11 E13 |]);
          exfalso; cbn in Hj; lia ]
      | 1%nat =>
        cw_run_to ltac:(sx_awr Htw B14) 0x84938; cw_keep ltac:(sx_kwr B14);
        (* the payload: drop the two cells, add pl[0 .. nn) and its shadow entry *)
        destruct (HPL ltac:(lia)) as (Hpl0 & HGp & Hcrd & Hdj);
        pose proof Hcrd as (Hpq0 & Hpn & Hprd & Hpra & Hphull & Hpam & Hpcw);
        unfold coff_win, T_sysex, ESTACK in Hpcw; unfold amem_range in Hpam; rewrite C3, C4, C5 in Hpam;
        assert (B12 : bv_unsigned (ew E 12) = pl) by (rewrite E12; apply unsigned_lit_small; lia);
        sx_drop_gb;
        let KP := fresh "KP" in let KS := fresh "KS" in let HS3 := fresh "HS3" in
        lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
        assert (KP : forall x, pl <= x < pl + z -> aview tfibsegs (w_H W) (ms_mem ms) x = aview tfibsegs (w_H W) memc x)
          by (intros x Hx; apply KE; [lia | unfold sx_zone, coff_win in *; intros [Hz|[Hz|Hz]]; lia]);
        assert (KS : forall x, pl <= x < pl + z ->
          aview tfibsegs (w_H W) (ms_mem ms) (shadow_of_addr SHADOW_OFF x) = aview tfibsegs (w_H W) memc (shadow_of_addr SHADOW_OFF x))
          by (intros x Hx; unfold shadow_of_addr, SHADOW_OFF; pose proof (sx_div8 x ltac:(lia)) as [Q1 Q2];
              apply KE; [lia | unfold sx_zone, coff_win in *; intros [Hz|[Hz|Hz]]; lia]);
        pose proof (ast_ok_add_region tfibsegs E ss (restrict (w_H W) ms) (sx_pl nn) HS eq_refl) as HS3
        end;
        specialize (HS3 ltac:(unfold region_ok, sx_pl;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
          rewrite B12; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
          replace (map sx_pc (map Z.of_nat (seq 0 nn))) with (map sx_pc (map Z.of_nat (seq 0 (length bs))))
            by (rewrite Hl; reflexivity);
          apply sx_pl_chunks_ok; [exact EXb|];
          apply (sx_garr8_kept _ memc); [exact HGp | rewrite Hl; exact KP]));
        specialize (HS3 ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
            let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, sx_pl; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite B2, B12, B14; repeat split; lia));
        clear HS; rename HS3 into HS;
        let SHOK2 := fresh "SHOK2" in
        lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms), SH : sh_ok _ _ _ _ _ |- _ =>
        assert (SHOK2 : sh_ok tfibsegs CW_Bx (mkSHE 12 0 z :: sx_SH) E (mrestrict (w_H W) (ms_mem ms)))
          by (constructor; [apply (cw_shent_ra W (ms_mem ms) E 12 pl z);
            [apply (sx_ra_keep _ memc); [exact Hpra | exact KS] | unfold amem_range; rewrite C3, C4, C5; lia
            | lia | lia | lia | exact E12 | exact E32] | exact SH]); clear SH end;
        (* the payload loop 0x84948-0x84970: byte i is atom 33 + i; bit 7 set returns E_RANGE *)
        cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14);
        let rec loop i :=
          lazymatch eval vm_compute in (Nat.ltb i nn) with
          | true =>
            let a := eval vm_compute in (33 + i)%nat in
            let i1 := eval vm_compute in (Nat.succ i) in
            let Hp := fresh "Hp" in
            cw_branch Hp;
            [ sx_bit Hp a i EXb HGp;
              let Hspec := fresh "Hspec" in
              pose proof (sx_spec_rpl dev fn bs ltac:(lia) Hb2 ltac:(lia) ltac:(rewrite Hl; cbn; lia)
                (sx_ex_hit bs i ltac:(lia) Hp)) as Hspec;
              cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14);
              sx_fail_leaf Hspec nn HJ0 Htd EX HGb Hlenb B14 B LAWS
            | sx_bit Hp a i EXb HGp; cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14);
              sx_seal HAE E1 (33 + nn + 32)%nat; loop i1 ]
          | false => idtac
          end in
        loop 0%nat;
        (* the loop's exit test after the last byte: the engine leaves a3 - nn = 0 open *)
        let Hz := fresh "Hz" in
        cw_branch Hz;
        [ clear Hz
        | exfalso; rewrite branch_eq_U in Hz;
          lazymatch type of Hz with context [U ?Ex (SOff 13 ?c)] =>
            rewrite (U_atom_off Ex 13 z c ltac:(sx_ew_peel; exact E13) ltac:(lia) ltac:(lia)) in Hz end;
          rewrite U_lit in Hz by lia; discriminate Hz ];
        cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14);
        (* 0x84a5c: __asan_memcpy (out + 4, pl, nn), the stop at its entry *)
        let Ga0 := fresh "Ga0" in let Ga1 := fresh "Ga1" in let Ga2 := fresh "Ga2" in
        let Gsp := fresh "Gsp" in let Ggp := fresh "Ggp" in let Gtp := fresh "Gtp" in let U2 := fresh "U2" in
        sx_rg HS (10%bv : bv 5) Ga0; sx_rg HS (11%bv : bv 5) Ga1; sx_rg HS (12%bv : bv 5) Ga2;
        sx_rg HS (2%bv : bv 5) Gsp; sx_rg HS (3%bv : bv 5) Ggp; sx_rg HS (4%bv : bv 5) Gtp;
        lazymatch goal with HS : st_ok _ ?Ex ?ss (restrict _ ?ms) |- SRr _ _ (mkCfg ?ms ?md) _ =>
        assert (U2 : spZ (ms_regs ms) = spZ regs - 48)
          by (unfold spZ at 1; rewrite Gsp, (sx_denot_off Ex 2 (spZ regs) (-48)) by (first [sx_ew_peel; exact E2 | lia]);
              unfold w64; apply unsigned_lit_small; lia);
        eapply (cw_intrin_call B LAWS OCpy CA_MEMCPY AMEMCPY W Ex ss ms md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k
          (out + 4) pl z 543328 200 (ss_mem ss)); [exact HS | vm_compute; reflexivity | reflexivity | exact HJ | .. ];
        [ rewrite Ga0; apply sx_denot_off; [sx_ew_peel; exact E14 | lia | lia]
        | rewrite Ga1, sv_denot_SOff0; sx_ew_peel; exact E12
        | rewrite Ga2, sv_denot_SOff0; sx_ew_peel; exact E13
        | lia | lia | lia
        | rewrite U2; unfold ESTACK; lia | rewrite U2; lia | rewrite U2, Zminus_mod, Hal16; reflexivity | exact Hsp0al
        | rewrite Ggp, sv_denot_SOff0; sx_ew_peel; rewrite E3; exact Hgp
        | rewrite Gtp, sv_denot_SOff0; sx_ew_peel; rewrite E4; exact Htp
        | vm_compute; reflexivity | lia | vm_compute; reflexivity
        | (* dest out[4 .. 4 + nn): the caller lets the call write it, off the runtime's stack below sp *)
          intros a Ha; split; [exact (proj1 (Htw a ltac:(lia))) | rewrite U2; unfold coff_win, ESTACK in *; lia]
        | unfold amem_range in *; lia
        | apply (sx_ra_keep _ memc); [apply (range_addressable_sub _ _ out 32); [exact Hra32 | lia | lia] |];
          intros x Hx; unfold shadow_of_addr, SHADOW_OFF; pose proof (sx_div8 x ltac:(lia)) as [Q1 Q2];
          apply KE; [lia | unfold sx_zone, coff_win, amem_range in *; intros [Hz|[Hz|Hz]]; lia]
        | intros _; apply (sx_hull_keep _ memc _ out 32); [exact (Hhull ltac:(lia)) | lia | lia | lia | lia |];
          intros s Hs; pose proof (sx_hull_band out 32 s ltac:(lia) ltac:(lia) ltac:(unfold amem_range in Ham; lia) Hs);
          apply KE; [unfold SHADOW_OFF in *; lia | unfold sx_zone, coff_win, SHADOW_OFF in *; intros [Hz|[Hz|Hz]]; lia]
        | (* source pl[0 .. nn): readable, off the window, usable, its hull visible, all kept since the entry *)
          split; [lia|]; split; [lia|]; split;
          [ intros a Ha; split; [rewrite KE; [exact (Hprd a Ha) | lia | unfold sx_zone, coff_win in *; intros [Hz|[Hz|Hz]]; lia]
                                | rewrite U2; unfold ESTACK; lia] |];
          split; [lia|]; split; [unfold amem_range; rewrite C3, C4, C5; lia|]; split;
          [ apply (sx_ra_keep _ memc); [exact Hpra|]; intros x Hx; unfold shadow_of_addr, SHADOW_OFF;
            pose proof (sx_div8 x ltac:(lia)) as [Q1 Q2]; apply KE; [lia | unfold sx_zone, coff_win in *; intros [Hz|[Hz|Hz]]; lia]
          | intros _; apply (sx_hull_keep _ memc _ pl z pl z); [exact (Hphull ltac:(lia)) | lia | lia | lia | lia |];
            intros s Hs; pose proof (sx_hull_band pl z s ltac:(lia) ltac:(lia) ltac:(lia) Hs);
            apply KE; [unfold SHADOW_OFF in *; lia | unfold sx_zone, coff_win, SHADOW_OFF in *; intros [Hz|[Hz|Hz]]; lia] ]
        | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | apply submem_refl
        | lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end;
          repeat apply Forall_cons; try apply Forall_nil;
          (split; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
                   cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; sx_ew_peel_in Ha;
                   rewrite ?B12, ?B2, ?B14 in Ha; split; [lia | rewrite U2; unfold coff_win, ESTACK in *; lia]
                  | cbn; lia])
        | idtac ] end;
        intros regs2 mem2 md2 HJ2 HP2 Ha02 Hcp Hfr Hpres2 Hsm HS2;
        clear HS SHOK2; rename HS2 into HS; cw_norm_model;
        (* what the call kept since the entry (K0, hidden from the runs), out[4 .. 4 + nn) the payload (Hcp'),
           and a fresh kept fact for the runs after the call, over the walk's own windows *)
        assert (K0 : (forall a, 0 <= a < 2 ^ 64 -> ~ sx_zone2 (spZ regs) out a ->
          aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memc a) /\ True)
          by (split; [|exact I]; intros a Ha Hz; unfold sx_zone2 in Hz;
              rewrite Hfr; [| exact Ha | lia | rewrite U2; unfold ESTACK; lia];
              apply KE; [exact Ha | unfold sx_zone; lia]);
        assert (Hcp' : forall i, 0 <= i < z -> aview tfibsegs (w_H W) mem2 (out + 4 + i) = Some (nth (Z.to_nat i) bs 0))
          by (intros i Hi; rewrite Hcp by lia; rewrite KE; [| lia | unfold sx_zone, coff_win in *; intros [Hz|[Hz|Hz]]; lia];
              destruct (HGp (Z.to_nat i) ltac:(lia)) as [Hv Hr]; rewrite Z2Nat.id in Hv by lia;
              exact (aview_of_val_mem1 tfibsegs (w_H W) memc (pl + i) _ Hv Hr));
        clear KE Hfr;
        assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ sx_zone (spZ regs) out nn a ->
          aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem2 a) by (intros; reflexivity);
        let HAE' := fresh "HAE" in
        lazymatch type of HS with st_ok _ ?En _ _ =>
        assert (HAE' : env_agree 32 (Ereg regs (cw_extra (bs ++ before))) En) by (env_agree_chain HAE);
        assert (SHOK : sh_ok tfibsegs CW_Bx (mkSHE 12 0 z :: sx_SH) En (mrestrict (w_H W) mem2))
        by (constructor; [|constructor; [|constructor]];
          [ apply (cw_shent_ra W mem2 En 12 pl z); [| unfold amem_range; rewrite C3, C4, C5; lia | lia | lia | lia
              | sx_ew_peel; exact E12 | sx_ew_peel; exact E32];
            apply (sx_ra_keep _ memc); [exact Hpra|]; intros x Hx; unfold shadow_of_addr, SHADOW_OFF;
            pose proof (sx_div8 x ltac:(lia)) as [Q1 Q2]; apply (proj1 K0); [lia | unfold sx_zone2, coff_win in *; lia]
          | apply (cw_shent_ra W mem2 En 14 out 32); [| exact Ham | lia | lia | lia
              | sx_ew_peel; exact E14 | sx_ew_peel; exact E32];
            apply (sx_ra_keep _ memc); [exact Hra32|]; intros x Hx; unfold shadow_of_addr, SHADOW_OFF;
            pose proof (sx_div8 x ltac:(lia)) as [Q1 Q2]; apply (proj1 K0); [lia | unfold sx_zone2, coff_win, amem_range in *; lia] ])
        end;
        cw_run_to ltac:(sx_awr Htw B14) 0x84a64; cw_keep ltac:(sx_kwr B14);
        (* 0x84a64: a0 = n + out, pinned to the offset nn of out's atom so the store of f7 lands in out's tail region *)
        let HS4 := fresh "HS4" in
        lazymatch goal with HS : st_ok _ ?Ex ?ss (restrict ?Hh ?ms) |- _ =>
          let e := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in
          pose proof (st_ok_pin_rege Ex ss (restrict Hh ms) (10%bv : bv 5) (SOff 14 z) HS ltac:(intros X; discriminate X)
            ltac:(cbn [ms_regs restrict]; rewrite (st_ok_restrict_reg tfibsegs Hh Ex ss ms (10%bv : bv 5) HS);
                  change (sr_get (ss_regs ss) (10%bv : bv 5)) with e;
                  rewrite (sx_denot_off Ex 14 out z) by (first [sx_ew_peel; exact E14 | lia]);
                  rewrite (denot_add2 Ex 13 14 z out) by (first [sx_ew_peel; first [exact E13 | exact E14] | lia]);
                  unfold w64; f_equal; lia)) as HS4 end;
        clear HS; rename HS4 into HS; norm_ss HS;
        cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14);
        let KF := fresh "KF" in let KM := fresh "KM" in
        lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
        assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ sx_zone2 (spZ regs) out a ->
          aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) memc a)
          by (intros a Ha Hz; rewrite KE; [apply (proj1 K0); [exact Ha | exact Hz] | exact Ha
              | unfold sx_zone, sx_zone2 in *; intros Hq; apply Hz; lia]);
        assert (KM : forall i : nat, (i < nn)%nat ->
          aview tfibsegs (w_H W) (ms_mem ms) (out + 4 + Z.of_nat i) = Some (nth i bs 0))
          by (intros i Hi; rewrite KE; [rewrite Hcp' by lia; rewrite Nat2Z.id; reflexivity | lia
              | unfold sx_zone, coff_win in *; intros [Hz|[Hz|Hz]]; lia])
        end;
        clear KE;
        cw_leaf ltac:(idtac; cw_kept (proj1 HJ0) KF
          ltac:(let a := fresh "a" in let Ha := fresh "Ha" in let Hi := fresh "Hi" in intros a Ha Hi; unfold cenc_wr in Ha;
                exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ 32 a (proj1 (proj1 HJ0)) Htd Ha Hi))
          ltac:(let a := fresh "a" in let Hz := fresh "Hz" in intros a Hz; unfold sx_zone2, cenc_wr, T_sysex, ESTACK in *;
                destruct Hz as [Hz|Hz]; [left; lia | right; lia])) ltac:(idtac);
        (* the result: a0 = 0, out = cmd_outZ before (Some cmd) *)
        unfold cenc_res;
        rewrite (sx_spec_ok dev fn bs ltac:(lia) Hb2 ltac:(lia) ltac:(rewrite Hl; cbn; lia)
          (sx_ex_none bs ltac:(intros i Hi; rewrite Hl in Hi; repeat (destruct i as [|i]; [assumption|]); exfalso; lia)));
        cbn [fst snd]; split;
        [ lazymatch goal with |- ?lhs = _ => lazymatch goal with R : lhs = _ |- _ => rewrite R end end; reflexivity
        | let Fh := fresh "Fh" in let Ft := fresh "Ft" in
          lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
            let HR3 := fresh "HR" in let HR4 := fresh "HR" in sx_reg14 HS 0 HR3; sx_reg14 HS (Z.of_nat nn + 4) HR4;
            unfold region_ok in HR3, HR4;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict] in HR3, HR4;
            sx_ew_peel_in HR3; sx_ew_peel_in HR4; rewrite B14 in HR3, HR4;
            destruct HR3 as (_ & _ & _ & Fh); destruct HR4 as (_ & _ & _ & Ft) end;
          (* the 32 bytes of out, each from its chunk, the copy, or the zero word *)
          sx_destr bs Hl 0%nat nn;
          sx_pose_bs HGp 0%nat nn;
          do 32 (destruct before as [|?x before]; [cbn [length] in Hlenb; discriminate Hlenb|]);
          destruct before as [|? ?]; [|cbn [length] in Hlenb; discriminate Hlenb];
          sx_pose_before HGb EX 0%nat;
          unfold cmd_outZ; cbn [map app firstn skipn length le4Z Z.of_nat Pos.of_succ_nat Pos.succ];
          unfold garr8; intros j Hj; cbn [length] in Hj;
          do 32 (destruct j as [|j]; [cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; sx_byte Fh Ft KM E10 E11 E13 |]);
          exfalso; cbn in Hj; lia ]
      end ]
  | (* fn = 0x70: return E_REFUSED *)
    rewrite branch_ne_U, (U_atom E 11 fn E11), U_lit in Hb2 by lia; apply negb_false_iff, Z.eqb_eq in Hb2; subst fn;
    pose proof (sx_spec_refused dev bs ltac:(lia)) as Hspec;
    cw_run ltac:(sx_awr Htw B14); cw_keep ltac:(sx_kwr B14);
    sx_fail_leaf Hspec nn HJ0 Htd EX HGb Hlenb B14 B LAWS ] ].
