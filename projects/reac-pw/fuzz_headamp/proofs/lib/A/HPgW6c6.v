(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the block lemma
   w6c_case6_stmt of lib/A/HPgW6cBase.v, case 6 of ent_build's `switch (kind % 10)` (pod.h:340-349) inside
   LLVMFuzzerTestOneInput (0x80bc0), from the case entry 0x81dc8 to the join J 0x8237c. Proves no function (kind:
   segment lemma).

   THE CODE (registers as in lib/A/HPgW6cEng.v: s1 = R, s7 = SHADOW_OFF, s8 = cur, s9 = |r|, a4 = cur - 1):
     0x81dc8  beqz s9 -> 0x82074                      no byte left
     0x81dcc .. 0x81ddc  the check of s8 (slow 0x82740), with `ld s4,0xd0(s1)` inside
     0x81de0 .. 0x81e04  a2 := t & 3; a0 := 0x210e0 + 4 (t & 3); the check of a0 (4 bytes, slow 0x8274c)
     0x81e08  a1 := 2; beq a2,a1 -> 0x821fc (a3 := 4)  else 0x81e10 a3 := 8
     0x82200  a1 := [R+0x118] - 2; s8 := a4 + 2; lw a0,0(a0) (= t6[t & 3]); a2 := (t & 3 = 3 ? 0 : a3)
     0x82074  (no byte left) a1 := 0; a2 := 8; a0 := 5; ld s4,0xd0(s1)
     0x82220  a3 := [R+0x110]; e.type := a0; e.size := a2; bltu a2,a1 -> 0x82234  else a2 := a1
     0x82234  s9 := s8 + a2; a1 := a1 - a2; [R+0x118] := a1; a0 := [R+0xe0]; a1 := s8; jal __asan_memcpy
   THE PROOF is cut at the calls of the engine (lib/Reusable/YCbq.v aj_run_to_tok, the token engine that follows a
   check's slow block itself and leaves one `range_addressable` obligation per check):
     w6c6_leaf   the state at the callee's entry 0x51d0c -> the join, by HPgW6cTail's w6c_jpost_trans and
                 w6c_tail_cpy: e's 104 bytes from its two header words, the copied slice from the input bytes.
     w6c6_nil    r = []: one run 0x81dc8 -> 0x51d0c over the regions RS (R's cells) and RE (e's header).
     w6c6_cons   r = t :: r1: one run 0x81dc8 -> 0x81e08 over RS and RI 1 (the kind byte's successor), then the
                 split on j = t mod 4 (a table load needs a literal address), the index and the table address
                 pinned to literals, RI dropped and RT (the 16 bytes of t at 0x210e0) and RE added, one run to
                 the `bltu a2,a1` 0x8222c, srr_branch_tok there, and one run per arm to 0x51d0c.
   The input and a .rodata table are never two regions of one state: the contract does not place the input outside
   the image, so the engine could not show them disjoint. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSteps HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW6cTail HPgW6cEng HPgW6cBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the pc after the two checks of the case, where the table index is split *)
Definition W6C6_J4 : Z := 0x81e08.

(* ===================================== the model of case 6 ===================================== *)
Definition w6c6_ent (r : list byte) : ent * list byte :=
  let '(t, r1) := Cursor.fuzz_u8 r in
  let ty := nth (Z.to_nat (t mod 4)) Tables.t6 0 in
  let sz := if ty =? POD_NONE then 0 else if ty =? POD_ID then 4 else 8 in
  let '(p, r2) := Cursor.fuzz_take (Z.to_nat sz) r1 in
  (Ent ty sz (p ++ zeros (Z.to_nat sz - length p)), r2).

Lemma w6c6_is_ent : forall r, w6c_ent 6 r = w6c6_ent r.
Proof.
intros r. unfold w6c_ent, ent_build, w6c6_ent.
replace (Cursor.fuzz_u8 (Z_to_bv 8 6 :: r)) with (6, r) by (vm_compute; reflexivity).
cbv beta iota zeta. replace (Z.to_nat (6 mod 10)) with 6%nat by (vm_compute; reflexivity).
reflexivity.
Qed.

Lemma w6c6_ent_nil : w6c_ent 6 [] = (Ent 5 8 (zeros 8), []).
Proof. rewrite w6c6_is_ent. vm_compute. reflexivity. Qed.

Lemma w6c6_ent_cons : forall b r1 j ty sz, bv_unsigned b mod 4 = j ->
nth (Z.to_nat j) Tables.t6 0 = ty -> (if ty =? POD_NONE then 0 else if ty =? POD_ID then 4 else 8) = sz ->
w6c_ent 6 (b :: r1) =
(Ent ty sz (firstn (Z.to_nat sz) r1 ++ zeros (Z.to_nat sz - length (firstn (Z.to_nat sz) r1))),
 skipn (Z.to_nat sz) r1).
Proof.
intros b r1 j ty sz Hj Hty Hsz. rewrite w6c6_is_ent. unfold w6c6_ent, Cursor.fuzz_take.
cbn [Cursor.fuzz_u8]. cbv beta iota zeta. rewrite Hj, Hty, Hsz. reflexivity.
Qed.

(* the four types and sizes of the table *)
Lemma w6c6_tysz : forall j, 0 <= j < 4 ->
(j = 0 /\ nth (Z.to_nat j) Tables.t6 0 = 5) \/ (j = 1 /\ nth (Z.to_nat j) Tables.t6 0 = 7) \/
(j = 2 /\ nth (Z.to_nat j) Tables.t6 0 = 3) \/ (j = 3 /\ nth (Z.to_nat j) Tables.t6 0 = 1).
Proof.
intros j Hj. assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
destruct E as [-> | [-> | [-> | ->]]]; [left | right; left | right; right; left | right; right; right];
  split; reflexivity.
Qed.

(* firstn at the two cut points of `bltu a2,a1` *)
Lemma w6c6_firstn_all : forall (l : list byte) (n m : nat), (length l <= n)%nat -> (n <= m)%nat ->
firstn n l = firstn m l.
Proof. intros l n m H1 H2. rewrite !firstn_all2 by lia. reflexivity. Qed.

(* ===================================== the two written windows ===================================== *)
Definition w6c6_win (R F a : Z) : Prop := (R + 0x118 <= a < R + 0x120) \/ (F + 0xf0 <= a < F + 0xf8).

Lemma w6c6_denot : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma w6c6_u64 : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof. intros x. apply u64_range. Qed.
Lemma w6c6_Uadd0 : forall E n1 n2, 0 <= bv_unsigned (ew E n1) + bv_unsigned (ew E n2) < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = bv_unsigned (ew E n1) + bv_unsigned (ew E n2).
Proof.
intros E n1 n2 H. pose proof (w6c6_u64 (ew E n1)). pose proof (w6c6_u64 (ew E n2)).
rewrite U_SAlu, !U_SOff, !(zcanon_id (_ + 0)) by (unfold M64; lia).
cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* the slice the case copies: min (sz, |r1|) bytes *)
Lemma w6c6_bs : forall (r1 : list byte) sz, 0 <= sz ->
firstn (Z.to_nat (Z.min sz (Z.of_nat (length r1)))) r1 = firstn (Z.to_nat sz) r1.
Proof.
intros r1 sz H. destruct (Z_le_gt_dec sz (Z.of_nat (length r1))) as [X|X].
- f_equal. lia.
- rewrite Z.min_r by lia. rewrite !firstn_all2 by lia. reflexivity.
Qed.
Lemma w6c6_bslen : forall (r1 : list byte) n, 0 <= n <= Z.of_nat (length r1) ->
Z.of_nat (length (firstn (Z.to_nat n) r1)) = n.
Proof. intros r1 n H. rewrite length_firstn. lia. Qed.

(* ===================================== tactic kit ===================================== *)
Ltac w6c6_norm H := cbn [ss_pc ss_regs ss_mem ss_resv ss_facts app] in H.
Ltac w6c6_sr := lazymatch goal with |- context [sr_get ?sr ?r0] =>
  let e := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with e end.
Ltac w6c6_kio := first [ eassumption
  | (eapply same_io_trans; [| apply same_io_wvb]); w6c6_kio ].
Ltac w6c6_atoms := repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H end.
Ltac w6c6_uc :=
  rewrite ?w6c6_Uadd0 by (w6c6_atoms; lia);
  rewrite ?U_SAlu; rewrite ?U_SOff; rewrite ?U_SLit; cbn [zalu_raw]; w6c6_atoms;
  rewrite ?zcanon_id by (unfold M64; lia); try lia;
  try (unfold W6C_RCPY, W6C_T6, SHADOW_OFF; lia).
Ltac w6c6_rv0 Wv HSx rr :=
  lazymatch type of HSx with st_ok _ _ _ (restrict _ ?msx) =>
    rewrite (st_ok_restrict_reg rsegs (w_H Wv) _ _ msx (rr : bv 5) HSx) end;
  w6c6_sr; unfold w64; apply w6c6_denot.
Ltac w6c6_rv Wv HSx rr := w6c6_rv0 Wv HSx rr; w6c6_uc.
Ltac w6c6_notin := first [ vm_compute; discriminate
  | cbv [In]; intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X ].
Ltac w6c6_chunk := cbv [In];
  first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
        | right; right; right; left; reflexivity | right; right; right; right; left; reflexivity].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* a run whose regions write only inside the two windows keeps every byte outside them *)
Lemma w6c6_kept : forall (Hb : word -> bool) E rs m m' (memc : word -> option byte) (Wn : Z -> Prop),
(forall a, in_wrange E rs a -> Wn a) -> frame_of E rs m m' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wn a -> aview rsegs Hb m a = aview rsegs Hb memc a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Wn a -> aview rsegs Hb m' a = aview rsegs Hb memc a.
Proof.
intros Hb E rs m m' memc Wn Hw HF K a Ha Hn. rewrite <- (K a Ha Hn).
apply (aview_eq_of rsegs). unfold mrestrict. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros Hin. rewrite unsigned_lit_small in Hin by lia. exact (Hn (Hw a Hin)).
Qed.
(* the shadow hull of an application range lies in the shadow band *)
Lemma w6c6_hull_keep : forall (Hb : word -> bool) m m' x n,
(forall s, 0x7fff8000 - 8 <= s < 0x10007fff8000 + 8 -> aview rsegs Hb m' s = aview rsegs Hb m s) ->
0 <= x -> x + n <= 0x800000000000 - 1 -> 0 < n ->
shadow_hull_vis (aview rsegs Hb m) x n -> shadow_hull_vis (aview rsegs Hb m') x n.
Proof.
intros Hb m m' x n K H0 H1 Hn Hh.
apply (hm_hull_kept rsegs Hb m Hb m' x n Hh). intros s Hs Hne.
pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as B1.
pose proof (hm_shadow_band (x + n - 1) ltac:(unfold kHighMemEnd; lia)) as B2.
unfold kLowMemEnd, kHighMemBeg, shadow_addr, shadow_of_addr, SHADOW_OFF in *.
pose proof (Z.div_mod (2147450880 + x / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (2147450880 + x / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)).
rewrite K; [exact Hne | lia].
Qed.


(* a read-only byte of the image lies below the shadow band *)
Lemma w6c6_rom_low : forall a, in_rom rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a Ha. apply w6c_segs_low. destruct Ha as (sg & Hsg & _ & Hr). exists sg. split; assumption.
Qed.

(* the atom facts of the entry state with an input byte (closed bounds: N in [2, 2^47], a4 <= 2^47 - 3) *)
Lemma w6c6_facts2 : forall E R F cur NN t,
bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F -> bv_unsigned (ew E 23) = 0x7fff8000 ->
bv_unsigned (ew E 14) = cur - 1 -> bv_unsigned (ew E 33) = NN -> bv_unsigned (ew E 34) = t ->
bv_unsigned (ew E 36) = 0 ->
0x10007fff8000 <= R <= 2 ^ 47 -> R mod 16 = 0 -> 4096 <= F <= 2 ^ 47 - 1024 -> F mod 32 = 0 ->
1 <= cur <= 2 ^ 47 - 2 -> 2 <= NN <= 2 ^ 47 -> 0 <= t <= 255 ->
facts_ok E (mkFacts (w6c_facts 2 (2 ^ 47) (2 ^ 47 - 3)) [] []).
Proof.
intros E R F cur NN t U9 U32 U23 U14 U33 U34 U36 BR HR BF HF Bc BN Bt.
unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok]. split; [|split; exact I].
apply (w6c_facts_ok E R F (cur - 1) NN t 0 2 (2 ^ 47) (2 ^ 47 - 3) U9 U32 U23 U14 U33 U34 U36 BR HR BF HF);
  lia.
Qed.

(* e's two header words are zero before the case writes them *)
Lemma w6c6_zero4 : forall (Hb : word -> bool) mem F, hm_bytes rsegs Hb mem (F + 0xf0) (zeros 104) ->
val_mem rsegs (mrestrict Hb mem) (F + 0xf0) 4 0 /\ val_mem rsegs (mrestrict Hb mem) (F + 0xf4) 4 0.
Proof.
intros Hb mem F Hz. split; apply (hm_val_of_bytes rsegs Hb mem).
- replace (Z_to_le_bytes 4 0) with (hm_slice (zeros 104) 0 4) by (vm_compute; reflexivity).
  replace (F + 0xf0) with (F + 0xf0 + Z.of_nat 0) by lia.
  apply (hm_bytes_slice rsegs Hb mem (F + 0xf0) (zeros 104) 0 4 Hz). rewrite length_zeros. lia.
- replace (Z_to_le_bytes 4 0) with (hm_slice (zeros 104) 4 4) by (vm_compute; reflexivity).
  replace (F + 0xf4) with (F + 0xf0 + Z.of_nat 4) by lia.
  apply (hm_bytes_slice rsegs Hb mem (F + 0xf0) (zeros 104) 4 4 Hz). rewrite length_zeros. lia.
Qed.

Section c. Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6C_CPY.

(* ===================================== the leaf: 0x51d0c -> J ===================================== *)
Lemma w6c6_leaf : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa r
mem1 md1 regs1 ty sz o (bs : list byte) ed cur' nl',
w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in_D B W memc regs R F cur sa r ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k -> same_io mdc md1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ w6c6_win R F a -> aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
(forall rr, In rr w6c_keep -> getr regs1 rr = getr regs rr) ->
getr regs1 1 = w64 W6C_RCPY -> getr regs1 10 = w64 (F + 0xf8) ->
getr regs1 11 = w64 (cur + o) -> getr regs1 12 = w64 (Z.of_nat (length bs)) ->
getr regs1 20 = w64 sa -> getr regs1 25 = w64 (cur + o + Z.of_nat (length bs)) ->
val_mem rsegs (mrestrict (w_H W) mem1) (F + 0xf0) 4 ty ->
val_mem rsegs (mrestrict (w_H W) mem1) (F + 0xf4) 4 sz ->
val_mem rsegs (mrestrict (w_H W) mem1) (R + 0x118) 8 (Z.of_nat (length r) - o - Z.of_nat (length bs)) ->
hm_bytes rsegs (w_H W) memc (cur + o) bs ->
0 <= o -> o + Z.of_nat (length bs) <= Z.of_nat (length r) -> 0 <= sz <= 96 ->
(length bs <= Z.to_nat sz)%nat ->
ed = Ent ty sz (bs ++ zeros (Z.to_nat sz - length bs)) ->
cur' = cur + o + Z.of_nat (length bs) -> nl' = Z.of_nat (length r) - o - Z.of_nat (length bs) ->
SRr rsegs W (mkCfg (mkst regs1 (Z_to_bv 64 W6C_CPY) mem1 (seg_rom rsegs)) md1)
(w6c_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F ed cur' nl' sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa r mem1 md1 regs1 ty sz o bs
ed cur' nl' Hctx Hin HJ1 Hio1 K1 Hk1 G1 G10 G11 G12 G20 G25 Vty Vsz V8 Hbs Ho Hon Hsz Hns Hed Hcur Hnl.
subst ed cur' nl'.
pose proof Hctx as (HJ & HG & Hrom).
destruct (w6c_frame B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ HG)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HFe & HFapp & HF32).
destruct Hin as (D2 & D3 & D4 & D9 & D23 & D24 & D14 & D25 & Dmul & Dsa & Dsa64 & Dc0 & Df0 & Df8 & Dz & Dfsh
  & Dbytes & Dra & Dhull & Damr & Dcur1 & Dcurhi & Ddis & DT6 & DT8 & Dtbl).
pose proof alloc_ceiling_value as (Hac1 & _). pose proof alloc_ceiling_lt as Hac2.
pose proof (Nat2Z.is_nonneg (length bs)) as Hbs0.
assert (HFband : F + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= F).
{ unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. destruct HFapp as [_ [X|[X Y]]]; [left | right]; lia. }
unfold T_SEG_STK, ASTACK in HRk, HSTK, HRc. unfold kHighMemBeg in HRk.
assert (Hband : forall x, 0x7fff8000 - 8 <= x < 0x10007fff8000 + 8 -> ~ w6c6_win R F x).
{ unfold w6c6_win. intros x Hx. lia. }
assert (Hin64 : forall x, cur <= x < cur + Z.of_nat (length r) -> 0 <= x < 0x800000000000).
{ intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Damr. lia. }
assert (Hsh : forall x, cur <= x < cur + Z.of_nat (length r) ->
  aview rsegs (w_H W) mem1 (shadow_of_addr SHADOW_OFF x) = aview rsegs (w_H W) memc (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; apply Hin64; lia)) as Hb.
  unfold kLowMemEnd, kHighMemBeg in Hb. apply K1; [lia | apply Hband; lia]. }
assert (Hbytes1 : hm_bytes rsegs (w_H W) mem1 (cur + o) bs).
{ apply (hm_bytes_kept rsegs (w_H W) memc); [exact Hbs|].
  intros x Hx. apply K1; [pose proof (Hin64 x ltac:(lia)); lia|].
  destruct (Ddis x ltac:(lia)) as (Dd1 & Dd2). unfold T_SEG_STK, ASTACK in Dd1. unfold w6c6_win. lia. }
eapply SRr_mono.
{ eapply (w6c_tail_cpy B AMEMCPY STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem1 md1 regs1 R F pos
    ty sz (cur + o) bs (cur + o + Z.of_nat (length bs)) (Z.of_nat (length r) - o - Z.of_nat (length bs)) sa
    HJ1 HG G1).
  - rewrite (Hk1 2%bv ltac:(cbv [w6c_keep In]; tauto)). exact D2.
  - rewrite (Hk1 3%bv ltac:(cbv [w6c_keep In]; tauto)). exact D3.
  - rewrite (Hk1 4%bv ltac:(cbv [w6c_keep In]; tauto)). exact D4.
  - exact G10.
  - exact G11.
  - exact G12.
  - exact G20.
  - exact G25.
  - exact Hns.
  - lia.
  - (* e's 104 bytes, from the two header words *)
    apply (w6c_e_hdr (w_H W) memc mem1 F ty sz Dz Vty Vsz).
    intros x Hx. apply K1; [lia|]. unfold w6c6_win. lia.
  - exact Hbytes1.
  - apply (hm_ra_kept rsegs (w_H W) memc).
    + apply (ra_sub _ _ cur (Z.of_nat (length r))); [exact Dra | lia | lia].
    + intros x Hx. apply Hsh. lia.
  - intros Hpos. apply (hm_hull_kept rsegs (w_H W) memc).
    + apply (hm_hull_sub _ cur (Z.of_nat (length r))); [apply Dhull; lia | lia | lia | lia].
    + intros s Hs Hne.
      assert (B1 : 0x7fff8000 <= shadow_addr (cur + o) < 0x10007fff8000).
      { pose proof (hm_shadow_band (cur + o) ltac:(unfold kHighMemEnd; apply Hin64; lia)) as Hb.
        unfold kLowMemEnd, kHighMemBeg, shadow_addr, shadow_of_addr in *. lia. }
      assert (B2 : 0x7fff8000 <= shadow_addr (cur + o + Z.of_nat (length bs) - 1) < 0x10007fff8000).
      { pose proof (hm_shadow_band (cur + o + Z.of_nat (length bs) - 1)
          ltac:(unfold kHighMemEnd; apply Hin64; lia)) as Hb.
        unfold kLowMemEnd, kHighMemBeg, shadow_addr, shadow_of_addr in *. lia. }
      pose proof (Z.div_mod (shadow_addr (cur + o)) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (shadow_addr (cur + o)) 8 ltac:(lia)).
      pose proof (Z.div_mod (shadow_addr (cur + o + Z.of_nat (length bs) - 1)) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (shadow_addr (cur + o + Z.of_nat (length bs) - 1)) 8 ltac:(lia)).
      rewrite K1; [exact Hne | lia | apply Hband; lia].
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Damr |- *. lia.
  - lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Damr. lia.
  - intros a Ha. destruct (Ddis a ltac:(lia)) as (Dd1 & Dd2).
    unfold T_SEG_STK, ASTACK, ESTACK in *. split; lia.
  - (* the frame's shadow bytes *)
    unfold hd_fsh. intros i Hi. change (Z.of_nat (length hs_PJ)) with 80 in Hi.
    assert (Hsf : 0x7fff8000 <= shadow_addr F /\ shadow_addr F + 80 < 0x10007fff8000 + 8).
    { unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
      assert (F / 8 <= 2 ^ 44 - 128) by (apply Z.div_le_upper_bound; lia). lia. }
    rewrite K1; [exact (Dfsh i Hi) | lia | apply Hband; lia].
  - rewrite Z.mod_small by (pose proof (Nat2Z.is_nonneg (length r)); lia). exact V8. }
cbv beta. intros W2 c2 _ HQ.
eapply (w6c_jpost_trans B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs mem1 md1 regs1 R F);
  [exact Hk1 | exact Hio1 | | exact HQ].
intros a Ha X1 X2 X3. apply K1; [exact Ha | unfold w6c6_win; unfold ESTACK in *; lia].
Qed.

(* ===================================== r = []: 0x81dc8 -> 0x51d0c ===================================== *)
Lemma w6c6_nil : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa ed cur' nl',
w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in_D B W memc regs R F cur sa [] ->
ed = Ent 5 8 (zeros 8) -> cur' = cur -> nl' = 0 ->
SRr rsegs W (cfg_at rsegs W6C_D6 regs memc mdc)
(w6c_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F ed cur' nl' sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa ed cur' nl'
Hctx Hin Hed Hcur Hnl.
pose proof Hctx as (HJ & HG & Hrom).
destruct (w6c_frame B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ HG)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HFe & HFapp & HF32).
destruct (w6c_present B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos Hctx) as (HpF & HpR).
pose proof Hin as (D2 & D3 & D4 & D9 & D23 & D24 & D14 & D25 & Dmul & Dsa & Dsa64 & Dc0 & Df0 & Df8 & Dz & Dfsh
  & Dbytes & Dra & Dhull & Damr & Dcur1 & Dcurhi & Ddis & DT6 & DT8 & Dtbl).
pose proof alloc_ceiling_value as (Hac1 & _). pose proof alloc_ceiling_lt as Hac2.
unfold T_SEG_STK, ASTACK in HRk, HSTK, HRc. unfold kHighMemBeg in HRk.
cbn [length] in D25, Df8, Damr, Dra, Dhull, Dcurhi, Ddis.
destruct (w6c6_zero4 (w_H W) memc F Dz) as (Vz0 & Vz4).
(* the entry state *)
assert (E9w : ew (Ereg regs (w6c_extra F 1 0 sa 0)) 9 = w64 R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact D9).
assert (E14w : ew (Ereg regs (w6c_extra F 1 0 sa 0)) 14 = w64 (cur - 1))
  by (rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact D14).
assert (E23w : ew (Ereg regs (w6c_extra F 1 0 sa 0)) 23 = w64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact D23).
assert (E24w : ew (Ereg regs (w6c_extra F 1 0 sa 0)) 24 = w64 cur)
  by (rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact D24).
pose proof (w6c_e32 regs F 1 0 sa 0) as E32w. pose proof (w6c_e33 regs F 1 0 sa 0) as E33w.
pose proof (w6c_e34 regs F 1 0 sa 0) as E34w. pose proof (w6c_e35 regs F 1 0 sa 0) as E35w.
pose proof (w6c_e36 regs F 1 0 sa 0) as E36w.
assert (E9u : bv_unsigned (ew (Ereg regs (w6c_extra F 1 0 sa 0)) 9) = R)
  by (rewrite E9w; unfold w64; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew (Ereg regs (w6c_extra F 1 0 sa 0)) 32) = F)
  by (rewrite E32w; unfold w64; apply unsigned_lit_small; lia).
assert (E14u : bv_unsigned (ew (Ereg regs (w6c_extra F 1 0 sa 0)) 14) = cur - 1)
  by (rewrite E14w; unfold w64; apply unsigned_lit_small; lia).
assert (E23u : bv_unsigned (ew (Ereg regs (w6c_extra F 1 0 sa 0)) 23) = 0x7fff8000)
  by (rewrite E23w; unfold w64, SHADOW_OFF; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew (Ereg regs (w6c_extra F 1 0 sa 0)) 33) = 1)
  by (rewrite E33w; unfold w64; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew (Ereg regs (w6c_extra F 1 0 sa 0)) 34) = 0)
  by (rewrite E34w; unfold w64; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew (Ereg regs (w6c_extra F 1 0 sa 0)) 36) = 0)
  by (rewrite E36w; unfold w64; apply unsigned_lit_small; lia).
assert (HS0 : st_ok rsegs (Ereg regs (w6c_extra F 1 0 sa 0))
  (mkSS W6C_D6 sr_atoms [w6c_RS; w6c_RE] None (mkFacts (w6c_facts 1 1 (2 ^ 47 - 2)) [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6C_D6) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (w6c_RS_ok _ W memc R F 1 sa E9u E32w E33w E35w); try lia.
      * intros o Ho. apply HpR. lia.
      * exact Dmul.
      * exact Dsa.
      * exact Dc0.
      * exact Df0.
      * exact Df8.
    + apply (w6c_RE_ok _ W memc F E32u); [lia | lia | | exact Vz0 | exact Vz4].
      intros o Ho. apply HpF. lia.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, w6c_RS, w6c_RE.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9u, E32u.
    split; [split; [lia | exact I] | split; exact I].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok]. split; [|split; exact I].
    apply (w6c_facts_ok _ R F (cur - 1) 1 0 0); try assumption; try lia. }
pose proof (w6c_pin _ _ _ (24%bv : bv 5) (SOff 14 1) HS0 eq_refl
  ltac:(cbn [ss_regs]; replace (sr_get sr_atoms (24%bv : bv 5)) with (SOff 24 0) by (vm_compute; reflexivity);
        cbn [sv_denot]; rewrite E14w, E24w; unfold w64;
        rewrite !unsigned_lit_small by lia; f_equal; lia)) as HS1.
pose proof (st_ok_pin_lit rsegs _ _ _ (25%bv : bv 5) 0 HS1 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite D25; reflexivity)) as HS.
clear HS0 HS1.
assert (SHOK : sh_ok rsegs w6c_Bx w6c_SH (Ereg regs (w6c_extra F 1 0 sa 0)) (mrestrict (w_H W) memc)).
{ apply (w6c_shok _ W memc F).
  - unfold w6c_Bx. apply (U_atom _ 23 SHADOW_OFF E23w). unfold SHADOW_OFF. lia.
  - apply (U_atom _ 32 F E32w). lia.
  - replace (F + 0xf0) with (F + HM_E + 0) by (unfold HM_E; lia).
    apply (hm_A_ra_e rsegs _ _ F false false false false false 0 8);
      [rewrite <- hs_PJ_sh; exact Dfsh | apply w6c_F8; exact HF32 | lia | lia].
  - exact HFapp. }
pose proof w6c_wx as Hwx. pose proof w6c_segs_low as Hsl. pose proof (AR_laws_ok rsegs B) as HL.
unfold cfg_at. change (w64 W6C_D6) with (Z_to_bv 64 W6C_D6).
aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_CPY.
{ eapply awr_ok_cons_stack_off with (n := 9%nat) (d := R - sp0);
    [reflexivity | cbn [YP09.r_base]; rewrite E9u; lia
    | cbn [w6c_RS YP09.r_wlo]; lia | cbn [w6c_RS YP09.r_whi]; lia |].
  eapply awr_ok_cons_gen with (k := 32%nat) (b := F); [reflexivity | exact E32u | | apply awr_ok_nil].
  cbn [w6c_RE YP09.r_wlo YP09.r_whi]. intros a Ha. apply HFw. lia. }
(* at 0x51d0c *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ w6c6_win R F a ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ lazymatch goal with HFx : frame_of ?Ev ?rsx memc (ms_mem ?msx) |- _ =>
    refine (w6c6_kept (w_H W) Ev rsx memc (ms_mem msx) memc (w6c6_win R F) _ HFx (fun a _ _ => eq_refl)) end.
  intros x (rg & Hin0 & Hr). cbn [In] in Hin0.
  repeat (destruct Hin0 as [<- | Hin0];
    [cbn [w6c_RS w6c_RE YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
     rewrite ?E9u, ?E32u in Hr; unfold w6c6_win; lia |]).
  destruct Hin0. }
lazymatch type of HS with st_ok _ ?Ev ?ssf _ =>
  let r0 := eval vm_compute in (nth_error (ss_mem ssf) 0%nat) in
  lazymatch r0 with Some ?rg =>
    assert (HRG0 : region_ok rsegs Ev (ms_mem (restrict (w_H W) ms)) rg)
      by (apply (w6c_region_nth Ev ssf _ 0%nat rg HS); vm_compute; reflexivity) end;
  let r1 := eval vm_compute in (nth_error (ss_mem ssf) 1%nat) in
  lazymatch r1 with Some ?rg =>
    assert (HRG1 : region_ok rsegs Ev (ms_mem (restrict (w_H W) ms)) rg)
      by (apply (w6c_region_nth Ev ssf _ 1%nat rg HS); vm_compute; reflexivity) end
end.
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl).
eapply (w6c6_leaf STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa []
  _ _ _ 5 8 0 []).
- exact Hctx.
- exact Hin.
- eassumption.
- first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; apply same_io_refl].
- exact K1.
- intros rr Hrr. eapply (regs_kept_of_st_ok rsegs _ _ ms regs (w6c_extra F 1 0 sa 0) (w_H W)
    [1; 10; 11; 12; 13; 20; 24; 25]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity) rr).
  + cbv [w6c_keep In] in Hrr. repeat (destruct Hrr as [<- | Hrr]; [vm_compute; discriminate|]). destruct Hrr.
  + cbv [w6c_keep In] in Hrr.
    repeat (destruct Hrr as [<- | Hrr]; [cbv [In]; intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]).
    destruct Hrr.
- rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (1%bv : bv 5) HS).
  lazymatch goal with |- context [sr_get ?sr ?r0] =>
    let e := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with e end.
  reflexivity.
- rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (10%bv : bv 5) HS).
  lazymatch goal with |- context [sr_get ?sr ?r0] =>
    let e := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with e end.
  cbn [sv_denot]. rewrite E32u. unfold w64. f_equal; lia.
- rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (11%bv : bv 5) HS).
  lazymatch goal with |- context [sr_get ?sr ?r0] =>
    let e := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with e end.
  cbn [sv_denot]. rewrite E14u. unfold w64. f_equal; lia.
- rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (12%bv : bv 5) HS).
  lazymatch goal with |- context [sr_get ?sr ?r0] =>
    let e := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with e end.
  reflexivity.
- rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (20%bv : bv 5) HS).
  lazymatch goal with |- context [sr_get ?sr ?r0] =>
    let e := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with e end.
  cbn [sv_denot]. rewrite E35w. unfold w64. rewrite unsigned_lit_small by lia. f_equal; lia.
- rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (25%bv : bv 5) HS).
  lazymatch goal with |- context [sr_get ?sr ?r0] =>
    let e := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with e end.
  cbn [sv_denot]. rewrite E14u. unfold w64. cbn [length]. f_equal; lia.
- apply (w6c_field _ _ 32%nat F _ _ _ _ _ 0xf0 4 (SLit 5) 5 HRG1 E32u);
    [cbv [In]; tauto | reflexivity | cbn; lia | cbn; lia].
- apply (w6c_field _ _ 32%nat F _ _ _ _ _ 0xf4 4 (SLit 8) 8 HRG1 E32u);
    [cbv [In]; tauto | reflexivity | cbn; lia | cbn; lia].
- apply (w6c_field _ _ 9%nat R _ _ _ _ _ 0x118 8 (SLit 0) 0 HRG0 E9u);
    [cbv [In]; tauto | reflexivity | cbn; lia | cbn; lia].
- unfold hm_bytes. cbn [map]. apply garr8_nil.
- lia.
- cbn [length]. lia.
- lia.
- cbn [length]. lia.
- rewrite Hed. reflexivity.
- rewrite Hcur. cbn [length]. lia.
- rewrite Hnl. cbn [length]. lia.
Qed.
(* =============================== r <> []: 0x81e08 -> 0x51d0c =============================== *)
(* the table index is split here: a table load needs a literal address *)
Lemma w6c6_mid : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa b r1
mem1 md1 regs1 j ty sz ed cur' nl',
w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in_D B W memc regs R F cur sa (b :: r1) ->
w6c_in_D B W mem1 regs1 R F cur sa (b :: r1) ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k -> same_io mdc md1 ->
rom_view rsegs W mem1 ->
(forall o, 0 <= o < 1024 -> apresent (w_H W) mem1 (F + o)) ->
(forall a, R <= a < R + 0x1e0 -> apresent (w_H W) mem1 a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ w6c6_win R F a -> aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
(forall rr, In rr w6c_keep -> getr regs1 rr = getr regs rr) ->
getr regs1 10 = w64 (W6C_T6 + 4 * j) -> getr regs1 12 = w64 j -> getr regs1 20 = w64 sa ->
bv_unsigned b mod 4 = j -> nth (Z.to_nat j) Tables.t6 0 = ty ->
(if ty =? POD_NONE then 0 else if ty =? POD_ID then 4 else 8) = sz ->
ed = fst (w6c_ent 6 (b :: r1)) ->
cur' = cur + Z.of_nat (length (b :: r1) - length (snd (w6c_ent 6 (b :: r1)))) ->
nl' = Z.of_nat (length (snd (w6c_ent 6 (b :: r1)))) ->
SRr rsegs W (cfg_at rsegs W6C6_J4 regs1 mem1 md1)
(w6c_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F ed cur' nl' sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa b r1 mem1 md1 regs1 j ty sz
ed cur' nl' Hctx Hin Hin1 HJ1 Hio1 ROM1 HpF1 HpR1 K1 Hk1 G10 G12 G20 Hj Hty Hsz Hed Hcur Hnl.
pose proof Hctx as (HJc & HGc & Hromc).
destruct (w6c_frame B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJc HGc)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
pose proof HGc as (HR16 & HSTK & HRS & HRk & Hown & HFe & HFapp & HF32).
pose proof Hin1 as (Q2 & Q3 & Q4 & Q9 & Q23 & Q24 & Q14 & Q25 & Qmul & Qsa & Qsa64 & Qc0 & Qf0 & Qf8 & Qz & Qfsh
  & Qbytes & Qra & Qhull & Qamr & Qcur1 & Qcurhi & Qdis & QT6 & QT8 & Qtbl).
pose proof Hin as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & Dbytes & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof alloc_ceiling_value as (Hac1 & _). pose proof alloc_ceiling_lt as Hac2.
unfold T_SEG_STK, ASTACK in HRk, HSTK, HRc. unfold kHighMemBeg in HRk.
pose proof (Cursor.byte_range b) as Htb.
destruct (w6c6_zero4 (w_H W) mem1 F Qz) as (Vz0 & Vz4).
assert (HTF : F + 1024 <= 0x210e0 \/ 0x21110 <= F).
{ destruct (Z_le_gt_dec (F + 1024) 0x210e0) as [X|X]; [left; exact X|].
  destruct (Z_le_gt_dec 0x21110 F) as [Y|Y]; [right; exact Y|].
  exfalso. apply (Qtbl (Z.max F 0x210e0)); unfold W6C_T6, W6C_T8; lia. }
assert (HNl : Z.of_nat (length (b :: r1)) = Z.of_nat (length r1) + 1)
  by (cbn [length]; rewrite Nat2Z.inj_succ; lia).
assert (HLb : (0 <= Z.of_nat (length r1))%Z) by lia.
rewrite (w6c6_ent_cons b r1 j ty sz Hj Hty Hsz) in Hed, Hcur, Hnl.
cbn [fst snd] in Hed, Hcur, Hnl.
assert (Hjv : j = 0 \/ j = 1 \/ j = 2 \/ j = 3)
  by (rewrite <- Hj; pose proof (Z.mod_pos_bound (bv_unsigned b) 4 ltac:(lia)); lia).
remember (Z.of_nat (length (b :: r1)) + 1) as NN eqn:HNN.
destruct Hjv as [-> | [-> | [-> | ->]]].
all: vm_compute in Hty; subst ty.
all: vm_compute in Hsz; subst sz.
(* ---- the entry state at 0x81e08 ---- *)
all: assert (E9w : ew (Ereg regs1 (w6c_extra F NN (bv_unsigned b) sa 0)) 9 = w64 R)
       by (rewrite (ew_Ereg_nat regs1 _ 9 9%bv eq_refl); exact Q9).
all: assert (E14w : ew (Ereg regs1 (w6c_extra F NN (bv_unsigned b) sa 0)) 14 = w64 (cur - 1))
       by (rewrite (ew_Ereg_nat regs1 _ 14 14%bv eq_refl); exact Q14).
all: assert (E23w : ew (Ereg regs1 (w6c_extra F NN (bv_unsigned b) sa 0)) 23 = w64 SHADOW_OFF)
       by (rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl); exact Q23).
all: pose proof (w6c_e32 regs1 F NN (bv_unsigned b) sa 0) as E32w.
all: pose proof (w6c_e33 regs1 F NN (bv_unsigned b) sa 0) as E33w.
all: pose proof (w6c_e34 regs1 F NN (bv_unsigned b) sa 0) as E34w.
all: pose proof (w6c_e35 regs1 F NN (bv_unsigned b) sa 0) as E35w.
all: pose proof (w6c_e36 regs1 F NN (bv_unsigned b) sa 0) as E36w.
all: assert (E9u : bv_unsigned (ew (Ereg regs1 (w6c_extra F NN (bv_unsigned b) sa 0)) 9) = R)
       by (rewrite E9w; unfold w64; apply unsigned_lit_small; lia).
all: assert (E32u : bv_unsigned (ew (Ereg regs1 (w6c_extra F NN (bv_unsigned b) sa 0)) 32) = F)
       by (rewrite E32w; unfold w64; apply unsigned_lit_small; lia).
all: assert (E14u : bv_unsigned (ew (Ereg regs1 (w6c_extra F NN (bv_unsigned b) sa 0)) 14) = cur - 1)
       by (rewrite E14w; unfold w64; apply unsigned_lit_small; lia).
all: assert (E23u : bv_unsigned (ew (Ereg regs1 (w6c_extra F NN (bv_unsigned b) sa 0)) 23) = 0x7fff8000)
       by (rewrite E23w; unfold w64, SHADOW_OFF; apply unsigned_lit_small; lia).
all: assert (E33u : bv_unsigned (ew (Ereg regs1 (w6c_extra F NN (bv_unsigned b) sa 0)) 33) = NN)
       by (rewrite E33w; unfold w64; apply unsigned_lit_small; lia).
all: assert (E34u : bv_unsigned (ew (Ereg regs1 (w6c_extra F NN (bv_unsigned b) sa 0)) 34) = bv_unsigned b)
       by (rewrite E34w; unfold w64; apply unsigned_lit_small; lia).
all: assert (E35u : bv_unsigned (ew (Ereg regs1 (w6c_extra F NN (bv_unsigned b) sa 0)) 35) = sa)
       by (rewrite E35w; unfold w64; apply unsigned_lit_small; lia).
all: assert (E36u : bv_unsigned (ew (Ereg regs1 (w6c_extra F NN (bv_unsigned b) sa 0)) 36) = 0)
       by (rewrite E36w; unfold w64; apply unsigned_lit_small; lia).
all: assert (E20u : bv_unsigned (ew (Ereg regs1 (w6c_extra F NN (bv_unsigned b) sa 0)) 20) = sa)
       by (rewrite (ew_Ereg_nat regs1 _ 20 20%bv eq_refl), G20; unfold w64;
           apply unsigned_lit_small; lia).
all: assert (HS0 : st_ok rsegs (Ereg regs1 (w6c_extra F NN (bv_unsigned b) sa 0))
       (mkSS W6C6_J4 sr_atoms [w6c_RT W6C_T6; w6c_RE; w6c_RS] None
         (mkFacts (w6c_facts 2 (2 ^ 47) (2 ^ 47 - 3)) [] []))
       (restrict (w_H W) (mkst regs1 (Z_to_bv 64 W6C6_J4) mem1 (seg_rom rsegs))))
     by (rewrite restrict_mkst_fx; apply (entry_st_ok_full rsegs);
         [ apply regs_ok_Ereg
         | vm_compute; reflexivity
         | constructor;
           [ apply (w6c_RT_ok _ W mem1 W6C_T6 ROM1 w6c_rom_tbl6); unfold W6C_T6; lia
           | constructor;
             [ apply (w6c_RE_ok _ W mem1 F E32u); [lia | lia | intros o Ho; apply HpF1; lia | exact Vz0 | exact Vz4]
             | constructor;
               [ apply (w6c_RS_ok _ W mem1 R F NN sa E9u E32w E33w E35w); try lia;
                 [ intros o Ho; apply HpR1; lia | exact Qmul | exact Qsa | exact Qc0 | exact Qf0 | exact Qf8 ]
               | constructor ]]]
         | cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint, w6c_RT, w6c_RE, w6c_RS;
           cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E9u, E32u;
           unfold W6C_T6; repeat split; try exact I; lia
         | unfold facts_ok; cbn [f_atoms f_conds f_alias conds_ok alias_ok]; split; [|split; exact I];
           apply (w6c_facts_ok _ R F (cur - 1) NN (bv_unsigned b) 0); try assumption; try lia ]).
(* ---- the index and the table address pinned to literals ---- *)
all: pose proof (st_ok_pin_lit rsegs _ _ _ (12%bv : bv 5) _ HS0 eq_refl
       ltac:(cbn [ms_regs restrict mkst]; exact G12)) as HS1.
all: w6c6_norm HS1.
all: pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) _ HS1 eq_refl
       ltac:(cbn [ms_regs restrict mkst]; exact G10)) as HS.
all: w6c6_norm HS.
all: clear HS0 HS1.
all: assert (SHOK : sh_ok rsegs w6c_Bx w6c_SH (Ereg regs1 (w6c_extra F NN (bv_unsigned b) sa 0))
       (mrestrict (w_H W) mem1))
     by (apply (w6c_shok _ W mem1 F);
         [ unfold w6c_Bx; apply (U_atom _ 23 SHADOW_OFF E23w); unfold SHADOW_OFF; lia
         | apply (U_atom _ 32 F E32w); lia
         | replace (F + 0xf0) with (F + HM_E + 0) by (unfold HM_E; lia);
           apply (hm_A_ra_e rsegs _ _ F false false false false false 0 8);
             [rewrite <- hs_PJ_sh; exact Qfsh | apply w6c_F8; exact HF32 | lia | lia]
         | exact HFapp ]).
all: pose proof w6c_wx as Hwx.
all: pose proof w6c_segs_low as Hsl.
all: pose proof (AR_laws_ok rsegs B) as HL.
all: unfold cfg_at; change (w64 W6C6_J4) with (Z_to_bv 64 W6C6_J4).
(* ---- 0x81e08 .. the `bltu a2,a1` of 0x8222c ---- *)
all: (aj_run_to_tok w6c_tbl_ok HS HJ1 SHOK w6c_Bspan W6C_CPY;
      [ apply awr_ok_cons_ro; [cbn [w6c_RT YP09.r_wlo YP09.r_whi]; lia|];
        eapply awr_ok_cons_gen with (k := 32%nat) (b := F);
          [reflexivity | exact E32u
          | cbn [w6c_RE YP09.r_wlo YP09.r_whi]; intros aa Haa; apply HFw; lia |];
        eapply awr_ok_cons_stack_off with (n := 9%nat) (d := R - sp0);
          [reflexivity | rewrite E9u; lia
          | cbn [w6c_RS YP09.r_wlo]; lia | cbn [w6c_RS YP09.r_whi]; lia | apply awr_ok_nil]
      | idtac ]).
(* the bytes kept, and the atoms of the new env *)
all: lazymatch goal with HFx : frame_of ?Ev ?rsx ?m0 (ms_mem ?msx) |- _ =>
       assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ w6c6_win R F a ->
                 aview rsegs (w_H W) (ms_mem msx) a = aview rsegs (w_H W) memc a)
         by (refine (w6c6_kept (w_H W) Ev rsx m0 (ms_mem msx) memc (w6c6_win R F) _ HFx K1);
             intros xx (rg & Hin0 & Hr); cbn [In] in Hin0;
             repeat (destruct Hin0 as [<- | Hin0];
               [cbn [w6c_RT w6c_RE w6c_RS YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
                rewrite ?E9u, ?E32u in Hr; unfold w6c6_win; lia|]);
             destruct Hin0) end.
all: lazymatch type of HS with st_ok _ ?Ev _ _ =>
       assert (PA : bv_unsigned (ew Ev 9) = R /\ bv_unsigned (ew Ev 32) = F /\
                    bv_unsigned (ew Ev 14) = cur - 1 /\ bv_unsigned (ew Ev 33) = NN /\
                    bv_unsigned (ew Ev 35) = sa /\ ew Ev 33 = w64 NN)
         by (repeat split; rewrite ?ew_ewset_other by lia; assumption) end.
all: destruct PA as (PA9 & PA32 & PA14 & PA33 & PA35 & PAw33).
(* ---- the branch the engine cannot decide ---- *)
all: srr_branch_tok w6c_tbl_ok HS SHOK w6c_Bspan.
all: rewrite branch_ltu_U, (U_atom_off _ 33 NN (-2) PAw33 ltac:(lia) ltac:(lia)), U_SLit,
       zcanon_id in Hc by (unfold M64; lia).
all: first [apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc].
(* ---- the rest of the block, the call set up ---- *)
all: (aj_run_to_tok w6c_tbl_ok HS HJ1 SHOK w6c_Bspan W6C_CPY;
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
        eapply awr_ok_cons_gen with (k := 32%nat) (b := F);
          [reflexivity | exact PA32
          | cbn [YP09.r_wlo YP09.r_whi]; intros aa Haa; apply HFw; lia |];
        eapply awr_ok_cons_stack_off with (n := 9%nat) (d := R - sp0);
          [reflexivity | rewrite PA9; lia
          | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]
      | idtac ]).
all: lazymatch goal with HFx : frame_of ?Ev ?rsx (ms_mem ?msb) (ms_mem ?msx) |- _ =>
       assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ w6c6_win R F a ->
                 aview rsegs (w_H W) (ms_mem msx) a = aview rsegs (w_H W) memc a)
         by (refine (w6c6_kept (w_H W) Ev rsx (ms_mem msb) (ms_mem msx) memc (w6c6_win R F) _ HFx KB);
             intros xx (rg & Hin0 & Hr); cbn [In] in Hin0;
             repeat (destruct Hin0 as [<- | Hin0];
               [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
                rewrite ?PA9, ?PA32 in Hr; unfold w6c6_win; lia|]);
             destruct Hin0) end.
all: lazymatch type of HS with st_ok _ ?Ev _ _ =>
       assert (PB : bv_unsigned (ew Ev 9) = R /\ bv_unsigned (ew Ev 32) = F /\
                    bv_unsigned (ew Ev 14) = cur - 1 /\ bv_unsigned (ew Ev 33) = NN /\
                    bv_unsigned (ew Ev 35) = sa)
         by (repeat split; rewrite ?ew_ewset_other by lia; assumption) end.
all: destruct PB as (PB9 & PB32 & PB14 & PB33 & PB35).
(* the two regions the leaf reads back *)
all: lazymatch type of HS with st_ok _ ?Ev ?ssf _ =>
       lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
         let re1 := eval vm_compute in (nth_error (ss_mem ssf) 1%nat) in
         lazymatch re1 with Some ?rg =>
           assert (HRGE : region_ok rsegs Ev (mrestrict (w_H W) (ms_mem msx)) rg)
             by (apply (w6c_region_nth Ev ssf _ 1%nat rg HS); vm_compute; reflexivity) end;
         let re2 := eval vm_compute in (nth_error (ss_mem ssf) 2%nat) in
         lazymatch re2 with Some ?rg =>
           assert (HRGS : region_ok rsegs Ev (mrestrict (w_H W) (ms_mem msx)) rg)
             by (apply (w6c_region_nth Ev ssf _ 2%nat rg HS); vm_compute; reflexivity) end
       end end.
all: lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
       rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msx HS eq_refl) end.
all: lazymatch type of Hed with _ = Ent ?tyv ?szv _ =>
  eapply (w6c6_leaf STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa (b :: r1)
    _ _ _ tyv szv 1 (firstn (Z.to_nat (Z.min szv (Z.of_nat (length r1)))) r1)) end;
  [ exact Hctx
  | exact Hin
  | exact HJ1
  | w6c6_kio
  | exact KC
  | intros rr Hrr;
    erewrite (regs_kept_of_st_ok rsegs _ _ _ regs1 (w6c_extra F NN (bv_unsigned b) sa 0) (w_H W)
      [1; 10; 11; 12; 13; 20; 24; 25]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity) rr);
    [ apply Hk1; exact Hrr
    | cbv [w6c_keep In] in Hrr; repeat (destruct Hrr as [<- | Hrr]; [vm_compute; discriminate|]); destruct Hrr
    | cbv [w6c_keep In] in Hrr;
      repeat (destruct Hrr as [<- | Hrr];
        [cbv [In]; intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]); destruct Hrr ]
  | w6c6_rv W HS ((1%bv) : bv 5)
  | w6c6_rv W HS ((10%bv) : bv 5)
  | w6c6_rv W HS ((11%bv) : bv 5)
  | w6c6_rv W HS ((12%bv) : bv 5); rewrite length_firstn; lia
  | w6c6_rv W HS ((20%bv) : bv 5)
  | w6c6_rv W HS ((25%bv) : bv 5); rewrite length_firstn; lia
  | eapply (w6c_field _ _ 32%nat F _ _ _ _ _ 0xf0 4 _ _ HRGE PB32);
      [ w6c6_chunk | apply w6c6_denot; w6c6_uc | cbn; lia | cbn; lia ]
  | eapply (w6c_field _ _ 32%nat F _ _ _ _ _ 0xf4 4 _ _ HRGE PB32);
      [ w6c6_chunk | apply w6c6_denot; w6c6_uc | cbn; lia | cbn; lia ]
  | eapply (w6c_field _ _ 9%nat R _ _ _ _ _ 0x118 8 _ _ HRGS PB9);
      [ w6c6_chunk
      | apply w6c6_denot; w6c6_uc; rewrite length_firstn; lia
      | cbn; rewrite length_firstn; lia | cbn; lia ]
  | replace (cur + 1) with (cur + Z.of_nat 1) by lia;
    lazymatch goal with |- hm_bytes _ _ _ _ (firstn ?nn _) =>
      pose proof (hm_bytes_slice rsegs (w_H W) memc cur (b :: r1) 1 nn Dbytes) as HH end;
    unfold hm_slice in HH; cbn [skipn] in HH; apply HH; cbn [length]; lia
  | lia
  | rewrite length_firstn; cbn [length]; lia
  | lia
  | rewrite length_firstn; lia
  | rewrite w6c6_bs by lia; exact Hed
  | rewrite Hcur, length_skipn, length_firstn; cbn [length]; lia
  | rewrite Hnl, length_skipn, length_firstn; cbn [length]; lia ].
Qed.
(* =============================== r <> []: 0x81dc8 -> 0x81e08 =============================== *)
Lemma w6c6_cons : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa b r1 ed cur' nl',
w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in_D B W memc regs R F cur sa (b :: r1) ->
ed = fst (w6c_ent 6 (b :: r1)) ->
cur' = cur + Z.of_nat (length (b :: r1) - length (snd (w6c_ent 6 (b :: r1)))) ->
nl' = Z.of_nat (length (snd (w6c_ent 6 (b :: r1)))) ->
SRr rsegs W (cfg_at rsegs W6C_D6 regs memc mdc)
(w6c_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F ed cur' nl' sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa b r1 ed cur' nl'
Hctx Hin Hed Hcur Hnl.
(* the model's terms go to the goal, out of reach of lia *)
subst ed cur' nl'.
pose proof Hctx as (HJc & HGc & Hromc).
destruct (w6c_frame B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJc HGc)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
pose proof HGc as (HR16 & HSTK & HRS & HRk & Hown & HFe & HFapp & HF32).
destruct (w6c_present B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos Hctx) as (HpF & HpR).
pose proof Hin as (D2 & D3 & D4 & D9 & D23 & D24 & D14 & D25 & Dmul & Dsa & Dsa64 & Dc0 & Df0 & Df8 & Dz & Dfsh
  & Dbytes & Dra & Dhull & Damr & Dcur1 & Dcurhi & Ddis & DT6 & DT8 & Dtbl).
pose proof alloc_ceiling_value as (Hac1 & _). pose proof alloc_ceiling_lt as Hac2.
unfold T_SEG_STK, ASTACK in HRk, HSTK, HRc. unfold kHighMemBeg in HRk.
pose proof (Cursor.byte_range b) as Htb.
assert (HNl : Z.of_nat (length (b :: r1)) = Z.of_nat (length r1) + 1)
  by (cbn [length]; rewrite Nat2Z.inj_succ; lia).
assert (Damr' : 0 <= cur /\ cur + Z.of_nat (length (b :: r1)) <= 0x800000000000 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Damr; lia).
assert (Dv1 : val_mem rsegs (mrestrict (w_H W) memc) (cur - 1 + 1) 1 (bv_unsigned b)).
{ unfold hm_bytes in Dbytes. destruct (Dbytes 0%nat ltac:(cbn [length map]; lia)) as (Hv & _).
  cbn [nth map] in Hv. replace (cur - 1 + 1) with (cur + Z.of_nat 0) by lia. exact Hv. }
remember (Z.of_nat (length (b :: r1)) + 1) as NN eqn:HNN.
(* the entry state: R's cells and the kind byte's successor *)
assert (E9w : ew (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0)) 9 = w64 R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact D9).
assert (E14w : ew (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0)) 14 = w64 (cur - 1))
  by (rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact D14).
assert (E23w : ew (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0)) 23 = w64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact D23).
assert (E24w : ew (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0)) 24 = w64 cur)
  by (rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact D24).
assert (E25w : ew (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0)) 25 = w64 (Z.of_nat (length (b :: r1))))
  by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact D25).
pose proof (w6c_e32 regs F NN (bv_unsigned b) sa 0) as E32w.
pose proof (w6c_e33 regs F NN (bv_unsigned b) sa 0) as E33w.
pose proof (w6c_e34 regs F NN (bv_unsigned b) sa 0) as E34w.
pose proof (w6c_e35 regs F NN (bv_unsigned b) sa 0) as E35w.
pose proof (w6c_e36 regs F NN (bv_unsigned b) sa 0) as E36w.
assert (E9u : bv_unsigned (ew (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0)) 9) = R)
  by (rewrite E9w; unfold w64; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0)) 32) = F)
  by (rewrite E32w; unfold w64; apply unsigned_lit_small; lia).
assert (E14u : bv_unsigned (ew (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0)) 14) = cur - 1)
  by (rewrite E14w; unfold w64; apply unsigned_lit_small; lia).
assert (E23u : bv_unsigned (ew (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0)) 23) = 0x7fff8000)
  by (rewrite E23w; unfold w64, SHADOW_OFF; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0)) 33) = NN)
  by (rewrite E33w; unfold w64; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0)) 34) = bv_unsigned b)
  by (rewrite E34w; unfold w64; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0)) 35) = sa)
  by (rewrite E35w; unfold w64; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0)) 36) = 0)
  by (rewrite E36w; unfold w64; apply unsigned_lit_small; lia).
assert (BR : 0x10007fff8000 <= R <= 2 ^ 47) by lia.
assert (BF : 4096 <= F <= 2 ^ 47 - 1024) by lia.
assert (Bc : 1 <= cur <= 2 ^ 47 - 2) by lia.
assert (BN : 2 <= NN <= 2 ^ 47) by lia.
assert (Bt : 0 <= bv_unsigned b <= 255) by lia.
assert (HS0 : st_ok rsegs (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0))
  (mkSS W6C_D6 sr_atoms [w6c_RS; w6c_RI 1] None (mkFacts (w6c_facts 2 (2 ^ 47) (2 ^ 47 - 3)) [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6C_D6) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (w6c_RS_ok _ W memc R F NN sa E9u E32w E33w E35w); try lia.
      * intros o Ho. apply HpR. lia.
      * exact Dmul.
      * exact Dsa.
      * exact Dc0.
      * exact Df0.
      * exact Df8.
    + apply (w6c_RI_ok _ W memc (cur - 1) (bv_unsigned b) 0 1 E14u E34w E36w); try lia.
      intros _. exact Dv1.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, w6c_RS, w6c_RI.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9u, E14u.
    destruct (Ddis cur ltac:(cbn [length]; lia)) as (Dd1 & Dd2).
    unfold T_SEG_STK, ASTACK in Dd1. split; [split; [lia | exact I] | split; exact I].
  - exact (w6c6_facts2 _ R F cur NN (bv_unsigned b) E9u E32u E23u E14u E33u E34u E36u BR HR16 BF HF32 Bc BN Bt). }
pose proof (w6c_pin _ _ _ (24%bv : bv 5) (SOff 14 1) HS0 eq_refl
  ltac:(cbn [ss_regs]; replace (sr_get sr_atoms (24%bv : bv 5)) with (SOff 24 0) by (vm_compute; reflexivity);
        cbn [sv_denot]; rewrite E14w, E24w; unfold w64;
        rewrite !unsigned_lit_small by lia; f_equal; lia)) as HS1.
w6c6_norm HS1.
pose proof (w6c_pin _ _ _ (25%bv : bv 5) (SOff 33 (-1)) HS1 eq_refl
  ltac:(cbn [ss_regs]; replace (sr_get (sr_set sr_atoms (24%bv : bv 5) (SOff 14 1)) (25%bv : bv 5))
          with (SOff 25 0) by (vm_compute; reflexivity);
        cbn [sv_denot]; rewrite E33w, E25w; unfold w64;
        rewrite !unsigned_lit_small by lia; f_equal; lia)) as HS.
w6c6_norm HS. clear HS0 HS1.
assert (SHOK : sh_ok rsegs w6c_Bx w6c_SH (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0))
  (mrestrict (w_H W) memc)).
{ apply (w6c_shok _ W memc F).
  - unfold w6c_Bx. apply (U_atom _ 23 SHADOW_OFF E23w). unfold SHADOW_OFF. lia.
  - apply (U_atom _ 32 F E32w). lia.
  - replace (F + 0xf0) with (F + HM_E + 0) by (unfold HM_E; lia).
    apply (hm_A_ra_e rsegs _ _ F false false false false false 0 8);
      [rewrite <- hs_PJ_sh; exact Dfsh | apply w6c_F8; exact HF32 | lia | lia].
  - exact HFapp. }
pose proof w6c_wx as Hwx. pose proof w6c_segs_low as Hsl. pose proof (AR_laws_ok rsegs B) as HL.
unfold cfg_at. change (w64 W6C_D6) with (Z_to_bv 64 W6C_D6).
(* ---- 0x81dc8 .. 0x81e08: the two checks ---- *)
aj_run_to_tok w6c_tbl_ok HS HJc SHOK w6c_Bspan W6C6_J4.
{ (* the table's entry *)
  apply (w6c_obl _ (w_H W) memc _ 4 (W6C_T6 + 4 * (bv_unsigned b mod 4))).
  - pose proof (Z.mod_pos_bound (bv_unsigned b) 4 ltac:(lia)).
    apply (ra_sub _ _ W6C_T6 16); [exact DT6 | lia | lia].
  - apply (U_atom _ 23 SHADOW_OFF E23w). unfold SHADOW_OFF. lia.
  - apply (w6c_U_tbl _ W6C_T6 (bv_unsigned b) E34w ltac:(lia) ltac:(unfold W6C_T6; lia)). }
{ (* the cursor's byte *)
  apply (w6c_obl _ (w_H W) memc _ 1 cur).
  - apply (ra_sub _ _ cur (Z.of_nat (length (b :: r1)))); [exact Dra | lia | lia].
  - apply (U_atom _ 23 SHADOW_OFF E23w). unfold SHADOW_OFF. lia.
  - rewrite (U_atom_off _ 14 (cur - 1) 1 E14w ltac:(lia) ltac:(lia)). lia. }
{ eapply awr_ok_cons_stack_off with (n := 9%nat) (d := R - sp0);
    [reflexivity | rewrite E9u; lia
    | cbn [w6c_RS YP09.r_wlo]; lia | cbn [w6c_RS YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbn [w6c_RI YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
(* ---- at 0x81e08 ---- *)
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (PA : bv_unsigned (ew Ev 9) = R /\ bv_unsigned (ew Ev 32) = F /\ bv_unsigned (ew Ev 14) = cur - 1 /\
               bv_unsigned (ew Ev 33) = NN /\ bv_unsigned (ew Ev 34) = bv_unsigned b /\
               bv_unsigned (ew Ev 35) = sa /\ ew Ev 34 = w64 (bv_unsigned b) /\ ew Ev 33 = w64 NN)
    by (repeat split; rewrite ?ew_ewset_other by lia; assumption) end.
destruct PA as (PA9 & PA32 & PA14 & PA33 & PA34 & PA35 & PAw34 & PAw33).
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x118 <= a < R + 0x120) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ lazymatch goal with HFx : frame_of ?Ev ?rsx ?m0 (ms_mem ?msx) |- _ =>
    refine (w6c6_kept (w_H W) Ev rsx m0 (ms_mem msx) memc (fun a => R + 0x118 <= a < R + 0x120)
              _ HFx (fun a _ _ => eq_refl)) end.
  intros xx (rg & Hin0 & Hr). cbn [In] in Hin0.
  repeat (destruct Hin0 as [<- | Hin0];
    [cbn [w6c_RS w6c_RI YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
     rewrite ?E9u, ?E14u in Hr; cbv beta; lia|]).
  destruct Hin0. }
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ w6c6_win R F a ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. apply KA; [exact Ha | unfold w6c6_win in Hn; tauto]. }
assert (Hshk : forall s, 0x7fff8000 - 8 <= s < 0x10007fff8000 + 8 ->
  aview rsegs (w_H W) (ms_mem ms) s = aview rsegs (w_H W) memc s)
  by (intros s Hs; apply KA; lia).
assert (Hsh : forall x, 0 <= x < 0x800000000000 ->
  aview rsegs (w_H W) (ms_mem ms) (shadow_of_addr SHADOW_OFF x)
  = aview rsegs (w_H W) memc (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as Hb.
  unfold kLowMemEnd, kHighMemBeg in Hb. apply Hshk. lia. }
assert (ROM1 : rom_view rsegs W (ms_mem ms)).
{ intros a Ha. pose proof (w6c6_rom_low a Ha) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite KA; [exact (Hromc a Ha) | lia | lia]. }
assert (HpF1 : forall o, 0 <= o < 1024 -> apresent (w_H W) (ms_mem ms) (F + o))
  by (intros o Ho; eapply apresent_grows; [eassumption | apply HpF; exact Ho]).
assert (HpR1 : forall a, R <= a < R + 0x1e0 -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; eapply apresent_grows; [eassumption | apply HpR; exact Ha]).
(* the registers the run kept *)
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (HAE : env_agree 32 (Ereg regs (w6c_extra F NN (bv_unsigned b) sa 0)) Ev)
    by (split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]) end.
assert (Hkp : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [1; 10; 11; 12; 13; 20; 24; 25]%bv ->
  getr (ms_regs ms) rr = getr regs rr)
  by (apply (regs_kept_of_st_ok rsegs _ _ ms regs (w6c_extra F NN (bv_unsigned b) sa 0) (w_H W)
        [1; 10; 11; 12; 13; 20; 24; 25]%bv HS HAE ltac:(vm_compute; reflexivity))).
lazymatch type of HS with st_ok _ ?Ev ?ssf _ =>
  let r0 := eval vm_compute in (nth_error (ss_mem ssf) 0%nat) in
  lazymatch r0 with Some ?rg =>
    assert (HRG0 : region_ok rsegs Ev (mrestrict (w_H W) (ms_mem ms)) rg)
      by (apply (w6c_region_nth Ev ssf _ 0%nat rg HS); vm_compute; reflexivity) end
end.
(* the cut's facts at the new memory *)
assert (Hin1 : w6c_in_D B W (ms_mem ms) (ms_regs ms) R F cur sa (b :: r1)).
{ unfold w6c_in_D. repeat apply conj.
  - rewrite Hkp by w6c6_notin. exact D2.
  - rewrite Hkp by w6c6_notin. exact D3.
  - rewrite Hkp by w6c6_notin. exact D4.
  - rewrite Hkp by w6c6_notin. exact D9.
  - rewrite Hkp by w6c6_notin. exact D23.
  - w6c6_rv W HS ((24%bv) : bv 5).
  - rewrite Hkp by w6c6_notin. exact D14.
  - w6c6_rv W HS ((25%bv) : bv 5).
  - apply (w6c_val_kept (w_H W) memc); [exact Dmul | intros i Hi; apply KA; lia].
  - apply (w6c_val_kept (w_H W) memc); [exact Dsa | intros i Hi; apply KA; lia].
  - lia.
  - lia.
  - apply (w6c_val_kept (w_H W) memc); [exact Dc0 | intros i Hi; apply KA; lia].
  - apply (w6c_val_kept (w_H W) memc); [exact Df0 | intros i Hi; apply KA; lia].
  - apply (w6c_field _ _ 9%nat R _ _ _ _ _ 0x118 8 (SOff 33 0) (Z.of_nat (length (b :: r1)) + 1) HRG0 PA9);
      [w6c6_chunk | apply w6c6_denot; w6c6_uc | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia].
  - apply (hm_bytes_kept rsegs (w_H W) memc); [exact Dz|].
    intros x Hx. rewrite length_zeros in Hx. apply KA; lia.
  - unfold hd_fsh. intros i Hi. change (Z.of_nat (length hs_PJ)) with 80 in Hi.
    assert (Hsf : 0x7fff8000 <= shadow_addr F /\ shadow_addr F + 80 < 0x10007fff8000 + 8).
    { unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
      assert (F / 8 <= 2 ^ 44 - 128) by (apply Z.div_le_upper_bound; lia). lia. }
    rewrite Hshk; [exact (Dfsh i Hi) | lia].
  - apply (hm_bytes_kept rsegs (w_H W) memc); [exact Dbytes|].
    intros x Hx. apply KA; [lia|]. destruct (Ddis x ltac:(lia)) as (Dd1 & Dd2).
    unfold T_SEG_STK, ASTACK in Dd1. lia.
  - apply (hm_ra_kept rsegs (w_H W) memc); [exact Dra|]. intros x Hx. apply Hsh. lia.
  - intros Hpos. apply (w6c6_hull_keep (w_H W) memc); [exact Hshk | lia | lia | lia | apply Dhull; lia].
  - exact Damr.
  - exact Dcur1.
  - exact Dcurhi.
  - exact Ddis.
  - apply (hm_ra_kept rsegs (w_H W) memc); [exact DT6|].
    intros x Hx. apply Hsh. unfold W6C_T6 in *. lia.
  - apply (hm_ra_kept rsegs (w_H W) memc); [exact DT8|].
    intros x Hx. apply Hsh. unfold W6C_T8 in *. lia.
  - exact Dtbl. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msx HS eq_refl) end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 W6C6_J4) mm (seg_rom rsegs)) md) with (cfg_at rsegs W6C6_J4 rg mm md) end.
eapply (w6c6_mid STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa b r1
  _ _ _ (bv_unsigned b mod 4) _ _ _ _ _ Hctx Hin Hin1).
- eassumption.
- first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; apply same_io_refl].
- exact ROM1.
- exact HpF1.
- exact HpR1.
- exact K1.
- intros rr Hrr. apply Hkp.
  + cbv [w6c_keep In] in Hrr. repeat (destruct Hrr as [<- | Hrr]; [vm_compute; discriminate|]). destruct Hrr.
  + cbv [w6c_keep In] in Hrr.
    repeat (destruct Hrr as [<- | Hrr];
      [cbv [In]; intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]). destruct Hrr.
- w6c6_rv0 W HS ((10%bv) : bv 5).
  exact (w6c_U_tbl _ W6C_T6 (bv_unsigned b) PAw34 ltac:(lia) ltac:(unfold W6C_T6; lia)).
- w6c6_rv0 W HS ((12%bv) : bv 5). exact (w6c_U_and3 _ 34 (bv_unsigned b) PAw34 ltac:(lia)).
- w6c6_rv W HS ((20%bv) : bv 5).
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.

(* ===================================== the block lemma ===================================== *)
Theorem w6c_case6 : w6c_case6_stmt B.
Proof.
unfold w6c_case6_stmt, w6c_case_stmt. cbv beta iota.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa r Hctx Hin.
replace (w6c_pc 6) with W6C_D6 by reflexivity.
destruct r as [|b r1].
- rewrite w6c6_ent_nil. cbn [fst snd length Nat.sub].
  apply (w6c6_nil STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa);
    [exact Hctx | exact Hin | reflexivity | lia | reflexivity].
- apply (w6c6_cons STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa b r1);
    [exact Hctx | exact Hin | reflexivity | reflexivity | reflexivity].
Qed.
End d.
End c.
End b.

Print Assumptions w6c_case6.
