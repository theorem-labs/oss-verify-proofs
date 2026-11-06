(* Modified by Theorem Labs, 2026-10: helpers adapted from proofs/reac-pw/fuzz_role/lib/A/RPgW6aC2h.v at
   616508a91de2 (c2_notin, c2_nz, c2_af, c2_all256, c2_keep_step, c2_keep, c2_regv, c2_kio renamed c1_*; c2_kio uses
   lib/A/RtPgSteps.v same_io_wvb) for reac-pw/fuzz_rate's image A; the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6bC1Kit.v at 32f84792c2a6; for image B
   (fuzz_rate.asan-ubsan): the pcs, the shadow offset's register (s4, atom 20), the real frame's bound (R + 0x220),
   the vocab table's address and the read-only check of the bytes after each string are image B's; the prefix c1_
   becomes c1b_; the value of the cell [R+0x100] (the complement of e62.body) and its closed bounds are added. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the kit of the block lemma
   w6bb_c1 of lib/AU/RtPgW6bBaseB.v (ent_build's case 1, pod.h:286-294, inside LLVMFuzzerTestOneInput 0x8076c, from
   the case entry 0x81900 to the join J 0x820dc). Proves no function (kind: segment lemma).
   The block is proved in four engine runs and two calls, each a lemma in continuation form (lib/AU/RtPgW6bC1HeadB.v,
   RtPgW6bC1MidB.v, RtPgW6bC1TailB.v), chained in lib/AU/RtPgW6bC1B.v:
     head    0x81900 .. 0x81b8c   the index byte (its UBSan tests T1 0x81908 and T2 0x81950), i = fuzz_u8 % 9,
                                  [R+0x128] := the kind byte, [R+0x70] := what is left, a0 := &vocab[i]
     vload   0x81b8c .. 0x421ec   the checked 8-byte load of vocab[i] and the call of the strlen wrapper
     strlen  0x421ec .. 0x81bac   the wrapper (lib/A/Rt/StrlenDef.v astrlen_realizes, the image-parametric definition)
     mid     0x81bac .. 0x518b8   l = min(len, 95) (never cut: len <= 18), the call of __asan_memcpy
     memcpy  0x518b8 .. 0x81bd4   lib/Reusable/YG0d.v aintrin_realizes OCpy
     tail    0x81bd4 .. J         the NUL, e62.type, e62.size and, when kind & 0x80, the two checked stores 'x', 0;
                                  the UBSan tests T3 0x81bd8, 0x81c14, 0x81c44 against the cell [R+0x100].
   This file: the pcs, the shadow machinery every run shares (the shadow offset is s4, atom 20, fact [K, K]), the
   model's index / string / length, the closed bounds of the cell [R+0x100] = ~(F + 0x218), the bytes below the
   allocation ceiling that every call keeps (c1b_lowk), and the helpers of the runs. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YP08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgMemB RtPgStepsB RtPgW6bBaseB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia reasons about the divisions of the shadow map in this file (RtPgStepsB.v turns that off for its importers) *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the pcs ======================================== *)
Definition C1B_V : Z := 0x81b8c.      (* a0 = &vocab[i], after the two spills: the check of the 8-byte load *)
Definition C1B_RSTR : Z := 0x81bac.   (* the strlen wrapper's return *)
Definition C1B_RCPY : Z := 0x81bd4.   (* __asan_memcpy's return *)

(* ======================================== the shadow machinery ======================================== *)
Definition C1B_Bx : sv := SOff 20 0.
Definition C1B_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition c1b_shf : nat * afact := (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0).
(* the real frame's base R (s1, atom 9): above the allocation ceiling, below 2^47, 16-aligned *)
Definition c1b_fR : nat * afact := (9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 4).

(* ======================================== the cell [R+0x100] ========================================
   [R+0x100] = ~(F + 0x218) = 2^64 - 1 - (F + 0x218), the complement of e62.body, which the T3 tests compare with a
   length. Its closed bounds, from 4096 <= F and F + 1024 <= alloc_ceiling <= 0x7fffff800000. *)
Definition C1B_NFLO : Z := 18446603336229584359.   (* 2^64 - 1 - 0x218 - 0x7fffff800000 *)
Definition C1B_NFHI : Z := 18446744073709546983.   (* 2^64 - 1 - 0x218 - 4096 *)
Lemma c1b_nf_range : forall F, 4096 <= F <= 0x7fffff800000 ->
  C1B_NFLO <= 2 ^ 64 - 1 - (F + 0x218) <= C1B_NFHI.
Proof. intros F HF. unfold C1B_NFLO, C1B_NFHI. lia. Qed.

(* ======================================== the model ======================================== *)
(* i mod 9 (the index the code computes), the string vocab[i] and its length *)
Definition c1b_j (r : list byte) : Z := fst (fuzz_u8 r) mod 9.
Definition c1b_v (j : Z) : list byte := nth (Z.to_nat j) vocab [].
Definition c1b_len (j : Z) : Z := Z.of_nat (length (c1b_v j)).
Lemma c1b_j_range : forall r, 0 <= c1b_j r < 9.
Proof. intros r. unfold c1b_j. apply Z.mod_pos_bound. lia. Qed.
Lemma c1b_len_vals : forall j, 0 <= j < 9 ->
  c1b_len j = 12 \/ c1b_len j = 13 \/ c1b_len j = 14 \/ c1b_len j = 15 \/ c1b_len j = 18.
Proof.
intros j Hj. assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia.
unfold c1b_len, c1b_v.
destruct E as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; vm_compute; lia.
Qed.
Lemma c1b_len_range : forall j, 0 <= j < 9 -> 12 <= c1b_len j <= 18.
Proof. intros j Hj. pose proof (c1b_len_vals j Hj). lia. Qed.
Lemma c1b_vptr_range : forall j, 0 <= j < 9 -> 0x20fa0 <= w6bb_vptr j <= 0x210c0.
Proof.
intros j Hj. assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia.
destruct E as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; split; vm_compute; intros Hx; discriminate Hx.
Qed.
(* the bytes from the NUL of vocab[i] to the end of the NUL's 8-byte word are read-only image bytes of image B *)
Definition c1b_tail_chk : bool :=
  forallb (fun j => let x := w6bb_vptr (Z.of_nat j) in let k := c1b_len (Z.of_nat j) in
    forallb (fun d => let a := x + k + Z.of_nat d in
      if a <? x + k - (x + k) mod 8 + 8 then in_rom_b a && YP08.img_byte_ok rsegs a else true) (seq 1 8)) (seq 0 9).
Lemma c1b_tail_chk_true : c1b_tail_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma c1b_tail_rom : forall j a, 0 <= j < 9 ->
  w6bb_vptr j + c1b_len j < a < w6bb_vptr j + c1b_len j - (w6bb_vptr j + c1b_len j) mod 8 + 8 ->
  in_rom_b a = true /\ YP08.img_byte_ok rsegs a = true.
Proof.
intros j a Hj Ha.
pose proof (proj1 (forallb_forall _ _) c1b_tail_chk_true (Z.to_nat j) ltac:(apply in_seq; lia)) as H1.
cbv beta zeta in H1. rewrite Z2Nat.id in H1 by lia.
pose proof (Z.mod_pos_bound (w6bb_vptr j + c1b_len j) 8 ltac:(lia)) as Hm.
pose proof (proj1 (forallb_forall _ _) H1 (Z.to_nat (a - (w6bb_vptr j + c1b_len j))) ltac:(apply in_seq; lia)) as H2.
cbv beta zeta in H2. rewrite Z2Nat.id in H2 by lia.
replace (w6bb_vptr j + c1b_len j + (a - (w6bb_vptr j + c1b_len j))) with a in H2 by lia.
replace (a <? w6bb_vptr j + c1b_len j - (w6bb_vptr j + c1b_len j) mod 8 + 8) with true in H2
  by (symmetry; apply Z.ltb_lt; lia).
apply andb_prop in H2. exact H2.
Qed.
(* kind & 0x80 and the sign of the sign-extended kind byte *)
Definition c1b_s6 (kd : Z) : Z := kd - 256 * (kd / 128).
Lemma c1b_all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall c, 0 <= c < 256 -> P c = true.
Proof.
intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c).
split; [lia | apply in_seq; lia].
Qed.
Lemma c1b_bge_s6 : forall kd, 0 <= kd < 256 ->
  branch_taken BC_GE (Z_to_bv 64 (c1b_s6 kd)) (Z_to_bv 64 0) = negb (Z.testbit kd 7).
Proof.
intros kd Hk. apply Bool.eqb_prop.
exact (c1b_all256 (fun kd => Bool.eqb (branch_taken BC_GE (Z_to_bv 64 (c1b_s6 kd)) (Z_to_bv 64 0)) (negb (Z.testbit kd 7)))
  ltac:(vm_compute; reflexivity) kd Hk).
Qed.
Lemma c1b_s6_range : forall kd, 0 <= kd < 256 -> -128 <= c1b_s6 kd < 128.
Proof. intros kd Hk. unfold c1b_s6. lia. Qed.

(* ======================================== small helpers ======================================== *)
Lemma c1b_notin : forall (r : bv 5) (l : list (bv 5)), existsb (fun c => bv_eqb c r) l = false -> ~ In r l.
Proof.
intros r l H Hin. induction l as [|c l IH]; [exact Hin|]. cbn [existsb] in H. apply orb_false_iff in H as [H1 H2].
destruct Hin as [<-|Hin]; [|exact (IH H2 Hin)]. unfold bv_eqb in H1. rewrite Z.eqb_refl in H1. discriminate H1.
Qed.
Lemma c1b_nz : forall r : bv 5, (bv_unsigned r =? 0) = false -> bv_unsigned r <> 0.
Proof. intros r H. apply Z.eqb_neq. exact H. Qed.
Lemma c1b_af : forall E n v lo hi al, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  v mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E n (mkAF lo hi al).
Proof. intros E n v lo hi al H Hv Hb Hm Ha. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H, unsigned_lit_small by lia. auto. Qed.
Lemma c1b_incl_sub : forall (l1 l2 : list (bv 5)) (r : bv 5), incl l1 l2 -> ~ In r l2 -> ~ In r l1.
Proof. intros l1 l2 r H Hn Hin. exact (Hn (H r Hin)). Qed.
(* a register of the state after a run, as its symbolic value's denotation *)
Ltac c1b_regv HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E ss ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity);
    cbn [sv_denot]; rewrite ?ew_ewset_other by lia
  end.
Ltac c1b_kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; c1b_kio].
(* a run whose regions have no write window keeps every byte *)
Lemma c1b_keep_step : forall {fx : YK11.FPState} E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
  (forall a, aview rsegs H m1 a = aview rsegs H m0 a) ->
  frame_of E rs (mrestrict H m1) (mrestrict H m2) -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros fx E rs H m0 m1 m2 K HF Hro a. rewrite <- (K a). unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr). pose proof (proj1 (forallb_forall _ _) Hro r Hin) as Hw. apply Z.leb_le in Hw. lia.
Qed.
Ltac c1b_keep :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, aview _ _ _ a = _ |- _ =>
    let KS := fresh "KS" in
    pose proof (c1b_keep_step _ _ _ _ _ _ KE HFr ltac:(vm_compute; reflexivity)) as KS;
    clear KE HFr; rename KS into KE
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* registers kept: a list that holds no register r, decided *)
Ltac c1b_out := first [apply c1b_notin; vm_compute; reflexivity | apply c1b_nz; reflexivity].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ======================================== the bytes every call keeps ======================================== *)
(* the image, the shadow of the image and of the frame for locals, and that frame, all lie below the allocation
   ceiling; the real frame and the callees' stack lie above it *)
Definition c1b_lowk (W : world rsegs) (mem mem' : word -> option byte) : Prop :=
  forall a, 0 <= a < alloc_ceiling -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a.
Lemma c1b_lowk_trans : forall W m1 m2 m3, c1b_lowk W m1 m2 -> c1b_lowk W m2 m3 -> c1b_lowk W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.
Lemma c1b_lowk_of : forall W m m' (X : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a) ->
  (forall a, X a -> alloc_ceiling <= a) -> c1b_lowk W m m'.
Proof.
intros W m m' X H HX a Ha. pose proof asan_consts as (Hc & _). apply H; [lia|]. intros Hx. pose proof (HX a Hx). lia.
Qed.
Lemma c1b_img_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof. exact rtsb_segs_low. Qed.
Lemma c1b_shadow_low : forall x, 0 <= x < kLowMemEnd -> 0 <= shadow_of_addr SHADOW_OFF x < alloc_ceiling.
Proof.
intros x Hx. pose proof asan_consts as (Hc & _). unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd in *.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 <= 0x7fff8000 / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma c1b_ra_lowk : forall W m m' a n, c1b_lowk W m m' -> 0 <= a -> a + n <= kLowMemEnd ->
  range_addressable (aview rsegs (w_H W) m) SHADOW_OFF a n -> range_addressable (aview rsegs (w_H W) m') SHADOW_OFF a n.
Proof.
intros W m m' a n HK Ha Hn H. apply (rtmb_ra_kept rsegs _ _ _ _ _ _ _ H). intros x Hx.
apply HK. apply c1b_shadow_low. lia.
Qed.
Lemma c1b_hull_lowk : forall W m m' a n, c1b_lowk W m m' -> 0 <= a -> 0 < n -> a + n <= kLowMemEnd ->
  shadow_hull_vis (aview rsegs (w_H W) m) a n -> shadow_hull_vis (aview rsegs (w_H W) m') a n.
Proof.
intros W m m' a n HK Ha Hn0 Hn H s Hs. rewrite HK; [exact (H s Hs)|].
pose proof asan_consts as (Hc & _). unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *.
assert (A1 : 0 <= (0x7fff8000 + a / 8) / 8 * 8).
{ pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (0x7fff8000 + a / 8) 8 ltac:(lia) ltac:(lia)). lia. }
assert (A2 : (a + n - 1) / 8 <= 0x7fff8000 / 8) by (apply Z.div_le_mono; lia).
assert (A3 : (0x7fff8000 + (a + n - 1) / 8) / 8 * 8 <= 0x7fff8000 + (a + n - 1) / 8).
{ pose proof (Z.mul_div_le (0x7fff8000 + (a + n - 1) / 8) 8 ltac:(lia)). lia. }
lia.
Qed.
Lemma c1b_cstr_lowk : forall W m m' a s, c1b_lowk W m m' -> rt_cstr rsegs (w_H W) m a s -> rt_cstr rsegs (w_H W) m' a s.
Proof.
intros W m m' a s HK (Hb & Hn & Hr & Ha0 & Ha63 & Himg & Ham & Hra & Hhu).
assert (Hlow : forall i, 0 <= i <= Z.of_nat (length s) -> 0 <= a + i < kLowMemEnd)
  by (intros i Hi; exact (c1b_img_low _ (Himg i Hi))).
pose proof asan_consts as (Hc & _).
assert (HL : forall i, 0 <= i <= Z.of_nat (length s) -> 0 <= a + i < alloc_ceiling).
{ intros i Hi. pose proof (Hlow i Hi). unfold kLowMemEnd in *. lia. }
split; [intros i Hi; rewrite HK by (apply HL; lia); exact (Hb i Hi)|].
split; [rewrite HK by (apply HL; lia); exact Hn|].
split; [exact Hr|]. split; [exact Ha0|]. split; [exact Ha63|]. split; [exact Himg|]. split; [exact Ham|].
pose proof (Hlow (Z.of_nat (length s)) ltac:(lia)) as Hl.
split; [apply (c1b_ra_lowk W m m'); [exact HK | lia | lia | exact Hra]|].
apply (c1b_hull_lowk W m m'); [exact HK | lia | lia | lia | exact Hhu].
Qed.
Lemma c1b_rom_lowk : forall W m m', c1b_lowk W m m' -> rom_view rsegs W m -> rom_view rsegs W m'.
Proof.
intros W m m' HK HR a Ha. pose proof asan_consts as (Hc & _).
assert (Hi : in_img rsegs a) by (destruct Ha as (sg & Hs & Hw & Hr); exists sg; auto).
pose proof (c1b_img_low a Hi) as Hl. unfold kLowMemEnd in Hl. rewrite HK by lia. exact (HR a Ha).
Qed.
Lemma c1b_vocab_lowk : forall W m m', c1b_lowk W m m' -> w6bb_vocab_ok W m -> w6bb_vocab_ok W m'.
Proof.
intros W m m' HK (Hra & Hv). pose proof asan_consts as (Hc & _). split.
- apply (c1b_ra_lowk W m m'); [exact HK | unfold W6BB_VOCAB; lia | unfold W6BB_VOCAB, kLowMemEnd; lia | exact Hra].
- intros i Hi. destruct (Hv i Hi) as [Hc1 Hc2]. split.
  + apply (rtsb_val_kept (w_H W) m m'); [|exact Hc1]. intros q Hq. change (Z.of_nat 8) with 8 in Hq.
    apply HK. unfold W6BB_VOCAB. lia.
  + exact (c1b_cstr_lowk W m m' _ _ HK Hc2).
Qed.
End b.
