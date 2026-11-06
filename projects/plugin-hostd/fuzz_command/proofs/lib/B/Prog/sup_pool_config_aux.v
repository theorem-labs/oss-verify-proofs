(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the helper facts of sup_pool_config's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, entry BASE + AF_sup_pool_config = 0x8bed0, 127 instructions, 0 report calls, 0 UBSan trap
   sites) that need none of the callee statements record_c / arg_s_c / answer_c: the walk's program points, the
   model step in the form the three callee posts chain it, the "%d" text of the inlined arg_i (snprintf's piece
   list against the recorder's dec), the read-only literals "pool_config" (0x21ec0) and "%d" (0x21f40), and the
   block bookkeeping of the post. Re-walked from lib/A/Prog/sup_pool_config_d.v (the verb lemmas),
   sup_pool_config_s2.v (spc_model) and sup_pool_config_s3.v (spc_final_blocks, here over an owned-block list given
   by membership, since B's callees return their lists in their own order). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdRo CmdChk CmdBase CmdRep CmdZsh CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSnText CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---------- program points, as listing offsets from BASE (B, measured with capstone from .symtab) ---------- *)
Definition SPCB_SMALLOC : Z := AF_sup_pool_config + 0x68.  (* 0x8bf38: jal __asan_stack_malloc_0, a0 = 64 *)
Definition SPCB_FLAG0 : Z := AF_sup_pool_config + 0x74.    (* 0x8bf44: the use-after-return flag is 0: s2 := 0 *)
Definition SPCB_FJOIN : Z := AF_sup_pool_config + 0x78.    (* 0x8bf48: the flag's two arms meet *)
Definition SPCB_REAL : Z := AF_sup_pool_config + 0x80.     (* 0x8bf50: the real-stack fallback (s2 = 0) *)
Definition SPCB_SEAT : Z := AF_sup_pool_config + 0x9c.     (* 0x8bf6c: the frame s8 is seated *)
Definition SPCB_RECORD : Z := AF_sup_pool_config + 0x100.  (* 0x8bfd0: jal record, a0 = 14 *)
Definition SPCB_ARGS1 : Z := AF_sup_pool_config + 0x10c.   (* 0x8bfdc: jal arg_s, a0 = slot, a1 = name *)
Definition SPCB_UNPOIS : Z := AF_sup_pool_config + 0x110.  (* 0x8bfe0: b's shadow := 00 00 *)
Definition SPCB_SNPRINTF : Z := AF_sup_pool_config + 0x12c. (* 0x8bffc: jal snprintf(b, 16, "%d", max) *)
Definition SPCB_ARGS2 : Z := AF_sup_pool_config + 0x138.   (* 0x8c008: jal arg_s, a0 = slot, a1 = b *)
Definition SPCB_REPOIS : Z := AF_sup_pool_config + 0x13c.  (* 0x8c00c: b's shadow := f8 f8 *)
Definition SPCB_SHAPE : Z := AF_sup_pool_config + 0x150.   (* 0x8c020: jal rec_shape_of("pool_config", 11) *)
Definition SPCB_ANSWER : Z := AF_sup_pool_config + 0x160.  (* 0x8c030: jal answer(slot, shape, 1) *)
Definition SPCB_FREE : Z := AF_sup_pool_config + 0x164.    (* 0x8c034: the frame's release (magic 0x45e0360e) *)
Definition SPCB_RFREE : Z := AF_sup_pool_config + 0x1a4.   (* 0x8c074: the real-stack arm of the release *)
Definition SPCB_EPI : Z := AF_sup_pool_config + 0x1c4.     (* 0x8c094: the epilogue, sp := s0 - 96 *)
Definition SPCB_RET : Z := AF_sup_pool_config + 0x1f8.     (* 0x8c0c8: ret *)

(* ---------- the model, in the order the walk's callees build it ---------- *)
(* record(14) leaves rec_record R 14 []; arg_s on name appends sarg name; arg_s on the printed max appends
   sarg (Some (dec max)); answer then answers that call with changes = 1 *)
Lemma spcb_args : forall name max, ([] ++ [sarg name]) ++ [sarg (Some (dec max))] = [sarg name; dec max].
Proof. reflexivity. Qed.

Definition spcb_verb : list byte := bstr "pool_config"%string.

Lemma spcb_model : forall R name max,
sup_pool_config_m R name max =
rec_answer (rec_record R REC_POOL_CONFIG [sarg name; dec max]) (REC_POOL_CONFIG, [sarg name; dec max])
  (shape_of spcb_verb) true.
Proof. intros R name max. unfold sup_pool_config_m, rec_stub, daemon_shape. reflexivity. Qed.

(* ---------- the inlined arg_i: snprintf(b, 16, "%d", max) prints dec max ---------- *)
Lemma spcb_pf_dec_len : forall v, -2 ^ 31 <= v < 2 ^ 31 -> (1 <= length (PF.pf_dec v) <= 11)%nat.
Proof.
intros v Hv. pose proof (dec_length v Hv) as H. rewrite <- (snt_pf_dec v Hv) in H.
unfold PF.pf_bytes in H. rewrite length_map in H. exact H.
Qed.

(* the format the inlined arg_i passes (0x21f40), its pieces and the text they give for max *)
Definition spcb_fmt : list Z := [37; 100].

Lemma spcb_fmt_lit : RO_lit_21f40 = PF.pf_bytes spcb_fmt ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Lemma spcb_fmt_parse : PF.pf_parse spcb_fmt = Some [PF.Pd].
Proof. reflexivity. Qed.

Lemma spcb_fmt_text_len : forall v, -2 ^ 31 <= v < 2 ^ 31 -> Z.of_nat (length (PF.pf_dec v)) < 2 ^ 31 - 1.
Proof. intros v Hv. pose proof (spcb_pf_dec_len v Hv). lia. Qed.

(* the 16-byte buffer b gets the whole text and its terminator: dec max and a NUL *)
Lemma spcb_snprintf_out : forall v, -2 ^ 31 <= v < 2 ^ 31 ->
PF.pf_bytes (firstn (Z.to_nat (16 - 1)) (PF.pf_dec v) ++ [0]) = dec v ++ [Z_to_bv 8 0].
Proof.
intros v Hv. pose proof (spcb_pf_dec_len v Hv) as HL.
change (Z.to_nat (16 - 1)) with 15%nat. rewrite firstn_all2 by lia.
unfold PF.pf_bytes. rewrite map_app. fold (PF.pf_bytes (PF.pf_dec v)). rewrite (snt_pf_dec v Hv). reflexivity.
Qed.

(* max goes to snprintf in a3 as the entry's a1 (s3 = a1, 0x8bf10 .. 0x8bff8) *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma spcb_aint_arg : forall segs stk (W : world segs) regs mem D n rs v, -2 ^ 31 <= v < 2 ^ 31 ->
apf_args_ok segs stk W regs mem D n (w64 v :: rs) [PF.AInt v].
Proof.
intros segs stk W regs mem D n rs v Hv. cbn [apf_args_ok apf_arg_ok]. split; [|destruct rs; exact I].
split; [exact Hv|].
unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_eq v (2 ^ 64)) by lia.
replace (v - 2 ^ 64 * (v / 2 ^ 64)) with (v + (- (2 ^ 32) * (v / 2 ^ 64)) * 2 ^ 32) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
End a.

(* ---------- the read-only literals: "pool_config" (rec_shape_of's verb) and "%d" ---------- *)
Lemma spcb_abytes_prefix : forall (rd : reader) a l1 l2, abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof. intros rd a l1 l2 H k Hk. rewrite (H k ltac:(rewrite length_app; lia)). rewrite app_nth1 by lia. reflexivity. Qed.

(* the shape answer instantiates fits its buffer (answer_c.v's fits premise) *)
Lemma spcb_fits : fits (shape_of spcb_verb).
Proof. unfold fits. vm_compute. congruence. Qed.

Lemma spcb_verb_lit : RO_lit_21ec0 = spcb_verb ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.
Lemma spcb_verb_len : Z.of_nat (length spcb_verb) = 11.
Proof. reflexivity. Qed.

Lemma spcb_verb_lit_at : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21ec0 RO_lit_21ec0.
Proof.
intros rd [HRO _]. unfold cmd_ro_bytes in HRO.
repeat match type of HRO with
| abytes_atR _ 0x21ec0 _ /\ _ => exact (proj1 HRO)
| _ /\ _ => apply proj2 in HRO
end.
Qed.

Lemma spcb_verb_bytes : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21ec0 spcb_verb.
Proof.
intros rd H. pose proof (spcb_verb_lit_at rd H) as HL. rewrite spcb_verb_lit in HL.
exact (spcb_abytes_prefix rd _ _ _ HL).
Qed.

Lemma spcb_verb_str : forall rd, cmd_ro_ok rd -> astr_atR rd 0x21ec0 spcb_verb.
Proof.
intros rd H. pose proof (spcb_verb_lit_at rd H) as HL. rewrite spcb_verb_lit in HL. split; [exact HL|].
vm_compute. intros Hc. repeat (destruct Hc as [Hc | Hc]; [discriminate Hc|]). exact Hc.
Qed.

Lemma spcb_verb_ro : forall ro, cmd_ro_in ro -> forall i, 0 <= i < 12 -> ro (0x21ec0 + i).
Proof.
intros ro HRO. unfold cmd_ro_in in HRO.
repeat match type of HRO with
| (forall i, 0 <= i < 12 -> ro (0x21ec0 + i)) /\ _ => exact (proj1 HRO)
| _ /\ _ => apply proj2 in HRO
end.
Qed.

Lemma spcb_fmt_lit_at : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21f40 RO_lit_21f40.
Proof.
intros rd [HRO _]. unfold cmd_ro_bytes in HRO.
repeat match type of HRO with
| abytes_atR _ 0x21f40 _ /\ _ => exact (proj1 HRO)
| _ /\ _ => apply proj2 in HRO
end.
Qed.

(* the format's bytes in fmt_at's form (RtPFShared.v): "%d" and its terminator *)
Lemma spcb_fmt_bytes : forall (rd : reader), cmd_ro_ok rd ->
forall i, 0 <= i <= Z.of_nat (length spcb_fmt) -> rd (0x21f40 + i) = Some (nth (Z.to_nat i) (spcb_fmt ++ [0]) 0).
Proof.
intros rd H i Hi. pose proof (spcb_fmt_lit_at rd H) as HL. cbn [length spcb_fmt Z.of_nat] in Hi.
assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
destruct Hi3 as [-> | [-> | ->]].
- exact (HL 0%nat ltac:(vm_compute; lia)).
- exact (HL 1%nat ltac:(vm_compute; lia)).
- exact (HL 2%nat ltac:(vm_compute; lia)).
Qed.

Lemma spcb_fmt_str : forall rd, cmd_ro_ok rd -> astr_atR rd 0x21f40 (PF.pf_bytes spcb_fmt).
Proof.
intros rd H. pose proof (spcb_fmt_lit_at rd H) as HL. rewrite spcb_fmt_lit in HL. split; [exact HL|].
vm_compute. intros Hc. repeat (destruct Hc as [Hc | Hc]; [discriminate Hc|]). exact Hc.
Qed.

Lemma spcb_fmt_ro : forall ro, cmd_ro_in ro -> forall i, 0 <= i < 3 -> ro (0x21f40 + i).
Proof.
intros ro HRO. unfold cmd_ro_in in HRO.
repeat match type of HRO with
| (forall i, 0 <= i < 3 -> ro (0x21f40 + i)) /\ _ => exact (proj1 HRO)
| _ /\ _ => apply proj2 in HRO
end.
Qed.

(* ---------- the block bookkeeping of the post (pure list reasoning) ---------- *)
(* rs is the allocator's rounded size (req_size); SEP: two different live blocks do not overlap *)
Definition spcb_sep (rs : Z -> Z) (bl : list (Z * Z)) : Prop :=
forall b m p n, In (b, m) bl -> In (p, n) bl -> (b, m) <> (p, n) -> b + rs m <= p \/ p + rs n <= b.
Definition spcb_pos (bl : list (Z * Z)) : Prop := forall b m, In (b, m) bl -> 0 < b /\ 0 <= m.

Lemma spcb_fb_pair_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. intros x y. decide equality; apply Z.eq_dec. Defined.

Lemma spcb_fb_in_dec : forall (pn : Z * Z) l, {In pn l} + {~ In pn l}.
Proof. intros pn l. exact (in_dec spcb_fb_pair_dec pn l). Defined.

(* two live blocks with the same start are the same block *)
Lemma spcb_fb_same : forall (rs : Z -> Z) bl a k m, (forall m, 0 <= m -> 1 <= rs m /\ m <= rs m) ->
spcb_sep rs bl -> spcb_pos bl -> In (a, k) bl -> In (a, m) bl -> (a, k) = (a, m).
Proof.
intros rs bl a k m Hrs S P Hk Hm. destruct (spcb_fb_pair_dec (a, k) (a, m)) as [E|E]; [exact E|].
exfalso. destruct (P a k Hk) as [_ Pk]. destruct (P a m Hm) as [_ Pm].
destruct (Hrs k Pk). destruct (Hrs m Pm). destruct (S a k a m Hk Hm E); lia.
Qed.

(* two different live blocks do not overlap, by their requested sizes *)
Lemma spcb_fb_apart : forall (rs : Z -> Z) bl b m p n, (forall m, 0 <= m -> 1 <= rs m /\ m <= rs m) ->
spcb_sep rs bl -> spcb_pos bl -> In (b, m) bl -> In (p, n) bl -> (b, m) <> (p, n) -> b + m <= p \/ p + n <= b.
Proof.
intros rs bl b m p n Hrs S P Hb Hp E. destruct (P b m Hb) as [_ Pm]. destruct (P p n Hp) as [_ Pn].
destruct (Hrs m Pm). destruct (Hrs n Pn). destruct (S b m p n Hb Hp E); lia.
Qed.

(* bl0: the blocks at the entry; record() frees F (its spill arm), all of them the recorder's O, leaving O0; the two
   arg_s calls make b1 (the copy of name) and b2 (the copy of the printed max); OA: the recorder's blocks at answer's
   entry, given by membership; answer frees the old answer old and makes the two copies (p1, n) (kept by the
   recorder) and (p2, n) (the caller's) *)
Lemma spcb_final_blocks : forall (rs : Z -> Z) (bl0 blA bl' O F O0 OA O' : list (Z * Z)) (b1 b2 : Z * Z)
  (old p1 p2 n : Z),
(forall m, 0 <= m -> 1 <= rs m /\ m <= rs m) ->
(forall pn, In pn O -> In pn bl0) ->
(forall pn, In pn F -> In pn O) ->
(forall pn, In pn O0 <-> In pn O /\ ~ In pn F) ->
(forall pn, In pn OA <-> In pn O0 \/ pn = b1 \/ pn = b2) ->
(forall pn, In pn blA <-> (In pn bl0 /\ ~ In pn F) \/ pn = b1 \/ pn = b2) ->
~ (In b1 bl0 /\ ~ In b1 F) -> ~ (In b2 bl0 /\ ~ In b2 F) -> b2 <> b1 ->
spcb_sep rs blA -> spcb_pos blA ->
(old = 0 \/ exists m, In (old, m) OA) ->
(forall pn, In pn bl' <-> (In pn blA /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) ->
(forall pn, In pn blA -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) -> p1 <> p2 ->
(forall pn, In pn O' <-> (In pn OA /\ fst pn <> old) \/ pn = (p1, n)) ->
spcb_sep rs bl' -> spcb_pos bl' ->
(forall pn, In pn O' -> In pn O \/ ~ In pn bl0) /\
In (p2, n) bl' /\
(forall pn, In pn bl0 -> ~ In pn O -> pn <> (p2, n)) /\
~ In p2 (map fst O') /\
(forall pn, In pn bl0 -> ~ In pn O -> In pn bl' /\ (fst pn + snd pn <= p2 \/ p2 + n <= fst pn)) /\
(forall pn, In pn bl' -> (In pn bl0 /\ ~ In pn O) \/ In pn O' \/ pn = (p2, n)).
Proof.
intros rs bl0 blA bl' O F O0 OA O' b1 b2 old p1 p2 n Hrs HOb HFO HO0 HOA HA Hb1 Hb2 Hb12 SA PA Hold HB' Hp12A
  Hp12 HO' SB PB.
assert (InA : forall pn, In pn bl0 -> ~ In pn F -> In pn blA)
  by (intros pn H1 H2; apply (proj2 (HA pn)); left; split; assumption).
assert (A1 : In b1 blA) by (apply (proj2 (HA b1)); right; left; reflexivity).
assert (A2 : In b2 blA) by (apply (proj2 (HA b2)); right; right; reflexivity).
assert (OAb : forall pn, In pn OA -> In pn blA).
{ intros pn H. apply (proj1 (HOA pn)) in H. destruct H as [H|[H|H]].
  - apply (proj1 (HO0 pn)) in H. destruct H as [H1 H2]. apply InA; [exact (HOb _ H1) | exact H2].
  - subst pn. exact A1.
  - subst pn. exact A2. }
assert (NF : forall pn, ~ (In pn bl0 /\ ~ In pn F) -> In pn bl0 -> In pn F).
{ intros pn H H0. destruct (spcb_fb_in_dec pn F) as [Hf|Hf]; [exact Hf | exfalso; apply H; split; assumption]. }
assert (Hn2 : In (p2, n) bl') by (apply (proj2 (HB' (p2, n))); right; right; reflexivity).
(* a block of blA with the old answer's start is one of the recorder's (OA) *)
assert (OLDR : forall a k, In (a, k) blA -> a = old -> In (a, k) OA).
{ intros a k Hk Ea. subst a. destruct Hold as [Ho | (m & Hm)].
  - destruct (PA old k Hk) as [Pa _]. lia.
  - pose proof (spcb_fb_same rs blA old k m Hrs SA PA Hk (OAb _ Hm)) as Ek. rewrite Ek. exact Hm. }
(* a block live at the entry and kept by record() is not one of the recorder's blocks OA unless in O *)
assert (KEPTR : forall pn, In pn bl0 -> ~ In pn O -> ~ In pn OA).
{ intros pn H0 HnO Hm. assert (HnF : ~ In pn F) by (intros Hf; exact (HnO (HFO _ Hf))).
  apply (proj1 (HOA pn)) in Hm. destruct Hm as [Hm|[Hm|Hm]].
  - exact (HnO (proj1 (proj1 (HO0 _) Hm))).
  - apply Hb1. rewrite <- Hm. split; assumption.
  - apply Hb2. rewrite <- Hm. split; assumption. }
split.
{ intros pn Hpn. apply (proj1 (HO' pn)) in Hpn. destruct Hpn as [[Hpn _] | ->].
  - apply (proj1 (HOA pn)) in Hpn. destruct Hpn as [Hpn | [-> | ->]].
    + left. exact (proj1 (proj1 (HO0 pn) Hpn)).
    + destruct (spcb_fb_in_dec b1 bl0) as [Hi|Hi]; [left; exact (HFO _ (NF b1 Hb1 Hi)) | right; exact Hi].
    + destruct (spcb_fb_in_dec b2 bl0) as [Hi|Hi]; [left; exact (HFO _ (NF b2 Hb2 Hi)) | right; exact Hi].
  - destruct (spcb_fb_in_dec (p1, n) bl0) as [Hi|Hi]; [|right; exact Hi].
    destruct (spcb_fb_in_dec (p1, n) F) as [Hf|Hf]; [left; exact (HFO _ Hf)|].
    pose proof (InA _ Hi Hf) as HiA.
    destruct (Z.eq_dec p1 old) as [Eo|Eo].
    + pose proof (OLDR p1 n HiA Eo) as Hr. destruct (spcb_fb_in_dec (p1, n) O) as [HO|HO]; [left; exact HO|].
      exfalso. exact (KEPTR _ Hi HO Hr).
    + exfalso. exact (proj1 (Hp12A _ HiA Eo) eq_refl). }
split; [exact Hn2|].
split.
{ intros pn H0 HnO E. subst pn.
  assert (HnF : ~ In (p2, n) F) by (intros Hf; exact (HnO (HFO _ Hf))).
  pose proof (InA _ H0 HnF) as HiA.
  destruct (Z.eq_dec p2 old) as [Eo|Eo].
  - exact (KEPTR _ H0 HnO (OLDR p2 n HiA Eo)).
  - exact (proj2 (Hp12A _ HiA Eo) eq_refl). }
split.
{ intros Hm. apply in_map_iff in Hm. destruct Hm as ([a k] & Ea & Hk). cbn [fst] in Ea. subst a.
  apply (proj1 (HO' (p2, k))) in Hk. destruct Hk as [[Hk Hne] | Hk].
  - assert (HkA : In (p2, k) blA) by exact (OAb _ Hk).
    assert (HkB : In (p2, k) bl') by (apply (proj2 (HB' (p2, k))); left; split; [exact HkA | exact Hne]).
    pose proof (spcb_fb_same rs bl' p2 k n Hrs SB PB HkB Hn2) as E. rewrite E in HkA.
    exact (proj2 (Hp12A _ HkA Hne) eq_refl).
  - injection Hk as E1 E2. exact (Hp12 (eq_sym E1)). }
split.
{ intros pn H0 HnO.
  assert (HnF : ~ In pn F) by (intros Hf; exact (HnO (HFO _ Hf))).
  assert (HpA : In pn blA) by exact (InA pn H0 HnF).
  assert (Hold' : fst pn <> old).
  { intros E. destruct pn as [a k]. cbn [fst] in E. exact (KEPTR _ H0 HnO (OLDR a k HpA E)). }
  assert (HpB : In pn bl') by (apply (proj2 (HB' pn)); left; split; assumption).
  split; [exact HpB|].
  destruct pn as [a k]. cbn [fst snd].
  apply (spcb_fb_apart rs bl' a k p2 n Hrs SB PB HpB Hn2).
  exact (proj2 (Hp12A _ HpA Hold')). }
intros pn Hpn. apply (proj1 (HB' pn)) in Hpn. destruct Hpn as [[HpA Hne] | [-> | ->]].
- apply (proj1 (HA pn)) in HpA. destruct HpA as [[H0 HnF] | [-> | ->]].
  + destruct (spcb_fb_in_dec pn O) as [Hi|Hi]; [right; left | left; split; assumption].
    apply (proj2 (HO' pn)). left. split; [|exact Hne]. apply (proj2 (HOA pn)). left. apply (proj2 (HO0 pn)).
    split; assumption.
  + right; left. apply (proj2 (HO' b1)). left. split; [|exact Hne]. apply (proj2 (HOA b1)). right. left. reflexivity.
  + right; left. apply (proj2 (HO' b2)). left. split; [|exact Hne]. apply (proj2 (HOA b2)). right. right. reflexivity.
- right; left. apply (proj2 (HO' (p1, n))). right. reflexivity.
- right; right. reflexivity.
Qed.

(* ---------- the record's shadow checks (lib/B/Prog/CmdChk.v) as AR facts: the B twins of lib/A/Prog/CmdRecBase.v's
   crf_zallf_ok, crf_cell_byte_ok, crf_cells_byte_ok, crf_zsh_hit_ok, cmd_byte_ok, cmd_addressable_chk and
   cmd_hull_vis_chk (a working branch 996e65731ba, lines 36-83 and 412-438), which a Theorem Labs lane does not state ---------- *)
Lemma spcb_zallf_ok : forall f k lo, crf_zallf f lo k = true -> forall x, lo <= x < lo + Z.of_nat k -> f x = true.
Proof.
intros f k. induction k as [|k IH]; intros lo H x Hx; [lia|].
cbn [crf_zallf] in H. apply andb_prop in H as [H1 H2].
destruct (Z.eq_dec x lo) as [->|Hne]; [exact H1|]. apply (IH (lo + 1) H2). lia.
Qed.

Lemma spcb_cell_byte_ok : forall B ly (rd : reader) c a v, cell_holds B ly rd c -> crf_cell_byte c a = Some v -> rd a = Some v.
Proof.
intros B ly rd [ca cw cv] a v Hc H. destruct ca; try (cbn in H; discriminate).
destruct cv as [e|m w]; [|cbn in H; discriminate]. destruct e; try (cbn in H; discriminate).
cbn [crf_cell_byte] in H.
destruct ((z <=? a) && (a <? z + Z.of_nat cw)) eqn:E; [|cbn in H; discriminate]. injection H as <-.
apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
unfold cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
specialize (Hc (Z.to_nat (a - z)) ltac:(lia)). rewrite Z2Nat.id in Hc by lia.
replace (z + (a - z)) with a in Hc by lia. exact Hc.
Qed.

Lemma spcb_cells_byte_ok : forall B ly (rd : reader) l a v,
Forall (cell_holds B ly rd) l -> crf_cells_byte l a = Some v -> rd a = Some v.
Proof.
intros B ly rd l a v Hl. induction Hl as [|c t Hc Ht IH]; cbn [crf_cells_byte]; [discriminate|].
destruct (crf_cell_byte c a) as [w|] eqn:E; [intros Hw; injection Hw as <-; exact (spcb_cell_byte_ok B ly rd c a w Hc E) | exact IH].
Qed.

Lemma spcb_zsh_hit_ok : forall (rd : reader) l s,
Forall (fun r => zero_shadow rd SHADOW_OFF (fst r) (snd r)) l -> crf_zsh_hit l s = true -> rd s = Some 0.
Proof.
intros rd l s Hl H. unfold crf_zsh_hit in H. apply existsb_exists in H as (r & Hr & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (proj1 (Forall_forall _ _) Hl r Hr (s - shadow_of_addr SHADOW_OFF (fst r)) ltac:(lia)) as HZ.
replace (shadow_of_addr SHADOW_OFF (fst r) + (s - shadow_of_addr SHADOW_OFF (fst r))) with s in HZ by lia. exact HZ.
Qed.

Section chk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HB : CmdBSyms B.
(* AR shows the byte the record pins *)
Lemma spcb_byte_ok : forall ly S (W : world segs) mem md a v, AR segs B ly S W mem md -> cmd_byte a = Some v ->
aview segs (w_H W) mem a = Some v.
Proof.
intros ly S W mem md a v HAR. unfold cmd_byte. destruct (crf_zsh_hit Tfib_zero_shadow a) eqn:E.
- intros Hv; injection Hv as <-. apply (spcb_zsh_hit_ok _ Tfib_zero_shadow a); [|exact E].
  apply Forall_forall. intros r Hr. exact (cmd_zshadow_rec segs B LAWS HB ly S W mem md r HAR Hr).
- apply (spcb_cells_byte_ok B ly). pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite (ts_const B HB ly) in HC.
  unfold Tfib_const in HC. apply Forall_app in HC as [_ HC]. exact HC.
Qed.
Lemma spcb_addressable_chk : forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md -> cmd_addr_b a n = true ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR H x Hx. pose proof (spcb_zallf_ok _ _ _ H x ltac:(lia)) as Hb. cbn beta in Hb.
destruct (cmd_byte (shadow_of_addr SHADOW_OFF x)) as [s|] eqn:E; [|cbn in Hb; discriminate].
exists s. split; [exact (spcb_byte_ok ly S W mem md _ s HAR E)|].
unfold crf_saddr_okb in Hb. unfold saddr_ok. apply orb_prop in Hb as [Hb|Hb].
- left. apply Z.eqb_eq. exact Hb.
- right. apply andb_prop in Hb as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma spcb_hull_vis_chk : forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md -> cmd_hull_b a n = true ->
shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof.
intros ly S W mem md x n HAR H s Hs. pose proof (spcb_zallf_ok _ _ _ H s ltac:(lia)) as Hb. cbn beta in Hb.
destruct (cmd_byte s) as [v|] eqn:E; [|cbn in Hb; discriminate]. rewrite (spcb_byte_ok ly S W mem md s v HAR E). discriminate.
Qed.
End chk.

(* ---------- the two literals the walk hands on, against the record's checkers (closed computations) ---------- *)
Lemma spcb_verb_chk : cmd_addr_b 0x21ec0 (Z.of_nat (length spcb_verb) + 1) = true /\
  cmd_hull_b 0x21ec0 (Z.of_nat (length spcb_verb) + 1) = true.
Proof. split; vm_compute; reflexivity. Qed.
Lemma spcb_verb_end : In (0x21ec0 + Z.of_nat (length spcb_verb)) cmd_ro_ends.
Proof.
assert (H : existsb (Z.eqb (0x21ec0 + Z.of_nat (length spcb_verb))) cmd_ro_ends = true) by (vm_compute; reflexivity).
apply existsb_exists in H as (e & He & Hq). apply Z.eqb_eq in Hq. rewrite Hq. exact He.
Qed.
Lemma spcb_fmt_chk : cmd_addr_b 0x21f40 3 = true /\ cmd_hull_b 0x21f40 3 = true.
Proof. split; vm_compute; reflexivity. Qed.
Lemma spcb_fmt_end : In (0x21f40 + 2) cmd_ro_ends.
Proof.
assert (H : existsb (Z.eqb (0x21f40 + 2)) cmd_ro_ends = true) by (vm_compute; reflexivity).
apply existsb_exists in H as (e & He & Hq). apply Z.eqb_eq in Hq. rewrite Hq. exact He.
Qed.
(* the bytes of an image range none of the record's owned statics, by computation over Tfib_owned_static *)
Lemma spcb_unowned_rng : forall a n (l : list (Z * Z)),
forallb (fun r => (a + n <=? fst r) || (fst r + snd r <=? a)) l = true ->
forall i, 0 <= i < n -> ~ Exists (in_zr (a + i)) l.
Proof.
intros a n l Hb i Hi Hex. apply Exists_exists in Hex as (r & Hr & Hz).
rewrite forallb_forall in Hb. specialize (Hb r Hr). unfold in_zr in Hz.
apply orb_true_iff in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.
Lemma spcb_verb_unowned_b : forallb (fun r => (0x21ec0 + 12 <=? fst r) || (fst r + snd r <=? 0x21ec0)) Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.
Lemma spcb_fmt_unowned_b : forallb (fun r => (0x21f40 + 3 <=? fst r) || (fst r + snd r <=? 0x21f40)) Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

Section lit. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Lemma spcb_verb_unowned : forall a, 0x21ec0 <= a < 0x21ec0 + 12 ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB). unfold TFIB_ERRNO. split; [|lia].
replace a with (0x21ec0 + (a - 0x21ec0)) by lia. apply (spcb_unowned_rng 0x21ec0 12); [exact spcb_verb_unowned_b | lia].
Qed.
Lemma spcb_fmt_unowned : forall a, 0x21f40 <= a < 0x21f40 + 3 ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB). unfold TFIB_ERRNO. split; [|lia].
replace a with (0x21f40 + (a - 0x21f40)) by lia. apply (spcb_unowned_rng 0x21f40 3); [exact spcb_fmt_unowned_b | lia].
Qed.
(* the verb "pool_config" in the read-only arm of astr_argA (CmdRep.v), for any owned-block list: what rec_shape_of's
   string premise asks (rec_shape_of_c.v:92-95) *)
Lemma spcb_verb_argA : forall rlo rhi ly S (rd : reader) O, cmd_ro_ok rd -> cmd_ro_in (in_roP segs rlo rhi) ->
astr_argA B ly S rd (in_roP segs rlo rhi) O 0x21ec0 (Some spcb_verb).
Proof.
intros rlo rhi ly S rd O HRO HIN. cbn [astr_argA].
split; [lia|]. split; [exact (spcb_verb_str rd HRO)|]. split; [rewrite spcb_verb_len; unfold LMAX; lia|].
right. split; [|split; [exact (proj1 spcb_verb_chk) | split; [exact (proj2 spcb_verb_chk) | exact spcb_verb_end]]].
intros i Hi. rewrite spcb_verb_len in Hi. split; [exact (spcb_verb_ro _ HIN i Hi)|].
exact (spcb_verb_unowned (0x21ec0 + i) ltac:(lia)).
Qed.
End lit.


(* ---------- the recorder's representation along a walk: sup_reset's B walk helpers (a working branch
   c79a9f2daf7 lib/B/Prog/sup_reset.v:62-280, srb_ renamed spr_; spr_answer_slot generalised to any recorded call
   (fn, A)), the same CmdRep forms ---------- *)

Lemma spr_aval_keep : forall rd rd' a n v, aval_mem rd a n v ->
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma spr_bytes_keep : forall rd rd' a l, abytes_atR rd a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma spr_str_keep : forall rd rd' p s, astr_atR rd p s ->
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H1 H2] K. split; [|exact H2].
  apply (spr_bytes_keep rd); [exact H1|]. intros x Hx. apply K. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma spr_call_keep : forall bl bl' rd rd' a c P, acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) KA KP.
  unfold acall_at, CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj H6 _)))))).
  - apply (spr_aval_keep rd); [exact H4|]. intros x Hx. apply KA. lia.
  - apply (spr_aval_keep rd); [exact H5|]. intros x Hx. apply KA. lia.
  - intros k s pn Es Ep. destruct (H7 k s pn Es Ep) as (G1 & G2 & G3 & G4 & G5).
    assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
    destruct (KP pn ltac:(eapply nth_error_In; exact Ep)) as [Kin Kx].
    refine (conj _ (conj G2 (conj Kin (conj G4 _)))).
    + apply (spr_aval_keep rd); [exact G1|]. intros x Hx. apply KA. lia.
    + apply (spr_str_keep rd); [exact G5|]. intros x Hx. apply Kx. lia.
Qed.

Lemma spr_answer_keep : forall bl bl' rd rd' gr t q, aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  aanswer_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q H KA KP.
  destruct t as [x|]; destruct q as [pn|]; cbn [aanswer_at] in H |- *; try contradiction.
  - destruct H as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj N2 (conj Kin (conj N4 (conj _ N6))))).
    + apply (spr_aval_keep rd); [exact N1|]. intros y Hy. apply KA. lia.
    + apply (spr_str_keep rd); [exact N5|]. intros y Hy. apply Kx. lia.
  - apply (spr_aval_keep rd); [exact H|]. intros y Hy. apply KA. lia.
Qed.

Lemma spr_reply_keep : forall bl bl' rd rd' gr y q, areply_at bl rd gr y q ->
  (forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY + 16 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  areply_at bl' rd' gr y q.
Proof.
  intros bl bl' rd rd' gr y q H KA KP.
  destruct y as [x|]; destruct q as [pn|]; cbn [areply_at] in H |- *; try contradiction;
    unfold OFF_REPLY, OFF_REPLY_SIZE in *.
  - destruct H as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj _ (conj P3 (conj P4 (conj Kin (conj P6 (conj _ P8))))))).
    + apply (spr_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (spr_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
    + apply (spr_bytes_keep rd); [exact P7|]. intros z Hz. apply Kx. lia.
  - destruct H as [P1 P2]. split.
    + apply (spr_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (spr_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
Qed.

Lemma spr_scalars_keep : forall rd rd' gr R, ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R (X1 & X2 & X3 & X4 & X5 & X6) K.
  unfold ag1_scalars, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  all: apply (spr_aval_keep rd); [eassumption|]; intros z Hz; apply K; lia.
Qed.

Lemma spr_in_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
  intros Q i P pn E H. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
  split; [eapply nth_error_In; exact E | exact H].
Qed.

Lemma spr_in_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

Lemma spr_in_reply : forall Q pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
  intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

(* arep_at reads the reader only at g_rec, record.spill and the bytes of the recorder's own blocks, and the block
   list only at those blocks *)
Lemma spr_arep_at_ext : forall bl bl' rd rd' gr sc R Q,
  arep_at bl rd gr sc R Q ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl') ->
  (forall a, (gr <= a < gr + REC_SIZE) \/ (sc <= a < sc + SC_SIZE) \/
             (exists pn, In pn (lay_blocks Q) /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  arep_at bl' rd' gr sc R Q.
Proof.
  intros bl bl' rd rd' gr sc R Q (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & HX & HW) KL K.
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn bl' /\
             forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x).
  { intros pn Hpn. split; [exact (KL pn Hpn)|]. intros x Hx. apply K. right. right. exists pn.
    split; [exact Hpn | exact Hx]. }
  assert (KR : forall x, gr <= x < gr + REC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; left; exact Hx).
  assert (KS : forall x, sc <= x < sc + SC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; right; left; exact Hx).
  unfold REC_SIZE, SC_SIZE in KR, KS.
  refine (conj G1 (conj G2 (conj G3 (conj _ (conj _ (conj _ (conj _ HW))))))).
  - refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (spr_aval_keep rd); [exact C3|]. intros x Hx. apply KR. unfold OFF_NCALLS in Hx. lia.
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (spr_call_keep bl _ rd); [exact Hc | |].
      * intros x Hx. apply KR. unfold OFF_CALLS, CALL_SIZE in *. lia.
      * intros pn Hpn. apply KQ. exact (spr_in_calls Q i P pn EP Hpn).
    + apply (spr_call_keep bl _ rd); [exact C5 | |].
      * intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KQ. apply spr_in_spill. exact Hpn.
  - apply (spr_answer_keep bl _ rd); [exact HA | |].
    + intros x Hx. apply KR. unfold OFF_ANSWER in Hx. lia.
    + intros pn Hpn. apply KQ. apply rca_in_answer. exact Hpn.
  - apply (spr_reply_keep bl _ rd); [exact HP | |].
    + intros x Hx. apply KR. unfold OFF_REPLY in Hx. lia.
    + intros pn Hpn. apply KQ. apply spr_in_reply. exact Hpn.
  - apply (spr_scalars_keep rd); [exact HX|]. intros x Hx. apply KR. lia.
Qed.

(* the recorder's answer field holds 0 or the start of one of its blocks *)
Definition spr_old (Q : rlay) : Z := match l_answer Q with Some pn => fst pn | None => 0 end.

Lemma spr_old_at : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  aval_mem rd (A_G_REC + OFF_ANSWER) 8 (spr_old Q) /\ (forall pn, l_answer Q = Some pn -> In pn (lay_blocks Q)).
Proof.
  intros bl rd R Q (_ & _ & _ & _ & HA & _). unfold spr_old. split.
  - unfold aanswer_at in HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn|]; try contradiction;
    [exact (proj1 HA) | exact HA].
  - intros pn Hpn. unfold lay_blocks. rewrite Hpn. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    left. reflexivity.
Qed.

(* the slot record() returns (record_c.v rec_slot): an entry of g_rec's table, or record.spill *)
Lemma spr_slot_bounds : forall R, (length (r_calls R) <= 16)%nat ->
  (A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + REC_SIZE) \/ rec_slot R = A_REC_SPILL.
Proof.
  intros R H. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L]; [left | right; reflexivity].
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia.
Qed.

(* the slot fact answer's pre asks (answer_c.v:128-130), for any call (fn, A) record() put in the slot *)
Lemma spr_answer_slot : forall R fn A,
(exists k, nth_error (r_calls (rec_record R fn A)) k = Some (fn, A) /\
   rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
(rec_slot R = A_REC_SPILL /\ (fn, A) = r_spill (rec_record R fn A)).
Proof.
intros R fn A. unfold rec_slot, rec_record. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L].
- left. exists (length (r_calls R)). cbn [set_calls r_calls]. split; [|reflexivity].
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
- right. cbn [set_spill r_spill]. split; reflexivity.
Qed.

Lemma spr_pair_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Qed.

(* the program's statics of the record (lib/B/YF0m.v TFIB_PROG_STATIC): g_rec, record.spill, g_quitting *)
Lemma spr_grec_in : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof. intros a Ha. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_G_REC, REC_SIZE in Ha. lia. Qed.

Lemma spr_spill_in : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a Ha. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
unfold A_REC_SPILL, SC_SIZE in Ha. lia.
Qed.

(* the footprint of the statement (sup_reset_c.v:105) *)
Definition spr_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma spr_FP_pos : forall O, (forall pn, In pn O -> 0 < fst pn) -> Forall (fun r => 0 < fst r) (spr_FP O).
Proof.
intros O HO. unfold spr_FP. constructor; [cbn; unfold A_G_REC; lia|]. constructor; [cbn; unfold A_REC_SPILL; lia|].
unfold ablocks_fp. rewrite Forall_map. apply Forall_forall. intros pn Hpn. cbn. exact (HO pn Hpn).
Qed.

Print Assumptions spcb_model.
Print Assumptions spcb_snprintf_out.
Print Assumptions spcb_aint_arg.
Print Assumptions spcb_verb_str.
Print Assumptions spcb_verb_ro.
Print Assumptions spcb_fmt_str.
Print Assumptions spcb_fmt_ro.
Print Assumptions spcb_final_blocks.
