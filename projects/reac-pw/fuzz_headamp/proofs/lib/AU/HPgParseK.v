(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseL.v at afaa3cb55c1 (the engine plumbing
   of a segment of a parse walk: entry state, run / branch / exit tactics, the frame temporaries as region chunks), for
   reac_headamp_prop_parse_result's pair loop on reac-pw/fuzz_headamp's ASan + UBSan image B, its two segments WALK
   and ADV of lib/AU/HPgParseCut.v; the arithmetic both images share is lib/A/HPgParseGWalk.v's; the entry states,
   the inner cuts WLB / WRET, the exits, the strncmp call inside the frame hole and the walks below are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgParseW.v, with its module names and numbers changed; 1577 of its 1791 lines of code are new or changed and 1129 lines of the source are left out. *)
(* reac_headamp_prop_parse_result 0x849ac of reac-pw/fuzz_headamp's ASan + UBSan image B (fuzz_headamp.asan-ubsan,
   pinned sha256 53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94): segment KEY of its walk, from the
   cut KEY 0x84db0 (strncmp said the key at ck has the prefix) to ADV 0x84edc (a refusal) or VAL 0x84f0c (the key
   read as the cell address (ch, p)). It proves lib/AU/HPgParseCut.v's segKEY_stmt.
   Proves no function by itself (kind: segment lemma of reac_headamp_prop_parse_result).

   THE CODE (neutral listing of the pinned image):
     0x84db0 addiw a0,s9,1; 0x84db4 blt a0,s9 -> trap (keys + 1 <= the final keys <= |bs| <= 16384: not taken);
     0x84db8 sd a0,24(sp) (keys + 1); 0x84dc0 bgeu s8,-13 -> trap (the key lies in the pod, below 2^63: not taken);
     0x84dc4 s9 = s8 + 13 (the rest of the key); 0x84dc8 sb zero,4(s10) (the hole's byte 4: PAT_KEY -> PAT_DOT);
     0x84dcc sd zero,96(sp) (the end pointer's cell); a2 = 10, a0 = s9, a1 = sp + 96; 0x84ddc jal 0x41ca8 (strtol);
     0x84de0 s8 = a0 (the channel); a0 = [sp + 96] (dot); t0 = 4; 0x84dec beq dot,s9 -> 0x84e80 -> refusal;
     a4 = [sp + 40], a6 = 8, a7 = [sp + 48]; 0x84dfc beqz dot -> trap (dot is in the pod: not taken); the 1-byte
     instrumented check of dot (0x84e00 .. 0x84e0c, slow path 0x85184); 0x84e10 lbu; 0x84e18 bne '.' -> refusal;
     0x84e20 beq dot,-1 -> trap (not taken); s9 = dot + 1 (the name); strcmp(name, "phantom" 0x214c0) 0x84e34,
     "pad" 0x214e0 0x84e48, "sens" 0x21500 0x84e5c: equal -> (a3, a1) = (0, 1), (1, 1), (2, 0), else refusal 4;
     0x84eb0 bltu s8,48 -> 0x84f04 sb -8,4(s10) (PAT_KEY again) -> VAL 0x84f0c; else t0 = 5 -> refusal.
     Refusal 0x84ebc: sb -8,4(s10) (PAT_KEY); rf' = rf ? rf : t0 -> [sp + 32]; s8 = 0; s9 = [sp + 24] -> ADV.
   The engine (lib/Reusable's symbolic runs over the hole's journal, lib/A/HPgHole.v) walks the straight code between
   the cut and the local cuts of this file: pbK_ST_at (the strtol call), pbK_SC_at (the i-th strcmp call), pbK_RT_at
   (its return), pbK_CH_at (0x84eb0) and pbK_REF_at (0x84ebc). The runs that write the hole (KEY, CH, REF) are
   non-token runs over the temporaries and the hole region; the others are token runs with the walk segment's
   plumbing (lib/AU/HPgParseW.v). The calls go through HPgHole.hj_strtol_at (pbK_strtol_call) and hj_strcmp_at
   (pbK_strcmp_call). Section hypotheses: STRTOL / STRCMP (the wrappers' contracts at B_TRAMP_STRTOL 0x41ca8 with
   headamp_himg_B's hi_gotw / hi_guard, B_TRAMP_STRCMP 0x41c20), errno_low, HBerrno (as_errno B = 0x5d812c, image B's
   errno cell). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Spa Strtol Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require CType.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole HPgParseBase HPgParseGWalk HPgParseGKey HPgParseGKit.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgParseCut HPgParseW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= the model ======================================= *)
Lemma pbK_nth_app_nul : forall (l : list byte) i, (i <= length l)%nat ->
nth i (l ++ [Cursor.NUL]) Cursor.NUL = nth i l Cursor.NUL.
Proof.
intros l i H. destruct (Nat.eq_dec i (length l)) as [->|N].
- rewrite app_nth2, Nat.sub_diag by lia. cbn [nth]. rewrite (nth_overflow l) by lia. reflexivity.
- rewrite app_nth1 by lia. reflexivity.
Qed.

(* The key the String child at ck holds (lib/A/HPgParseGWalk.v hgw_key_bytes): a C string at offset ck + 8 of the pod
   with its NUL inside the pod. *)
Lemma pbK_kstr : forall (x : @hp_ctx rsegs) ck, hp_key_ok x ck ->
~ In Cursor.NUL (hp_kstr x ck) /\ ck + 8 + Z.of_nat (length (hp_kstr x ck)) + 1 <= hx_len x /\
(forall i, (i <= length (hp_kstr x ck))%nat ->
 nth (Z.to_nat (ck + 8) + i) (hx_bs x) Cursor.NUL = nth i (hp_kstr x ck ++ [Cursor.NUL]) Cursor.NUL).
Proof.
intros x ck HK. destruct (hgw_key_bytes x ck HK) as (HN & L1 & L2 & Hb & Hz).
split; [exact HN|]. split; [lia|].
intros i Hi. destruct (Nat.eq_dec i (length (hp_kstr x ck))) as [->|N].
- rewrite app_nth2, Nat.sub_diag by lia. cbn [nth]. apply bv_eq. rewrite Hz. reflexivity.
- rewrite app_nth1 by lia. apply Hb. lia.
Qed.

(* keys + 1 is at most the final keys, which is at most the pod's length *)
Lemma pbK_fold_after_keys : forall cap v rest cl keys rf,
keys + 1 <= snd (fst (hp_fold_after cap v rest cl keys rf)).
Proof.
intros cap v rest cl keys rf. unfold hp_fold_after. destruct v as [bad|cv].
- pose proof (Headamp.ha_fold_keys Headamp.parse_cell cap rest cl (keys + 1)
    (if rf =? Headamp.REFUSE_NONE then bad else rf)). lia.
- destruct (cap <=? Z.of_nat (length cl)); [cbn; lia|].
  pose proof (Headamp.ha_fold_keys Headamp.parse_cell cap rest (cl ++ [cv]) (keys + 1) rf). lia.
Qed.

Lemma pbK_keys_bound : forall bs cap o, Headamp.parse_model bs cap = Headamp.ha_result o ->
snd (fst o) <= Z.of_nat (length bs).
Proof.
intros bs cap [[cl keys] rf] H. pose proof (Headamp.parse_model_keys bs cap) as K. rewrite H in K.
unfold Headamp.ha_result in K. cbn [fst snd]. lia.
Qed.

(* a suffix of a C string held at offset o of bs is a C string at o + j *)
Lemma pbK_suffix : forall (bs s : list byte) (o j : nat),
(forall i, (i <= length s)%nat -> nth (o + i) bs Cursor.NUL = nth i (s ++ [Cursor.NUL]) Cursor.NUL) ->
(j <= length s)%nat ->
forall i, (i <= length (skipn j s))%nat ->
nth (o + j + i) bs Cursor.NUL = nth i (skipn j s ++ [Cursor.NUL]) Cursor.NUL.
Proof.
intros bs s o j H Hj i Hi. rewrite length_skipn in Hi. rewrite <- Nat.add_assoc, H by lia.
rewrite <- (firstn_skipn j s) at 1. rewrite <- app_assoc, app_nth2 by (rewrite length_firstn; lia).
rewrite length_firstn. f_equal. lia.
Qed.

(* the rest of the key after the prefix, k + 13, at offset ck + 21 of the pod *)
Definition pbK_str (x : @hp_ctx rsegs) (ck : Z) : list byte := skipn 13 (hp_kstr x ck).

Lemma pbK_str_pod : forall (x : @hp_ctx rsegs) ck, hp_key_ok x ck -> Headamp.ha_prefix (hp_kstr x ck) = true ->
~ In Cursor.NUL (pbK_str x ck) /\ ck + 21 + Z.of_nat (length (pbK_str x ck)) + 1 <= hx_len x /\
(forall i, (i <= length (pbK_str x ck))%nat ->
 nth (Z.to_nat (ck + 21) + i) (hx_bs x) Cursor.NUL = nth i (pbK_str x ck ++ [Cursor.NUL]) Cursor.NUL).
Proof.
intros x ck HK HP. pose proof HK as (Hck & _).
destruct (pbK_kstr x ck HK) as (HN & HL & HB). pose proof (hgk_prefix_len _ HP) as H13.
unfold pbK_str. split; [apply hgk_nonul_skipn; exact HN|].
split; [rewrite length_skipn; lia|].
intros i Hi. replace (Z.to_nat (ck + 21) + i)%nat with (Z.to_nat (ck + 8) + 13 + i)%nat by lia.
apply pbK_suffix; [exact HB | lia | exact Hi].
Qed.

(* bytes of a string inside the pod, through the view of a memory that holds the pod *)
Lemma pbK_pod_view : forall H mem P (bs : list byte) o (s : list byte),
garr8 rsegs (mrestrict H mem) P (hd_zbytes bs) -> 0 <= o ->
o + Z.of_nat (length s) + 1 <= Z.of_nat (length bs) ->
(forall i, (i <= length s)%nat -> nth (Z.to_nat o + i) bs Cursor.NUL = nth i (s ++ [Cursor.NUL]) Cursor.NUL) ->
forall i, (i < length (s ++ [Cursor.NUL]))%nat ->
aview rsegs H mem (P + o + Z.of_nat i) = Some (bv_unsigned (nth i (s ++ [Cursor.NUL]) Cursor.NUL)).
Proof.
intros H mem P bs o s HG Ho Hl Hs i Hi. rewrite length_app in Hi. cbn [length] in Hi.
assert (Hj : (Z.to_nat o + i < length (hd_zbytes bs))%nat) by (unfold hd_zbytes; rewrite length_map; lia).
unfold aview. replace (P + o + Z.of_nat i) with (P + Z.of_nat (Z.to_nat o + i)) by lia.
rewrite (garr8_mbyte rsegs _ _ _ _ HG Hj). cbn [option_map]. rewrite hgw_nth_zbytes, Z_to_bv_bv_unsigned.
rewrite Hs by lia. reflexivity.
Qed.

(* ======================================= the local cuts ======================================= *)
(* the pcs inside the segment: the strtol call's return, the channel test, the refusal *)
Definition PC_AFTER_STRTOL : Z := 0x84de0.
Definition PC_CH : Z := 0x84eb0.
Definition PC_REF : Z := 0x84ebc.
(* the three strcmp calls: the literal (a1), the name it stands for, the return address *)
Definition pbK_lit (i : nat) : Z := nth i [hi_aph headamp_himg_B; hi_apad headamp_himg_B; hi_asens headamp_himg_B] 0.
Definition pbK_lnm (i : nat) : list byte := nth i [Headamp.NAME_PHANTOM; Headamp.NAME_PAD; Headamp.NAME_SENS] [].
Definition pbK_ret (i : nat) : Z := nth i [0x84e38; 0x84e4c; 0x84e60] 0.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Notation pctx := (@hp_ctx rsegs).

Definition pbK_rb0 : list byte := ha_res_bytes 0 0 0.
(* the rest of the key (strtol's string) at P + ck + 21, strtol's end offset and value, the name after the dot *)
Definition pbK_xs (x : pctx) (ck : Z) : Z := hx_P x + ck + 21.
Definition pbK_e (x : pctx) (ck : Z) : Z := PIS.s10_end (pbK_str x ck).
Definition pbK_ch (x : pctx) (ck : Z) : Z := PIS.s10_val (pbK_str x ck).
Definition pbK_nm (x : pctx) (ck : Z) : list byte := skipn (S (Z.to_nat (pbK_e x ck))) (pbK_str x ck).
Definition pbK_y (x : pctx) (ck : Z) : Z := pbK_xs x ck + pbK_e x ck + 1.

(* 0x84ebc: a refusal bad (t0) of the key at ck; the hole's pattern is PAT_DOT *)
Definition pbK_REF_at (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf bad : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_DOT cl pbK_rb0 regs mem md /\ hp_fxw F fc /\ hp_m_key x r cc n ck cl keys rf /\
Headamp.parse_cell (hp_kstr x ck) (Spa.child_at (hx_bs x) cc) = inl bad /\ 0 <= bad <= 5 /\
pb_loop x r cl rf regs mem /\ pb_a46 x r regs /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 5 = w64 bad /\ getr regs 17 = w64 (shadow_addr (hx_P x + cc)) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 24) 8 (keys + 1).

(* 0x84eb0: the name was the param p; s8 = strtol's value, the channel test next *)
Definition pbK_CH_at (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf p : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_DOT cl pbK_rb0 regs mem md /\ hp_fxw F fc /\ hp_m_key x r cc n ck cl keys rf /\
Headamp.parse_key (pbK_str x ck) =
  (if (pbK_ch x ck <? 0) || (Headamp.REAC_HEADAMP_MAX_CH <=? pbK_ch x ck) then Headamp.KRange
   else Headamp.KCell (pbK_ch x ck) p) /\
0 <= p <= Headamp.HA_SENS /\
pb_loop x r cl rf regs mem /\ pb_a46 x r regs /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 24 = w64 (pbK_ch x ck) /\ getr regs 13 = w64 p /\
getr regs 11 = w64 (if p =? Headamp.HA_SENS then 0 else 1) /\ getr regs 17 = w64 (shadow_addr (hx_P x + cc)) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 24) 8 (keys + 1) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)).

(* B_TRAMP_STRCMP: the i-th strcmp call, the name at y = dot + 1 against the i-th literal *)
Definition pbK_SC_at (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z) (i : nat)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_DOT cl pbK_rb0 regs mem md /\ hp_fxw F fc /\ hp_m_key x r cc n ck cl keys rf /\
(i < 3)%nat /\ pbK_e x ck <> 0 /\
bv_unsigned (nth (Z.to_nat (pbK_e x ck)) (pbK_str x ck) Cursor.NUL) = 46 /\
(forall j, (j < i)%nat -> pbK_nm x ck <> pbK_lnm j) /\
pb_loop x r cl rf regs mem /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 24 = w64 (pbK_ch x ck) /\ getr regs 25 = w64 (pbK_y x ck) /\
getr regs 10 = w64 (pbK_y x ck) /\ getr regs 11 = w64 (pbK_lit i) /\ getr regs 1 = w64 (pbK_ret i) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 24) 8 (keys + 1) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)).

(* B_TRAMP_STRTOL: strtol(k + 13, sp + 96, 10), the end pointer's cell zeroed, the hole at PAT_DOT *)
Definition pbK_ST_at (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_DOT cl pbK_rb0 regs mem md /\ hp_fxw F fc /\ hp_m_key x r cc n ck cl keys rf /\
pb_loop x r cl rf regs mem /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 25 = w64 (pbK_xs x ck) /\
getr regs 10 = w64 (pbK_xs x ck) /\ getr regs 11 = w64 (hx_spa x + 0x60) /\ getr regs 12 = w64 10 /\
getr regs 1 = w64 PC_AFTER_STRTOL /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 24) 8 (keys + 1) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)).

Definition pbK_REF_ok (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
forall bad F fc regs mem md, pbK_REF_at x r cc n ck cl keys rf bad F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_REF regs mem md) (PPOST B MT x).
Definition pbK_CH_ok (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
forall p F fc regs mem md, pbK_CH_at x r cc n ck cl keys rf p F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_CH regs mem md) (PPOST B MT x).
Definition pbK_SC_ok (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z) (i : nat) : Prop :=
forall F fc regs mem md, pbK_SC_at x r cc n ck cl keys rf i F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs B_TRAMP_STRCMP regs mem md) (PPOST B MT x).
Definition pbK_ST_ok (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
forall F fc regs mem md, pbK_ST_at x r cc n ck cl keys rf F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs B_TRAMP_STRTOL regs mem md) (PPOST B MT x).

(* ---------------------------------- the model at each way out ---------------------------------- *)
Lemma pbK_cell_key : forall (x : pctx) ck v,
Headamp.parse_cell (hp_kstr x ck) v =
match Headamp.parse_key (pbK_str x ck) with
| Headamp.KBad => inl Headamp.REFUSE_BAD_KEY
| Headamp.KRange => inl Headamp.REFUSE_OUT_OF_RANGE
| Headamp.KCell ch p => hp_vcell ch p v
end.
Proof. intros x ck v. reflexivity. Qed.

Lemma pbK_cell_bad : forall (x : pctx) ck v, Headamp.parse_key (pbK_str x ck) = Headamp.KBad ->
Headamp.parse_cell (hp_kstr x ck) v = inl 4.
Proof. intros x ck v H. rewrite pbK_cell_key, H. reflexivity. Qed.

Lemma pbK_cell_range : forall (x : pctx) ck v, Headamp.parse_key (pbK_str x ck) = Headamp.KRange ->
Headamp.parse_cell (hp_kstr x ck) v = inl 5.
Proof. intros x ck v H. rewrite pbK_cell_key, H. reflexivity. Qed.

(* the key after a dot and a name: the name is a C string, so cstr leaves it *)
Lemma pbK_key_named : forall (x : pctx) ck,
~ In Cursor.NUL (pbK_str x ck) -> pbK_e x ck <> 0 ->
bv_unsigned (nth (Z.to_nat (pbK_e x ck)) (pbK_str x ck) Cursor.NUL) = 46 ->
Headamp.parse_key (pbK_str x ck) =
match Headamp.param_of_name (pbK_nm x ck) with
| None => Headamp.KBad
| Some p => if (pbK_ch x ck <? 0) || (Headamp.REAC_HEADAMP_MAX_CH <=? pbK_ch x ck) then Headamp.KRange
            else Headamp.KCell (pbK_ch x ck) p
end.
Proof.
intros x ck HN H1 H2. unfold pbK_e, pbK_nm, pbK_ch in *. rewrite (hgk_key_name _ H1 H2).
rewrite (hgk_cstr_nonul _ (hgk_nonul_skipn _ _ HN)). reflexivity.
Qed.

(* keys + 1 stays below 2^31 (the overflow trap at 0x84db4) *)
Lemma pbK_keys_small : forall (x : pctx) r cc n ck cl keys rf,
hp_m_key x r cc n ck cl keys rf -> Z.of_nat (length (hx_bs x)) <= 16384 -> 0 <= keys /\ keys + 1 <= 16384.
Proof.
intros x r cc n ck cl keys rf (_ & _ & _ & _ & _ & _ & _ & (_ & Hk & _) & _ & HW) Hlen.
pose proof (pbK_keys_bound (hx_bs x) (hx_cap x) _ HW) as K. pose proof (pbK_fold_after_keys (hx_cap x)
  (Headamp.parse_cell (hp_kstr x ck) (Spa.child_at (hx_bs x) cc))
  (hp_walk_pairs (hx_bs x) r (hp_next x cc) n None) cl keys rf) as K2. lia.
Qed.

End k.

(* the 8 bytes at gotw and at guard lie in image B's segments *)
Lemma pbK_guard_img : forall i, 0 <= i < 8 ->
in_img rsegs (hi_gotw headamp_himg_B + i) /\ in_img rsegs (hi_guard headamp_himg_B + i).
Proof.
intros i Hi. split; (apply (HPgSat.img_chk_ok rsegs _ 8); [vm_compute; reflexivity | lia]).
Qed.

Lemma pbK_rom_img : forall a, in_rom rsegs a -> in_img rsegs a.
Proof. intros a (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.
Hypothesis HBerrno : as_errno B = 0x5d812c.
Hypothesis STRTOL : forall F fc, hd_astrtol_hole (fx := mkFP F fc) rsegs B B_TRAMP_STRTOL (hi_gotw headamp_himg_B)
  (hi_guard headamp_himg_B).
Hypothesis STRCMP : forall F fc, hd_astrcmp_hole (fx := mkFP F fc) rsegs B B_TRAMP_STRCMP.
Local Notation pctx := (@hp_ctx rsegs).

(* strtol(k + 13, sp + 96, 10) at B_TRAMP_STRTOL, from the cut's journal and the pod's bytes, shadow and hull at the
   call's memory and the image's bytes as at the parse's call *)
Lemma pbK_strtol_call : forall (x : pctx) r cc n ck cl keys rf F fc regsT memT mdT (Q : world rsegs -> config -> Prop),
call_ok B x -> hp_m_key x r cc n ck cl keys rf ->
hjournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) memT mdT (hx_k x) (hx_fr x) PAT_DOT ->
spZ regsT = hx_spa x -> getr regsT 3 = getr (hx_regs x) 3 -> getr regsT 4 = getr (hx_regs x) 4 ->
getr regsT 10 = w64 (pbK_xs x ck) -> getr regsT 11 = w64 (hx_spa x + 0x60) -> getr regsT 12 = w64 10 ->
getr regsT 1 = w64 PC_AFTER_STRTOL ->
garr8 rsegs (hx_rd x memT) (hx_P x) (hd_zbytes (hx_bs x)) ->
range_addressable (hx_view x memT) SHADOW_OFF (hx_P x) (hx_len x) ->
shadow_hull_vis (hx_view x memT) (hx_P x) (hx_len x) ->
(forall a, in_img rsegs a -> ~ (as_errno B <= a < as_errno B + 4) -> hx_view x memT a = hx_view x (hx_memc x) a) ->
(exists ev, rd32 (hx_view x memT) (as_errno B) ev) ->
(forall regs2 mem2 md2,
 hjournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
   (hx_lyc x) (hx_Sc x) (hx_W x) mem2 md2 (hx_k x) (hx_fr x) PAT_DOT ->
 aregs_preserved regsT regs2 -> same_io mdT md2 ->
 getr regs2 10 = w64 (pbK_ch x ck) ->
 rdword (hx_view x mem2) (hx_spa x + 0x60) = Some (pbK_xs x ck + pbK_e x ck) ->
 (exists ev', rd32 (hx_view x mem2) (as_errno B) ev') ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 0x60 <= a < hx_spa x + 0x68) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (hx_spa x - 3 * ESTACK <= a < hx_spa x) -> hx_view x mem2 a = hx_view x memT a) ->
 SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_AFTER_STRTOL regs2 mem2 md2) Q) ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs B_TRAMP_STRTOL regsT memT mdT) Q.
Proof.
intros x r cc n ck cl keys rf F fc regsT memT mdT Q Hc HK HJ Hsp R3 R4 R10 R11 R12 R1 HGp HRAp HHVp HIMG [ev HEV] HQ.
pose proof Hc as (HPRE & _ & _ & _ & _ & _ & HARGS).
pose proof HPRE as (HJc & _ & _ & Hgp & Htp & _ & _ & Hw2 & _).
pose proof HK as (Hnull & _ & _ & _ & _ & _ & HKo & _ & HPfx & _).
destruct HARGS as (Hpod & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgd & _ & Haro & _).
destruct (Hpod Hnull) as (HP0 & HP16 & Hlen & Hlen8 & _ & HP63 & _ & _ & _ & _ & HPE & _ & _ & HAM & HOFF).
pose proof (hd_parse_frame rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPRE) as (F32 & F1 & F2 & F2' & F3 & F4 & F16 & S16).
fold (hx_sp x) in F1, F2, F2', F3, F4, F32, F16. fold (hx_spa x) in F1, F2, F2', F3, F4, F32, F16.
fold (hx_fr x) in F3, F4. fold (hx_sp x) in Hw2.
pose proof HJc as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (am_layout B _ _ _ (proj1 HAR)) as LO. pose proof (lo_img _ LO) as (I1 & _ & I3 & _).
destruct (pbK_str_pod x ck HKo HPfx) as (HNs & HLs & HBs).
pose proof HKo as (Hck & _).
unfold hx_len in *. unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. unfold hd_fr in *. unfold hx_sp in *.
unfold hd_off_stack in HOFF.
set (xs := pbK_xs x ck) in *. set (str := pbK_str x ck) in *. set (spa := hx_spa x) in *.
assert (Exs : xs = hx_P x + (ck + 21)) by (subst xs; unfold pbK_xs; lia).
assert (Hwin : forall a, hx_P x <= a < hx_P x + Z.of_nat (length (hx_bs x)) -> ~ (spa - 3 * 4096 <= a < spa)).
{ intros a Ha Hw. apply (HOFF a Ha). lia. }
assert (HSB : forall i, (i < length (str ++ [Z_to_bv 8 0]))%nat ->
  aview rsegs (w_H (hx_W x)) memT (xs + Z.of_nat i) = Some (bv_unsigned (nth i (str ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)))).
{ intros i Hi. rewrite Exs. apply (pbK_pod_view _ _ _ (hx_bs x) _ str HGp); [lia | lia | exact HBs | exact Hi]. }
eapply SRr_bind.
{ apply (hj_strtol_at (fx := mkFP F fc) rsegs B pb_segs_low errno_low B_TRAMP_STRTOL _ _ (STRTOL F fc) (hx_W x) regsT memT
    (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x) (hx_lyc x)
    (hx_Sc x) mdT (hx_k x) xs (spa + 0x60) str ev (spa - hx_sp0 x) (w64 PC_AFTER_STRTOL) (hx_fr x) PAT_DOT HJ
    R10 R11 R12); unfold ESTACK.
  - lia.
  - lia.
  - lia.
  - rewrite Zminus_mod, F16, S16. reflexivity.
  - lia.
  - lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply ret_ok_even. vm_compute. reflexivity.
  - destruct Hgd as (G1 & can & G2). split.
    + refine (hk_rdword_kept (aview rsegs (w_H (hx_W x)) (hx_memc x)) _ (hi_gotw headamp_himg_B) _ _ G1).
      intros i Hi. apply HIMG; [exact (proj1 (pbK_guard_img i Hi))|]. rewrite HBerrno. cbn. lia.
    + exists can.
      refine (hk_rdword_kept (aview rsegs (w_H (hx_W x)) (hx_memc x)) _ (hi_guard headamp_himg_B) _ _ G2).
      intros i Hi. apply HIMG; [exact (proj2 (pbK_guard_img i Hi))|]. rewrite HBerrno. cbn. lia.
  - split; [exact HSB | exact HNs].
  - lia.
  - split; [lia|]. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - replace a with (xs + Z.of_nat (Z.to_nat (a - xs))) by lia. rewrite HSB; [discriminate|].
        rewrite length_app. cbn [length]. lia.
      - rewrite Hsp. apply Hwin. lia. }
    split; [destruct HAM as [HA|[HA1 HA2]]; [left; lia | right; lia]|].
    split; [intros y Hy; apply HRAp; lia|].
    intros _. apply (hk_hull_sub _ (hx_P x) (Z.of_nat (length (hx_bs x)))); [exact HHVp | lia | lia | lia].
  - destruct HAM as [HA|[HA1 HA2]]; [left; lia | right; lia].
  - apply (hgw_str_tail (w_H (hx_W x)) memT (hx_P x) (hd_zbytes (hx_bs x))); [exact HGp | lia | | ].
    + unfold hd_zbytes. rewrite length_map. exact Hlen8.
    + unfold hd_zbytes. rewrite length_map. lia.
  - lia.
  - lia.
  - lia.
  - right. unfold kHighMemBeg, kHighMemEnd in *. lia.
  - pose proof (hd_dot_ok rsegs B _ _ _ _ _ _ (hj_AR rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) F3 F4) as [D1 _].
    unfold hx_fr, hd_fr in D1. replace (spa + 0x60) with (spa + 64 + 32) by lia. exact D1.
  - pose proof (hd_dot_ok rsegs B _ _ _ _ _ _ (hj_AR rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) F3 F4) as [_ D2].
    unfold hx_fr, hd_fr in D2. replace (spa + 0x60) with (spa + 64 + 32) by lia. exact D2.
  - destruct (Z_le_gt_dec (spa + 0x60 + 8) xs) as [D|D]; [left; exact D|].
    destruct (Z_le_gt_dec (xs + Z.of_nat (length str) + 1) (spa + 0x60)) as [D'|D']; [right; exact D'|].
    exfalso. apply (HOFF (Z.max xs (spa + 0x60))); lia.
  - right. rewrite HBerrno. lia.
  - apply Z.mod_divide in F32 as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 32 + 0x60) with ((4 * q + 12) * 8) by lia. apply Z.mod_mul. lia.
  - intros a Ha HI. unfold in_zr in HI. rewrite I1 in HI. unfold kImgLo, kImgEnd in *. lia.
  - rewrite HBerrno in HPE |- *. lia.
  - exact HEV.
  - intros a Ha Hst He. pose proof (HIMG a (pbK_rom_img a Ha) He) as E. unfold hx_view in E. rewrite E.
    apply Haro; [left; exact Ha | exact Hst | exact He]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPr & Hio & H10 & Hend & Herr & HK2 & _).
apply (HQ regs2 mem2 md2 HJ2 HPr Hio H10 Hend (ex_intro _ _ Herr)).
intros a Ha H1 H2 H3. apply HK2; [exact Ha | lia | exact H2 | unfold ESTACK; lia].
Qed.

(* the name after the dot: a C string at P + ck + 21 + e + 1 inside the pod *)
Lemma pbK_nm_pod : forall (x : pctx) ck, hp_key_ok x ck -> Headamp.ha_prefix (hp_kstr x ck) = true ->
pbK_e x ck <> 0 -> bv_unsigned (nth (Z.to_nat (pbK_e x ck)) (pbK_str x ck) Cursor.NUL) = 46 ->
~ In Cursor.NUL (pbK_nm x ck) /\ 0 < pbK_e x ck < Z.of_nat (length (pbK_str x ck)) /\
ck + 21 + pbK_e x ck + 1 + Z.of_nat (length (pbK_nm x ck)) + 1 <= hx_len x /\
(forall i, (i <= length (pbK_nm x ck))%nat ->
 nth (Z.to_nat (ck + 21 + pbK_e x ck + 1) + i) (hx_bs x) Cursor.NUL = nth i (pbK_nm x ck ++ [Cursor.NUL]) Cursor.NUL).
Proof.
intros x ck HKo HPfx He0 Hdot. pose proof HKo as (Hck & _).
destruct (pbK_str_pod x ck HKo HPfx) as (HNs & HLs & HBs).
pose proof (hgk_end_le (pbK_str x ck)) as HE. fold (pbK_e x ck) in HE.
assert (Hlt : (Z.to_nat (pbK_e x ck) < length (pbK_str x ck))%nat).
{ destruct (Nat.lt_ge_cases (Z.to_nat (pbK_e x ck)) (length (pbK_str x ck))) as [L|L]; [exact L|].
  rewrite nth_overflow in Hdot by exact L. vm_compute in Hdot. discriminate Hdot. }
unfold pbK_nm. split; [apply hgk_nonul_skipn; exact HNs|]. split; [lia|].
split; [rewrite length_skipn; lia|].
intros i Hi. replace (Z.to_nat (ck + 21 + pbK_e x ck + 1) + i)%nat
  with (Z.to_nat (ck + 21) + S (Z.to_nat (pbK_e x ck)) + i)%nat by lia.
apply pbK_suffix; [exact HBs | lia | exact Hi].
Qed.

Lemma pbK_lit_cstr : forall (x : pctx) i, call_ok B x -> (i < 3)%nat ->
hd_cstr rsegs (w_H (hx_W x)) (hx_memc x) (pbK_lit i) (hd_zbytes (pbK_lnm i)).
Proof.
intros x i Hc Hi. destruct Hc as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & Hph & Hpad & Hsens & _)).
destruct i as [|[|[|i]]]; [exact Hph | exact Hpad | exact Hsens | lia].
Qed.

(* each literal's 16 bytes lie in image B's segments, far from the errno cell *)
Lemma pbK_lit_img : forall i b, (i < 3)%nat -> pbK_lit i <= b < pbK_lit i + 16 ->
in_img rsegs b /\ ~ (0x5d812c <= b < 0x5d812c + 4).
Proof.
intros i b Hi Hb. split; [|destruct i as [|[|[|i]]]; cbn [pbK_lit nth hi_aph hi_apad hi_asens headamp_himg_B] in Hb; lia].
destruct i as [|[|[|i]]]; [| | | lia]; cbn [pbK_lit nth hi_aph hi_apad hi_asens headamp_himg_B] in Hb;
match type of Hb with ?l <= _ < _ => replace b with (l + (b - l)) by lia; apply (HPgSat.img_chk_ok rsegs l 16);
  [vm_compute; reflexivity | lia] end.
Qed.

(* the i-th strcmp(name, literal) at B_TRAMP_STRCMP, from the cut's journal, the pod at the call's memory and the
   literal's facts there; a0 is 0 exactly when the name is the literal's *)
Lemma pbK_strcmp_call : forall (x : pctx) r cc n ck cl keys rf (i : nat) F fc regsT memT mdT
  (Q : world rsegs -> config -> Prop),
call_ok B x -> hp_m_key x r cc n ck cl keys rf -> (i < 3)%nat ->
pbK_e x ck <> 0 -> bv_unsigned (nth (Z.to_nat (pbK_e x ck)) (pbK_str x ck) Cursor.NUL) = 46 ->
hjournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) memT mdT (hx_k x) (hx_fr x) PAT_DOT ->
spZ regsT = hx_spa x -> getr regsT 3 = getr (hx_regs x) 3 -> getr regsT 4 = getr (hx_regs x) 4 ->
getr regsT 10 = w64 (pbK_y x ck) -> getr regsT 11 = w64 (pbK_lit i) -> getr regsT 1 = w64 (pbK_ret i) ->
garr8 rsegs (hx_rd x memT) (hx_P x) (hd_zbytes (hx_bs x)) ->
range_addressable (hx_view x memT) SHADOW_OFF (hx_P x) (hx_len x) ->
shadow_hull_vis (hx_view x memT) (hx_P x) (hx_len x) ->
hd_cstr rsegs (w_H (hx_W x)) memT (pbK_lit i) (hd_zbytes (pbK_lnm i)) ->
(forall regs2 mem2 md2 v,
 hjournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
   (hx_lyc x) (hx_Sc x) (hx_W x) mem2 md2 (hx_k x) (hx_fr x) PAT_DOT ->
 aregs_preserved regsT regs2 -> same_io mdT md2 ->
 getr regs2 10 = w64 v -> -1 <= v <= 1 -> (v = 0 <-> pbK_nm x ck = pbK_lnm i) ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x - 2 * ESTACK <= a < hx_spa x) -> hx_view x mem2 a = hx_view x memT a) ->
 SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs (pbK_ret i) regs2 mem2 md2) Q) ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs B_TRAMP_STRCMP regsT memT mdT) Q.
Proof.
intros x r cc n ck cl keys rf i F fc regsT memT mdT Q Hc HK Hi He0 Hdot HJ Hsp R3 R4 R10 R11 R1 HGp HRAp HHVp HL HQ.
pose proof Hc as (HPRE & _ & _ & _ & _ & _ & HARGS).
pose proof HPRE as (HJc & _ & _ & Hgp & Htp & _ & _ & Hw2 & _).
pose proof HK as (Hnull & _ & _ & _ & _ & _ & HKo & _ & HPfx & _).
destruct HARGS as (Hpod & _).
destruct (Hpod Hnull) as (HP0 & HP16 & Hlen & Hlen8 & _ & HP63 & _ & _ & _ & _ & HPE & _ & _ & HAM & HOFF).
pose proof (hd_parse_frame rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPRE) as (F32 & F1 & F2 & F2' & F3 & F4 & F16 & S16).
fold (hx_sp x) in F1, F2, F2', F3, F4, F32, F16. fold (hx_spa x) in F1, F2, F2', F3, F4, F32, F16.
fold (hx_sp x) in Hw2.
pose proof HJc as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (pbK_nm_pod x ck HKo HPfx He0 Hdot) as (HNn & He & HLn & HBn).
pose proof HKo as (Hck & _).
assert (Ll : length (hd_zbytes (pbK_lnm i)) = length (pbK_lnm i)) by (unfold hd_zbytes; apply length_map).
assert (Ln : length (hd_zbytes (pbK_nm x ck)) = length (pbK_nm x ck)) by (unfold hd_zbytes; apply length_map).
pose proof HL as (Hlb & Hln & Hlf & Hl0 & Hlhi & Hlimg & Hlm8 & Hlra & Hlhv & _).
rewrite Ll in Hln, Hlhi, Hlimg, Hlm8, Hlra, Hlhv.
assert (Hlow : pbK_lit i + Z.of_nat (length (pbK_lnm i)) < kLowMemEnd)
  by (exact (proj2 (pb_segs_low _ (Hlimg (Z.of_nat (length (pbK_lnm i))) ltac:(lia))))).
unfold hx_len in *. unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. unfold hd_fr in *. unfold hx_sp in *.
unfold hd_off_stack in HOFF.
set (y := pbK_y x ck) in *. set (nm := pbK_nm x ck) in *. set (lit := pbK_lit i) in *. set (ln := pbK_lnm i) in *.
set (spa := hx_spa x) in *.
assert (Ey : y = hx_P x + (ck + 21 + pbK_e x ck + 1)) by (subst y; unfold pbK_y, pbK_xs; lia).
assert (HNB : forall j, (j < length (nm ++ [Cursor.NUL]))%nat ->
  aview rsegs (w_H (hx_W x)) memT (y + Z.of_nat j) = Some (bv_unsigned (nth j (nm ++ [Cursor.NUL]) Cursor.NUL))).
{ intros j Hj. rewrite Ey. apply (pbK_pod_view _ _ _ (hx_bs x) _ nm HGp); [lia | lia | exact HBn | exact Hj]. }
assert (HNC : hgk_cstr_at (segs := rsegs) (w_H (hx_W x)) memT y (hd_zbytes nm)).
{ split; [|split].
  - intros j Hj. rewrite Ln in Hj. replace (y + j) with (y + Z.of_nat (Z.to_nat j)) by lia.
    rewrite HNB by (rewrite length_app; cbn [length]; lia). rewrite hgw_nth_zbytes, pbK_nth_app_nul by lia. reflexivity.
  - rewrite Ln, HNB by (rewrite length_app; cbn [length]; lia). rewrite app_nth2, Nat.sub_diag by lia. reflexivity.
  - exact (hgk_zbytes_pos nm HNn). }
destruct (hgk_str_meet (segs := rsegs) (hd_zbytes nm) (w_H (hx_W x)) memT y (hd_zbytes ln) lit HNC (hgk_cstr_of_hd (segs := rsegs) _ _ _ _ HL))
  as (kk & c1 & c2 & HM & Hk1 & Hk2 & Hres).
rewrite Ln in Hk1. rewrite Ll in Hk2.
assert (HNY : forall a, y <= a < y + kk + 1 -> aview rsegs (w_H (hx_W x)) memT a <> None).
{ intros a Ha. replace a with (y + Z.of_nat (Z.to_nat (a - y))) by lia. rewrite HNB by (rewrite length_app; cbn [length]; lia).
  discriminate. }
assert (HLY : forall a, lit <= a < lit + kk + 1 -> aview rsegs (w_H (hx_W x)) memT a <> None).
{ intros a Ha. destruct (Z.eq_dec a (lit + Z.of_nat (length ln))) as [->|Na]; [rewrite Hln; discriminate|].
  replace a with (lit + (a - lit)) by lia. rewrite Hlb by (rewrite Ll; lia). discriminate. }
eapply SRr_bind.
{ apply (hj_strcmp_at (fx := mkFP F fc) rsegs B pb_segs_low B_TRAMP_STRCMP (STRCMP F fc) (hx_W x) regsT memT
    (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x) (hx_lyc x)
    (hx_Sc x) mdT (hx_k x) y lit kk c1 c2 (spa - hx_sp0 x) (w64 (pbK_ret i)) (hx_fr x) PAT_DOT HJ
    R10 R11); unfold ESTACK.
  - lia.
  - exact Hl0.
  - lia.
  - rewrite Zminus_mod, F16, S16. reflexivity.
  - lia.
  - lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply ret_ok_even. subst lit ln. destruct i as [|[|[|i]]]; [vm_compute; reflexivity.. | lia].
  - unfold kLowMemEnd in Hlow. lia.
  - lia.
  - lia.
  - exact HM.
  - intros a Ha. split; [apply HNY; lia|]. rewrite Hsp. unfold ESTACK. intros Hw. apply (HOFF a); lia.
  - intros a Ha. split; [apply HLY; lia|]. rewrite Hsp. unfold ESTACK. lia.
  - intros a Ha. rewrite Hsp. intros Hw. apply (HOFF a); lia.
  - intros a Ha. rewrite Hsp. lia.
  - destruct HAM as [HA|[HA1 HA2]]; [left; lia | right; lia].
  - destruct Hlm8 as [HA|[HA1 HA2]]; [left; lia | right; lia].
  - intros a Ha. apply HRAp. lia.
  - apply (hk_hull_sub _ (hx_P x) (Z.of_nat (length (hx_bs x)))); [exact HHVp | lia | lia | lia].
  - intros a Ha. apply Hlra. lia.
  - apply (hk_hull_sub _ lit (Z.of_nat (length ln) + 1)); [exact Hlhv | lia | lia | lia]. }
cbv beta. intros W2 c2' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPr & Hio & H10 & HK2 & _).
apply (HQ regs2 mem2 md2 (hgk_res c1 c2) HJ2 HPr Hio H10 (hgk_res_range c1 c2)).
- rewrite Hres. split; [apply hgk_zbytes_inj | intros ->; reflexivity].
- intros a Ha Hw. apply HK2; [exact Ha | unfold ESTACK; lia].
Qed.

End w.

(* ======================================= the engine's states ======================================= *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a region of a stop's symbolic state holds in the stop's memory *)
Lemma pbK_region_of_st : forall E ss (H : word -> bool) ms r, st_ok rsegs E ss (restrict H ms) -> In r (ss_mem ss) ->
region_ok rsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros E ss H ms r HS Hin. pose proof (st_ok_mem_ok rsegs E ss _ HS) as (_ & HR & _).
exact (proj1 (Forall_forall _ _) HR _ Hin).
Qed.

(* a value chunk of a region based at atom n *)
Lemma pbK_chunk_val : forall E m n lo hi wlo whi cs off w e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> In (YP09.mkChunk off (CVal w e)) cs ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
val_mem rsegs m (bv_unsigned (ew E n) + off) (N.to_nat w) v.
Proof.
intros E m n lo hi wlo whi cs off w e v (_ & _ & _ & HC) Hin He Hv Hw. cbn [YP09.r_chunks YP09.r_base base_val] in HC.
exact (val_of_chunk_ok rsegs E m _ off w e v (proj1 (Forall_forall _ _) HC _ Hin) He Hv Hw).
Qed.

Lemma pbK_SLit : forall E v, 0 <= v < 2 ^ 64 -> sv_denot E (SLit v) = Z_to_bv 64 v.
Proof. intros E v Hv. rewrite denot_lit_U, U_SLit. f_equal. apply zcanon_id. unfold M64. lia. Qed.

Lemma pbK_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* the hole's pattern from the hole region's eight byte chunks (each a literal whose low byte is the pattern's) *)
Lemma pbK_hpat_of_region : forall (x : @hp_ctx rsegs) E mem cs pat,
region_ok rsegs E (hx_rd x mem) (YP09.mkRegion (Some 26%nat) 0 8 0 8 cs) -> bv_unsigned (ew E 26) = hx_shf x ->
length pat = 8%nat ->
(forall i, (i < 8)%nat -> exists v, In (YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit v))) cs /\ 0 <= v < 2 ^ 64 /\
  v mod 256 = nth i pat 0) ->
hpat rsegs (hx_W x) mem (hx_fr x) pat.
Proof.
intros x E mem cs pat (_ & _ & _ & HC) H26 Hl Hin i Hi. rewrite Hl in Hi.
cbn [YP09.r_chunks YP09.r_base base_val] in HC. rewrite H26 in HC.
destruct (Hin (Z.to_nat i) ltac:(lia)) as (v & Hv & Hv64 & Hm).
pose proof (proj1 (Forall_forall _ _) HC _ Hv 0 ltac:(cbn; lia)) as (b & Hcb & Hmb).
cbn [YP09.c_off YP09.c_val] in Hcb, Hmb. cbv beta iota delta [cbyte] in Hcb. injection Hcb as <-.
rewrite Z2Nat.id, Z.add_0_r in Hmb by lia.
unfold aview. unfold hx_rd in Hmb. unfold hx_shf in Hmb. rewrite Hmb. cbn [option_map]. f_equal.
unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_unsigned.
rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64). rewrite <- Hm.
Z.div_mod_to_equations. lia.
Qed.

(* frames of two runs one after the other *)
Lemma pbK_frame_trans : forall E rs1 rs2 (m0 m1 m2 : word -> option byte),
frame_of E rs1 m0 m1 -> frame_of E rs2 m1 m2 -> frame_of E (rs1 ++ rs2) m0 m2.
Proof.
intros E rs1 rs2 m0 m1 m2 H1 H2 w Hw. rewrite H2, H1; [reflexivity| |];
intros (r & Hr & Hb); apply Hw; exists r; (split; [apply in_or_app; tauto | exact Hb]).
Qed.

(* the write windows of a run whose writable regions are the temporaries at sp = spa and the hole at s10 *)
Lemma pbK_windows : forall (x : @hp_ctx rsegs) E rs,
bv_unsigned (ew E 2) = hx_spa x -> bv_unsigned (ew E 26) = hx_shf x ->
(forall r, In r rs -> (YP09.r_base r = Some 2%nat /\ 0 <= YP09.r_wlo r /\ YP09.r_whi r <= 0x80) \/
  (YP09.r_base r = Some 26%nat /\ 0 <= YP09.r_wlo r /\ YP09.r_whi r <= 8) \/ YP09.r_whi r <= YP09.r_wlo r) ->
forall a, in_wrange E rs a -> hx_spa x <= a < hx_spa x + 0x80 \/ hp_hole x a.
Proof.
intros x E rs H2 H26 HR a (r & Hr & Ha). unfold hp_hole.
destruct (HR r Hr) as [(Hb & H1 & H3) | [(Hb & H1 & H3) | H]]; rewrite ?Hb in Ha; cbn [base_val] in Ha;
[rewrite H2 in Ha; left | rewrite H26 in Ha; right | ]; lia.
Qed.

End e.

Ltac pbK_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* ======================================= leaving a run at a cut ======================================= *)
Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis errno_low : api_env rsegs B.
Local Notation pctx := (@hp_ctx rsegs).

Lemma pbK_view_frame : forall E rs (H : word -> bool) (m1 m2 : word -> option byte) a,
frame_of E rs (mrestrict H m1) (mrestrict H m2) -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview rsegs H m2 a = aview rsegs H m1 a.
Proof.
intros E rs H m1 m2 a HF Ha Hw. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. exact Hw.
Qed.

Lemma pbK_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md. repeat split; reflexivity. Qed.

(* hp_core at the end of runs whose writes lie in the temporaries [spa, spa + 0x80) and the hole *)
Lemma pbK_core_exit : forall (x : pctx) pat pat' cl rb regs mem md regs2 mem2 md2 E rs,
call_ok B x -> hp_core B x pat cl rb regs mem md -> Z.of_nat (length cl) <= hx_cap x -> length rb = 12%nat ->
frame_of E rs (hx_rd x mem) (hx_rd x mem2) ->
(forall a, in_wrange E rs a -> hx_spa x <= a < hx_spa x + 0x80 \/ hp_hole x a) ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) pat) mem2) md2 (hx_k x) ->
length pat' = length pat -> Forall (fun v => 0 <= v < 256) pat' -> hpat rsegs (hx_W x) mem2 (hx_fr x) pat' ->
same_io md md2 -> hk_cregs x regs2 ->
hp_core B x pat' cl rb regs2 mem2 md2.
Proof.
intros x pat pat' cl rb regs mem md regs2 mem2 md2 E rs Hc Hcore Hcl Hrb12 HFr HW HJ2 Hlp Hbp HP2 Hio Hcr.
pose proof (hk_core_cells B _ _ _ _ _ _ _ Hcore) as (HO & HR & _).
pose proof (hk_out B x Hc) as (Hcap & _ & _ & _ & _ & H4096 & Hceil & Happ & _ & Hoff & _).
pose proof (hk_frame_win B x Hc) as (W1 & W2 & _ & _ & W5).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HNW : forall a, ~ (hx_spa x <= a < hx_spa x + 0x80) -> ~ hp_hole x a -> ~ in_wrange E rs a)
  by (intros a H1 H2 Hw; destruct (HW a Hw); contradiction).
apply (hk_core_of_run B pb_segs_low x pat pat' cl cl rb rb regs mem md regs2 mem2 md2 E rs errno_low Hc Hcore
  (le_n _) ltac:(lia) HFr).
- intros a Ha. destruct (HW a Ha) as [H|H]; [left; exact H | right; left; exact H].
- exact HJ2.
- exact Hlp.
- exact Hbp.
- exact HP2.
- exact Hio.
- apply (hk_garr8_kept x mem mem2 (hx_O x) _); [|exact HO].
  intros a Ha. unfold hd_zbytes in Ha. rewrite length_map, length_ha_cells_bytes in Ha.
  unfold hx_view. apply (pbK_view_frame E rs); [exact HFr | unfold in_app, kLowShadowBeg, kHighMemBeg in *; lia|].
  apply HNW.
  + unfold hd_off_stack in Hoff. intros Hw. apply (Hoff a); unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia.
  + intros Hh. pose proof (hk_hole_band B x a Hc Hh) as [B1 B2].
    unfold in_app, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, SHADOW_OFF in *. lia.
- intros HR0. apply (hk_garr8_kept x mem mem2 (hx_R x) _); [|exact (HR HR0)].
  pose proof (hk_res B pb_segs_low x Hc HR0) as (_ & _ & Hside & Hrb).
  intros a Ha. unfold hd_zbytes in Ha. rewrite length_map, Hrb12 in Ha.
  destruct (Hrb a ltac:(lia)) as (_ & _ & Hband).
  unfold hx_view. apply (pbK_view_frame E rs); [exact HFr | unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Hband; lia|].
  apply HNW.
  + intros Hw. unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
  + intros Hh. pose proof (hk_hole_band B x a Hc Hh) as [B1 B2].
    unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, SHADOW_OFF in *. lia.
- exact Hcr.
Qed.

End x.

(* ======================================= the refusal 0x84ebc .. ADV 0x84edc ======================================= *)
(* The temporaries the run reads and writes: [16] (s6's slow-path bound), [24] keys + 1, [32] rf, [40] P + r + 16
   (atoms 47 .. 50); the hole region (byte 4 written back to f8). *)
Definition pbK_csE : list YP09.chunk :=
[YP09.mkChunk 16 (CVal 8 (SOff 47 0)); YP09.mkChunk 24 (CVal 8 (SOff 48 0)); YP09.mkChunk 32 (CVal 8 (SOff 49 0));
 YP09.mkChunk 40 (CVal 8 (SOff 50 0))].
Definition pbK_ssE : sstate := mkSS PC_REF sr_atoms [hk_temps pbK_csE; hk_hole_rg PAT_DOT] None
  (mkFacts (hk_atoms ++ [(49%nat, mkAF 0 5 0)]) [] []).
Definition pbK_LE (x : @hp_ctx rsegs) (r keys rf : Z) : list word :=
[w64 ((hx_P x + r + 8) mod 8 + 3); w64 (keys + 1); w64 rf; w64 (hx_P x + r + 16)].

Section E. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.
Local Notation pctx := (@hp_ctx rsegs).

Lemma pbK_chunk8 : forall E m base off (n : nat) v, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
val_mem rsegs m (base + off) 8 v -> YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E m base off n v He Hv Hm. apply (chunk_ok_val rsegs E m base off 8 (SOff n 0) v); [| | lia | exact Hm].
- rewrite pbK_SOff0. exact He.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
Qed.

(* the cut's own atoms: sp, s10 and s11 from hk_cregs *)
Lemma pbK_U2_26 : forall (x : pctx) regs L, call_ok B x -> hk_cregs x regs ->
bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x /\ bv_unsigned (ew (hk_env x regs L) 26) = hx_shf x /\
2 ^ 46 <= hx_spa x /\ hx_spa x + 0x80 < 2 ^ 47 /\ SHADOW_OFF + 2 ^ 43 <= hx_shf x /\ hx_shf x + 8 <= kHighShadowEnd.
Proof.
intros x regs L Hc (H2 & _ & _ & _ & _ & _ & _ & H26 & _).
pose proof (hk_stack B x Hc) as (S1 & S2 & S3 & S4 & S5 & S6 & _).
pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5).
pose proof (hk_hole_band B x (hx_shf x) Hc ltac:(unfold hp_hole; lia)) as [B1 B2].
pose proof (hk_hole_band B x (hx_shf x + 7) Hc ltac:(unfold hp_hole; lia)) as [B3 B4].
pose proof asan_consts as (C1 & _).
rewrite (hk_env_reg x regs L 2 2%bv eq_refl), (hk_env_reg x regs L 26 26%bv eq_refl), H2, H26. unfold w64.
unfold T_parse_STK, T_PARSE_FRAME, ESTACK, kHighShadowEnd, SHADOW_OFF in *.
rewrite !unsigned_lit_small by lia. lia.
Qed.

Lemma pbK_REF_entry : forall (x : pctx) r cc n ck cl keys rf bad F fc regs mem md, call_ok B x ->
pbK_REF_at B x r cc n ck cl keys rf bad F fc regs mem md ->
st_ok (fx := mkFP F fc) rsegs (hk_env x regs (pbK_LE x r keys rf)) pbK_ssE
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_REF) mem (seg_rom rsegs))).
Proof.
intros x r cc n ck cl keys rf bad F fc regs mem md Hc HR.
destruct HR as (Hcore & Hfxw & Hm & Hpc & Hbad & (L20 & L21 & L22 & V16 & V32 & V40) & H46 & R23 & R5 & R17 & V24).
pose proof (hk_core_cregs B _ _ _ _ _ _ _ Hcore) as HCR.
pose proof Hm as (Hnull & (Hr16 & Hr8 & Hvs & Hrl) & _ & _ & _ & _ & _ & (Hcl & Hk0 & Hrf) & _).
pose proof (hk_pod B x Hc Hnull) as (HP0 & _ & Hlen & _ & _ & HP63 & _).
pose proof (pbK_keys_small x r cc n ck cl keys rf Hm ltac:(unfold hx_len in Hlen; lia)) as Hks.
pose proof (pbK_U2_26 x regs (pbK_LE x r keys rf) Hc HCR) as (U2 & U26 & S1 & S2 & S3 & S4).
set (E := hk_env x regs (pbK_LE x r keys rf)) in *.
assert (E47 : ew E 47 = w64 ((hx_P x + r + 8) mod 8 + 3)) by exact (hk_env_seg x regs _ 0).
assert (E48 : ew E 48 = w64 (keys + 1)) by exact (hk_env_seg x regs _ 1).
assert (E49 : ew E 49 = w64 rf) by exact (hk_env_seg x regs _ 2).
assert (E50 : ew E 50 = w64 (hx_P x + r + 16)) by exact (hk_env_seg x regs _ 3).
unfold hp_vs, hx_len in *.
pose proof (hgw_u32_range (hx_bs x) (r + 8)).
assert (HA49 : afact_ok E 49 (mkAF 0 5 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E49. unfold w64.
  rewrite unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
rewrite restrict_mkst_fx. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + apply (hk_temps_ok B x PAT_DOT cl pbK_rb0 regs mem md _ pbK_csE Hc Hcore).
    repeat constructor.
    * apply (pbK_chunk8 E _ _ 16 47 _ E47); [pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8); lia | exact V16].
    * apply (pbK_chunk8 E _ _ 24 48 _ E48); [lia | exact V24].
    * apply (pbK_chunk8 E _ _ 32 49 _ E49); [lia | exact V32].
    * apply (pbK_chunk8 E _ _ 40 50 _ E50); [lia | exact V40].
  + exact (hk_hole_ok B pb_segs_low x PAT_DOT cl pbK_rb0 regs mem md _ Hc Hcore eq_refl).
- apply pairwise_disjoint_of_extents. unfold extent_of_region, hk_temps, hk_hole_rg.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  change (Ereg regs (w64 SHADOW_OFF :: hk_saved_vals x ++ hk_fs0 :: pbK_LE x r keys rf)) with E. rewrite U2, U26.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF, kHighShadowEnd in *.
  repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms]. apply (hk_atoms_ok B x regs (pbK_LE x r keys rf) _ Hc HCR).
  cbn [atoms_ok]. split; [exact HA49 | exact I].
Qed.

Lemma pbK_br_eq0 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof. intros E n v H Hv. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit by lia. reflexivity. Qed.

Lemma pbK_reg_kept : forall (fx' : YK11.FPState) (x : pctx) regs L ss ms (H : word -> bool) (r : bv 5) (n : nat),
st_ok (fx := fx') rsegs (hk_env (fx := fx) x regs L) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 ->
Z.of_nat n = bv_unsigned r -> getr (ms_regs ms) r = getr regs r.
Proof.
intros fx' x regs L ss ms H r n HS Hr Hn. rewrite (st_ok_restrict_reg (fx := fx') rsegs H _ ss ms r HS), Hr, pbK_SOff0.
apply (hk_env_reg (fx := fx)). exact Hn.
Qed.

Lemma pbK_reg_sv : forall (fx' : YK11.FPState) E ss ms (H : word -> bool) (r : bv 5) e,
st_ok (fx := fx') rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> getr (ms_regs ms) r = sv_denot E e.
Proof. intros fx' E ss ms H r e HS Hr. rewrite (st_ok_restrict_reg (fx := fx') rsegs H _ ss ms r HS), Hr. reflexivity. Qed.

Ltac pbK_regions HS R0 R1 :=
lazymatch type of HS with @st_ok _ ?f _ (mkSST _ _ _ (?r0 :: ?r1 :: _) _ _) _ =>
  pose proof (pbK_region_of_st (fx := f) _ _ _ _ r0 HS (or_introl eq_refl)) as R0;
  pose proof (pbK_region_of_st (fx := f) _ _ _ _ r1 HS (or_intror (or_introl eq_refl))) as R1 end.
Ltac pbK_win_regions := let rr := fresh "rr" in let Hrr := fresh "Hrr" in
intros rr Hrr; cbn [ss_mem pbK_ssE add_cond app In] in Hrr;
repeat (destruct Hrr as [<-|Hrr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi hk_temps hk_hole_rg];
  first [left; split; [reflexivity|lia] | right; left; split; [reflexivity|lia] | right; right; lia] |]);
destruct Hrr.
Ltac pbK_kept HS :=
lazymatch goal with |- getr _ ?r = getr ?regs ?r =>
  let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
  lazymatch type of HS with @st_ok _ ?f _ _ _ =>
    exact (pbK_reg_kept f _ regs _ _ _ _ r n HS ltac:(vm_compute; reflexivity) eq_refl) end end.
Ltac pbK_io := let rec kio := first [apply same_io_refl | assumption |
  eapply same_io_trans; [| apply pbK_same_io_wvb]; kio] in kio.

(* 0x84ebc .. 0x84edc: the hole's byte 4 back to f8, rf' = rf ? rf : t0 into [sp + 32], s8 = 0, s9 = keys + 1 *)
Lemma pbK_REF : forall (x : pctx) r cc n ck cl keys rf, call_ok B x ->
(forall rf', ADV_ok B MT x r cc n None cl (keys + 1) rf') -> pbK_REF_ok B MT x r cc n ck cl keys rf.
Proof.
intros x r cc n ck cl keys rf Hc HADV bad F fc regs mem md HR.
pose proof (pbK_REF_entry x r cc n ck cl keys rf bad F fc regs mem md Hc HR) as HS.
destruct HR as (Hcore & Hfxw & Hm & Hpc & Hbad & (L20 & L21 & L22 & V16 & V32 & V40) & (A14 & A16) & R23 & R5 & R17 & V24).
pose proof (hk_core_cregs B _ _ _ _ _ _ _ Hcore) as HCR.
pose proof (hk_core_journal B _ _ _ _ _ _ _ Hcore) as (HJ & HOK & HP).
pose proof Hm as (Hnull & (Hr16 & Hr8 & Hvs & Hrl) & _ & _ & _ & _ & _ & (Hcl & Hk0 & Hrf) & _).
pose proof (hk_pod B x Hc Hnull) as (HP0 & _ & Hlen & _ & _ & HP63 & _).
pose proof (pbK_keys_small x r cc n ck cl keys rf Hm ltac:(unfold hx_len in Hlen; lia)) as Hks.
pose proof (pbK_U2_26 x regs (pbK_LE x r keys rf) Hc HCR) as (U2 & U26 & S1 & S2 & S3 & S4).
pose proof (hgw_u32_range (hx_bs x) (r + 8)).
unfold hp_vs, hx_len in *.
set (E := hk_env x regs (pbK_LE x r keys rf)) in *.
assert (E47 : ew E 47 = w64 ((hx_P x + r + 8) mod 8 + 3)) by exact (hk_env_seg x regs _ 0).
assert (E48 : ew E 48 = w64 (keys + 1)) by exact (hk_env_seg x regs _ 1).
assert (E49 : ew E 49 = w64 rf) by exact (hk_env_seg x regs _ 2).
assert (E50 : ew E 50 = w64 (hx_P x + r + 16)) by exact (hk_env_seg x regs _ 3).
assert (E5 : ew E 5 = w64 bad) by (rewrite (hk_env_reg x regs (pbK_LE x r keys rf) 5 5%bv eq_refl); exact R5).
pose proof pb_segs_low as Hsegs. pose proof pb_wx as Hwx.
pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8 ltac:(lia)) as Hm8.
unfold cfg_at. change (w64 PC_REF) with (Z_to_bv 64 PC_REF).
aj_runH pb_tbl_ok HS HJ.
{ cbn [ss_mem pbK_ssE]. eapply (hk_awr_temps B x E); [exact Hc | exact U2 |].
  apply (hk_awr_hole B x E); [exact U26 | reflexivity | apply awr_okH_nil]. }
rename HFr into HFr1.
apply (SRr_sym_branch rsegs (hx_W x) E _ ms _ _ BC_EQ (SOff 49 0) (SLit 0) HS); intros Hbr HS1;
  rewrite (pbK_br_eq0 E 49 rf E49 ltac:(lia)) in Hbr.
- (* rf = 0: t0 (the refusal bad) into [sp + 32] *)
  apply Z.eqb_eq in Hbr.
  aj_run_toH pb_tbl_ok HS1 HJ PC_ADV.
  { lazymatch goal with |- awr_okH _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply (hk_awr_temps B x E); [exact Hc | exact U2 |].
    eapply (awr_okH_cons_hole E _ _ _ _ _ _ _ _ _ (hx_fr x) PAT_DOT 26%nat); [reflexivity | exact U26 | cbn; lia | cbn; lia |
      apply awr_okH_nil]. }
  pbK_regions HS1 R0 R1.
  assert (HP2 : hpat rsegs (hx_W x) (ms_mem ms0) (hx_fr x) PAT_KEY).
  { apply (pbK_hpat_of_region x E _ _ PAT_KEY R1 U26 eq_refl).
    intros i Hi. do 8 (destruct i as [|i]; [eexists; split; [pbK_in | split; [lia | reflexivity]] |]). lia. }
  assert (HCR2 : hk_cregs x (ms_regs ms0)).
  { apply (hk_cregs_same x regs _ HCR); pbK_kept HS1. }
  assert (Hcore2 : hp_core B x PAT_KEY cl pbK_rb0 (ms_regs ms0) (ms_mem ms0) (with_vm_backing (m_vm_lazy md) mat0 md)).
  { apply (pbK_core_exit B errno_low x PAT_DOT PAT_KEY cl pbK_rb0 regs mem md _ _ _ E _ Hc Hcore ltac:(lia)
      (length_ha_res_bytes 0 0 0) (pbK_frame_trans E _ _ _ _ _ HFr1 HFr) ); [ | exact HJ | reflexivity | | exact HP2 | pbK_io | exact HCR2].
    - apply (pbK_windows x E _ U2 U26). pbK_win_regions.
    - unfold PAT_KEY. repeat constructor; lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) E _ ms0 HS1 eq_refl). cbn [ss_pc].
  apply (HADV bad F fc (ms_regs ms0) (ms_mem ms0) _).
  split; [exact Hcore2|]. split; [exact Hfxw|].
  split; [pose proof (hgk_key_refuse x r cc n ck cl keys rf bad Hm Hbad Hpc) as HA; rewrite Hbr in HA; exact HA|].
  split.
  { split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 20%bv 20 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact L20|].
    split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 21%bv 21 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact L21|].
    split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 22%bv 22 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact L22|].
    pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 16 8 (SOff 47 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E47)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C16.
    pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 32 8 (SOff 5 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E5)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C32.
    pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 40 8 (SOff 50 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E50)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C40.
    rewrite U2 in C16, C32, C40. split; [exact C16|]. split; [exact C32 | exact C40]. }
  split.
  { split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 14%bv 14 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact A14|].
    rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 16%bv 16 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact A16. }
  split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 23%bv 23 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact R23|].
  split; [rewrite (pbK_reg_sv (mkFP F fc) E _ _ _ 24%bv (SLit 0) HS1 ltac:(vm_compute; reflexivity)),
    pbK_SLit by (split; [apply Z.le_refl | reflexivity]); reflexivity|].
  split; [rewrite (pbK_reg_sv (mkFP F fc) E _ _ _ 25%bv (SOff 48 0) HS1 ltac:(vm_compute; reflexivity)), pbK_SOff0;
    exact E48|].
  rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 17%bv 17 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact R17.
- (* rf <> 0: rf stays *)
  apply Z.eqb_neq in Hbr.
  aj_run_toH pb_tbl_ok HS1 HJ PC_ADV.
  { lazymatch goal with |- awr_okH _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply (hk_awr_temps B x E); [exact Hc | exact U2 |].
    eapply (awr_okH_cons_hole E _ _ _ _ _ _ _ _ _ (hx_fr x) PAT_DOT 26%nat); [reflexivity | exact U26 | cbn; lia | cbn; lia |
      apply awr_okH_nil]. }
  pbK_regions HS1 R0 R1.
  assert (HP2 : hpat rsegs (hx_W x) (ms_mem ms0) (hx_fr x) PAT_KEY).
  { apply (pbK_hpat_of_region x E _ _ PAT_KEY R1 U26 eq_refl).
    intros i Hi. do 8 (destruct i as [|i]; [eexists; split; [pbK_in | split; [lia | reflexivity]] |]). lia. }
  assert (HCR2 : hk_cregs x (ms_regs ms0)).
  { apply (hk_cregs_same x regs _ HCR); pbK_kept HS1. }
  assert (Hcore2 : hp_core B x PAT_KEY cl pbK_rb0 (ms_regs ms0) (ms_mem ms0) (with_vm_backing (m_vm_lazy md) mat0 md)).
  { apply (pbK_core_exit B errno_low x PAT_DOT PAT_KEY cl pbK_rb0 regs mem md _ _ _ E _ Hc Hcore ltac:(lia)
      (length_ha_res_bytes 0 0 0) (pbK_frame_trans E _ _ _ _ _ HFr1 HFr) ); [ | exact HJ | reflexivity | | exact HP2 | pbK_io | exact HCR2].
    - apply (pbK_windows x E _ U2 U26). pbK_win_regions.
    - unfold PAT_KEY. repeat constructor; lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) E _ ms0 HS1 eq_refl). cbn [ss_pc].
  apply (HADV rf F fc (ms_regs ms0) (ms_mem ms0) _).
  assert (Erf : (if rf =? Headamp.REFUSE_NONE then bad else rf) = rf)
    by (unfold Headamp.REFUSE_NONE; destruct (Z.eqb_spec rf 0); [lia | reflexivity]).
  split; [exact Hcore2|]. split; [exact Hfxw|].
  split; [pose proof (hgk_key_refuse x r cc n ck cl keys rf bad Hm Hbad Hpc) as HA; rewrite Erf in HA; exact HA|].
  split.
  { split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 20%bv 20 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact L20|].
    split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 21%bv 21 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact L21|].
    split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 22%bv 22 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact L22|].
    pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 16 8 (SOff 47 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E47)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C16.
    pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 32 8 (SOff 49 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E49)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C32.
    pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 40 8 (SOff 50 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E50)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C40.
    rewrite U2 in C16, C32, C40. split; [exact C16|]. split; [exact C32 | exact C40]. }
  split.
  { split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 14%bv 14 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact A14|].
    rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 16%bv 16 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact A16. }
  split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 23%bv 23 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact R23|].
  split; [rewrite (pbK_reg_sv (mkFP F fc) E _ _ _ 24%bv (SLit 0) HS1 ltac:(vm_compute; reflexivity)),
    pbK_SLit by (split; [apply Z.le_refl | reflexivity]); reflexivity|].
  split; [rewrite (pbK_reg_sv (mkFP F fc) E _ _ _ 25%bv (SOff 48 0) HS1 ltac:(vm_compute; reflexivity)), pbK_SOff0;
    exact E48|].
  rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 17%bv 17 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact R17.
Qed.

(* the entry of a non-token run at a cut: the temporaries with 8-byte chunks, the hole at pat *)
Lemma pbK_entry_hole : forall (x : pctx) pat cl rb regs mem md F fc pc L cs G, call_ok B x ->
hp_core B x pat cl rb regs mem md -> length pat = 8%nat -> regions_wf [hk_temps cs; hk_hole_rg pat] = true ->
Forall (YP09.chunk_ok rsegs (hk_env x regs L) (hx_rd x mem) (hx_spa x)) cs -> atoms_ok (hk_env x regs L) G ->
st_ok (fx := mkFP F fc) rsegs (hk_env x regs L)
  (mkSS pc sr_atoms [hk_temps cs; hk_hole_rg pat] None (mkFacts (hk_atoms ++ G) [] []))
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 pc) mem (seg_rom rsegs))).
Proof.
intros x pat cl rb regs mem md F fc pc L cs G Hc Hcore Hl Hwf Hcs HG.
pose proof (hk_core_cregs B _ _ _ _ _ _ _ Hcore) as HCR.
pose proof (pbK_U2_26 x regs L Hc HCR) as (U2 & U26 & S1 & S2 & S3 & S4).
rewrite restrict_mkst_fx. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [exact (hk_temps_ok B x pat cl rb regs mem md L cs Hc Hcore Hcs)|].
  constructor; [exact (hk_hole_ok B pb_segs_low x pat cl rb regs mem md L Hc Hcore Hl) | constructor].
- apply pairwise_disjoint_of_extents. unfold extent_of_region, hk_temps, hk_hole_rg.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  change (Ereg regs (w64 SHADOW_OFF :: hk_saved_vals x ++ hk_fs0 :: L)) with (hk_env x regs L). rewrite U2, U26.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF, kHighShadowEnd in *.
  repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms]. exact (hk_atoms_ok B x regs L G Hc HCR HG).
Qed.

Lemma pbK_br_ltu48 : forall E n v, ew E n = w64 v -> - 2 ^ 63 <= v < 2 ^ 63 ->
branch_taken BC_LTU (sv_denot E (SOff n 0)) (sv_denot E (SLit 48)) = (0 <=? v) && (v <? 48).
Proof.
intros E n v H Hv. rewrite branch_ltu_U, U_lit by lia. rewrite U_SOff, H, Z.add_0_r.
unfold w64. rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia.
destruct (Z.leb_spec 0 v) as [H0|H0].
- rewrite Z.mod_small by lia. reflexivity.
- cbn [andb]. apply Z.ltb_ge. replace (v mod 2 ^ 64) with (v + 2 ^ 64); [lia|].
  symmetry. rewrite <- (Z.mod_small (v + 2 ^ 64) (2 ^ 64)) by lia.
  rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.

(* ======================================= the channel test 0x84eb0 ======================================= *)
Definition pbK_csC : list YP09.chunk :=
[YP09.mkChunk 16 (CVal 8 (SOff 47 0)); YP09.mkChunk 24 (CVal 8 (SOff 48 0)); YP09.mkChunk 32 (CVal 8 (SOff 49 0));
 YP09.mkChunk 40 (CVal 8 (SOff 50 0)); YP09.mkChunk 48 (CVal 8 (SOff 51 0))].
Definition pbK_LC (x : pctx) (r cc keys rf : Z) : list word :=
[w64 ((hx_P x + r + 8) mod 8 + 3); w64 (keys + 1); w64 rf; w64 (hx_P x + r + 16); w64 (shadow_addr (hx_P x + cc))].

Definition pbK_KS (x : pctx) (ck p : Z) : Prop :=
Headamp.parse_key (pbK_str x ck) =
  (if (pbK_ch x ck <? 0) || (Headamp.REAC_HEADAMP_MAX_CH <=? pbK_ch x ck) then Headamp.KRange
   else Headamp.KCell (pbK_ch x ck) p).

(* bltu s8,48: 0 <= ch < 48 -> 0x84f04 (byte 4 of the hole back to f8) -> VAL 0x84f0c; else t0 = 5 -> 0x84ebc *)
Lemma pbK_CH : forall (x : pctx) r cc n ck cl keys rf, call_ok B x ->
(forall rf', ADV_ok B MT x r cc n None cl (keys + 1) rf') -> (forall ch p, VAL_ok B MT x r cc n ch p cl keys rf) ->
pbK_CH_ok B MT x r cc n ck cl keys rf.
Proof.
intros x r cc n ck cl keys rf Hc HADV HVAL p F fc regs mem md HC.
pose proof HC as (Hcore & Hfxw & Hm & Hpk & Hp & (L20 & L21 & L22 & V16 & V32 & V40) & (A14 & A16) & R23 & R24 & R13 & R11
  & R17 & V24 & V48).
assert (Hpk2 : pbK_KS x ck p) by exact Hpk. clear Hpk HC.
pose proof (hk_core_cregs B _ _ _ _ _ _ _ Hcore) as HCR.
pose proof (hk_core_journal B _ _ _ _ _ _ _ Hcore) as (HJ & HOK & HP).
pose proof Hm as (Hnull & (Hr16 & Hr8 & Hvs & Hrl) & Hcc & Hcc8 & Hin & _ & _ & (Hcl & Hk0 & Hrf) & _).
pose proof (hk_pod B x Hc Hnull) as (HP0 & _ & Hlen & _ & _ & HP63 & _).
pose proof (hgw_next_bounds x r cc (conj Hr16 (conj Hr8 (conj Hvs Hrl))) Hcc Hcc8 Hin) as (Hnx & _).
pose proof (pbK_keys_small x r cc n ck cl keys rf Hm ltac:(unfold hx_len in Hlen; lia)) as Hks.
pose proof (pbK_U2_26 x regs (pbK_LC x r cc keys rf) Hc HCR) as (U2 & U26 & S1 & S2 & S3 & S4).
pose proof (hgw_u32_range (hx_bs x) (r + 8)).
pose proof (hgk_val_range (pbK_str x ck)) as Hchr. fold (pbK_ch x ck) in Hchr.
unfold hp_vs, hx_len in *.
assert (Hsh : 0 <= shadow_addr (hx_P x + cc) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF.
  assert (0 <= hx_P x + cc < 2 ^ 63) by lia.
  assert (0 <= (hx_P x + cc) / 8 <= hx_P x + cc) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia. }
set (E := hk_env x regs (pbK_LC x r cc keys rf)) in *.
assert (E47 : ew E 47 = w64 ((hx_P x + r + 8) mod 8 + 3)) by exact (hk_env_seg x regs _ 0).
assert (E48 : ew E 48 = w64 (keys + 1)) by exact (hk_env_seg x regs _ 1).
assert (E49 : ew E 49 = w64 rf) by exact (hk_env_seg x regs _ 2).
assert (E50 : ew E 50 = w64 (hx_P x + r + 16)) by exact (hk_env_seg x regs _ 3).
assert (E51 : ew E 51 = w64 (shadow_addr (hx_P x + cc))) by exact (hk_env_seg x regs _ 4).
assert (E24 : ew E 24 = w64 (pbK_ch x ck)) by (rewrite (hk_env_reg x regs (pbK_LC x r cc keys rf) 24 24%bv eq_refl); exact R24).
pose proof pb_segs_low as Hsegs. pose proof pb_wx as Hwx.
pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8 ltac:(lia)) as Hm8.
pose proof (pbK_entry_hole x PAT_DOT cl pbK_rb0 regs mem md F fc PC_CH (pbK_LC x r cc keys rf) pbK_csC [] Hc Hcore
  eq_refl ltac:(vm_compute; reflexivity)) as HS.
specialize (HS ltac:(repeat constructor;
  [ apply (pbK_chunk8 E _ _ 16 47 _ E47); [lia | exact V16]
  | apply (pbK_chunk8 E _ _ 24 48 _ E48); [lia | exact V24]
  | apply (pbK_chunk8 E _ _ 32 49 _ E49); [lia | exact V32]
  | apply (pbK_chunk8 E _ _ 40 50 _ E50); [lia | exact V40]
  | apply (pbK_chunk8 E _ _ 48 51 _ E51); [lia | exact V48] ]) I).
unfold cfg_at. change (w64 PC_CH) with (Z_to_bv 64 PC_CH).
aj_runH pb_tbl_ok HS HJ.
{ cbn [ss_mem]. eapply (hk_awr_temps B x E); [exact Hc | exact U2 |].
  apply (hk_awr_hole B x E); [exact U26 | reflexivity | apply awr_okH_nil]. }
rename HFr into HFr1.
apply (SRr_sym_branch rsegs (hx_W x) E _ ms _ _ BC_LTU (SOff 24 0) (SLit 48) HS); intros Hbr HS1;
  rewrite (pbK_br_ltu48 E 24 (pbK_ch x ck) E24 ltac:(lia)) in Hbr.
- (* 0 <= ch < 48: VAL *)
  apply andb_true_iff in Hbr as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
  aj_run_toH pb_tbl_ok HS1 HJ PC_VAL.
  { lazymatch goal with |- awr_okH _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply (hk_awr_temps B x E); [exact Hc | exact U2 |].
    eapply (awr_okH_cons_hole E _ _ _ _ _ _ _ _ _ (hx_fr x) PAT_DOT 26%nat); [reflexivity | exact U26 | cbn; lia | cbn; lia |
      apply awr_okH_nil]. }
  pbK_regions HS1 R0 R1.
  assert (HP2 : hpat rsegs (hx_W x) (ms_mem ms0) (hx_fr x) PAT_KEY).
  { apply (pbK_hpat_of_region x E _ _ PAT_KEY R1 U26 eq_refl).
    intros i Hi. do 8 (destruct i as [|i]; [eexists; split; [pbK_in | split; [lia | reflexivity]] |]). lia. }
  assert (HCR2 : hk_cregs x (ms_regs ms0)) by (apply (hk_cregs_same x regs _ HCR); pbK_kept HS1).
  assert (Hcore2 : hp_core B x PAT_KEY cl pbK_rb0 (ms_regs ms0) (ms_mem ms0) (with_vm_backing (m_vm_lazy md) mat0 md)).
  { apply (pbK_core_exit B errno_low x PAT_DOT PAT_KEY cl pbK_rb0 regs mem md _ _ _ E _ Hc Hcore ltac:(lia)
      (length_ha_res_bytes 0 0 0) (pbK_frame_trans E _ _ _ _ _ HFr1 HFr) ); [ | exact HJ | reflexivity | | exact HP2 | pbK_io | exact HCR2].
    - apply (pbK_windows x E _ U2 U26). pbK_win_regions.
    - unfold PAT_KEY. repeat constructor; lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) E _ ms0 HS1 eq_refl). cbn [ss_pc].
  assert (Hkc : Headamp.parse_key (pbK_str x ck) = Headamp.KCell (pbK_ch x ck) p).
  { pose proof Hpk2 as Hpk. unfold pbK_KS in Hpk. rewrite Hpk. clear Hpk. unfold Headamp.REAC_HEADAMP_MAX_CH.
    rewrite (proj2 (Z.ltb_ge _ _) Hb1), (proj2 (Z.leb_gt _ _) Hb2). reflexivity. }
  apply (HVAL (pbK_ch x ck) p F fc (ms_regs ms0) (ms_mem ms0) _).
  split; [exact Hcore2|]. split; [exact Hfxw|]. split; [exact (hgk_key_val x r cc n ck cl keys rf _ p Hm Hkc)|].
  pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 16 8 (SOff 47 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E47)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C16.
  pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 24 8 (SOff 48 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E48)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C24.
  pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 32 8 (SOff 49 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E49)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C32.
  pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 40 8 (SOff 50 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E50)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C40.
  pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 48 8 (SOff 51 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E51)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C48.
  rewrite U2 in C16, C24, C32, C40, C48.
  split; [split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 20%bv 20 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact L20|]; split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 21%bv 21 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact L21|]; split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 22%bv 22 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact L22|];
    split; [exact C16|]; split; [exact C32 | exact C40]|].
  split; [split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 14%bv 14 HS1 ltac:(vm_compute; reflexivity) eq_refl);
    exact A14 | rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 16%bv 16 HS1 ltac:(vm_compute; reflexivity) eq_refl);
    exact A16]|].
  split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 23%bv 23 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact R23|].
  split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 24%bv 24 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact R24|].
  split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 13%bv 13 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact R13|].
  split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 11%bv 11 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact R11|].
  split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 17%bv 17 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact R17|].
  split; [exact C24 | exact C48].
- (* ch < 0 or ch >= 48: the refusal OUT_OF_RANGE *)
  aj_run_toH pb_tbl_ok HS1 HJ PC_REF.
  { lazymatch goal with |- awr_okH _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply (hk_awr_temps B x E); [exact Hc | exact U2 |].
    eapply (awr_okH_cons_hole E _ _ _ _ _ _ _ _ _ (hx_fr x) PAT_DOT 26%nat); [reflexivity | exact U26 | cbn; lia | cbn; lia |
      apply awr_okH_nil]. }
  pbK_regions HS1 R0 R1.
  assert (HP2 : hpat rsegs (hx_W x) (ms_mem ms0) (hx_fr x) PAT_DOT).
  { apply (pbK_hpat_of_region x E _ _ PAT_DOT R1 U26 eq_refl).
    intros i Hi. do 8 (destruct i as [|i]; [eexists; split; [pbK_in | split; [lia | reflexivity]] |]). lia. }
  assert (HCR2 : hk_cregs x (ms_regs ms0)) by (apply (hk_cregs_same x regs _ HCR); pbK_kept HS1).
  assert (Hcore2 : hp_core B x PAT_DOT cl pbK_rb0 (ms_regs ms0) (ms_mem ms0) (with_vm_backing (m_vm_lazy md) mat0 md)).
  { apply (pbK_core_exit B errno_low x PAT_DOT PAT_DOT cl pbK_rb0 regs mem md _ _ _ E _ Hc Hcore ltac:(lia)
      (length_ha_res_bytes 0 0 0) (pbK_frame_trans E _ _ _ _ _ HFr1 HFr) ); [ | exact HJ | reflexivity | | exact HP2 | pbK_io | exact HCR2].
    - apply (pbK_windows x E _ U2 U26). pbK_win_regions.
    - unfold PAT_DOT. repeat constructor; lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) E _ ms0 HS1 eq_refl). cbn [ss_pc].
  assert (Hkr : Headamp.parse_key (pbK_str x ck) = Headamp.KRange).
  { pose proof Hpk2 as Hpk. unfold pbK_KS in Hpk. rewrite Hpk. clear Hpk. unfold Headamp.REAC_HEADAMP_MAX_CH.
    destruct (Z.ltb_spec (pbK_ch x ck) 0); [reflexivity|]. destruct (Z.leb_spec 48 (pbK_ch x ck)); [reflexivity|].
    exfalso. rewrite (proj2 (Z.leb_le _ _) ltac:(lia)), (proj2 (Z.ltb_lt _ _) ltac:(lia)) in Hbr. discriminate Hbr. }
  apply (pbK_REF x r cc n ck cl keys rf Hc HADV 5 F fc (ms_regs ms0) (ms_mem ms0) _).
  pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 16 8 (SOff 47 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E47)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C16.
  pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 24 8 (SOff 48 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E48)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C24.
  pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 32 8 (SOff 49 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E49)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C32.
  pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 40 8 (SOff 50 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E50)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C40.
  rewrite U2 in C16, C24, C32, C40.
  split; [exact Hcore2|]. split; [exact Hfxw|]. split; [exact Hm|].
  split; [exact (pbK_cell_range x ck _ Hkr)|]. split; [lia|].
  split; [split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 20%bv 20 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact L20|]; split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 21%bv 21 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact L21|]; split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 22%bv 22 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact L22|];
    split; [exact C16|]; split; [exact C32 | exact C40]|].
  split; [split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 14%bv 14 HS1 ltac:(vm_compute; reflexivity) eq_refl);
    exact A14 | rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 16%bv 16 HS1 ltac:(vm_compute; reflexivity) eq_refl);
    exact A16]|].
  split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 23%bv 23 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact R23|].
  split; [rewrite (pbK_reg_sv (mkFP F fc) E _ _ _ 5%bv (SLit 5) HS1 ltac:(vm_compute; reflexivity)),
    pbK_SLit by (split; [discriminate | reflexivity]); reflexivity|].
  split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 17%bv 17 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact R17|].
  exact C24.
Qed.

End E.

(* ======================================= the strcmp chain ======================================= *)
Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.
Hypothesis HBerrno : as_errno B = 0x5d812c.
Hypothesis STRTOL : forall F fc, hd_astrtol_hole (fx := mkFP F fc) rsegs B B_TRAMP_STRTOL (hi_gotw headamp_himg_B)
  (hi_guard headamp_himg_B).
Hypothesis STRCMP : forall F fc, hd_astrcmp_hole (fx := mkFP F fc) rsegs B B_TRAMP_STRCMP.
Local Notation pctx := (@hp_ctx rsegs).

(* the walk segment's run tactics (lib/AU/HPgParseW.v; Ltac does not leave its section) *)
Ltac pbK_post x HAE KM Hio U2 :=
  lazymatch goal with HS : st_ok _ ?E' _ _ |- _ =>
  lazymatch type of HAE with env_agree ?k ?E0 ?E1 =>
  lazymatch goal with HFr : frame_of E1 ?rs (mrestrict _ _) (mrestrict _ _) |- _ =>
    let KM' := fresh "KM" in
    pose proof (pbW_keep x E1 rs _ _ _ ltac:(first [exact U2 | rewrite (proj1 HAE 2%nat ltac:(lia)); exact U2])
      ltac:(vm_compute; reflexivity) HFr KM) as KM';
    clear KM; rename KM' into KM end;
  let H' := fresh "HAE'" in assert (H' : env_agree k E0 E') by env_agree_chain HAE; clear HAE; rename H' into HAE
  end end;
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md _ |- _ =>
  lazymatch type of Hio with same_io ?m0 _ =>
  let H' := fresh "Hio'" in
  assert (H' : same_io m0 md)
    by (first [exact Hio | eapply same_io_trans; [exact Hio | apply same_io_materialized; apply same_but_materialized_wvb_any]]);
  clear Hio; rename H' into Hio end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac pbK_awr_tac x Hc HAE U2 :=
  apply (pbW_awr B x); [exact Hc | first [exact U2 | rewrite (proj1 HAE 2%nat ltac:(lia)); exact U2] | vm_compute; reflexivity].
Ltac pbK_run x Hc HAE KM Hio U2 :=
  lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tokH pb_tbl_ok HS HJ SHOK hk_Bspan; [pbK_awr_tac x Hc HAE U2 | ] end;
  pbK_post x HAE KM Hio U2.
Ltac pbK_run_to x Hc HAE KM Hio U2 stop :=
  lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tokH pb_tbl_ok HS HJ SHOK hk_Bspan stop; [pbK_awr_tac x Hc HAE U2 | ] end;
  pbK_post x HAE KM Hio U2.
Ltac pbK_branch HAE HB :=
  lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok pb_tbl_ok HS SH hk_Bspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HB end;
  rewrite ?branch_ltu_U, ?branch_geu_U, ?branch_eq_U, ?branch_ne_U in HB;
  lazymatch type of HAE with env_agree ?k ?E0 ?E1 =>
  first [ constr_eq E0 E1 | repeat (rewrite (U_agree k E0 E1 _ HAE) in HB by (vm_compute; reflexivity)) ] end.
Ltac pbK_ureg HAE :=
  lazymatch goal with |- U ?E (sr_get (ss_regs ?ss) ?r) = _ =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity) end;
  lazymatch type of HAE with env_agree ?k ?E0 ?E1 =>
  first [constr_eq E0 E1 | rewrite (U_agree k E0 E1 _ HAE) by (vm_compute; reflexivity)] end.
Ltac pbK_uat HAE H := first [exact H | rewrite (U_agree _ _ _ _ HAE) by (vm_compute; reflexivity); exact H].
Ltac pbK_ukept HAE H := pbK_ureg HAE; exact H.
Ltac pbK_fixed_tac := repeat split; vm_compute; reflexivity.
Ltac pbK_win := vm_compute; repeat first [left; reflexivity | right].

Ltac pbK_acs := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; unfold acallee_saved; lia end.

(* ---------------------------------- the exits of the token runs below ---------------------------------- *)
Lemma pbK_exit_ref : forall F fc (x : pctx) r cc n ck cl keys rf bad regs mem md L E ss ms md2 k cs v1 v2 v3 v4,
call_ok B x -> hp_core B x PAT_DOT cl pbK_rb0 regs mem md -> hp_fxw F fc -> hp_m_key x r cc n ck cl keys rf ->
Headamp.parse_cell (hp_kstr x ck) (Spa.child_at (hx_bs x) cc) = inl bad -> 0 <= bad <= 5 ->
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> ss_resv ss = None -> ss_pc ss = PC_REF ->
env_agree k (hk_env x regs L) E -> (28 <= k)%nat -> pbW_fixed (ss_regs ss) ->
U E (sr_get (ss_regs ss) 20%bv) = Z.of_nat (length cl) ->
U E (sr_get (ss_regs ss) 21%bv) = shadow_addr (hx_P x + r + 8) ->
U E (sr_get (ss_regs ss) 22%bv) = hx_P x + r + 8 ->
U E (sr_get (ss_regs ss) 14%bv) = hx_P x + r + 16 -> U E (sr_get (ss_regs ss) 16%bv) = 8 ->
U E (sr_get (ss_regs ss) 23%bv) = hx_P x + cc -> U E (sr_get (ss_regs ss) 5%bv) = bad ->
U E (sr_get (ss_regs ss) 17%bv) = shadow_addr (hx_P x + cc) ->
In (hk_temps cs) (ss_mem ss) -> bv_unsigned (ew E 2) = hx_spa x ->
In (YP09.mkChunk 0x10 (CVal 8 v1)) cs -> U E v1 = (hx_P x + r + 8) mod 8 + 3 ->
In (YP09.mkChunk 0x20 (CVal 8 v2)) cs -> U E v2 = rf ->
In (YP09.mkChunk 0x28 (CVal 8 v3)) cs -> U E v3 = hx_P x + r + 16 ->
In (YP09.mkChunk 0x18 (CVal 8 v4)) cs -> U E v4 = keys + 1 ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_DOT) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
pbK_REF_ok B MT x r cc n ck cl keys rf -> SRr rsegs (hx_W x) (mkCfg ms md2) (PPOST B MT x).
Proof.
intros F fc x r cc n ck cl keys rf bad regs mem md L E ss ms md2 k cs v1 v2 v3 v4 Hc HC Hfx HM Hpc Hbad HS Hrv Hpp HAE Hk
  Hfix U20 U21 U22 U14 U16 U23 U5 U17 Hin U2 C1 V1 C2 V2 C3 V3 C4 V4 HJ Hio KM HREF.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & (Hcl & _ & _) & _).
rewrite (pbW_cfg_stop F fc E ss ms _ PC_REF md2 HS Hrv Hpp).
apply (HREF bad F fc (ms_regs ms) (ms_mem ms) md2).
split; [exact (pbW_stop B errno_low F fc x PAT_DOT cl _ regs mem md L E ss ms md2 k Hc HC ltac:(lia) eq_refl HS HAE Hk Hfix
  HJ Hio KM)|].
split; [exact Hfx|]. split; [exact HM|]. split; [exact Hpc|]. split; [exact Hbad|].
split; [exact (pbW_loop_stop F fc x r cl rf E ss ms cs v1 v2 v3 HS U20 U21 U22 Hin U2 C1 V1 C2 V2 C3 V3)|].
split; [split; [exact (pbW_reg_U F fc E ss ms _ 14%bv _ HS U14) | exact (pbW_reg_U F fc E ss ms _ 16%bv _ HS U16)]|].
split; [exact (pbW_reg_U F fc E ss ms _ 23%bv _ HS U23)|].
split; [exact (pbW_reg_U F fc E ss ms _ 5%bv _ HS U5)|].
split; [exact (pbW_reg_U F fc E ss ms _ 17%bv _ HS U17)|].
exact (pbW_temps_val F fc x E ss ms cs 0x18 v4 _ HS Hin U2 C4 V4).
Qed.

Lemma pbK_exit_ch : forall F fc (x : pctx) r cc n ck cl keys rf p regs mem md L E ss ms md2 k cs v1 v2 v3 v4 v5,
call_ok B x -> hp_core B x PAT_DOT cl pbK_rb0 regs mem md -> hp_fxw F fc -> hp_m_key x r cc n ck cl keys rf ->
pbK_KS x ck p -> 0 <= p <= Headamp.HA_SENS ->
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> ss_resv ss = None -> ss_pc ss = PC_CH ->
env_agree k (hk_env x regs L) E -> (28 <= k)%nat -> pbW_fixed (ss_regs ss) ->
U E (sr_get (ss_regs ss) 20%bv) = Z.of_nat (length cl) ->
U E (sr_get (ss_regs ss) 21%bv) = shadow_addr (hx_P x + r + 8) ->
U E (sr_get (ss_regs ss) 22%bv) = hx_P x + r + 8 ->
U E (sr_get (ss_regs ss) 14%bv) = hx_P x + r + 16 -> U E (sr_get (ss_regs ss) 16%bv) = 8 ->
U E (sr_get (ss_regs ss) 23%bv) = hx_P x + cc -> getr (ms_regs ms) 24%bv = w64 (pbK_ch x ck) ->
U E (sr_get (ss_regs ss) 13%bv) = p -> U E (sr_get (ss_regs ss) 11%bv) = (if p =? Headamp.HA_SENS then 0 else 1) ->
U E (sr_get (ss_regs ss) 17%bv) = shadow_addr (hx_P x + cc) ->
In (hk_temps cs) (ss_mem ss) -> bv_unsigned (ew E 2) = hx_spa x ->
In (YP09.mkChunk 0x10 (CVal 8 v1)) cs -> U E v1 = (hx_P x + r + 8) mod 8 + 3 ->
In (YP09.mkChunk 0x20 (CVal 8 v2)) cs -> U E v2 = rf ->
In (YP09.mkChunk 0x28 (CVal 8 v3)) cs -> U E v3 = hx_P x + r + 16 ->
In (YP09.mkChunk 0x18 (CVal 8 v4)) cs -> U E v4 = keys + 1 ->
In (YP09.mkChunk 0x30 (CVal 8 v5)) cs -> U E v5 = shadow_addr (hx_P x + cc) ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_DOT) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
pbK_CH_ok B MT x r cc n ck cl keys rf -> SRr rsegs (hx_W x) (mkCfg ms md2) (PPOST B MT x).
Proof.
intros F fc x r cc n ck cl keys rf p regs mem md L E ss ms md2 k cs v1 v2 v3 v4 v5 Hc HC Hfx HM HKS Hp HS Hrv Hpp HAE Hk
  Hfix U20 U21 U22 U14 U16 U23 G24 U13 U11 U17 Hin U2 C1 V1 C2 V2 C3 V3 C4 V4 C5 V5 HJ Hio KM HCH.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & (Hcl & _ & _) & _).
rewrite (pbW_cfg_stop F fc E ss ms _ PC_CH md2 HS Hrv Hpp).
apply (HCH p F fc (ms_regs ms) (ms_mem ms) md2).
split; [exact (pbW_stop B errno_low F fc x PAT_DOT cl _ regs mem md L E ss ms md2 k Hc HC ltac:(lia) eq_refl HS HAE Hk Hfix
  HJ Hio KM)|].
split; [exact Hfx|]. split; [exact HM|]. split; [exact HKS|]. split; [exact Hp|].
split; [exact (pbW_loop_stop F fc x r cl rf E ss ms cs v1 v2 v3 HS U20 U21 U22 Hin U2 C1 V1 C2 V2 C3 V3)|].
split; [split; [exact (pbW_reg_U F fc E ss ms _ 14%bv _ HS U14) | exact (pbW_reg_U F fc E ss ms _ 16%bv _ HS U16)]|].
split; [exact (pbW_reg_U F fc E ss ms _ 23%bv _ HS U23)|].
split; [exact G24|].
split; [exact (pbW_reg_U F fc E ss ms _ 13%bv _ HS U13)|].
split; [exact (pbW_reg_U F fc E ss ms _ 11%bv _ HS U11)|].
split; [exact (pbW_reg_U F fc E ss ms _ 17%bv _ HS U17)|].
split; [exact (pbW_temps_val F fc x E ss ms cs 0x18 v4 _ HS Hin U2 C4 V4)|].
exact (pbW_temps_val F fc x E ss ms cs 0x30 v5 _ HS Hin U2 C5 V5).
Qed.

Lemma pbK_exit_sc : forall F fc (x : pctx) r cc n ck cl keys rf (i : nat) regs mem md L E ss ms md2 k cs v1 v2 v3 v4 v5,
call_ok B x -> hp_core B x PAT_DOT cl pbK_rb0 regs mem md -> hp_fxw F fc -> hp_m_key x r cc n ck cl keys rf ->
(i < 3)%nat -> pbK_e x ck <> 0 -> bv_unsigned (nth (Z.to_nat (pbK_e x ck)) (pbK_str x ck) Cursor.NUL) = 46 ->
(forall j, (j < i)%nat -> pbK_nm x ck <> pbK_lnm j) ->
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> ss_resv ss = None -> ss_pc ss = B_TRAMP_STRCMP ->
env_agree k (hk_env x regs L) E -> (28 <= k)%nat -> pbW_fixed (ss_regs ss) ->
U E (sr_get (ss_regs ss) 20%bv) = Z.of_nat (length cl) ->
U E (sr_get (ss_regs ss) 21%bv) = shadow_addr (hx_P x + r + 8) ->
U E (sr_get (ss_regs ss) 22%bv) = hx_P x + r + 8 ->
U E (sr_get (ss_regs ss) 23%bv) = hx_P x + cc -> getr (ms_regs ms) 24%bv = w64 (pbK_ch x ck) ->
U E (sr_get (ss_regs ss) 25%bv) = pbK_y x ck -> U E (sr_get (ss_regs ss) 10%bv) = pbK_y x ck ->
U E (sr_get (ss_regs ss) 11%bv) = pbK_lit i -> U E (sr_get (ss_regs ss) 1%bv) = pbK_ret i ->
In (hk_temps cs) (ss_mem ss) -> bv_unsigned (ew E 2) = hx_spa x ->
In (YP09.mkChunk 0x10 (CVal 8 v1)) cs -> U E v1 = (hx_P x + r + 8) mod 8 + 3 ->
In (YP09.mkChunk 0x20 (CVal 8 v2)) cs -> U E v2 = rf ->
In (YP09.mkChunk 0x28 (CVal 8 v3)) cs -> U E v3 = hx_P x + r + 16 ->
In (YP09.mkChunk 0x18 (CVal 8 v4)) cs -> U E v4 = keys + 1 ->
In (YP09.mkChunk 0x30 (CVal 8 v5)) cs -> U E v5 = shadow_addr (hx_P x + cc) ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_DOT) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
pbK_SC_ok B MT x r cc n ck cl keys rf i -> SRr rsegs (hx_W x) (mkCfg ms md2) (PPOST B MT x).
Proof.
intros F fc x r cc n ck cl keys rf i regs mem md L E ss ms md2 k cs v1 v2 v3 v4 v5 Hc HC Hfx HM Hi He0 Hdot Hne HS Hrv Hpp
  HAE Hk Hfix U20 U21 U22 U23 G24 U25 U10 U11 U1 Hin U2 C1 V1 C2 V2 C3 V3 C4 V4 C5 V5 HJ Hio KM HSC.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & (Hcl & _ & _) & _).
rewrite (pbW_cfg_stop F fc E ss ms _ B_TRAMP_STRCMP md2 HS Hrv Hpp).
apply (HSC F fc (ms_regs ms) (ms_mem ms) md2).
split; [exact (pbW_stop B errno_low F fc x PAT_DOT cl _ regs mem md L E ss ms md2 k Hc HC ltac:(lia) eq_refl HS HAE Hk Hfix
  HJ Hio KM)|].
split; [exact Hfx|]. split; [exact HM|]. split; [exact Hi|]. split; [exact He0|]. split; [exact Hdot|]. split; [exact Hne|].
split; [exact (pbW_loop_stop F fc x r cl rf E ss ms cs v1 v2 v3 HS U20 U21 U22 Hin U2 C1 V1 C2 V2 C3 V3)|].
split; [exact (pbW_reg_U F fc E ss ms _ 23%bv _ HS U23)|].
split; [exact G24|].
split; [exact (pbW_reg_U F fc E ss ms _ 25%bv _ HS U25)|].
split; [exact (pbW_reg_U F fc E ss ms _ 10%bv _ HS U10)|].
split; [exact (pbW_reg_U F fc E ss ms _ 11%bv _ HS U11)|].
split; [exact (pbW_reg_U F fc E ss ms _ 1%bv _ HS U1)|].
split; [exact (pbW_temps_val F fc x E ss ms cs 0x18 v4 _ HS Hin U2 C4 V4)|].
exact (pbW_temps_val F fc x E ss ms cs 0x30 v5 _ HS Hin U2 C5 V5).
Qed.

(* ---------------------------------- the return of the i-th strcmp call ---------------------------------- *)
Definition pbK_RT_at (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z) (i : nat) (v : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_DOT cl pbK_rb0 regs mem md /\ hp_fxw F fc /\ hp_m_key x r cc n ck cl keys rf /\
(i < 3)%nat /\ pbK_e x ck <> 0 /\
bv_unsigned (nth (Z.to_nat (pbK_e x ck)) (pbK_str x ck) Cursor.NUL) = 46 /\
(forall j, (j < i)%nat -> pbK_nm x ck <> pbK_lnm j) /\
pb_loop x r cl rf regs mem /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 24 = w64 (pbK_ch x ck) /\ getr regs 25 = w64 (pbK_y x ck) /\
getr regs 10 = w64 v /\ -1 <= v <= 1 /\ (v = 0 <-> pbK_nm x ck = pbK_lnm i) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 24) 8 (keys + 1) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)).

Definition pbK_RT_ok (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z) (i : nat) : Prop :=
forall v F fc regs mem md, pbK_RT_at x r cc n ck cl keys rf i v F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs (pbK_ret i) regs mem md) (PPOST B MT x).

Lemma pbK_SC_of_RT : forall (x : pctx) r cc n ck cl keys rf i, call_ok B x ->
pbK_RT_ok x r cc n ck cl keys rf i -> pbK_SC_ok B MT x r cc n ck cl keys rf i.
Proof.
intros x r cc n ck cl keys rf i Hc HRT F fc regs mem md HSC.
pose proof HSC as (HC & Hfx & HM & Hi & He0 & Hdot & Hne & HL & R23 & R24 & R25 & R10 & R11 & R1 & V24 & V48).
pose proof HM as (Hnull & _ & _ & _ & _ & _ & _ & (Hcl & _ & _) & _).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
pose proof (hk_stack B x Hc) as HS0. pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5).
pose proof alloc_ceiling_value as [[AC1 AC2] _].
pose proof (hk_pod_at_cut B pb_segs_low x PAT_DOT cl _ regs mem md errno_low Hc Hnull HC ltac:(lia)) as (HG & HRA & HHV).
assert (Hsp : spZ regs = hx_spa x) by (unfold spZ; rewrite C2; unfold w64; apply unsigned_lit_small; lia).
assert (HLc : hd_cstr rsegs (w_H (hx_W x)) mem (pbK_lit i) (hd_zbytes (pbK_lnm i))).
{ apply (hk_cstr_at_cut B pb_segs_low x PAT_DOT cl _ regs mem md _ _ errno_low Hc HC ltac:(lia) eq_refl
    (pbK_lit_cstr B x i Hc Hi)).
  intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj. rewrite HBerrno.
  assert (Lj : Z.of_nat (length (pbK_lnm i)) <= 7) by (destruct i as [|[|[|i]]]; cbn; lia).
  exact (proj2 (pbK_lit_img i (pbK_lit i + j) Hi ltac:(lia))). }
apply (pbK_strcmp_call B HBerrno STRCMP x r cc n ck cl keys rf i F fc regs mem md _ Hc HM Hi He0 Hdot (proj1 HC) Hsp C3 C4
  R10 R11 R1 HG HRA HHV HLc).
intros regs2 mem2 md2 v HJ2 HPr Hio2 H10 Hv Hiff HK2.
assert (HKc : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x - 3 * ESTACK <= a < hx_spa x) ->
  ~ (hx_spa x + 96 <= a < hx_spa x + 104) -> ~ (as_errno B <= a < as_errno B + 4) -> hx_view x mem2 a = hx_view x mem a).
{ intros a Ha Hw _ _. apply HK2; [exact Ha|]. intros Hw'. apply Hw. unfold ESTACK in *. lia. }
assert (Herr2 : exists ev', rd32 (hx_view x mem2) (as_errno B) ev').
{ destruct (hk_core_cells B x _ _ _ _ _ _ HC) as (_ & _ & (ev' & Hev)). exists ev'.
  apply (hk_rd32_kept (hx_view x mem)); [|exact Hev].
  intros j Hj. apply HK2; rewrite HBerrno; [lia|].
  pose proof (hk_window_band B x (hx_spa x - 2 * ESTACK) Hc ltac:(unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia)).
  lia. }
assert (HC2 : hp_core B x PAT_DOT cl pbK_rb0 regs2 mem2 md2)
  by exact (hk_core_of_call B pb_segs_low x PAT_DOT cl _ regs mem md regs2 mem2 md2 errno_low Hc HC ltac:(lia) eq_refl
    HJ2 HPr Hio2 HKc Herr2).
apply (HRT v F fc regs2 mem2 md2).
pose proof HL as (L20 & L21 & L22 & L16 & L32 & L40).
assert (KV : forall o w, 0 <= o /\ o + 8 <= 96 -> val_mem rsegs (hx_rd x mem) (hx_spa x + o) 8 w ->
  val_mem rsegs (hx_rd x mem2) (hx_spa x + o) 8 w)
  by (intros o w Ho Hw; exact (hk_temps_kept_call B x mem mem2 o w errno_low Hc HKc (or_introl Ho) Hw)).
split; [exact HC2|]. split; [exact Hfx|]. split; [exact HM|]. split; [exact Hi|]. split; [exact He0|].
split; [exact Hdot|]. split; [exact Hne|].
split.
{ unfold pb_loop. rewrite (pbW_pres regs regs2 20%bv HPr ltac:(pbK_acs)), (pbW_pres regs regs2 21%bv HPr ltac:(pbK_acs)),
    (pbW_pres regs regs2 22%bv HPr ltac:(pbK_acs)).
  split; [exact L20|]. split; [exact L21|]. split; [exact L22|].
  split; [exact (KV 16 _ ltac:(lia) L16)|]. split; [exact (KV 32 _ ltac:(lia) L32)|]. exact (KV 40 _ ltac:(lia) L40). }
rewrite (pbW_pres regs regs2 23%bv HPr ltac:(pbK_acs)), (pbW_pres regs regs2 24%bv HPr ltac:(pbK_acs)),
  (pbW_pres regs regs2 25%bv HPr ltac:(pbK_acs)).
split; [exact R23|]. split; [exact R24|]. split; [exact R25|].
split; [exact H10|]. split; [exact Hv|]. split; [exact Hiff|].
split; [exact (KV 24 _ ltac:(lia) V24) | exact (KV 48 _ ltac:(lia) V48)].
Qed.

(* ---------------------------------- the runs after the i-th strcmp ---------------------------------- *)
(* 0x84e38 / 0x84e4c beqz a0: the name is the literal -> (a3, a1) = (0, 1) / (1, 1), reloads, CH 0x84eb0; else the next
   strcmp. 0x84e60: reloads, t0 = 4, bnez a0 -> 0x84ebc (no param); else (a1, a3) = (0, 2), CH. Env: L = pbK_LC
   ([spa + 16]; keys + 1; rf; P + r + 16; shadow (P + cc)) at slots 47 .. 51. *)
Definition pbK_ssR (pc : Z) : sstate := mkSS pc sr_atoms [hk_saves; hk_temps pbK_csC] None (mkFacts (hk_atoms ++ []) [] []).

Lemma pbK_RT : forall (x : pctx) r cc n ck cl keys rf i, call_ok B x ->
(forall rf', ADV_ok B MT x r cc n None cl (keys + 1) rf') -> (forall ch p, VAL_ok B MT x r cc n ch p cl keys rf) ->
((i < 2)%nat -> pbK_SC_ok B MT x r cc n ck cl keys rf (S i)) ->
pbK_RT_ok x r cc n ck cl keys rf i.
Proof.
intros x r cc n ck cl keys rf i Hc HADV HVAL HSC v F fc regs mem md HR.
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsl.
pose proof HR as (HC & Hfx & HM & Hi & He0 & Hdot & Hne & HL & R23 & R24 & R25 & R10 & Hv & Hiff & V24 & V48).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hin & Hn & HKo & Hs & HPfx & HW).
pose proof Hs as (Hcl & Hk0 & Hrf). pose proof Hst as (Hr16 & Hr8 & Hvs & Hrl).
pose proof HL as (L20 & L21 & L22 & L16 & L32 & L40).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hl8 & Hl8m & HSZ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & HOFF).
pose proof (hk_stack B x Hc) as HS0. pose proof (hk_frame_win B x Hc) as HFW.
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
pose proof (hgw_next_bounds x r cc Hst Hc1 Hc8 Hin) as (Hnx & _).
pose proof (pbK_keys_small x r cc n ck cl keys rf HM ltac:(unfold hx_len in Hl8; lia)) as Hks.
pose proof (hgw_u32_range (hx_bs x) (r + 8)) as RVS.
destruct (pbK_str_pod x ck HKo HPfx) as (HNs & HLs & HBs).
destruct (pbK_nm_pod x ck HKo HPfx He0 Hdot) as (HNn & He & HLn & HBn).
pose proof HKo as (Hck0 & _).
unfold hp_vs in *.
assert (Hhi : hx_P x + hx_len x + 8 <= 2 ^ 47)
by (destruct HAM as [HAl|[HAh1 HAh2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8 ltac:(lia)) as RM.
assert (Hsh : forall a, 0 <= a <= 2 ^ 47 -> 0 <= shadow_addr a < 2 ^ 64).
{ intros a Ha. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound a 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
assert (Hy : 0 <= pbK_y x ck < 2 ^ 47) by (unfold pbK_y, pbK_xs; lia).
pose proof (hk_out B x Hc) as (Hcap & _).
set (L := pbK_LC x r cc keys rf).
set (E0 := hk_env x regs L).
assert (EG : forall (n : nat) (rg : bv 5) v, Z.of_nat n = bv_unsigned rg -> getr regs rg = w64 v -> ew E0 n = w64 v).
{ intros n0 rg v0 Hn0 Hv0. subst E0. rewrite (hk_env_reg x regs L n0 rg Hn0). exact Hv0. }
assert (UG : forall (n : nat) (rg : bv 5) v, Z.of_nat n = bv_unsigned rg -> getr regs rg = w64 v -> 0 <= v < 2 ^ 64 ->
  U E0 (SOff n 0) = v) by (intros n0 rg v0 Hn0 Hv0 Hr; apply U_atom; [exact (EG n0 rg v0 Hn0 Hv0) | exact Hr]).
assert (UL : forall j v, nth j L (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 -> U E0 (SOff (47 + j) 0) = v)
by (intros j v0 Hv0 Hr; apply U_atom; [subst E0; rewrite hk_env_seg; exact Hv0 | exact Hr]).
assert (U2 : bv_unsigned (ew E0 2) = hx_spa x) by (rewrite (EG 2%nat 2%bv _ eq_refl C2); apply unsigned_lit_small; lia).
assert (E47 : ew E0 47 = w64 ((hx_P x + r + 8) mod 8 + 3)) by exact (hk_env_seg x regs L 0).
assert (E48 : ew E0 48 = w64 (keys + 1)) by exact (hk_env_seg x regs L 1).
assert (E49 : ew E0 49 = w64 rf) by exact (hk_env_seg x regs L 2).
assert (E50 : ew E0 50 = w64 (hx_P x + r + 16)) by exact (hk_env_seg x regs L 3).
assert (E51 : ew E0 51 = w64 (shadow_addr (hx_P x + cc))) by exact (hk_env_seg x regs L 4).
assert (HS : st_ok (fx := mkFP F fc) rsegs E0 (pbK_ssR (pbK_ret i))
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 (pbK_ret i)) mem (seg_rom rsegs)))).
{ unfold pbK_ssR. apply (pbW_entry B F fc x PAT_DOT cl _ regs mem md L (pbK_ret i) _ _ _ _ Hc HC).
  - unfold hk_env. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold pbK_csC. repeat apply Forall_cons; try apply Forall_nil.
    + apply (pbK_chunk8 E0 _ _ 16 47 _ E47); [lia | exact L16].
    + apply (pbK_chunk8 E0 _ _ 24 48 _ E48); [lia | exact V24].
    + apply (pbK_chunk8 E0 _ _ 32 49 _ E49); [lia | exact L32].
    + apply (pbK_chunk8 E0 _ _ 40 50 _ E50); [lia | exact L40].
    + apply (pbK_chunk8 E0 _ _ 48 51 _ E51); [apply Hsh; lia | exact V48].
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. unfold hk_saves, hk_temps.
    cbn [map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E0.
    rewrite (EG 2%nat 2%bv _ eq_refl C2), (EG 8%nat 8%bv _ eq_refl C8), !unsigned_lit_small by (unfold hx_sp in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *. repeat split; lia.
  - first [exact I | apply Forall_nil | constructor]. }
assert (SHOK : sh_ok rsegs hk_Bx [] E0 (hx_rd x mem)) by apply Forall_nil.
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & _ & _).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
  hx_rd x mem (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) by reflexivity.
pose proof (same_io_refl md) as Hio.
assert (HAE : env_agree 52 E0 E0) by apply env_agree_refl.
assert (U10 : U E0 (SOff 10 0) = 0 <-> v = 0).
{ pose proof (pbW_U_reg0 x regs L 10 10%bv eq_refl) as Hr0. fold E0 in Hr0. rewrite Hr0, R10.
  split; [|intros ->; reflexivity].
  intros Hw. assert (v = -1 \/ v = 0 \/ v = 1) as [-> | [-> | ->]] by lia; [|reflexivity|];
  apply (f_equal bv_unsigned) in Hw; vm_compute in Hw; discriminate Hw. }
assert (G24 : forall E ss ms, st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> env_agree 52 E0 E ->
  sr_get (ss_regs ss) 24%bv = SOff 24 0 -> getr (ms_regs ms) 24%bv = w64 (pbK_ch x ck)).
{ intros E ss ms HS' HAE' H24. rewrite (pbW_reg_kept F fc E0 E ss ms _ 52 24 24%bv HS' HAE' ltac:(lia) H24).
  subst E0. rewrite (hk_env_reg x regs L 24 24%bv eq_refl). exact R24. }
assert (UY : U E0 (SOff 25 0) = pbK_y x ck) by (apply (UG 25%nat 25%bv); [reflexivity | exact R25 | lia]).
unfold cfg_at.
destruct i as [|[|[|i]]]; [| | | lia].
- (* i = 0 *)
  change (w64 (pbK_ret 0)) with (Z_to_bv 64 (pbK_ret 0)).
  pbK_run x Hc HAE KM Hio U2.
  pbK_branch HAE HB.
  + (* the name is "phantom" *)
    rewrite ?U_lit in HB by lia. apply Z.eqb_eq in HB. apply U10 in HB. apply Hiff in HB. cbn [pbK_lnm nth] in HB.
    pbK_run_to x Hc HAE KM Hio U2 PC_CH.
    eapply (pbK_exit_ch F fc x r cc n ck cl keys rf Headamp.HA_PHANTOM regs mem md L _ _ _ _ 52 pbK_csC (SOff 47 0)
      (SOff 49 0) (SOff 50 0) (SOff 48 0) (SOff 51 0) Hc HC Hfx HM);
    [ unfold pbK_KS; rewrite (pbK_key_named x ck HNs He0 Hdot), HB; reflexivity
    | unfold Headamp.HA_PHANTOM, Headamp.HA_SENS; lia
    | exact HS | vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbK_fixed_tac
    | pbK_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
    | pbK_ukept HAE (UG 21%nat 21%bv _ eq_refl L21 ltac:(apply Hsh; lia))
    | pbK_ukept HAE (UG 22%nat 22%bv _ eq_refl L22 ltac:(lia))
    | pbK_ukept HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ukept HAE (UG 23%nat 23%bv _ eq_refl R23 ltac:(lia))
    | apply (G24 _ _ _ HS HAE); vm_compute; reflexivity
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ukept HAE (UL 4%nat _ eq_refl ltac:(apply Hsh; lia))
    | pbK_win | exact U2
    | pbK_win | pbK_uat HAE (UL 0%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 2%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 1%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 4%nat _ eq_refl ltac:(apply Hsh; lia))
    | exact HJ | exact Hio | exact KM | exact (pbK_CH B MT errno_low x r cc n ck cl keys rf Hc HADV HVAL) ].
  + (* not "phantom": strcmp(name, "pad") *)
    rewrite ?U_lit in HB by lia. apply Z.eqb_neq in HB.
    assert (Hn0 : pbK_nm x ck <> pbK_lnm 0) by (intros E; apply HB, U10, Hiff, E).
    pbK_run_to x Hc HAE KM Hio U2 B_TRAMP_STRCMP.
    eapply (pbK_exit_sc F fc x r cc n ck cl keys rf 1 regs mem md L _ _ _ _ 52 pbK_csC (SOff 47 0)
      (SOff 49 0) (SOff 50 0) (SOff 48 0) (SOff 51 0) Hc HC Hfx HM);
    [ lia | exact He0 | exact Hdot | intros j Hj; assert (j = 0%nat) as -> by lia; exact Hn0
    | exact HS | vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbK_fixed_tac
    | pbK_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
    | pbK_ukept HAE (UG 21%nat 21%bv _ eq_refl L21 ltac:(apply Hsh; lia))
    | pbK_ukept HAE (UG 22%nat 22%bv _ eq_refl L22 ltac:(lia))
    | pbK_ukept HAE (UG 23%nat 23%bv _ eq_refl R23 ltac:(lia))
    | apply (G24 _ _ _ HS HAE); vm_compute; reflexivity
    | pbK_ukept HAE UY
    | pbK_ukept HAE UY
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_win | exact U2
    | pbK_win | pbK_uat HAE (UL 0%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 2%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 1%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 4%nat _ eq_refl ltac:(apply Hsh; lia))
    | exact HJ | exact Hio | exact KM | exact (HSC ltac:(lia)) ].
- (* i = 1 *)
  change (w64 (pbK_ret 1)) with (Z_to_bv 64 (pbK_ret 1)).
  pbK_run x Hc HAE KM Hio U2.
  pbK_branch HAE HB.
  + (* the name is "pad" *)
    rewrite ?U_lit in HB by lia. apply Z.eqb_eq in HB. apply U10 in HB. apply Hiff in HB. cbn [pbK_lnm nth] in HB.
    pbK_run_to x Hc HAE KM Hio U2 PC_CH.
    eapply (pbK_exit_ch F fc x r cc n ck cl keys rf Headamp.HA_PAD regs mem md L _ _ _ _ 52 pbK_csC (SOff 47 0)
      (SOff 49 0) (SOff 50 0) (SOff 48 0) (SOff 51 0) Hc HC Hfx HM);
    [ unfold pbK_KS; rewrite (pbK_key_named x ck HNs He0 Hdot), HB; reflexivity
    | unfold Headamp.HA_PAD, Headamp.HA_SENS; lia
    | exact HS | vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbK_fixed_tac
    | pbK_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
    | pbK_ukept HAE (UG 21%nat 21%bv _ eq_refl L21 ltac:(apply Hsh; lia))
    | pbK_ukept HAE (UG 22%nat 22%bv _ eq_refl L22 ltac:(lia))
    | pbK_ukept HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ukept HAE (UG 23%nat 23%bv _ eq_refl R23 ltac:(lia))
    | apply (G24 _ _ _ HS HAE); vm_compute; reflexivity
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ukept HAE (UL 4%nat _ eq_refl ltac:(apply Hsh; lia))
    | pbK_win | exact U2
    | pbK_win | pbK_uat HAE (UL 0%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 2%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 1%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 4%nat _ eq_refl ltac:(apply Hsh; lia))
    | exact HJ | exact Hio | exact KM | exact (pbK_CH B MT errno_low x r cc n ck cl keys rf Hc HADV HVAL) ].
  + (* not "pad": strcmp(name, "sens") *)
    rewrite ?U_lit in HB by lia. apply Z.eqb_neq in HB.
    assert (Hn1 : pbK_nm x ck <> pbK_lnm 1) by (intros E; apply HB, U10, Hiff, E).
    pbK_run_to x Hc HAE KM Hio U2 B_TRAMP_STRCMP.
    eapply (pbK_exit_sc F fc x r cc n ck cl keys rf 2 regs mem md L _ _ _ _ 52 pbK_csC (SOff 47 0)
      (SOff 49 0) (SOff 50 0) (SOff 48 0) (SOff 51 0) Hc HC Hfx HM);
    [ lia | exact He0 | exact Hdot
    | intros j Hj; destruct (Nat.eq_dec j 1) as [->|Nj]; [exact Hn1 | apply Hne; lia]
    | exact HS | vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbK_fixed_tac
    | pbK_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
    | pbK_ukept HAE (UG 21%nat 21%bv _ eq_refl L21 ltac:(apply Hsh; lia))
    | pbK_ukept HAE (UG 22%nat 22%bv _ eq_refl L22 ltac:(lia))
    | pbK_ukept HAE (UG 23%nat 23%bv _ eq_refl R23 ltac:(lia))
    | apply (G24 _ _ _ HS HAE); vm_compute; reflexivity
    | pbK_ukept HAE UY
    | pbK_ukept HAE UY
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_win | exact U2
    | pbK_win | pbK_uat HAE (UL 0%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 2%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 1%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 4%nat _ eq_refl ltac:(apply Hsh; lia))
    | exact HJ | exact Hio | exact KM | exact (HSC ltac:(lia)) ].
- (* i = 2 *)
  change (w64 (pbK_ret 2)) with (Z_to_bv 64 (pbK_ret 2)).
  pbK_run x Hc HAE KM Hio U2.
  pbK_branch HAE HB.
  + (* not "sens": no param, the refusal BAD_KEY *)
    rewrite ?U_lit in HB by lia. apply negb_true_iff, Z.eqb_neq in HB.
    assert (Hn2 : pbK_nm x ck <> pbK_lnm 2) by (intros E; apply HB, U10, Hiff, E).
    assert (Hkb : Headamp.parse_key (pbK_str x ck) = Headamp.KBad).
    { rewrite (pbK_key_named x ck HNs He0 Hdot).
      rewrite (hgk_param_none _ (Hne 0%nat ltac:(lia)) (Hne 1%nat ltac:(lia)) Hn2). reflexivity. }
    pbK_run_to x Hc HAE KM Hio U2 PC_REF.
    eapply (pbK_exit_ref F fc x r cc n ck cl keys rf 4 regs mem md L _ _ _ _ 52 pbK_csC (SOff 47 0)
      (SOff 49 0) (SOff 50 0) (SOff 48 0) Hc HC Hfx HM (pbK_cell_bad x ck _ Hkb));
    [ lia
    | exact HS | vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbK_fixed_tac
    | pbK_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
    | pbK_ukept HAE (UG 21%nat 21%bv _ eq_refl L21 ltac:(apply Hsh; lia))
    | pbK_ukept HAE (UG 22%nat 22%bv _ eq_refl L22 ltac:(lia))
    | pbK_ukept HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ukept HAE (UG 23%nat 23%bv _ eq_refl R23 ltac:(lia))
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ukept HAE (UL 4%nat _ eq_refl ltac:(apply Hsh; lia))
    | pbK_win | exact U2
    | pbK_win | pbK_uat HAE (UL 0%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 2%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 1%nat _ eq_refl ltac:(lia))
    | exact HJ | exact Hio | exact KM | exact (pbK_REF B MT errno_low x r cc n ck cl keys rf Hc HADV) ].
  + (* the name is "sens" *)
    rewrite ?U_lit in HB by lia. apply negb_false_iff, Z.eqb_eq in HB. apply U10 in HB. apply Hiff in HB.
    cbn [pbK_lnm nth] in HB.
    pbK_run_to x Hc HAE KM Hio U2 PC_CH.
    eapply (pbK_exit_ch F fc x r cc n ck cl keys rf Headamp.HA_SENS regs mem md L _ _ _ _ 52 pbK_csC (SOff 47 0)
      (SOff 49 0) (SOff 50 0) (SOff 48 0) (SOff 51 0) Hc HC Hfx HM);
    [ unfold pbK_KS; rewrite (pbK_key_named x ck HNs He0 Hdot), HB; reflexivity
    | unfold Headamp.HA_SENS; lia
    | exact HS | vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbK_fixed_tac
    | pbK_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
    | pbK_ukept HAE (UG 21%nat 21%bv _ eq_refl L21 ltac:(apply Hsh; lia))
    | pbK_ukept HAE (UG 22%nat 22%bv _ eq_refl L22 ltac:(lia))
    | pbK_ukept HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ukept HAE (UG 23%nat 23%bv _ eq_refl R23 ltac:(lia))
    | apply (G24 _ _ _ HS HAE); vm_compute; reflexivity
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ukept HAE (UL 4%nat _ eq_refl ltac:(apply Hsh; lia))
    | pbK_win | exact U2
    | pbK_win | pbK_uat HAE (UL 0%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 2%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 1%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 4%nat _ eq_refl ltac:(apply Hsh; lia))
    | exact HJ | exact Hio | exact KM | exact (pbK_CH B MT errno_low x r cc n ck cl keys rf Hc HADV HVAL) ].
Qed.

(* the strcmp chain from the first call *)
Lemma pbK_SC0 : forall (x : pctx) r cc n ck cl keys rf, call_ok B x ->
(forall rf', ADV_ok B MT x r cc n None cl (keys + 1) rf') -> (forall ch p, VAL_ok B MT x r cc n ch p cl keys rf) ->
pbK_SC_ok B MT x r cc n ck cl keys rf 0.
Proof.
intros x r cc n ck cl keys rf Hc HADV HVAL.
assert (S2 : pbK_SC_ok B MT x r cc n ck cl keys rf 2)
  by (apply (pbK_SC_of_RT x r cc n ck cl keys rf 2 Hc); apply (pbK_RT x r cc n ck cl keys rf 2 Hc HADV HVAL); lia).
assert (S1 : pbK_SC_ok B MT x r cc n ck cl keys rf 1)
  by (apply (pbK_SC_of_RT x r cc n ck cl keys rf 1 Hc); apply (pbK_RT x r cc n ck cl keys rf 1 Hc HADV HVAL);
      intros _; exact S2).
apply (pbK_SC_of_RT x r cc n ck cl keys rf 0 Hc); apply (pbK_RT x r cc n ck cl keys rf 0 Hc HADV HVAL); intros _; exact S1.
Qed.

(* ---------------------------------- strtol and the dot (0x84ddc .. 0x84e34) ---------------------------------- *)
(* 0x84de0: s8 = ch; a0 = [sp + 96] = dot; t0 = 4; beq dot,s9 -> 0x84e80 (reloads) -> REF; reloads; the check of dot
   (shadow entry mkSHE 52 0 1); lbu c; bne c,'.' -> REF; s9 = dot + 1; a1 = "phantom"; a0 = s9; jal strcmp.
   Env: L = pbK_LC ++ [dot; c] at slots 47 .. 53. *)
Definition pbK_csA : list YP09.chunk := pbK_csC ++ [YP09.mkChunk 0x60 (CVal 8 (SOff 52 0))].
Definition pbK_dotr : YP09.region := YP09.mkRegion (Some 52%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 53 0))].
Definition pbK_fA : list (nat * afact) := [(52%nat, mkAF 1 (2 ^ 47 - 9) 0); (53%nat, mkAF 0 255 0)].
Definition pbK_ssA : sstate := mkSS PC_AFTER_STRTOL sr_atoms [hk_saves; hk_temps pbK_csA; pbK_dotr] None
  (mkFacts (hk_atoms ++ pbK_fA) [] []).
Definition pbK_SHA : list shent := [mkSHE 52 0 1].
Definition pbK_dc (x : pctx) (ck : Z) : Z := bv_unsigned (nth (Z.to_nat (pbK_e x ck)) (pbK_str x ck) Cursor.NUL).
Definition pbK_LA (x : pctx) (r cc ck keys rf : Z) : list word :=
  pbK_LC x r cc keys rf ++ [w64 (pbK_xs x ck + pbK_e x ck); w64 (pbK_dc x ck)].

Lemma pbK_U_off : forall E n v k, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + k < 2 ^ 64 -> U E (SOff n k) = v + k.
Proof.
intros E n v k H Hv Hk. rewrite U_SOff, H. unfold w64. rewrite unsigned_lit_small by exact Hv.
unfold zcanon, M64. apply Z.mod_small. exact Hk.
Qed.

Lemma pbK_ST : forall (x : pctx) r cc n ck cl keys rf, call_ok B x ->
(forall rf', ADV_ok B MT x r cc n None cl (keys + 1) rf') -> (forall ch p, VAL_ok B MT x r cc n ch p cl keys rf) ->
pbK_ST_ok B MT x r cc n ck cl keys rf.
Proof.
intros x r cc n ck cl keys rf Hc HADV HVAL F fc regs mem md HST.
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsl.
pose proof HST as (HC & Hfx & HM & HL & R23 & R25 & R10 & R11 & R12 & R1 & V24 & V48).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hin & Hn & HKo & Hs & HPfx & HW).
pose proof Hs as (Hcl & Hk0 & Hrf). pose proof Hst as (Hr16 & Hr8 & Hvs & Hrl).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
pose proof (hk_stack B x Hc) as HS0. pose proof (hk_frame_win B x Hc) as HFW.
pose proof alloc_ceiling_value as [[AC1 AC2] _].
pose proof (hk_pod_at_cut B pb_segs_low x PAT_DOT cl _ regs mem md errno_low Hc Hnull HC ltac:(lia)) as (HG & HRA & HHV).
assert (Hsp : spZ regs = hx_spa x) by (unfold spZ; rewrite C2; unfold w64; apply unsigned_lit_small; lia).
assert (HIMG : forall a, in_img rsegs a -> ~ (as_errno B <= a < as_errno B + 4) -> hx_view x mem a = hx_view x (hx_memc x) a)
  by (intros a Ha He; exact (hk_kept_img B pb_segs_low x PAT_DOT cl _ regs mem md a Hc HC ltac:(lia) Ha He)).
destruct (hk_core_cells B x _ _ _ _ _ _ HC) as (_ & _ & HEV).
apply (pbK_strtol_call B errno_low HBerrno STRTOL x r cc n ck cl keys rf F fc regs mem md _ Hc HM (proj1 HC) Hsp C3 C4
  R10 R11 R12 R1 HG HRA HHV HIMG HEV).
intros regs2 mem2 md2 HJ2 HPr Hio2 H10 Hend Herr2 HK2.
assert (HKc : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x - 3 * ESTACK <= a < hx_spa x) ->
  ~ (hx_spa x + 96 <= a < hx_spa x + 104) -> ~ (as_errno B <= a < as_errno B + 4) -> hx_view x mem2 a = hx_view x mem a).
{ intros a Ha H1 H2 H3. apply HK2; [exact Ha | lia | exact H3 | exact H1]. }
assert (HC2 : hp_core B x PAT_DOT cl pbK_rb0 regs2 mem2 md2)
  by exact (hk_core_of_call B pb_segs_low x PAT_DOT cl _ regs mem md regs2 mem2 md2 errno_low Hc HC ltac:(lia) eq_refl
    HJ2 HPr Hio2 HKc Herr2).
clear HG HRA HHV.
pose proof (hk_pod_at_cut B pb_segs_low x PAT_DOT cl _ regs2 mem2 md2 errno_low Hc Hnull HC2 ltac:(lia)) as (HG & HRA & HHV).
pose proof HL as (L20 & L21 & L22 & L16 & L32 & L40).
assert (KV : forall o w, 0 <= o /\ o + 8 <= 96 -> val_mem rsegs (hx_rd x mem) (hx_spa x + o) 8 w ->
  val_mem rsegs (hx_rd x mem2) (hx_spa x + o) 8 w)
  by (intros o w Ho Hw; exact (hk_temps_kept_call B x mem mem2 o w errno_low Hc HKc (or_introl Ho) Hw)).
pose proof (KV 16 _ ltac:(lia) L16) as L16'. pose proof (KV 32 _ ltac:(lia) L32) as L32'.
pose proof (KV 40 _ ltac:(lia) L40) as L40'. pose proof (KV 24 _ ltac:(lia) V24) as V24'.
pose proof (KV 48 _ ltac:(lia) V48) as V48'.
pose proof (val_mem_of_rdword rsegs (w_H (hx_W x)) mem2 (hx_spa x + 0x60) _ Hend) as V96.
rewrite <- (pbW_pres regs regs2 20%bv HPr ltac:(pbK_acs)) in L20.
rewrite <- (pbW_pres regs regs2 21%bv HPr ltac:(pbK_acs)) in L21.
rewrite <- (pbW_pres regs regs2 22%bv HPr ltac:(pbK_acs)) in L22.
rewrite <- (pbW_pres regs regs2 23%bv HPr ltac:(pbK_acs)) in R23.
rewrite <- (pbW_pres regs regs2 25%bv HPr ltac:(pbK_acs)) in R25.
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC2) as (D2 & D8 & D3 & D4 & D9 & D18 & D19 & D26 & D27).
clear regs mem md HST HC HL HK2 HKc KV L16 L32 L40 V24 V48 HJ2 HPr Hio2 Hend Herr2 HIMG HEV Hsp C2 C8 C3 C4 C9 C18 C19 C26 C27
  R10 R11 R12 R1.
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hl8 & Hl8m & HSZ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & HOFF).
pose proof (hk_pod_side B x Hc Hnull) as Hside.
pose proof (hgw_next_bounds x r cc Hst Hc1 Hc8 Hin) as (Hnx & _).
pose proof (pbK_keys_small x r cc n ck cl keys rf HM ltac:(unfold hx_len in Hl8; lia)) as Hks.
pose proof (hgw_u32_range (hx_bs x) (r + 8)) as RVS.
destruct (pbK_str_pod x ck HKo HPfx) as (HNs & HLs & HBs).
pose proof (hgk_end_le (pbK_str x ck)) as HE. fold (pbK_e x ck) in HE.
pose proof HKo as (Hck0 & _).
pose proof (hk_out B x Hc) as (Hcap & _).
unfold hp_vs in *.
assert (Hhi : hx_P x + hx_len x + 8 <= 2 ^ 47)
by (destruct HAM as [HAl|[HAh1 HAh2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8 ltac:(lia)) as RM.
assert (Hsh : forall a, 0 <= a <= 2 ^ 47 -> 0 <= shadow_addr a < 2 ^ 64).
{ intros a Ha. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound a 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
(* the dot byte c in the pod *)
destruct (hgw_pod_u8 (hx_rd x mem2) (hx_P x) (hx_bs x) (ck + 21 + pbK_e x ck) HG ltac:(lia) ltac:(unfold hx_len in *; lia))
  as [Vc Rc].
assert (Ec : bv_unsigned (nth (Z.to_nat (ck + 21 + pbK_e x ck)) (hx_bs x) Cursor.NUL) = pbK_dc x ck).
{ unfold pbK_dc. replace (Z.to_nat (ck + 21 + pbK_e x ck)) with (Z.to_nat (ck + 21) + Z.to_nat (pbK_e x ck))%nat by lia.
  rewrite HBs by lia. rewrite pbK_nth_app_nul by lia. reflexivity. }
rewrite Ec in Vc, Rc.
set (L := pbK_LA x r cc ck keys rf).
set (E0 := hk_env x regs2 L).
assert (EG : forall (n : nat) (rg : bv 5) v, Z.of_nat n = bv_unsigned rg -> getr regs2 rg = w64 v -> ew E0 n = w64 v).
{ intros n0 rg v0 Hn0 Hv0. subst E0. rewrite (hk_env_reg x regs2 L n0 rg Hn0). exact Hv0. }
assert (UG : forall (n : nat) (rg : bv 5) v, Z.of_nat n = bv_unsigned rg -> getr regs2 rg = w64 v -> 0 <= v < 2 ^ 64 ->
  U E0 (SOff n 0) = v) by (intros n0 rg v0 Hn0 Hv0 Hr; apply U_atom; [exact (EG n0 rg v0 Hn0 Hv0) | exact Hr]).
assert (UL : forall j v, nth j L (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 -> U E0 (SOff (47 + j) 0) = v)
by (intros j v0 Hv0 Hr; apply U_atom; [subst E0; rewrite hk_env_seg; exact Hv0 | exact Hr]).
assert (U2 : bv_unsigned (ew E0 2) = hx_spa x) by (rewrite (EG 2%nat 2%bv _ eq_refl D2); apply unsigned_lit_small; lia).
assert (E47 : ew E0 47 = w64 ((hx_P x + r + 8) mod 8 + 3)) by exact (hk_env_seg x regs2 L 0).
assert (E48 : ew E0 48 = w64 (keys + 1)) by exact (hk_env_seg x regs2 L 1).
assert (E49 : ew E0 49 = w64 rf) by exact (hk_env_seg x regs2 L 2).
assert (E50 : ew E0 50 = w64 (hx_P x + r + 16)) by exact (hk_env_seg x regs2 L 3).
assert (E51 : ew E0 51 = w64 (shadow_addr (hx_P x + cc))) by exact (hk_env_seg x regs2 L 4).
assert (E52 : ew E0 52 = w64 (pbK_xs x ck + pbK_e x ck)) by exact (hk_env_seg x regs2 L 5).
assert (E53 : ew E0 53 = w64 (pbK_dc x ck)) by exact (hk_env_seg x regs2 L 6).
assert (E27 : ew E0 27 = w64 SHADOW_OFF) by exact (EG 27%nat 27%bv _ eq_refl D27).
assert (Hdot : 1 <= pbK_xs x ck + pbK_e x ck <= 2 ^ 47 - 9) by (unfold pbK_xs; unfold hx_len in *; lia).
assert (HS : st_ok (fx := mkFP F fc) rsegs E0 pbK_ssA
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs2 (Z_to_bv 64 PC_AFTER_STRTOL) mem2 (seg_rom rsegs)))).
{ unfold pbK_ssA. apply (pbW_entry B F fc x PAT_DOT cl _ regs2 mem2 md2 L PC_AFTER_STRTOL _ _ _ _ Hc HC2).
  - unfold hk_env. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold pbK_csA, pbK_csC. repeat apply Forall_cons; try apply Forall_nil.
    + apply (pbK_chunk8 E0 _ _ 16 47 _ E47); [lia | exact L16'].
    + apply (pbK_chunk8 E0 _ _ 24 48 _ E48); [lia | exact V24'].
    + apply (pbK_chunk8 E0 _ _ 32 49 _ E49); [lia | exact L32'].
    + apply (pbK_chunk8 E0 _ _ 40 50 _ E50); [lia | exact L40'].
    + apply (pbK_chunk8 E0 _ _ 48 51 _ E51); [apply Hsh; lia | exact V48'].
    + apply (pbK_chunk8 E0 _ _ 0x60 52 _ E52); [lia | exact V96].
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, pbK_dotr.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E0.
    rewrite E52, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ _ 0 1 (SOff 53 0) (pbK_dc x ck)); [rewrite hk_sv_SOff0; exact E53 | cbn; lia | lia |].
    rewrite Z.add_0_r. replace (pbK_xs x ck + pbK_e x ck) with (hx_P x + (ck + 21 + pbK_e x ck)) by (unfold pbK_xs; lia).
    exact Vc.
  - apply pairwise_disjoint_of_extents. unfold hk_saves, hk_temps, pbK_dotr.
    cbn [map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E0.
    rewrite (EG 2%nat 2%bv _ eq_refl D2), (EG 8%nat 8%bv _ eq_refl D8), E52, !unsigned_lit_small by (unfold hx_sp in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold pbK_xs, hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *. unfold hx_len in *. destruct Hside; repeat split; lia.
  - cbn [atoms_ok pbK_fA]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E0.
    rewrite E52, E53, !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (SHOK : sh_ok rsegs hk_Bx pbK_SHA E0 (hx_rd x mem2)).
{ apply Forall_cons; [|apply Forall_nil].
  assert (E52' : ew E0 52 = w64 (hx_P x + (ck + 21 + pbK_e x ck))) by (rewrite E52; unfold pbK_xs; f_equal; lia).
  exact (hk_shent_pod B x (w_H (hx_W x)) mem2 E0 52 (ck + 21 + pbK_e x ck) 0 1 Hc Hnull E27 E52' HRA ltac:(unfold hx_len in *; lia)
    ltac:(lia) ltac:(lia) ltac:(unfold hx_len in *; lia)). }
pose proof (hk_core_journal B x _ _ _ _ _ _ HC2) as (HJ & _ & _).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
  hx_rd x mem2 (Z_to_bv 64 a) = hx_rd x mem2 (Z_to_bv 64 a)) by reflexivity.
pose proof (same_io_refl md2) as Hio.
assert (HAE : env_agree 54 E0 E0) by apply env_agree_refl.
assert (Hxs : 0 <= pbK_xs x ck < 2 ^ 47) by (unfold pbK_xs; unfold hx_len in *; lia).
assert (U25 : U E0 (SOff 25 0) = pbK_xs x ck) by (apply (UG 25%nat 25%bv); [reflexivity | exact R25 | lia]).
assert (U52 : U E0 (SOff 52 0) = pbK_xs x ck + pbK_e x ck) by (apply (UL 5%nat); [reflexivity | lia]).
assert (U53 : U E0 (SOff 53 0) = pbK_dc x ck) by (apply (UL 6%nat); [reflexivity | lia]).
assert (G24 : forall E ss ms, st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> env_agree 54 E0 E ->
  sr_get (ss_regs ss) 24%bv = SOff 10 0 -> getr (ms_regs ms) 24%bv = w64 (pbK_ch x ck)).
{ intros E ss ms HS' HAE' H24. rewrite (pbW_reg_kept F fc E0 E ss ms _ 54 10 24%bv HS' HAE' ltac:(lia) H24).
  subst E0. rewrite (hk_env_reg x regs2 L 10 10%bv eq_refl). exact H10. }
unfold cfg_at. change (w64 PC_AFTER_STRTOL) with (Z_to_bv 64 PC_AFTER_STRTOL).
pbK_run x Hc HAE KM Hio U2.
pbK_branch HAE HB.
- (* dot = k + 13: no digits, the refusal BAD_KEY *)
  rewrite U52, U25 in HB. apply Z.eqb_eq in HB.
  assert (Hkb : Headamp.parse_key (pbK_str x ck) = Headamp.KBad) by (apply hgk_key_e0; fold (pbK_e x ck); lia).
  pbK_run_to x Hc HAE KM Hio U2 PC_REF.
  eapply (pbK_exit_ref F fc x r cc n ck cl keys rf 4 regs2 mem2 md2 L _ _ _ _ 54 pbK_csA (SOff 47 0)
    (SOff 49 0) (SOff 50 0) (SOff 48 0) Hc HC2 Hfx HM (pbK_cell_bad x ck _ Hkb));
  [ lia
  | exact HS | vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbK_fixed_tac
  | pbK_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
  | pbK_ukept HAE (UG 21%nat 21%bv _ eq_refl L21 ltac:(apply Hsh; lia))
  | pbK_ukept HAE (UG 22%nat 22%bv _ eq_refl L22 ltac:(lia))
  | pbK_ukept HAE (UL 3%nat _ eq_refl ltac:(lia))
  | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
  | pbK_ukept HAE (UG 23%nat 23%bv _ eq_refl R23 ltac:(lia))
  | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
  | pbK_ukept HAE (UL 4%nat _ eq_refl ltac:(apply Hsh; lia))
  | pbK_win | exact U2
  | pbK_win | pbK_uat HAE (UL 0%nat _ eq_refl ltac:(lia))
  | pbK_win | pbK_uat HAE (UL 2%nat _ eq_refl ltac:(lia))
  | pbK_win | pbK_uat HAE (UL 3%nat _ eq_refl ltac:(lia))
  | pbK_win | pbK_uat HAE (UL 1%nat _ eq_refl ltac:(lia))
  | exact HJ | exact Hio | exact KM | exact (pbK_REF B MT errno_low x r cc n ck cl keys rf Hc HADV) ].
- rewrite U52, U25 in HB. apply Z.eqb_neq in HB.
  assert (He0 : pbK_e x ck <> 0) by lia.
  pbK_run x Hc HAE KM Hio U2.
  pbK_branch HAE HB2.
  + (* no dot after the digits: the refusal BAD_KEY *)
    rewrite ?U_lit in HB2 by lia. rewrite U53 in HB2. apply negb_true_iff, Z.eqb_neq in HB2.
    assert (Hkb : Headamp.parse_key (pbK_str x ck) = Headamp.KBad) by (apply hgk_key_nodot; [exact He0 | exact HB2]).
    pbK_run_to x Hc HAE KM Hio U2 PC_REF.
    eapply (pbK_exit_ref F fc x r cc n ck cl keys rf 4 regs2 mem2 md2 L _ _ _ _ 54 pbK_csA (SOff 47 0)
      (SOff 49 0) (SOff 50 0) (SOff 48 0) Hc HC2 Hfx HM (pbK_cell_bad x ck _ Hkb));
    [ lia
    | exact HS | vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbK_fixed_tac
    | pbK_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
    | pbK_ukept HAE (UG 21%nat 21%bv _ eq_refl L21 ltac:(apply Hsh; lia))
    | pbK_ukept HAE (UG 22%nat 22%bv _ eq_refl L22 ltac:(lia))
    | pbK_ukept HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ukept HAE (UG 23%nat 23%bv _ eq_refl R23 ltac:(lia))
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ukept HAE (UL 4%nat _ eq_refl ltac:(apply Hsh; lia))
    | pbK_win | exact U2
    | pbK_win | pbK_uat HAE (UL 0%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 2%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 1%nat _ eq_refl ltac:(lia))
    | exact HJ | exact Hio | exact KM | exact (pbK_REF B MT errno_low x r cc n ck cl keys rf Hc HADV) ].
  + (* the dot: strcmp(name, "phantom") *)
    rewrite ?U_lit in HB2 by lia. rewrite U53 in HB2. apply negb_false_iff, Z.eqb_eq in HB2.
    pbK_run_to x Hc HAE KM Hio U2 B_TRAMP_STRCMP.
    assert (UY : U E0 (SOff 52 1) = pbK_y x ck) by (unfold pbK_y; apply (pbK_U_off E0 52 _ 1 E52); lia).
    eapply (pbK_exit_sc F fc x r cc n ck cl keys rf 0 regs2 mem2 md2 L _ _ _ _ 54 pbK_csA (SOff 47 0)
      (SOff 49 0) (SOff 50 0) (SOff 48 0) (SOff 51 0) Hc HC2 Hfx HM);
    [ lia | exact He0 | exact HB2 | intros j Hj; lia
    | exact HS | vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbK_fixed_tac
    | pbK_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
    | pbK_ukept HAE (UG 21%nat 21%bv _ eq_refl L21 ltac:(apply Hsh; lia))
    | pbK_ukept HAE (UG 22%nat 22%bv _ eq_refl L22 ltac:(lia))
    | pbK_ukept HAE (UG 23%nat 23%bv _ eq_refl R23 ltac:(lia))
    | apply (G24 _ _ _ HS HAE); vm_compute; reflexivity
    | pbK_ukept HAE UY
    | pbK_ukept HAE UY
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_ureg HAE; rewrite U_lit by lia; reflexivity
    | pbK_win | exact U2
    | pbK_win | pbK_uat HAE (UL 0%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 2%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 1%nat _ eq_refl ltac:(lia))
    | pbK_win | pbK_uat HAE (UL 4%nat _ eq_refl ltac:(apply Hsh; lia))
    | exact HJ | exact Hio | exact KM | exact (pbK_SC0 x r cc n ck cl keys rf Hc HADV HVAL) ].
Qed.

(* ======================================= KEY 0x84db0 .. strtol ======================================= *)
(* 0x84db0 a0 = keys + 1 (the traps 0x84db4 and 0x84dc0 decided by the facts on s9 and s8); [sp + 24] = keys + 1;
   s9 = key + 13; the hole's byte 4 := 00 (PAT_DOT); [sp + 96] = 0; strtol(s9, sp + 96, 10). Env: L = pbK_LC. *)
Definition pbK_csK : list YP09.chunk :=
[YP09.mkChunk 16 (CVal 8 (SOff 47 0)); YP09.mkChunk 32 (CVal 8 (SOff 49 0)); YP09.mkChunk 40 (CVal 8 (SOff 50 0));
 YP09.mkChunk 48 (CVal 8 (SOff 51 0))].
Definition pbK_fK : list (nat * afact) := [(24%nat, mkAF 1 (2 ^ 63) 0); (25%nat, mkAF 0 16383 0)].

Lemma pbK_sv_off : forall E n v k, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity. Qed.

(* the hole runs' tactics of Section E (Ltac does not leave its section) *)
Ltac pbK_regions HS R0 R1 :=
lazymatch type of HS with @st_ok _ ?f _ (mkSST _ _ _ (?r0 :: ?r1 :: _) _ _) _ =>
  pose proof (pbK_region_of_st (fx := f) _ _ _ _ r0 HS (or_introl eq_refl)) as R0;
  pose proof (pbK_region_of_st (fx := f) _ _ _ _ r1 HS (or_intror (or_introl eq_refl))) as R1 end.
Ltac pbK_win_regions := let rr := fresh "rr" in let Hrr := fresh "Hrr" in
intros rr Hrr; cbn [ss_mem pbK_ssE add_cond app In] in Hrr;
repeat (destruct Hrr as [<-|Hrr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi hk_temps hk_hole_rg];
  first [left; split; [reflexivity|lia] | right; left; split; [reflexivity|lia] | right; right; lia] |]);
destruct Hrr.
Ltac pbK_kept HS :=
lazymatch goal with |- getr _ ?r = getr ?regs ?r =>
  let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
  lazymatch type of HS with @st_ok _ ?f _ _ _ =>
    exact (pbK_reg_kept f _ regs _ _ _ _ r n HS ltac:(vm_compute; reflexivity) eq_refl) end end.
Ltac pbK_io := let rec kio := first [apply same_io_refl | assumption |
  eapply same_io_trans; [| apply pbK_same_io_wvb]; kio] in kio.

Theorem segKEY_ok : segKEY_stmt B MT.
Proof.
unfold segKEY_stmt. intros x r cc n ck cl keys rf Hc HADV HVAL F fc regs mem md HK.
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsl.
pose proof HK as (Hcore & Hfx & HM & (L20 & L21 & L22 & V16 & V32 & V40) & R23 & R24 & R25 & V48).
pose proof (hk_core_cregs B _ _ _ _ _ _ _ Hcore) as HCR.
pose proof (hk_core_journal B _ _ _ _ _ _ _ Hcore) as (HJ & HOK & HP).
pose proof HM as (Hnull & (Hr16 & Hr8 & Hvs & Hrl) & Hcc & Hcc8 & Hin & _ & HKo & (Hcl & Hk0 & Hrf) & _).
pose proof (hk_pod B x Hc Hnull) as (HP0 & _ & Hlen & _ & _ & HP63 & _).
pose proof (hgw_next_bounds x r cc (conj Hr16 (conj Hr8 (conj Hvs Hrl))) Hcc Hcc8 Hin) as (Hnx & _).
pose proof (pbK_keys_small x r cc n ck cl keys rf HM ltac:(unfold hx_len in Hlen; lia)) as Hks.
pose proof (pbK_U2_26 B x regs (pbK_LC x r cc keys rf) Hc HCR) as (U2 & U26 & S1 & S2 & S3 & S4).
pose proof (hgw_u32_range (hx_bs x) (r + 8)).
pose proof (pbK_kstr x ck HKo) as (_ & HLk & _). pose proof HKo as (Hck0 & _).
unfold hp_vs, hx_len in *.
assert (Hsh : 0 <= shadow_addr (hx_P x + cc) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. assert (0 <= hx_P x + cc < 2 ^ 63) by lia.
  assert (0 <= (hx_P x + cc) / 8 <= hx_P x + cc) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia. }
set (E := hk_env x regs (pbK_LC x r cc keys rf)) in *.
assert (E47 : ew E 47 = w64 ((hx_P x + r + 8) mod 8 + 3)) by exact (hk_env_seg x regs _ 0).
assert (E49 : ew E 49 = w64 rf) by exact (hk_env_seg x regs _ 2).
assert (E50 : ew E 50 = w64 (hx_P x + r + 16)) by exact (hk_env_seg x regs _ 3).
assert (E51 : ew E 51 = w64 (shadow_addr (hx_P x + cc))) by exact (hk_env_seg x regs _ 4).
assert (E24 : ew E 24 = w64 (hx_P x + ck + 8)) by (rewrite (hk_env_reg x regs (pbK_LC x r cc keys rf) 24 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = w64 keys) by (rewrite (hk_env_reg x regs (pbK_LC x r cc keys rf) 25 25%bv eq_refl); exact R25).
pose proof HCR as (C2 & _).
assert (E2 : ew E 2 = w64 (hx_spa x)) by (rewrite (hk_env_reg x regs (pbK_LC x r cc keys rf) 2 2%bv eq_refl); exact C2).
pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8 ltac:(lia)) as Hm8.
assert (HA : atoms_ok E pbK_fK).
{ cbn [atoms_ok pbK_fK]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E24, E25, !unsigned_lit_small by lia.
  change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
pose proof (pbK_entry_hole B x PAT_KEY cl pbK_rb0 regs mem md F fc PC_KEY (pbK_LC x r cc keys rf) pbK_csK pbK_fK Hc Hcore
  eq_refl ltac:(vm_compute; reflexivity)) as HS.
specialize (HS ltac:(repeat constructor;
  [ apply (pbK_chunk8 E _ _ 16 47 _ E47); [lia | exact V16]
  | apply (pbK_chunk8 E _ _ 32 49 _ E49); [lia | exact V32]
  | apply (pbK_chunk8 E _ _ 40 50 _ E50); [lia | exact V40]
  | apply (pbK_chunk8 E _ _ 48 51 _ E51); [lia | exact V48] ]) HA).
unfold cfg_at. change (w64 PC_KEY) with (Z_to_bv 64 PC_KEY).
aj_run_toH pb_tbl_ok HS HJ B_TRAMP_STRTOL.
{ cbn [ss_mem]. eapply (hk_awr_temps B x E); [exact Hc | exact U2 |].
  apply (hk_awr_hole B x E); [exact U26 | reflexivity | apply awr_okH_nil]. }
pbK_regions HS R0 R1.
assert (HP2 : hpat rsegs (hx_W x) (ms_mem ms) (hx_fr x) PAT_DOT).
{ apply (pbK_hpat_of_region x E _ _ PAT_DOT R1 U26 eq_refl).
  intros i Hi. do 8 (destruct i as [|i]; [eexists; split; [pbK_in | split; [lia | reflexivity]] |]). lia. }
assert (HCR2 : hk_cregs x (ms_regs ms)) by (apply (hk_cregs_same x regs _ HCR); pbK_kept HS).
assert (Hcore2 : hp_core B x PAT_DOT cl pbK_rb0 (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md)).
{ apply (pbK_core_exit B errno_low x PAT_KEY PAT_DOT cl pbK_rb0 regs mem md _ _ _ E _ Hc Hcore ltac:(lia)
    (length_ha_res_bytes 0 0 0) HFr); [ | exact HJ | reflexivity | | exact HP2 | pbK_io | exact HCR2].
  - apply (pbK_windows x E _ U2 U26). pbK_win_regions.
  - unfold PAT_DOT. repeat constructor; lia. }
rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) E _ ms HS eq_refl). cbn [ss_pc].
apply (pbK_ST x r cc n ck cl keys rf Hc HADV HVAL F fc (ms_regs ms) (ms_mem ms) _).
pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 16 8 (SOff 47 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E47)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C16.
pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 24 8 (SOff 25 1) (keys + 1) R0 ltac:(pbK_in)
  ltac:(apply (pbK_sv_off E 25 keys 1 E25); lia)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C24.
pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 32 8 (SOff 49 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E49)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C32.
pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 40 8 (SOff 50 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E50)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C40.
pose proof (pbK_chunk_val E _ 2 0 128 0 128 _ 48 8 (SOff 51 0) _ R0 ltac:(pbK_in) ltac:(rewrite pbK_SOff0; exact E51)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as C48.
rewrite U2 in C16, C24, C32, C40, C48.
split; [exact Hcore2|]. split; [exact Hfx|]. split; [exact HM|].
split.
{ split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 20%bv 20 HS ltac:(vm_compute; reflexivity) eq_refl); exact L20|].
  split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 21%bv 21 HS ltac:(vm_compute; reflexivity) eq_refl); exact L21|].
  split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 22%bv 22 HS ltac:(vm_compute; reflexivity) eq_refl); exact L22|].
  split; [exact C16|]. split; [exact C32 | exact C40]. }
split; [rewrite (pbK_reg_kept (mkFP F fc) x regs _ _ _ _ 23%bv 23 HS ltac:(vm_compute; reflexivity) eq_refl); exact R23|].
split; [rewrite (pbK_reg_sv (mkFP F fc) E _ _ _ 25%bv (SOff 24 13) HS ltac:(vm_compute; reflexivity)),
  (pbK_sv_off E 24 _ 13 E24) by lia; unfold pbK_xs, w64; f_equal; lia|].
split; [rewrite (pbK_reg_sv (mkFP F fc) E _ _ _ 10%bv (SOff 24 13) HS ltac:(vm_compute; reflexivity)),
  (pbK_sv_off E 24 _ 13 E24) by lia; unfold pbK_xs, w64; f_equal; lia|].
split; [rewrite (pbK_reg_sv (mkFP F fc) E _ _ _ 11%bv (SOff 2 96) HS ltac:(vm_compute; reflexivity)),
  (pbK_sv_off E 2 _ 96 E2) by lia; reflexivity|].
split; [rewrite (pbK_reg_sv (mkFP F fc) E _ _ _ 12%bv (SLit 10) HS ltac:(vm_compute; reflexivity)),
  pbK_SLit by (split; [discriminate | reflexivity]); reflexivity|].
split; [rewrite (pbK_reg_sv (mkFP F fc) E _ _ _ 1%bv (SLit 0x84de0) HS ltac:(vm_compute; reflexivity)),
  pbK_SLit by (split; [discriminate | reflexivity]); reflexivity|].
split; [exact C24 | exact C48].
Qed.

End z.

Print Assumptions segKEY_ok.
