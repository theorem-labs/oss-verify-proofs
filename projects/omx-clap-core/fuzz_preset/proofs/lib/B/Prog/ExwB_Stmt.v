(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, ex_word (fuzz_preset.c :295-305): the BOUNDED text, the PRE-04388d628fb
   tex_word_specX (lib/A/PRH_FnEx.v blob 76731d160419, kit a3bdeca3920) with ONE added premise, the range of v, stated
   as an explicit argument. Kit 04388d628fb (PRH_FnEx.v blob d32e3229d5dc) took the range into tex_word_specX itself
   (unconditionally) and made the post an m-form; ExwB.v ex_word_holds_B proves that text. This bounded copy stays
   while ex_value's EHW cites it (origin/cold/h-rw-pre-7-b-ex_value 30962b8840a, ExvB_Disp.v:39-40).
   WHY: as written the text admits values of v the code cannot meet (the internal file specX-obstacle.md, BExWord 2026-10-29,
   accepted by K0's owner h-hpreset-7 09:16Z): v = 2 ^ 64 (the register a3 = w64 v = 0, so `beqz s2` at B 0x8497c takes
   the NULL branch while the text, v <> 0, asks in->differs = 1), and v >= sp with v's shadow byte inside ex_word's own
   frame (the prologue's `sd ra,72(sp)` at B 0x848d8 overwrites it before the check at B 0x84990).
   THE PREMISE (ex_word_vrange): v <> 0 -> 0 <= v /\ v + 4 <= 2 ^ 47. It kills both: w64 v = 0 only at v = 0, and the
   shadow bytes of [v, v + 4) lie at or below 0x10007fff7fff, under CEIL_MIN = 0x7fff7f800000 <= YM05.alloc_ceiling
   (the RunCeil field, YM05.v:21 alloc_ceiling_value) and so under every
   byte ex_word's run writes before the check. ex_value, the one caller in B's listing (B 0x8395c), pays it from its tree
   facts (ExvB_Open_kt.v exv_foot_rng).
   tex_word_specX_vr below is the pre-04388d628fb tex_word_specX VERBATIM plus the line `ex_word_vrange v ->` after the
   v clause, at the #102 kit's ledger (prh_ledger with the two #102 cells, arguments most own: walkkit-next
   decff67d721f, PRH_Base.v blob 3004a98fe2d9); tex_word_specX_vr_of_specX shows that kit's tex_word_specX (PRH_FnEx.v
   blob 45ddb7a7d5ae) implies it (the range premise from ex_word_vrange, the post weakened: the memnorm keep and S' = S
   dropped). The pcs above are image B' pcs (the #102 pin d663f82d), relocated from the old-pin text 2e2ab2f3deb4.
   Numerals: 4 (LENGTH: v->type), 2 ^ 47 (DERIVED: the user address space top, ly_stk_hi's bound in astk_ok). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
Import ListNotations.
Local Open Scope Z_scope.

(* the added premise: the range of a non-NULL v *)
Definition ex_word_vrange (v : Z) : Prop := v <> 0 -> 0 <= v /\ v + 4 <= 2 ^ 47.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* PRH_FnEx.v:216-244 (the #102 kit decff67d721f) verbatim but for its range premise `0 <= v /\ v + 4 <= 2 ^ 47` and
   the post's S' = S / memnorm keep (the pre-04388d628fb shape), plus `ex_word_vrange v ->` after the v clause *)
Definition tex_word_specX_vr : Prop :=
  forall ly S Hp W regs mem md ch (q w ty v t x0 i0 d : Z) (wl x : list Z) Lam peak cnt fail ran most own,
  let len := Z.of_nat (length x) in
  let hit := Z.of_nat (length wl) <= len - i0 /\ firstn (length wl) (skipn (Z.to_nat i0) x) = wl in
  fpre B ARx STK_ex_word ly S Hp W regs mem md ch ->
  getr regs 10 = w64 q -> getr regs 11 = w64 w -> getr regs 12 = w64 ty -> getr regs 13 = w64 v ->
  cstr_ok W mem w wl -> 0 <= ty <= 2 ->
  val_mem segs (rdW W mem) q 8 (x0 + i0) -> val_mem segs (rdW W mem) (q + 8) 8 (x0 + len) -> q mod 8 = 0 ->
  spZ regs <= q -> q + 36 <= spZ regs + d -> fwin ly W regs mem d ->
  src_rd W mem x0 x -> prhex_inblk B ly S Hp x0 len -> len <= 3 * 2 ^ 20 -> 0 <= i0 <= len ->
  (v <> 0 -> val_mem segs (rdW W mem) v 4 t /\ 0 <= t < 2 ^ 32 /\ v mod 8 = 0 /\
     range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 4 /\
     (v + 4 <= spZ regs - STK_ex_word \/ spZ regs <= v)) ->
  ex_word_vrange v ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_ex_word) regs mem md)
    (fpostW B ARx SK STK_ex_word d [(q, q + 8); (q + 32, q + 36)] regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       ((hit /\ getr regs' 10 = w64 0 /\ val_mem segs (rdW W' mem') q 8 (x0 + i0 + Z.of_nat (length wl)) /\
         ((v <> 0 /\ t <> ty /\ val_mem segs (rdW W' mem') (q + 32) 4 1) \/
          ((v = 0 \/ t = ty) /\ prhex_same W mem W' mem' (q + 32) 4)))
        \/
        (~ hit /\ getr regs' 10 = w64 (-1) /\ prhex_same W mem W' mem' q 8 /\
         prhex_same W mem W' mem' (q + 32) 4)))).

(* kit 04388d628fb's tex_word_specX gives this one: its range premise `0 <= v /\ v + 4 <= 2 ^ 47` follows from
   ex_word_vrange (trivially at v = 0), every other premise is passed through, and its post fpostWm (fpostW at
   fQmn mem Q) gives fpostW at Q by dropping S' = S and the memnorm keep *)
Lemma tex_word_specX_vr_of_specX : tex_word_specX B ARx SK -> tex_word_specX_vr.
Proof.
intros H ly S Hp W regs mem md ch q w ty v t x0 i0 d wl x Lam peak cnt fail ran most own len hit
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 HVR H19.
assert (Hv : 0 <= v /\ v + 4 <= 2 ^ 47) by (destruct (Z.eq_dec v 0) as [->|Hv0]; [lia | exact (HVR Hv0)]).
eapply SRr_mono; [exact (H ly S Hp W regs mem md ch q w ty v t x0 i0 d wl x Lam peak cnt fail ran most own
  H1 H2 H3 H4 H5 H6 H7 Hv H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19) |].
unfold fpostWm, fpostW, fQmn. cbv beta.
intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HK & HP & (Hr & Hhp & _ & Hab & Hled & Hres) & _).
exists ly', S', Hp', regs', mem', md', k.
exact (conj Hc (conj HJ (conj HK (conj HP (conj Hr (conj Hhp (conj Hab (conj Hled Hres)))))))).
Qed.
End c.
