(* fs WRITER, put's GROW arm (preset_file.c:454-476), the model half: what the grow arm needs about
   WriterSpec.newcap and the writer's own-trace budget, over the live definitions of lib/A/FSH_Fn_writer.v
   (WMAX :62, bsz :82, wcalls :92, wbudget_pre :93-96, wbudget_kept :109-110; line numbers of statement head
   0e39966a268, the budgets-by-own-trace text, over S0 400b2a240b3's FP-keyed core) and lib/Prog/WriterSpec.v
   (dbl / newcap :29-35). No engine run, no walk, no image, no Section variable: pure arithmetic that the put
   walk `apply`s.

   The walk's names: `cap` the buffer's capacity, `cnt` g_count, `S S'` the allocator states at put's entry and
   at its return, and put1's need (lib/Prog/WriterApp.v:18) `Z.of_nat (length text) + Z.of_nat (length bs) + 1`
   (`need` in the lemmas that do not mention put1). The grow arm is put1's `need <=? cap = false` branch
   (WriterApp.v:19-25), so `cap < need`; its two outcomes are refused, `mkW 1 text cap ((cnt + 1) mod 2 ^ 64) ..`
   (WriterApp.v:23), and granted, `mkW 0 (text ++ bs) (newcap cap need) ((cnt + 1) mod 2 ^ 64) ..` (WriterApp.v:25);
   both append the one request newcap to w_calls.
   The class hypothesis `cap = 0 \/ exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j` is the one wout_ok carries
   (FSH_Fn_writer.v:125-126); `need <= WMAX`, `cap <= WMAX` and `wbudget_pre S cap cnt live st'` are put_spec's
   premises (FSH_Fn_writer.v:214-216, with `Z.of_nat (length bs) = n` at :212); `0 <= cap` is wout_ok's (:119);
   `0 <= cnt` is fs_glob's (FSH_Base.v:266 -> FSH_Gen.v:318). put_spec's post has, with
   `st' = put1 (mkW failed text cap cnt fail []) bs` (FSH_Fn_writer.v:219), the journal count `3 * wcalls st'`
   (:222) and `wbudget_kept S S' failed cap cnt (w_failed st') (w_cap st') (w_cnt st')` (:225). Every put1 lemma
   here is stated over exactly that `mkW _ text cap cnt fail []` (the calls list is [] in put_spec).

   Where a statement differs from the form first asked for, it is because that form is false or gone:
   - `4096 <= newcap cap need` needs the class (cap = 1, need = 1: newcap = 1); with it, `0 < need` is not used.
   - `newcap cap need <= WMAX` needs `cap <= WMAX` too (cap = 2^28, need = 1: newcap = 2^28 > WMAX).
   - the size-class budget (wgrows / wbud, the wbud budget step and the wbud form of wbudget_kept) left every
     spec at 0e39966a268, which states each budget by the call's own trace; the count facts are now
     put_grow_wcalls_* and wbudget_kept is re-proved in its new body.
   - put1's count is `(cnt + 1) mod 2 ^ 64` (WriterApp.v:23,25); `cnt <= cnt'` holds because wbudget_pre gives
     `cnt + wcalls st' < 2 ^ 64` and wcalls st' = 1 on a grow (put_grow_kept_put1 reads it off wbudget_pre).

   Reused, not copied, from fs's released plain chain (ossv/recipes 566eb6ffa5df, also
   release/pau-projects-recipes b6a0088adcb4; proofs/omx-clap-core/fuzz_state/lib/Prog/, last touched there by
   84b1ffc6d7d0; byte-identical to this tree's lib/Prog/put_blocks.v and WriterRet.v, the modules Required
   here): put_blocks.v:264 newcap_pow, WriterRet.v:52 dbl_ge, WriterRet.v:163 newcap_pos. Re-proved: the 2^27
   bound (put_grow_dbl_le / put_grow_newcap_le), because the released bound WriterSpecFacts.v:464 newcap_le28
   fixes the plain 2^28 in its statement and the ASan WMAX is 2^27. FSW_writer_model.v:76 newcap_ge_4096 is
   fact 1 with an extra `need <= 2^63` premise; put_grow_newcap_ge_4096 drops it.
   Rule 24 (git grep over origin/main d65b67070f2, ossv/recipes 566eb6ffa5d, ossv/candidates ee89628c997,
   release/pau-projects-recipes b6a0088adcb, under proofs/, for the prefix `put_grow_`): the one hit is
   put_blocks.v:304 put_grow_to_call, not a name used here; no lemma name in this file is taken. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSH_Gen FSH_Fn_writer.
(* lib/Prog modules are Required, never Imported (a Theorem Labs lane 21:43Z) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp put_blocks WriterRet.
Import ListNotations.
Local Open Scope Z_scope.

(* released newcap_pow's premise need <= 2^63 from need <= WMAX = 2^27 (FSH_Fn_writer.v:62) *)
Lemma put_grow_need63 : forall need, need <= WMAX -> need <= 2 ^ 63.
Proof.
  intros need H. unfold WMAX in H.
  assert (2 ^ 27 <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* ---- 1. the grown buffer is at least 4096 bytes: newcap starts at 4096 or at cap >= 4096 (WriterSpec.v:35)
   and dbl never goes below its start (released WriterRet.v:52 dbl_ge) ---- *)
Lemma put_grow_newcap_ge_4096 : forall cap need,
  (cap = 0 \/ exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) ->
  4096 <= WriterSpec.newcap cap need.
Proof.
  intros cap need Hc. unfold WriterSpec.newcap.
  assert (S0 : 4096 <= (if cap =? 0 then 4096 else cap)).
  { destruct Hc as [-> | (j & Hj & ->)]; [apply Z.leb_le; reflexivity|].
    assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
    destruct (Z.eqb_spec (4096 * 2 ^ j) 0); lia. }
  pose proof (WriterRet.dbl_ge 64 (if cap =? 0 then 4096 else cap) need ltac:(lia)). lia.
Qed.

(* ---- 2. the grown buffer stays in its class and under WMAX ---- *)

(* dbl from a class value below WMAX stops at or below WMAX when need <= WMAX: it doubles only while
   c < need <= 2^27, and a class value below 2^27 doubles to at most 2^27 (WriterSpec.v:29-33) *)
Lemma put_grow_dbl_le : forall f j need, 0 <= j -> 4096 * 2 ^ j <= WMAX -> need <= WMAX ->
  WriterSpec.dbl f (4096 * 2 ^ j) need <= WMAX.
Proof.
  unfold WMAX. induction f as [|f IH]; intros j need Hj Hc Hn; cbn [WriterSpec.dbl]; [exact Hc|].
  destruct (Z.leb_spec need (4096 * 2 ^ j)) as [H|H]; [exact Hc|].
  assert (E2 : 2 * (4096 * 2 ^ j) = 4096 * 2 ^ (j + 1)) by (rewrite Z.pow_add_r by lia; ring).
  rewrite E2. apply IH; [lia | | exact Hn].
  assert (J : j < 15).
  { destruct (Z.lt_ge_cases j 15) as [|Hge]; [assumption|].
    assert (2 ^ 15 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 27) with (4096 * 2 ^ 15) in Hn. lia. }
  assert (2 ^ (j + 1) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 27) with (4096 * 2 ^ 15). lia.
Qed.

Lemma put_grow_newcap_le : forall cap need,
  (cap = 0 \/ exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) -> cap <= WMAX -> need <= WMAX ->
  WriterSpec.newcap cap need <= WMAX.
Proof.
  intros cap need Hc Hcap Hn. unfold WriterSpec.newcap.
  destruct Hc as [-> | (j & Hj & ->)].
  - change (if 0 =? 0 then 4096 else 0) with (4096 * 2 ^ 0).
    apply put_grow_dbl_le; [lia | unfold WMAX; apply Z.leb_le; reflexivity | exact Hn].
  - assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
    destruct (Z.eqb_spec (4096 * 2 ^ j) 0) as [E0|_]; [lia|].
    apply put_grow_dbl_le; [lia | exact Hcap | exact Hn].
Qed.

(* the class half rests on the released newcap_pow (put_blocks.v:264), whose need <= 2^63 follows from
   need <= WMAX = 2^27 *)
Lemma put_grow_newcap_class : forall cap need,
  (cap = 0 \/ exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) -> cap <= WMAX -> need <= WMAX ->
  (exists j', 0 <= j' <= 51 /\ WriterSpec.newcap cap need = 4096 * 2 ^ j') /\
  WriterSpec.newcap cap need <= WMAX.
Proof.
  intros cap need Hc Hcap Hn. split; [|exact (put_grow_newcap_le cap need Hc Hcap Hn)].
  destruct (put_blocks.newcap_pow cap need Hc (put_grow_need63 need Hn)) as (j' & Hj' & E & _).
  exists j'. split; assumption.
Qed.

(* ---- 3. the grown buffer holds the text: released newcap_pow (put_blocks.v:264) ---- *)
Lemma put_grow_need_le : forall cap need,
  (cap = 0 \/ exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) -> need <= WMAX ->
  need <= WriterSpec.newcap cap need.
Proof.
  intros cap need Hc Hn.
  destruct (put_blocks.newcap_pow cap need Hc (put_grow_need63 need Hn)) as (j' & _ & _ & Hle). exact Hle.
Qed.

(* ---- 4. the call's own trace (wcalls, FSH_Fn_writer.v:92): put1 (WriterApp.v:15-25) records one request on a
   grow, in both outcomes (w_calls st ++ [c'], :23 and :25), none on the fast arm (:19) and none once failed
   (:16). So put_spec's journal count 3 * wcalls st' (FSH_Fn_writer.v:222) is 3 = EV_fuzz_realloc
   (FSH_Gen.v:76) on a grow and 0 otherwise. ---- *)
Lemma put_grow_wcalls_grow : forall text cap cnt fail (bs : list Z),
  cap < Z.of_nat (length text) + Z.of_nat (length bs) + 1 ->
  wcalls (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs) = 1.
Proof.
  intros text cap cnt fail bs Hlt. unfold wcalls, WriterApp.put1.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls
       negb Z.eqb].
  rewrite (proj2 (Z.leb_gt _ _) Hlt).
  destruct (cnt =? fail); reflexivity.
Qed.

Lemma put_grow_wcalls_fast : forall text cap cnt fail (bs : list Z),
  Z.of_nat (length text) + Z.of_nat (length bs) + 1 <= cap ->
  wcalls (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs) = 0.
Proof.
  intros text cap cnt fail bs Hle. unfold wcalls, WriterApp.put1.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls
       negb Z.eqb].
  rewrite (proj2 (Z.leb_le _ _) Hle). reflexivity.
Qed.

Lemma put_grow_wcalls_failed : forall failed text cap cnt fail (bs : list Z),
  failed <> 0 ->
  wcalls (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs) = 0.
Proof.
  intros failed text cap cnt fail bs Hf. unfold wcalls, WriterApp.put1.
  cbn [WriterApp.w_failed WriterApp.w_calls].
  destruct (Z.eqb_spec failed 0) as [E|_]; [contradiction | reflexivity].
Qed.

(* ---- 5. wbudget_kept (FSH_Fn_writer.v:109-110: cap' <= WMAX, blocks_bytes kept, cnt <= cnt') for the grow arm's
   two outcomes. The count is (cnt + 1) mod 2^64 (WriterApp.v:23,25), which is cnt + 1 when cnt + 1 < 2^64. ---- *)
Lemma put_grow_kept_refused : forall S S' cap cnt,
  cap <= WMAX -> 0 <= cnt -> cnt + 1 < 2 ^ 64 ->
  blocks_bytes S' - bsz cap <= blocks_bytes S - bsz cap ->
  wbudget_kept S S' 0 cap cnt 1 cap ((cnt + 1) mod 2 ^ 64).
Proof.
  intros S S' cap cnt Hcap Hc0 Hc1 Hbb. unfold wbudget_kept.
  split; [exact Hcap|]. split; [exact Hbb|]. rewrite Z.mod_small by lia. lia.
Qed.

(* granted: the new capacity's bound is put_grow_newcap_le *)
Lemma put_grow_kept_granted : forall S S' cap need cnt,
  (cap = 0 \/ exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) -> cap <= WMAX -> need <= WMAX ->
  0 <= cnt -> cnt + 1 < 2 ^ 64 ->
  blocks_bytes S' - bsz (WriterSpec.newcap cap need) <= blocks_bytes S - bsz cap ->
  wbudget_kept S S' 0 cap cnt 0 (WriterSpec.newcap cap need) ((cnt + 1) mod 2 ^ 64).
Proof.
  intros S S' cap need cnt Hc Hcap Hn Hc0 Hc1 Hbb. unfold wbudget_kept.
  split; [exact (put_grow_newcap_le cap need Hc Hcap Hn)|]. split; [exact Hbb|].
  rewrite Z.mod_small by lia. lia.
Qed.

(* the clause put_spec's post asks for (FSH_Fn_writer.v:219,225), on put1's grow arm (failed = 0, need > cap),
   both outcomes at once; `cnt + 1 < 2^64` is read off put_spec's own wbudget_pre (:216, FSH_Fn_writer.v:96) with
   put_grow_wcalls_grow, and `cap <= WMAX` from cap < need <= WMAX *)
Lemma put_grow_kept_put1 : forall S S' live text cap cnt fail (bs : list Z),
  (cap = 0 \/ exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) ->
  cap < Z.of_nat (length text) + Z.of_nat (length bs) + 1 ->
  Z.of_nat (length text) + Z.of_nat (length bs) + 1 <= WMAX -> 0 <= cnt ->
  wbudget_pre S cap cnt live (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs) ->
  blocks_bytes S' - bsz (WriterApp.w_cap (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs))
    <= blocks_bytes S - bsz cap ->
  wbudget_kept S S' 0 cap cnt
    (WriterApp.w_failed (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs))
    (WriterApp.w_cap (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs))
    (WriterApp.w_cnt (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs)).
Proof.
  intros S S' live text cap cnt fail bs Hc Hlt Hn Hc0 HP.
  unfold wbudget_pre in HP. destruct HP as (_ & _ & _ & Hcnt).
  rewrite (put_grow_wcalls_grow text cap cnt fail bs Hlt) in Hcnt.
  unfold WriterApp.put1.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls
       negb Z.eqb].
  rewrite (proj2 (Z.leb_gt _ _) Hlt).
  destruct (cnt =? fail); cbn [WriterApp.w_failed WriterApp.w_cap WriterApp.w_cnt]; intro Hbb.
  - apply put_grow_kept_refused; [lia | exact Hc0 | exact Hcnt | exact Hbb].
  - apply put_grow_kept_granted; [exact Hc | lia | exact Hn | exact Hc0 | exact Hcnt | exact Hbb].
Qed.

(* ---- 6. the buffer's block size (FSH_Fn_writer.v:82): newcap is never 0 (released WriterRet.v:163
   newcap_pos, from wout_ok's 0 <= cap) ---- *)
Lemma put_grow_bsz_newcap : forall cap need, 0 <= cap ->
  bsz (WriterSpec.newcap cap need) = WriterSpec.newcap cap need + HEAD.
Proof.
  intros cap need Hc. pose proof (WriterRet.newcap_pos cap need Hc). unfold bsz.
  destruct (Z.eqb_spec (WriterSpec.newcap cap need) 0); [lia | reflexivity].
Qed.

Lemma put_grow_bsz_0 : bsz 0 = 0.
Proof. reflexivity. Qed.
