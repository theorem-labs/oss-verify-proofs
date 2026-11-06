(* Modified by Theorem Labs, 2026-10: the image-B (fuzz_reply.asan-ubsan) twin of lib/A/AD1r_heap_cf.v
   (commit 46f1762ad5a), by a Theorem Labs lane for a Theorem Labs lane's DRIVER_CF_B: the same text over lib/B's
   YCfn_cf.v names (fr_hblks_b, fr_surv_b, fr_live_pre_b, fr_live_post_b over W_rep.v's fr_globals_b), which have the
   same shape as A's; module paths changed. No image numeral: the file reasons over ablocks and blocks_bytes only. *)
(* The heap half of the cf driver loop (calls_loop, donor A/AD1r.v:570; B: YD1r.v): what replaces the donor's
   `Permutation (ablocks B ly S) [(buf, cap)]` / `[(buf, cap); (q, len)]` (AD1r.v:578-579), which is FALSE for
   fuzz_reply after its first call, since the entry keeps g_src's table and g_out's buffer alive across calls and may
   move g_out's buffer.  The split with the cf driver lane (CfDriver, commit 46f1762ad5a, agreed 2026-10-29):
   this file defines fr_heap and proves H_init / H_in / H_live / H_step over ablocks and blocks_bytes only (no AR,
   no ARcf, no events); CfDriver's calls_loop_cf uses them where the donor has the Permutation.
   fr_heap j: after j calls, the driver's input buffer (buf, cap) and payload copy (q, len, when len > 0) are alive
   and are not harness blocks (YCfn_cf.v fr_hblks_b), and the live bytes grew by at most j times the entry's room
   (YCfn_cf.v fr_live_post_b).  At most 4 calls (sv_calls = in[0] & 3 + 1, AD2f.v:23), so H_live gives fr_live_pre_b at
   every call with room to spare: 2^26 + 2^26 + 3 * (896 + OUT_MAX) + CALL_ROOM_B < 2^34 = LIVE_MAX at OUT_MAX =
   133,953,540 (YCfn_cf.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YP09 YI04 YI00 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v W_rep YCfn_cf.
(* Required, not Imported: the program globals G_fr_c (and its range lemmas), the image instance, ra_rel and the
   count names, cited by their qualified names in the XCNT lemmas *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_journal W_img W_contract ReplyCnt
  W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_G.
Import ListNotations.
Open Scope Z_scope.

Section h. Context {rc : YM05.RunCeil}.
Context {fx : YK11.FPState}.
Variable B : asyms.

Lemma heap_blocks_bytes_blocks : forall s, blocks_bytes s = fold_right (fun b acc => snd b + acc) 0 (blocks s).
Proof.
  intros s. unfold blocks_bytes, blocks. induction (st_chunks s) as [|k ks IH]; cbn; [reflexivity|].
  destruct (is_alloc k); cbn; rewrite IH; reflexivity.
Qed.

Definition fr_heap (j : nat) (buf cap q len : Z) (ly : alayout) (S : astate) (W : world tfibsegs)
  (mem : word -> option byte) : Prop :=
  In (buf, cap) (ablocks B ly S) /\ ~ In (buf, cap) (fr_hblks_b W mem) /\
  (0 < len -> In (q, len) (ablocks B ly S) /\ ~ In (q, len) (fr_hblks_b W mem)) /\
  blocks_bytes S <= cap + len + Z.of_nat j * (ATABLE + OUT_MAX) /\
  (* the harness blocks are distinct and alive: W8Entry-2's HB clause as LANDED on the B cut
     (commit e879350a388, lib/B/W_LLVMFuzzerTestOneInput_cut.v): the pre ends with
     `List.NoDup ((if n =? 0 then [] else [(p, n)]) ++ fr_hblks W mem) /\ incl (fr_hblks W mem) (ablocks B ly S)`
     (:282) and the post with the harness-only `List.NoDup (fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks ..)`
     (:296); fr_hblks (:251) is fr_hblks_b's text. Stdlib's List.NoDup (bare NoDup is stdpp's here). With the payload
     copy's own clause above, it gives the call's pre clause (H_call); the post's is H_step's premise as it is. *)
  List.NoDup (fr_hblks_b W mem) /\ incl (fr_hblks_b W mem) (ablocks B ly S) /\
  (* 0 <= g_capout <= CAPOUT_MAX (W8's CAPOUT clause, the call's pre and post, last; YCfn_cf.v fr_capout_ok_b) *)
  fr_capout_ok_b W mem /\
  (* W8's XCNT clause (the call's pre and post, before CAPOUT; YCfn_cf.v fr_xcnt_ok_b) at the call's input block: the
     relay and g_out as the globals hold them, and few other live blocks.  The loop's p is q when len > 0, so the
     call's input list is this one (H_xcnt) *)
  fr_xcnt_ok_b B ly S W mem (if len =? 0 then [] else [(q, len)]).

(* before the first call: the driver's blocks are exactly buf (and q), and no harness block is named yet (g_src = 0
   and g_capout = 0 in the start-up state) *)
Lemma H_init : forall (pb pq : sptr) buf cap q len ly S (W : world tfibsegs) mem,
  sptr_addr B ly pb = buf -> fr_hblks_b W mem = [] -> fr_capout_ok_b W mem ->
  fr_xcnt_ok_b B ly S W mem (if len =? 0 then [] else [(q, len)]) ->
  ((len = 0 /\ q = 0 /\ blocks S = [(pb, cap)]) \/
   (0 < len /\ blocks S = [(pb, cap); (pq, len)] /\ sptr_addr B ly pq = q)) ->
  fr_heap 0 buf cap q len ly S W mem.
Proof.
  intros pb pq buf cap q len ly S W mem Hb Hh Hc Hx Hbl. unfold fr_heap, ablocks. rewrite Hh.
  rewrite heap_blocks_bytes_blocks. cbn [Z.of_nat].
  destruct Hbl as [(-> & -> & Hbl) | (Hl & Hbl & Hq)]; rewrite Hbl; cbn [map fold_right fst snd].
  - rewrite Hb. split; [left; reflexivity|]. split; [intros []|]. split; [intros H; lia|].
    split; [lia | split; [constructor | split; [intros x [] | exact (conj Hc Hx)]]].
  - rewrite Hb, Hq. split; [left; reflexivity|]. split; [intros []|].
    split; [intros _; split; [right; left; reflexivity | intros []]|].
    split; [lia | split; [constructor | split; [intros x [] | exact (conj Hc Hx)]]].
Qed.

Lemma H_in : forall j buf cap q len ly S (W : world tfibsegs) mem,
  fr_heap j buf cap q len ly S W mem ->
  In (buf, cap) (ablocks B ly S) /\ (0 < len -> In (q, len) (ablocks B ly S)).
Proof.
  intros j buf cap q len ly S W mem (Hb & _ & Hq & _). split; [exact Hb|]. intros Hl. exact (proj1 (Hq Hl)).
Qed.

Lemma H_live : forall j buf cap q len ly S (W : world tfibsegs) mem,
  fr_heap j buf cap q len ly S W mem -> (j < 4)%nat -> 65536 <= cap <= 2 ^ 26 -> 0 <= len < cap ->
  fr_live_pre_b S.
Proof.
  intros j buf cap q len ly S W mem (_ & _ & _ & Hbb & _) Hj Hc Hl. unfold fr_live_pre_b, CALL_ROOM_B, LIVE_MAX, ATABLE, OUT_MAX in *.
  assert (Hj' : Z.of_nat j <= 3) by lia. nia.
Qed.

(* the live bytes at a call, as fr_heap gives them: the input buffer, q, and at most j entries' worth of growth
   (ATABLE + OUT_MAX each).  fr_surv_b does NOT say that a harness block the entry stops naming is freed, so an old
   g_out buffer may still count; the bound is therefore j-indexed, at most 3 growths at the fourth call.  A
   j-independent cap + len + ATABLE + OUT_MAX needs fr_surv_b's clause (2) to read `In b (fr_hblks_b W' mem') \/
   (In b (ablocks B ly S) /\ ~ In b (fr_hblks_b W mem))`, which holds for the program (realloc frees the old buffer)
   but is a change to W8's contract. *)
Lemma H_bytes : forall j buf cap q len ly S (W : world tfibsegs) mem,
  fr_heap j buf cap q len ly S W mem -> (j < 4)%nat ->
  blocks_bytes S <= cap + len + Z.of_nat j * (ATABLE + OUT_MAX) /\
  blocks_bytes S <= cap + len + 3 * (ATABLE + OUT_MAX).
Proof.
  intros j buf cap q len ly S W mem (_ & _ & _ & Hbb & _) Hj. split; [exact Hbb|].
  assert (Hj' : Z.of_nat j <= 3) by lia. unfold ATABLE, OUT_MAX in *. nia.
Qed.

Lemma H_step : forall j buf cap q len ly S (W : world tfibsegs) mem ly' S' (W' : world tfibsegs) mem' k,
  fr_heap j buf cap q len ly S W mem -> fr_surv_b B ly S W mem ly' S' W' mem' -> fr_live_post_b S S' k ->
  List.NoDup (fr_hblks_b W' mem') /\ incl (fr_hblks_b W' mem') (ablocks B ly' S') -> fr_capout_ok_b W' mem' ->
  fr_xcnt_ok_b B ly' S' W' mem' (if len =? 0 then [] else [(q, len)]) ->
  fr_heap (Datatypes.S j) buf cap q len ly' S' W' mem'.
Proof.
  intros j buf cap q len ly S W mem ly' S' W' mem' k (Hb & Hbh & Hq & Hbb & _) (Hs1 & _ & Hs3) (Hlp & _) HHB' HCAP'
    HXC'.
  (* a driver block that is not a harness block at the entry survives, and is not a harness block at the return:
     the return's harness blocks are fresh or were harness blocks at the entry *)
  assert (KEEP : forall b, In b (ablocks B ly S) -> ~ In b (fr_hblks_b W mem) ->
            In b (ablocks B ly' S') /\ ~ In b (fr_hblks_b W' mem')).
  { intros b Hin Hnh. split; [exact (Hs1 b Hin Hnh)|].
    intros Hh'. destruct (Hs3 b Hh') as [Hn | Hh]; [exact (Hn Hin) | exact (Hnh Hh)]. }
  destruct (KEEP _ Hb Hbh) as (Hb' & Hbh').
  unfold fr_heap. split; [exact Hb'|]. split; [exact Hbh'|]. split.
  - intros Hl. destruct (Hq Hl) as (Hqi & Hqh). exact (KEEP _ Hqi Hqh).
  - split; [|exact (conj (proj1 HHB') (conj (proj2 HHB') (conj HCAP' HXC')))].
    rewrite Nat2Z.inj_succ. unfold ATABLE, OUT_MAX in *. lia.
Qed.

(* the call's HFP clause from fr_heap, at the argument the loop passes (A_EMPTY_tfa when there is no payload) *)
Lemma H_call : forall j buf cap q len ly S (W : world tfibsegs) mem (pe : Z),
  fr_heap j buf cap q len ly S W mem -> 0 <= len ->
  List.NoDup ((if len =? 0 then [] else [((if len =? 0 then pe else q), len)]) ++ fr_hblks_b W mem) /\
  incl (fr_hblks_b W mem) (ablocks B ly S).
Proof.
  intros j buf cap q len ly S W mem pe (_ & _ & Hq & _ & Hnd & Hinc & _) Hl. split; [|exact Hinc].
  destruct (len =? 0) eqn:E; cbn [app]; [exact Hnd|]. apply Z.eqb_neq in E.
  change (if false then pe else q) with q.
  assert (Hlen : 0 < len) by lia. destruct (Hq Hlen) as [_ Hni].
  constructor; [exact Hni | exact Hnd].
Qed.

(* the call's CAPOUT clause from fr_heap *)
Lemma H_capout : forall j buf cap q len ly S (W : world tfibsegs) mem,
  fr_heap j buf cap q len ly S W mem -> fr_capout_ok_b W mem.
Proof. intros j buf cap q len ly S W mem (_ & _ & _ & _ & _ & _ & HC & _). exact HC. Qed.

(* the call's XCNT clause from fr_heap, at the argument the loop passes (A_EMPTY_tfa when there is no payload) *)
Lemma H_xcnt : forall j buf cap q len ly S (W : world tfibsegs) mem (pe : Z),
  fr_heap j buf cap q len ly S W mem ->
  fr_xcnt_ok_b B ly S W mem (if len =? 0 then [] else [((if len =? 0 then pe else q), len)]).
Proof.
  intros j buf cap q len ly S W mem pe (_ & _ & _ & _ & _ & _ & _ & HX). revert HX.
  destruct (len =? 0); intros HX; exact HX.
Qed.

(* XCNT at the first call: fr_gi (the per-call invariant) names the relay and g_out, and the driver holds at most two
   blocks (buf and q), so every count is at most 2 <= SEC0 = CLS0 = 64 (ReplyCnt.v) *)
Lemma fr_xcnt_init : forall ly S (W : world tfibsegs) mem inp,
  (exists T, W_contract.ra_rel B W_LLVMFuzzerTestOneInput_cut.fr_RG ly S W mem T []) ->
  (exists c O mx cap out,
     aout_at B W_LLVMFuzzerTestOneInput_cut.fr_RG ly S W mem c O mx (Z.of_nat (length O)) cap out) ->
  (length (blocks S) <= 2)%nat -> fr_xcnt_ok_b B ly S W mem inp.
Proof.
  intros ly S W mem inp (T & HT) (c & O & mx & cap & out & HO) Hlen.
  exists T, c, O, mx, cap, out. split; [exact HT|]. split; [exact HO|].
  assert (FL : forall (f : Z -> bool) (l : list Z), (length (List.filter f l) <= length l)%nat).
  { intros f l. induction l as [|x l IH]; cbn [List.filter length]; [lia|]. destruct (f x); cbn [length]; lia. }
  assert (L : forall P, (ReplyCnt.acnt P (ablocks B ly S) <= 2)%nat).
  { intros P. unfold ReplyCnt.acnt. eapply Nat.le_trans; [apply FL|]. unfold ablocks. rewrite !length_map. exact Hlen. }
  unfold ReplyCnt.xcnt_ok, ReplyCnt.cnt_sec, ReplyCnt.cnt_cls, ReplyCnt.SEC0, ReplyCnt.CLS0.
  split; [pose proof (L ReplyCnt.Psec); lia|]. intros c0 _. pose proof (L (ReplyCnt.Pcls c0)). lia.
Qed.

Lemma rdword_ext : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  assert (H0 : rd' a = rd a) by (rewrite <- (Z.add_0_r a); apply H; lia).
  rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* fr_hblks_b reads only the three 8-byte words g_src, g_out and g_capout *)
Definition fr_hwords_kept (W : world tfibsegs) (mem : word -> option byte) (W' : world tfibsegs)
  (mem' : word -> option byte) : Prop :=
  forall i, 0 <= i < 8 ->
    aview tfibsegs (w_H W') mem' (rg_src fr_globals_b + i) = aview tfibsegs (w_H W) mem (rg_src fr_globals_b + i) /\
    aview tfibsegs (w_H W') mem' (rg_out fr_globals_b + i) = aview tfibsegs (w_H W) mem (rg_out fr_globals_b + i) /\
    aview tfibsegs (w_H W') mem' (rg_capout fr_globals_b + i) = aview tfibsegs (w_H W) mem (rg_capout fr_globals_b + i).

Lemma fr_hblks_kept : forall (W : world tfibsegs) mem (W' : world tfibsegs) mem',
  fr_hwords_kept W mem W' mem' -> fr_hblks_b W' mem' = fr_hblks_b W mem.
Proof.
  intros W mem W' mem' HK. unfold fr_hblks_b.
  rewrite (rdword_ext (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W') mem') (rg_src fr_globals_b))
    by (intros i Hi; exact (proj1 (HK i Hi))).
  rewrite (rdword_ext (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W') mem') (rg_out fr_globals_b))
    by (intros i Hi; exact (proj1 (proj2 (HK i Hi)))).
  rewrite (rdword_ext (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W') mem') (rg_capout fr_globals_b))
    by (intros i Hi; exact (proj2 (proj2 (HK i Hi)))).
  reflexivity.
Qed.

(* the CAPOUT clause reads only g_capout's 8 bytes (fr_hwords_kept's third clause): aview is bv_unsigned over mbyte,
   so equal views give equal bytes *)
Lemma fr_capout_kept : forall (W : world tfibsegs) mem (W' : world tfibsegs) mem',
  fr_hwords_kept W mem W' mem' -> fr_capout_ok_b W mem -> fr_capout_ok_b W' mem'.
Proof.
  intros W mem W' mem' HK (c & Hv & Hc). exists c. split; [|exact Hc].
  intros k Hk. assert (Hi : 0 <= Z.of_nat k < 8) by lia.
  pose proof (proj2 (proj2 (HK _ Hi))) as E. pose proof (Hv k Hk) as Hb.
  change (mbyte tfibsegs (mrestrict (w_H W) mem) (rg_capout fr_globals_b + Z.of_nat k) = Some (Z_to_bv 8 (le_byte c 8 k)))
    in Hb.
  change (mbyte tfibsegs (mrestrict (w_H W') mem') (rg_capout fr_globals_b + Z.of_nat k) = Some (Z_to_bv 8 (le_byte c 8 k))).
  unfold aview in E. cbv beta in E. rewrite Hb in E.
  destruct (mbyte tfibsegs (mrestrict (w_H W') mem') (rg_capout fr_globals_b + Z.of_nat k)) as [b'|] eqn:Eb';
    rewrite ?Eb' in E; cbn [option_map] in E; [|discriminate].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Local Ltac kg KG := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; try (cbn [fst snd] in Hx); eapply KG; [|exact Hx]; vm_compute; reflexivity.

(* the XCNT clause reads the program globals (g_src, g_nsrc, g_capsrc, the stream's cells and errno: G_fr_c) and the
   bytes of live blocks (the relay's table, g_out's buffer); with those bytes kept and the live blocks unchanged it is
   kept with the same witnesses (W_rep.v arelay_at_kept / aout_at_kept; the counts read ablocks only) *)
Lemma fr_xcnt_kept : forall ly S (W : world tfibsegs) mem ly' S' (W' : world tfibsegs) mem' inp,
  fr_xcnt_ok_b B ly S W mem inp ->
  (forall a, W_journal.inG (W_LLVMFuzzerTestOneInput_G.G_fr_c B) a -> abyte_kept (PI := W_img.PB_fr) W mem W' mem' a) ->
  (forall b n a, In (b, n) (ablocks B ly S) -> b <= a < b + n -> abyte_kept (PI := W_img.PB_fr) W mem W' mem' a) ->
  ablocks B ly' S' = ablocks B ly S ->
  fr_xcnt_ok_b B ly' S' W' mem' inp.
Proof.
  intros ly S W mem ly' S' W' mem' inp (T0 & c & O & mx & cap & out & Hra & Hao & Hx) KGF KB Hab.
  assert (KG : forall lo hi, W_LLVMFuzzerTestOneInput_G.rng_inb lo (hi - lo) W_LLVMFuzzerTestOneInput_G.G_fr_obj = true ->
    forall a, lo <= a < hi -> abyte_kept (PI := W_img.PB_fr) W mem W' mem' a).
  { intros lo hi Hb a Ha. apply KGF. apply (W_LLVMFuzzerTestOneInput_G.obj_c B).
    apply (W_LLVMFuzzerTestOneInput_G.rng_cover lo (hi - lo) _ Hb). lia. }
  exists T0, c, O, mx, cap, out. split; [|split].
  - destruct Hra as [(HT & Hes & E1 & E2 & E3 & E4 & E5 & E6) | A].
    + left. split; [exact HT|]. split; [exact Hes|].
      split; [apply (akept_vm (PI := W_img.PB_fr) W mem); [kg KG | exact E1]|].
      split; [apply (akept_awr (PI := W_img.PB_fr) W mem); [kg KG | exact E2]|].
      split; [apply (akept_vm (PI := W_img.PB_fr) W mem); [kg KG | exact E3]|].
      split; [apply (akept_awr (PI := W_img.PB_fr) W mem); [kg KG | exact E4]|].
      split; [apply (akept_vm (PI := W_img.PB_fr) W mem); [kg KG | exact E5]|].
      apply (akept_awr (PI := W_img.PB_fr) W mem); [kg KG | exact E6].
    + right. pose proof A as (_ & _ & _ & _ & _ & _ & _ & A8 & _).
      apply (arelay_at_kept (PI := W_img.PB_fr) B W_LLVMFuzzerTestOneInput_cut.fr_RG ly S W mem); [exact A | |].
      * intros r Hr. cbn [arelay_fp concat map In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; [kg KG | kg KG | kg KG |].
        intros a Ha. cbn [fst snd] in Ha. exact (KB T0 ATABLE a A8 Ha).
      * intros b Hb. cbn [arelay_blks concat map In] in Hb. destruct Hb as [<-|[]]. rewrite Hab. exact A8.
  - assert (Hblk : cap <> 0 -> In (out, cap) (ablocks B ly S)).
    { intros Hc. pose proof Hao as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & _ & _ & H26).
      destruct H26 as [(E & _) | (_ & _ & Hin & _)]; [contradiction | exact Hin]. }
    apply (aout_at_kept (PI := W_img.PB_fr) B W_LLVMFuzzerTestOneInput_cut.fr_RG ly S W mem); [exact Hao | |].
    + intros r Hr. unfold aout_fp in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]];
        [kg KG | kg KG | kg KG | kg KG | kg KG | kg KG | kg KG | kg KG | |].
      * intros a Ha. cbn [fst snd] in Ha. apply KGF. apply (W_LLVMFuzzerTestOneInput_G.err_c B). exact Ha.
      * revert Hr. destruct (Z.eqb_spec cap 0) as [_|Hc]; intros Hr; [destruct Hr|].
        destruct Hr as [<-|[]]. intros a Ha. cbn [fst snd] in Ha. exact (KB out cap a (Hblk Hc) Ha).
    + intros b Hb. unfold aout_blks in Hb. revert Hb.
      destruct (Z.eqb_spec cap 0) as [_|Hc]; intros Hb; [destruct Hb|].
      destruct Hb as [<-|[]]. rewrite Hab. exact (Hblk Hc).
  - unfold ReplyCnt.xcnt_ok in *. rewrite Hab. exact Hx.
Qed.

(* between calls the driver frees nothing and keeps the three harness words (printf, the vprintf interceptor, the
   branch run), the program globals and the bytes of the live blocks: fr_heap is kept *)
Lemma H_frame : forall j buf cap q len ly S (W : world tfibsegs) mem ly' S' (W' : world tfibsegs) mem',
  fr_heap j buf cap q len ly S W mem -> fr_hwords_kept W mem W' mem' ->
  (forall a, W_journal.inG (W_LLVMFuzzerTestOneInput_G.G_fr_c B) a -> abyte_kept (PI := W_img.PB_fr) W mem W' mem' a) ->
  (forall b n a, In (b, n) (ablocks B ly S) -> b <= a < b + n -> abyte_kept (PI := W_img.PB_fr) W mem W' mem' a) ->
  ablocks B ly' S' = ablocks B ly S -> blocks_bytes S' = blocks_bytes S ->
  fr_heap j buf cap q len ly' S' W' mem'.
Proof.
  intros j buf cap q len ly S W mem ly' S' W' mem' HH HK KGF KB Hab Hbb.
  pose proof (fr_capout_kept W mem W' mem' HK (H_capout _ _ _ _ _ _ _ _ _ HH)) as HC'.
  pose proof HH as (_ & _ & _ & _ & _ & _ & _ & HX).
  pose proof (fr_xcnt_kept ly S W mem ly' S' W' mem' _ HX KGF KB Hab) as HX'.
  unfold fr_heap in *. rewrite (fr_hblks_kept W mem W' mem' HK), Hab, Hbb.
  destruct HH as (H1 & H2 & H3 & H4 & H5 & H6 & _).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj HC' HX'))))))).
Qed.
End h.
