(* fuzz_preset, kit: THE WITNESS THAT THE UNIVERSE CLOSURE IS SATISFIABLE AT THE REAL IMAGES (the P'' landing's
   acceptance condition, the kit owner and the unit owner). Every text's universe premise is
   PRH_Base.prh_univ_closure B CTX0 (no run words: the universe is a function of the IMAGE only, the S1 owner's P''
   answer). This file proves that premise TRUE, and the old clause-4 forms FALSE, at
   - B': PI := PRH_ImgB.prh_img_B, ci := lib.AU.CfImgB.CfImg_B, CTX0 := [[0x815c8]] (the driver's context
         [[RA_LLVMF]], RA_LLVMF 0x815c8), the universe lib.Reusable.YCej.Tfib_universe (the B' walker's Univ form,
         blob dd7d1838e568) and the code record lib.Reusable.YF0l.Tfib_code;
   - A': PI := PRH_Img.prh_img_A, ci := lib.A.CfImgA.CfImg_A, CTX0 := [[0x814dc]] (RA_LLVMF 0x814dc), the universe
         lib.A.ACej.Tfib_universe (`tools/startup/gen_acej.py --univ --wild-cursor --clause5`, sha256 e889984e3326,
         blob 9c1da4e01665: the 176 fixed traces, the 98 of the round-trip stack walker's f707fd5a39dd and the 78 clause 5 adds,
         Tfib_wild = the two cursor prefixes [0x53878; 0x87764], [0x53878; 0x87e50] and tx_put's [0x53c74; 0x84db0])
         and the code record lib.A.AF0l.Tfib_code.
   STATED OVER THE IMAGE UNIVERSES THEMSELVES, NOT OVER THE INSTANCE RECORDS: each theorem holds for EVERY asyms B
   whose as_universe and as_code are the image's (the fields the closure reads, with the CfImg's
   cf_pc_realloc_ra0), the way tools/satchk ran with --image U. A KNOWN LIMIT, reported by the round-trip stack walker: on univcore +
   int102, lib/A/AF0m.v:1810 and lib/Reusable/YF0m.v:1812 FAIL, so AD2l / YD2l do not build. So this file does not
   Require the instance records lib/A/AD2l.v / lib/Reusable/YD2l.v.
   THE WITNESS MENTIONS NO METER AND NO START STATE: it is a statement about the image's universe only. Whether a
   run's depot has ROOM for the wild traces (YG01.admits) is the room COUNT thread (PRH_Base.prh_univ_closure's
   note; owned by the S1 owner), not stated here.
   METHOD: a decision procedure proved sound once (prh_univ_closure_of_check), run by vm_compute at each image.
   Clause 3 quantifies over every context prh_reach derives (infinitely many: ex_value calls itself and keeps a frame
   pointer); the procedure tracks each reachable (F, firstn kUnwindMax c), a finite set computed to its fixpoint
   (prh_wit_iter) and CHECKED closed (prh_wit_closed), and uses that no context word is an allocator trace's start
   pc (prh_wit_avoid), so a trace reads only the first kUnwindMax - 1 words of a context (prh_trace_firstn).
   Clause 4b quantifies over EVERY word w; the procedure checks, at each cursor free site r, r <> pc0 and the wild
   prefix [pc0; r] (prh_wit_c4b), which gives inU of prh_trace pc0 r [w] for every w (prh_wit_inU_wild).
   CLAUSES 1-3 AND 4a: on paper they carry over BY INCLUSION from the old universes (the old A' c4a400418590's 98 and
   the old B' 8a099324acb0's traces have zero missing against the new fixed lists); this file does not rely on that
   argument: it RE-CHECKS all six clauses (1, 2, 3, 4a, 4b, 5) at the new universes by vm_compute, so once it builds
   the carry-over is a machine check.
   CLAUSE 5 (the frame-pointer-less callee F of a frame-pointer caller G, F's site over G's context): checked at each
   reachable frame-pointer state (G, c) of the fixpoint and each such F that G calls (prh_wit_c5), soundness as for
   clause 3. Its consumer is padded on B': c5_padded_trace_B below derives padded's trace over its caller's chain.
   THE NEGATIVE CONTROLS: B', the OLD clause 4 (`In _ (as_universe B)`, list membership, which under P'' is
   membership in the FIXED part through the coercion u_fix) is FALSE for a data word (the S1 owner's
   B_clause4_In_fails, lib/ZZUnivWild.v on commit 8f07344ff7b7; restated here,
   because the kit cannot Require that scratch file). A', a universe with the OLD A' wild part (ACej 0ee7e2bcf2f0:
   Tfib_wild = [[0x53c74; 0x84db0]] only, fixed traces among the 98 that file had) FAILS clause 4b (the S1 owner's
   A_clause4_inU_fails_today, same scratch file; the old file is not carried: the theorem is stated for every
   universe with that wild part and fixed traces among today's ACej's, which hold that file's 98).
   NOT A KIT TEXT: it Requires the image tables and the image universes, so no kit text Requires it. Nothing here is
   a function's proof (rule 24). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0f YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Img CfImgA AF0l ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0l YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require WildRoomInstA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require WildRoomInstB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require WildBudget.
Import ListNotations.
Local Open Scope Z_scope.

Scheme Equality for prh_fn.

(* every program function and every allocator entry, listed *)
Definition prh_wit_fns : list prh_fn :=
  [F_LLVMFuzzerTestOneInput; F_check_no_overread; F_check_bounded_alloc; F_check_as_written; F_check_reject_clean;
   F_check_reject_clean_starved; F_check_round_trip; F_parse_noting; F_same; F_ex_value; F_ex_string; F_ex_word;
   F_ex_hex4; F_ex_utf8; F_round_trip_text; F_tx_put; F_tx_value; F_tx_string; F_tx_line; F_fuzz_malloc;
   F_fuzz_realloc; F_fuzz_strdup; F_fuzz_free; F_fuzz_alloc_live; F_fuzz_alloc_peak; F_fuzz_alloc_peak_reset;
   F_fuzz_alloc_count; F_fuzz_alloc_fail; F_fuzz_alloc_ran_out; F_fuzz_alloc_ran_out_reset; F_pj_parse;
   F_parse_value; F_pj_free; F_pj_get; F_pj_get_str; F_pj_set; F_grow; F_pj_string; F_pj_write; F_write_value;
   F_put; F_parse_items; F_parse_string; F_literal; F_hex4; F_put_utf8; F_put_string; F_indent;
   F_read_members; F_fuzz_alloc_most; F_own; F_skip_ws; F_ex_ws; F_padded; F_fuzz_pick].
Lemma prh_wit_fns_all : forall F, In F prh_wit_fns.
Proof. intros F; destruct F; cbn [In prh_wit_fns]; repeat (first [left; reflexivity | right]). Qed.
Definition prh_wit_rts : list prh_rt := [RT_malloc; RT_free; RT_realloc; RT_fuzz_free].
Lemma prh_wit_rts_all : forall rt, In rt prh_wit_rts.
Proof. intros rt; destruct rt; cbn [In prh_wit_rts]; repeat (first [left; reflexivity | right]). Qed.

(* membership of a trace in a list of traces, decided *)
Definition prh_wit_memU (t : list Z) (U : list (list Z)) : bool :=
  existsb (fun u => if list_eq_dec Z.eq_dec u t then true else false) U.
Lemma prh_wit_memU_In : forall t U, prh_wit_memU t U = true -> In t U.
Proof.
  intros t U H. apply existsb_exists in H as (u & Hu & Hb).
  destruct (list_eq_dec Z.eq_dec u t) as [<-|]; [exact Hu | discriminate].
Qed.
Lemma prh_wit_In_memU : forall t U, In t U -> prh_wit_memU t U = true.
Proof.
  intros t U H. apply existsb_exists. exists t. split; [exact H|].
  destruct (list_eq_dec Z.eq_dec t t) as [_|E]; [reflexivity | contradiction E; reflexivity].
Qed.

(* a word that is not the trace's start pc passes prh_trace's filter *)
Lemma prh_wit_fm_avoid : forall pc0 l, Forall (fun a => a <> pc0) l ->
  flat_map (fun ra => if ra =? pc0 then [] else [ra]) l = l.
Proof.
  intros pc0 l H. induction H as [|a l Ha _ IH]; [reflexivity|].
  cbn [flat_map]. rewrite IH. destruct (Z.eqb_spec a pc0); [contradiction | reflexivity].
Qed.
Lemma prh_wit_Forall_firstn : forall (P : Z -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof.
  intros P n l H. revert n. induction H as [|a l Ha _ IH]; intros [|n]; cbn [firstn]; constructor; auto.
Qed.
(* a trace reads only the first kUnwindMax - 1 words of a context free of the start pc *)
Lemma prh_trace_firstn : forall pc0 r l n, (29 <= n)%nat -> Forall (fun a => a <> pc0) l ->
  prh_trace pc0 r l = prh_trace pc0 r (firstn n l).
Proof.
  intros pc0 r l n Hn Hl. unfold prh_trace. cbn [flat_map].
  rewrite (prh_wit_fm_avoid pc0 l Hl), (prh_wit_fm_avoid pc0 (firstn n l) (prh_wit_Forall_firstn _ n l Hl)).
  unfold kUnwindMax. cbn [firstn]. f_equal.
  destruct (r =? pc0); cbn [app firstn]; [|f_equal]; rewrite firstn_firstn, Nat.min_l by lia; reflexivity.
Qed.

(* A CURSOR FREE'S TRACE AT ANY WORD IS WILD-SHAPED: with r <> pc0, prh_trace pc0 r [w] is [pc0; r] followed by
   w (or nothing, when w = pc0), so a wild prefix [pc0; r] puts it in the universe for EVERY w *)
Lemma prh_wit_trace_w : forall pc0 r w, r <> pc0 ->
  prh_trace pc0 r [w] = [pc0; r] ++ (if w =? pc0 then [] else [w]).
Proof.
  intros pc0 r w Hr. unfold prh_trace. cbn [flat_map app].
  destruct (Z.eqb_spec r pc0) as [E|_]; [contradiction|].
  destruct (w =? pc0); reflexivity.
Qed.
Lemma prh_wit_inU_wild : forall (U : Univ) pc0 r w, r <> pc0 -> In [pc0; r] (u_wild U) ->
  inU U (prh_trace pc0 r [w]).
Proof.
  intros U pc0 r w Hr Hw. rewrite (prh_wit_trace_w pc0 r w Hr). split.
  - destruct (w =? pc0); unfold kUnwindMax; cbn; lia.
  - right. exists [pc0; r], (if w =? pc0 then [] else [w]). split; [exact Hw | reflexivity].
Qed.

Section check.
Context {PI : PrhImg} (B : asyms) {ci : CfImg}.

Definition prh_wit_K : nat := kUnwindMax.

(* the abstract reachable states: a function and the first kUnwindMax words of a context it runs in *)
Definition prh_wit_st_eqb (p q : prh_fn * list Z) : bool :=
  (if prh_fn_eq_dec (fst p) (fst q) then true else false) &&
  (if list_eq_dec Z.eq_dec (snd p) (snd q) then true else false).
Definition prh_wit_mem (p : prh_fn * list Z) (L : list (prh_fn * list Z)) : bool := existsb (prh_wit_st_eqb p) L.
Lemma prh_wit_mem_In : forall p L, prh_wit_mem p L = true -> In p L.
Proof.
  intros [F x] L H. apply existsb_exists in H as ([G y] & Hq & Hb). unfold prh_wit_st_eqb in Hb. cbn [fst snd] in Hb.
  destruct (prh_fn_eq_dec F G) as [<-|]; [|discriminate].
  destruct (list_eq_dec Z.eq_dec x y) as [<-|]; [exact Hq | discriminate].
Qed.
Lemma prh_wit_In_mem : forall p L, In p L -> prh_wit_mem p L = true.
Proof.
  intros [F x] L H. apply existsb_exists. exists (F, x). split; [exact H|].
  unfold prh_wit_st_eqb. cbn [fst snd].
  destruct (prh_fn_eq_dec F F) as [_|E]; [|contradiction E; reflexivity].
  destruct (list_eq_dec Z.eq_dec x x) as [_|E]; [reflexivity | contradiction E; reflexivity].
Qed.

(* one step of prh_reach on abstract states *)
Definition prh_wit_succ (p : prh_fn * list Z) : list (prh_fn * list Z) :=
  flat_map (fun G =>
    map (fun r => (G, firstn prh_wit_K (if pi_fp (fst p) then r :: snd p else [r]))) (pi_call_rets (fst p) G) ++
    (if pi_tails (fst p) G then [(G, snd p)] else [])) prh_wit_fns.
Definition prh_wit_add (L l : list (prh_fn * list Z)) : list (prh_fn * list Z) :=
  fold_left (fun acc q => if prh_wit_mem q acc then acc else q :: acc) l L.
Fixpoint prh_wit_iter (n : nat) (L : list (prh_fn * list Z)) : list (prh_fn * list Z) :=
  match n with
  | O => L
  | Datatypes.S n' => prh_wit_iter n' (prh_wit_add L (flat_map prh_wit_succ L))
  end.
Definition prh_wit_closed (CTX0 : list (list Z)) (L : list (prh_fn * list Z)) : bool :=
  forallb (fun c => prh_wit_mem (F_LLVMFuzzerTestOneInput, firstn prh_wit_K c) L) CTX0 &&
  forallb (fun p => forallb (fun q => prh_wit_mem q L) (prh_wit_succ p)) L.

Lemma prh_wit_firstn_cons : forall (r : Z) (c : list Z),
  firstn prh_wit_K (r :: firstn prh_wit_K c) = firstn prh_wit_K (r :: c).
Proof.
  intros r c. unfold prh_wit_K, kUnwindMax. cbn [firstn]. f_equal.
  rewrite firstn_firstn, Nat.min_l by lia. reflexivity.
Qed.

Lemma prh_wit_reach_in : forall CTX0 L, prh_wit_closed CTX0 L = true ->
  forall F c, prh_reach CTX0 F c -> In (F, firstn prh_wit_K c) L.
Proof.
  intros CTX0 L HC. apply andb_prop in HC as [H0 H1].
  rewrite forallb_forall in H0, H1.
  induction 1 as [c Hc | F G c r HR IH Hr | F G c HR IH Ht].
  - apply prh_wit_mem_In. exact (H0 c Hc).
  - apply prh_wit_mem_In. pose proof (H1 _ IH) as Hs. rewrite forallb_forall in Hs. apply Hs.
    unfold prh_wit_succ. cbn [fst snd]. apply in_flat_map. exists G. split; [apply prh_wit_fns_all|].
    apply in_or_app. left. apply in_map_iff. exists r. split; [|exact Hr].
    destruct (pi_fp F); [rewrite prh_wit_firstn_cons|]; reflexivity.
  - apply prh_wit_mem_In. pose proof (H1 _ IH) as Hs. rewrite forallb_forall in Hs. apply Hs.
    unfold prh_wit_succ. cbn [fst snd]. apply in_flat_map. exists G. split; [apply prh_wit_fns_all|].
    apply in_or_app. right. rewrite Ht. left. reflexivity.
Qed.

(* every context word is a return site of the table or a word of CTX0 *)
Definition prh_wit_words (CTX0 : list (list Z)) : list Z :=
  concat CTX0 ++ flat_map (fun F => flat_map (pi_call_rets F) prh_wit_fns) prh_wit_fns.
Lemma prh_wit_reach_words : forall CTX0 F c, prh_reach CTX0 F c -> Forall (fun a => In a (prh_wit_words CTX0)) c.
Proof.
  intros CTX0 F c HR.
  assert (Hr : forall F G r, In r (pi_call_rets F G) -> In r (prh_wit_words CTX0)).
  { intros F0 G0 r0 H. unfold prh_wit_words. apply in_or_app. right. apply in_flat_map. exists F0.
    split; [apply prh_wit_fns_all|]. apply in_flat_map. exists G0. split; [apply prh_wit_fns_all | exact H]. }
  induction HR as [c Hc | F G c r HR IH Hrr | F G c HR IH Ht].
  - apply Forall_forall. intros a Ha. unfold prh_wit_words. apply in_or_app. left. apply in_concat.
    exists c. split; [exact Hc | exact Ha].
  - destruct (pi_fp F); constructor; [exact (Hr _ _ _ Hrr) | exact IH | exact (Hr _ _ _ Hrr) | constructor].
  - exact IH.
Qed.
Definition prh_wit_avoid (CTX0 : list (list Z)) : bool :=
  forallb (fun rt => forallb (fun a => negb (a =? prh_pc0 B rt)) (prh_wit_words CTX0)) prh_wit_rts.
Lemma prh_wit_avoid_ok : forall CTX0 F c rt, prh_wit_avoid CTX0 = true -> prh_reach CTX0 F c ->
  Forall (fun a => a <> prh_pc0 B rt) c.
Proof.
  intros CTX0 F c rt HA HR. unfold prh_wit_avoid in HA. rewrite forallb_forall in HA.
  pose proof (HA rt (prh_wit_rts_all rt)) as H. rewrite forallb_forall in H.
  eapply Forall_impl; [|exact (prh_wit_reach_words CTX0 F c HR)]. cbn beta. intros a Ha E.
  specialize (H a Ha). rewrite E, Z.eqb_refl in H. cbn in H. discriminate.
Qed.

(* the five clauses, decided; clauses 1-3 and 4a in the FIXED part, 4b through the wild prefixes *)
Definition prh_wit_c1 : bool :=
  forallb (fun rt => prh_wit_memU [prh_pc0 B rt] (u_fix (as_universe B))) prh_wit_rts.
Definition prh_wit_c2 : bool :=
  forallb (fun F => forallb (fun rt => forallb (fun r =>
    prh_wit_memU (prh_trace (prh_pc0 B rt) r []) (u_fix (as_universe B)))
    (pi_ret_sites F rt)) prh_wit_rts) prh_wit_fns.
Definition prh_wit_c3 (L : list (prh_fn * list Z)) : bool :=
  forallb (fun p => if pi_fp (fst p) then
    forallb (fun rt => forallb (fun r => forallb (fun j =>
      prh_wit_memU (prh_trace (prh_pc0 B rt) r (firstn j (snd p))) (u_fix (as_universe B)))
      (seq 0 (Datatypes.S prh_wit_K))) (pi_ret_sites (fst p) rt)) prh_wit_rts
    else true) L.
Definition prh_wit_c4a : bool :=
  forallb (fun F => forallb (fun r => forallb (fun w =>
    prh_wit_memU (prh_trace (pc_free_ra0 (as_code B)) r [w]) (u_fix (as_universe B)))
    (pi_call_rets F_pj_parse F_parse_value)) (prh_free_sites F)) [F_parse_string; F_parse_items].
Definition prh_wit_c4b : bool :=
  forallb (fun F => forallb (fun r =>
    negb (r =? pc_free_ra0 (as_code B)) &&
    prh_wit_memU [pc_free_ra0 (as_code B); r] (u_wild (as_universe B)))
    (prh_free_sites F)) [F_parse_string; F_parse_items].
(* clause 5, at each reachable FRAME-POINTER state (G, c) and each F without a frame pointer that G calls *)
Definition prh_wit_c5 (L : list (prh_fn * list Z)) : bool :=
  forallb (fun p => if pi_fp (fst p) then
    forallb (fun F => if pi_fp F then true else
      match pi_call_rets (fst p) F with
      | [] => true
      | _ :: _ => forallb (fun rt => forallb (fun r => forallb (fun j =>
          prh_wit_memU (prh_trace (prh_pc0 B rt) r (firstn j (snd p))) (u_fix (as_universe B)))
          (seq 0 (Datatypes.S prh_wit_K))) (pi_ret_sites F rt)) prh_wit_rts
      end) prh_wit_fns
    else true) L.
Definition prh_wit_check (CTX0 : list (list Z)) (L : list (prh_fn * list Z)) : bool :=
  prh_wit_c1 && prh_wit_c2 && prh_wit_closed CTX0 L && prh_wit_avoid CTX0 && prh_wit_c3 L && prh_wit_c4a &&
  prh_wit_c4b && prh_wit_c5 L.

(* THE DECISION PROCEDURE IS SOUND *)
Theorem prh_univ_closure_of_check : forall CTX0 L, prh_wit_check CTX0 L = true ->
  prh_univ_closure B CTX0.
Proof.
  intros CTX0 L H. unfold prh_wit_check in H.
  apply andb_prop in H as [H H5].
  apply andb_prop in H as [H H4b]. apply andb_prop in H as [H H4a].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H HA].
  apply andb_prop in H as [H HC]. apply andb_prop in H as [H1 H2].
  unfold prh_wit_c1 in H1. unfold prh_wit_c2 in H2. unfold prh_wit_c3 in H3.
  unfold prh_wit_c4a in H4a. unfold prh_wit_c4b in H4b. unfold prh_wit_c5 in H5.
  rewrite forallb_forall in H1, H2, H3, H4a, H4b, H5.
  split; [|split; [|split; [|split; [|split]]]].
  - intros rt. apply prh_wit_memU_In. exact (H1 rt (prh_wit_rts_all rt)).
  - intros F rt r Hr. apply prh_wit_memU_In.
    pose proof (H2 F (prh_wit_fns_all F)) as H. rewrite forallb_forall in H.
    pose proof (H rt (prh_wit_rts_all rt)) as H'. rewrite forallb_forall in H'. exact (H' r Hr).
  - intros F c rt r j HR Hfp Hr. apply prh_wit_memU_In.
    pose proof (H3 _ (prh_wit_reach_in CTX0 L HC F c HR)) as H. cbn [fst snd] in H. rewrite Hfp in H.
    rewrite forallb_forall in H. pose proof (H rt (prh_wit_rts_all rt)) as H'. rewrite forallb_forall in H'.
    pose proof (H' r Hr) as H''. rewrite forallb_forall in H''.
    destruct (le_lt_dec j prh_wit_K) as [Hj | Hj].
    + replace (firstn j c) with (firstn j (firstn prh_wit_K c)) by (rewrite firstn_firstn, Nat.min_l by lia; reflexivity).
      apply H''. apply in_seq. lia.
    + rewrite (prh_trace_firstn (prh_pc0 B rt) r (firstn j c) prh_wit_K); cycle 1.
      { unfold prh_wit_K, kUnwindMax. lia. }
      { exact (prh_wit_Forall_firstn _ j c (prh_wit_avoid_ok CTX0 F c rt HA HR)). }
      replace (firstn prh_wit_K (firstn j c)) with (firstn prh_wit_K (firstn prh_wit_K c))
        by (rewrite !firstn_firstn, !Nat.min_l by lia; reflexivity).
      apply H''. apply in_seq. lia.
  - intros F r w Hk Hr Hw. apply prh_wit_memU_In.
    assert (HF : In F [F_parse_string; F_parse_items]) by (destruct Hk as [-> | ->]; [left | right; left]; reflexivity).
    pose proof (H4a F HF) as H. rewrite forallb_forall in H. pose proof (H r Hr) as H'. rewrite forallb_forall in H'.
    exact (H' w Hw).
  - intros F r w Hk Hr.
    assert (HF : In F [F_parse_string; F_parse_items]) by (destruct Hk as [-> | ->]; [left | right; left]; reflexivity).
    pose proof (H4b F HF) as H. rewrite forallb_forall in H. pose proof (H r Hr) as H'.
    apply andb_prop in H' as [Hne Hm]. apply negb_true_iff, Z.eqb_neq in Hne.
    exact (prh_wit_inU_wild (as_universe B) (pc_free_ra0 (as_code B)) r w Hne (prh_wit_memU_In _ _ Hm)).
  - intros G F c r' rt r j HR HfpG HfpF Hr' Hr. apply prh_wit_memU_In.
    pose proof (H5 _ (prh_wit_reach_in CTX0 L HC G c HR)) as H. cbn [fst snd] in H. rewrite HfpG in H.
    cbn beta iota in H. rewrite forallb_forall in H.
    pose proof (H F (prh_wit_fns_all F)) as H'. cbn beta in H'. rewrite HfpF in H'. cbn beta iota in H'.
    revert H' Hr'. destruct (pi_call_rets G F) as [|r0 rs]; intros H' Hr'; [destruct Hr'|].
    cbn beta iota in H'. rewrite forallb_forall in H'. pose proof (H' rt (prh_wit_rts_all rt)) as H''. cbn beta in H''.
    rewrite forallb_forall in H''. pose proof (H'' r Hr) as H3'. cbn beta in H3'. rewrite forallb_forall in H3'.
    destruct (le_lt_dec j prh_wit_K) as [Hj | Hj].
    + replace (firstn j c) with (firstn j (firstn prh_wit_K c)) by (rewrite firstn_firstn, Nat.min_l by lia; reflexivity).
      apply H3'. apply in_seq. lia.
    + rewrite (prh_trace_firstn (prh_pc0 B rt) r (firstn j c) prh_wit_K); cycle 1.
      { unfold prh_wit_K, kUnwindMax. lia. }
      { exact (prh_wit_Forall_firstn _ j c (prh_wit_avoid_ok CTX0 G c rt HA HR)). }
      replace (firstn prh_wit_K (firstn j c)) with (firstn prh_wit_K (firstn prh_wit_K c))
        by (rewrite !firstn_firstn, !Nat.min_l by lia; reflexivity).
      apply H3'. apply in_seq. lia.
Qed.
End check.

(* ---- B': image B's tables, CfImg_B, the driver's context [[RA_LLVMF]] with RA_LLVMF = 0x815c8, the universe
   YCej.Tfib_universe (dd7d1838e568: 170 fixed traces, Tfib_wild = [0x53964; 0x87f34] (parse_items' free),
   [0x53964; 0x885e4] (parse_string's free), [0x53d60; 0x8529c] (tx_put's realloc)) ---- *)
Definition prh_wit_L_B : list (prh_fn * list Z) :=
  Eval vm_compute in @prh_wit_iter PRH_ImgB.prh_img_B 64 [(F_LLVMFuzzerTestOneInput, [0x815c8])].
Theorem prh_univ_closure_witness_B : forall B : asyms,
  as_code B = YF0l.Tfib_code -> as_universe B = YCej.Tfib_universe ->
  @prh_univ_closure PRH_ImgB.prh_img_B B CfImgB.CfImg_B [[0x815c8]].
Proof.
  intros B Hc Hu.
  apply (@prh_univ_closure_of_check PRH_ImgB.prh_img_B B CfImgB.CfImg_B [[0x815c8]] prh_wit_L_B).
  unfold prh_wit_check, prh_wit_c1, prh_wit_c2, prh_wit_c3, prh_wit_c4a, prh_wit_c4b, prh_wit_c5, prh_wit_avoid, prh_pc0.
  rewrite Hc, Hu. vm_compute. reflexivity.
Qed.
(* NEGATIVE CONTROL, B': the OLD clause 4, verbatim in its old spelling `In _ (as_universe B)` (membership in the
   FIXED part through the coercion u_fix: PRH_Base.prh_In_univ_is_fixed), at a run-word list holding ONE data word,
   is FALSE: the trace [0x53964; 0x87f34; 0x7fe1e7ff0017] of parse_items' free is not a fixed trace
   (the S1 owner's B_clause4_In_fails / B_neg_concrete, restated) *)
Theorem prh_old_clause4_fails_B : forall B : asyms,
  as_code B = YF0l.Tfib_code -> as_universe B = YCej.Tfib_universe ->
  ~ (forall F r w, prh_cursor F -> In r (@prh_free_sites PRH_ImgB.prh_img_B F) ->
       In w [0x7fe1e7ff0017] \/ In w (@pi_call_rets PRH_ImgB.prh_img_B F_pj_parse F_parse_value) ->
       In (prh_trace (pc_free_ra0 (as_code B)) r [w]) (as_universe B)).
Proof.
  intros B Hc Hu H.
  specialize (H F_parse_items 0x87f34 0x7fe1e7ff0017 (or_intror eq_refl) ltac:(vm_compute; left; reflexivity)
    (or_introl (or_introl eq_refl))).
  rewrite Hc, Hu in H. apply prh_wit_In_memU in H. revert H. vm_compute. intros E. discriminate E.
Qed.

(* ---- B': padded's trace from clause 5. padded has no frame pointer and calls malloc before it writes s0, so the
   run stores its site's trace over its caller's chain. From the closure and padded's own observed context x0 :: xs
   (prh_ctx, the premise tpadded_specX states), the trace over xs is a fixed trace of the universe: at x0 := raZ regs
   and xs := spine ch this is the premise the B' walker's interim pd_trace_prem ch (lib/B/Prog/Padded102B.v in the tree
   `preset-tree-at-2026-10-30T06-40-52Z.tsv (sha256 319a4c5d29fd; internal record)`) states, at the same image table prh_img_B and for EVERY CfImg ci, as that file's
   Section takes ci. ---- *)
Theorem c5_padded_trace_B {ci : CfImg} : forall (B : asyms) CTX0 (x0 : Z) (xs : list Z),
  @prh_univ_closure PRH_ImgB.prh_img_B B ci CTX0 ->
  @prh_ctx PRH_ImgB.prh_img_B CTX0 F_padded (x0 :: xs) ->
  forall r, In r (@pi_ret_sites PRH_ImgB.prh_img_B F_padded RT_malloc) ->
  In (prh_trace (pc_malloc_ra0 (as_code B)) r xs) (u_fix (as_universe B)).
Proof.
  intros B CTX0 x0 xs HU HC r Hr.
  exact (prh_univ_closure_nfp (PI := PRH_ImgB.prh_img_B) (ci := ci) B CTX0 F_padded x0 xs RT_malloc r
    HU HC ltac:(discriminate) ltac:(intros []; reflexivity) eq_refl Hr).
Qed.
(* at the real B' image and universe, through the witness *)
Corollary c5_padded_trace_TfibB : forall (B : asyms),
  as_code B = YF0l.Tfib_code -> as_universe B = YCej.Tfib_universe ->
  forall (x0 : Z) (xs : list Z), @prh_ctx PRH_ImgB.prh_img_B [[0x815c8]] F_padded (x0 :: xs) ->
  forall r, In r (@pi_ret_sites PRH_ImgB.prh_img_B F_padded RT_malloc) ->
  In (prh_trace (pc_malloc_ra0 (as_code B)) r xs) (u_fix (as_universe B)).
Proof.
  intros B Hc Hu x0 xs HC r Hr.
  exact (c5_padded_trace_B (ci := CfImgB.CfImg_B) B [[0x815c8]] x0 xs (prh_univ_closure_witness_B B Hc Hu) HC r Hr).
Qed.

(* ---- A': image A's tables, CfImg_A, the driver's context [[RA_LLVMF]] with RA_LLVMF = 0x814dc, the universe
   ACej.Tfib_universe (9c1da4e01665: 176 fixed traces, 78 of them clause 5's) ---- *)
Definition prh_wit_L_A : list (prh_fn * list Z) :=
  Eval vm_compute in @prh_wit_iter PRH_Img.prh_img_A 64 [(F_LLVMFuzzerTestOneInput, [0x814dc])].
Theorem prh_univ_closure_witness_A : forall B : asyms,
  as_code B = AF0l.Tfib_code -> as_universe B = ACej.Tfib_universe ->
  @prh_univ_closure PRH_Img.prh_img_A B CfImgA.CfImg_A [[0x814dc]].
Proof.
  intros B Hc Hu.
  apply (@prh_univ_closure_of_check PRH_Img.prh_img_A B CfImgA.CfImg_A [[0x814dc]] prh_wit_L_A).
  unfold prh_wit_check, prh_wit_c1, prh_wit_c2, prh_wit_c3, prh_wit_c4a, prh_wit_c4b, prh_wit_c5, prh_wit_avoid, prh_pc0.
  rewrite Hc, Hu. vm_compute. reflexivity.
Qed.
(* both A' cursor sites, at EVERY word: parse_items' free (0x87764) and parse_string's free (0x87e50) *)
Corollary prh_wit_A_cursor_sites : forall (B : asyms) (w : Z),
  as_code B = AF0l.Tfib_code -> as_universe B = ACej.Tfib_universe ->
  inU (as_universe B) (prh_trace 0x53878 0x87764 [w]) /\ inU (as_universe B) (prh_trace 0x53878 0x87e50 [w]).
Proof.
  intros B w Hc Hu. pose proof (prh_univ_closure_witness_A B Hc Hu) as H.
  assert (E : pc_free_ra0 (as_code B) = 0x53878) by (rewrite Hc; reflexivity).
  split.
  - rewrite <- E. apply (@prh_univ_closure_wild PRH_Img.prh_img_A B CfImgA.CfImg_A [[0x814dc]] F_parse_items);
      [exact H | right; reflexivity | vm_compute; tauto].
  - rewrite <- E. apply (@prh_univ_closure_wild PRH_Img.prh_img_A B CfImgA.CfImg_A [[0x814dc]] F_parse_string);
      [exact H | left; reflexivity | vm_compute; tauto].
Qed.
(* NEGATIVE CONTROL, A': a universe with the OLD A' wild part (ACej 0ee7e2bcf2f0: Tfib_wild = [[0x53c74; 0x84db0]]
   only) and fixed traces among today's ACej's 176 FAILS clause 4b: parse_items' free at the word 0 is neither a
   fixed trace nor under tx_put's prefix (the S1 owner's A_clause4_inU_fails_today, restated) *)
Theorem prh_old_A_universe_4b_fails : forall B : asyms,
  as_code B = AF0l.Tfib_code -> u_wild (as_universe B) = [[0x53c74; 0x84db0]] ->
  (forall t, In t (u_fix (as_universe B)) -> In t (u_fix ACej.Tfib_universe)) ->
  ~ (forall F r w, prh_cursor F -> In r (@prh_free_sites PRH_Img.prh_img_A F) ->
       inU (as_universe B) (prh_trace (pc_free_ra0 (as_code B)) r [w])).
Proof.
  intros B Hc Hw Hf H.
  specialize (H F_parse_items 0x87764 0 (or_intror eq_refl) ltac:(vm_compute; left; reflexivity)).
  destruct H as [_ [Hin | (p & sfx & Hp & Ht)]].
  - apply Hf in Hin. rewrite Hc in Hin. apply prh_wit_In_memU in Hin. revert Hin. vm_compute. intros E. discriminate E.
  - rewrite Hw in Hp. destruct Hp as [<- | []]. rewrite Hc in Ht. revert Ht. vm_compute. intros E. discriminate E.
Qed.

(* ---- THE ROOM CONJUNCT IS SATISFIABLE AT THE REAL INSTANCES (VERIFY rule 1 for the new premise the wild-budget
   rows add, PRH_Base's BUDGETED TWINS). NOT A REBUILD: the S1 owner proved it, in lib/A/WildRoomInstA.v and lib/AU/WildRoomInstB.v (ONE FILE PER IMAGE since the set's
    23:2xZ split, which killed the wrong-image hazard the driver-contract owner found; the old single lib/A/WildRoomInst.v is deleted) (taken by
   path from commit d8fc0356da28), at the start state YG00.init_state, whose depot is [] -
   that is the harness's allocator state at the driver's entry on both images (lib/A/AD1v.v:125,
   lib/AU/PresetD1preB.v:260). These two corollaries only restate it in the KIT'S OWN SPELLING, the shape the texts
   write: `wild_room (as_universe B) [] (prh_wk F) (st_depot S)` under the image's universe equation. The budgets
   are prh_wk's own values, every one of them at most YCbqGwild.K_LLVMF = 140, for which
   WildRoomInstA.wild_room_run_fits_A / _B prove 4 * 140 <= u_wmax (3920 on A', 3926 on B'). The CW form
   (`wild_room .. CW 0 ..`, the four reader rows) is WildRoomInstA.wild_room_cw_init_A / _B and
   wild_room_cw_stored_A / _B, for EVERY two words. ---- *)
Theorem prh_wild_room_witness_A : forall (B : asyms) (F : prh_fn),
  as_universe B = ACej.Tfib_universe -> (prh_wk F <= YCbqGwild.K_LLVMF)%nat ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F) (st_depot init_state).
Proof.
  intros B F Hu Hk. rewrite Hu.
  exact (YCbqGwild.wild_room_le _ _ _ _ _ Hk WildRoomInstA.wild_room_init_A).
Qed.
Theorem prh_wild_room_witness_B : forall (B : asyms) (F : prh_fn),
  as_universe B = YCej.Tfib_universe -> (prh_wk F <= YCbqGwild.K_LLVMF)%nat ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F) (st_depot init_state).
Proof.
  intros B F Hu Hk. rewrite Hu.
  exact (YCbqGwild.wild_room_le _ _ _ _ _ Hk WildRoomInstB.wild_room_init_B).
Qed.
(* every budget the kit's texts write is within K_LLVMF, so the two above apply to every row. ONE HOME: that fact is
   the S1 owner's WildBudget.prh_wk_le_K (lib/A/WildBudget.v 9134df4ca2c5, commit
   9a41ac98d791, beside lib_wild_budget and lib_wild_need = 76), cited here; the kit's own copy
   prh_wk_le_K_LLVMF was the same statement in a second file and is deleted (2026-10-30). *)

Print Assumptions prh_univ_closure_witness_B.
Print Assumptions prh_old_clause4_fails_B.
Print Assumptions c5_padded_trace_B.
Print Assumptions c5_padded_trace_TfibB.
Print Assumptions prh_univ_closure_witness_A.
Print Assumptions prh_wit_A_cursor_sites.
Print Assumptions prh_old_A_universe_4b_fails.
Print Assumptions prh_wild_room_witness_A.
Print Assumptions prh_wild_room_witness_B.
Print Assumptions WildBudget.prh_wk_le_K.
