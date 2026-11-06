(* fuzz_preset image B' (asan-ubsan, #102), parse_value 0x8637c, segment D (the dispatch): the STRING
   ARM's packaging lemma. The first byte after the white space is the double quote (34); the machine stores v->type = 4
   before `jal parse_string`, v->str = the result after it, and returns (res <> 0) - 1. pvD_Qm_str turns the parts of
   parse_string's post it reads (the kit's tparse_string_specX, lib/A/PRH_FnReader.v:533, the post-implication form:
   each arm's result, Hp, blocks, ledger (with the #102 statics most / own, kept;
   the allocator's refusal moves g_peak by the refused request and g_ran_out when it is at most g_most) and cursor,
   its two room conjuncts over prhPs_evs at the arm's outcome list ([] / [false] / [true]), and the refusal arm's
   outcome exclusion (no refusal on a run that consumes the grant-all event), at the memory after v->str is stored)
   and the reader state at the dispatch (pv_reader0, its room keep from entry) into pv_Qm, the memory part of
   parse_value's post (lib/B/Prog/PvB_Defs.v pv_Qm). The room post is PvB_Room.v rp_call: the value's events ARE the
   callee's (pvs_evs: jr_value's string arm makes jr_string's trace, and PRH_FnReader.prhPs_evs_model at the instance
   fact cf_head = PresetReqAt.HEAD); the outcome is PvB_Defs.pv_outc_call over parse_string's grant-all events; the
   ledger move is the batch kit's rd_ledger_move (pvs_move_one, pvs_oks_*, pvs_rpeak1); the free-order tie is a leaf's
   (PvB_Frees: the string's one block, the model's lf of the value's trace). pvs_counts gives the callee's two
   live-count premises from pv_pre's (the granted run of parse_value at the quote IS jr_string's granted run).
   State-free: no machine code is walked here. The model side is PvB_Model.pvm_unfold / pvm_string / pvm_skip_rest /
   pvm_hpeak; the two pure bounds are PjGrammar.G1_4 (the decoded string is no longer than the scanned span) and
   PjGrammar.G10_1 (the held bytes of a successful read against the bytes it consumed); the string's length bound
   (PRH_Reader.v pj_cstrR's `length s + 1 < 2 ^ 32`) is the request bound of the dispatch's rd_room (the granted
   request Q + 1 + cf_head < cf_malloc_max, and cf_malloc_max + 15 <= 2 ^ 30 by YG08cf.v).
   Numerals: 34 the double quote (WORD), 4 the node tag of a string (PjTree.tag), 56 / 4 / 8 / 16 / 24 / 32 / 40 / 48
   the node layout (LENGTH), 2 ^ 32 / 2 ^ 64 the field ranges. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC88.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjRoundTrip PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_Frees.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun PresetRoom
  PresetLiveBounds PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive YGcfSecsStep.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- pure: the string arm of the model, by the allocation outcome ---- *)

Lemma pvs_model : forall sm d x y ok, PjGrammar.skip x = 34 :: y ->
  PjGrammar.jr_value sm d x ok =
  match PjGrammar.scan y with
  | None => (None, [], ok)
  | Some q =>
      let (b, ok1) := PjGrammar.take ok in
      if b then
        match PjGrammar.decode y with
        | Some (s, r) => (Some (PjTree.JStr s, r), [PjGrammar.EAlloc (S q)], ok1)
        | None => (None, [PjGrammar.EAlloc (S q); PjGrammar.EFree (S q)], ok1)
        end
      else (None, [PjGrammar.EFail (S q)], ok1)
  end.
Proof.
intros sm d x y ok Hs. rewrite pvm_unfold, Hs. cbv beta iota.
assert (E1 : (34 =? 123) = false) by reflexivity.
assert (E2 : (34 =? 91) = false) by reflexivity.
assert (E3 : (34 =? 34) = true) by reflexivity.
rewrite E1, E2, E3. cbv beta iota.
unfold PjGrammar.jbind. cbv beta. rewrite pvm_string.
destruct (PjGrammar.scan y) as [q|]; [|reflexivity].
destruct ok as [|b ok]; [|destruct b]; destruct (PjGrammar.decode y) as [[s r]|]; reflexivity.
Qed.

Lemma pvs_model_none : forall sm d x y ok, PjGrammar.skip x = 34 :: y -> PjGrammar.scan y = None ->
  PjGrammar.jr_value sm d x ok = (None, [], ok).
Proof. intros sm d x y ok Hs Hq. rewrite (pvs_model sm d x y ok Hs), Hq. reflexivity. Qed.

Lemma pvs_model_fail : forall sm d x y Q, PjGrammar.skip x = 34 :: y -> PjGrammar.scan y = Some Q ->
  PjGrammar.jr_value sm d x [false] = (None, [PjGrammar.EFail (S Q)], []).
Proof. intros sm d x y Q Hs Hq. rewrite (pvs_model sm d x y [false] Hs), Hq. reflexivity. Qed.

Lemma pvs_model_bad : forall sm d x y Q, PjGrammar.skip x = 34 :: y -> PjGrammar.scan y = Some Q ->
  PjGrammar.decode y = None ->
  PjGrammar.jr_value sm d x [true] = (None, [PjGrammar.EAlloc (S Q); PjGrammar.EFree (S Q)], []).
Proof. intros sm d x y Q Hs Hq Hd. rewrite (pvs_model sm d x y [true] Hs), Hq, Hd. reflexivity. Qed.

Lemma pvs_model_ok : forall sm d x y Q s r, PjGrammar.skip x = 34 :: y -> PjGrammar.scan y = Some Q ->
  PjGrammar.decode y = Some (s, r) ->
  PjGrammar.jr_value sm d x [true] = (Some (PjTree.JStr s, r), [PjGrammar.EAlloc (S Q)], []).
Proof. intros sm d x y Q s r Hs Hq Hd. rewrite (pvs_model sm d x y [true] Hs), Hq, Hd. reflexivity. Qed.

(* the string arm's trace is jr_string's (jret adds no event) *)
Lemma pvs_trace : forall sm d x y ok, PjGrammar.skip x = 34 :: y ->
  snd (fst (PjGrammar.jr_value sm d x ok)) = snd (fst (PjGrammar.jr_string y ok)).
Proof.
intros sm d x y ok Hs. rewrite (pvs_model sm d x y ok Hs), pvm_string.
destruct (PjGrammar.scan y) as [q|]; [|reflexivity].
destruct ok as [|b ok]; [|destruct b]; destruct (PjGrammar.decode y) as [[s r]|]; reflexivity.
Qed.

(* ---- memory: zero bytes, the cursor after a refusal ---- *)

Lemma pvs_zero_byte : forall segs m v x, pj_zeroR segs m v -> v <= x < v + 56 ->
  mbyte segs m x = Some (Z_to_bv 8 0).
Proof.
intros segs m v x Hz Hx.
destruct (Hz (Z.to_nat (x - v)) ltac:(rewrite repeat_length; lia)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)). rewrite nth_repeat in Hv.
replace (v + Z.of_nat (Z.to_nat (x - v)) + Z.of_nat 0) with x in Hv by lia.
exact Hv.
Qed.

Lemma pvs_val0 : forall segs m a, (forall x, a <= x < a + 8 -> mbyte segs m x = Some (Z_to_bv 8 0)) ->
  val_mem segs m a 8 0.
Proof.
intros segs m a H k Hk. rewrite H by lia.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try reflexivity. lia.
Qed.

Lemma pvs_after : forall segs m q text len p d tb,
  pj_in_okR segs m q text len p d tb -> pj_in_afterR segs m q text len d 33.
Proof.
intros segs m q text len p d tb (V1 & V2 & V3 & Hrw & _ & _ & _ & Hp & _ & _ & _ & Hd).
exists p, d. split; [lia|]. split; [lia|]. split; [exact V1|]. split; [exact V2|]. split; [exact V3|exact Hrw].
Qed.

(* ---- the ledger move of a read that makes no / exactly one allocator call (the batch kit's rd_ledger_move: g_most, the
   grant-all trace gt, the refused peak) ---- *)

Lemma pvs_move_none : forall Lam peak cnt fail ran most gt,
  0 <= cnt < 2 ^ 64 -> 0 <= Ledger.lsum Lam <= peak ->
  rd_ledger_move Lam peak cnt fail ran most [] gt [] [] Lam peak cnt fail ran.
Proof.
intros Lam peak cnt fail ran most gt Hc Hl.
unfold rd_ledger_move, prh_oks, fail_afterR. cbn [PjGrammar.calls hpeakR].
split; [split; [intros i Hi; lia | split; [left; reflexivity | intros i Hi; lia]]|].
split; [rewrite Z.add_0_r, Z.mod_small by lia; reflexivity|].
split; [split; [intros H; lia | intros _; reflexivity]|].
split; [apply Permutation_refl|].
split; [apply Permutation_refl|].
split; [reflexivity|].
unfold prh_refused_peak. cbn [List.seq map fold_right]. lia.
Qed.

Lemma pvs_move_one : forall Lam peak cnt fail ran most (b : bool) gt tr D Lam' peak' cnt' fail' ran',
  PjGrammar.calls tr = 1%nat ->
  prh_oks [b] cnt fail 1 (prh_ev_reqs tr) most ran ran' ->
  cnt' = (cnt + 1) mod 2 ^ 64 ->
  (cnt = fail -> fail' = SIZE_MAXZ) -> (cnt <> fail -> fail' = fail) ->
  Permutation Lam' (D ++ Lam) -> Permutation (map snd D) (map Z.of_nat (lszR tr)) ->
  Z.of_nat (length D) = nliveR tr ->
  peak' = Z.max (Z.max peak (Ledger.lsum Lam + hpeakR tr))
    (prh_refused_peak [b] cnt fail 1 (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds gt))) ->
  rd_ledger_move Lam peak cnt fail ran most [b] gt tr D Lam' peak' cnt' fail' ran'.
Proof.
intros Lam peak cnt fail ran most b gt tr D Lam' peak' cnt' fail' ran' Hcl Hok Hc Hf1 Hf2 HP1 HP2 HN HPk.
unfold rd_ledger_move, fail_afterR. rewrite Hcl.
split; [exact Hok|]. split; [exact Hc|].
split; [split; [intros H; apply Hf1; lia | intros H; apply Hf2; lia]|].
split; [exact HP1|]. split; [exact HP2|]. split; [exact HN|exact HPk].
Qed.

(* the harness's fail counter refuses the call: no refusal by the allocator, g_ran_out kept *)
Lemma pvs_oks_cf : forall cnt fail ns most ran, cnt = fail -> prh_oks [false] cnt fail 1 ns most ran ran.
Proof.
intros cnt fail ns most ran E. unfold prh_oks.
split; [intros i Hi _; destruct i as [|i]; [reflexivity|lia]|].
split; [left; reflexivity|].
intros i Hi Hr _. destruct i as [|i]; [|lia]. exfalso. unfold prh_refused in Hr. cbn [nth Z.of_nat] in Hr.
rewrite Z.add_0_r, (proj2 (Z.eqb_eq cnt fail) E) in Hr. discriminate Hr.
Qed.

(* the allocator refuses a request n: g_ran_out set exactly when n is at most g_most (the batch kit's re-keyed prh_oks) *)
Lemma pvs_oks_refused : forall cnt fail n most ran, cnt <> fail ->
  prh_oks [false] cnt fail 1 [n] most ran (if n <=? most then 1 else ran).
Proof.
intros cnt fail n most ran E. unfold prh_oks.
assert (Hr0 : prh_refused [false] cnt fail 0 = true).
{ unfold prh_refused. cbn [nth Z.of_nat]. rewrite Z.add_0_r, (proj2 (Z.eqb_neq cnt fail) E). reflexivity. }
split; [intros i Hi Hf; destruct i as [|i]; [cbn [Z.of_nat] in Hf; lia|lia]|].
split.
- destruct (Z.leb_spec n most) as [Hle|Hgt];
    [right; split; [reflexivity|exists 0%nat; split; [lia|split; [exact Hr0|cbn [nth]; exact Hle]]]
    |left; reflexivity].
- intros i Hi _ Hm. destruct i as [|i]; [|lia]. cbn [nth] in Hm. destruct (Z.leb_spec n most); [reflexivity|lia].
Qed.

(* the call is granted: g_ran_out kept *)
Lemma pvs_oks_granted : forall cnt fail ns most ran, cnt <> fail -> prh_oks [true] cnt fail 1 ns most ran ran.
Proof.
intros cnt fail ns most ran E. unfold prh_oks.
split; [intros i Hi Hf; destruct i as [|i]; [cbn [Z.of_nat] in Hf; lia|lia]|].
split; [left; reflexivity|].
intros i Hi Hr _. destruct i as [|i]; [|lia]. unfold prh_refused in Hr. cbn [nth negb andb] in Hr. discriminate Hr.
Qed.

(* the refused peak of one call *)
Lemma pvs_rpeak1 : forall (b : bool) cnt fail h,
  prh_refused_peak [b] cnt fail 1 [h] = Z.max (if negb b && negb (cnt =? fail) then Z.min SIZE_MAXZ h else 0) 0.
Proof.
intros b cnt fail h. unfold prh_refused_peak, prh_refused. cbn [List.seq map fold_right nth Z.of_nat].
rewrite Z.add_0_r. reflexivity.
Qed.

(* the grant-all run at the quote, when the string closes: one call, its held bytes the scanned span + 1 *)
Lemma pvs_gt_some : forall sm d x y Q, PjGrammar.skip x = 34 :: y -> PjGrammar.scan y = Some Q ->
  PjGrammar.calls (snd (fst (PjGrammar.jr_value sm d x []))) = 1%nat /\
  prh_ev_helds (snd (fst (PjGrammar.jr_value sm d x []))) = [Z.of_nat (S Q)].
Proof.
intros sm d x y Q Hs Hq. rewrite (pvs_model sm d x y [] Hs), Hq. cbn [PjGrammar.take].
destruct (PjGrammar.decode y) as [[s r]|]; split; reflexivity.
Qed.

(* ---- the allocator's live bytes are the sum of its blocks' sizes (YCbq.blocks_bytes_bsum's statement) ---- *)
Lemma pvs_bb : forall (B0 : asyms) ly S, blocks_bytes S = bsum (ablocks B0 ly S).
Proof.
intros B0 ly S. unfold blocks_bytes, ablocks, blocks, bsum.
induction (st_chunks S) as [|c l IH]; cbn; [reflexivity|].
destruct (is_alloc c); cbn; rewrite IH; reflexivity.
Qed.

(* split a right-nested conjunction into its conjuncts, so a cut's conjunct is found by its statement, not its place *)
Local Ltac pvs_split H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "Hc" in destruct H as [H1 H]; pvs_split H
  | _ => idtac
  end.

#[local] Instance PIB : PrhImg := prh_img_B.
Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* the value's model events on the string arm are parse_string's, under the same outcome list (prhPs_evs_model at
   the instance fact cf_head = PresetReqAt.HEAD) *)
Lemma pvs_evs : forall sm d x y ok res tr okr, cf_head = PresetReqAt.HEAD -> PjGrammar.skip x = 34 :: y ->
  PjGrammar.jr_value sm d x ok = (res, tr, okr) -> PresetReqAt.rd_hevs tr = prhPs_evs y ok.
Proof.
intros sm d x y ok res tr okr HHD Hs Hj.
rewrite (prhPs_evs_model y ok HHD), <- (pvs_trace sm d x y ok Hs), Hj. reflexivity.
Qed.

(* parse_string's two live-count premises at a call state Sc the room keep from entry reaches: pv_pre's over
   parse_value's granted run, which at the quote IS parse_string's granted run prhPs_evs y [] *)
Lemma pvs_counts : forall en y Sc, cf_head = PresetReqAt.HEAD -> pv_pre B ARx en ->
  PjGrammar.skip (pe_rest en) = 34 :: y -> rp_keep (pe_S en) Sc ->
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) (prhPs_evs y []))
    <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
    (prhPs_evs y [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros en y Sc HHD Hpre Hsk HK.
assert (E : PresetReqAt.rd_hevs (pe_gt en) = prhPs_evs y []).
{ unfold pe_gt, prhPv_gtrace. rewrite (pvs_trace prh_jr_strtod (pe_d en) (pe_rest en) y [] Hsk).
  symmetry. exact (prhPs_evs_model y [] HHD). }
unfold pv_pre in Hpre. destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS & H24 & _ & _).
rewrite E in HS, H24.
split; rewrite (rp_keep_pkR (pe_S en) Sc _ _ HK); assumption.
Qed.

(* the granted outcome list [true] makes the same events as the grant-all list [] (one allocation, granted) *)
Lemma pvs_evs_true : forall y, cf_head = PresetReqAt.HEAD -> prhPs_evs y [true] = prhPs_evs y [].
Proof.
intros y HHD. rewrite !(prhPs_evs_model y _ HHD), !pvm_string.
destruct (PjGrammar.scan y) as [q|]; reflexivity.
Qed.

(* THE STRING ARM: parse_string's post at the call (lyc, Sc, pe_Hp en, Wc, memc) with result res, the two stores
   around the call and the node bytes the call kept, give pv_Qm with code (res <> 0) - 1. *)
Lemma pvD_Qm_str : forall (en : PvEnt) (pos p1 res code : Z) (y : list Z) (lyc : alayout) (Sc : astate)
    (Wc : world SEGS) (memc : word -> option byte) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world SEGS)
    (mem' : word -> option byte),
  cf_head = PresetReqAt.HEAD ->
  pv_pre B ARx en ->
  p1 = pe_text en + pe_len en - Z.of_nat (length (PjGrammar.skip (pe_rest en))) ->
  PjGrammar.skip (pe_rest en) = 34 :: y ->
  pv_reader0 B en pos p1 lyc Sc Wc memc ->
  frames S' = frames Sc ->
  (* the parts of parse_string's post the packaging reads, at the final memory (W', mem'), result res; its hull use
     over the all-granted events from the call state; each arm's room conjuncts are the text's (lib/A/PRH_FnReader.v
     tparse_string_specX) over prhPs_evs at the arm's outcome list, from the call state Sc; the allocator's refusal
     arm (cnt <> fail, res = 0) carries the text's outcome exclusion and its ledger (g_peak by the refused request,
     g_ran_out when it is at most g_most) *)
  (room_live_cf S' /\ PresetHullBudget.hull_used Sc S' (prhPs_evs (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) []) /\
   match PjGrammar.scan (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) with
   | None => res = 0 /\ Hp' = pe_Hp en /\ ablocks B ly' S' = ablocks B lyc Sc /\
       prh_ledger B ly' S' Hp' W' mem' (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en)
         (pe_own en) /\
       pj_in_okR SEGS (mrestrict (w_H W') mem') (pe_q en) (pe_text en) (pe_len en) p1 (Z.of_nat (pe_d en)) (pe_tb en) /\
       Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
         (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
           (prhPs_evs (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) [])) /\
       rp_pos (prhPs_evs (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) []) Sc S'
   | Some Q =>
       (pe_cnt en = pe_fail en /\ res = 0 /\ Hp' = pe_Hp en /\ ablocks B ly' S' = ablocks B lyc Sc /\
        prh_ledger B ly' S' Hp' W' mem' (pe_Lam en) (pe_peak en) (pe_cnt en + 1) SIZE_MAXZ (pe_ran en) (pe_most en)
          (pe_own en) /\
        pj_in_okR SEGS (mrestrict (w_H W') mem') (pe_q en) (pe_text en) (pe_len en) p1 (Z.of_nat (pe_d en)) (pe_tb en) /\
        Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
          (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
            (prhPs_evs (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) [false])) /\
        rp_pos (prhPs_evs (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) [false]) Sc S')
       \/
       (pe_cnt en <> pe_fail en /\ res = 0 /\ Hp' = pe_Hp en /\ ablocks B ly' S' = ablocks B lyc Sc /\
        (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
           (H0 : list Z) (hist : list YG00.chunk),
           PresetRoomPos.iface_room_pos sm x os i H0 hist Sc ->
           PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) []) ->
           PRH_Base.prh_cons_from sm x os i (length (prhPs_evs (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) [])) ->
           False) /\
        prh_ledger B ly' S' Hp' W' mem' (pe_Lam en)
          (Z.max (pe_peak en) (Z.min SIZE_MAXZ (Ledger.lsum (pe_Lam en) + (Z.of_nat Q + 1))))
          ((pe_cnt en + 1) mod 2 ^ 64) (pe_fail en) (if Z.of_nat Q + 1 <=? pe_most en then 1 else pe_ran en)
          (pe_most en) (pe_own en) /\
        pj_in_okR SEGS (mrestrict (w_H W') mem') (pe_q en) (pe_text en) (pe_len en) p1 (Z.of_nat (pe_d en)) (pe_tb en) /\
        Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
          (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
            (prhPs_evs (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) [false])) /\
        rp_pos (prhPs_evs (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) [false]) Sc S')
       \/
       (pe_cnt en <> pe_fail en /\ res = 0 /\ PjGrammar.decode (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) = None /\
        Hp' = pe_Hp en /\ ablocks B ly' S' = ablocks B lyc Sc /\
        prh_ledger B ly' S' Hp' W' mem' (pe_Lam en)
          (Z.max (pe_peak en) (Ledger.lsum (pe_Lam en) + (Z.of_nat Q + 1))) (pe_cnt en + 1) (pe_fail en) (pe_ran en)
          (pe_most en) (pe_own en) /\
        pj_in_okR SEGS (mrestrict (w_H W') mem') (pe_q en) (pe_text en) (pe_len en) p1 (Z.of_nat (pe_d en)) (pe_tb en) /\
        Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
          (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
            (prhPs_evs (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) [true])) /\
        rp_pos (prhPs_evs (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) [true]) Sc S')
       \/
       (pe_cnt en <> pe_fail en /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\
        exists s r, PjGrammar.decode (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) = Some (s, r) /\
          Hp' = (res - cf_head) :: pe_Hp en /\
          ablocks B ly' S' = ablocks B lyc Sc ++ [(res - cf_head, Z.of_nat Q + 1 + cf_head)] /\
          pj_cbytesR SEGS (mrestrict (w_H W') mem') res s /\
          prh_ledger B ly' S' Hp' W' mem' ((res, Z.of_nat Q + 1) :: pe_Lam en)
            (Z.max (pe_peak en) (Ledger.lsum (pe_Lam en) + (Z.of_nat Q + 1))) (pe_cnt en + 1) (pe_fail en) (pe_ran en)
            (pe_most en) (pe_own en) /\
          pj_in_okR SEGS (mrestrict (w_H W') mem') (pe_q en) (pe_text en) (pe_len en)
            (p1 + Z.of_nat Q + 2) (Z.of_nat (pe_d en)) (pe_tb en) /\
          Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
            (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
              (prhPs_evs (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) [true])) /\
          rp_pos (prhPs_evs (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) [true]) Sc S')
   end) ->
  (* ADDED (not in the brief's statement; the generic ARx gives none of it): the success arm's new block is a 64-bit
     address, is not among the allocator's blocks at the call, and is apart from the node. The walk discharges it from
     ARx at the post (fpostW's journal) with AR_laws_x (alx_blocks: p + req_size n <= alloc_ceiling, pairwise
     zdisjoint with req_size n >= 1; alx_sep for the node's frame / block) and prhReader_at of the node. *)
  (forall Q, PjGrammar.scan (rest_atR (pe_tb en) (pe_text en) (p1 + 1)) = Some Q -> res <> 0 ->
     res < 2 ^ 64 /\ ~ In (res - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B lyc Sc) /\
     (forall x, res <= x < res + Z.of_nat Q + 1 -> ~ (pe_v en <= x < pe_v en + 56))) ->
  (* what the machine stored around the call, and what it kept *)
  code = (if res =? 0 then -1 else 0) ->
  val_mem SEGS (mrestrict (w_H W') mem') (pe_v en) 4 4 ->
  val_mem SEGS (mrestrict (w_H W') mem') (pe_v en + 16) 8 res ->
  (forall a, pe_v en + 4 <= a < pe_v en + 16 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H Wc) memc a) ->
  (forall a, pe_v en + 24 <= a < pe_v en + 56 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H Wc) memc a) ->
  pj_rwR SEGS (mrestrict (w_H W') mem') (pe_v en) ->
  pv_Qm B en (fun S2 => Permutation (frames S2) ((0, pos) :: frames (pe_S en))) code ly' S' Hp' W' mem'.
Proof.
intros en pos p1 res code y lyc Sc Wc memc ly' S' Hp' W' mem' HHD Hpre Hp1 Hsk Hr0 Hfr HPS Hnew Hcode Hty Hstr Hk1
  Hk2 Hrw.
assert (E64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
assert (E32 : 2 ^ 32 = 4294967296) by reflexivity.
pose proof cf_head_nonneg as Hch.
unfold pv_pre in Hpre.
assert (Hrd : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
    (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
    (pe_q en) (pe_text en)
    (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (clear - Hpre; pvs_split Hpre; assumption).
clear Hpre.
unfold rd_pre in Hrd.
assert (Hin0 : pj_in_okR SEGS (mrestrict (w_H (pe_W en)) (pe_mem en)) (pe_q en) (pe_text en) (pe_len en) (pe_p en)
    (Z.of_nat (pe_d en)) (pe_tb en)) by (clear - Hrd; pvs_split Hrd; assumption).
assert (Hnode : prhPv_node B (pe_STK en) (pe_e en) (pe_ly en) (pe_S en) (pe_W en) (pe_regs en) (pe_mem en)
    (pe_Lam en) (pe_v en)) by (clear - Hrd; pvs_split Hrd; assumption).
assert (Hled0 : prh_ledger B (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_Lam en) (pe_peak en)
    (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en)) by (clear - Hrd; pvs_split Hrd; assumption).
assert (Hcnt : pe_cnt en + 2 * Z.of_nat (length (rest_atR (pe_tb en) (pe_text en) (pe_p en))) + 2 < 2 ^ 64 - 1)
  by (clear - Hrd; pvs_split Hrd; assumption).
clear Hrd.
destruct Hnode as (_ & _ & _ & Hz0 & _).
destruct Hin0 as (_ & _ & _ & _ & _ & _ & _ & Hpr & Hlen & _).
destruct Hled0 as ((_ & _ & _ & _ & _ & _ & _ & Hlp & _ & Hc & _) & _).
unfold pv_reader0 in Hr0.
assert (Hfr0 : frames Sc = (0, pos) :: frames (pe_S en)) by (clear - Hr0; pvs_split Hr0; assumption).
assert (Hab0 : ablocks B lyc Sc = ablocks B (pe_ly en) (pe_S en)) by (clear - Hr0; pvs_split Hr0; assumption).
assert (Hbb0 : blocks_bytes Sc = blocks_bytes (pe_S en)) by (clear - Hr0; pvs_split Hr0; assumption).
assert (Hroom0 : rd_room Sc (pe_gt en)) by (clear - Hr0; pvs_split Hr0; assumption).
assert (Hkv0 : forall a, pe_v en <= a < pe_v en + 56 ->
    aview SEGS (w_H Wc) memc a = aview SEGS (w_H (pe_W en)) (pe_mem en) a) by (clear - Hr0; pvs_split Hr0; assumption).
(* the room keep from entry to the call state, and the hull meters kept (pv_reader0's last two conjuncts) *)
assert (HK0 : rp_keep (pe_S en) Sc) by (clear - Hr0; pvs_split Hr0; assumption).
assert (HSEC0 : YGcfSecsStep.secs_same (pe_S en) Sc) by (clear - Hr0; pvs_split Hr0; assumption).
clear Hr0.
(* the cursor after the white space and after the quote *)
pose proof (pvm_skip_rest (pe_tb en) (pe_text en) (pe_len en) (pe_p en) Hlen Hpr) as [Hrest1 Hp1b].
change (rest_atR (pe_tb en) (pe_text en) (pe_p en)) with (pe_rest en) in Hrest1, Hp1b.
rewrite <- Hp1 in Hrest1, Hp1b. rewrite Hsk in Hrest1.
assert (Hrest2 : rest_atR (pe_tb en) (pe_text en) (p1 + 1) = y).
{ pose proof Hrest1 as H. unfold rest_atR in H |- *.
  replace (Z.to_nat (p1 + 1 - pe_text en)) with (1 + Z.to_nat (p1 - pe_text en))%nat by lia.
  rewrite <- skipn_skipn, H. reflexivity. }
assert (Hlsk : length (PjGrammar.skip (pe_rest en)) = S (length y)) by (rewrite Hsk; reflexivity).
pose proof (PjGrammar.skip_len (pe_rest en)) as Hsl.
change (rest_atR (pe_tb en) (pe_text en) (pe_p en)) with (pe_rest en) in Hcnt.
assert (Hc1 : pe_cnt en + 1 < 2 ^ 64) by lia.
assert (Ec1 : pe_cnt en + 1 = (pe_cnt en + 1) mod 2 ^ 64) by (symmetry; apply Z.mod_small; lia).
(* the frames clause *)
assert (Hfrm : Permutation (frames S') ((0, pos) :: frames (pe_S en))) by (rewrite Hfr, Hfr0; apply Permutation_refl).
(* the value's grant-all events are parse_string's (prhPs_evs_model at cf_head = HEAD) *)
assert (Egt0 : PresetReqAt.rd_hevs (pe_gt en) = prhPs_evs y []).
{ unfold pe_gt, prhPv_gtrace. rewrite (pvs_trace prh_jr_strtod (pe_d en) (pe_rest en) y [] Hsk).
  symmetry. exact (prhPs_evs_model y [] HHD). }
(* the value's frees are the leaf's (PvB_Frees.pvf_frees_leaf) *)
assert (Efr : forall ok, prhPv_frees (pe_d en) (pe_rest en) ok =
  PresetReqAt.lf (snd (fst (PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) ok))))
  by (intros ok; exact (PvB_Frees.pvf_frees_leaf _ _ ok 34 y Hsk ltac:(discriminate) ltac:(discriminate))).
(* the node: the bytes the call kept are the entry's zeros *)
assert (Hzb : forall a, pe_v en + 4 <= a < pe_v en + 16 \/ pe_v en + 24 <= a < pe_v en + 56 ->
          mbyte SEGS (mrestrict (w_H W') mem') a = Some (Z_to_bv 8 0)).
{ intros a Ha.
  assert (E1 : aview SEGS (w_H W') mem' a = aview SEGS (w_H (pe_W en)) (pe_mem en) a).
  { destruct Ha as [Ha|Ha]; [rewrite (Hk1 a Ha)|rewrite (Hk2 a Ha)]; apply Hkv0; lia. }
  rewrite (YC88.mbyte_of_aview_eq SEGS _ _ _ _ _ _ E1).
  apply (pvs_zero_byte SEGS _ (pe_v en)); [exact Hz0|lia]. }
assert (Hv8 : val_mem SEGS (mrestrict (w_H W') mem') (pe_v en + 8) 8 0)
  by (apply pvs_val0; intros x Hx; apply Hzb; lia).
assert (Hv24 : val_mem SEGS (mrestrict (w_H W') mem') (pe_v en + 24) 8 0)
  by (apply pvs_val0; intros x Hx; apply Hzb; lia).
assert (Hv32 : val_mem SEGS (mrestrict (w_H W') mem') (pe_v en + 32) 8 0)
  by (apply pvs_val0; intros x Hx; apply Hzb; lia).
assert (Hv40 : val_mem SEGS (mrestrict (w_H W') mem') (pe_v en + 40) 8 0)
  by (apply pvs_val0; intros x Hx; apply Hzb; lia).
assert (Hv48 : val_mem SEGS (mrestrict (w_H W') mem') (pe_v en + 48) 8 0)
  by (apply pvs_val0; intros x Hx; apply Hzb; lia).
assert (Hhdr : forall str, 0 <= str < 2 ^ 64 -> val_mem SEGS (mrestrict (w_H W') mem') (pe_v en + 16) 8 str ->
          pj_hdrR SEGS (mrestrict (w_H W') mem') (pe_v en) 4 0 str 0 0 0 0).
{ intros str Hb Hs. split; [exact Hrw|].
  split; [split; [lia|exact Hty]|].
  split; [split; [lia|exact Hv8]|].
  split; [split; [exact Hb|exact Hs]|].
  split; [split; [lia|exact Hv24]|].
  split; [split; [lia|exact Hv32]|].
  split; [split; [lia|exact Hv40]|].
  split; [lia|exact Hv48]. }
(* the refused node: type 4, every other field 0, no block *)
assert (HZ : res = 0 -> pj_hdrR SEGS (mrestrict (w_H W') mem') (pe_v en) 4 0 0 0 0 0 0)
  by (intros E0; apply Hhdr; [lia|rewrite <- E0; exact Hstr]).
assert (Hfd : forall lblk, res = 0 ->
          pj_fdR SEGS (mrestrict (w_H W') mem') lblk (PjGrammar.MAXD - pe_d en) (pe_v en) []).
{ intros lblk E0.
  assert (Hsh : forall (Pi : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop), Pi false 0 0 0 [] ->
            pj_fshapeR SEGS (mrestrict (w_H W') mem') lblk Pi (pe_v en) []).
  { intros Pi HPi. split; [constructor|]. split; [intros b x []|].
    exists 4, 0, 0, 0, 0, 0, 0, false, [], [], [], [].
    split; [exact (HZ E0)|].
    split; [left; split; reflexivity|].
    split; [left; split; [reflexivity|split; reflexivity]|].
    split; [left; split; [reflexivity|split; reflexivity]|].
    split; [apply Permutation_refl|exact HPi]. }
  destruct (PjGrammar.MAXD - pe_d en)%nat as [|n]; cbn [pj_fdR]; apply Hsh; cbn; [split|]; reflexivity. }
(* the refused node's free order: none (an empty trace's lf), at every depth *)
assert (HTN : forall ok Lam', res = 0 -> PresetReqAt.lf (snd (fst (PjGrammar.jr_value prh_jr_strtod (pe_d en)
    (pe_rest en) ok))) = [] -> pv_ftie en (PjGrammar.MAXD - pe_d en) Lam' W' mem' [] ok).
{ intros ok Lam' E0 Elf _ n _. exists []. split; [exact (PvB_Frees.pvf_zero_foR SEGS _ _ n (pe_v en) 4 (HZ E0))|].
  rewrite Efr, Elf. reflexivity. }
(* the arms *)
destruct HPS as (Hroom & Hhull & HPS).
rewrite Hrest2 in HPS, Hnew, Hhull.
(* the hull use from the entry: the meters kept to the call state, then parse_string's use over the value's events *)
assert (HHULL : PresetHullBudget.hull_used (pe_S en) S' (PresetReqAt.rd_hevs (pe_gt en))).
{ rewrite Egt0. exact (PresetHullBudget.hull_used_app (pe_S en) Sc S' [] _
    (PresetHullBudget.hull_used_same (pe_S en) Sc [] HSEC0) Hhull). }
revert HPS. destruct (PjGrammar.scan y) as [Q|] eqn:Esc; intros HPS.
2:{ (* no closing quote: no call to the allocator *)
  destruct HPS as (Er & _ & Eab & Hled' & Hin' & HL & HP).
  pose proof (pvs_model_none prh_jr_strtod (pe_d en) (pe_rest en) y [] Hsk Esc) as Hj.
  unfold pv_Qm.
  exists [], None, [], [], [], (pe_Lam en), (pe_peak en), (pe_cnt en), (pe_fail en), (pe_ran en).
  split; [exact Hj|]. split; [exact Hled'|]. split; [exact Hroom|]. split; [exact HHULL|].
  split; [exact (rp_call _ _ (pe_S en) Sc S' S' (pvs_evs _ _ _ _ _ _ _ _ HHD Hsk Hj) HK0 HL HP (rp_keep_refl S'))|].
  split.
  { apply (pv_outc_call en None [] (pe_ran en) Sc S' S' (prhPs_evs y []) Egt0 HK0); [|exact (rp_keep_refl S')].
    intros sm x os i H0 hist P R _ _. split; [reflexivity|]. split; [rewrite Hj; reflexivity|].
    exact (HP sm x os i H0 hist P R). }
  (* the injected reading: no call, nothing refused *)
  split; [intros sm x os i H0 hist _ _ _ _ j Hj' _; cbn in Hj'; lia|].
  split; [apply pvs_move_none; lia|].
  split; [intros a k []|].
  split; [rewrite Eab, Hab0; apply Permutation_refl|].
  split; [exact Hfrm|].
  split; [pose proof (pvm_hpeak prh_jr_strtod (pe_d en) (pe_rest en) []) as Hh; rewrite Hj in Hh; exact Hh|].
  split; [rewrite <- Hbb0, (pvs_bb B lyc Sc), (pvs_bb B ly' S'), Eab; unfold prh_held;
    cbn [PjGrammar.held PjGrammar.calls]; lia|].
  split; [reflexivity|].
  split; [rewrite Hcode, Er; reflexivity|].
  split; [exact (HTN [] _ Er ltac:(rewrite Hj; reflexivity))|].
  split; [exact (pvs_after _ _ _ _ _ _ _ _ Hin')|].
  exact (Hfd _ Er). }
pose proof (PjGrammar.scan_quote y Q Esc) as [HQ _].
destruct (pvs_gt_some prh_jr_strtod (pe_d en) (pe_rest en) y Q Hsk Esc) as [Hcalls Hhelds].
change (snd (fst (PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) []))) with (pe_gt en) in Hcalls, Hhelds.
assert (Hrp : forall b, prh_refused_peak [b] (pe_cnt en) (pe_fail en) 1
    (map (Z.add (Ledger.lsum (pe_Lam en))) (prh_ev_helds (pe_gt en))) =
  Z.max (if negb b && negb (pe_cnt en =? pe_fail en)
         then Z.min SIZE_MAXZ (Ledger.lsum (pe_Lam en) + Z.of_nat (S Q)) else 0) 0)
  by (intros b; rewrite Hhelds; cbn [map]; apply pvs_rpeak1).
destruct HPS as [HA|[HA|[HA|HA]]].
- (* the harness's chosen failure *)
  destruct HA as (Ecf & Er & _ & Eab & Hled' & Hin' & HL & HP).
  pose proof (pvs_model_fail prh_jr_strtod (pe_d en) (pe_rest en) y Q Hsk Esc) as Hj.
  unfold pv_Qm.
  exists [false], None, [PjGrammar.EFail (S Q)], [], [], (pe_Lam en), (pe_peak en), (pe_cnt en + 1), SIZE_MAXZ,
    (pe_ran en).
  split; [exact Hj|]. split; [exact Hled'|]. split; [exact Hroom|]. split; [exact HHULL|].
  split; [exact (rp_call _ _ (pe_S en) Sc S' S' (pvs_evs _ _ _ _ _ _ _ _ HHD Hsk Hj) HK0 HL HP (rp_keep_refl S'))|].
  split.
  { apply (pv_outc_call en None [PjGrammar.EFail (S Q)] (pe_ran en) Sc S' S' (prhPs_evs y []) Egt0 HK0);
      [|exact (rp_keep_refl S')].
    intros sm x os i H0 hist _ _ _ F. exfalso. rewrite Hcalls in F. cbn [Z.of_nat] in F. lia. }
  (* the injected reading: the one failed outcome is the chosen one (cnt = fail) *)
  split.
  { intros sm x os i H0 hist _ _ _ _ j Hj' _. cbn [PjGrammar.calls PjGrammar.is_call] in Hj'.
    assert (Ej : j = 0%nat) by (clear - Hj'; lia). subst j. cbn [Z.of_nat]. lia. }
  split.
  { apply pvs_move_one.
    - reflexivity.
    - exact (pvs_oks_cf _ _ _ _ _ Ecf).
    - exact Ec1.
    - intros _; reflexivity.
    - intros H; exfalso; exact (H Ecf).
    - apply Permutation_refl.
    - apply Permutation_refl.
    - reflexivity.
    - rewrite (Hrp false), (proj2 (Z.eqb_eq _ _) Ecf). cbn [negb andb hpeakR PjGrammar.held_ev]. lia. }
  split; [intros a k []|].
  split; [rewrite Eab, Hab0; apply Permutation_refl|].
  split; [exact Hfrm|].
  split; [pose proof (pvm_hpeak prh_jr_strtod (pe_d en) (pe_rest en) [false]) as Hh; rewrite Hj in Hh; exact Hh|].
  split; [rewrite <- Hbb0, (pvs_bb B lyc Sc), (pvs_bb B ly' S'), Eab; unfold prh_held;
    cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]; lia|].
  split; [reflexivity|].
  split; [rewrite Hcode, Er; reflexivity|].
  split; [exact (HTN [false] _ Er ltac:(rewrite Hj; reflexivity))|].
  split; [exact (pvs_after _ _ _ _ _ _ _ _ Hin')|].
  exact (Hfd _ Er).
- (* the allocator's refusal *)
  destruct HA as (Ecf & Er & _ & Eab & HNO & Hled' & Hin' & HL & HP).
  pose proof (pvs_model_fail prh_jr_strtod (pe_d en) (pe_rest en) y Q Hsk Esc) as Hj.
  unfold pv_Qm.
  exists [false], None, [PjGrammar.EFail (S Q)], [], [], (pe_Lam en),
    (Z.max (pe_peak en) (Z.min SIZE_MAXZ (Ledger.lsum (pe_Lam en) + (Z.of_nat Q + 1)))),
    ((pe_cnt en + 1) mod 2 ^ 64), (pe_fail en), (if Z.of_nat Q + 1 <=? pe_most en then 1 else pe_ran en).
  split; [exact Hj|]. split; [exact Hled'|]. split; [exact Hroom|]. split; [exact HHULL|].
  split; [exact (rp_call _ _ (pe_S en) Sc S' S' (pvs_evs _ _ _ _ _ _ _ _ HHD Hsk Hj) HK0 HL HP (rp_keep_refl S'))|].
  split.
  { apply (pv_outc_call en None [PjGrammar.EFail (S Q)] _ Sc S' S' (prhPs_evs y []) Egt0 HK0);
      [|exact (rp_keep_refl S')].
    intros sm x os i H0 hist P R C _. exfalso. exact (HNO sm x os i H0 hist P R C). }
  (* the injected reading: the value's window is its one call, so the chosen failure is at cnt, which this arm is not *)
  split; [intros sm x os i H0 hist _ _ _ F; exfalso; rewrite Hcalls in F; cbn [Z.of_nat] in F; lia|].
  split.
  { apply pvs_move_one.
    - reflexivity.
    - replace (Z.of_nat Q + 1) with (Z.of_nat (S Q)) by lia.
      change (prh_ev_reqs [PjGrammar.EFail (S Q)]) with [Z.of_nat (S Q)].
      exact (pvs_oks_refused _ _ _ _ _ Ecf).
    - reflexivity.
    - intros H; exfalso; exact (Ecf H).
    - intros _; reflexivity.
    - apply Permutation_refl.
    - apply Permutation_refl.
    - reflexivity.
    - rewrite (Hrp false), (proj2 (Z.eqb_neq _ _) Ecf). cbn [negb andb hpeakR PjGrammar.held_ev].
      unfold SIZE_MAXZ. lia. }
  split; [intros a k []|].
  split; [rewrite Eab, Hab0; apply Permutation_refl|].
  split; [exact Hfrm|].
  split; [pose proof (pvm_hpeak prh_jr_strtod (pe_d en) (pe_rest en) [false]) as Hh; rewrite Hj in Hh; exact Hh|].
  split; [rewrite <- Hbb0, (pvs_bb B lyc Sc), (pvs_bb B ly' S'), Eab; unfold prh_held;
    cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]; lia|].
  split; [reflexivity|].
  split; [rewrite Hcode, Er; reflexivity|].
  split; [exact (HTN [false] _ Er ltac:(rewrite Hj; reflexivity))|].
  split; [exact (pvs_after _ _ _ _ _ _ _ _ Hin')|].
  exact (Hfd _ Er).
- (* a bad escape: the block taken and given back *)
  destruct HA as (Ecf & Er & Ed & _ & Eab & Hled' & Hin' & HL & HP).
  pose proof (pvs_model_bad prh_jr_strtod (pe_d en) (pe_rest en) y Q Hsk Esc Ed) as Hj.
  assert (Hj0 : fst (PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) []) =
    (None, [PjGrammar.EAlloc (S Q); PjGrammar.EFree (S Q)])).
  { rewrite (pvs_model prh_jr_strtod (pe_d en) (pe_rest en) y [] Hsk), Esc, Ed. reflexivity. }
  unfold pv_Qm.
  exists [true], None, [PjGrammar.EAlloc (S Q); PjGrammar.EFree (S Q)], [], [], (pe_Lam en),
    (Z.max (pe_peak en) (Ledger.lsum (pe_Lam en) + (Z.of_nat Q + 1))), (pe_cnt en + 1), (pe_fail en), (pe_ran en).
  split; [exact Hj|]. split; [exact Hled'|]. split; [exact Hroom|]. split; [exact HHULL|].
  split; [exact (rp_call _ _ (pe_S en) Sc S' S' (pvs_evs _ _ _ _ _ _ _ _ HHD Hsk Hj) HK0 HL HP (rp_keep_refl S'))|].
  split.
  { apply (pv_outc_call en None _ (pe_ran en) Sc S' S' (prhPs_evs y []) Egt0 HK0); [|exact (rp_keep_refl S')].
    intros sm x os i H0 hist P R _ _. split; [reflexivity|]. split; [exact Hj0|].
    rewrite <- (pvs_evs_true y HHD) in R |- *. exact (HP sm x os i H0 hist P R). }
  (* the injected reading: the one call granted (ok = [true]) *)
  split; [intros sm x os i H0 hist _ _ _ _ j _ Hn; exfalso; destruct j as [|[|j]]; cbn in Hn; discriminate Hn|].
  split.
  { apply pvs_move_one.
    - reflexivity.
    - exact (pvs_oks_granted _ _ _ _ _ Ecf).
    - exact Ec1.
    - intros H; exfalso; exact (Ecf H).
    - intros _; reflexivity.
    - apply Permutation_refl.
    - cbn [lszR fold_left lsz_evR rm1nR]. rewrite Nat.eqb_refl. apply Permutation_refl.
    - reflexivity.
    - rewrite (Hrp true). cbn [negb andb hpeakR PjGrammar.held_ev]. lia. }
  split; [intros a k []|].
  split; [rewrite Eab, Hab0; apply Permutation_refl|].
  split; [exact Hfrm|].
  split; [pose proof (pvm_hpeak prh_jr_strtod (pe_d en) (pe_rest en) [true]) as Hh; rewrite Hj in Hh; exact Hh|].
  split; [rewrite <- Hbb0, (pvs_bb B lyc Sc), (pvs_bb B ly' S'), Eab; unfold prh_held;
    cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]; lia|].
  split; [cbn [Ledger.lsum PjGrammar.held PjGrammar.held_ev]; lia|].
  split; [rewrite Hcode, Er; reflexivity|].
  split; [exact (HTN [true] _ Er ltac:(rewrite Hj; reflexivity))|].
  split; [exact (pvs_after _ _ _ _ _ _ _ _ Hin')|].
  exact (Hfd _ Er).
- (* the string, in a new harness block of Q + 1 bytes *)
  destruct HA as (Ecf & Hres & _ & s & r & Ed & _ & Eab & Hcb & Hled' & Hin' & HL & HP).
  assert (Hb1 : bsum [(res - cf_head, Z.of_nat Q + 1 + cf_head)] = Z.of_nat Q + 1 + cf_head)
    by (unfold bsum; cbn [fold_right snd]; lia).
  destruct (Hnew Q eq_refl ltac:(lia)) as (Hr64 & Hfresh & Hap).
  destruct (PjGrammar.G1_4 y s r Ed) as (q' & Esc' & Er & Hls & _).
  rewrite Esc in Esc'. injection Esc' as <-.
  assert (Hlr : length r = (length y - S Q)%nat) by (rewrite Er, length_skipn; reflexivity).
  assert (Hpos : pe_text en + pe_len en - Z.of_nat (length r) = p1 + Z.of_nat Q + 2)
    by (rewrite Hp1, Hlsk, Hlr; lia).
  pose proof (pvs_model_ok prh_jr_strtod (pe_d en) (pe_rest en) y Q s r Hsk Esc Ed) as Hj.
  assert (Hj0 : fst (PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) []) =
    (Some (PjTree.JStr s, r), [PjGrammar.EAlloc (S Q)])).
  { rewrite (pvs_model prh_jr_strtod (pe_d en) (pe_rest en) y [] Hsk), Esc, Ed. reflexivity. }
  (* the node: a string leaf holding the new block *)
  assert (HNODE : pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin ((res, Z.of_nat Q + 1) :: pe_Lam en)) (pe_v en)
    (PjTree.JStr s) [(res, Z.of_nat Q + 1)]).
  { cbn [pj_nodeR PjTree.tag].
    split; [first [apply NoDup_singleton | constructor; [intros Hin; inversion Hin | constructor]]|].
    split.
    { intros b x [<-|[]] Hx. unfold pj_holdsR in Hx. cbn [fst snd] in Hx. apply (Hap x). lia. }
    exists 0, res, 0, 0, 0, 0.
    split; [apply Hhdr; [lia|exact Hstr]|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exists (Z.of_nat Q + 1). split; [|reflexivity].
    split; [left; reflexivity|]. split; [lia|]. split; [|exact Hcb].
    (* the string's length bound: length s <= Q (G1_4), Q's request is below cf_malloc_max (the dispatch's rd_room) *)
    pose proof Hroom0 as (_ & Hmaxreq & _). unfold pe_gt, prhPv_gtrace in Hmaxreq.
    rewrite (pvs_model prh_jr_strtod (pe_d en) (pe_rest en) y [] Hsk), Esc in Hmaxreq.
    unfold prh_maxreq in Hmaxreq. pose proof YG08cf.cf_malloc_max_bound as Hmb.
    destruct (PjGrammar.decode y) as [[s0 r0]|];
      cbn [PjGrammar.take fst snd map fold_right PjGrammar.esize] in Hmaxreq; clear - Hmaxreq Hmb Hch Hls; lia. }
  unfold pv_Qm.
  exists [true], (Some (PjTree.JStr s, r)), [PjGrammar.EAlloc (S Q)], [], [(res, Z.of_nat Q + 1)],
    ((res, Z.of_nat Q + 1) :: pe_Lam en), (Z.max (pe_peak en) (Ledger.lsum (pe_Lam en) + (Z.of_nat Q + 1))),
    (pe_cnt en + 1), (pe_fail en), (pe_ran en).
  split; [exact Hj|]. split; [exact Hled'|]. split; [exact Hroom|]. split; [exact HHULL|].
  split; [exact (rp_call _ _ (pe_S en) Sc S' S' (pvs_evs _ _ _ _ _ _ _ _ HHD Hsk Hj) HK0 HL HP (rp_keep_refl S'))|].
  split.
  { apply (pv_outc_call en _ _ (pe_ran en) Sc S' S' (prhPs_evs y []) Egt0 HK0); [|exact (rp_keep_refl S')].
    intros sm x os i H0 hist P R _ _. split; [reflexivity|]. split; [exact Hj0|].
    rewrite <- (pvs_evs_true y HHD) in R |- *. exact (HP sm x os i H0 hist P R). }
  (* the injected reading: the one call granted (ok = [true]) *)
  split; [intros sm x os i H0 hist _ _ _ _ j _ Hn; exfalso; destruct j as [|[|j]]; cbn in Hn; discriminate Hn|].
  split.
  { apply pvs_move_one.
    - reflexivity.
    - exact (pvs_oks_granted _ _ _ _ _ Ecf).
    - exact Ec1.
    - intros H; exfalso; exact (Ecf H).
    - intros _; reflexivity.
    - apply Permutation_refl.
    - cbn [map snd lszR fold_left lsz_evR]. rewrite Nat2Z.inj_succ. apply Permutation_refl.
    - reflexivity.
    - rewrite (Hrp true). cbn [negb andb hpeakR PjGrammar.held_ev]. lia. }
  split.
  { intros a k [Eak|[]]. injection Eak as <- <-. rewrite <- Hab0. exact Hfresh. }
  split.
  { rewrite Eab, Hab0. unfold prhReader_ab. cbn [map fst snd]. apply Permutation_app_comm. }
  split; [exact Hfrm|].
  split; [pose proof (pvm_hpeak prh_jr_strtod (pe_d en) (pe_rest en) [true]) as Hh; rewrite Hj in Hh; exact Hh|].
  split; [rewrite <- Hbb0, (pvs_bb B lyc Sc), (pvs_bb B ly' S'), Eab, bsum_app, Hb1; unfold prh_held;
    cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]; lia|].
  split; [cbn [Ledger.lsum PjGrammar.held PjGrammar.held_ev]; lia|].
  split; [rewrite Hcode, (proj2 (Z.eqb_neq res 0)) by lia; reflexivity|].
  (* the free order: the string's one block, the model's lf of the granted trace *)
  split.
  { intros _ n _. exists [(res, Z.of_nat Q + 1)]. split.
    - exact (PvB_Frees.pvf_node_leaf_foR SEGS _ _ n (pe_v en) (PjTree.JStr s) _ HNODE
        ltac:(intros ? E; discriminate E) ltac:(intros ? E; discriminate E)).
    - rewrite Efr, Hj. cbn [fst snd map]. rewrite PvB_Frees.pvf_lf_one, HHD. f_equal. lia. }
  split; [rewrite Hpos; exact Hin'|].
  split; [exact HNODE|].
  split; [exact (PvB_Frees.pvf_ncap_leaf SEGS _ (pe_v en) (PjTree.JStr s)
    ltac:(intros ? E; discriminate E) ltac:(intros ? E; discriminate E))|].
  pose proof (PjGrammar.G10_1 prh_jr_strtod (pe_d en) (pe_rest en) [true] (PjTree.JStr s) r
    [PjGrammar.EAlloc (S Q)] [] Hj) as Hg.
  cbn [PjGrammar.held PjGrammar.held_ev Ledger.lsum] in Hg |- *. lia.
Qed.

End c.
