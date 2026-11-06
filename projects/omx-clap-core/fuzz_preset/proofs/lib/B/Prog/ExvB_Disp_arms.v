(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value, segment C1 DISP (lane ExvDisp, cut CUT_C1 of ExvB_Stmt.v at exv_pc 0x11c = B 0x83648): the PIECE
   STATEMENTS of the segment and the pure grammar lemmas its arms use. Proves nothing about the program.
   - The two arms the dispatch hands on, each from the state the dispatch run leaves (EXB with only 144(s1) and
     152(s1) written since C1), each ending in EXV_POST through CUT_CX:
       EXVD_STR  at exv_pc 0x1d0 (B 0x836fc): the string arm (ex_string, v->type, strcmp, in->differs)
       EXVD_WORD at exv_pc 0x42c (B 0x83958): the word arms joined (a0 = in, a1 = the literal, a2 = its type, then
                 a3 = 152(s1) = v and ex_word); 't' reaches it through 0x83948-0x83954, 'f' through 0x836c4-0x836d0
                 and 0x83954, 'n' through 0x83790-0x837a0.
   - EX-LIT-SHADOW (PRH_FnEx.v's named gap): the literals' shadow is EXV_HYP's MARKED eh_litsh (over ExvB_Stmt.v's
     exvd_lit, both from this lane, 2026-10-29).
   - Pure lemmas: plain lib/Prog/ex_value_m.v's ex_V_ws / ex_V_str / ex_V_true / ex_V_false / ex_V_null and
     ex_string_rest restated over the prhex_V (ReaderRes.jr_strtod); no plain lemma is cited, no lib/Prog file
     Required. PjGrammar.v (lib/Spec) lemmas are cited.
   Numerals: 0x1d0, 0x42c (DERIVED: B 0x836fc / 0x83958 minus ex_value's entry 0x8352c, the internal file neutral_dis.py on the rebuilt
   image); 34 (WORD: the ASCII quote byte); 152 (LENGTH: the spill slot of v). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.
(* plain lia (YZ00's `lia` prunes hypotheses and fails on goals over record projections) *)
Ltac zl := Zify.zify; xlia zchecker.

(* ---- pure: the prhex_V at the first byte (plain ex_value_m.v restated) ---- *)
Lemma exvd_skip_nws : forall b y, PjGrammar.ws b = false -> PjGrammar.skip (b :: y) = b :: y.
Proof. intros b y H. cbn [PjGrammar.skip]. rewrite H. reflexivity. Qed.
Lemma exvd_skip_ws : forall b y, PjGrammar.ws b = true -> PjGrammar.skip (b :: y) = PjGrammar.skip y.
Proof. intros b y H. cbn [PjGrammar.skip]. rewrite H. reflexivity. Qed.

Lemma exvd_V_ws : forall d b y, PjGrammar.ws b = true -> prhex_V d (b :: y) = prhex_V d y.
Proof.
intros d b y H. unfold prhex_V.
rewrite <- (PjGrammar.jr_value_fuel ReaderRes.jr_strtod (S (2 * length (b :: y))) (Z.to_nat d) y [])
  by (cbn [length]; lia).
unfold PjGrammar.jr_value. cbn [PjGrammar.jrv]. rewrite (exvd_skip_ws b y H). reflexivity.
Qed.

Lemma exvd_V_skip : forall d x, prhex_V d x = prhex_V d (PjGrammar.skip x).
Proof.
intros d x. induction x as [|b y IH]; [reflexivity|].
destruct (PjGrammar.ws b) eqn:Hw.
- rewrite (exvd_V_ws d b y Hw), (exvd_skip_ws b y Hw). exact IH.
- rewrite (exvd_skip_nws b y Hw). reflexivity.
Qed.

Lemma exvd_V_nil : forall d, prhex_V d [] = None.
Proof. reflexivity. Qed.

Lemma exvd_V_str : forall d y,
  prhex_V d (34 :: y) =
    match fst (fst (PjGrammar.jr_string y [])) with
    | Some (s, r) => Some (PjTree.JStr s, r)
    | None => None
    end.
Proof.
intros d y.
transitivity (fst (fst (PjGrammar.jbind (PjGrammar.jr_string y)
  (fun '(s, r) => PjGrammar.jret (PjTree.JStr s, r)) []))).
{ unfold prhex_V, PjGrammar.jr_value. cbn [PjGrammar.jrv]. rewrite exvd_skip_nws by reflexivity. reflexivity. }
unfold PjGrammar.jbind. destruct (PjGrammar.jr_string y []) as [[[[s r]|] t] ok]; reflexivity.
Qed.

Lemma exvd_V_lit : forall d c w ty wl u y, exvd_lit c w ty wl u ->
  prhex_V d (c :: y) =
    if PjGrammar.prefixb wl (c :: y) then Some (u, skipn (length wl) (c :: y)) else None.
Proof.
intros d c w ty wl u y H.
destruct H as [(-> & _ & _ & -> & ->) | [(-> & _ & _ & -> & ->) | (-> & _ & _ & -> & ->)]].
- transitivity (fst (fst (PjGrammar.lit PjGrammar.w_true PjTree.JTrue (116 :: y) []))).
  { unfold prhex_V, PjGrammar.jr_value. cbn [PjGrammar.jrv]. rewrite exvd_skip_nws by reflexivity. reflexivity. }
  unfold PjGrammar.lit. destruct (PjGrammar.prefixb PjGrammar.w_true (116 :: y)); reflexivity.
- transitivity (fst (fst (PjGrammar.lit PjGrammar.w_false PjTree.JFalse (102 :: y) []))).
  { unfold prhex_V, PjGrammar.jr_value. cbn [PjGrammar.jrv]. rewrite exvd_skip_nws by reflexivity. reflexivity. }
  unfold PjGrammar.lit. destruct (PjGrammar.prefixb PjGrammar.w_false (102 :: y)); reflexivity.
- transitivity (fst (fst (PjGrammar.lit PjGrammar.w_null PjTree.JNull (110 :: y) []))).
  { unfold prhex_V, PjGrammar.jr_value. cbn [PjGrammar.jrv]. rewrite exvd_skip_nws by reflexivity. reflexivity. }
  unfold PjGrammar.lit. destruct (PjGrammar.prefixb PjGrammar.w_null (110 :: y)); reflexivity.
Qed.

(* prefixb is ex_word's hit (tex_word_specX): the word fits and the text starts with it *)
Lemma exvd_prefixb_iff : forall w l,
  PjGrammar.prefixb w l = true <-> (length w <= length l)%nat /\ firstn (length w) l = w.
Proof.
induction w as [|a w IH]; intros l; [cbn; split; [intros _; split; [lia | reflexivity] | reflexivity]|].
destruct l as [|b l]; cbn [PjGrammar.prefixb length firstn].
- split; [intros H; discriminate H | intros (H & _); lia].
- rewrite andb_true_iff, IH, Z.eqb_eq. split.
  + intros (-> & Hl & Hf). split; [lia | rewrite Hf; reflexivity].
  + intros (Hl & Hf). injection Hf as -> Hf. split; [reflexivity | split; [lia | exact Hf]].
Qed.

(* the text after the blanks is a suffix of the text, at exv_i1 *)
Lemma exvd_skip_suffix : forall l : list Z,
  PjGrammar.skip l = skipn (length l - length (PjGrammar.skip l)) l.
Proof.
induction l as [|b y IH]; [reflexivity|]. cbn [PjGrammar.skip].
destruct (PjGrammar.ws b) eqn:Hw.
- pose proof (PjGrammar.skip_len y) as L. cbn [length].
  replace (S (length y) - length (PjGrammar.skip y))%nat with (S (length y - length (PjGrammar.skip y)))%nat by lia.
  exact IH.
- cbn [length]. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma exvd_skipn_skipn : forall (x : list Z) a b, skipn a (skipn b x) = skipn (b + a) x.
Proof.
induction x as [|c x IH]; intros a b; [rewrite !skipn_nil; reflexivity|].
destruct b as [|b]; [reflexivity|]. cbn [skipn Nat.add]. apply IH.
Qed.
Lemma exvd_skip_X : forall E, e_i0 E <= exv_len E ->
  PjGrammar.skip (exv_X E) = skipn (Z.to_nat (exv_i1 E)) (e_x E).
Proof.
intros E Hi. unfold exv_i1, exv_X, exv_len in *.
rewrite exvd_skip_suffix at 1. rewrite exvd_skipn_skipn. f_equal.
remember (e_x E) as x eqn:Ex. remember (e_i0 E) as i0 eqn:Ei.
pose proof (PjGrammar.skip_len (skipn (Z.to_nat i0) x)) as L.
remember (PjGrammar.skip (skipn (Z.to_nat i0) x)) as s eqn:Es.
rewrite length_skipn in *. zl.
Qed.
Lemma exvd_i1_range : forall E, 0 <= exv_i1 E <= exv_len E.
Proof.
intros E. unfold exv_i1, exv_X, exv_len.
remember (e_x E) as x eqn:Ex. remember (e_i0 E) as i0 eqn:Ei.
pose proof (PjGrammar.skip_len (skipn (Z.to_nat i0) x)) as L.
remember (PjGrammar.skip (skipn (Z.to_nat i0) x)) as s eqn:Es.
rewrite length_skipn in L. zl.
Qed.
Lemma exvd_skipn_nth : forall (x : list Z) i, (i < length x)%nat -> skipn i x = nth i x 0 :: skipn (S i) x.
Proof.
induction x as [|b y IH]; intros i Hi; [cbn in Hi; lia|].
destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn [length] in Hi. lia.
Qed.
Lemma exvd_V_at : forall E, e_i0 E <= exv_len E ->
  exv_i1 E < exv_len E ->
  exv_V E = prhex_V (e_dep E) (nth (Z.to_nat (exv_i1 E)) (e_x E) 0 :: skipn (S (Z.to_nat (exv_i1 E))) (e_x E)).
Proof.
intros E Hi Hl. unfold exv_V. rewrite exvd_V_skip, (exvd_skip_X E Hi). f_equal.
apply exvd_skipn_nth. pose proof (exvd_i1_range E). unfold exv_len in *. zl.
Qed.
Lemma exvd_V_end : forall E, e_i0 E <= exv_len E -> exv_len E <= exv_i1 E -> exv_V E = None.
Proof.
intros E Hi Hl. unfold exv_V. rewrite exvd_V_skip, (exvd_skip_X E Hi). rewrite skipn_all2; [reflexivity|].
unfold exv_len in Hl. zl.
Qed.

(* ex_string's success: the rest (plain ex_value_m.v ex_string_rest, over PjGrammar's decode_stop) *)
Lemma exvd_string_rest : forall y s r, fst (fst (PjGrammar.jr_string y [])) = Some (s, r) ->
  exists c, PjGrammar.scan y = Some c /\ r = skipn (S c) y /\ (c < length y)%nat.
Proof.
intros y s r H. unfold PjGrammar.jr_string in H.
destruct (PjGrammar.scan y) as [c|] eqn:Es; [|discriminate H].
exists c. split; [reflexivity|]. pose proof (PjGrammar.scan_quote y c Es) as [Hc _].
split; [|exact Hc].
unfold PjGrammar.jbind, PjGrammar.jalloc, PjGrammar.take in H. cbn in H.
destruct (PjGrammar.decode y) as [[s' r']|] eqn:Ed; cbn in H; [|discriminate H].
injection H as -> ->. destruct (PjGrammar.decode_stop y s r Ed) as (c' & Hc' & Hr & _).
rewrite Es in Hc'. injection Hc' as <-. exact Hr.
Qed.

(* ---- the arm statements ---- *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

(* the string arm at B 0x836fc (the byte at in->p is the quote, 34): s5 = -1, 152(s1) = v *)
Definition EXVD_STR (n : nat) : Prop :=
  forall E lyc Sc Hpc Wc regs memc mdc k pos,
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  prhex_cur Wc memc (e_q E) (e_x0 E + exv_i1 E) (e_x0 E + exv_len E) (e_dep E) (e_scr E) (e_dl E) ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = 34 ->
  getr regs 21 = w64 (-1) -> exv_spill E Wc memc 152 (e_v E) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x1d0) regs memc mdc) (EXV_POST B ARx SK E).

(* the word arms joined at B 0x83958 (the byte at in->p is c, a literal's first byte): a0 = in, a1 = the literal,
   a2 = its type, 152(s1) = v *)
Definition EXVD_WORD (n : nat) : Prop :=
  forall E lyc Sc Hpc Wc regs memc mdc k pos (c w ty : Z) (wl : list Z) (u : PjTree.jv),
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  prhex_cur Wc memc (e_q E) (e_x0 E + exv_i1 E) (e_x0 E + exv_len E) (e_dep E) (e_scr E) (e_dl E) ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> exvd_lit c w ty wl u ->
  getr regs 10 = w64 (e_q E) -> getr regs 11 = w64 w -> getr regs 12 = w64 ty ->
  exv_spill E Wc memc 152 (e_v E) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x42c) regs memc mdc) (EXV_POST B ARx SK E).

(* ---- the shared kits the arms cite, all on the statement branch (ExValueB's base a90f298c25a): ExvLoop's
   lib/B/Prog/ExvB_Loop_kit.v (KIT_EXB_CALL, KIT_CALL_CHAIN, KIT_RODATA, KIT_WDEST) with their proofs exv_kit_call
   (ExvB_Loop_kitP.v) and exv_kit_chain / exv_kit_rodata / exv_kit_wdest (ExvB_Loop_kitQ.v), and ExvOpen's
   lib/B/Prog/ExvB_Open_sh.v (exv_sh_blk, exv_sh_lam) and lib/B/Prog/ExvB_Open_kt.v (exv_kt). ---- *)
End c.
