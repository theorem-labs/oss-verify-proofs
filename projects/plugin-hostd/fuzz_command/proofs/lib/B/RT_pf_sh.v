(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/RT_pf_sh.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* ASan's printf_common at fuzz_manifest.asan (RT_pf_Tbl.v PF_PRINTF_COMMON) in the shared contracts' form:
   sh_apcommon_realizesUz (FMsnprintfSx.v) for fm's format family FF_fm, from the relocated Bz walk (RT_pf_bz.v
   pcom_call, lib/B/Bz/A/I_pcxlist.v pcom_genx_spec).
   - the grammar: a format pf_parse reads as literals, %s and %.*s (pf_fm_piece) is one printf_common's own grammar
     accepts (I_pcxgram.v pcomx_ok), with the arguments mapped piece by piece (pa_of) and the coverage list pc_cin
     (a %.*s string is not range-checked by the walk; a %s string is);
   - the memory: the walk runs on the cleaned store (FMbz_clean.v), so every read-only byte must read as the image:
     the non-owned ones from the contract's consts_view over PCM_CR, the owned ones from AR (FMInst.fmi_rom_viewO);
   - the post: the walk changes only [sp - PCOM_DEPTH, sp), inside the contract's window [sp - K, sp). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A Require Import I_pcxgram.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0d YG0f YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFPf RtPFShared.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import FMpfStep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---- the grammar ---- *)
(* fm's conversions (FMsnprintfShared.v pf_fm_piece) *)
Definition pf_fm_pc (p : pf_piece) : Prop := match p with PLit _ | Ps | Pps => True | _ => False end.

(* a pf argument as the Bz grammar's argument kind *)
Definition pa_of (a : pf_arg) : parg :=
  match a with AInt v => PA_i v | AU64 u => PA_u u | APtr s => PA_s s end.

(* the coverage the Bz walk is given per argument: a %.*s string is covered by its precision (not range-checked),
   a %s string is not covered (range-checked), the %.*s precision itself is not a string *)
Fixpoint pc_cin (ps : list pf_piece) : list (option Z) :=
  match ps with
  | [] => []
  | Ps :: ps' => None :: pc_cin ps'
  | Pps :: ps' => None :: Some 0 :: pc_cin ps'
  | _ :: ps' => pc_cin ps'
  end.

Lemma pcx_fm : forall fuel fmt ps args T,
  (length fmt < fuel)%nat -> pf_parse fmt = Some ps -> Forall pf_fm_pc ps -> pf_text ps args = Some T ->
  (exists n, pcx_walk fuel (fmt ++ [0]) (map pa_of args) = Some n) /\
  pcx_covs fuel (fmt ++ [0]) (map pa_of args) (pc_cin ps) = pc_cin ps.
Proof.
  induction fuel as [|fuel IH]; intros fmt ps args T Hf Hp HK HT; [lia|].
  destruct fmt as [|b r].
  - cbn in Hp. injection Hp as <-. cbn in HT. destruct args as [|a args]; [|discriminate HT].
    split; [exists 0%nat; reflexivity | reflexivity].
  - cbn [length] in Hf. cbn [pf_parse] in Hp.
    destruct (Z.eqb_spec b 37) as [->|N37].
    + destruct r as [|c r1]; [discriminate Hp|].
      destruct (Z.eqb_spec c 100) as [->|N100].
      { destruct (pf_parse r1); [|discriminate Hp]. injection Hp as <-. inversion HK as [|? ? Hk _]. destruct Hk. }
      destruct (Z.eqb_spec c 99) as [->|N99].
      { destruct (pf_parse r1); [|discriminate Hp]. injection Hp as <-. inversion HK as [|? ? Hk _]. destruct Hk. }
      destruct (Z.eqb_spec c 115) as [->|N115].
      { (* %s *)
        destruct (pf_parse r1) as [ps1|] eqn:Hp1; [|discriminate Hp]. injection Hp as <-.
        inversion HK as [|? ? _ HK1]; subst.
        cbn [pf_text] in HT. destruct args as [|[v|u|s] args1]; try discriminate HT.
        destruct (pf_text ps1 args1) as [T1|] eqn:HT1; [|discriminate HT].
        destruct (IH r1 ps1 args1 T1 ltac:(cbn [length] in Hf; lia) Hp1 HK1 HT1) as ((n1 & W1) & C1).
        split.
        - exists (1 + n1)%nat. cbn [app map pcx_walk]. cbn. rewrite W1. reflexivity.
        - cbn [app map pc_cin]. cbn. rewrite C1. reflexivity. }
      destruct (Z.eqb_spec c 48) as [->|N48].
      { destruct r1 as [|c2 [|c3 r3]]; try discriminate Hp.
        destruct ((c2 =? 52) && (c3 =? 120)); [destruct (pf_parse r3); [|discriminate Hp]; injection Hp as <-;
          inversion HK as [|? ? Hk _]; destruct Hk|].
        destruct ((c2 =? 50) && (c3 =? 120)); [destruct (pf_parse r3); [|discriminate Hp]; injection Hp as <-;
          inversion HK as [|? ? Hk _]; destruct Hk | discriminate Hp]. }
      destruct (Z.eqb_spec c 108) as [->|N108].
      { destruct r1 as [|c2 [|c3 r3]]; try discriminate Hp.
        destruct ((c2 =? 108) && (c3 =? 117)); [destruct (pf_parse r3); [|discriminate Hp]; injection Hp as <-;
          inversion HK as [|? ? Hk _]; destruct Hk | discriminate Hp]. }
      destruct (Z.eqb_spec c 46) as [->|N46]; [|discriminate Hp].
      (* %.*s *)
      destruct r1 as [|c2 [|c3 r3]]; try discriminate Hp.
      destruct (Z.eqb_spec c2 42) as [->|N42]; [|cbn in Hp; discriminate Hp].
      destruct (Z.eqb_spec c3 115) as [->|N115']; [|cbn in Hp; discriminate Hp].
      cbn in Hp. destruct (pf_parse r3) as [ps3|] eqn:Hp3; [|discriminate Hp]. injection Hp as <-.
      inversion HK as [|? ? _ HK3]; subst.
      cbn [pf_text] in HT. destruct args as [|[k|u|s0] [|[v|u'|s] args3]]; try discriminate HT.
      destruct ((0 <=? k) && (k <=? Z.of_nat (length s))); [|discriminate HT].
      destruct (pf_text ps3 args3) as [T3|] eqn:HT3; [|discriminate HT].
      destruct (IH r3 ps3 args3 T3 ltac:(cbn [length] in Hf; lia) Hp3 HK3 HT3) as ((n3 & W3) & C3).
      split.
      * exists (1 + 1 + n3)%nat. cbn [app map]. cbn. rewrite W3. reflexivity.
      * cbn [app map pc_cin]. cbn. rewrite C3. reflexivity.
    + (* a literal byte *)
      destruct ((0 <? b) && (b <? 256)) eqn:Hb; [|discriminate Hp].
      destruct (pf_parse r) as [ps1|] eqn:Hp1; [|discriminate Hp]. injection Hp as <-.
      inversion HK as [|? ? _ HK1]; subst.
      cbn [pf_text] in HT. destruct (pf_text ps1 args) as [T1|] eqn:HT1; [|discriminate HT].
      destruct (IH r ps1 args T1 ltac:(lia) Hp1 HK1 HT1) as ((n1 & W1) & C1).
      apply andb_prop in Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2.
      assert (E0 : (b =? 0) = false) by (apply Z.eqb_neq; lia).
      assert (E37 : (b =? 37) = false) by (apply Z.eqb_neq; exact N37).
      assert (Er : (0 <? b) && (b <? 256) = true) by (apply andb_true_intro; split; apply Z.ltb_lt; lia).
      split.
      * exists n1. cbn [app pcx_walk]. rewrite E0, E37, Er. exact W1.
      * cbn [app pcx_covs pc_cin]. rewrite E0, E37, Er. exact C1.
Qed.

Lemma pcomx_fm : forall fmt ps args T,
  pf_parse fmt = Some ps -> Forall pf_fm_pc ps -> pf_text ps args = Some T ->
  pcomx_ok (fmt ++ [0]) (map pa_of args) = true /\
  pcx_covs (length (fmt ++ [0])) (fmt ++ [0]) (map pa_of args) (pc_cin ps) = pc_cin ps.
Proof.
  intros fmt ps args T Hp HK HT.
  destruct (pcx_fm (length (fmt ++ [0])) fmt ps args T ltac:(rewrite length_app; cbn; lia) Hp HK HT) as ((n & W) & C).
  split; [unfold pcomx_ok; rewrite W; reflexivity | exact C].
Qed.

(* ==== the per-piece pcom arm (fm's non-%s printf widening) ==== *)
(* the coverage entries of the arguments one piece consumes: none for a literal, the string's for %.*s after its
   precision's, None for each other argument *)
Definition pc_cin1 (p : pf_piece) : list (option Z) :=
  match p with PLit _ => [] | Pps => [None; Some 0] | _ => [None] end.
Fixpoint pc_cinK (ps : list pf_piece) : list (option Z) :=
  match ps with [] => [] | p :: ps' => pc_cin1 p ++ pc_cinK ps' end.

(* the pcx arm: one pcx_walk step reads p's code with the arguments p consumes (FMpfStep.v pf_step), whatever follows *)
Definition pcom_pcx_arm (p : pf_piece) : Prop :=
  forall (fuel : nat) (rest : list Z) (args : list pf_arg) (c : list Z) (a' : list pf_arg) (C : list (option Z)),
    pf_code_ok p -> pf_step p args = Some (c, a') ->
    (forall n, pcx_walk fuel rest (map pa_of a') = Some n ->
       exists n', pcx_walk (S fuel) (pf_code p ++ rest) (map pa_of args) = Some n') /\
    pcx_covs (S fuel) (pf_code p ++ rest) (map pa_of args) (pc_cin1 p ++ C) =
      pc_cin1 p ++ pcx_covs fuel rest (map pa_of a') C.

(* ---- fm's pieces have their arms ---- *)
Lemma pcom_pcx_arm_lit : forall b, pcom_pcx_arm (PLit b).
Proof.
  intros b fuel rest args c a' C Hok H. cbn [pf_step] in H. injection H as <- <-. cbn [pf_code_ok] in Hok.
  assert (E0 : (b =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (E37 : (b =? 37) = false) by (apply Z.eqb_neq; lia).
  assert (Er : (0 <? b) && (b <? 256) = true) by (apply andb_true_intro; split; apply Z.ltb_lt; lia).
  split.
  - intros n W. exists n. cbn [pf_code app pcx_walk]. rewrite E0, E37, Er. exact W.
  - cbn [pf_code pc_cin1 app pcx_covs]. rewrite E0, E37, Er. reflexivity.
Qed.
Lemma pcom_pcx_arm_ps : pcom_pcx_arm Ps.
Proof.
  intros fuel rest args c a' C _ H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
  injection H as <- <-. split.
  - intros n W. exists (1 + n)%nat. cbn [pf_code app map pcx_walk]. cbn. rewrite W. reflexivity.
  - cbn [pf_code pc_cin1 app map]. cbn. reflexivity.
Qed.
Lemma pcom_pcx_arm_pps : pcom_pcx_arm Pps.
Proof.
  intros fuel rest args c a' C _ H. destruct args as [|[k|u|s0] [|[v|u'|s] a'']]; cbn [pf_step] in H; try discriminate H.
  destruct ((0 <=? k) && (k <=? Z.of_nat (length s))); [|discriminate H]. injection H as <- <-. split.
  - intros n W. exists (1 + 1 + n)%nat. cbn [pf_code app map pcx_walk]. cbn. rewrite W. reflexivity.
  - cbn [pf_code pc_cin1 app map]. cbn. reflexivity.
Qed.
Lemma pf_fm_pcx_arms : forall p, pf_fm_pc p -> pcom_pcx_arm p.
Proof.
  intros p Hp. destruct p; try (exfalso; exact Hp).
  - apply pcom_pcx_arm_lit.
  - exact pcom_pcx_arm_ps.
  - exact pcom_pcx_arm_pps.
Qed.

(* ==== printf_common's grammar for any piece predicate PK whose pieces have their pcx arm ==== *)
Section PcomK.
Variable PK : pf_piece -> Prop.
Hypothesis ARM_pcx : forall p, PK p -> pcom_pcx_arm p.

Lemma pcx_K : forall fuel fmt ps args T,
  (length fmt < fuel)%nat -> pf_parse fmt = Some ps -> Forall PK ps -> pf_text ps args = Some T ->
  (exists n, pcx_walk fuel (fmt ++ [0]) (map pa_of args) = Some n) /\
  pcx_covs fuel (fmt ++ [0]) (map pa_of args) (pc_cinK ps) = pc_cinK ps.
Proof.
  induction fuel as [|fuel IH]; intros fmt ps args T Hf Hp HK HT; [lia|].
  destruct ps as [|p ps].
  - rewrite (pf_parse_nil fmt Hp). cbn in HT. destruct args as [|a args]; [|discriminate HT].
    split; [exists 0%nat; reflexivity | reflexivity].
  - destruct (pf_parse_split fmt p ps Hp) as (r & -> & Hr & Hok).
    inversion HK as [|? ? Hk HK1]; subst.
    rewrite pf_text_step in HT. destruct (pf_step p args) as [[c a']|] eqn:ES; [|discriminate HT].
    destruct (pf_text ps a') as [T1|] eqn:HT1; [|discriminate HT].
    assert (L : (1 <= length (pf_code p))%nat) by (destruct p; cbn; lia).
    rewrite length_app in Hf.
    destruct (IH r ps a' T1 ltac:(lia) Hr HK1 HT1) as ((n1 & W1) & C1).
    destruct (ARM_pcx p Hk fuel (r ++ [0]) args c a' (pc_cinK ps) Hok ES) as (AW & AC).
    rewrite <- app_assoc. split.
    + exact (AW n1 W1).
    + change (pc_cinK (p :: ps)) with (pc_cin1 p ++ pc_cinK ps). rewrite AC, C1. reflexivity.
Qed.

Lemma pcomx_K : forall fmt ps args T,
  pf_parse fmt = Some ps -> Forall PK ps -> pf_text ps args = Some T ->
  pcomx_ok (fmt ++ [0]) (map pa_of args) = true /\
  pcx_covs (length (fmt ++ [0])) (fmt ++ [0]) (map pa_of args) (pc_cinK ps) = pc_cinK ps.
Proof.
  intros fmt ps args T Hp HK HT.
  destruct (pcx_K (length (fmt ++ [0])) fmt ps args T ltac:(rewrite length_app; cbn; lia) Hp HK HT) as ((n & W) & C).
  split; [unfold pcomx_ok; rewrite W; reflexivity | exact C].
Qed.
End PcomK.

(* every byte of a parsed format is a nonzero byte *)
Lemma pf_parse_bytes : forall fmt ps, pf_parse fmt = Some ps -> Forall (fun c => 0 < c < 256) fmt.
Proof.
  fix IH 1. intros fmt ps Hp. destruct fmt as [|b r]; [constructor|].
  revert Hp. cbn [pf_parse].
  destruct (b =? 37) eqn:E37.
  - apply Z.eqb_eq in E37. subst b. destruct r as [|c r1]; [intro Hq; discriminate Hq|]. intro Hp.
    constructor; [lia|]. revert Hp.
    destruct (c =? 100) eqn:E1.
    { apply Z.eqb_eq in E1. subst c. destruct (pf_parse r1) as [p1|] eqn:E; [intros _ | intro Hq; discriminate Hq].
      constructor; [lia | exact (IH r1 p1 E)]. }
    destruct (c =? 99) eqn:E2.
    { apply Z.eqb_eq in E2. subst c. destruct (pf_parse r1) as [p1|] eqn:E; [intros _ | intro Hq; discriminate Hq].
      constructor; [lia | exact (IH r1 p1 E)]. }
    destruct (c =? 115) eqn:E3.
    { apply Z.eqb_eq in E3. subst c. destruct (pf_parse r1) as [p1|] eqn:E; [intros _ | intro Hq; discriminate Hq].
      constructor; [lia | exact (IH r1 p1 E)]. }
    destruct (c =? 48) eqn:E4.
    { apply Z.eqb_eq in E4. subst c. destruct r1 as [|c2 [|c3 r3]]; [intro Hq; discriminate Hq | intro Hq; discriminate Hq|].
      destruct ((c2 =? 52) && (c3 =? 120)) eqn:F1.
      - apply andb_prop in F1 as [F1 F2]. apply Z.eqb_eq in F1. apply Z.eqb_eq in F2. subst c2 c3.
        destruct (pf_parse r3) as [p3|] eqn:E; [intros _ | intro Hq; discriminate Hq].
        constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. exact (IH r3 p3 E).
      - destruct ((c2 =? 50) && (c3 =? 120)) eqn:F2; [|intro Hq; discriminate Hq].
        apply andb_prop in F2 as [F2 F3]. apply Z.eqb_eq in F2. apply Z.eqb_eq in F3. subst c2 c3.
        destruct (pf_parse r3) as [p3|] eqn:E; [intros _ | intro Hq; discriminate Hq].
        constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. exact (IH r3 p3 E). }
    destruct (c =? 108) eqn:E5.
    { apply Z.eqb_eq in E5. subst c. destruct r1 as [|c2 [|c3 r3]]; [intro Hq; discriminate Hq | intro Hq; discriminate Hq|].
      destruct ((c2 =? 108) && (c3 =? 117)) eqn:F1; [|intro Hq; discriminate Hq].
      apply andb_prop in F1 as [F1 F2]. apply Z.eqb_eq in F1. apply Z.eqb_eq in F2. subst c2 c3.
      destruct (pf_parse r3) as [p3|] eqn:E; [intros _ | intro Hq; discriminate Hq].
      constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. exact (IH r3 p3 E). }
    destruct (c =? 46) eqn:E6; [|intro Hq; discriminate Hq].
    apply Z.eqb_eq in E6. subst c. destruct r1 as [|c2 [|c3 r3]]; [intro Hq; discriminate Hq | intro Hq; discriminate Hq|].
    destruct ((c2 =? 42) && (c3 =? 115)) eqn:F1; [|intro Hq; discriminate Hq].
    apply andb_prop in F1 as [F1 F2]. apply Z.eqb_eq in F1. apply Z.eqb_eq in F2. subst c2 c3.
    destruct (pf_parse r3) as [p3|] eqn:E; [intros _ | intro Hq; discriminate Hq].
    constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. exact (IH r3 p3 E).
  - destruct ((0 <? b) && (b <? 256)) eqn:Hb; [|intro Hq; discriminate Hq].
    apply andb_prop in Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2.
    destruct (pf_parse r) as [p1|] eqn:E; [intros _ | intro Hq; discriminate Hq].
    constructor; [lia | exact (IH r p1 E)].
Qed.

(* ---- fm's format family ---- *)
(* every %s / %.*s string with its NUL word inside the application memory (cstr_ok's amem_range p (len + 8)) *)
Fixpoint pf_args_amem (ws : list Z) (args : list pf_arg) : Prop :=
  match args, ws with
  | APtr s :: a', w :: w' => amem_range w (Z.of_nat (length s) + 8) /\ pf_args_amem w' a'
  | _ :: a', _ :: w' => pf_args_amem w' a'
  | _, _ => True
  end.
(* printf_common's family at fm: literals, %s and %.*s; a nonempty format inside fm's image (every format fm passes is a
   .rodata literal); the chain's FF_fm (Param, lib/B/FMsnprintfFm.v) is a subfamily *)
Definition FF_pcom : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
  fmt_at rd rs f fmt /\ fmt <> [] /\ f + Z.of_nat (length fmt) + 1 <= TFIB_IMG_END /\
  pf_parse fmt = Some ps /\ Forall pf_fm_piece ps /\ pf_args_asan rd rs ws args /\ pf_args_amem ws args /\
  pf_text ps args = Some T /\ pf_prec_pos ps args.

(* FF_pcom at any piece predicate PK (fm's non-%s printf widening); FF_pcom is FF_pcomK pf_fm_piece *)
Definition FF_pcomK (PK : pf_piece -> Prop) : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
  fmt_at rd rs f fmt /\ fmt <> [] /\ f + Z.of_nat (length fmt) + 1 <= TFIB_IMG_END /\
  pf_parse fmt = Some ps /\ Forall PK ps /\ pf_args_asan rd rs ws args /\ pf_args_amem ws args /\
  pf_text ps args = Some T /\ pf_prec_pos ps args.
Lemma FF_pcom_K : forall rd rs f ws T, FF_pcom rd rs f ws T <-> FF_pcomK pf_fm_piece rd rs f ws T.
Proof. intros rd rs f ws T. split; intro H; exact H. Qed.
