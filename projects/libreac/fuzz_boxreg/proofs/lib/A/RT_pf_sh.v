(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/RT_pf_sh.v (a working branch 7e395de08f5) to libreac/fuzz_boxreg.asan: module paths changed; 0 address numerals relocated (port_addr_check 5033540ba83b predict mode, symbol + offset); re-pointed Requires: FMsnprintfPf -> lib.A.Rt, FMsnprintfShared -> lib.A.Rt. *)
(* ASan's printf_common at fuzz_manifest.asan (RT_pf_Tbl.v PF_PRINTF_COMMON) in the shared contracts' form:
   sh_apcommon_realizesUz (FMsnprintfSx.v) for fm's format family FF_fm, from the relocated Bz walk (RT_pf_bz.v
   pcom_call, lib/A/Bz/A/I_pcxlist.v pcom_genx_spec).
   - the grammar: a format pf_parse reads as literals, %s and %.*s (pf_fm_piece) is one printf_common's own grammar
     accepts (I_pcxgram.v pcomx_ok), with the arguments mapped piece by piece (pa_of) and the coverage list pc_cin
     (a %.*s string is not range-checked by the walk; a %s string is);
   - the memory: the walk runs on the cleaned store (FMbz_clean.v), so every read-only byte must read as the image:
     the non-owned ones from the contract's consts_view over PCM_CR, the owned ones from AR (FMInst.fmi_rom_viewO);
   - the post: the walk changes only [sp - PCOM_DEPTH, sp), inside the contract's window [sp - K, sp). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Bz.A Require Import I_pcxgram.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0d YG0f YG0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AF0x.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMsnprintfPf FMsnprintfShared.
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
   .rodata literal); the chain's FF_fm (Param, lib/A/FMsnprintfFm.v) is a subfamily *)
Definition FF_pcom : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
  fmt_at rd rs f fmt /\ fmt <> [] /\ f + Z.of_nat (length fmt) + 1 <= TFIB_IMG_END /\
  pf_parse fmt = Some ps /\ Forall pf_fm_piece ps /\ pf_args_asan rd rs ws args /\ pf_args_amem ws args /\
  pf_text ps args = Some T /\ pf_prec_pos ps args.
