(* reac_served_mark on image A: reac_code_emit's Pre, read set and line length at the two call sites of
   reac_served_mark: +0x2c8 (.str.3, after a failed reac_link_alias_read) and +0x5f4 (.str.5, after a
   failed reac_link_alias_write).

   The formats and the constant strings are .rodata literals whose exact bytes the Pre states (amk_policy_ok:
   S_STR3, S_STR5, S_STR6, S_SERVED, .str.7 = []), so each parse, conversion order and length is a computation
   here. A format pf_parse accepts holds only byte values (pf_parse_bytes), so `map (Z_to_bv 8) fmt` determines
   fmt, and by acstr_at_unique every format `aemit_fmt` can name at these two addresses is the Pre's: that pins
   the conversions, hence which vararg registers the callee reads as strings (srm_emit_rd_read, srm_emit_rd_mark).

   The printf length lemmas pf_text_length / pf_digits_len / pf_dec_len are the plain lane's
   (lib/Prog/link_msgs_fit.v, over the same printf_facts_c.pf_text), restated here because that file Requires
   the plain image.

   Proves no function (kind: segment lemma of reac_served_mark's walk: reac_code_emit's call-site facts). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI04 YI16 YM05 YG0v YG0f YG0n YG0d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkPa.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_markDefs reac_served_markUniq
reac_served_markXfer.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import printf_facts_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. printf: parsed formats hold bytes; the conversions a text takes; its length
   ========================================================================== *)

Lemma ea_om_some : forall {A C : Type} (f : A -> C) o y, option_map f o = Some y -> exists x, o = Some x.
Proof. intros A C f o y H. destruct o as [x|]; [exists x; reflexivity | discriminate H]. Qed.

Lemma pf_parse_bytes_n : forall n f ps, (length f <= n)%nat -> pf_parse f = Some ps ->
  Forall (fun c => 0 < c < 256) f.
Proof.
  induction n as [|n IH]; intros f ps Hl H.
  { destruct f; [constructor | cbn in Hl; lia]. }
  destruct f as [|b r]; [constructor|]. cbn [length] in Hl. cbn [pf_parse] in H. revert H.
  destruct (b =? 37) eqn:E37.
  - apply Z.eqb_eq in E37. subst b. destruct r as [|c r1]; [intros H; discriminate H|]. cbn [length] in Hl.
    intros H. constructor; [lia|]. revert H.
    destruct (c =? 100) eqn:E1.
    { apply Z.eqb_eq in E1. subst c. intros H. cbn in H. destruct (ea_om_some _ _ _ H) as (x & Hx).
      constructor; [lia|]. exact (IH r1 x ltac:(lia) Hx). }
    destruct (c =? 99) eqn:E2.
    { apply Z.eqb_eq in E2. subst c. intros H. cbn in H. destruct (ea_om_some _ _ _ H) as (x & Hx).
      constructor; [lia|]. exact (IH r1 x ltac:(lia) Hx). }
    destruct (c =? 115) eqn:E3.
    { apply Z.eqb_eq in E3. subst c. intros H. cbn in H. destruct (ea_om_some _ _ _ H) as (x & Hx).
      constructor; [lia|]. exact (IH r1 x ltac:(lia) Hx). }
    destruct (c =? 48) eqn:E4.
    { apply Z.eqb_eq in E4. subst c. destruct r1 as [|c2 [|c3 r3]]; try (intros H; cbn in H; discriminate H).
      cbn [length] in Hl. intros H. cbn in H. revert H.
      destruct ((c2 =? 52) && (c3 =? 120)) eqn:Ea.
      - apply andb_prop in Ea as [Ea1 Ea2]. apply Z.eqb_eq in Ea1, Ea2. subst c2 c3.
        intros H. cbn in H. destruct (ea_om_some _ _ _ H) as (x & Hx).
        constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. exact (IH r3 x ltac:(lia) Hx).
      - destruct ((c2 =? 50) && (c3 =? 120)) eqn:Eb; [|intros H; discriminate H].
        apply andb_prop in Eb as [Eb1 Eb2]. apply Z.eqb_eq in Eb1, Eb2. subst c2 c3.
        intros H. cbn in H. destruct (ea_om_some _ _ _ H) as (x & Hx).
        constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. exact (IH r3 x ltac:(lia) Hx). }
    destruct (c =? 108) eqn:E5.
    { apply Z.eqb_eq in E5. subst c. destruct r1 as [|c2 [|c3 r3]]; try (intros H; cbn in H; discriminate H).
      cbn [length] in Hl. intros H. cbn in H. revert H.
      destruct ((c2 =? 108) && (c3 =? 117)) eqn:Ea; [|intros H; discriminate H].
      apply andb_prop in Ea as [Ea1 Ea2]. apply Z.eqb_eq in Ea1, Ea2. subst c2 c3.
      intros H. cbn in H. destruct (ea_om_some _ _ _ H) as (x & Hx).
      constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. exact (IH r3 x ltac:(lia) Hx). }
    destruct (c =? 46) eqn:E6.
    { apply Z.eqb_eq in E6. subst c. destruct r1 as [|c2 [|c3 r3]]; try (intros H; cbn in H; discriminate H).
      cbn [length] in Hl. intros H. cbn in H. revert H.
      destruct ((c2 =? 42) && (c3 =? 115)) eqn:Ea; [|intros H; discriminate H].
      apply andb_prop in Ea as [Ea1 Ea2]. apply Z.eqb_eq in Ea1, Ea2. subst c2 c3.
      intros H. cbn in H. destruct (ea_om_some _ _ _ H) as (x & Hx).
      constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. exact (IH r3 x ltac:(lia) Hx). }
    intros H. discriminate H.
  - destruct ((0 <? b) && (b <? 256)) eqn:Eb; [|intros H; discriminate H].
    apply andb_prop in Eb as [Eb1 Eb2]. apply Z.ltb_lt in Eb1, Eb2.
    intros H. cbn in H. destruct (ea_om_some _ _ _ H) as (x & Hx). constructor; [lia|]. exact (IH r x ltac:(lia) Hx).
Qed.

Lemma pf_parse_bytes : forall f ps, pf_parse f = Some ps -> Forall (fun c => 0 < c < 256) f.
Proof. intros f ps H. exact (pf_parse_bytes_n (length f) f ps (le_n _) H). Qed.

Lemma ea_map_bytes : forall f, Forall (fun c => 0 < c < 256) f -> map bv_unsigned (map (Z_to_bv 8) f) = f.
Proof.
  induction f as [|c f IH]; intros H; [reflexivity|]. inversion H as [|c' f' Hc Hf]; subst.
  cbn [map]. rewrite IH by exact Hf. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8) with 256. lia.
Qed.

(* the pieces link's formats use, the literal bytes, the conversions *)
Definition pc_lds (p : pf_piece) : bool := match p with PLit _ | Pd | Ps => true | _ => false end.
Fixpoint pf_lits (ps : list pf_piece) : Z :=
  match ps with [] => 0 | PLit _ :: r => 1 + pf_lits r | _ :: r => pf_lits r end.
Definition pa_len (a : pf_arg) : Z :=
  match a with
  | AInt v => Z.of_nat (length (pf_dec v)) | AU64 u => Z.of_nat (length (pf_udec u)) | APtr s => Z.of_nat (length s)
  end.
Fixpoint pa_lens (args : list pf_arg) : Z := match args with [] => 0 | a :: r => pa_len a + pa_lens r end.

Lemma pc_lds_link : forall ps, forallb pc_lds ps = true -> Forall apf_link_piece ps.
Proof.
  induction ps as [|p ps IH]; intros H; [constructor|]. cbn [forallb] in H. apply andb_prop in H as [Hp H].
  constructor; [destruct p; cbn in Hp |- *; try discriminate Hp; exact I | exact (IH H)].
Qed.

(* the conversion list of a format: 1 for %s, 0 for %d (2 for any other) *)
Fixpoint convs (ps : list pf_piece) : list nat :=
  match ps with
  | [] => [] | PLit _ :: r => convs r | Ps :: r => 1%nat :: convs r | Pd :: r => 0%nat :: convs r
  | _ :: r => 2%nat :: convs r
  end.
Fixpoint args_fit (cs : list nat) (args : list pf_arg) : Prop :=
  match cs, args with
  | [], [] => True
  | S O :: cs', APtr _ :: args' => args_fit cs' args'
  | O :: cs', AInt _ :: args' => args_fit cs' args'
  | _, _ => False
  end.

Lemma pf_text_length : forall ps args T, forallb pc_lds ps = true -> pf_text ps args = Some T ->
  Z.of_nat (length T) = pf_lits ps + pa_lens args.
Proof.
  induction ps as [|p ps IH]; intros args T Hl Ht.
  - destruct args as [|a args]; cbn [pf_text] in Ht; [|discriminate Ht]. injection Ht as <-. reflexivity.
  - cbn [forallb] in Hl. apply andb_prop in Hl as [Hp Hl].
    destruct p; cbn [pc_lds] in Hp; try discriminate Hp.
    + cbn [pf_text] in Ht. destruct (pf_text ps args) as [T'|] eqn:E; cbn [option_map] in Ht; [|discriminate Ht].
      injection Ht as <-. pose proof (IH args T' Hl E) as L. cbn [length pf_lits]. lia.
    + destruct args as [|[v|u|s] args]; cbn [pf_text] in Ht; try discriminate Ht.
      destruct (pf_text ps args) as [T'|] eqn:E; cbn [option_map] in Ht; [|discriminate Ht].
      injection Ht as <-. pose proof (IH args T' Hl E) as L. rewrite length_app. cbn [pa_lens pa_len pf_lits]. lia.
    + destruct args as [|[v|u|s] args]; cbn [pf_text] in Ht; try discriminate Ht.
      destruct (pf_text ps args) as [T'|] eqn:E; cbn [option_map] in Ht; [|discriminate Ht].
      injection Ht as <-. pose proof (IH args T' Hl E) as L. rewrite length_app. cbn [pa_lens pa_len pf_lits]. lia.
Qed.

Lemma pf_text_fit : forall ps args T, forallb pc_lds ps = true -> pf_text ps args = Some T -> args_fit (convs ps) args.
Proof.
  induction ps as [|p ps IH]; intros args T Hl Ht.
  - destruct args; cbn in Ht; [exact I | discriminate Ht].
  - cbn [forallb] in Hl. apply andb_prop in Hl as [Hp Hl].
    destruct p; cbn [pc_lds] in Hp; try discriminate Hp; cbn [convs].
    + cbn [pf_text] in Ht. destruct (ea_om_some _ _ _ Ht) as (x & Hx). exact (IH args x Hl Hx).
    + destruct args as [|[v|u|s] args]; cbn [pf_text] in Ht; try discriminate Ht.
      destruct (ea_om_some _ _ _ Ht) as (x & Hx). exact (IH args x Hl Hx).
    + destruct args as [|[v|u|s] args]; cbn [pf_text] in Ht; try discriminate Ht.
      destruct (ea_om_some _ _ _ Ht) as (x & Hx). exact (IH args x Hl Hx).
Qed.

Lemma pf_text_of_fit : forall ps args, forallb pc_lds ps = true -> args_fit (convs ps) args ->
  exists T, pf_text ps args = Some T.
Proof.
  induction ps as [|p ps IH]; intros args Hl Hf.
  - destruct args; cbn in Hf; [exists []; reflexivity | contradiction].
  - cbn [forallb] in Hl. apply andb_prop in Hl as [Hp Hl].
    destruct p; cbn [pc_lds] in Hp; try discriminate Hp; cbn [convs] in Hf.
    + destruct (IH args Hl Hf) as (T & HT). exists (b :: T). cbn [pf_text]. rewrite HT. reflexivity.
    + destruct args as [|[v|u|s] args]; cbn in Hf; try contradiction.
      destruct (IH args Hl Hf) as (T & HT). exists (pf_dec v ++ T). cbn [pf_text]. rewrite HT. reflexivity.
    + destruct args as [|[v|u|s] args]; cbn in Hf; try contradiction.
      destruct (IH args Hl Hf) as (T & HT). exists (s ++ T). cbn [pf_text]. rewrite HT. reflexivity.
Qed.

Lemma pf_digits_len : forall fuel x acc n, 0 <= x < 10 ^ n -> 1 <= n ->
  Z.of_nat (length (pf_digits fuel x acc)) <= Z.of_nat (length acc) + n.
Proof.
  induction fuel as [|fuel IH]; intros x acc n Hx Hn; cbn [pf_digits]; [lia|].
  destruct (Z.ltb_spec x 10) as [H|H]; [cbn [length]; lia|].
  assert (Hn2 : 2 <= n).
  { destruct (Z_le_gt_dec 2 n) as [H2|H2]; [exact H2|].
    assert (E1 : n = 1) by lia. subst n. cbn in Hx. lia. }
  assert (E : 10 ^ n = 10 * 10 ^ (n - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (Hd : 0 <= x / 10 < 10 ^ (n - 1)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  pose proof (IH (x / 10) ((48 + x mod 10) :: acc) (n - 1) Hd ltac:(lia)) as L. cbn [length] in L. lia.
Qed.

Lemma pf_dec_len : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> Z.of_nat (length (pf_dec v)) <= 11.
Proof.
  intros v Hv. assert (P : 2 ^ 31 = 2147483648) by reflexivity.
  assert (Q : 10 ^ 10 = 10000000000) by reflexivity.
  unfold pf_dec. destruct (Z.ltb_spec v 0) as [H|H].
  - pose proof (pf_digits_len 11 (- v) [] 10 ltac:(lia) ltac:(lia)) as L. cbn [length] in *. lia.
  - pose proof (pf_digits_len 11 v [] 10 ltac:(lia) ltac:(lia)) as L. cbn [length] in *. lia.
Qed.

(* the int32 a register holds in its low 32 bits *)
Definition ea_sx32 (z : Z) : Z := let w := z mod 2 ^ 32 in if w <? 2 ^ 31 then w else w - 2 ^ 32.
Lemma ea_sx32_ok : forall z, - 2 ^ 31 <= ea_sx32 z < 2 ^ 31 /\ z mod 2 ^ 32 = ea_sx32 z mod 2 ^ 32.
Proof.
  intros z. assert (P31 : 2 ^ 31 = 2147483648) by reflexivity. assert (P32 : 2 ^ 32 = 4294967296) by reflexivity.
  unfold ea_sx32. cbv zeta. rewrite P31, P32. pose proof (Z.mod_pos_bound z 4294967296 ltac:(lia)) as H.
  destruct (Z.ltb_spec (z mod 4294967296) 2147483648); split; lia.
Qed.

Lemma ea_pos_of_nonul : forall s : list byte, ~ In (zb 0) s -> Forall (fun c => 0 < c < 256) (map bv_unsigned s).
Proof.
  intros s N. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [|lia].
  exfalso. apply N. replace (zb 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma ea_map_rt : forall s : list byte, map (Z_to_bv 8) (map bv_unsigned s) = s.
Proof. induction s as [|b s IH]; [reflexivity|]. cbn [map]. rewrite IH, Z_to_bv_bv_unsigned. reflexivity. Qed.

(* ==========================================================================
   2. the literals: their bytes as numbers, their parses
   ========================================================================== *)

Definition FMT_R : list Z := map bv_unsigned S_STR3.
Definition FMT_M : list Z := map bv_unsigned S_STR5.
Definition S_SERVEDZ : list Z := map bv_unsigned S_SERVED.

Definition PS_R : list pf_piece := Eval vm_compute in match pf_parse FMT_R with Some ps => ps | None => [] end.
Definition PS_M : list pf_piece := Eval vm_compute in match pf_parse FMT_M with Some ps => ps | None => [] end.
Lemma PS_R_ok : pf_parse FMT_R = Some PS_R. Proof. vm_compute. reflexivity. Qed.
Lemma PS_M_ok : pf_parse FMT_M = Some PS_M. Proof. vm_compute. reflexivity. Qed.
Lemma PS_R_lds : forallb pc_lds PS_R = true. Proof. vm_compute. reflexivity. Qed.
Lemma PS_M_lds : forallb pc_lds PS_M = true. Proof. vm_compute. reflexivity. Qed.
Lemma PS_R_convs : convs PS_R = [1; 0]%nat. Proof. vm_compute. reflexivity. Qed.
Lemma PS_M_convs : convs PS_M = [1; 1; 0; 1]%nat. Proof. vm_compute. reflexivity. Qed.
Lemma PS_R_lits : pf_lits PS_R = 143. Proof. vm_compute. reflexivity. Qed.
Lemma PS_M_lits : pf_lits PS_M = 94. Proof. vm_compute. reflexivity. Qed.
Lemma FMT_lens : length S_STR3 = 147%nat /\ length S_STR5 = 102%nat /\ length S_STR6 = 34%nat /\
  length S_SERVED = 14%nat.
Proof. split; [|split; [|split]]; vm_compute; reflexivity. Qed.
Lemma FMT_nonempty : FMT_R <> [] /\ FMT_M <> [].
Proof. split; vm_compute; discriminate. Qed.

(* the literal bytes and their NULs: .str.3, .str.4, .str.5, .str.6, .str.7 *)
Definition srm_lit_byte (a : Z) : Prop :=
  (LA_S_READERR <= a <= LA_S_READERR + 147) \/ (LA_S_SERVED <= a <= LA_S_SERVED + 14) \/
  (LA_S_WRITEERR <= a <= LA_S_WRITEERR + 102) \/ (LA_S_NOCAP <= a <= LA_S_NOCAP + 34) \/ a = LA_S_EMPTY.

Lemma xf_lit_not_owned : forall a, srm_lit_byte a -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros a Ha X. unfold srm_lit_byte, LA_S_READERR, LA_S_SERVED, LA_S_WRITEERR, LA_S_NOCAP, LA_S_EMPTY in Ha.
  unfold Tfib_owned_static in X.
  repeat (apply Exists_cons in X; destruct X as [X|X]; [unfold in_zr in X; cbn [fst snd] in X; lia|]).
  inversion X.
Qed.

(* a string the Pre states at p: any other reading of the same bytes, as a parsed format, is it *)
Lemma ea_same_str : forall segs (m : word -> option byte) p s fmt ps,
  acstr_at segs m p s -> acstr_at segs m p (map (Z_to_bv 8) fmt) -> pf_parse fmt = Some ps ->
  fmt = map bv_unsigned s.
Proof.
  intros segs m p s fmt ps H1 H2 Hp. rewrite <- (acstr_at_unique segs m p _ _ H2 H1).
  symmetry. exact (ea_map_bytes fmt (pf_parse_bytes fmt ps Hp)).
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis TB : PcapSyms B.

Lemma srm_lit_akb : forall lyc Sc slo shi a, srm_lit_byte a -> akb SEGS B lyc Sc slo shi a.
Proof.
  intros lyc Sc slo shi a Ha. right. right. left.
  assert (Hr : 0x21300 <= a <= 0x214e0)
    by (unfold srm_lit_byte, LA_S_READERR, LA_S_SERVED, LA_S_WRITEERR, LA_S_NOCAP, LA_S_EMPTY in Ha; lia).
  rewrite HSEGS, (ts_owned B TB), (ts_errno B TB).
  split; [apply xf_tfib_hull; lia|]. split; [exact (xf_lit_not_owned a Ha) | unfold TFIB_ERRNO; lia].
Qed.

End b.
End a.

(* ==========================================================================
   3. the facts at a reac_code_emit call, and what they give
   ========================================================================== *)

Section c.
Variable segs : list Segment.
Variable regs : bvmap 5 word.
Variable m : word -> option byte.
#[local] Notation K := REAC_CODE_EMIT_AK.

Definition srm_emit_facts (bl : list (Z * Z)) (k name : Z) (s : list byte) : Prop :=
  aarg regs 0 <> 0 /\ In (aarg regs 0, AMF_BLOCK) bl
  /\ amemfile_k segs m (aarg regs 0) k /\ k + MARK_LINE_MAX <= AMF_BUFSIZ
  /\ amf_blk_ok segs regs K m (aarg regs 0)
  /\ YCbq.off_img (aarg regs 0) AMF_BLOCK
  /\ getr regs 14 = w64 name /\ name <> 0 /\ acstr_at segs m name s /\ (length s <= 15)%nat
  /\ astr_rt_ok segs regs K m name s
  /\ apart name (Z.of_nat (length s) + 8) (aarg regs 0) AMF_BLOCK
  /\ acstr_at segs m LA_FMT_SS S_FMT_SS /\ astr_rt_ok segs regs K m LA_FMT_SS S_FMT_SS
  /\ acstr_at segs m LA_S_REACPW S_REACPW /\ astr_rt_ok segs regs K m LA_S_REACPW S_REACPW
  /\ acstr_at segs m LA_S_E_NOT_MARKED S_E_NOT_MARKED
  /\ astr_rt_ok segs regs K m LA_S_E_NOT_MARKED S_E_NOT_MARKED.

Lemma ea_w64 : forall p, 0 <= p < 2 ^ 64 -> bv_unsigned (w64 p) = p.
Proof.
  intros p Hp. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* a string as a %s argument *)
Lemma ea_str_arg : forall f (r : word) p s,
  bv_unsigned r = p -> acstr_at segs m p s -> astr_rt_ok segs regs K m p s ->
  apart p (Z.of_nat (length s) + 8) f AMF_BLOCK ->
  apf_arg_ok segs regs K m f r (APtr (map bv_unsigned s)).
Proof.
  intros f r p s Hr HS HT HA. cbn [apf_arg_ok]. rewrite Hr, ea_map_rt, length_map.
  split; [apply ea_pos_of_nonul; exact (proj2 HS)|]. split; [exact HS|]. split; [exact HT | exact HA].
Qed.

(* a literal lies apart from the FILE block, which is off the image *)
Lemma ea_lit_apart : forall f p n, YCbq.off_img f AMF_BLOCK -> 0x10000 <= p -> p + n <= 0x654000 ->
  apart p n f AMF_BLOCK.
Proof.
  intros f p n Hf H1 H2. unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, AMF_BLOCK in *. unfold apart. lia.
Qed.

(* ---- .str.3 at +0x2c8: a3 = .str.3, a4 = name, a5 = the code (its low 32 bits, as %d) ---- *)
Lemma srm_emit_pre_read : forall bl k name s,
  srm_emit_facts bl k name s ->
  aarg regs 3 = LA_S_READERR -> acstr_at segs m LA_S_READERR S_STR3 ->
  astr_rt_ok segs regs K m LA_S_READERR S_STR3 ->
  exists fmt ps args T,
    aemit_fmt segs regs K m (aarg regs 0) (aarg regs 3) fmt ps args T
    /\ EMIT_HEAD + Z.of_nat (length T) <= MARK_LINE_MAX
    /\ reac_code_emit_apre segs bl regs m.
Proof.
  intros bl k name s (F0 & Fbl & Fmf & Fk & Fblk & Foff & F14 & Fn0 & Fs & Fl & Frt & Fap &
    G1 & G2 & G3 & G4 & G5 & G6) A3 S3 R3.
  pose proof (xf_acstr_range segs m name s Fs) as Hnr.
  set (v := ea_sx32 (bv_unsigned (getr regs 15))).
  assert (Hfit : args_fit (convs PS_R) [APtr (map bv_unsigned s); AInt v]) by (rewrite PS_R_convs; cbn; exact I).
  destruct (pf_text_of_fit PS_R _ PS_R_lds Hfit) as (T & HT).
  pose proof (pf_text_length PS_R _ T PS_R_lds HT) as HL. rewrite PS_R_lits in HL. cbn [pa_lens pa_len] in HL.
  rewrite length_map in HL.
  pose proof (ea_sx32_ok (bv_unsigned (getr regs 15))) as (Hv1 & Hv2). fold v in Hv1, Hv2.
  pose proof (pf_dec_len v Hv1) as Hd.
  destruct FMT_lens as (L3 & _).
  assert (EF : aemit_fmt segs regs K m (aarg regs 0) (aarg regs 3) FMT_R PS_R [APtr (map bv_unsigned s); AInt v] T).
  { unfold aemit_fmt, FMT_R. rewrite A3, ea_map_rt, length_map, L3.
    split; [exact S3|]. split; [exact R3|]. unfold LA_RO_LO, LA_GOT_GUARD, LA_S_READERR.
    split; [lia|]. split; [lia|]. split; [exact PS_R_ok|].
    split; [exact (proj1 FMT_nonempty)|]. split; [exact (pc_lds_link PS_R PS_R_lds)|]. split; [exact HT|].
    cbn [apf_args_ok]. split; [|split; [|exact I]].
    - apply (ea_str_arg (aarg regs 0) (getr regs 14) name s);
        [rewrite F14; apply ea_w64; lia | exact Fs | exact Frt | exact Fap].
    - cbn [apf_arg_ok]. split; [exact Hv1 | exact Hv2]. }
  exists FMT_R, PS_R, [APtr (map bv_unsigned s); AInt v], T.
  split; [exact EF|]. split; [unfold EMIT_HEAD, MARK_LINE_MAX; lia|].
  exists FMT_R, PS_R, [APtr (map bv_unsigned s); AInt v], T, k.
  split; [exact F0|]. split; [rewrite A3; unfold LA_S_READERR; lia|]. split; [exact Fbl|].
  split; [exact Fmf|]. split; [exact Fblk|]. split; [unfold EMIT_HEAD, MARK_LINE_MAX, AMF_BUFSIZ in *; lia|].
  split; [exact EF|]. repeat (split; [assumption|]). assumption.
Qed.

(* every format aemit_fmt can name at .str.3 is the Pre's, with its two conversions *)
Lemma srm_emit_shape_read : forall f fmt ps args T,
  acstr_at segs m LA_S_READERR S_STR3 ->
  aemit_fmt segs regs K m f LA_S_READERR fmt ps args T ->
  fmt = FMT_R /\ ps = PS_R /\ exists s v, args = [APtr s; AInt v].
Proof.
  intros f fmt ps args T S3 (HS & _ & _ & _ & Hp & _ & _ & Ht & _).
  pose proof (ea_same_str segs m _ S_STR3 fmt ps S3 HS Hp) as E. fold FMT_R in E. subst fmt.
  rewrite PS_R_ok in Hp. injection Hp as <-. split; [reflexivity|]. split; [reflexivity|].
  pose proof (pf_text_fit PS_R args T PS_R_lds Ht) as Hf. rewrite PS_R_convs in Hf.
  destruct args as [|[v|u|s] [|[v'|u'|s'] [|a3 args]]]; cbn in Hf; try contradiction.
  exists s, v'. reflexivity.
Qed.

Lemma srm_emit_rd_read : forall name a,
  acstr_at segs m LA_S_READERR S_STR3 ->
  getr regs 14 = w64 name -> 0 <= name < 2 ^ 64 -> aarg regs 3 = LA_S_READERR ->
  reac_code_emit_ard segs regs m a ->
  (exists s', acstr_at segs m name s' /\ name <= a <= name + Z.of_nat (length s')) \/ srm_lit_byte a.
Proof.
  intros name a S3 R14 Hn A3 [(_ & s0 & HS0 & Ha) | (fmt & ps & args & T & HF & Hrd)].
  - right. rewrite A3 in HS0, Ha. rewrite (acstr_at_unique segs m _ _ _ HS0 S3) in Ha.
    destruct FMT_lens as (L3 & _). rewrite L3 in Ha. unfold srm_lit_byte. left. exact Ha.
  - rewrite A3 in HF. destruct (srm_emit_shape_read _ fmt ps args T S3 HF) as (_ & _ & s & v & ->).
    destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & HA). cbn [apf_args_ok apf_arg_ok] in HA.
    destruct HA as ((_ & Hs & _) & _). rewrite R14, (ea_w64 name Hn) in Hs.
    cbn [apf_rd] in Hrd. destruct Hrd as [Hrd|[]].
    left. exists (map (Z_to_bv 8) s). split; [exact Hs|]. rewrite length_map.
    rewrite R14, (ea_w64 name Hn) in Hrd. exact Hrd.
Qed.

(* ---- .str.5 at +0x5f4: a3 = .str.5, a4 = name, a5 = .str.4, a6 = the code (%d), a7 = .str.6 or .str.7 ---- *)
Lemma srm_emit_pre_mark : forall bl k name s cap sc,
  srm_emit_facts bl k name s ->
  aarg regs 3 = LA_S_WRITEERR -> acstr_at segs m LA_S_WRITEERR S_STR5 ->
  astr_rt_ok segs regs K m LA_S_WRITEERR S_STR5 ->
  getr regs 15 = w64 LA_S_SERVED -> acstr_at segs m LA_S_SERVED S_SERVED ->
  astr_rt_ok segs regs K m LA_S_SERVED S_SERVED ->
  ((cap = LA_S_NOCAP /\ sc = S_STR6) \/ (cap = LA_S_EMPTY /\ sc = [])) -> getr regs 17 = w64 cap ->
  acstr_at segs m cap sc -> astr_rt_ok segs regs K m cap sc ->
  exists fmt ps args T,
    aemit_fmt segs regs K m (aarg regs 0) (aarg regs 3) fmt ps args T
    /\ EMIT_HEAD + Z.of_nat (length T) <= MARK_LINE_MAX
    /\ reac_code_emit_apre segs bl regs m.
Proof.
  intros bl k name s cap sc (F0 & Fbl & Fmf & Fk & Fblk & Foff & F14 & Fn0 & Fs & Fl & Frt & Fap &
    G1 & G2 & G3 & G4 & G5 & G6) A3 S5 R5 R15 SS SR Hcap R17 SC RC.
  destruct FMT_lens as (L3 & L5 & L6 & L4).
  assert (Hcz : Z.of_nat (length sc) <= 34 /\ LA_S_NOCAP <= cap <= LA_S_EMPTY).
  { destruct Hcap as [(-> & ->) | (-> & ->)]; [rewrite L6 | cbn [length]]; unfold LA_S_NOCAP, LA_S_EMPTY; lia. }
  pose proof (xf_acstr_range segs m name s Fs) as Hnr.
  set (v := ea_sx32 (bv_unsigned (getr regs 16))).
  set (args := [APtr (map bv_unsigned s); APtr S_SERVEDZ; AInt v; APtr (map bv_unsigned sc)]).
  assert (Hfit : args_fit (convs PS_M) args) by (rewrite PS_M_convs; cbn; exact I).
  destruct (pf_text_of_fit PS_M _ PS_M_lds Hfit) as (T & HT).
  pose proof (pf_text_length PS_M _ T PS_M_lds HT) as HL. rewrite PS_M_lits in HL.
  unfold args in HL. cbn [pa_lens pa_len] in HL. unfold S_SERVEDZ in HL. rewrite !length_map, L4 in HL.
  pose proof (ea_sx32_ok (bv_unsigned (getr regs 16))) as (Hv1 & Hv2). fold v in Hv1, Hv2.
  pose proof (pf_dec_len v Hv1) as Hd.
  assert (EF : aemit_fmt segs regs K m (aarg regs 0) (aarg regs 3) FMT_M PS_M args T).
  { unfold aemit_fmt, FMT_M. rewrite A3, ea_map_rt, length_map, L5.
    split; [exact S5|]. split; [exact R5|]. unfold LA_RO_LO, LA_GOT_GUARD, LA_S_WRITEERR.
    split; [lia|]. split; [lia|]. split; [exact PS_M_ok|].
    split; [exact (proj2 FMT_nonempty)|]. split; [exact (pc_lds_link PS_M PS_M_lds)|]. split; [exact HT|].
    unfold args. cbn [apf_args_ok]. split; [|split; [|split; [|split; [|exact I]]]].
    - apply (ea_str_arg (aarg regs 0) (getr regs 14) name s);
        [rewrite F14; apply ea_w64; lia | exact Fs | exact Frt | exact Fap].
    - apply (ea_str_arg (aarg regs 0) (getr regs 15) LA_S_SERVED S_SERVED);
        [rewrite R15; apply ea_w64; unfold LA_S_SERVED; lia | exact SS | exact SR |].
      rewrite L4. apply ea_lit_apart; [exact Foff | unfold LA_S_SERVED; lia | unfold LA_S_SERVED; lia].
    - cbn [apf_arg_ok]. split; [exact Hv1 | exact Hv2].
    - apply (ea_str_arg (aarg regs 0) (getr regs 17) cap sc);
        [rewrite R17; apply ea_w64; unfold LA_S_NOCAP, LA_S_EMPTY in Hcz; lia | exact SC | exact RC |].
      apply ea_lit_apart; [exact Foff | unfold LA_S_NOCAP, LA_S_EMPTY in Hcz; lia
        | unfold LA_S_NOCAP, LA_S_EMPTY in Hcz; lia]. }
  exists FMT_M, PS_M, args, T.
  split; [exact EF|]. split; [unfold EMIT_HEAD, MARK_LINE_MAX; lia|].
  exists FMT_M, PS_M, args, T, k.
  split; [exact F0|]. split; [rewrite A3; unfold LA_S_WRITEERR; lia|]. split; [exact Fbl|].
  split; [exact Fmf|]. split; [exact Fblk|]. split; [unfold EMIT_HEAD, MARK_LINE_MAX, AMF_BUFSIZ in *; lia|].
  split; [exact EF|]. repeat (split; [assumption|]). assumption.
Qed.

Lemma srm_emit_shape_mark : forall f fmt ps args T,
  acstr_at segs m LA_S_WRITEERR S_STR5 ->
  aemit_fmt segs regs K m f LA_S_WRITEERR fmt ps args T ->
  fmt = FMT_M /\ ps = PS_M /\ exists s1 s2 v s3, args = [APtr s1; APtr s2; AInt v; APtr s3].
Proof.
  intros f fmt ps args T S5 (HS & _ & _ & _ & Hp & _ & _ & Ht & _).
  pose proof (ea_same_str segs m _ S_STR5 fmt ps S5 HS Hp) as E. fold FMT_M in E. subst fmt.
  rewrite PS_M_ok in Hp. injection Hp as <-. split; [reflexivity|]. split; [reflexivity|].
  pose proof (pf_text_fit PS_M args T PS_M_lds Ht) as Hf. rewrite PS_M_convs in Hf.
  destruct args as [|[v1|u1|s1] [|[v2|u2|s2] [|[v3|u3|s3] [|[v4|u4|s4] [|a5 args]]]]];
    cbn in Hf; try contradiction.
  exists s1, s2, v3, s4. reflexivity.
Qed.

Lemma srm_emit_rd_mark : forall name cap sc a,
  acstr_at segs m LA_S_WRITEERR S_STR5 -> acstr_at segs m LA_S_SERVED S_SERVED ->
  getr regs 14 = w64 name -> 0 <= name < 2 ^ 64 -> aarg regs 3 = LA_S_WRITEERR ->
  getr regs 15 = w64 LA_S_SERVED ->
  ((cap = LA_S_NOCAP /\ sc = S_STR6) \/ (cap = LA_S_EMPTY /\ sc = [])) -> getr regs 17 = w64 cap ->
  acstr_at segs m cap sc ->
  reac_code_emit_ard segs regs m a ->
  (exists s', acstr_at segs m name s' /\ name <= a <= name + Z.of_nat (length s')) \/ srm_lit_byte a.
Proof.
  intros name cap sc a S5 SS R14 Hn A3 R15 Hcap R17 SC [(_ & s0 & HS0 & Ha) | (fmt & ps & args & T & HF & Hrd)].
  - right. rewrite A3 in HS0, Ha. rewrite (acstr_at_unique segs m _ _ _ HS0 S5) in Ha.
    destruct FMT_lens as (_ & L5 & _). rewrite L5 in Ha. unfold srm_lit_byte. right. right. left. exact Ha.
  - rewrite A3 in HF.
    destruct (srm_emit_shape_mark _ fmt ps args T S5 HF) as (_ & _ & s1 & s2 & v & s3 & ->).
    destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & HA). cbn [apf_args_ok apf_arg_ok] in HA.
    destruct HA as ((P1 & H1 & _) & (P2 & H2 & _) & _ & (P3 & H3 & _) & _).
    destruct FMT_lens as (_ & _ & L6 & L4).
    assert (Hcr : 0 <= cap < 2 ^ 64)
      by (destruct Hcap as [(-> & _) | (-> & _)]; unfold LA_S_NOCAP, LA_S_EMPTY; lia).
    rewrite R14, (ea_w64 name Hn) in H1. rewrite R15, ea_w64 in H2 by (unfold LA_S_SERVED; lia).
    rewrite R17, (ea_w64 cap Hcr) in H3.
    cbn [apf_rd] in Hrd. destruct Hrd as [Hrd | [Hrd | [Hrd | []]]].
    + left. exists (map (Z_to_bv 8) s1). rewrite R14, (ea_w64 name Hn) in Hrd.
      split; [exact H1|]. rewrite length_map. exact Hrd.
    + right. rewrite R15, ea_w64 in Hrd by (unfold LA_S_SERVED; lia).
      pose proof (acstr_at_unique segs m _ _ _ H2 SS) as E.
      assert (L2 : length s2 = length S_SERVED) by (rewrite <- E, length_map; reflexivity).
      rewrite L2, L4 in Hrd. unfold srm_lit_byte. right. left. exact Hrd.
    + right. rewrite R17, (ea_w64 cap Hcr) in Hrd.
      pose proof (acstr_at_unique segs m _ _ _ H3 SC) as E.
      assert (L2 : length s3 = length sc) by (rewrite <- E, length_map; reflexivity). rewrite L2 in Hrd.
      unfold srm_lit_byte. destruct Hcap as [(-> & ->) | (-> & ->)].
      * rewrite L6 in Hrd. right. right. right. left. exact Hrd.
      * cbn [length Z.of_nat] in Hrd. right. right. right. right. lia.
Qed.

End c.
