From Stdlib Require Import String Ascii ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Mem.
Import ListNotations.
Open Scope Z_scope.

Definition REC_ADD : Z := 0.
Definition REC_CALL : Z := 1.
Definition REC_REMOVE : Z := 2.
Definition REC_REMOVE_ALL : Z := 3.
Definition REC_CONNECT : Z := 4.
Definition REC_BROADCAST : Z := 5.
Definition REC_HOST_SETTING : Z := 6.
Definition REC_INSTANCE_VERB : Z := 7.
Definition REC_WORKER_LIST : Z := 8.
Definition REC_INSTANCE_INFO : Z := 9.
Definition REC_RESET : Z := 10.
Definition REC_QUARANTINE_CLEAR : Z := 11.
Definition REC_POLICY_SET : Z := 12.
Definition REC_PIN_ACCEPT : Z := 13.
Definition REC_POOL_CONFIG : Z := 14.
Definition REC_LV2_WORKER_SET : Z := 15.
Definition REC_WORKER_ENV : Z := 16.
Definition REC_CHAIN : Z := 17.
Definition REC_CHAIN_CLEAR : Z := 18.
Definition REC_AFTER_REPLY : Z := 19.
Definition REC_PINS_SET : Z := 20.
Definition REC_PINS_CLEAR : Z := 21.
Definition REC_DESCRIPTORS_ADD : Z := 22.
Definition REC_DESCRIPTORS_GET : Z := 23.
Definition REC_DESCRIPTORS_PANEL_GET : Z := 24.
Definition REC_LV2_REFUSALS_FORGET : Z := 25.
Definition REC_FN_COUNT : Z := 26.
Definition REC_ARGS_MAX : Z := 6.
Definition REC_CALLS_MAX : Z := 16.
Definition PHD_LINE_MAX : Z := 4096.
Definition LMAX : Z := 8192.

Definition bstr (s : string) : list byte :=
  map (fun c => Z_to_bv 8 (Z.of_N (N_of_ascii c))) (list_ascii_of_string s).

Definition bl_eqb (x y : list byte) : bool :=
  if list_eq_dec Z.eq_dec (map bv_unsigned x) (map bv_unsigned y) then true else false.

Definition no0 (x : list byte) : Prop := ~ In (Z_to_bv 8 0) x.

Definition nz (x : list byte) : bool := forallb (fun b => negb (bv_unsigned b =? 0)) x.

Lemma byte_unsigned : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z H. rewrite Z_to_bv_unsigned. change (bv_wrap 8 z) with (z mod 256). apply Z.mod_small. exact H.
Qed.

Lemma no0_forall : forall x, Forall (fun b => bv_unsigned b <> 0) x -> no0 x.
Proof.
  intros x HF HI. rewrite Forall_forall in HF. apply (HF _ HI). rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma no0_nz : forall x, nz x = true -> no0 x.
Proof.
  intros x H. apply no0_forall. unfold nz in H. rewrite forallb_forall in H. rewrite Forall_forall.
  intros b Hb E. specialize (H b Hb). apply negb_true_iff, Z.eqb_neq in H. exact (H E).
Qed.

Lemma no0_app : forall x y, no0 x -> no0 y -> no0 (x ++ y).
Proof. unfold no0. intros x y Hx Hy H. apply in_app_or in H. tauto. Qed.

Fixpoint digits (k : nat) (n : Z) (acc : list byte) : list byte :=
  match k with
  | O => acc
  | S k' =>
      if n <? 10 then Z_to_bv 8 (48 + n) :: acc
      else digits k' (n / 10) (Z_to_bv 8 (48 + n mod 10) :: acc)
  end.

Definition dec (v : Z) : list byte :=
  (if v <? 0 then [Z_to_bv 8 45] else []) ++ digits 10 (Z.abs v) [].

Lemma digits_S : forall k n acc, digits (S k) n acc =
  if n <? 10 then Z_to_bv 8 (48 + n) :: acc else digits k (n / 10) (Z_to_bv 8 (48 + n mod 10) :: acc).
Proof. reflexivity. Qed.

Lemma digits_length : forall k n acc, 0 <= n < 10 ^ Z.of_nat (S k) ->
  (S (length acc) <= length (digits (S k) n acc) <= S k + length acc)%nat.
Proof.
  induction k as [|k IH]; intros n acc Hn.
  - cbn [digits]. destruct (n <? 10); cbn [length]; lia.
  - rewrite (digits_S (S k)). destruct (Z.ltb_spec n 10) as [H|H].
    + cbn [length]. lia.
    + assert (Hq : 0 <= n / 10 < 10 ^ Z.of_nat (S k)).
      { replace (10 ^ Z.of_nat (S (S k))) with (10 * 10 ^ Z.of_nat (S k)) in Hn
          by (rewrite (Nat2Z.inj_succ (S k)), Z.pow_succ_r by lia; ring).
        split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
      pose proof (IH (n / 10) (Z_to_bv 8 (48 + n mod 10) :: acc) Hq) as E. cbn [length] in E. lia.
Qed.

Lemma dec_length : forall v, -2^31 <= v < 2^31 -> (1 <= length (dec v) <= 11)%nat.
Proof.
  intros v Hv. unfold dec. rewrite length_app.
  assert (Ha : 0 <= Z.abs v < 10 ^ Z.of_nat (S 9)) by (change (10 ^ Z.of_nat (S 9)) with 10000000000; lia).
  pose proof (digits_length 9 (Z.abs v) [] Ha) as E. cbn [length] in E.
  destruct (v <? 0); cbn [length]; lia.
Qed.

Lemma digits_nz : forall k n acc, 0 <= n -> Forall (fun b => bv_unsigned b <> 0) acc ->
  Forall (fun b => bv_unsigned b <> 0) (digits k n acc).
Proof.
  induction k as [|k IH]; intros n acc Hn Hacc; cbn [digits]; [exact Hacc|].
  destruct (Z.ltb_spec n 10) as [H|H].
  - apply Forall_cons; [|exact Hacc]. rewrite byte_unsigned by lia. lia.
  - apply IH; [apply Z.div_pos; lia|]. apply Forall_cons; [|exact Hacc].
    pose proof (Z.mod_pos_bound n 10 ltac:(lia)). rewrite byte_unsigned by lia. lia.
Qed.

Lemma dec_no0 : forall v, no0 (dec v).
Proof.
  intros v. apply no0_forall. unfold dec. apply Forall_app. split.
  - destruct (v <? 0); [apply Forall_cons; [rewrite byte_unsigned by lia; lia | apply Forall_nil] | apply Forall_nil].
  - apply digits_nz; [lia | apply Forall_nil].
Qed.

Definition resp (c : Z) : list byte := bstr "resp "%string ++ dec c.

Lemma resp_length : forall c, -2^31 <= c < 2^31 -> (6 <= length (resp c) <= 16)%nat.
Proof.
  intros c Hc. unfold resp. rewrite length_app. pose proof (dec_length c Hc).
  change (length (bstr "resp "%string)) with 5%nat. lia.
Qed.

Lemma resp_no0 : forall c, no0 (resp c).
Proof. intros c. apply no0_app; [apply no0_nz; vm_compute; reflexivity | apply dec_no0]. Qed.

Definition SPACE : byte := Z_to_bv 8 32.

Definition is_sep (b : byte) : bool := (bv_unsigned b =? 32) || (bv_unsigned b =? 9).

Fixpoint words_go (cur : list byte) (T : list byte) : list (list byte) :=
  match T with
  | [] => match cur with [] => [] | _ :: _ => [rev cur] end
  | b :: T' =>
      if is_sep b
      then match cur with [] => words_go [] T' | _ :: _ => rev cur :: words_go [] T' end
      else words_go (b :: cur) T'
  end.

Definition words (T : list byte) : list (list byte) := words_go [] T.

Fixpoint join_sp (ws : list (list byte)) : list byte :=
  match ws with
  | [] => []
  | w :: ws' => match ws' with [] => w | _ :: _ => w ++ SPACE :: join_sp ws' end
  end.

Definition canon (T : list byte) : list byte := join_sp (words T).

Definition sp_concat (ws : list (list byte)) : list byte := concat (map (cons SPACE) ws).

Lemma join_sp_concat : forall ws, join_sp ws = tl (sp_concat ws).
Proof.
  induction ws as [|w ws IH]; [reflexivity|].
  unfold sp_concat in *. cbn [join_sp map concat tl app].
  destruct ws as [|w2 ws']; [cbn; rewrite app_nil_r; reflexivity|].
  rewrite IH. cbn [map concat app tl]. reflexivity.
Qed.

Lemma words_go_length : forall T cur,
  (length (sp_concat (words_go cur T)) <= length T + length cur + 1)%nat.
Proof.
  unfold sp_concat. induction T as [|b T IH]; intros cur.
  - destruct cur as [|x r]; cbn [words_go map concat length]; [lia|].
    rewrite app_nil_r. cbn [length]. rewrite length_rev. cbn [length]. lia.
  - cbn [words_go]. destruct (is_sep b).
    + destruct cur as [|x r].
      * specialize (IH []). cbn [length] in *. lia.
      * cbn [map concat]. rewrite length_app. cbn [length] in *. rewrite length_rev.
        specialize (IH []). cbn [length] in *. lia.
    + specialize (IH (b :: cur)). cbn [length] in *. lia.
Qed.

Lemma canon_length : forall T, (length (canon T) <= length T)%nat.
Proof.
  intros T. unfold canon, words. rewrite join_sp_concat.
  pose proof (words_go_length T []) as E. cbn [length] in E.
  destruct (sp_concat (words_go [] T)); cbn [tl length] in *; lia.
Qed.

Lemma words_go_in : forall T cur x,
  In x (sp_concat (words_go cur T)) -> x = SPACE \/ In x cur \/ In x T.
Proof.
  unfold sp_concat. induction T as [|b T IH]; intros cur x H.
  - destruct cur as [|y r]; cbn [words_go map concat] in H; [destruct H|].
    rewrite app_nil_r in H. destruct H as [H|H]; [left; congruence|]. right; left. apply in_rev. exact H.
  - cbn [words_go] in H. destruct (is_sep b).
    + destruct cur as [|y r].
      * destruct (IH [] x H) as [E|[E|E]]; [left; exact E | destruct E | right; right; right; exact E].
      * cbn [map concat] in H. destruct H as [H|H]; [left; congruence|].
        apply in_app_or in H. destruct H as [H|H]; [right; left; apply in_rev; exact H|].
        destruct (IH [] x H) as [E|[E|E]]; [left; exact E | destruct E | right; right; right; exact E].
    + destruct (IH (b :: cur) x H) as [E|[[E|E]|E]].
      * left; exact E.
      * right; right; left; congruence.
      * right; left; exact E.
      * right; right; right; exact E.
Qed.

Lemma canon_no0 : forall T, no0 T -> no0 (canon T).
Proof.
  intros T HT H. unfold canon, words in H. rewrite join_sp_concat in H.
  assert (H' : In (Z_to_bv 8 0) (sp_concat (words_go [] T)))
    by (destruct (sp_concat (words_go [] T)); [destruct H | right; exact H]).
  destruct (words_go_in T [] _ H') as [E|[E|E]]; [|destruct E|exact (HT E)].
  apply (f_equal bv_unsigned) in E. unfold SPACE in E. rewrite !byte_unsigned in E by lia. discriminate.
Qed.

Definition FNV_B0 : Z := 0xcbf29ce484222325.
Definition FNV_P : Z := 0x100000001b3.

Fixpoint fnv (h : Z) (bs : list byte) : Z :=
  match bs with
  | [] => h
  | b :: bs' => fnv ((Z.lxor h (bv_unsigned b) * FNV_P) mod 2^64) bs'
  end.

Definition mix (h : Z) (bs : list byte) : Z := fnv (if h =? 0 then FNV_B0 else h) bs.

Definition le32 (fn : Z) : list byte := le4 (Z_to_bv 64 fn).

Definition mixcall (h fn : Z) (A : list (list byte)) : Z :=
  fold_left (fun g a => mix g (a ++ [Z_to_bv 8 0])) A (mix h (le32 fn)).

Lemma fnv_app : forall x y h, fnv h (x ++ y) = fnv (fnv h x) y.
Proof. induction x as [|b x IH]; intros y h; [reflexivity|]. cbn [app fnv]. apply IH. Qed.

Lemma fnv_range : forall bs h, 0 <= h < 2^64 -> 0 <= fnv h bs < 2^64.
Proof.
  induction bs as [|b bs IH]; intros h Hh; [exact Hh|]. cbn [fnv]. apply IH. apply Z.mod_pos_bound. lia.
Qed.

Lemma mix_range : forall h bs, 0 <= h < 2^64 -> 0 <= mix h bs < 2^64.
Proof. intros h bs Hh. unfold mix. apply fnv_range. destruct (h =? 0); unfold FNV_B0; lia. Qed.

Lemma mixcall_range : forall h fn A, 0 <= h < 2^64 -> 0 <= mixcall h fn A < 2^64.
Proof.
  intros h fn A Hh. unfold mixcall. generalize (mix_range h (le32 fn) Hh).
  generalize (mix h (le32 fn)). induction A as [|a A IH]; intros g Hg; [exact Hg|].
  cbn [fold_left]. apply IH. apply mix_range. exact Hg.
Qed.

Fixpoint inst_go (d : nat) (s : list byte) : list byte :=
  match s with
  | [] => []
  | b :: s' =>
      match d with
      | O => if bv_unsigned b =? 60 then Z_to_bv 8 49 :: inst_go 1 s' else b :: inst_go O s'
      | S d' =>
          if bv_unsigned b =? 60 then inst_go (S (S d')) s'
          else if bv_unsigned b =? 62 then inst_go d' s'
          else inst_go d s'
      end
  end.

Definition inst (s : list byte) : list byte := inst_go O s.

Definition fits (s : list byte) : Prop := Z.of_nat (length (inst s)) <= PHD_LINE_MAX - 1.

Lemma inst_go_length : forall s d, (length (inst_go d s) <= length s)%nat.
Proof.
  induction s as [|b s IH]; intros d; [cbn; lia|]. cbn [inst_go length].
  pose proof (IH 1%nat) as I1. pose proof (IH O) as I0. pose proof (IH d) as Id.
  pose proof (IH (S d)) as I2. pose proof (IH (S (S d))) as I3.
  destruct d as [|d]; [destruct (bv_unsigned b =? 60); cbn [length]; lia|].
  destruct (bv_unsigned b =? 60); [lia|].
  destruct (bv_unsigned b =? 62); [|lia].
  pose proof (IH d) as Id'. lia.
Qed.

Lemma inst_length : forall s, (length (inst s) <= length s)%nat.
Proof. intros s. apply inst_go_length. Qed.

Definition shape_table : list (list byte * list byte) :=
  map (fun r => (bstr (fst r), bstr (snd r)))
  [("add", "resp <instance>");
   ("worker_list", "resp <n> <worker>:<pid>:<format>:<state>:<place>:<i>,<i>,...");
   ("instance_info", "resp 0 <worker> <pid> <state> <crashes> <quarantined>");
   ("supervisor_reset", "resp 0");
   ("quarantine_clear", "resp 0");
   ("policy_set", "resp 0");
   ("pool_config", "resp 0");
   ("worker_env", "resp 0");
   ("pin_set", "resp 0");
   ("pin_clear", "resp 0");
   ("lv2_worker_set", "resp 0");
   ("pin_accept", "resp 0");
   ("pin_layout", "resp 0 <scheme>:<sha256>");
   ("pin_expect", "resp 0");
   ("chain", "resp 0");
   ("chain_clear", "resp 0");
   ("descriptor_get", "resp 0 ""<path>""");
   ("panel_get", "resp 0 ""<path>""");
   ("track_info", "resp 0");
   ("remote_pages", "resp <count>");
   ("remote_page_get", "resp 0 <page_id> <section> <page_name> <s1> <s2> <s3> <s4> <s5> <s6> <s7> <s8>");
   ("param_info", "resp 0 <unit> <scale> <min> <max> <default> <step> <stable_symbol>");
   ("preset_list", "resp <count>");
   ("preset_get", "resp 0 <load_key> <name>");
   ("note_input", "resp 0 <port | ->");
   ("note_on", "resp 0");
   ("note_off", "resp 0");
   ("all_notes_off", "resp 0")]%string.

Definition REC_MOD_HOST_SHAPE : list byte := bstr "resp 0"%string.

Fixpoint shape_lookup (rows : list (list byte * list byte)) (v : list byte) : list byte :=
  match rows with
  | [] => REC_MOD_HOST_SHAPE
  | (nm, rp) :: rows' => if bl_eqb nm v then rp else shape_lookup rows' v
  end.

Definition shape_of (v : list byte) : list byte := shape_lookup shape_table v.

Definition shape_set : list (list byte) := REC_MOD_HOST_SHAPE :: map snd shape_table.

Lemma shape_table_length : length shape_table = 28%nat.
Proof. reflexivity. Qed.

Lemma shape_lookup_in : forall rows v, In (shape_lookup rows v) (REC_MOD_HOST_SHAPE :: map snd rows).
Proof.
  induction rows as [|[nm rp] rows IH]; intros v; [left; reflexivity|].
  cbn [shape_lookup map snd]. destruct (bl_eqb nm v); [right; left; reflexivity|].
  destruct (IH v) as [E|E]; [left; exact E | right; right; exact E].
Qed.

Lemma shape_of_in : forall v, In (shape_of v) shape_set.
Proof. intros v. apply shape_lookup_in. Qed.

Definition shape_ok (s : list byte) : bool :=
  (Z.of_nat (length (inst s)) <=? 28) && (Z.of_nat (length s) <=? 78) && nz s.

Lemma shape_set_ok : forallb shape_ok shape_set = true.
Proof. vm_compute. reflexivity. Qed.

Lemma shape_set_facts : forall s, In s shape_set ->
  fits s /\ (length (inst s) <= 28)%nat /\ (length s <= 78)%nat /\ no0 s.
Proof.
  intros s Hs. pose proof shape_set_ok as H. rewrite forallb_forall in H. specialize (H s Hs).
  unfold shape_ok in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply no0_nz in H3.
  unfold fits, PHD_LINE_MAX. repeat split; [lia | lia | lia | exact H3].
Qed.

Lemma fits_shape_set : forall s, In s shape_set -> fits s.
Proof. intros s Hs. apply (shape_set_facts s Hs). Qed.

Lemma shape_of_facts : forall v,
  fits (shape_of v) /\ (length (inst (shape_of v)) <= 28)%nat /\ (length (shape_of v) <= 78)%nat /\ no0 (shape_of v).
Proof. intros v. apply shape_set_facts. apply shape_of_in. Qed.

Definition rec_codes : list Z :=
  [-1; -2; -3; -4;
   -101; -102; -103; -104; -105;
   -201; -202; -203; -204; -205; -206; -207;
   -301; -302; -303; -304; -305;
   -401; -402; -403; -404;
   -901; -902;
   -501; -502; -503; -504; -505; -506; -507; -508; -509; -510;
   -511; -512; -513; -514; -515; -516; -517; -518; -519; -520;
   -521; -522; -523; -524; -525; -526; -527; -528; -529; -530; -531].

Definition declared (c : Z) : bool := existsb (Z.eqb c) rec_codes.

Lemma rec_codes_length : length rec_codes = 58%nat.
Proof. reflexivity. Qed.

Lemma declared_range : forall c, declared c = true -> -2^31 <= c < 0.
Proof.
  intros c H. unfold declared in H. apply existsb_exists in H as (v & Hv & E). apply Z.eqb_eq in E. subst c.
  assert (HA : forallb (fun v => (-2^31 <=? v) && (v <? 0)) rec_codes = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in HA. specialize (HA v Hv). apply andb_prop in HA as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
