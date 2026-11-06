(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac mlia := first [ lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; nia ].

(* [comment removed for export] *)
Definition kept (P : Prop) : Prop := P.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac hide H := (lazymatch type of H with ?T__ => change (kept T__) in H end).
Ltac unhide H := (lazymatch type of H with kept ?T__ => change T__ in H | _ => idtac end).
Ltac unhide_all := repeat match goal with H : kept _ |- _ => unhide H end.

(* [comment removed for export] *)
Lemma mapped_munch : forall W (m m' : word -> option byte) a n,
  munch W m m' -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  (forall i, (0 <= i < n)%Z -> outside W (a + i)%Z) ->
  mapped m a n -> mapped m' a n.
Proof.
  intros W m m' a n MU Ha Hn OUT MP i Hi.
  unfold munch in MU. rewrite (MU (Z_to_bv 64 (a + i))).
  - apply MP. exact Hi.
  - rewrite unsigned_lit by lia. apply OUT. exact Hi.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kShadowOffset_val : kShadowOffset = 2147450880.
Proof. reflexivity. Qed.

Lemma shr3_div8 : forall a, Z.shiftr a 3 = a / 8.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma land7_mod8 : forall a, 0 <= a -> Z.land a 7 = a mod 8.
Proof. intros a Ha. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b). exact H. Qed.

Lemma bv_signed_byte_small : forall b : byte, bv_unsigned b <= 127 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. pose proof (byte_range b).
  unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  rewrite Z.mod_small; lia.
Qed.

Lemma sxb_unsigned : forall b : byte, bv_unsigned b <= 127 -> bv_unsigned (sxb b) = bv_unsigned b.
Proof.
  intros b Hb. pose proof (byte_range b). unfold sxb. rewrite (bv_signed_byte_small b Hb).
  apply unsigned_lit. lia.
Qed.

Lemma sxb_signed_small : forall b : byte, bv_unsigned b <= 127 -> bv_signed (sxb b) = bv_unsigned b.
Proof.
  intros b Hb. pose proof (byte_range b). unfold sxb. rewrite (bv_signed_byte_small b Hb).
  apply signed_lit. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma signed_land7 : forall a, 0 <= a -> bv_signed (Z_to_bv 64 (Z.land a 7)) = a mod 8.
Proof.
  intros a Ha. rewrite land7_mod8 by lia. pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
  apply signed_lit. lia.
Qed.

Lemma signed_land7_add : forall a c, 0 <= a -> 0 <= c <= 8 ->
  bv_signed (Z_to_bv 64 (Z.land a 7 + c)) = a mod 8 + c.
Proof.
  intros a c Ha Hc. rewrite land7_mod8 by lia. pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
  apply signed_lit. lia.
Qed.

Lemma unsigned_land7 : forall a, 0 <= a -> bv_unsigned (Z_to_bv 64 (Z.land a 7)) = a mod 8.
Proof.
  intros a Ha. rewrite land7_mod8 by lia. pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
  apply unsigned_lit. lia.
Qed.

(* [comment removed for export] *)
Definition shadow_val_ok (b : byte) (a k : Z) : Prop :=
  bv_unsigned b = 0 \/ (1 <= bv_unsigned b <= 7 /\ a mod 8 + k <= bv_unsigned b).

Lemma shadow_val_ok_zero : forall a k, shadow_val_ok (Z_to_bv 8 0) a k.
Proof. intros. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma shpat_nth_full : forall n i, 0 <= n -> 0 <= i < n / 8 ->
  nth_error (shpat n) (Z.to_nat i) = Some (Z_to_bv 8 0).
Proof.
  intros n i Hn Hi. unfold shpat. rewrite nth_error_app1 by (rewrite repeat_length; lia).
  apply nth_error_repeat. lia.
Qed.

Lemma shpat_nth_tail : forall n, 0 <= n -> n mod 8 <> 0 ->
  nth_error (shpat n) (Z.to_nat (n / 8)) = Some (Z_to_bv 8 (n mod 8)).
Proof.
  intros n Hn Hm. unfold shpat. rewrite nth_error_app2 by (rewrite repeat_length; lia).
  rewrite repeat_length, Nat.sub_diag. destruct (Z.eqb_spec (n mod 8) 0); [lia | reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SHMAX : Z := 17594332446720.   (* [comment removed for export] *)

Lemma SHMAX_below_highmem : SHMAX + 1048576 = kHighMemBeg.
Proof. reflexivity. Qed.
Lemma SHMAX_val : SHMAX = 17594332446720.
Proof. reflexivity. Qed.

Section CEILNUM.
Context {Clg : Ceiling}.
Lemma alloc_ceiling_num : 140735332483072 <= alloc_ceiling <= 140737479966720.
Proof. exact alloc_ceiling_val. Qed.

Lemma sh_mono : forall a b, a <= b -> sh a <= sh b.
Proof. intros. unfold sh. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

Lemma sh_bound : forall p n, 0 <= p -> 0 <= n -> p + n <= alloc_ceiling ->
  0 <= sh p /\ sh p + (n + 7) / 8 <= SHMAX /\ SHMAX + 8 <= alloc_ceiling.
Proof.
  intros p n Hp Hn Hpn. pose proof alloc_ceiling_num. unfold sh, kShadowOffset, SHMAX.
  Z.div_mod_to_equations. lia.
Qed.

Lemma shpat_sh_bound : forall p n, 0 <= p -> 0 <= n -> p + n <= alloc_ceiling ->
  0 <= sh p /\ sh p + Z.of_nat (length (shpat n)) <= SHMAX /\ SHMAX + 8 <= alloc_ceiling.
Proof. intros p n Hp Hn H. rewrite shpat_length by lia. apply sh_bound; lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sh_word_bound : forall a, 0 <= a -> a < alloc_ceiling ->
  0 <= sh a - sh a mod 8 /\ sh a - sh a mod 8 + 8 <= SHMAX + 8.
Proof.
  intros a Ha H. pose proof alloc_ceiling_num. unfold sh, kShadowOffset, SHMAX.
  Z.div_mod_to_equations. lia.
Qed.

End CEILNUM.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Reads.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Lemma shadow_read_nth : forall m p bs a i b,
    bytes_at segs m (sh p) bs -> p mod 8 = 0 ->
    nth_error bs (Z.to_nat i) = Some b -> 0 <= i -> 8 * i <= a - p < 8 * i + 8 ->
    ov_read_bytes segs m (Z_to_bv 64 (a / 8 + kShadowOffset)) 1 = Some [b].
  Proof.
    intros m p bs a i b SH Hal Hn Hi Hr.
    assert (E : a / 8 + kShadowOffset = sh p + i).
    { unfold sh. Z.div_mod_to_equations. nia. }
    rewrite E. apply (u8ro_read segs m (sh p) bs i b); [exact SH | exact Hn | exact Hi | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma shadow_read_zero : forall m p (N : nat) a k,
    bytes_at segs m (sh p) (repeat (Z_to_bv 8 0) N) -> p mod 8 = 0 ->
    p <= a -> a + k <= p + 8 * Z.of_nat N -> 1 <= k ->
    ov_read_bytes segs m (Z_to_bv 64 (a / 8 + kShadowOffset)) 1 = Some [Z_to_bv 8 0].
  Proof.
    intros m p N a k SH Hal Hlo Hhi Hk.
    apply (shadow_read_nth m p _ a ((a - p) / 8) _ SH Hal).
    - apply nth_error_repeat. Z.div_mod_to_equations. nia.
    - Z.div_mod_to_equations. nia.
    - Z.div_mod_to_equations. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma shadow_read_obj : forall m p n a k,
    bytes_at segs m (sh p) (shpat n) -> p mod 8 = 0 ->
    p <= a -> a + k <= p + n -> 1 <= k -> a mod 8 + k <= 8 ->
    exists b, ov_read_bytes segs m (Z_to_bv 64 (a / 8 + kShadowOffset)) 1 = Some [b]
              /\ shadow_val_ok b a k.
  Proof.
    intros m p n a k SH Hal Hlo Hhi Hk Hgr.
    set (i := (a - p) / 8).
    assert (Hi : 0 <= i /\ 8 * i <= a - p < 8 * i + 8) by (unfold i; Z.div_mod_to_equations; nia).
    assert (Hn : 0 <= n) by lia.
    destruct (Z_lt_le_dec i (n / 8)) as [Hfull | Htail].
    - exists (Z_to_bv 8 0). split; [| apply shadow_val_ok_zero].
      apply (shadow_read_nth m p (shpat n) a i); [exact SH | exact Hal | apply shpat_nth_full; lia | lia | lia].
    - assert (Hm : n mod 8 <> 0 /\ i = n / 8 /\ a mod 8 + k <= n mod 8).
      { unfold i in *. Z.div_mod_to_equations. nia. }
      destruct Hm as (Hm & Ei & Hok).
      exists (Z_to_bv 8 (n mod 8)). split.
      + apply (shadow_read_nth m p (shpat n) a i); [exact SH | exact Hal | rewrite Ei; apply shpat_nth_tail; lia | lia | lia].
      + right. pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
        assert (Eb : bv_unsigned (Z_to_bv 8 (n mod 8)) = n mod 8).
        { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. }
        rewrite Eb. lia.
  Qed.
End Reads.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sb_facts SOK :=
  lazymatch type of SOK with shadow_val_ok ?b ?a ?k =>
    let BR := fresh "SBR" in pose proof (byte_range b) as BR;
    let MB := fresh "SMB" in
    first [ pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as MB | idtac ]
  end.

(* [comment removed for export] *)
Ltac sb_norm b a :=
  repeat match goal with
  | H : context [bv_unsigned (sxb b)] |- _ => rewrite (sxb_unsigned b) in H by lia
  | H : context [bv_signed (sxb b)] |- _ => rewrite (sxb_signed_small b) in H by lia
  | H : context [bv_signed (Z_to_bv 64 (Z.land a 7 + ?c))] |- _ => rewrite (signed_land7_add a c) in H by lia
  | H : context [bv_signed (Z_to_bv 64 (Z.land a 7))] |- _ => rewrite (signed_land7 a) in H by lia
  | H : context [bv_unsigned (Z_to_bv 64 (Z.land a 7))] |- _ => rewrite (unsigned_land7 a) in H by lia
  | H : context [bv_unsigned (Z_to_bv 64 (bv_unsigned b))] |- _ => rewrite (unsigned_lit (bv_unsigned b)) in H by lia
  end.

(* [comment removed for export] *)
Ltac shadow_dead :=
  exfalso;
  match goal with SOK : shadow_val_ok ?b ?a ?k |- _ =>
    sb_facts SOK;
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; sb_norm b a; mlia
  end.

(* [comment removed for export] *)
Ltac shadow_addr_at SRC X k :=
  lazymatch type of SRC with
  | bytes_at ?segs ?v (sh ?p) (shpat ?n) =>
      let b := fresh "sb" in let RD := fresh "SRD" in let OK := fresh "SOK" in
      destruct (shadow_read_obj segs v p n X k SRC ltac:(mlia) ltac:(mlia) ltac:(mlia) ltac:(mlia) ltac:(mlia))
        as (b & RD & OK);
      rewrite kShadowOffset_val in RD
  | bytes_at ?segs ?v (sh ?p) (shpat ?n ++ ?rest) =>
      let b := fresh "sb" in let RD := fresh "SRD" in let OK := fresh "SOK" in
      destruct (shadow_read_obj segs v p n X k (proj1 (proj1 (bytes_at_app segs v (sh p) (shpat n) rest) SRC))
                  ltac:(mlia) ltac:(mlia) ltac:(mlia) ltac:(mlia) ltac:(mlia))
        as (b & RD & OK);
      rewrite kShadowOffset_val in RD
  | bytes_at ?segs ?v (sh ?p) (repeat (Z_to_bv 8 0) ?N) =>
      let RD := fresh "SRD" in
      pose proof (shadow_read_zero segs v p N X k SRC ltac:(mlia) ltac:(mlia) ltac:(mlia) ltac:(mlia)) as RD;
      rewrite kShadowOffset_val in RD
  | _ => fail "shadow_addr: the source must be  bytes_at segs v (sh p) (shpat n [++ _] | repeat (Z_to_bv 8 0) N)"
  end.

Ltac shadow_addr SRC k :=
  lazymatch goal with |- context [Z_to_bv 64 (Z.shiftr ?X 3 + ?off)] =>
    rewrite (shr3_div8 X); try rewrite kShadowOffset_val;
    shadow_addr_at SRC X k
  | |- _ => fail "shadow_addr: no  Z_to_bv 64 (Z.shiftr X 3 + off)  in the goal (are we right after srli;add?)"
  end.

(* [comment removed for export] *)
Ltac shadow_fast K := lazymatch type of K with (_ = 0)%Z => idtac | (_ = Z0)%Z => idtac end.

Ltac shadow_cleanup :=
  try match goal with SOK : shadow_val_ok _ _ _ |- _ => clear SOK end;
  try match goal with RD : ov_read_bytes _ _ _ 1 = Some [_] |- _ => clear RD end.

(* [comment removed for export] *)
Ltac shadow_chk0 SRC k :=
  zstep; zstep; shadow_addr SRC k; zstep;
  let K := fresh "KS" in
  zstep; if_cases K; zify_cond K;
  [ first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead
          | fail 1 "shadow_chk0: could not prove the report branch dead (shadow byte not provably 0?)" ]
  | first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead
          | fail 1 "shadow_chk0: could not prove the report branch dead (shadow byte not provably 0?)" ] ].

(* [comment removed for export] *)
Ltac shadow_join U :=
  apply evt_done;
  lazymatch goal with
  | |- ?P (MS ?R ?F ?pc ?fc None ?m ?rom) =>
    first [ is_evar P; unify P (fun ms : machine_state => exists x : word, ms = MS (bvmap_set (Z_to_bv 5 U) x R) F pc fc None m rom)
          | idtac ];
    cbv beta; eexists; simp_regs; reflexivity
  | |- _ => (* [comment removed for export] *)
    cbv beta; eexists; simp_regs; reflexivity
  end.

(* [comment removed for export] *)
Ltac shadow_slow U :=
  zstep;
  let K2 := fresh "KS2" in
  first [ zstep; if_cases K2; zify_cond K2
        | zstep; zstep; if_cases K2; zify_cond K2 ];
  [ first [ shadow_dead | shadow_join U ] | first [ shadow_dead | shadow_join U ] ].

(* [comment removed for export] *)
Ltac shadow_chk SRC k U :=
  zstep; zstep; shadow_addr SRC k;
  lazymatch goal with |- evt ?segs ?Q _ =>
    eapply (evt_cut segs _ Q);
    [ zstep;
      let K := fresh "KS" in
      zstep; if_cases K; zify_cond K;
      [ first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ]
      | first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ] ]
    | let ms := fresh "ms" in let x := fresh "junk" in
      intros ms [x ->]; simp_regs ]
  end;
  shadow_cleanup.

(* [comment removed for export] *)
Ltac shadow_rechk0 SRC X k :=
  shadow_addr_at SRC X k; zstep;
  let K := fresh "KS" in
  zstep; if_cases K; zify_cond K;
  [ first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead
          | fail 1 "shadow_rechk0: could not prove the report branch dead" ]
  | first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead
          | fail 1 "shadow_rechk0: could not prove the report branch dead" ] ].

Ltac shadow_rechk SRC X k U :=
  shadow_addr_at SRC X k;
  lazymatch goal with |- evt ?segs ?Q _ =>
    eapply (evt_cut segs _ Q);
    [ zstep;
      let K := fresh "KS" in
      zstep; if_cases K; zify_cond K;
      [ first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ]
      | first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ] ]
    | let ms := fresh "ms" in let x := fresh "junk" in
      intros ms [x ->]; simp_regs ]
  end;
  shadow_cleanup.

(* [comment removed for export] *)
Tactic Notation "shadow_ld" constr(SRC) constr(k) := shadow_chk0 SRC k.
Tactic Notation "shadow_ld_slow" constr(SRC) constr(k) constr(U) := shadow_chk SRC k U.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac icall_consts_in H := idtac.
Ltac atac_head_of t := lazymatch t with ?f _ => atac_head_of f | _ => t end.
Ltac post_icall segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  (let T := type of PO in let h := atac_head_of T in try unfold h in PO);
  icall_consts_in PO;
  rewrite ?unsigned_lit in PO by lia;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Tactic Notation "icall" uconstr(SPEC) "by" tactic3(side) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC; side | post_icall segs m ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section GoStop.
  Context {Clg : Ceiling} {L : clayout} {AI : AsanAlloc L}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma ago_lemma : forall (A : AS) R F pc fc m rom md T,
    ainv A m md ->
    evt (cl_segs L) (srz_at_r (cl_segs L) (ahull A) (alhull A) (aeager A) m md T)
        (MS R F pc fc None (aview A m) rom) ->
    srealizes (cl_segs L) (mkCfg (MS R F pc fc None m rom) md) T.
  Proof.
    intros A R F pc fc m rom md T AINV EV. destruct (as_minv L A m md AINV) as [MI Hh].
    apply (srz_go_restrict (cl_segs L) (ahull A) (as_hull_segs L A m md AINV) (as_wx L) (alhull A) (aeager A)
             (MS R F pc fc None m rom) md T MI Hh).
    rewrite restrict_MS. exact EV.
  Qed.

  (* [comment removed for export] *)
  Lemma astop_lemma : forall (A : AS) m md T W R F pc fc (v' : mem) rom,
    ainv A m md ->
    munch W (aview A m) v' -> wmono (cl_segs L) (aview A m) v' -> client_fp L A (aview A m) W ->
    (forall (m1 : mem) (md1 : Model),
        ainv A m1 md1 -> aview A m1 = v' -> same_but_materialized md md1 ->
        (forall a, hidc (ahull A) a = true -> m1 a = m a) ->
        srealizes (cl_segs L) (mkCfg (MS R F pc fc None m1 rom) md1) T) ->
    evt (cl_segs L) (srz_at_r (cl_segs L) (ahull A) (alhull A) (aeager A) m md T) (MS R F pc fc None v' rom).
  Proof.
    intros A m md T W R F pc fc v' rom AINV MU WM CF K.
    apply srz_stop_restrict. intros md1 MI1 SB HC. rewrite unrestrict_MS.
    assert (HC' : forall a, hidc (ahull A) a = true -> v' a = None) by exact HC.
    apply K.
    - exact (ainv_munch L A m md md1 v' W AINV MU WM CF HC' MI1 SB).
    - apply aview_recombine. exact HC'.
    - exact SB.
    - intros a Ha. apply munrestrict_hidden. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma astop_rel1_lemma : forall (A : AS) m md T W R F pc fc (v' : mem) rom ff k age (faw : word),
    ainv A m md -> a_frame A ff = Some (k, age) ->
    bytes_at (cl_segs L) (aview A m) (ff + fsize k - 8) (le8 faw) ->
    munch W (aview A m) v' -> wmono (cl_segs L) (aview A m) v' -> client_fp_rel L A [ff] (aview A m) W ->
    v' faw = Some (Z_to_bv 8 0) ->
    (forall (m1 : mem) (md1 : Model),
        ainv (a_release A ff) m1 md1 -> aview (a_release A ff) m1 = v' -> same_but_materialized md md1 ->
        (forall a, hidc (ahull A) a = true -> m1 a = m a) ->
        srealizes (cl_segs L) (mkCfg (MS R F pc fc None m1 rom) md1) T) ->
    evt (cl_segs L) (srz_at_r (cl_segs L) (ahull A) (alhull A) (aeager A) m md T) (MS R F pc fc None v' rom).
  Proof.
    intros A m md T W R F pc fc v' rom ff k age faw AINV HF FB MU WM CF FL K.
    apply srz_stop_restrict. intros md1 MI1 SB HC. rewrite unrestrict_MS.
    assert (HC' : forall a, hidc (ahull A) a = true -> v' a = None) by exact HC.
    apply K.
    - change (a_release A ff) with (fold_left a_release [ff] A).
      apply (ainv_munch_release L A [ff] m md md1 v' W AINV); try assumption.
      + intros ff0 [<-|[]]. exists k, age. exact HF.
      + constructor; [| constructor]. intros HIN. inversion HIN.
      + intros ff0 k0 age0 faw0 [<-|[]] HF0 FB0.
        rewrite HF in HF0. injection HF0 as <- <-.
        pose proof (bytes_at_same L _ _ _ _ FB0 FB ltac:(rewrite !length_le8; reflexivity)) as E8.
        apply le8_inj in E8. subst faw0. exact FL.
    - rewrite (aview_release1 L A m md ff k age _ AINV HF). apply aview_recombine. exact HC'.
    - exact SB.
    - intros a Ha. apply munrestrict_hidden. exact Ha.
  Qed.
End GoStop.

(* [comment removed for export] *)
Ltac ago AINV :=
  lazymatch type of AINV with @ainv _ ?L ?AI ?A ?m ?md =>
    first [ apply (ago_lemma (L:=L) A _ _ _ _ m _ md _ AINV)
          | fail 1 "ago: goal is not  srealizes (cl_segs L) (mkCfg (MS R F pc fc None m rom) md) T  for the m/md of" AINV ]
  end.

(* [comment removed for export] *)
Ltac astop AINV MU WM CF :=
  lazymatch type of AINV with @ainv _ ?L ?AI ?A ?m ?md =>
    apply (astop_lemma (L:=L) A m md _ _ _ _ _ _ _ _ AINV MU WM CF);
    let m1 := fresh "m" in let md1 := fresh "md" in
    let A1 := fresh "AINV" in let EV := fresh "EVIEW" in let SB := fresh "SBM" in let HID := fresh "HID" in
    intros m1 md1 A1 EV SB HID;
    first [ subst_view EV | rewrite <- EV in *; clear EV ]
  end
with subst_view EV :=
  lazymatch type of EV with ?av = ?v' => is_var v'; subst v' end.

(* [comment removed for export] *)
Ltac astop_rel1 AINV HF FB MU WM CF FL :=
  lazymatch type of AINV with @ainv _ ?L ?AI ?A ?m ?md =>
    apply (astop_rel1_lemma (L:=L) A m md _ _ _ _ _ _ _ _ _ _ _ _ AINV HF FB MU WM CF FL);
    let m1 := fresh "m" in let md1 := fresh "md" in
    let A1 := fresh "AINV" in let EV := fresh "EVIEW" in let SB := fresh "SBM" in let HID := fresh "HID" in
    intros m1 md1 A1 EV SB HID;
    first [ subst_view EV | rewrite <- EV in *; clear EV ]
  end.

Ltac astop0 AINV :=
  lazymatch type of AINV with @ainv _ ?L ?AI ?A ?m ?md =>
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?v' _) =>
      let MU := fresh "MU" in let WM := fresh "WM" in let CF := fresh "CF" in
      pose proof (munch_refl [] (aview A m) : munch [] (aview A m) v') as MU;
      pose proof (wmono_refl segs (aview A m) : wmono segs (aview A m) v') as WM;
      pose proof (I : client_fp L A (aview A m) []) as CF;
      astop AINV MU WM CF; clear MU WM CF
    end
  end.

(* [comment removed for export] *)
Section GoStopTest.
  Context {Clg : Ceiling} {L : clayout} {AI : AsanAlloc L}.   (* [comment removed for export] *)
  Goal forall (A : AS) R F pc fc m md T,
    ainv A m md ->
    (forall m1 md1, ainv A m1 md1 -> same_but_materialized md md1 ->
       srealizes (cl_segs L) (mkCfg (MS R F pc fc None m1 (seg_rom (cl_segs L))) md1) T) ->
    srealizes (cl_segs L) (mkCfg (MS R F pc fc None m (seg_rom (cl_segs L))) md) T.
  Proof.
    intros A R F pc fc m md T AINV K.
    ago AINV.
    astop0 AINV.
    apply K; assumption.
  Qed.
End GoStopTest.
