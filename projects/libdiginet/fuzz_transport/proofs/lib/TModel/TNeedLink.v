(* TNeed.v transcribed three C functions before the shared model held them. The shared DgnLink.v now models
   each of them over list Z buffers (C pointers as offsets). The lemmas below say that TNeed's reading is DgnLink's
   reading of the same bytes (zs of TNeed's byte lists), so TNeed's definitions stay and every use of them
   carries over to DgnLink's model:
   - spec_build_frame_link: TNeed.spec_build_frame (fuzz/spec.h:228-247) is DgnLink.spec_build_frame. On the way,
     tneed_spec_build_frame: TNeed's statement-by-statement writes give DgnSpec.build_frame.
   - frame_build_code_link: TNeed.diginet_frame_build_code (diginet_frame.c:100-111) is the code (the first
     component) of DgnLink.diginet_frame_build, for every dst, src and header.
   - personality_from_name_link: TNeed.diginet_personality_from_name, which takes the bytes before the NUL, is
     DgnLink.diginet_personality_from_name of the char array: those bytes, the NUL, then any bytes. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnLink.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TNeed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* ---- z_list_eqb is list equality ---- *)

Lemma z_list_eqb_eq : forall x y, z_list_eqb x y = true <-> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y]; cbn [z_list_eqb]; try (split; intros H; discriminate H).
  - split; intros _; reflexivity.
  - rewrite andb_true_iff, Z.eqb_eq, IH. split; [intros [-> ->]; reflexivity | intros E; injection E as -> ->; split; reflexivity].
Qed.

(* ---- spec_build_frame ---- *)

Lemma tnl_skipn_repeat : forall (x : byte) k m, skipn k (repeat x m) = repeat x (m - k).
Proof.
  induction k as [|k IH]; intros m; [rewrite Nat.sub_0_r; reflexivity|].
  destruct m as [|m]; [reflexivity|]. cbn [repeat skipn]. rewrite IH. reflexivity.
Qed.

(* upd at the end p of the bytes written so far, into the zeros of the memset *)
Lemma tnl_upd_tail : forall (p v : list byte) (m : nat) (k : Z), k = Z.of_nat (length p) -> (length v <= m)%nat ->
  upd (p ++ repeat (b8 0) m) k v = (p ++ v) ++ repeat (b8 0) (m - length v).
Proof.
  intros p v m k -> Hm. unfold upd. rewrite Nat2Z.id.
  rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all.
  rewrite skipn_app, (skipn_all2 p) by lia. cbn [app].
  replace (length p + length v - length p)%nat with (length v) by lia.
  rewrite tnl_skipn_repeat, app_assoc. reflexivity.
Qed.

Lemma tnl_put16_mod32 : forall v, put16 (v mod 2 ^ 32) = put16 v.
Proof. intros v. unfold put16. rewrite (b8_div_mod v 8 32), (b8_mod_w v 32) by lia. reflexivity. Qed.

(* TNeed's writes, :232-246, are DgnSpec.v's build_frame (zero_sum as the bool zero_sum <> 0, :238), and n is
   frame_len *)
Lemma tneed_spec_build_frame : forall dst src send ack retry cmd ncmds body zero_sum,
  length dst = 6%nat -> length src = 6%nat ->
  spec_build_frame dst src send ack retry cmd ncmds body zero_sum =
  (build_frame dst src send ack retry cmd ncmds body (negb (zero_sum =? 0)), frame_len (length body)).
Proof.
  intros dst src send ack retry cmd ncmds body zero_sum Hd Hs.
  assert (HN : Z.to_nat (if 30 + Z.of_nat (length body) <? 60 then 60 else 30 + Z.of_nat (length body)) =
               (30 + length body + (30 - length body))%nat)
    by (destruct (Z.ltb_spec (30 + Z.of_nat (length body)) 60); lia).
  assert (Hn : (if 30 + Z.of_nat (length body) <? 60 then 60 else 30 + Z.of_nat (length body)) =
               frame_len (length body))
    by (unfold frame_len; destruct (Z.ltb_spec (30 + Z.of_nat (length body)) 60); lia).
  unfold spec_build_frame; cbv zeta. rewrite HN, Hn.
  change (repeat (b8 0) (30 + length body + (30 - length body)))
    with ([] ++ repeat (b8 0) (30 + length body + (30 - length body))).
  rewrite !tnl_upd_tail
    by (rewrite ?length_app, ?length_firstn, ?length_put16, ?length_put32, ?Hd, ?Hs; cbn [length]; lia).
  rewrite (firstn_all2 dst) by lia. rewrite (firstn_all2 src) by lia. rewrite tnl_put16_mod32.
  assert (Ez : (if zero_sum =? 0 then spec_sum body else 0) = (if negb (zero_sum =? 0) then 0 else spec_sum body))
    by (destruct (zero_sum =? 0); reflexivity).
  rewrite Ez. clear Ez.
  f_equal.
  destruct (Z.of_nat (length body) =? 0) eqn:E; cbn beta iota.
  - apply Z.eqb_eq in E. destruct body as [|x body]; [|cbn [length] in E; lia].
    match goal with |- context [repeat (b8 0) ?m] =>
      replace m with 30%nat by (rewrite ?length_put16, ?length_put32, ?Hd, ?Hs; cbn [length]; lia) end.
    unfold build_frame. rewrite <- !app_assoc. reflexivity.
  - match goal with |- context [repeat (b8 0) ?m] =>
      replace m with (30 - length body)%nat by (rewrite ?length_put16, ?length_put32, ?Hd, ?Hs; cbn [length]; lia)
    end.
    unfold build_frame. rewrite <- !app_assoc. reflexivity.
Qed.

(* TNeed.spec_build_frame is DgnLink.spec_build_frame on the bytes of the MACs and the body: the same n,
   and the bytes it writes *)
Lemma spec_build_frame_link : forall dst src send ack retry cmd ncmds body zero_sum,
  length dst = 6%nat -> length src = 6%nat -> 0 <= cmd < 256 -> 0 <= ncmds < 256 ->
  DgnLink.spec_build_frame (zs dst) (zs src) send ack retry cmd ncmds (zs body) (Z.of_nat (length body)) zero_sum =
  (snd (spec_build_frame dst src send ack retry cmd ncmds body zero_sum),
   zs (fst (spec_build_frame dst src send ack retry cmd ncmds body zero_sum))).
Proof.
  intros dst src send ack retry cmd ncmds body zero_sum Hd Hs Hc Hn.
  rewrite tneed_spec_build_frame by assumption. cbn [fst snd].
  exact (DgnLink.spec_build_frame_build_frame dst src send ack retry cmd ncmds body zero_sum Hd Hs Hc Hn).
Qed.

(* ---- diginet_frame_build's code ---- *)

Lemma frame_build_code_link : forall cap dst src h body mode,
  diginet_frame_build_code body cap mode =
  fst (DgnLink.diginet_frame_build cap dst src h (zs body) (Z.of_nat (length body)) mode).
Proof.
  intros cap dst src h body mode.
  assert (Eb : diginet_body_check (zs body) (Z.of_nat (length body)) = body_check body)
    by exact (diginet_body_check_body_check (map bz body) body (holds_body_map body)).
  assert (Eo : (if DgnLink.DIGINET_BODY_OFFSET + Z.of_nat (length body) <? DgnLink.DIGINET_MIN_FRAME_LEN
                then DgnLink.DIGINET_MIN_FRAME_LEN else DgnLink.DIGINET_BODY_OFFSET + Z.of_nat (length body)) =
               frame_len (length body))
    by (unfold frame_len, DgnLink.DIGINET_BODY_OFFSET, DgnLink.DIGINET_MIN_FRAME_LEN;
        destruct (Z.ltb_spec (30 + Z.of_nat (length body)) 60); lia).
  unfold diginet_frame_build_code, DgnLink.diginet_frame_build, lib_build_code; cbv zeta.
  rewrite Eb, Eo.
  unfold DgnLink.DIGINET_SUM_BODY, DgnLink.DIGINET_SUM_ZERO, DgnLink.DIGINET_MAX_BODY_LEN, DIGINET_OK.
  destruct (negb ((mode =? 0) || (mode =? 1))); [reflexivity|].
  destruct (1484 <? Z.of_nat (length body)); [reflexivity|].
  destruct (negb (body_check body =? 0)); [reflexivity|].
  destruct (cap <? frame_len (length body)); reflexivity.
Qed.

(* ---- diginet_personality_from_name ---- *)

(* strcmp of a string x (then its NUL, then anything) with a string s (then its NUL), neither holding a NUL, is
   list equality *)
Lemma tnl_strcmp_eq_list : forall (x tx s : list Z),
  (forall j, 0 <= j < Z.of_nat (length x) -> byte_at x j <> 0) ->
  (forall j, 0 <= j < Z.of_nat (length s) -> byte_at s j <> 0) ->
  DgnLink.strcmp_eq (x ++ 0 :: tx) (s ++ [0]) 0 (S (length s)) = z_list_eqb x s.
Proof.
  intros x tx s Hx Hs. apply Bool.eq_true_iff_eq. rewrite z_list_eqb_eq.
  rewrite (DgnLink.lnk_strcmp_eq (x ++ 0 :: tx) (s ++ [0]) (Z.of_nat (length x)) (Z.of_nat (length s))
             (S (length s)) 0);
    [ | lia | lia
      | intros j Hj; rewrite DgnLink.lnk_byte_at_app_l by lia; apply Hx; lia
      | rewrite DgnLink.lnk_byte_at_app_r by lia; rewrite Z.sub_diag; reflexivity
      | intros j Hj; rewrite DgnLink.lnk_byte_at_app_l by lia; apply Hs; lia
      | rewrite DgnLink.lnk_byte_at_app_r by lia; rewrite Z.sub_diag; reflexivity
      | lia ].
  split.
  - intros [Hk Hj]. apply nth_ext with (d := 0) (d' := 0); [lia|]. intros k Hk'.
    specialize (Hj (Z.of_nat k) ltac:(lia)).
    rewrite !DgnLink.lnk_byte_at_app_l in Hj by lia. unfold byte_at in Hj. rewrite Nat2Z.id in Hj. exact Hj.
  - intros ->. split; [reflexivity|]. intros j Hj. rewrite !DgnLink.lnk_byte_at_app_l by lia. reflexivity.
Qed.

Lemma personality_from_name_link : forall (name : list byte) (tail : list Z),
  (forall i, (i < length name)%nat -> at8 name i <> 0) ->
  diginet_personality_from_name name = DgnLink.diginet_personality_from_name (zs name ++ 0 :: tail).
Proof.
  intros name tail Hn.
  assert (Hx : forall j, 0 <= j < Z.of_nat (length (zs name)) -> byte_at (zs name) j <> 0).
  { intros j Hj. unfold zs in Hj. rewrite length_map in Hj. replace j with (Z.of_nat (Z.to_nat j)) by lia.
    change (zs name) with (map bz name). rewrite DgnLink.lnk_byte_at_map_bz. apply Hn. lia. }
  rewrite DgnLink.lnk_from_name_cases.
  rewrite !tnl_strcmp_eq_list by (first [exact Hx | apply DgnLink.lnk_no_nul; vm_compute; reflexivity]).
  reflexivity.
Qed.
