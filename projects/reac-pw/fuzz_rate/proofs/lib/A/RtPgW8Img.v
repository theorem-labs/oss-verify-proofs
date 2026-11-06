(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Seg.v at 164759458cdd; w5_img_gen's method (an image rebuilt from its parts) written new for rate's pod step: buf grown by x, len, and the entry area and n_ent when the step records an entry. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a): the bytes of the first block after one pod
   of the params Struct is written (pod_put of its bytes, the len store) and, when the Struct is the first params
   property, recorded (pp->ent[pp->n_ent++] = e, pod.h:432). Proves no function (kind: model lemma).
   - rw8_img_step: the block holds pp_image b ... es before the step; the step writes x at pp + |b|, len, and
     (fi = true) the entry ent_mem ed at ent[|es|] and n_ent; every other byte of the block is unchanged. Then the
     block holds pp_image (b ++ x) ... (es ++ [ed] when fi, es otherwise). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v YK04 YG0n YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the lengths of the image's parts *)
Ltac rw8_len := repeat first [ rewrite length_app | rewrite length_zeros | rewrite length_le32 | rewrite length_le64
  | rewrite length_flat_ent_mem by assumption | rewrite length_ent_mem by assumption ].
Ltac rw8_lenH h := repeat first [ rewrite length_app in h | rewrite length_zeros in h | rewrite length_le32 in h
  | rewrite length_le64 in h | rewrite length_flat_ent_mem in h by assumption
  | rewrite length_ent_mem in h by assumption ].
(* a byte of the block outside the four written ranges: the step's frame hypothesis K *)
Ltac rw8_k K := apply K;
  [ lia | lia | lia
  | first [ intros [? _]; discriminate | intros [_ ?]; lia ]
  | first [ intros [? _]; discriminate | intros [_ ?]; lia ] ].

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

Lemma rw8_at : forall H mem a a' l, rtm_bytes segs H mem a l -> a' = a -> rtm_bytes segs H mem a' l.
Proof. intros H mem a a' l B E. rewrite E. exact B. Qed.

Lemma rw8_kept_at : forall H mem H' mem' a a' l, rtm_bytes segs H mem a l -> a' = a ->
  (forall y, a <= y < a + Z.of_nat (length l) -> aview segs H' mem' y = aview segs H mem y) ->
  rtm_bytes segs H' mem' a' l.
Proof. intros H mem H' mem' a a' l B E K. rewrite E. exact (rtm_bytes_kept segs H mem H' mem' a l B K). Qed.

(* a part of the new image read off the old one at the same address, kept by the step *)
Ltac rw8_kept O K := eapply rw8_kept_at;
  [ exact O | rw8_len; lia
  | let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy; rw8_lenH Hy; rw8_k K ].

Lemma rw8_img_step : forall H mem H' mem' pp (b x : list byte) isp hasp pst (es : list ent) (ed : ent) (fi : bool),
  Z.of_nat (length b) <= POD_BUF_MAX -> Z.of_nat (length b + length x) <= POD_BUF_MAX ->
  (length es <= 32)%nat ->
  (fi = true -> (length es < 32)%nat) ->
  Forall (fun e => (length (e_body e) <= 96)%nat) es -> (length (e_body ed) <= 96)%nat ->
  rtm_bytes segs H mem pp (pp_image b isp hasp pst es false) ->
  rtm_bytes segs H' mem' (pp + Z.of_nat (length b)) x ->
  val_mem segs (mrestrict H' mem') (pp + OFF_LEN) 8 (Z.of_nat (length b + length x)) ->
  (fi = true -> rtm_bytes segs H' mem' (pp + OFF_ENT + ENT_SIZE * Z.of_nat (length es)) (ent_mem ed) /\
                val_mem segs (mrestrict H' mem') (pp + OFF_N_ENT) 4 (Z.of_nat (length es) + 1)) ->
  (forall y, pp <= y < pp + PP_SIZE ->
     ~ (pp + Z.of_nat (length b) <= y < pp + Z.of_nat (length b + length x)) ->
     ~ (pp + OFF_LEN <= y < pp + OFF_LEN + 8) ->
     ~ (fi = true /\ pp + OFF_ENT + ENT_SIZE * Z.of_nat (length es) <= y
                     < pp + OFF_ENT + ENT_SIZE * Z.of_nat (length es) + ENT_SIZE) ->
     ~ (fi = true /\ pp + OFF_N_ENT <= y < pp + OFF_N_ENT + 4) ->
     aview segs H' mem' y = aview segs H mem y) ->
  rtm_bytes segs H' mem' pp (pp_image (b ++ x) isp hasp pst (if fi then es ++ [ed] else es) false).
Proof.
intros H mem H' mem' pp b x isp hasp pst es ed fi Hb Hbx Hes Hes1 Hs Hed Old Nx Nlen Nfi K.
unfold pp_image in Old |- *.
unfold POD_BUF_MAX, POD_ENT_MAX, OFF_LEN, OFF_ENT, ENT_SIZE, OFF_N_ENT, PP_SIZE in *.
(* buf's zero tail: |x| bytes for x, then the new tail *)
assert (Ez1 : zeros (Z.to_nat (16384 - Z.of_nat (length b)))
              = zeros (length x) ++ zeros (Z.to_nat (16384 - Z.of_nat (length b + length x)))).
{ rewrite <- zeros_app. f_equal. lia. }
rewrite Ez1 in Old.
apply rtm_bytes_app in Old as [Ob Old]. apply rtm_bytes_app in Old as [Oz Old].
apply rtm_bytes_app in Oz as [_ Oz1]. apply rtm_bytes_app in Old as [_ Old].
rewrite !length_app.
(* buf, its zero tail, len *)
apply rtm_bytes_app. split.
{ apply rtm_bytes_app. split; [rw8_kept Ob K | exact Nx]. }
apply rtm_bytes_app. split; [rw8_kept Oz1 K|].
apply rtm_bytes_app. split.
{ eapply rw8_at; [unfold le64; apply rtm_bytes_of_val; exact Nlen | rw8_len; lia]. }
destruct fi.
- (* the entry recorded: the flags, ent[0..|es|), the new entry, the zero tail, n_ent, corrupt and the padding *)
  change (if true then es ++ [ed] else es) with (es ++ [ed]).
  pose proof (Hes1 eq_refl) as Hlt. clear Hes1.
  rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r, !length_app. cbn [length].
  replace (Z.of_nat (length es + 1)) with (Z.of_nat (length es) + 1) by lia.
  assert (Ez2 : zeros (Z.to_nat (104 * (32 - Z.of_nat (length es))))
                = zeros 104 ++ zeros (Z.to_nat (104 * (32 - (Z.of_nat (length es) + 1))))).
  { rewrite <- zeros_app. f_equal. lia. }
  rewrite Ez2 in Old.
  apply rtm_bytes_app in Old as [O1 Old]. apply rtm_bytes_app in Old as [O2 Old].
  apply rtm_bytes_app in Old as [O3 Old]. apply rtm_bytes_app in Old as [OF Old].
  apply rtm_bytes_app in Old as [OZ Old]. apply rtm_bytes_app in OZ as [_ OZ2].
  apply rtm_bytes_app in Old as [_ OC].
  destruct (Nfi eq_refl) as [Ne Nn].
  apply rtm_bytes_app. split; [rw8_kept O1 K|].
  apply rtm_bytes_app. split; [rw8_kept O2 K|].
  apply rtm_bytes_app. split; [rw8_kept O3 K|].
  apply rtm_bytes_app. split.
  { apply rtm_bytes_app. split; [rw8_kept OF K|].
    eapply rw8_at; [exact Ne | rw8_len; lia]. }
  apply rtm_bytes_app. split; [rw8_kept OZ2 K|].
  apply rtm_bytes_app. split.
  { eapply rw8_at; [unfold le32; apply rtm_bytes_of_val; exact Nn | rw8_len; lia]. }
  rw8_kept OC K.
- (* no entry recorded: everything after len is the old image's *)
  change (if false then es ++ [ed] else es) with es.
  clear Hes1.
  rw8_kept Old K.
Qed.
End i.

Print Assumptions rw8_img_step.
