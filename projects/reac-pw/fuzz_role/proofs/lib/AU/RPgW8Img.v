(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Seg.v at 164759458cdd; w5_img_gen's method (an image rebuilt from its parts) written new for rate's pod step: buf grown by x, len, and the entry area and n_ent when the step records an entry. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW8Img.v at 8f1d7a0a9084 for the same unit's
   image B (fuzz_rate.asan-ubsan): RtPgMem's rtm_ becomes RtPgMemB's rtmb_ and the prefix rw8_ becomes rbw8_; the
   model step itself is the same (the first block's layout is the shared Pod/Layout's). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgBW8Img.v at 6c65f5a5cf5c for reac-pw/fuzz_role's
   image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role; RtPgMemB's rtmb_ becomes RPgMem's rm_ and the
   prefix rbw8_ becomes w8_; the model step itself is the same (the same pod.h builder, Pod/Layout's layout). *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a): the bytes of the first block after one pod of
   the params Struct is written by the walk piece "write + record" of LLVMFuzzerTestOneInput (J 0x818d8 -> C 0x80b54 /
   CL 0x81ccc: pod_write_ent's bytes and its len store) and, when the Struct is the first params property, recorded
   (pp->ent[pp->n_ent++] = e62, pod.h:432). Proves no function (kind: model lemma).
   - w8_img_step: the block holds pp_image b ... es before the step; the step writes x at pp + |b|, len, and
     (fi = true) the entry ent_mem ed at ent[|es|] and n_ent; every other byte of the block is unchanged. Then the
     block holds pp_image (b ++ x) ... (es ++ [ed] when fi, es otherwise). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v YK04 YG0n YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the lengths of the image's parts *)
Ltac w8_len := repeat first [ rewrite length_app | rewrite length_zeros | rewrite length_le32 | rewrite length_le64
  | rewrite length_flat_ent_mem by assumption | rewrite length_ent_mem by assumption ].
Ltac w8_lenH h := repeat first [ rewrite length_app in h | rewrite length_zeros in h | rewrite length_le32 in h
  | rewrite length_le64 in h | rewrite length_flat_ent_mem in h by assumption
  | rewrite length_ent_mem in h by assumption ].
(* a byte of the block outside the four written ranges: the step's frame hypothesis K *)
Ltac w8_k K := apply K;
  [ lia | lia | lia
  | first [ intros [? _]; discriminate | intros [_ ?]; lia ]
  | first [ intros [? _]; discriminate | intros [_ ?]; lia ] ].

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

Lemma w8_at : forall H mem a a' l, rm_bytes segs H mem a l -> a' = a -> rm_bytes segs H mem a' l.
Proof. intros H mem a a' l B E. rewrite E. exact B. Qed.

Lemma w8_kept_at : forall H mem H' mem' a a' l, rm_bytes segs H mem a l -> a' = a ->
  (forall y, a <= y < a + Z.of_nat (length l) -> aview segs H' mem' y = aview segs H mem y) ->
  rm_bytes segs H' mem' a' l.
Proof. intros H mem H' mem' a a' l B E K. rewrite E. exact (rm_bytes_kept segs H mem H' mem' a l B K). Qed.

(* a part of the new image read off the old one at the same address, kept by the step *)
Ltac w8_kept O K := eapply w8_kept_at;
  [ exact O | w8_len; lia
  | let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy; w8_lenH Hy; w8_k K ].

Lemma w8_img_step : forall H mem H' mem' pp (b x : list byte) isp hasp pst (es : list ent) (ed : ent) (fi : bool),
  Z.of_nat (length b) <= POD_BUF_MAX -> Z.of_nat (length b + length x) <= POD_BUF_MAX ->
  (length es <= 32)%nat ->
  (fi = true -> (length es < 32)%nat) ->
  Forall (fun e => (length (e_body e) <= 96)%nat) es -> (length (e_body ed) <= 96)%nat ->
  rm_bytes segs H mem pp (pp_image b isp hasp pst es false) ->
  rm_bytes segs H' mem' (pp + Z.of_nat (length b)) x ->
  val_mem segs (mrestrict H' mem') (pp + OFF_LEN) 8 (Z.of_nat (length b + length x)) ->
  (fi = true -> rm_bytes segs H' mem' (pp + OFF_ENT + ENT_SIZE * Z.of_nat (length es)) (ent_mem ed) /\
                val_mem segs (mrestrict H' mem') (pp + OFF_N_ENT) 4 (Z.of_nat (length es) + 1)) ->
  (forall y, pp <= y < pp + PP_SIZE ->
     ~ (pp + Z.of_nat (length b) <= y < pp + Z.of_nat (length b + length x)) ->
     ~ (pp + OFF_LEN <= y < pp + OFF_LEN + 8) ->
     ~ (fi = true /\ pp + OFF_ENT + ENT_SIZE * Z.of_nat (length es) <= y
                     < pp + OFF_ENT + ENT_SIZE * Z.of_nat (length es) + ENT_SIZE) ->
     ~ (fi = true /\ pp + OFF_N_ENT <= y < pp + OFF_N_ENT + 4) ->
     aview segs H' mem' y = aview segs H mem y) ->
  rm_bytes segs H' mem' pp (pp_image (b ++ x) isp hasp pst (if fi then es ++ [ed] else es) false).
Proof.
intros H mem H' mem' pp b x isp hasp pst es ed fi Hb Hbx Hes Hes1 Hs Hed Old Nx Nlen Nfi K.
unfold pp_image in Old |- *.
unfold POD_BUF_MAX, POD_ENT_MAX, OFF_LEN, OFF_ENT, ENT_SIZE, OFF_N_ENT, PP_SIZE in *.
(* buf's zero tail: |x| bytes for x, then the new tail *)
assert (Ez1 : zeros (Z.to_nat (16384 - Z.of_nat (length b)))
              = zeros (length x) ++ zeros (Z.to_nat (16384 - Z.of_nat (length b + length x)))).
{ rewrite <- zeros_app. f_equal. lia. }
rewrite Ez1 in Old.
apply rm_bytes_app in Old as [Ob Old]. apply rm_bytes_app in Old as [Oz Old].
apply rm_bytes_app in Oz as [_ Oz1]. apply rm_bytes_app in Old as [_ Old].
rewrite !length_app.
(* buf, its zero tail, len *)
apply rm_bytes_app. split.
{ apply rm_bytes_app. split; [w8_kept Ob K | exact Nx]. }
apply rm_bytes_app. split; [w8_kept Oz1 K|].
apply rm_bytes_app. split.
{ eapply w8_at; [unfold le64; apply rm_bytes_of_val; exact Nlen | w8_len; lia]. }
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
  apply rm_bytes_app in Old as [O1 Old]. apply rm_bytes_app in Old as [O2 Old].
  apply rm_bytes_app in Old as [O3 Old]. apply rm_bytes_app in Old as [OF Old].
  apply rm_bytes_app in Old as [OZ Old]. apply rm_bytes_app in OZ as [_ OZ2].
  apply rm_bytes_app in Old as [_ OC].
  destruct (Nfi eq_refl) as [Ne Nn].
  apply rm_bytes_app. split; [w8_kept O1 K|].
  apply rm_bytes_app. split; [w8_kept O2 K|].
  apply rm_bytes_app. split; [w8_kept O3 K|].
  apply rm_bytes_app. split.
  { apply rm_bytes_app. split; [w8_kept OF K|].
    eapply w8_at; [exact Ne | w8_len; lia]. }
  apply rm_bytes_app. split; [w8_kept OZ2 K|].
  apply rm_bytes_app. split.
  { eapply w8_at; [unfold le32; apply rm_bytes_of_val; exact Nn | w8_len; lia]. }
  w8_kept OC K.
- (* no entry recorded: everything after len is the old image's *)
  change (if false then es ++ [ed] else es) with es.
  clear Hes1.
  w8_kept Old K.
Qed.
End i.
