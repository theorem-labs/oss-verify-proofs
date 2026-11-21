(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel PrintfFormats Stdio Driver.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_memset F_memcpy F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Printf_mlib F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_vfprintf.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_vfprintf.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_vfprintf.

Module Printf_sn.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ITree.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.

Lemma zlength_app : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_nil : zlength (@nil Z) = 0.
Proof. reflexivity. Qed.
Lemma zlength_concat_cons : forall {A} (p : list A) ps, zlength (concat (p :: ps)) = zlength p + zlength (concat ps).
Proof. intros. cbn [concat]. apply zlength_app. Qed.
Lemma zlength_concat_app : forall {A} (ps qs : list (list A)), zlength (concat (ps ++ qs)) = zlength (concat ps) + zlength (concat qs).
Proof. intros. rewrite concat_app. apply zlength_app. Qed.
Lemma zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Lemma mbind_eq : forall {St A B} (m : M St A) (f : A -> M St B) s a s',
  m s = ITree.Ret (Ok (a, s')) -> mbind m f s = f a s'.
Proof. intros St A B m f s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma OUT_sn_eq : forall bs o, zlength o + zlength bs <= SN_CAP -> OUT_sn bs o = ITree.Ret (Ok (tt, o ++ bs)).
Proof.
  intros bs o H. unfold OUT_sn. rewrite (mbind_eq mget _ o o o) by reflexivity.
  replace (zlength o + zlength bs <=? SN_CAP) with true by (symmetry; apply Z.leb_le; exact H). reflexivity.
Qed.

Lemma mbind_mbind_eq : forall {St A B C} (m : M St A) (f : A -> M St B) (g : B -> M St C) s a s',
  m s = ITree.Ret (Ok (a, s')) -> mbind (mbind m f) g s = mbind (f a) g s'.
Proof. intros St A B C m f g s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma mpad_sn_eq : forall c w l fl o ps,
  pad_pieces c w l fl = Some ps -> zlength o + zlength (concat ps) <= SN_CAP ->
  mpad OUT_sn c w l fl o = ITree.Ret (Ok (tt, o ++ concat ps)).
Proof.
  intros c w l fl o ps P H. unfold mpad, pad_pieces in *.
  destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
  - inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity.
  - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [concat] in *. rewrite app_nil_r in *.
    apply OUT_sn_eq. exact H.
Qed.

Ltac msn E := first [ rewrite (mbind_mbind_eq _ _ _ _ _ _ E) | rewrite (mbind_eq _ _ _ _ _ E) ]; cbv beta.

Lemma conv_tail_sn : forall cnt fl w p prefix body (k : Z -> M (list Z) Z) o ps r,
  tail_pieces cnt fl w p prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  mbind (conv_tail OUT_sn cnt fl w p prefix body) k o = k r (o ++ concat ps).
Proof.
  intros cnt fl w p prefix body k o ps r T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
  destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
  destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
  destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
  destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
  destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
  destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
  inversion T; subst. clear T.
  repeat first [rewrite zlength_concat_app in H | rewrite zlength_concat_cons in H]. rewrite ?zlength_nil in H. cbn [concat] in H. rewrite ?app_nil_r, ?zlength_nil in H.
  pose proof (zlength_nonneg (concat p1)). pose proof (zlength_nonneg (concat p2)). pose proof (zlength_nonneg (concat p3)).
  pose proof (zlength_nonneg (concat p4)). pose proof (zlength_nonneg prefix). pose proof (zlength_nonneg body). pose proof (zlength_nonneg o).
  pose proof (mpad_sn_eq _ _ _ _ o _ P1 ltac:(lia)) as E1. msn E1.
  pose proof (OUT_sn_eq prefix (o ++ concat p1) ltac:(rewrite zlength_app; lia)) as E2. msn E2.
  pose proof (mpad_sn_eq _ _ _ _ ((o ++ concat p1) ++ prefix) _ P2 ltac:(rewrite !zlength_app; lia)) as E3. msn E3.
  pose proof (mpad_sn_eq _ _ _ _ (((o ++ concat p1) ++ prefix) ++ concat p2) _ P3 ltac:(rewrite !zlength_app; lia)) as E4. msn E4.
  pose proof (OUT_sn_eq body ((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ltac:(rewrite !zlength_app; lia)) as E5. msn E5.
  pose proof (mpad_sn_eq _ _ _ _ (((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ++ body) _ P4 ltac:(rewrite !zlength_app; lia)) as E6. msn E6.
  rewrite mbind_mret. rewrite ?concat_app. cbn [concat]. rewrite ?concat_app. cbn [concat]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma conv_int_sn : forall cnt fl w p xp argi prefix body (k : Z -> M (list Z) Z) o ps r,
  int_pieces cnt fl w p xp argi prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  mbind (conv_int OUT_sn cnt fl w p xp argi prefix body) k o = k r (o ++ concat ps).
Proof.
  intros cnt fl w p xp argi prefix body k o ps r T H. unfold conv_int, int_pieces in *.
  destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
  destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_sn; eassumption.
Qed.

Lemma conv_sn : forall cnt d a (k : Z -> M (list Z) Z) o ps r,
  conv_pieces cnt d a = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  mbind (conv OUT_sn OUTFP_sn cnt d a) k o = k r (o ++ concat ps).
Proof.
  intros cnt d a k o ps r T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
  destruct a as [s| |i|u|u|dd].
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
    eapply conv_tail_sn; eassumption.
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength NULLSTR))%bool; [discriminate|].
    eapply conv_tail_sn; eassumption.
  - destruct (negb (d_ty d =? T_INT)); [discriminate|].
    destruct (INTMAX_MAX <? i mod 2 ^ 64);
      [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
      eapply conv_int_sn; eassumption.
  - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
    destruct (d_t d =? 117); eapply conv_int_sn; eassumption.
  - destruct (negb (d_ty d =? T_SIZET)); [discriminate|].
    destruct (d_t d =? 117); [|discriminate]. eapply conv_int_sn; eassumption.
  - discriminate.
Qed.

Lemma printf_loop_sn : forall fuel s args cnt o ps r,
  printf_pieces_loop fuel s args cnt = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  printf_loop OUT_sn OUTFP_sn fuel s args cnt o = ITree.Ret (Ok (r, o ++ concat ps)).
Proof.
  induction fuel as [|fuel IH]; intros s args cnt o ps r P H; [discriminate|].
  cbn [printf_pieces_loop] in P. cbn [printf_loop].
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0). { inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity. }
  cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  pose proof (zlength_nonneg o) as Ho.
  destruct (0 <? zlength lit).
  - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
    destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
    inversion P; subst. clear P. rewrite zlength_concat_cons in H. pose proof (zlength_nonneg (concat ps')).
    pose proof (OUT_sn_eq lit o ltac:(lia)) as E1. msn E1.
    rewrite (IH _ _ _ _ _ _ R) by (rewrite zlength_app; lia). cbn [concat]. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
  - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
    destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
    destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
    inversion P; subst. clear P. rewrite zlength_concat_cons, zlength_concat_app, zlength_nil in H.
    pose proof (zlength_nonneg (concat ps1)). pose proof (zlength_nonneg (concat ps2)).
    pose proof (OUT_sn_eq [] o ltac:(rewrite zlength_nil; lia)) as E1. msn E1. rewrite app_nil_r.
    rewrite (conv_sn _ _ _ _ _ _ _ C) by lia.
    rewrite (IH _ _ _ _ _ _ R) by (rewrite ?zlength_app; lia). cbn [concat]. rewrite ?concat_app. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
Qed.

Theorem printf_model_sn : forall fmt args ps r,
  printf_pieces fmt args = Some (ps, r) -> zlength (concat ps) <= SN_CAP ->
  printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, concat ps)).
Proof.
  intros fmt args ps r P H. unfold printf_model, printf_pieces in *.
  exact (printf_loop_sn _ _ _ _ [] _ _ P ltac:(rewrite zlength_nil; lia)).
Qed.

End Printf_sn.

Module F_vsnprintf.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_memset F_memcpy F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Printf_mlib F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_vfprintf.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_printf_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_vfprintf.F_printf_core.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_vfprintf.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_sn_write.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_vfprintf.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_vfprintf.F_printf_snsink OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_sn_write OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.F_towrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_vfprintf OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fprintf.Printf_sn.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call usegs m mm MU WM end end.
Import ListNotations.
Import ITree.Exc.
Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Local Ltac tslia ::= first [ exact I | clear_big; first [ tlia | split; [ tlia | exact I ] ] ].
Local Open Scope Z_scope.
Local Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= clear_big; lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Lemma rw_cells_recast : forall m A cs cs', rw_cells usegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells usegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma rw_cells_C4_eqv : forall m A pre v v' post, rw_cells usegs m A (pre ++ C4 v :: post) -> le4 v = le4 v' -> rw_cells usegs m A (pre ++ C4 v' :: post).
Proof.
  intros m A pre v v' post H E. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 [_ W2]]. apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
Qed.
Ltac c4_eqv H k v' :=
  lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
    lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some (C4 ?v) =>
      let H' := fresh in
      pose proof (rw_cells_C4_eqv m A pre v v' post) as H'; cbn [app] in H';
      specialize (H' H ltac:(unfold le4; cbn [Z_to_le_bytes]; repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity)); clear H; rename H' into H
    end end.

Lemma arg_ok_relayout : forall Fp' B' BS' m lo sp ap' sp' w a,
  arg_ok 0 0 0 m lo sp 0 w a -> lo <= Fp' -> Fp' + 232 <= sp -> lo <= B' -> B' + BS' <= sp -> lo <= ap' -> ap' + 8 <= sp -> sp' <= sp ->
  arg_ok Fp' B' BS' m lo sp' ap' w a.
Proof.
  intros Fp' B' BS' m lo sp ap' sp' w a H H1 H2 H3 H4 H5 H6 H7. destruct a as [s| |i|u|u|d]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4). exists slack.
  repeat (split; [first [assumption | lia]|]). lia.
Qed.
Lemma args_ok_relayout : forall Fp' B' BS' m lo sp ap' sp' ws args,
  args_ok 0 0 0 m lo sp 0 ws args -> lo <= Fp' -> Fp' + 232 <= sp -> lo <= B' -> B' + BS' <= sp -> lo <= ap' -> ap' + 8 <= sp -> sp' <= sp ->
  args_ok Fp' B' BS' m lo sp' ap' ws args.
Proof.
  intros Fp' B' BS' m lo sp ap' sp' ws args. revert ws. induction args as [|a args IH]; intros ws H H1 H2 H3 H4 H5 H6 H7; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [Ha Hr].
  split; [eapply arg_ok_relayout; eassumption | apply IH; assumption].
Qed.

Lemma fmt_bytes_at : forall m A f, mem_inv usegs m -> ro_bytes_b usegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at usegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at usegs m A _ (ro_cells_image usegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.
End F_vsnprintf.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Printf_pieces Printf_stdio_iface.

Module F_vfprintf_stdout.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel PrintfFormats Stdio.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_memset F_memcpy F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Printf_mlib F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_vfprintf.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_vfprintf.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_vfprintf.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_printf_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_vfprintf.F_printf_core OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_vfprintf.F_printf_snsink OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.F_towrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_vfprintf OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fprintf.F_vsnprintf.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Printf_pieces Printf_stdio_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Local Ltac tslia ::= first [ exact I | clear_big; first [ tlia | split; [ tlia | exact I ] ] ].
Local Open Scope Z_scope.
Local Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= clear_big; lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM usegs c s Q ms) | _ => idtac end.

Lemma land_mod_low : forall f c k, 0 <= k -> 0 <= c < 2^k -> Z.land f c = Z.land (f mod 2^k) c.
Proof.
  intros f c k Hk Hc. rewrite <- (Z.land_ones f k) by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones k) c), Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma dec128 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 128)) = true -> forall x, 0 <= x < 128 -> P x = true.
Proof.
  intros P H x Hx. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma land_sub_mask : forall u a b, Z.land a b = b -> Z.land u a = 0 -> Z.land u b = 0.
Proof. intros u a b Hab Hu. rewrite <- Hab, Z.land_assoc, Hu. apply Z.land_0_l. Qed.
Lemma mod_128_of_32 : forall a, (a mod 2^32) mod 128 = a mod 128.
Proof.
  intros a. change 128 with (2^7). rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.
Lemma sx32_mod128 : forall w : word, bv_unsigned (sx32 w) mod 128 = bv_unsigned w mod 128.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R. change (2^64)%Z with 18446744073709551616%Z.
  rewrite <- (mod_128_of_32 (bv_unsigned w)). change (2^32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.
Lemma land_low7 : forall a c, 0 <= c < 128 -> Z.land a c = Z.land (a mod 128) c.
Proof. intros a c Hc. change 128 with (2^7). apply land_mod_low; lia. Qed.

Lemma flags_noerr_nowr : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.
Lemma flags_noerr_104 : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 104 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 104) with 72.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. exact H.
Qed.
Lemma flags_olderr_72 : forall (flags2 flags : word), Z.land (bv_unsigned flags2) 104 = 0 ->
  Z.land (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32)) 72 = 0.
Proof.
  intros flags2 flags H. rewrite Z.land_lor_distr_l. rewrite <- (Z.land_assoc _ 32 72). change (Z.land 32 72) with 0. rewrite Z.land_0_r, Z.lor_0_r.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.


Section StdoutSinkProofs.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Let SINK := SINK_stdout (St:=St) get_so.

  Lemma stdout_sink_frame : sink_frame_stmt RSTDOUT RSTDOUT_BUF 1024 SINK.
  Proof using get_so.
    unfold sink_frame_stmt. intros W m m' st (ACT & flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN) MU WM D1 D2.
    split; [exact ACT|]. exists flags, mode, tail, bufbytes.
    split; [|split; [exact FL | split; [| split; [exact PFX | exact LEN]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
  Qed.

  Lemma file_cells_flags_byte : forall m A flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
    rw_cells usegs m A (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
    rw_cells usegs m A [CB 1 [Z_to_bv 8 (bv_unsigned flags)]].
  Proof using .
    intros until tail. intros FC. unfold file_cells in FC.
    apply (proj1 (rw_cells_app usegs m A [_] _)) in FC. destruct FC as [F0 _].
    pose proof (rw_cells_recast m A _ [CB 1 [Z_to_bv 8 (bv_unsigned flags)]; CB 3 (Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8))] F0
                  ltac:(cbn; repeat split) ltac:(reflexivity)) as F1.
    apply (proj1 (rw_cells_app usegs m A [_] _)) in F1. exact (proj1 F1).
  Qed.

  Lemma stdout_sink_flags : sink_flags_stmt RSTDOUT SINK.
  Proof using get_so.
    unfold sink_flags_stmt. intros m st (ACT & flags & mode & tail & bufbytes & FC & FL & _).
    exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
    rewrite <- land_mod_low by lia. eapply land_sub_mask; [|exact FL]. reflexivity.
  Qed.

  Lemma topok_none : topok_stmt TOPOK_none.
  Proof using . unfold topok_stmt, TOPOK_none. intros. exact I. Qed.
End StdoutSinkProofs.

Lemma implM_upd_l {St B} : forall (f : St -> St) (k : unit -> M St B) s Q ms,
  Monad.implM usegs (k tt) (f s) Q ms -> Monad.implM usegs (mbind (mupd f) k) s Q ms.
Proof. intros. exact H. Qed.

Section Stdout.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.
  Hypothesis FWX : fwritex_stdout_stmt.

  Let OUT := OUT_stdout get_so set_so.
  Let SINK := SINK_stdout (St:=St) get_so.

  Definition vfprintf_stdout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ ssp_cells m' canary.

  Definition vfprintf_stdout_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stdout_file m (get_so st) ->
      bytes_at usegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDOUT RSTDOUT_BUF 1024 m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk usegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      Monad.implM usegs (stdout_towrite get_so set_so ;;; outsk OUT ps (mret tt)) st
        (vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x25ab0) fc None m (seg_rom usegs)).

  Theorem vfprintf_stdout_proof : vfprintf_stdout_stmt.
  Proof using FWX GS SS.
    unfold vfprintf_stdout_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & PFX & BLEN & INACT). unfold file_cells in FC.
    pose proof (rw_CB_length _ _ _ _ BUF) as LBB.
    unfold stdout_towrite, upd_so. apply implM_upd_l.
    apply (printf_model_outs usegs OUT (OUTFP_stdout (St:=St)) fmt args ps r (fun _ => mret tt) _ _ _ PP).
    ienter.
    carve_frame 368%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 368 junk [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 12 zs. do 14 zs.
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evt_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
    cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit. zs. zs. zs.
    destruct (so_active (get_so st)) eqn:ACT.
    -
      if_lit. cbv beta iota in FC.
      zs. zs. zs. zs. zs. zs.
      apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      ileave.
      pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
                    (stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS)) as PC2.
      unfold printf_core_stmt in PC2.
      assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
      { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      eapply implM_bind.
      { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
          clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
        all: try lia. all: try exact I.
        - unfold SINK, SINK_stdout. rewrite GS, ACT. split; [reflexivity|].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode, tail, bufbytes.
          split; [unfold file_cells; exact FC|]. split; [exact FL'|]. split; [exact BUF|]. split; [exact PFX | exact BLEN].
        - exact BY.
        - exact HF.
        - reflexivity.
        - replace (VA + 8 * 0) with VA by lia. exact APC.
        - exact VAA.
        - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
        - rewrite FPC. apply Forall_nil.
        - exact STc.
        - split; [exact SSP1 | exact SSP2].
        - assumption.
        - exact FRM. }
      cbv beta. intros r' st' ms' P. clear PC2 MU1.
      unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
      destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
      unfold SR in MUc. cbn [app] in MUc.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
      apply implM_ret. fix_ret.
      destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
      clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
      zs. zs. zs. if_lit.
      zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
      zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
      do 9 zs.
      replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
        by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
      change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
      rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
      lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
        assert (FALL : rw_cells usegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
        [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
        | clear AP FR ] end.
      cbn [app] in FALL.
      release_frame FALL ST3 (bv_unsigned sp).
      apply evt_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
      split; [exact ST3|].
      split.
      { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
        rewrite ACT3. split; [unfold file_cells; exact FC3|].
        split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
        rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
        pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
        unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
        split; [apply Z.lor_nonneg; lia|].
        apply (lor_lt_pow2 _ _ 64); lia. }
      split; [exact SSP1 | exact SSP2].
    -
      if_lit. cbv beta iota in FC. zs. zs. zs.
      pose proof towrite_proof as TW. unfold towrite_stmt in TW.
      eapply evt_cut.
      { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption ].
        rewrite unsigned_lit; [apply flags_noerr_nowr; exact FL72|].
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      cbv beta. intros ms' P. clear TW.
      destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
      rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
      fix_ret.
      zs. if_lit. zs. zs. zs. zs. zs. zs.
      apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      ileave.
      pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
                    (stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS)) as PC2.
      unfold printf_core_stmt in PC2.
      assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
      { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      eapply implM_bind.
      { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
          clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
        all: try lia. all: try exact I.
        - unfold SINK, SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [reflexivity|].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, bufbytes.
          change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
          split; [exact FCt|]. split; [exact FL'|]. split; [exact BUF|]. split; [reflexivity | lia].
        - exact BY.
        - exact HF.
        - reflexivity.
        - replace (VA + 8 * 0) with VA by lia. exact APC.
        - exact VAA.
        - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
        - rewrite FPC. apply Forall_nil.
        - exact STc.
        - split; [exact SSP1 | exact SSP2].
        - assumption.
        - exact FRM. }
      cbv beta. intros r' st' ms' P. clear PC2 MU1.
      unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
      destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
      unfold SR in MUc. cbn [app] in MUc.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
      apply implM_ret. fix_ret.
      destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
      clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
      zs. zs. zs. if_lit.
      zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
      zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
      do 9 zs.
      replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
        by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
      change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
      rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
      lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
        assert (FALL : rw_cells usegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
        [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
        | clear AP FR ] end.
      cbn [app] in FALL.
      release_frame FALL ST3 (bv_unsigned sp).
      apply evt_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
      split; [exact ST3|].
      split.
      { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
        rewrite ACT3. split; [unfold file_cells; exact FC3|].
        split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
        rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
        pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
        unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
        split; [apply Z.lor_nonneg; lia|].
        apply (lor_lt_pow2 _ _ 64); lia. }
      split; [exact SSP1 | exact SSP2].
  Qed.
End Stdout.

Lemma stdout_file_stk : forall m m' so lo hi, stdout_file m so -> munch [(lo, hi)] m m' -> wmono usegs m m' -> 385024 <= lo -> stdout_file m' so.
Proof.
  intros m m' so lo hi (flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & INACT) MU WM Hlo.
  exists flags, mode, tail, bufbytes. split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN | exact INACT]]]]].
  - eapply rw_cells_transport; [exact FC | exact MU | exact WM | cbn [disjoint_from cells_size file_cells csize Nat.add]; lia].
  - eapply rw_cells_transport; [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed.

Theorem emit_printf_proof : forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
  emit_printf_stmt get_so set_so.
Proof.
  intros St get_so set_so. unfold emit_printf_stmt. intros until canary. intros GS SS FWX SF Ha1 ST LO GLO QHI SSP MI FRM.
  unfold EMIT_DEPTH, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
  unfold stdout_vprintf.
  change (out_pieces get_so set_so pieces_emit_0) with (outsk (OUT_stdout get_so set_so) pieces_emit_0 (mret tt)).
  ienter.
  carve_frame 80%nat ST.
  do 15 zs.
  do 7 zs.
  apply (proj1 (rw_cells_app usegs _ _ [_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
  replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in VAC by lia.
  pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
  change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.
  ileave.
  pose proof (vfprintf_stdout_proof get_so set_so GS SS FWX) as VF. unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
  eapply implM_post_evt.
  { eapply VF with (A := A_FMT_emit) (VA := bv_unsigned sp + -56) (fmt := FMT_emit) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [PA_i 0])
                   (r := 2) (lo := lo) (canary := canary);
      clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
    all: try reflexivity. all: try lia.
    - eapply stdout_file_stk; [exact SF | exact MU1 | exact WM | lia].
    - apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_emit; lia | vm_compute; discriminate].
    - unfold FMT_emit. forall_range.
    - exact VAA.
    - cbn [args_ok arg_ok]. split; [|exact I]. split; [lia|]. rewrite Ha1. reflexivity.
    - exact ST.
    - split; [exact SSP1 | exact SSP2].
    - exact MI.
    - exact FRM.
    - unfold A_FMT_emit, FMT_emit. cbn [length]. lia.
    - unfold A_FMT_emit, FMT_emit. cbn [length]. lia. }
  cbv beta. intros [] st' ms' P. clear MU1.
  unfold vfprintf_stdout_post in P. rewrite !unsigned_lit in P by lia.
  destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
  fix_ret.
  zs. zs. zs.
  lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -56)%Z ?rest |- _ =>
    assert (FALL : rw_cells usegs mm (bv_unsigned sp + -80) (hd ++ rest));
    [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
    | clear FR VAC ] end.
  cbn [app] in FALL.
  release_frame FALL ST3 (bv_unsigned sp).
  apply evt_done. unfold emit_printf_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST3|]. split; [exact SF3|]. exact SSP3.
Qed.
End F_vfprintf_stdout.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_printf_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_vfprintf.F_printf_core OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_vfprintf.F_printf_snsink OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.F_towrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_vfprintf OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fprintf.F_vsnprintf OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_pieces OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fprintf.F_vfprintf_stdout.

Module Printf_bridge.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState Mem Exec ITree Nodes Decode.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.MState.PropExec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.MState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Mem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Exec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ITree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Nodes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel Stdio.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfFormats.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Printf_mlib F_printf_iface Printf_stdio_iface Printf_pieces.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_printf_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Printf_pieces OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fprintf.Printf_sn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.

Section ITreeFacts.
  Variable segs : list Segment.
  Context {node : Type}.
  Variable atn : node -> machine_state -> Prop.
  Local Notation impl := (ITree.impl segs atn).
  Local Notation bind := (ITree.bind node).

  Fixpoint tforall {A} (P : A -> Prop) (t : itree node A) : Prop :=
    match t with
    | ITree.Ret r => P r
    | Vis n k => forall x, tforall P (k x)
    end.

  Lemma tforall_bind : forall {A B} (P : A -> Prop) (P' : B -> Prop) (t : itree node A) (f : A -> itree node B),
    tforall P t -> (forall a, P a -> tforall P' (f a)) -> tforall P' (bind t f).
  Proof.
    induction t as [r|n k IH]; intros f H Hf; cbn in *; [apply Hf; exact H|].
    intros x. apply IH; [apply H | exact Hf].
  Qed.

  Lemma impl_bind_ext2 : forall {A B C} (P : A -> Prop) (t : itree node A) (f : A -> itree node B) (g : A -> itree node C) Q1 Q2 ms,
    tforall P t ->
    (forall r ms', P r -> impl (f r) Q1 ms' -> impl (g r) Q2 ms') ->
    impl (bind t f) Q1 ms -> impl (bind t g) Q2 ms.
  Proof.
    induction t as [r|n k IH]; intros f g Q1 Q2 ms HP Hfg H; cbn [ITree.bind] in *.
    - apply Hfg; [exact HP | exact H].
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. eapply IH; [apply HP | exact Hfg | apply Hk].
  Qed.

  Lemma impl_bind_elim : forall {A B} (P : A -> Prop) (t : itree node A) (h : A -> itree node B) Q1 Q2 ms,
    tforall P t ->
    (forall r ms', P r -> impl (h r) Q1 ms' -> evt segs (Q2 r) ms') ->
    impl (bind t h) Q1 ms -> impl t Q2 ms.
  Proof.
    induction t as [r|n k IH]; intros h Q1 Q2 ms HP Hh H; cbn [ITree.bind] in *.
    - cbn. apply (Hh r); [exact HP | exact H].
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. eapply IH; [apply HP | exact Hh | apply Hk].
  Qed.

  Lemma impl_tforall : forall {A} (P : A -> Prop) (t : itree node A) Q ms,
    tforall P t -> impl t Q ms -> impl t (fun r ms' => Q r ms' /\ P r) ms.
  Proof.
    induction t as [r|n k IH]; intros Q ms HP H; cbn in *.
    - eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ | exact HP].
    - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; [apply HP | apply Hk].
  Qed.
End ITreeFacts.

Section StderrBridge.
  Variable segs : list Segment.
  Context {St : Type}.
  Local Notation impl := (ITree.impl segs (at_node segs)).

  Definition FLUSH_stderr : M (list Z * St) unit :=
    fun bs => let '(buf, st) := bs in
      ebind (stdio_writev 2 buf [] st) (fun r => ITree.Ret (Ok (tt, (@nil Z, snd r)))).

  Lemma wv_loop_leaves : forall fuel fd iovs (st : St),
    tforall (fun r => match r with Ok q => snd q = st | Unr => True end) (mloop fuel (wv_body fd) iovs st).
  Proof.
    induction fuel as [|fuel IH]; intros fd iovs st; cbn [mloop]; [exact I|].
    unfold mbind at 1. unfold wv_body, mbind, msys, enode, ebind. cbn [ITree.bind].
    intros x. destruct (dec_writev (iov_total iovs) x) as [k|]; cbn [ITree.bind fst snd]; [|exact I].
    unfold mret. cbn [ITree.bind fst snd].
    destruct (k =? iov_total iovs); cbn [ITree.bind fst snd]; [reflexivity | apply IH].
  Qed.
  Lemma stdio_writev_leaves : forall fd buf s (st : St),
    tforall (fun r => match r with Ok q => snd q = st | Unr => True end) (stdio_writev fd buf s st).
  Proof. intros fd buf s st. unfold stdio_writev. apply wv_loop_leaves. Qed.

  Lemma OUT_stderr_leaves : forall p buf (st : St),
    tforall (fun r => match r with Ok q => snd (snd q) = st | Unr => True end) (OUT_stderr p (buf, st)).
  Proof.
    intros p buf st. unfold OUT_stderr.
    destruct (OUT_MAX <? zlength p); [cbn; exact I|].
    destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p); [|cbn; reflexivity].
    unfold ebind. eapply tforall_bind; [apply stdio_writev_leaves|]. intros [|[a s']] H; cbn; [exact I | exact H].
  Qed.

  Lemma outsk_flush_leaves : forall ps buf (st : St),
    tforall (fun r => match r with Ok q => snd (snd q) = st | Unr => True end) (outsk OUT_stderr ps FLUSH_stderr (buf, st)).
  Proof.
    induction ps as [|p ps IH]; intros buf st; cbn [outsk].
    - unfold FLUSH_stderr, ebind. eapply tforall_bind; [apply stdio_writev_leaves|]. intros [|[a s']] H; cbn; [exact I | exact H].
    - unfold mbind at 1. unfold ebind. eapply tforall_bind; [apply OUT_stderr_leaves|].
      intros [|[[] [buf' st']]] H; cbn in H |- *; [exact I|]. subst st'. apply IH.
  Qed.

  Lemma stderr_bridge : forall ps buf (st : St) (Q : St -> machine_state -> Prop) ms,
    Forall (fun p => zlength p <= OUT_MAX) ps ->
    impl (outsk OUT_stderr ps FLUSH_stderr (buf, st)) (epost (fun p ms' => Q (snd (snd p)) ms')) ms ->
    impl (mbind (stderr_pieces buf ps) (fun b => stdio_writev 2 b []) st) (epost (fun p ms' => Q (snd p) ms')) ms.
  Proof.
    induction ps as [|p ps IH]; intros buf st Q ms SZ H; cbn [outsk stderr_pieces] in H |- *.
    -
      rewrite mbind_mret. unfold FLUSH_stderr, ebind in H.
      eapply (impl_bind_elim segs (at_node segs) _ _ _ _ _ _ (stdio_writev_leaves 2 buf [] st)); [|exact H].
      intros [|[[] st']] ms' Hr Hi; cbn in Hi |- *; [apply evt_done; exact I|].
      cbn in Hi. exact Hi.
    - apply Forall_cons_iff in SZ. destruct SZ as [SZp SZ].
      assert (G : (OUT_MAX <? zlength p) = false) by (apply Z.ltb_ge; lia).
      destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p) eqn:T.
      +
        unfold mbind at 1 in H. unfold OUT_stderr in H. rewrite G, T in H. unfold ebind in H.
        apply impl_bind_assoc_rev in H.
        unfold mbind at 1. change ((stdio_writev 2 buf p ;;; stderr_pieces [] ps) st) with (ebind (stdio_writev 2 buf p st) (fun q => stderr_pieces [] ps (snd q))).
        unfold ebind. apply impl_bind_assoc.
        eapply (impl_bind_ext2 segs (at_node segs) _ _ _ _ _ _ _ (stdio_writev_leaves 2 buf p st)); [|exact H].
        intros [|[[] st']] ms' Hr Hi; cbn [ITree.bind] in Hi |- *.
        * exact Hi.
        * cbn in Hr. subst st'. apply IH; [exact SZ | exact Hi].
      +
        unfold mbind at 1 in H. unfold OUT_stderr in H. rewrite G, T in H. cbn [ebind ITree.bind fst snd] in H.
        apply IH; [exact SZ | exact H].
  Qed.
End StderrBridge.

Section OnePiece.
  Context {St : Type}.
  Let zlength_app := @Printf_sn.zlength_app Z.

  Lemma stderr_pieces_fit : forall ps buf,
    zlength buf + zlength (concat ps) <= INTERNAL_BUFSIZ ->
    stderr_pieces (St:=St) buf ps = mret (buf ++ concat ps).
  Proof.
    induction ps as [|p ps IH]; intros buf H; cbn [stderr_pieces concat].
    - rewrite app_nil_r. reflexivity.
    - cbn [concat] in H. rewrite zlength_app in H.
      pose proof (zlength_nonneg' buf). pose proof (zlength_nonneg' p). pose proof (zlength_nonneg' (concat ps)).
      replace (INTERNAL_BUFSIZ - zlength buf <? zlength p) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite IH by (rewrite zlength_app; lia). rewrite app_assoc. reflexivity.
  Qed.

  Lemma stderr_fprintf_onepiece : forall ps,
    zlength (concat ps) <= INTERNAL_BUFSIZ ->
    stderr_fprintf (St:=St) ps = stderr_fprintf [concat ps].
  Proof.
    intros ps H. unfold stderr_fprintf.
    rewrite (stderr_pieces_fit ps []) by (change (zlength (@nil Z)) with 0; lia).
    rewrite (stderr_pieces_fit [concat ps] []) by (cbn [concat]; rewrite app_nil_r; change (zlength (@nil Z)) with 0; lia).
    cbn [concat app]. rewrite app_nil_r. reflexivity.
  Qed.
End OnePiece.
End Printf_bridge.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_fprintf.Printf_bridge.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Local Ltac tslia ::= first [ exact I | clear_big; first [ tlia | split; [ tlia | exact I ] ] ].
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= clear_big; lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM usegs c s Q ms) | _ => idtac end.

Section StderrSinkProofs.
  Context {St : Type}.
  Variable B : Z.
  Let SINK := SINK_stderr (St:=St) B.

  Lemma stderr_sink_frame : sink_frame_stmt RSTDERR B 80 SINK.
  Proof using .
    unfold sink_frame_stmt. intros W m m' [buf st] (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BLO) MU WM D1 D2.
    exists flags, mode, tail, rest.
    split; [|split; [exact FL32 | split; [exact FL8 | split; [| split; [exact LEN | split; [exact BHI | exact BLO]]]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
  Qed.

  Lemma stderr_sink_flags : sink_flags_stmt RSTDERR SINK.
  Proof using B.
    unfold sink_flags_stmt. intros m [buf st] (flags & mode & tail & rest & FC & FL32 & _).
    exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
    rewrite <- land_mod_low by lia. exact FL32.
  Qed.
End StderrSinkProofs.

Lemma flags40_8 : forall f, Z.land f 40 = 0 -> Z.land f 8 = 0.
Proof. intros f. apply land_sub_mask. reflexivity. Qed.
Lemma flags40_32 : forall f, Z.land f 40 = 0 -> Z.land f 32 = 0.
Proof. intros f. apply land_sub_mask. reflexivity. Qed.
Lemma sflags_noerr_8 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_8. exact H.
Qed.
Lemma sflags_noerr_32 : forall (flags : word),
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 32 = 0.
Proof.
  intros flags. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 32) with 0. apply Z.land_0_r.
Qed.
Lemma sflags_olderr0 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 -> Z.land (bv_unsigned (sx32 flags)) 32 = 0.
Proof. intros flags H. rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_32. exact H. Qed.
Lemma sflags_final_40 : forall (flags2 : word), Z.land (bv_unsigned flags2) 32 = 0 -> Z.land (bv_unsigned flags2) 8 = 0 ->
  Z.land (Z.lor (bv_unsigned (sx32 flags2)) 0) 40 = 0.
Proof.
  intros flags2 H32 H8. rewrite Z.lor_0_r. rewrite land_low7, sx32_mod128, <- land_low7 by lia.
  replace 40 with (Z.lor 32 8) by reflexivity. rewrite Z.land_lor_distr_r, H32, H8. reflexivity.
Qed.

Section Stderr.
  Context {St : Type}.
  Hypothesis FWE : fwritex_stderr_stmt.
  Hypothesis FLS : stdio_write_flush_stmt.

  Definition vfprintf_stderr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : St -> machine_state -> Prop :=
    fun st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary.

  Definition vfprintf_stderr_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stderr_wfile m ->
      bytes_at usegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDERR (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk usegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      Monad.implM usegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x25ab0) fc None m (seg_rom usegs)).

  Theorem vfprintf_stderr_proof : vfprintf_stderr_stmt.
  Proof using FLS FWE.
    unfold vfprintf_stderr_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
    apply (printf_model_outs usegs OUT_stderr (OUTFP_stderr (St:=St)) fmt args ps r (fun _ => FLUSH_stderr) _ _ _ PP).
    match goal with |- Monad.implM _ _ _ ?Q _ => set (QQ := Q) end.
    ienter.
    carve_frame 368%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 368 junk [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 12 zs. do 14 zs.
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evt_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
    cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit.
    do 10 zs.
    pose proof towrite_proof as TW. unfold towrite_stmt in TW.
    eapply evt_cut.
    { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption ].
      rewrite unsigned_lit; [apply sflags_noerr_8; exact FL40|].
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    cbv beta. intros ms' P. clear TW.
    destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
    rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. do 6 zs.
    set (B := bv_unsigned sp + -352) in *.
    match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
    apply (rw_cells_split_CB usegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with B in BUFc by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FRv by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in AP2 by lia.
    match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
    match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
    pose proof (rw_CB_length _ _ _ _ BUFc) as LJB.
    replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).
    ileave.
    pose proof (printf_core_proof (list Z * St) RSTDERR B 80 (SINK_stderr B) TOPOK_none OUT_stderr (OUTFP_stderr (St:=St))
                  (stderr_sink_frame B) (stderr_sink_flags B) (topok_none) (FWE St B)) as PC2.
    unfold printf_core_stmt in PC2.
    assert (FR3 : 0 <= Z.land (bv_unsigned (sx32 flags)) 18446744073709551583 < 2^64).
    { pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    eapply implM_bind.
    { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
        clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
      all: try lia. all: try exact I.
      - unfold SINK_stderr. cbn [fst].
        exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, jb.
        change (zlength (@nil Z)) with 0. rewrite Z.add_0_r. cbn [zb map app].
        split; [exact FCt|]. rewrite unsigned_lit by lia.
        split; [apply sflags_noerr_32|]. split; [apply sflags_noerr_8; exact FL40|]. split; [exact BUFc|].
        unfold zlength. rewrite LJB. unfold GLOBALS_TOP. subst B. lia.
      - exact BY.
      - exact HF.
      - reflexivity.
      - exact APC.
      - exact VAA.
      - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
      - rewrite FPC. apply Forall_nil.
      - exact STc.
      - split; [exact SSP1 | exact SSP2].
      - assumption.
      - exact FRM. }
    cbv beta. intros r' [buf3 st3] ms' P. clear PC2 MU1.
    unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
    ienter. fix_ret.
    pose proof SNK3 as SNK3'. destruct SNK3' as (flags2 & mode2 & tail2 & rest2 & FC3 & FL32 & FL8 & BUF3 & LEN3 & BHI3 & BLO3). cbn [fst] in FC3, BUF3, LEN3.
    unfold file_cells in FC3.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs.
    ileave. unfold FLUSH_stderr, Monad.implM. cbv beta iota.
    pose proof (FLS St B) as FL. unfold stdio_write_flush_stmt in FL.
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 1024) _ H ltac:(lia)) as [ST4a ST4b]; clear H end.
    eapply impl_ebind.
    { unfold Monad.implM in FL.
      eapply FL with (lo := bv_unsigned sp + -368 - 1024) (canary := canary); clear FL; rewrite ?unsigned_lit by lia; unfold OUT_DEPTH, GLOBALS_TOP.
      all: try lia.
      - exact SNK3.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact ST4b.
      - split; [exact SSP1 | exact SSP2].
      - assumption. }
    cbv beta. intros [[] st4] ms' P.
    unfold stdio_write_flush_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (z5 & z6 & z7 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & ST4b' & SNK4 & SSP4).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m4 MUc WMc; clear MUc WMc end.
    apply impl_ret_intro. cbn [snd]. fix_ret.
    cbn [fst snd] in SNK4 |- *. clear SNK3 FL.
    destruct SNK4 as (flags4 & mode4 & tail4 & rest4 & FC4 & FL32' & FL8' & BUF4 & LEN4 & _ & _). cbn [fst snd] in FC4, BUF4, LEN4.
    unfold file_cells in FC4. change (zlength (@nil Z)) with 0 in FC4. rewrite Z.add_0_r in FC4.
    clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    do 9 zs.
    zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368 - 1024)%Z, H' : stk _ ?mm (bv_unsigned sp + -368 - 1024)%Z _ |- _ =>
      pose proof (stk_merge _ _ _ _ _ H H' ltac:(lia)) as ST5; clear H H' end.
    pose proof (rw_CB_length _ _ _ _ BUF4) as LB4.
    lazymatch goal with A1 : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, A2 : rw_cells _ ?mm (bv_unsigned sp + -360)%Z _,
                        BU : rw_cells _ ?mm B [CB 80 ?bb], FR : rw_cells _ ?mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA)] ++ [CB 80 bb] ++ rest));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact A1|];
        apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact A2 | lia] |];
        apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact BU | subst B; lia] |];
        cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
      | clear A1 A2 BU FR ] end.
    cbn [app] in FALL.
    release_frame FALL ST5 (bv_unsigned sp).
    apply evt_done. subst QQ. cbn [epost fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST5|].
    split.
    { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags4)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode4, 0, 0, tail4.
      split; [unfold file_cells; exact FC4|]. split; [| split; [left; reflexivity| lia]].
      rewrite (sflags_olderr0 flags FL40). rewrite unsigned_lit; [apply sflags_final_40; [exact FL32' | exact FL8']|].
      rewrite Z.lor_0_r. pose proof (bv_unsigned_in_range 64 (sx32 flags4)) as R4. unfold bv_modulus in R4. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R4. lia. }
    split; [exact SSP1 | exact SSP2].
  Qed.

  Definition fprintf_gen_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z) (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A ->
      stderr_wfile m ->
      bytes_at usegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      args_ok RSTDERR (q - 80 - 352) 80 m lo q (q - 80 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk usegs m lo q -> (lo <= q - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      Monad.implM usegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x253c0) fc None m (seg_rom usegs)).

  Theorem fprintf_gen_proof : fprintf_gen_stmt.
  Proof using FLS FWE.
    unfold fprintf_gen_stmt. intros until canary. cbv zeta.
    intros -> -> SF BY HF P1 AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA.
    unfold FPRINTF_DEPTH, VF_FRAME, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
    destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
    match goal with |- Monad.implM _ _ _ ?Q _ => set (QQ := Q) end.
    ienter.
    carve_frame 80%nat ST.
    do 17 zs.
    apply (proj1 (rw_cells_app usegs _ _ [_;_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (bv_unsigned sp + -80 + Z.of_nat 32)%Z with (bv_unsigned sp + -48)%Z in VAC by lia.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
    change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA.
    ileave.
    pose proof vfprintf_stderr_proof as VF. unfold vfprintf_stderr_stmt in VF. cbv zeta in VF.
    eapply implM_post_evt.
    { eapply VF with (A := A) (VA := bv_unsigned sp + -48) (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := args) (lo := lo) (canary := canary);
        clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
      all: try reflexivity. all: try lia.
      - exists flags, mode, e, wend, tail. split; [unfold file_cells; exact FC | exact FL40].
      - exact BY.
      - exact HF.
      - exact P1.
      - exact VAA.
      - eapply args_ok_vf; [| | exact MU]; [|lia].
        replace (bv_unsigned sp + -80 - 352)%Z with (bv_unsigned sp - 80 - 352)%Z by lia.
        replace (bv_unsigned sp + -80 - 368)%Z with (bv_unsigned sp - 80 - 368)%Z by lia. exact AOK.
      - exact PP.
      - exact FPC.
      - exact ST.
      - split; [exact SSP1 | exact SSP2].
      - exact MI.
      - exact FRM. }
    cbv beta. intros [] [b4 st4] ms' P. clear VF MU1. cbn [snd] in P.
    unfold vfprintf_stderr_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    zs. zs. zs. zs.
    lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -48)%Z ?rest |- _ =>
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -80) (hd ++ rest));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
      | clear FR VAC ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evt_done. subst QQ. cbn [fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST3|]. split; [exact SF3|]. split; [exact SSP1 | exact SSP2].
  Qed.
End Stderr.

Lemma forall_range_b : forall l, forallb (fun c => (0 <=? c) && (c <? 256))%bool l = true -> Forall (fun c => 0 <= c < 256) l.
Proof.
  intros l H. rewrite forallb_forall in H. apply Forall_forall. intros c Hc. specialize (H c Hc).
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma vf_to_diag_post : forall St ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (st st' : St) ms,
  vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st' ms -> st' = st ->
  fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt st' ms.
Proof.
  intros until ms. intros (x5 & x6 & x7 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & E & MU & WM & MI & FRM & FOK & ST & SF & SSP) Est.
  exists x5, x6, x7, a0, a1, a2, a3, a4, a5, a6, a7, x28, x29, x30, x31, Ft, fc', m'.
  apply stderr_wfile0_wfile in SF. repeat (split; [assumption|]). exact Est.
Qed.

Theorem fprintf_diag_proof : forall St : Type, @fprintf_diag_stmt St.
Proof.
  intros St. unfold fprintf_diag_stmt. intros d. intros until canary. intros FWE FLS SF Ha0 DA ST LO GLO QHI SSP MI FRM.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  unfold FPRINTF_DEPTH, GLOBALS_TOP in *.
  assert (BR : forall ps, Forall (fun p => zlength p <= OUT_MAX) ps -> Monad.implM usegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
                            (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
                            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x253c0) fc None m (seg_rom usegs)) ->
               Monad.implM usegs (stderr_fprintf ps) st
                            (fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
                            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x253c0) fc None m (seg_rom usegs))).
  { intros ps SZ H. unfold stderr_fprintf, Monad.implM in *.
    eapply impl_epost_mono.
    - eapply (stderr_bridge usegs ps [] st (fun s' ms' => fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt s' ms') _ SZ).
      eapply impl_mono; [eapply (impl_tforall usegs (at_node usegs) _ _ _ _ (outsk_flush_leaves ps [] st)); exact H|].
      intros [|[[] [b s']]] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I|]. eapply vf_to_diag_post; [exact H1 | exact H2].
    - intros [[] s'] ms' H'. exact H'. }
  pose proof (@fprintf_gen_proof St FWE FLS) as FG. unfold fprintf_gen_stmt in FG. cbv zeta in FG. unfold VF_FRAME, FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT in FG.
  destruct d as [argv0 | path | path | | | |]; cbn [diag_args] in DA; try contradiction; unfold s_diag; (apply BR; clear BR;
    [
      try (pose proof DA as DA'; destruct DA' as (_ & _ & _ & _ & _ & LEN' & _));
      unfold pieces_usage, pieces_cannot_open, pieces_read_error, pieces_too_big;
      repeat (apply Forall_cons; [ first [ unfold OUT_MAX; lia
                                          | unfold zlength; rewrite ?length_app; unfold OUT_MAX; cbn; lia
                                          | vm_compute; discriminate ] | ]); apply Forall_nil
    | ]).
  - destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA). unfold GLOBALS_TOP in GA.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length argv0) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
    eapply FG with (fmt := FMT_usage) (args := [PA_s argv0]) (A := A_FMT_usage); clear FG;
      first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
            | apply printf_pieces_usage; unfold zlength, INT_MAX in *; lia
            | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_usage; lia | vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity
            | cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
            | split; [exact (proj1 SSP) | exact (proj2 SSP)]
            | lia
            | reflexivity
            | vm_compute; discriminate ].
  - destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA). unfold GLOBALS_TOP in GA.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length path) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
    eapply FG with (fmt := FMT_cannot_open) (args := [PA_s path]) (A := A_FMT_cannot_open); clear FG;
      first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
            | apply printf_pieces_cannot_open; unfold zlength, INT_MAX in *; lia
            | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_cannot_open; lia | vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity
            | cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
            | split; [exact (proj1 SSP) | exact (proj2 SSP)]
            | lia
            | reflexivity
            | vm_compute; discriminate ].
  - destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA). unfold GLOBALS_TOP in GA.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length path) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
    eapply FG with (fmt := FMT_read_error) (args := [PA_s path]) (A := A_FMT_read_error); clear FG;
      first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
            | apply printf_pieces_read_error; unfold zlength, INT_MAX in *; lia
            | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_read_error; lia | vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity
            | cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
            | split; [exact (proj1 SSP) | exact (proj2 SSP)]
            | lia
            | reflexivity
            | vm_compute; discriminate ].
  - destruct DA as [Ha1 Hu]. pose proof (bv_unsigned_in_range 64 a2) as R2.
    eapply FG with (fmt := FMT_too_big) (args := [PA_u 67108864]) (A := A_FMT_too_big); clear FG;
      first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
            | apply printf_pieces_too_big
            | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_too_big; lia | vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity
            | cbn [args_ok arg_ok]; split; [split; [lia | exact Hu] | exact I]
            | split; [exact (proj1 SSP) | exact (proj2 SSP)]
            | lia
            | reflexivity
            | vm_compute; discriminate ].
Qed.
